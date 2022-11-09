import Lean

namespace MyServer.FileWorker
open Lean
open Lean.Server
open Lean.Server.FileWorker
open Lsp
open IO
open Snapshots
open JsonRpc

def mkEmptySnapshot : IO Snapshot := do
  return {
      beginPos := 0
      stx := Syntax.missing
      mpState := default
      cmdState := default
      interactiveDiags := default
      tacticCache := ← IO.mkRef {}
    }
    

section Updates

  def compileProof (newMeta : DocumentMeta) : IO Snapshot := do
    let message : Widget.InteractiveDiagnostic := {
      range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩,
      severity? := DiagnosticSeverity.information,
      message := Widget.TaggedText.text newMeta.text.source
    }
    let  snap := {
      beginPos := 0
      stx := default
      mpState := default
      cmdState := default
      interactiveDiags := PersistentArray.empty.push message
      tacticCache := (← IO.mkRef {})
    }  
    return snap

  def updateDocument (newMeta : DocumentMeta) : WorkerM Unit := do
    let cancelTk ← CancelToken.new
    let newSnaps ← EIO.asTask (ε := ElabTaskError) <| do 
      return AsyncList.ofList [← mkEmptySnapshot, ← compileProof newMeta]
    modify fun st => { st with doc := ⟨newMeta, AsyncList.delayed newSnaps, cancelTk⟩ }

end Updates

section Initialization

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    -- NOTE (AB): We don't have header tasks, so we just set it to some default values
    let headerTask ← EIO.asTask $ pure ⟨← mkEmptySnapshot, {}⟩
    let cancelTk ← CancelToken.new
    let ctx :=
      { hIn  := i
        hOut := o
        hLog := e
        headerTask
        initParams
        clientHasWidgets
      }
    let cmdSnaps ← EIO.mapTask (t := headerTask) (match · with
      | Except.ok (s, _) => unfoldCmdSnaps meta #[s] cancelTk ctx
      | Except.error e   => throw (e : ElabTaskError))
    let doc : EditableDocument := ⟨meta, AsyncList.delayed cmdSnaps, cancelTk⟩
    return (ctx,
    { doc             := doc
      pendingRequests := RBMap.empty
      rpcSessions     := RBMap.empty
    })

end Initialization

section NotificationHandling

  def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc := (←get).doc
    let some newVersion ← pure docId.version?
      | throwServerError "Expected version number"
    if newVersion ≤ oldDoc.meta.version then
      -- TODO(WN): This happens on restart sometimes.
      IO.eprintln s!"Got outdated version number: {newVersion} ≤ {oldDoc.meta.version}"
    else if ¬ changes.isEmpty then
      let newDocText := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText⟩

end NotificationHandling

section MessageHandling

  def handleNotification (method : String) (params : Json) : WorkerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams handleRpcKeepAlive
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

end MessageHandling

section MainLoop
  partial def mainLoop : WorkerM Unit := do
    let ctx ← read
    let mut st ← get
    let msg ← ctx.hIn.readLspMessage
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : IO PendingRequestMap := do
      if (← hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        pure <| acc.erase id
      else pure acc
    let pendingRequests ← st.pendingRequests.foldM (fun acc id task => filterFinishedTasks acc id task) st.pendingRequests
    st := { st with pendingRequests }

    -- Opportunistically (i.e. when we wake up on messages) check if any RPC session has expired.
    for (id, seshRef) in st.rpcSessions do
      let sesh ← seshRef.get
      if (← sesh.hasExpired) then
        st := { st with rpcSessions := st.rpcSessions.erase id }

    set st
    match msg with
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      mainLoop
    | Message.notification "exit" none =>
      let doc := st.doc
      doc.cancelTk.set
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) (opts : Options) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let doc := param.textDocument
  /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
    "\n", which should be enough to handle both LF and CRLF correctly.
    This is because LSP always refers to characters by (line, column),
    so if we get the line number correct it shouldn't matter that there
    is a CR there. -/
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap⟩
  let e := e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let (ctx, st) ← initializeWorker meta i o e initParams.param opts
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) mainLoop
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
    return (1 : UInt32)

def workerMain (opts : Options) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let exitCode ← initAndRunWorker i o e opts
    -- HACK: all `Task`s are currently "foreground", i.e. we join on them on main thread exit, but we definitely don't
    -- want to do that in the case of the worker processes, which can produce non-terminating tasks evaluating user code
    o.flush
    e.flush
    IO.Process.exit exitCode.toUInt8
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return (1 : UInt32)

end MyServer.FileWorker

def main : List String → IO UInt32 := fun args => do
  let e ← IO.getStderr
  if args[0]? == some "--server" then
    Lean.Server.Watchdog.watchdogMain []
  else if args[0]? == some "--worker" then
    MyServer.FileWorker.workerMain {}
  else
    e.putStrLn s!"Expected `--server` or `--worker`"
    return 1
