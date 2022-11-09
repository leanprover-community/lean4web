import Lean

def main : List String → IO UInt32 := fun args => do
  let e ← IO.getStderr
  e.putStrLn (← Lean.getBuildDir).toString
  e.flush
  if args.contains "--server" then
    Lean.Server.Watchdog.watchdogMain []
  else
    Lean.Server.FileWorker.workerMain {}


