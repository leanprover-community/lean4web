import './css/InfoPane.css'

import { faCode } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { isRpcError, RpcErrorCode } from '@leanprover/infoview-api'
import { LeanClient, LeanMonaco } from 'lean4monaco'
import { RefObject, useEffect, useState } from 'react'

interface InfoPaneProps {
  infoviewRef: RefObject<HTMLDivElement | null>
  codeMirror: boolean
  isVerso: boolean
  leanMonaco: LeanMonaco | undefined
}

const TABS = ['Infoview', 'Verso'] as const

/**
 * Upon detecting a Verso document has finished elaborating, we will
 * immediately request the HTML document the first time. The next request will
 * be delayed by DEBOUNCE_MS milliseconds.
 */
const DEBOUNCE_MS = 1_000

type GetVersoContentsResult = { success: string } | { errors: string[] } | 'noDoc'
type VersoState = GetVersoContentsResult | 'loading' | 'noRpc'

async function getVersoContents(client: LeanClient, uri: string): Promise<GetVersoContentsResult> {
  const { sessionId } = await client.sendRequest('$/lean/rpc/connect', { uri })
  const result = await client.sendRequest('$/lean/rpc/call', {
    textDocument: { uri },
    position: { line: 0, character: 0 },
    sessionId,
    method: 'Verso.getLiveDocument',
    params: {},
  })
  return result
}

/**
 * Wraps the useEffect handler that controls Verso RPCs.
 */
function useVersoRPC(
  leanMonaco: LeanMonaco | undefined,
  isVerso: boolean,
  setVersoState: (srcDoc: VersoState) => void,
) {
  useEffect(() => {
    if (!leanMonaco?.clientProvider) return
    if (!isVerso) return

    // There's only going to be one client and two subscriptions, but the API is
    // set up for many and it's easier to go along with that design
    const subscriptions: { dispose: () => void }[] = []

    let currentDocumentVersion = -1
    let currentVersionHasRpcRequest = false
    let versionDebounceTimer: ReturnType<typeof setTimeout> | undefined = undefined

    const report = async (client: LeanClient, uri: string) => {
      const documentVersionBeforeRpc = currentDocumentVersion
      currentVersionHasRpcRequest = true

      try {
        const result = await getVersoContents(client, uri)
        if (currentDocumentVersion !== documentVersionBeforeRpc) {
          console.log('ignoring stale RPC response', result)
          return
        }
        setVersoState(result)
      } catch (e) {
        if (isRpcError(e) && e.code === RpcErrorCode.RpcNeedsReconnect) {
          return
        } else if (isRpcError(e) && e.code === RpcErrorCode.MethodNotFound) {
          setVersoState('noRpc')
        } else {
          console.warn('There was an error collecting verso content:', e)
        }
      }
    }

    const register = (client: LeanClient) => {
      console.log('CLIENT: ', client)

      subscriptions.push(
        client.didChange(({ textDocument }) => {
          currentVersionHasRpcRequest = false
          currentDocumentVersion = textDocument.version
        }),
      )
      subscriptions.push(
        client.progressChanged(([uri, processing]) => {
          if (processing.length > 0) return // partial progress only
          if (currentVersionHasRpcRequest) return // there are usually duplicate signals
          if (versionDebounceTimer === undefined) {
            void report(client, uri)
            versionDebounceTimer = setTimeout(() => {
              versionDebounceTimer = undefined
            }, DEBOUNCE_MS)
          } else {
            clearTimeout(versionDebounceTimer)
            versionDebounceTimer = setTimeout(() => {
              versionDebounceTimer = undefined
              void report(client, uri)
            }, DEBOUNCE_MS)
          }
        }),
      )
    }

    // realistically, there's one client ever
    // but we add the watcher to "all clients" (all one of them in lean4web)
    leanMonaco.clientProvider.getClients().forEach(register)
    // and to all future clients (there won't be any of them in lean4web)
    subscriptions.push(leanMonaco.clientProvider.clientAdded(register))

    return () => {
      clearTimeout(versionDebounceTimer)
      subscriptions.forEach((d) => d.dispose())
    }
  }, [leanMonaco, isVerso, setVersoState])
}

export default function InfoPane({ codeMirror, infoviewRef, isVerso, leanMonaco }: InfoPaneProps) {
  const [tab, setTab] = useState<(typeof TABS)[number]>(isVerso ? 'Verso' : 'Infoview')
  const [versoState, setVersoState] = useState<VersoState>('loading')
  useVersoRPC(leanMonaco, isVerso, setVersoState)

  return (
    <div
      id="infopane"
      style={{
        display: 'grid',
        gridTemplateRows: isVerso ? 'auto minmax(0, 1fr)' : '1fr',
        gridTemplateColumns: '1fr',
      }}
    >
      {isVerso && (
        <div role="tablist">
          {TABS.map((label) => (
            <button
              role="tab"
              className={tab === label ? 'infoview-tab selected' : 'infoview-tab not-selected'}
              key={label}
              aria-selected={tab === label}
              onClick={() => setTab(label)}
            >
              {label}
            </button>
          ))}
        </div>
      )}
      <div
        hidden={tab !== 'Infoview'}
        ref={infoviewRef}
        className="vscode-light infoview"
        style={{ width: '100%', height: '100%' }}
      >
        <p className={`editor-support-warning${codeMirror ? '' : ' hidden'}`}>
          You are in the plain text editor
          <br />
          <br />
          Go back to the Monaco Editor (click <FontAwesomeIcon icon={faCode} />) for the infoview to
          update!
        </p>
      </div>
      {isVerso &&
        tab === 'Verso' &&
        (versoState === 'loading' ? (
          <div style={{ paddingInline: '1em' }}>
            <p>Loading...</p>
          </div>
        ) : versoState === 'noRpc' ? (
          <div style={{ paddingInline: '1em' }}>
            <p>
              This Lean file does not import VersoManual, so it's not possible to read out a Lean
              document.
            </p>
            <p>A minimal Verso document looks like this:</p>
            <pre>
              {`import VersoManual
open Verso Genre Manual InlineLean

#doc (Manual) "Example" =>

Hello World`}
            </pre>
            <p>
              If you want to work on a normal Lean development, switch to the Infoview tab (or a
              different project).
            </p>
          </div>
        ) : versoState === 'noDoc' ? (
          <div style={{ paddingInline: '1em' }}>
            <p>
              Verso did not find a VersoManual document in this Lean file. This may be because
              you're missing a <code style={{ fontFamily: 'monospace' }}>#doc</code> command, or it
              may be because a Lean type error prevented the document from loading correctly.
            </p>
            <p>Switching to the Infoview tab may help you diagnose the problem.</p>
          </div>
        ) : 'success' in versoState ? (
          <iframe
            srcDoc={versoState.success}
            style={{ border: 'none', width: '100%', height: '100%', background: 'white' }}
          />
        ) : (
          'errors' in versoState && (
            <div style={{ paddingInline: '1em' }}>
              <p>Error{versoState.errors.length !== 1 && 's'} in document generation</p>
              <ul>
                {versoState.errors.map((err, i) => (
                  <li key={i}>{err}</li>
                ))}
              </ul>
            </div>
          )
        ))}
    </div>
  )
}
