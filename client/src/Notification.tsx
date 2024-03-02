import * as React from 'react'

const ErrorMessage: React.FC<{restart, close}> = ({restart, close}) => {
  return (
    <div className="notification-toasts">
      <div className="notification-toast-container">
        <div className="notification-toast">
          <div className="notification-row">
            <div className="notification-icon-wrapper">
              <div className="notification-icon codicon codicon-error"></div>
            </div>
            <div className="notification-row-main">The Lean Server has stopped processing this file.</div>
            <div className="notification-close-wrapper" onClick={close}>
              <div className="codicon codicon-close notification-close"></div>
            </div>
          </div>
          <div className="notification-row">
            <div className="notification-row-main"></div>
            <button onClick={restart}>Restart Lean Server on this file</button>
          </div>
        </div>
      </div>
    </div>
  )
}

const CommitNotification = ({close}) => {
    return <div className="notification-toasts">
        <div className="notification-toast-container">
        <div className="notification-toast">
            <div className="notification-row">
            <div className="notification-icon-wrapper">
                <div className="notification-icon codicon codicon-check"></div>
            </div>
            <div className="notification-row-main">File committed</div>
            <div className="notification-close-wrapper" onClick={close}>
                <div className="codicon codicon-close notification-close"></div>
            </div>
            </div>
        </div>
        </div>
    </div>
}
export {ErrorMessage, CommitNotification}

