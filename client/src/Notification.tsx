import * as React from 'react'

const ErrorMessage: React.FC = () => {
  return (
    <div className="notification-toasts">
      <div className="notification-toast-container">
        <div className="notification-toast">
          <div className="notification-row">
            <div className="notification-icon-wrapper">
              <div className="notification-icon codicon codicon-error"></div>
            </div>
            <div className="notification-row-main">The Lean Server has stopped processing this file.</div>
            <div className="notification-close-wrapper">
              <div className="codicon codicon-close notification-close"></div>
            </div>
            {/* onClick={handleClose} */}
          </div>
          <div className="notification-row">
            <div className="notification-row-main"></div>
            <button>Restart Lean Server on this file</button>
          </div>
        </div>
      </div>
    </div>
  )
}

export default ErrorMessage
