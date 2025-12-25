import ReactDOM from 'react-dom/client'
import App from './App.tsx'
import './css/index.css'
import { StrictMode } from 'react'
import { NavBarProvider } from './context/NavBarContext.tsx'

ReactDOM.createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <NavBarProvider>
      <App />
    </NavBarProvider>
  </StrictMode>,
)
