import './css/index.css'

import { StrictMode } from 'react'
import ReactDOM from 'react-dom/client'

import App from './App.tsx'
import { NavBarComp } from './NavBar.tsx'

ReactDOM.createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <NavBarComp />
    <App />
  </StrictMode>,
)
