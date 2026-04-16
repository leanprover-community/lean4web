import './css/index.css'

import { StrictMode } from 'react'
import ReactDOM from 'react-dom/client'

import { NavBarProvider } from './context/NavBarContext.tsx'
import { NavBarLean, NavBar, NavItem, NavBarMathLib, NavBarComp } from './NavBar'

import App from './App.tsx'

ReactDOM.createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <NavBarProvider>
      <NavBarComp />
      <App />
    </NavBarProvider>
  </StrictMode>,
)
