import * as React from 'react'
import {useState, Suspense, useEffect} from 'react'
import './css/App.css'
import './css/Topbar.css'
import './css/Modal.css'
//import './css/dark-theme.css'
import PrivacyPolicy from './PrivacyPolicy'
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome'
import {
    faArrowRotateRight,
    faArrowUpRightFromSquare,
    faDownload,
    faBars,
    faXmark
} from '@fortawesome/free-solid-svg-icons'

const Editor = React.lazy(() => import('./Editor'))
import {ReactComponent as Logo} from './assets/logo.svg'
import {saveAs} from 'file-saver';
import Settings from './Settings'
import Tools from './Tools'
import Examples from './Examples'
import LoadingMenu from './LoadingMenu'
import {config} from './config/config'

function formatArgs(args) {
    let out = '#' + Object.entries(args).map(([key, val]) => (val ? `${key}=${val}` : null)).filter((x) => x).join('&')
    if (out == '#') {
        return ' '
    }
    return out
}

function parseArgs() {
    let _args = window.location.hash.replace('#', '').split('&').map((s) => s.split('=')).filter(x => x[0])
    return Object.fromEntries(_args)
}

const App: React.FC = () => {
    const [restart, setRestart] = useState<(project?) => Promise<void>>()
    const [navOpen, setNavOpen] = useState(false)
    const menuRef = React.useRef<HTMLDivElement>()
    const submenuRef = React.useRef<HTMLDivElement>()

    // Open a submenu. We manage submenus here so that only one submenu can be open at any time.
    const [submenu, setSubmenu] = useState<React.JSX.Element>(null)

    function openSubmenu(ev: React.MouseEvent, component: React.JSX.Element) {
        setNavOpen(true)
        setSubmenu(component)
        ev.stopPropagation()
    }

    function closeNav() {
        setNavOpen(false)
    }

    /* Option to change themes */
    const isBrowserDefaultDark = () => window.matchMedia('(prefers-color-scheme: dark)').matches
    const [theme, setTheme] = React.useState(isBrowserDefaultDark() ? 'GithubDark' : 'lightPlus')

    const [content, setContent] = useState<string>('')
    const [url, setUrl] = useState<string>(null)
    const [project, setProject] = useState<string>('banach-tarski')
    const [contentFromUrl, setContentFromUrl] = useState<string>(null)

    const readHash = () => {
        let args = parseArgs()
        if (args.file) {
            loadFromFile(decodeURIComponent(args.file))
        }
        console.log("Setting url to", decodeURIComponent(args.url))
        //if (args.project) {
        //  console.log(`setting project to ${args.project}`)
        //  setProject(args.project)
        //}
    }

    const onDidChangeContent = (newContent) => {
        setContent(newContent)
    }

    const save = () => {
        var blob = new Blob([content], {type: "text/plain;charset=utf-8"});
        saveAs(blob, "Lean4WebDownload.lean");
    }


    const loadFromFile = (fileName: string) => {
        // file in public folder
        if (fileName != null) {
            fetch(window.location.origin + "/project/" + fileName)
                .then((response) => response.text())
                .then((content) => {
                    setContent(content)
                    setContentFromUrl(content)
                    console.log(`loaded file fr from ${fileName}`, content)
                })
                .catch(err => {
                    setContent(err.toString())
                    setContentFromUrl(err.toString())
                })
        }
    }

    useEffect(() => {
        // Trigger onhashchange once in the beginning
        readHash()

        // Closing the dropdown menu or submenu when clicking outside it.
        // Use `ev.stopPropagation()` or `ev.stopImmediatePropagation()` inside
        // the menu to prevent.
        document.body.addEventListener("click", (ev) => {
            if (menuRef?.current) {
                if (menuRef.current.contains(ev.target as HTMLElement)) {

                    if (submenuRef?.current && submenuRef.current.contains(ev.target as HTMLElement)) {
                        console.log('keeping submenu open')
                    } else {
                        // Close submenu when clicking inside the menu
                        setSubmenu(null)
                        console.log('closing submenu')
                    }
                    ev.stopImmediatePropagation()
                } else {
                    // Close Nav on clicking somewhere outside the menu
                    setNavOpen(false)
                    console.log('closing nav')
                }
            }
        })
    }, [])


    useEffect(() => {
        console.log(`url changed to ${url}`)
        readHash()
    }, [url])

    useEffect(() => {
        if (restart) {
            console.log(`changing Lean version to ${project}`)
            restart(project)
        }
    }, [project])

    return (
        <div className={'app monaco-editor'}>
            <div className='nav'>
                <Logo className='logo'/>
                <div className='menu' ref={menuRef}>
                    {!config.verticalLayout && <>
                        {/* Buttons for desktop version */}
                        <LoadingMenu openSubmenu={openSubmenu}
                                     closeNav={closeNav} setUrl={setUrl}/>
                    </>
                    }
                    <span className={"nav-link nav-icon"} onClick={(ev) => {
                        setNavOpen(!navOpen)
                    }}>
            {navOpen ? <FontAwesomeIcon icon={faXmark}/> : <FontAwesomeIcon icon={faBars}/>}
          </span>
                    <div className={'dropdown' + (navOpen ? '' : ' hidden')}>
                        {config.verticalLayout && <>
                            {/* Buttons for mobile version */}
                            <LoadingMenu openSubmenu={openSubmenu}
                                         closeNav={closeNav} setUrl={setUrl}/>
                        </>}
                        <Settings closeNav={closeNav} theme={theme} setTheme={setTheme}
                                  project={project} setProject={setProject}/>
                        <span className="nav-link" onClick={restart}>
              <FontAwesomeIcon icon={faArrowRotateRight}/> Restart server
            </span>
                        <Tools/>
                        <span className="nav-link" onClick={save}>
              <FontAwesomeIcon icon={faDownload}/> Save file
            </span>
                        <PrivacyPolicy/>
                        <a className="nav-link" href="https://leanprover-community.github.io/" target="_blank">
                            <FontAwesomeIcon icon={faArrowUpRightFromSquare}/> Lean community
                        </a>
                        <a className="nav-link" href="https://leanprover.github.io/lean4/doc/" target="_blank">
                            <FontAwesomeIcon icon={faArrowUpRightFromSquare}/> Lean documentation
                        </a>
                        <a className="nav-link" href="https://github.com/hhu-adam/lean4web" target="_blank">
                            <FontAwesomeIcon icon={faArrowUpRightFromSquare}/> GitHub
                        </a>
                        <div className="submenu" ref={submenuRef}>
                            {submenu && submenu}
                        </div>
                    </div>
                </div>
            </div>
            <Suspense fallback={<div className="loading-ring"></div>}>
                <Editor setRestart={setRestart} setContent={setContent}
                        value={content} onDidChangeContent={onDidChangeContent} theme={theme} project={project}/>
            </Suspense>
        </div>
    )
}

export default App
