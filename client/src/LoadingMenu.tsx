import {faCodeCommit, faFolder, faUpload, faUser} from '@fortawesome/free-solid-svg-icons';
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome';
import * as React from 'react'
import ExpandMoreIcon from '@mui/icons-material/ExpandMore';
import ChevronRightIcon from '@mui/icons-material/ChevronRight';
import {TreeView} from '@mui/x-tree-view/TreeView';
import {TreeItem} from '@mui/x-tree-view/TreeItem';
import {useEffect} from 'react';
//import {LoadUrl, LoadZulipMessage} from './LoadUrl';

import {AuthContext} from "./App";

const LoginButton = ({closeNav}) => {
    const client_id = "Iv1.c5ca1b845a9814d5"
    const redirect_uri = "http://localhost:3000/login"
    const login = () => {
        window.location.href = `https://github.com/login/oauth/authorize?scope=user&client_id=${client_id}&redirect_uri=${redirect_uri}`
    }
    return <span className="nav-link" onClick={login}>
        <FontAwesomeIcon icon={faUser}/> Login
        </span>
}

const UserBadge = ({user}) => {
    return <div style={{display: "flex", alignItems: "center", flexDirection: "row", marginRight: "10px",paddingTop: "0rem", paddingBottom: "0rem"}} className="nav-link">
        <img src={user.avatar_url} alt="None" width="30" height="30"/>
        <span style={{marginLeft: "5px"}} >{user.login}</span>
    </div>
}

const CommitButton = ({dispatch}) => {
    // a simple button to commit the current file to the repo
    return <span className="nav-link" onClick={dispatch}>
        <FontAwesomeIcon icon={faCodeCommit}/> Commit File
        </span>
}

const GreyCommitButton = () => {
    return <span className="nav-link" style={{color: "grey"}}>
        <FontAwesomeIcon icon={faCodeCommit}/> Commit File
        </span>
}

const LoadingMenu: ({setContent, openSubmenu, closeNav, setUrl}: {
    openSubmenu: any;
    closeNav: any;
    setUrl: any;
}) => void = ({openSubmenu, closeNav, setUrl}) => {
    const [fileTree, setFileTree] = React.useState(null)
    // @ts-ignore
    const {state, dispatch} = React.useContext(AuthContext)

    useEffect(() => {
        const root_path = window.location.origin + "/project"

        // fetch project/file_structure.json
        let file_structure;

        fetch(root_path + "/file_structure.json")
            .then(response => response.json())
            .then(data => {
                file_structure = data
                console.log("File structure", file_structure)
                setFileTree(generate_file_tree(file_structure, "."))
            })


        const onclick = (file) => {
            return () => {
                window.location.href = window.location.origin + "#project=banach-tarski&file=" + file
                setUrl(window.location.href)
                window.location.reload()
            }
        }

        const generate_file_tree = (file_structure, parent) => {
            let fileTree = []
            for (var key in file_structure) {
                if (file_structure[key] == null) {
                    console.log("file: ", key)
                    fileTree.push(<TreeItem
                        nodeId={key} label={key} onClick={onclick(parent + "%2F" + key)}/>)
                } else {
                    console.log("folder: ", key)
                    fileTree.push(<TreeItem nodeId={key}
                                            label={key}>{generate_file_tree(file_structure[key], parent + "%2F" + key)}</TreeItem>)
                }
            }
            return fileTree
        }
    }, []);


    const submenu = <TreeView
        // shift the tree to the left
        aria-label="file system navigator"
        defaultCollapseIcon={<ExpandMoreIcon/>}
        defaultExpandIcon={<ChevronRightIcon/>}
        multiSelect>{fileTree}
    </TreeView>
    /*<>
    <label htmlFor="file-upload" className="nav-link" >
    <FontAwesomeIcon icon={faUpload} /> Load file from disk
    </label>
    <LoadUrl loadFromUrl={loadFromUrl} closeNav={closeNav} />
    <LoadZulipMessage setContent={setContent} closeNav={closeNav} />
    <input id="file-upload" type="file" onChange={loadFileFromDisk} />
    </>*/
    const press_commit_button = () => {
        dispatch({type: "COMMIT_NOW"})
    }

    return <div style={{display: "flex", flexDirection: "row"}}>
        {(state.isLoggedIn && state.committing)  ? <GreyCommitButton/> : null}
        {(state.isLoggedIn && !state.committing) ? <CommitButton dispatch={press_commit_button}/> : null}

        {(!state.isLoggedIn) ? <LoginButton closeNav={closeNav}/> : <UserBadge user={state.user}/>}
        <span className="nav-link" onClick={(ev) => openSubmenu(ev, submenu)}>
            <FontAwesomeIcon icon={faFolder}/> Open File from Repo
            </span>
    </div>
}

export default LoadingMenu
