import {faUpload} from '@fortawesome/free-solid-svg-icons';
import {FontAwesomeIcon} from '@fortawesome/react-fontawesome';
import * as React from 'react'
import ExpandMoreIcon from '@mui/icons-material/ExpandMore';
import ChevronRightIcon from '@mui/icons-material/ChevronRight';
import {TreeView} from '@mui/x-tree-view/TreeView';
import {TreeItem} from '@mui/x-tree-view/TreeItem';
import {useEffect} from 'react';
import {LoadUrl, LoadZulipMessage} from './LoadUrl';

const LoadingMenu: ({setContent, openSubmenu, closeNav, setUrl}: {
    openSubmenu: any;
    closeNav: any;
    setUrl: any;
}) => void = ({openSubmenu, closeNav, setUrl}) => {
    const [fileTree, setFileTree] = React.useState(null)

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

    return <span className="nav-link" onClick={(ev) => openSubmenu(ev, submenu)}>
    <FontAwesomeIcon icon={faUpload}/> Open File from Repo
  </span>
}

export default LoadingMenu
