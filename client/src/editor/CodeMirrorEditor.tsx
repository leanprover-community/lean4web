import CodeMirror, { EditorView } from '@uiw/react-codemirror'
import { useAtom } from 'jotai'
import { codeAtom } from './code-atoms'
import { lightThemes } from '../settings/settings-types'
import { settingsAtom } from '../settings/settings-atoms'

/**
 * The Code-Mirror editor is used in mobile layout as it provides better mobile-integration. Unfortunately it has
 * no Lean-integration.
 */
export default function CodeMirrorEditor({
  setContent,
}: {
  setContent: (_code: string) => void
}) {
  const [code] = useAtom(codeAtom)
  const [settings] = useAtom(settingsAtom)

  return (
    <CodeMirror
      className="codeview plain"
      value={code}
      extensions={[EditorView.lineWrapping]}
      height="100%"
      maxHeight="100%"
      theme={lightThemes.includes(settings.theme) ? 'light' : 'dark'}
      onChange={setContent}
    />
  )
}
