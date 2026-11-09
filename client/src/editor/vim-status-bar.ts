import { StatusBar, StatusBarInputOptions } from 'monaco-vim'

export { initVimMode } from 'monaco-vim'

const kbEventTocmKeyName: Record<string, string> = {
  "Escape": "Esc",
  "ArrowUp": "Up",
  "ArrowDown": "Down",
  "ArrowLeft": "Left",
  "ArrowRight": "Right",
  "Control": "Ctrl",
   " ": "Space"
}

/**
 * Map a native KeyboardEvent from the status bar's <input> to the
 * CodeMirror-style key name that monaco-vim's prompt handlers expect
 * (e.g. "Esc", "Up", "Y", "Ctrl-C").
 *
 * monaco-vim's own `keyName` implementation is written for Monaco's
 * IKeyboardEvent and falls back to `e.key` verbatim for native events, so the
 * handlers for the `:s///c` confirm prompt (which match "Y"/"N"/"A"/"Q"/"L")
 * and the search/ex history (which match "Up"/"Down") never fire.
 */
function cmKeyName(e: KeyboardEvent): string {
  let key = e.key
  if (key in kbEventTocmKeyName) {
    key = kbEventTocmKeyName[key]
  } else if (key.length === 1) {
    key = key.toUpperCase();
  }
  // Same prefix order as monaco-vim's `monacoToCmKey`
  if (e.altKey && key !== 'Alt') key = `Alt-${key}`
  if (e.ctrlKey && key !== 'Ctrl') key = `Ctrl-${key}`
  if (e.metaKey && key !== 'Meta') key = `Meta-${key}`
  if (e.shiftKey && key !== 'Shift') key = `Shift-${key}`
  return key
}

/**
 * Event facade handed to monaco-vim's prompt handlers: `keyName` returns the
 * precomputed name for it, and `e_stop`/history navigation still reach the
 * real event through the delegating methods and `target`.
 */
function toCmEvent(e: KeyboardEvent): KeyboardEvent {
  return {
    key: cmKeyName(e),
    keyCode: 0,
    altKey: false,
    ctrlKey: false,
    metaKey: false,
    shiftKey: false,
    target: e.target,
    preventDefault: () => e.preventDefault(),
    stopPropagation: () => e.stopPropagation(),
  } as unknown as KeyboardEvent
}

/**
 * StatusBar that fixes key handling in the vim prompts (`:` command line,
 * `/` search, and the `:s///c` confirm prompt). Without this, answering the
 * confirm prompt does nothing and it cannot even be closed with Escape.
 */
export class VimStatusBar extends StatusBar {
  setSec(
    text: Node | string | null | undefined,
    callback?: (value: string) => void,
    options?: StatusBarInputOptions,
  ) {
    if (options) {
      const { onKeyDown, onKeyUp } = options
      options = {
        ...options,
        onKeyDown:
          onKeyDown && ((e, value, close) => onKeyDown(toCmEvent(e), value, close)),
        onKeyUp: onKeyUp && ((e, value, close) => onKeyUp(toCmEvent(e), value, close)),
      }
    }
    return super.setSec(text, callback, options)
  }
}
