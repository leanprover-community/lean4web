declare module 'monaco-vim' {
  import type * as monaco from 'monaco-editor'
  export interface VimModeInstance {
    dispose(): void
  }
  export interface StatusBarInputOptions {
    selectValueOnOpen?: boolean
    value?: string
    onKeyUp?: (event: KeyboardEvent, value: string, close: () => void) => void
    onKeyDown?: (
      event: KeyboardEvent,
      value: string,
      close: () => void,
    ) => boolean | void
    onKeyInput?: (event: InputEvent, value: string, close: () => void) => void
    onBlur?: (event: FocusEvent, close: () => void) => void
    closeOnBlur?: boolean
    closeOnEnter?: boolean
  }
  export class StatusBar {
    constructor(
      node: HTMLElement,
      editor: monaco.editor.IStandaloneCodeEditor | null,
      sanitizer?: ((node: Node) => Node) | null,
    )
    setMode(ev: { mode: string; subMode?: string }): void
    setSec(
      text: Node | string | null | undefined,
      callback?: (value: string) => void,
      options?: StatusBarInputOptions,
    ): (() => void) | undefined
    toggleVisibility(toggle: boolean): void
    closeInput: () => void
    clear: () => void
  }
  export function initVimMode(
    editor: monaco.editor.IStandaloneCodeEditor,
    statusBarNode?: HTMLElement | null,
    StatusBarClass?: typeof StatusBar,
    sanitizer?: ((node: Node) => Node) | null,
  ): VimModeInstance
}
