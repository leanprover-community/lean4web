declare module 'monaco-vim' {
  import type * as monaco from 'monaco-editor'
  export interface VimModeInstance {
    dispose(): void
  }
  export function initVimMode(
    editor: monaco.editor.IStandaloneCodeEditor,
    statusBarNode?: HTMLElement | null,
  ): VimModeInstance
}
