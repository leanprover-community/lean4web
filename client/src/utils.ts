/* This file is based on `vscode-lean4/src/utils/converters.ts` */

/**
 * For LSP communication, we need a way to translate between LSP types and corresponding VSCode types.
 * By default this translation is provided as a bunch of methods on a `LanguageClient`, but this is
 * awkward to use in multi-client workspaces wherein we need to look up specific clients. In fact the
 * conversions are *not* stateful, so having them depend on the client is unnecessary. Instead, we
 * provide global converters here.
 *
 * Some of the conversions are patched to support extended Lean-specific structures.
 *
 * @module
 */


import { createConverter as createC2PConverter } from 'vscode-languageclient/lib/common/codeConverter'
import * as ls from 'vscode-languageserver-protocol'

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

export const c2pConverter = createC2PConverter(undefined)

export function toLanguageServerRange (range: monaco.Range): ls.Range {
  return {
    start: { line: range.startLineNumber - 1, character: range.startColumn - 1},
    end: { line: range.endLineNumber - 1, character: range.endColumn - 1}
  }
}

export function fromLanguageServerPosition (pos: ls.Position): monaco.Position {
  return new monaco.Position(
    pos.line + 1,
    pos.character + 1
  )
}

export function fromLanguageServerRange (range: ls.Range): monaco.Range {
  return new monaco.Range(
    range.start.line + 1,
    range.start.character + 1,
    range.end.line + 1,
    range.end.character + 1
  )
}
