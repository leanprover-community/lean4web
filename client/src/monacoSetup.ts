import { Registry } from 'monaco-textmate' // peer dependency
import { wireTmGrammars } from 'monaco-editor-textmate'
import * as leanSyntax from './syntaxes/lean.json'
import * as leanMarkdownSyntax from './syntaxes/lean-markdown.json'
import * as codeblockSyntax from './syntaxes/codeblock.json'
import languageConfig from '../vscode-lean4/vscode-lean4/language-configuration.json';
import { loadWASM } from 'onigasm'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { MonacoServices } from 'monaco-languageclient';
import { StandaloneServices } from 'vscode/services';
import getMessageServiceOverride from 'vscode/service-override/messages';
//@ts-ignore
import onigasmUrl from 'onigasm/lib/onigasm.wasm?url'
import * as lightPlusTheme from './css/lightPlus.json'

export function monacoSetup () {

  StandaloneServices.initialize({
    ...getMessageServiceOverride(document.body)
  });

  // install Monaco language client services
  MonacoServices.install();

  // map of monaco "language id's" to TextMate scopeNames
  const grammars = new Map()
  grammars.set('lean4', 'source.lean')

  // define one hard-coded theme as default
  monaco.editor.defineTheme('lightPlus', lightPlusTheme as any);

  // register Monaco languages
  monaco.languages.register({
    id: 'lean4',
    extensions: ['.lean']
  })

  let config: any = { ...languageConfig }
  const translateBrackets = (f) => f.map(
    pair => { return {'open': pair[0], 'close': pair[1]} }
  )
  config.autoClosingPairs = translateBrackets(config.autoClosingPairs)
  config.surroundingPairs = translateBrackets(config.surroundingPairs)
  monaco.languages.setLanguageConfiguration('lean4', config);

  const registry = new Registry({
    getGrammarDefinition: async (scopeName) => {
      if (scopeName === 'source.lean') {
        return {
            format: 'json',
            content: JSON.stringify(leanSyntax)
        }
      } else if (scopeName === 'source.lean.markdown') {
        return {
            format: 'json',
            content: JSON.stringify(leanMarkdownSyntax)
        }
      } else {
        return {
            format: 'json',
            content: JSON.stringify(codeblockSyntax)
        }
      }
    }
  });

  // Load onigasm
  (async () => {
    try {
      await loadWASM(onigasmUrl)
    } catch (err) {
      // Hot module replacement can cause us to run this code twice and that's ok.
      if (!(err as Error).message?.startsWith('Onigasm#init has been called')) {
        throw err
      }
    }
    wireTmGrammars(monaco, registry, grammars)
  })()
}
