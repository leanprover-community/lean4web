/* This file is based on `vscode-lean4/vscode-lean4/src/abbreviation/AbbreviationHoverProvider.ts` */

import { AbbreviationProvider } from './AbbreviationProvider';
import { config } from '../../config/config';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

/**
 * Adds hover behaviour for getting translations of unicode characters.
 * Eg: "Type ⊓ using \glb or \sqcap"
 */
export class AbbreviationHoverProvider implements monaco.languages.HoverProvider {
	constructor(
		private readonly abbreviations: AbbreviationProvider
	) {}

	provideHover(model: monaco.editor.ITextModel, pos: monaco.Position): monaco.languages.Hover | undefined {
		const context = model.getLineContent(pos.lineNumber).substring(pos.column-1);
		const symbolsAtCursor = this.abbreviations.findSymbolsIn(context);
		const allAbbrevs = symbolsAtCursor.map((symbol) => ({
			symbol,
			abbrevs: this.abbreviations.getAllAbbreviations(symbol),
		}));

		if (
			allAbbrevs.length === 0 ||
			allAbbrevs.every((a) => a.abbrevs.length === 0)
		) {
			return undefined;
		}

		const leader = config.abbreviationCharacter;

		const hoverMarkdown = allAbbrevs
			.map(
				({ symbol, abbrevs }) =>
					`Type ${symbol} using ${abbrevs
						.map((a) => '`' + leader + a + '`')
						.join(' or ')}`
			)
			.join('\n\n');

		const maxSymbolLength = Math.max(
			...allAbbrevs.map((a) => a.symbol.length)
		);
		const hoverRange = new monaco.Range(pos.lineNumber, pos.column-1, pos.lineNumber, pos.column-1 + maxSymbolLength);

		return {contents: [{value: hoverMarkdown}], range: hoverRange};
	}
}
