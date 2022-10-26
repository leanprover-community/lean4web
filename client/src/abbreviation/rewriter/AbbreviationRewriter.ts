// import { Range as LineColRange } from 'vscode';
// import { commands, Disposable, TextEditor, window, workspace, Selection, OutputChannel, TextDocument } from 'vscode';
import { assert } from '../../utils/assert';
import { AbbreviationProvider } from '../AbbreviationProvider';
import { config } from '../config';
import { Range } from './Range';
import { TrackedAbbreviation } from './TrackedAbbreviation';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import {IRange, Range as MonacoRange} from 'monaco-editor'

/**
 * Tracks abbreviations in a given text editor and replaces them when dynamically.
 */
export class AbbreviationRewriter {
	// private readonly disposables = new Array<Disposable>();
	// /**
	//  * All tracked abbreviations are disjoint.
	//  */
	private readonly trackedAbbreviations = new Set<TrackedAbbreviation>();
	// private readonly decorationType = window.createTextEditorDecorationType({
	// 	textDecoration: 'underline',
	// });

	private dontTrackNewAbbr = false;
	private decosIds: string[] = [];
	private isActiveContextKey: monaco.editor.IContextKey<boolean>;
	// private stderrOutput: OutputChannel;
	// private firstOutput = true;

	constructor(
		private readonly abbreviationProvider: AbbreviationProvider,
		private readonly model: monaco.editor.ITextModel,
		private readonly editor: monaco.editor.IStandaloneCodeEditor
	) {
		model.onDidChangeContent((e: monaco.editor.IModelContentChangedEvent) => {
			const changes = e.changes.slice(0);
			// // We need to process the changes at the bottom first.
			// // Otherwise, changes at the top will move spans at the bottom down.
			changes.sort((c1, c2) => c2.rangeOffset - c1.rangeOffset);

			for (const c of changes) {
				const range = new Range(c.rangeOffset, c.rangeLength);
				this.processChange(range, c.text);
			}

			this.updateState();

			// // Replace any tracked abbreviation that is either finished or unique.
			void this.forceReplace(
				[...this.trackedAbbreviations].filter(
					(abbr) =>
						abbr.finished ||
						(config.eagerReplacementEnabled &&
							abbr.isAbbreviationUniqueAndComplete)
				)
			);
		})


		editor.onDidChangeCursorSelection((e: monaco.editor.ICursorSelectionChangedEvent) => {
			// Replace any tracked abbreviation that lost selection.
			void this.forceReplace(
				[...this.trackedAbbreviations].filter(
					(abbr) =>
						![...e.secondarySelections, e.selection].some((s) =>
							abbr.range.containsRange(
								fromVsCodeRange(
									s,
									this.model
								).withLength(0)
							)
						)
				)
			);
		})

		this.isActiveContextKey = this.editor.createContextKey('lean4.input.isActive', false);

		monaco.editor.addEditorAction({
			id: 'lean4.input.convert',
			label: 'Convert abbreviation',
			precondition: "editorTextFocus && editorLangId == lean4 && lean4.input.isActive",
			keybindings: [monaco.KeyCode.Tab],
			run: async () => this.forceReplace([...this.trackedAbbreviations])
		})
	}

	private async forceReplace(
		abbreviations: TrackedAbbreviation[]
	): Promise<void> {
		if (abbreviations.length === 0) {
			return;
		}
		for (const a of abbreviations) {
			this.trackedAbbreviations.delete(a);
		}

		// Wait for VS Code to trigger `onDidChangeTextEditorSelection`
		await waitForNextTick();

		const cursorVar = '$CURSOR';
		const replacements = new Array<{
			range: Range;
			newText: string;
			transformOffsetInRange: (offset: number) => number;
		}>();
		for (const abbr of abbreviations) {
			const symbol = abbr.matchingSymbol;
			if (symbol) {
				const newText = symbol.replace(cursorVar, '');
				let cursorOffset = symbol.indexOf(cursorVar);
				if (cursorOffset === -1) {
					// position the cursor after the inserted symbol
					cursorOffset = newText.length;
				}
				replacements.push({
					range: abbr.range,
					newText,
					transformOffsetInRange: (offset) => cursorOffset,
				});
			}
		}
		// Process replacements with highest offset first
		replacements.sort((a, b) => b.range.offset - a.range.offset);

		// We cannot rely on VS Code to update the selections -
		// it becomes janky if symbols are inserted that are longer
		// than their abbreviation. It also does not really work for \[[]].
		const newSelections = this.editor.getSelections()
			.map((s) => ({range: fromVsCodeRange(s, this.model), dir: s.getDirection()}))
			.map(({range: s, dir}) => {
				// Apply the replacement of abbreviations to the selections.
				let newSel = s;
				for (const r of replacements) {
					if (
						r.range.isBefore(newSel) &&
						!r.range.containsRange(newSel)
					) {
						// don't do this on ` \abbr| `
						newSel = newSel.move(r.newText.length - r.range.length);
					} else if (
						!r.range.isAfter(newSel) ||
						r.range.containsRange(newSel)
					) {
						// do this on ` \abbr| ` or ` \ab|br `
						// newSel and r.range intersect
						const offset = newSel.offset - r.range.offset;
						const newOffset = r.transformOffsetInRange(offset);
						newSel = newSel.move(newOffset - offset);
					}
				}
				return {range: newSel, dir};
			});

		// We don't want replaced symbols (e.g. "\") to trigger abbreviations.
		this.dontTrackNewAbbr = true;
		let ok = false;
		try {
			await this.model.applyEdits(replacements.map((r) => {
				return {
					range: toVsCodeRange(r.range, this.model),
					text:	r.newText
				}
			}));
			ok = true
		} catch (e) {
			throw Error('Error: while replacing abbreviation: ' + e);
		}
		this.dontTrackNewAbbr = false;

		if (ok) {
			this.editor.setSelections(newSelections.map(({range: s, dir}) => {
				const vr = toVsCodeRange(s, this.model);
				return monaco.Selection.fromRange(vr, dir);
			}));

			// this.abbreviationProvider.onAbbreviationsCompleted(this.textEditor);
		}
		else {
			// Our edit did not succeed, do not update the selections.
			// This can happen if `waitForNextTick` waits too long.
			throw Error('Error: Unable to replace abbreviation');
		}

		this.updateState();
	}

	private updateState() {
		this.decosIds = this.model.deltaDecorations(this.decosIds,
		  [...this.trackedAbbreviations].map<monaco.editor.IModelDeltaDecoration>((a: TrackedAbbreviation) => {
				return {
					range: toVsCodeRange(a.range, this.model),
					options: {
						inlineClassName: 'abbreviation'
					}
		}}))

		void this.setInputActive(this.trackedAbbreviations.size > 0);
	}

	private async setInputActive(isActive: boolean) {
		this.isActiveContextKey.set(isActive);
	}

	private processChange(
		range: Range,
		text: string
	): { affectedAbbr: TrackedAbbreviation | undefined } {
		let affectedAbbr: TrackedAbbreviation | undefined;
		for (const abbr of [...this.trackedAbbreviations]) {
			const { isAffected, shouldStopTracking } = abbr.processChange(
				range,
				text
			);
			if (isAffected) {
				// At most one abbreviation should be affected
				assert(() => !affectedAbbr);
				affectedAbbr = abbr;
			}
			if (shouldStopTracking) {
				this.trackedAbbreviations.delete(abbr);
			}
		}

		if (
			text === config.abbreviationCharacter &&
			!affectedAbbr &&
			!this.dontTrackNewAbbr
		) {
			const abbr = new TrackedAbbreviation(
				new Range(range.offset + 1, 0),
				'',
				this.abbreviationProvider
			);
			this.trackedAbbreviations.add(abbr);
		}
		return { affectedAbbr };
	}
}

function fromVsCodeRange(range: IRange, model: monaco.editor.ITextModel): Range {
	const start = model.getOffsetAt(MonacoRange.getStartPosition(range));
	const end = model.getOffsetAt(MonacoRange.getEndPosition(range));
	return new Range(start, end - start);
}

function toVsCodeRange(range: Range, model: monaco.editor.ITextModel): monaco.Range {
	const start = model.getPositionAt(range.offset);
	const end = model.getPositionAt(range.offsetEnd + 1);
	return MonacoRange.fromPositions(start, end);
}

function waitForNextTick(): Promise<void> {
	return new Promise((res) => setTimeout(res, 0));
}
