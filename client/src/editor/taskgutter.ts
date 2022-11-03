/* This file is based on `vscode-lean4/src/taskgutter.ts` */

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { LeanFileProgressKind, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api';
import { LeanClient } from './leanclient';

class LeanFileTaskGutter {
    private timeout?: NodeJS.Timeout
    private decoIds: string[] = []

    constructor(private editor: monaco.editor.IStandaloneCodeEditor, private decorations: Map<LeanFileProgressKind, monaco.editor.IModelDecorationOptions>, private processed: LeanFileProgressProcessingInfo[]) {
        this.schedule(100)
    }

    setProcessed(processed: LeanFileProgressProcessingInfo[]) {
        if (processed === this.processed) return;
        const oldProcessed = this.processed;
        this.processed = processed;
        if (processed === undefined) {
            this.processed = []
            this.clearTimeout();
            this.updateDecos();
        } else if (this.timeout === undefined) {
            this.schedule(oldProcessed === undefined ? 500 : 20)
        }
    }

    private schedule(ms: number) {
        this.timeout = setTimeout(() => {
            this.timeout = undefined
            this.updateDecos()
        }, ms)
    }

    private clearTimeout() {
        if (this.timeout !== undefined) {
            clearTimeout(this.timeout)
            this.timeout = undefined;
        }
    }

    private updateDecos() {
      this.decoIds = this.editor.getModel().deltaDecorations(this.decoIds,
        this.processed
          .map(info => ({
            options: this.decorations.get(info.kind === undefined ? LeanFileProgressKind.Processing : info.kind),
            range : new monaco.Range(info.range.start.line, 0, info.range.end.line, 0)
          }))
      )
    }

    dispose() {
        this.clearTimeout();
    }
}

export class LeanTaskGutter {
    private decorations: Map<LeanFileProgressKind, monaco.editor.IModelDecorationOptions> =
      new Map<LeanFileProgressKind, monaco.editor.IModelDecorationOptions>();
    private status: { [uri: string]: LeanFileProgressProcessingInfo[] } = {};
    private gutters: { [uri: string]: LeanFileTaskGutter | undefined } = {};
    private subscriptions: any[] = [];

    constructor(private client: LeanClient, private editor: monaco.editor.IStandaloneCodeEditor) {
        this.decorations.set(LeanFileProgressKind.Processing,
            {
                overviewRuler: {
                  position: monaco.editor.OverviewRulerLane.Left,
                  color: 'rgba(255, 165, 0, 0.5)',
                },
                glyphMarginClassName: 'processing',
                hoverMessage: {value: 'busily processing...'}
            })
        this.decorations.set(LeanFileProgressKind.FatalError,
            {
                overviewRuler: {
                  position: monaco.editor.OverviewRulerLane.Left,
                  color: 'rgba(255, 0, 0, 0.5)',
                },
                glyphMarginClassName: 'glyph-margin-error',
                hoverMessage: {value: 'processing stopped'}
            },
        )

        this.subscriptions.push(
            client.progressChanged(([uri, processing]) => {
                this.status[uri.toString()] = processing
                this.updateDecos()
            }));
    }

    private updateDecos() {
        const uris: { [uri: string]: boolean } = {}
        // for (const editor of window.visibleTextEditors) {
            const uri = this.editor.getModel().uri.toString();
            uris[uri] = true
            const processed = uri in this.status ? this.status[uri] : []
            if (this.gutters[uri]) {
                const gutter = this.gutters[uri];
                if (gutter) gutter.setProcessed(processed)
            } else {
                this.gutters[uri] = new LeanFileTaskGutter(this.editor, this.decorations, processed)
            }
        // }
        for (const uri of Object.getOwnPropertyNames(this.gutters)) {
            if (!uris[uri]) {
                this.gutters[uri]?.dispose();
                this.gutters[uri] = undefined;
                // TODO: also clear this.status for this uri ?
            }
        }
    }

    // dispose(): void {
    //     for (const [decoration, _message] of this.decorations.values()) { decoration.dispose() }
    //     for (const s of this.subscriptions) { s.dispose(); }
    // }
}
