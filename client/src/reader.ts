import { WebSocketMessageReader } from 'vscode-ws-jsonrpc';

export class DisposingWebSocketMessageReader extends WebSocketMessageReader {
    dispose() {
      super.dispose();
      this.socket.dispose();
    }
}
