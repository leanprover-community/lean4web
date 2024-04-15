const WebSocket = require("ws");
const { spawn } = require('child_process');
const os = require('os');
const anonymize = require('ip-anonymize')
const path = require("path")

// TODO: Use server-side connection forwarding
// https://github.com/TypeFox/monaco-languageclient/tree/main/packages/vscode-ws-jsonrpc

class ClientConnection {
  header = ''
  content = ''
  contentLength = 0
  headerMode = true
  ws = null
  lean = null

  re = /Content-Length: (\d+)\r\n/i

  constructor (ws, useBubblewrap, project) {
    this.useBubblewrap = useBubblewrap

    this.startProcess(project)

    this.ws = ws
    ws.on('message', (msg) => {
      console.log(`[client] ${msg}`)
      this.send(JSON.parse(msg.toString('utf8')))
    })

    ws.on('close', () => {
      if (this.lean) {
        if (this.useBubblewrap) {
          // We need to shut down the Docker container. Simply killing the process does not cut it.
          console.log(this.lean.pid)
          this.lean?.kill()
        } else {
          // Simply kill the Lean process
          this.lean?.kill()
        }
      }
    })

    this.lean.stdout.on('readable', () => {
      this.read()
    })

    this.lean.stderr?.on('data', (data) => {
      console.error('stderr: ')
      console.error(data.toString('utf8'))
    })
  }

  read () {
    if (this.headerMode) {
      while (true) {
        const chr = this.lean?.stdout?.read(1)
        if (chr === null) { break }
        this.header += (chr.toString('ascii'))
        if (this.header.endsWith('\r\n\r\n')) {
          const found = this.header.match(this.re)
          if (found == null) { throw Error(`Invalid header: ${this.header}`) }
          this.contentLength = parseInt(found[1])
          this.content = ''
          this.headerMode = false
          this.read()
        }
      }
    } else {
      while (true) {
        const str =
          this.lean?.stdout?.read(Math.min(this.lean.stdout.readableLength, this.contentLength))
        if (str === null) { break }
        this.contentLength -= str.length
        this.content += (str.toString('utf8'))
        if (this.contentLength <= 0) {
          if (this.ws?.readyState === WebSocket.OPEN) { // check if client is ready
            // console.log(`[server] ${this.content}`)
            this.ws?.send(this.content)
          }
          this.headerMode = true
          this.header = ''
          this.read()
        }
      }
    }
  }

  send (data) {
    const str = JSON.stringify(data) + '\r\n'
    const byteLength = Buffer.byteLength(str, 'utf-8')
    if (this.lean === null || this.lean.stdin === null) { throw Error('Lean not running yet.') }
    this.lean.stdin.cork()
    this.lean.stdin.write(`Content-Length: ${byteLength}\r\n\r\n`, 'ascii')
    this.lean.stdin.write(str, 'utf-8')
    this.lean.stdin.uncork()
  }

  startProcess (project) {
    let path = __dirname + `/../Projects/` + project

    console.log(`The path is ${path}`)

    let cmd, cmdArgs, cwd;
    if (this.useBubblewrap) {
      cmd = path.join (__dirname, "bubblewrap.sh");
      cmdArgs = [path];
    } else{
      console.warn("Running without Bubblewrap container!")
      cmd = "lake";
      cmdArgs = ["serve", "--"];
    }

    this.lean = spawn(cmd, cmdArgs, {})
  }
}

const urlRegEx = /^\/websocket\/([\w.-]+)$/

class WebsocketServer {

  constructor(server, useBubblewrap) {
    this.wss = new WebSocket.Server({ server })
    this.socketCounter = 0;

    this.wss.on('connection', (ws, req) => {
      const reRes = urlRegEx.exec(req.url)
      if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
      const project = reRes[1]

      console.log(`Open with project: ${project}`)

      this.socketCounter += 1;
      const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
      console.log(`[${new Date()}] Socket opened - ${ip}`)
      this.logStats()

      new ClientConnection(ws, useBubblewrap, project)
      ws.on('close', () => {
        console.log(`[${new Date()}] Socket closed - ${ip}`)
        this.socketCounter -= 1;
      })
    })
  }

  logStats() {
    console.log(`[${new Date()}] Number of open sockets - ${this.socketCounter}`)
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)
  }
}

module.exports = WebsocketServer
