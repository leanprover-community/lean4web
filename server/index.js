const WebSocket = require("ws");
const express = require("express");
const path = require("path")
const { spawn } = require('child_process');

const app = express()

const PORT = process.env.PORT ?? 8080

const server = app
  .use(express.static(path.join(__dirname, '../client/dist/')))
  .listen(PORT, () => console.log(`Listening on ${PORT}`))

const wss = new WebSocket.Server({ server })

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

let cmd, cmdArgs;
if (isDevelopment) {
    cmd = "lean";
    cmdArgs = ["--server"];
} else{
    cmd = "docker";
    cmdArgs = ["run",
     "--runtime=runsc",
     "--network=none", "--rm", "-i", "elan:latest", "\"lean --server\""];
}
const cwd = '.'

class ClientConnection {
  header = ''
  content = ''
  contentLength = 0
  headerMode = true
  ws = null
  lean = null

  re = /Content-Length: (\d+)\r\n/i

  constructor (ws) {
    console.log('Socket opened.')
    this.ws = ws
    ws.on('message', (msg) => {
      console.log(`[client] ${msg}`)
      this.send(JSON.parse(msg.toString('utf8')))
    })

    ws.on('close', () => {
      this.lean?.kill()
      console.log('Socket closed.')
    })

    const lean = spawn(cmd, cmdArgs, { cwd })
    lean.stdout.on('readable', () => {
      this.read()
    })
    lean.stderr?.on('data', (data) => {
      console.error('stderr: ')
      console.error(data.toString('utf8'))
    })
    this.lean = lean
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
            console.log(`[server] ${this.content}`)
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
}

const clientConnections = []

wss.on('connection', function (ws) { // what should a websocket do on connection
  clientConnections.push(new ClientConnection(ws))
})
