import { WebSocketServer } from 'ws';
import express from 'express'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as path from 'path'
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import nocache from 'nocache'
import anonymize from 'ip-anonymize'
import os from 'os'
import http from 'http'
import https from 'https'

let socketCounter = 0

function logStats() {
  console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`)
  console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const environment = process.env.NODE_ENV
const isGithubAction = process.env.GITHUB_ACTIONS
const isDevelopment = environment === 'development'

const crtFile = process.env.SSL_CRT_FILE
const keyFile = process.env.SSL_KEY_FILE

const app = express()

// `*` has the form `mathlib-demo/MathlibLatest/Logic.lean`
app.use('/api/examples/*', (req, res, next) => {
  const filename = req.params[0]
  req.url = filename
  // the nix setup has the files in ~/deploy/live
  express.static(path.join(os.homedir(), 'deploy', 'live'))(req, res, next)
})
// `*` is the project like `mathlib-demo`
app.use('/api/manifest/*', (req, res, next) => {
  const project = req.params[0]
  req.url = 'lake-manifest.json'
  // the nix setup has the files in ~/deploy/live
  express.static(path.join(os.homedir(), 'deploy', 'live', project))(req, res, next)
})
// `*` is the project like `mathlib-demo`
app.use('/api/toolchain/*', (req, res, next) => {
  const project = req.params[0]
  req.url = 'lean-toolchain'
  // the nix setup has the files in ~/deploy/live
  express.static(path.join(os.homedir(), 'deploy', 'live', project))(req, res, next)
})
// Using the client files
app.use(express.static(path.join(__dirname, '..', 'client', 'dist')))
app.use(nocache())

let server
if (crtFile && keyFile) {
  var privateKey  = fs.readFileSync(keyFile, 'utf8');
  var certificate = fs.readFileSync(crtFile, 'utf8');
  var credentials = {key: privateKey, cert: certificate};

  const PORT = process.env.PORT ?? 443
  server = https.createServer(credentials, app).listen(PORT,
    () => console.log(`HTTPS on port ${PORT}`));

  // redirect http to https
  express().get('*', function(req, res) {
    res.redirect('https://' + req.headers.host + req.url).listen(80);
  })
} else {
  const PORT = process.env.PORT ?? 8080
  server = app.listen(PORT,
    () => console.log(`HTTP on port ${PORT}`))
}

const wss = new WebSocketServer({ server })

// The path to the projects folder relative to the server
let projectsBasePath = path.join(__dirname, '..', 'Projects')

function startServerProcess(project) {
  let projectPath = path.join(projectsBasePath, project)

  let serverProcess
  if (isDevelopment) {
    if (!isGithubAction) {
      console.warn("Running without Bubblewrap container!")
    }
    serverProcess = cp.spawn("lake", ["serve", "--"], { cwd: projectPath })
  } else {
    // the nix setup runs the server in ~,
    // `bubblewrap.sh` is somewhere relative to the js source file
    // and the projects are in ~/deploy/live/<project>
    let cmd = path.join (__dirname, "bubblewrap.sh");
    let cmdArgs = [path.join("deploy","live",project)];
    console.info(`Running with Bubblewrap container: ${cmd} ${cmdArgs}.`)
    serverProcess = cp.spawn(cmd, cmdArgs, {})
  }

  // serverProcess.stdout.on('data', (data) => {
  //   console.log(`Lean Server: ${data}`);
  // });

  serverProcess.stderr.on('data', data =>
    console.error(`Lean Server: ${data}`)
  )

  serverProcess.on('error', error =>
    console.error(`Launching Lean Server failed: ${error}`)
  )

  serverProcess.on('close', (code) => {
    console.log(`lean server exited with code ${code}`);
  });

  return serverProcess
}

/** Transform client URI to valid file on the server */
function urisToFilenames(prefix, obj) {
  for (let key in obj) {
    if (obj.hasOwnProperty(key)) {
      if (key === 'uri') {
        obj[key] = obj[key].replace('file://', `file://${prefix}`)
      } else if (key === 'rootUri') {
        obj[key] = obj[key].replace('file://', `file://${prefix}`)
      } else if (key === 'rootPath') {
        obj[key] = path.join(prefix, obj[key])
      }
      if (typeof obj[key] === 'object' && obj[key] !== null) {
        urisToFilenames(prefix, obj[key]);
      }
    }
  }
  return obj;
}

/** Transform server file back into client URI */
function FilenamesToUri(prefix, obj) {
  for (let key in obj) {
    if (obj.hasOwnProperty(key)) {
      if (key === 'uri') {
        obj[key] = obj[key].replace(prefix, '')
      }
      if (typeof obj[key] === 'object' && obj[key] !== null) {
        FilenamesToUri(prefix, obj[key]);
      }
    }
  }
  return obj;
}

wss.addListener("connection", function(ws, req) {
  const urlRegEx = /^\/websocket\/([\w.-]+)$/
  const reRes = urlRegEx.exec(req.url)
  if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
  const project = reRes[1]

  const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
  const ps = startServerProcess(project)

  const socket = {
      onMessage: (cb) => { ws.on("message", cb) },
      onError: (cb) => { ws.on("error", cb) },
      onClose: (cb) => { ws.on("close", cb) },
      send: (data, cb) => { ws.send(data,cb) }
  }
  const reader = new rpc.WebSocketMessageReader(socket)
  const writer = new rpc.WebSocketMessageWriter(socket)
  const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
  const serverConnection = jsonrpcserver.createProcessStreamConnection(ps)
  socketConnection.forward(serverConnection, message => {
    const prefix = isDevelopment ? projectsBasePath : ""

    if (!message.method === 'textDocument/definition') {
      urisToFilenames(prefix, message)
    }

    if (isDevelopment && !isGithubAction) {
      console.log(`CLIENT: ${JSON.stringify(message)}`)
    }
    return message;
  })
  serverConnection.forward(socketConnection, message => {
    const prefix = isDevelopment ? projectsBasePath : ""
    FilenamesToUri(prefix, message)
    if (isDevelopment && !isGithubAction) {
      console.log(`SERVER: ${JSON.stringify(message)}`)
    }
    return message;
  });

  ws.on('close', () => {
    socketCounter -= 1
    if (!isGithubAction) {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      logStats()
    }
  })

  socketConnection.onClose(() => serverConnection.dispose())
  serverConnection.onClose(() => socketConnection.dispose())

  socketCounter += 1
  if (!isGithubAction) {
    console.log(`[${new Date()}] Socket opened - ${ip}`)
    logStats()
  }
})
