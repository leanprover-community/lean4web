const WebSocket = require("ws");
const {spawn} = require('child_process');
const os = require('os');
const anonymize = require('ip-anonymize')
const fetch = (...args) => import('node-fetch').then(({default: fetch}) => fetch(...args));


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

    authenticationToken = null
    authenticated = false
    user = null

    constructor(ws, useBubblewrap, project, fileName, loginCode) {
        this.ws = ws

        this.loginCode = loginCode

        this.useBubblewrap = useBubblewrap
        this.fileName = fileName
        this.absolutePath = __dirname + `/../Projects/` + project + "/" + fileName
        this.file = null

        this.updateCount = 0
        this.updateThreshold = 10
        this.num_sent = 0

        if (project === "banach-tarski") {
            this.init_banach_tarski()
            console.log("...project initialized: " + project)
        } else {
            console.log("...project not banach tarski: " + project)
        }
        this.init_file()
        this.startProcess(project)

        ws.on('message', (msg) => {
            //console.log(`[client] ${msg}`)
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
                    if (this.updateCount > 0) {

                        this.commit_banach_tarski(this.fileName)
                    }
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

    async authenticate(loginCode) {
        const data = new FormData();
        const client_id = "Iv1.c5ca1b845a9814d5"
        const redirect_uri = "http://localhost:3000/login"
        const client_secret = "2d5d60d01fd246858e18d9dfb4b08258460e8350"

        data.append("client_id", client_id);
        data.append("client_secret", client_secret);
        data.append("code", loginCode);
        data.append("redirect_uri", redirect_uri);

        const response = fetch(`https://github.com/login/oauth/access_token`, {
            method: "POST",
            body: data,
        })
            .then((response) => response.text())
            .then((paramsString) => {
                let params = new URLSearchParams(paramsString);

                this.access_token = params.get("access_token");

                console.log("fetching, access_token", this.access_token);

                // Request to return data of a user that has been authenticated
                return fetch(`https://api.github.com/user`, {
                    headers: {
                        Authorization: `token ${this.access_token}`,
                    },
                });
            })
            .then((response) => response.json())
            .then((response) => {
                this.user = response;
                console.log("Ready state: ", this.ws.readyState)
                this.ws?.send(JSON.stringify({method: "$/authenticated", params: {information: response},"jsonrpc":"2.0"}))
                console.log("sent: ", JSON.stringify({method: "$/authenticated", params: {information: response},"jsonrpc":"2.0"}))
            })

    }


    read() {
        if (this.headerMode) {
            while (true) {
                const chr = this.lean?.stdout?.read(1)
                if (chr === null) {
                    break
                }
                this.header += (chr.toString('ascii'))
                if (this.header.endsWith('\r\n\r\n')) {
                    const found = this.header.match(this.re)
                    if (found == null) {
                        throw Error(`Invalid header: ${this.header}`)
                    }
                    this.contentLength = parseInt(found[1])
                    this.content = ''
                    this.headerMode = false
                    this.read()
                }
            }
        } else {
            while (true) {
                const str = this.lean?.stdout?.read(Math.min(this.lean.stdout.readableLength, this.contentLength))
                if (str === null) {
                    break
                }
                this.contentLength -= str.length
                this.content += (str.toString('utf8'))
                if (this.contentLength <= 0) {
                    if (this.ws?.readyState === WebSocket.OPEN) { // check if client is ready
                        console.log(`[server] (${this.num_sent} ${this.content}`)
                        this.ws?.send(this.content)
                        this.num_sent += 1
                    }
                    this.headerMode = true
                    this.header = ''
                    this.read()
                }
            }
        }
    }

    init_banach_tarski() {
        // run the init_banch_tarski.sh script
        const {execSync} = require("child_process");
        const path = __dirname + `/../Projects`
        try {
            execSync(`./init_banach_tarski.sh`, {cwd: path, stdio: 'inherit'})
        } catch (e) {
            console.log("Error while initializing banach-tarski ", e)
        }
    }

    async commit_banach_tarski(filename) {
        // add the file to the git repository
        const {execSync} = require("child_process");
        const path = __dirname + `/../Projects/banach-tarski`
        await this.write_file_to_disk()
        // add commit and push the file
        // wait for each command to finish before executing the next by using await
        try {
            await execSync(`git add ${filename}`, {cwd: path, stdio: 'inherit'})
            console.log("Added file to git repository")
            await execSync(`git commit -m "Update ${filename}"`, {cwd: path, stdio: 'inherit'})
            console.log("Committed file to git repository")
            await execSync(`git push`, {cwd: path, stdio: 'inherit'})
            console.log("Pushed file to git repository")
        } catch (e) {
            console.log("Error while committing to git repository: ", e)
        }

    }

    get_char_pos(line, char) {
        // get the character position in the file
        const lines = this.file.split("\n")
        let pos = 0
        for (let i = 0; i < line; i++) {
            pos += lines[i].length + 1
        }
        pos += char
        return pos
    }

    init_file() {
        // TODO make async
        const fs = require('fs');
        const path = this.absolutePath
        console.log("...fileName: " + this.fileName)
        fs.readFile(path, 'utf8', (err, data) => {
            if (err) {
                console.error(err)
                return
            }
            //console.log("...Filedata: " + data)
            this.file = data
        })
        console.log("Read file")
    }

    async check_update(data) {
        // check if the data updates the file TODO make async
        // if this is the case, update the file on disk
        // print method
        console.log("...method: " + data["method"])
        if (data["method"] === "initialized") {
            console.log("...initialized, loginCode: ", this.loginCode)
            if (this.loginCode) {
                this.authenticate(this.loginCode)
            }
        }

        if (data["params"] !== undefined) {
            console.log("...information: " + data["params"]["information"])
            //if (this.user) {
            //    console.log("user: ", this.user)
            //}
        }
        if (data["method"] === "authenticate") {
            console.log("...authenticate", data["params"])
        }

        if (data["method"] === "textDocument/didChange") {
            let i = 0
            while (this.file === null) {
                // wait until the file is initialized
                console.log("Waiting for file to be initialized")
                i += 1
                if (i >= 100) {
                    console.error("File could not be initialized")
                    return
                }
            }
            // apply the change to the file
            for (let i = 0; i < data["params"]["contentChanges"].length; i++) {
                const change = data["params"]["contentChanges"][i]
                const range = change["range"]
                const text = change["text"]
                const start = range["start"]
                const end = range["end"]
                const startLine = start["line"]
                const startChar = start["character"]
                const endLine = end["line"]
                const endChar = end["character"]
                // apply the change to the file
                this.file = this.file.slice(0, this.get_char_pos(startLine, startChar)) + text + this.file.slice(this.get_char_pos(endLine, endChar), this.file.length)
                this.updateCount += 1
                if (this.updateCount >= this.updateThreshold) {
                    await this.write_file_to_disk()
                    this.updateCount = 1
                }
            }
        }
    }

    async write_file_to_disk() {
        // TODO make async
        const fs = require('fs');
        const path = this.absolutePath

        await fs.writeFileSync(path, this.file, (err) => {
            if (err) {
                console.error(err)
                return
            }
        })
        console.log("Wrote file to disk")
    }

    send(data) {
        this.check_update(data)
        const str = JSON.stringify(data) + '\r\n'
        const byteLength = Buffer.byteLength(str, 'utf-8')
        if (this.lean === null || this.lean.stdin === null) {
            throw Error('Lean not running yet.')
        }
        this.lean.stdin.cork()
        this.lean.stdin.write(`Content-Length: ${byteLength}\r\n\r\n`, 'ascii')
        this.lean.stdin.write(str, 'utf-8')
        this.lean.stdin.uncork()
    }

    startProcess(project) {
        let path = __dirname + `/../Projects/` + project

        console.log(`The path is ${path}`)

        let cmd, cmdArgs, cwd;
        if (this.useBubblewrap) {
            cmd = "./bubblewrap.sh";
            cmdArgs = [path];
            cwd = __dirname;
        } else {
            console.warn("Running without Bubblewrap container!")
            cmd = "lake";
            cmdArgs = ["serve", "--"];
            cwd = path
        }

        this.lean = spawn(cmd, cmdArgs, {cwd})
    }
}

const urlRegEx = /^\/websocket\/([\w.-]+\/)$/

class WebsocketServer {

    constructor(server, useBubblewrap) {
        this.wss = new WebSocket.Server({server})
        this.socketCounter = 0;

        this.wss.on('connection', (ws, req) => {
            console.log("...url: " + req.url)
            const reRes = req.url.split("/")
            console.log("...reRes: " + reRes)
            if (!reRes || reRes[1] !== "websocket") {
                console.error(`Connection refused because of invalid URL: ${req.url}`);
                return;
            }
            const project = reRes[2]

            const url = reRes[3] || null
            //let path = null
            let fileName = null
            if (url) {
                let urlParts = url.split("%2F")
                fileName = urlParts.join("/")
                console.log("...fileName: " + fileName)
                // check if the file exists
                const fs = require('fs');
                const path = __dirname + `/../Projects/` + project + "/" + fileName
                fs.access(path, fs.F_OK, (err) => {
                    if (err) {
                        console.error(err)
                        return
                    }
                    console.log("File exists")
                })
            } else {
                throw Error("No file name provided")
            }
            console.log("...url: " + url)

            console.log(`Open with project: ${project}`)

            const loginCodeParam = reRes[4];
            var loginCode = null;
            if (loginCodeParam) {
                loginCode = loginCodeParam.split("=")[1]
                console.log(`Login code: ${loginCode}`)
            }

            this.socketCounter += 1;
            const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
            console.log(`[${new Date()}] Socket opened - ${ip}`)
            this.logStats()

            new ClientConnection(ws, useBubblewrap, project, fileName, loginCode)
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
