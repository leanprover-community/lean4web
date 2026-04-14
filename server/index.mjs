import * as cp from "node:child_process";
import * as fs from "node:fs";
import https from "node:https";
import os from "node:os";
import * as path from "node:path";
import * as url from "node:url";

import express from "express";
import anonymize from "ip-anonymize";
import nocache from "nocache";
import * as rpc from "vscode-ws-jsonrpc";
import * as jsonrpcserver from "vscode-ws-jsonrpc/server";
import { WebSocketServer } from "ws";

let socketCounter = 0;

function logStats() {
  console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`);
  console.log(
    `[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`,
  );
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL(".", import.meta.url));

const environment = process.env.NODE_ENV;
const isGithubAction = process.env.GITHUB_ACTIONS;
const isDevelopment = environment === "development";
const NO_BWRAP = process.env.NO_BWRAP?.toLowerCase() === "true" ?? false;

const crtFile = process.env.SSL_CRT_FILE;
const keyFile = process.env.SSL_KEY_FILE;

const PROJECTS_BASE_PATH = path.join(
  __dirname,
  "..",
  process.env.PROJECTS_BASE_PATH ?? "Projects",
);

const app = express();

// our test setup waits until the server returns `200`
app.get("/health", (_req, res) => {
  res.status(200).send("Server is running");
});

// endpoint to list all available projects
app.use("/api/projects", async (req, res) => {
  try {
    const entries = await fs.promises.readdir(PROJECTS_BASE_PATH, {
      withFileTypes: true,
    });
    const projects = [];

    for (const entry of entries) {
      if (!entry.isDirectory()) continue;

      const projectDir = path.join(PROJECTS_BASE_PATH, entry.name);
      const configPath = path.join(projectDir, "leanweb-config.json");

      let config = null;
      try {
        const raw = await fs.promises.readFile(configPath, "utf-8");
        config = JSON.parse(raw);
      } catch (err) {
        console.debug(err);
        // File missing or invalid JSON — keep config as null
      }

      if (config) {
        projects.push({
          folder: entry.name,
          config: {
            name: String(config.name), // TODO: ensure this is not null
            hidden: Boolean(config.hidden) ?? false,
            default: Boolean(config.default) ?? false,
            examples: config.examples ?? [], // TODO: validate
          },
        });
      }
    }

    res.json(projects);
  } catch (err) {
    console.error(err);
    res.status(500).json({ error: "Failed to load projects" });
  }
});

// `*example` has the form `mathlib-demo/MathlibLatest/Logic.lean`
app.use("/api/example/:project/*example", (req, res, next) => {
  const pathComponents = req.params.example.filter((it) => it.length > 0);
  if (!(pathComponents[pathComponents.length - 1] ?? "").endsWith(".lean")) {
    res.status(400).json({ error: "Bad request" });
  } else {
    const filePath = path.join(req.params.project, ...pathComponents);
    req.url = filePath;
    express.static(PROJECTS_BASE_PATH)(req, res, next);
  }
});

// `:project` is the project like `mathlib-demo`
app.use("/api/manifest/:project", (req, res, next) => {
  const project = req.params.project;
  req.url = "lake-manifest.json";
  express.static(path.join(PROJECTS_BASE_PATH, project))(req, res, next);
});

// `:project` is the project like `mathlib-demo`
app.use("/api/toolchain/:project", (req, res, next) => {
  const project = req.params.project;
  req.url = "lean-toolchain";
  express.static(path.join(PROJECTS_BASE_PATH, project))(req, res, next);
});

// Using the client files
app.use(express.static(path.join(__dirname, "..", "client", "dist")));

app.use(nocache());

const hasBwrap = hasWorkingBwrap();
if (!hasBwrap) {
  if (isDevelopment) {
    if (!isGithubAction) {
      console.info("Bubblewrap is not available.");
    }
  } else {
    console.warn("Bubblewrap is not available!");
  }
}

let server;
if (crtFile && keyFile) {
  var privateKey = fs.readFileSync(keyFile, "utf8");
  var certificate = fs.readFileSync(crtFile, "utf8");
  var credentials = { key: privateKey, cert: certificate };

  const PORT = process.env.PORT ?? 443;
  server = https
    .createServer(credentials, app)
    .listen(PORT, () => console.log(`HTTPS on port ${PORT}`));

  // redirect http to https
  express().get("*", function (req, res) {
    res.redirect("https://" + req.headers.host + req.url).listen(80);
  });
} else {
  const PORT = process.env.PORT ?? 8080;
  server = app.listen(PORT, () => console.log(`HTTP on port ${PORT}`));
}

const wss = new WebSocketServer({ server });

function startServerProcess(project) {
  const PROJECT_PATH = path.join(PROJECTS_BASE_PATH, project);
  let serverProcess;
  if (isDevelopment) {
    serverProcess = cp.spawn("lake", ["serve", "--"], {
      cwd: PROJECT_PATH,
    });
  } else {
    if (hasWorkingBwrap()) {
      serverProcess = cp.spawn("./bubblewrap.sh", [PROJECT_PATH], {
        cwd: __dirname,
      });
    } else if (NO_BWRAP) {
      console.warn("Started process witouut bubblewrap!");
      serverProcess = cp.spawn("lake", ["serve", "--"], { cwd: PROJECT_PATH });
    } else {
      console.error(
        "Bubblewrap is not available! You can set `NO_BWRAP=true` to start the processes without container.",
      );
      return 300;
    }
  }

  // serverProcess.stdout.on('data', (data) => {
  //   console.log(`Lean Server: ${data}`);
  // });

  serverProcess.stderr.on("data", (data) =>
    console.error(`Lean Server: ${data}`),
  );

  serverProcess.on("error", (error) =>
    console.error(`Launching Lean Server failed: ${error}`),
  );

  serverProcess.on("close", (code) => {
    console.log(`lean server exited with code ${code}`);
  });

  return serverProcess;
}

/** Transform client URI to valid file on the server */
function urisToFilenames(prefix, obj) {
  for (let key in obj) {
    if (obj.hasOwnProperty(key)) {
      if (key === "uri") {
        obj[key] = obj[key].replace("file://", `file://${prefix}`);
      } else if (key === "rootUri") {
        obj[key] = obj[key].replace("file://", `file://${prefix}`);
      } else if (key === "rootPath") {
        obj[key] = path.join(prefix, obj[key]);
      }
      if (typeof obj[key] === "object" && obj[key] !== null) {
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
      if (key === "uri") {
        obj[key] = obj[key].replace(prefix, "");
      }
      if (typeof obj[key] === "object" && obj[key] !== null) {
        FilenamesToUri(prefix, obj[key]);
      }
    }
  }
  return obj;
}

const enableCollab = process.argv.includes('--collab=yes');
if (enableCollab) {
  console.log("COLLAB: Enabling signaling server for collaboration.");
}

const yjsTopics = new Map(); // roomName -> Set<Connection>

const sendYjs = (conn, message) => {
  if (conn.readyState !== 0 && conn.readyState !== 1) {
    conn.close();
  }
  try {
    conn.send(JSON.stringify(message));
  } catch (e) {
    conn.close();
  }
};

const setupYjsConnection = (conn, req) => {
  const ip = req ? (req.headers["x-forwarded-for"] || req.socket.remoteAddress) : "unknown";
  console.log(`COLLAB: New connection established from ${ip}`);
  const subscribedTopics = new Set();
  let closed = false;
  // Check if connection is still alive
  let pongReceived = true;
  const pingInterval = setInterval(() => {
    if (!pongReceived) {
      conn.close();
      clearInterval(pingInterval);
    } else {
      pongReceived = false;
      try {
        conn.ping();
      } catch (e) {
        conn.close();
      }
    }
  }, 30000);
  conn.on("pong", () => {
    pongReceived = true;
  });
  conn.on("close", () => {
    console.log(`COLLAB: Connection closed from ${ip}`);
    subscribedTopics.forEach((topicName) => {
      const subs = yjsTopics.get(topicName) || new Set();
      subs.delete(conn);
      if (subs.size === 0) {
        yjsTopics.delete(topicName);
      }
    });
    subscribedTopics.clear();
    closed = true;
  });
  conn.on("message", (message) => {
    if (typeof message === "string" || message instanceof Buffer) {
      try {
        message = JSON.parse(message);
      } catch (e) {
        return;
      }
    }
    if (message && message.type && !closed) {
      switch (message.type) {
        case "subscribe":
          (message.topics || []).forEach((topicName) => {
            if (typeof topicName === "string") {
              let topic = yjsTopics.get(topicName);
              if (!topic) {
                topic = new Set();
                yjsTopics.set(topicName, topic);
              }
              topic.add(conn);
              subscribedTopics.add(topicName);
              console.log(`COLLAB: Client subscribed to topic: ${topicName}`);
            }
          });
          break;
        case "unsubscribe":
          (message.topics || []).forEach((topicName) => {
            const subs = yjsTopics.get(topicName);
            if (subs) {
              subs.delete(conn);
              console.log(`COLLAB: Client unsubscribed from topic: ${topicName}`);
            }
          });
          break;
        case "publish":
          if (message.topic) {
            const receivers = yjsTopics.get(message.topic);
            console.log(`COLLAB: Client published to topic ${message.topic} (receivers: ${receivers ? receivers.size : 0})`);
            if (receivers) {
              message.clients = receivers.size;
              receivers.forEach((receiver) => sendYjs(receiver, message));
            }
          }
          break;
        case "ping":
          sendYjs(conn, { type: "pong" });
      }
    }
  });
};

wss.addListener("connection", async function (ws, req) {
  const urlRegEx = /^\/websocket\/([\w.-]+)$/;
  const reRes = urlRegEx.exec(req.url);
  if (!reRes) {
    if (enableCollab && (req.url === "/yjs-signaling" || req.url === "/yjs-signaling/")) {
      setupYjsConnection(ws, req);
      return;
    }
    console.error(`Connection refused because of invalid URL: ${req.url}`);
    return;
  }
  const project = reRes[1];

  if (!project.match(/^[a-zA-Z][a-zA-Z1-9.-_]*/)) {
    console.error(
      `Connection refused because of invalid project name: ${project}`,
    );
    return;
  }

  const ip = anonymize(
    req.headers["x-forwarded-for"] || req.socket.remoteAddress,
  );
  const ps = await startServerProcess(project);

  if (ps === null) {
    console.error(
      `Connection refused because of nonexistent project directory: ${project}`,
    );
    return;
  }

  const socket = {
    onMessage: (cb) => {
      ws.on("message", cb);
    },
    onError: (cb) => {
      ws.on("error", cb);
    },
    onClose: (cb) => {
      ws.on("close", cb);
    },
    send: (data, cb) => {
      ws.send(data, cb);
    },
  };
  const reader = new rpc.WebSocketMessageReader(socket);
  const writer = new rpc.WebSocketMessageWriter(socket);
  const socketConnection = jsonrpcserver.createConnection(reader, writer, () =>
    ws.close(),
  );
  const serverConnection = jsonrpcserver.createProcessStreamConnection(ps);
  socketConnection.forward(serverConnection, (message) => {
    const prefix = isDevelopment ? PROJECTS_BASE_PATH : "";

    if (!message.method === "textDocument/definition") {
      urisToFilenames(prefix, message);
    }

    if (isDevelopment && !isGithubAction) {
      console.log(`CLIENT: ${JSON.stringify(message)}`);
    }
    return message;
  });
  serverConnection.forward(socketConnection, (message) => {
    const prefix = isDevelopment ? PROJECTS_BASE_PATH : "";
    FilenamesToUri(prefix, message);
    if (isDevelopment && !isGithubAction) {
      console.log(`SERVER: ${JSON.stringify(message)}`);
    }
    return message;
  });

  ws.on("close", () => {
    socketCounter -= 1;
    if (!isGithubAction) {
      console.log(`[${new Date()}] Socket closed - ${ip}`);
      logStats();
    }
  });

  socketConnection.onClose(() => serverConnection.dispose());
  serverConnection.onClose(() => socketConnection.dispose());

  socketCounter += 1;
  if (!isGithubAction) {
    console.log(`[${new Date()}] Socket opened - ${ip}`);
    logStats();
  }
});

function hasWorkingBwrap() {
  const which = cp.spawnSync("which", ["bwrap"], { stdio: "ignore" });
  if (which.status !== 0) return false;
  const test = cp.spawnSync("bwrap", ["--version"], { stdio: "ignore" });
  return test.status === 0;
}
