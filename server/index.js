const WebSocketServer = require("./WebsocketServer");
const express = require("express");
const path = require("path")
const fs = require('fs');
const http = require('http');
const https = require('https');
const nocache = require("nocache");

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

const crtFile = process.env.SSL_CRT_FILE
const keyFile = process.env.SSL_KEY_FILE

const app = express()
app.use('/examples/*', (req, res, next) => {
  const filename = req.params[0];
  console.debug(`trying to load ${filename}`)
  req.url = filename;
  express.static(path.join(__dirname, '..', 'Projects'))(req, res, next)
  // express.static(path.join(__dirname, '..', 'Projects', filename))(req, res, next);
})
app.use(express.static(path.join(__dirname, '..', 'client', 'dist')))

app.use(nocache())

let server;
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

const wss = new WebSocketServer(server, !isDevelopment)
