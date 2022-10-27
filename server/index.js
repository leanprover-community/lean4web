const WebSocketServer = require("./WebsocketServer");
const express = require("express");
const path = require("path")
const fs = require('fs');
const http = require('http');
const https = require('https');

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

const crtFile = process.env.SSL_CRT_FILE
const keyFile = process.env.SSL_KEY_FILE

const app = express()
app.use(express.static(path.join(__dirname, '../client/dist/')))

let server;
if (crtFile && keyFile) {
  var privateKey  = fs.readFileSync(keyFile, 'utf8');
  var certificate = fs.readFileSync(crtFile, 'utf8');
  var credentials = {key: privateKey, cert: certificate};

  app.use(function(req,resp,next){
    if (req.headers['x-forwarded-proto'] == 'http') {
        return resp.redirect(301, 'https://' + req.headers.host + '/');
    } else {
        return next();
    }
  });

  http.createServer(app).listen(80)
  const PORT = process.env.PORT ?? 443
  server = https.createServer(credentials, app).listen(PORT,
    () => console.log(`HTTPS on port ${PORT}`));
} else {
  const PORT = process.env.PORT ?? 8080
  server = app.listen(PORT,
    () => console.log(`HTTP on port ${PORT}`))
}

const wss = new WebSocketServer(server, !isDevelopment)
