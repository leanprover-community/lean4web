
const WebSocketServer = require("./WebsocketServer")
const express = require("express")
const path = require("path")
const nocache = require("nocache")

const app = express()
app.use(express.static(path.join(__dirname, '../client/dist/')))
app.use(nocache())

const PORT = process.env.PORT ?? 8080
const server = app.listen(PORT, () => console.log(`HTTP on port ${PORT}`))

new WebSocketServer(server)
