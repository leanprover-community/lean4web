import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [react()],
  publicDir: "client/public",
  server: {
    proxy: {
      '/websocket': {
        target: 'ws://localhost:8080',
        ws: true
      },
    }
  }
})
