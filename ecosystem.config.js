// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps : [{
    name   : "lean4web",
    script : "server/index.js",
    env: {
       NODE_ENV: "production",
       SSL_CRT_FILE: "~/adam_math_uni-duesseldorf_de_cert.cer",
       SSL_KEY_FILE: "~/private_ssl_key.pem"
    },
  }]
}
