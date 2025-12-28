// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps: [
    {
      name: "lean4web",
      script: "server/index.mjs",
      env: {
        NODE_ENV: "production",
        PORT: 8001,
      },
    },
  ],
};
