// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps: [
    {
      name: "lean4web",
      script: "server/index.mjs",
      env: {
        NODE_ENV: "production",
        PORT: 8001,
        ALLOW_NO_BUBBLEWRAP: false,
        PROJECTS_BASE_PATH: "Projects", // relative path to the folder containing all projects
        SSL_CRT_FILE: undefined,
        SSL_KEY_FILE: undefined,
      },
    },
  ],
};
