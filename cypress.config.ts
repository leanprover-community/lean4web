import { defineConfig } from "cypress";

export default defineConfig({
  defaultCommandTimeout: 15000,
  retries: 2,
  e2e: {
    baseUrl: "http://localhost:3000",
    setupNodeEvents(on, config) {
      on("before:browser:launch", (browser, launchOptions) => {
        if (browser.name === "chromium" && process.env.CYPRESS_USER_AGENT_OS) {
          launchOptions.args.push(
            `--user-agent=\"Mozilla/5.0 (${process.env.CYPRESS_USER_AGENT_OS}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/28.0.1500.52 Safari/537.36\"`,
          );
          return launchOptions;
        }
      });
    },
  },
});
