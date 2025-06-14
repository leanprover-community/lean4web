import { defineConfig } from "cypress";

export default defineConfig({
    defaultCommandTimeout: 15000,
    retries: 2,
    e2e: {
        baseUrl: "http://localhost:3000",
        setupNodeEvents(on, config) {
            // implement node event listeners here
        },
    },
});