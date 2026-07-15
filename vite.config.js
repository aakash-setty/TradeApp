import { defineConfig } from "vite";

// Serves /api/shifts during local dev using the same core module the
// Netlify function uses in production, so `npm run dev` needs no netlify-cli.
function devApiPlugin() {
  return {
    name: "dev-shifts-api",
    configureServer(server) {
      server.middlewares.use("/api/shifts", async (req, res) => {
        try {
          const { getShifts } = await import("./netlify/functions/lib/shifts-core.mjs");
          const data = await getShifts();
          res.setHeader("Content-Type", "application/json");
          res.end(JSON.stringify(data));
        } catch (e) {
          res.statusCode = 500;
          res.setHeader("Content-Type", "application/json");
          res.end(JSON.stringify({ error: String(e && e.message ? e.message : e) }));
        }
      });
    },
  };
}

export default defineConfig({
  plugins: [devApiPlugin()],
  server: {
    port: 5173,
    strictPort: true,
  },
});
