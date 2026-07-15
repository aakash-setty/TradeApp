# The Shift Exchange — JMH / HCH shift trading

A static site + one serverless function. The browser downloads everyone's
shifts once, then computes valid trades instantly on the client using the same
rules as the original Flask app (verified 1:1 against it — identical results for
all 183 eligible shifts / 4,344 valid pairs at time of port).

Works on **Vercel** (uses `api/shifts.mjs`, configured by `vercel.json`) and on
**Netlify** (uses `netlify/functions/shifts.mjs`, configured by `netlify.toml`).
Both wrap the same core module: `netlify/functions/lib/shifts-core.mjs`.

## Rules (unchanged from the Flask app)

- Tradable shifts match the Day/Eve/Night/Pod/Side patterns; trauma, ultrasound,
  "US", and sick call are excluded. Future shifts only (starting tomorrow+, ET).
- A swap is valid when: both people are free for each other's shift, the local
  rest rule holds (gap ≥ prior shift's duration on both sides), and neither
  person exceeds 60h in the Mon–Sun week of their new shift.
- ED/Tra stamp: the partner works an ED (JMH/HCH) or Trauma shift during the
  Mon–Sun week of the shift you're giving away.

## Local development

```bash
npm install
npm run dev        # http://localhost:5173  (serves /api/shifts too)
npm run build      # production build into dist/
```

## Deploy to Vercel (free Hobby tier)

1. Push this folder's contents to a **private** GitHub repo (root of the repo =
   this folder, so `package.json` and `vercel.json` sit at the top level).
2. In Vercel: "Add New… → Project" → import the repo. The framework (Vite),
   build command, and output directory are read from `vercel.json`; the
   function in `api/` is picked up automatically. Leave "Root Directory" as
   the repo root.
3. Deploy. The schedule API is served at `/api/shifts` with a 2-minute cache.

## Deploy to Netlify (alternative)

Import the same repo; `netlify.toml` supplies all settings.

## Security notes

- The private QGenda iCal keys live in
  `netlify/functions/lib/calendars.data.mjs`. That module is only ever bundled
  into the serverless function (server-side), never into the browser bundle —
  but it *is* in the repo, so **keep the repo private**.
  To keep keys out of the repo entirely, blank that file and set a
  `CALENDARS_JSON` environment variable (same JSON array of `{name, url}`)
  in your Vercel/Netlify project settings.
- Free tiers have no site password; the URL is the only gate.
