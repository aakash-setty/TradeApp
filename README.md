# The Shift Exchange — JMH / HCH shift trading

A static site + one Netlify serverless function. The browser downloads everyone's
shifts once, then computes valid trades instantly on the client using the same
rules as the original Flask app (verified 1:1 against it — identical results for
all 183 eligible shifts / 4,344 valid pairs at time of port).

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
npm run dev        # http://localhost:5173  (serves /api/shifts too — no netlify-cli needed)
npm run build      # production build into dist/
```

## Deploy to Netlify (free tier)

1. Push this folder to a **private** GitHub repo (see security note below).
2. In Netlify: "Add new site" → "Import an existing project" → pick the repo.
   Build settings are read from `netlify.toml` automatically
   (build `npm run build`, publish `dist`, functions in `netlify/functions`).
3. Deploy. The function is served at `/api/shifts` with a 2-minute CDN cache.

## Security notes

- `netlify/functions/calendars.json` holds the private QGenda iCal keys. It is
  bundled into the serverless function (server-side only, never shipped to the
  browser) — but it *is* in the repo, so keep the repo private.
  To keep keys out of the repo entirely, delete the file and set a
  `CALENDARS_JSON` environment variable in Netlify (Site settings →
  Environment variables) containing the same JSON array.
- Free-tier Netlify has no site password; the URL is the only gate.
