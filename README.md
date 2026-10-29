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
  Mon–Sun week of the shift you're giving away. Peds stamp: same, for Peds ER.
- Weekly hours include shifts already worked earlier that week. All-day calendar
  entries are not counted as hours.

## Peds ER shifts (Amion)

The server also imports Peds ER shifts from the UM peds Amion schedule
(`netlify/functions/lib/amion-peds.mjs`):

- It opens `amion.com/cgi-bin/ocs?Lo=umipe`, takes the fresh `File=!...` token from
  that page's Shift link, then follows each page's "Next rotation" link until it
  covers 3 months ahead (plus the previous rotation for the 21-day lookback).
- Only ER rows with a time in the label are read ("ER* 9p-7a", "ER* 3PM - 11PM").
  Overnight shifts end the next morning, and times are converted as Eastern wall
  clock, so DST nights come out the right length.
- Only names with an `ED 1/2` or `ER 3` style prefix are imported, and only when the
  last name matches an app user. Last names come from QGenda titles ("[Setty EM28]").
  To override, add `"lastName": "..."` to that person's entry in `calendars.data.mjs`.
- Peds shifts are tradable, count toward the rest rule and 60h cap, and get a Peds badge.
- Amion is re-fetched at most every 10 minutes per warm server instance.
- Settings: `AMION_PEDS_LOGIN` env var overrides the login code; set it to `off` to
  disable the import. If Amion can't be reached or its layout changes, the app still
  loads QGenda shifts and shows "1 feed unreachable" (hover for the reason).

Check the live import any time with `npm run check:amion` (or `npm run check:amion -- Setty`).
Run the tests with `npm test`.

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
