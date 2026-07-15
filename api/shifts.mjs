// Vercel serverless function (the Netlify equivalent lives in netlify/functions/).
import { getShifts } from "../netlify/functions/lib/shifts-core.mjs";

export default async function handler(req, res) {
  try {
    const data = await getShifts();
    res.setHeader("Cache-Control", "public, max-age=120, s-maxage=120");
    res.status(200).json(data);
  } catch (e) {
    res.status(500).json({ error: String(e && e.message ? e.message : e) });
  }
}
