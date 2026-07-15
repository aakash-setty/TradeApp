import { getShifts } from "./lib/shifts-core.mjs";

export default async () => {
  try {
    const data = await getShifts();
    return new Response(JSON.stringify(data), {
      headers: {
        "Content-Type": "application/json",
        "Cache-Control": "public, max-age=120",
      },
    });
  } catch (e) {
    return new Response(
      JSON.stringify({ error: String(e && e.message ? e.message : e) }),
      { status: 500, headers: { "Content-Type": "application/json" } }
    );
  }
};

export const config = {
  path: "/api/shifts",
};
