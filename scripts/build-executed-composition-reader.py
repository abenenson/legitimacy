#!/usr/bin/env python3
"""Generate a self-contained, no-upload reader from retained host evidence."""
import argparse
import base64
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def build():
    fixture = ROOT / "fixtures/executed-composition-v1"
    bundle = json.loads((fixture / "capture/bundle.json").read_text())
    data = {"bundle": bundle, "table": json.loads((fixture / "generated/table.json").read_text()),
            "policy": (fixture / "policy.json").read_text(),
            "bundle_sha256": hashlib.sha256(json.dumps(bundle, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()}
    encoded = json.dumps(data, separators=(",", ":"), ensure_ascii=True).replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")
    script = (ROOT / "docs/executed-composition-reader.js").read_text()
    assert "</script" not in script.lower(), "inline script terminator must be escaped"
    digest = base64.b64encode(hashlib.sha256(script.encode()).digest()).decode()
    return '''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; script-src 'sha256-''' + digest + ''''; style-src 'unsafe-inline'; connect-src 'none'; base-uri 'none'; form-action 'none'">
<title>Executed composition — Legitimacy</title>
<style>
:root{font-family:system-ui,sans-serif;color:#172334;background:#f6f5f0;font-size:16px;line-height:1.55}*{box-sizing:border-box}body{margin:0}main{max-width:1180px;margin:auto;padding:48px 28px}h1{font-size:clamp(2.3rem,5vw,4.2rem);line-height:1.06;letter-spacing:-.055em;max-width:850px;margin:20px 0}h2{font-size:1.35rem;letter-spacing:-.02em}h3{font-size:1rem}p{max-width:850px}.eyebrow{color:#456078;font-size:.8rem;letter-spacing:.15em;text-transform:uppercase;font-weight:700}.lead{font-size:1.18rem;color:#47566a;max-width:760px}header{padding-bottom:28px;border-bottom:2px solid #172334}.contract{background:#e8edf1;border-left:4px solid #386582;padding:18px 24px;margin:26px 0}.contract code{overflow-wrap:anywhere}#integrity,.note{font-size:.84rem;color:#536477}#runs{display:flex;flex-wrap:wrap;gap:8px;margin:24px 0}button,select{font:inherit;border:1px solid #b8c2ca;border-radius:5px;padding:9px 13px;background:#fff;color:#172334;cursor:pointer}button[aria-pressed=true]{background:#203d55;color:#fff;border-color:#203d55}button:focus-visible,select:focus-visible{outline:3px solid #ad6916;outline-offset:2px}.panel{background:white;border:1px solid #d4d9dc;border-radius:8px;padding:24px;margin:16px 0}.status{display:flex;gap:35px;flex-wrap:wrap}.label{font-size:.78rem;letter-spacing:.1em;text-transform:uppercase;color:#536477}.verdict,#governance{font-size:2rem;font-weight:700}.violated,.invalid{color:#a33326}.safe{color:#216648}.inconclusive{color:#8a6017}#run-id{overflow-wrap:anywhere;font-family:monospace;color:#536477}.scroll{overflow:auto}table{width:100%;border-collapse:collapse;font-size:.87rem}th{text-align:left;font-size:.7rem;letter-spacing:.08em;text-transform:uppercase;color:#536477}td,th{padding:12px 10px;border-bottom:1px solid #e3e7e9;vertical-align:top}td:last-child{font-family:monospace;overflow-wrap:anywhere;min-width:140px}.two{display:grid;grid-template-columns:1fr 1fr;gap:20px}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#f3f5f6;padding:15px;font-size:.83rem}footer{margin-top:35px;padding-top:22px;border-top:1px solid #b8c2ca;font-size:.86rem;color:#536477}@media(max-width:700px){main{padding:25px 14px}.panel{padding:16px}.two{grid-template-columns:1fr}button{font-size:.8rem}}
</style>
<main><header><div class="eyebrow">Legitimacy · executed composition · offline artifact</div>
<h1>Two approvals.<br>One collective effect.</h1>
<p class="lead">Two supplied principals deliver harmless synthetic fragments. Local authorization permits each action. Their public deliveries can still compose into a forbidden result. Inspect the execution, then test a useful repair.</p></header>
<div class="contract"><strong>One fixed property throughout</strong><br>Both distinct synthetic fragments must never reach the public channel.<br><code>Legitimacy.boolJointForbiddenList</code><br><span class="note">A public exposure maps to A=true; B public exposure maps to B=false. Lean proves this principal-dependent encoding matches the existing conjunctive property.</span></div>
<p id="integrity" role="status">Checking pinned fixture bytes…</p><noscript>This reader needs JavaScript. The supplied offline CLI independently checks the artifact.</noscript>
<div id="reader"><nav id="runs" aria-label="Controlled executions"></nav>
<section class="panel"><div id="mode" class="eyebrow"></div><p id="run-id"></p><div class="status"><div><div class="label">Monitor knowledge</div><div id="knowledge" class="verdict"></div></div><div><div class="label">Governance decision</div><div id="governance"></div></div><div><div class="label">Per-call baseline</div><div id="local-baseline"></div></div><div><div class="label">Full-context baseline</div><div id="full-baseline"></div></div></div><p id="reason"></p><p id="witness"></p></section>
<section class="panel"><h2>What the host actually delivered</h2><p class="note">Event order is supplied by the sequential host. Actions come from its instrumented delivery boundary, never inferred from model prose.</p><div class="scroll"><table><thead><tr><th>Event</th><th>Principal</th><th>Payload</th><th>Channel</th><th>Local</th><th>Executed gate</th><th>Recorded effect</th></tr></thead><tbody id="events"></tbody></table></div><div class="two"><div><h3>Public sink readback</h3><pre id="public-sink"></pre></div><div><h3>Vault sink readback</h3><pre id="vault-sink"></pre></div></div></section>
<section class="panel"><h2>Challenge the evidence</h2><label for="controls">Apply a local semantic control </label><select id="controls"><option value="original">Original evidence</option><option value="authority">Remove scoped authority</option><option value="effect">Invent a recorded effect</option><option value="property">Substitute the forbidden property</option><option value="rename">Rename an incidental identifier</option></select><p id="control-note" class="note"></p></section></div>
<section class="two"><div><h2>The missing obligation</h2><p>Tracking the cross-agent conjunction is already present. The useful addition is to require each authorized delivery to preserve exclusion of the original collective property in the current exposure state.</p><p>Vault delivery and a public summary remain permitted. The same B fragment request is permitted before A's public release and denied afterward.</p></div><div><h2>What the proof adds</h2><p>Lean proves the executed-action refinement, safety for every finite guarded request list, and concrete useful alternatives. A full-context conventional checker reaches the same decisions. The contribution is the checked connection and repair, not superior detection.</p><p>Without scoped delegation, two observation-identical modeled requests require different decisions. Authentication alone cannot resolve that missing fact.</p></div></section>
<section class="panel"><h2>How much context must survive observation?</h2><p>For exact next-request decisions, the monitor must distinguish these three reachable safe states. Lean proves one exposure-state bit cannot suffice; the two exposure bits are sufficient for every modeled request. A deny-all monitor is outside this selectivity requirement.</p><table><thead><tr><th>Prior public exposure</th><th>Next A public fragment</th><th>Next B public fragment</th></tr></thead><tbody><tr><td>Neither</td><td>Permit</td><td>Permit</td></tr><tr><td>A only</td><td>Permit</td><td>Deny</td></tr><tr><td>B only</td><td>Deny</td><td>Permit</td></tr></tbody></table><p class="note">These answers assume authenticated, delegated requests. This finite bound concerns retained exposure context, not model capability or Shannon capacity.</p></section>
<section class="panel"><h2>Reproduce and inspect</h2><pre>./reproduce.sh
# Or: ./legitimacy-executed-composition check capture/bundle.json \\
#       --trust capture/trust-policy.json</pre><p>The CLI reuses the existing typed Ed25519 replay authority boundary and checks concrete effects independently of this page. The browser checks pinned fixture bytes and recomputes finite semantics; it does not verify the signed replay receipt.</p><p class="note">Trusted: the supplied host, principal slots, declared channels, host completion, action-to-effect implementation, and published public trust root. This is a sequential synthetic experiment. It proves no model alignment, production incident prevention, hidden-intent recovery, or unmodeled-channel discovery.</p></section>
<footer>Spera's conjunctive-capability non-composition result is prior work. PCAS supplies a strong history/provenance policy baseline; AgentSpec supplies runtime constraints. Legitimacy adds a checked executed-action connection and a useful same-property repair in this finite model. Paper 03 remains independently citable; spectral results retain their modeled-carrier assumptions.</footer>
</main><script id="artifact-data" type="application/json">''' + encoded + '''</script><script>''' + script + '''</script></html>\n'''

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "docs/executed-composition-reader.html")
    args = parser.parse_args()
    args.output.write_text(build())
