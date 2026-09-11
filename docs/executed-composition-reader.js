/* Offline reader: generated Lean table, explicit evidence checks, inert fields.
 * The CLI verifies signatures; this reader pins fixture bytes and recomputes
 * semantics. Mutations are unsigned modeled controls, never authenticated runs. */
"use strict";
// Match the Rust serde boundary before interpreting evidence or Boolean values.
// Optional facts may be absent/null; a supplied value of the wrong type is invalid.
function admittedRun(run) {
  const object=x=>x!==null && typeof x==="object" && !Array.isArray(x);
  const shape=(x,keys)=>object(x) && Object.keys(x).every(k=>keys.includes(k));
  const string=x=>typeof x==="string", boolean=x=>typeof x==="boolean";
  const optional=(x,p)=>x===undefined || x===null || p(x);
  const channel=x=>["public","vault"].includes(x);
  const payload=x=>["fragment","summary"].includes(x);
  const decision=x=>["Permit","Deny","Review"].includes(x);
  const strings=x=>Array.isArray(x) && x.every(string);
  const grant=g=>shape(g,["principal","channel","payload","task"]) &&
    string(g.principal) && channel(g.channel) && payload(g.payload) && string(g.task);
  const event=e=>shape(e,["index","principal","channel","payload","authenticated","local","decision","effect"]) &&
    Number.isSafeInteger(e.index) && e.index>=0 && decision(e.local) && decision(e.decision) &&
    optional(e.principal,string) && optional(e.channel,channel) &&
    optional(e.payload,payload) && optional(e.authenticated,boolean) && optional(e.effect,string);
  return shape(run,["format","id","policy","guarded","complete","principals","grants","events","public_sink","vault_sink"]) &&
    string(run.format) && string(run.id) && string(run.policy) &&
    boolean(run.guarded) && boolean(run.complete) &&
    optional(run.principals,x=>strings(x) && x.length===2) &&
    optional(run.grants,x=>Array.isArray(x) && x.every(grant)) &&
    Array.isArray(run.events) && run.events.every(event) &&
    optional(run.public_sink,strings) && optional(run.vault_sink,strings);
}
function evaluate(run, table, policy) {
  const base = {knowledge:"Invalid", governance:"Review", reason:"Malformed evidence", state:null, witness:[]};
  const result = (knowledge, reason) => ({...base, knowledge, reason});
  if (!admittedRun(run)) return result("Invalid", "The record does not satisfy the typed evidence schema.");
  if (run.events.length>256 || new TextEncoder().encode(run.id).length>512)
    return result("Invalid", "The bounded experiment limits were exceeded.");
  if (run.policy !== policy || run.format !== "legitimacy.executed-composition.run.v1")
    return result("Invalid", "The fixed policy/property was substituted.");
  if (!run.complete || !run.events.length || !run.grants || !run.principals || !run.public_sink || !run.vault_sink)
    return result("Inconclusive", "Identity, scoped authority, completion, or sink evidence is missing.");
  if (run.principals.some(p=>p.length===0) || new Set(run.principals).size !== 2 ||
      run.grants.length>32 || run.grants.some(g=>!run.principals.includes(g.principal)))
    return result("Invalid", "The declared principal set or event sequence is invalid.");
  if (run.events.some(e => [e.principal,e.channel,e.payload,e.authenticated,e.effect].some(v => v === null || v === undefined)))
    return result("Inconclusive", "A load-bearing event fact is missing; safety cannot be certified.");
  let state=0, all=true, localAll=true, fullAll=true, first=null, witnesses=[null,null], sinks=[[],[]];
  for (const [i,e] of run.events.entries()) {
    const actor=run.principals.indexOf(e.principal);
    if (actor<0 || e.index!==i || !["public","vault"].includes(e.channel) || !["fragment","summary"].includes(e.payload))
      return result("Invalid", "Identity, channel, payload, or host order is invalid.");
    const scoped=run.grants.some(g=>g.principal===e.principal && g.channel===e.channel && g.payload===e.payload && g.task==="synthetic-release");
    const row=table.rows[state*32+actor*16+(e.payload==="fragment"?8:0)+(e.channel==="public"?4:0)+(e.authenticated?2:0)+(scoped?1:0)];
    const allowed=row[run.guarded?2:1]===1;
    const bytes=allowed?(e.payload==="fragment"?["SYNTHETIC-ALPHA","SYNTHETIC-BETA"][actor]:"SUMMARY: one synthetic fragment processed"):"";
    if (e.local!==(row[1]?"Permit":"Deny") || e.decision!==(allowed?"Permit":"Deny") || e.effect!==bytes)
      return result("Invalid", "Recorded decision/effect disagrees with the Lean transition and scoped request.");
    fullAll=fullAll&&row[2]===1;
    all=all&&allowed; localAll=localAll&&row[1]===1;
    if (allowed) {
      sinks[e.channel==="public"?0:1].push(bytes);
      if(e.channel==="public" && e.payload==="fragment" && witnesses[actor]===null) witnesses[actor]=i;
    }
    state=row[run.guarded?4:3];
    if(state!==((witnesses[0]===null?0:2)+(witnesses[1]===null?0:1))) return result("Invalid","Effect abstraction mismatch.");
    if(state===3 && first===null) first=i;
  }
  if(JSON.stringify(sinks)!==JSON.stringify([run.public_sink,run.vault_sink])) return result("Invalid","Sink readback does not match deliveries.");
  return {knowledge:first===null?"Safe":"Violated", governance:first!==null||!all?"Deny":"Permit", state,
    local:localAll?"Permit":"Deny", full:fullAll?"Permit":"Deny", first, witness:first===null?[]:witnesses,
    reason:first!==null?"The realized public fragment deliveries passed local authorization and expose both fragments.":
      all?"Useful authorized deliveries completed under the identical forbidden property.":"The guard denied a requested action; the recorded effects remain safe."};
}
if (typeof module !== "undefined") module.exports={evaluate};
if (typeof document !== "undefined") {
  const data=JSON.parse(document.getElementById("artifact-data").textContent);
  const byId=id=>document.getElementById(id);
  const node=(tag,text,cls)=>{const n=document.createElement(tag);n.textContent=text;if(cls)n.className=cls;return n;};
  let selected=0, mutation="original";
  const names=["Local approvals → collective harm","Equal length, vault action","Guard blocks joint release","Useful vault repair","Useful summary repair","Authentication without delegation","Missing authority evidence"];
  function draw(){
    const run=structuredClone(data.bundle[selected].run);
    if(mutation==="authority")run.grants=null;
    if(mutation==="effect")run.events[0].effect="invented effect";
    if(mutation==="property")run.policy=run.policy.replace("boolJointForbiddenList","boolTrackedSafeForbiddenList");
    if(mutation==="rename")run.id="\u003cscript>untrusted presentation text\u003c/script>";
    const verdict=evaluate(run,data.table,data.policy);
    byId("run-id").textContent=run.id;
    byId("mode").textContent=run.guarded?"Composition guard enabled":"Per-call authorization only";
    byId("knowledge").textContent=verdict.knowledge;
    byId("knowledge").className="verdict "+verdict.knowledge.toLowerCase();
    byId("governance").textContent=verdict.governance;
    byId("reason").textContent=verdict.reason;
    byId("control-note").textContent=mutation==="original"?"Original captured record. CLI authentication is checked separately.":"Unsigned semantic mutation. The original signature does not authenticate these edited bytes.";
    byId("events").replaceChildren();
    for(const event of run.events){
      const tr=document.createElement("tr");
      for(const v of [event.index+1,event.principal,event.payload,event.channel,event.local,event.decision,event.effect||"No delivery"])
        tr.append(node("td",v??"Missing evidence"));
      byId("events").append(tr);
    }
    byId("public-sink").textContent=JSON.stringify(run.public_sink,null,2);
    byId("vault-sink").textContent=JSON.stringify(run.vault_sink,null,2);
    byId("witness").textContent=verdict.witness.length?"Events "+verdict.witness.map(x=>x+1).join(" + ")+". First forbidden prefix ends at event "+(verdict.first+1)+".":"No collective witness certified in this view.";
    byId("local-baseline").textContent=verdict.local??"Review";
    byId("full-baseline").textContent=verdict.full??"Review";
  }
  names.forEach((name,i)=>{const b=node("button",name);b.type="button";b.onclick=()=>{selected=i;mutation="original";byId("controls").value=mutation;draw();for(const x of byId("runs").children)x.setAttribute("aria-pressed",String(x===b));};b.setAttribute("aria-pressed",String(i===0));byId("runs").append(b);});
  byId("controls").onchange=e=>{mutation=e.target.value;draw();};
  const encoded=new TextEncoder().encode(JSON.stringify(data.bundle));
  if(globalThis.crypto?.subtle){
    crypto.subtle.digest("SHA-256",encoded).then(hash=>{
      const actual=[...new Uint8Array(hash)].map(b=>b.toString(16).padStart(2,"0")).join("");
      if(actual!==data.bundle_sha256)throw new Error("Pinned fixture bytes changed");
      byId("integrity").textContent="Pinned fixture bytes match · semantics recomputed locally · no network or uploads";
      draw();
    }).catch(()=>{byId("integrity").textContent="INVALID: fixture integrity check failed";byId("reader").hidden=true;});
  }else{byId("integrity").textContent="Browser hashing unavailable. Use the offline CLI before relying on this view.";draw();}
}
