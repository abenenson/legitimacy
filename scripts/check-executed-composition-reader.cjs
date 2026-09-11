// Node runs the same reader evaluator without a DOM, with independent expected fixtures.
const assert=require('node:assert/strict'),fs=require('node:fs'),crypto=require('node:crypto');
const {evaluate}=require('../docs/executed-composition-reader.js');
const root=__dirname+'/../fixtures/executed-composition-v1/';
const bundle=JSON.parse(fs.readFileSync(root+'capture/bundle.json'));
const expected=JSON.parse(fs.readFileSync(root+'capture/reports.json'));
const table=JSON.parse(fs.readFileSync(root+'generated/table.json'));
const policy=fs.readFileSync(root+'policy.json','utf8');
for(const [i,signed] of bundle.entries()) {
  const result=evaluate(signed.run,table,policy);
  assert.equal(result.knowledge,expected[i].knowledge);
  assert.equal(result.governance,expected[i].governance);
  assert.equal(result.full??"Review",expected[i].full_context_baseline);
  assert.deepEqual(result.witness,expected[i].participating_events);
}
for(const field of ['principal','channel','payload','authenticated','effect']) {
  const r=structuredClone(bundle[3].run);r.events[0][field]=null;
  assert.equal(evaluate(r,table,policy).knowledge,'Inconclusive');
}
let r=structuredClone(bundle[3].run);r.policy+=' ';
assert.equal(evaluate(r,table,policy).knowledge,'Invalid');
r=structuredClone(bundle[3].run);r.events[0].effect='forged';
assert.equal(evaluate(r,table,policy).knowledge,'Invalid');
r=structuredClone(bundle[3].run);r.id='</script><img onerror=alert(1)>';
assert.equal(evaluate(r,table,policy).knowledge,'Safe');
const html=fs.readFileSync(__dirname+'/../docs/executed-composition-reader.html','utf8');
const data=JSON.parse(html.match(/<script id="artifact-data" type="application\/json">([\s\S]*?)<\/script>/)[1]);
assert.equal(crypto.createHash('sha256').update(JSON.stringify(data.bundle)).digest('hex'),data.bundle_sha256);
const script=fs.readFileSync(__dirname+'/../docs/executed-composition-reader.js','utf8');
assert(html.includes("script-src 'sha256-"+crypto.createHash('sha256').update(script).digest('base64')+"'"));
assert(!script.toLowerCase().includes("</script"));
assert(!/innerHTML|outerHTML|document\.write|\beval\(|\bfetch\(|XMLHttpRequest|WebSocket/.test(script));
console.log('reader: 7 fixture results, evidence mutations, inert-field and CSP checks passed');

// Typed admission must precede semantic interpretation, matching Rust's boundary.
const invalidMutations=[
  r=>{r.events[0].authenticated="false";},
  r=>{r.complete="false";}, r=>{r.guarded="false";},
  r=>{const old=r.principals[0];r.principals[0]="";
    for(const e of r.events)if(e.principal===old)e.principal="";
    for(const g of r.grants)if(g.principal===old)g.principal="";},
  r=>{r.events[0].index="0";}, r=>{r.events[0].effect=42;},
  r=>{r.events[0].unknown=true;}, r=>{r.grants[0].channel="unmodeled";},
  r=>{r.grants[0].principal="undeclared";}, r=>{r.grants={};},
  r=>{r.public_sink=[null];}, r=>{r.events=null;},
  r=>{r.principals=["one"];}, r=>{delete r.guarded;},
  r=>{r.id="x".repeat(513);}, r=>{r.id="é".repeat(257);},
  r=>{r.events=Array.from({length:257},()=>r.events[0]);}
];
for(const mutate of invalidMutations) {
  const r=structuredClone(bundle[3].run);mutate(r);
  assert.equal(evaluate(r,table,policy).knowledge,"Invalid");
}
for(const r of [null,[],{},true]) assert.equal(evaluate(r,table,policy).knowledge,"Invalid");
for(const field of ["principal","channel","payload","authenticated","effect"]) {
  const r=structuredClone(bundle[3].run);delete r.events[0][field];
  assert.equal(evaluate(r,table,policy).knowledge,"Inconclusive");
}
for(const mutate of [
  r=>{r.complete=false;},r=>{r.events=[];},
  r=>{delete r.grants;},r=>{r.public_sink=null;}
]) {
  const r=structuredClone(bundle[3].run);mutate(r);
  assert.equal(evaluate(r,table,policy).knowledge,"Inconclusive");
}
console.log("reader: strict typed admission and missing-evidence regressions passed");
