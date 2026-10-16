// hgraph's native hash router accepts statement IDs and chapter numbers. Resolve
// the paper/map labels through its own reference index before navigating.
const projects=new Map();
let scheduled=false, pendingScroll=null;
async function resolveLocation() {
  const match=location.hash.match(/^#\/(smooth|discrete)#(.+)$/);
  if (!match) return;
  const [,kind,raw]=match;const label=decodeURIComponent(raw);
  if (!projects.has(kind)) projects.set(kind,fetch(`./${kind}/project.json`).then(r=>{if(!r.ok)throw new Error('Cannot read blueprint references');return r.json();}));
  const project=await projects.get(kind),ref=project.refs[label];
  if (!ref || location.hash!==match[0]) return;
  const destination=ref.id || `ch-${ref.ch+1}`;
  pendingScroll=ref.anchor || null;
  history.replaceState(null,'',`#/${kind}#${destination}`);
  window.dispatchEvent(new Event('hashchange'));
}
function annotate() {
  scheduled=false;
  for (const stat of document.querySelectorAll('.project-stats .pstat')) {
    if (/\d+%/.test(stat.textContent)) {stat.hidden=true;continue;}
    for (const text of stat.childNodes) {
      if (text.nodeType===Node.TEXT_NODE && text.textContent.includes('formalized')) {
        text.textContent=text.textContent.replace('formalized','source linked');
        stat.title='Declarations associated with paper statements; not a new build audit.';
      }
    }
  }
  if (pendingScroll) {
    const target=document.getElementById(pendingScroll);
    if(target){target.scrollIntoView({block:'center'});pendingScroll=null;}
  }
  const doc=document.querySelector('.doc-main .doc');
  const kind=location.hash.startsWith('#/discrete')?'discrete':location.hash.startsWith('#/smooth')?'smooth':null;
  if (!doc || !kind || doc.querySelector(':scope > .reader-scope')) return;
  const aside=document.createElement('aside');aside.className='reader-scope';
  aside.innerHTML=`<a href="/web/blueprint/">All projects</a> · <a href="/web/#playground">Playground</a><p>The paper and its supporting proofs, with linked Lean declarations. <a href="/paper/tabachnikov-converse.pdf">The paper</a>.</p>`;
  doc.prepend(aside);
}
new MutationObserver(()=>{if(!scheduled){scheduled=true;requestAnimationFrame(annotate);}}).observe(document.body,{childList:true,subtree:true});
window.addEventListener('hashchange',()=>{resolveLocation();requestAnimationFrame(annotate);});
resolveLocation();annotate();
