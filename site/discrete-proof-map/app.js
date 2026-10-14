const $ = selector => document.querySelector(selector);
const escape = value => String(value).replace(/[&<>"']/g, char => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[char]));

async function start() {
  const response = await fetch(new URL('./graph.json', import.meta.url));
  if (!response.ok) throw new Error(`Map data could not be loaded (${response.status}).`);
  const {nodes, routes, edges, story} = await response.json();
  const byId = new Map(nodes.map(node => [node.id, node]));
  const routeById = new Map(routes.map(route => [route.id, route]));
  const initial = new URL(location.href);
  let selected = routeById.has(initial.searchParams.get('case')) ? initial.searchParams.get('case') : '';
  let compared = selected && routeById.has(initial.searchParams.get('compare')) ? initial.searchParams.get('compare') : '';
  if (compared === selected) compared = '';
  let inspected = '', returnFocus = null, drawRequest = 0;
  const dialog = $('#inspector');
  const nodeButtons = new Map();

  function routeSet(id) { return new Set(routeById.get(id)?.nodes || []); }
  function saveLocation() {
    const url = new URL(location.href);
    if (selected) url.searchParams.set('case', selected); else url.searchParams.delete('case');
    if (compared) url.searchParams.set('compare', compared); else url.searchParams.delete('compare');
    url.hash = inspected || (document.querySelector('#proof-map') ? 'proof-map' : location.hash === '#map-title' ? 'map-title' : '');
    history.replaceState(null, '', url);
  }
  function related(ids) {
    return ids.map(id => `<button type="button" class="related-node" data-explainer="${id}">${escape(byId.get(id).title)} <span aria-hidden="true">→</span></button>`).join('');
  }
  function detail(node) {
    const incoming = edges.filter(([,to]) => to === node.id).map(([from]) => from);
    const outgoing = edges.filter(([from]) => from === node.id).map(([,to]) => to);
    const conditions = node.conditions ? `<section class="detail-section"><h3>Hypotheses and conclusion</h3><dl class="condition-list">${node.conditions.map(({name,text}) => `<div><dt>${escape(name)}</dt><dd>${escape(text)}</dd></div>`).join('')}</dl></section>` : '';
    $('#detail').innerHTML = `<div class="detail-title"><span class="status established">${node.stage === 'extensions' ? 'Separate local-continuity theorem' : 'Completed discrete construction'}</span><h2 id="explainer-title" tabindex="-1">${escape(node.title)}</h2><p class="detail-subtitle">${escape(node.subtitle)}</p></div>
      <div class="detail-formula">${escape(node.formula)}</div>
      <section class="detail-section"><h3>What this contributes</h3><p>${escape(node.summary)}</p></section>
      ${conditions}<section class="detail-section"><h3>How the argument works</h3><ol class="mechanism-list">${node.mechanism.map(step => `<li>${escape(step)}</li>`).join('')}</ol></section>
      <section class="detail-section"><h3>Role in the proof</h3><p>${escape(node.role)}</p>${node.caveat ? `<p class="detail-caveat">${escape(node.caveat)}</p>` : ''}</section>
      ${incoming.length ? `<section class="detail-section"><h3>Previous steps${incoming.length > 1 ? ' · alternative branches' : ''}</h3><div class="related-nodes">${related(incoming)}</div></section>` : ''}
      ${outgoing.length ? `<section class="detail-section"><h3>Next steps</h3><div class="related-nodes">${related(outgoing)}</div></section>` : ''}
      <section class="detail-section detail-blueprint"><h3>Read the mathematical argument</h3><div class="blueprint-links">${node.links.map(link => `<a href="${escape(link.url)}">${escape(link.title)} ↗</a>`).join('')}</div></section>
      <section class="detail-section"><h3>Lean source</h3>${node.sources.map(source => `<div class="source-entry"><code>${escape(source.declaration)}</code><a href="https://github.com/kejace/cd4vt/blob/main/Gluck/Discrete/${encodeURIComponent(source.file)}" target="_blank" rel="noopener">${escape(source.file)} ↗</a></div>`).join('')}<p class="source-note">Lean source in the cd4vt repository. These cards explain the source; they are not a compiled extraction.</p></section>`;
  }
  function openExplainer(id) {
    const node = byId.get(id);
    if (!node) return;
    if (!dialog.open) returnFocus = document.activeElement;
    inspected = id;
    detail(node);
    dialog.dataset.node = id;
    dialog.dataset.color = node.color;
    if (!dialog.open) { document.body.classList.add('explainer-open'); dialog.showModal(); }
    dialog.scrollTop = 0;
    $('#explainer-title').focus({preventScroll:true});
    saveLocation();
    update();
  }
  for (const node of nodes) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = `node ${node.color}`;
    button.id = `node-${node.id}`;
    button.dataset.node = node.id;
    button.style.setProperty('--column', node.column);
    button.style.setProperty('--span', node.span);
    button.setAttribute('aria-haspopup', 'dialog');
    button.setAttribute('aria-controls', 'inspector');
    button.setAttribute('aria-label', `${node.title}. ${node.subtitle}. Open explanation.`);
    button.innerHTML = `<span class="node-status" aria-hidden="true"></span><span class="node-title">${escape(node.title)}</span><span class="node-subtitle">${escape(node.subtitle)}</span><span class="node-formula">${escape(node.formula)}</span><span class="node-expand" aria-hidden="true">↗</span>`;
    button.addEventListener('click', () => openExplainer(node.id));
    $(`#${node.stage}`).append(button);
    nodeButtons.set(node.id, button);
  }
  $('#story-grid').innerHTML = story.map((step,i) => `<button type="button" class="story-card" data-explainer="${step.node}" aria-haspopup="dialog" aria-controls="inspector"><span class="story-number">0${i+1}</span><span><strong>${escape(step.title)}</strong><small>${escape(step.subtitle)}</small></span><span class="story-open" aria-hidden="true">↗</span></button>`).join('');
  for (const route of routes) for (const id of ['trace','compare']) {
    const option = document.createElement('option');
    option.value = route.id;
    option.textContent = route.title;
    $(`#${id}`).append(option);
  }
  function update() {
    const first = routeSet(selected), second = routeSet(compared);
    for (const node of nodes) {
      const button = nodeButtons.get(node.id);
      button.classList.toggle('dimmed', node.stage !== 'extensions' && Boolean(selected) && !first.has(node.id) && !second.has(node.id));
      button.classList.toggle('common', Boolean(compared) && first.has(node.id) && second.has(node.id));
      button.classList.toggle('inspected', node.id === inspected);
    }
    $('#trace').value = selected;
    $('#compare').value = compared;
    $('.common-key').hidden = !compared;
    $('#trace-description').textContent = compared
      ? `${routeById.get(selected).title} + ${routeById.get(compared).title}. Dark green marks the steps shared by both cases. Each colored branch is an alternative construction.`
      : selected ? routeById.get(selected).description : 'All cases are shown. The four colored branches are alternatives; each nonconstant case rejoins the same restoration and opening argument.';
    $('#route-outline').hidden = !selected;
    if (selected) {
      $('#route-title').textContent = `Trace: ${routeById.get(selected).title}`;
      $('#route-steps').innerHTML = routeById.get(selected).nodes.map(id => `<li><button type="button" data-explainer="${id}" aria-haspopup="dialog">${escape(byId.get(id).title)}</button></li>`).join('');
    }
    cancelAnimationFrame(drawRequest);
    drawRequest = requestAnimationFrame(drawEdges);
  }
  function drawEdges() {
    const map = $('#map').getBoundingClientRect();
    const first = routeSet(selected), second = routeSet(compared);
    const box = id => { const b = nodeButtons.get(id).getBoundingClientRect(); return {x:b.left-map.left,y:b.top-map.top,w:b.width,h:b.height}; };
    const paths = [];
    for (const [from,to] of edges) {
      const a=box(from), b=box(to);
      const active = (first.has(from) && first.has(to)) || (second.has(from) && second.has(to));
      const common = compared && first.has(from) && first.has(to) && second.has(from) && second.has(to);
      let path;
      if (Math.abs(a.y-b.y) < 10) {
        const x1=a.x+a.w+2, y1=a.y+a.h/2, x2=b.x-3, y2=b.y+b.h/2;
        path=`M ${x1} ${y1} C ${x1+14} ${y1}, ${x2-14} ${y2}, ${x2} ${y2}`;
      } else if (from === 'constant') {
        const x1=a.x+a.w, y1=a.y+a.h/2, rail=map.width-13, x2=b.x+b.w, y2=b.y+b.h/2;
        path=`M ${x1} ${y1} H ${rail} V ${y2} H ${x2+3}`;
      } else {
        const x1=a.x+a.w/2, y1=a.y+a.h+2, x2=b.x+b.w/2, y2=b.y-3, dy=y2-y1;
        path=`M ${x1} ${y1} C ${x1} ${y1+dy*.5}, ${x2} ${y2-dy*.5}, ${x2} ${y2}`;
      }
      paths.push(`<path data-from="${from}" data-to="${to}" class="edge ${common ? 'common' : active ? 'active' : selected ? 'dimmed' : ''}" d="${path}"/>`);
    }
    $('#edge-paths').innerHTML=paths.join('');
    $('#edges').setAttribute('viewBox',`0 0 ${map.width} ${map.height}`);
  }
  $('#trace').addEventListener('change', event => {
    selected=event.target.value;
    if (!selected || selected === compared) compared='';
    saveLocation();update();
  });
  $('#compare').addEventListener('change', event => {
    compared=event.target.value;
    if (compared && !selected) selected=routes.find(route => route.id!==compared).id;
    if (compared===selected) compared='';
    saveLocation();update();
  });
  $('#map-reset').addEventListener('click', () => { selected='';compared='';saveLocation();update(); });
  $('#close-explainer').addEventListener('click', () => dialog.close());
  dialog.addEventListener('close', () => {
    inspected=''; document.body.classList.remove('explainer-open'); saveLocation();update();
    if (returnFocus?.isConnected) returnFocus.focus({preventScroll:true});
  });
  dialog.addEventListener('click', event => {
    const rect=dialog.getBoundingClientRect();
    if (event.target===dialog && (event.clientX<rect.left || event.clientX>rect.right || event.clientY<rect.top || event.clientY>rect.bottom)) dialog.close();
  });
  document.addEventListener('click', event => {
    const button=event.target.closest('button[data-explainer]');
    if (button) openExplainer(button.dataset.explainer);
  });
  window.addEventListener('hashchange', () => {
    const id=location.hash.slice(1);
    if (byId.has(id)) openExplainer(id); else if (dialog.open) dialog.close();
  });
  new ResizeObserver(() => { cancelAnimationFrame(drawRequest); drawRequest=requestAnimationFrame(drawEdges); }).observe($('#map'));
  for (const id of ['trace','compare','map-reset']) $(`#${id}`).disabled=false;
  update();
  if (byId.has(initial.hash.slice(1))) openExplainer(initial.hash.slice(1));
  document.documentElement.dataset.ready='true';
}
start().catch(error => {
  console.error(error);
  $('#trace-description').textContent='The interactive map could not load. The comparison table and discrete blueprint links below remain available; reload to try again.';
  $('#trace-description').setAttribute('role','alert');
  document.documentElement.dataset.ready='error';
});
