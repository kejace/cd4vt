const $=selector=>document.querySelector(selector);
// 24 saturated hues, 105° apart so neighbouring vertices contrast.
const colors=Array.from({length:24},(_,i)=>`hsl(${i*105%360} 85% 36%)`);
const fmt=x=>Number.isFinite(x)?Number(x.toPrecision(7)).toString():'—';
const state={k:[],solution:null,display:null,ready:false,busy:false,pending:null,revision:0,seed:17,fit:false,drag:null,range:null,selected:-1,current:false,status:'loading',message:'Loading the numerical engine…'};
let paintRequest=0,dispatchRequest=0;
const worker=new Worker(new URL('./worker.js',import.meta.url),{type:'module'});

function admissibility(k){
  if(k.some(x=>!Number.isFinite(x)||x<=0))return {valid:false,message:'Every curvature reading must be positive.'};
  if(k.length<4||k.length>24)return {valid:false,message:'Choose between 4 and 24 readings.'};
  const max=Math.max(...k),min=Math.min(...k);
  if(min<1e-6||max>1e6||max/min>10000)return {valid:false,message:'This numerical solver supports readings from 10⁻⁶ to 10⁶, with a maximum ratio of 10,000.'};
  if(k.every(x=>x===k[0]))return {valid:true,constant:true,message:'Constant positive profile · the regular-polygon case.'};
  const values=[...new Set(k)].sort((a,b)=>a-b);
  for(let j=0;j<values.length-1;j++){
    const c=(values[j]+values[j+1])/2;
    const crossing=k.map((x,i)=>(x>c)!==(k[(i+k.length-1)%k.length]>c)?i:-1).filter(i=>i>=0);
    if(crossing.length>=4){
      const offset=crossing.findIndex(i=>k[i]>c);
      const witness=Array.from({length:4},(_,j)=>crossing[(offset+j)%crossing.length]);
      return {valid:true,c,witness,message:`DFV holds · readings ${witness.join(', ')} alternate above and below c = ${fmt(c)}.`};
    }
  }
  return {valid:false,message:'No strict four-vertex window. Restore two alternating high and low readings, or use a constant profile.'};
}
function setStatus(status,message){state.status=status;state.message=message;paint();}
function queueSolve(cold=false){
  state.revision++;state.current=false;
  const check=admissibility(state.k);
  if(!check.valid){state.pending=null;setStatus('invalid',check.message);return;}
  state.pending={id:state.revision,k:state.k.slice(),cold};
  setStatus(state.ready?'solving':'loading',state.ready?'Checking the current profile…':'Loading the numerical engine…');
  scheduleDispatch();
}
function scheduleDispatch(){
  if(dispatchRequest)return;
  dispatchRequest=requestAnimationFrame(()=>{dispatchRequest=0;dispatch();});
}
function dispatch(){
  if(!state.ready||state.busy||!state.pending)return;
  const request=state.pending;state.pending=null;
  const previous=!request.cold&&state.solution?.k.length===request.k.length?state.solution:null;
  state.busy=true;
  worker.postMessage({type:'solve',id:request.id,k:request.k,previous:previous?{k:previous.k,lengths:previous.lengths}:null,seed:state.seed,mode:previous?1:0});
}
worker.onmessage=({data})=>{
  if(data.type==='ready'){
    state.ready=true;$('#engine-badge').textContent='WASM · ready';$('#new-realization').disabled=false;
    document.documentElement.dataset.ready='true';scheduleDispatch();return;
  }
  if(data.type==='fatal'){
    state.ready=false;state.busy=false;$('#engine-badge').textContent='Engine unavailable';
    document.documentElement.dataset.ready='error';setStatus('failed','The numerical engine could not load. Reload the page to try again.');return;
  }
  if(data.type!=='result')return;
  state.busy=false;
  if(data.status===1&&data.k.length===state.k.length)state.solution=data;
  if(data.id===state.revision){
    if(data.status===1){
      state.display=data;state.current=true;
      const method=data.metrics.method===1?'Regular polygon':data.metrics.method===2?'Four-edge anchor opened':'Current branch continued';
      setStatus('valid',`${method} · numerical checks passed · ${data.milliseconds.toFixed(2)} ms`);
    }else if(data.status===-4){
      setStatus('branch','The current branch could not be continued. The faded polygon belongs to the previous profile. Choose “Find a new realization” to restart here.');
    }else if(data.status===-3){setStatus('invalid','This profile is outside the positive DFV hypothesis.');}
    else if(data.status===-2){setStatus('invalid','The readings exceed the numerical range of this prototype.');}
    else {setStatus('failed','The bounded search did not find a checked polygon. Try “Find a new realization” for another starting point, or adjust the profile. This is not a nonexistence result.');}
  }
  scheduleDispatch();paint();
};
worker.onerror=()=>{state.ready=false;state.busy=false;setStatus('failed','The numerical worker stopped. Reload to restart the engine.');};

function makeProfile(n,preset){
  if(preset==='obstruction')return [14,11,10,5,7,3];
  if(preset==='constant')return Array(n).fill(3);
  if(preset==='repeated')return Array.from({length:n},(_,i)=>i===0||i===Math.floor(n/2)?4:1+.3*(i%3));
  if(preset==='runs')return [4,4,1,3,1,...Array(Math.max(0,n-5)).fill(1)].slice(0,n);
  const values=Array.from({length:n},(_,i)=>2.2+1.4*Math.cos(4*Math.PI*i/n)+.5*Math.sin(2*Math.PI*i/n+.3));
  return values.map(x=>preset==='near'?1+.001*x:Number(x.toFixed(3)));
}
function buildReadings(){
  $('#readings').innerHTML=state.k.map((k,i)=>`<label class="reading" data-reading="${i}"><span><i style="background:${colors[i]}"></i>κ${i}</span><input type="number" min="0.000001" max="1000000" step="any" inputmode="decimal" data-index="${i}" aria-label="Curvature at vertex ${i}" value="${fmt(k)}"></label>`).join('');
}
function loadPreset(){
  let n=Number($('#size').value),preset=$('#preset').value;
  if(preset==='obstruction'){n=6;$('#size').value='6';}
  if(preset==='runs'&&n<5){preset='varied';$('#preset').value=preset;}
  state.k=makeProfile(n,preset);state.solution=null;state.display=null;state.current=false;state.seed=17;
  state.fit=preset==='near';state.range=null;state.drag=null;state.selected=-1;
  $('#path-control').hidden=preset!=='obstruction';$('#path-position').value='0';$('#path-value').textContent='s = 0.000';
  $('#preset option[value="runs"]').disabled=n<5;
  buildReadings();queueSolve(true);
}
function edit(k){state.k=k;queueSolve();}
$('#size').addEventListener('change',()=>{if($('#preset').value==='obstruction')$('#preset').value='varied';loadPreset();});
$('#preset').addEventListener('change',loadPreset);
$('#reset').addEventListener('click',loadPreset);
$('#new-realization').addEventListener('click',()=>{state.seed++;queueSolve(true);});
$('#path-position').addEventListener('input',event=>{
  const s=Number(event.target.value);$('#path-value').textContent=`s = ${s.toFixed(3)}`;
  edit([14,11,10+3*s,5,7-3*s,3]);
});
$('#readings').addEventListener('input',event=>{
  const i=Number(event.target.dataset.index);
  if(!Number.isInteger(i))return;
  const k=state.k.slice();k[i]=event.target.value===''?NaN:Number(event.target.value);
  if($('#preset').value==='obstruction')$('#path-control').hidden=true;
  edit(k);
});
$('#readings').addEventListener('focusin',event=>{if(event.target.dataset.index!==undefined){state.selected=Number(event.target.dataset.index);paint();}});
$('#show-circles').addEventListener('change',paint);
$('#zoom-profile').addEventListener('click',()=>{state.fit=!state.fit;state.range=null;paint();});
$('#apply-profile').addEventListener('click',()=>{
  const tokens=$('#profile-text').value.trim().split(/[\s,;]+/).filter(Boolean),k=tokens.map(Number);
  if(k.length<4||k.length>24||k.some(x=>!Number.isFinite(x)||x<=0)){$('#paste-error').textContent='Enter 4–24 positive numbers.';return;}
  $('#paste-error').textContent='';$('#size').value=String(k.length);$('#path-control').hidden=true;
  state.k=k;state.solution=null;state.display=null;state.range=null;state.fit=false;state.seed=17;state.selected=-1;
  buildReadings();queueSolve(true);
});
function bounds(){
  if(state.drag&&state.range)return state.range;
  const finite=state.k.filter(x=>Number.isFinite(x)&&x>0),max=Math.max(1e-6,...finite),min=Math.min(max,...finite);
  if(state.fit){const padding=Math.max((max-min)*.2,max*.08);state.range=[0,max+padding];}
  else {const top=max*1.22,unit=10**Math.floor(Math.log10(top));state.range=[0,Math.ceil(top/unit*4)/4*unit];}
  return state.range;
}
const W=660,H=400,L=54,R=24,T=32,B=49;
function profilePoint(i,k){const [lo,hi]=state.range;return [L+(W-L-R)*i/state.k.length,T+(H-T-B)*(hi-k)/(hi-lo)];}
function renderProfile(){
  bounds();const n=state.k.length,[lo,hi]=state.range,check=admissibility(state.k);
  const oldFocus=document.activeElement?.classList.contains('profile-point')?Number(document.activeElement.dataset.index):null;
  const parts=[];
  for(let i=0;i<=4;i++){
    const value=lo+(hi-lo)*i/4,y=profilePoint(0,value)[1];
    parts.push(`<line class="grid-line${value===0?' zero-line':''}" x1="${L}" x2="${W-R}" y1="${y}" y2="${y}"/><text class="tick-label" text-anchor="end" x="${L-9}" y="${y+4}">${Number(value.toPrecision(4))}</text>`);
  }
  parts.push(`<text class="axis-label" x="${L}" y="17">κ${state.fit?' · fitted':''}</text>`);
  if(check.c){const y=profilePoint(0,check.c)[1];parts.push(`<line class="witness-line" x1="${L}" x2="${W-R}" y1="${y}" y2="${y}"/>`);}
  const positions=state.k.map((k,i)=>profilePoint(i,Number.isFinite(k)?k:lo));
  const baseline=profilePoint(0,0)[1];
  const wrap=profilePoint(n,Number.isFinite(state.k[0])?state.k[0]:lo);
  parts.push(`<line class="profile-stem wrap-stem" x1="${wrap[0]}" y1="${baseline}" x2="${wrap[0]}" y2="${wrap[1]}" stroke="${colors[0]}"/><circle cx="${wrap[0]}" cy="${wrap[1]}" r="4" fill="white" stroke="${colors[0]}"/>`);
  for(let i=0;i<n;i++){
    const [x,y]=positions[i];
    parts.push(`<line class="profile-stem" data-index="${i}" x1="${x}" y1="${baseline}" x2="${x}" y2="${y}" stroke="${colors[i]}"/>`);
    if(check.witness?.includes(i))parts.push(`<circle class="point-ring" cx="${x}" cy="${y}" r="11" stroke="${colors[i]}"/>`);
    if(state.selected===i)parts.push(`<circle class="highlight-ring" cx="${x}" cy="${y}" r="14"/>`);
    parts.push(`<text class="tick-label" text-anchor="middle" x="${x}" y="${H-B+23}">${i}</text><text class="value-label" text-anchor="middle" x="${x}" y="${y-18}">${Number.isFinite(state.k[i])?Number(state.k[i].toPrecision(state.fit?6:4)):'—'}</text><circle class="profile-point" data-index="${i}" tabindex="0" role="slider" aria-label="Curvature at vertex ${i}" aria-valuemin="0.000001" aria-valuemax="1000000" aria-valuenow="${Number.isFinite(state.k[i])?state.k[i]:0}" aria-valuetext="${fmt(state.k[i])}" cx="${x}" cy="${y}" r="7" fill="${colors[i]}"><title>κ${i} = ${fmt(state.k[i])} · drag vertically</title></circle>`);
  }
  parts.push(`<text class="tick-label" text-anchor="middle" x="${wrap[0]}" y="${H-B+23}">0 ↻</text>`);
  $('#profile').innerHTML=parts.join('');
  if(oldFocus!==null)$(`#profile .profile-point[data-index="${oldFocus}"]`)?.focus({preventScroll:true});
  $('#dfv-status').textContent=check.message;
  $('#zoom-profile').setAttribute('aria-pressed',String(state.fit));
  $('#zoom-profile').textContent=state.fit?'More headroom':'Fit values';
}
// Circumcircle through three displayed vertices. Translating to the middle
// vertex keeps the determinant stable; the plot uses a uniform Euclidean scale.
function mengerCircle(previous,vertex,next){
  const ux=previous[0]-vertex[0],uy=previous[1]-vertex[1];
  const vx=next[0]-vertex[0],vy=next[1]-vertex[1];
  const u2=ux*ux+uy*uy,v2=vx*vx+vy*vy,d=2*(ux*vy-uy*vx);
  const dx=(u2*vy-v2*uy)/d,dy=(ux*v2-vx*u2)/d;
  return {cx:vertex[0]+dx,cy:vertex[1]+dy,r:Math.hypot(dx,dy)};
}
function renderPolygon(){
  const solution=state.display;
  $('#polygon-empty').hidden=Boolean(solution);
  $('#polygon').classList.toggle('ghost',!state.current);
  if(!solution){$('#polygon').innerHTML='';$('#polygon-caption').textContent='Waiting for a checked realization.';return;}
  const vertices=solution.vertices,n=vertices.length,xs=vertices.map(p=>p[0]),ys=vertices.map(p=>p[1]);
  const minx=Math.min(...xs),maxx=Math.max(...xs),miny=Math.min(...ys),maxy=Math.max(...ys);
  const scale=Math.min((W-140)/(maxx-minx),(H-115)/(maxy-miny));
  const xy=vertices.map(([x,y])=>[W/2+(x-(minx+maxx)/2)*scale,H/2-(y-(miny+maxy)/2)*scale]);
  const center=[xy.reduce((s,p)=>s+p[0],0)/n,xy.reduce((s,p)=>s+p[1],0)/n];
  const labels=xy.map(([x,y])=>{const dx=x-center[0],dy=y-center[1],r=Math.hypot(dx,dy)||1;return [x+26*dx/r,y+26*dy/r];});
  for(let pass=0;pass<30;pass++)for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    let dx=labels[i][0]-labels[j][0],dy=labels[i][1]-labels[j][1],r=Math.hypot(dx,dy);
    if(r<23){if(r<1e-8){dx=1;dy=0;r=1;}const shift=(23-r)/2;labels[i][0]+=dx/r*shift;labels[i][1]+=dy/r*shift;labels[j][0]-=dx/r*shift;labels[j][1]-=dy/r*shift;}
  }
  const parts=[`<defs><clipPath id="circle-view"><rect x="18" y="18" width="${W-36}" height="${H-36}"/></clipPath></defs>`];
  if($('#show-circles').checked){
    parts.push('<g class="menger-circles" clip-path="url(#circle-view)" aria-label="Menger circles through adjacent triples">');
    for(let i=0;i<n;i++){
      const {cx,cy,r}=mengerCircle(xy[(i+n-1)%n],xy[i],xy[(i+1)%n]);
      parts.push(`<circle class="menger-circle${state.selected===i?' selected':''}" data-index="${i}" cx="${cx}" cy="${cy}" r="${r}" stroke="${colors[i]}"><title>Menger circle ${i} · through vertices ${(i+n-1)%n}, ${i}, ${(i+1)%n} · radius ${fmt(r/scale)}</title></circle>`);
    }
    parts.push('</g>');
  }
  parts.push(`<polygon class="polygon-edge" points="${xy.map(p=>p.join(',')).join(' ')}"/>`);
  for(let i=0;i<n;i++){
    const [x,y]=xy[i],[lx,ly]=labels[i];
    parts.push(`<line class="leader" x1="${x}" y1="${y}" x2="${lx}" y2="${ly}"/><text class="vertex-label" text-anchor="middle" dominant-baseline="central" x="${lx}" y="${ly}">${i}</text>`);
    if(state.selected===i)parts.push(`<circle class="highlight-ring" cx="${x}" cy="${y}" r="11"/>`);
    parts.push(`<circle class="vertex-point" data-index="${i}" cx="${x}" cy="${y}" r="5" fill="${colors[i]}"><title>Vertex ${i} · κ = ${fmt(solution.k[i])} · outgoing length ${fmt(solution.lengths[i])}</title></circle>`);
  }
  $('#polygon').innerHTML=parts.join('');
  $('#polygon-caption').textContent=state.current?`Current profile · ${n} vertices · positive lengths and strict convexity checked.`:'Previous valid polygon — it does not realize the currently edited profile.';
}
function paint(){
  if(paintRequest)return;
  paintRequest=requestAnimationFrame(()=>{
    paintRequest=0;renderProfile();renderPolygon();
    $('#status').dataset.state=state.status;$('#status').textContent=state.message;
    document.documentElement.dataset.status=state.status;
    document.documentElement.dataset.current=String(state.current);
    $('#export').disabled=!state.current;
    for(const label of document.querySelectorAll('.reading')){
      const i=Number(label.dataset.reading),input=label.querySelector('input');
      label.classList.toggle('active',i===state.selected);
      if(document.activeElement!==input)input.value=Number.isFinite(state.k[i])?fmt(state.k[i]):'';
    }
    const metrics=state.current?state.display.metrics:null;
    $('#metric-wall').textContent=metrics?metrics.wall.toPrecision(3):'—';
  });
}
function valueAtPointer(event){
  const rect=$('#profile').getBoundingClientRect(),y=(event.clientY-rect.top)*H/rect.height;
  const [lo,hi]=state.range;
  return Number(Math.max(1e-6,Math.min(1e6,hi-(Math.max(T,Math.min(H-B,y))-T)/(H-T-B)*(hi-lo))).toPrecision(10));
}
$('#profile').addEventListener('pointerdown',event=>{
  const point=event.target.closest('.profile-point');if(!point)return;
  event.preventDefault();point.focus({preventScroll:true});state.selected=Number(point.dataset.index);
  state.drag={index:state.selected,pointer:event.pointerId};$('#profile').setPointerCapture(event.pointerId);paint();
});
$('#profile').addEventListener('pointermove',event=>{
  if(!state.drag)return;event.preventDefault();const k=state.k.slice();k[state.drag.index]=valueAtPointer(event);
  if($('#preset').value==='obstruction')$('#path-control').hidden=true;
  edit(k);
});
for(const type of ['pointerup','pointercancel'])$('#profile').addEventListener(type,event=>{
  if(!state.drag)return;state.drag=null;if($('#profile').hasPointerCapture(event.pointerId))$('#profile').releasePointerCapture(event.pointerId);state.range=null;paint();
});
$('#profile').addEventListener('keydown',event=>{
  const point=event.target.closest('.profile-point');if(!point||!['ArrowUp','ArrowDown','Home','End'].includes(event.key))return;
  event.preventDefault();const i=Number(point.dataset.index),[lo,hi]=state.range,k=state.k.slice(),step=(hi-lo)/(event.shiftKey?20:200);
  k[i]=Number(Math.max(1e-6,event.key==='Home'?Math.max(1e-6,lo):event.key==='End'?hi:k[i]+(event.key==='ArrowUp'?step:-step)).toPrecision(10));
  if($('#preset').value==='obstruction')$('#path-control').hidden=true;
  state.selected=i;edit(k);
});
$('#profile').addEventListener('focusin',event=>{if(event.target.dataset.index!==undefined){const i=Number(event.target.dataset.index);if(state.selected!==i){state.selected=i;paint();}}});
$('#polygon').addEventListener('pointerover',event=>{if(event.target.dataset.index!==undefined){state.selected=Number(event.target.dataset.index);paint();}});
$('#export').addEventListener('click',()=>{
  if(!state.current)return;
  const data={description:'Numerically checked coherent discrete realization; not a formal certificate.',k:state.display.k,lengths:state.display.lengths,vertices:state.display.vertices,metrics:state.display.metrics};
  const url=URL.createObjectURL(new Blob([JSON.stringify(data,null,2)+'\n'],{type:'application/json'}));
  const a=document.createElement('a');a.href=url;a.download='gluck-discrete-realization.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
});
loadPreset();
