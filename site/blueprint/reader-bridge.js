// The native blueprint uses a plasTeX-only figure macro. The preview builder
// expands it to a standard link plus its original caption in the snapshot.
// Upgrade those links to images without modifying hgraph's bundled renderer.
const response = await fetch('./figures.json');
if (!response.ok) throw new Error(`Cannot load figure metadata: ${response.status}`);
const figures = await response.json();
let queued = false;
function decorateFigures() {
  queued = false;
  document.querySelectorAll('a.tex-link[href^="../figures/"]:not([data-preview-figure])').forEach((link) => {
    const name = link.getAttribute('href').split('/').pop().replace(/\.svg$/, '');
    if (!figures[name]) return;
    const image = new Image();
    image.src = link.getAttribute('href');
    image.alt = figures[name].alt;
    image.loading = 'lazy';
    link.dataset.previewFigure = name;
    link.id = figures[name].label;
    link.replaceChildren(image);
    link.title = 'Open the full illustration';
  });
}
new MutationObserver(() => {
  if (!queued) { queued = true; requestAnimationFrame(decorateFigures); }
}).observe(document.body, {childList:true, subtree:true});
decorateFigures();
