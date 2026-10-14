// Section links share one continuous page with the numerical construction.
const links = [...document.querySelectorAll('.path-nav a[href^="#"]')];
const sections = links.map(link => document.querySelector(link.getAttribute('href'))).filter(Boolean);
function markSection() {
  const section = [...sections].reverse().find(item => item.getBoundingClientRect().top <= 150) || sections[0];
  for (const link of links) {
    if (link.hash === `#${section?.id}`) link.setAttribute('aria-current', 'location');
    else link.removeAttribute('aria-current');
  }
}
if (sections.length) {
  window.addEventListener('scroll', markSection, {passive:true});
  window.addEventListener('resize', markSection);
  markSection();
}
