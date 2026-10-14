#!/usr/bin/env python3
"""Check the actual WASM worker, interactive UI, navigation, and mobile layout."""
import argparse
import hashlib
import json
import math
from pathlib import Path
from playwright.sync_api import sync_playwright
from validate import ROOT, geometry, run_suite

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base', default='http://127.0.0.1:8788')
parser.add_argument('--report', type=Path)
parser.add_argument('--ui-only', action='store_true', help='Reuse a matching numerical report; run all UI checks.')
parser.add_argument('--cdp', help='Attach to a browser started outside the CAS virtual-address cap.')
args = parser.parse_args()
base = args.base.rstrip('/')
site = ROOT / 'site/discrete-playground'
metadata = json.loads((site / 'build.json').read_text())
assert hashlib.sha256((ROOT / metadata['source']).read_bytes()).hexdigest() == metadata['sha256']
for name, digest in metadata['artifacts'].items():
    assert hashlib.sha256((site / name).read_bytes()).hexdigest() == digest

with sync_playwright() as p:
    browser = p.chromium.connect_over_cdp(args.cdp) if args.cdp else p.chromium.launch()
    page = browser.new_page(viewport={'width':1440, 'height':1080}, accept_downloads=True)
    errors, failures = [], []
    page.on('pageerror', lambda e: errors.append(str(e)))
    page.on('requestfailed', lambda r: failures.append([r.url, r.failure]))
    page.goto(base + '/web/discrete-playground/', wait_until='networkidle')

    def settle(expected='valid'):
        page.evaluate('() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))')
        page.wait_for_function("['valid','invalid','branch','failed'].includes(document.documentElement.dataset.status)", timeout=20000)
        status = page.locator('html').get_attribute('data-status')
        if expected:
            assert status == expected, page.locator('#status').inner_text()
        return status

    def exported():
        # Chromium throttles rapid batches of downloads; this is a UI check.
        page.wait_for_timeout(150)
        with page.expect_download() as download:
            page.click('#export')
        data = json.loads(Path(download.value.path()).read_text())
        geometry(data['k'], data['lengths'], data['vertices'])
        drawing = page.locator('#polygon').evaluate("""svg => ({
          points:[...svg.querySelectorAll('.vertex-point')].map(p=>[+p.getAttribute('cx'),+p.getAttribute('cy')]),
          circles:[...svg.querySelectorAll('.menger-circle')].map(p=>[+p.getAttribute('cx'),+p.getAttribute('cy'),+p.getAttribute('r')]),
          clip:svg.querySelector('.menger-circles')?.getAttribute('clip-path')
        })""")
        assert drawing['clip'] == 'url(#circle-view)'
        n=len(data['k'])
        assert len(drawing['circles']) == n
        scale=math.dist(*drawing['points'][:2])/data['lengths'][0]
        for i,(cx,cy,radius) in enumerate(drawing['circles']):
            assert abs(radius*data['k'][i]/scale-1) < 2e-6
            for j in [(i-1)%n,i,(i+1)%n]:
                assert abs(math.dist([cx,cy],drawing['points'][j])/radius-1) < 1e-8
        return data

    settle()
    page.evaluate('''async () => {
      const worker = new Worker('/web/discrete-playground/worker.js', {type:'module'});
      await new Promise((resolve,reject) => {worker.onmessage=({data})=>data.type==='ready'?resolve():reject(data); worker.onerror=reject;});
      let serial=0;
      window.testSolve = request => new Promise(resolve => {
        worker.onmessage=({data})=>resolve(data);
        worker.postMessage({type:'solve',id:++serial,mode:request.previous?1:0,...request});
      });
    }''')
    def solve(k, previous=None, seed=17):
        return page.evaluate('request => window.testSolve(request)', dict(k=k, previous=previous, seed=seed))
    if args.ui_only:
        assert args.report and args.report.is_file(), 'UI-only needs an existing numerical report.'
        report = json.loads(args.report.read_text())
        assert report['source_sha256'] == metadata['sha256']
        assert report['wasm_sha256'] == metadata['artifacts']['solver.wasm']
    else:
        report = run_suite(solve)
    report['backend'] = 'WebAssembly in Chromium worker'
    report['browser'] = browser.version
    report['wasm_sha256'] = metadata['artifacts']['solver.wasm']

    # Every shipped preset and supported size.
    preset_count = 0
    for n in range(4, 12):
        page.select_option('#size', str(n)); settle()
        for kind in ['varied', 'repeated', 'runs', 'near', 'constant']:
            if n == 4 and kind == 'runs':
                continue
            page.select_option('#preset', kind); settle()
            assert page.locator('#polygon .vertex-point').count() == n
            data = exported()
            assert len(data['k']) == n
            preset_count += 1
        print(f'UI presets n={n}: checked.', flush=True)
    page.select_option('#size', '8'); settle()
    page.select_option('#preset', 'varied'); settle()
    before = exported()
    polygon_before = page.locator('#polygon .polygon-edge').get_attribute('points')
    page.uncheck('#show-circles'); settle()
    assert page.locator('#polygon .menger-circle').count() == 0
    assert page.locator('#polygon .polygon-edge').get_attribute('points') == polygon_before
    page.check('#show-circles'); settle()
    assert page.locator('#polygon .polygon-edge').get_attribute('points') == polygon_before
    point = page.locator('#profile .profile-point[data-index="0"]')
    rect = point.bounding_box()
    page.mouse.move(rect['x'] + rect['width']/2, rect['y'] + rect['height']/2)
    page.mouse.down(); page.mouse.move(rect['x'] + rect['width']/2, rect['y'] + rect['height']/2 + 12, steps=12); page.mouse.up()
    settle(); after = exported()
    assert after['k'][0] != before['k'][0]
    assert max(abs(a-b) for a,b in zip(after['lengths'], before['lengths'])) > 1e-7
    point.focus(); page.keyboard.press('ArrowUp'); settle()
    assert exported()['k'][0] > after['k'][0]
    page.locator('#readings input').first.fill('0'); settle('invalid')
    assert page.locator('#polygon.ghost').count() == 1 and page.locator('#export').is_disabled()
    assert page.locator('#metric-closure').inner_text() == '—'
    assert 'Previous valid' in page.locator('#polygon-caption').inner_text()
    page.locator('#readings input').first.fill(str(after['k'][0])); settle()
    page.click('.paste summary')
    page.fill('#profile-text', '1, 2, 3, 4'); page.click('#apply-profile'); settle('invalid')
    page.fill('#profile-text', '5, 2, 3.5, 1.5, 4, 1'); page.click('#apply-profile'); settle()
    assert exported()['k'] == [5, 2, 3.5, 1.5, 4, 1]
    page.click('.paste summary')
    # Latest-request scheduling: many valid edits, then a final invalid one.
    page.evaluate('''() => {const input=document.querySelector('#readings input');for(let i=0;i<80;i++){input.value=5+i*.002;input.dispatchEvent(new Event('input',{bubbles:true}));}input.value='0';input.dispatchEvent(new Event('input',{bubbles:true}));}''')
    settle('invalid'); page.wait_for_timeout(200)
    assert page.locator('html').get_attribute('data-current') == 'false'
    page.evaluate('''() => {const input=document.querySelector('#readings input');for(let i=0;i<80;i++){input.value=5+i*.002;input.dispatchEvent(new Event('input',{bubbles:true}));}}''')
    settle(); assert abs(exported()['k'][0] - 5.158) < 1e-12
    # Follow the exposed obstruction path using the real UI. No automatic restart.
    page.select_option('#preset', 'obstruction'); settle()
    ui_stop = None
    for step in range(1, 101):
        s = step / 100
        page.locator('#path-position').evaluate('(el,s)=>{el.value=s;el.dispatchEvent(new Event("input",{bubbles:true}));}', s)
        status = settle(None)
        if status == 'branch':
            ui_stop = s
            break
        assert status == 'valid', page.locator('#status').inner_text()
    assert ui_stop is not None
    assert page.locator('#export').is_disabled() and page.locator('#polygon.ghost').count() == 1
    page.click('#new-realization'); settle()
    assert abs(exported()['k'][2] - (10 + 3 * ui_stop)) < 1e-12
    page.select_option('#preset', 'varied'); settle()
    page.select_option('#size', '8'); settle()
    page.screenshot(path='/tmp/discrete-playground-desktop.png', full_page=True)
    for width in [390, 320]:
        page.set_viewport_size({'width':width, 'height':844})
        page.evaluate('() => new Promise(resolve=>requestAnimationFrame(resolve))')
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth'), width
    page.set_viewport_size({'width':390, 'height':844})
    page.screenshot(path='/tmp/discrete-playground-mobile.png', full_page=True)
    # Engine loading failure must show a usable failure state.
    blocked = browser.new_page()
    blocked.route('**/solver.wasm', lambda route: route.abort())
    blocked.goto(base + '/web/discrete-playground/')
    blocked.wait_for_selector('html[data-ready="error"]')
    assert blocked.locator('#export').is_disabled()
    blocked.close()
    # Verify page links, including the documentation and checked build metadata.
    for href in page.locator('a[href]').evaluate_all('(as)=>as.map(a=>a.href)'):
        if href.startswith(base):
            response = page.request.get(href)
            assert response.ok, (href, response.status)
    for route in ['/', '/docs', '/inv', '/viz', '/illustrations', '/moduli', '/coverage', '/blueprint/']:
        response = page.request.get(base + route)
        assert response.ok and '/web/discrete-playground/' in response.text(), route
    assert not errors and not failures, (errors, failures)
    report['ui'] = dict(presets=preset_count, pointer_drag=True, keyboard=True, numeric_edit=True,
                        menger_circles_through_triples=True, clipped_circles=True, unchanged_polygon_view=True,
                        independent_export_checks=True, invalid_profile=True, latest_request=True,
                        obstruction_stop=ui_stop, explicit_reseed=True, engine_failure=True,
                        responsive_widths=[390, 320], navigation_routes=8, page_errors=errors, request_failures=failures)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print('UI checks:', json.dumps(report['ui']))
    print('WASM cold timing:', json.dumps(report['cold_timing']))
    print('WASM continuation:', json.dumps(report['continuation']))
    browser.close()
