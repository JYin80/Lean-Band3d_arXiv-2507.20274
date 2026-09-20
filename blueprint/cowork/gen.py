# Layered DAG -> SVG. Nodes are placed on explicit rows; x is distributed per row.
import math, html

W_PAD = 14
ROW_H = 64
CHAR_W = 6.15
NODE_H = 27

# kind -> (fill, stroke, textfill)  [light theme; dark handled via CSS vars on a wrapper]
KIND = {
  "def":   ("#cfe9dc", "#7cbfa4", "#123a2b"),   # definition, compiled
  "done":  ("#1a8a5e", "#13704b", "#ffffff"),   # proved and compiled
  "ready": ("#3d74ad", "#2d5a8a", "#ffffff"),   # dependencies met, can start now
  "todo":  ("#ffffff", "#b9c1c9", "#5d6873"),   # blocked / not started
  "axiom": ("#fbf1de", "#cda85f", "#6d5016"),   # interface axiom, borrowed
  "star":  ("#146b4a", "#0e5237", "#ffffff"),   # the high-value node, done
}

def esc(s): return html.escape(s, quote=True)

def textw(label):
    """Approximate rendered width at font-size 11.3. CJK glyphs are full-width, so they
    count about double an ASCII character -- estimating them as ASCII is what made nodes
    narrower than their own text and let neighbouring labels collide."""
    return sum(2.0 if ord(c) > 0x2E80 else 1.0 for c in label) * CHAR_W

def build(nodes, edges, width, band=None, band_label=""):
    """nodes: list of (id, label, kind, row). edges: list of (src,dst) or (src,dst,'dash')."""
    rows = {}
    for n in nodes: rows.setdefault(n[3], []).append(n)
    nrows = max(rows) + 1
    H = nrows * ROW_H + 24
    # Widen the canvas to the widest row rather than letting a crowded row overlap.
    GAP = 26
    need = max((sum(textw(i[1]) + 26 for i in items) + GAP * (len(items) - 1)
                for items in rows.values()), default=0)
    width = max(width, int(need) + 2 * W_PAD)
    pos = {}
    for r, items in rows.items():
        widths = [textw(i[1]) + 26 for i in items]
        total = sum(widths) + GAP * (len(items) - 1)
        x = (width - total) / 2
        for (nid, label, kind, _), w in zip(items, widths):
            pos[nid] = (x + w / 2, 22 + r * ROW_H, w)
            x += w + GAP
    out = []
    out.append(f'<svg class="dep" viewBox="0 0 {width} {H}" role="img" '
               f'preserveAspectRatio="xMidYMin meet" xmlns="http://www.w3.org/2000/svg">')
    out.append('<defs><marker id="ah" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" '
               'markerHeight="6" orient="auto-start-reverse">'
               '<path d="M0,1 L7,4 L0,7 z" fill="var(--edge)"/></marker></defs>')
    if band is not None:
        # `band` = how many TOP rows form the interface strip. The strip runs from the top
        # of the drawing to just below row `band-1`, so the label sits on the borrowed
        # results themselves rather than on everything else.
        y = 22 + (band - 1) * ROW_H + NODE_H/2 + (ROW_H - NODE_H)/2
        out.append(f'<rect x="0" y="0" width="{width}" height="{y:.1f}" fill="var(--axband)"/>')
        out.append(f'<line x1="0" y1="{y:.1f}" x2="{width}" y2="{y:.1f}" stroke="var(--axline)" '
                   f'stroke-width="1.2" stroke-dasharray="6 4"/>')
        out.append(f'<text x="{width-8}" y="{y-7:.1f}" text-anchor="end" font-size="10.5" '
                   f'letter-spacing="0.09em" fill="var(--axtext)">{esc(band_label)}</text>')
    for e in edges:
        s, d = e[0], e[1]
        dash = ' stroke-dasharray="5 3"' if len(e) > 2 else ''
        (x1, y1, w1), (x2, y2, w2) = pos[s], pos[d]
        y1b, y2t = y1 + NODE_H/2, y2 - NODE_H/2
        my = (y1b + y2t) / 2
        out.append(f'<path d="M{x1:.1f},{y1b:.1f} C{x1:.1f},{my:.1f} {x2:.1f},{my:.1f} {x2:.1f},{y2t:.1f}" '
                   f'fill="none" stroke="var(--edge)" stroke-width="1.15"{dash} marker-end="url(#ah)"/>')
    for nid, label, kind, r in nodes:
        x, y, w = pos[nid]
        fill, stroke, tf = KIND[kind]
        rx = 13 if kind in ("draft", "ready", "star") else 6
        cls = f"n-{kind}"
        out.append(f'<g class="{cls}"><rect x="{x-w/2:.1f}" y="{y-NODE_H/2:.1f}" width="{w:.1f}" '
                   f'height="{NODE_H}" rx="{rx}" fill="{fill}" stroke="{stroke}" stroke-width="1.3"/>'
                   f'<text x="{x:.1f}" y="{y+3.9:.1f}" text-anchor="middle" font-size="11.3" '
                   f'fill="{tf}">{esc(label)}</text></g>')
    out.append('</svg>')
    return "\n".join(out)
