#!/usr/bin/env python3
"""Writes square-antiprism.svg: the Coulomb minimizer for eight points, rotating about its axis.

    python3 Visualization/make_svg.py

The picture is an animated SVG without scripts. The configuration is mapped to itself by a rotation
of 90 degrees about its axis, so the animation only stores a turn of 90 degrees and repeats it: every
point then stands where its neighbour stood, and the picture is the same. Between the stored
positions the browser interpolates. The program uses the standard library of Python only.
"""
import math
import os

# ---- the configuration ----------------------------------------------------------------------------
SQ2 = math.sqrt(2)


def stationarity(a):
    """The function `F(1, a)` of the paper, whose zero in (0, 1) is the squared height for `s = 1`."""
    d_a, d_b = 2 * (1 - a), 4 * (1 - a)
    d_c, d_d = 2 - SQ2 + (2 + SQ2) * a, 2 + SQ2 + (2 - SQ2) * a
    return 16 * d_a ** -1.5 + 16 * d_b ** -1.5 - 8 * (2 + SQ2) * d_c ** -1.5 - 8 * (2 - SQ2) * d_d ** -1.5


def solve():
    lo, hi = 0.1, 0.6
    assert stationarity(lo) * stationarity(hi) < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if stationarity(lo) * stationarity(mid) > 0 else (lo, mid)
    return (lo + hi) / 2


A1 = solve()                             # the squared height for the Coulomb energy
H = math.sqrt(A1)
R_RING = math.sqrt(1 - A1)

UP = [k for k in range(4)]              # the square at height h
LOW = [4 + k for k in range(4)]         # the square at height -h, rotated by 45 degrees
N = 8
FOLD = 4                                 # a rotation by 360 / FOLD degrees maps the configuration to itself


def vertices(theta):
    """The eight points after a rotation by `theta` about the axis."""
    pts = []
    for k in range(4):
        a = theta + k * math.pi / 2
        pts.append((R_RING * math.cos(a), R_RING * math.sin(a), H))
    for k in range(4):
        a = theta + k * math.pi / 2 + math.pi / 4
        pts.append((R_RING * math.cos(a), R_RING * math.sin(a), -H))
    return pts


def coulomb(pts):
    return sum(1 / math.dist(pts[i], pts[j]) for i in range(len(pts)) for j in range(i + 1, len(pts)))


# the numbers that the README states
assert abs(A1 - 0.314089367889) < 1e-11 and abs(coulomb(vertices(0.0)) - 19.675287861233) < 1e-11
ENERGY = f"{coulomb(vertices(0.0)):.3f}"

FACES = [tuple(UP), tuple(reversed(LOW))]   # the two squares and the eight triangles, outward orientation
for k in range(4):
    u0, u1, l0, l1 = UP[k], UP[(k + 1) % 4], LOW[k], LOW[(k + 1) % 4]
    FACES += [(u0, l0, u1), (u1, l0, l1)]

EDGES = []                               # (i, j, kind): the 16 edges
for k in range(4):
    u0, u1, l0, l1 = UP[k], UP[(k + 1) % 4], LOW[k], LOW[(k + 1) % 4]
    EDGES += [(u0, u1, "up"), (l0, l1, "low"), (u0, l0, "side"), (u1, l0, "side")]

# ---- the picture ----------------------------------------------------------------------------------
W, HEIGHT = 840, 440
CX, CY, RAD = 228, 212, 160              # the centre and the radius of the sphere in the picture
DIST = 6.0                               # the distance of the camera from the centre
ELEV = math.radians(19)                  # its elevation
START = math.radians(17)                 # the rotation of the first picture
BALL = 0.058                             # the radius of a point, in units of the sphere
STEPS = 18                               # stored positions per 90 degrees: every 5 degrees
DUR = "10.5s"                            # the time of a turn of 90 degrees

PAGE, INK, INK2, MUTED = "#f9f9f7", "#0b0b0b", "#52514e", "#6f6e69"
BLUE, GREEN = "#2a78d6", "#149a6b"
EDGE, FACE, TINT, RIM = "#6f6e68", "#6a7f9e", "#8794a8", "#5b6b84"
COLOR = {**{i: BLUE for i in UP}, **{i: GREEN for i in LOW}}
GRAD = {BLUE: "b", GREEN: "g"}

FOCAL = RAD * math.sqrt(DIST * DIST - 1)                     # the sphere has the radius RAD
CAM = (math.cos(ELEV), 0.0, math.sin(ELEV))                  # the direction to the camera
RIGHT = (0.0, 1.0, 0.0)
UPV = (-math.sin(ELEV), 0.0, math.cos(ELEV))
LIGHT = (0.45, -0.55, 0.70)                                  # the direction to the light
LIGHT = tuple(c / math.sqrt(sum(x * x for x in LIGHT)) for c in LIGHT)


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def unit(a):
    n = math.sqrt(dot(a, a))
    return (a[0] / n, a[1] / n, a[2] / n)


def smooth(x, lo, hi):
    t = min(1.0, max(0.0, (x - lo) / (hi - lo)))
    return t * t * (3 - 2 * t)


def project(p):
    """The place of a point in the picture, and the scale of lengths at this point."""
    s = FOCAL / (DIST - dot(p, CAM))
    return CX + s * dot(p, RIGHT), CY - s * dot(p, UPV), s


def frame(theta):
    """Everything that the picture shows for one rotation."""
    pts = vertices(theta)
    eye = tuple(DIST * c for c in CAM)
    xy = [project(p) for p in pts]
    # a point is in front if it lies on the side of the sphere that the camera sees
    front = [smooth(dot(p, CAM) - 1 / DIST, -0.035, 0.035) for p in pts]
    facing, shade = [], []
    for face in FACES:
        a, b, c = face[:3]
        n = unit(cross(sub(pts[b], pts[a]), sub(pts[c], pts[a])))
        assert all(dot(n, sub(q, pts[a])) < 1e-9 for q in pts), "the faces are not the convex hull"
        centre = tuple(sum(pts[i][k] for i in face) / len(face) for k in range(3))
        facing.append(dot(n, unit(sub(eye, centre))))
        shade.append(max(0.0, dot(n, LIGHT)))
    return pts, xy, front, facing, shade


FRAMES = [frame(START + j * (2 * math.pi / FOLD) / STEPS) for j in range(STEPS + 1)]


def num(x, digits=1):
    s = f"{x:.{digits}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def animate(attr, values):
    """An attribute with its first value, and the animation if the value changes."""
    if all(v == values[0] for v in values):
        return f' {attr}="{values[0]}"', ""
    return (f' {attr}="{values[0]}"',
            f'<animate attributeName="{attr}" dur="{DUR}" repeatCount="indefinite" values="{";".join(values)}"/>')


def element(tag, static, animated):
    attrs, anims = "", ""
    for attr, values in animated:
        a, b = animate(attr, values)
        attrs += a
        anims += b
    return f"<{tag}{static}{attrs}>{anims}</{tag}>" if anims else f"<{tag}{static}{attrs}/>"


def mix(color, other, t):
    a = [int(color[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(other[i:i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{round(x + (y - x) * t):02x}" for x, y in zip(a, b))


def faces():
    out = []
    for f, face in enumerate(FACES):
        pts = [" ".join(f"{num(fr[1][i][0])},{num(fr[1][i][1])}" for i in face) for fr in FRAMES]
        # a face that looks at the camera is shaded by the light, a face on the far side is faint
        op = [num(0.035 + smooth(fr[3][f], -0.04, 0.04) * (0.025 + 0.095 * fr[4][f]), 3) for fr in FRAMES]
        out.append(element("polygon", "", [("points", pts), ("fill-opacity", op)]))
    return out


def edges():
    out = []
    adjacent = {}
    for f, face in enumerate(FACES):
        for i in range(len(face)):
            adjacent.setdefault(frozenset((face[i], face[(i + 1) % len(face)])), []).append(f)
    for a, b, kind in EDGES:
        fa = adjacent[frozenset((a, b))]
        assert len(fa) == 2
        ds, ops = [], []
        for pts, xy, front, facing, shade in FRAMES:
            (x1, y1, s1), (x2, y2, s2) = xy[a], xy[b]
            # the edge ends at the surfaces of its two points
            length = math.hypot(x2 - x1, y2 - y1)
            ux, uy = (x2 - x1) / length, (y2 - y1) / length
            t1, t2 = BALL * s1 * 0.92, BALL * s2 * 0.92
            ds.append(f"M{num(x1 + ux * t1)} {num(y1 + uy * t1)}L{num(x2 - ux * t2)} {num(y2 - uy * t2)}")
            # an edge is in front if one of its two faces looks at the camera
            vis = smooth(max(facing[fa[0]], facing[fa[1]]), -0.04, 0.04)
            ops.append(num(0.22 + 0.7 * vis, 2))
        cls = {"up": ' class="u"', "low": ' class="l"', "side": ""}[kind]
        out.append(element("path", cls, [("d", ds), ("stroke-opacity", ops)]))
    return out


def points(layer):
    """The points of the far side (`layer` 0) or of the near side (`layer` 1).

    A point of the far side is drawn in a paler colour, as if seen through haze, and it is opaque. While
    a point passes the outline of the sphere, its near copy fades in over its far copy."""
    out = []
    for i in range(N):
        near = [fr[2][i] for fr in FRAMES]
        if layer:
            op = [num(v, 2) for v in near]
        else:
            op = ["1" if v < 0.98 else "0" for v in near]
        if all(v == "0" for v in op):
            continue
        cx = [num(fr[1][i][0]) for fr in FRAMES]
        cy = [num(fr[1][i][1]) for fr in FRAMES]
        r = [num(BALL * fr[1][i][2], 2) for fr in FRAMES]
        grad = GRAD[COLOR[i]] + ("" if layer else "f")
        out.append(element("circle", f' fill="url(#{grad})"', [("cx", cx), ("cy", cy), ("r", r), ("opacity", op)]))
    return out


HAZE = "#e7e8ea"                         # the colour towards which the far side fades


def gradient(name, color, haze=0.0):
    stops = [(0, mix(color, "#ffffff", 0.62)), (.45, color), (1, mix(color, "#000000", 0.38))]
    return (f'<radialGradient id="{name}" cx=".34" cy=".3" r=".8">'
            + "".join(f'<stop offset="{num(o, 2)}" stop-color="{mix(c, HAZE, haze)}"/>' for o, c in stops)
            + "</radialGradient>")


TX = 506                                 # the left edge of the text


def legend(y, color, text):
    return (f'<circle cx="{TX + 6}" cy="{y - 5}" r="5.5" fill="url(#{GRAD[color]})"/>'
            f'<text x="{TX + 23}" y="{y}">{text}</text>')


def check_loop():
    """After 90 degrees the picture is the first picture: every point stands where its neighbour stood."""
    first, last = FRAMES[0], FRAMES[-1]
    def key(fr, i):
        return (COLOR[i], round(fr[1][i][0], 6), round(fr[1][i][1], 6), round(fr[2][i], 6))
    assert sorted(key(first, i) for i in range(N)) == sorted(key(last, i) for i in range(N))
    def fkey(fr, f):
        return (tuple(sorted((round(fr[1][i][0], 6), round(fr[1][i][1], 6)) for i in FACES[f])),
                round(fr[3][f], 6), round(fr[4][f], 6))
    assert sorted(fkey(first, f) for f in range(len(FACES))) == sorted(fkey(last, f) for f in range(len(FACES)))


def svg():
    font = "Inter,system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
    a1 = ('√<tspan font-style="italic" font-family="Georgia,\'Times New Roman\',serif">a</tspan>'
          '<tspan dy="4" font-size="10">1</tspan>')
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {HEIGHT}" width="{W}" height="{HEIGHT}" '
        f'font-family="{font}" role="img" aria-labelledby="t d">',
        '<title id="t">The square antiprism</title>',
        '<desc id="d">Eight points on the unit sphere, rotating about their axis: a square at height '
        f'{H:.4f} and a square at height -{H:.4f} that is rotated by 45 degrees. Its Coulomb energy {ENERGY} is '
        'the minimum for eight points.</desc>',
        "<defs>",
        gradient("b", BLUE), gradient("g", GREEN), gradient("bf", BLUE, 0.52), gradient("gf", GREEN, 0.52),
        f'<radialGradient id="glass"><stop offset="0" stop-color="{TINT}" stop-opacity=".02"/>'
        f'<stop offset=".7" stop-color="{TINT}" stop-opacity=".05"/>'
        f'<stop offset=".92" stop-color="{RIM}" stop-opacity=".13"/>'
        f'<stop offset="1" stop-color="{RIM}" stop-opacity=".34"/></radialGradient>',
        '<radialGradient id="shine"><stop offset="0" stop-color="#fff" stop-opacity=".75"/>'
        '<stop offset=".5" stop-color="#fff" stop-opacity=".22"/>'
        '<stop offset="1" stop-color="#fff" stop-opacity="0"/></radialGradient>',
        '<radialGradient id="shadow"><stop offset="0" stop-color="#141a2a" stop-opacity=".19"/>'
        '<stop offset=".6" stop-color="#141a2a" stop-opacity=".06"/>'
        '<stop offset="1" stop-color="#141a2a" stop-opacity="0"/></radialGradient>',
        "</defs>",
        f'<rect x=".5" y=".5" width="{W - 1}" height="{HEIGHT - 1}" rx="14" fill="{PAGE}" stroke="{INK}" '
        'stroke-opacity=".1"/>',
        f'<ellipse cx="{CX}" cy="{CY + RAD + 25}" rx="{round(RAD * 0.8)}" ry="14" fill="url(#shadow)"/>',
        f'<circle cx="{CX}" cy="{CY}" r="{RAD}" fill="url(#glass)" stroke="{RIM}" stroke-opacity=".28"/>',
        "<g>", *points(0), "</g>",
        f'<g fill="{FACE}">', *faces(), "</g>",
        f'<g fill="none" stroke="{EDGE}" stroke-width="1.4" stroke-linecap="round">',
        f"<style>.u{{stroke:{BLUE};stroke-width:2.1}}.l{{stroke:{GREEN};stroke-width:2.1}}</style>",
        *edges(), "</g>",
        "<g>", *points(1), "</g>",
        f'<ellipse cx="{CX - 64}" cy="{CY - 86}" rx="54" ry="29" transform="rotate(-38 {CX - 64} {CY - 86})" '
        'fill="url(#shine)"/>',
        # the text, in the manner of the page lukasliehr.github.io/energy-minimization
        f'<text x="{TX}" y="114" font-size="13" fill="{MUTED}">Energy minimization for 8 points</text>',
        f'<text x="{TX}" y="147" font-size="23" font-weight="600" fill="{INK}" letter-spacing="-.35">'
        "Square antiprism</text>",
        f'<g font-size="14" fill="{INK2}">',
        legend(192, BLUE, f'Square at height {a1}<tspan dy="-4"> ≈ {H:.4f}</tspan>'),
        legend(220, GREEN, f'Square at height −{a1}<tspan dy="-4">, rotated by 45°</tspan>'),
        "</g>",
        f'<line x1="{TX}" y1="250" x2="{W - 44}" y2="250" stroke="{INK}" stroke-opacity=".1"/>',
        f'<text x="{TX}" y="280" font-size="12" fill="{MUTED}">Minimal Coulomb energy</text>',
        f'<text x="{TX}" y="314" font-size="27" font-weight="600" fill="{INK}" letter-spacing="-.5">{ENERGY}</text>',
        "</svg>",
    ]
    return "\n".join(parts) + "\n"


if __name__ == "__main__":
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "square-antiprism.svg")
    check_loop()
    text = svg()
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print(path, len(text.encode()), "bytes")
