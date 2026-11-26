#!/usr/bin/env python3
"""Generate colored frontispieces BookNN/front.svg in the style of Byrne's Euclid."""
import itertools
import math
import os

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')

R, Y, B = '#d1342b', '#f2b632', '#1f5fa8'
K, C = '#1a1a1a', '#f6eedc'
RYB = [R, Y, B]
SW = 2.6          # outline width in px of a 400 px canvas
PHI = (1 + 5 ** 0.5) / 2


def rot(p, a):
    c, s = math.cos(a), math.sin(a)
    return (p[0] * c - p[1] * s, p[0] * s + p[1] * c)


def add(p, q, k=1):
    return (p[0] + k * q[0], p[1] + k * q[1])


def regular(n, r, c=(0, 0), start=90):
    return [add(c, (r * math.cos(math.radians(start + 360 * i / n)),
                    r * math.sin(math.radians(start + 360 * i / n)))) for i in range(n)]


def arc(c, rx, ry, a0, a1, n=48):
    return [(c[0] + rx * math.cos(math.radians(a0 + (a1 - a0) * i / n)),
             c[1] + ry * math.sin(math.radians(a0 + (a1 - a0) * i / n))) for i in range(n + 1)]


class Scene:
    """Shapes in math coordinates (y up), scaled to a 400 px SVG on save."""

    def __init__(self):
        self.items = []

    def poly(self, pts, fill=None, sw=1.0, close=True, dash=False):
        self.items.append(('poly', list(pts), fill, sw, close, dash))

    def line(self, a, b, sw=1.0, color=K, dash=False):
        self.items.append(('line', [a, b], color, sw, False, dash))

    def circle(self, c, r, fill=None, sw=1.0, dash=False):
        self.items.append(('circle', [c], fill, sw, r, dash))

    def save(self, path, size=400, pad=0.03):
        xs, ys = [], []
        for kind, pts, _, _, extra, _ in self.items:
            r = extra if kind == 'circle' else 0
            for x, y in pts:
                xs += [x - r, x + r]
                ys += [y - r, y + r]
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        k = size / max(x1 - x0, y1 - y0) * (1 - 2 * pad)
        m = size * pad
        w, h = (x1 - x0) * k + 2 * m, (y1 - y0) * k + 2 * m

        def P(p):
            return '%.2f,%.2f' % ((p[0] - x0) * k + m, (y1 - p[1]) * k + m)

        out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%.0f" height="%.0f" '
               'viewBox="0 0 %.2f %.2f">' % (w, h, w, h),
               '<g stroke-linejoin="round" stroke-linecap="round">']
        for kind, pts, fill, sw, extra, dash in self.items:
            st = 'stroke="%s" stroke-width="%.2f"' % (K if kind != 'line' else fill, SW * sw)
            if dash:
                st += ' stroke-dasharray="%.1f %.1f"' % (3 * SW * sw, 2.5 * SW * sw)
            if kind == 'circle':
                cx, cy = P(pts[0]).split(',')
                out.append('<circle cx="%s" cy="%s" r="%.2f" fill="%s" %s/>'
                           % (cx, cy, extra * k, fill or 'none', st))
            elif kind == 'line':
                out.append('<polyline points="%s" fill="none" %s/>' % (' '.join(map(P, pts)), st))
            else:
                tag = 'polygon' if extra else 'polyline'
                out.append('<%s points="%s" fill="%s" %s/>'
                           % (tag, ' '.join(map(P, pts)), fill or 'none', st))
        out += ['</g>', '</svg>']
        open(path, 'w').write('\n'.join(out) + '\n')


# --- 3D ---------------------------------------------------------------------

def sub3(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot3(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def unit(a):
    n = math.sqrt(dot3(a, a))
    return tuple(x / n for x in a)


class Camera:
    def __init__(self, yaw=35, pitch=25):
        self.yaw, self.pitch = math.radians(yaw), math.radians(pitch)
        self.light = unit((-0.45, 0.8, 0.5))     # camera coords: x right, y up, z toward viewer

    def view(self, p):
        x, y = rot((p[0], p[1]), self.yaw)
        z = p[2]
        c, s = math.cos(self.pitch), math.sin(self.pitch)
        return (x, z * c + y * s, -y * c + z * s)  # (screen x, screen y, toward viewer)

    def color(self, normal):
        n = unit(normal)
        l = dot3(n, self.light)
        return C if l > 0.92 else Y if l > 0.55 else R if l > 0.15 else B


def hull_faces(vs):
    """Faces of a convex polyhedron as ordered vertex lists (outward)."""
    faces = set()
    for i, j, k in itertools.combinations(range(len(vs)), 3):
        n = cross(sub3(vs[j], vs[i]), sub3(vs[k], vs[i]))
        if dot3(n, n) < 1e-9:
            continue
        d = [dot3(n, sub3(v, vs[i])) for v in vs]
        if all(x <= 1e-6 for x in d) or all(x >= -1e-6 for x in d):
            faces.add(frozenset(m for m, x in enumerate(d) if abs(x) < 1e-6))
    cen = tuple(sum(c) / len(vs) for c in zip(*vs))
    out = []
    for f in faces:
        f = list(f)
        fc = tuple(sum(vs[m][a] for m in f) / len(f) for a in range(3))
        n = unit(sub3(fc, cen))
        u = unit(sub3(vs[f[0]], fc))
        w = cross(n, u)
        f.sort(key=lambda m: math.atan2(dot3(sub3(vs[m], fc), w), dot3(sub3(vs[m], fc), u)))
        out.append([vs[m] for m in f])
    return out


def draw_solid(sc, cam, faces, offset=(0, 0), scale=1.0):
    """Draw visible faces of a convex solid (vertices already in world coords)."""
    for f in faces:
        p = [cam.view(v) for v in f]
        n = cross(sub3(p[1], p[0]), sub3(p[2], p[0]))
        if n[2] <= 1e-9:
            continue
        sc.poly([add(offset, (q[0] * scale, q[1] * scale)) for q in p], cam.color(n))


def depth(cam, pts):
    return sum(cam.view(v)[2] for v in pts) / len(pts)


def box(x, y, z, dx, dy, dz):
    return hull_faces([(x + a * dx, y + b * dy, z + c * dz)
                       for a in (0, 1) for b in (0, 1) for c in (0, 1)])


# --- Books ------------------------------------------------------------------

def book1():
    """I.47: squares on the sides of a right triangle, the large one split by the altitude."""
    sc = Scene()
    P, Q, A = (0, 0), (5, 0), (3.2, 2.4)
    foot = (3.2, 0)
    n1 = rot(add(A, P, -1), math.pi / 2)
    n2 = rot(add(Q, A, -1), math.pi / 2)
    sc.poly([P, foot, (3.2, -5), (0, -5)], R)
    sc.poly([foot, Q, (5, -5), (3.2, -5)], B)
    sc.poly([P, A, add(A, n1), add(P, n1)], R)
    sc.poly([A, Q, add(Q, n2), add(A, n2)], B)
    sc.poly([P, Q, A], Y)
    sc.line(A, (3.2, -5), 0.8, dash=True)
    return sc


def book2():
    """II.4: square on a whole line split into two squares and two equal rectangles; II.1 below."""
    sc = Scene()
    sc.poly([(0, 0), (3, 0), (3, 3), (0, 3)], R)
    sc.poly([(3, 3), (5, 3), (5, 5), (3, 5)], B)
    sc.poly([(3, 0), (5, 0), (5, 3), (3, 3)], Y)
    sc.poly([(0, 3), (3, 3), (3, 5), (0, 5)], Y)
    sc.line((0, 0), (5, 5), 0.8, dash=True)
    xs = [0, 2, 3.5, 5]
    for i in range(3):
        sc.poly([(xs[i], -2), (xs[i + 1], -2), (xs[i + 1], -0.8), (xs[i], -0.8)], RYB[i])
    return sc


def book3():
    """Circles: central and inscribed angles on one arc, tangent line, touching circle."""
    sc = Scene()
    O = (0, 0)
    P, Q, V = (regular(1, 1, start=a)[0] for a in (215, 325, 100))
    sc.circle(O, 1, C, 1.2)
    sc.poly([V, P, Q], Y)
    sc.poly([O, P, Q], R)
    sc.poly([V] + arc(V, 0.28, 0.28, math.degrees(math.atan2(P[1] - V[1], P[0] - V[0])),
                      math.degrees(math.atan2(Q[1] - V[1], Q[0] - V[0])), 16), B, 0.6)
    t = rot((1, 0), math.radians(100))
    tan = (-t[1], t[0])
    sc.line(add(V, tan, 1.1), add(V, tan, -1.1), 1.4, R)
    c2 = regular(1, 1.42, start=-10)[0]
    sc.line(O, c2, 0.6, dash=True)
    sc.circle(c2, 0.42, B, 1.2)
    return sc


def book4():
    """Figures in and around circles, nested alternately."""
    sc = Scene()
    sc.poly([(-1, -1), (1, -1), (1, 1), (-1, 1)], B)
    r = 1.0
    for n, fills in ((5, (C, R)), (6, (Y, B)), (3, (C, R))):
        sc.circle((0, 0), r, fills[0])
        sc.poly(regular(n, r), fills[1])
        r *= math.cos(math.pi / n)
    sc.circle((0, 0), r, Y)
    return sc


def book5():
    """V.def.5: A : B :: C : D shown by equimultiples 2A = 3B and 2C = 3D."""
    sc = Scene()
    rows = [([3], R), ([2], B), ([3, 3], R), ([2, 2, 2], B),
            ([4.5], Y), ([3], K), ([4.5, 4.5], Y), ([3, 3, 3], K)]
    y = 0
    for i, (segs, col) in enumerate(rows):
        x = 0
        for s in segs:
            sc.poly([(x, y), (x + s, y), (x + s, y + 0.7), (x, y + 0.7)], col)
            x += s
        y -= 1.6 if i == 3 else 1.0
    return sc


def book6():
    """VI.2: parallels to a side cut a triangle proportionally; VI.8: the altitude makes similar triangles."""
    sc = Scene()
    A, Bv, Cv = (0.7, 2.2), (0, 0), (3, 0)
    for t, col in ((1, R), (0.75, Y), (0.5, B), (0.25, R)):
        sc.poly([A, add(A, add(Bv, A, -1), t), add(A, add(Cv, A, -1), t)], col)
    y = -2.7
    d = 1.08
    h = math.sqrt(d * (3 - d))
    P, Q, F, T = (0, y), (3, y), (d, y), (d, y + h)
    sc.poly([P, F, T], R)
    sc.poly([F, Q, T], B)
    sc.poly([P, Q, T], None, 1.2)
    return sc


def book7():
    """Euclid's algorithm (VII.1-2): a 7 x 12 rectangle tiled by ever smaller squares."""
    sc = Scene()
    W, H = 7, 12
    x, y, w, h = 0, 0, W, H
    sq, step, last = [], -1, None
    while w > 0 and h > 0:
        s = min(w, h)
        if s != last:
            step, last = step + 1, s
        if h >= w:
            sq.append((x, y, s, step))
            y, h = y + s, h - s
        else:
            sq.append((x, y, s, step))
            x, w = x + s, w - s
    for x, y, s, st in sq:
        sc.poly([(x, y), (x + s, y), (x + s, y + s), (x, y + s)], RYB[st % 3])
    for i in range(1, W):
        sc.line((i, 0), (i, H), 0.25)
    for j in range(1, H):
        sc.line((0, j), (W, j), 0.25)
    for x, y, s, _ in sq:
        sc.poly([(x, y), (x + s, y), (x + s, y + s), (x, y + s)], None, 1.2)
    return sc


def book8():
    """Continued proportion: squares whose areas run 32, 16, 8, ... each the mean of its neighbours."""
    sc = Scene()
    pts = [(-1, -1), (1, -1), (1, 1), (-1, 1)]
    for i in range(7):
        sc.poly(pts, RYB[i % 3])
        pts = [((pts[j][0] + pts[(j + 1) % 4][0]) / 2, (pts[j][1] + pts[(j + 1) % 4][1]) / 2)
               for j in range(4)]
    return sc


def book9():
    """IX.35-36: 1 + 1 + 2 + 4 + ... + 32 = 64, the doubling series filling a square."""
    sc = Scene()
    x, y, w, h = 0, 0, 8, 8
    parts = []
    for i in range(6):
        if i % 2 == 0:
            parts.append((x, y, w / 2, h))
            x, w = x + w / 2, w / 2
        else:
            parts.append((x, y + h / 2, w, h / 2))
            h = h / 2
    parts.append((x, y, w, h))
    for i, (x, y, w, h) in enumerate(parts):
        sc.poly([(x, y), (x + w, y), (x + w, y + h), (x, y + h)], RYB[i % 3] if i < 6 else C)
    for i in range(1, 8):
        sc.line((i, 0), (i, 8), 0.25)
        sc.line((0, i), (8, i), 0.25)
    for x, y, w, h in parts:
        sc.poly([(x, y), (x + w, y), (x + w, y + h), (x, y + h)], None, 1.2)
    return sc


def book10():
    """Incommensurables: the spiral of right triangles with hypotenuses root 2, root 3, ..."""
    sc = Scene()
    O, p = (0, 0), (1, 0)
    for k in range(1, 17):
        r = math.hypot(*p)
        q = add(p, (-p[1] / r, p[0] / r))
        sc.poly([O, p, q], RYB[(k - 1) % 3])
        p = q
    return sc


def book11():
    """Solids: parallelepipeds and a prism, the halves of XI.28."""
    sc = Scene()
    cam = Camera(30, 28)
    solids = [box(-2.6, 0.6, 0, 1, 1, 2.6), box(-1, -1, 0, 2, 2, 2), box(1.4, -0.6, 0, 2.2, 1.2, 0.7),
              hull_faces([(-2.8, -2.2, 0), (-1.6, -2.2, 0), (-2.8, -0.9, 0),
                          (-2.8, -2.2, 1.2), (-1.6, -2.2, 1.2), (-2.8, -0.9, 1.2)]),
              hull_faces([(1.6, 1.4, 0), (2.8, 1.4, 0), (2.8, 2.6, 0), (1.6, 2.6, 0), (2.2, 2.0, 1.8)])]
    solids.sort(key=lambda f: depth(cam, [v for face in f for v in face]))
    for f in solids:
        draw_solid(sc, cam, f)
    return sc


def book12():
    """XII.2 by exhaustion: polygons of 4, 8, 16 sides filling a circle; XII.10 cone in cylinder; sphere."""
    sc = Scene()
    sc.circle((0, 0), 1, C, 1.2)
    for n, col in ((16, B), (8, Y), (4, R)):
        sc.poly(regular(n, 1, start=45), col)
    rx, ry, top, bot, cx = 0.42, 0.12, -1.45, -2.55, -0.52
    sc.poly([(cx - rx, top), (cx - rx, bot)] + arc((cx, bot), rx, ry, 180, 360)
            + [(cx + rx, top)] + arc((cx, top), rx, ry, 360, 180), B)
    sc.poly(arc((cx, top), rx, ry, 0, 360), C)
    sc.poly([(cx, top), (cx - rx, bot)] + arc((cx, bot), rx, ry, 180, 360), R)
    sc.poly(arc((cx, bot), rx, ry, 0, 180), None, 0.6, close=False, dash=True)
    s = (0.52, (top + bot) / 2)
    sc.circle(s, 0.55, Y, 1.0)
    sc.poly(arc(s, 0.55, 0.15, 180, 360), None, 0.7, close=False)
    sc.poly(arc(s, 0.55, 0.15, 0, 180), None, 0.5, close=False, dash=True)
    return sc


def platonic():
    t = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
    cube = list(itertools.product((-1, 1), repeat=3))
    octa = [v for i in range(3) for s in (-1, 1) for v in [tuple(s if j == i else 0 for j in range(3))]]

    def cyc(a, b, c):
        return [(a, b, c), (c, a, b), (b, c, a)]
    ico = [v for s1 in (-1, 1) for s2 in (-1, 1) for v in cyc(0, s1, s2 * PHI)]
    dod = cube + [v for s1 in (-1, 1) for s2 in (-1, 1) for v in cyc(0, s1 / PHI, s2 * PHI)]
    out = []
    for vs in (t, cube, octa, ico, dod):
        r = math.sqrt(dot3(vs[0], vs[0]))
        out.append([tuple(x / r for x in v) for v in vs])
    return out


def turn(vs, a, b):
    """Rotate about x by a, then about z by b (degrees)."""
    a, b = math.radians(a), math.radians(b)
    out = []
    for x, y, z in vs:
        y, z = y * math.cos(a) - z * math.sin(a), y * math.sin(a) + z * math.cos(a)
        x, y = rot((x, y), b)
        out.append((x, y, z))
    return out


def book13():
    """The five regular solids, the dodecahedron in its sphere at the centre."""
    sc = Scene()
    cam = Camera(20, 20)
    tet, cube, octa, ico, dod = platonic()
    sc.circle((0, 0), 1.45, C, 1.0)
    draw_solid(sc, cam, hull_faces(turn(dod, 12, 17)), (0, 0), 1.45)
    for vs, pos, ang in ((tet, (-2.25, 2.25), (25, 40)), (cube, (2.25, 2.25), (10, 25)),
                         (octa, (-2.25, -2.25), (15, 20)), (ico, (2.25, -2.25), (20, 10))):
        draw_solid(sc, cam, hull_faces(turn(vs, *ang)), pos, 1.15)
    return sc


def main():
    for n, f in enumerate([book1, book2, book3, book4, book5, book6, book7,
                           book8, book9, book10, book11, book12, book13], 1):
        f().save(os.path.join(ROOT, 'Book%02d' % n, 'front.svg'))


if __name__ == '__main__':
    main()
