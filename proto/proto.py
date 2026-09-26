"""Prototype: standard map on the torus, float64 vs exact lattice map, forward then backward.

Continuous (unit torus):  y' = y + (K/2pi) sin(2pi x),  x' = x + y'          (mod 1)
Lattice (Z_N x Z_N):      Y' = Y + F[X],                X' = X + Y'           (mod N)
                          F[X] = round(N K/(2pi) sin(2pi X/N))
Display: column = X, row = (N/2 - 1 - Y) mod N, so the elliptic island at (1/2, 0) sits mid-frame.
"""
import sys
import numpy as np
from PIL import Image, ImageDraw

N = 256
OUT = sys.argv[1] if len(sys.argv) > 1 else 'proto.png'


def test_image(n):
    """Hue gradient background with a camel silhouette."""
    c = np.linspace(0, 1, n)
    X, Y = np.meshgrid(c, c)
    h = (X * 0.8 + Y * 0.2) % 1
    r = 0.5 + 0.5 * np.cos(2 * np.pi * (h + 0.0))
    g = 0.5 + 0.5 * np.cos(2 * np.pi * (h + 0.33))
    b = 0.5 + 0.5 * np.cos(2 * np.pi * (h + 0.66))
    base = np.stack([r, g, b], -1) * (0.35 + 0.35 * Y[..., None])
    img = Image.fromarray((base * 255).astype(np.uint8))
    d = ImageDraw.Draw(img)
    s = n / 256
    E = lambda x0, y0, x1, y1: d.ellipse([x0 * s, y0 * s, x1 * s, y1 * s], fill=(250, 235, 200))
    E(70, 110, 190, 170)            # body
    E(88, 78, 132, 130)             # hump 1
    E(128, 82, 170, 132)            # hump 2
    d.polygon([(178 * s, 140 * s), (200 * s, 86 * s), (214 * s, 88 * s), (196 * s, 150 * s)], fill=(250, 235, 200))  # neck
    E(196, 74, 232, 100)            # head
    for x in (84, 104, 150, 170):   # legs
        d.rectangle([x * s, 160 * s, (x + 9) * s, 214 * s], fill=(250, 235, 200))
    d.rectangle([0, 214 * s, n, 218 * s], fill=(250, 235, 200))
    return np.asarray(img)


def disp_to_lattice(n):
    r, c = np.meshgrid(np.arange(n), np.arange(n), indexing='ij')
    return c.ravel(), ((n // 2 - 1 - r) % n).ravel()


def render(Xs, Ys, colors, n):
    out = np.zeros((n, n, 3), np.uint8)
    rows = (n // 2 - 1 - Ys) % n
    out[rows, Xs % n] = colors
    return out


def lattice_fwd(X, Y, F, n, k):
    for _ in range(k):
        Y = (Y + F[X]) % n
        X = (X + Y) % n
    return X, Y


def lattice_bwd(X, Y, F, n, k):
    for _ in range(k):
        X = (X - Y) % n
        Y = (Y - F[X]) % n
    return X, Y


def float_fwd(x, y, K, k):
    a = K / (2 * np.pi)
    for _ in range(k):
        y = (y + a * np.sin(2 * np.pi * x)) % 1.0
        x = (x + y) % 1.0
    return x, y


def float_bwd(x, y, K, k):
    a = K / (2 * np.pi)
    for _ in range(k):
        x = (x - y) % 1.0
        y = (y - a * np.sin(2 * np.pi * x)) % 1.0
    return x, y


def naive_fwd(X, Y, K, n, k):
    """Round the *position* to the grid after each float step: not a bijection."""
    for _ in range(k):
        x, y = X / n, Y / n
        x, y = float_fwd(x, y, K, 1)
        X, Y = np.rint(x * n).astype(np.int64) % n, np.rint(y * n).astype(np.int64) % n
    return X, Y


img = test_image(N)
X0, Y0 = disp_to_lattice(N)
cols = img.reshape(-1, 3)
tiles, labels = [], []
for K in (1.2, 2.0):
    F = np.rint(N * K / (2 * np.pi) * np.sin(2 * np.pi * np.arange(N) / N)).astype(np.int64)
    for k in (40, 120):
        Xl, Yl = lattice_fwd(X0, Y0, F, N, k)
        Xb, Yb = lattice_bwd(Xl, Yl, F, N, k)
        exact = np.all(Xb == X0) and np.all(Yb == Y0)
        x0, y0 = (X0 + 0.5) / N, (Y0 + 0.5) / N
        xf, yf = float_fwd(x0, y0, K, k)
        xb, yb = float_bwd(xf, yf, K, k)
        err = np.minimum(np.abs(xb - x0), 1 - np.abs(xb - x0))
        back_ok = np.mean(err < 0.5 / N)
        Xn, Yn = naive_fwd(X0, Y0, K, N, k)
        survivors = len(np.unique(Xn * N + Yn)) / N ** 2
        row = [render(Xl, Yl, cols, N), render(Xb, Yb, cols, N),
               render(np.floor(xb * N).astype(int), np.floor(yb * N).astype(int), cols, N),
               render(Xn, Yn, cols, N)]
        tiles.append(np.concatenate(row, 1))
        print(f'K={K} k={k}: lattice exact return={exact}; float returns {back_ok:.1%} of pixels; '
              f'naive rounding keeps {survivors:.1%} distinct pixels')
sheet = np.concatenate([np.concatenate([img, np.zeros((N, 3 * N, 3), np.uint8)], 1)] + tiles, 0)
Image.fromarray(sheet).save(OUT)
print('wrote', OUT)
