import numpy as np
from PIL import Image
N, K = 256, 2.0; a = K / (2 * np.pi)
r, c = np.meshgrid(np.arange(N), np.arange(N), indexing='ij')
X, Y = c.ravel(), ((N // 2 - 1 - r) % N).ravel()
x0, y0 = (X + 0.5) / N, (Y + 0.5) / N
def fwd(x, y, k):
    for _ in range(k): y = (y + a * np.sin(2*np.pi*x)) % 1.0; x = (x + y) % 1.0
    return x, y
def bwd(x, y, k):
    for _ in range(k): x = (x - y) % 1.0; y = (y - a * np.sin(2*np.pi*x)) % 1.0
    return x, y
home = lambda x, y: np.mean((np.floor(x*N).astype(int) == X) & (np.floor(y*N).astype(int) == Y))
for k in (40, 45, 50, 60):
    x, y = x0.copy(), y0.copy(); out = []
    for cyc in range(8):
        x, y = bwd(*fwd(x, y, k), k); out.append(f"{home(x, y):.1%}")
    print(f"rotor k={k}: pixels home after cycles 1..8:", " ".join(out))
# rotation by theta and back with bilinear resampling
img = np.asarray(Image.open('camel256.png').convert('RGB')).astype(np.float64)
def rot(im, th):
    cy = cx = (N - 1) / 2
    yy, xx = np.meshgrid(np.arange(N), np.arange(N), indexing='ij')
    ct, st = np.cos(th), np.sin(th)
    xs = ct * (xx - cx) + st * (yy - cy) + cx; ys = -st * (xx - cx) + ct * (yy - cy) + cy
    x0_ = np.floor(xs).astype(int); y0_ = np.floor(ys).astype(int); fx = xs - x0_; fy = ys - y0_
    def px(yi, xi):
        ok = (xi >= 0) & (xi < N) & (yi >= 0) & (yi < N)
        v = np.zeros(xi.shape + (3,)); v[ok] = im[yi[ok], xi[ok]]; return v
    return ((1-fx)*(1-fy))[..., None]*px(y0_, x0_) + (fx*(1-fy))[..., None]*px(y0_, x0_+1) + ((1-fx)*fy)[..., None]*px(y0_+1, x0_) + (fx*fy)[..., None]*px(y0_+1, x0_+1)
mask = ((r - 127.5)**2 + (c - 127.5)**2) < 110**2
for th in (10, 30):
    im = img.copy(); errs = []
    for cyc in range(8):
        im = rot(rot(im, np.radians(th)), -np.radians(th)); errs.append(np.abs(im - img)[mask].mean())
    print(f"rotate {th} deg and back, bilinear: mean abs error (of 255) after cycles 1..8:", " ".join(f"{e:.1f}" for e in errs))
    Image.fromarray(np.clip(im, 0, 255).astype(np.uint8)).resize((512, 512), Image.NEAREST).save(f'rot{th}_8cycles.png')
