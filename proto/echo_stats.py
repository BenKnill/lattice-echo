import numpy as np
N, K = 256, 2.0
a = K / (2 * np.pi)
X0, Y0 = np.meshgrid(np.arange(N), np.arange(N), indexing='ij')
x0 = (X0.ravel() + 0.5) / N; y0 = (Y0.ravel() + 0.5) / N
def fwd(x, y, k):
    for _ in range(k):
        y = (y + a * np.sin(2 * np.pi * x)) % 1.0; x = (x + y) % 1.0
    return x, y
def bwd(x, y, k):
    for _ in range(k):
        x = (x - y) % 1.0; y = (y - a * np.sin(2 * np.pi * x)) % 1.0
    return x, y
def torus_err(u, v):
    d = np.abs(u - v); return np.minimum(d, 1 - d)
print(" k   returned  median-err(all)  90th-pct-err")
for k in (10, 20, 30, 40, 50, 60, 80, 100, 120, 160):
    x, y = fwd(x0, y0, k); xb, yb = bwd(x, y, k)
    e = np.maximum(torus_err(xb, x0), torus_err(yb, y0))
    print(f"{k:3d}   {np.mean(e < 0.5/N):6.1%}    {np.median(e):9.1e}      {np.percentile(e, 90):9.1e}")
# growth of a single chaotic-sea point's round-trip error vs k
i = np.argmax((np.abs(x0 - 0.12) < 0.003) & (np.abs(y0 - 0.37) < 0.003))
print("single sea point round-trip error by k:")
print(" ".join(f"{k}:{torus_err(bwd(*fwd(x0[i:i+1], y0[i:i+1], k), k)[0], x0[i:i+1])[0]:.0e}" for k in (5,10,15,20,25,30,35,40,45,50)))
