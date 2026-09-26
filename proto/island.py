import numpy as np
from PIL import Image
N, K, k = 256, 2.0, 100
a = K / (2 * np.pi)
r, c = np.meshgrid(np.arange(N), np.arange(N), indexing='ij')
X, Y = c.ravel(), ((N // 2 - 1 - r) % N).ravel()          # display -> lattice
x0, y0 = (X + 0.5) / N, (Y + 0.5) / N
x, y = x0.copy(), y0.copy()
for _ in range(k):
    y = (y + a * np.sin(2 * np.pi * x)) % 1.0; x = (x + y) % 1.0
for _ in range(k):
    x = (x - y) % 1.0; y = (y - a * np.sin(2 * np.pi * x)) % 1.0
e = np.maximum(np.minimum(abs(x - x0), 1 - abs(x - x0)), np.minimum(abs(y - y0), 1 - abs(y - y0)))
ok = (e < 0.5 / N).reshape(N, N)
print('returned fraction', ok.mean())
rows = np.where(ok.any(1))[0]; cols = np.where(ok.any(0))[0]
print('central island bbox rows', rows.min(), rows.max(), 'cols', cols.min(), cols.max())
Image.fromarray((ok * 255).astype(np.uint8)).resize((512, 512), Image.NEAREST).save('island_mask.png')
