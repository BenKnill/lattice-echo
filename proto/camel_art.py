import numpy as np, base64, io, json
from PIL import Image, ImageDraw
N = 256
r, c = np.meshgrid(np.arange(N), np.arange(N), indexing='ij')
t = r / (N - 1)
teal, lav, navy = np.array([79, 209, 197]), np.array([169, 156, 255]), np.array([22, 30, 48])
bg = (1 - t)[..., None] * lav + t[..., None] * teal
bg = bg * (0.55 + 0.25 * np.cos(2 * np.pi * c / N)[..., None]) + navy * 0.35
grid = ((r % 16 == 0) | (c % 16 == 0))
bg[grid] = bg[grid] * 0.55 + 255 * 0.12
img = Image.fromarray(np.clip(bg, 0, 255).astype(np.uint8))
d = ImageDraw.Draw(img)
cream, shade = (246, 232, 204), (214, 186, 140)
d.ellipse([66, 118, 190, 170], fill=cream)                 # body
d.ellipse([84, 80, 128, 136], fill=cream)                  # front hump
d.ellipse([124, 84, 166, 138], fill=cream)                 # rear hump... (camel faces right; humps along back)
d.polygon([(178, 146), (190, 118), (200, 96), (210, 92), (204, 120), (194, 152)], fill=cream)  # neck
d.ellipse([196, 80, 232, 102], fill=cream)                 # head
d.polygon([(226, 84), (238, 88), (230, 94)], fill=cream)   # muzzle
d.polygon([(202, 82), (205, 74), (209, 82)], fill=cream)   # ear
d.polygon([(70, 136), (58, 158), (62, 160), (74, 142)], fill=shade)  # tail
for x, knee in ((82, 190), (100, 192), (150, 190), (168, 192)):   # legs with knees
    d.rectangle([x, 162, x + 8, 214], fill=cream)
    d.rectangle([x - 1, knee, x + 9, knee + 5], fill=shade)
d.rectangle([0, 214, N, 217], fill=(250, 190, 110))        # ground line
img.save('proto/camel256.png')
buf = io.BytesIO(); img.save(buf, format='PNG')
open('web/camel.js', 'w').write('window.CAMEL_PNG = "data:image/png;base64,' + base64.b64encode(buf.getvalue()).decode() + '";\n')
img.resize((768, 768), Image.NEAREST).save('proto/camel768.png')
print('ok')
