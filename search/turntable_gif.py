#!/usr/bin/env python3
# Assembles turntable.exe's PNG frames into a looping animated GIF.
# Usage: turntable_gif.py FRAME_DIR OUT.gif [ms_per_frame]
import glob
import sys

from PIL import Image

frame_dir, out = sys.argv[1], sys.argv[2]
ms = int(sys.argv[3]) if len(sys.argv) > 3 else 50
frames = [Image.open(f).convert("RGB") for f in sorted(glob.glob(f"{frame_dir}/frame*.png"))]
assert frames, f"no frames in {frame_dir}"
frames = [f.quantize(colors=128, method=Image.Quantize.MEDIANCUT) for f in frames]
frames[0].save(out, save_all=True, append_images=frames[1:], duration=ms, loop=0, optimize=True)
print(f"{len(frames)} frames -> {out}")
