with open("find_3_complement_axes.cc", "r") as f:
    text = f.read()

old_targets = """  BigVecQ3 targets[6] = {
    {target_scale, 0, 0},
    {-target_scale, 0, 0},
    {0, target_scale, 0},
    {0, -target_scale, 0},
    {0, 0, target_scale},
    {0, 0, -target_scale}
  };"""

new_targets = """  BigRat z0(0);
  BigVecQ3 targets[6] = {
    BigVecQ3(target_scale, z0, z0),
    BigVecQ3(-target_scale, z0, z0),
    BigVecQ3(z0, target_scale, z0),
    BigVecQ3(z0, -target_scale, z0),
    BigVecQ3(z0, z0, target_scale),
    BigVecQ3(z0, z0, -target_scale)
  };"""

text = text.replace(old_targets, new_targets)
with open("find_3_complement_axes.cc", "w") as f:
    f.write(text)
