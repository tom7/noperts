import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def c_core : ℚ := (55 : ℚ) / 100000
def delta : ℚ := (234013 : ℚ) / 1000000000
def r_min : ℚ := (5 : ℚ) / 10000

def main : IO Unit := do
  IO.println s!"val: {decide (r_min ^ 2 * (1 + (c_core - delta) ^ 2) ≤ 4 * (c_core - delta) ^ 2)}"
