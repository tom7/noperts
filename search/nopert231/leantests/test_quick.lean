import Mathlib.Data.Rat.Basic

def c_cone : ℚ := 15 / 1000
def c_core : ℚ := 10 / 1000
def r_min : ℚ := 8 / 1000
def D0 : ℚ := 15 / 100000
def box_δ : ℚ := 234013 / 1000000000

def main : IO Unit := do
  IO.println s!"core_angle: {decide (r_min ^ 2 * (1 + (c_core - box_δ) ^ 2) ≤ 4 * (c_core - box_δ) ^ 2)}"
  IO.println s!"c_core_margin: {decide (box_δ ≤ c_core)}"
