import Noperthedron.Nopert229.TestFlockTheorem

def c_core : ℚ := 15 / 10000
def r_min : ℚ := 23 / 10000
def δ : ℚ := 260 / 1000000
def r : ℚ := 4 / 100000
def B0 : ℚ := 700862849 / 500000000
def D0 : ℚ := 734 / 10000000  -- 7.34e-5
def c_cone : ℚ := 20 / 1000

theorem h_core_angle : r_min ^ 2 * (1 + (c_core - δ) ^ 2) ≤ 4 * (c_core - δ) ^ 2 := by
  decide +kernel

theorem h_annular : ((1/2 : ℚ) * r^2 * B0 + D0)^2 ≤ r_min^2 * (1 - (1/4 : ℚ) * r^2) * ((c_cone - δ)^2 * B0^2) := by
  unfold r B0 D0 r_min c_cone δ
  decide +kernel
