import Noperthedron.Nopert229.TestEvalRealCage
import Noperthedron.Nopert229.TestFlockTheorem

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def c_core : ℚ := 15 / 10000
def r_min : ℚ := 23 / 10000
def c_cone : ℚ := 25 / 1000
def D0 : ℚ := 734 / 10000000

def testBox : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 265 / 1000000
  δ := 260 / 1000000
  r := 4 / 100000

theorem test_core_angle :
    r_min ^ 2 * (1 + (c_core - testBox.δ) ^ 2) ≤ 4 * (c_core - testBox.δ) ^ 2 := by
  decide +kernel

theorem test_annular :
    ((1/2 : ℚ) * testBox.r^2 * (testBox.certificate 0).B + D0)^2 ≤
    r_min^2 * (1 - (1/4 : ℚ)*testBox.r^2) * ((c_cone - testBox.δ)^2 * (testBox.certificate 0).B^2) := by
  have hB : (testBox.certificate 0).B = 349290553 / 250000000 := rfl
  rw [hB]
  decide +kernel
