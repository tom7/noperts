import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestFlockTheorem

open Noperthedron

def tri : TriangleQ := TriangleQ.fromPath "03121303200"

-- Exceptional axis (ax0)
def ax0 : AxisCertificate := {
  edgeStart := ![3, 1, 13],
  edgeFinish := ![2, 4, 14],
  edgeStart₂ := ![2, 4, 14],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 200],
  index := ![2, 4, 14],
  nonzeroWitness := ![14, 1, 9],
  B := 139707629 / 100000000
}

-- Complement cage axes
def ax1 : AxisCertificate := {
  edgeStart := ![2, 10, 10],
  edgeFinish := ![1, 15, 15],
  edgeStart₂ := ![1, 15, 15],
  edgeFinish₂ := ![4, 19, 19],
  mix := ![0, 1000, 0],
  index := ![1, 15, 15],
  nonzeroWitness := ![15, 1, 10],
  B := 415819063 / 1000000000
}

def ax2 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 666, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 617773827 / 1000000000
}

def ax3 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![800, 1000, 333],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 1],
  B := 415819063 / 1000000000
}

def box : Box := {
  interval := { lower := 0, upper := 0 },
  root := 0,
  triangle := tri,
  chart := 0,
  symmetryIndex := 0,
  certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
  c := 1 / 1000,
  δ := 234013 / 1000000000,
  r := 25 / 10000000000
}

def c_cone : ℚ := 15 / 1000
def c_core : ℚ := 10 / 1000
def r_min : ℚ := 8 / 1000
def D0 : ℚ := 15 / 100000

#eval box.decomposedBarycentricValid c_cone
#eval decide (box.mismatchRadius <= box.r)
#eval decide (((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))
#eval decide (r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)
#eval decide (box.δ ≤ c_core)
#eval decide (0 < c_core)
#eval decide (0 < r_min)
#eval decide (0 < c_cone)
#eval decide (box.δ < c_cone)
