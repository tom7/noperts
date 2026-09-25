import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def flockAx0 : AxisCertificate := {
  edgeStart := ![1, 10, 10],
  edgeFinish := ![4, 15, 15],
  edgeStart₂ := ![4, 15, 15],
  edgeFinish₂ := ![8, 19, 19],
  mix := ![1000, 333, 200],
  index := ![4, 15, 15],
  nonzeroWitness := ![15, 1, 4],
  B := 101690303 / 500000000
}

def flockAx1 : AxisCertificate := {
  edgeStart := ![2, 10, 19],
  edgeFinish := ![1, 15, 3],
  edgeStart₂ := ![1, 15, 3],
  edgeFinish₂ := ![4, 19, 2],
  mix := ![0, 800, 800],
  index := ![1, 15, 3],
  nonzeroWitness := ![15, 1, 9],
  B := 41861781 / 25000000
}

def flockAx2 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 500, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 128900569 / 200000000
}

def delta_box : ℚ := 195 / 1000000
def c_core : ℚ := 3 / 10000
def r_min : ℚ := 31 / 100000

def testAxis (ax : AxisCertificate) : Prop :=
  let b := box.withCoreAxis ax c_core r_min
  (b.variationRadiusSum 0 + 3 * variationError ≤ ax.B * delta_box) ∧
  (∀ (i : Fin 3) (k : Nopert229.VertexIndex), b.supportUpper 0 i k ≤ 0) ∧
  (∀ (i : Fin 3), b.supportUpper 0 i (ax.nonzeroWitness i) < 0) ∧
  (b.weightBudget 0 ≤ ax.B) ∧
  (∀ (i : Fin 3), 0 ≤ b.weightLower 0 i) ∧
  (∃ (i : Fin 3), 0 < b.weightLower 0 i)

instance (ax : AxisCertificate) : Decidable (testAxis ax) := by
  unfold testAxis
  infer_instance

#eval decide (testAxis flockAx0)
#eval decide (testAxis flockAx1)
#eval decide (testAxis flockAx2)

