import Noperthedron.Nopert229.TestEvalRealCage
import Noperthedron.Nopert229.TestFlockTheorem

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def box260 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 265 / 1000000
  δ := 260 / 1000000
  r := 4 / 100000

def c_core : ℚ := 15 / 10000
def r_min : ℚ := 23 / 10000

def coreAx0 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 800, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 578456463/1000000000
}

def coreAx1 : AxisCertificate := {
  edgeStart := ![2, 10, 19],
  edgeFinish := ![1, 15, 3],
  edgeStart₂ := ![1, 15, 3],
  edgeFinish₂ := ![4, 19, 2],
  mix := ![0, 800, 200],
  index := ![1, 15, 3],
  nonzeroWitness := ![15, 1, 9],
  B := 96698479/50000000
}

def coreAx2 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 1000, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 519773829/1000000000
}

def coreAx3 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 333, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 519773829/1000000000
}

def coreAx4 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 666, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 38424249/50000000
}

def flockAxes : Fin 5 → AxisCertificate :=
  fun | 0 => coreAx0
      | 1 => coreAx1
      | 2 => coreAx2
      | 3 => coreAx3
      | 4 => coreAx4

def main : IO Unit := do
  IO.println s!"Testing flock of 5 axes..."
  for m in (List.finRange 5) do
    let ax := flockAxes m
    let cb := box260.withCoreAxis ax c_core r_min
    let var := cb.variationRadiusSum 0 + 3 * variationError
    let bud := ax.B * box260.δ
    let var_ok := decide (var ≤ bud)
    let bud_ok := decide (cb.weightBudget 0 ≤ ax.B)
    let w0 := cb.weightLower 0 0
    let w1 := cb.weightLower 0 1
    let w2 := cb.weightLower 0 2
    let w_ok := decide (0 ≤ w0 ∧ 0 ≤ w1 ∧ 0 ≤ w2 ∧ (0 < w0 ∨ 0 < w1 ∨ 0 < w2))
    let mut supp_ok := true
    for i in (List.finRange 3) do
      for k in (List.finRange 20) do
        if cb.supportUpper 0 i k > 0 then supp_ok := false
      if cb.supportUpper 0 i (ax.nonzeroWitness i) ≥ 0 then supp_ok := false
    IO.println s!"m = {m.val}: var={var_ok}, budget={bud_ok}, weights={w_ok}, supp={supp_ok}"
