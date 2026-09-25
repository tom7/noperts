import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def flockAx0 : AxisCertificate := {
  edgeStart := ![1, 10, 10],
  edgeFinish := ![4, 15, 15],
  edgeStart₂ := ![4, 15, 15],
  edgeFinish₂ := ![8, 19, 19],
  mix := ![1000, 333, 200],
  index := ![4, 15, 15],
  nonzeroWitness := ![15, 1, 4],
  B := 101690303/500000000
}

def flockAx1 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![200, 1000, 800],
  index := ![2, 4, 15],
  nonzeroWitness := ![9, 15, 1],
  B := 549469387/500000000
}

def flockAx2 : AxisCertificate := {
  edgeStart := ![2, 10, 10],
  edgeFinish := ![1, 15, 15],
  edgeStart₂ := ![1, 15, 15],
  edgeFinish₂ := ![4, 19, 19],
  mix := ![0, 333, 200],
  index := ![1, 15, 15],
  nonzeroWitness := ![15, 1, 4],
  B := 101690303/500000000
}

def flockAx3 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 800, 200],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 9],
  B := 549469387/500000000
}

def flock : Fin 4 → AxisCertificate := ![flockAx0, flockAx1, flockAx2, flockAx3]
def c_core : ℚ := 14 / 100000
def r_min : ℚ := 35 / 10000

def main : IO Unit := do
  let indices : List (Fin 4) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
  for m in indices do
    let ax := flock m
    let cb := box.withCoreAxis ax c_core r_min
    let lhs := cb.variationRadiusSum 0 + 3 * variationError
    let ok240 := decide (lhs ≤ ax.B * (240 / 1000000))
    let ok250 := decide (lhs ≤ ax.B * (250 / 1000000))
    let ok260 := decide (lhs ≤ ax.B * (260 / 1000000))
    IO.println s!"flock {m.val}: ok240={ok240}, ok250={ok250}, ok260={ok260}"
