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

def main : IO Unit := do
  let u0 := box.approxNormalizedCenter 0
  let norm_sq_u0 := u0 0 * u0 0 + u0 1 * u0 1 + u0 2 * u0 2
  IO.println s!"u0 = ({u0 0}, {u0 1}, {u0 2}), norm_sq = {norm_sq_u0}"
  let idxs : List (Fin 4) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
  for m in idxs do
    let ax := flock m
    let cb := box.withCoreAxis ax (1/100) (8/1000)
    let c := cb.approxNormalizedCenter 0
    let norm_sq := c 0 * c 0 + c 1 * c 1 + c 2 * c 2
    IO.println s!"flock {m.val}: center = ({c 0}, {c 1}, {c 2}), norm_sq = {norm_sq}"
