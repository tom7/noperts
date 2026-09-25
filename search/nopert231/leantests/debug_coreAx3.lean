import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def coreAx3 : AxisCertificate := {
  edgeStart := ![3, 1, 13],
  edgeFinish := ![2, 4, 14],
  edgeStart₂ := ![2, 4, 14],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 300],
  index := ![2, 4, 14],
  nonzeroWitness := ![9, 15, 1],
  B := 1372116187 / 1000000000
}

def c_core : ℚ := 5 / 1000
def r_min : ℚ := 51 / 10000

#eval show IO Unit from do
  let cb := box.withCoreAxis coreAx3 c_core r_min
  for i in [0, 1, 2] do
    for k in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] do
      let s := cb.supportUpper 0 ⟨i, by decide⟩ ⟨k, by decide⟩
      if s > 0 then
        IO.println s!"i={i}, k={k}: supportUpper = {s}"

