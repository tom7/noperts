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

#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 0 ⟨9, by decide⟩)
#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 1 ⟨15, by decide⟩)
#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 2 ⟨1, by decide⟩)

-- Check contact 2 against all 24 vertices
#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 2 ⟨13, by decide⟩)
#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 2 ⟨14, by decide⟩)
#eval ((box.withCoreAxis coreAx3 c_core r_min).supportUpper 0 2 ⟨15, by decide⟩)
