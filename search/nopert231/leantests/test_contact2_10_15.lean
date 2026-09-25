import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def coreAxSingle : AxisCertificate := {
  edgeStart := ![3, 1, 13],
  edgeFinish := ![2, 4, 14],
  edgeStart₂ := ![2, 4, 14],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 1000],
  index := ![2, 4, 14],
  nonzeroWitness := ![9, 15, 1],
  B := 1196812417 / 1000000000
}

def c_core : ℚ := 5 / 1000
def r_min : ℚ := 51 / 10000

#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 10
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 15
