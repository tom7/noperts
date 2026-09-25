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

#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 0 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 1 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 2 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 3 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 4 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 5 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 6 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 7 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 8 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 9 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 10 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 11 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 12 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 13 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 14 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 15 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 16 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 17 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 18 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 19 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 20 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 21 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 22 ≤ 0
#eval (box.withCoreAxis coreAxSingle c_core r_min).supportUpper 0 2 23 ≤ 0

