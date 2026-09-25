import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def ax0_zero : AxisCertificate := {
  edgeStart := ![3, 1, 9],
  edgeFinish := ![2, 4, 10],
  edgeStart₂ := ![2, 4, 10],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 1000],
  index := ![2, 4, 10],
  nonzeroWitness := ![9, 15, 2],
  B := 573018997 / 500000000
}

def box_zero : Box := { box with certificate := fun | 0 => ax0_zero | 1 => ax1 | 2 => ax2 | 3 => ax3 }

#eval decide (∀ k, box_zero.supportUpper 0 0 k ≤ 0)
#eval decide (∀ k, box_zero.supportUpper 0 1 k ≤ 0)
#eval decide (∀ k, box_zero.supportUpper 0 2 k ≤ 0)
#eval decide (box_zero.decomposedBarycentricValid (17 / 1000))
