import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def box200 : Box := { box with δ := 200 / 1000000 }

#eval decide (∀ (j : Fin 4), box200.variationRadiusSum j + 3 * variationError ≤ (box200.certificate j).B * box200.δ)
