import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

#eval decide (∀ (j : Fin 4), box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
