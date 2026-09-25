import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

#eval decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
#eval (box.variationRadiusSum 0 + 3 * variationError)
#eval ((box.certificate 0).B * box.δ)
#eval ((box.variationRadiusSum 0 + 3 * variationError) / (box.certificate 0).B)
