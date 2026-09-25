import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

#eval decide (box.variationRadiusSum 0 + 3 * variationError ≤ (box.certificate 0).B * box.δ)
#eval decide (box.variationRadiusSum 1 + 3 * variationError ≤ (box.certificate 1).B * box.δ)
#eval decide (box.variationRadiusSum 2 + 3 * variationError ≤ (box.certificate 2).B * box.δ)
#eval decide (box.variationRadiusSum 3 + 3 * variationError ≤ (box.certificate 3).B * box.δ)

#eval (box.variationRadiusSum 0 + 3 * variationError) / (box.certificate 0).B
#eval (box.variationRadiusSum 1 + 3 * variationError) / (box.certificate 1).B
#eval (box.variationRadiusSum 2 + 3 * variationError) / (box.certificate 2).B
#eval (box.variationRadiusSum 3 + 3 * variationError) / (box.certificate 3).B
