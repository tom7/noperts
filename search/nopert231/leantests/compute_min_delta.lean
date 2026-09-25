import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def main : IO Unit := do
  IO.println s!"j=0: {((box.variationRadiusSum 0 + 3 * variationError) / (box.certificate 0).B)}"
  IO.println s!"j=1: {((box.variationRadiusSum 1 + 3 * variationError) / (box.certificate 1).B)}"
  IO.println s!"j=2: {((box.variationRadiusSum 2 + 3 * variationError) / (box.certificate 2).B)}"
  IO.println s!"j=3: {((box.variationRadiusSum 3 + 3 * variationError) / (box.certificate 3).B)}"
