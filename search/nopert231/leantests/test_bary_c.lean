import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def makeBox (c_val : ℚ) : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := c_val
  δ := 260 / 1000000
  r := 4 / 100000

#eval (makeBox (285 / 1000000)).decomposedBarycentricValid (25 / 1000)
#eval (makeBox (290 / 1000000)).decomposedBarycentricValid (25 / 1000)
#eval (makeBox (300 / 1000000)).decomposedBarycentricValid (25 / 1000)
#eval (makeBox (350 / 1000000)).decomposedBarycentricValid (25 / 1000)
#eval (makeBox (400 / 1000000)).decomposedBarycentricValid (25 / 1000)
#eval (makeBox (1 / 1000)).decomposedBarycentricValid (25 / 1000)
