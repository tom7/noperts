import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def box180 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 1 / 1000
  δ := 170 / 1000000
  r := 4 / 100000

#eval decide (∀ j, box180.variationRadiusSum j + 3 * variationError ≤ (box180.certificate j).B * box180.δ)
#eval box180.decomposedBarycentricValid (20 / 1000)
#eval box180.decomposedBarycentricValid (22 / 1000)
#eval box180.decomposedBarycentricValid (25 / 1000)
#eval box180.decomposedBarycentricValid (17 / 1000)
