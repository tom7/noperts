import Noperthedron.Nopert229.TestFlockTheorem
import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def box260 : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := 265 / 1000000
  δ := 260 / 1000000
  r := 4 / 100000

#eval box260.decomposedBarycentricValid (25 / 1000)
#eval box260.decomposedBarycentricValid (26 / 1000)
#eval box260.decomposedBarycentricValid (27 / 1000)
#eval box260.decomposedBarycentricValid (24 / 1000)
