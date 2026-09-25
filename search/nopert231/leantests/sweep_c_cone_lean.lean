import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def box200 : AtlasProjectiveLocalCertificate.Box := { box with δ := 200 / 1000000 }

#eval decide (box200.decomposedBarycentricValid (25 / 1000))
#eval decide (box200.decomposedBarycentricValid (26 / 1000))
#eval decide (box200.decomposedBarycentricValid (27 / 1000))
#eval decide (box200.decomposedBarycentricValid (28 / 1000))
#eval decide (box200.decomposedBarycentricValid (29 / 1000))
#eval decide (box200.decomposedBarycentricValid (30 / 1000))
