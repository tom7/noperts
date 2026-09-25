import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Nopert229

def box200 : AtlasProjectiveAnnularCertificate.Box := { TestEvalRealCage.box with δ := 200 / 1000000 }

#eval decide (box200.decomposedBarycentricValid (17 / 1000))
