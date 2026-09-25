import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def b260 : Box := { box with δ := 260 / 1000000 }

#eval b260.decomposedBarycentricValid (17 / 1000)
#eval b260.decomposedBarycentricValid (18 / 1000)
#eval b260.decomposedBarycentricValid (19 / 1000)
#eval b260.decomposedBarycentricValid (20 / 1000)
#eval b260.decomposedBarycentricValid (25 / 1000)
