import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView
open Noperthedron.BalancedSupport

-- Load node 03121303200 box:
def test_triangle : TriangleQ := {
  corners := ![
    ![1102553147814983/1099511627776, 219702280261179/1099511627776, 680671607599023/1099511627776],
    ![1102542490538185/1099511627776, 219702280261179/1099511627776, 680688863673419/1099511627776],
    ![1102542490538185/1099511627776, 219709772390141/1099511627776, 680686443420822/1099511627776]
  ]
}

-- Let's check with an actual test script using lake env lean
