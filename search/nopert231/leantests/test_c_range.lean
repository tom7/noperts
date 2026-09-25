import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .decomposed _ box _ _ _ _ _ _ _ _ =>
      let d26_delta : ℚ := 38/1000000000
      let c_cone_val : ℚ := 3/200
      for c_inv in [500, 1000, 2000, 3000, 4000, 5000, 6000, 8000, 10000] do
        let c_val : ℚ := 1 / c_inv
        let testBox : Box := { box with c := c_val, δ := d26_delta }
        let ok := decide (testBox.decomposedBarycentricValid c_cone_val)
        IO.println s!"c = 1/{c_inv}: {ok}"
  | _ => IO.println "Not decomposed"

