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
      let c_val : ℚ := 1 / 100000
      let testBox : Box := { box with c := c_val, δ := d26_delta }
      for c_cone_num in [10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40] do
        let c_cone_val : ℚ := c_cone_num / 1000
        let ok := decide (testBox.decomposedBarycentricValid c_cone_val)
        IO.println s!"c_cone = {c_cone_val}: {ok}"
  | _ => IO.println "Not decomposed"

