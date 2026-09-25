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
      -- Depth 26 has delta = 38/1000000000
      let d26_delta : ℚ := 38/1000000000
      for c_inv in [10000, 20000, 50000, 100000, 200000, 500000] do
        let c_val : ℚ := 1 / c_inv
        let testBox : Box := { box with c := c_val, δ := d26_delta }
        for c_cone_num in [10, 15, 20, 25, 30, 35, 38, 40] do
          let c_cone_val : ℚ := c_cone_num / 1000
          if testBox.decomposedBarycentricValid c_cone_val then
            IO.println s!"FOUND WINNER AT DEPTH 26! c_cone = {c_cone_val}, c = 1/{c_inv}!"
  | _ => IO.println "Not decomposed"

