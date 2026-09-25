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
      let testBox : Box := { box with c := 1/100000, δ := 4/10000000 }
      let c_cone_val : ℚ := 38/1000
      IO.println s!"c_cone = {c_cone_val}:"
      for k in ([⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩] : List (Fin 6)) do
        let b := testBox.decomposedBarycentric c_cone_val k
        let min_b := min (min (b 0) (b 1)) (min (b 2) (b 3))
        IO.println s!"Target {k}: min_b = {min_b}"
  | _ => IO.println "Not decomposed"

