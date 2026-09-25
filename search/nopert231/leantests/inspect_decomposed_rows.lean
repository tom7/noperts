import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

open Noperthedron.Nopert229

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  for i in [0:table.size] do
    match table.get i with
    | .decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
        IO.println s!"Row {i} (id={id}): c_cone={c_cone}, c_core={c_core}, r_min={r_min}, c={box.c}, δ={box.δ}, r={box.r}"
    | _ => pure ()

