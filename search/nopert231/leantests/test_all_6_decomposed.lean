import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let rows := [3253, 7135, 11638, 11639, 11640, 11661]
  for r in rows do
    match table.get r with
    | .decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
        let ok := decide (box.DecomposedViewValid coreAxis defect0 D0 r_min c_cone c_core lam w)
        IO.println s!"Row {r} (id={id}): DecomposedViewValid = {ok}"
    | _ => IO.println s!"Row {r}: not decomposed"

