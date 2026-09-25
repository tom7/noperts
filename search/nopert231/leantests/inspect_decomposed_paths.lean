import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

open Noperthedron.Nopert229

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let rows := [3253, 7135, 11638, 11639, 11640, 11661]
  for r in rows do
    match table.get r with
    | .decomposed id box _ _ _ _ _ _ _ _ =>
        IO.println s!"Row {r}: root={box.root}, delta={box.δ}, r={box.r}, c={box.c}"
    | _ => pure ()

