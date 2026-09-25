import Noperthedron.Nopert229.PackedLocalViewTree

open Noperthedron.Nopert229

def main : IO Unit := do
  let data ← IO.FS.readFile "local-view0.pack"
  IO.println s!"Read {data.length} characters from local-view0.pack."
  let table := PackedLocalViewTree.decodePackedTable 0 data
  IO.println s!"Decoded table size: {table.size}, r: {table.r}"
