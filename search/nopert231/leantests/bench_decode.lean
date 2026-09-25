import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.PackedLocalViewTree
open Noperthedron.Nopert229.SparseLocalViewTree

def main : IO Unit := do
  let bytes ← IO.FS.readBinFile "local-view0.pack"
  let table := decodePackedByteArray 0 bytes
  IO.println s!"Decoded table with {table.size} rows"

  let mut invalidCount := 0
  for i in [0:table.size] do
    let v := sparseValidIxAtB table.symmetryIndex table.r table.get table.size i
    if !v then
      IO.println s!"Row {i} is INVALID!"
      invalidCount := invalidCount + 1
      if invalidCount > 10 then break
    if i % 10000 = 0 then
      IO.println s!"Checked {i}/{table.size} rows..."
  IO.println s!"Finished check with {invalidCount} invalid rows"
