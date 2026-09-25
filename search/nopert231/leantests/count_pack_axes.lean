import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

open Noperthedron.Nopert229

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  IO.println s!"Total rows: {table.size}"
  let mut split_count := 0
  let mut cert_count := 0
  let mut decomposed_count := 0
  for i in [0:table.size] do
    match table.get i with
    | .split .. => split_count := split_count + 1
    | .certificate .. => cert_count := cert_count + 1
    | .decomposed .. => decomposed_count := decomposed_count + 1
  IO.println s!"Split rows: {split_count}"
  IO.println s!"Certificate rows: {cert_count}"
  IO.println s!"Decomposed rows: {decomposed_count}"

