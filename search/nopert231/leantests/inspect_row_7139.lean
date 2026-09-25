import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.PackedLocalViewTree
open Noperthedron.Nopert229.SparseLocalViewTree

def main : IO Unit := do
  let table ← loadTableFromPackedFile "/tmp/test_export_0.pack" 0
  let row := table.get 7139
  match row with
  | Row.certificate _ box =>
      IO.println s!"Row 7139 box.triangle = {box.triangle 0}, {box.triangle 1}, {box.triangle 2}"
      IO.println s!"box.c = {box.c}, box.δ = {box.δ}, box.r = {box.r}"
      for j in [0, 1, 2, 3] do
        if hj : j < 4 then
          let ax := box.certificate ⟨j, hj⟩
          IO.println s!"axis {j}: B = {ax.B}, edgeStart = {ax.edgeStart}, edgeFinish = {ax.edgeFinish}, mix = {ax.mix}"
  | _ => IO.println "Not a certificate row"
