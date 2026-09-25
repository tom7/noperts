import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .split .. => IO.println "Row is split"
  | .certificate .. => IO.println "Row is certificate"
  | .decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
      IO.println s!"Row 3253: c = {box.c}, delta = {box.δ}, r = {box.r}"
      IO.println s!"D0 = {D0}, r_min = {r_min}, c_cone = {c_cone}, c_core = {c_core}"
      let u0 := box.approxNormalizedCenter 0
      IO.println s!"u0 = ({u0 0}, {u0 1}, {u0 2})"

      let coreBox := box.withCoreAxis coreAxis c_core r_min
      let v := coreBox.approxNormalizedCenter 0
      IO.println s!"v = ({v 0}, {v 1}, {v 2})"

      -- Check decomposedBarycentricValid for current box
      let isValid := decide (box.decomposedBarycentricValid c_cone)
      IO.println s!"decomposedBarycentricValid(c_cone={c_cone}) = {isValid}"

      -- Check if we set box.c to smaller values
      for c_val in [1/5000, 1/10000, 1/20000] do
        let testBox := { box with c := c_val, δ := 4/10000000 }
        let valid := decide (testBox.decomposedBarycentricValid (9/200))
        IO.println s!"testBox(c={c_val}, c_cone=9/200): valid = {valid}"
