import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def main : IO Unit := do
  let packed ← IO.FS.readFile "local-view0.pack"
  let table := PackedLocalViewTree.decodePackedTable 0 packed
  let row := table.get 3253
  match row with
  | .split .. => IO.println "Row 3253 is split"
  | .certificate .. => IO.println "Row 3253 is certificate"
  | .decomposed id box coreAxis defect0 D0 r_min c_cone c_core lam w =>
      IO.println s!"Row 3253 decomposed: id={id}"
      IO.println s!"bary: {decide (box.decomposedBarycentricValid c_cone)}"
      IO.println s!"annular_dominance: {decide (((1/2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1/4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))}"
      IO.println s!"c_cone_margin: {decide (box.δ ≤ c_cone)}"
      IO.println s!"core_angle: {decide (r_min ^ 2 * (1 + (c_core - box.δ) ^ 2) ≤ 4 * (c_core - box.δ) ^ 2)}"
      IO.println s!"hmargin: {decide (0 ≤ lam * c_cone - c_core)}"
      let u_sq := (box.approxNormalizedCenter 0 0)^2 + (box.approxNormalizedCenter 0 1)^2 + (box.approxNormalizedCenter 0 2)^2
      let w_sq := (w 0)^2 + (w 1)^2 + (w 2)^2
      IO.println s!"hineq: {decide (w_sq * (u_sq - c_cone^2) ≤ u_sq * (lam * c_cone - c_core)^2)}"
      IO.println s!"Row.ValidAt: {decide (row.ValidAt table.symmetryIndex table.r table.get table.size)}"
