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
  | .decomposed id box coreAxis defect0 D0 r_min _ c_core lam w =>
      -- Supply tuned parameters
      let c_cone_val : ℚ := 3 / 200 -- 0.015
      let c_val : ℚ := 1 / 1000
      let testBox : Box := { box with c := c_val }
      IO.println s!"Testing Row 3253 with c_cone = {c_cone_val}, c = {c_val}:"
      IO.println s!"  r_min_nonneg: {decide (0 ≤ r_min)}"
      IO.println s!"  r_nonneg: {decide (0 ≤ testBox.r)}"
      IO.println s!"  r_le_two: {decide (testBox.r ≤ 2)}"
      IO.println s!"  delta_nonneg: {decide (0 ≤ testBox.δ)}"
      IO.println s!"  c_nonneg: {decide (0 ≤ testBox.c)}"
      IO.println s!"  bary: {decide (testBox.decomposedBarycentricValid c_cone_val)}"
      IO.println s!"  D0_nonneg: {decide (0 ≤ D0)}"
      IO.println s!"  defect0_nonneg: {decide (∀ i, 0 ≤ defect0 i)}"
      IO.println s!"  defect_budget0: {decide ((∑ i, testBox.weightUpper 0 i * defect0 i) ≤ D0)}"
      IO.println s!"  c_cone_margin: {decide (testBox.δ ≤ c_cone_val)}"
      let B0 := (testBox.certificate 0).B
      let lhs := ((1 / 2 : ℚ) * testBox.r ^ 2 * B0 + D0) ^ 2
      let rhs := r_min ^ 2 * (1 - (1 / 4 : ℚ) * testBox.r ^ 2) * ((c_cone_val - testBox.δ) ^ 2 * B0 ^ 2)
      IO.println s!"  annular_dominance: {decide (lhs ≤ rhs)}"
      IO.println s!"  B_pos: {decide (∀ j, 0 < (testBox.certificate j).B)}"
      IO.println s!"  var: {decide (∀ j, testBox.variationRadiusSum j + 3 * variationError ≤ (testBox.certificate j).B * testBox.δ)}"
      IO.println s!"  supp: {decide (∀ j i k, testBox.supportUpper j i k ≤ if j = 0 then defect0 i else 0)}"
      IO.println s!"  dir_nonzero: {decide (∀ j i, testBox.supportUpper j i ((testBox.certificate j).nonzeroWitness i) < 0)}"
      IO.println s!"  budget: {decide (∀ j, testBox.weightBudget j ≤ (testBox.certificate j).B)}"
      IO.println s!"  weight_nonneg: {decide (∀ j i, 0 ≤ testBox.weightLower j i)}"
      IO.println s!"  comp_angle: {decide (testBox.r ^ 2 * (1 + (testBox.c - testBox.δ) ^ 2) ≤ 4 * (testBox.c - testBox.δ) ^ 2)}"
      IO.println s!"  c_core_margin: {decide (testBox.δ ≤ c_core)}"
      IO.println s!"  core_B_pos: {decide (0 < coreAxis.B)}"
      IO.println s!"  c_cone_pos: {decide (0 < c_cone_val)}"
      IO.println s!"  c_margin: {decide (testBox.δ ≤ testBox.c)}"
      IO.println s!"  c_sum_pos: {decide (0 < testBox.c + testBox.δ)}"
  | _ => IO.println "Not decomposed"

