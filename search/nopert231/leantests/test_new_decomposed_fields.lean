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
  | .decomposed id box _ _ _ _ _ _ _ _ =>
      let ax0 : AxisCertificate := {
        edgeStart := ![3, 1, 14],
        edgeFinish := ![2, 4, 15],
        edgeStart₂ := ![2, 4, 15],
        edgeFinish₂ := ![1, 8, 19],
        mix := ![800, 800, 400],
        index := ![2, 4, 15],
        nonzeroWitness := ![1, 8, 19],
        B := 31962907 / 25000000
      }
      let ax1 : AxisCertificate := {
        edgeStart := ![3, 10, 14],
        edgeFinish := ![2, 15, 15],
        edgeStart₂ := ![2, 15, 15],
        edgeFinish₂ := ![1, 19, 19],
        mix := ![800, 400, 600],
        index := ![2, 15, 15],
        nonzeroWitness := ![1, 19, 19],
        B := 15852579 / 12500000
      }
      let ax2 : AxisCertificate := {
        edgeStart := ![3, 4, 14],
        edgeFinish := ![2, 8, 15],
        edgeStart₂ := ![2, 8, 15],
        edgeFinish₂ := ![1, 9, 19],
        mix := ![800, 600, 200],
        index := ![2, 8, 15],
        nonzeroWitness := ![1, 9, 19],
        B := 13028751 / 10000000
      }
      let ax3 : AxisCertificate := {
        edgeStart := ![3, 10, 14],
        edgeFinish := ![2, 15, 15],
        edgeStart₂ := ![2, 15, 15],
        edgeFinish₂ := ![1, 19, 19],
        mix := ![800, 600, 400],
        index := ![2, 15, 15],
        nonzeroWitness := ![1, 19, 19],
        B := 15852579 / 12500000
      }
      let coreAx : AxisCertificate := {
        edgeStart := ![3, 4, 15],
        edgeFinish := ![2, 8, 19],
        edgeStart₂ := ![2, 8, 19],
        edgeFinish₂ := ![1, 9, 3],
        mix := ![0, 666, 1000],
        index := ![2, 8, 19],
        nonzeroWitness := ![1, 9, 3],
        B := 309449531 / 500000000
      }
      let testBox : Box := {
        box with
        certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
        c := 18 / 10000,
        δ := 13 / 10000,
        r := 1 / 2000
      }
      let c_cone_val : ℚ := 133 / 10000
      let c_core_val : ℚ := 18 / 10000
      let r_min_val : ℚ := 1 / 10000
      let defect0_val : Fin 3 → ℚ := ![0, 0, 0]
      let D0_val : ℚ := 0

      IO.println "Testing NEW Certificate in Lean:"
      IO.println s!"  r_min_nonneg: {decide (0 ≤ r_min_val)}"
      IO.println s!"  r_nonneg: {decide (0 ≤ testBox.r)}"
      IO.println s!"  r_le_two: {decide (testBox.r ≤ 2)}"
      IO.println s!"  delta_nonneg: {decide (0 ≤ testBox.δ)}"
      IO.println s!"  c_nonneg: {decide (0 ≤ testBox.c)}"
      IO.println s!"  bary: {decide (testBox.decomposedBarycentricValid c_cone_val)}"
      IO.println s!"  D0_nonneg: {decide (0 ≤ D0_val)}"
      IO.println s!"  defect0_nonneg: {decide (∀ i, 0 ≤ defect0_val i)}"
      IO.println s!"  defect_budget0: {decide ((∑ i, testBox.weightUpper 0 i * defect0_val i) ≤ D0_val)}"
      IO.println s!"  c_cone_margin: {decide (testBox.δ ≤ c_cone_val)}"
      let B0 := (testBox.certificate 0).B
      let lhs := ((1 / 2 : ℚ) * testBox.r ^ 2 * B0 + D0_val) ^ 2
      let rhs := r_min_val ^ 2 * (1 - (1 / 4 : ℚ) * testBox.r ^ 2) * ((c_cone_val - testBox.δ) ^ 2 * B0 ^ 2)
      IO.println s!"  annular_dominance: {decide (lhs ≤ rhs)}"
      IO.println s!"  B_pos: {decide (∀ j, 0 < (testBox.certificate j).B)}"
      IO.println s!"  var: {decide (∀ j, testBox.variationRadiusSum j + 3 * variationError ≤ (testBox.certificate j).B * testBox.δ)}"
      IO.println s!"  supp: {decide (∀ j i k, testBox.supportUpper j i k ≤ if j = 0 then defect0_val i else 0)}"
      IO.println s!"  dir_nonzero: {decide (∀ j i, testBox.supportUpper j i ((testBox.certificate j).nonzeroWitness i) < 0)}"
      IO.println s!"  budget: {decide (∀ j, testBox.weightBudget j ≤ (testBox.certificate j).B)}"
      IO.println s!"  weight_nonneg: {decide (∀ j i, 0 ≤ testBox.weightLower j i)}"
      IO.println s!"  comp_angle: {decide (testBox.r ^ 2 * (1 + (testBox.c - testBox.δ) ^ 2) ≤ 4 * (testBox.c - testBox.δ) ^ 2)}"
      IO.println s!"  c_core_margin: {decide (testBox.δ ≤ c_core_val)}"
      IO.println s!"  core_B_pos: {decide (0 < coreAx.B)}"
      IO.println s!"  core_var: {decide ((testBox.withCoreAxis coreAx c_core_val r_min_val).variationRadiusSum 0 + 3 * variationError ≤ coreAx.B * testBox.δ)}"
      IO.println s!"  core_supp: {decide (∀ i k, (testBox.withCoreAxis coreAx c_core_val r_min_val).supportUpper 0 i k ≤ 0)}"
      IO.println s!"  core_dir_nonzero: {decide (∀ i, (testBox.withCoreAxis coreAx c_core_val r_min_val).supportUpper 0 i (coreAx.nonzeroWitness i) < 0)}"
      IO.println s!"  core_budget: {decide ((testBox.withCoreAxis coreAx c_core_val r_min_val).weightBudget 0 ≤ coreAx.B)}"
      IO.println s!"  core_weight_nonneg: {decide (∀ i, 0 ≤ (testBox.withCoreAxis coreAx c_core_val r_min_val).weightLower 0 i)}"
      IO.println s!"  core_weight_pos: {decide (∃ i, 0 < (testBox.withCoreAxis coreAx c_core_val r_min_val).weightLower 0 i)}"
      IO.println s!"  core_angle: {decide (r_min_val ^ 2 * (1 + (c_core_val - testBox.δ) ^ 2) ≤ 4 * (c_core_val - testBox.δ) ^ 2)}"
      IO.println s!"  c_cone_pos: {decide (0 < c_cone_val)}"
      IO.println s!"  c_margin: {decide (testBox.δ ≤ testBox.c)}"
      IO.println s!"  c_sum_pos: {decide (0 < testBox.c + testBox.δ)}"
  | _ => IO.println "Not decomposed"
