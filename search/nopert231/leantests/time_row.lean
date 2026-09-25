import Noperthedron.Nopert229.PackedLocalViewTree
import Noperthedron.Nopert229.SparseLocalViewTree

open Noperthedron.Nopert229
open Noperthedron.Nopert229.PackedLocalViewTree
open Noperthedron.Nopert229.SparseLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def validateAllRows (table : Table) : IO Unit := do
  IO.println s!"Validating {table.size} rows of Tree (r={table.r}, root={table.root})..."
  let start ← IO.monoNanosNow
  let mut splitCount := 0
  let mut certCount := 0
  let mut failCount := 0
  let checkRows := [7139]
  for i in checkRows do
    let rowStart ← IO.monoNanosNow
    let row := table.get i
    IO.print s!"Row {i} ({match row with | Row.split .. => "split" | Row.certificate .. => "cert" | Row.decomposed .. => "decomp"})... "
    (← IO.getStdout).flush
    let valid := decide (row.id = i ∧ SparseRowValidAt table.symmetryIndex table.r table.get table.size row)
    let rowStop ← IO.monoNanosNow
    let rowMs := (rowStop - rowStart) / 1000000
    IO.println s!"{if valid then "OK" else "FAIL"} in {rowMs} ms"
    if ¬valid then
      failCount := failCount + 1
      match row with
      | Row.decomposed _ box coreAxis defect0 D0 r_min c_cone c_core lam w =>
          IO.println s!"Row {i} Decomposed diagnostics:"
          IO.println s!"  box.r = {box.r}, table.r = {table.r}, r_check = {decide (table.r ≤ box.r)}"
          IO.println s!"  c_cone = {c_cone}, box.c = {box.c}, c_cone_eq = {decide (c_cone = box.c)}"
          IO.println s!"  r_min_nonneg = {decide (0 ≤ r_min)}"
          IO.println s!"  r_nonneg = {decide (0 ≤ box.r)}"
          IO.println s!"  delta_nonneg = {decide (0 ≤ box.δ)}"
          IO.println s!"  c_nonneg = {decide (0 ≤ box.c)}"
          IO.println s!"  bary = {decide (box.decomposedBarycentricValid c_cone)}"
          IO.println s!"  annular_dominance = {decide (((1/2 : ℚ) * box.r^2 * (box.certificate 0).B + D0)^2 ≤ r_min^2 * (1 - (1/4 : ℚ) * box.r^2) * ((c_cone - box.δ)^2 * (box.certificate 0).B^2))}"
          IO.println s!"  c_cone_margin = {decide (box.δ ≤ c_cone)}"
          IO.println s!"  c_core_margin = {decide (box.δ ≤ c_core)}"
          IO.println s!"  hdecomp = {decide ((box.withCoreAxis coreAxis c_core r_min).approxNormalizedCenter 0 = lam • box.approxNormalizedCenter 0 + w)}"
          IO.println s!"  hortho = {decide ((∑ i, (box.approxNormalizedCenter 0 i) * (w i)) = 0)}"
          IO.println s!"  hmargin = {decide (0 ≤ lam * c_cone - c_core)}"
          IO.println s!"  hineq = {decide ((∑ i, (w i) ^ 2) * ((∑ i, (box.approxNormalizedCenter 0 i) ^ 2) - c_cone^2) ≤ (∑ i, (box.approxNormalizedCenter 0 i) ^ 2) * (lam * c_cone - c_core)^2)}"
      | Row.certificate _ box =>
          IO.println s!"Row {i} Certificate diagnostics:"
          IO.println s!"  box.triangle = {box.triangle 0}, {box.triangle 1}, {box.triangle 2}"
          IO.println s!"  box.c = {box.c}, box.δ = {box.δ}, box.r = {box.r}"
          for j in [0, 1, 2, 3] do
            if hj : j < 4 then
              let ax := box.certificate ⟨j, hj⟩
              IO.println s!"  axis {j}: B = {ax.B}, edgeStart = {ax.edgeStart}, edgeFinish = {ax.edgeFinish}, mix = {ax.mix}"
          IO.println s!"  box.symmetryIndex = {box.symmetryIndex.1}, table.symmetryIndex = {table.symmetryIndex.1}, sym_eq = {decide (box.symmetryIndex = table.symmetryIndex)}"
          IO.println s!"  box.r = {box.r}, table.r = {table.r}, r_check = {decide (table.r ≤ box.r)}"
          IO.println s!"  barycentricValid = {decide box.barycentricValid}"
          IO.println s!"  variationRadiusSum = {decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)}"
          IO.println s!"  supportUpper = {decide (∀ j i k, box.supportUpper j i k ≤ 0)}"
          IO.println s!"  nonzeroWitness = {decide (∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)}"
          IO.println s!"  weightBudget = {decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)}"
          IO.println s!"  weightLower = {decide (∀ j i, 0 ≤ box.weightLower j i)}"
          IO.println s!"  angleBound = {decide (box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)}"
      | _ => IO.println s!"Row {i} FAILED validation!"

  let stop ← IO.monoNanosNow
  let totalMs := (stop - start) / 1000000
  IO.println s!"Done in {totalMs} ms! Valid splits: {splitCount}, valid certs: {certCount}, FAILED: {failCount}"

def main (args : List String) : IO Unit := do
  let filename := args.headD "local-view3.pack"
  let bytes ← IO.FS.readBinFile filename
  let root := if filename.contains "1" then 1 else if filename.contains "2" then 2 else if filename.contains "3" then 3 else 0
  let table := decodePackedByteArray root bytes
  validateAllRows table
