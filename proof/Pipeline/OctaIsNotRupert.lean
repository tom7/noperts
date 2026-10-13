module

public import Pipeline.OctaSolutionTree
public import Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The non-Rupert conclusion from valid octahedral tables

The bridge of `Pipeline.IsNotRupert`, for the octahedral trees: four valid
Cayley-chart tables, the cover check and the cap claims exclude every Rupert
pose of an `OModel`, in the vertex-set formulation of the Rupert property.
-/

open scoped Matrix

open Noperts Noperts.Pipeline

namespace Noperts.Pipeline.OctaSolutionTree

variable [OctahedralSolid] [OctaCodeTriangleCover] [OctaCaps]

open CayleyAtlas

omit [OctahedralSolid] [OctaCodeTriangleCover] [OctaCaps] in
private lemma octa_rupert_set_implies_matrix_pose {S : Set ℝ³}
    (h : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, innerSO3, offset, outer, outerSO3, hshadow⟩ := h
  let p : MatrixPose :=
    MatrixPose.mk ⟨inner, innerSO3⟩ ⟨outer, outerSO3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact hshadow

/-- Valid exclusion tables for all four Cayley charts prove that no
octahedral model (`OModel`) whose hull satisfies the cap claims is Rupert. -/
theorem not_rupert_of_valid_tables (Q : OModel)
    (table : ChartIndex → OctaSolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) (hcover : octaCoverValid = true)
    (hcaps : OctaCaps.CapsHold Q.toC4.polyhedron.hull) :
    ¬ IsRupert Q.toC4.verts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ Q.toC4.verts) :=
    (rupert_iff_rupert_set Q.toC4.verts).mp hrupert
  rw [← Q.toC4.polyhedron_hull] at hset
  exact no_matrixPose_of_valid_tables Q table hchart hvalid hcover hcaps
    (octa_rupert_set_implies_matrix_pose hset)

end Noperts.Pipeline.OctaSolutionTree

end
