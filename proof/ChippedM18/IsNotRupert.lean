module

public import ChippedM18.SolutionTree
public import Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The 19-vertex solid (ChippedM18) is not Rupert, given valid tables

`verts` is the ChippedM18's vertex set (the 19 rational vertices of
`ModelData`), whose convex hull is `solid`.
`not_rupert_of_valid_tables`: four valid chart tables
(`SolutionTree.Table.Valid`, with their shared identity-tube tables) and a
checked cap certificates (`SolutionTree.CapOk`, `SolutionTree.ArcOk`) give `¬ IsRupert verts`, in the
vertex-set form of `MainTheorem.IsRupert` (as the DH's
`not_rupert_of_valid_tables`).
-/

namespace ChippedM18
open Noperts

open Noperts.Pipeline
open SolutionTree

/-- The vertices of the ChippedM18. -/
noncomputable def verts : Finset ℝ³ := Finset.univ.image fun i : Fin 19 => toR3 (vertexQ i)

theorem convexHull_verts : convexHull ℝ (verts : Set ℝ³) = solid := by
  unfold verts solid Polyhedron.hull poly
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

theorem exists_matrixPose_of_rupertSet {S : Set ℝ³} (h : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, innerSO3, offset, outer, outerSO3, hshadow⟩ := h
  let p : MatrixPose := MatrixPose.mk ⟨inner, innerSO3⟩ ⟨outer, outerSO3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact hshadow

/-- **The ChippedM18 is not Rupert**, given four valid chart tables and checked cap and
arc cap certificates. -/
theorem not_rupert_of_valid_tables (table : CayleyAtlas.ChartIndex → SolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) (hcap : CapOk) (harc : ArcOk) :
    ¬ IsRupert verts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ (verts : Set ℝ³)) :=
    (rupert_iff_rupert_set verts).mp hrupert
  rw [convexHull_verts] at hset
  exact no_matrixPose_of_valid_tables table hchart hvalid hcap harc
    (exists_matrixPose_of_rupertSet hset)

end ChippedM18
