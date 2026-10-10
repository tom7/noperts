module

public import Pipeline.SparseLocalViewTree
public import SnubDodecahedron.SolidModel
public import SnubDodecahedron.GeneratedTangentCones
public import SnubDodecahedron.TangentCones

@[expose] public section

/-!
# Sparse support checks

For a linear functional to be maximized at a vertex of a polytope, it is
enough to compare that vertex with the generators of its tangent cone
(`TangentCones`). The rational checker model has at most seven such
generators at each vertex. This reduces the repeated local-certificate
support check from all sixty vertices to seven (with padding entries equal
to the selected vertex).
-/

open Noperts Noperts.Pipeline

namespace SnubDodecahedron.SparseSupport


open Noperts.Checker
open AtlasProjectiveView
open AtlasProjectiveLocalCertificate

theorem crossQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    LocalCertificate.crossQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l • LocalCertificate.crossQ u (v l) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [LocalCertificate.crossQ, Fin.sum_univ_three] <;>
    ring

theorem dotQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    AtlasProjectiveEdgeCertificate.dotQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l * AtlasProjectiveEdgeCertificate.dotQ u (v l) := by
  simp [AtlasProjectiveEdgeCertificate.dotQ, Fin.sum_univ_three]
  ring

theorem supportAt_eq_sum
    (combination : TangentCombination) (box : Box)
    (j : Fin 4) (corner : Fin 3) (i : Fin 3) (target : VertexIndex)
    (hcombination : combination.Valid
      ((box.certificate j).supportIndex box i) target) :
    box.supportAt j corner i target =
      ∑ l, combination.coefficient l *
        box.supportAt j corner i
          (supportGenerator ((box.certificate j).supportIndex box i)
            (combination.generator l)) := by
  have hdelta : Noperts.Pipeline.rationalVertex target -
      Noperts.Pipeline.rationalVertex ((box.certificate j).supportIndex box i) = _ :=
    hcombination.2.2.2
  unfold Box.supportAt AxisCertificate.deltaQ
  rw [hdelta]
  rw [crossQ_sum3, dotQ_sum3]
  rfl

/-- Fast decision of one contact's tangent-generator support checks in
compiled code (the contact's edge is evaluated once; see
`Box.supportListOK`). -/
@[reducible] instance (priority := high) (box : Box) (j : Fin 4) (i : Fin 3) :
    Decidable (∀ generator : Fin 7, box.supportUpper j i
      (supportGenerator ((box.certificate j).supportIndex box i) generator) ≤ 0) :=
  decidable_of_iff (box.supportListOK j i ((List.finRange 7).map
      (supportGenerator ((box.certificate j).supportIndex box i))) = true)
    (by simp [Box.supportListOK_iff, List.mem_finRange])

@[mk_iff]
structure Box.SparseViewValid (box : Box) : Prop where
  triangle_valid :
    AtlasProjectiveEdgeCertificate.SignedTriangleValid box.root box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  r_nonneg : 0 ≤ box.r
  B_pos : ∀ j, 0 < (box.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.weightLower j i
  support_generators : ∀ j i generator,
    box.supportUpper j i
      (supportGenerator ((box.certificate j).supportIndex box i) generator) ≤ 0
  /-- Exact cone-boundary directions can tie a second edge endpoint.  The
  tangent-generator reduction spends strict approximation slack and therefore
  cannot propagate through that zero-slack generator; for just these rare
  axes, check all twenty support vertices directly. -/
  support_boundary : ∀ j i,
    ((box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000) →
    ∀ target, box.supportUpper j i target ≤ 0
  direction_nonzero : ∀ j i,
    box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.weightBudget j ≤ (box.certificate j).B
  variation : ∀ j,
    box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ
  barycentric : box.barycentricValid
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

@[reducible] instance (box : Box) : Decidable (Box.SparseViewValid box) :=
  decidable_of_iff _ (Box.sparseViewValid_iff box).symm

theorem Box.SparseViewValid.support_all {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) :
    ∀ j i target, box.supportUpper j i target ≤ 0 := by
  intro j i target
  by_cases hboundary : (box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000
  · exact h.support_boundary j i hboundary target
  · have hzero : (box.certificate j).mix i ≠ 0 :=
      fun hz => hboundary (Or.inl hz)
    have hthousand : (box.certificate j).mix i ≠ 1000 :=
      fun ht => hboundary (Or.inr ht)
    let base := (box.certificate j).supportIndex box i
    by_cases htie : target = base
    · simp [Box.supportUpper, Box.exactSupportTie, base, htie]
    · let selected := combination base target
      have htie' : target ≠ (box.certificate j).supportIndex box i := by
        simpa [base] using htie
      have hselected : selected.Valid base target := htangent base target htie
      have hat (corner : Fin 3) :
          box.supportAt j corner i target ≤ -supportError := by
        rw [supportAt_eq_sum selected box j corner i target hselected]
        calc
          ∑ l, selected.coefficient l *
                box.supportAt j corner i
                  (supportGenerator base (selected.generator l)) ≤
              ∑ l, selected.coefficient l * (-supportError) := by
            apply Finset.sum_le_sum
            intro l _
            by_cases hcoefficient : selected.coefficient l = 0
            · simp [hcoefficient]
            · have hgenerator :
                  supportGenerator base (selected.generator l) ≠ base :=
                hselected.2.2.1 l hcoefficient
              have hsparse := h.support_generators j i (selected.generator l)
              have hgenerator' :
                  supportGenerator
                      ((box.certificate j).supportIndex box i)
                      (selected.generator l) ≠
                    (box.certificate j).supportIndex box i := by
                simpa [base] using hgenerator
              have hcorner := AtlasProjectiveEdgeCertificate.le_max3
                (fun c => box.supportAt j c i
                  (supportGenerator base (selected.generator l))) corner
              have hraw : box.supportAt j corner i
                    (supportGenerator base (selected.generator l)) ≤
                  -supportError := by
                simp [Box.supportUpper, Box.exactSupportTie, hgenerator',
                  hzero, hthousand] at hsparse
                linarith
              exact mul_le_mul_of_nonneg_left hraw (hselected.1 l)
          _ = -supportError * ∑ l, selected.coefficient l := by
            simp only [Fin.sum_univ_three]
            ring
          _ ≤ -supportError := by
            have herror : 0 < supportError := by
              decide +kernel
            nlinarith [hselected.2.1]
      simp [Box.supportUpper, Box.exactSupportTie, htie', hzero,
        hthousand]
      have hmax :
          AtlasProjectiveEdgeCertificate.max3
              (fun corner => box.supportAt j corner i target) ≤
            -supportError := by
        simp only [AtlasProjectiveEdgeCertificate.max3, max_le_iff]
        exact ⟨hat 0, hat 1, hat 2⟩
      linarith

theorem Box.SparseViewValid.toViewValid {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) : box.ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support_all combination htangent
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

end SnubDodecahedron.SparseSupport

namespace SnubDodecahedron

open Noperts.Pipeline SparseSupport

/-- The snub dodecahedron's native checker validates certificate rows by
`Box.SparseViewValid` (tangent-cone generators; sound by the kernel-checked
tangent-cone table `GeneratedTangentCones.table_valid_kernel`) instead of the
default check against every vertex. A scoped instance, in effect inside
`namespace SnubDodecahedron`. -/
@[reducible] scoped instance certificateViewCheck :
    SparseLocalViewTree.CertificateViewCheck where
  Valid := Box.SparseViewValid
  decValid _ := inferInstance
  toViewValid h := h.toViewValid GeneratedTangentCones.table
    GeneratedTangentCones.table_valid_kernel

end SnubDodecahedron

end
