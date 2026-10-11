module

public import Pipeline.SparseLocalViewTree

@[expose] public section

/-!
# Sparse support checks from tangent cones

For a linear functional to be maximized at a vertex `v` of a polytope, it is
enough that it does not increase along the edges at `v`, i.e. towards the
generators of `v`'s tangent cone. A solid whose rational model has at most
seven such generators at each vertex (`TangentCones.supportGenerator`,
padded with the vertex itself) can check the support condition of the
identity-tube certificate rows against those seven vertices instead of all
of them (`Box.SparseViewValid`). This is sound because every other vertex
`w` lies in the tangent cone at `v`: `w - v` is a nonnegative combination,
with coefficients summing to at least 1, of three generator directions
(`TangentCones.tangent`; each solid proves it from a kernel-checked table).

`TangentCones.certificateViewCheck` is the resulting certificate-row check
for the native local-table checker (`SparseLocalViewTree.CertificateViewCheck`).
The snub dodecahedron and candidate #231 provide `TangentCones` and this
check as scoped instances.
-/

namespace Noperts.Pipeline.SparseSupport

variable [SolidModel]

open Noperts.Checker
open AtlasProjectiveView
open AtlasProjectiveLocalCertificate

/-- Tangent-cone generators of a solid's rational vertices, and the fact
that every other vertex lies in the tangent cone they span (see the module
documentation). -/
class TangentCones where
  /-- The (at most seven) tangent-cone generators of each vertex, padded by
  the vertex itself. -/
  supportGenerator : VertexIndex → Fin 7 → VertexIndex
  /-- Every vertex `target ≠ base` is `base` plus a nonnegative combination,
  with coefficients summing to at least 1, of three generator directions. -/
  tangent : ∀ base target, target ≠ base →
    ∃ generator : Fin 3 → Fin 7, ∃ coefficient : Fin 3 → ℚ,
      (∀ l, 0 ≤ coefficient l) ∧
      1 ≤ ∑ l, coefficient l ∧
      (∀ l, coefficient l ≠ 0 → supportGenerator base (generator l) ≠ base) ∧
      rationalVertex target - rationalVertex base =
        ∑ l, coefficient l •
          (rationalVertex (supportGenerator base (generator l)) - rationalVertex base)
  /-- The support slack is positive (the model error is). -/
  supportError_pos : 0 < supportError

variable [TangentCones]

open TangentCones (supportGenerator)

omit [SolidModel] [TangentCones] in
theorem crossQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    LocalCertificate.crossQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l • LocalCertificate.crossQ u (v l) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [LocalCertificate.crossQ, Fin.sum_univ_three] <;>
    ring

omit [SolidModel] [TangentCones] in
theorem dotQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    AtlasProjectiveEdgeCertificate.dotQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l * AtlasProjectiveEdgeCertificate.dotQ u (v l) := by
  simp [AtlasProjectiveEdgeCertificate.dotQ, Fin.sum_univ_three]
  ring

omit [TangentCones] in
theorem supportAt_eq_sum (base : VertexIndex) (generators : Fin 7 → VertexIndex)
    (generator : Fin 3 → Fin 7) (coefficient : Fin 3 → ℚ) (box : Box)
    (j : Fin 4) (corner : Fin 3) (i : Fin 3) (target : VertexIndex)
    (hbase : base = (box.certificate j).supportIndex box i)
    (hdelta : rationalVertex target - rationalVertex base =
      ∑ l, coefficient l • (rationalVertex (generators (generator l)) - rationalVertex base)) :
    box.supportAt j corner i target =
      ∑ l, coefficient l * box.supportAt j corner i (generators (generator l)) := by
  subst hbase
  unfold Box.supportAt AxisCertificate.deltaQ
  rw [hdelta]
  rw [crossQ_sum3, dotQ_sum3]

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
  axes, check all support vertices directly. -/
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
    (h : Box.SparseViewValid box) :
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
    · obtain ⟨generator, coefficient, hcoef_nonneg, hcoef_sum, hgen, hdelta⟩ :=
        TangentCones.tangent base target htie
      have htie' : target ≠ (box.certificate j).supportIndex box i := by
        simpa [base] using htie
      have hat (corner : Fin 3) :
          box.supportAt j corner i target ≤ -supportError := by
        rw [supportAt_eq_sum base (supportGenerator base) generator coefficient box j corner i
          target rfl hdelta]
        calc
          ∑ l, coefficient l *
                box.supportAt j corner i
                  (supportGenerator base (generator l)) ≤
              ∑ l, coefficient l * (-supportError) := by
            apply Finset.sum_le_sum
            intro l _
            by_cases hcoefficient : coefficient l = 0
            · simp [hcoefficient]
            · have hgenerator :
                  supportGenerator base (generator l) ≠ base :=
                hgen l hcoefficient
              have hsparse := h.support_generators j i (generator l)
              have hgenerator' :
                  supportGenerator
                      ((box.certificate j).supportIndex box i)
                      (generator l) ≠
                    (box.certificate j).supportIndex box i := by
                simpa [base] using hgenerator
              have hraw : box.supportAt j corner i
                    (supportGenerator base (generator l)) ≤
                  -supportError := by
                have hcorner := AtlasProjectiveEdgeCertificate.le_max3
                  (fun c => box.supportAt j c i
                    (supportGenerator base (generator l))) corner
                simp [Box.supportUpper, Box.exactSupportTie, hgenerator',
                  hzero, hthousand] at hsparse
                linarith
              exact mul_le_mul_of_nonneg_left hraw (hcoef_nonneg l)
          _ = -supportError * ∑ l, coefficient l := by
            simp only [Fin.sum_univ_three]
            ring
          _ ≤ -supportError := by
            have herror : 0 < supportError := TangentCones.supportError_pos
            nlinarith [hcoef_sum]
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
    (h : Box.SparseViewValid box) : box.ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support_all
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

/-- The native checker's certificate-row check for a solid with
`TangentCones`: `Box.SparseViewValid` (seven tangent-cone generators per
support vertex) instead of the default check against every vertex. -/
@[reducible] def TangentCones.certificateViewCheck :
    SparseLocalViewTree.CertificateViewCheck where
  Valid := Box.SparseViewValid
  decValid _ := inferInstance
  toViewValid h := h.toViewValid

end Noperts.Pipeline.SparseSupport

end
