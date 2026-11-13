module

public import Minimality.HullChain
public import Minimality.TriShadow2
public import Minimality.TriBridge

@[expose] public section

/-!
# Lemma T for two facets sharing an edge

The edge analogue of `TriFacets.lean`: two facets `Q1`, `Q2` of `V` sharing the
edge `v w`, viewed along it.  If every point off both facets projects strictly
inside the triangle of the edge's shadow point and the far points of the two
facets, `V` is Rupert (the edge views of Theorems E–L of
`FEWER-FACES-PROOFS.md` §7).  The chains come from `exists_chainOK_edge`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- `orient_ne_of_frame1` for any two distinct points of the first ray's plane. -/
theorem orient_ne_of_frame1' {O r1 r2 : ℝ²} {ai zi aj zj ak zk : ℝ} (hij : (ai, zi) ≠ (aj, zj))
    (h : ∀ c : ℝ, oblPt O r1 r2 ak 0 zk - oblPt O r1 r2 ai 0 zi ≠
      c • (oblPt O r1 r2 aj 0 zj - oblPt O r1 r2 ai 0 zi)) :
    orient2 ai zi aj zj ak zk ≠ 0 := by
  by_cases ha : ai = aj
  · have hz : zj - zi ≠ 0 := fun e => hij (by rw [ha, show zi = zj by linarith])
    intro h0
    unfold orient2 at h0
    rw [ha, sub_self, zero_mul, zero_sub, neg_eq_zero] at h0
    have hk : ak = aj := by
      have := (mul_eq_zero.mp h0).resolve_left hz; linarith
    apply h ((zk - zi) / (zj - zi))
    rw [ha, hk]
    ext j; fin_cases j <;> simp [oblPt]
    field_simp
  · exact orient_ne_of_frame1 ha h

/-- The same on the second ray's plane. -/
theorem orient_ne_of_frame2' {O r1 r2 : ℝ²} {bi zi bj zj bk zk : ℝ} (hij : (bi, zi) ≠ (bj, zj))
    (h : ∀ c : ℝ, oblPt O r1 r2 0 bk zk - oblPt O r1 r2 0 bi zi ≠
      c • (oblPt O r1 r2 0 bj zj - oblPt O r1 r2 0 bi zi)) :
    orient2 bi zi bj zj bk zk ≠ 0 := by
  by_cases hb : bi = bj
  · have hz : zj - zi ≠ 0 := fun e => hij (by rw [hb, show zi = zj by linarith])
    intro h0
    unfold orient2 at h0
    rw [hb, sub_self, zero_mul, zero_sub, neg_eq_zero] at h0
    have hk : bk = bj := by
      have := (mul_eq_zero.mp h0).resolve_left hz; linarith
    apply h ((zk - zi) / (zj - zi))
    rw [hb, hk]
    ext j; fin_cases j <;> simp [oblPt]
    field_simp
  · exact orient_ne_of_frame2 hb h

/-- General position for Lemma T along an edge `v w` shared by two facets `Q1`,
`Q2`: no other segment of `V` is parallel to the edge, and the far ends of the
two faces in the shadow (the point of `Q1` where `f2` is least, that of `Q2`
where `f1` is least) have distinct depths along it. Weaker than `GenPos` with
distinct depths on all of `V` (`EdgeFar.of_genPos`). -/
def EdgeFar (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v)) ∧
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      ⟪p, w - v⟫ ≠ ⟪q, w - v⟫

end Minimality

end
