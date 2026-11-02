module

public import Minimality.Type08S.C2K20B

@[expose] public section


/-!
# K20 / C: triangle with three tops at positive heights, plus a base point beyond an edge

`V = {(o,0), (s,0), (t,0), (e,0), (o,h0), (s,h1), (t,h2)}` with `(o,s,t)` ccw and `e` strictly beyond the edge `s t`
(`cross2 (e - s) (t - e) > 0`): Rupert (`k20_triExt`).  The tilt `v` is `v0 + t u` with `v0 = (e - s) - (t - e)`
(pointing out of the polygon at `e`) and `u` generic; the extra point `e` gets the corner certificate `(s, e, t)`
once `λ` is large.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k20_vel (κ ψ lam : ℝ) (M v q : ℝ²) (z : ℝ) :
    proj_xy (cross (k20ω κ ψ v) (liftPt q z) + k20τ ψ lam M v) =
      ψ • rot90 (q - M) - lam • v + (z * κ) • v := by
  ext i; fin_cases i <;> simp [cross, liftPt, proj_xy, rot90, k20ω, k20τ] <;> ring

theorem k20_affine_neg {c d : ℝ} (hc : c < 0) : ∃ δ > 0, ∀ t, 0 < t → t < δ → c + t * d < 0 := by
  refine ⟨-c / (|d| + 1), div_pos (by linarith) (by positivity), fun t ht htδ => ?_⟩
  have h1 : t * d ≤ t * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) ht.le
  have h2 : t * (|d| + 1) < -c := by rwa [lt_div_iff₀ (by positivity)] at htδ
  nlinarith [abs_nonneg d]

/-- A tilt direction generic for the triangle and pointing out at `e` (`cross2 (e-s) v < 0`, `cross2 (t-e) v < 0`). -/
theorem k20_pick_v (o s t e : ℝ²) (hccw : 0 < cross2 (s - o) (t - o)) (hE : 0 < cross2 (e - s) (t - e)) :
    ∃ v : ℝ², (∀ i, cross2 (tri o s t (i + 1) - tri o s t i) v ≠ 0) ∧
      (∀ i j, i ≠ j → ⟪v, tri o s t i - tri o s t j⟫ ≠ 0) ∧
      cross2 (e - s) v < 0 ∧ cross2 (t - e) v < 0 := by
  classical
  have hp := isCcwPolygon_tri hccw
  set p := tri o s t
  obtain ⟨u, hu1, hu2⟩ := exists_generic_dir (ι := ZMod 3)
    (κ := {q : ZMod 3 × ZMod 3 // q.1 ≠ q.2}) (fun i => p (i + 1) - p i)
    (fun i => hp.edge_ne_zero i) (fun q => p q.1.1 - p q.1.2)
    (fun q => sub_ne_zero.mpr (hp.injective.ne q.2))
  set v0 : ℝ² := (e - s) - (t - e)
  have g1 : cross2 (e - s) v0 < 0 := by
    have : cross2 (e - s) v0 = -cross2 (e - s) (t - e) := by simp [v0, cross2]; ring
    rw [this]; linarith
  have g2 : cross2 (t - e) v0 < 0 := by
    have : cross2 (t - e) v0 = -cross2 (e - s) (t - e) := by simp [v0, cross2]; ring
    rw [this]; linarith
  obtain ⟨δ1, hδ1, H1⟩ := k20_affine_neg (d := cross2 (e - s) u) g1
  obtain ⟨δ2, hδ2, H2⟩ := k20_affine_neg (d := cross2 (t - e) u) g2
  have hfin : ((⋃ i, {x : ℝ | cross2 (p (i + 1) - p i) u * x + cross2 (p (i + 1) - p i) v0 = 0}) ∪
      ⋃ q : {q : ZMod 3 × ZMod 3 // q.1 ≠ q.2},
        {x : ℝ | ⟪u, p q.1.1 - p q.1.2⟫ * x + ⟪v0, p q.1.1 - p q.1.2⟫ = 0}).Finite :=
    (Set.finite_iUnion fun i => finite_affine_zero (Or.inl (hu1 i))).union
      (Set.finite_iUnion fun q => finite_affine_zero (Or.inl (hu2 q)))
  obtain ⟨x, hx, hxB⟩ := ((Set.Ioo_infinite (lt_min hδ1 hδ2)).diff hfin).nonempty
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hxB
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨v0 + x • u, fun i h => hxB.1 i ?_, fun i j hij h => hxB.2 ⟨(i, j), hij⟩ ?_, ?_, ?_⟩
  · rw [cross2_add_right, cross2_smul_right] at h; linarith
  · rw [inner_add_left, inner_smul_left] at h; simp only [RCLike.conj_to_real] at h; linarith
  · rw [cross2_add_right, cross2_smul_right]
    have := H1 x hx0 (lt_of_lt_of_le hx1 (min_le_left _ _)); linarith
  · rw [cross2_add_right, cross2_smul_right]
    have := H2 x hx0 (lt_of_lt_of_le hx1 (min_le_right _ _)); linarith

theorem k20_triExt (o s t e : ℝ²) {h0 h1 h2 : ℝ} (hh0 : 0 < h0) (hh1 : 0 < h1) (hh2 : 0 < h2)
    (hccw : 0 < cross2 (s - o) (t - o)) (hE : 0 < cross2 (e - s) (t - e)) :
    IsRupert ({liftPt o 0, liftPt s 0, liftPt t 0, liftPt e 0, liftPt o h0, liftPt s h1, liftPt t h2} :
      Finset ℝ³) := by
  classical
  obtain ⟨v, hv1, hv2, he1, he2⟩ := k20_pick_v o s t e hccw hE
  set V : Finset ℝ³ := {liftPt o 0, liftPt s 0, liftPt t 0, liftPt e 0, liftPt o h0, liftPt s h1, liftPt t h2}
  have hz3 : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  refine k20_truncPrism_gen (tri o s t) (isCcwPolygon_tri hccw) (tri h0 h1 h2) ?_ V ?_ ?_ v hv1 hv2 ?_
  · intro j; rcases hz3 j with rfl | rfl | rfl <;> simp [tri] <;> assumption
  · intro j; rcases hz3 j with rfl | rfl | rfl <;> simp [tri, V]
  · intro j; rcases hz3 j with rfl | rfl | rfl <;> simp [tri, V]
  · intro ψ M
    have L1 := eventually_atTop_pos (ψ * cross2 (t - e) (rot90 (e - M))) (-cross2 (t - e) v) (by linarith)
    have L2 := eventually_atTop_pos (ψ * cross2 (e - s) (rot90 (e - M))) (-cross2 (e - s) v) (by linarith)
    filter_upwards [L1, L2] with lam l1 l2 κ
    have hs : liftPt s 0 ∈ V := by simp [V]
    have ht : liftPt t 0 ∈ V := by simp [V]
    have hvel := k20_vel κ ψ lam M v e 0
    have c1 : 0 < cross2 (t - e) (proj_xy (cross (k20ω κ ψ v) (liftPt e 0) + k20τ ψ lam M v)) := by
      rw [hvel]; simp only [cross2_add_right, cross2_sub_right, cross2_smul_right]; nlinarith
    have c2 : 0 < cross2 (e - s) (proj_xy (cross (k20ω κ ψ v) (liftPt e 0) + k20τ ψ lam M v)) := by
      rw [hvel]; simp only [cross2_add_right, cross2_sub_right, cross2_smul_right]; nlinarith
    filter_upwards [k20_cert_flat V v (k20ω κ ψ v) (k20τ ψ lam M v) hs ht hE c1 c2] with ε hε y hy hb ht'
    have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2
    have ht0 := ht' 0; have ht1 := ht' 1; have ht2 := ht' 2
    simp only [tri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons] at hb0 hb1 hb2 ht0 ht1 ht2
    simp only [V, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hε | exact absurd rfl ‹_›

end C2
end Type08Sp
end Minimality
