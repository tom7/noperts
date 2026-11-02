module

public import Minimality.Type08S.C2K17GB5

@[expose] public section


/-!
# K17GB / GB6: S1.8a cell and theorem.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- ccw `c' (α1,0,-β1), b' (α4,γ4,0), c (0,1,0), d 0, b (0,0,-1)` in the frame `(a-d, c-d, d-b)`. -/
def k17gbY8a (α1 β1 α4 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (α1, 0, -β1) (α4, γ4, 0) (0, 1, 0) (0, 0, 0) (0, 0, -1)

set_option maxHeartbeats 3200000 in
theorem k17gb_s18a_tsc {D α1 β1 α4 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hα4 : 0 < α4) (hα41 : α4 < 1) (hγ4 : 1 < γ4) (hβ6 : 0 < β6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gbY8a α1 β1 α4 γ4 (i + 1) - k17gbY8a α1 β1 α4 γ4 i)
        (k17gbY8a α1 β1 α4 γ4 j - k17gbY8a α1 β1 α4 γ4 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gbY8a α1 β1 α4 γ4 (i + 1) - k17gbY8a α1 β1 α4 γ4 i)
        ((1, 0, 0) - k17gbY8a α1 β1 α4 γ4 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gbY8a α1 β1 α4 γ4 (i + 1) - k17gbY8a α1 β1 α4 γ4 i)
        ((0, 1, -β6) - k17gbY8a α1 β1 α4 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have ka := mul_pos hD (by linarith : (0:ℝ) < α1)
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have kg := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kg1 := mul_pos hD (sub_pos.2 hγ4)
  have kp := mul_pos hD hα4
  have kp1 := mul_pos hD (sub_pos.2 hα41)
  have kpg := mul_pos (mul_pos hD hα4) (by linarith : (0:ℝ) < γ4)
  have kag := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < γ4)
  have ka1g := mul_pos (mul_pos hD (sub_pos.2 hα1)) (by linarith : (0:ℝ) < γ4)
  have kg1a := mul_pos (mul_pos hD (sub_pos.2 hγ4)) (sub_pos.2 (by linarith : α4 < α1))
  have kpg1 := mul_pos (mul_pos hD hα4) (sub_pos.2 hγ4)
  have kv1 := mul_pos hD hv1
  have knv2 := mul_pos hD (neg_pos.2 hv2)
  have kanv2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (neg_pos.2 hv2)
  have kbnv2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  have kg1v1 := mul_pos (mul_pos hD (sub_pos.2 hγ4)) hv1
  have kgv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kb6 := mul_pos hD hβ6
  have kb6v1 := mul_pos (mul_pos hD hβ6) hv1
  have kb6g1v1 := mul_pos (mul_pos (mul_pos hD hβ6) (sub_pos.2 hγ4)) hv1
  have kb6pnv2 := mul_pos (mul_pos (mul_pos hD hβ6) hα4) (neg_pos.2 hv2)
  have kb6nv2 := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have kpnv2 := mul_pos (mul_pos hD hα4) (neg_pos.2 hv2)
  have kb6a := mul_pos (mul_pos hD hβ6) (by linarith : (0:ℝ) < α1)
  refine ⟨?_, ?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gbY8a, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  all_goals
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gbY8a, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gbY8a_inj {α1 β1 α4 γ4 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : α4 < 1) (hγ4 : 1 < γ4) :
    ∀ i j, k17gbY8a α1 β1 α4 γ4 i = k17gbY8a α1 β1 α4 γ4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gbY8a, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 6400000 in
/-- **S1.8a cell**: `(c',b',c,d,b)` at `d - b`, frame `(a-d, c-d, d-b)`, tilt `(rr, -λ pr)`. -/
theorem k17gb_s18a_cell {a a' b b' c c' d : ℝ³} {α1 β1 α4 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 0 < α4)
    (hα41 : α4 < 1) (hγ4 : 1 < γ4) (hβ6 : 1 < β6)
    (hqr : ⟪b - d, c - d⟫ = 0) (hpq : ⟪a - d, b - d⟫ = 0) (hpr : 0 < ⟪a - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gb_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gb_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gb_fp, hR]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gb_fp, hQ]; module
  have Ea' : fpoint P Q R d (0, 1, -β6) = a' := by rw [k17gb_fp, ha', hR, hQ]; module
  have Eb' : fpoint P Q R d (α4, γ4, 0) = b' := by rw [k17gb_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (α1, 0, -β1) = c' := by rw [k17gb_fp, hc', hP, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gb_r0 hΔ)
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hPQ : 0 < ⟪P, Q⟫ := hpr
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  refine ⟨R, k17gb_r0 hΔ, ?_⟩
  refine k8_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gbY8a α1 β1 α4 γ4)
    (k17gbY8a_inj hα1 (by linarith) hα41 hγ4) (u1 := ⟪Q, Q⟫) (u2 := 0) (t1 := 0) (t2 := -⟪P, Q⟫)
    (by have := mul_pos hQQ hPQ; nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gbY8a, pc5_0, Ec']; simp [V8]
    · simp only [k17gbY8a, pc5_1, Eb']; simp [V8]
    · simp only [k17gbY8a, pc5_2, Ec]; simp [V8]
    · simp only [k17gbY8a, pc5_3, Ed]; simp [V8]
    · simp only [k17gbY8a, pc5_4, Eb]; simp [V8]
  · intro lam h0 h1 D hD
    exact (k17gb_s18a_tsc hD hα1 (by linarith) hα4 hα41 hγ4 (by linarith) (by nlinarith)
      (by nlinarith [mul_pos h0 hPQ])).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (α1, 0, -β1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (0, 1, -β6) := by
      rw [Ec', Eb', Ec, Ed, Eb, Ea, Ea']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gbY8a, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gbY8a, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gbY8a, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gbY8a, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gbY8a, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s18a_tsc hD hα1 (by linarith) hα4 hα41 hγ4 (by linarith) (by nlinarith)
        (by nlinarith [mul_pos h0 hPQ])).2.1 i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s18a_tsc hD hα1 (by linarith) hα4 hα41 hγ4 (by linarith) (by nlinarith)
        (by nlinarith [mul_pos h0 hPQ])).2.2 i
  · intro lam h0 h1 w hw hinj
    refine k17gb_lex5_plat123 _ w hinj ?_ ?_ ?_ ?_ ?_
    · simp only [k17gbY8a, pc5_0, pc5_4, hz, hQR, hPR]; nlinarith
    · simp only [k17gbY8a, pc5_4, pc5_1, hz, hQR, hPR]; nlinarith
    · simp only [k17gbY8a, pc5_1, pc5_2, hz, hQR, hPR]; ring
    · simp only [k17gbY8a, pc5_2, pc5_3, hz, hQR, hPR]; ring
    · rw [hw, hw]
      simp only [k17gbY8a, pc5_2, pc5_3, hwx, hQR]
      nlinarith [mul_pos (mul_pos hQQ hPQ) (sub_pos.2 h1)]

/-- **S1.8a**: `K14TaC` (with `¬ T'`), `⟪a-d,b-d⟫ = 0`: a lex cell unless `ζ_{a-c'}(a,b') ≤ 0`. -/
theorem k17gb_s18a {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K14TaC a a' b b' c c' d) (hpq : ⟪a - d, b - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - b', a - c'⟫ ≤ 0 := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hα4, hα41, hγ4, hβ6, hpl, hqr, hL⟩ :=
    k17gb_tac_frame W hT' h hpq
  by_cases hle : ⟪a - b', a - c'⟫ ≤ 0
  · exact Or.inr hle
  · push Not at hle
    left
    have hpp : 0 < ⟪a - d, a - d⟫ := by
      apply real_inner_self_pos.2
      intro h0; apply hdet; rw [h0]; simp [det3_expand]
    have hpr : 0 < ⟪a - d, c - d⟫ := by
      rw [hL] at hle
      by_contra hh; push Not at hh
      have h1 : 0 < α1 - 1 := by linarith
      have h2 : γ4 * ⟪a - d, c - d⟫ - (1 - α4) * ⟪a - d, a - d⟫ ≤ 0 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ γ4) (neg_nonneg.2 hh), mul_pos (sub_pos.2 hα41) hpp]
      nlinarith [mul_nonneg h1.le (neg_nonneg.2 h2)]
    exact k17gb_s18a_cell hdet hc' hb' ha' hα1 hβ1 hα4 hα41 hγ4 hβ6 hqr hpq hpr

end C2
end Type08Sp
end Minimality
