module

public import Minimality.Type08S.C2K20TE2

@[expose] public section


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

theorem k20t_cone4 {x y u t : ℝ × ℝ} {v1 v2 : ℝ} (h : k18Cone [x, y, u, t] v1 v2) :
    0 < x.1 * v1 + x.2 * v2 ∧ 0 < y.1 * v1 + y.2 * v2 ∧ 0 < u.1 * v1 + u.2 * v2 ∧ 0 < t.1 * v1 + t.2 * v2 :=
  ⟨h x (by simp), h y (by simp), h u (by simp), h t (by simp)⟩

theorem k20tE_inj {A G b1 b6 : ℝ} (hA : 0 < A) (hG : 0 < G) (hs : 1 < A + G) (hb1 : 0 < b1) (hb6 : 0 < b6) :
    ∀ i j, k20tE A G b1 b6 i = k20tE A G b1 b6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20tE_0, k20tE_1, k20tE_2, k20tE_3, k20tE_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
/-- **Cell E** `(b, c', a, b', a')` at `d - b` (tie slice: `⟪P,R⟫ = ⟪Q,R⟫ = 0`), `G > 1`, `b1 < 1 ∨ b6 < 1`:
a lex cell, no Gram condition. -/
theorem k20tE_cell (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {A G b1 b6 : ℝ} (hA : 0 < A) (hG : 1 < G)
    (hs : 1 < A + G) (hb1 : 0 < b1) (hb6 : 0 < b6) (hlow : b1 < 1 ∨ b6 < 1)
    (hPR : ⟪P, R⟫ = 0) (hQR : ⟪Q, R⟫ = 0)
    (hmem : ∀ i, fpoint P Q R d (k20tE A G b1 b6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, -b1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (A, G, 0) ∨ y = fpoint P Q R d (0, 1, -b6) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0)) :
    HasLexCellAt V R := by
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k18_cone_cell V P Q R d hΔ (k := 5) (by norm_num) (k20tE A G b1 b6)
    (k20tE_inj hA (by linarith) hs hb1 hb6) hmem [(-1, 0), (0, -1), (-G, A - 1), (1 - G, A)] (by simp)
    ?_ ?_ ?_ (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) ?_
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
    simp only at h1 h2 h3 h4
    exact tsc_scale hD ((k20tE_tsc hA (by linarith) hs hb1 hb6 (by linarith) (by linarith) (by linarith)
      (by linarith)).1 i j hi hj)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k20tE_0])).elim
    · exact (hyx 1 (by simp only [k20tE_1])).elim
    · exact (hyx 2 (by simp only [k20tE_2])).elim
    · exact (hyx 3 (by simp only [k20tE_3])).elim
    · exact (hyx 4 (by simp only [k20tE_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
      simp only at h1 h2 h3 h4
      exact tsc_scale hD ((k20tE_tsc hA (by linarith) hs hb1 hb6 (by linarith) (by linarith) (by linarith)
        (by linarith)).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
      simp only at h1 h2 h3 h4
      exact tsc_scale hD ((k20tE_tsc hA (by linarith) hs hb1 hb6 (by linarith) (by linarith) (by linarith)
        (by linarith)).2 _ (by simp) i)
  · intro v1 v2 hC hw
    refine k20tE_lex _ _ hw (z := ⟪d, R⟫) (rr := ⟪R, R⟫) hRR hb1 hb6 hlow ?_ ?_ ?_ ?_ ?_
    · simp only [k20tE_0, hz, hPR, hQR]; ring
    · simp only [k20tE_1, hz, hPR, hQR]; ring
    · simp only [k20tE_2, hz, hPR, hQR]; ring
    · simp only [k20tE_3, hz, hPR, hQR]; ring
    · simp only [k20tE_4, hz, hPR, hQR]; ring
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; norm_num
    · right; norm_num
    · left; simp only; linarith
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
