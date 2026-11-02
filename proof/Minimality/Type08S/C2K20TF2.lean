module

public import Minimality.Type08S.C2K20TF1

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

theorem k20tF_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j) {z rr b1 b6 : ℝ}
    (hrr : 0 < rr) (hb1 : 0 < b1) (hb6 : 0 < b6) (hlow : b1 < 1 ∨ b6 < 1)
    (h0 : zz 0 = z - b1 * rr) (h1 : zz 1 = z) (h2 : zz 2 = z) (h3 : zz 3 = z - b6 * rr) (h4 : zz 4 = z - rr) :
    LexUni zz ww := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have l01 : LexLt (zz 0, ww 0) (zz 1, ww 1) := Or.inl (by rw [h0, h1]; nlinarith)
  have l32 : LexLt (zz 3, ww 3) (zz 2, ww 2) := Or.inl (by rw [h3, h2]; nlinarith)
  have l4 : LexLt (zz 4, ww 4) (zz 3, ww 3) ∨ LexLt (zz 4, ww 4) (zz 0, ww 0) := by
    rcases hlow with h | h
    · right; left; show zz 4 < zz 0; rw [h4, h0]; nlinarith
    · left; left; show zz 4 < zz 3; rw [h4, h3]; nlinarith
  rcases lexLt_total (k20t_ne5 hinj (show (1 : ZMod 5) ≠ 2 by decide)) with h | h
  · refine k19_lexUni_nb zz ww hinj 2 ?_ ?_ ?_
    · rw [e2]; exact h
    · rw [f2]; exact l32
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; exact l01
      · right; rw [f1]; exact h
      · exact absurd rfl hi
      · left; rw [e3]; exact l32
      · rw [e4, f4]; exact l4
  · refine k19_lexUni_nb zz ww hinj 1 ?_ ?_ ?_
    · rw [e1]; exact l01
    · rw [f1]; exact h
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · right; rw [f0]; exact l01
      · exact absurd rfl hi
      · left; rw [e2]; exact h
      · left; rw [e3]; exact l32
      · rw [e4, f4]; exact l4

theorem k20tF_inj {A G b1 b6 : ℝ} (hA : 0 < A) (hG : 0 < G) (hs : 1 < A + G) (hb1 : 0 < b1) (hb6 : 0 < b6) :
    ∀ i j, k20tF A G b1 b6 i = k20tF A G b1 b6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20tF_0, k20tF_1, k20tF_2, k20tF_3, k20tF_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
/-- **Cell E'** `(c', b', c, a', b)` at `d - b` (tie slice), `A > 1`, `b1 < 1 ∨ b6 < 1`: a lex cell, no Gram condition. -/
theorem k20tF_cell (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {A G b1 b6 : ℝ} (hA : 1 < A) (hG : 0 < G)
    (hs : 1 < A + G) (hb1 : 0 < b1) (hb6 : 0 < b6) (hlow : b1 < 1 ∨ b6 < 1)
    (hPR : ⟪P, R⟫ = 0) (hQR : ⟪Q, R⟫ = 0)
    (hmem : ∀ i, fpoint P Q R d (k20tF A G b1 b6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (1, 0, -b1) ∨ y = fpoint P Q R d (A, G, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (0, 1, -b6) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0)) :
    HasLexCellAt V R := by
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k18_cone_cell V P Q R d hΔ (k := 5) (by norm_num) (k20tF A G b1 b6)
    (k20tF_inj (by linarith) hG hs hb1 hb6) hmem [(-1, 0), (0, -1), (G, 1 - A), (G - 1, -A)] (by simp)
    ?_ ?_ ?_ (ρ1 := 0) (ρ2 := -1) (δ1 := -1) (δ2 := 0) ?_
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
    simp only at h1 h2 h3 h4
    exact tsc_scale hD ((k20tF_tsc (by linarith) hG hs hb1 hb6 (by linarith) (by linarith) (by linarith)
      (by linarith)).1 i j hi hj)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k20tF_0])).elim
    · exact (hyx 1 (by simp only [k20tF_1])).elim
    · exact (hyx 2 (by simp only [k20tF_2])).elim
    · exact (hyx 3 (by simp only [k20tF_3])).elim
    · exact (hyx 4 (by simp only [k20tF_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
      simp only at h1 h2 h3 h4
      exact tsc_scale hD ((k20tF_tsc (by linarith) hG hs hb1 hb6 (by linarith) (by linarith) (by linarith)
        (by linarith)).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := k20t_cone4 hC
      simp only at h1 h2 h3 h4
      exact tsc_scale hD ((k20tF_tsc (by linarith) hG hs hb1 hb6 (by linarith) (by linarith) (by linarith)
        (by linarith)).2 _ (by simp) i)
  · intro v1 v2 hC hw
    refine k20tF_lex _ _ hw (z := ⟪d, R⟫) (rr := ⟪R, R⟫) hRR hb1 hb6 hlow ?_ ?_ ?_ ?_ ?_
    · simp only [k20tF_0, hz, hPR, hQR]; ring
    · simp only [k20tF_1, hz, hPR, hQR]; ring
    · simp only [k20tF_2, hz, hPR, hQR]; ring
    · simp only [k20tF_3, hz, hPR, hQR]; ring
    · simp only [k20tF_4, hz, hPR, hQR]; ring
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · right; norm_num
    · left; norm_num
    · left; simp only; linarith
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
