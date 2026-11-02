module

public import Minimality.Type08S.C2K20TZ1

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

theorem k20t_z4 : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧ (3 : ZMod 4) - 1 = 2 ∧
    (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by decide

theorem k20t_ne4 {z w : ZMod 4 → ℝ} (hinj : ∀ i j, z i = z j → w i = w j → i = j) {i j : ZMod 4} (h : i ≠ j) :
    (z i, w i) ≠ (z j, w j) := fun h' => h (hinj i j (congrArg Prod.fst h') (congrArg Prod.snd h'))

/-- Lex unimodality of cell Z `(a, b', a', c')`: `z b' < z a < z c'` (strict). -/
theorem k20tZ_lex (zz ww : ZMod 4 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j)
    (h10 : zz 1 < zz 0) (h03 : zz 0 < zz 3) : LexUni zz ww := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k20t_z4
  have l10 : LexLt (zz 1, ww 1) (zz 0, ww 0) := Or.inl h10
  have l03 : LexLt (zz 0, ww 0) (zz 3, ww 3) := Or.inl h03
  have l13 : LexLt (zz 1, ww 1) (zz 3, ww 3) := Or.inl (lt_trans h10 h03)
  rcases lexLt_total (k20t_ne4 hinj (show (2 : ZMod 4) ≠ 3 by decide)) with h | h
  · refine k19_lexUni_nb zz ww hinj 3 ?_ ?_ ?_
    · rw [e3]; exact h
    · rw [f3]; exact l03
    · intro i hi
      rcases z4_cases' i with rfl | rfl | rfl | rfl
      · left; rw [e0]; exact l03
      · left; rw [e1]; exact l10
      · right; rw [f2]; exact h
      · exact absurd rfl hi
  · have l12 : LexLt (zz 1, ww 1) (zz 2, ww 2) := lexLt_trans_K2 l13 h.symm.symm
    refine k19_lexUni_nb zz ww hinj 2 ?_ ?_ ?_
    · rw [e2]; exact l12
    · rw [f2]; exact h
    · intro i hi
      rcases z4_cases' i with rfl | rfl | rfl | rfl
      · left; rw [e0]; exact l03
      · left; rw [e1]; exact l10
      · exact absurd rfl hi
      · left; rw [e3]; exact h

theorem k20tZ_inj {A G b1 b6 : ℝ} (hG : 0 < G) (hb1 : 1 < b1) (hb6 : 0 < b6) :
    ∀ i j, k20tZ A G b1 b6 i = k20tZ A G b1 b6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z4_cases' i with rfl | rfl | rfl | rfl <;> rcases z4_cases' j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20tZ_0, k20tZ_1, k20tZ_2, k20tZ_3] at e1 e2 e3; nlinarith)

theorem k20t_cone2 {x y : ℝ × ℝ} {v1 v2 : ℝ} (h : k18Cone [x, y] v1 v2) :
    0 < x.1 * v1 + x.2 * v2 ∧ 0 < y.1 * v1 + y.2 * v2 := ⟨h x (by simp), h y (by simp)⟩

set_option maxHeartbeats 6400000 in
/-- **Cell Z** `(a, b', a', c')` at `c' - b`, frame `(P,Q,R)` (coordinates of `V8`: `a = (0,1-b1,1)`, `b' = (G,-A(b1-1),A)`,
`a' = (1,b6,0)`, `c' = (0,1,1)`, `d = 0`, `b = (0,1,0)`, `c = (1,0,0)`), depths `x1 = ⟪P,R⟫, x2 = ⟪Q,R⟫, x3 = ⟪R,R⟫`:
needs `b1 > 1`, `G > 1`, `x2 > 0` and `z b' < z a`. Ray `ρ = (1, b6 - 2)`. -/
theorem k20tZ_cell (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {A G b1 b6 : ℝ} (hA : 0 < A) (hG : 1 < G)
    (hs : 1 < A + G) (hb1 : 1 < b1) (hb6 : 0 < b6) (hF : A * (1 - b1) + G * (1 - b6) < 1)
    (hx2 : 0 < ⟪Q, R⟫) (hba : G * ⟪P, R⟫ + (A - 1) * (⟪R, R⟫ - (b1 - 1) * ⟪Q, R⟫) < 0)
    (hmem : ∀ i, fpoint P Q R d (k20tZ A G b1 b6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1 - b1, 1) ∨ y = fpoint P Q R d (G, -A * (b1 - 1), A) ∨
      y = fpoint P Q R d (1, b6, 0) ∨ y = fpoint P Q R d (0, 1, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (1, 0, 0)) :
    HasLexCellAt V R := by
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k18_cone_cell V P Q R d hΔ (k := 4) (by norm_num) (k20tZ A G b1 b6)
    (k20tZ_inj (by linarith) hb1 hb6) hmem [(1, 0), (b6 - 1, -1)] (by simp)
    ?_ ?_ ?_ (ρ1 := 1) (ρ2 := b6 - 2) (δ1 := 0) (δ2 := 0) ?_
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨h1, h2⟩ := k20t_cone2 hC
    simp only at h1 h2
    exact tsc_scale hD ((k20tZ_tsc hA hG hs hb1 hb6 hF (by linarith) (by linarith)).1 i j hi hj)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k20tZ_0])).elim
    · exact (hyx 1 (by simp only [k20tZ_1])).elim
    · exact (hyx 2 (by simp only [k20tZ_2])).elim
    · exact (hyx 3 (by simp only [k20tZ_3])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tZ_tsc hA hG hs hb1 hb6 hF (by linarith) (by linarith)).2 (0, 0, 0) (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tZ_tsc hA hG hs hb1 hb6 hF (by linarith) (by linarith)).2 (0, 1, 0) (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tZ_tsc hA hG hs hb1 hb6 hF (by linarith) (by linarith)).2 (1, 0, 0) (by simp) i)
  · intro v1 v2 hC hw
    refine k20tZ_lex _ _ hw ?_ ?_
    · simp only [k20tZ_0, k20tZ_1, hz]; nlinarith
    · simp only [k20tZ_0, k20tZ_3, hz]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; norm_num
    · left; simp only; linarith

end C2
end Type08Sp
end Minimality
