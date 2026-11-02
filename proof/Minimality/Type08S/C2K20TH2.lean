module

public import Minimality.Type08S.C2K20TH1

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

/-- Lex unimodality of the facet cell `(d, b, a', c)`: depths `z, z, z + x, z + x`, `x ≠ 0`. -/
theorem k20tH_lex (zz ww : ZMod 4 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j) {z x : ℝ} (hx : x ≠ 0)
    (h0 : zz 0 = z) (h1 : zz 1 = z) (h2 : zz 2 = z + x) (h3 : zz 3 = z + x) : LexUni zz ww := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k20t_z4
  have z01 : zz 0 = zz 1 := by rw [h0, h1]
  have z23 : zz 2 = zz 3 := by rw [h2, h3]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- x < 0: top group {0,1}
    have l20 : zz 2 < zz 0 := by rw [h2, h0]; linarith
    have l21 : zz 2 < zz 1 := by rw [h2, h1]; linarith
    have l30 : zz 3 < zz 0 := by rw [h3, h0]; linarith
    have l31 : zz 3 < zz 1 := by rw [h3, h1]; linarith
    rcases lexLt_total (k20t_ne4 hinj (show (0 : ZMod 4) ≠ 1 by decide)) with h | h
    · refine k19_lexUni_nb zz ww hinj 1 ?_ ?_ ?_
      · rw [e1]; exact h
      · rw [f1]; exact Or.inl l21
      · intro i hi
        rcases z4_cases' i with rfl | rfl | rfl | rfl
        · right; rw [f0]; exact h
        · exact absurd rfl hi
        · left; rw [e2]; exact Or.inl l21
        · right; rw [f3]; exact Or.inl l30
    · refine k19_lexUni_nb zz ww hinj 0 ?_ ?_ ?_
      · rw [e0]; exact Or.inl l30
      · rw [f0]; exact h
      · intro i hi
        rcases z4_cases' i with rfl | rfl | rfl | rfl
        · exact absurd rfl hi
        · left; rw [e1]; exact h
        · left; rw [e2]; exact Or.inl l21
        · right; rw [f3]; exact Or.inl l30
  · -- x > 0: top group {2,3}
    have l02 : zz 0 < zz 2 := by rw [h2, h0]; linarith
    have l12 : zz 1 < zz 2 := by rw [h2, h1]; linarith
    have l03 : zz 0 < zz 3 := by rw [h3, h0]; linarith
    have l13 : zz 1 < zz 3 := by rw [h3, h1]; linarith
    rcases lexLt_total (k20t_ne4 hinj (show (2 : ZMod 4) ≠ 3 by decide)) with h | h
    · refine k19_lexUni_nb zz ww hinj 3 ?_ ?_ ?_
      · rw [e3]; exact h
      · rw [f3]; exact Or.inl l03
      · intro i hi
        rcases z4_cases' i with rfl | rfl | rfl | rfl
        · left; rw [e0]; exact Or.inl l03
        · right; rw [f1]; exact Or.inl l12
        · right; rw [f2]; exact h
        · exact absurd rfl hi
    · refine k19_lexUni_nb zz ww hinj 2 ?_ ?_ ?_
      · rw [e2]; exact Or.inl l12
      · rw [f2]; exact h
      · intro i hi
        rcases z4_cases' i with rfl | rfl | rfl | rfl
        · left; rw [e0]; exact Or.inl l03
        · right; rw [f1]; exact Or.inl l12
        · exact absurd rfl hi
        · left; rw [e3]; exact h

theorem k20tH_inj {b6 : ℝ} (hb6 : 0 < b6) : ∀ i j, k20tH b6 i = k20tH b6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases z4_cases' i with rfl | rfl | rfl | rfl <;> rcases z4_cases' j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20tH_0, k20tH_1, k20tH_2, k20tH_3] at e1 e2; first | linarith | (norm_num at e1 e2; linarith) | norm_num at e1 e2)

set_option maxHeartbeats 6400000 in
/-- **Facet cell** `(d, b, a', c)` at `a - d` (tie slice: frame `(P,Q,R) = (b-d, c-d, a-d)` with `⟪P,R⟫ = 0`), `b1 < 1`, `G < 1`,
`⟪Q,R⟫ ≠ 0`: a lex cell, ray `(-1,-1)`. -/
theorem k20tH_cell (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {A G b1 b6 : ℝ} (hA : 0 < A) (hG0 : 0 < G)
    (hG : G < 1) (hb1 : 0 < b1) (hb11 : b1 < 1) (hb6 : 0 < b6)
    (hPR : ⟪P, R⟫ = 0) (hx2 : ⟪Q, R⟫ ≠ 0)
    (hmem : ∀ i, fpoint P Q R d (k20tH b6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (b6, 1, 0) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (b1, 0, 1) ∨
      y = fpoint P Q R d (0, G, A)) :
    HasLexCellAt V R := by
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k18_cone_cell V P Q R d hΔ (k := 4) (by norm_num) (k20tH b6)
    (k20tH_inj hb6) hmem [(-1, 0), (0, -1)] (by simp)
    ?_ ?_ ?_ (ρ1 := -1) (ρ2 := -1) (δ1 := 0) (δ2 := 0) ?_
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨h1, h2⟩ := k20t_cone2 hC
    simp only at h1 h2
    exact tsc_scale hD ((k20tH_tsc (A := A) (G := G) (b1 := b1) hA hG0 hG hb1 hb11 hb6 (by linarith) (by linarith)).1 i j hi hj)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k20tH_0])).elim
    · exact (hyx 1 (by simp only [k20tH_1])).elim
    · exact (hyx 2 (by simp only [k20tH_2])).elim
    · exact (hyx 3 (by simp only [k20tH_3])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tH_tsc (A := A) (G := G) (b1 := b1) hA hG0 hG hb1 hb11 hb6 (by linarith) (by linarith)).2
        (0, 0, 1) (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tH_tsc (A := A) (G := G) (b1 := b1) hA hG0 hG hb1 hb11 hb6 (by linarith) (by linarith)).2
        (b1, 0, 1) (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2⟩ := k20t_cone2 hC
      simp only at h1 h2
      exact tsc_scale hD ((k20tH_tsc (A := A) (G := G) (b1 := b1) hA hG0 hG hb1 hb11 hb6 (by linarith) (by linarith)).2
        (0, G, A) (by simp) i)
  · intro v1 v2 hC hw
    refine k20tH_lex _ _ hw (z := ⟪d, R⟫) (x := ⟪Q, R⟫) hx2 ?_ ?_ ?_ ?_
    · simp only [k20tH_0, hz, hPR]; ring
    · simp only [k20tH_1, hz, hPR]; ring
    · simp only [k20tH_2, hz, hPR]; ring
    · simp only [k20tH_3, hz, hPR]; ring
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; norm_num
    · left; norm_num

end C2
end Type08Sp
end Minimality
