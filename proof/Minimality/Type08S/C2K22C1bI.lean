module

public import Minimality.Type08S.C2K22C1bH

@[expose] public section


/-!
# K22C1b / I: the face-on cell `F2 = (d, b, a', b', a)` at `p = a - d` (`β1 ≤ 1 ≤ γ4`, `qr > 0`)

Tilt `v = λ q - r` (`0 < λ`, `λ (qq + qr) < qr`): the top copies of `d, c` (`a, b'`) step out across the edge `d c`;
depths: top `P` above bottom `0`; bottom secondary `b (λ qq - qr) < d 0`.
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

set_option maxHeartbeats 6400000 in
theorem k22c1b_cellF2 {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ}
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d))
    (hβ1 : 0 < β1) (hβ11 : β1 ≤ 1) (hγ41 : 1 ≤ γ4) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hqr : 0 < ⟪b - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hΔ : det3 q r p ≠ 0 := by
    have : det3 q r p = det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact hdet
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hP : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hR : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hQ : 0 < ⟪q, q⟫ := real_inner_self_pos.2 (show q ≠ 0 by intro h0; apply hdet; rw [h0]; simp [det3_expand])
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint q r p d (0, 0, 1) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint q r p d (1, 0, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint q r p d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint q r p d (β1, 0, 1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint q r p d (0, γ4, 1) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint q r p d (1, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  obtain ⟨g0, g1, g2, g3, g4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k22c1b_z5sub
  have hA : HasLexCellAt (V8 a a' b b' c c' d) p := by
    refine cyc_cell (V8 a a' b b' c c' d) q r p d hΔ (k := 5) (by norm_num) (k22c1bF2 γ4 γ6) ?_ ?_
      [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (β1, 0, 1)] ?_
      (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := ⟪q, r⟫ / (⟪q, q⟫ + ⟪q, r⟫))
      (by norm_num) (div_pos hqr (by linarith))
      (fun v1 v2 => v2 = -1 ∧ 0 < v1 ∧ v1 * (⟪q, q⟫ + ⟪q, r⟫) < ⟪q, r⟫) ?_ ?_ ?_
    · intro i j h
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        first
        | rfl
        | (exfalso
           simp only [k22c1bF2_0, k22c1bF2_1, k22c1bF2_2, k22c1bF2_3, k22c1bF2_4, Prod.mk.injEq] at h <;>
           first
           | linarith
           | (obtain ⟨h1, h2, h3⟩ := h; linarith)
           | (obtain ⟨h1, h2⟩ := h; linarith))
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k22c1bF2_0, eO]; simp [V8]
      · simp only [k22c1bF2_1, eB]; simp [V8]
      · simp only [k22c1bF2_2, eA']; simp [V8]
      · simp only [k22c1bF2_3, eB']; simp [V8]
      · simp only [k22c1bF2_4, eA]; simp [V8]
    · intro y hy
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨0, by rw [k22c1bF2_0, eO]⟩
      · exact Or.inl ⟨4, by rw [k22c1bF2_4, eA]⟩
      · exact Or.inl ⟨2, by rw [k22c1bF2_2, eA']⟩
      · exact Or.inl ⟨1, by rw [k22c1bF2_1, eB]⟩
      · exact Or.inl ⟨3, by rw [k22c1bF2_3, eB']⟩
      · exact Or.inr ⟨_, by simp, eC.symm⟩
      · exact Or.inr ⟨_, by simp, eC'.symm⟩
    · intro lam h0 h1
      refine ⟨by ring, by linarith, ?_⟩
      rw [lt_div_iff₀ (by nlinarith [hQ])] at h1
      linarith
    · intro v1 v2 ⟨hv, hv2, hv3⟩; subst hv
      exact k22c1b_tscF2 hβ1 hβ11 hγ41 hγ6 hγ61 hv2 (by nlinarith)
    · intro v1 v2 ⟨hv, hv2, hv3⟩ hinj
      subst hv
      have hz := fun t => (k22c1b_frameF p q r d hpq hpr v1 (-1) t).1
      have hs := fun t => (k22c1b_frameF p q r d hpq hpr v1 (-1) t).2
      refine k22c1b_uni (by decide) _ _ hinj 3 ?_
      intro j hj1 hj2
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl
      · left; simp only [s0]; unfold LexLt; left
        simp only [hz, k22c1bF2_0, k22c1bF2_4]; nlinarith
      · left; simp only [s1]; unfold LexLt; right
        simp only [hz, hs, k22c1bF2_1, k22c1bF2_0]
        refine ⟨trivial, ?_⟩
        nlinarith [mul_pos hv2 hqr]
      · right; simp only [g2]; unfold LexLt; left
        simp only [hz, k22c1bF2_2, k22c1bF2_3]; nlinarith
      · exact (hj1 rfl).elim
      · exact (hj2 (by decide)).elim
  exact ⟨p, hp0, hA⟩

end C2
end Type08Sp
end Minimality
