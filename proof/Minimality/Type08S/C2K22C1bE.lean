module

public import Minimality.Type08S.C2K22C1bD

@[expose] public section


/-!
# K22C1b / E: the cell `C⁺ = (b', a, c', b, a', c)` at the edge-on view `w = λ q + r`, tilt `+p`

Depths at `w` (relative to `d`): `b' γ4 R, a 0, c' β1 Q, b Q, a' Q + γ6 R, c R`; the tilt `+p` puts the top points
lexicographically above.  Regimes: (iv) `β1 < 1`, `0 < Q`, `Q + γ6 R < R`; (v) `β1 < 1`, `γ4 < 1`, `0 < Q`, `0 < R`,
`R < Q + γ6 R`.
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
theorem k22c1b_cellP {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 l Q R : ℝ}
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d))
    (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hl : 0 < l)
    (hQ : ⟪b - d, l • (b - d) + (c - d)⟫ = Q) (hR : ⟪c - d, l • (b - d) + (c - d)⟫ = R)
    (hreg : (β1 < 1 ∧ 0 < Q ∧ Q + γ6 * R < R) ∨ (β1 < 1 ∧ γ4 < 1 ∧ 0 < Q ∧ 0 < R ∧ R < Q + γ6 * R)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set w := l • q + r with hw
  have hΔ : det3 p q w ≠ 0 := by
    have : det3 p q w = det3 p q r := by
      simp only [hw, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [this]; exact hdet
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hP : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hw0 : w ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have eO : fpoint p q w d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q w d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q w d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q w d (0, -l, 1) = c := by simp only [fpoint, fcomb, hw, hq, hr]; module
  have eC' : fpoint p q w d (1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q w d (1, -(γ4 * l), γ4) = b' := by
    rw [hb']; simp only [fpoint, fcomb, hp, hw, hq, hr]; module
  have eA' : fpoint p q w d (0, 1 - γ6 * l, γ6) = a' := by
    rw [ha']; simp only [fpoint, fcomb, hw, hq, hr]; module
  have hz : ∀ t, ⟪fpoint p q w d t, w⟫ = ⟪d, w⟫ + t.2.1 * Q + t.2.2 * (l * Q + R) := by
    intro t; rw [(k22c1b_frame p q r d l hpq hpr 0 0 t).1, hQ, hR]
  have hs : ∀ v2 t, ⟪fpoint p q w d t, fcomb p q w 1 v2 0⟫ =
      ⟪d, fcomb p q w 1 v2 0⟫ + t.1 * 1 * ⟪p, p⟫ + v2 * (t.2.1 * ⟪q, q⟫ + t.2.2 * Q) := by
    intro v2 t; rw [(k22c1b_frame p q r d l hpq hpr 1 v2 t).2, hQ]
  have hA : HasLexCellAt (V8 a a' b b' c c' d) w := by
    refine cyc_cell (V8 a a' b b' c c' d) p q w d hΔ (k := 6) (by norm_num) (k22c1bP l β1 γ4 γ6) ?_ ?_
      [((0 : ℝ), (0 : ℝ), (0 : ℝ))] ?_
      (u1 := 1) (u2 := 0) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
      (fun v1 v2 => v1 = 1) ?_ ?_ ?_
    · intro i j h
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | rfl
        | (exfalso
           simp only [k22c1bP_0, k22c1bP_1, k22c1bP_2, k22c1bP_3, k22c1bP_4, k22c1bP_5, Prod.mk.injEq] at h
           first
           | linarith [h.1, h.2.1, h.2.2]
           | nlinarith [h.1, h.2.1, h.2.2])
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k22c1bP_0, eB']; simp [V8]
      · simp only [k22c1bP_1, eA]; simp [V8]
      · simp only [k22c1bP_2, eC']; simp [V8]
      · simp only [k22c1bP_3, eB]; simp [V8]
      · simp only [k22c1bP_4, eA']; simp [V8]
      · simp only [k22c1bP_5, eC]; simp [V8]
    · intro y hy
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨_, by simp, eO.symm⟩
      · exact Or.inl ⟨1, by rw [k22c1bP_1, eA]⟩
      · exact Or.inl ⟨4, by rw [k22c1bP_4, eA']⟩
      · exact Or.inl ⟨3, by rw [k22c1bP_3, eB]⟩
      · exact Or.inl ⟨0, by rw [k22c1bP_0, eB']⟩
      · exact Or.inl ⟨5, by rw [k22c1bP_5, eC]⟩
      · exact Or.inl ⟨2, by rw [k22c1bP_2, eC']⟩
    · intro lam h0 h1; simp
    · intro v1 v2 hv; subst hv; exact k22c1b_tscP hl hβ1 hγ4 hγ6 hγ61
    · intro v1 v2 hv hinj
      subst hv
      have L : ∀ s t : ℝ × ℝ × ℝ,
          (s.2.1 * Q + s.2.2 * (l * Q + R) < t.2.1 * Q + t.2.2 * (l * Q + R) ∨
            (s.2.1 * Q + s.2.2 * (l * Q + R) = t.2.1 * Q + t.2.2 * (l * Q + R) ∧
              s.1 * 1 * ⟪p, p⟫ + v2 * (s.2.1 * ⟪q, q⟫ + s.2.2 * Q) <
                t.1 * 1 * ⟪p, p⟫ + v2 * (t.2.1 * ⟪q, q⟫ + t.2.2 * Q))) →
          LexLt (⟪fpoint p q w d s, w⟫, ⟪fpoint p q w d s, fcomb p q w 1 v2 0⟫)
            (⟪fpoint p q w d t, w⟫, ⟪fpoint p q w d t, fcomb p q w 1 v2 0⟫) := by
        intro s t h
        unfold LexLt
        simp only [hz, hs]
        rcases h with h | ⟨h1, h2⟩
        · left; linarith
        · right; constructor <;> linarith
      obtain ⟨g0, g1, g2, g3, g4, g5⟩ := z6_add_one
      obtain ⟨s0, s1, s2, s3, s4, s5⟩ := k22c1b_z6sub
      rcases hreg with ⟨hb1, hQp, hlt⟩ | ⟨hb1, hg4, hQp, hRp, hlt⟩
      · have hRp : 0 < R := by nlinarith
        refine k22c1b_uni (by decide) _ _ hinj 5 ?_
        intro j hj1 hj2
        rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hj2 (by decide)).elim
        · right; simp only [g1]; apply L; left
          simp only [k22c1bP_1, k22c1bP_2]; nlinarith
        · right; simp only [g2]; apply L; left
          simp only [k22c1bP_2, k22c1bP_3]; nlinarith
        · right; simp only [g3]; apply L; left
          simp only [k22c1bP_3, k22c1bP_4]; nlinarith
        · right; simp only [g4]; apply L; left
          simp only [k22c1bP_4, k22c1bP_5]; nlinarith
        · exact (hj1 rfl).elim
      · refine k22c1b_uni (by decide) _ _ hinj 4 ?_
        intro j hj1 hj2
        rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
        · left; simp only [s0]; apply L; left
          simp only [k22c1bP_0, k22c1bP_5]; nlinarith
        · right; simp only [g1]; apply L; left
          simp only [k22c1bP_1, k22c1bP_2]; nlinarith
        · right; simp only [g2]; apply L; left
          simp only [k22c1bP_2, k22c1bP_3]; nlinarith
        · right; simp only [g3]; apply L; left
          simp only [k22c1bP_3, k22c1bP_4]; nlinarith
        · exact (hj1 rfl).elim
        · exact (hj2 (by decide)).elim
  exact ⟨w, hw0, hA⟩

end C2
end Type08Sp
end Minimality
