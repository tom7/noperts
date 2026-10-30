module

public import Minimality.Type08S.P2S7
public import Minimality.Type08S.P2F2

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-- **Case A in the T′ frame** (`α4 > 1`, `{d, a}` strictly below `{b′, c}`): a pure tilt
`w = -(α4-1) A - 2 γ4 C` of the view `B`, with the rim `(d, a, b′, c)` (`Q4A`-unimodal). -/
theorem Tp_caseA_core (d A B C : ℝ³) {α4 β1 γ4 β6 γ6 : ℝ}
    (hH : 0 < det3 A C B)
    (hα4 : 1 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hsep : max 0 ⟪A, B⟫ < min (α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫) ⟪C, B⟫) :
    IsRupert (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)) := by
  have f1 : 0 < α4 - 1 := by linarith
  have f2 : 0 < α4 + γ4 - 1 := by linarith
  have f3 : 0 < α4 := by linarith
  have f4 : 0 < 1 - γ6 := sub_pos.2 hγ61
  have f5 : 0 < (α4 - 1) * γ6 + γ4 := by nlinarith
  have hB : B ≠ 0 := by
    intro h0; rw [h0] at hH; simp [det3, cross] at hH
  obtain ⟨w, hw⟩ : ∃ w : ℝ³, w = (-(α4 - 1)) • A + (-(2 * γ4)) • C := ⟨_, rfl⟩
  obtain ⟨b0, b1', b2', b3⟩ := zmod4_add_one
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TiltSign (quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) (i + 1) -
          quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i)
        (quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) j -
          quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i) B w := by
    intro i j h1 h2
    subst hw
    rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1', b2', b3, quad_0, quad_1, quad_2,
        quad_3]
    · exact Or.inl (lt_of_lt_of_eq (mul_pos hγ4 hH) (by ex))
    · exact Or.inl (lt_of_lt_of_eq hH (by ex))
    · exact Or.inl (lt_of_lt_of_eq (mul_pos f2 hH) (by ex))
    · exact Or.inl (lt_of_lt_of_eq (mul_pos hγ4 hH) (by ex))
    · exact Or.inl (lt_of_lt_of_eq (mul_pos f3 hH) (by ex))
    · exact Or.inl (lt_of_lt_of_eq (mul_pos f2 hH) (by ex))
    · exact Or.inl (lt_of_lt_of_eq hH (by ex))
    · exact Or.inl (lt_of_lt_of_eq (mul_pos f3 hH) (by ex))
  have hrest : ∀ y ∈ (insert d ({d + A, d + β6 • B + γ6 • C, d + B, d + α4 • A + γ4 • C, d + C,
      d + A + β1 • B} : Finset ℝ³)), (∀ j, y ≠ quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) j) →
      ∀ i, TiltSign (quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) (i + 1) -
          quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i)
        (y - quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i) B w := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have hx0 := hyx 0
    have hx1 := hyx 1
    have hx2 := hyx 2
    have hx3 := hyx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at hx0 hx1 hx2 hx3
    subst hw
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hx0
    · -- c' ... order: d, a, a', b, b', c, c'
      exact absurd rfl hx1
    · -- a'
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3]
      · exact Or.inl (lt_of_lt_of_eq (mul_pos hγ6 hH) (by ex))
      · exact Or.inl (lt_of_lt_of_eq (mul_pos f5 hH) (by ex))
      · exact Or.inl (lt_of_lt_of_eq (mul_pos (mul_pos f3 f4) hH) (by ex))
      · exact Or.inr ⟨by ex, lt_of_lt_of_eq (mul_pos (mul_pos hβ6 f1) hH) (by ex)⟩
    · -- b
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3]
      · exact Or.inr ⟨by ex, lt_of_lt_of_eq (mul_pos (mul_pos two_pos hγ4) hH) (by ex)⟩
      · exact Or.inl (lt_of_lt_of_eq (mul_pos hγ4 hH) (by ex))
      · exact Or.inl (lt_of_lt_of_eq (mul_pos f3 hH) (by ex))
      · exact Or.inr ⟨by ex, lt_of_lt_of_eq (mul_pos f1 hH) (by ex)⟩
    · exact absurd rfl hx2
    · exact absurd rfl hx3
    · -- c'
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [b0, b1', b2', b3, quad_0, quad_1, quad_2, quad_3]
      · exact Or.inr ⟨by ex, lt_of_lt_of_eq (mul_pos (mul_pos (mul_pos two_pos hβ1) hγ4) hH) (by ex)⟩
      · exact Or.inr ⟨by ex, lt_of_lt_of_eq (mul_pos (mul_pos (mul_pos hβ1 hγ4) f1) hH) (by ex)⟩
      · exact Or.inl (lt_of_lt_of_eq (mul_pos f2 hH) (by ex))
      · exact Or.inl (lt_of_lt_of_eq hH (by ex))
  refine isRupert_of_tilted_unimodal' _ B w hB (k := 4) (by norm_num)
    (quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C)) ?_ hcyc hrest Type08Sp.Q4A Type08Sp.Q4A_open
    (fun z c hc => Type08Sp.Q4A_smul hc) ?_ (fun z hinj => Type08Sp.Q4A_unimodal hinj)
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3]
  · have hc : Continuous fun ε : ℝ => fun i : ZMod 4 =>
        ⟪quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i, B + ε • w⟫ :=
      continuous_pi fun i => by fun_prop
    have h0 : Type08Sp.Q4A fun i : ZMod 4 =>
        ⟪quad (d) (d + A) (d + α4 • A + γ4 • C) (d + C) i, B + (0 : ℝ) • w⟫ := by
      simp only [zero_smul, add_zero]
      simp only [max_lt_iff, lt_min_iff] at hsep
      obtain ⟨⟨s1, s2⟩, s3, s4⟩ := hsep
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [quad_0, quad_1, quad_2, quad_3, inner_add_left, real_inner_smul_left] <;> linarith
    have hm := (Type08Sp.Q4A_open.preimage hc).mem_nhds h0
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (show ∀ᶠ ε in 𝓝 (0 : ℝ), _ from hm)

end Minimality
