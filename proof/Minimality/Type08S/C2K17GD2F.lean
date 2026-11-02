module

public import Minimality.Type08S.C2K17GD2E

@[expose] public section


/-!
# K17GD / GD2: the slice `K6tTcA41` (Tc, `α4 = 1`; forces `β6 = 1`)

Cells (coordinates in `(p,q,r) = (a-d, b-d, c-d)`, `c' = (α1,β1,0)`, `b' = (1,0,γ4)`, `a' = (0,1,1)`):
* A = `(a, c', a', c, d)` at `r` (`= a - b'` up to sign): cone `v1 > 0 > v2`, `α1(-v2) + (β1-1)v1 > 0`;
  works for `⟪q,r⟫ > 0`, and for `⟪q,r⟫ = 0` with `α1⟪p,r⟫ < ⟪r,r⟫`, `⟪p,r⟫ ≠ 0` (tie `a' = c` in depth, either tilt side).
* B = `(c', b', c, d, b)` at `q` (`= d - b` up to sign), frame `(p, r, q)`: tilt `(-1, v2)`, `v2 > max 0 (1-γ4)`;
  needs the Gale inequality `E = 1 - β1 - α1 + α1γ4 ≥ 0`; works for `⟪q,r⟫ < 0`, and for `⟪q,r⟫ = 0` with `α1⟪p,r⟫ ≥ ⟪r,r⟫`.
* Leftover: `⟪q,r⟫ = 0 = ⟪p,r⟫` (note `ζ(d,b) = γ4 ⟪q,r⟫`).
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

set_option maxHeartbeats 3200000 in
/-- **K6tTcA41**: a lex cell, or the leftover `⟪b-d,c-d⟫ = ⟪a-d,c-d⟫ = 0`.  Context needed from `K5ZsTc`:
`hfar := k5z_far2 W hT hT'` and `hκb := k5z_kb_pos W hT hT'`. -/
theorem k17gd_tca41 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6tTcA41 a a' b b' c c' d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hκb : 0 < galeD W.G.l W.G.m b b') :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪b - d, c - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0) := by
  obtain ⟨hT, hκc, hα4⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 hα4 with h | h
    · linarith
    · exact absurd h hdet
  subst hα41
  have hβ61 : β6 = 1 := by
    have : γ4 * (1 - β6) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hβ61
  obtain ⟨μ, hμa, hμb⟩ := gale_pt W hdet hc' hb' ha' (by norm_num)
  have hμ : 0 < μ := by
    rw [hμb] at hκb
    have : 0 < α1 - 1 := by linarith
    by_contra hh; push Not at hh
    nlinarith
  have hE0 : 0 ≤ 1 - β1 - α1 + α1 * γ4 := by
    have := W.hκa
    rw [hμa] at this
    have h2 := nonneg_of_mul_nonneg_right this hμ
    linarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hq0 : q ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hΔ' : det3 p r q ≠ 0 := by
    have : det3 p r q = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hdet
  have hfp : ∀ (u v w : ℝ³) (x y z : ℝ), fpoint u v w d (x, y, z) = d + x • u + y • v + z • w := by
    intro u v w x y z; simp only [fpoint, fcomb]; module
  have A_a : fpoint p q r d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have A_c' : fpoint p q r d (α1, β1, 0) = c' := by rw [hfp, hc']; simp only [hp, hq]; module
  have A_a' : fpoint p q r d (0, 1, 1) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  have A_c : fpoint p q r d (0, 0, 1) = c := by rw [hfp]; simp only [hr]; module
  have A_d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have A_b : fpoint p q r d (0, 1, 0) = b := by rw [hfp]; simp only [hq]; module
  have A_b' : fpoint p q r d (1, 0, γ4) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have B_c' : fpoint p r q d (α1, 0, β1) = c' := by rw [hfp, hc']; simp only [hp, hq]; module
  have B_b' : fpoint p r q d (1, γ4, 0) = b' := by rw [hfp, hb']; simp only [hp, hr]; module
  have B_c : fpoint p r q d (0, 1, 0) = c := by rw [hfp]; simp only [hr]; module
  have B_d : fpoint p r q d (0, 0, 0) = d := by rw [hfp]; module
  have B_b : fpoint p r q d (0, 0, 1) = b := by rw [hfp]; simp only [hq]; module
  have B_a : fpoint p r q d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have B_a' : fpoint p r q d (0, 1, 1) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  have hmemA : ∀ i, fpoint p q r d (k17gdA α1 β1 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gdA, pc5_0, A_a]; simp [V8]
    · simp only [k17gdA, pc5_1, A_c']; simp [V8]
    · simp only [k17gdA, pc5_2, A_a']; simp [V8]
    · simp only [k17gdA, pc5_3, A_c]; simp [V8]
    · simp only [k17gdA, pc5_4, A_d]; simp [V8]
  have hVA : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4) := by
    intro y hy
    rw [A_a, A_c', A_a', A_c, A_d, A_b, A_b']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have hmemB : ∀ i, fpoint p r q d (k17gdB α1 β1 γ4 i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gdB, pc5_0, B_c']; simp [V8]
    · simp only [k17gdB, pc5_1, B_b']; simp [V8]
    · simp only [k17gdB, pc5_2, B_c]; simp [V8]
    · simp only [k17gdB, pc5_3, B_d]; simp [V8]
    · simp only [k17gdB, pc5_4, B_b]; simp [V8]
  have hVB : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p r q d (α1, 0, β1) ∨ y = fpoint p r q d (1, γ4, 0) ∨
      y = fpoint p r q d (0, 1, 0) ∨ y = fpoint p r q d (0, 0, 0) ∨ y = fpoint p r q d (0, 0, 1) ∨
      y = fpoint p r q d (1, 0, 0) ∨ y = fpoint p r q d (0, 1, 1) := by
    intro y hy
    rw [B_c', B_b', B_c, B_d, B_b, B_a, B_a']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  have cellA : (0 < ⟪q, r⟫ ∨ (⟪q, r⟫ = 0 ∧ α1 * ⟪p, r⟫ < ⟪r, r⟫ ∧ ⟪p, r⟫ ≠ 0)) →
      HasLexCell (V8 a a' b b' c c' d) := fun hc =>
    ⟨r, hr0, k17gdA_frame (V8 a a' b b' c c' d) p q r d hdet hα11 hβ1 hγ4 hc hmemA hVA⟩
  have cellB : ∀ σ1 : ℝ, max 0 (1 - γ4) < σ1 → (⟪r, q⟫ < 0 ∨ (⟪r, q⟫ = 0 ∧ σ1 * ⟪r, r⟫ ≤ ⟪p, r⟫)) →
      HasLexCell (V8 a a' b b' c c' d) := fun σ1 hσ hc =>
    ⟨q, hq0, k17gdB_frame (V8 a a' b b' c c' d) p q r d hΔ' hα11 hβ1 hγ4 hE0 hrr σ1 hσ hc hmemB hVB⟩
  have hqr : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  rcases lt_trichotomy ⟪q, r⟫ 0 with hneg | hzero | hpos
  · exact Or.inl (cellB (max 0 (1 - γ4) + 1) (by linarith) (Or.inl (by rw [hqr]; exact hneg)))
  · by_cases hp0 : ⟪p, r⟫ = 0
    · exact Or.inr ⟨hzero, hp0⟩
    · by_cases hlit : α1 * ⟪p, r⟫ < ⟪r, r⟫
      · exact Or.inl (cellA (Or.inr ⟨hzero, hlit, hp0⟩))
      · push Not at hlit
        obtain ⟨σ1, hσ1⟩ : ∃ σ1 : ℝ, σ1 * ⟪r, r⟫ = ⟪p, r⟫ := ⟨⟪p, r⟫ / ⟪r, r⟫, div_mul_cancel₀ _ hrr.ne'⟩
        have hα0 : 0 < α1 := by linarith
        have hs1 : 1 ≤ α1 * σ1 := by
          by_contra hh; push Not at hh
          nlinarith [mul_pos (sub_pos.2 hh) hrr]
        have hs0 : 0 < σ1 := by nlinarith
        have hs2 : 1 - γ4 < σ1 := by
          by_contra hh; push Not at hh
          nlinarith [mul_nonneg hα0.le (sub_nonneg.2 hh)]
        refine Or.inl (cellB σ1 (max_lt hs0 hs2) (Or.inr ⟨by rw [hqr]; exact hzero, by rw [hσ1]⟩))
  · exact Or.inl (cellA (Or.inl hpos))

end C2
end Type08Sp
end Minimality
