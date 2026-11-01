module

public import Minimality.Type08S.C2K6
public import Minimality.Type08S.C2K7B
public import Minimality.Type08S.C2K7C

@[expose] public section

/-!
# K7 / D: `s4TRK4_hasLexCell`
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k7_cs (P Q R : ℝ³) (hΔ : det3 P Q R ≠ 0) (hB : 0 < ⟪Q, R⟫) (hA : 0 < ⟪R, R⟫) :
    0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by
  set w : ℝ³ := ⟪R, R⟫ • Q - ⟪Q, R⟫ • R with hw
  have hdet : det3 P Q w = -⟪Q, R⟫ * det3 P Q R := by
    simp only [hw, det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : det3 P Q (0 : ℝ³) = 0 := by simp [det3_expand]
    rw [this] at hdet
    have := mul_eq_zero.mp hdet.symm
    rcases this with h | h
    · linarith
    · exact hΔ h
  have hpos : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hw0
  have e : ⟪w, w⟫ = ⟪R, R⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by
    simp only [hw, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm Q R]; ring
  rw [e] at hpos
  exact pos_of_mul_pos_right hpos hA.le

end C2

set_option maxHeartbeats 6400000 in
theorem s4TRK4_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : S4TRK4 a a' b b' c c' d) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨⟨⟨hT, hL, hγ⟩, hs⟩, hBpos, hx0, hy0⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have eA : det3 (c - b') (a - d) (b - d) = -(1 - γ4) * D := by
    rw [hb']; simp only [hD, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hγ41 : γ4 = 1 := by
    have := (mul_eq_zero.mp (by rw [← eA]; exact hγ : -(1 - γ4) * D = 0)).resolve_right hD0
    linarith
  subst hγ41
  have hβ11 : β1 < 1 := by nlinarith
  have hfac : α4 * (1 - β1) < α1 * β6 := C2.k7_facet N hc' hb' ha' (lt_trans one_pos hα1) hβ6
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hΔ : det3 q r p ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 q r p := by simp only [hp, hq, hr, det3_expand]; ring
    rw [e, h]
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hB : 0 < ⟪r, p⟫ := hBpos
  have hf : a' - b = (β6 - 1) • p + q := by rw [ha']; module
  have hx : ⟪q, p⟫ + (β6 - 1) * ⟪p, p⟫ = 0 := by
    have := hx0; rw [hf, inner_add_left, real_inner_smul_left] at this; linarith
  have hs' : ⟪q, r⟫ + (β6 - 1) * ⟪r, p⟫ = 0 := by
    have := hs; rw [hf, inner_add_left, real_inner_smul_left, real_inner_comm r p] at this; linarith
  -- depths at the view p
  have eC' : ⟪c', p⟫ = ⟪d, p⟫ + α1 * ⟪r, p⟫ + β1 * ⟪p, p⟫ := by
    rw [hc']; simp only [inner_add_left, real_inner_smul_left]
  have eB' : ⟪b', p⟫ = ⟪d, p⟫ + α4 * ⟪r, p⟫ + ⟪q, p⟫ := by
    rw [hb']; simp only [inner_add_left, real_inner_smul_left]; ring
  have eB : ⟪b, p⟫ = ⟪d, p⟫ + ⟪p, p⟫ := by
    nth_rewrite 1 [show b = d + (b - d) by abel]; rw [inner_add_left]
  have eA' : ⟪a', p⟫ = ⟪b, p⟫ := by
    have := hx0; rw [inner_sub_left] at this; linarith
  have eC : ⟪c, p⟫ = ⟪d, p⟫ + ⟪q, p⟫ := by rw [hq, inner_sub_left]; ring
  have hEq0 : ⟪c', p⟫ = ⟪b', p⟫ := by
    rcases hL with ⟨hK, hN, -, -⟩ | ⟨hK, hX, -, hE', -, -⟩
    · exact hN.2.1.symm
    · exact hE'
  have hEq : α1 * ⟪r, p⟫ + β1 * ⟪p, p⟫ = ⟪q, p⟫ + α4 * ⟪r, p⟫ := by
    rw [eC', eB'] at hEq0; linarith
  -- (B3): `⟪c', p⟫ < ⟪b, p⟫`; (B2) is impossible by the facet
  have hZ : α1 * ⟪r, p⟫ + β1 * ⟪p, p⟫ < ⟪p, p⟫ := by
    rcases hL with ⟨hK, hN, -, -⟩ | ⟨hK, hX, -, hE', -, -⟩
    · exfalso
      have h1 : ⟪b, p⟫ = ⟪c', p⟫ := hN.1
      rw [eB, eC'] at h1
      have h2 : α1 * ⟪r, p⟫ + β1 * ⟪p, p⟫ = ⟪p, p⟫ := by linarith
      have h3 : α4 * ⟪r, p⟫ = β6 * ⟪p, p⟫ := by nlinarith
      nlinarith [mul_pos hB hpp, mul_pos hB hB]
    · have hsep : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪c, b - d⟫ := by
        by_contra hn; exact hK (C2.robKb_of_not_sep hn)
      have hcb' : ⟪c, p⟫ < ⟪b', p⟫ := by rw [eC, eB']; nlinarith [mul_pos hα4 hB]
      have hle : ⟪c', p⟫ ≤ ⟪b, p⟫ := by
        unfold Sep at hsep
        rcases hsep with h | h
        · simp only [max_le_iff, le_min_iff] at h; exact h.1.1
        · simp only [max_le_iff, le_min_iff] at h; linarith [h.1.2, h.2.2]
      have hne : ⟪c', p⟫ ≠ ⟪b, p⟫ := by
        intro heq
        apply hX
        unfold Sep
        left
        simp only [max_le_iff, le_min_iff]
        have : ⟪a', b - d⟫ = ⟪b, b - d⟫ := eA'
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      have := lt_of_le_of_ne hle hne
      rw [eC', eB] at this; linarith
  have hy : 0 < ⟪q, q⟫ + (β6 - 1) * ⟪q, p⟫ := by
    have hf0 : (β6 - 1) • p + q ≠ 0 := by
      intro h0
      have hq' : q = (1 - β6) • p := by
        have h' : q = -((β6 - 1) • p) := eq_neg_of_add_eq_zero_right h0
        rw [h']; module
      apply hΔ; rw [hq']
      simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
    have hpos := real_inner_self_pos.2 hf0
    have e : ⟪(β6 - 1) • p + q, (β6 - 1) • p + q⟫ = ⟪q, q⟫ + (β6 - 1) * ⟪q, p⟫ := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm q p]
      linear_combination (β6 - 1) * hx
    rw [e] at hpos; exact hpos
  have hA : 0 < ⟪p, p⟫ := hpp
  have hCS := C2.k7_cs q r p hΔ hB hA
  have eO : fpoint q r p d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eBp : fpoint q r p d (0, 0, 1) = b := by simp only [fpoint, fcomb, hp]; module
  have eCq : fpoint q r p d (1, 0, 0) = c := by simp only [fpoint, fcomb, hq]; module
  have eAr : fpoint q r p d (0, 1, 0) = a := by simp only [fpoint, fcomb, hr]; module
  have eA'f : fpoint q r p d (1, 0, β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eC'f : fpoint q r p d (0, α1, β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB'f : fpoint q r p d (1, α4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint q r p d (0, 1, 0) ∨ y = fpoint q r p d (0, 0, 0) ∨
      y = fpoint q r p d (0, 0, 1) ∨ y = fpoint q r p d (1, 0, β6) ∨ y = fpoint q r p d (1, α4, 0) ∨
      y = fpoint q r p d (1, 0, 0) ∨ y = fpoint q r p d (0, α1, β1) := by
    intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl eO.symm)
    · exact Or.inl eAr.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl eA'f.symm)))
    · exact Or.inr (Or.inr (Or.inl eBp.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eB'f.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eCq.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eC'f.symm)))))
  have hne : b - d ≠ 0 := hp0
  refine ⟨b - d, hne, ?_⟩
  refine C2.k7_hasLexCellAt (V8 a a' b b' c c' d) q r p d hΔ hα1 hβ1 hα4 hβ6 hB hx hs' hEq hZ hy hfac hCS ?_ hVall
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
  · simp only [C2.k7Cyc, pc5_0, eBp]; simp [V8]
  · simp only [C2.k7Cyc, pc5_1, eA'f]; simp [V8]
  · simp only [C2.k7Cyc, pc5_2, eCq]; simp [V8]
  · simp only [C2.k7Cyc, pc5_3, eB'f]; simp [V8]
  · simp only [C2.k7Cyc, pc5_4, eC'f]; simp [V8]

end Type08Sp
end Minimality
