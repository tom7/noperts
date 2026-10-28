module

public import Minimality.Type08S.G6C
public import Minimality.Type08S.G6H6

@[expose] public section

set_option autoImplicit true

/-!
# G6' : Lemma 08.H2 (T on H2), wired: `close_T_H2'`
Selection of a robust HDN-free corner polygon on `T ∩ H2` (real core `h2_real`, polygon step
`poly_rupert_H2`), using `¬ PolyHDN2` and `¬ TwoTies` from `¬ CoT2`.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- depth facts on `T ∩ H2`. -/
theorem h2_select {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H2 a b b' c d) :
    c ≠ d ∧ b ≠ d ∧
    let u := b - d
    ((¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫) ∨
     (¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫) ∨
     (¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫) ∨
     (¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫) ∨
     (¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫) ∨
     (¬ Sep ⟪b, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫ ∧ ¬ Sep ⟪d, u⟫ ⟪b', u⟫ ⟪a', u⟫ ⟪c', u⟫) ∨
     (⟪b', u⟫ = ⟪c', u⟫ ∧ (⟪b', u⟫ = ⟪c, u⟫ ∨ ⟪b', u⟫ = ⟪a', u⟫ ∨ ⟪c', u⟫ = ⟪b, u⟫))) := by
  obtain ⟨α1, α4, β1, β6, hdet, hc', hb', ha', hα, hα4, hb1, hb11, hb6⟩ := norm08_coords2 N hT hH
  have hu : 0 < ⟪b - d, b - d⟫ := by
    apply real_inner_self_pos.mpr
    intro h
    apply hdet
    have : b - d = 0 := h
    simp [det3_expand, this]
  refine ⟨?_, ?_, ?_⟩
  · intro h; apply hdet
    have : c - d = 0 := sub_eq_zero.mpr h
    simp [det3_expand, this]
  · intro h; rw [h, sub_self, inner_zero_left] at hu; exact lt_irrefl _ hu
  intro u
  have e : ∀ x : ℝ³, ⟪x, b - d⟫ = ⟪d, b - d⟫ + ⟪x - d, b - d⟫ := by
    intro x; rw [← inner_add_left]; congr 1; abel
  have ec' : ⟪c', b - d⟫ = ⟪d, b - d⟫ + α1 * ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    rw [hc']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α4 * ⟪a - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [hb']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
  have ea' : ⟪a', b - d⟫ = ⟪d, b - d⟫ + β6 * ⟪b - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb : ⟪b, b - d⟫ = ⟪d, b - d⟫ + ⟪b - d, b - d⟫ := e b
  have ec : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := e c
  have hs : (α4 * ⟪a - d, b - d⟫ = 0 ∧ α1 * ⟪a - d, b - d⟫ = 0) ∨
      (0 < α4 * ⟪a - d, b - d⟫ ∧ 0 < α1 * ⟪a - d, b - d⟫) ∨
      (α4 * ⟪a - d, b - d⟫ < 0 ∧ α1 * ⟪a - d, b - d⟫ < 0) := by
    rcases lt_trichotomy ⟪a - d, b - d⟫ 0 with h | h | h
    · exact Or.inr (Or.inr ⟨mul_neg_of_pos_of_neg hα4 h, mul_neg_of_pos_of_neg (by linarith) h⟩)
    · left; rw [h]; simp
    · exact Or.inr (Or.inl ⟨mul_pos hα4 h, mul_pos (by linarith) h⟩)
  have key := h2_real (z0 := ⟪d, b - d⟫) (q := ⟪c - d, b - d⟫) hs hu hb1 hb11 hb6
  simp only [u]
  rw [eb, eb', ec, ec', ea']
  convert key using 4 <;> ring_nf

end Type08Sp
end Minimality
