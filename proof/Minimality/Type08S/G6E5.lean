module

public import Minimality.Type08S.G6E4

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **Case B polygon lemma** (Theorem 18.1 at `ℓ` on one of the four corner polygons of `T ∩ H1`).
The polygon is `(x0, c', b', y0)` with `x0 ∈ {b, d}`, `y0 ∈ {c, a'}` (the other of each pair is a
double over the corner, `a` a middle over the side `[x0, c']`); it is robust (`¬ Sep`, i.e. not
weakly two-peaked) and has no horizontal double normal. -/
theorem poly_rupert_H1 {a a' b b' c c' d x0 x0' y0 y0' : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H1 b b' c c' d)
    (hx : (x0 = b ∧ x0' = d) ∨ (x0 = d ∧ x0' = b))
    (hy : (y0 = c ∧ y0' = a') ∨ (y0 = a' ∧ y0' = c))
    (hrob : ¬ Sep ⟪x0, b - d⟫ ⟪b', b - d⟫ ⟪y0, b - d⟫ ⟪c', b - d⟫)
    (hno : NoHDNAt ({x0, c', b', y0} : Finset ℝ³) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α, β1, γ4, β6, hF, hν, hv1, hha, hα, hβ1, hγ,
    hβ6, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h1_setup N hT hH
  have i3 := fun X Y z => inner_pt_3 hF o X Y z
  have ez : ∀ (p : ℝ³) (X Y z : ℝ), p = pt e1 e2 e3 o X Y z → ⟪p, b - d⟫ = ν * (z + ⟪o, e3⟫) := by
    intro p X Y z hp; rw [hdep, hp, i3, add_comm]
  obtain ⟨zx, zx', hzx, hx0, hx0'⟩ : ∃ zx zx' : ℝ, ((zx = ν ∧ zx' = 0) ∨ (zx = 0 ∧ zx' = ν)) ∧
      x0 = pt e1 e2 e3 o (-v1) 0 zx ∧ x0' = pt e1 e2 e3 o (-v1) 0 zx' := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨ν, 0, Or.inl ⟨rfl, rfl⟩, by rw [h1, hb], by rw [h2, hd]⟩
    · exact ⟨0, ν, Or.inr ⟨rfl, rfl⟩, by rw [h1, hd], by rw [h2, hb]⟩
  obtain ⟨zy, zy', hzy, hy0, hy0'⟩ : ∃ zy zy' : ℝ, (zy = C0 ∧ zy' = β6 * ν + C0 ∨
      zy = β6 * ν + C0 ∧ zy' = C0) ∧
      y0 = pt e1 e2 e3 o 0 0 zy ∧ y0' = pt e1 e2 e3 o 0 0 zy' := by
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨C0, β6 * ν + C0, Or.inl ⟨rfl, rfl⟩, by rw [h1, hc], by rw [h2, ha']⟩
    · exact ⟨β6 * ν + C0, C0, Or.inr ⟨rfl, rfl⟩, by rw [h1, ha'], by rw [h2, hc]⟩
  have hzx0 : 0 ≤ zx := by rcases hzx with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  have hzxne : zx' ≠ zx := by
    rcases hzx with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> intro e <;> linarith
  have hzyne : zy' ≠ zy := by
    rcases hzy with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> intro e <;> nlinarith [mul_pos hβ6 hν]
  have hrob' : ¬ Sep zx (α * w3 + γ4 * C0) zy (α * w3 + β1 * ν) := by
    have e0 := ez x0 _ _ _ hx0
    have e1' := ez b' _ _ _ hb'
    have e2' := ez y0 _ _ _ hy0
    have e3' := ez c' _ _ _ hc'
    rw [e0, e1', e2', e3', sep_aff hν] at hrob
    exact hrob
  have hmem : ∀ p : ℝ³, (p = d ∨ p = a ∨ p = a' ∨ p = b ∨ p = b' ∨ p = c ∨ p = c') →
      p ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  rw [hu] at hno
  refine poly_core hF o (w1 := w1) (C0 := C0) hν hv1 hha hα hβ1 (by linarith) hzx0 hzxne hzyne hrob'
    (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ?_ ?_ ?_ ?_ ?_ ({x0, c', b', y0} : Finset ℝ³)
    ?_ ?_ ?_ ?_ hno
  · intro v hv'
    simp only [mem_insert, mem_singleton] at hv'
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hv' with h | h | h | h | h | h | h <;>
      simp only [h, haa, hb', hc', ← h1, ← h2, ← h3, ← h4, hx0, hx0', hy0, hy0', hd, hb, hc, ha',
        true_or, or_true]
  · rw [← hx0]; apply hmem; rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  · rw [← hy0]; apply hmem; rcases hy with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  · rw [← hb']; apply hmem; simp
  · rw [← hc']; apply hmem; simp
  · rw [← hx0]; simp
  · rw [← hy0]; simp
  · rw [← hb']; simp
  · rw [← hc']; simp

end Type08Sp
end Minimality
