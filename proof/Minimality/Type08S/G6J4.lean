module

public import Minimality.Type08S.G6J3

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The frame data of `T ∩ H1` (copied from `closeT_H1_caseA`): all seven points in the frame
with `e3 ∥ b - d`. -/
theorem h3_setup {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) :
    ∃ (e1 e2 e3 o : ℝ³) (ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 : ℝ), Fr e1 e2 e3 ∧ 0 < ν ∧ v1 ≠ 0 ∧
      0 < ha ∧ 1 < α1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 0 < β1 ∧ 0 < β6 ∧ 0 < α4 - α4 * β1 - α1 * (1 - γ4) ∧ b - d = ν • e3 ∧
      d = pt e1 e2 e3 o (-v1) 0 0 ∧ b = pt e1 e2 e3 o (-v1) 0 ν ∧ c = pt e1 e2 e3 o 0 0 C0 ∧
      a = pt e1 e2 e3 o (-v1 + w1) ha w3 ∧ a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0) ∧
      b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∧
      c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∧
      c - d = v1 • e1 + C0 • e3 ∧ ∀ p : ℝ³, ⟪p, b - d⟫ = ν * (⟪p, e3⟫) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : b - d = ⟪b - d, e3⟫ • e3 := by
    have := hF.expand (b - d); rw [hu1, hu2] at this; simpa using this
  have hv : c - d = ⟪c - d, e1⟫ • e1 + ⟪c - d, e3⟫ • e3 := by
    have := hF.expand (c - d); rw [hv2] at this; simpa using this
  have hw := hF.expand (a - d)
  generalize hν : ⟪b - d, e3⟫ = ν at *
  generalize hV1 : ⟪c - d, e1⟫ = v1 at *
  generalize hC0 : ⟪c - d, e3⟫ = C0 at *
  generalize hW1 : ⟪a - d, e1⟫ = w1 at *
  generalize hHA : ⟪a - d, e2⟫ = ha at *
  generalize hW3 : ⟪a - d, e3⟫ = w3 at *
  obtain ⟨o, ho⟩ : ∃ o : ℝ³, o = d + v1 • e1 := ⟨_, rfl⟩
  have hd_pt : d = pt e1 e2 e3 o (-v1) 0 0 := by simp only [pt, pc, ho]; module
  have hb_pt : b = pt e1 e2 e3 o (-v1) 0 ν := by
    have : b = d + ν • e3 := by rw [← hu]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have hc_pt : c = pt e1 e2 e3 o 0 0 C0 := by
    have : c = d + (v1 • e1 + C0 • e3) := by rw [← hv]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha_pt : a = pt e1 e2 e3 o (-v1 + w1) ha w3 := by
    have : a = d + (w1 • e1 + ha • e2 + w3 • e3) := by rw [← hw]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha'_pt : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0) := by
    rw [ha', hu, hv]; simp only [pt, pc, ho]; module
  have hb'_pt : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) := by
    rw [hb', hw, hv]; simp only [pt, pc, ho]; module
  have hc'_pt : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) := by
    rw [hc', hw, hu]; simp only [pt, pc, ho]; module
  refine ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hu3, hv1, hw2, hα, hα4, hγ4, hβ1,
    hβ6, hE, hu, hd_pt, hb_pt, hc_pt, ha_pt, ha'_pt, hb'_pt, hc'_pt, hv, ?_⟩
  intro p; rw [hu, real_inner_smul_right]


/-- **Case B polygon lemma** (Theorem 18.1 at `ℓ` on one of the four corner polygons of `T ∩ H1`).
The polygon is `(x0, c', b', y0)` with `x0 ∈ {b, d}`, `y0 ∈ {c, a'}` (the other of each pair is a
double over the corner, `a` a middle over the side `[x0, c']`); it is robust (`¬ Sep`, i.e. not
weakly two-peaked) and has no horizontal double normal. -/
theorem poly_rupert_off {a a' b b' c c' d x0 x0' y0 y0' : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d)
    (hx : (x0 = b ∧ x0' = d) ∨ (x0 = d ∧ x0' = b))
    (hy : (y0 = c ∧ y0' = a') ∨ (y0 = a' ∧ y0' = c))
    (hrob : ¬ Sep ⟪x0, b - d⟫ ⟪b', b - d⟫ ⟪y0, b - d⟫ ⟪c', b - d⟫)
    (hno : NoHDNAt ({x0, c', b', y0} : Finset ℝ³) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hν, hv1, hha, hα, hα4, hγ4, hβ1,
    hβ6, hE, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h3_setup N hT
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
  have hrob' : ¬ Sep zx (α4 * w3 + γ4 * C0) zy (α1 * w3 + β1 * ν) := by
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
  refine poly_core3 hF o (w1 := w1) (C0 := C0) hν hv1 hha hα hβ1 hα4 hγ4 (by nlinarith [mul_pos hα4 hβ1]) hzx0 hzxne hzyne hrob'
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
