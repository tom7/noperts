module

public import Minimality.Type08S.G6H3

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 2000000 in
/-- **The rim polygon `(x0, c', b', y0)` of Theorem 18.1 at `ℓ`, in the frame of H1.**
`x0 ∈ {b, d}` and `y0 ∈ {c, a'}` (the other of each pair is a double over the corner). -/
theorem poly_core2 (hF : Fr e1 e2 e3) (o : ℝ³)
    {ν v1 ha w1 w3 C0 α1 β1 α4 zx zx' zy zy' : ℝ}
    (hν : 0 < ν) (hv1 : v1 ≠ 0) (hha : 0 < ha) (hα : 1 < α1) (hβ1 : 0 < β1) (hγ : 0 < α4)
    (hzx : 0 ≤ zx) (hx : zx' ≠ zx) (hy : zy' ≠ zy)
    (hrob : ¬ Sep zx (α4 * w3 + C0) zy (α1 * w3 + β1 * ν))
    (V : Finset ℝ³)
    (hV : ∀ v ∈ V, v = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨ v = pt e1 e2 e3 o (-v1) 0 zx ∨
      v = pt e1 e2 e3 o (-v1) 0 zx' ∨ v = pt e1 e2 e3 o 0 0 zy ∨ v = pt e1 e2 e3 o 0 0 zy' ∨
      v = pt e1 e2 e3 o (α4 * w1) (α4 * ha) (α4 * w3 + C0) ∨
      v = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν))
    (h1 : pt e1 e2 e3 o (-v1) 0 zx ∈ V) (h2 : pt e1 e2 e3 o 0 0 zy ∈ V)
    (h3 : pt e1 e2 e3 o (α4 * w1) (α4 * ha) (α4 * w3 + C0) ∈ V)
    (h4 : pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∈ V)
    (S : Finset ℝ³) (g1 : pt e1 e2 e3 o (-v1) 0 zx ∈ S) (g2 : pt e1 e2 e3 o 0 0 zy ∈ S)
    (g3 : pt e1 e2 e3 o (α4 * w1) (α4 * ha) (α4 * w3 + C0) ∈ S)
    (g4 : pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∈ S)
    (hno : NoHDNAt S (ν • e3)) : IsRupert V := by
  have i1 := fun X Y z => inner_pt_1 hF o X Y z
  have i2 := fun X Y z => inner_pt_2 hF o X Y z
  have i3 := fun X Y z => inner_pt_3 hF o X Y z
  have hαpos : 0 < α1 := by linarith
  have hαne : α1 ≠ 0 := hαpos.ne'
  have hνne : ν ≠ 0 := hν.ne'
  set A := pt e1 e2 e3 o (-v1 + w1) ha w3 with hA
  set X0p := pt e1 e2 e3 o (-v1) 0 zx with hX0p
  set X0q := pt e1 e2 e3 o (-v1) 0 zx' with hX0q
  set Y0p := pt e1 e2 e3 o 0 0 zy with hY0p
  set Y0q := pt e1 e2 e3 o 0 0 zy' with hY0q
  set B' := pt e1 e2 e3 o (α4 * w1) (α4 * ha) (α4 * w3 + C0) with hB'
  set C' := pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) with hC'
  have hnA : ∀ p, ⟪p, e2⟫ ≠ ⟪A, e2⟫ → p ≠ A := fun p h e => h (by rw [e])
  have hA2 : ⟪A, e2⟫ = ⟪o, e2⟫ + ha := i2 _ _ _
  have hsep' : ¬ Sep (⟪o, e3⟫ + zx) (⟪o, e3⟫ + (α4 * w3 + C0)) (⟪o, e3⟫ + (α1 * w3 + β1 * ν))
      (⟪o, e3⟫ + zy) := by
    rw [sep_shift, sep_swap]; exact hrob
  have hδ : (0 : ℝ) < α1 * ν := mul_pos hαpos hν
  -- the middle `A`
  have hMpt : ∀ s : ℝ, s = 1 / α1 →
      A = X0p + s • (C' - X0p) + (-(zx * (α1 - 1) + β1 * ν) / (α1 * ν)) • (ν • e3) := by
    intro s hs
    subst hs
    simp only [hA, hX0p, hC', pt, pc]
    match_scalars <;> field_simp <;> ring
  have hδne : -(zx * (α1 - 1) + β1 * ν) / (α1 * ν) ≠ 0 := by
    have : 0 < zx * (α1 - 1) + β1 * ν := by
      have := mul_nonneg hzx (sub_nonneg.mpr hα.le)
      have := mul_pos hβ1 hν
      linarith
    exact div_ne_zero (neg_ne_zero.mpr this.ne') hδ.ne'
  have hs0 : 0 < 1 / α1 := by positivity
  have hs1 : 1 / α1 < 1 := by rw [div_lt_one hαpos]; exact hα
  have hDx : X0q = X0p - ((zx - zx') / ν) • (ν • e3) := by
    simp only [hX0q, hX0p, pt, pc]; match_scalars <;> field_simp <;> ring
  have hDy : Y0q = Y0p - ((zy - zy') / ν) • (ν • e3) := by
    simp only [hY0q, hY0p, pt, pc]; match_scalars <;> field_simp <;> ring
  have hdx : (zx - zx') / ν ≠ 0 := div_ne_zero (sub_ne_zero.mpr hx.symm) hνne
  have hdy : (zy - zy') / ν ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy.symm) hνne
  have hne : X0p ≠ A ∧ Y0p ≠ A ∧ B' ≠ A ∧ C' ≠ A := by
    refine ⟨hnA _ ?_, hnA _ ?_, ?_, hnA _ ?_⟩
    · rw [hA2]; simp only [hX0p, i2]; intro h; linarith
    · rw [hA2]; simp only [hY0p, i2]; intro h; linarith
    · intro h
      have h1 : ⟪B', e2⟫ = ⟪A, e2⟫ := by rw [h]
      have h2 : ⟪B', e1⟫ = ⟪A, e1⟫ := by rw [h]
      simp only [hB', hA, i1, i2] at h1 h2
      have h4 : α4 = 1 := by
        have : (α4 - 1) * ha = 0 := by linarith
        rcases mul_eq_zero.mp this with h5 | h5
        · linarith
        · exact absurd h5 hha.ne'
      subst h4
      apply hv1; linarith
    · rw [hA2]; simp only [hC', i2]; intro h
      nlinarith [mul_pos (sub_pos.mpr hα) hha]
  have hz3 : ∀ (X Y z : ℝ), ⟪pt e1 e2 e3 o X Y z, e3⟫ = ⟪o, e3⟫ + z := fun X Y z => i3 X Y z
  have hnoS : ∀ x : ZMod 4 → ℝ³, (∀ i, x i ∈ S) → NoHDNAt (Finset.univ.image x) (ν • e3) :=
    fun x hx => hno.mono (fun p hp => by
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp; exact hx i)
  rcases lt_or_gt_of_ne hv1 with hneg | hpos
  · -- chirality: `L = -v1 > 0`, forward order
    have hq : ∀ i, (!₂[⟪(quad X0p C' B' Y0p) i, e1⟫, ⟪(quad X0p C' B' Y0p) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] : ℝ²) !₂[⟪o, e1⟫ + (-v1 + α1 * w1), ⟪o, e2⟫ + α1 * ha]
          !₂[⟪o, e1⟫ + α4 * w1, ⟪o, e2⟫ + α4 * ha] !₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hX0p, hC', hB', hY0p, i1, i2]
    have hxV : ∀ i, (quad X0p C' B' Y0p) i ∈ V := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [h1, h4, h3, h2]
    have hxS : ∀ i, (quad X0p C' B' Y0p) i ∈ S := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [g1, g4, g3, g2]
    refine frame_uniform hF V {A} {X0q, Y0q} hν (quad X0p C' B' Y0p) hxV ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, Finset.mem_singleton] <;>
        first | exact hne.1 | exact hne.2.1 | exact hne.2.2.1 | exact hne.2.2.2
    · intro v hv
      rcases hV v hv with h | h | h | h | h | h | h
      · exact Or.inl (mem_singleton.mpr h)
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inr (Or.inl (mem_insert.mpr (Or.inl h)))
      · exact Or.inr (Or.inr ⟨3, h⟩)
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton.mpr h)))
      · exact Or.inr (Or.inr ⟨2, h⟩)
      · exact Or.inr (Or.inr ⟨1, h⟩)
    · rw [show (fun i => (!₂[⟪(quad X0p C' B' Y0p) i, e1⟫, ⟪(quad X0p C' B' Y0p) i, e2⟫] : ℝ²)) =
          _ from funext hq]
      have k1 := mul_pos (mul_pos hαpos hha) (neg_pos.mpr hneg)
      have k2 := mul_pos (mul_pos hγ hha) (neg_pos.mpr hneg)
      refine ccw4gen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> nlinarith [k1, k2]
    · rw [show (fun i => ⟪(quad X0p C' B' Y0p) i, e3⟫) = quad (⟪o, e3⟫ + zx)
          (⟪o, e3⟫ + (α1 * w3 + β1 * ν)) (⟪o, e3⟫ + (α4 * w3 + C0)) (⟪o, e3⟫ + zy) from by
        funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, hX0p, hC', hB', hY0p, i3]]
      exact robust4 hsep'
    · exact hnoS _ hxS
    · intro m hm
      rw [mem_singleton] at hm
      have e : (0 : ZMod 4) + 1 = 1 := by decide
      exact ⟨0, 1 / α1, _, hs0, hs1, hδne, by rw [hm, e]; exact hMpt _ rfl⟩
    · intro y hy
      rcases mem_insert.mp hy with h | h
      · exact ⟨0, _, hdx, by rw [h]; exact hDx⟩
      · exact ⟨3, _, hdy, by rw [mem_singleton.mp h]; exact hDy⟩
  · -- reversed order
    have hq : ∀ i, (!₂[⟪(quad Y0p B' C' X0p) i, e1⟫, ⟪(quad Y0p B' C' X0p) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] : ℝ²)
          !₂[⟪o, e1⟫ + α4 * w1, ⟪o, e2⟫ + α4 * ha]
          !₂[⟪o, e1⟫ + (-v1 + α1 * w1), ⟪o, e2⟫ + α1 * ha] !₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hX0p, hC', hB', hY0p, i1, i2]
    have hxV : ∀ i, (quad Y0p B' C' X0p) i ∈ V := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [h2, h3, h4, h1]
    have hxS : ∀ i, (quad Y0p B' C' X0p) i ∈ S := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [g2, g3, g4, g1]
    refine frame_uniform hF V {A} {X0q, Y0q} hν (quad Y0p B' C' X0p) hxV ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, Finset.mem_singleton] <;>
        first | exact hne.1 | exact hne.2.1 | exact hne.2.2.1 | exact hne.2.2.2
    · intro v hv
      rcases hV v hv with h | h | h | h | h | h | h
      · exact Or.inl (mem_singleton.mpr h)
      · exact Or.inr (Or.inr ⟨3, h⟩)
      · exact Or.inr (Or.inl (mem_insert.mpr (Or.inl h)))
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton.mpr h)))
      · exact Or.inr (Or.inr ⟨1, h⟩)
      · exact Or.inr (Or.inr ⟨2, h⟩)
    · rw [show (fun i => (!₂[⟪(quad Y0p B' C' X0p) i, e1⟫, ⟪(quad Y0p B' C' X0p) i, e2⟫] : ℝ²)) =
          _ from funext hq]
      have k1 := mul_pos (mul_pos hαpos hha) hpos
      have k2 := mul_pos (mul_pos hγ hha) hpos
      refine ccw4gen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> nlinarith [k1, k2]
    · rw [show (fun i => ⟪(quad Y0p B' C' X0p) i, e3⟫) = quad (⟪o, e3⟫ + zy)
          (⟪o, e3⟫ + (α4 * w3 + C0)) (⟪o, e3⟫ + (α1 * w3 + β1 * ν)) (⟪o, e3⟫ + zx) from by
        funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, hX0p, hC', hB', hY0p, i3]]
      refine robust4 ?_
      rw [sep_shift, sep_swap, ← sep_comm']; exact hrob
    · exact hnoS _ hxS
    · intro m hm
      rw [mem_singleton] at hm
      have e : (2 : ZMod 4) + 1 = 3 := by decide
      refine ⟨2, 1 - 1 / α1, _, by linarith, by linarith, hδne, ?_⟩
      rw [hm, e]
      have := hMpt _ rfl
      show A = C' + (1 - 1 / α1) • (X0p - C') + _ • (ν • e3)
      rw [this]; module
    · intro y hy
      rcases mem_insert.mp hy with h | h
      · exact ⟨3, _, hdx, by rw [h]; exact hDx⟩
      · exact ⟨0, _, hdy, by rw [mem_singleton.mp h]; exact hDy⟩

end Type08Sp
end Minimality
