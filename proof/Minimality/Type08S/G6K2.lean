module

public import Minimality.Type08S.G6K1

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 2000000 in
/-- **Theorem 18.1 at `ℓ` on the planar corner polygon `X_2a = (d, a, b', c)` at `T'`** in the frame
`e3 ∥ b - d`.  `b` is a double over the corner `d`, `c'` a double over the corner `a`, `a'` a middle
over the side `[c, d]`. -/
theorem poly_coreTp (hF : Fr e1 e2 e3) (o : ℝ³)
    {ν v1 ha w1 w3 C0 α4 β1 γ4 β6 γ6 : ℝ}
    (hν : 0 < ν) (hv1 : v1 ≠ 0) (hha : 0 < ha) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 0 < α4 + γ4 - 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hrob : ¬ Sep 0 (α4 * w3 + γ4 * C0) w3 C0)
    (V : Finset ℝ³)
    (hV : ∀ v ∈ V, v = pt e1 e2 e3 o (-v1) 0 0 ∨ v = pt e1 e2 e3 o (-v1) 0 ν ∨
      v = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨ v = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) ∨
      v = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∨
      v = pt e1 e2 e3 o 0 0 C0 ∨ v = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν))
    (h1 : pt e1 e2 e3 o (-v1) 0 0 ∈ V) (h2 : pt e1 e2 e3 o (-v1 + w1) ha w3 ∈ V)
    (h3 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ V)
    (h4 : pt e1 e2 e3 o 0 0 C0 ∈ V)
    (S : Finset ℝ³) (g1 : pt e1 e2 e3 o (-v1) 0 0 ∈ S) (g2 : pt e1 e2 e3 o (-v1 + w1) ha w3 ∈ S)
    (g3 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ S)
    (g4 : pt e1 e2 e3 o 0 0 C0 ∈ S)
    (hno : NoHDNAt S (ν • e3)) : IsRupert V := by
  have i1 := fun X Y z => inner_pt_1 hF o X Y z
  have i2 := fun X Y z => inner_pt_2 hF o X Y z
  have i3 := fun X Y z => inner_pt_3 hF o X Y z
  have hνne : ν ≠ 0 := hν.ne'
  set D0 := pt e1 e2 e3 o (-v1) 0 0 with hD0
  set Bq := pt e1 e2 e3 o (-v1) 0 ν with hBq
  set A := pt e1 e2 e3 o (-v1 + w1) ha w3 with hA
  set C1 := pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) with hC1
  set Bp := pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) with hBp
  set Cc := pt e1 e2 e3 o 0 0 C0 with hCc
  set A' := pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) with hA'
  have hsep' : ¬ Sep (⟪o, e3⟫ + 0) (⟪o, e3⟫ + (α4 * w3 + γ4 * C0)) (⟪o, e3⟫ + w3)
      (⟪o, e3⟫ + C0) := by
    rw [sep_shift]; exact hrob
  have hsep'' : ¬ Sep (⟪o, e3⟫ + C0) (⟪o, e3⟫ + w3) (⟪o, e3⟫ + (α4 * w3 + γ4 * C0))
      (⟪o, e3⟫ + 0) := by
    rw [sep_shift]
    intro h; apply hrob
    simp only [Sep, max_comm C0 w3, min_comm C0 w3, max_comm (α4 * w3 + γ4 * C0) 0,
      min_comm (α4 * w3 + γ4 * C0) 0] at h ⊢
    tauto
  have hs1 : 0 < 1 - γ6 := by linarith
  have hMpt : A' = Cc + (1 - γ6) • (D0 - Cc) + β6 • (ν • e3) := by
    simp only [hA', hCc, hD0, pt, pc]
    match_scalars <;> ring
  have hMpt' : A' = D0 + γ6 • (Cc - D0) + β6 • (ν • e3) := by
    simp only [hA', hCc, hD0, pt, pc]
    match_scalars <;> ring
  have hDx : Bq = D0 - (-1 : ℝ) • (ν • e3) := by
    simp only [hBq, hD0, pt, pc]; match_scalars <;> ring
  have hDy : C1 = A - (-β1) • (ν • e3) := by
    simp only [hC1, hA, pt, pc]; match_scalars <;> ring
  have hne : D0 ≠ A' ∧ A ≠ A' ∧ Bp ≠ A' ∧ Cc ≠ A' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have h1 : ⟪D0, e1⟫ = ⟪A', e1⟫ := by rw [h]
      simp only [hD0, hA', i1] at h1
      have : v1 * γ6 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      exacts [hv1 h, hγ6.ne' h]
    · intro h
      have h1 : ⟪A, e2⟫ = ⟪A', e2⟫ := by rw [h]
      simp only [hA, hA', i2] at h1
      linarith
    · intro h
      have h1 : ⟪Bp, e2⟫ = ⟪A', e2⟫ := by rw [h]
      simp only [hBp, hA', i2] at h1
      nlinarith [mul_pos hα4 hha]
    · intro h
      have h1 : ⟪Cc, e1⟫ = ⟪A', e1⟫ := by rw [h]
      simp only [hCc, hA', i1] at h1
      have : v1 * (1 - γ6) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      exacts [hv1 h, hs1.ne' h]
  have hnoS : ∀ x : ZMod 4 → ℝ³, (∀ i, x i ∈ S) → NoHDNAt (Finset.univ.image x) (ν • e3) :=
    fun x hx => hno.mono (fun p hp => by
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp; exact hx i)
  rcases lt_or_gt_of_ne hv1 with hneg | hpos
  · -- `L = -v1 > 0`
    have hq : ∀ i, (!₂[⟪(quad D0 A Bp Cc) i, e1⟫, ⟪(quad D0 A Bp Cc) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] : ℝ²)
          !₂[⟪o, e1⟫ + (-v1 + w1), ⟪o, e2⟫ + ha]
          !₂[⟪o, e1⟫ + (-v1 * (1 - γ4) + α4 * w1), ⟪o, e2⟫ + α4 * ha]
          !₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hD0, hA, hBp, hCc, i1, i2]
    have hxV : ∀ i, (quad D0 A Bp Cc) i ∈ V := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h4]
    have hxS : ∀ i, (quad D0 A Bp Cc) i ∈ S := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [g1, g2, g3, g4]
    refine frame_uniform hF V {A'} {Bq, C1} hν (quad D0 A Bp Cc) hxV ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, Finset.mem_singleton] <;>
        first | exact hne.1 | exact hne.2.1 | exact hne.2.2.1 | exact hne.2.2.2
    · intro v hv
      rcases hV v hv with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inr (Or.inl (mem_insert.mpr (Or.inl h)))
      · exact Or.inr (Or.inr ⟨1, h⟩)
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton.mpr h)))
      · exact Or.inr (Or.inr ⟨2, h⟩)
      · exact Or.inr (Or.inr ⟨3, h⟩)
      · exact Or.inl (mem_singleton.mpr h)
    · rw [show (fun i => (!₂[⟪(quad D0 A Bp Cc) i, e1⟫, ⟪(quad D0 A Bp Cc) i, e2⟫] : ℝ²)) =
          _ from funext hq]
      have hL := neg_pos.mpr hneg
      have k1 := mul_pos (mul_pos hL hha) hγ4
      have k2 := mul_pos hL hha
      have k3 := mul_pos (mul_pos hL hha) hE
      have k4 := mul_pos (mul_pos hL hha) hα4
      refine ccw4gen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> nlinarith [k1, k2, k3, k4]
    · rw [show (fun i => ⟪(quad D0 A Bp Cc) i, e3⟫) = quad (⟪o, e3⟫ + 0)
          (⟪o, e3⟫ + w3) (⟪o, e3⟫ + (α4 * w3 + γ4 * C0)) (⟪o, e3⟫ + C0) from by
        funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, hD0, hA, hBp, hCc, i3]]
      exact robust4 hsep'
    · exact hnoS _ hxS
    · intro m hm
      rw [mem_singleton] at hm
      have e : (3 : ZMod 4) + 1 = 0 := by decide
      refine ⟨3, 1 - γ6, β6, hs1, by linarith, hβ6.ne', ?_⟩
      rw [hm, e]
      simpa only [quad_0, quad_3] using hMpt
    · intro y hy
      rcases mem_insert.mp hy with h | h
      · exact ⟨0, -1, by norm_num, by rw [h, quad_0]; exact hDx⟩
      · exact ⟨1, -β1, neg_ne_zero.mpr hβ1.ne', by rw [mem_singleton.mp h, quad_1]; exact hDy⟩
  · -- reversed order
    have hq : ∀ i, (!₂[⟪(quad Cc Bp A D0) i, e1⟫, ⟪(quad Cc Bp A D0) i, e2⟫] : ℝ²) =
        quad (!₂[⟪o, e1⟫ + 0, ⟪o, e2⟫ + 0] : ℝ²)
          !₂[⟪o, e1⟫ + (-v1 * (1 - γ4) + α4 * w1), ⟪o, e2⟫ + α4 * ha]
          !₂[⟪o, e1⟫ + (-v1 + w1), ⟪o, e2⟫ + ha]
          !₂[⟪o, e1⟫ + (-v1), ⟪o, e2⟫ + 0] i := by
      intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, hD0, hA, hBp, hCc, i1, i2]
    have hxV : ∀ i, (quad Cc Bp A D0) i ∈ V := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [h4, h3, h2, h1]
    have hxS : ∀ i, (quad Cc Bp A D0) i ∈ S := by
      intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [g4, g3, g2, g1]
    refine frame_uniform hF V {A'} {Bq, C1} hν (quad Cc Bp A D0) hxV ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, Finset.mem_singleton] <;>
        first | exact hne.1 | exact hne.2.1 | exact hne.2.2.1 | exact hne.2.2.2
    · intro v hv
      rcases hV v hv with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr ⟨3, h⟩)
      · exact Or.inr (Or.inl (mem_insert.mpr (Or.inl h)))
      · exact Or.inr (Or.inr ⟨2, h⟩)
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton.mpr h)))
      · exact Or.inr (Or.inr ⟨1, h⟩)
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inl (mem_singleton.mpr h)
    · rw [show (fun i => (!₂[⟪(quad Cc Bp A D0) i, e1⟫, ⟪(quad Cc Bp A D0) i, e2⟫] : ℝ²)) =
          _ from funext hq]
      have k1 := mul_pos (mul_pos hpos hha) hγ4
      have k2 := mul_pos hpos hha
      have k3 := mul_pos (mul_pos hpos hha) hE
      have k4 := mul_pos (mul_pos hpos hha) hα4
      refine ccw4gen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> nlinarith [k1, k2, k3, k4]
    · rw [show (fun i => ⟪(quad Cc Bp A D0) i, e3⟫) = quad (⟪o, e3⟫ + C0)
          (⟪o, e3⟫ + (α4 * w3 + γ4 * C0)) (⟪o, e3⟫ + w3) (⟪o, e3⟫ + 0) from by
        funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, hD0, hA, hBp, hCc, i3]]
      exact robust4 hsep''
    · exact hnoS _ hxS
    · intro m hm
      rw [mem_singleton] at hm
      have e : (3 : ZMod 4) + 1 = 0 := by decide
      refine ⟨3, γ6, β6, hγ6, hγ61, hβ6.ne', ?_⟩
      rw [hm, e]
      simpa only [quad_0, quad_3] using hMpt'
    · intro y hy
      rcases mem_insert.mp hy with h | h
      · exact ⟨3, -1, by norm_num, by rw [h, quad_3]; exact hDx⟩
      · exact ⟨2, -β1, neg_ne_zero.mpr hβ1.ne', by rw [mem_singleton.mp h, quad_2]; exact hDy⟩

end Type08Sp
end Minimality
