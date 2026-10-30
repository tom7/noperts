module

public import Minimality.Type08S.P2TB2c

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B2d: `angBig_Yrg` (AngBig <=> `Yg < Yr` in the `K_2` frame) and `np_K2T`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem angBig_Yrg {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫) (hang : AngBig a b b' c d)
    (hYg : 0 < ⟪c - b, e2⟫) (hYp : ⟪a - b, e2⟫ = 0) (hXa : 0 < ⟪a - b, e1⟫) :
    ⟪c - b, e2⟫ < ⟪b' - b, e2⟫ := by
  have hd1 : ⟪d - b, e1⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hd2 : ⟪d - b, e2⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n23]; ring
  have hd3 : ⟪d - b, e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  have h1 := det3_pts hF b c b' a d b d
  have h2 := det3_pts hF b a d c d b d
  simp only [sub_self, inner_zero_left, sub_zero, hd1, hd2, hd3, hYp] at h1 h2
  unfold AngBig at hang
  rw [h1, h2] at hang
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos hXa hYg, mul_pos (mul_pos hXa hYg) (mul_self_pos.mpr hκ), mul_pos hXa hXa,
    mul_nonneg (mul_nonneg (mul_pos hXa hYg).le (mul_self_pos.mpr hκ).le) (sub_nonneg.mpr hcon), mul_pos (mul_pos hXa hXa) (mul_self_pos.mpr hκ)]

theorem np_K2T {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) (hang : AngBig a b b' c d)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : d - b = κ • e3)
    (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c' - b, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad d c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad d c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_K2T N hT hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hcop, hchord⟩ := extra_K2T N hT hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : d = fpt e1 e2 e3 b 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c' = fpt e1 e2 e3 b ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ := by
    have := pc_coords hF b c'; rw [hf2] at this; exact this
  have hxr : b' = fpt e1 e2 e3 b ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ := pc_coords hF b b'
  have hxg : c = fpt e1 e2 e3 b ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ := pc_coords hF b c
  have hxp : a = fpt e1 e2 e3 b ⟪a - b, e1⟫ 0 ⟪a - b, e3⟫ := by
    have := pc_coords hF b a; rw [hYp] at this; exact this
  have hxw : a' = fpt e1 e2 e3 b ⟪a' - b, e1⟫ ⟪a' - b, e2⟫ ⟪a' - b, e3⟫ := pc_coords hF b a'
  have hP : ∀ j, quad d c' b' c j = Qg e1 e2 e3 b κ ⟪c' - b, e1⟫ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫
      ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ (id j) := by
    intro j
    simp only [Qg, id]
    rw [← hxx, ← hxf, ← hxr, ← hxg]
  have hXq : ⟪a' - b, e1⟫ = ⟪c - b, e1⟫ := by
    rw [hlam] at hcop
    exact mul_right_cancel₀ hYg.ne' (by linarith [hcop])
  have hzq : κ * (⟪a' - b, e3⟫ - ⟪c - b, e3⟫) < 0 := by
    rw [hlam] at hchord
    nlinarith [hchord, hYg]
  have hYrg : ⟪c - b, e2⟫ < ⟪b' - b, e2⟫ := angBig_Yrg N hT hF hκ hxe hf2 hL hr hang hYg hYp hXd0
  have hxw' : a' = fpt e1 e2 e3 b ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪a' - b, e3⟫ := by
    rw [← hXq, ← hlam]; exact hxw
  have hw := rows_T4g hF b (κ := κ) (κv := κv) (L := ⟪c' - b, e1⟫) (zf := ⟪c' - b, e3⟫)
    (Xr := ⟪b' - b, e1⟫) (Yr := ⟪b' - b, e2⟫) (zr := ⟪b' - b, e3⟫) (Xg := ⟪c - b, e1⟫)
    (Yg := ⟪c - b, e2⟫) (zg := ⟪c - b, e3⟫) (zq := ⟪a' - b, e3⟫) hκ hκv0 hL hYg hYrg hcr hzq
  have key := close_np_frame hF b (fpt e1 e2 e3 b ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪a' - b, e3⟫) hκ hκv0 hL hr
    hYg hcr hcg hXd0 hXdL hDp hw (quad d c' b' c) id (fun _ => rfl) hP hk3 σ u e hu
    (by rw [he]) hcyc hleft hz hbad
  rw [← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw'] at key
  convert key using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

end Type08Sp
end Minimality

