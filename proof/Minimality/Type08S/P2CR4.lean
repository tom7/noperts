module

public import Minimality.Type08S.P2CR3

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 4: `slide_core` — the slide along `u₀ + t e` of the screen quadrilateral
`(x, f, r, g)` with middles `x'` and `p` over the side `x f` (`G-RS` applied).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem fpt_inj (hF : Fr e1 e2 e3) {O : ℝ³} {X Y z X' Y' z' : ℝ}
    (h : fpt e1 e2 e3 O X Y z = fpt e1 e2 e3 O X' Y' z') : X = X' ∧ Y = Y' ∧ z = z' := by
  have h' : pc e1 e2 e3 X Y z = pc e1 e2 e3 X' Y' z' := add_left_cancel h
  have a1 := congrArg (fun v => ⟪v, e1⟫) h'
  have a2 := congrArg (fun v => ⟪v, e2⟫) h'
  have a3 := congrArg (fun v => ⟪v, e3⟫) h'
  simp only [inner_pc_e1 hF, inner_pc_e2 hF, inner_pc_e3 hF] at a1 a2 a3
  exact ⟨a1, a2, a3⟩

theorem fpt_origin (O : ℝ³) : O = fpt e1 e2 e3 O 0 0 0 := by
  simp [fpt, pc]

set_option maxHeartbeats 4000000 in
theorem slide_core (hF : Fr e1 e2 e3) (O w : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg Xp zp : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hXp0 : 0 < Xp) (hXpL : Xp < L) (hDp : L * (zp - κ) - Xp * (zf - κ) ≠ 0)
    (hw : ∀ i : ZMod 4, SlideTest κv
      (quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
        (fpt e1 e2 e3 O Xg Yg zg) (i + 1) -
       quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
        (fpt e1 e2 e3 O Xg Yg zg) i)
      (w - quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
        (fpt e1 e2 e3 O Xg Yg zg) i) (κv • e3) ((κ * κv) • e1))
    (hz : IsRobustUnimodal (fun i => ⟪quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf)
      (fpt e1 e2 e3 O Xr Yr zr) (fpt e1 e2 e3 O Xg Yg zg) i, κv • e3⟫))
    (hbad : NoPersistHDN (quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf)
      (fpt e1 e2 e3 O Xr Yr zr) (fpt e1 e2 e3 O Xg Yg zg)) (κv • e3) ((κ * κv) • e1)) :
    IsRupert ({O, fpt e1 e2 e3 O 0 0 κ, fpt e1 e2 e3 O L 0 zf, fpt e1 e2 e3 O Xr Yr zr,
      fpt e1 e2 e3 O Xg Yg zg, fpt e1 e2 e3 O Xp 0 zp, w} : Finset ℝ³) := by
  classical
  set xx := fpt e1 e2 e3 O 0 0 κ with hxx
  set xf := fpt e1 e2 e3 O L 0 zf with hxf
  set xr := fpt e1 e2 e3 O Xr Yr zr with hxr
  set xg := fpt e1 e2 e3 O Xg Yg zg with hxg
  set xp := fpt e1 e2 e3 O Xp 0 zp with hxp
  have hO : O = fpt e1 e2 e3 O 0 0 0 := fpt_origin O
  have hu₀ : κv • e3 ≠ 0 := by
    intro h
    have := congrArg (fun v => ⟪v, e3⟫) h
    simp only [real_inner_smul_left, hF.n33, inner_zero_left, mul_one] at this
    exact hκv this
  have hMne : ∀ P : ℝ³, ∀ X Y z : ℝ, P = fpt e1 e2 e3 O X Y z → (X ≠ 0 ∨ Y ≠ 0 ∨ z ≠ 0) → P ≠ O := by
    intro P X Y z hP hne hPO
    obtain ⟨h1, h2, h3⟩ := fpt_inj hF ((hP.symm.trans hPO).trans (fpt_origin O))
    rcases hne with h | h | h <;> contradiction
  refine isRupert_of_slide_robust _ ({O, xp} : Finset ℝ³) (κv • e3) ((κ * κv) • e1) hu₀
    (quad xx xf xr xg) ?_ ?_ (by norm_num) κv hκv (core_hcyc hF O hκv hL hYr hYg hcr hcg _) ?_ ?_ hz hbad
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, Finset.mem_insert, Finset.mem_singleton, not_or]
    · exact ⟨hMne _ 0 0 κ rfl (Or.inr (Or.inr hκ)), fun h => by
        have := (fpt_inj hF h).1; linarith⟩
    · exact ⟨hMne _ L 0 zf rfl (Or.inl hL.ne'), fun h => by
        have := (fpt_inj hF h).1; linarith⟩
    · exact ⟨hMne _ Xr Yr zr rfl (Or.inr (Or.inl hYr.ne')), fun h => by
        have := (fpt_inj hF h).2.1; linarith⟩
    · exact ⟨hMne _ Xg Yg zg rfl (Or.inr (Or.inl hYg.ne')), fun h => by
        have := (fpt_inj hF h).2.1; linarith⟩
  · intro y hy hyM hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hyM
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (Or.inl rfl) hyM
    · exact absurd (by simp [quad]) (hyx 0)
    · exact absurd (by simp [quad]) (hyx 1)
    · exact absurd (by simp [quad]) (hyx 2)
    · exact absurd (by simp [quad]) (hyx 3)
    · exact absurd (Or.inr rfl) hyM
    · exact hw i
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · filter_upwards [mid_exists_origin (e1 := e1) (e2 := e2) (e3 := e3) m (zf := zf) hL hκ hκv] with t
        ⟨s, δ, h0, h1, h2, h3⟩
      exact ⟨0, s, δ, h0, h1, h2, (fpt_origin m).trans h3⟩
    · filter_upwards [mid_exists_open (e1 := e1) (e2 := e2) (e3 := e3) O (c := κ * κv) hL hκv hXp0 hXpL hDp]
        with t ⟨s, δ, h0, h1, h2, h3⟩
      exact ⟨0, s, δ, h0, h1, h2, h3⟩

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.slide_core
