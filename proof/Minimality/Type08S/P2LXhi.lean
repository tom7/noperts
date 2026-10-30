module

public import Minimality.Type08S.P2LXcyc

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii) for SC2-V (package K): `lemmaSC2V_hi`  (`σ(zf - zp) < 0`, i.e. `h_{x'} > h_f`)
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The depth pattern: for `S` with `S Xg - Yg ≠ 0`, the pentagon depths `h + s c` have eventually a unique local max. -/
theorem lx_depth {σ S L zp zx zf Xr Yr zr Xg Yg zg : ℝ} (hσσ : σ * σ = 1)
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hlo : σ * (zf - zp) < 0) (hYr : 0 < Yr)
    (hcg0 : S * Xg - Yg ≠ 0) (hc : ClassV2tail L zx zf Xr Yr zr Xg Yg zg) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), QTop 5 fun i =>
      five (σ * zp) (σ * zf) (σ * zr) (σ * zg) (σ * zx) i + s * five 0 (S * L) (S * Xr - Yr) (S * Xg - Yg) 0 i := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := z5_sub_one
  have fx' : LL (σ * zp) 0 (σ * zx) 0 := Or.inl (by linarith)
  have ffx' : LL (σ * zf) (S * L) (σ * zp) 0 := Or.inl (by linarith)
  have hxf : 0 < σ * (zx - zf) := by linarith
  rcases hc with ⟨hXr, hzr, hYgr, hsep⟩ | ⟨hXg, hzg, hYrg, hsep⟩ | ⟨hYY, hXg, hzg, hXr, hsep⟩
  · -- t = r : r ties f in h, below it in c
    have hrf : LL (σ * zr) (S * Xr - Yr) (σ * zf) (S * L) :=
      Or.inr ⟨by rw [hzr], by rw [hXr]; linarith⟩
    have hgf : 0 < σ * (zg - zf) := sgn_pos hσσ hxf (by nlinarith)
    have tri : LL (σ * zx) 0 (σ * zg) (S * Xg - Yg) ∨ LL (σ * zg) (S * Xg - Yg) (σ * zx) 0 := by
      rcases lt_trichotomy (σ * zx) (σ * zg) with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases lt_or_gt_of_ne hcg0 with h' | h'
        · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
        · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl h)
    rcases tri with hxg | hgx
    · refine qtop_ev _ _ 3 ?_
      intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; simp only [t0, five_0, five_4]; exact fx'
      · left; simp only [t1, five_0, five_1]; exact ffx'
      · left; simp only [t2, five_1, five_2]; exact hrf
      · exact absurd rfl hi
      · left; simp only [t4, five_3, five_4]; exact hxg
    · refine qtop_ev _ _ 4 ?_
      intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; simp only [t0, five_0, five_4]; exact fx'
      · left; simp only [t1, five_0, five_1]; exact ffx'
      · left; simp only [t2, five_1, five_2]; exact hrf
      · right; simp only [s3, five_3, five_4]; exact hgx
      · exact absurd rfl hi
  · -- t = g : g ties f, r strictly below f
    have hrf : LL (σ * zr) (S * Xr - Yr) (σ * zf) (S * L) := Or.inl (by linarith [sgn_neg (b := zr - zf) hσσ hxf (by linarith [hsep, mul_comm (zr - zf) (zx - zf)])])
    have hgx : LL (σ * zg) (S * Xg - Yg) (σ * zx) 0 := Or.inl (by rw [hzg]; linarith)
    refine qtop_ev _ _ 4 ?_
    intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; simp only [t0, five_0, five_4]; exact fx'
    · left; simp only [t1, five_0, five_1]; exact ffx'
    · left; simp only [t2, five_1, five_2]; exact hrf
    · right; simp only [s3, five_3, five_4]; exact hgx
    · exact absurd rfl hi
  · have hrf : LL (σ * zr) (S * Xr - Yr) (σ * zf) (S * L) := Or.inl (by linarith [sgn_neg (b := zr - zf) hσσ hxf (by linarith [hsep, mul_comm (zr - zf) (zx - zf)])])
    have hgx : LL (σ * zg) (S * Xg - Yg) (σ * zx) 0 := Or.inl (by rw [hzg]; linarith)
    refine qtop_ev _ _ 4 ?_
    intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; simp only [t0, five_0, five_4]; exact fx'
    · left; simp only [t1, five_0, five_1]; exact ffx'
    · left; simp only [t2, five_1, five_2]; exact hrf
    · right; simp only [s3, five_3, five_4]; exact hgx
    · exact absurd rfl hi

end Type08Sp
end Minimality
