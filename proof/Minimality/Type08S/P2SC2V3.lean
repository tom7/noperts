module

public import Minimality.Type08S.P2SC2V1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-V, near end `f̄ = ḡ` of a top side (package G): parameter form

`g = (L, Y, zf)`, `r = (Xr, Y, zr)`, `L < Xr`; `x` and `r` strictly on opposite sides of `z_f`.  Motion `M0` as for
a top vertex but `γ0` is shifted by `η > 0` (`V(g) = (η, 0)`, so `g`'s G-row is strict); `S = {F-row of f, top row of g}`
(one dependency), `M1 = (0,0,0,0,aY)`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem sc2V_core_end (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr zr Y b κ : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hY : 0 < Y) (hXr : L < Xr)
    (hb : 0 < b) (hb1 : 0 < L + σ * b * (zp - zf)) (hb2 : 0 < L + σ * b * (zx - zf))
    (hb3 : 0 < (L - Xr) * (L - Xr + σ * b * (zr - zf)))
    (hzf : 0 ≤ σ * (zf - zp))
    (hκr : κ * (zr - zf) < 0) (hκx : 0 < κ * (zx - zf))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx zf Xr Y zr L Y zf E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Y zr L Y zf E) := by
  have hσ : σ ≠ 0 := by rintro rfl; simp at hzx
  have hXL : 0 < Xr - L := sub_pos.2 hXr
  -- choice of η
  obtain ⟨η, hη0, hηY, hgap⟩ : ∃ η : ℝ, 0 < η ∧ η < Y ∧
      σ * (zf - zr) * η / (Xr - L) < (σ ^ 2 * b * Y * L + σ * (zf - zp) * (Y - η)) / L := by
    set g0 := (σ ^ 2 * b * Y * L + σ * (zf - zp) * Y) / L with hg0
    set k := σ * (zf - zp) / L + σ * (zf - zr) / (Xr - L) with hk
    have hg00 : 0 < g0 := by
      have : 0 < σ ^ 2 * b * Y * L := by positivity
      rw [hg0]; have : 0 ≤ σ * (zf - zp) * Y := mul_nonneg hzf hY.le
      positivity
    refine ⟨min (Y / 2) (g0 / (2 * (|k| + 1))), lt_min (by positivity) (by positivity),
      (min_le_left _ _).trans_lt (by linarith), ?_⟩
    set η := min (Y / 2) (g0 / (2 * (|k| + 1))) with hη
    have hη1 : η ≤ g0 / (2 * (|k| + 1)) := min_le_right _ _
    have hη2 : η * (2 * (|k| + 1)) ≤ g0 := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * (|k| + 1))).1 hη1; exact this
    have hηp : 0 < η := lt_min (by positivity) (by positivity)
    have key : (σ ^ 2 * b * Y * L + σ * (zf - zp) * (Y - η)) / L - σ * (zf - zr) * η / (Xr - L) = g0 - η * k := by
      rw [hg0, hk]; field_simp; ring
    have : 0 < g0 - η * k := by
      have := neg_abs_le k
      have := le_abs_self k
      nlinarith [mul_nonneg hηp.le (abs_nonneg k)]
    linarith
  have e4 := ev_lin3 (β := -L * (L + σ * b * (zx - zf)) + Y * (-Y + η)) (α := Y * (κ * (zx - zf)))
    (mul_pos hY hκx)
  have e8 := ev_lin3 (β := (Xr - L) * (L - Xr + σ * b * (zr - zf)) - Y * η)
    (α := -(Y * (κ * (zr - zf)))) (by nlinarith)
  obtain ⟨M, h4, h8⟩ := (e4.and e8).exists
  have f2 := ev_lin3 (β := σ * (zx - zp) * (-Y + η + M * κ * (zp - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zp - zf))) (mul_pos hzx hb1)
  have f3 := ev_lin3 (β := σ * (zx - zp) * (-Y + η + M * κ * (zx - zf)))
    (α := σ * (zx - zp) * (L + σ * b * (zx - zf))) (mul_pos hzx hb2)
  have fs := ev_lin3 (β := L) (α := Y) hY
  obtain ⟨s, h2, h3, hs, hEs⟩ := (f2.and (f3.and (fs.and hE))).exists
  obtain ⟨H, hHd⟩ : ∃ H, H = ((σ ^ 2 * b * Y * L + σ * (zf - zp) * (Y - η)) / L +
      σ * (zf - zr) * η / (Xr - L)) / 2 := ⟨_, rfl⟩
  -- gap relations (as products)
  obtain ⟨Gn, hGnd⟩ : ∃ Gn, Gn = (σ ^ 2 * b * Y * L + σ * (zf - zp) * (Y - η)) / L := ⟨_, rfl⟩
  obtain ⟨r0, hr0d⟩ : ∃ r0, r0 = σ * (zf - zr) * η / (Xr - L) := ⟨_, rfl⟩
  have hGn : Gn * L = σ ^ 2 * b * Y * L + σ * (zf - zp) * (Y - η) := by rw [hGnd]; field_simp
  have hr0 : r0 * (Xr - L) = σ * (zf - zr) * η := by rw [hr0d]; field_simp
  rw [← hGnd, ← hr0d] at hgap
  have hgapL : 0 < (Gn - r0) / 2 := by linarith
  refine sc5_core2 hF o E (S := s) (⟨-(σ * b), M * κ, -1, -Y + η - M * κ * zf, L - σ * b * zf⟩ : Mo)
    (⟨0, 0, 0, 0, σ * (σ * b * Y + M * κ * L) - (Gn + r0) / 2⟩ : Mo)
    hL hzx (by nlinarith [mul_pos hXL hY]) hY (by nlinarith [mul_pos hXL hY]) (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hEs
  all_goals simp only [Rw, L2, VX, VY]
  · left; linarith [mul_pos hL hb1]
  · right; refine ⟨by ring, ?_⟩
    linarith [h2]
  · right; refine ⟨by ring, ?_⟩
    linarith [h3]
  · left; linarith [h4]
  · left; linarith [mul_pos hY (sub_pos.2 hηY)]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hL hgapL, hGn]
  · left; linarith [hb3]
  · left; linarith [h8]
  · left; linarith [mul_pos hY hη0]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hXL hgapL, hr0, hGn]

end Type08Sp
end Minimality
