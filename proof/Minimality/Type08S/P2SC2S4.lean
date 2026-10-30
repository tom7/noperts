module

public import Minimality.Type08S.P2SC2S4a

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Corollary SC2-S, far-end coincidence `f̄ = r̄` (package G)

`Xr = L`, `zr = zf`.  Motion `Φ̃ = σ(σ0 + mX - z) + μ(X - L)` (the `μ`-term makes `g`'s top row strict), `M1 = (0,0,0,0,c¹)`.
`S = {F-row of f, top row of r}` (one common point `f̄ = r̄`), one dependency.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

noncomputable def moSr (σ m σ0 z0 κ ρ μ L s : ℝ) : Mo :=
  ⟨σ, ρ * s * κ, σ * m + μ, -(ρ * s * κ * z0), σ * σ0 - μ * L⟩

noncomputable def DSr (σ L zp Y m σ0 z0 κ ρ μ s : ℝ) : ℝ :=
  σ * κ * (ρ * s) * (σ0 - zp) * (z0 - (σ0 + m * L)) - L * σ ^ 2 * Y * (1 + m ^ 2) - L * σ * μ * m * Y

theorem sc2S_core_r (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx Xg Y m σ0 z0 κ ρ μ : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hY : 0 < Y) (hXg : Xg < L)
    (hPi : 0 < σ * (σ0 - zp)) (hρ : 0 < ρ) (hμ : 0 < μ) (hμ1 : μ * L < σ * (σ0 - zp))
    (hf : κ * ((σ0 + m * L) - z0) < 0)
    (hg : 0 < κ * ((σ0 + m * Xg) - z0)) (hx : 0 < κ * (zx - z0))
    (hR2 : μ * L < ρ * κ * (zp - z0) + σ * (σ0 - zp))
    (hR3 : μ * L < ρ * κ * (zx - z0) + σ * (σ0 - zx))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) L Y (σ0 + m * L) Xg Y (σ0 + m * Xg) E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) L Y (σ0 + m * L) Xg Y (σ0 + m * Xg) E) := by
  have hD : 0 < σ * κ * ρ * (σ0 - zp) * (z0 - (σ0 + m * L)) := by
    have : σ * κ * ρ * (σ0 - zp) * (z0 - (σ0 + m * L)) =
        ρ * (σ * (σ0 - zp)) * (-(κ * ((σ0 + m * L) - z0))) := by ring
    rw [this]; exact mul_pos (mul_pos hρ hPi) (by linarith)
  have e1' := ev_lin' (β := -(L * σ ^ 2 * Y * (1 + m ^ 2)) - L * σ * μ * m * Y) hD
  have e4 := ev_lin' (β := -Xg * (σ * (σ0 - zx) - μ * L)) (α := ρ * Y * (κ * (zx - z0))) (by positivity)
  have e5 := ev_lin' (β := 0) (α := -(Y * ρ * (κ * ((σ0 + m * L) - z0)))) (by nlinarith [mul_pos hY hρ])
  have e8 := ev_lin' (β := (σ * m + μ) * Y * Y) (α := -(Y * ρ * (κ * ((σ0 + m * L) - z0)))) (by nlinarith [mul_pos hY hρ])
  have e9 := ev_lin' (β := -Xg * (μ * (Xg - L)) - (σ * m + μ) * Y * Y)
    (α := Y * ρ * (κ * ((σ0 + m * Xg) - z0))) (by nlinarith [mul_pos hY hρ])
  have es := ev_lin' (β := Xg) (α := Y) hY
  obtain ⟨s, ⟨⟨hDs, h4, h5⟩, ⟨h8, h9, hs⟩⟩, hEs⟩ :=
    (((e1'.and (e4.and e5)).and (e8.and (e9.and es))).and hE).exists
  have hs0 : 0 < s := by
    have : 0 < Xg + s * Y := by linarith
    by_contra hneg; push_neg at hneg
    nlinarith [mul_nonneg (by linarith : 0 ≤ -s) hY.le, hXg, hL]
  have hDpos : 0 < DSr σ L zp Y m σ0 z0 κ ρ μ s := by unfold DSr; nlinarith [hDs]
  have hDdef : DSr σ L zp Y m σ0 z0 κ ρ μ s = σ * κ * (ρ * s) * (σ0 - zp) * (z0 - (σ0 + m * L)) -
      L * σ ^ 2 * Y * (1 + m ^ 2) - L * σ * μ * m * Y := rfl
  obtain ⟨η, hη⟩ : ∃ η, η = DSr σ L zp Y m σ0 z0 κ ρ μ s / (2 * L) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη2 : η * (2 * L) = DSr σ L zp Y m σ0 z0 κ ρ μ s := by rw [hη]; field_simp
  have hρs : 0 < ρ * s := mul_pos hρ hs0
  have hLX : 0 < L - Xg := sub_pos.2 hXg
  refine sc5_core2 hF o E (S := s) (moSr σ m σ0 z0 κ ρ μ L s)
    (⟨0, 0, 0, 0, -σ ^ 2 * Y * (1 + m ^ 2) - σ * μ * m * Y +
      σ * κ * (ρ * s) * (L * (1 + m ^ 2) + m * (σ0 - z0)) - η⟩ : Mo) hL hzx
    (by nlinarith [mul_pos hY hLX]) hY (by nlinarith [mul_pos hY hLX]) (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hEs
  all_goals simp only [Rw, L2, moSr, VX, VY]
  · left; linarith [mul_pos hL (sub_pos.2 hμ1)]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos (mul_pos hzx hs0) (sub_pos.2 hR2)]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos (mul_pos hzx hs0) (sub_pos.2 hR3)]
  · left; linarith [h4]
  · left; linarith [h5]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hη0 hL, hη2, hDdef]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hη0 hLX, hη2, hDdef]
  · left; linarith [h8]
  · left; linarith [h9]
  · left; linarith [mul_pos hμ (mul_pos hLX hLX)]

/-- **Corollary SC2-S, `f̄ = r̄`**, frame form (`r = (L, Y, σ0 + mL)`). -/
theorem lemmaSC2S_r (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx Xg Y m σ0 : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hY : 0 < Y)
    (hc : ClassS2r σ L zp zx Xg m σ0)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) L Y (σ0 + m * L) Xg Y (σ0 + m * Xg) E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) L Y (σ0 + m * L) Xg Y (σ0 + m * Xg) E) := by
  obtain ⟨z0, κ, ρ, hρ, hf, hg, hx, hR2, hR3⟩ := sc2S_params_r hL hzx hc
  obtain ⟨hXg, hPi, -⟩ := hc
  have hmin : 0 < min (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx))) := lt_min hPi (lt_min hR2 hR3)
  set μ := min (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx))) / (2 * L) with hμ
  have hμL : μ * L = min (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx))) / 2 := by rw [hμ]; field_simp
  have a1 := min_le_left (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx)))
  have a2 := (min_le_right (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx)))).trans (min_le_left _ _)
  have a3 := (min_le_right (σ * (σ0 - zp)) (min (ρ * κ * (zp - z0) + σ * (σ0 - zp))
      (ρ * κ * (zx - z0) + σ * (σ0 - zx)))).trans (min_le_right _ _)
  exact sc2S_core_r hF o E hL hzx hY hXg hPi hρ (show 0 < μ by rw [hμ]; exact div_pos hmin (by positivity)) (by linarith) hf hg hx
    (by linarith) (by linarith) hE

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSC2S_r
