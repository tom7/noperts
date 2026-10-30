module

public import Minimality.Type08S.P2SC2core

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-S core (package G): parameter form of Corollary SC2-S, `f̄` strictly inside the top side `(ḡ, r̄)`

Frame data `x' = (0,0,zp)`, `x = (0,0,zx)`, `f = (L,0,zf)`, top side `Yr = Yg = Y`, the line `z = σ0 + m X` through
`r̄ = (Xr, zr)`, `ḡ = (Xg, zg)` and `f̄ = (L, zf)`, `Xg < L < Xr`.  Motion `M0`: `Φ̃ = σ(σ0 + m X - z)`,
`γ(z) = M κ (z - z0)`, `M = ρ s`, tilt `d = σ(s e1 - e2)`; `M1` changes only `Φ̃` (`θ¹ X + c¹`, explicit).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem ev_lin' {α β : ℝ} (hα : 0 < α) : ∀ᶠ s : ℝ in atTop, 0 < α * s + β := by
  filter_upwards [eventually_gt_atTop (|β| / α)] with M hM
  have := (div_lt_iff₀ hα).1 hM
  nlinarith [neg_abs_le β]

/-- The explicit motions of SC2-S. -/
noncomputable def moS (σ m σ0 z0 κ ρ s : ℝ) : Mo := ⟨σ, ρ * s * κ, σ * m, -(ρ * s * κ * z0), σ * σ0⟩

noncomputable def DS (σ L zp Y m σ0 z0 κ ρ s : ℝ) : ℝ :=
  σ * κ * (ρ * s) * (σ0 - zp) * (z0 - (σ0 + m * L)) - L * σ ^ 2 * Y * (1 + m ^ 2)

noncomputable def mo1S (σ L zp Y m σ0 z0 κ ρ s : ℝ) : Mo :=
  ⟨0, 0, σ * κ * (ρ * s) * (1 + m ^ 2),
    0, -σ ^ 2 * Y * (1 + m ^ 2) + σ * κ * (ρ * s) * m * (σ0 - z0) - DS σ L zp Y m σ0 z0 κ ρ s / (2 * L)⟩

theorem sc2S_core (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx Xr Xg Y m σ0 z0 κ ρ : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hY : 0 < Y) (hXg : Xg < L) (hXr : L < Xr)
    (hPi : 0 < σ * (σ0 - zp)) (hρ : 0 < ρ)
    (hf : κ * ((σ0 + m * L) - z0) < 0) (hr : κ * ((σ0 + m * Xr) - z0) < 0)
    (hg : 0 < κ * ((σ0 + m * Xg) - z0)) (hx : 0 < κ * (zx - z0))
    (hR2 : 0 < ρ * κ * (zp - z0) + σ * (σ0 - zp)) (hR3 : 0 < ρ * κ * (zx - z0) + σ * (σ0 - zx))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert
      (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) Xr Y (σ0 + m * Xr) Xg Y (σ0 + m * Xg) E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx (σ0 + m * L) Xr Y (σ0 + m * Xr) Xg Y (σ0 + m * Xg) E) := by
  have hD : 0 < σ * κ * ρ * (σ0 - zp) * (z0 - (σ0 + m * L)) := by
    have : σ * κ * ρ * (σ0 - zp) * (z0 - (σ0 + m * L)) =
        ρ * (σ * (σ0 - zp)) * (-(κ * ((σ0 + m * L) - z0))) := by ring
    rw [this]; exact mul_pos (mul_pos hρ hPi) (by linarith)
  have e1' := ev_lin' (β := -(L * σ ^ 2 * Y * (1 + m ^ 2))) hD
  have e4 := ev_lin' (β := -Xg * (σ * (σ0 - zx))) (α := ρ * Y * (κ * (zx - z0))) (by positivity)
  have e5 := ev_lin' (β := 0) (α := -(Y * ρ * (κ * ((σ0 + m * L) - z0)))) (by nlinarith [mul_pos hY hρ])
  have e8 := ev_lin' (β := σ * m * Y * Y) (α := -(Y * ρ * (κ * ((σ0 + m * Xr) - z0)))) (by nlinarith [mul_pos hY hρ])
  have e9 := ev_lin' (β := -(σ * m * Y * Y)) (α := Y * ρ * (κ * ((σ0 + m * Xg) - z0))) (by nlinarith [mul_pos hY hρ])
  have es := ev_lin' (β := Xg) (α := Y) hY
  obtain ⟨s, ⟨⟨hDs, h4, h5⟩, ⟨h8, h9, hs⟩⟩, hEs⟩ :=
    (((e1'.and (e4.and e5)).and (e8.and (e9.and es))).and hE).exists
  have hs0 : 0 < s := by
    have : 0 < Xg + s * Y := by linarith
    by_contra hneg; push_neg at hneg
    nlinarith [mul_nonneg (by linarith : 0 ≤ -s) hY.le, hXg, hL]
  have hDpos : 0 < DS σ L zp Y m σ0 z0 κ ρ s := by unfold DS; nlinarith [hDs]
  have hDdef : DS σ L zp Y m σ0 z0 κ ρ s = σ * κ * (ρ * s) * (σ0 - zp) * (z0 - (σ0 + m * L)) -
      L * σ ^ 2 * Y * (1 + m ^ 2) := rfl
  obtain ⟨η, hη⟩ : ∃ η, η = DS σ L zp Y m σ0 z0 κ ρ s / (2 * L) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη2 : η * (2 * L) = DS σ L zp Y m σ0 z0 κ ρ s := by rw [hη]; field_simp
  have hmo : mo1S σ L zp Y m σ0 z0 κ ρ s = ⟨0, 0, σ * κ * (ρ * s) * (1 + m ^ 2),
    0, -σ ^ 2 * Y * (1 + m ^ 2) + σ * κ * (ρ * s) * m * (σ0 - z0) - η⟩ := by
    rw [mo1S, hη]
  have hρs : 0 < ρ * s := mul_pos hρ hs0
  refine sc5_core2 hF o E (S := s) (moS σ m σ0 z0 κ ρ s) (mo1S σ L zp Y m σ0 z0 κ ρ s) hL hzx
    (by nlinarith [mul_pos hY (sub_pos.2 hXg), mul_pos hY (sub_pos.2 hXr)]) hY
    (by nlinarith [mul_pos hY (sub_pos.2 hXg), mul_pos hY (sub_pos.2 hXr)]) (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hEs
  all_goals simp only [Rw, L2, moS, hmo, VX, VY]
  · left; linarith [mul_pos hL hPi]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos (mul_pos hzx hs0) hR2]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos (mul_pos hzx hs0) hR3]
  · left; linarith [h4]
  · left; linarith [h5]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hη0 hL, hη2, hDdef]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hη0 (sub_pos.2 (hXg.trans hXr)), hη2, hDdef]
  · left; linarith [h8]
  · left; linarith [h9]
  · right; refine ⟨by ring, ?_⟩
    linarith [mul_pos hη0 (sub_pos.2 (hXg.trans hXr)), hη2, hDdef]

end Type08Sp
end Minimality
