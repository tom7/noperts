module

public import Minimality.Type08S.SCg

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Lemma SC (decoupled split corner), top side `rg` (`Yr = Yg`, class (d))**, five-corner rim
`(x', f, r, g, x)`; `Φ(X,z) = φ0 + φ1 z + θ X`, `χ(z) = χ0 + χ1 z`. -/
theorem lemmaSC_s (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg φ0 φ1 θ χ0 χ1 : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hYr : 0 < Yr) (hYrg : Yg = Yr) (hXrg : Xg < Xr)
    -- (R1)
    (hχf : χ0 + χ1 * zf < 0) (hχr : χ0 + χ1 * zr < 0) (hχg : 0 < χ0 + χ1 * zg)
    (hχx : 0 < χ0 + χ1 * zx)
    -- (R2)
    (hΦp : 0 < φ0 + φ1 * zp + θ * 0) (hΦf : 0 < φ0 + φ1 * zf + θ * L)
    (hΦr : φ0 + φ1 * zr + θ * Xr < 0) (hΦg : φ0 + φ1 * zg + θ * Xg < 0)
    -- (R3)
    (hR3x : 0 ≤ (χ0 + χ1 * zx) + (φ0 + φ1 * zx + θ * 0))
    (hR3p : 0 ≤ (χ0 + χ1 * zp) + (φ0 + φ1 * zp + θ * 0))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  subst hYrg
  have hcr : 0 < (Xg - Xr) * (-Yg) - (Yg - Yg) * (L - Xr) := by nlinarith
  have hcg : 0 < Yg * Xr - Xg * Yg := by nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 0 := ⟨0, rfl⟩
  -- the motion (no top vertex: `c = 0`)
  have hcond : ∀ a b : ℝ, 0 ≤ a → 0 < b → 0 < a ∨ (a = 0 ∧ 0 < b) := fun a b ha hb => by
    rcases ha.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, hb⟩
  have e0 := ev_of_eq (P := fun s => Xg + s * Yg) Yg Xg 0 (Or.inl hYr) (fun s hs => by ring)
  have e1 := ev_of_eq (P := fun s => VY (-φ1) θ (φ0 - c / s) 0 zp) 0 (φ0 + φ1 * zp + θ * 0) (-c)
    (Or.inr ⟨rfl, hΦp⟩) (fun s hs => by simp only [VY]; field_simp; ring)
  have e2 := ev_of_eq (P := fun s => σ * (zx - zp) * (s * VY (-φ1) θ (φ0 - c / s) 0 zp +
      VX (s * χ1) θ (s * χ0 + c + 1) 0 zp))
    (σ * (zx - zp) * ((χ0 + χ1 * zp) + (φ0 + φ1 * zp + θ * 0))) (σ * (zx - zp)) 0
    (hcond _ _ (mul_nonneg hzx.le hR3p) hzx) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e3 := ev_of_eq (P := fun s => σ * (zx - zp) * (s * VY (-φ1) θ (φ0 - c / s) 0 zx +
      VX (s * χ1) θ (s * χ0 + c + 1) 0 zx))
    (σ * (zx - zp) * ((χ0 + χ1 * zx) + (φ0 + φ1 * zx + θ * 0))) (σ * (zx - zp)) 0
    (hcond _ _ (mul_nonneg hzx.le hR3x) hzx) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e4 := ev_of_eq (P := fun s => -Xg * VY (-φ1) θ (φ0 - c / s) 0 zx +
      Yg * VX (s * χ1) θ (s * χ0 + c + 1) 0 zx)
    (Yg * (χ0 + χ1 * zx)) (-Xg * (φ0 + φ1 * zx + θ * 0) + Yg * (c + 1)) (Xg * c)
    (Or.inl (mul_pos hYr hχx)) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e5 := ev_of_eq (P := fun s => (Xr - L) * VY (-φ1) θ (φ0 - c / s) L zf -
      Yg * VX (s * χ1) θ (s * χ0 + c + 1) 0 zf)
    (-Yg * (χ0 + χ1 * zf)) ((Xr - L) * (φ0 + φ1 * zf + θ * L) - Yg * (c + 1)) (-(Xr - L) * c)
    (Or.inl (by nlinarith)) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e6 := ev_of_eq (P := fun s => VY (-φ1) θ (φ0 - c / s) L zf) 0 (φ0 + φ1 * zf + θ * L) (-c)
    (Or.inr ⟨rfl, hΦf⟩) (fun s hs => by simp only [VY]; field_simp; ring)
  have e7 := ev_of_eq (P := fun s => (Xg - Xr) * VY (-φ1) θ (φ0 - c / s) Xr zr -
      (Yg - Yg) * VX (s * χ1) θ (s * χ0 + c + 1) Yg zr)
    (-(Yg - Yg) * (χ0 + χ1 * zr)) ((Xg - Xr) * (φ0 + φ1 * zr + θ * Xr)) (-(Xg - Xr) * c)
    (Or.inr ⟨by ring, by nlinarith⟩) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e8 := ev_of_eq (P := fun s => (Xr - L) * VY (-φ1) θ (φ0 - c / s) Xr zr -
      Yg * VX (s * χ1) θ (s * χ0 + c + 1) Yg zr)
    (-Yg * (χ0 + χ1 * zr)) ((Xr - L) * (φ0 + φ1 * zr + θ * Xr) - Yg * (c + 1 - θ * Yg)) (-(Xr - L) * c)
    (Or.inl (by nlinarith)) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e9 := ev_of_eq (P := fun s => -Xg * VY (-φ1) θ (φ0 - c / s) Xg zg +
      Yg * VX (s * χ1) θ (s * χ0 + c + 1) Yg zg)
    (Yg * (χ0 + χ1 * zg)) (-Xg * (φ0 + φ1 * zg + θ * Xg) + Yg * (c + 1 - θ * Yg)) (Xg * c)
    (Or.inl (mul_pos hYr hχg)) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  have e10 := ev_of_eq (P := fun s => (Xg - Xr) * VY (-φ1) θ (φ0 - c / s) Xg zg -
      (Yg - Yg) * VX (s * χ1) θ (s * χ0 + c + 1) Yg zg)
    (-(Yg - Yg) * (χ0 + χ1 * zg)) ((Xg - Xr) * (φ0 + φ1 * zg + θ * Xg)) (-(Xg - Xr) * c)
    (Or.inr ⟨by ring, by nlinarith⟩) (fun s hs => by simp only [VY, VX]; field_simp; ring)
  obtain ⟨s, hs, hEs⟩ := (((e0.and e1).and (e2.and e3)).and ((e4.and e5).and (e6.and e7)) |>.and
    ((e8.and e9).and e10) |>.and hE).exists
  obtain ⟨⟨⟨⟨h0, h1⟩, h2, h3⟩, ⟨h4, h5⟩, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hs
  exact sc5_core hF o E (σ := σ) (s := s) hL hzx hcr hYr hcg h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hEs

end Type08Sp
end Minimality
