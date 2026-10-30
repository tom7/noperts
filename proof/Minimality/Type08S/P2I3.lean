module

public import Minimality.Type08S.P2I2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 9: `close_np_frame` — the rim given through the labelled points `Pt = pts ∘ lab`
(`Pt j = Qg (μ j)`, `μ` an involution: the identity or `j ↦ -j`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem close_np_frame_g (hF : Fr e1 e2 e3) (O w : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg Xp zp : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hpx : fpt e1 e2 e3 O Xp 0 zp ≠ fpt e1 e2 e3 O 0 0 κ) (hpf : fpt e1 e2 e3 O Xp 0 zp ≠ fpt e1 e2 e3 O L 0 zf)
    (hpm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O Xp 0 zp = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • ((κ * κv) • e1)))
    (hw : ∀ i : ZMod 4, SlideTest κv
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (w - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i) (κv • e3) ((κ * κv) • e1))
    (Pt : ZMod 4 → ℝ³) (μ : ZMod 4 → ZMod 4) (hμ : ∀ a, μ (μ a) = a)
    (hP : ∀ j, Pt j = Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (μ j))
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = L • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (Pt (σ (i + 1)) - Pt (σ i))
      (Pt (σ j) - Pt (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3 (Pt (σ (i + 1)) - Pt (σ i)) (Pt a - Pt (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪Pt (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => Pt (σ i)) u e) :
    IsRupert ({O, fpt e1 e2 e3 O 0 0 κ, fpt e1 e2 e3 O L 0 zf, fpt e1 e2 e3 O Xr Yr zr,
      fpt e1 e2 e3 O Xg Yg zg, fpt e1 e2 e3 O Xp 0 zp, w} : Finset ℝ³) := by
  subst hu he
  refine close_core_g hF O w hκ hκv hL hYr hYg hcr hcg hpx hpf hpm hw hk3 (fun i => μ (σ i)) ?_ ?_ ?_ ?_
  · intro i j hi hj
    have := hcyc i j hi hj
    simpa only [hP] using this
  · intro i a
    have := hleft i (μ a)
    simpa only [hP, hμ] using this
  · simpa only [hP] using hz
  · simpa only [hP] using hbad

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_np_frame_g
