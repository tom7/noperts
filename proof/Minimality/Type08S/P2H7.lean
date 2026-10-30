module

public import Minimality.Type08S.P2H6

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H7: P-K at the frame level — a robust rim of the closing with a persistent HDN

`pers_frame`: the rim (any `RimCertAt` rim `Pt ∘ σ` of the labelled quadrilateral `Pt = Qg ∘ μ`, `μ` an involution),
robust, with a persistent HDN along the face circle (`¬ NoPersistHDN … (L e1)`), plus the TriCerts of the extra
vertices `E` (tilt `(κ s, -κ, 0)`) and Lemma E (`LemEF`, only used for a top side) give: Rupert (class (c): SC-c;
class (d): SC-d, either orientation; chord end at `x`: SC-X), or the SC2 cases (chord end at `f`, parallel set),
returned with the robust order data for the caller's SC2 hypothesis.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 1000000 in
theorem pers_frame (hF : Fr e1 e2 e3) (O : ℝ³) (E : Finset ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y)
    (hLem : Yr = Yg → LemEF 0 L κ zf Xr zr Xg zg)
    (Pt : ZMod 4 → ℝ³) (μ : ZMod 4 → ZMod 4) (hμ : ∀ a, μ (μ a) = a)
    (hP : ∀ j, Pt j = Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (μ j))
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = L • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (Pt (σ (i + 1)) - Pt (σ i))
      (Pt (σ j) - Pt (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3 (Pt (σ (i + 1)) - Pt (σ i)) (Pt a - Pt (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪Pt (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => Pt (σ i)) u e) :
    IsRupert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E) ∨
      (Rob4 κ zf zr zg ∧ (CEf5 L κ zf Xr Yr zr Xg Yg zg ∨ Par5 L κ zf Xr Yr zr Xg Yg zg)) := by
  subst hu he
  obtain ⟨hrob', hp'⟩ := canon_of_rim hF O hκv hL hYr hYg hcr hcg hk3 (fun i => μ (σ i))
    (fun i j hi hj => by simpa only [hP] using hcyc i j hi hj)
    (fun i a => by have := hleft i (μ a); simpa only [hP, hμ] using this)
    (by simpa only [hP] using hz) (by simpa only [hP] using hp)
  have hrob := rob4_canon hF O hκv hrob'
  have hpf := persF_of_hdn hF O hYr hYg hκv hL.ne' hp'
  have hzx : 0 < κ * (κ - 0) := by rw [sub_zero]; exact mul_self_pos.mpr hκ
  rcases classify_pers hL hYr hYg hcg hrob hpf with hc | ⟨hd, hnc⟩ | ⟨hx, hnc⟩ | hf | hpar
  · exact Or.inl (lemmaSC8 hF O E hL hzx hcr hYr hYg hcg (Or.inl hc) hE)
  · left
    have hY := hd.1
    have hXrg : Xg < Xr := by rw [hY] at hcg; nlinarith
    have hLE := hLem hY
    have hcert : SCcert 0 L κ zf Xr zr Xg zg := by
      rcases lt_or_gt_of_ne hκ with hn | hpos
      · exact cert_neg (by
          have := certD_of hL (classD5_neg (zp := 0) hL (by linarith) hXrg hd hnc hrob hLE)
          simpa using this)
      · exact certD_of hL (classD5_of hL hpos hXrg hd hnc hrob hLE)
    exact lemmaSC8 hF O E hL hzx hcr hYr hYg hcg (Or.inr (Or.inl ⟨hY.symm, hXrg, hcert⟩)) hE
  · exact Or.inl (lemmaSC8 hF O E hL hzx hcr hYr hYg hcg
      (Or.inr (Or.inr (classX5_of hzx hYr hcg hx hnc hLem))) hE)
  · exact Or.inr ⟨hrob, Or.inl hf⟩
  · exact Or.inr ⟨hrob, Or.inr hpar⟩

end Type08Sp
end Minimality
