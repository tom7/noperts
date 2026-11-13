module

public import Minimality.SlideRim
public import Minimality.CaseC18Reduce

@[expose] public section

/-!
# Type 18: `V`'s rim slid along `F1`'s circle 
(`FEWER-FACES-PROOFS.md` Theorem 27.41, Steps 1-3; stage M5 of `lean2741/PLAN.md`)

Plan.  `CaseC18Special` excludes "`V` (resp. `V^Z`) has a horizontal double normal at its view
`uV`".  Instead of excluding that, slide the view of `V` along the circle of `F1`
(`uV + η e1`, `e1 = m1- - m1+`, `η → 0⁺`).  At `uV` all the strict tests of `vN4_rupert` /
`vNt_rupert` hold, so they hold at the slid views, and the rim stays robustly unimodal
(`Q4_ev_strict`, `robust_quad_of_nws`; for the triangle, unless the three depths are equal).
What remains is the horizontal double normals of the rim at the slid views: by
`eventually_noHDNRim_slide` (M3, `SlideRim.lean`) there are none for small `η` as soon as no
double normal of the rim in space is perpendicular to `uV` and `e1` (`NoPersistHDN`).  Lemma 27.38
(a) with Lemma 27.36, 27.40 classifies those persistent pairs: they are the class `H_F1`, the
perpendicular from `xb` to the line of `F1`'s side (foot in the open chord), and that happens
exactly on one hyperplane of the metric,
`A12 (h+ + h-) = A11 (t+ h- + t- h+)` (`Frame18.ClassH`).
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09 Minimality.CaseC20
open scoped RealInnerProductSpace Topology

namespace Shape18
variable (S : Shape18)

/-- The slide direction `m1- - m1+` of `F1`'s circle, in frame coordinates (`y = 0`).  The sign
is irrelevant for `NoPersistHDN` (it only uses `⟪·, e⟫ = 0`). -/
def eF1 : C3 := ⟨S.tm - S.tp, 0, -S.hm - S.hp⟩

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-! ### (i) The persistent-pair classification -/

end Frame18

/-! ### Slide tests -/

theorem mid_slide_gen (px pz qx qz mx mz ux uz ex ez : ℝ)
    (hD : (qx - px) * uz - (qz - pz) * ux ≠ 0)
    (h : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ mx = px + s * (qx - px) + δ * ux ∧
      mz = pz + s * (qz - pz) + δ * uz) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      mx = px + s * (qx - px) + δ * (ux + η * ex) ∧ mz = pz + s * (qz - pz) + δ * (uz + η * ez) := by
  obtain ⟨s0, δ0, hs0, hs1, hδ0, hx, hz⟩ := h
  set D : ℝ → ℝ := fun η => (qx - px) * (uz + η * ez) - (qz - pz) * (ux + η * ex) with hDdef
  set Sn : ℝ → ℝ := fun η => (mx - px) * (uz + η * ez) - (mz - pz) * (ux + η * ex) with hSdef
  set Dn : ℝ := (qx - px) * (mz - pz) - (qz - pz) * (mx - px) with hDn
  have hcD : Continuous D := by simp only [hDdef]; fun_prop
  have hcS : Continuous Sn := by simp only [hSdef]; fun_prop
  have hD0 : D 0 ≠ 0 := by simpa [hDdef] using hD
  have hS0 : Sn 0 / D 0 = s0 := by
    rw [div_eq_iff hD0]
    simp only [hSdef, hDdef, zero_mul, add_zero]
    rw [hx, hz]; ring
  have hδ0' : Dn / D 0 = δ0 := by
    rw [div_eq_iff hD0]
    simp only [hDdef, hDn, zero_mul, add_zero]
    rw [hx, hz]; ring
  have c1 : ContinuousAt (fun η => Sn η / D η) 0 := hcS.continuousAt.div hcD.continuousAt hD0
  have c2 : ContinuousAt (fun η => Dn / D η) 0 := continuousAt_const.div hcD.continuousAt hD0
  have e1 := c1.eventually_mem (Ioo_mem_nhds (a := (0:ℝ)) (b := 1) (by rw [hS0]; exact hs0)
    (by rw [hS0]; exact hs1))
  have e2 := c2.eventually_ne (by rw [hδ0']; exact hδ0)
  have e3 := hcD.continuousAt.eventually_ne hD0
  filter_upwards [(e1.and (e2.and e3)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))]
    with η ⟨hη1, hη2, hη3⟩
  refine ⟨Sn η / D η, Dn / D η, hη1.1, hη1.2, hη2, ?_, ?_⟩
  · field_simp
    simp only [hSdef, hDdef, hDn]; ring
  · field_simp
    simp only [hSdef, hDdef, hDn]; ring

namespace Shape18
variable (S : Shape18)

/-- `m2+ = sp xb + (1 - sp) m1+ - uV` (it lies in the plane of the face `014`, edge-on at `uV`). -/
theorem Dc_m2p (a P : C3) :
    Dc a ((⟨0, S.sp, S.kp⟩ : C3).sub P) S.uV =
      S.sp * Dc a ((⟨0, 1, 0⟩ : C3).sub P) S.uV +
        (1 - S.sp) * Dc a ((⟨S.tp, 0, S.hp⟩ : C3).sub P) S.uV := by
  simp only [Dc, C3.sub, uV]; ring

theorem Dc_self (a w : C3) : Dc a a w = 0 := by simp only [Dc]; ring
theorem Dc_zero_right (a w : C3) (P : C3) : Dc a (P.sub P) w = 0 := by
  simp only [Dc, C3.sub]; ring

/-- The tangent test of `m2+` along the slide: it is exactly `η (Vp + k+ t+)`. -/
theorem tang_slide (η : ℝ) :
    PS 1 (C3.slide S.uV S.eF1 η) ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩)
        ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩) ↔ 0 < η * (S.Vp + S.kp * S.tp) := by
  have : Dc ((⟨S.tp, 0, S.hp⟩ : C3).sub ⟨0, 1, 0⟩) ((⟨0, S.sp, S.kp⟩ : C3).sub ⟨0, 1, 0⟩)
      (C3.slide S.uV S.eF1 η) = η * (S.Vp + S.kp * S.tp) := by
    simp only [Dc, C3.sub, C3.slide, uV, eF1, Vp]; ring
  unfold PS
  rw [this, one_mul]

theorem uD_ne (hV : 0 < S.Vp) :
    (S.tm - S.tp) * S.uV.z - (-S.hm - S.hp) * S.uV.x ≠ 0 := by
  have : (S.tm - S.tp) * S.uV.z - (-S.hm - S.hp) * S.uV.x = S.Vp + S.kp * S.tp := by
    simp only [uV, Vp]; ring
  rw [this]
  have := mul_pos S.kp_pos S.tp_pos
  linarith

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-! ### (ii) The slide Rupert theorems: one hyperplane instead of the HDN items -/

end Frame18

/-!
## Proof summary

* `persist_gen` (the classification, 27.35-27.38 (a), 27.40): a persistent extremal pair `Y' - Y` is
  perpendicular to `uV` and `e1`, hence (the determinant is `Vp + k+ t+ > 0`) to `u1` and `e`
  (`persist_perp`); then `⟪Y'-Y, ·⟫ = ν y` on the rim corners (`persist_vals`), with `ν ≠ 0`
  (`persist_nu_ne`).  Extremality forces `Y' = xb` (the only corner with `y = 1`) and `Y` on the
  chord `[m1+, m1-]` (`y = 0`), and the perpendicularity to `e` is `ClassH`.  So the corner `m2-` and the
  level edge of 27.40 never occur (they have `y < 1`).
* The slide: the strict tests of `vN4_cyc` / `vNt_cyc` persist (`PS_ev`); `m2+` lies in the plane of the
  face `014` edge-on at `uV` (`Dc_m2p`), so its tests against the three other sides are strict and
  the test against `[xb, m1+]` equals `η (Vp + k+ t+)` along `+eF1` (`tang_slide`); the middles
  `v`, `xa` stay over the chord (`mid_slide_gen`); the depths stay robustly unimodal
  (`Q4_ev_strict`) or the triangle is not level (a level triangle has an HDN, excluded by `NoHDNRim`).
-/

end Minimality.CaseC18

end
