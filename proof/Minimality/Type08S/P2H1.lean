module

public import Minimality.Type08S.P2H2
public import Minimality.Type08S.P2CR8

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H1: a persistent HDN of the closing's 4-cycle, in frame numbers (29.5 for 4-corner rims)

Frame of pkB (`Qg`): `x = (0,0,κ)`, `f = (L,0,zf)`, `r = (Xr,Yr,zr)`, `g = (Xg,Yg,zg)` about `O = x'`, view `κv e3`,
circle direction `e1`.  `PersF`: the low point of the HDN is `x̄ + s (f̄ - x̄)` on the chord (`Y = 0`), the high
point is `r + s' (g - r)` on the top (`s' = 0` / `1` if the top is the vertex `r` / `g`), with equal `(X, z)`.

* `persF_of_hdn`: `¬ NoPersistHDN Qg (κv e3) (c e1)` ⇒ `PersF`.
* `canon_of_rim`: an arbitrary `RimCertAt` rim `Qg ∘ τ` (rotation / reflection, pkB CR6) passes robustness and the
  persistent HDN to the canonical `Qg`; `rob4_canon`: robustness of `Qg`'s depths is `Rob4 κ zf zr zg`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The persistent HDN of the closing `(x, f, r, g)` in frame numbers (`zx` = depth of `x`). -/
def PersF (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ∃ s s' : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ s' ∧ s' ≤ 1 ∧
    (Yr = Yg ∨ (s' = 0 ∧ Yg < Yr) ∨ (s' = 1 ∧ Yr < Yg)) ∧
    s * L = Xr + s' * (Xg - Xr) ∧ zx + s * (zf - zx) = zr + s' * (zg - zr)

/-- A point of an edge of `Qg` as a convex combination of the four corners. -/
theorem seg_Qg (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ} (i : ZMod 4) {Y : ℝ³}
    (hY : Y ∈ segment ℝ (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i)
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (i + 1))) :
    ∃ l0 l1 l2 l3 : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ l0 + l1 + l2 + l3 = 1 ∧
      Y = fpt e1 e2 e3 O (l1 * L + l2 * Xr + l3 * Xg) (l2 * Yr + l3 * Yg)
        (l0 * κ + l1 * zf + l2 * zr + l3 * zg) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hY
  obtain rfl : a = 1 - b := by linarith
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · refine ⟨1 - b, b, 0, 0, ha, hb, le_refl _, le_refl _, by ring, ?_⟩
    show (1 - b) • fpt e1 e2 e3 O 0 0 κ + b • fpt e1 e2 e3 O L 0 zf = _
    simp only [fpt, pc]; module
  · refine ⟨0, 1 - b, b, 0, le_refl _, ha, hb, le_refl _, by ring, ?_⟩
    show (1 - b) • fpt e1 e2 e3 O L 0 zf + b • fpt e1 e2 e3 O Xr Yr zr = _
    simp only [fpt, pc]; module
  · refine ⟨0, 0, 1 - b, b, le_refl _, le_refl _, ha, hb, by ring, ?_⟩
    show (1 - b) • fpt e1 e2 e3 O Xr Yr zr + b • fpt e1 e2 e3 O Xg Yg zg = _
    simp only [fpt, pc]; module
  · refine ⟨b, 0, 0, 1 - b, hb, le_refl _, le_refl _, ha, by ring, ?_⟩
    show (1 - b) • fpt e1 e2 e3 O Xg Yg zg + b • fpt e1 e2 e3 O 0 0 κ = _
    simp only [fpt, pc]; module

/-- The real core: the low point has `Y = 0`, the high point is on the top. -/
theorem persF_core {κ L zf Xr Yr zr Xg Yg zg : ℝ} (hYr : 0 < Yr) (hYg : 0 < Yg)
    {l0 l1 l2 l3 m0 m1 m2 m3 : ℝ} (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3)
    (hl : l0 + l1 + l2 + l3 = 1) (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hm3 : 0 ≤ m3)
    (hm : m0 + m1 + m2 + m3 = 1)
    (hX : l1 * L + l2 * Xr + l3 * Xg = m1 * L + m2 * Xr + m3 * Xg)
    (hz : l0 * κ + l1 * zf + l2 * zr + l3 * zg = m0 * κ + m1 * zf + m2 * zr + m3 * zg)
    (hlow : l2 * Yr + l3 * Yg ≤ 0)
    (hr : Yr ≤ m2 * Yr + m3 * Yg) (hg : Yg ≤ m2 * Yr + m3 * Yg) :
    PersF L κ zf Xr Yr zr Xg Yg zg := by
  have e2 : l2 = 0 := le_antisymm (by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hc hYr, mul_nonneg hl3 hYg.le]) hl2
  have e3 : l3 = 0 := le_antisymm (by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hc hYg, mul_nonneg hl2 hYr.le]) hl3
  subst e2 e3
  have hm01 : m0 + m1 = 0 := by
    rcases le_total Yg Yr with h | h
    · refine le_antisymm ?_ (add_nonneg hm0 hm1)
      by_contra hc; push_neg at hc
      nlinarith [mul_nonneg hm3 (sub_nonneg.2 h), mul_pos hc hYr]
    · refine le_antisymm ?_ (add_nonneg hm0 hm1)
      by_contra hc; push_neg at hc
      nlinarith [mul_nonneg hm2 (sub_nonneg.2 h), mul_pos hc hYg]
  have f0 : m0 = 0 := by linarith
  have f1 : m1 = 0 := by linarith
  subst f0 f1
  refine ⟨l1, m3, hl1, by linarith, hm3, by linarith, ?_, ?_, ?_⟩
  · rcases lt_trichotomy Yr Yg with h | h | h
    · right; right; refine ⟨?_, h⟩
      have : m2 = 0 := le_antisymm (by
        by_contra hc; push_neg at hc; nlinarith [mul_pos hc (sub_pos.2 h)]) hm2
      linarith
    · left; exact h
    · right; left; refine ⟨?_, h⟩
      exact le_antisymm (by
        by_contra hc; push_neg at hc; nlinarith [mul_pos hc (sub_pos.2 h)]) hm3
  · have : m2 = 1 - m3 := by linarith
    subst this; linarith
  · have : m2 = 1 - m3 := by linarith
    have : l0 = 1 - l1 := by linarith
    subst_vars; linarith

theorem inner_fpt_e (hF : Fr e1 e2 e3) (O : ℝ³) (X Y z X' Y' z' X'' Y'' z'' : ℝ) :
    ⟪fpt e1 e2 e3 O X Y z - fpt e1 e2 e3 O X' Y' z', fpt e1 e2 e3 O X'' Y'' z'' - fpt e1 e2 e3 O X Y z⟫ =
      (X - X') * (X'' - X) + (Y - Y') * (Y'' - Y) + (z - z') * (z'' - z) := by
  rw [fpt_sub, fpt_sub, inner_pc hF]

theorem low_of {A B : ℝ} (hlt : A < B) (h : (A - B) * (0 - A) ≤ 0) : A ≤ 0 := by
  by_contra hc; push_neg at hc; nlinarith [mul_pos (sub_pos.2 hlt) hc]

theorem high_of {A B Ym : ℝ} (hlt : A < B) (h : (B - A) * (Ym - B) ≤ 0) : Ym ≤ B := by
  by_contra hc; push_neg at hc; nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]

/-- **Lemma A (29.5 for the 4-cycle).**  A persistent HDN of `Qg` along the circle `(κv e3, c e1)` is `PersF`. -/
theorem persF_of_hdn (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg κv c : ℝ}
    (hYr : 0 < Yr) (hYg : 0 < Yg) (hκv : κv ≠ 0) (hc : c ≠ 0)
    (h : ¬ NoPersistHDN (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg) (κv • e3) (c • e1)) :
    PersF L κ zf Xr Yr zr Xg Yg zg := by
  unfold NoPersistHDN at h
  push_neg at h
  obtain ⟨i, j, Y, hY, Y', hY', hne, hu, he, hall⟩ := h
  obtain ⟨l0, l1, l2, l3, hl0, hl1, hl2, hl3, hl, rfl⟩ := seg_Qg O i hY
  obtain ⟨m0, m1, m2, m3, hm0, hm1, hm2, hm3, hm, rfl⟩ := seg_Qg O j hY'
  rw [fpt_sub] at hu he
  rw [pc_smul_e3 hF, inner_pc hF] at hu
  rw [pc_smul_e1, inner_pc hF] at he
  have hz : m0 * κ + m1 * zf + m2 * zr + m3 * zg = l0 * κ + l1 * zf + l2 * zr + l3 * zg := by
    have : κv * ((m0 * κ + m1 * zf + m2 * zr + m3 * zg) - (l0 * κ + l1 * zf + l2 * zr + l3 * zg)) = 0 := by
      linarith
    have := (mul_eq_zero.mp this).resolve_left hκv
    linarith
  have hX : m1 * L + m2 * Xr + m3 * Xg = l1 * L + l2 * Xr + l3 * Xg := by
    have : c * ((m1 * L + m2 * Xr + m3 * Xg) - (l1 * L + l2 * Xr + l3 * Xg)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hc
    linarith
  have hYne : m2 * Yr + m3 * Yg ≠ l2 * Yr + l3 * Yg := by
    intro hh; apply hne; rw [hX, hz, hh]
  -- the four vertex conditions, in coordinates
  have hv : ∀ (Xm Ym zm : ℝ) (m : ZMod 4),
      Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg m = fpt e1 e2 e3 O Xm Ym zm →
      ((m2 * Yr + m3 * Yg) - (l2 * Yr + l3 * Yg)) * (Ym - (m2 * Yr + m3 * Yg)) ≤ 0 ∧
      ((l2 * Yr + l3 * Yg) - (m2 * Yr + m3 * Yg)) * (Ym - (l2 * Yr + l3 * Yg)) ≤ 0 := by
    intro Xm Ym zm m hm'
    obtain ⟨k1, k2⟩ := hall m
    rw [hm', inner_fpt_e hF] at k1 k2
    rw [hX, hz] at k1
    rw [← hX, ← hz] at k2
    constructor <;> nlinarith
  obtain ⟨vx1, vx2⟩ := hv 0 0 κ 0 rfl
  obtain ⟨vr1, vr2⟩ := hv Xr Yr zr 2 rfl
  obtain ⟨vg1, vg2⟩ := hv Xg Yg zg 3 rfl
  rcases lt_or_gt_of_ne hYne with hlt | hgt
  · -- the point `Y'` (coefficients `m`) is low
    exact persF_core hYr hYg hm0 hm1 hm2 hm3 hm hl0 hl1 hl2 hl3 hl hX hz (low_of hlt vx1)
      (high_of hlt vr2) (high_of hlt vg2)
  · exact persF_core hYr hYg hl0 hl1 hl2 hl3 hl hm0 hm1 hm2 hm3 hm hX.symm hz.symm (low_of hgt vx2)
      (high_of hgt vr1) (high_of hgt vg1)

/-- Robustness of the canonical cycle's depths, unpacked. -/
theorem rob4_canon (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg κv : ℝ} (hκv : κv ≠ 0)
    (hz : IsRobustUnimodal (fun j => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫)) :
    Rob4 κ zf zr zg := by
  have hw : ∀ j, ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫ =
      ⟪O, κv • e3⟫ + κv * quad κ zf zr zg j := by
    intro j
    have key : ∀ X Y z : ℝ, ⟪fpt e1 e2 e3 O X Y z, κv • e3⟫ = ⟪O, κv • e3⟫ + κv * z := by
      intro X Y z
      simp only [fpt, inner_add_left, real_inner_smul_right, inner_pc_e3 hF]
    rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact key 0 0 κ
    · exact key L 0 zf
    · exact key Xr Yr zr
    · exact key Xg Yg zg
  apply rob4_of
  rcases lt_or_gt_of_ne hκv with hn | hp
  · refine hz.neg.refine fun a b hab => ?_
    simp only [hw] at hab
    nlinarith
  · refine hz.refine fun a b hab => ?_
    simp only [hw] at hab
    nlinarith

/-- From any `RimCertAt` rim `Qg ∘ τ` (robust, with a persistent HDN) to the canonical cycle `Qg`. -/
theorem canon_of_rim (hF : Fr e1 e2 e3) (O : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg : ℝ} (hκv : κv ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (τ : ZMod k' → ZMod 4)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hzR : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i), κv • e3⟫))
    {e : ℝ³}
    (hp : ¬ NoPersistHDN (fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3) e) :
    IsRobustUnimodal (fun j => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫) ∧
      ¬ NoPersistHDN (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg) (κv • e3) e := by
  have hk4 := rim_k_eq_4 hF hκv hL hYr hYg hcr hcg hk3 τ hcyc hleft (O := O) (κ := κ) (zf := zf)
    (zr := zr) (zg := zg)
  subst hk4
  obtain ⟨hpos, hneg⟩ := rim_orient4 hF hκv hL hYr hYg hcr hcg τ hcyc hleft (O := O) (κ := κ)
    (zf := zf) (zr := zr) (zg := zg)
  rcases lt_or_gt_of_ne hκv with hn | hpv
  · obtain ⟨c, hc⟩ := hneg hn
    refine ⟨?_, fun hN => hp ?_⟩
    · exact robust_of_reflect (z := fun j : ZMod 4 => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫) c
        (by convert hzR using 2 with i; rw [hc i])
    · have hτ : (fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) =
          fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (c - i) := funext fun i => by rw [hc i]
      rw [hτ]
      refine noPersist_of_reflect c ?_
      convert hN using 2 with i
      congr 1; ring
  · obtain ⟨c, hc⟩ := hpos hpv
    refine ⟨?_, fun hN => hp ?_⟩
    · exact robust_of_shift (z := fun j : ZMod 4 => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg j, κv • e3⟫) c
        (by convert hzR using 2 with i; rw [hc i])
    · have hτ : (fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) =
          fun i => Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (c + i) := funext fun i => by rw [hc i]
      rw [hτ]
      refine noPersist_of_shift (-c) ?_
      convert hN using 2 with i
      congr 1; ring

end Type08Sp
end Minimality
