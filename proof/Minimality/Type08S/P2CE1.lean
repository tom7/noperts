module

public import Minimality.Type08S.P2H13
public import Minimality.Type08S.P2SC2S3
public import Minimality.Type08S.P2SC2S4
public import Minimality.Type08S.P2LXall

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkL CE1: the chord end at `f` (`CEf5`) in a canonical frame is Rupert (frame level)

`ce_frame`: from `Rob4`, strict Lemma E (`Yr = Yg` only), `CEf5` and the TriCert of the extra vertices `E`
(tilt `(κ s, -κ, 0)`), the five-point rim `rim5` is Rupert, by `lemmaSC2S` (f̄ interior of the top side),
`lemmaSC2S_r` (f̄ = r̄ on a top side), `lemmaSC2V_all` (top vertex over f̄, or f̄ = ḡ).
S uses σ = κ; V uses σ = sgn κ (the TriCert tilt is rescaled by |κ|, `hE_scale`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem triCert_smul {V : Finset ℝ³} {u0 d x : ℝ³} {c : ℝ} (hc : 0 < c) (h : TriCert V u0 (c • d) x) :
    TriCert V u0 d x := by
  obtain ⟨a, ha, b, hb, c', hc', h1, h2, h3, h4⟩ := h
  have key : ∀ {p q : ℝ³}, TiltSign p q u0 (c • d) → TiltSign p q u0 d := by
    intro p q h
    rcases h with h | ⟨h0, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨h0, ?_⟩
      rw [det3_smul_right] at h
      exact (mul_pos_iff_of_pos_left hc).1 h
  exact ⟨a, ha, b, hb, c', hc', key h1, key h2, key h3, key h4⟩

theorem hE_scale {V E : Finset ℝ³} {κ σ c : ℝ} (hc : 0 < c) (hk : κ = c * σ)
    (h : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y) :
    ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y := by
  filter_upwards [h] with s hs y hy
  have e : pc e1 e2 e3 (κ * s) (-κ) 0 = c • pc e1 e2 e3 (σ * s) (-σ) 0 := by
    subst hk; simp only [pc]; module
  have := hs y hy
  rw [e] at this
  exact triCert_smul hc this

/-- strict Lemma E in frame form -/
theorem lemEs_frame (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ} (hYr : 0 < Yr) (hY : Yr = Yg)
    (h : LemE3s O (O + pc e1 e2 e3 0 0 κ) (O + pc e1 e2 e3 L 0 zf) (O + pc e1 e2 e3 Xr Yr zr)
      (O + pc e1 e2 e3 Xg Yg zg)) :
    ((Xr - Xg) * (κ - zf) + L * (zr - zg)) * ((Xr - Xg) * (0 - zf) + L * (zr - zg)) < 0 := by
  unfold LemE3s at h
  have hOd : O - (O + pc e1 e2 e3 L 0 zf) = pc e1 e2 e3 (0 - L) (0 - 0) (0 - zf) := by
    simp only [pc]; module
  rw [hOd] at h
  simp only [add_sub_add_left_eq_sub, pc_sub, det3_pc hF] at h
  subst hY
  have key : Yr ^ 2 * (((Xr - Xg) * (κ - zf) + L * (zr - zg)) * ((Xr - Xg) * (0 - zf) + L * (zr - zg))) < 0 := by
    convert h using 1; ring
  by_contra hc; push_neg at hc
  nlinarith [mul_nonneg (sq_nonneg Yr) hc]

theorem rob_S {κ zf zr zg s' : ℝ} (hrob : Rob4 κ zf zr zg) (h0 : 0 < s') (h1 : s' < 1)
    (hzf : zf = zr + s' * (zg - zr)) :
    (zr < zf ∧ zf < zg ∧ zf < κ) ∨ (zg < zf ∧ zf < zr ∧ κ < zf) := by
  obtain ⟨pk1, pk2, t012, t013, t023, t123, l0, l1, l2, l3⟩ := hrob
  rcases lt_trichotomy zr zg with h | h | h
  · left
    have a1 : zr < zf := by nlinarith
    have a2 : zf < zg := by nlinarith
    refine ⟨a1, a2, ?_⟩
    rcases lt_trichotomy zf κ with k | k | k
    · exact k
    · exfalso; exact (l3 k.symm).2 ⟨by linarith, a1⟩
    · exfalso; exact pk2 ⟨k, by linarith, a1, by linarith⟩
  · exfalso
    apply t123
    refine ⟨?_, h⟩
    rw [hzf, ← h]; ring
  · right
    have a1 : zg < zf := by nlinarith
    have a2 : zf < zr := by nlinarith
    refine ⟨a1, a2, ?_⟩
    rcases lt_trichotomy zf κ with k | k | k
    · exfalso; exact pk1 ⟨k, a2, by linarith, h⟩
    · exfalso; exact (l3 k.symm).1 ⟨by linarith, a2⟩
    · exact k

theorem rob_Sr {κ zf zg : ℝ} (hrob : Rob4 κ zf zf zg) :
    (zf < zg ∧ zf < κ) ∨ (zg < zf ∧ κ < zf) := by
  obtain ⟨pk1, pk2, t012, t013, t023, t123, l0, l1, l2, l3⟩ := hrob
  have hg : zg ≠ zf := fun h => t123 ⟨rfl, h.symm⟩
  have hx : κ ≠ zf := fun h => t012 ⟨h, rfl⟩
  obtain ⟨l01, l02⟩ := l0 rfl
  rcases lt_or_gt_of_ne hg with h | h
  · right
    refine ⟨h, ?_⟩
    rcases lt_or_gt_of_ne hx with k | k
    · exact k
    · exfalso; exact l02 ⟨k, h⟩
  · left
    refine ⟨h, ?_⟩
    rcases lt_or_gt_of_ne hx with k | k
    · exfalso; exact l01 ⟨k, h⟩
    · exact k

theorem rob_Vg {κ zf zr : ℝ} (hrob : Rob4 κ zf zr zf) : (zr - zf) * (κ - zf) < 0 := by
  obtain ⟨pk1, pk2, t012, t013, t023, t123, l0, l1, l2, l3⟩ := hrob
  have hr : zr ≠ zf := fun h => t123 ⟨h.symm, h⟩
  have hx : κ ≠ zf := fun h => t013 ⟨h, rfl⟩
  rcases lt_or_gt_of_ne hr with h | h <;> rcases lt_or_gt_of_ne hx with k | k
  · exfalso; exact pk2 ⟨k, k, h, h⟩
  · nlinarith
  · nlinarith
  · exfalso; exact pk1 ⟨k, h, k, h⟩

theorem ce_V (hF : Fr e1 e2 e3) (O : ℝ³) (E : Finset ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ} (hκ : κ ≠ 0)
    (hL : 0 < L) (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassV2tail L κ zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y) :
    IsRupert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E) := by
  obtain ⟨σ, c, hσ, hc0, hkσ⟩ : ∃ σ c : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < c ∧ κ = c * σ := by
    rcases lt_or_gt_of_ne hκ with h | h
    · exact ⟨-1, -κ, Or.inr rfl, by linarith, by ring⟩
    · exact ⟨1, κ, Or.inl rfl, h, by ring⟩
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hzx : 0 < σ * (κ - 0) := by
    have : σ * (κ - 0) = c * (σ * σ) := by rw [hkσ]; ring
    rw [this, hσσ]; linarith
  exact lemmaSC2V_all hF O E hσ hL hzx hcr hYr hYg hcg hc (hE_scale hc0 hkσ hE)

theorem ce_frame (hF : Fr e1 e2 e3) (O : ℝ³) (E : Finset ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ} (hκ : κ ≠ 0)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y)
    (hrob : Rob4 κ zf zr zg)
    (hLs : Yr = Yg → ((Xr - Xg) * (κ - zf) + L * (zr - zg)) * ((Xr - Xg) * (0 - zf) + L * (zr - zg)) < 0)
    (hce : CEf5 L κ zf Xr Yr zr Xg Yg zg) :
    IsRupert (rim5 e1 e2 e3 O L 0 κ zf Xr Yr zr Xg Yg zg E) := by
  have hzx : 0 < κ * (κ - 0) := by rw [sub_zero]; exact mul_self_pos.mpr hκ
  have m1 : ∀ x y : ℝ, x < y → 0 < κ → κ * x < κ * y := fun x y h hk => mul_lt_mul_of_pos_left h hk
  have m2 : ∀ x y : ℝ, x < y → κ < 0 → κ * y < κ * x := fun x y h hk => mul_lt_mul_of_neg_left h hk
  obtain ⟨s', hs0, hs1, hY, hLX, hzf⟩ := hce
  rcases hY with hYeq | ⟨hs0', hlt⟩ | ⟨hs1', hlt⟩
  · -- top side
    have hXrg : Xg < Xr := by
      by_contra hh; push_neg at hh
      rw [← hYeq] at hcg
      nlinarith [mul_nonneg hYr.le (sub_nonneg.2 hh)]
    obtain ⟨m, σ0, hzr', hzg'⟩ : ∃ m σ0 : ℝ, σ0 + m * Xr = zr ∧ σ0 + m * Xg = zg := by
      have hne : Xg - Xr ≠ 0 := (by linarith : Xg - Xr < 0).ne
      refine ⟨(zg - zr) / (Xg - Xr), zr - (zg - zr) / (Xg - Xr) * Xr, by ring, ?_⟩
      have h : (zg - zr) / (Xg - Xr) * (Xg - Xr) = zg - zr := div_mul_cancel₀ _ hne
      linear_combination h
    have hzfL : σ0 + m * L = zf := by
      linear_combination (1 - s') * hzr' + s' * hzg' + m * hLX - hzf
    have hD : ∀ z, (Xr - Xg) * (z - zf) + L * (zr - zg) = (Xr - Xg) * (z - σ0) := by
      intro z; rw [← hzfL, ← hzr', ← hzg']; ring
    have hPi : 0 < κ * (σ0 - 0) := by
      have h := hLs hYeq
      rw [hD, hD] at h
      have h2 : 0 < (Xr - Xg) ^ 2 := pow_pos (sub_pos.2 hXrg) 2
      have h3 : (κ - σ0) * (0 - σ0) < 0 := by
        by_contra hh; push_neg at hh
        nlinarith [mul_nonneg h2.le hh]
      nlinarith [sq_nonneg σ0]
    rcases hs0.eq_or_lt with h0 | h0
    · -- f̄ = r̄
      have hXr : Xr = L := by rw [hLX, ← h0]; ring
      have hzrf : zr = zf := by rw [hzf, ← h0]; ring
      have hrobr : Rob4 κ zf zf zg := by rw [hzrf] at hrob; exact hrob
      have hc : ClassS2r κ L 0 κ Xg m σ0 := by
        refine ⟨by rw [← hXr]; exact hXrg, hPi, ?_⟩
        rw [hzfL, hzg']
        rcases rob_Sr hrobr with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases lt_or_gt_of_ne hκ with hk | hk
        · right; exact ⟨m2 _ _ a1 hk, m2 _ _ a2 hk⟩
        · left; exact ⟨m1 _ _ a1 hk, m1 _ _ a2 hk⟩
        · left; exact ⟨m2 _ _ a1 hk, m2 _ _ a2 hk⟩
        · right; exact ⟨m1 _ _ a1 hk, m1 _ _ a2 hk⟩
      have hE' := hE
      rw [← hYeq, hXr, hzrf] at hE'
      have := lemmaSC2S_r hF O E (σ := κ) (zp := 0) (zx := κ) (L := L) (Xg := Xg) (Y := Yr) (m := m)
        (σ0 := σ0) hL hzx hYr hc (by rw [hzfL, hzg']; exact hE')
      rw [hzfL, hzg'] at this
      rw [hXr, hzrf, ← hYeq]
      exact this
    · rcases hs1.eq_or_lt with h1 | h1
      · -- f̄ = ḡ
        refine ce_V hF O E hκ hL hcr hYr hYg hcg ?_ hE
        right; right
        have hXg : Xg = L := by rw [hLX, h1]; ring
        have hzg : zg = zf := by rw [hzf, h1]; ring
        refine ⟨hYeq.symm, hXg, hzg, by rw [← hXg]; exact hXrg, ?_⟩
        rw [hzg] at hrob; exact rob_Vg hrob
      · -- f̄ interior
        have hc : ClassS2 κ L 0 κ Xr Xg m σ0 := by
          refine ⟨?_, ?_, hPi, ?_⟩
          · have e : L - Xg = (1 - s') * (Xr - Xg) := by rw [hLX]; ring
            have := mul_pos (sub_pos.2 h1) (sub_pos.2 hXrg)
            linarith
          · have e : Xr - L = s' * (Xr - Xg) := by rw [hLX]; ring
            have := mul_pos h0 (sub_pos.2 hXrg)
            linarith
          · rw [hzfL, hzr', hzg']
            rcases rob_S hrob h0 h1 hzf with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;> rcases lt_or_gt_of_ne hκ with hk | hk
            · right; exact ⟨m2 _ _ a2 hk, m2 _ _ a3 hk, m2 _ _ (a1.trans a2) hk, m2 _ _ (a1.trans a3) hk⟩
            · left; exact ⟨m1 _ _ a2 hk, m1 _ _ a3 hk, m1 _ _ (a1.trans a2) hk, m1 _ _ (a1.trans a3) hk⟩
            · left; exact ⟨m2 _ _ a1 hk, m2 _ _ a3 hk, m2 _ _ (a1.trans a2) hk, m2 _ _ (a3.trans a2) hk⟩
            · right; exact ⟨m1 _ _ a1 hk, m1 _ _ a3 hk, m1 _ _ (a1.trans a2) hk, m1 _ _ (a3.trans a2) hk⟩
        have hE' := hE
        rw [← hYeq] at hE'
        have := lemmaSC2S hF O E (σ := κ) (zp := 0) (zx := κ) (L := L) (Xr := Xr) (Xg := Xg) (Y := Yr)
          (m := m) (σ0 := σ0) hL hzx hYr hc (by rw [hzfL, hzr', hzg']; exact hE')
        rw [hzfL, hzr', hzg'] at this
        rw [← hYeq]
        exact this
  · -- s' = 0, Yg < Yr : top vertex r over f̄
    have hXr : Xr = L := by rw [hLX, hs0']; ring
    have hzrf : zr = zf := by rw [hzf, hs0']; ring
    have hrobr : Rob4 κ zf zf zg := by rw [hzrf] at hrob; exact hrob
    refine ce_V hF O E hκ hL hcr hYr hYg hcg ?_ hE
    left
    refine ⟨hXr, hzrf, hlt, ?_⟩
    rcases rob_Sr hrobr with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> nlinarith
  · -- s' = 1, Yr < Yg : top vertex g over f̄
    have hXg : Xg = L := by rw [hLX, hs1']; ring
    have hzg : zg = zf := by rw [hzf, hs1']; ring
    refine ce_V hF O E hκ hL hcr hYr hYg hcg ?_ hE
    right; left
    refine ⟨hXg, hzg, hlt, ?_⟩
    rw [hzg] at hrob; exact rob_Vg hrob

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.ce_frame
