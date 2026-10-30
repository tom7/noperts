module

public import Minimality.Type08S.P2CB

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 5: the rim of the closing is the screen quadrilateral (rotation or reflection).

`inc`-combinatorics (`comb3`, `comb4`) + the planar orientation table of `(x, f, r, g)`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The cycle `(x, f, r, g)` as a function on `ZMod 4`. -/
def Qg (e1 e2 e3 O : ℝ³) (κ L zf Xr Yr zr Xg Yg zg : ℝ) : ZMod 4 → ℝ³ :=
  quad (fpt e1 e2 e3 O 0 0 κ) (fpt e1 e2 e3 O L 0 zf) (fpt e1 e2 e3 O Xr Yr zr)
    (fpt e1 e2 e3 O Xg Yg zg)

/-- Planar orientation of the screen positions of `Qg a, Qg b, Qg c`. -/
def crQ (L Xr Yr Xg Yg : ℝ) (a b c : ZMod 4) : ℝ :=
  (quad 0 L Xr Xg b - quad 0 L Xr Xg a) * (quad 0 0 Yr Yg c - quad 0 0 Yr Yg a) -
  (quad 0 0 Yr Yg b - quad 0 0 Yr Yg a) * (quad 0 L Xr Xg c - quad 0 L Xr Xg a)

theorem crQ_swap (L Xr Yr Xg Yg : ℝ) (a b c : ZMod 4) :
    crQ L Xr Yr Xg Yg a c b = - crQ L Xr Yr Xg Yg a b c := by
  simp only [crQ]; ring

theorem crQ_pos_iff {L Xr Yr Xg Yg : ℝ} (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (a b c : ZMod 4) : 0 < crQ L Xr Yr Xg Yg a b c ↔ inc a b c := by
  have hLY : 0 < L * Yr := mul_pos hL hYr
  have hLG : 0 < L * Yg := mul_pos hL hYg
  rcases zmod4_cases a with rfl | rfl | rfl | rfl <;> rcases zmod4_cases b with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases c with rfl | rfl | rfl | rfl <;>
    first
    | (refine iff_of_true ?_ (by decide); simp only [crQ, quad_0, quad_1, quad_2, quad_3]; nlinarith)
    | (refine iff_of_false ?_ (by decide); simp only [crQ, quad_0, quad_1, quad_2, quad_3, not_lt]; nlinarith)

theorem crQ_neg_iff {L Xr Yr Xg Yg : ℝ} (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (a b c : ZMod 4) : crQ L Xr Yr Xg Yg a b c < 0 ↔ inc a c b := by
  rw [← crQ_pos_iff hL hYr hYg hcr hcg, crQ_swap]; constructor <;> intro h <;> linarith

theorem det3_Qg (hF : Fr e1 e2 e3) (O : ℝ³) (κ L zf Xr Yr zr Xg Yg zg κv : ℝ) (a b c : ZMod 4) :
    det3 (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg b - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a)
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg c - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a)
      (κv • e3) = κv * crQ L Xr Yr Xg Yg a b c := by
  have hQ : ∀ a : ZMod 4, Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a =
      fpt e1 e2 e3 O (quad 0 L Xr Xg a) (quad 0 0 Yr Yg a) (quad κ zf zr zg a) := by
    intro a; rcases zmod4_cases a with rfl | rfl | rfl | rfl <;> rfl
  rw [hQ a, hQ b, hQ c, fpt_sub, fpt_sub, det3_u0 hF]
  simp only [crQ]


theorem two_ne_zero_of (k' : ℕ) (hk3 : 3 ≤ k') : (2 : ZMod k') ≠ 0 ∧ (1 : ZMod k') ≠ 0 := by
  constructor
  · intro h
    have : ((2 : ℕ) : ZMod k') = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · intro h
    have : ((1 : ℕ) : ZMod k') = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

section classify
variable {O : ℝ³} {κ L zf Xr Yr zr Xg Yg zg κv : ℝ}

/-- Translation of the rim hypotheses into `inc`-form, `κv > 0`. -/
theorem rim_inc_pos (hF : Fr e1 e2 e3) (hκv : 0 < κv) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    {k' : ℕ} [NeZero k'] (τ : ZMod k' → ZMod 4)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3)) :
    (∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → inc (τ i) (τ (i + 1)) (τ j)) ∧
    (∀ (i : ZMod k') (m : ZMod 4), ¬ inc (τ i) m (τ (i + 1))) := by
  constructor
  · intro i j hi hj
    have h := hcyc i j hi hj
    rw [det3_Qg hF] at h
    exact (crQ_pos_iff hL hYr hYg hcr hcg _ _ _).mp (pos_of_mul_pos_right h hκv.le)
  · intro i m hm
    have h := hleft i m
    rw [det3_Qg hF] at h
    have h2 := (crQ_neg_iff hL hYr hYg hcr hcg (τ i) (τ (i + 1)) m).mpr hm
    nlinarith

theorem rim_inc_neg (hF : Fr e1 e2 e3) (hκv : κv < 0) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    {k' : ℕ} [NeZero k'] (τ : ZMod k' → ZMod 4)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3)) :
    (∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → inc (τ i) (τ j) (τ (i + 1))) ∧
    (∀ (i : ZMod k') (m : ZMod 4), ¬ inc (τ i) (τ (i + 1)) m) := by
  constructor
  · intro i j hi hj
    have h := hcyc i j hi hj
    rw [det3_Qg hF] at h
    have : crQ L Xr Yr Xg Yg (τ i) (τ (i + 1)) (τ j) < 0 := by nlinarith
    exact (crQ_neg_iff hL hYr hYg hcr hcg _ _ _).mp this
  · intro i m hm
    have h := hleft i m
    rw [det3_Qg hF] at h
    have h2 := (crQ_pos_iff hL hYr hYg hcr hcg (τ i) (τ (i + 1)) m).mpr hm
    nlinarith

end classify

theorem inj_of_H1 {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (τ : ZMod k' → ZMod 4)
    (H : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → τ i ≠ τ (i + 1) ∧ τ i ≠ τ j) : Function.Injective τ := by
  obtain ⟨h2, h1⟩ := two_ne_zero_of k' hk3
  intro i j hij
  by_contra hne
  by_cases hj : j = i + 1
  · have := (H i (i + 2) (by intro h; apply h2; have := congrArg (· - i) h; simpa using this)
      (by intro h; apply h1; have := congrArg (· - (i + 1)) h; ring_nf at this; simpa using this)).1
    apply this; rw [hij, hj]
  · exact (H i j (Ne.symm hne) hj).2 hij

theorem k_le_four {k' : ℕ} [NeZero k'] (τ : ZMod k' → ZMod 4) (h : Function.Injective τ) : k' ≤ 4 := by
  have := Fintype.card_le_of_injective τ h
  simpa [ZMod.card] using this

end Type08Sp
end Minimality
