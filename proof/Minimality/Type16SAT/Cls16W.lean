module

public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16: the class boundaries (walls) with one zero bracket (J10)

`SgnP e b` : `e = 0` means `b = 0`, otherwise `0 < e * b`.  `Vec16 e1 e2 e3 e4 x` : the products `C * [0126]`, `C * [0134]`, `C * [1234]`,
`C * [2346]` (C = `[3056]`) have the signs `e1 .. e4 ∈ {-1, 0, 1}` (0 = the product is zero).
`Core16W e1 e2 e3 e4` is the shape of a wall core theorem on `0 < C`.  The nine UNSAT wall representatives are
`+++0 ++0+ +0++ 0+++ +-0+ 0++- ++0- 0+-+ 0+--`; sigma16 maps `s` to `(-s1, s4, s3, s2)` (zero stays zero), which gives 16 distinct vectors
(`0+++` and `0+-+` are their own images).  Mirror leaves the products `C * bracket` invariant.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Sign test with a zero case: `e = 0` means `b = 0`, otherwise `0 < e * b`. -/
def SgnP (e b : ℝ) : Prop := if e = 0 then b = 0 else 0 < e * b

theorem sgnP_neg (e b : ℝ) : SgnP e (-b) ↔ SgnP (-e) b := by
  by_cases h : e = 0
  · subst h; simp [SgnP]
  · have h' : -e ≠ 0 := neg_ne_zero.mpr h
    simp only [SgnP, h, h', ite_false]
    constructor <;> intro k <;> linarith

theorem sgnP_pos {e C b : ℝ} (hC : 0 < C) (h : SgnP e (C * b)) : SgnP e b := by
  by_cases he : e = 0
  · subst he
    simp only [SgnP, ite_true] at h ⊢
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hC.ne'
    · exact h
  · simp only [SgnP, he, ite_false] at h ⊢
    have : 0 < C * (e * b) := by linarith
    exact (pos_iff_pos_of_mul_pos this).mp hC

theorem sgnP_neg_of_neg {e C b : ℝ} (hC : C < 0) (h : SgnP e (C * b)) : SgnP e (-b) := by
  by_cases he : e = 0
  · subst he
    simp only [SgnP, ite_true] at h ⊢
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hC.ne
    · simp [h]
  · simp only [SgnP, he, ite_false] at h ⊢
    have h2 : 0 < C * (e * b) := by linarith
    have : e * b < 0 := by nlinarith
    linarith

/-- The products `C * bracket` have the sign pattern `e1 e2 e3 e4` (0 = zero). -/
def Vec16 (e1 e2 e3 e4 : ℝ) (x : Fin 7 → ℝ³) : Prop :=
  SgnP e1 (C16 x * br16 x 0 1 2 6) ∧ SgnP e2 (C16 x * br16 x 0 1 3 4) ∧
  SgnP e3 (C16 x * br16 x 1 2 3 4) ∧ SgnP e4 (C16 x * br16 x 2 3 4 6)

/-- The shape of a wall core theorem on `0 < C` (`e_i = 0`: that bracket is zero). -/
def Core16W (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³}, S0xFac 8 Minimality.V2.fIdx y → 0 < C16 y →
    SgnP e1 (br16 y 0 1 2 6) → SgnP e2 (br16 y 0 1 3 4) → SgnP e3 (br16 y 1 2 3 4) → SgnP e4 (br16 y 2 3 4 6) →
    IsRupert (univ.image y)

/-- Both chiralities for a wall core. -/
theorem rupert_of_core_bothW {e1 e2 e3 e4 : ℝ} (hcore : Core16W e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0) (h : Vec16 e1 e2 e3 e4 y) :
    IsRupert (univ.image y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_)
    · rw [C16_mir]; linarith
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h1
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h2
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h3
    · rw [br16_mir]; exact sgnP_neg_of_neg hn h4
  · exact hcore F hp (sgnP_pos hp h1) (sgnP_pos hp h2) (sgnP_pos hp h3) (sgnP_pos hp h4)

/-- A wall vector closes by its core. -/
theorem rupert_wall {e1 e2 e3 e4 : ℝ} (hcore : Core16W e1 e2 e3 e4) {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : Vec16 e1 e2 e3 e4 x) : IsRupert (univ.image x) :=
  rupert_of_core_bothW hcore (Minimality.H16A.h16g_fac T) T.det_ne h

/-- The sigma image `(-e1, e4, e3, e2)` of a wall vector closes by the same core. -/
theorem rupert_wall_sigma {e1 e2 e3 e4 f1 f2 f3 f4 : ℝ} (hcore : Core16W e1 e2 e3 e4) {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : Vec16 f1 f2 f3 f4 x) (g1 : f1 = -e1) (g2 : f2 = e4) (g3 : f3 = e3) (g4 : f4 = e2) :
    IsRupert (univ.image x) := by
  subst g1 g2 g3 g4
  obtain ⟨h1, h2, h3, h4⟩ := h
  have a1 := C16_sigma x
  have a2 := b1_sigma x
  have a3 := b2_sigma x
  have a4 := b3_sigma x
  have a5 := b4_sigma x
  have := rupert_of_core_bothW hcore (Minimality.H16A.h16g_fac T.sigma) T.sigma.det_ne
    ⟨by rw [a1, a2, neg_mul, sgnP_neg]; exact h1, by rw [a1, a3, neg_mul_neg]; exact h4,
     by rw [a1, a4, neg_mul_neg]; exact h3, by rw [a1, a5, neg_mul_neg]; exact h2⟩
  rwa [Minimality.image_sigma16] at this

/-- **Closed walls**: the 16 sign vectors with exactly one zero among the products `C * bracket` (the sigma orbits of the nine UNSAT
representatives `+++0 ++0+ +0++ 0+++ +-0+ 0++- ++0- 0+-+ 0+--`). -/
def Cls16ClosedW (x : Fin 7 → ℝ³) : Prop :=
  Vec16 1 1 1 0 x
  ∨ Vec16 (-1) 0 1 1 x
  ∨ Vec16 1 1 0 1 x
  ∨ Vec16 (-1) 1 0 1 x
  ∨ Vec16 1 0 1 1 x
  ∨ Vec16 (-1) 1 1 0 x
  ∨ Vec16 0 1 1 1 x
  ∨ Vec16 1 (-1) 0 1 x
  ∨ Vec16 (-1) 1 0 (-1) x
  ∨ Vec16 0 1 1 (-1) x
  ∨ Vec16 0 (-1) 1 1 x
  ∨ Vec16 1 1 0 (-1) x
  ∨ Vec16 (-1) (-1) 0 1 x
  ∨ Vec16 0 1 (-1) 1 x
  ∨ Vec16 0 1 (-1) (-1) x
  ∨ Vec16 0 (-1) (-1) 1 x

/-- **Type 16, the walls, from the nine core theorems.** -/
theorem isRupert_cls3w_of
    (hPPPZ : Core16W 1 1 1 0)
    (hPPZP : Core16W 1 1 0 1)
    (hPZPP : Core16W 1 0 1 1)
    (hZPPP : Core16W 0 1 1 1)
    (hPMZP : Core16W 1 (-1) 0 1)
    (hZPPM : Core16W 0 1 1 (-1))
    (hPPZM : Core16W 1 1 0 (-1))
    (hZPMP : Core16W 0 1 (-1) 1)
    (hZPMM : Core16W 0 1 (-1) (-1))
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16ClosedW x) : IsRupert (univ.image x) := by
  simp only [Cls16ClosedW] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rupert_wall hPPPZ T h
  · exact rupert_wall_sigma hPPPZ T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hPPZP T h
  · exact rupert_wall_sigma hPPZP T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hPZPP T h
  · exact rupert_wall_sigma hPZPP T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hZPPP T h
  · exact rupert_wall hPMZP T h
  · exact rupert_wall_sigma hPMZP T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hZPPM T h
  · exact rupert_wall_sigma hZPPM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hPPZM T h
  · exact rupert_wall_sigma hPPZM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact rupert_wall hZPMP T h
  · exact rupert_wall hZPMM T h
  · exact rupert_wall_sigma hZPMM T h (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Minimality.H16.SAT
