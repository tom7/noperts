module

public import Minimality.Type24ROff

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.RCell Minimality.T24.Sym
  Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A19 Minimality.T24 Minimality.T24.Q45

namespace Minimality.T24.Reg

/-! ### Class brackets under `x ∘ pi24` -/

theorem chi24_comp_pi24 (x : Fin 7 → ℝ³) : chi24 (x ∘ pi24) = - chi24 x := by
  unfold chi24 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem b1234_comp_pi24 (x : Fin 7 → ℝ³) : b1234 (x ∘ pi24) = b1356 x := by
  unfold b1234 b1356 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem b1356_comp_pi24 (x : Fin 7 → ℝ³) : b1356 (x ∘ pi24) = b1234 x := by
  unfold b1234 b1356 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem b1245_comp_pi24 (x : Fin 7 → ℝ³) : b1245 (x ∘ pi24) = - b1456 x := by
  unfold b1245 b1456 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem b1456_comp_pi24 (x : Fin 7 → ℝ³) : b1456 (x ∘ pi24) = - b1245 x := by
  unfold b1245 b1456 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem b2456_comp_pi24 (x : Fin 7 → ℝ³) : b2456 (x ∘ pi24) = b2456 x := by
  unfold b2456 det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring


theorem resid24_comp_pi24 {x : Fin 7 → ℝ³} (h : Resid24 x) : Resid24 (x ∘ pi24) := by
  rcases h with h | h | h | h
  · exact Or.inl ((ob1_comp_pi24 x).2 h)
  · refine Or.inr (Or.inl ?_)
    unfold ZRes24 clsz24 at h ⊢
    simp only [sgz, flipz, sg, Bool.not_true, Bool.not_false] at h ⊢
    simp only [chi24_comp_pi24, b1234_comp_pi24, b1356_comp_pi24, b1245_comp_pi24, b1456_comp_pi24,
      b2456_comp_pi24]
    rcases h with ⟨a, b, c, d, e, f⟩ | ⟨a, b, c, d, e, f⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith, f⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith, f⟩
  · refine Or.inr (Or.inr (Or.inr ?_))
    unfold cls24 at h ⊢
    simp only [sg, Bool.not_true, Bool.not_false] at h ⊢
    simp only [chi24_comp_pi24, b1234_comp_pi24, b1356_comp_pi24, b1245_comp_pi24, b1456_comp_pi24,
      b2456_comp_pi24]
    rcases h with ⟨a, b, c, d, e, f⟩ | ⟨a, b, c, d, e, f⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · refine Or.inr (Or.inr (Or.inl ?_))
    unfold cls24 at h ⊢
    simp only [sg, Bool.not_true, Bool.not_false] at h ⊢
    simp only [chi24_comp_pi24, b1234_comp_pi24, b1356_comp_pi24, b1245_comp_pi24, b1456_comp_pi24,
      b2456_comp_pi24]
    rcases h with ⟨a, b, c, d, e, f⟩ | ⟨a, b, c, d, e, f⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩


theorem q45_det_comp_pi24 (x : Fin 7 → ℝ³) :
    det3 ((x ∘ pi24) 5 - (x ∘ pi24) 6) ((x ∘ pi24) 2 - (x ∘ pi24) 6) ((x ∘ pi24) 4 - (x ∘ pi24) 6) =
      det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  unfold det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem q45_chi_comp_pi24 (x : Fin 7 → ℝ³) :
    det3 ((x ∘ pi24) 0 - (x ∘ pi24) 1) ((x ∘ pi24) 2 - (x ∘ pi24) 1) ((x ∘ pi24) 6 - (x ∘ pi24) 1) =
      - det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  unfold det3
  simp [Function.comp_apply, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- `Q45HalfHyp` of the mirror at `(t, s)` gives `Q45HalfHyp` of `x` at `(s, t)`. -/
theorem q45HalfHyp_of_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ)
    (h : Q45HalfHyp (sym24 F) t s) : Q45HalfHyp F s t := by
  unfold Q45HalfHyp at h ⊢
  simp only [q45_det_comp_pi24, q45_chi_comp_pi24] at h
  simp only [sym24_N, sig24_5, Function.comp_apply, pi24_0, pi24_1, pi24_2, pi24_3, pi24_4, pi24_5,
    pi24_6] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hP => ?_, fun hP => ?_, fun hP => ?_⟩
  · have := h2 (by nlinarith)
    exact this
  · have := h1 (by nlinarith)
    exact this
  · have := h3 hP
    exact ⟨this.2, this.1⟩

/-- `Q45HalfPred` of the mirror gives `Q45HalfPred` of `x`. -/
theorem q45HalfPred_of_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Q45HalfPred (sym24 F)) :
    Q45HalfPred F := by
  intro s t hs ht hst hdec
  refine q45HalfHyp_of_sym F s t (h t s ht hs (by linarith) ?_)
  simpa [Function.comp_apply, pi24_0, pi24_3, pi24_4, pi24_5, add_comm] using hdec

theorem anyFaceChord_of_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : AnyFaceChord (sym24 F)) :
    AnyFaceChord F := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, faceChordView_sym F ht⟩

/-- **Target 1**: `Hole24R` transports along `pi24`. -/
theorem hole24R_comp_pi24 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24R x F) :
    Hole24R (x ∘ pi24) (sym24 F) := by
  obtain ⟨hC, hR, hQ, hA, hL, hS⟩ := h
  exact ⟨(cbarIn_comp_pi24 x).2 hC, resid24_comp_pi24 hR, fun hq => hQ (q45HalfPred_of_sym F hq),
    fun ha => hA (anyFaceChord_of_sym F ha), fun hl => hL (lexAny_sym F hl),
    fun hs => hS (splitAny24_sym F hs)⟩


/-! ### Coordinate maps -/

theorem oblX0_comp_pi24_4 (x : Fin 7 → ℝ³) : oblX0 (x ∘ pi24) 4 = oblX0 x 5 := by
  simp [oblX0_comp_pi24]

theorem oblX0_comp_pi24_5 (x : Fin 7 → ℝ³) : oblX0 (x ∘ pi24) 5 = oblX0 x 4 := by
  simp [oblX0_comp_pi24]

/-- sigma of the mirror is tau (facet 6 = 235 of `x`): the `f8` values at `x'0, x'5` are the `f6` values at
`x0, x4`. -/
theorem sym24_f8_x0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (sym24 F).f 8 ((x ∘ pi24) 0) = F.f 6 (x 0) := by simp
theorem sym24_f8_x5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (sym24 F).f 8 ((x ∘ pi24) 5) = F.f 6 (x 4) := by simp
/-- tau of the mirror is sigma. -/
theorem sym24_f6_x0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (sym24 F).f 6 ((x ∘ pi24) 0) = F.f 8 (x 0) := by simp
theorem sym24_f6_x4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    (sym24 F).f 6 ((x ∘ pi24) 4) = F.f 8 (x 5) := by simp

/-! ### Region maps -/

/-- `BA4 -> A1 or A2` of the image (`A1` iff `tau <= 1`). -/
theorem ba4_to_a {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : BA4 x F) :
    A1 (x ∘ pi24) (sym24 F) ∨ A2 (x ∘ pi24) (sym24 F) := by
  obtain ⟨-, -, h4⟩ := h
  unfold A1 A2
  rw [oblX0_comp_pi24_5, sym24_f8_x0, sym24_f8_x5]
  rcases le_or_gt (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
  · exact Or.inl ⟨h4, ht⟩
  · exact Or.inr ⟨h4, ht⟩

/-- `CA -> A1` of the image. -/
theorem ca_to_a1 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CA x F) :
    A1 (x ∘ pi24) (sym24 F) := by
  obtain ⟨-, -, h4, ht⟩ := h
  unfold A1
  rw [oblX0_comp_pi24_5, sym24_f8_x0, sym24_f8_x5]
  exact ⟨h4, ht⟩

/-- `CA2 -> A2` of the image. -/
theorem ca2_to_a2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CA2 x F) :
    A2 (x ∘ pi24) (sym24 F) := by
  obtain ⟨-, -, h4, ht⟩ := h
  unfold A2
  rw [oblX0_comp_pi24_5, sym24_f8_x0, sym24_f8_x5]
  exact ⟨h4, ht⟩

/-- `A1 -> BA4 or CA or WallA5` of the image, on `Hole24R` (`a4 <= 1` there). -/
theorem a1_to_b {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) (h : A1 x F) :
    BA4 (x ∘ pi24) (sym24 F) ∨ CA (x ∘ pi24) (sym24 F) ∨ WallA5 (x ∘ pi24) := by
  obtain ⟨h5, hs⟩ := h
  have h4 : oblX0 x 4 ≤ 1 := by
    by_contra hc; exact hole24R_not_both_gt hR ⟨not_le.mp hc, h5⟩
  unfold BA4 CA WallA5
  simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4]
  rcases lt_or_eq_of_le h4 with h4 | h4
  · rcases lt_or_ge (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
    · exact Or.inl ⟨h4, ht, h5⟩
    · exact Or.inr (Or.inl ⟨h4, ht, h5, hs⟩)
  · exact Or.inr (Or.inr h4)

/-- `A2 -> BA4 or CA2 or WallA5` of the image, on `Hole24R`. -/
theorem a2_to_b {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) (h : A2 x F) :
    BA4 (x ∘ pi24) (sym24 F) ∨ CA2 (x ∘ pi24) (sym24 F) ∨ WallA5 (x ∘ pi24) := by
  obtain ⟨h5, hs⟩ := h
  have h4 : oblX0 x 4 ≤ 1 := by
    by_contra hc; exact hole24R_not_both_gt hR ⟨not_le.mp hc, h5⟩
  unfold BA4 CA2 WallA5
  simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4]
  rcases lt_or_eq_of_le h4 with h4 | h4
  · rcases lt_or_ge (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
    · exact Or.inl ⟨h4, ht, h5⟩
    · exact Or.inr (Or.inl ⟨h4, ht, h5, hs⟩)
  · exact Or.inr (Or.inr h4)

/-- `C_flip`: `a5 < 1`, `sigma >= 1`, `a4 < 1`, `tau < 1` (the part of `CB` and `CC` with `a4 < 1`, `tau < 1`). -/
def CFlip (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ oblX0 x 4 < 1 ∧ F.f 6 (x 0) < F.f 6 (x 4)

theorem cb_a4lt_cflip {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CB x F) (h4 : oblX0 x 4 < 1) :
    CFlip x F := ⟨h.1, h.2.1, h4, h.2.2.2.2⟩

theorem cc_tau_cflip {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CC x F) (h4 : oblX0 x 4 < 1)
    (ht : F.f 6 (x 0) < F.f 6 (x 4)) : CFlip x F := ⟨h.1, h.2.1, h4, ht⟩

/-- `CFlip -> BRest` of the image. -/
theorem cflip_to_brest {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CFlip x F) :
    BRest (x ∘ pi24) (sym24 F) := by
  obtain ⟨h5, hs, h4, ht⟩ := h
  unfold BRest
  simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4]
  exact ⟨h4, ht, h5.le, fun hq => absurd hq.2 (not_lt.mpr hs)⟩

/-- `BE0416 -> BRest or BE0416` of the image (when `a4 < 1`); `BE0416'` iff `nB < 0`. -/
theorem be0416_to_b {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : BE0416 x F) (h4 : oblX0 x 4 < 1) :
    BRest (x ∘ pi24) (sym24 F) ∨ BE0416 (x ∘ pi24) (sym24 F) := by
  obtain ⟨h5, hs, -, -, ht⟩ := h
  by_cases hB : nB x < 0
  · right
    unfold BE0416
    simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4,
      nC_comp_pi24]
    exact ⟨h4, ht, h5.le, hB, hs⟩
  · left
    unfold BRest
    simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4,
      nC_comp_pi24]
    exact ⟨h4, ht, h5.le, fun hq => hB hq.1⟩

/-- `CC` with `tau >= 1`, `a4 < 1`: fixed class, image in `CC`. -/
theorem cc_tau_ge_to_cc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : CC x F) (h4 : oblX0 x 4 < 1)
    (ht : F.f 6 (x 4) ≤ F.f 6 (x 0)) : CC (x ∘ pi24) (sym24 F) := by
  obtain ⟨h5, hs, -, -⟩ := h
  unfold CC
  simp only [oblX0_comp_pi24_5, oblX0_comp_pi24_4, sym24_f8_x0, sym24_f8_x5, sym24_f6_x0, sym24_f6_x4]
  exact ⟨h4, ht, h5.le, fun hq => absurd hq.2 (not_lt.mpr hs)⟩


/-- **Payoff**: if the `A`-side (`A1`, `A2`) and the `B`-side (`BRest`, `BE0416`) are closed inside `OB1`
on `Hole24R`, then so are `BA4`, `CA`, `CA2` and `CFlip` (that is `CB` and `CC` with `a4 < 1`, `tau < 1`).
Remaining: `WallA5`; `CB`/`CC` with `a4 = 1`; `CC` with `a4 < 1`, `tau >= 1` (self-twin). -/
theorem hole24R_wlog
    (hA : ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24R x F → H24K.SAT.OB1 x →
      (A1 x F ∨ A2 x F) → IsRupert (univ.image x))
    (hB : ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), Hole24R x F → H24K.SAT.OB1 x →
      (BRest x F ∨ BE0416 x F) → IsRupert (univ.image x))
    (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F) (hO : H24K.SAT.OB1 x)
    (h : BA4 x F ∨ CA x F ∨ CA2 x F ∨ CFlip x F) : IsRupert (univ.image x) := by
  have hR' := hole24R_comp_pi24 hR
  have hO' := (ob1_comp_pi24 x).2 hO
  refine isRupert_of_comp_pi24 ?_
  rcases h with h | h | h | h
  · exact hA _ _ hR' hO' (ba4_to_a h)
  · exact hA _ _ hR' hO' (Or.inl (ca_to_a1 h))
  · exact hA _ _ hR' hO' (Or.inr (ca2_to_a2 h))
  · exact hB _ _ hR' hO' (Or.inl (cflip_to_brest h))

end Minimality.T24.Reg
