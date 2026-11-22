module

public import Minimality.Type24Hole
public import Minimality.M4bType24
public import Minimality.M4Type24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT

/-!
# Type 24: the region skeleton of `Hole24R`

Every region predicate is stated in the frame functions of the tree (`oblX0`, `oblX2`, `oblX6`, `nC`) and in the
facet functionals of `F` (`F.f 8` = facet 346 gives sigma, `F.f 6` = facet 235 gives tau), so no existential
decomposition is needed.  `hole24R_cases` is proved by trichotomies only.  No region is claimed closed.
-/

namespace Minimality.T24.Reg

open Minimality.T24 Minimality.T24.A7

/-! ### Region predicates -/

/-- Off-OB1 region: exactly the hypotheses of S7 `offOB1_closed` beyond `Hole24R` (`CbarIn`, `not LexAny`):
frame forms of `b1234 < 0 < b1356, b1456`, and `a4 < 1 or a5 < 1`, off `OB1`. -/
def ROff (x : Fin 7 → ℝ³) : Prop :=
  ¬ H24K.SAT.OB1 x ∧
    oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 ∧
    0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 ∧
    0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 ∧
    (oblX0 x 4 < 1 ∨ oblX0 x 5 < 1)

/-- Off `OB1` with `a4 >= 1` and `a5 >= 1` (the complement of S7's last hypothesis). -/
def OffWall (x : Fin 7 → ℝ³) : Prop :=
  ¬ H24K.SAT.OB1 x ∧ 1 ≤ oblX0 x 4 ∧ 1 ≤ oblX0 x 5

/-- A1: `a5 > 1`, `sigma <= 1` (in the `h346` form `f8(x0) <= f8(x5)`, A1PLAN section 1). -/
def A1 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  1 < oblX0 x 5 ∧ F.f 8 (x 0) ≤ F.f 8 (x 5)

/-- A2: `a5 > 1`, `sigma > 1`. -/
def A2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  1 < oblX0 x 5 ∧ F.f 8 (x 5) < F.f 8 (x 0)

/-- The wall `a5 = 1` (in no region of A10). -/
def WallA5 (x : Fin 7 → ℝ³) : Prop := oblX0 x 5 = 1

/-- B-a4>1: `a5 < 1`, `sigma < 1`, `a4 > 1`. -/
def BA4 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 0) < F.f 8 (x 5) ∧ 1 < oblX0 x 4

/-- B-E0416: `a5 < 1`, `sigma < 1`, `a4 <= 1`, `nC < 0`, `tau < 1` (`tau < 1` iff `f6(x0) < f6(x4)`). -/
def BE0416 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 0) < F.f 8 (x 5) ∧ oblX0 x 4 ≤ 1 ∧ nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4)

/-- B-rest: `a5 < 1`, `sigma < 1`, `a4 <= 1`, not (`nC < 0` and `tau < 1`). -/
def BRest (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 0) < F.f 8 (x 5) ∧ oblX0 x 4 ≤ 1 ∧
    ¬ (nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4))

/-- C_a: `a5 < 1`, `sigma >= 1`, `a4 > 1`, `tau <= 1` (`tau <= 1` iff `f6(x0) <= f6(x4)`). -/
def CA (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ 1 < oblX0 x 4 ∧ F.f 6 (x 0) ≤ F.f 6 (x 4)

/-- C_a2: `a5 < 1`, `sigma >= 1`, `a4 > 1`, `tau > 1`. -/
def CA2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ 1 < oblX0 x 4 ∧ F.f 6 (x 4) < F.f 6 (x 0)

/-- C_b: `a5 < 1`, `sigma >= 1`, `a4 <= 1`, `nC < 0`, `tau < 1`. -/
def CB (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ oblX0 x 4 ≤ 1 ∧ nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4)

/-- C_c: the rest of `a5 < 1`, `sigma >= 1`. -/
def CC (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ oblX0 x 4 ≤ 1 ∧
    ¬ (nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4))

/-! ### sigma and tau in the `h`-forms -/

/-- `sigma` against `1` through facet 346: `(s - 1) * (-f8 x0) = t * (f8 x0 - f8 x5)`. -/
theorem sigma_cmp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (ht : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    (s < 1 ↔ F.f 8 (x 0) < F.f 8 (x 5)) ∧ (s = 1 ↔ F.f 8 (x 0) = F.f 8 (x 5)) ∧
      (1 < s ↔ F.f 8 (x 5) < F.f 8 (x 0)) := by
  have ev8 := congrArg (fun v => ⟪F.N 8, v⟫) hdec
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← F.hN 8 (x 3) (x 0), ← F.hN 8 (x 4) (x 0), ← F.hN 8 (x 5) (x 0),
    F.zero 8 3 (by decide), F.zero 8 4 (by decide), zero_sub] at ev8
  have hmul : (s - 1) * (-F.f 8 (x 0)) = t * (F.f 8 (x 0) - F.f 8 (x 5)) := by linarith
  have h80 : 0 < -F.f 8 (x 0) := neg_pos.mpr (F.neg 8 0 (by decide))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hc), mul_pos (sub_pos.mpr h) h80]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg h80.le (sub_nonneg.mpr hc), mul_pos ht (sub_pos.mpr h)]
  · subst h; have : t * (F.f 8 (x 0) - F.f 8 (x 5)) = 0 := by rw [← hmul]; ring
    rcases mul_eq_zero.mp this with h | h <;> [exact absurd h ht.ne'; linarith]
  · have : (s - 1) * (-F.f 8 (x 0)) = 0 := by rw [hmul, h]; ring
    rcases mul_eq_zero.mp this with h | h <;> [linarith; exact absurd h h80.ne']
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hc), mul_pos (sub_pos.mpr h) h80]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg h80.le (sub_nonneg.mpr hc), mul_pos ht (sub_pos.mpr h)]

/-- `tau` against `1` through facet 235: `(t - 1) * (-f6 x0) = s * (f6 x0 - f6 x4)`. -/
theorem tau_cmp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : 0 < s)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    (t < 1 ↔ F.f 6 (x 0) < F.f 6 (x 4)) ∧ (1 < t ↔ F.f 6 (x 4) < F.f 6 (x 0)) := by
  have ev := congrArg (fun v => ⟪F.N 6, v⟫) hdec
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← F.hN 6 (x 3) (x 0), ← F.hN 6 (x 4) (x 0), ← F.hN 6 (x 5) (x 0),
    F.zero 6 3 (by decide), F.zero 6 5 (by decide), zero_sub] at ev
  have hmul : (t - 1) * (-F.f 6 (x 0)) = s * (F.f 6 (x 0) - F.f 6 (x 4)) := by linarith
  have h0 : 0 < -F.f 6 (x 0) := neg_pos.mpr (F.neg 6 0 (by decide))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hc), mul_pos (sub_pos.mpr h) h0]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hc), mul_pos hs (sub_pos.mpr h)]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hc), mul_pos (sub_pos.mpr h) h0]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hc), mul_pos hs (sub_pos.mpr h)]

/-! ### Bracket bridge: Resid24 off OB1 gives the three frame signs -/

theorem chi24_eq (x : Fin 7 → ℝ³) : chi24 x = - det24 x := by
  unfold chi24 det24 det3 vol3
  simp [Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Plucker-type identity behind the frame forms of the class brackets. -/
theorem plucker (A B C p q : ℝ³) :
    det3 B p q * vol3 A B C =
      vol3 q B C * vol3 A B p - vol3 p B C * vol3 A B q := by
  unfold det3 vol3
  simp [Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem plucker2 (A B C p q : ℝ³) :
    det3 p q C * vol3 A B C =
      vol3 p B C * vol3 A q C - vol3 q B C * vol3 A p C := by
  unfold det3 vol3
  simp [Minimality.cross, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem frame1234 {x : Fin 7 → ℝ³} (hD : det24 x ≠ 0) :
    oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 = b1234 x / det24 x := by
  have := plucker (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 3 - x 1) (x 4 - x 1)
  unfold oblX0 oblX6 b1234
  unfold det24 at hD ⊢
  rw [eq_div_iff hD]; field_simp
  linear_combination (-1 : ℝ) * this

theorem frame1356 {x : Fin 7 → ℝ³} (hD : det24 x ≠ 0) :
    oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 = b1356 x / det24 x := by
  have := plucker2 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 3 - x 1) (x 5 - x 1)
  unfold oblX0 oblX2 b1356
  unfold det24 at hD ⊢
  rw [eq_div_iff hD]; field_simp
  linear_combination (-1 : ℝ) * this

theorem frame1456 {x : Fin 7 → ℝ³} (hD : det24 x ≠ 0) :
    oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 = b1456 x / det24 x := by
  have := plucker2 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 4 - x 1) (x 5 - x 1)
  unfold oblX0 oblX2 b1456
  unfold det24 at hD ⊢
  rw [eq_div_iff hD]; field_simp
  linear_combination (-1 : ℝ) * this

/-- Every non-`OB1` disjunct of `Resid24` has the bracket signs `[1234] < 0 < [1356], [1456]` in the reference
orientation (`[0126] < 0`), or all reversed in the mirror. -/
theorem resid24_signs {x : Fin 7 → ℝ³} (h : Resid24 x) (hO : ¬ H24K.SAT.OB1 x) :
    (chi24 x < 0 ∧ b1234 x < 0 ∧ 0 < b1356 x ∧ 0 < b1456 x) ∨
      (0 < chi24 x ∧ 0 < b1234 x ∧ b1356 x < 0 ∧ b1456 x < 0) := by
  rcases h with h | h | h | h
  · exact absurd h hO
  · unfold ZRes24 clsz24 at h
    simp only [sgz, flipz, sg, Bool.not_true, Bool.not_false] at h
    rcases h with ⟨a, b, -, c, d, -⟩ | ⟨a, b, -, c, d, -⟩
    · exact Or.inl ⟨a, b, c, d⟩
    · exact Or.inr ⟨a, b, c, d⟩
  · unfold cls24 at h
    simp only [sg, Bool.not_true, Bool.not_false] at h
    rcases h with ⟨a, b, -, c, d, -⟩ | ⟨a, b, -, c, d, -⟩
    · exact Or.inl ⟨a, b, c, d⟩
    · exact Or.inr ⟨a, b, c, d⟩
  · unfold cls24 at h
    simp only [sg, Bool.not_true, Bool.not_false] at h
    rcases h with ⟨a, b, -, c, d, -⟩ | ⟨a, b, -, c, d, -⟩
    · exact Or.inl ⟨a, b, c, d⟩
    · exact Or.inr ⟨a, b, c, d⟩

/-- The three S7 frame signs hold on `Resid24` off `OB1`. -/
theorem resid24_frame_signs {x : Fin 7 → ℝ³} (h : Resid24 x) (hO : ¬ H24K.SAT.OB1 x) :
    oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 ∧
    0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 ∧
    0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 := by
  have hc := chi24_eq x
  rcases resid24_signs h hO with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · have hD : 0 < det24 x := by linarith
    rw [frame1234 hD.ne', frame1356 hD.ne', frame1456 hD.ne']
    exact ⟨div_neg_of_neg_of_pos b hD, div_pos c hD, div_pos d hD⟩
  · have hD : det24 x < 0 := by linarith
    rw [frame1234 hD.ne, frame1356 hD.ne, frame1456 hD.ne]
    exact ⟨div_neg_of_pos_of_neg b hD, div_pos_of_neg_of_neg c hD, div_pos_of_neg_of_neg d hD⟩

/-! ### The covering theorem -/

/-- The regions inside `OB1`, by trichotomies only (no hypothesis at all). -/
theorem frame_cases (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    A1 x F ∨ A2 x F ∨ WallA5 x ∨ BA4 x F ∨ BE0416 x F ∨ BRest x F ∨
      CA x F ∨ CA2 x F ∨ CB x F ∨ CC x F := by
  unfold A1 A2 WallA5 BA4 BE0416 BRest CA CA2 CB CC
  rcases lt_trichotomy (oblX0 x 5) 1 with h5 | h5 | h5
  · -- a5 < 1
    rcases lt_or_ge (F.f 8 (x 0)) (F.f 8 (x 5)) with hs | hs
    · rcases lt_or_ge 1 (oblX0 x 4) with h4 | h4
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, hs, h4⟩)))
      · by_cases hq : nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, hs, h4, hq⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, hs, h4, hq⟩)))))
    · rcases lt_or_ge 1 (oblX0 x 4) with h4 | h4
      · rcases le_or_gt (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, hs, h4, ht⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, hs, h4, ht⟩)))))))
      · by_cases hq : nC x < 0 ∧ F.f 6 (x 0) < F.f 6 (x 4)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨h5, hs, h4, hq⟩))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨h5, hs, h4, hq⟩))))))))
  · exact Or.inr (Or.inr (Or.inl h5))
  · rcases le_or_gt (F.f 8 (x 0)) (F.f 8 (x 5)) with hs | hs
    · exact Or.inl ⟨h5, hs⟩
    · exact Or.inr (Or.inl ⟨h5, hs⟩)

/-- **The region cover of `Hole24R`**: off `OB1` the point is in `ROff` or `OffWall`; inside `OB1` it is in one of
the ten regions. -/
theorem hole24R_cases {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) :
    ROff x ∨ OffWall x ∨
      (H24K.SAT.OB1 x ∧ (A1 x F ∨ A2 x F ∨ WallA5 x ∨ BA4 x F ∨ BE0416 x F ∨ BRest x F ∨
        CA x F ∨ CA2 x F ∨ CB x F ∨ CC x F)) := by
  by_cases hO : H24K.SAT.OB1 x
  · exact Or.inr (Or.inr ⟨hO, frame_cases x F⟩)
  · obtain ⟨h1, h2, h3⟩ := resid24_frame_signs hR.2.1 hO
    by_cases ha : oblX0 x 4 < 1 ∨ oblX0 x 5 < 1
    · exact Or.inl ⟨hO, h1, h2, h3, ha⟩
    · push Not at ha
      exact Or.inr (Or.inl ⟨hO, ha.1, ha.2⟩)

/-- The flat form: the plain region predicates (no `OB1`), `OffWall` kept as its own piece. -/
theorem hole24R_cases_flat {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) :
    ROff x ∨ OffWall x ∨ A1 x F ∨ A2 x F ∨ WallA5 x ∨ BA4 x F ∨ BE0416 x F ∨ BRest x F ∨
      CA x F ∨ CA2 x F ∨ CB x F ∨ CC x F := by
  rcases hole24R_cases hR with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ### `a4 > 1` and `a5 > 1` contradict `not Q45HalfPred` -/

/-- If `a4 > 1` and `a5 > 1` then `Q45HalfPred` holds (all three clauses of `Q45HalfHyp`, for every
decomposition).  So `Hole24R` forces `a4 <= 1` or `a5 <= 1`. -/
theorem q45HalfPred_of_gt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : 1 < oblX0 x 4) (ha5 : 1 < oblX0 x 5) : Q45HalfPred F := by
  intro s t hs ht _ hdec
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have e4 : F.f 5 (x 4) = oblX0 x 4 * F.f 5 (x 0) := by
    rw [Minimality.T24.M4.fac_eval F 5 4, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring
  have e5 : F.f 5 (x 5) = oblX0 x 5 * F.f 5 (x 0) := by
    rw [Minimality.T24.M4.fac_eval F 5 5, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring
  have g4 : F.f 5 (x 4) - F.f 5 (x 0) < 0 := by rw [e4]; nlinarith
  have g5 : F.f 5 (x 5) - F.f 5 (x 0) < 0 := by rw [e5]; nlinarith
  have ev := congrArg (fun v => ⟪F.N 5, v⟫) hdec
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← F.hN 5 (x 3) (x 0), ← F.hN 5 (x 4) (x 0), ← F.hN 5 (x 5) (x 0)] at ev
  have i40 : ⟪F.N 5, x 4 - x 0⟫ = F.f 5 (x 4) - F.f 5 (x 0) := (F.hN 5 _ _).symm
  have i50 : ⟪F.N 5, x 5 - x 0⟫ = F.f 5 (x 5) - F.f 5 (x 0) := (F.hN 5 _ _).symm
  have i34 : ⟪F.N 5, x 3 - x 4⟫ = F.f 5 (x 3) - F.f 5 (x 4) := (F.hN 5 _ _).symm
  have i35 : ⟪F.N 5, x 3 - x 5⟫ = F.f 5 (x 3) - F.f 5 (x 5) := (F.hN 5 _ _).symm
  refine ⟨fun _ => ⟨fun _ => ?_, fun h1 => ?_⟩, fun _ => ⟨fun _ => ?_, fun h1 => ?_⟩, fun _ => ⟨?_, ?_⟩⟩
  · rw [i50]; exact g5
  · rw [i34]; nlinarith [mul_pos (sub_pos.mpr h1) (neg_pos.mpr g4), mul_pos ht (neg_pos.mpr g5)]
  · rw [i40]; exact g4
  · rw [i35]; nlinarith [mul_pos (sub_pos.mpr h1) (neg_pos.mpr g5), mul_pos hs (neg_pos.mpr g4)]
  · rw [i40]; exact g4
  · rw [i50]; exact g5

/-- `Hole24R` excludes `a4 > 1 and a5 > 1`. -/
theorem hole24R_not_both_gt {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) :
    ¬ (1 < oblX0 x 4 ∧ 1 < oblX0 x 5) :=
  fun h => hR.2.2.1 (q45HalfPred_of_gt F h.1 h.2)

/-- On `Hole24R`, `OffWall` is confined to the walls `a4 = 1` or `a5 = 1`. -/
theorem offWall_wall {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) (h : OffWall x) :
    oblX0 x 4 = 1 ∨ oblX0 x 5 = 1 := by
  by_contra hc
  push Not at hc
  exact hole24R_not_both_gt hR ⟨lt_of_le_of_ne h.2.1 (Ne.symm hc.1), lt_of_le_of_ne h.2.2 (Ne.symm hc.2)⟩

end Minimality.T24.Reg
