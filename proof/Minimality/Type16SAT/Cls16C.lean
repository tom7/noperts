module

public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16: the class `+---` with a nonzero inner product (case A), from one core theorem

`CaseT16 y`: the edge `y 1 - y 6` is not orthogonal to both `y 0 - y 3` and `y 0 - y 6` (inner products `T(d03, d16)`
and `T(d06, d16)` of the metric step, nonzero for at least one).  `Core16T e1 e2 e3 e4` is the shape of a core theorem
for the class with the signs `e1 .. e4` of the four brackets on `0 < C` and `CaseT16`.

`isRupert_cls16A_of`: if `Core16T 1 (-1) (-1) (-1)` holds, a type 16 shape of the class `+---` (strict signs of
`C * [0126]`, `C * [0134]`, `C * [1234]`, `C * [2346]`) with `CaseT16 x`, or of the class `----` with `CaseT16 (x ∘ sigma16)`
(the `sigma16` image of `+---`), is Rupert.  The class cores of `Cls16.lean` have no case hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Case A of the class `+---`: `x 1 - x 6` is not orthogonal to both `x 0 - x 3` and `x 0 - x 6`. -/
def CaseT16 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 0 - x 3, x 1 - x 6⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 1 - x 6⟫ ≠ 0

/-- The mirror image has the same inner products. -/
theorem caseT16_mir (y : Fin 7 → ℝ³) : CaseT16 (fun i => mir (y i)) ↔ CaseT16 y := by
  simp only [CaseT16, ← mir_sub, mir_inner]

/-- The shape of a core theorem for the class with signs `e1 e2 e3 e4 = ±1` of the four brackets on `0 < C`, with the
case hypothesis `CaseT16`. -/
def Core16T (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³}, S0xFac 8 Minimality.V2.fIdx y → 0 < C16 y →
    0 < e1 * br16 y 0 1 2 6 → 0 < e2 * br16 y 0 1 3 4 → 0 < e3 * br16 y 1 2 3 4 → 0 < e4 * br16 y 2 3 4 6 →
    CaseT16 y → IsRupert (univ.image y)

/-- Both chiralities: a core for `0 < C` closes the class in the form of strict signs of the products `C * bracket`. -/
theorem rupert_of_core_bothT {e1 e2 e3 e4 : ℝ} (hcore : Core16T e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0)
    (h1 : 0 < e1 * (C16 y * br16 y 0 1 2 6)) (h2 : 0 < e2 * (C16 y * br16 y 0 1 3 4))
    (h3 : 0 < e3 * (C16 y * br16 y 1 2 3 4)) (h4 : 0 < e4 * (C16 y * br16 y 2 3 4 6))
    (hA : CaseT16 y) : IsRupert (univ.image y) := by
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ ((caseT16_mir y).2 hA))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
  · exact hcore F hp (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) hA

/-- The class `+---` with case A, and its `sigma16` image `----` with case A on `x ∘ sigma16`
(`CaseA16 x`: the strict signs of `C * [0126]`, `C * [0134]`, `C * [1234]`, `C * [2346]` are `+---` and `CaseT16 x`,
or `----` and `CaseT16 (x ∘ sigma16)`). -/
def Cls16A (x : Fin 7 → ℝ³) : Prop :=
  let C := C16 x
  let b1 := br16 x 0 1 2 6
  let b2 := br16 x 0 1 3 4
  let b3 := br16 x 1 2 3 4
  let b4 := br16 x 2 3 4 6
  (0 < C * b1 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0 ∧ CaseT16 x) ∨
  (C * b1 < 0 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0 ∧ CaseT16 (x ∘ sigma16))

/-- **Type 16, class `+---` (and `----`) with case A, from the core theorem.** -/
theorem isRupert_cls16A_of (hP : Core16T 1 (-1) (-1) (-1))
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16A x) : IsRupert (univ.image x) := by
  have hne : C16 x ≠ 0 := T.det_ne
  have hne' : C16 (x ∘ sigma16) ≠ 0 := T.sigma.det_ne
  have F := Minimality.H16A.h16g_fac T
  have F' := Minimality.H16A.h16g_fac T.sigma
  have e1 := C16_sigma x
  have e2 := b1_sigma x
  have e3 := b2_sigma x
  have e4 := b3_sigma x
  have e5 := b4_sigma x
  simp only [Cls16A] at h
  rcases h with ⟨h1, h2, h3, h4, hA⟩ | ⟨h1, h2, h3, h4, hA⟩
  · exact rupert_of_core_bothT hP F hne (by linarith) (by linarith) (by linarith) (by linarith) hA
  · have := rupert_of_core_bothT hP F' hne' (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith) hA
    rwa [Minimality.image_sigma16] at this

end Minimality.H16.SAT
