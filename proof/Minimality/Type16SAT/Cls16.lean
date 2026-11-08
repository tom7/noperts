module

public import Minimality.Type16GenA
public import Minimality.Type16NF
public import Minimality.Type16M
public import Minimality.Type29SAT.Mir
public import Minimality.Type29SAT.Ent2
public import Minimality.Type29SAT.Nf

@[expose] public section

/-!
# Type 16: the closed classes (J9; renamed from Final.lean to Cls16.lean in J8)

`Cls16Closed x`: the strict sign vector `(sign C[0126], sign C[0134], sign C[1234], sign C[2346])` (C = `[3056]`, the
chirality bracket) is one of `++-+`, `++--`, `+--+` (the three class cores) or their `sigma16` images `-+-+`, `---+`, `-+--`.
`isRupert_cls3_of` takes the three core theorems (`rupert_of_core<K>`, for `S0xFac 8 V2.fIdx y` with `0 < C y` and the four signs)
as hypotheses.  The bracket rule under `sigma16`: `C' = -C`, `[0126]' = [0126]`, `[0134]' = -[2346]`, `[1234]' = -[1234]`,
`[2346]' = -[0134]`, so `s' = (-s1, s4, s3, s2)`.  The three core theorems are applied in `Final.lean` (J8).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The bracket `[a b c d] = det3 (y b - y a) (y c - y a) (y d - y a)`. -/
noncomputable def br16 (y : Fin 7 → ℝ³) (a b c d : Fin 7) : ℝ :=
  det3 (y b - y a) (y c - y a) (y d - y a)

/-- The chirality bracket `[3056]`. -/
noncomputable def C16 (y : Fin 7 → ℝ³) : ℝ := br16 y 3 0 5 6

theorem C16_sigma (y : Fin 7 → ℝ³) : C16 (y ∘ sigma16) = - C16 y := by
  simp only [C16, br16, det3_expand, Function.comp, sigma16, PiLp.sub_apply]
  simp [Matrix.cons_val]
  ring

theorem b1_sigma (y : Fin 7 → ℝ³) : br16 (y ∘ sigma16) 0 1 2 6 = br16 y 0 1 2 6 := by
  simp only [br16, det3_expand, Function.comp, sigma16, PiLp.sub_apply]
  simp [Matrix.cons_val]
  ring

theorem b2_sigma (y : Fin 7 → ℝ³) : br16 (y ∘ sigma16) 0 1 3 4 = - br16 y 2 3 4 6 := by
  simp only [br16, det3_expand, Function.comp, sigma16, PiLp.sub_apply]
  simp [Matrix.cons_val]
  ring

theorem b3_sigma (y : Fin 7 → ℝ³) : br16 (y ∘ sigma16) 1 2 3 4 = - br16 y 1 2 3 4 := by
  simp only [br16, det3_expand, Function.comp, sigma16, PiLp.sub_apply]
  simp [Matrix.cons_val]
  ring

theorem b4_sigma (y : Fin 7 → ℝ³) : br16 (y ∘ sigma16) 2 3 4 6 = - br16 y 0 1 3 4 := by
  simp only [br16, det3_expand, Function.comp, sigma16, PiLp.sub_apply]
  simp [Matrix.cons_val]
  ring

theorem C16_mir (y : Fin 7 → ℝ³) : C16 (fun i => mir (y i)) = - C16 y := mir_br _ _ _ _
theorem br16_mir (y : Fin 7 → ℝ³) (a b c d : Fin 7) :
    br16 (fun i => mir (y i)) a b c d = - br16 y a b c d := mir_br _ _ _ _

/-- **Closed classes**: the strict class vector `(C[0126], C[0134], C[1234], C[2346])` has the signs of one of
`++-+`, `++--`, `+--+`, `-+-+`, `---+`, `-+--`. -/
def Cls16Closed (x : Fin 7 → ℝ³) : Prop :=
  let C := C16 x
  let b1 := br16 x 0 1 2 6
  let b2 := br16 x 0 1 3 4
  let b3 := br16 x 1 2 3 4
  let b4 := br16 x 2 3 4 6
  (0 < C * b1 ∧ 0 < C * b2 ∧ C * b3 < 0 ∧ 0 < C * b4) ∨
  (0 < C * b1 ∧ 0 < C * b2 ∧ C * b3 < 0 ∧ C * b4 < 0) ∨
  (0 < C * b1 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ 0 < C * b4) ∨
  (C * b1 < 0 ∧ 0 < C * b2 ∧ C * b3 < 0 ∧ 0 < C * b4) ∨
  (C * b1 < 0 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ 0 < C * b4) ∨
  (C * b1 < 0 ∧ 0 < C * b2 ∧ C * b3 < 0 ∧ C * b4 < 0)

/-- The shape of a core theorem for the class with signs `e1 e2 e3 e4 = ±1` of the four brackets, on `0 < C`
(`rupert_of_core<K>` has this shape; `e = (1,1,-1,1)` for `++-+`, `(1,1,-1,-1)` for `++--`, `(1,-1,-1,1)` for `+--+`). -/
def Core16 (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³}, S0xFac 8 Minimality.V2.fIdx y → 0 < C16 y →
    0 < e1 * br16 y 0 1 2 6 → 0 < e2 * br16 y 0 1 3 4 → 0 < e3 * br16 y 1 2 3 4 → 0 < e4 * br16 y 2 3 4 6 →
    IsRupert (univ.image y)

/-- Both chiralities: a core for `0 < C` closes the class in the form of strict signs of the products `C * bracket`. -/
theorem rupert_of_core_both {e1 e2 e3 e4 : ℝ} (hcore : Core16 e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0)
    (h1 : 0 < e1 * (C16 y * br16 y 0 1 2 6)) (h2 : 0 < e2 * (C16 y * br16 y 0 1 3 4))
    (h3 : 0 < e3 * (C16 y * br16 y 1 2 3 4)) (h4 : 0 < e4 * (C16 y * br16 y 2 3 4 6)) :
    IsRupert (univ.image y) := by
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_)
    · rw [C16_mir]; linarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
  · exact hcore F hp (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- **Type 16, the three closed classes and their sigma images, from the three core theorems** (the hypothesis-free form is
`isRupert_cls3` in `Final.lean`). -/
theorem isRupert_cls3_of
    (hA : Core16 1 1 (-1) 1) (hB : Core16 1 1 (-1) (-1)) (hC : Core16 1 (-1) (-1) 1)
    {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Closed x) : IsRupert (univ.image x) := by
  have hne : C16 x ≠ 0 := T.det_ne
  have hne' : C16 (x ∘ sigma16) ≠ 0 := T.sigma.det_ne
  have F := Minimality.H16A.h16g_fac T
  have F' := Minimality.H16A.h16g_fac T.sigma
  have e1 := C16_sigma x
  have e2 := b1_sigma x
  have e3 := b2_sigma x
  have e4 := b3_sigma x
  have e5 := b4_sigma x
  simp only [Cls16Closed] at h
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact rupert_of_core_both hA F hne (by linarith) (by linarith) (by linarith) (by linarith)
  · exact rupert_of_core_both hB F hne (by linarith) (by linarith) (by linarith) (by linarith)
  · exact rupert_of_core_both hC F hne (by linarith) (by linarith) (by linarith) (by linarith)
  · have := rupert_of_core_both hA F' hne' (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith)
    rwa [Minimality.image_sigma16] at this
  · have := rupert_of_core_both hB F' hne' (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith)
    rwa [Minimality.image_sigma16] at this
  · have := rupert_of_core_both hC F' hne' (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith)
    rwa [Minimality.image_sigma16] at this

end Minimality.H16.SAT
