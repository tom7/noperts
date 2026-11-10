module

public import Minimality.Type16SAT.Cls16

@[expose] public section

/-!
# Type 16: the class `+---` with a nonzero shape entry of `Z` (case A for the shape zeros), from one core theorem

`ZShape16 y F`: the 18 shape entries of the stratum `Z` vanish: the seven brackets
`[0 1 5 | 3 6]`, `[0 1 6 | 3 5]`, `[1 2 5 | 3 6]`, `[1 2 6 | 3 5]`, `[2 3 6 | 1 5]`, `[3 4 6 | 1 5]`, `[3 4 5 | 1 6]`
(`det3 (y b - y a) (y c - y a) (y p - y q)`), the two mixed products `det3 (d15) (d36) (N B)`, `det3 (d16) (d35) (N B)`, the eight facet
equations `<N A, y1 - y6>`, `<N D, y1 - y4>`, `<N D, y1 - y5>`, `<N D, y4 - y5>`, `<N F, y0 - y3>`, `<N F, y0 - y6>`, `<N F, y3 - y6>`,
`<N G, y3 - y5>` (facets `A .. H = 0 .. 7`), and the determinant of the normals `N C`, `N D`, `N F`.
`Core16Z e1 e2 e3 e4` is the shape of a core theorem for the class with the signs `e1 .. e4` of the four brackets on `0 < C`
and `¬ ZShape16`.  `isRupert_cls16Z_of`: if `Core16Z 1 (-1) (-1) (-1)` holds, the class `+---` with some entry of `Z` nonzero,
or the class `----` with some entry nonzero for `x ∘ sigma16`, is Rupert.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The 18 shape entries of `Z` vanish (`F.N t` the normal of facet `t`). -/
def ZShape16 (y : Fin 7 → ℝ³) (F : S0xFac 8 Minimality.V2.fIdx y) : Prop :=
  det3 (y 1 - y 0) (y 5 - y 0) (y 3 - y 6) = 0 ∧ det3 (y 1 - y 0) (y 6 - y 0) (y 3 - y 5) = 0 ∧
  det3 (y 1 - y 5) (y 3 - y 6) (F.N 1) = 0 ∧ det3 (y 1 - y 6) (y 3 - y 5) (F.N 1) = 0 ∧
  ⟪F.N 0, y 1 - y 6⟫ = 0 ∧ ⟪F.N 3, y 1 - y 4⟫ = 0 ∧ ⟪F.N 3, y 1 - y 5⟫ = 0 ∧ ⟪F.N 3, y 4 - y 5⟫ = 0 ∧
  ⟪F.N 5, y 0 - y 3⟫ = 0 ∧ ⟪F.N 5, y 0 - y 6⟫ = 0 ∧
  det3 (y 2 - y 1) (y 5 - y 1) (y 3 - y 6) = 0 ∧ det3 (y 2 - y 1) (y 6 - y 1) (y 3 - y 5) = 0 ∧
  ⟪F.N 5, y 3 - y 6⟫ = 0 ∧ ⟪F.N 6, y 3 - y 5⟫ = 0 ∧
  det3 (y 3 - y 2) (y 6 - y 2) (y 1 - y 5) = 0 ∧ det3 (y 4 - y 3) (y 6 - y 3) (y 1 - y 5) = 0 ∧
  det3 (y 4 - y 3) (y 5 - y 3) (y 1 - y 6) = 0 ∧ det3 (F.N 2) (F.N 3) (F.N 5) = 0

/-- The mirror image has the same zero entries. -/
theorem zShape16_mir (y : Fin 7 → ℝ³) (F : S0xFac 8 Minimality.V2.fIdx y) :
    ZShape16 (fun i => mir (y i)) (mirFac F) ↔ ZShape16 y F := by
  simp only [ZShape16, mirFac, ← mir_sub, mir_det3, mir_inner, neg_eq_zero]

/-- The shape of a core theorem for the class with signs `e1 e2 e3 e4 = ±1` of the four brackets on `0 < C`, with the
case hypothesis that some entry of `Z` is nonzero. -/
def Core16Z (e1 e2 e3 e4 : ℝ) : Prop :=
  ∀ {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y), 0 < C16 y →
    0 < e1 * br16 y 0 1 2 6 → 0 < e2 * br16 y 0 1 3 4 → 0 < e3 * br16 y 1 2 3 4 → 0 < e4 * br16 y 2 3 4 6 →
    ¬ ZShape16 y F → IsRupert (univ.image y)

/-- Both chiralities. -/
theorem rupert_of_core_bothZ {e1 e2 e3 e4 : ℝ} (hcore : Core16Z e1 e2 e3 e4)
    {y : Fin 7 → ℝ³} (F : S0xFac 8 Minimality.V2.fIdx y) (hC : C16 y ≠ 0)
    (h1 : 0 < e1 * (C16 y * br16 y 0 1 2 6)) (h2 : 0 < e2 * (C16 y * br16 y 0 1 3 4))
    (h3 : 0 < e3 * (C16 y * br16 y 1 2 3 4)) (h4 : 0 < e4 * (C16 y * br16 y 2 3 4 6))
    (hA : ¬ ZShape16 y F) : IsRupert (univ.image y) := by
  rcases lt_or_gt_of_ne hC with hn | hp
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ ?_ (fun h => hA ((zShape16_mir y F).1 h)))
    · rw [C16_mir]; linarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
    · rw [br16_mir]; nlinarith
  · exact hcore F hp (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) hA

/-- **Type 16, class `+---` (and `----`) with a nonzero entry of `Z`, from the core theorem.**  `hF`, `hF'` are the facet
families of `x` and of `x ∘ sigma16` (any, e.g. `h16g_fac T` and `h16g_fac T.sigma`). -/
theorem isRupert_cls16Z_of (hP : Core16Z 1 (-1) (-1) (-1))
    {x : Fin 7 → ℝ³} (T : Type16 x) (F : S0xFac 8 Minimality.V2.fIdx x)
    (F' : S0xFac 8 Minimality.V2.fIdx (x ∘ sigma16))
    (h : (0 < C16 x * br16 x 0 1 2 6 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ C16 x * br16 x 1 2 3 4 < 0 ∧
        C16 x * br16 x 2 3 4 6 < 0 ∧ ¬ ZShape16 x F) ∨
      (C16 x * br16 x 0 1 2 6 < 0 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ C16 x * br16 x 1 2 3 4 < 0 ∧
        C16 x * br16 x 2 3 4 6 < 0 ∧ ¬ ZShape16 (x ∘ sigma16) F')) : IsRupert (univ.image x) := by
  have hne : C16 x ≠ 0 := T.det_ne
  have hne' : C16 (x ∘ sigma16) ≠ 0 := T.sigma.det_ne
  have e1 := C16_sigma x
  have e2 := b1_sigma x
  have e3 := b2_sigma x
  have e4 := b3_sigma x
  have e5 := b4_sigma x
  rcases h with ⟨h1, h2, h3, h4, hA⟩ | ⟨h1, h2, h3, h4, hA⟩
  · exact rupert_of_core_bothZ hP F hne (by linarith) (by linarith) (by linarith) (by linarith) hA
  · have := rupert_of_core_bothZ hP F' hne' (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith) hA
    rwa [Minimality.image_sigma16] at this

end Minimality.H16.SAT
