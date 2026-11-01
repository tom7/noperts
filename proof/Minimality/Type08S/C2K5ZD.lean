module

public import Minimality.Type08S.C2K5ZC
public import Minimality.Type08S.C2K5DM
public import Minimality.Type08S.C2K5AG

@[expose] public section


/-!
# K5Z / D: the planar residual `ResidP6` split into the K5 sub-items; `Resid08FinalK10`

In one labelling with a `Norm08w` structure `W`, `ResP = LeftTT ∨ (κ_a = 0 ∧ ParEnd)` and some equator is
planar (`PlanarEq`, from `PlanarTwo ∨ PlanarGen` of `Resid08FinalK9`, invariant under the labellings).  Split:
* `LeftTT` (`T ∨ T'`; the HDN / `TouchT` part is used only for QTouch):
  `T ∩ T'` → QTT; `T`, not `T'`: `κ_a = 0` → QTouch on `TouchT`, else QTa (boxes A–E); `κ_c = 0` → QTc;
  `κ_b = 0` is impossible (it forces `T'`);  `T'`, not `T`: `κ_a = 0` → QPa, `κ_c = 0` → QPc, `κ_b = 0` impossible.
  The far ends are strict off `T ∩ T'` (`k5z_far1`, `k5z_far2`), `κ_b > 0` at `T` off `T'` (`k5z_kb_pos`).
* `κ_a = 0 ∧ ParEnd`: `ParEndN2` → QN2, `ParEndKb` → QCEb (both K5b, hypotheses `K5ZbHyp`), `ParEndK2` → QCE2.
  QCEb and QCE2 need the strict T4 region `RegT4 W.F`, which `ResP` does not record: its failure is a leftover.

Every branch not closed is a named slice predicate (`K5Zs*`); `K5ZSlice W` is their disjunction.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ## The K5b wrappers (to be supplied when K5b lands) -/

/-- **The two K5b cell lemmas**, as hypotheses (package K5b, QN2 and QCEb at the view `b - c`).
`qn2`: `κ_a = 0`, `ParEndN2`, `ρ_a = ⟪a - d, b - c⟫ ≠ 0`.  `qceb`: `κ_a = 0`, `ParEndKb`, the two T4 far ends
(`RegT4 W.F`), `ρ_a ≠ 0` and `ζ(a,c') = ⟪a - c', b - c⟫ ≠ 0`. -/
structure K5ZbHyp : Prop where
  qn2 : ∀ {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d),
    det3 (c - b) (b' - b) (c' - b) = 0 → ParEndN2 a a' b b' c c' → ⟪a - d, b - c⟫ ≠ 0 →
      HasLexCell (V8 a a' b b' c c' d)
  qceb : ∀ {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d),
    det3 (c - b) (b' - b) (c' - b) = 0 → ParEndKb b b' c c' d →
      W.F.abc'.f c < W.F.abc'.f a' → W.F.a'bc.f c' < W.F.a'bc.f a →
      ⟪a - d, b - c⟫ ≠ 0 → ⟪a - c', b - c⟫ ≠ 0 → HasLexCell (V8 a a' b b' c c' d)

/-! ## The leftover slices (one labelling; all codim 4 in the item, except `¬ RegT4` in `K5ZsCE2`, `K5ZsCEb`)

Notation: `κ_a = 0` is `det3 (c - b) (b' - b) (c' - b) = 0`, `κ_c = 0` is `det3 (b - a) (a' - a) (b' - a) = 0`;
in the W0 frame (`Δ = det3 (a - d) (b - d) (c - d) ≠ 0`) `β1 = 1 ⇔ det3 (a - d) (c' - b) (c - d) = 0`,
`α4 = 1 ⇔ det3 (b' - a) (b - d) (c - d) = 0`, `β6 = 1 ⇔ det3 (a' - b) (c - d) (a - d) = 0` (at `T`). -/

/-- QTT (`T ∩ T'`, view `d - b`): one of the three ties `ζ(a,b')`, `ζ(b',a')`, `ζ(a,d)`. -/
def K5ZsTT (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ IsT' a b c' d ∧
    (⟪a - b', d - b⟫ = 0 ∨ ⟪b' - a', d - b⟫ = 0 ∨ ⟪a - d, d - b⟫ = 0)

/-- QPa (`T'` off `T`, `κ_a = 0`, view `d - b`): `ζ(a,c) = 0`, `α4 = 1` or `ζ(b',c) = 0`. -/
def K5ZsPa (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ ¬ IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
    (⟪a - c, d - b⟫ = 0 ∨ det3 (b' - a) (b - d) (c - d) = 0 ∨ ⟪b' - c, d - b⟫ = 0)

/-- QPc (`T'` off `T`, `κ_c = 0`): `α4 = 1`. -/
def K5ZsPc (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ ¬ IsT a' b c d ∧ det3 (b - a) (a' - a) (b' - a) = 0 ∧
    det3 (b' - a) (b - d) (c - d) = 0

/-- QTouch (`T` off `T'`, `κ_a = 0`, `TouchT`): `β1 = 1`. -/
def K5ZsTouch (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ ¬ IsT' a b c' d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧ TouchT b b' c c' d ∧
    det3 (a - d) (c' - b) (c - d) = 0

/-- QTa (`T` off `T'`, `κ_a = 0`, not `TouchT`): `β1 = 1`, `α4 = 1`, `β6 = 1`, `D_c = ⟪b - d, c - d⟫ = 0`,
`D_c < 0 ∧ ζ_C = ⟪c' - a, c - d⟫ = 0`, `ζ_E = ⟪b - a', a - c'⟫ = 0` or `ζ_D = ⟪d - b, a - b'⟫ = 0`. -/
def K5ZsTa (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ ¬ IsT' a b c' d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧ ¬ TouchT b b' c c' d ∧
    (det3 (a - d) (c' - b) (c - d) = 0 ∨ det3 (b' - a) (b - d) (c - d) = 0 ∨
      det3 (a' - b) (c - d) (a - d) = 0 ∨ ⟪b - d, c - d⟫ = 0 ∨
      (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ = 0) ∨ ⟪b - a', a - c'⟫ = 0 ∨ ⟪d - b, a - b'⟫ = 0)

/-- QTc (`T` off `T'`, `κ_c = 0`, view `a - b'`): `α4 = 1` or `ζ(d,b) = ⟪d - b, a - b'⟫ = 0`. -/
def K5ZsTc (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ ¬ IsT' a b c' d ∧ det3 (b - a) (a' - a) (b' - a) = 0 ∧
    (det3 (b' - a) (b - d) (c - d) = 0 ∨ ⟪d - b, a - b'⟫ = 0)

/-- QN2 (`κ_a = 0`, `ParEndN2`, view `b - c`): `ρ_a = ⟪a - d, b - c⟫ = 0`. -/
def K5ZsN2 (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndN2 a a' b b' c c' ∧ ⟪a - d, b - c⟫ = 0

/-- QCEb (`κ_a = 0`, `ParEndKb`, view `b - c`): outside the strict T4 region (**codim 3**, not recorded by
`ResP`), or `ρ_a = 0`, or `ζ(a,c') = ⟪a - c', b - c⟫ = 0`. -/
def K5ZsCEb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndKb b b' c c' d ∧
    (¬ RegT4 W.F ∨ ⟪a - d, b - c⟫ = 0 ∨ ⟪a - c', b - c⟫ = 0)

/-- QCE2 (`κ_a = 0`, `ParEndK2`, view `a - d`): outside the strict T4 region (**codim 3**), or
`ζ(b,c) = ⟪b - c, a - d⟫ = 0`. -/
def K5ZsCE2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndK2 b b' c c' d ∧
    (¬ RegT4 W.F ∨ ⟪b - c, a - d⟫ = 0)

/-- **The K5 leftover in one labelling**: one of the named slices. -/
def K5ZSlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K5ZsTT a a' b b' c c' d ∨ K5ZsPa a a' b b' c c' d ∨ K5ZsPc a a' b b' c c' d ∨
  K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d ∨ K5ZsTc a a' b b' c c' d ∨
  K5ZsN2 a a' b b' c c' d ∨ K5ZsCEb W ∨ K5ZsCE2 W

/-! ## The split in one labelling -/

open C2 in
theorem k5z_resP_split (H : K5ZbHyp) {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hpl : PlanarEq a a' b b' c c') (h : ResP a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K5ZSlice W := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, -⟩ := norm08w_coords W
  have hne : ∀ {x : ℝ}, x ≠ 0 → x * det3 (a - d) (b - d) (c - d) ≠ 0 := fun hx => mul_ne_zero hx hdet
  rcases h with ⟨hTT, -⟩ | ⟨hκ, hpe⟩
  · by_cases hT : IsT a' b c d
    · by_cases hT' : IsT' a b c' d
      · -- QTT
        by_cases hs : ⟪a - b', d - b⟫ = 0 ∨ ⟪b' - a', d - b⟫ = 0 ∨ ⟪a - d, d - b⟫ = 0
        · exact Or.inr (Or.inl ⟨hT, hT', hs⟩)
        · push Not at hs
          exact Or.inl (k5d_qtt_hasLexCell W hT hT' hs.1 hs.2.1 hs.2.2)
      · have hfar := k5z_far2 W hT hT'
        rcases hpl with hκa | hκb | hκc
        · by_cases hTo : TouchT b b' c c' d
          · -- QTouch
            by_cases hβ : det3 (a - d) (c' - b) (c - d) = 0
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, hT', hκa, hTo, hβ⟩))))
            · left
              rcases lt_or_gt_of_ne (hne hβ) with h1 | h1
              · exact k5e_lt_hasLexCell W hT hκa h1
              · exact k5e_gt_hasLexCell W hT hκa h1 hfar hTo.1
          · -- QTa
            by_cases hs : det3 (a - d) (c' - b) (c - d) = 0 ∨ det3 (b' - a) (b - d) (c - d) = 0 ∨
                det3 (a' - b) (c - d) (a - d) = 0 ∨ ⟪b - d, c - d⟫ = 0 ∨
                (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ = 0) ∨ ⟪b - a', a - c'⟫ = 0 ∨
                ⟪d - b, a - b'⟫ = 0
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, hT', hκa, hTo, hs⟩)))))
            · simp only [not_or, not_and] at hs
              obtain ⟨h1, h4, h6, hD0, hC, hE, hDz⟩ := hs
              have hcase : 0 < ⟪b - d, c - d⟫ ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ ≠ 0) := by
                rcases lt_or_gt_of_ne hD0 with h0 | h0
                · exact Or.inr ⟨h0, hC h0⟩
                · exact Or.inl h0
              exact Or.inl (k5z_qta_hasLexCell W hT hκa hfar (hne h1) (hne h4) (hne h6) hcase hE hDz)
        · exact (hT' (k5z_kb0_T W hT hκb)).elim
        · -- QTc
          by_cases hs : det3 (b' - a) (b - d) (c - d) = 0 ∨ ⟪d - b, a - b'⟫ = 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT, hT', hκc, hs⟩))))))
          · push Not at hs
            left
            rcases lt_or_gt_of_ne (hne hs.1) with h4 | h4
            · exact k5c_qtc_lt_hasLexCell W hT hκc h4
            · exact k5c_qtc_gt_hasLexCell W hT hκc h4 hfar (k5z_kb_pos W hT hT') hs.2
    · have hT' : IsT' a b c' d := hTT.resolve_left hT
      have hfar := k5z_far1 W hT' hT
      rcases hpl with hκa | hκb | hκc
      · -- QPa
        by_cases hs : ⟪a - c, d - b⟫ = 0 ∨ det3 (b' - a) (b - d) (c - d) = 0 ∨ ⟪b' - c, d - b⟫ = 0
        · exact Or.inr (Or.inr (Or.inl ⟨hT', hT, hκa, hs⟩))
        · push Not at hs
          exact Or.inl (k5d_qpa_hasLexCell W hT' hκa hfar hs.1 (hne hs.2.1) hs.2.2)
      · exact (hT (k5z_kb0_Tp W hT' hκb)).elim
      · -- QPc
        by_cases hs : det3 (b' - a) (b - d) (c - d) = 0
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hT', hT, hκc, hs⟩)))
        · left
          rcases lt_or_gt_of_ne (hne hs) with h4 | h4
          · exact k5c_qpc_lt_hasLexCell W hT' hκc h4
          · exact k5c_qpc_gt_hasLexCell W hT' hfar h4
  · rcases hpe with hN2 | hKb | hK2
    · -- QN2
      by_cases hs : ⟪a - d, b - c⟫ = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hκ, hN2, hs⟩)))))))
      · exact Or.inl (H.qn2 W hκ hN2 hs)
    · -- QCEb
      by_cases hs : ¬ RegT4 W.F ∨ ⟪a - d, b - c⟫ = 0 ∨ ⟪a - c', b - c⟫ = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hκ, hKb, hs⟩))))))))
      · simp only [not_or, not_not] at hs
        obtain ⟨⟨hr1, hr2⟩, h1, h2⟩ := hs
        exact Or.inl (H.qceb W hκ hKb hr1 hr2 h1 h2)
    · -- QCE2
      by_cases hs : ¬ RegT4 W.F ∨ ⟪b - c, a - d⟫ = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hκ, hK2, hs⟩))))))))
      · simp only [not_or, not_not] at hs
        obtain ⟨⟨hr1, hr2⟩, h1⟩ := hs
        exact Or.inl (k5a_qce2_hasLexCell W hκ hK2 hr1 hr2 h1)

/-! ## The new residual -/

/-- The K5 leftover in one labelling (with its `Norm08w` structure and the `ResP` it came from). -/
def K5ZResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP a a' b b' c c' d ∧ K5ZSlice W

/-- The K5 leftover in one of the six labellings (same order as `ResidP6`). -/
def K5ZResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K5ZResidP a a' b b' c c' d ∨ K5ZResidP b b' a a' c c' d ∨ K5ZResidP a a' c c' b b' d ∨
  K5ZResidP c c' a a' b b' d ∨ K5ZResidP b b' c c' a a' d ∨ K5ZResidP c c' b b' a a' d

/-- **`Resid08FinalK10`**: `Resid08FinalK9` with `ResidP6` cut down to the K5 slices `K5ZResidP6`. -/
def Resid08FinalK10 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K5ZResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k5z_residP_step (H : K5ZbHyp) {p p' q q' r r' d : ℝ³} (hpl : PlanarEq p p' q q' r r')
    (h : ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K5ZResidP p p' q q' r r' d := by
  obtain ⟨W, hR⟩ := h
  rcases k5z_resP_split H W hpl hR with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK9_imp_K10 (H : K5ZbHyp) {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK9 a a' b b' c c' d) : Resid08FinalK10 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have P := C2.k5z_planarEq_of hpl
  obtain ⟨P2, P3, P4, P5, P6⟩ := C2.k5z_planarEq_perm P
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k5z_residP_step H P h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k5z_residP_step H P2 h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k5z_residP_step H P3 h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k5z_residP_step H P4 h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k5z_residP_step H P5 h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k5z_residP_step H P6 h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
