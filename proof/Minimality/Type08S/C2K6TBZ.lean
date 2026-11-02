module

public import Minimality.Type08S.C2K6TBO

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp

/-- **Leftover of QTT** (`ζ(X,Y) = ⟪X - Y, d - b⟫`, `γ4 - 1 = det3 (a-d)(b-d)(b'-c) / Δ`):
* `ζ(a,d) = 0 ∧ ζ(c,d) = 0` (5c with `a ≡ d ≡ c ≡ b'` in depth; codim 6);
* `ζ(b',a') = 0 ∧ ζ(a,b') > 0 ∧ γ4 ≤ 1` (5b, the part where no depth-only cell is available; the spec's rule
  puts `(c',b',c,d,b)` here, which is not valid on depth alone: it needs the hidden sample constraints). -/
def K6tLeftTT (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪a - d, d - b⟫ = 0 ∧ ⟪c - d, d - b⟫ = 0) ∨
  (⟪b' - a', d - b⟫ = 0 ∧ 0 < ⟪a - b', d - b⟫ ∧
    det3 (a - d) (b - d) (b' - c) * det3 (a - d) (b - d) (c - d) ≤ 0)

/-- **Leftover of QPa** (`α4 - 1 = det3 (b'-a)(b-d)(c-d) / Δ`, `β1 - 1 = det3 (a-d)(c'-b)(c-d) / Δ`), all with `β1 ≥ 1`
(`β1 < 1` is closed by the face `Q_bc`):
* `ζ(a,c) = 0 ∧ ζ(a,d) = 0` (6a with `a ≡ c ≡ d ≡ b'` in depth);
* `ζ(b',c) = 0 ∧ α4 < 1 ∧ (β1 = 1 ∨ ζ(a,d) ≥ 0)` (6b: `β1 = 1` is a codim-5 tie; `ζ(a,d) ≥ 0` needs the cell
  `(a,b',a',c')` at `b' - c`, not formalized);
* `α4 = 1 ∧ (β1 = 1 ∨ ζ(b',c) ≥ 0)` (6c: `β1 = 1` is a codim-5 tie; `ζ(b',c) ≥ 0` needs `(a,b',a',c')` at `b' - c`). -/
def K6tLeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  (⟪a - c, d - b⟫ = 0 ∧ ⟪a - d, d - b⟫ = 0) ∨
  (⟪b' - c, d - b⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
    0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ 0 ≤ ⟪a - d, d - b⟫)) ∨
  (det3 (b' - a) (b - d) (c - d) = 0 ∧ 0 ≤ det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
    (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ 0 ≤ ⟪b' - c, d - b⟫))

/-- **Leftover of QPc** (`α1 = α4 = β6 = 1`, view `c - a'`): the whole slice (not formalized; see HANDOFF). -/
def K6tLeftPc (a a' b b' c c' d : ℝ³) : Prop := K5ZsPc a a' b b' c c' d

open C2 in
/-- **QTT wrapper.** -/
theorem k6t2_TT {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsTT a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTT a a' b b' c c' d := by
  obtain ⟨hT, hT', hs⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, -⟩ :=
    norm08w_coordsTp W hT'
  by_cases hu : ⟪a - d, d - b⟫ = 0
  · by_cases ht : ⟪c - d, d - b⟫ = 0
    · exact Or.inr (Or.inl ⟨hu, ht⟩)
    · exact Or.inl (k6t2_tt5c W hT hT' hu ht)
  · by_cases hg : 0 < det3 (a - d) (b - d) (b' - c) * det3 (a - d) (b - d) (c - d)
    · by_cases h2 : ⟪b' - a', d - b⟫ = 0
      · exact Or.inl (k6t2_tt5b_gt W hT hT' h2 hg)
      · rcases hs with h1 | h2' | h3
        · exact Or.inl (k6t2_tt5a W hT hT' h1 hu)
        · exact (h2 h2').elim
        · exact (hu h3).elim
    · push Not at hg
      rcases hs with h1 | h2 | h3
      · exact Or.inl (k6t2_tt5a W hT hT' h1 hu)
      · rcases lt_trichotomy ⟪a - b', d - b⟫ 0 with hn | hz | hp
        · exact Or.inl (k6t2_tt5b_neg W hT hT' hn hu)
        · exact Or.inl (k6t2_tt5a W hT hT' hz hu)
        · exact Or.inr (Or.inr ⟨h2, hp, hg⟩)
      · exact (hu h3).elim

open C2 in
/-- **QPa wrapper.**  Extra hypothesis (not carried by `K5ZsPa`): `hfar : W.F.abc'.f c < W.F.abc'.f a'`. -/
theorem k6t2_Pa {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h : K5ZsPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftPa a a' b b' c c' d := by
  obtain ⟨hT', hnT, hκ, hs⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, -⟩ :=
    norm08w_coordsTp W hT'
  rcases lt_or_ge (det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d)) 0 with hb | hb
  · exact Or.inl (k6t2_pa_faceA W hT' hκ hb)
  · by_cases hα : det3 (b' - a) (b - d) (c - d) = 0
    · -- 6c (`α4 = 1`)
      rcases hb.lt_or_eq with hbp | hb0
      · by_cases hz : ⟪b' - c, d - b⟫ < 0
        · exact Or.inl (k6t2_pa_p4 W hT' hκ hfar hbp (Or.inl hz))
        · exact Or.inr (Or.inr (Or.inr ⟨hα, hb, Or.inr (not_lt.1 hz)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hα, hb, Or.inl hb0.symm⟩))
    · have hα' : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0 := mul_ne_zero hα hdet
      rcases hs with hac | hα1 | hbc
      · by_cases hu0 : ⟪a - d, d - b⟫ = 0
        · exact Or.inr (Or.inl ⟨hac, hu0⟩)
        · exact Or.inl (k6t2_pa6a W hT' hκ hfar hac hu0 hα')
      · exact (hα hα1).elim
      · rcases lt_or_gt_of_ne hα' with hn | hp
        · -- `α4 < 1`
          rcases hb.lt_or_eq with hbp | hb0
          · by_cases hu : ⟪a - d, d - b⟫ < 0
            · exact Or.inl (k6t2_pa_p4 W hT' hκ hfar hbp (Or.inr ⟨hbc, hu⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨hbc, hn, hb, Or.inr (not_lt.1 hu)⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hbc, hn, hb, Or.inl hb0.symm⟩))
        · exact Or.inl (k5c_qpc_gt_hasLexCell W hT' hfar hp)

/-- **QPc wrapper** (whole slice left). -/
theorem k6t2_Pc {a a' b b' c c' d : ℝ³} (h : K5ZsPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftPc a a' b b' c c' d := Or.inr h

end Type08Sp
end Minimality
