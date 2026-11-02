module

public import Minimality.Type08S.C2K6MP

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Box boundaries of the K6M split (`σ = β6 + γ6`), all of codimension at least 5 in the item. -/
def K6mBoundary (α1 β1 β6 γ6 : ℝ) : Prop :=
  β1 = 1 ∨ (1 < β1 ∧ β6 + γ6 = β1) ∨ (1 < β1 ∧ β1 < β6 + γ6 ∧ α1 = 1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ (β6 = 1 ∨ γ6 = 1))

/-- Literal ties of H2 (`ζ_{a-b'}(c, a') = 0`) and of H4 (`ζ_{a-c'}(b, a') = 0`). -/
def K6mTie (a a' b b' c c' : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < α1 ∧ 1 < β1 ∧ 1 < β6 ∧ γ6 < 1 ∧ ⟪c - a', a - b'⟫ = 0) ∨
    (1 < α1 ∧ 1 < β1 ∧ β6 < 1 ∧ 1 < γ6 ∧ ⟪b - a', a - c'⟫ = 0)

/-- H1: `α1, β1, β6, γ6 > 1`, `σ > β1` (open here; the spec's 4-leaf tree is not formalized). -/
def K6mH1 (α1 β1 β6 γ6 : ℝ) : Prop := 1 < α1 ∧ 1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < β6 ∧ 1 < γ6

/-- H5: `α1, β1 > 1`, `σ > β1`, `β6, γ6 < 1` (open, as in the spec). -/
def K6mH5 (α1 β1 β6 γ6 : ℝ) : Prop := 1 < α1 ∧ 1 < β1 ∧ β1 < β6 + γ6 ∧ β6 < 1 ∧ γ6 < 1

/-- The K6M frame data of a configuration. -/
def K6mCoords (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  det3 (a - d) (b - d) (c - d) ≠ 0 ∧ c' = d + α1 • (a - d) + β1 • (b - d) ∧
    b' = d + α1 • (a - d) + β1 • (c - d) ∧ a' = d + β6 • (b - d) + γ6 • (c - d) ∧
    0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6

/-- Leftover of `k6m_qn2`. -/
def K6sMLeftN2 (a a' b b' c c' d : ℝ³) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (K6mBoundary α1 β1 β6 γ6 ∨ K6mTie a a' b b' c c' α1 β1 β6 γ6 ∨ K6mH1 α1 β1 β6 γ6 ∨ K6mH5 α1 β1 β6 γ6)

/-- Leftover of `k6m_qceb` (there `γ6 < 1`, so H1 and the H4 tie cannot occur). -/
def K6sMLeftKb (a a' b b' c c' d : ℝ³) : Prop :=
  K6sMKb a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (K6mBoundary α1 β1 β6 γ6 ∨ K6mTie a a' b b' c c' α1 β1 β6 γ6 ∨ K6mH5 α1 β1 β6 γ6)

/-- The box split: every M configuration is closed by a metric-free box, or lies in a named leftover. -/
theorem k6m_core {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6mBoundary α1 β1 β6 γ6 ∨ K6mTie a a' b b' c c' α1 β1 β6 γ6 ∨
      K6mH1 α1 β1 β6 γ6 ∨ K6mH5 α1 β1 β6 γ6 := by
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩ := hC
  rcases lt_trichotomy β1 1 with hb | hb | hb
  · exact Or.inl (k6m_A_hasLexCell hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h3 hb)
  · exact Or.inr (Or.inl (Or.inl hb))
  rcases lt_trichotomy (β6 + γ6) β1 with hs | hs | hs
  · exact Or.inl (k6m_T_hasLexCell hdet hc' hb' ha' hα1 hβ6 hγ6 hb hs)
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hb, hs⟩)))
  rcases lt_trichotomy α1 1 with ha | ha | ha
  · exact Or.inl (k6m_B_hasLexCell W hdet hc' hb' ha' hα1 hβ1 h1 hβ6 hγ6 ha)
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hb, hs, ha⟩))))
  rcases lt_trichotomy β6 1 with h6 | h6 | h6
  · rcases lt_trichotomy γ6 1 with g6 | g6 | g6
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hs, h6, g6⟩)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hb, hs, ha, Or.inr g6⟩))))
    · rcases eq_or_ne ⟪b - a', a - c'⟫ 0 with hl | hl
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨ha, hb, h6, g6, hl⟩)))
      · exact Or.inl (k6m_H4_hasLexCell hdet hc' hb' ha' ha hb hβ6 h6 g6 hM hl)
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hb, hs, ha, Or.inl h6⟩))))
  · rcases lt_trichotomy γ6 1 with g6 | g6 | g6
    · rcases eq_or_ne ⟪c - a', a - b'⟫ 0 with hl | hl
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨ha, hb, h6, g6, hl⟩)))
      · exact Or.inl (k6m_H2_hasLexCell hdet hc' hb' ha' ha hb h6 hγ6 g6 hM hl)
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨hb, hs, ha, Or.inr g6⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hs, h6, g6⟩)))

/-- Coordinates (QCEb) with the far ends: `γ6 < 1` and `1 < α1`. -/
theorem k6m_coords_kb' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndKb b b' c c' d)
    (hfar1 : W.F.abc'.f c < W.F.abc'.f a') (hfar2 : W.F.a'bc.f c' < W.F.a'bc.f a) :
    ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧ 1 < α1 ∧ γ6 < 1 := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hP0, hα, hγ, -⟩ := p0_kb_collpers W hκ h
  obtain ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩ := hP0
  refine ⟨α1, β1, β6, γ6, ⟨hdet, hc', ?_, ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩, hfb hfar2, hfa hfar1⟩
  rw [hb', hα, hγ]

/-- **QN2 on M**: closed by the metric-free boxes A, B, T, H2, H4, or in the named leftover. -/
theorem k6m_qn2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hs : K6sMN2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sMLeftN2 a a' b b' c c' d := by
  obtain ⟨hκ, h, hM⟩ := hs
  obtain ⟨α1, β1, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩ := k6m_coords_n2 W hκ h
  have hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6 := ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩
  rcases k6m_core W hC hM with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ⟨⟨hκ, h, hM⟩, α1, β1, β6, γ6, hC, h0⟩

/-- **QCEb on M** (with the far ends `T4`): closed by A, T, H2 (B is empty since `α1 > 1`), or in the named leftover. -/
theorem k6m_qceb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hfar1 : W.F.abc'.f c < W.F.abc'.f a') (hfar2 : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hs : K6sMKb a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6sMLeftKb a a' b b' c c' d := by
  obtain ⟨hκ, h, hM⟩ := hs
  obtain ⟨α1, β1, β6, γ6, hC, ha1, hg1⟩ := k6m_coords_kb' W hκ h hfar1 hfar2
  rcases k6m_core W hC hM with h0 | h0 | h0 | h0 | h0
  · exact Or.inl h0
  · exact Or.inr ⟨⟨hκ, h, hM⟩, α1, β1, β6, γ6, hC, Or.inl h0⟩
  · exact Or.inr ⟨⟨hκ, h, hM⟩, α1, β1, β6, γ6, hC, Or.inr (Or.inl h0)⟩
  · exact absurd hg1 (not_lt.2 h0.2.2.2.2.le)
  · exact Or.inr ⟨⟨hκ, h, hM⟩, α1, β1, β6, γ6, hC, Or.inr (Or.inr h0)⟩

end C2
end Type08Sp
end Minimality
