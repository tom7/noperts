module

public import Minimality.LemmaTQ
public import Minimality.Type24Z0

@[expose] public section

/-!
# Lemma TQ without the empty-triangle-cell hypotheses

A nonempty single-front-facet cell `{t}` of a triangular facet `t` gives `IsRupert` by
`Z0.rupert_of_tri` (the silhouette is the 3-rim of the facet, robustly unimodal), so the
hypotheses `hNo235 hNo346 hNo025 hNo046` of `lemmaTQ`, `lemmaTQ_04325`, `lemmaTQ_04635` are
dropped.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.TQ
open Minimality Minimality.H21 Minimality.T24.SAT

/-- A cell with front set `{t}` and all other facets back, for a triangular facet `t ≠ 3`. -/
theorem isRupert_of_cell_single {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ≠ 3)
    {D : Finset (Fin 9)} (hD : Z0.nb t ⊆ D) {w : ℝ³} (h : CellAt F {t} D w) :
    IsRupert (Finset.univ.image x) :=
  Z0.rupert_of_tri F ht ⟨h.1, fun s hs => h.2 s (hD hs)⟩

/-- **Lemma TQ**, frame `04325`, without the empty-cell hypotheses. -/
theorem lemmaTQ_04325' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6} {0, 1, 2, 4, 5, 7, 8} u)
    (hgen : ∀ w : ℝ³, ⟪F.N 3, w⟫ = 0 → ⟪F.N 4, w⟫ = 0 → ⟪F.N 7, w⟫ = 0 → w = 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases h1 : ∃ w, CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w
  · obtain ⟨w, hw⟩ := h1
    exact isRupert_of_cell_single F (t := 6) (by decide) (by decide) hw
  by_cases h2 : ∃ w, CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w
  · obtain ⟨w, hw⟩ := h2
    exact isRupert_of_cell_single F (t := 8) (by decide) (by decide) hw
  by_cases h3 : ∃ w, CellAt F {2} {0, 1, 3, 4, 5, 6, 7, 8} w
  · obtain ⟨w, hw⟩ := h3
    exact isRupert_of_cell_single F (t := 2) (by decide) (by decide) hw
  push Not at h1 h2 h3
  exact lemmaTQ_04325 F hx hli hab hbc hu hR h1 h2 h3 hgen

/-- **Lemma TQ**, frame `04635`, without the empty-cell hypotheses. -/
theorem lemmaTQ_04635' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 8} {0, 1, 2, 4, 5, 6, 7} u)
    (hgen : ∀ w : ℝ³, ⟪F.N 3, w⟫ = 0 → ⟪F.N 2, w⟫ = 0 → ⟪F.N 7, w⟫ = 0 → w = 0) :
    IsRupert (Finset.univ.image x) := by
  by_cases h1 : ∃ w, CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w
  · obtain ⟨w, hw⟩ := h1
    exact isRupert_of_cell_single F (t := 8) (by decide) (by decide) hw
  by_cases h2 : ∃ w, CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w
  · obtain ⟨w, hw⟩ := h2
    exact isRupert_of_cell_single F (t := 6) (by decide) (by decide) hw
  by_cases h3 : ∃ w, CellAt F {4} {0, 1, 2, 3, 5, 6, 7, 8} w
  · obtain ⟨w, hw⟩ := h3
    exact isRupert_of_cell_single F (t := 4) (by decide) (by decide) hw
  push Not at h1 h2 h3
  exact lemmaTQ_04635 F hx hli hac hbc hu hR h1 h2 h3 hgen

/-- **Lemma TQ'** (type 24, obtuse corner 1) without the four empty-cell hypotheses. -/
theorem lemmaTQ' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6} {0, 1, 2, 4, 5, 7, 8} u ∨ CellAt F {3, 8} {0, 1, 2, 4, 5, 6, 7} u)
    (hgen : ∀ w : ℝ³, ⟪F.N 3, w⟫ = 0 → ⟪F.N 4, w⟫ = 0 → ⟪F.N 7, w⟫ = 0 → w = 0)
    (hgen' : ∀ w : ℝ³, ⟪F.N 3, w⟫ = 0 → ⟪F.N 2, w⟫ = 0 → ⟪F.N 7, w⟫ = 0 → w = 0) :
    IsRupert (Finset.univ.image x) := by
  rcases hR with h | h
  · exact lemmaTQ_04325' F hx hli hab hbc hu h hgen
  · exact lemmaTQ_04635' F hx hli hac hbc hu h hgen'

end Minimality.T24.TQ
