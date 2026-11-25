module

public import Minimality.Type24Z0
public import Minimality.RCell24
public import Minimality.LexCell
public import Minimality.GenericLeaves

@[expose] public section

/-!
# A facet cell on the quadrilateral `0345` is a lexicographic closed cell (type 24)

`lexAny_of_quadCell`: a `CellAt F {3} (nb 3) a` point (facet `G`, the planar quadrilateral `0345`,
strictly facing) gives `RCell.LexAny F` on the rim `0 4 3 5` (`k = 4`).  The depths on a planar
convex quadrilateral are `RobUni` unless `z 0 = z 4` (`Z0.robUni_quad`), and a tilt of the cell point
removes that tie (`Z0.exists_cell_nonconst`).  So `¬ LexAny F` already excludes a facet cell on
`0345`; `FacetCell24` is needed only for the eight triangle facets.
-/

set_option autoImplicit false
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Z0 Minimality.LexCell
open scoped RealInnerProductSpace

namespace Minimality.T24

/-- A real robustly unimodal cycle, padded with zeros, is lexicographically robustly unimodal. -/
theorem robUniLex_of_robUni_pad {k : ℕ} {z : ZMod k → ℝ} (h : RobUni z) :
    RobUniLex (fun i => (z i, (0 : ℝ), (0 : ℝ))) := by
  intro B b c d hb hbc hcd hd
  have := h B b c d hb hbc hcd hd
  simp only [LexLt3, LexPos3, sub_pos]
  by_contra hn
  simp only [not_or] at hn
  exact this ⟨not_lt.mp hn.1.1, not_lt.mp hn.2.1.1, not_lt.mp hn.2.2.1.1, not_lt.mp hn.2.2.2.1⟩

/-- A facet cell on the quadrilateral `0345` is a lexicographic closed cell. -/
theorem lexAny_of_quadCell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a : ℝ³}
    (ha : CellAt F {3} (nb 3) a) : Minimality.T24.RCell.LexAny F := by
  obtain ⟨a', ha', hne⟩ := exists_cell_nonconst F ha
  obtain ⟨al, be, hal, hbe, hab, hq⟩ := Minimality.T24.Par.par2546_quad F
  have hr : ⟪x 3, a'⟫ - ⟪x 0, a'⟫ = al * (⟪x 5, a'⟫ - ⟪x 0, a'⟫) + be * (⟪x 4, a'⟫ - ⟪x 0, a'⟫) := by
    have := congrArg (fun v => ⟪v, a'⟫) hq
    simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
  have hne' : ⟪x 4, a'⟫ ≠ ⟪x 0, a'⟫ := fun h => hne (by rw [inner_sub_left, h, sub_self])
  have hR : RobUni (fun i => ⟪x (rimG i), a'⟫) :=
    robUni_quad (z := fun i => ⟪x (rimG i), a'⟫) hal hbe hab (by simpa [rimG] using hr)
      (by simpa [rimG] using hne')
  refine ⟨4, inferInstance, rimG, {3}, nb 3, a', 0, 0, le_rfl, by decide, rimG_cyc, ?_, ?_, ?_⟩
  · intro t ht; exact Or.inl (ha'.1 t ht)
  · intro t ht; exact Or.inl (neg_pos.mpr (ha'.2 t ht))
  · simpa only [inner_zero_right] using robUniLex_of_robUni_pad hR

end Minimality.T24
