module

public import Minimality.Type24SAT.K24.Wire24Res
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

/-!
# Type 24: a facet cell closes the case (Lemma Z0 at the solid's own apex)

Source: `nopert229/notes/Z0-WIRING.md`, `TENT-GENERALIZE.md` item 2 (Z0 at the own apex).

If some facet `t` of the nine facets of type 24 has a view `u` with `t` facing the viewer and every facet across
an edge of `t` facing away, then the silhouette of the solid in direction `u` is the boundary of the facet `t`
(a planar convex polygon: a triangle, or the quadrilateral `G`), its depths are robustly unimodal, and the
solid is Rupert (`isRupert_of_closedCell`).  Lemma Z0 (cells `{Q}`, `{P}`, `{R}` of the base over a tent apex)
is the case of the facets `G`, `H`, `I` at a view in the cone of the apex; it needs no `x*`, no frame and no
`caseC`.

* `FacetCell24 fs`: the explicit Prop on the nine facet functionals (`fs = ![fA, fB, fF, fG, fE, fC, fH, fD, fI]`,
  the order of `s0x_S24`).
* `isRupert_of_facetCell24`: `FacetCell24` gives `IsRupert`.
* `rupert_or_resid24_noFacetCell`: Rupert, or `Resid24 x` and not `FacetCell24`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.T24.Z0
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

/-- The facets across the edges of facet `t` (indices of `s0x_S24`). -/
def nb : Fin 9 → Finset (Fin 9) :=
  ![{1, 5, 2}, {0, 5, 4}, {0, 6, 3}, {4, 8, 6, 2}, {3, 8, 1}, {0, 7, 1}, {7, 3, 2}, {6, 8, 5}, {3, 4, 7}]

/-- The vertices of the triangular facet `t` in order (the entry `3` is the quadrilateral and is not used). -/
def rim3 : Fin 9 → ZMod 3 → Fin 7 :=
  ![![0, 1, 2], ![0, 1, 6], ![0, 2, 5], ![0, 3, 4], ![0, 4, 6], ![1, 2, 6], ![2, 3, 5], ![2, 3, 6], ![3, 4, 6]]

/-- The rim of the quadrilateral facet `G = 0345`. -/
def rimG : ZMod 4 → Fin 7 := ![0, 4, 3, 5]

theorem rim3_inj : ∀ t : Fin 9, t ≠ 3 → Function.Injective (rim3 t) := by decide

theorem rim3_cyc : ∀ t : Fin 9, t ≠ 3 → S0xCycUD s0x_S24 (rim3 t) {t} (nb t) := by decide

theorem rimG_cyc : S0xCycUD s0x_S24 rimG {3} (nb 3) := by decide

/-- A triangular facet cell: Rupert. -/
theorem rupert_of_tri (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ≠ 3) {a : ℝ³}
    (ha : CellAt F {t} (nb t) a) : IsRupert (univ.image x) := by
  obtain ⟨D⟩ := silL_of_cell F (rim3_cyc t ht) ha.cellLe ha
  have hu0 : a ≠ 0 := by
    rintro rfl
    have := ha.1 t (by simp)
    simp at this
  exact s0x_sil_isRupert_lex (by norm_num) (Minimality.H24.SAT.inj_of_fac F) (rim3_inj t ht) hu0 D
    (Minimality.H24K.SAT.robUni_three _)

/-- Planar quadrilateral, case 1: `z1, z3 <= z0, z2`. -/
theorem quad_not_low {z0 z1 z2 z3 al be : ℝ} (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hr : z2 - z0 = al * (z3 - z0) + be * (z1 - z0)) (hne : z1 ≠ z0)
    (h1 : z1 ≤ z0) (h2 : z1 ≤ z2) (h3 : z3 ≤ z0) (h4 : z3 ≤ z2) : False := by
  have hle : z2 ≤ z0 := by
    nlinarith [mul_nonneg hal.le (sub_nonneg.2 h3), mul_nonneg hbe.le (sub_nonneg.2 h1)]
  have hge : z0 ≤ z2 := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hlt), mul_nonneg hal.le (sub_nonneg.2 h4),
      mul_nonneg hbe.le (sub_nonneg.2 h2)]
  have he : z2 = z0 := le_antisymm hle hge
  apply hne
  by_contra hlt
  have hlt' : z1 < z0 := lt_of_le_of_ne h1 hlt
  nlinarith [mul_pos hbe (sub_pos.2 hlt'), mul_nonneg hal.le (sub_nonneg.2 h3)]

/-- Planar quadrilateral: the depths are robustly unimodal as soon as `z1 ≠ z0`. -/
theorem robUni_quad {z : ZMod 4 → ℝ} {al be : ℝ} (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hr : z 2 - z 0 = al * (z 3 - z 0) + be * (z 1 - z 0)) (hne : z 1 ≠ z 0) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  have e : ((0 : ZMod 4) + 1 = 1 ∧ (0 : ZMod 4) + 2 = 2 ∧ (0 : ZMod 4) + 3 = 3) ∧
      ((1 : ZMod 4) + 1 = 2 ∧ (1 : ZMod 4) + 2 = 3 ∧ (1 : ZMod 4) + 3 = 0) ∧
      ((2 : ZMod 4) + 1 = 3 ∧ (2 : ZMod 4) + 2 = 0 ∧ (2 : ZMod 4) + 3 = 1) ∧
      ((3 : ZMod 4) + 1 = 0 ∧ (3 : ZMod 4) + 2 = 1 ∧ (3 : ZMod 4) + 3 = 2) := by decide
  obtain ⟨⟨e01, e02, e03⟩, ⟨e11, e12, e13⟩, ⟨e21, e22, e23⟩, ⟨e31, e32, e33⟩⟩ := e
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by revert B; decide
  have hr' : (-z 2) - (-z 0) = al * ((-z 3) - (-z 0)) + be * ((-z 1) - (-z 0)) := by linarith
  have hne' : -z 1 ≠ -z 0 := fun h => hne (neg_injective h)
  rcases hB with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.cast_one, Nat.cast_ofNat]
    rintro ⟨h1, h2, h3, h4⟩
    simp only [e01, e02, e03, e11, e12, e13, e21, e22, e23, e31, e32, e33] at h1 h2 h3 h4
    clear e01 e02 e03 e11 e12 e13 e21 e22 e23 e31 e32 e33
    first
      | exact quad_not_low hal hbe hab hr hne (by assumption) (by assumption) (by assumption)
          (by assumption)
      | exact quad_not_low hal hbe hab hr' hne' (by linarith) (by linarith) (by linarith)
          (by linarith)

/-- The quadrilateral facet `G`: a cell point gives a cell point with distinct depths on `x 0, x 4`. -/
theorem exists_cell_nonconst (F : S0xFac 9 s0x_S24 x) {a : ℝ³} (ha : CellAt F {3} (nb 3) a) :
    ∃ a', CellAt F {3} (nb 3) a' ∧ ⟪x 4 - x 0, a'⟫ ≠ 0 := by
  by_cases h0 : ⟪x 4 - x 0, a⟫ = 0
  · have hx := Minimality.H24.SAT.inj_of_fac F
    have hd : x 4 - x 0 ≠ 0 := sub_ne_zero.2 fun h => absurd (hx h) (by decide)
    have e : ∀ t ε, ⟪F.N t, a + ε • (x 4 - x 0)⟫ = ⟪F.N t, a⟫ + ε * ⟪F.N t, x 4 - x 0⟫ := by
      intro t ε; rw [inner_add_right, inner_smul_right]
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F {3} (nb 3) (a + ε • (x 4 - x 0)) := by
      refine (Filter.eventually_all_finset {3} |>.2 fun t ht => ?_).and
        (Filter.eventually_all_finset (nb 3) |>.2 fun t ht => ?_)
      · exact (eventually_pos_affine (Or.inl (ha.1 t ht))).mono fun ε hε => by rw [e]; exact hε
      · exact (eventually_pos_affine (B := -⟪F.N t, x 4 - x 0⟫) (Or.inl (neg_pos.2 (ha.2 t ht)))).mono fun ε hε => by
          rw [e]; linarith
    obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
    refine ⟨_, hε, ?_⟩
    have hpos : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 hd
    rw [inner_add_right, inner_smul_right, h0]
    have : (0 : ℝ) < ε := hε0
    positivity
  · exact ⟨a, ha, h0⟩

/-- The quadrilateral facet cell: Rupert. -/
theorem rupert_of_quadG (F : S0xFac 9 s0x_S24 x) {a : ℝ³} (ha : CellAt F {3} (nb 3) a) :
    IsRupert (univ.image x) := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  obtain ⟨a', ha', hne⟩ := exists_cell_nonconst F ha
  obtain ⟨al, be, hal, hbe, hab, hq⟩ := Minimality.T24.Par.par2546_quad F
  have hr : ⟪x 3, a'⟫ - ⟪x 0, a'⟫ = al * (⟪x 5, a'⟫ - ⟪x 0, a'⟫) + be * (⟪x 4, a'⟫ - ⟪x 0, a'⟫) := by
    have := congrArg (fun v => ⟪v, a'⟫) hq
    simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
  have hne' : ⟪x 4, a'⟫ ≠ ⟪x 0, a'⟫ := fun h => hne (by rw [inner_sub_left, h, sub_self])
  have hR : RobUni (fun i => ⟪x (rimG i), a'⟫) :=
    robUni_quad (z := fun i => ⟪x (rimG i), a'⟫) hal hbe hab (by simpa [rimG] using hr)
      (by simpa [rimG] using hne')
  exact isRupert_of_closedCell (by norm_num) F hx (by decide) rimG_cyc ha' ha'.cellLe hR

/-- **The facet cell condition** on the nine facet functionals `fs` (in the order of `s0x_S24`, that is
`![fA, fB, fF, fG, fE, fC, fH, fD, fI]`): some facet `t` faces a view `u` while every facet across an edge of `t`
(`nb t`) faces away from it. -/
def FacetCell24 (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ∃ t : Fin 9, ∃ u : ℝ³, 0 < (fs t).linear u ∧ ∀ s ∈ nb t, (fs s).linear u < 0

/-- **A facet cell closes the case** (Lemma Z0 at the solid's own apex). -/
theorem isRupert_of_facetCell24 (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hz : FacetCell24 fs) : IsRupert (univ.image x) := by
  obtain ⟨t, u, hu, hn⟩ := hz
  let F := Minimality.T24.mkFac24 fs h
  have hN : ∀ s, ⟪F.N s, u⟫ = (fs s).linear u := by
    intro s
    have h1 := F.hN s u 0
    have h2 : (fs s).linear u = fs s u - fs s 0 := by simpa using (fs s).linear_apply_vsub u 0
    rw [h2]
    simpa [F, Minimality.T24.mkFac24] using h1.symm
  have ha : CellAt F {t} (nb t) u :=
    ⟨fun s hs => by rw [mem_singleton.1 hs, hN]; exact hu, fun s hs => by rw [hN]; exact hn s hs⟩
  by_cases ht : t = 3
  · subst ht; exact rupert_of_quadG F ha
  · exact rupert_of_tri F ht ha

/-- **The type 24 branch, closed off the residual and the facet cells**: Rupert, or `Resid24 x` holds and no facet
has a cell (`FacetCell24`, which contains Lemma Z0's cells `{Q}`, `{P}`, `{R}` = the facets `G`, `H`, `I`). -/
theorem rupert_or_resid24_noFacetCell {x : Fin 7 → ℝ³} (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨
      (Resid24 x ∧ ¬ FacetCell24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI]) := by
  have hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
      (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0) := by
    intro t i
    fin_cases t
    exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]
  by_cases hz : FacetCell24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI]
  · exact Or.inl (isRupert_of_facetCell24 _ hh hz)
  · rcases rupert_or_resid24 fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hz⟩

end Minimality.T24.Z0
