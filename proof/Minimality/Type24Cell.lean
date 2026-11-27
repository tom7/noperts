module

public import Minimality.Type24OffOB1
public import Minimality.Type24WallFoot
public import Minimality.EdgePlaneRev

/-!
# Type 24: cell certificates (generic form of the named-view cover, task CELL24, 2026-11-27)

Design: nopert229 notes/GENREV-NAMEDCOVER.md items 1, 2, 4, 5.  The 21 named certificates of `Type24NamedCover`
are certificates on open cells of the 9-facet arrangement (2-parameter families = charts of cells, 1-parameter
families = walls).  Here a cell is data, and there is one generic theorem per leaf kind.

* `Cell24`: a rim `r : ZMod k → Fin 7` (`k ≥ 4`, injective) and an up-set `U` of facets; the down-set is the
  complement; `S0xCycUD` (the rim is the silhouette of the sign pattern) is a field, proved by `decide`.
* `CellCert F c w`: `w` is in the open cell and carries a strict certificate on the rim:
  `RobUni` depths (Lex), a strict-apex order certificate `ApexCert` (Split), or `HiddenInTriangles` plus Edge-Plane
  rows `EPCert` (any `s, α, μ`; no `sh = ±1`, no `c_i ≠ 0` normalization).  `Cell24.Hid c` (every off-rim vertex
  is hidden at every view of the open cell) makes the hidden conjunct automatic (`cellCert_of_ep`).
* Generic leaves: `lexAny_of_cellRob`, `splitAny_of_cellApex`, `edgePlaneAny_of_cellEP`, combined in
  `cellCert_leaf`; `holeLeaf_not_cellCert`, `holeLeaf_not_cellCert_twin`.
* Order certificates with ties (`Split.Slope.OrderCertAt`) are Edge-Plane certificates: `epCert_of_orderCert`.
* `CellCoverResidue L x F`, `CellCoverEmpty L` (the open Prop), `hole24_cellCoverResidue`,
  `not_hole24_of_cellCoverEmpty` (with `OSpec.OpenSpecialW`), `openOB1_of_cellCoverEmpty`, `cellCoverEmpty_mono`.
* The list `cells24`: the 7 named cells (C = w_C, D = w_D, D6 = w_D6, A2, B2 = T_2, A0, B0 = interior T_0), the
  4-rim wall cells `0.5.2.6` (C', vertices 1, 3, 4 hidden; closes sBa_298), `0.2.3.6`, `0.5.3.6`, and the pentagon
  `0.4.6.2.5` (vertices 1, 3 hidden).  The `π_24` twins are the `Sym.sym24 F` side of the residue.
* Hidden vertices (CELL24B): `link_winding` (any vertex, any number of incident facets: if the facets around `v`
  have one strict sign at `w`, the projected link edges `x (p i) - x v` turn strictly one way; one chain link may
  fail, e.g. inside a quad facet), `hidden_of_link5` / `hidden_of_link3` (triangle extraction), `hidden_two`
  (vertex 2, degree 5), `hidden_three` (vertex 3, degree 4: its link `5.2.6.4` extended by the opposite vertex `0`
  of the quad `0345` is a 5-cycle, so no genericity condition is needed).
* `Hid` proved for all 11 cells of `cells24` (C, D, D6, A0, B0, `0.2.3.6` earlier; A2, B2, `0.5.3.6`, C', P here).
* Wall persistence, the named cover as a sub-cover (`cellCoverEmpty_of_namedCoverEmpty`) and the `OpenSpecialR`
  chain: Type24CellWall.lean.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

/-! ## Cells and certificates -/

/-- A cell of the type-24 facet arrangement with its rim: up facets `U`, down facets `univ \ U`, rim `r`
(the silhouette cycle of the sign pattern, `cyc`). -/
structure Cell24 where
  k : ℕ
  [nz : NeZero k]
  hk : 4 ≤ k
  r : ZMod k → Fin 7
  U : Finset (Fin 9)
  inj : Function.Injective r
  cyc : S0xCycUD s0x_S24 r U (univ \ U)

attribute [instance] Cell24.nz

/-- Strict-apex order certificate on a rim `X` at `w` (the hypotheses of `SF.oc_splitAny_of_cell`): apex `cc`
off the base edge `a`, strictly extreme in the base-edge determinant, one open arc strictly above `z cc` and the
other strictly below. -/
def ApexCert {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∃ a cc : ZMod k, cc ≠ a ∧ cc ≠ a + 1 ∧
    (∀ j : ZMod k, j ≠ a → j ≠ a + 1 → j ≠ cc →
      |Split.det3 (X j - X a) (X (a + 1) - X a) w| < |Split.det3 (X cc - X a) (X (a + 1) - X a) w|) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ j : ZMod k, (j - a - 1).val < (cc - a - 1).val → σ * (⟪X j, w⟫ - ⟪X cc, w⟫) < 0) ∧
      (∀ j : ZMod k, (cc - a - 1).val < (j - a - 1).val → 0 < σ * (⟪X j, w⟫ - ⟪X cc, w⟫))

/-- Edge-Plane rows on a rim `X` at `w` (base edge `a` not level, any `s, α, μ`). -/
def EPCert {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∃ (a : ZMod k) (s α μ : ℝ), ⟪X (a + 1) - X a, w⟫ ≠ 0 ∧ Split.EV.EPRows X w a s α μ

/-- **Cell certificate**: `w` lies in the open cell `c` and carries a strict leaf certificate on the rim. -/
def CellCert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (c : Cell24) (w : ℝ³) : Prop :=
  CellAt F c.U (univ \ c.U) w ∧
    (RobUni (fun i => ⟪x (c.r i), w⟫) ∨ ApexCert (fun i => x (c.r i)) w ∨
      (Split.HiddenInTriangles x w c.r ∧ EPCert (fun i => x (c.r i)) w))

/-- Every vertex off the rim is hidden in a projected triangle at every view of the open cell. -/
def Cell24.Hid (c : Cell24) : Prop :=
  ∀ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³},
    CellAt F c.U (univ \ c.U) w → Split.HiddenInTriangles x w c.r

/-! ## Generic leaves -/

variable {x : Fin 7 → ℝ³}

/-- **Lex kind**: a `RobUni` view of the open cell gives `Gen.LexAny`. -/
theorem lexAny_of_cellRob (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³}
    (hcell : CellAt F c.U (univ \ c.U) w) (hrob : RobUni (fun i => ⟪x (c.r i), w⟫)) : Gen.LexAny F :=
  WC.lexAny_of_cellAt_robUni c.hk F c.inj c.cyc hcell hrob

/-- **Split kind**: a strict-apex order certificate at a view of the open cell gives `Gen.SplitAny`. -/
theorem splitAny_of_cellApex (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³}
    (hcell : CellAt F c.U (univ \ c.U) w) (hA : ApexCert (fun i => x (c.r i)) w) : Gen.SplitAny F := by
  obtain ⟨a, cc, hca, hca1, hext, hsep⟩ := hA
  exact oc_splitAny_of_cell F (by have := c.hk; omega) c.r c.inj
    (fun t => by by_cases ht : t ∈ c.U <;> simp [ht]) c.cyc hcell hca hca1 hext hsep

/-- The spin term of an Edge-Plane row does not change under `w ↦ -w` (same rim). -/
theorem edgePlaneSpin_neg_view {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k) :
    Split.edgePlaneSpin X (-w) a i j = Split.edgePlaneSpin X w a i j := by
  unfold Split.edgePlaneSpin
  have e1 : Split.det3 (X (i + 1) - X i) (cross (-w) (X j - X a)) (-w) =
      Split.det3 (X (i + 1) - X i) (cross w (X j - X a)) w := by
    simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2, PiLp.sub_apply, PiLp.neg_apply]
    ring
  have e2 : Split.det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) (-w)) (-w) =
      Split.det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) w) w := by
    simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2, PiLp.sub_apply, PiLp.neg_apply]
    ring
  rw [e1, e2, inner_neg_right, inner_neg_right, neg_div_neg_eq]

/-- `HiddenInTriangles` does not depend on the sign of the view. -/
theorem hiddenInTriangles_neg_view {n k : ℕ} [NeZero k] {y : Fin n → ℝ³} {w : ℝ³} {lab : ZMod k → Fin n}
    (h : Split.HiddenInTriangles y w lab) : Split.HiddenInTriangles y (-w) lab := fun m hm =>
  Split.Rev.hiddenInTriangles_rev y w lab h m (fun i => by simpa using hm (-i))

/-- **Edge-Plane kind**: Edge-Plane rows at a view of the open cell with the off-rim vertices hidden give
`Gen.EdgePlaneAny` (the rim orientation is fixed by passing to `-w` if needed). -/
theorem edgePlaneAny_of_cellEP (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³}
    (hcell : CellAt F c.U (univ \ c.U) w) (hhid : Split.HiddenInTriangles x w c.r)
    (hE : EPCert (fun i => x (c.r i)) w) : Gen.EdgePlaneAny x := by
  obtain ⟨a, s, α, μ, hD, hrows⟩ := hE
  have hk3 : 3 ≤ c.k := by have := c.hk; omega
  rcases LexEP.strictRimN_of_openCell hk3 F c.inj c.cyc hcell with hrim | hrim
  · exact ⟨c.k, inferInstance, c.r, w, a, s, α, μ, hk3, c.inj, hrim, hhid, hD, hrows⟩
  · have hrim' : Split.StrictRimN x (-w) c.r := by
      simpa using Split.Rev.strictRimN_rev x w (fun i => c.r (-i)) hrim
    refine ⟨c.k, inferInstance, c.r, -w, a, s, -α, μ, hk3, c.inj, hrim', hiddenInTriangles_neg_view hhid,
      ?_, fun i j hi hj => ?_⟩
    · rw [inner_neg_right]; exact neg_ne_zero.mpr hD
    · have h := hrows i j hi hj
      have e : Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r (a + 1)) - x (c.r a)) (-w) =
          -Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r (a + 1)) - x (c.r a)) w := by
        simp only [Split.det3, PiLp.neg_apply]; ring
      rw [e, edgePlaneSpin_neg_view, inner_neg_right]
      have e2 : (-α + μ * -⟪x (c.r j) - x (c.r a), w⟫) *
            -Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r (a + 1)) - x (c.r a)) w =
          (α + μ * ⟪x (c.r j) - x (c.r a), w⟫) *
            Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r (a + 1)) - x (c.r a)) w := by ring
      rw [e2]; exact h

/-- On a cell with `Hid`, Edge-Plane rows at a view of the open cell are a cell certificate. -/
theorem cellCert_of_ep (F : S0xFac 9 s0x_S24 x) {c : Cell24} (hH : c.Hid) {w : ℝ³}
    (hcell : CellAt F c.U (univ \ c.U) w) (hE : EPCert (fun i => x (c.r i)) w) : CellCert F c w :=
  ⟨hcell, Or.inr (Or.inr ⟨hH F hcell, hE⟩)⟩

/-- An order certificate with ties (`Split.Slope.OrderCertAt`) is an Edge-Plane certificate
(`lineSep_of_depthOrder_ties` and `epRows_of_lineSep`). -/
theorem epCert_of_orderCert {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (h : Split.Slope.OrderCertAt X w) :
    EPCert X w := by
  rcases h with ⟨a, hD, hc_ne, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties X w a sh hOrd hEq
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep X w a hD hc_ne sh hsh α' μ' hB hO
  exact ⟨a, s, α, μ, hD, hrows⟩

/-- **Every cell certificate is a generic leaf** (Lex, Split or Edge-Plane). -/
theorem cellCert_leaf (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³} (h : CellCert F c w) :
    Gen.LexAny F ∨ Gen.SplitAny F ∨ Gen.EdgePlaneAny x := by
  obtain ⟨hcell, hR | hA | ⟨hH, hE⟩⟩ := h
  · exact Or.inl (lexAny_of_cellRob F c hcell hR)
  · exact Or.inr (Or.inl (splitAny_of_cellApex F c hcell hA))
  · exact Or.inr (Or.inr (edgePlaneAny_of_cellEP F c hcell hH hE))

/-- A cell certificate on the `π_24` twin `(x ∘ π_24, sym24 F)` is a generic leaf of `(x, F)`. -/
theorem cellCert_twin_leaf (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³} (h : CellCert (Sym.sym24 F) c w) :
    Gen.LexAny F ∨ Gen.SplitAny F ∨ Gen.EdgePlaneAny x := by
  rcases cellCert_leaf (Sym.sym24 F) c h with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr (TwoCone.edgePlaneAny_of_comp_pi24 x hE))

/-- A point of the generic hole has no cell certificate, in any cell. -/
theorem holeLeaf_not_cellCert {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F) (c : Cell24) (w : ℝ³) :
    ¬ CellCert F c w := fun hc => by
  rcases cellCert_leaf F c hc with hL | hS | hE
  · exact h.2.2.2.1 hL
  · exact h.2.2.2.2.1 hS
  · exact h.2.2.2.2.2.2 hE

/-- A point of the generic hole has no cell certificate on its `π_24` twin, in any cell. -/
theorem holeLeaf_not_cellCert_twin {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F) (c : Cell24) (w : ℝ³) :
    ¬ CellCert (Sym.sym24 F) c w := fun hc => by
  rcases cellCert_twin_leaf F c hc with hL | hS | hE
  · exact h.2.2.2.1 hL
  · exact h.2.2.2.2.1 hS
  · exact h.2.2.2.2.2.2 hE

/-! ## Hidden vertices -/

/-- A projected triangle at `-w` is a projected triangle at `w` (order `p, r, q`). -/
theorem tri_of_neg_view {p q r y w : ℝ³}
    (h1 : 0 < Split.det3 (q - p) (r - p) (-w)) (h2 : 0 < Split.det3 (q - p) (y - p) (-w))
    (h3 : 0 < Split.det3 (r - q) (y - q) (-w)) (h4 : 0 < Split.det3 (p - r) (y - r) (-w)) :
    0 < Split.det3 (r - p) (q - p) w ∧ 0 < Split.det3 (r - p) (y - p) w ∧
      0 < Split.det3 (q - r) (y - r) w ∧ 0 < Split.det3 (p - q) (y - q) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : Split.det3 (r - p) (q - p) w = Split.det3 (q - p) (r - p) (-w) := by
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : Split.det3 (r - p) (y - p) w = Split.det3 (p - r) (y - r) (-w) := by
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : Split.det3 (q - r) (y - r) w = Split.det3 (r - q) (y - q) (-w) := by
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : Split.det3 (p - q) (y - q) w = Split.det3 (q - p) (y - p) (-w) := by
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith

/-- **Degree-3 hidden vertex, either sign** (`TwoCone.hidden_of_three_facets` for both signs): if the three facets
`t0 ∋ v, p0, p1`, `t1 ∋ v, p1, p2`, `t2 ∋ v, p2, p0` around `v` have one strict sign at `w`, then `x v` is strictly
inside a projected triangle of `x`.  (`TwoCone.hidden_four_of_cell` is the instance `v = 4`, positive sign.) -/
theorem hidden_of_three_facets_sign (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (v p0 p1 p2 : Fin 7) (t0 t1 t2 : Fin 9)
    (hv0 : v ∈ s0x_S24 t0) (hp00 : p0 ∈ s0x_S24 t0) (hp10 : p1 ∈ s0x_S24 t0) (hp20 : p2 ∉ s0x_S24 t0)
    (hv1 : v ∈ s0x_S24 t1) (hp11 : p1 ∈ s0x_S24 t1) (hp21 : p2 ∈ s0x_S24 t1) (hp01 : p0 ∉ s0x_S24 t1)
    (hv2 : v ∈ s0x_S24 t2) (hp22 : p2 ∈ s0x_S24 t2) (hp02 : p0 ∈ s0x_S24 t2) (hp12 : p1 ∉ s0x_S24 t2)
    (hs : (⟪F.N t0, w⟫ < 0 ∧ ⟪F.N t1, w⟫ < 0 ∧ ⟪F.N t2, w⟫ < 0) ∨
      (0 < ⟪F.N t0, w⟫ ∧ 0 < ⟪F.N t1, w⟫ ∧ 0 < ⟪F.N t2, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x v - p) w ∧
      0 < Split.det3 (r - q) (x v - q) w ∧ 0 < Split.det3 (p - r) (x v - r) w := by
  have hsub : ∀ y ∈ ({x p0, x p1, x p2} : Finset ℝ³), y ∈ univ.image x := fun y hy => by
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> exact mem_image_of_mem x (mem_univ _)
  rcases hs with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · obtain ⟨p, hp, q, hq, r, hr, d1, d2, d3, d4⟩ := TwoCone.hidden_of_three_facets F v p0 p1 p2 t0 t1 t2
      hv0 hp00 hp10 hp20 hv1 hp11 hp21 hp01 hv2 hp22 hp02 hp12 h0 h1 h2
    exact ⟨p, hsub p hp, q, hsub q hq, r, hsub r hr, d1, d2, d3, d4⟩
  · have n0 : ⟪F.N t0, -w⟫ < 0 := by rw [inner_neg_right]; linarith
    have n1 : ⟪F.N t1, -w⟫ < 0 := by rw [inner_neg_right]; linarith
    have n2 : ⟪F.N t2, -w⟫ < 0 := by rw [inner_neg_right]; linarith
    obtain ⟨p, hp, q, hq, r, hr, d1, d2, d3, d4⟩ := TwoCone.hidden_of_three_facets F v p0 p1 p2 t0 t1 t2
      hv0 hp00 hp10 hp20 hv1 hp11 hp21 hp01 hv2 hp22 hp02 hp12 n0 n1 n2
    obtain ⟨e1, e2, e3, e4⟩ := tri_of_neg_view d1 d2 d3 d4
    exact ⟨p, hsub p hp, r, hsub r hr, q, hsub q hq, e1, e2, e3, e4⟩

/-- Vertex `1` (facets `0, 1, 5`, link `0.2.6`) is hidden when its three facets have one strict sign. -/
theorem hidden_one (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hs : (⟪F.N 0, w⟫ < 0 ∧ ⟪F.N 5, w⟫ < 0 ∧ ⟪F.N 1, w⟫ < 0) ∨
      (0 < ⟪F.N 0, w⟫ ∧ 0 < ⟪F.N 5, w⟫ ∧ 0 < ⟪F.N 1, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 1 - p) w ∧
      0 < Split.det3 (r - q) (x 1 - q) w ∧ 0 < Split.det3 (p - r) (x 1 - r) w :=
  hidden_of_three_facets_sign F 1 0 2 6 0 5 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs

/-- Vertex `4` (facets `3, 8, 4`, link `0.3.6`). -/
theorem hidden_four (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hs : (⟪F.N 3, w⟫ < 0 ∧ ⟪F.N 8, w⟫ < 0 ∧ ⟪F.N 4, w⟫ < 0) ∨
      (0 < ⟪F.N 3, w⟫ ∧ 0 < ⟪F.N 8, w⟫ ∧ 0 < ⟪F.N 4, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 4 - p) w ∧
      0 < Split.det3 (r - q) (x 4 - q) w ∧ 0 < Split.det3 (p - r) (x 4 - r) w :=
  hidden_of_three_facets_sign F 4 0 3 6 3 8 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs

/-- Vertex `5` (facets `3, 6, 2`, link `0.3.2`). -/
theorem hidden_five (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hs : (⟪F.N 3, w⟫ < 0 ∧ ⟪F.N 6, w⟫ < 0 ∧ ⟪F.N 2, w⟫ < 0) ∨
      (0 < ⟪F.N 3, w⟫ ∧ 0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 2, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 5 - p) w ∧
      0 < Split.det3 (r - q) (x 5 - q) w ∧ 0 < Split.det3 (p - r) (x 5 - r) w :=
  hidden_of_three_facets_sign F 5 0 3 2 3 6 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs

/-! ## Hidden vertices of any degree: link winding -/

/-- For `N ⊥ u1, u2`: `det3 u1 u2 w * ⟪N, q⟫ = det3 u1 u2 q * ⟪N, w⟫` (no nondegeneracy needed). -/
theorem det3_mul_inner_of_perp (N u1 u2 q w : ℝ³) (h1 : ⟪N, u1⟫ = 0) (h2 : ⟪N, u2⟫ = 0) :
    Split.det3 u1 u2 w * ⟪N, q⟫ = Split.det3 u1 u2 q * ⟪N, w⟫ := by
  have e : Split.det3 u1 u2 w * ⟪N, q⟫ - Split.det3 u1 u2 q * ⟪N, w⟫ =
      ⟪N, u1⟫ * Split.det3 u2 w q - ⟪N, u2⟫ * Split.det3 u1 w q := by
    simp only [Split.det3, Split.inner3]; ring
  rw [h1, h2] at e; linarith

/-- Lagrange identity: `det3 a b (cross M N) = ⟪M, a⟫ ⟪N, b⟫ - ⟪M, b⟫ ⟪N, a⟫`. -/
theorem det3_cross_lagrange (a b M N : ℝ³) :
    Split.det3 a b (cross M N) = ⟪M, a⟫ * ⟪N, b⟫ - ⟪M, b⟫ * ⟪N, a⟫ := by
  simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring

section Link
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³}

/-- **Link winding (any vertex, any number of incident facets).**  Let `v` be a vertex with a cyclic list of link
vertices `p i` and facets `t i ∋ v, p i, p (i+1)`, and assume the chain conditions `p (i+2) ∉ t i`,
`p i ∉ t (i+1)` for `i = 0, …, d-2` (one link of the cycle may fail, e.g. inside a quad facet).  If all `t i` have
one strict sign at `w`, the projected edge vectors `y (p i) - y v` turn strictly one way around `y v`:
all `det3 (y (p i) - y v) (y (p (i+1)) - y v) w` are nonzero of one sign. -/
theorem link_winding (F : S0xFac m S y) {w : ℝ³} {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (v : Fin n) (p : ZMod d → Fin n) (t : ZMod d → Fin m)
    (hv : ∀ i, v ∈ S (t i)) (hp : ∀ i, p i ∈ S (t i)) (hp1 : ∀ i, p (i + 1) ∈ S (t i))
    (hc2 : ∀ i : ZMod d, i.val + 1 < d → p (i + 2) ∉ S (t i))
    (hc0 : ∀ i : ZMod d, i.val + 1 < d → p i ∉ S (t (i + 1)))
    (hs : (∀ i, ⟪F.N (t i), w⟫ < 0) ∨ (∀ i, 0 < ⟪F.N (t i), w⟫)) :
    (∀ i, 0 < Split.det3 (y (p i) - y v) (y (p (i + 1)) - y v) w) ∨
      (∀ i, Split.det3 (y (p i) - y v) (y (p (i + 1)) - y v) w < 0) := by
  set e : Fin n → ℝ³ := fun q => y q - y v with he
  set A : ZMod d → ℝ := fun i => Split.det3 (e (p i)) (e (p (i + 1))) w with hA
  have hperp : ∀ i q, q ∈ S (t i) → ⟪F.N (t i), e q⟫ = 0 := fun i q hq => by
    simp only [he]; rw [F.inner_sub, F.zero _ _ hq, F.zero _ _ (hv i), sub_self]
  have hneg : ∀ i q, q ∉ S (t i) → ⟪F.N (t i), e q⟫ < 0 := fun i q hq => by
    simp only [he]; rw [F.inner_sub, F.zero _ _ (hv i), sub_zero]; exact F.neg _ _ hq
  have hYY : ∀ i j, 0 < ⟪F.N (t i), w⟫ * ⟪F.N (t j), w⟫ := fun i j => by
    rcases hs with h | h
    · exact mul_pos_of_neg_of_neg (h i) (h j)
    · exact mul_pos (h i) (h j)
  have hY : ∀ i, ⟪F.N (t i), w⟫ ≠ 0 := fun i h0 => by have := hYY i i; rw [h0, zero_mul] at this; exact lt_irrefl 0 this
  -- the link step
  have hlink : ∀ i : ZMod d, i.val + 1 < d → A i ≠ 0 ∨ A (i + 1) ≠ 0 → 0 < A i * A (i + 1) := by
    intro i hi hAi
    have I1 := det3_mul_inner_of_perp (F.N (t i)) (e (p i)) (e (p (i + 1))) (e (p (i + 2))) w
      (hperp i _ (hp i)) (hperp i _ (hp1 i))
    have I2 := det3_mul_inner_of_perp (F.N (t (i + 1))) (e (p (i + 1))) (e (p (i + 1 + 1))) (e (p i)) w
      (hperp (i + 1) _ (hp (i + 1))) (hperp (i + 1) _ (hp1 (i + 1)))
    rw [show i + 1 + 1 = i + 2 by ring] at I2
    have hcyc : Split.det3 (e (p (i + 1))) (e (p (i + 2))) (e (p i)) =
        Split.det3 (e (p i)) (e (p (i + 1))) (e (p (i + 2))) := by simp only [Split.det3]; ring
    rw [hcyc] at I2
    set D := Split.det3 (e (p i)) (e (p (i + 1))) (e (p (i + 2)))
    have X1 := hneg i _ (hc2 i hi)
    have X2 := hneg (i + 1) _ (hc0 i hi)
    have hD : D ≠ 0 := by
      intro h0; rw [h0, zero_mul] at I1 I2
      rcases hAi with hAi | hAi
      · exact (mul_ne_zero hAi X1.ne) I1
      · have : A (i + 1) = Split.det3 (e (p (i + 1))) (e (p (i + 2))) w := by
          simp only [hA]; rw [show i + 1 + 1 = i + 2 by ring]
        rw [← this] at I2; exact (mul_ne_zero hAi X2.ne) I2
    have hprod : (A i * A (i + 1)) * (⟪F.N (t i), e (p (i + 2))⟫ * ⟪F.N (t (i + 1)), e (p i)⟫) =
        D ^ 2 * (⟪F.N (t i), w⟫ * ⟪F.N (t (i + 1)), w⟫) := by
      simp only [hA]; rw [show (i + 1 + 1) = i + 2 by ring]; linear_combination
        (Split.det3 (e (p (i + 1))) (e (p (i + 2))) w * ⟪F.N (t (i + 1)), e (p i)⟫) * I1 +
          (D * ⟪F.N (t i), w⟫) * I2
    have hpos : 0 < D ^ 2 * (⟪F.N (t i), w⟫ * ⟪F.N (t (i + 1)), w⟫) :=
      mul_pos (lt_of_le_of_ne (sq_nonneg D) (Ne.symm (pow_ne_zero 2 hD))) (hYY _ _)
    rw [← hprod] at hpos
    exact pos_of_mul_pos_left hpos (mul_pos_of_neg_of_neg X1 X2).le
  -- nondegeneracy at edge `1`: `y (p 1) - y v`, `y (p 2) - y v` independent (facets `t 0`, `t 2`), and
  -- `y (p 0) - y v` off their plane (facet `t 1`)
  have hv1 : (1 : ZMod d).val + 1 < d := by rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr (by omega)]; omega
  have hv0 : (0 : ZMod d).val + 1 < d := by rw [ZMod.val_zero]; omega
  have h12 : (1 : ZMod d) + 1 = 2 := by ring
  have h02 : (0 : ZMod d) + 2 = 2 := by ring
  have h01 : (0 : ZMod d) + 1 = 1 := by ring
  have hA1 : A 1 ≠ 0 := by
    have ha1 : ⟪F.N (t 0), e (p 1)⟫ = 0 := hperp 0 _ (by simpa [h01] using hp1 0)
    have ha2 : ⟪F.N (t 0), e (p 2)⟫ < 0 := hneg 0 _ (by simpa [h02] using hc2 0 hv0)
    have hb2 : ⟪F.N (t 2), e (p 2)⟫ = 0 := hperp 2 _ (hp 2)
    have hb1 : ⟪F.N (t 2), e (p 1)⟫ < 0 := hneg 2 _ (by simpa [h12] using hc0 1 hv1)
    have hL := det3_cross_lagrange (e (p 1)) (e (p 2)) (F.N (t 0)) (F.N (t 2))
    rw [ha1, hb2] at hL
    have hLne : Split.det3 (e (p 1)) (e (p 2)) (cross (F.N (t 0)) (F.N (t 2))) ≠ 0 := by
      rw [hL]; nlinarith [mul_pos_of_neg_of_neg ha2 hb1]
    have hq : ⟪F.N (t 1), e (p 0)⟫ < 0 := hneg 1 _ (by simpa using hc0 0 hv0)
    have hn1 : ⟪F.N (t 1), e (p 1)⟫ = 0 := hperp 1 _ (hp 1)
    have hn2 : ⟪F.N (t 1), e (p 2)⟫ = 0 := hperp 1 _ (by simpa [h12] using hp1 1)
    have I3 := det3_mul_inner_of_perp (F.N (t 1)) (e (p 1)) (e (p 2)) (e (p 0))
      (cross (F.N (t 0)) (F.N (t 2))) hn1 hn2
    have hD0 : Split.det3 (e (p 1)) (e (p 2)) (e (p 0)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at I3; exact mul_ne_zero hLne hq.ne I3
    have I4 := det3_mul_inner_of_perp (F.N (t 1)) (e (p 1)) (e (p 2)) (e (p 0)) w hn1 hn2
    intro h0
    have : Split.det3 (e (p 1)) (e (p 2)) w = 0 := by simpa [hA, h12] using h0
    rw [this, zero_mul] at I4
    exact mul_ne_zero hD0 (hY 1) I4.symm
  have hA0 : A 0 ≠ 0 := by
    have h := hlink 0 hv0 (Or.inr (by rw [h01]; exact hA1))
    intro h0; rw [h0, zero_mul] at h; exact lt_irrefl 0 h
  have hind : ∀ k : ℕ, k < d → 0 < A 0 * A k := by
    intro k
    induction k with
    | zero => intro _; simpa using mul_self_pos.mpr hA0
    | succ k ih =>
      intro hk
      have h0k := ih (by omega)
      have hkv : ((k : ℕ) : ZMod d).val = k := ZMod.val_cast_of_lt (by omega)
      have hl := hlink (k : ZMod d) (by rw [hkv]; omega)
        (Or.inl fun h0 => by rw [h0, mul_zero] at h0k; exact lt_irrefl 0 h0k)
      push_cast
      have : 0 < (A 0 * A k) * (A k * A (k + 1)) := mul_pos h0k hl
      have h2 : (A 0 * A k) * (A k * A (k + 1)) = (A 0 * A (k + 1)) * (A k * A k) := by ring
      rw [h2] at this
      exact pos_of_mul_pos_left this (mul_self_nonneg _)
  have hall : ∀ i, 0 < A 0 * A i := fun i => by
    have := hind i.val (ZMod.val_lt i)
    rwa [ZMod.natCast_zmod_val] at this
  rcases lt_or_gt_of_ne hA0 with hneg0 | hpos0
  · right; intro i; have := hall i; exact (neg_of_mul_pos_right this hneg0.le)
  · left; intro i; have := hall i; exact (pos_of_mul_pos_right this hpos0.le)

/-- A triangle around `0` of edge vectors `y q - y v` is a projected triangle of points around `y v`. -/
theorem tri_of_edge_vectors (v : Fin n) {w a b c : ℝ³} (ha : a + y v ∈ univ.image y) (hb : b + y v ∈ univ.image y)
    (hc : c + y v ∈ univ.image y)
    (h1 : 0 < Split.det3 (b - a) (c - a) w) (h2 : 0 < Split.det3 (b - a) (-a) w)
    (h3 : 0 < Split.det3 (c - b) (-b) w) (h4 : 0 < Split.det3 (a - c) (-c) w) :
    ∃ P ∈ univ.image y, ∃ Q ∈ univ.image y, ∃ R ∈ univ.image y,
      0 < Split.det3 (Q - P) (R - P) w ∧ 0 < Split.det3 (Q - P) (y v - P) w ∧
      0 < Split.det3 (R - Q) (y v - Q) w ∧ 0 < Split.det3 (P - R) (y v - R) w := by
  refine ⟨a + y v, ha, b + y v, hb, c + y v, hc, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [add_sub_add_right_eq_sub, sub_add_cancel_right] using by assumption

/-- **Hidden vertex, link of length 5** (`link_winding` + `DeepC.triangle_of_five_ccw`): a vertex whose five link
facets have one strict sign at `w` lies strictly inside a projected triangle of link points. -/
theorem hidden_of_link5 (F : S0xFac m S y) {w : ℝ³} (v : Fin n) (p : ZMod 5 → Fin n) (t : ZMod 5 → Fin m)
    (hv : ∀ i, v ∈ S (t i)) (hp : ∀ i, p i ∈ S (t i)) (hp1 : ∀ i, p (i + 1) ∈ S (t i))
    (hc2 : ∀ i : ZMod 5, i.val + 1 < 5 → p (i + 2) ∉ S (t i))
    (hc0 : ∀ i : ZMod 5, i.val + 1 < 5 → p i ∉ S (t (i + 1)))
    (hs : (∀ i, ⟪F.N (t i), w⟫ < 0) ∨ (∀ i, 0 < ⟪F.N (t i), w⟫)) :
    ∃ P ∈ univ.image y, ∃ Q ∈ univ.image y, ∃ R ∈ univ.image y,
      0 < Split.det3 (Q - P) (R - P) w ∧ 0 < Split.det3 (Q - P) (y v - P) w ∧
      0 < Split.det3 (R - Q) (y v - Q) w ∧ 0 < Split.det3 (P - R) (y v - R) w := by
  have hmem : ∀ a ∈ ({y (p 0) - y v, y (p 1) - y v, y (p 2) - y v, y (p 3) - y v, y (p 4) - y v} : Finset ℝ³),
      a + y v ∈ univ.image y := fun a ha => by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp
  have hW := link_winding F (by norm_num) v p t hv hp hp1 hc2 hc0 hs
  have e1 : (0 : ZMod 5) + 1 = 1 := by decide
  have e2 : (1 : ZMod 5) + 1 = 2 := by decide
  have e3 : (2 : ZMod 5) + 1 = 3 := by decide
  have e4 : (3 : ZMod 5) + 1 = 4 := by decide
  have e5 : (4 : ZMod 5) + 1 = 0 := by decide
  have asym : ∀ a b : ℝ³, Split.det3 b a w = -Split.det3 a b w := fun a b => by simp only [Split.det3]; ring
  rcases hW with h | h
  · have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    rw [e1] at h0; rw [e2] at h1; rw [e3] at h2; rw [e4] at h3; rw [e5] at h4
    obtain ⟨a, b, c, ⟨ha, hb, hc⟩, d1, d2, d3, d4⟩ :=
      DeepC.triangle_of_five_ccw _ _ _ _ _ w h0 h1 h2 h3 h4
    exact tri_of_edge_vectors v (hmem a ha) (hmem b hb) (hmem c hc) d1 d2 d3 d4
  · have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    rw [e1] at h0; rw [e2] at h1; rw [e3] at h2; rw [e4] at h3; rw [e5] at h4
    have hmem' : ∀ a ∈ ({y (p 0) - y v, y (p 4) - y v, y (p 3) - y v, y (p 2) - y v, y (p 1) - y v} :
        Finset ℝ³), a + y v ∈ univ.image y := fun a ha => by
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨a, b, c, ⟨ha, hb, hc⟩, d1, d2, d3, d4⟩ :=
      DeepC.triangle_of_five_ccw (y (p 0) - y v) (y (p 4) - y v) (y (p 3) - y v) (y (p 2) - y v)
        (y (p 1) - y v) w (by rw [asym]; linarith) (by rw [asym]; linarith) (by rw [asym]; linarith)
        (by rw [asym]; linarith) (by rw [asym]; linarith)
    exact tri_of_edge_vectors v (hmem' a ha) (hmem' b hb) (hmem' c hc) d1 d2 d3 d4

/-- **Hidden vertex, link of length 3** (`link_winding`; the general form of `hidden_of_three_facets_sign`). -/
theorem hidden_of_link3 (F : S0xFac m S y) {w : ℝ³} (v : Fin n) (p : ZMod 3 → Fin n) (t : ZMod 3 → Fin m)
    (hv : ∀ i, v ∈ S (t i)) (hp : ∀ i, p i ∈ S (t i)) (hp1 : ∀ i, p (i + 1) ∈ S (t i))
    (hc2 : ∀ i : ZMod 3, i.val + 1 < 3 → p (i + 2) ∉ S (t i))
    (hc0 : ∀ i : ZMod 3, i.val + 1 < 3 → p i ∉ S (t (i + 1)))
    (hs : (∀ i, ⟪F.N (t i), w⟫ < 0) ∨ (∀ i, 0 < ⟪F.N (t i), w⟫)) :
    ∃ P ∈ univ.image y, ∃ Q ∈ univ.image y, ∃ R ∈ univ.image y,
      0 < Split.det3 (Q - P) (R - P) w ∧ 0 < Split.det3 (Q - P) (y v - P) w ∧
      0 < Split.det3 (R - Q) (y v - Q) w ∧ 0 < Split.det3 (P - R) (y v - R) w := by
  have hW := link_winding F (by norm_num) v p t hv hp hp1 hc2 hc0 hs
  have e1 : (0 : ZMod 3) + 1 = 1 := by decide
  have e2 : (1 : ZMod 3) + 1 = 2 := by decide
  have e3 : (2 : ZMod 3) + 1 = 0 := by decide
  have m : ∀ i, (y (p i) - y v) + y v ∈ univ.image y := fun i => by simp
  rcases hW with h | h
  · have h0 := h 0; have h1 := h 1; have h2 := h 2
    rw [e1] at h0; rw [e2] at h1; rw [e3] at h2
    refine tri_of_edge_vectors v (m 0) (m 1) (m 2) ?_ ?_ ?_ ?_ <;>
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply] at * <;> nlinarith
  · have h0 := h 0; have h1 := h 1; have h2 := h 2
    rw [e1] at h0; rw [e2] at h1; rw [e3] at h2
    refine tri_of_edge_vectors v (m 0) (m 2) (m 1) ?_ ?_ ?_ ?_ <;>
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply] at * <;> nlinarith

end Link

/-- Decide a finite link condition over `ZMod k` case by case. -/
macro "link_dec" : tactic => `(tactic| (intro i; fin_cases i <;> decide))

/-- Vertex `2` (degree 5: link `0.1.6.3.5`, facets `012, 126, 236, 235, 025` = `0, 5, 7, 6, 2`). -/
theorem hidden_two (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hs : (⟪F.N 0, w⟫ < 0 ∧ ⟪F.N 5, w⟫ < 0 ∧ ⟪F.N 7, w⟫ < 0 ∧ ⟪F.N 6, w⟫ < 0 ∧ ⟪F.N 2, w⟫ < 0) ∨
      (0 < ⟪F.N 0, w⟫ ∧ 0 < ⟪F.N 5, w⟫ ∧ 0 < ⟪F.N 7, w⟫ ∧ 0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 2, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 2 - p) w ∧
      0 < Split.det3 (r - q) (x 2 - q) w ∧ 0 < Split.det3 (p - r) (x 2 - r) w :=
  hidden_of_link5 F 2 ![0, 1, 6, 3, 5] ![0, 5, 7, 6, 2] (by link_dec) (by link_dec) (by link_dec) (by link_dec)
    (by link_dec) (by
      rcases hs with ⟨h0, h5, h7, h6, h2⟩ | ⟨h0, h5, h7, h6, h2⟩
      · exact Or.inl fun i => by fin_cases i <;> assumption
      · exact Or.inr fun i => by fin_cases i <;> assumption)

/-- Vertex `3` (degree 4, facets `0345, 235, 236, 346` = `3, 6, 7, 8`): the link `5.2.6.4` extended by the
opposite vertex `0` of the quad `0345` is a 5-cycle `0.5.2.6.4` (facets `3, 6, 7, 8, 3`; the chain link
`4.0 → 0.5` inside the quad is the one not needed), so no genericity condition is needed. -/
theorem hidden_three (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hs : (⟪F.N 3, w⟫ < 0 ∧ ⟪F.N 6, w⟫ < 0 ∧ ⟪F.N 7, w⟫ < 0 ∧ ⟪F.N 8, w⟫ < 0) ∨
      (0 < ⟪F.N 3, w⟫ ∧ 0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 7, w⟫ ∧ 0 < ⟪F.N 8, w⟫)) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 3 - p) w ∧
      0 < Split.det3 (r - q) (x 3 - q) w ∧ 0 < Split.det3 (p - r) (x 3 - r) w :=
  hidden_of_link5 F 3 ![0, 5, 2, 6, 4] ![3, 6, 7, 8, 3] (by link_dec) (by link_dec) (by link_dec) (by link_dec)
    (by link_dec) (by
      rcases hs with ⟨h3, h6, h7, h8⟩ | ⟨h3, h6, h7, h8⟩
      · exact Or.inl fun i => by fin_cases i <;> assumption
      · exact Or.inr fun i => by fin_cases i <;> assumption)

/-! ## The cells of the cover -/

/-- Rim injectivity of a concrete rim, by cases. -/
macro "cell24_rim_inj" : tactic =>
  `(tactic| (intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)))

/-- `C` = cell of `w_C` (rim `0.5.2.3.6`, vertices `1, 4` hidden). -/
def cellC : Cell24 where
  k := 5
  hk := by norm_num
  r := TwoCone.wcRim
  U := {3, 4, 6, 8}
  inj := TwoCone.wcRim_inj
  cyc := by decide

/-- `D` = cell of `w_D` (rim `0.1.2.3.6`, vertices `4, 5` hidden). -/
def cellD : Cell24 where
  k := 5
  hk := by norm_num
  r := TwoCone.rD
  U := TwoCone.U_D
  inj := TwoCone.rD_inj
  cyc := by decide

/-- `D6` = cell of `w_D6` (rim `0.1.2.3.4.6`, vertex `5` hidden). -/
def cellD6 : Cell24 where
  k := 6
  hk := by norm_num
  r := TwoCone.rD6
  U := TwoCone.U_D6
  inj := TwoCone.rD6_inj
  cyc := by decide

/-- `A2` = `T_2` cell `cA2` (rim `0.5.3.6.1`, vertices `2, 4` hidden). -/
def cellA2 : Cell24 where
  k := 5
  hk := by norm_num
  r := TwoCone.cA2
  U := TwoCone.U_A2
  inj := TwoCone.cA2_inj
  cyc := by decide

/-- `B2` = `T_2` cell `cB2` (rim `0.5.3.4.6.1`, vertex `2` hidden). -/
def cellB2 : Cell24 where
  k := 6
  hk := by norm_num
  r := TwoCone.cB2
  U := TwoCone.U_B2
  inj := TwoCone.cB2_inj
  cyc := by decide

/-- `A0` = interior `T_0` cell `cA0` (rim `1.2.5.3.6`, vertices `0, 4` hidden). -/
def cellA0 : Cell24 where
  k := 5
  hk := by norm_num
  r := SF.cA
  U := TwoCone.U_A0
  inj := SF.cA_inj
  cyc := by decide

/-- `B0` = interior `T_0` cell `cB0` (rim `1.2.5.3.4.6`, vertex `0` hidden). -/
def cellB0 : Cell24 where
  k := 6
  hk := by norm_num
  r := SF.cB
  U := TwoCone.U_B0
  inj := SF.cB_inj
  cyc := by decide

/-- `C'` = wall cell `0.5.2.6` (vertices `1, 3, 4` hidden), beyond the facet-`7` wall of `C`; closes sBa_298. -/
def cellC' : Cell24 where
  k := 4
  hk := le_rfl
  r := WallFoot.c0526
  U := WallFoot.U0526
  inj := WallFoot.c0526_inj
  cyc := by decide

/-- Wall cell `0.2.3.6` (vertices `1, 4, 5` hidden). -/
def cell0236 : Cell24 where
  k := 4
  hk := le_rfl
  r := WallFoot.c0236
  U := WallFoot.U0236
  inj := WallFoot.c0236_inj
  cyc := by decide

/-- Wall cell `0.5.3.6` (rim `0.6.3.5`, vertices `1, 2, 4` hidden). -/
def cell0536 : Cell24 where
  k := 4
  hk := le_rfl
  r := Cell0234.c0536
  U := Cell0234.U0536
  inj := by cell24_rim_inj
  cyc := by decide

/-- Rim `0.4.6.2.5` of the pentagon cell. -/
def rP : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

/-- Pentagon cell `0.4.6.2.5` (= Fable's `0.5.2.6.4`; vertices `1, 3` hidden; LEXWHERE family `---+--+++`). -/
def cellP : Cell24 where
  k := 5
  hk := by norm_num
  r := rP
  U := {3, 6, 7, 8}
  inj := by cell24_rim_inj
  cyc := by decide

/-- **The cell list of the cover**: the 7 named cells, `C'`, the wall cells `0.2.3.6`, `0.5.3.6` and the pentagon
`0.4.6.2.5`.  (`π_24` twins are the `sym24 F` side of `CellCoverResidue`.) -/
def cells24 : List Cell24 :=
  [cellC, cellD, cellD6, cellA2, cellB2, cellA0, cellB0, cellC', cell0236, cell0536, cellP]

/-! ## `Hid` for the cells with degree-3 (and vertex-0) hidden vertices -/

theorem cellC_hid : cellC.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact hidden_one F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 1 (by decide)⟩)
  · exact absurd rfl (hm 2)
  · exact absurd rfl (hm 3)
  · exact hidden_four F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 8 (by decide), hcell.1 4 (by decide)⟩)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 4)

theorem cell0236_hid : cell0236.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact hidden_one F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 1 (by decide)⟩)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 2)
  · exact hidden_four F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 8 (by decide), hcell.1 4 (by decide)⟩)
  · exact hidden_five F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 6 (by decide), hcell.1 2 (by decide)⟩)
  · exact absurd rfl (hm 3)

theorem cellD_hid : cellD.Hid := by
  intro x F w hcell
  have e : (univ \ TwoCone.U_D : Finset (Fin 9)) = TwoCone.D_D := by decide
  exact TwoCone.hidden_in_rD_of_cell F ⟨hcell.1, fun t ht => hcell.2 t (by show t ∈ univ \ TwoCone.U_D; rw [e]; exact ht)⟩

theorem cellD6_hid : cellD6.Hid := by
  intro x F w hcell
  have e : (univ \ TwoCone.U_D6 : Finset (Fin 9)) = TwoCone.D_D6 := by decide
  exact TwoCone.hidden_in_rD6_of_cell F
    ⟨hcell.1, fun t ht => hcell.2 t (by show t ∈ univ \ TwoCone.U_D6; rw [e]; exact ht)⟩

theorem cellA0_hid : cellA0.Hid := by
  intro x F w hcell
  have e : (univ \ TwoCone.U_A0 : Finset (Fin 9)) = TwoCone.D_A0 := by decide
  exact TwoCone.hidden_in_cA_of_cell F
    ⟨hcell.1, fun t ht => hcell.2 t (by show t ∈ univ \ TwoCone.U_A0; rw [e]; exact ht)⟩

theorem cellB0_hid : cellB0.Hid := by
  intro x F w hcell
  have e : (univ \ TwoCone.U_B0 : Finset (Fin 9)) = TwoCone.D_B0 := by decide
  exact TwoCone.hidden_in_cB_of_cell F
    ⟨hcell.1, fun t ht => hcell.2 t (by show t ∈ univ \ TwoCone.U_B0; rw [e]; exact ht)⟩

/-- `C'` hides `1` and `4` (degree 3); vertex `3` (degree 4) is `hidden_three`, combined in `cellC'_hid`. -/
theorem cellC'_hid_off3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hcell : CellAt F cellC'.U (univ \ cellC'.U) w) (m : Fin 7) (hm : ∀ i, m ≠ cellC'.r i) (h3 : m ≠ 3) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x m - p) w ∧
      0 < Split.det3 (r - q) (x m - q) w ∧ 0 < Split.det3 (p - r) (x m - r) w := by
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact hidden_one F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 1 (by decide)⟩)
  · exact absurd rfl (hm 2)
  · exact absurd rfl h3
  · exact hidden_four F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 8 (by decide), hcell.1 4 (by decide)⟩)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 3)

/-! ## `Hid` for the cells with hidden vertices `2` (degree 5) and `3` (degree 4) -/

theorem cellA2_hid : cellA2.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact absurd rfl (hm 4)
  · exact hidden_two F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 7 (by decide),
      hcell.2 6 (by decide), hcell.2 2 (by decide)⟩)
  · exact absurd rfl (hm 2)
  · exact hidden_four F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 8 (by decide), hcell.1 4 (by decide)⟩)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 3)

theorem cellB2_hid : cellB2.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact absurd rfl (hm 5)
  · exact hidden_two F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 7 (by decide),
      hcell.2 6 (by decide), hcell.2 2 (by decide)⟩)
  · exact absurd rfl (hm 2)
  · exact absurd rfl (hm 3)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 4)

theorem cell0536_hid : cell0536.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact hidden_one F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 1 (by decide)⟩)
  · exact hidden_two F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 7 (by decide),
      hcell.2 6 (by decide), hcell.2 2 (by decide)⟩)
  · exact absurd rfl (hm 2)
  · exact hidden_four F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 8 (by decide), hcell.1 4 (by decide)⟩)
  · exact absurd rfl (hm 3)
  · exact absurd rfl (hm 1)

theorem cellC'_hid : cellC'.Hid := by
  intro x F w hcell m hm
  by_cases h3 : m = 3
  · subst h3
    exact hidden_three F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 6 (by decide), hcell.1 7 (by decide),
      hcell.1 8 (by decide)⟩)
  · exact cellC'_hid_off3 F hcell m hm h3

theorem cellP_hid : cellP.Hid := by
  intro x F w hcell m hm
  fin_cases m
  · exact absurd rfl (hm 0)
  · exact hidden_one F (Or.inl ⟨hcell.2 0 (by decide), hcell.2 5 (by decide), hcell.2 1 (by decide)⟩)
  · exact absurd rfl (hm 3)
  · exact hidden_three F (Or.inr ⟨hcell.1 3 (by decide), hcell.1 6 (by decide), hcell.1 7 (by decide),
      hcell.1 8 (by decide)⟩)
  · exact absurd rfl (hm 1)
  · exact absurd rfl (hm 4)
  · exact absurd rfl (hm 2)

/-! ## The residue, the open Prop, and the chain -/

/-- **Cell-cover residue**: `CbarIn`, no Split-family view (both sides), and no cell certificate in any cell of `L`,
on `(x, F)` and on the `π_24` twin `(x ∘ π_24, sym24 F)`. -/
def CellCoverResidue (L : List Cell24) (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ (∀ x0 : ℝ, InI5 x x0 → ¬ SplitFamily F x0) ∧
    (∀ x0 : ℝ, InI5 (x ∘ Sym.pi24) x0 → ¬ SplitFamilyTwin F x0) ∧
    ∀ c ∈ L, ∀ w : ℝ³, ¬ CellCert F c w ∧ ¬ CellCert (Sym.sym24 F) c w

/-- A `HoleLeaf` point lies in the cell-cover residue of every cell list. -/
theorem holeLeaf_cellCoverResidue (L : List Cell24) {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F) :
    CellCoverResidue L x F :=
  ⟨h.1, fun _ hI => holeLeaf_not_splitFamily F h hI, fun _ hI => holeLeaf_not_splitFamilyTwin F h hI,
    fun c _ w => ⟨holeLeaf_not_cellCert h c w, holeLeaf_not_cellCert_twin h c w⟩⟩

/-- A `Hole24` point lies in the cell-cover residue of every cell list. -/
theorem hole24_cellCoverResidue (L : List Cell24) {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) :
    CellCoverResidue L x F :=
  holeLeaf_cellCoverResidue L (holeLeaf_of_holeFull (holeFull_of_hole24 h))

/-- **[OPEN] `CellCoverEmpty L`**: on `CbarIn` and `OB1`, some Split-family view or some cell certificate of `L`
(on `x` or its `π_24` twin) exists. -/
def CellCoverEmpty (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → ¬ CellCoverResidue L x F

/-- More cells, weaker obligation. -/
theorem cellCoverEmpty_mono {L L' : List Cell24} (hLL : ∀ c ∈ L, c ∈ L') (h : CellCoverEmpty L) :
    CellCoverEmpty L' := fun x F hC hO hres =>
  h x F hC hO ⟨hres.1, hres.2.1, hres.2.2.1, fun c hc w => hres.2.2.2 c (hLL c hc) w⟩

/-- `CellCoverEmpty L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmpty {L : List Cell24} (hN : CellCoverEmpty L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmpty L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmpty {L : List Cell24} (hN : CellCoverEmpty L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmpty hN x F hO (holeLeaf_of_holeFull hF)

/-- **Chain**: `CellCoverEmpty L` and the restricted special piece `OSpec.OpenSpecialW` rule out every `Hole24`
point. -/
theorem not_hole24_of_cellCoverEmpty {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialW) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ Hole24 x F := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)
  · exact OSpec.hole24_offOB1 hH hO hS

/-- `CellCoverEmpty L` and `OSpec.OpenSpecialW` give `Stmt.Open24`. -/
theorem open24_of_cellCoverEmpty {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialW) : Open24 :=
  OSpec.open24_of_split_W (openOB1_of_cellCoverEmpty hN) hS

/-! ## Old certificates are cell certificates (charts of the named 2-parameter cells, and `C'`)

The wall families (`w_C`, `FamA`, `FamB`) and the `T_2` charts are translated in Type24CellWall.lean
(`wcCert_cellCert`, `famACert_cellCert`, `famBCert_cellCert`, `cA2Cert_cellCert`, `cB2Cert_cellCert`). -/

/-- `w_D` chart: `WDCertAt x F β γ` is a cell certificate of `D` at `wD x β γ`. -/
theorem wdCert_cellCert {F : S0xFac 9 s0x_S24 x} (hC : CbarIn x) {beta gamma : ℝ}
    (h : TwoCone.WDCertAt x F beta gamma) : CellCert F cellD (TwoCone.wD x beta gamma) := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hcell := (TwoCone.wd_cellAt_iff F hC hb hg hr).mpr ⟨h6, h8⟩
  have e : (univ \ TwoCone.U_D : Finset (Fin 9)) = TwoCone.D_D := by decide
  have hcell' : CellAt F cellD.U (univ \ cellD.U) (TwoCone.wD x beta gamma) :=
    ⟨hcell.1, fun t ht => hcell.2 t (by rw [← e]; exact ht)⟩
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (TwoCone.rD t)) (TwoCone.wD x beta gamma) a hD0 hcn sh hsh
    α' μ' hB hO
  have hE : EPCert (fun t => x (TwoCone.rD t)) (TwoCone.wD x beta gamma) := ⟨a, s, α, μ, hD0, hrows⟩
  exact cellCert_of_ep F cellD_hid hcell' hE

/-- `w_D6` chart: `WD6CertAt x F β γ` is a cell certificate of `D6` at `wD x β γ`. -/
theorem wd6Cert_cellCert {F : S0xFac 9 s0x_S24 x} (hC : CbarIn x) {beta gamma : ℝ}
    (h : TwoCone.WD6CertAt x F beta gamma) : CellCert F cellD6 (TwoCone.wD x beta gamma) := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hcell := (TwoCone.wd6_cellAt_iff F hC hb hg hr).mpr ⟨h6, h8⟩
  have e : (univ \ TwoCone.U_D6 : Finset (Fin 9)) = TwoCone.D_D6 := by decide
  have hcell' : CellAt F cellD6.U (univ \ cellD6.U) (TwoCone.wD x beta gamma) :=
    ⟨hcell.1, fun t ht => hcell.2 t (by rw [← e]; exact ht)⟩
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (TwoCone.rD6 t)) (TwoCone.wD x beta gamma) a hD0 hcn sh hsh
    α' μ' hB hO
  have hE : EPCert (fun t => x (TwoCone.rD6 t)) (TwoCone.wD x beta gamma) := ⟨a, s, α, μ, hD0, hrows⟩
  exact cellCert_of_ep F cellD6_hid hcell' hE

/-- Interior `T_0` chart: `CA0CertAt x F b γ` is a cell certificate of `A0` at `uT0 x b γ`. -/
theorem cA0Cert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {b gamma : ℝ}
    (h : TwoCone.CA0CertAt x F b gamma) : CellCert F cellA0 (TwoCone.uT0 x b gamma) := by
  rcases h with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hcell := (TwoCone.cA0_cellAt_iff F hC hb hg).mpr ⟨hlo, hhi, hnC, hs6⟩
  have e : (univ \ TwoCone.U_A0 : Finset (Fin 9)) = TwoCone.D_A0 := by decide
  have hcell' : CellAt F cellA0.U (univ \ cellA0.U) (TwoCone.uT0 x b gamma) :=
    ⟨hcell.1, fun t ht => hcell.2 t (by rw [← e]; exact ht)⟩
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (SF.cA t)) (TwoCone.uT0 x b gamma) a hD0 hcn sh hsh
    α' μ' hB hO
  have hE : EPCert (fun t => x (SF.cA t)) (TwoCone.uT0 x b gamma) := ⟨a, s, α, μ, hD0, hrows⟩
  exact cellCert_of_ep F cellA0_hid hcell' hE

/-- Interior `T_0` chart: `CB0CertAt x F b γ` is a cell certificate of `B0` at `uT0 x b γ`. -/
theorem cB0Cert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {b gamma : ℝ}
    (h : TwoCone.CB0CertAt x F b gamma) : CellCert F cellB0 (TwoCone.uT0 x b gamma) := by
  rcases h with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hcell := (TwoCone.cB0_cellAt_iff F hC hb hg).mpr ⟨hlo, hhi, hnC, hs6⟩
  have e : (univ \ TwoCone.U_B0 : Finset (Fin 9)) = TwoCone.D_B0 := by decide
  have hcell' : CellAt F cellB0.U (univ \ cellB0.U) (TwoCone.uT0 x b gamma) :=
    ⟨hcell.1, fun t ht => hcell.2 t (by rw [← e]; exact ht)⟩
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (SF.cB t)) (TwoCone.uT0 x b gamma) a hD0 hcn sh hsh
    α' μ' hB hO
  have hE : EPCert (fun t => x (SF.cB t)) (TwoCone.uT0 x b gamma) := ⟨a, s, α, μ, hD0, hrows⟩
  exact cellCert_of_ep F cellB0_hid hcell' hE

/-- `C'` (Lemma F4 form, `WallFoot.cellAt0526_lexAny`): an open-cell view whose rim depths are not a crown is a
cell certificate of `C'`. -/
theorem cellC'_cert_of_mixed (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hw : CellAt F WallFoot.U0526 WallFoot.Dn0526 w)
    (hn : ⟪x 0, w⟫ < ⟪x 5, w⟫ ∨ ⟪x 0, w⟫ < ⟪x 6, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 5, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 6, w⟫)
    (hp : ⟪x 5, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 5, w⟫ < ⟪x 2, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 2, w⟫) :
    CellCert F cellC' w := by
  have e : (univ \ WallFoot.U0526 : Finset (Fin 9)) = WallFoot.Dn0526 := by decide
  refine ⟨⟨hw.1, fun t ht => hw.2 t (by rw [← e]; exact ht)⟩, Or.inl (robUni_four_of_mixed ?_ ?_)⟩
  · rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
  · rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [cellC', WallFoot.c0526, Matrix.cons_val]; linarith⟩

end Minimality.T24.Cell
