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
* `Hid` proved for C, D, D6, A0, B0, `0.2.3.6` (degree-3 hidden vertices via `hidden_of_three_facets`, and the
  existing degree-5 lemma for vertex 0).  Not proved (no degree-4 / generic degree-5 lemma yet): A2, B2, `0.5.3.6`
  (vertex 2), C', pentagon (vertex 3); there the Edge-Plane branch carries `HiddenInTriangles` explicitly.
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

/-- `C'` hides `1` and `4` automatically (degree 3); vertex `3` (degree 4, link `5.2.6.4`) is the only vertex whose
hiding the Edge-Plane branch of `C'` must check. -/
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

The wall families (`w_C`, `FamA`, `FamB`, Split family) and the `T_2` cells (vertex `2` hidden, degree 5, no
standalone `HiddenInTriangles` lemma) are not translated here; see the report in nopert229
notes/TYPE24-HOLE-STATEMENT.md. -/

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
