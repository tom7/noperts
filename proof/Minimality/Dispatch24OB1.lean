module

public import Mathlib
public import Minimality.RimClass24
public import Minimality.LeafBGen
public import Minimality.LemmaTQHex
public import Minimality.LinkRim24
public import Pipeline.Similarity

@[expose] public section

/-!
# Type 24, obtuse corner OB1: the dispatcher at the orthocentre view

Setting: `F : S0xFac 9 s0x_S24 x` (type 24), vertex `1` an obtuse corner (edges `x 0 - x 1`,
`x 2 - x 1`, `x 6 - x 1` independent, pairwise `⟪·,·⟫ ≤ 0`), `u* = NCone.apexView v 1` the
orthocentre view of the corner, and no facet edge-on at `u*`.  The rim class split
`orthocentre_rim_class_split_closed` (RimClass24) puts `u*` in one of the open cells of three
classes; this file closes every cell for which a Lean leaf exists and names the rest:

* contiguous ends (22 cells, `FeasibleCellC`): Theorem P, `theoremP24_of_obtuse_corner`;
* 3-rim cells `{t}` (`t = 2, 4, 6, 7, 8`): `LemmaTQ2.isRupert_of_cell_single`; the waist cell
  (all six variable facets front): `TriangleT.isRupert_of_cell026` (rim `0 2 6`);
* single-isolated end (7 rims): Leaf B (`isRupert_leafB_cell`, from the rim-generic
  `LeafBGen.isRupert_leafB_gen`) when `A_r(c*) > 0` (`leafBA`); the rest, `A_r(c*) ≤ 0`, is
  `Residual_SI`;
* multi-isolated: `04325`, `04635` by `LemmaTQ2.lemmaTQ'`; `0435` is the Theorem P cell `c0435`; the
  hexagon `046325` by `LemmaTQHex.lemmaTQHex` under its hypotheses, else `Residual_Hex`.

Main theorem: `dispatch24OB1`.

Bridges proved here:
* `rim_orient`: at a strict cell view, the rim of an `S0xCycUD` cycle is a strictly convex polygon
  on the screen, with all triple tests of one sign (either orientation occurs: the mirror image of
  a type-24 solid is a type-24 solid with the same labels);
* `isRupert_of_neg_image`: Rupertness of `-x`, used to reduce the negative orientation to Leaf B;
* `isRupert_leafB_rim`: Leaf B on a labelled rim `c` (stretch `V = c a, E' = c (a+1),
  E'' = c (a+2), W = c (a+3)`, third end `c b`) in either orientation;
* `isRupert_leafB_ortho`: the same at the orthocentre view of a strict `S0xCycUD` cell, the ties and
  depth rows from `orthocentre_depths`; the seven rims are `decide` instances of it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.OB1
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.TheoremP Minimality.T24.RimClass

/-! ## Rim orientation at a strict cell view -/

section Orient
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- One rim edge `p → q` of a strict cell (shared by a front facet `a` and a back facet `b`): all
other vertices are strictly on one side of it on the screen. -/
theorem edge_det_sign (F : S0xFac m S x) {u : ℝ³} {a b : Fin m} {p q : Fin n} (hpq : x p ≠ x q)
    (hpa : p ∈ S a) (hpb : p ∈ S b) (hqa : q ∈ S a) (hqb : q ∈ S b)
    (hA : 0 < ⟪F.N a, u⟫) (hB : ⟪F.N b, u⟫ < 0)
    (hoff : ∀ r, r ≠ p → r ≠ q → r ∉ S a ∨ r ∉ S b) :
    (∀ r, r ≠ p → r ≠ q → 0 < det3 (x q - x p) (x r - x p) u) ∨
      (∀ r, r ≠ p → r ≠ q → det3 (x q - x p) (x r - x p) u < 0) := by
  have hNa : ⟪F.N a, x q - x p⟫ = 0 := by
    rw [F.inner_sub, F.zero a q hqa, F.zero a p hpa]; ring
  have hNb : ⟪F.N b, x q - x p⟫ = 0 := by
    rw [F.inner_sub, F.zero b q hqb, F.zero b p hpb]; ring
  obtain ⟨κ, hκ⟩ := Link24R.cross_par_of_orth (F.N a) (F.N b) (x q - x p)
    (sub_ne_zero.mpr hpq.symm) hNa hNb
  have R : ∀ r, r ≠ p → r ≠ q → 0 < κ * det3 (x q - x p) (x r - x p) u := by
    intro r hrp hrq
    rw [Link24R.edge_ident (F.N a) (F.N b) _ _ u κ hκ, F.inner_sub, F.inner_sub,
      F.zero a p hpa, F.zero b p hpb, sub_zero, sub_zero]
    have la := F.le a r
    have lb := F.le b r
    rcases hoff r hrp hrq with h | h
    · have := F.neg a r h
      nlinarith [mul_nonneg (neg_nonneg.mpr lb) hA.le]
    · have := F.neg b r h
      nlinarith [mul_nonneg (neg_nonneg.mpr la) (neg_nonneg.mpr hB.le)]
  rcases lt_or_ge 0 κ with hκ0 | hκ0
  · left; intro r hrp hrq
    have := R r hrp hrq
    by_contra hc; push Not at hc
    nlinarith
  · right; intro r hrp hrq
    have := R r hrp hrq
    by_contra hc; push Not at hc
    nlinarith

/-- **Rim orientation.**  At a strict cell view `u` whose rim is the `S0xCycUD` cycle `c`, the
triple tests of the rim have one common strict sign: positive for every edge and every vertex off
the edge, or negative for all of them. -/
theorem rim_orient {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} (hc : Function.Injective c) (h1 : (1 : ZMod k) ≠ 0)
    (h2 : (2 : ZMod k) ≠ 0) {U D : Finset (Fin m)} (hcyc : S0xCycUD S c U D) {u : ℝ³}
    (hu : CellAt F U D u) :
    (∀ i r, r ≠ c i → r ≠ c (i + 1) → 0 < det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u) ∨
      (∀ i r, r ≠ c i → r ≠ c (i + 1) →
        det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u < 0) := by
  set Pos : ZMod k → Prop := fun i => ∀ r, r ≠ c i → r ≠ c (i + 1) →
    0 < det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u
  set Neg : ZMod k → Prop := fun i => ∀ r, r ≠ c i → r ≠ c (i + 1) →
    det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u < 0
  have ne1 : ∀ i : ZMod k, c i ≠ c (i + 1) := fun i h => by
    have := hc h; apply h1; linear_combination -this
  have ne2 : ∀ i : ZMod k, c i ≠ c (i + 1 + 1) := fun i h => by
    have := hc h; apply h2; linear_combination -this
  have hPN : ∀ i, Pos i ∨ Neg i := by
    intro i
    obtain ⟨a, ha, b, hb, hpa, hpb, hqa, hqb, hoff⟩ := hcyc i
    exact edge_det_sign F (fun h => ne1 i (hx h)) hpa hpb hqa hqb (hu.1 a ha) (hu.2 b hb) hoff
  -- the triple `(c i, c (i+1), c (i+2))` read from edge `i` and from edge `i + 1`
  have cyc : ∀ i : ZMod k, det3 (x (c (i + 1 + 1)) - x (c (i + 1))) (x (c i) - x (c (i + 1))) u =
      det3 (x (c (i + 1)) - x (c i)) (x (c (i + 1 + 1)) - x (c i)) u := fun i =>
    det3_cyc (x (c i)) (x (c (i + 1))) (x (c (i + 1 + 1))) u
  have stepP : ∀ i, Pos i → Pos (i + 1) := by
    intro i hP
    have h0 := hP (c (i + 1 + 1)) (ne2 i).symm (ne1 (i + 1)).symm
    rcases hPN (i + 1) with h | h
    · exact h
    · have := h (c i) (ne1 i) (ne2 i)
      rw [cyc] at this; linarith
  have stepN : ∀ i, Neg i → Neg (i + 1) := by
    intro i hN
    have h0 := hN (c (i + 1 + 1)) (ne2 i).symm (ne1 (i + 1)).symm
    rcases hPN (i + 1) with h | h
    · have := h (c i) (ne1 i) (ne2 i)
      rw [cyc] at this; linarith
    · exact h
  have all : ∀ P : ZMod k → Prop, (∀ i, P i → P (i + 1)) → P 0 → ∀ i, P i := by
    intro P hs h0 i
    have : ∀ j : ℕ, P (j : ZMod k) := by
      intro j; induction j with
      | zero => simpa using h0
      | succ j ih => simpa [Nat.cast_succ] using hs _ ih
    simpa using this i.val
  rcases hPN 0 with h | h
  · exact Or.inl (all Pos stepP h)
  · exact Or.inr (all Neg stepN h)

end Orient

/-! ## Point reflection -/

/-- Rupertness is invariant under the point reflection `z ↦ -z`. -/
theorem isRupert_of_neg_image (V : Finset ℝ³) (h : IsRupert (V.image fun z => -z)) :
    IsRupert V := by
  classical
  have hM : (-1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']; simp
  have h1 := Noperts.Pipeline.isRupert_image_similarity 0 1 one_pos _ hM _ h
  convert h1 using 1
  rw [Finset.image_image]
  have : ((fun z : ℝ³ => (0 : ℝ³) + (1 : ℝ) • (-1 : Matrix (Fin 3) (Fin 3) ℝ).toEuclideanLin z) ∘
      fun z => -z) = id := by
    funext z; simp
  rw [this, Finset.image_id]

theorem det3_neg_sub' (a b c d u : ℝ³) :
    det3 (-a - -b) (-c - -d) (-u) = -det3 (a - b) (c - d) u := by
  simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring

/-! ## Leaf B on a labelled rim, either orientation -/

/-- **Leaf B on a labelled rim** (`LeafBGen.isRupert_leafB_gen` for both orientations).  The rim
`c` of the solid `x` at the view `u` has one common strict sign of all triple tests (`rim_orient`);
`V = c a`, `E' = c (a+1)`, `E'' = c (a+2)`, `W = c (a+3)`, `E = c b`; the depths of `E', E'', E` tie
and every other rim corner is strictly deeper; and the Leaf B quantity
`A = det3 (E' - V) (E'' - E') u * det3 (E' - V) (E'' - W) u` (the rim orientation times the
antipodality row) is positive.  Then the solid is Rupert.  The negative orientation is the
positive one for `-x` at `-u`. -/
theorem isRupert_leafB_rim {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin 7 → ℝ³}
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {u : ℝ³} (hu : u ≠ 0)
    (hor : (∀ i r, r ≠ c i → r ≠ c (i + 1) →
        0 < det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u) ∨
      (∀ i r, r ≠ c i → r ≠ c (i + 1) → det3 (x (c (i + 1)) - x (c i)) (x r - x (c i)) u < 0))
    (a b : ZMod k) (hb0 : b ≠ a) (hb1 : b ≠ a + 1) (hb2 : b ≠ a + 2) (hb3 : b ≠ a + 3)
    (t1 : ⟪x (c (a + 1)), u⟫ = ⟪x (c (a + 2)), u⟫) (tb : ⟪x (c b), u⟫ = ⟪x (c (a + 2)), u⟫)
    (hv : ∀ j, j ≠ a + 1 → j ≠ a + 2 → j ≠ b → ⟪x (c (a + 2)), u⟫ < ⟪x (c j), u⟫)
    (hA : 0 < det3 (x (c (a + 1)) - x (c a)) (x (c (a + 2)) - x (c (a + 1))) u *
      det3 (x (c (a + 1)) - x (c a)) (x (c (a + 2)) - x (c (a + 3))) u) :
    IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨-, d20, -, d21, -, -⟩ := LeafBGen.four_distinct hk a
  have hcne : ∀ {i j : ZMod k}, i ≠ j → c i ≠ c j := fun h h' => h (hc h')
  have eo : det3 (x (c (a + 1)) - x (c a)) (x (c (a + 2)) - x (c (a + 1))) u =
      det3 (x (c (a + 1)) - x (c a)) (x (c (a + 2)) - x (c a)) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have ek : det3 (x (c (a + 1)) - x (c a)) (x (c (a + 2)) - x (c (a + 3))) u =
      -det3 (x (c (a + 1)) - x (c a)) (x (c (a + 3)) - x (c (a + 2))) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [eo, ek] at hA
  rcases hor with P | N
  · have ho := P a (c (a + 2)) (hcne d20) (hcne d21)
    have key : det3 (x (c (a + 1)) - x (c a)) (x (c (a + 3)) - x (c (a + 2))) u < 0 := by
      by_contra h; push Not at h; nlinarith [mul_nonneg ho.le h]
    refine LeafBGen.isRupert_leafB_gen _ hk (fun i => x (c i))
      (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hu ?_ ?_ a b hb0 hb1 hb2 hb3 t1 tb
      hv key
    · intro i j hi hj; exact P i (c j) (hcne hi) (hcne hj)
    · intro v hv' hvp i
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv'
      exact P i m (fun h => hvp i (by rw [h])) (fun h => hvp (i + 1) (by rw [h]))
  · have ho := N a (c (a + 2)) (hcne d20) (hcne d21)
    have key : 0 < det3 (x (c (a + 1)) - x (c a)) (x (c (a + 3)) - x (c (a + 2))) u := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg (neg_nonneg.mpr ho.le) (neg_nonneg.mpr h)]
    apply isRupert_of_neg_image
    rw [Finset.image_image]
    have ip : ∀ i, ⟪-x i, -u⟫ = ⟪x i, u⟫ := fun i => by simp
    refine LeafBGen.isRupert_leafB_gen _ hk (fun i => -x (c i))
      (fun i => Finset.mem_image_of_mem ((fun z => -z) ∘ x) (Finset.mem_univ (c i)))
      (neg_ne_zero.mpr hu) ?_ ?_ a b hb0 hb1 hb2 hb3 (by simp only [ip]; exact t1)
      (by simp only [ip]; exact tb) (fun j h1 h2 h3 => by simp only [ip]; exact hv j h1 h2 h3) ?_
    · intro i j hi hj
      rw [det3_neg_sub']
      exact neg_pos.mpr (N i (c j) (hcne hi) (hcne hj))
    · intro v hv' hvp i
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv'
      dsimp only [Function.comp] at hvp ⊢
      rw [det3_neg_sub']
      exact neg_pos.mpr (N i m (fun h => hvp i (by rw [h])) (fun h => hvp (i + 1) (by rw [h])))
    · rw [det3_neg_sub']; linarith

/-! ## The orthocentre view -/

section Ortho
variable {x : Fin 7 → ℝ³}

theorem cellAt_mono {F : S0xFac 9 s0x_S24 x} {U D U' D' : Finset (Fin 9)} {u : ℝ³}
    (h : CellAt F U D u) (hU : U' ⊆ U) (hD : D' ⊆ D) : CellAt F U' D' u :=
  ⟨fun t ht => h.1 t (hU ht), fun t ht => h.2 t (hD ht)⟩

/-- Depths at the orthocentre view `u* = apexView v 1`: the ends `0, 2, 6` tie, and `3`, `4`, `5`
are strictly deeper (Theorem P's `σ > 1`). -/
theorem orthocentre_depths (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    u ≠ 0 ∧ ⟪x 2, u⟫ = ⟪x 0, u⟫ ∧ ⟪x 2, u⟫ = ⟪x 6, u⟫ ∧ ⟪x 2, u⟫ < ⟪x 3, u⟫ ∧
      ⟪x 2, u⟫ < ⟪x 4, u⟫ ∧ ⟪x 2, u⟫ < ⟪x 5, u⟫ := by
  intro u
  set p := x 1
  set v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
  have hu : ∀ e, ⟪v e, u⟫ = 1 := fun e => Minimality.NCone.inner_edge_apexView hli 1 e
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - p) e
  have hxy : ∀ i, x i = p + ∑ e, y i e • v e := by
    intro i
    have hrepr := B.sum_repr (x i - p)
    have hcoe : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hsum : ∑ e, y i e • v e = x i - p := by
      show ∑ e, B.repr (x i - p) e • v e = x i - p
      rw [← hcoe]
      exact hrepr
    rw [hsum]
    abel
  have ⟨hV3, hV4, hV5, hE0, hE2, hE6⟩ := type24_sigma_gt_one F p v y hxy rfl rfl rfl rfl
  have D := depth_orthocentre x p v y hxy u hu
  have d30 := D 3 2
  have d40 := D 4 2
  have d50 := D 5 2
  have d02 := D 0 2
  have d62 := D 6 2
  simp only [inner_sub_left] at d30 d40 d50 d02 d62
  have hu0 : u ≠ 0 := by
    intro h0; have := hu 0; rw [h0, inner_zero_right] at this; norm_num at this
  refine ⟨hu0, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The Leaf B quantity of a rim stretch `V, E', E'', W` (`LEAFB24.md` section 1.3): the rim
orientation `det3 (E' - V) (E'' - E') u` times the antipodality row `det3 (E' - V) (E'' - W) u`.
Positive iff the interior angles of the screen rim at `E'` and `E''` sum to less than `π`. -/
noncomputable def leafBAv (x : Fin 7 → ℝ³) (u : ℝ³) (V E₁ E₂ W : Fin 7) : ℝ :=
  det3 (x E₁ - x V) (x E₂ - x E₁) u * det3 (x E₁ - x V) (x E₂ - x W) u

/-- **`A(c*)` of the seven single-isolated rims** (`LEAFB24.md` sections 1 and 5), with
`(V, E', E'', W)`: `04625` `(4,6,2,5)`, `043625` `(3,6,2,5)`, `046235` `(4,6,2,3)`, `05236`
`(3,6,0,5)`, `052346` `(4,6,0,5)`, `02364` `(4,0,2,3)`, `025364` `(4,0,2,5)`. -/
noncomputable def leafBA (x : Fin 7 → ℝ³) (u : ℝ³) : SingleIsoRim → ℝ
  | .c04625 => leafBAv x u 4 6 2 5
  | .c043625 => leafBAv x u 3 6 2 5
  | .c046235 => leafBAv x u 4 6 2 3
  | .c05236 => leafBAv x u 3 6 0 5
  | .c052346 => leafBAv x u 4 6 0 5
  | .c02364 => leafBAv x u 4 0 2 3
  | .c025364 => leafBAv x u 4 0 2 5

/-- **Leaf B at the orthocentre view, any single-isolated-type rim.**  `u*` in the open cell of
an `S0xCycUD` rim `c` with `V = c a, E' = c (a+1), E'' = c (a+2), W = c (a+3)`, the three ends
`E', E'', E = c b` and the other corners in `{3, 4, 5}`, and `A > 0`: Rupert. -/
theorem isRupert_leafB_ortho {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    {c : ZMod k → Fin 7} (hc : Function.Injective c) (h1 : (1 : ZMod k) ≠ 0)
    (h2 : (2 : ZMod k) ≠ 0) {U D : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U D)
    (hcell : CellAt F U D (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1))
    (a b : ZMod k) (hb0 : b ≠ a) (hb1 : b ≠ a + 1) (hb2 : b ≠ a + 2) (hb3 : b ≠ a + 3)
    (hE : ∀ j, (j = a + 1 ∨ j = a + 2 ∨ j = b) → c j = 0 ∨ c j = 2 ∨ c j = 6)
    (hV : ∀ j, j ≠ a + 1 → j ≠ a + 2 → j ≠ b → c j = 3 ∨ c j = 4 ∨ c j = 5)
    {V E₁ E₂ W : Fin 7} (cV : c a = V) (c1 : c (a + 1) = E₁) (c2 : c (a + 2) = E₂)
    (c3 : c (a + 3) = W)
    (hA : 0 < leafBAv x (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1)
      V E₁ E₂ W) :
    IsRupert (Finset.univ.image x) := by
  set u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
  obtain ⟨hu0, t0, t6, d3, d4, d5⟩ := orthocentre_depths F hli
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hend : ∀ j, (j = a + 1 ∨ j = a + 2 ∨ j = b) → ⟪x (c j), u⟫ = ⟪x 2, u⟫ := by
    intro j hj
    rcases hE j hj with h | h | h <;> rw [h] <;> first | exact t0.symm | exact t6.symm
  have hdeep : ∀ j, j ≠ a + 1 → j ≠ a + 2 → j ≠ b → ⟪x 2, u⟫ < ⟪x (c j), u⟫ := by
    intro j j1 j2 jb
    rcases hV j j1 j2 jb with h | h | h <;> rw [h]
    exacts [d3, d4, d5]
  have e1 := hend (a + 1) (Or.inl rfl)
  have e2 := hend (a + 2) (Or.inr (Or.inl rfl))
  have eb := hend b (Or.inr (Or.inr rfl))
  refine isRupert_leafB_rim hk hc hu0 (rim_orient F hx hc h1 h2 hcyc hcell) a b hb0 hb1 hb2 hb3
    (by rw [e1, e2]) (by rw [eb, e2]) (fun j j1 j2 jb => by rw [e2]; exact hdeep j j1 j2 jb) ?_
  rw [cV, c1, c2, c3]; exact hA

/-- **Leaf B on the seven single-isolated rims.**  `u*` in the open cell of the single-isolated
rim `r` and `A_r(c*) > 0` (`leafBA`): Rupert. -/
theorem isRupert_leafB_cell (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) (r : SingleIsoRim)
    (hcell : InSingleIsoCell F (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1) r)
    (hA : 0 < leafBA x (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1) r) :
    IsRupert (Finset.univ.image x) := by
  cases r
  case c04625 =>
    exact isRupert_leafB_ortho (k := 5) (by norm_num) F hli inj_c04625 (by decide) (by decide)
      cyc04625 hcell 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c043625 =>
    exact isRupert_leafB_ortho (k := 6) (by norm_num) F hli inj_c043625 (by decide) (by decide)
      cyc043625 hcell 2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c046235 =>
    exact isRupert_leafB_ortho (k := 6) (by norm_num) F hli inj_c046235 (by decide) (by decide)
      cyc046235 hcell 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c05236 =>
    exact isRupert_leafB_ortho (k := 5) (by norm_num) F hli inj_c05236 (by decide) (by decide)
      cyc05236 hcell 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c052346 =>
    exact isRupert_leafB_ortho (k := 6) (by norm_num) F hli inj_c052346 (by decide) (by decide)
      cyc052346 hcell 4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c02364 =>
    exact isRupert_leafB_ortho (k := 5) (by norm_num) F hli inj_c02364 (by decide) (by decide)
      cyc02364 hcell 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA
  case c025364 =>
    exact isRupert_leafB_ortho (k := 6) (by norm_num) F hli inj_c025364 (by decide) (by decide)
      cyc025364 hcell 5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA

end Ortho

/-! ## The residual cases and the dispatcher -/

section Dispatch
variable {x : Fin 7 → ℝ³}

/-- Leaf B holds in Lean on the single-isolated rim `r` at the view `u`: `A_r(u) > 0`
(`leafBA`, `isRupert_leafB_cell`), for each of the seven rims. -/
def LeafBLean (x : Fin 7 → ℝ³) (u : ℝ³) (r : SingleIsoRim) : Prop :=
  0 < leafBA x u r

/-- **Residual, single-isolated end.**  `u` lies in the open cell of a single-isolated-end rim `r`
(`InSingleIsoCell`, seven rims) and `A_r(u) ≤ 0` (`leafBA`): the interior screen angles of the rim
at its two adjacent ends `E'`, `E''` sum to at least `π`. -/
def Residual_SI (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ∃ r : SingleIsoRim, InSingleIsoCell F u r ∧ leafBA x u r ≤ 0

/-- The hypothesis of `lemmaTQHex` (HEXSPLIT24 "not S"): NOT (`b3 < 1` and `c3 < 1`), i.e. not both
`⟪N_016, x3 - x2⟫ > 0` and `⟪N_012, x3 - x6⟫ > 0`; plus the special positions `c3 = 1`, `b3 ≤ 1`
(needs `⟪N_346, x2 - x1⟫ > 0`) and `b3 = 1`, `c3 ≤ 1` (needs `⟪N_235, x6 - x1⟫ > 0`). -/
def HexTQHyp (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ (0 < ⟪F.N 1, x 3 - x 2⟫ ∧ 0 < ⟪F.N 0, x 3 - x 6⟫) ∧
    (⟪F.N 0, x 3 - x 6⟫ = 0 → 0 ≤ ⟪F.N 1, x 3 - x 2⟫ → 0 < ⟪F.N 8, x 2 - x 1⟫) ∧
    (⟪F.N 1, x 3 - x 2⟫ = 0 → 0 ≤ ⟪F.N 0, x 3 - x 6⟫ → 0 < ⟪F.N 6, x 6 - x 1⟫)

/-- **Residual, hexagon.**  `u` lies in the open hexagon cell `046325` (front facets exactly
`0345, 235, 346`) and the hypothesis of `lemmaTQHex` fails: `b3 < 1 ∧ c3 < 1` (HEXSPLIT24 "S"), or a
special position `c3 = 1, b3 ≤ 1, ⟪N_346, x2 - x1⟫ ≤ 0` (resp. `b3 = 1, c3 ≤ 1,
⟪N_235, x6 - x1⟫ ≤ 0`). -/
def Residual_Hex (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  InMultiIsoCell F u .c046325 ∧ ¬ HexTQHyp F

/-- **Type 24, obtuse corner OB1, dispatcher.**  Type-24 solid, vertex `1` an obtuse corner
(independent edges, pairwise `⟪·,·⟫ ≤ 0`), no facet edge-on at the orthocentre view
`u* = apexView v 1`.  Then the solid is Rupert, or `u*` is in a single-isolated cell without a Lean
Leaf B (`Residual_SI`), or in the hexagon cell outside Lemma TQ-hex (`Residual_Hex`). -/
theorem dispatch24OB1 (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f →
      ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9,
      ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    IsRupert (Finset.univ.image x) ∨ Residual_SI F u ∨ Residual_Hex F u := by
  intro u
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1 := fun e =>
    Minimality.NCone.inner_edge_apexView hli 1 e
  have hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 := by simpa using hobt 0 1 (by decide)
  have hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 := by simpa using hobt 0 2 (by decide)
  have hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by simpa using hobt 1 2 (by decide)
  rcases orthocentre_rim_class_split_closed F hli hobt h_no_edge_on with hA | hB | hC
  · -- contiguous ends or a 3-rim cell
    left
    rcases hA with ⟨cell, hcell⟩ | h3
    · exact theoremP24_of_obtuse_corner F hli hobt cell hcell
    rcases h3 with h | h | h | h | h | h
    · exact TQ.isRupert_of_cell_single F (t := 2) (by decide) (by decide) h
    · exact TQ.isRupert_of_cell_single F (t := 4) (by decide) (by decide) h
    · exact TQ.isRupert_of_cell_single F (t := 6) (by decide) (by decide) h
    · exact TQ.isRupert_of_cell_single F (t := 7) (by decide) (by decide) h
    · exact TQ.isRupert_of_cell_single F (t := 8) (by decide) (by decide) h
    · exact Hexagon.isRupert_of_cell026 F (cellAt_mono h (by decide) (by decide))
  · -- single-isolated end
    obtain ⟨r, hr⟩ := hB
    by_cases hL : LeafBLean x u r
    · exact Or.inl (isRupert_leafB_cell F hli r hr hL)
    · exact Or.inr (Or.inl ⟨r, hr, not_lt.mp hL⟩)
  · -- multi-isolated ends
    obtain ⟨r, hr⟩ := hC
    cases r
    case c046325 =>
      by_cases hT : HexTQHyp F
      · left
        exact TQ.lemmaTQHex F hx hli hab hac hbc hu (cellAt_mono hr (by decide) (by decide))
          hT.1 hT.2.1 hT.2.2
      · exact Or.inr (Or.inr ⟨hr, hT⟩)
    case c04325 =>
      exact Or.inl (TQ.lemmaTQ' F hx hli hab hac hbc hu
        (Or.inl (cellAt_mono hr (by decide) (by decide))))
    case c04635 =>
      exact Or.inl (TQ.lemmaTQ' F hx hli hab hac hbc hu
        (Or.inr (cellAt_mono hr (by decide) (by decide))))
    case c0435 =>
      exact Or.inl (theoremP24_of_obtuse_corner F hli hobt .c0435
        (show CellAt F U0435 D0435 u from cellAt_mono hr (by decide) (by decide)))

end Dispatch

end Minimality.T24.OB1
