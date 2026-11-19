module

public import Mathlib
public import Minimality.RimClass24
public import Minimality.TorqueLeaves
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
* single-isolated end (7 rims): Leaf B (`isRupert_leafB_04625_of_det'`, TorqueLeaves) on the rim
  `04625` when `A(c*) > 0`; everything else is `Residual_SI`;
* multi-isolated: `04325`, `04635` by `LemmaTQ2.lemmaTQ'`; `0435` is the Theorem P cell `c0435`; the
  hexagon `046325` by `LemmaTQHex.lemmaTQHex` under its hypotheses, else `Residual_Hex`.

Main theorem: `dispatch24OB1`.

Bridges proved here:
* `rim_orient`: at a strict cell view, the rim of an `S0xCycUD` cycle is a strictly convex polygon
  on the screen, with all triple tests of one sign (either orientation occurs: the mirror image of
  a type-24 solid is a type-24 solid with the same labels);
* `isRupert_of_neg_image`: Rupertness of `-x`, used to reduce the negative orientation to Leaf B;
* `hang_of_key`: Leaf B's hypothesis `hang` (the angles at `6` and `2` of the rim are not both
  right) follows from its key determinant and the tie `⟪x 2, u⟫ = ⟪x 6, u⟫`: if both were right, the
  edges `4 → 6` and `2 → 5` and `u` would all be orthogonal to `x 2 - x 6 ≠ 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.OB1
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.TheoremP

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

/-! ## Point reflection and the hang condition -/

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

theorem det3_neg_sub (x : Fin 7 → ℝ³) (u : ℝ³) (a b c d : Fin 7) :
    det3 ((fun i => -x i) a - (fun i => -x i) b) ((fun i => -x i) c - (fun i => -x i) d) (-u) =
      -det3 (x a - x b) (x c - x d) u := by
  simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring

/-- **The hang condition of Leaf B is automatic.**  If `u ⟂ x 2 - x 6` and the key determinant is
nonzero, the rim angles at `6` (of `2 6 4`) and at `2` (of `6 2 5`) are not both right. -/
theorem hang_of_key {x : Fin 7 → ℝ³} {u : ℝ³} (h26 : x 2 ≠ x 6) (t6 : ⟪x 2, u⟫ = ⟪x 6, u⟫)
    (key : det3 (x 6 - x 4) (x 5 - x 2) u ≠ 0) :
    ⟪x 2 - x 6, x 6 - x 4⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 2⟫ ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨ha, hb⟩ := hc
  set w := x 2 - x 6
  set a := x 6 - x 4
  set b := x 5 - x 2
  have hb' : ⟪w, b⟫ = 0 := by
    have : x 6 - x 2 = -w := by simp [w]
    rw [this, inner_neg_left] at hb; linarith
  have hu' : ⟪w, u⟫ = 0 := by simp only [w, inner_sub_left]; linarith
  have hw : w ≠ 0 := sub_ne_zero.mpr h26
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at ha hb' hu'
  rw [det3_expand] at key
  apply hw
  ext l
  fin_cases l
  · simp only [Fin.zero_eta, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 0 = 0)).resolve_left key
    linear_combination (b 1 * u 2 - b 2 * u 1) * ha + (u 1 * a 2 - u 2 * a 1) * hb' +
      (a 1 * b 2 - a 2 * b 1) * hu'
  · simp only [Fin.mk_one, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 1 = 0)).resolve_left key
    linear_combination (b 2 * u 0 - b 0 * u 2) * ha + (u 2 * a 0 - u 0 * a 2) * hb' +
      (a 2 * b 0 - a 0 * b 2) * hu'
  · simp only [Fin.reduceFinMk, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 2 = 0)).resolve_left key
    linear_combination (b 0 * u 1 - b 1 * u 0) * ha + (u 0 * a 1 - u 1 * a 0) * hb' +
      (a 0 * b 1 - a 1 * b 0) * hu'

/-! ## The orthocentre view -/

section Ortho
variable {x : Fin 7 → ℝ³}

theorem cellAt_mono {F : S0xFac 9 s0x_S24 x} {U D U' D' : Finset (Fin 9)} {u : ℝ³}
    (h : CellAt F U D u) (hU : U' ⊆ U) (hD : D' ⊆ D) : CellAt F U' D' u :=
  ⟨fun t ht => h.1 t (hU ht), fun t ht => h.2 t (hD ht)⟩

/-- Depths at the orthocentre view `u* = apexView v 1`: the ends `0, 2, 6` tie, and `4`, `5` are
strictly deeper (Theorem P's `σ > 1`). -/
theorem orthocentre_depths (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    u ≠ 0 ∧ ⟪x 2, u⟫ = ⟪x 0, u⟫ ∧ ⟪x 2, u⟫ = ⟪x 6, u⟫ ∧ ⟪x 2, u⟫ < ⟪x 4, u⟫ ∧
      ⟪x 2, u⟫ < ⟪x 5, u⟫ := by
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
  have ⟨_, hV4, hV5, hE0, hE2, hE6⟩ := type24_sigma_gt_one F p v y hxy rfl rfl rfl rfl
  have D := depth_orthocentre x p v y hxy u hu
  have d40 := D 4 2
  have d50 := D 5 2
  have d02 := D 0 2
  have d62 := D 6 2
  simp only [inner_sub_left] at d40 d50 d02 d62
  have hu0 : u ≠ 0 := by
    intro h0; have := hu 0; rw [h0, inner_zero_right] at this; norm_num at this
  refine ⟨hu0, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The Leaf B quantity `A(c*)` of the single-isolated rim `04625` (`LEAFB24.md`): the orientation
`o = det(x6 - x4, x2 - x6, u)` of the rim times `det(x6 - x4, x5 - x2, u)`, negated.  `A > 0` iff
the interior angles of the screen rim at `6` and `2` sum to less than `π`. -/
noncomputable def leafBA (x : Fin 7 → ℝ³) (u : ℝ³) : ℝ :=
  -(det3 (x 6 - x 4) (x 2 - x 6) u * det3 (x 6 - x 4) (x 5 - x 2) u)

/-- **Leaf B at the orthocentre view, rim `04625`.**  `u*` in the open cell with front facets
`{0345, 235, 236, 346}` and `A(c*) > 0`: Rupert (both orientations of the rim). -/
theorem isRupert_leafB_cell04625 (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hcell : InSingleIsoCell F (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1)
      .c04625)
    (hA : 0 < leafBA x (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1)) :
    IsRupert (Finset.univ.image x) := by
  set u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
  obtain ⟨hu0, t0, t6, h4, h5⟩ := orthocentre_depths F hli
  have hx := Minimality.H24.SAT.inj_of_fac F
  have h26 : x 2 ≠ x 6 := fun h => absurd (hx h) (by decide)
  have nr : ∀ i : ZMod 5, c04625 i ≠ 1 ∧ c04625 i ≠ 3 := by decide
  have off : ∀ {w : Fin 7}, w ∈ ({1, 3} : Finset (Fin 7)) → ∀ i : ZMod 5, w ≠ c04625 i := by
    intro w hw i
    have hw' : w = 1 ∨ w = 3 := by simpa using hw
    rcases hw' with rfl | rfl
    exacts [fun h => (nr i).1 h.symm, fun h => (nr i).2 h.symm]
  have c1 : c04625 1 = 4 := by decide
  have c2 : c04625 (1 + 1) = 6 := by decide
  have eo : det3 (x 6 - x 4) (x 2 - x 6) u = det3 (x 6 - x 4) (x 2 - x 4) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  unfold leafBA at hA
  rcases rim_orient F hx inj_c04625 (by decide) (by decide) cyc04625 hcell with P | N
  · have ho : 0 < det3 (x 6 - x 4) (x 2 - x 6) u := by
      have := P 1 2 (by decide) (by decide)
      rw [c1, c2] at this; rw [eo]; exact this
    have key : det3 (x 6 - x 4) (x 5 - x 2) u < 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_nonneg ho.le hc]
    refine LeafB24.isRupert_leafB_04625_of_det' hu0 ?_ ?_ t0 t6 h4 h5 key
      (hang_of_key h26 t6 key.ne)
    · intro i j hi hj
      exact P i (c04625 j) (fun h => hi (inj_c04625 h)) (fun h => hj (inj_c04625 h))
    · intro w hw i
      exact P i w (off hw i) (off hw (i + 1))
  · have ho : det3 (x 6 - x 4) (x 2 - x 6) u < 0 := by
      have := N 1 2 (by decide) (by decide)
      rw [c1, c2] at this; rw [eo]; exact this
    have key : 0 < det3 (x 6 - x 4) (x 5 - x 2) u := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg (neg_nonneg.mpr ho.le) (neg_nonneg.mpr hc)]
    set y : Fin 7 → ℝ³ := fun i => -x i with hy
    apply isRupert_of_neg_image
    rw [Finset.image_image]
    change IsRupert (Finset.univ.image y)
    have ip : ∀ i, ⟪y i, -u⟫ = ⟪x i, u⟫ := fun i => by simp [y]
    have key' : det3 (y 6 - y 4) (y 5 - y 2) (-u) < 0 := by
      rw [det3_neg_sub]; linarith
    have t6' : ⟪y 2, -u⟫ = ⟪y 6, -u⟫ := by rw [ip, ip]; exact t6
    refine LeafB24.isRupert_leafB_04625_of_det' (neg_ne_zero.mpr hu0) ?_ ?_
      (by rw [ip, ip]; exact t0) t6' (by rw [ip, ip]; exact h4) (by rw [ip, ip]; exact h5) key'
      (hang_of_key (fun h => h26 (neg_inj.mp h)) t6' key'.ne)
    · intro i j hi hj
      rw [det3_neg_sub]
      have := N i (c04625 j) (fun h => hi (inj_c04625 h)) (fun h => hj (inj_c04625 h))
      exact neg_pos.mpr this
    · intro w hw i
      rw [det3_neg_sub]
      exact neg_pos.mpr (N i w (off hw i) (off hw (i + 1)))

end Ortho

/-! ## The residual cases and the dispatcher -/

section Dispatch
variable {x : Fin 7 → ℝ³}

/-- Leaf B is available in Lean on the single-isolated rim `r` at the view `u`.  Only the rim
`04625` has a Lean Leaf B (`isRupert_leafB_cell04625`), with the condition `A(c*) > 0`.  The hand
proof (`LEAFB24.md` section 5) gives the same leaf on the other six rims with their own `A`
(`043625`: `det(y6 - y3, y5 - y2, c*)`, `046235`: `det(y6 - y4, y3 - y2, c*)`, `05236`:
`det(y6 - y3, y0 - y5, c*)`, `052346`: `det(y6 - y4, y0 - y5, c*)`,
`02364`: `det(y0 - y4, y2 - y3, c*)`,
`025364`: `det(y0 - y4, y2 - y5, c*)`, each times the rim orientation); they are not formalized,
so those rims are residual as a whole. -/
def LeafBLean (x : Fin 7 → ℝ³) (u : ℝ³) : SingleIsoRim → Prop
  | .c04625 => 0 < leafBA x u
  | _ => False

/-- **Residual, single-isolated end.**  `u` lies in the open cell of a single-isolated-end rim `r`
(`InSingleIsoCell`, seven rims) and Leaf B is not available in Lean there: for `r = 04625` this is
`A(c*) ≤ 0` (`leafBA x u ≤ 0`, the interior screen angles at `6` and `2` sum to at least `π`); for
the other six rims it is the whole cell. -/
def Residual_SI (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ∃ r : SingleIsoRim, InSingleIsoCell F u r ∧ ¬ LeafBLean x u r

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
    · left
      cases r
      case c04625 => exact isRupert_leafB_cell04625 F hli hr hL
      all_goals exact hL.elim
    · exact Or.inr (Or.inl ⟨r, hr, hL⟩)
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
