module

public import Minimality.Type16SAT.TRule
public import Minimality.Type16SAT.TLink

@[expose] public section

/-!
# Type 16 (J5): the split families 40 to 44 (ST16 18.3, 18.8; FORMAT16.md of L16/T0)

The split flag `sf kind view f sd cyc` means "no split certificate" (`rhoW_sf`, TSem: `SplitCert` = `SplitRows` at the menu
view `vv view` for kind 0, `LexRows` at the tie view `(wf t f, sdR sd * dplus t f)`, `t = view`, for kind 1, with
`a cc : ZMod k`, `cc != a, a + 1`, `sigma = +-1`).  The schemas:

* **40, kind 0** (menu split rule, tag `40 0 e 0 pp sfv`, sibling rule `17 e pp mask ..`): the clause covers the RobUni rule's
  context `ctxLits e pp mask sigp` (Rule2) and `sf(0, e, 0, 0, cyc)`.  `split0OK`; `split0OK_sound` by `rule_ctx`
  (the tope at `vv e`) and `Split.split_tope_rupert'`.
* **40, kind 1** (tie split rule, tag `40 1 (32 t + f) sd pp sfv`, sibling `23 t f sd pp mask zs ..`): the clause covers
  `tieCtxLits t f sd pp zs1` (TRule) and `sf(1, t, f, sd, cyc)`.  `split1OK`; `split1OK_sound` by `tie_ctx` (its last
  conjunct is `hfac` of `Split.split_lex2_rupert`) and `split_lex2_rupert`.
  In both, the cycle `cyc` of the flag is checked by `cycChk pp cyc` itself (orientation free, every rotation and reflection
  of the pattern's cycle passes), so a flag created for the reversed cycle (5 of the 28 core rows) needs no reindexing:
  `cycFacts` gives the cycle facts for `cOf cyc` directly.  `NoBetween` by `noBetween_of_fac` and `decide` on `V2.fIdx`.
* **41** (certificate, tag `41 sfv kind key side a cc sig : cyc`): the clause covers `-sf` and the negated row literals
  `certRows` recomputed as in `splitFail` (split9.inc): for `i != a`, `j in {i, i+1}`, `j != cc` the literal
  `p` (sig = +1) or `q` (sig = -1) of `mul3(depth(c_j, c_cc), Delta_i)`.  `certOK`; `certOK_sound` (any shape with `GeoOK`):
  all rows true give `SplitRows` (kind 0, depth `ordS`) or `LexRows` (kind 1, depth `ordD`, lex at `(wf, sdR dplus)`) for
  `(a, cc, sigma)`, i.e. `SplitCert`, against `sf`.  `Delta_i = Dd(c_i, c_i+1; c_a, c_a+1)`: the chirotope entry `entS e1 e2 e`
  (sorted lookup in `triOf`, keys checked by `entK`) for a menu view `e < 21`, the variable `Q(0, e, e1, e2)` for a line view,
  `Q(1, 32 t + f, e1, e2)` for a tie view.
* **42 / 43** (Q zero sums, line / tie): Binet-Cauchy `det(d1, d2, a x b) = <d1,a><d2,b> - <d1,b><d2,a>`, as `z4W` rows.
* **44** (`{-Q.p, -Q.q}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset

namespace Minimality.H16T.SAT
open Minimality Minimality.H21 Minimality.H29.SAT Minimality.H16.SAT

/-! ### Generic facts -/

/-- The coordinate `det3` of `SplitRows` is `det3`. -/
theorem split_det3 (a b c : ℝ³) : Minimality.Split.det3 a b c = det3 a b c := by
  rw [Minimality.Split.det3_eq_inner_cross]; rfl

/-- Every two points of type 16 are separated by a facet (the `NoBetween` side condition). -/
theorem fIdx_sep : ∀ i j : Fin 7, j ≠ i → ∃ T : Fin 8, i ∈ V2.fIdx T ∧ j ∉ V2.fIdx T := by decide

theorem noBetween16 {x : Fin 7 → ℝ³} (F : S0xFac 8 V2.fIdx x) : Minimality.Split.NoBetween x :=
  Minimality.Split.noBetween_of_fac F fIdx_sep

/-- Entries of a checked cycle are points. -/
theorem cycChk_lt7 {pp : Nat} {L : List Nat} (h : cycChk pp L = true) : ∀ v ∈ L, v < 7 := by
  unfold cycChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun v hv => h.1.1.2 v hv

/-- The vertex cycle of a flag is the cycle map of `cOf`. -/
theorem cycX_geoF {x : Fin 7 → ℝ³} (F : S0xFac 8 V2.fIdx x) {cyc : List Nat} [NeZero cyc.length]
    (h7 : ∀ v ∈ cyc, v < 7) : cycX (geoF F) cyc = fun i => x (cOf (k := cyc.length) cyc i) := by
  funext i
  rw [← geoF_x F (cOf cyc i), cOf_val h7 i]
  rfl

/-- The flag literal of a clause (first `sf kind view f sd _` literal). -/
def sfOf (cl : List LitW) (kind view f sd : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (true, .sf k' v' f' sd' c) => if k' == kind && v' == view && f' == f && sd' == sd then some c else none
    | _ => none).getD []

/-- The `Tp` signature in a lifted clause (first `not Tp e mask _` literal), as `tpvOf` of Rule2. -/
def tpvOfW (cl : List LitW) (e mask : Nat) : Nat :=
  (cl.findSome? fun l => match l with
    | (false, .base (.tpv e' m' s')) => if e' == e && m' == mask then some s' else none
    | _ => none).getD 0

/-- `rhoW` of a flag that is false: a certificate exists. -/
theorem splitCert_of_sf {g : Geo} {kind view f sd : Nat} {cyc : List Nat}
    (h : evalW (rhoW g) ((true, W.sf kind view f sd cyc) : LitW) = false) : SplitCert g kind view f sd cyc := by
  have : rhoW g (W.sf kind view f sd cyc) = false := by simpa [evalW] using h
  rw [rhoW_sf] at this
  simpa using this

/-! ### Family 40, kind 0: the menu split rule -/

/-- The literals of the menu split rule `(e, pp, mask)`: the rule's context and the flag. -/
def splitLits0 (e pp mask sigp : Nat) (cyc : List Nat) : List LitW :=
  liftCl (ctxLits e pp mask sigp) ++ [(true, W.sf 0 e 0 0 cyc)]

/-- **The check of a menu split rule row** (tag `40 0 e 0 pp sfv`; `mask` from the sibling rule `17 e pp mask ..`). -/
def split0OK (e pp mask : Nat) (cl : List LitW) : Bool :=
  let sigp := tpvOfW cl e mask
  let cyc := sfOf cl 0 e 0 0
  decide (e < 36 ∧ pp < 256 ∧ mask < 255) && sigOK pp mask sigp && cycChk pp (patCyc.getD pp []) &&
    cycChk pp cyc && coversW cl (splitLits0 e pp mask sigp cyc)

/-- **Soundness of family 40, kind 0**: a menu split rule row that passes the check is true of the real data, if the shape is
not Rupert. -/
theorem split0OK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) {e pp mask : Nat} {cl : List LitW}
    (h : split0OK e pp mask cl = true) : HoldsW (rhoW (geoF F)) cl := by
  by_contra hn
  apply hNR
  unfold split0OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨he, -, hmask⟩, hsig⟩, hcyc⟩, hcyc2⟩, hcov⟩ := h
  have hno := false_of_covers (rhoW_proper _) hcov hn
  have hctx : ∀ l ∈ ctxLits e pp mask (tpvOfW cl e mask), evalL (rho (geoF F)) l = false := by
    intro l hl
    have := hno (liftL l) (List.mem_append_left _ (List.mem_map_of_mem hl))
    rwa [evalW_lift] at this
  obtain ⟨_, -, -, -, -, ht⟩ := rule_ctx F hG e pp mask _ he hmask hsig hcyc hctx
  have hC := splitCert_of_sf (hno _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hlen := cycChk_len hcyc2
  have : NeZero (sfOf cl 0 e 0 0).length := ⟨by omega⟩
  obtain ⟨a, cc, σ, hca, hca1, -, hrows⟩ := hC
  rw [if_pos rfl] at hrows
  obtain ⟨h3, hinj, hcycOK⟩ := cycFacts (k := (sfOf cl 0 e 0 0).length) rfl hcyc2
  rw [cycX_geoF F (cycChk_lt7 hcyc2), geoF_vv] at hrows
  exact Minimality.Split.split_tope_rupert' F hx (noBetween16 F) hinj h3 hcycOK ht a cc σ hca hca1 hrows

/-! ### Family 40, kind 1: the tie split rule -/

/-- The literals of the tie split rule `(t, f, sd, pp, zs1)`: the tie rule's context and the flag. -/
def splitLits1 (t f sd pp zs1 : Nat) (cyc : List Nat) : List LitW :=
  tieCtxLits t f sd pp zs1 ++ [(true, W.sf 1 t f sd cyc)]

/-- **The check of a tie split rule row** (tag `40 1 (32 t + f) sd pp sfv`; `zs1 = zs + 1` from the sibling tie rule
`23 t f sd pp mask zs ..`). -/
def split1OK (t f sd pp zs1 : Nat) (cl : List LitW) : Bool :=
  let cyc := sfOf cl 1 t f sd
  decide (tieParOK t f sd pp zs1) && cycChk pp (patCyc.getD pp []) && cycChk pp cyc &&
    coversW cl (splitLits1 t f sd pp zs1 cyc)

/-- **Soundness of family 40, kind 1**: a tie split rule row that passes the check is true of the real data, if the shape is
not Rupert. -/
theorem split1OK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) {t f sd pp zs1 : Nat} {cl : List LitW}
    (h : split1OK t f sd pp zs1 cl = true) : HoldsW (rhoW (geoF F)) cl := by
  by_contra hn
  apply hNR
  unfold split1OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hcyc⟩, hcyc2⟩, hcov⟩ := h
  have hno := false_of_covers (rhoW_proper _) hcov hn
  obtain ⟨_, -, -, -, -, hfac⟩ := tie_ctx F hG hp hcyc (fun l hl => hno l (List.mem_append_left _ hl))
  have hC := splitCert_of_sf (hno _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hlen := cycChk_len hcyc2
  have : NeZero (sfOf cl 1 t f sd).length := ⟨by omega⟩
  obtain ⟨a, cc, σ, hca, hca1, -, hrows⟩ := hC
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by norm_num))] at hrows
  obtain ⟨h3, hinj, hcycOK⟩ := cycFacts (k := (sfOf cl 1 t f sd).length) rfl hcyc2
  rw [cycX_geoF F (cycChk_lt7 hcyc2)] at hrows
  exact Minimality.Split.split_lex2_rupert F hx (noBetween16 F) hinj h3 hcycOK hfac a cc σ hca hca1 hrows

/-! ### Family 41: the split certificate -/

/-- The edge of the ordered pair `(x, y)` (encoder's `edS`): the index of `{x, y}`. -/
def edE (x y : Nat) : Nat := if y < x then EI y x else EI x y
/-- The sign of `x_y - x_x` against `d_(edE x y)`: `true` (`+1`) iff `y < x`. -/
def edP (x y : Nat) : Bool := decide (y < x)

/-- `x_y - x_x = (+-1) d_(edE x y)`. -/
theorem dv_edE (g : Geo) {x y : Nat} (hx : x < 7) (hy : y < 7) (hxy : x ≠ y) :
    g.x y - g.x x = (if edP x y then (1 : ℝ) else -1) • g.dv (edE x y) := by
  unfold edP edE
  by_cases h : y < x
  · simp only [h, decide_true, if_true, one_smul]
    rw [dv_EI g hy hx h]
  · have h' : x < y := by omega
    simp only [h, decide_false, if_false, Bool.false_eq_true]
    rw [dv_EI g hx hy h', neg_smul, one_smul, neg_sub]

theorem edE_lt {x y : Nat} (hx : x < 7) (hy : y < 7) (hxy : x ≠ y) : edE x y < 21 := by
  unfold edE
  split_ifs with h
  · exact EI_lt21 y hy x hx h
  · exact EI_lt21 x hx y hy (by omega)

/-- The chirotope entry of the triple `(a, b, c)` of differences (the encoder's `ent`): the sorted entry of `triOf`
with the sign of the permutation, `0` for a repeated difference. -/
def entS (a b c : Nat) : S3 :=
  if a < b ∧ b < c then triOf a b c
  else if a < c ∧ c < b then negS (triOf a c b)
  else if b < a ∧ a < c then negS (triOf b a c)
  else if b < c ∧ c < a then triOf b c a
  else if c < a ∧ a < b then triOf c a b
  else if c < b ∧ b < a then negS (triOf c b a)
  else zeroS

/-- The sorted triple of `entS` is a key of the triple table (or there is a repeat). -/
def entK (a b c : Nat) : Bool :=
  if a < b ∧ b < c then hasKey3 triRoutes a b c
  else if a < c ∧ c < b then hasKey3 triRoutes a c b
  else if b < a ∧ a < c then hasKey3 triRoutes b a c
  else if b < c ∧ c < a then hasKey3 triRoutes b c a
  else if c < a ∧ a < b then hasKey3 triRoutes c a b
  else if c < b ∧ b < a then hasKey3 triRoutes c b a
  else true

/-- **`entS` tells the truth** on a key. -/
theorem entS_sound {g : Geo} (hG : GeoOK g) {a b c : Nat} (hk : entK a b c = true) :
    Sg3 (rho g) (entS a b c) (det3 (g.dv a) (g.dv b) (g.dv c)) := by
  have E := entOK_tab3 hG.hF hG.hO
  have T : ∀ x y z, hasKey3 triRoutes x y z = true →
      Sg3 (rho g) (triOf x y z) (det3 (g.dv x) (g.dv y) (g.dv z)) := fun x y z h => E.ent x y z h
  unfold entS entK at *
  split_ifs at hk ⊢ with h1 h2 h3 h4 h5 h6
  · exact T _ _ _ hk
  · rw [show det3 (g.dv a) (g.dv b) (g.dv c) = -det3 (g.dv a) (g.dv c) (g.dv b) by
      simp only [det3_expand]; ring]
    exact (T _ _ _ hk).neg
  · rw [show det3 (g.dv a) (g.dv b) (g.dv c) = -det3 (g.dv b) (g.dv a) (g.dv c) by
      simp only [det3_expand]; ring]
    exact (T _ _ _ hk).neg
  · rw [show det3 (g.dv a) (g.dv b) (g.dv c) = det3 (g.dv b) (g.dv c) (g.dv a) by
      simp only [det3_expand]; ring]
    exact T _ _ _ hk
  · rw [show det3 (g.dv a) (g.dv b) (g.dv c) = det3 (g.dv c) (g.dv a) (g.dv b) by
      simp only [det3_expand]; ring]
    exact T _ _ _ hk
  · rw [show det3 (g.dv a) (g.dv b) (g.dv c) = -det3 (g.dv c) (g.dv b) (g.dv a) by
      simp only [det3_expand]; ring]
    exact (T _ _ _ hk).neg
  · have : a = b ∨ b = c ∨ a = c := by omega
    rw [show det3 (g.dv a) (g.dv b) (g.dv c) = 0 by
      rcases this with h | h | h <;> rw [h] <;> simp only [det3_expand] <;> ring]
    exact Sg3_zero (rho_proper g)

/-- The vector of the leaf view: `vv view` (kind 0, menu or line view), `wf view f` (kind 1, tie view). -/
noncomputable def leafU (g : Geo) (kind view f : Nat) : ℝ³ := if kind = 0 then g.vv view else wf g view f

/-- `Delta` of two differences `e1 < e2` at the leaf view (`dlt` of split9.inc): the chirotope entry at a menu view
`e < 21`, else the `Q` variable (`Q(0, e, e1, e2)` of a line view, `Q(1, 32 t + f, e1, e2)` of a tie view). -/
def dltW (kind view f e1 e2 : Nat) : S3W :=
  if kind = 0 ∧ view < 21 then liftS (entS e1 e2 view)
  else if kind = 0 then QS 0 view e1 e2 else QS 1 (32 * view + f) e1 e2

/-- The table key that `dltW` needs. -/
def dltK (kind view e1 e2 : Nat) : Bool := !(decide (kind = 0 ∧ view < 21)) || entK e1 e2 view

theorem dltW_sound {g : Geo} (hG : GeoOK g) {kind view f e1 e2 : Nat} (hkind : kind = 0 ∨ (kind = 1 ∧ f < 21))
    (hk : dltK kind view e1 e2 = true) :
    SgW (rhoW g) (dltW kind view f e1 e2) (det3 (g.dv e1) (g.dv e2) (leafU g kind view f)) := by
  unfold dltW leafU
  by_cases h0 : kind = 0 ∧ view < 21
  · rw [if_pos h0, if_pos h0.1, vv_lt g h0.2]
    have hk' : entK e1 e2 view = true := by simpa [dltK, h0] using hk
    exact sgW_rho_lift (entS_sound hG hk')
  · rw [if_neg h0]
    by_cases h1 : kind = 0
    · rw [if_pos h1, if_pos h1]
      have := SgW_Q g 0 view e1 e2
      simpa [Qv, qvVec] using this
    · rw [if_neg h1, if_neg h1]
      have hf : f < 21 := by omega
      have := SgW_Q g 1 (32 * view + f) e1 e2
      have e1' : (32 * view + f) / 32 = view := by omega
      have e2' : (32 * view + f) % 32 = f := by omega
      simpa [Qv, qvVec, e1', e2'] using this

/-- `Delta_i = Dd(x, y; p, q)` (split9.inc): the sign of `det(x_y - x_x, x_q - x_p, u)` at the leaf view `u`, from
`dlt` of the two edges, flipped by the orientations of the pairs, zero for the same edge. -/
def dDW (kind view f x y p q : Nat) : S3W :=
  if edE x y = edE p q then zeroSW
  else
    let r := if edE x y < edE p q then dltW kind view f (edE x y) (edE p q)
      else negSW (dltW kind view f (edE p q) (edE x y))
    if edP x y = edP p q then r else negSW r

/-- The table key that `dDW` needs. -/
def dKey (kind view x y p q : Nat) : Bool :=
  edE x y == edE p q ||
    (if edE x y < edE p q then dltK kind view (edE x y) (edE p q) else dltK kind view (edE p q) (edE x y))

theorem det3_smul12 (s t : ℝ) (a b c : ℝ³) : det3 (s • a) (t • b) c = s * t * det3 a b c := by
  simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring

theorem dDW_sound {g : Geo} (hG : GeoOK g) {kind view f x y p q : Nat} (hkind : kind = 0 ∨ (kind = 1 ∧ f < 21))
    (hx : x < 7) (hy : y < 7) (hp : p < 7) (hq : q < 7) (hxy : x ≠ y) (hpq : p ≠ q)
    (hk : dKey kind view x y p q = true) :
    SgW (rhoW g) (dDW kind view f x y p q) (det3 (g.x y - g.x x) (g.x q - g.x p) (leafU g kind view f)) := by
  rw [dv_edE g hx hy hxy, dv_edE g hp hq hpq, det3_smul12]
  unfold dDW
  by_cases he : edE x y = edE p q
  · rw [if_pos he, he, show det3 (g.dv (edE p q)) (g.dv (edE p q)) (leafU g kind view f) = 0 by
      simp only [det3_expand]; ring, mul_zero]
    exact SgW_zero (rhoW_proper g)
  · rw [if_neg he]
    have hk' : (if edE x y < edE p q then dltK kind view (edE x y) (edE p q)
        else dltK kind view (edE p q) (edE x y)) = true := by simpa [dKey, he] using hk
    have hr : SgW (rhoW g) (if edE x y < edE p q then dltW kind view f (edE x y) (edE p q)
        else negSW (dltW kind view f (edE p q) (edE x y)))
        (det3 (g.dv (edE x y)) (g.dv (edE p q)) (leafU g kind view f)) := by
      by_cases hl : edE x y < edE p q
      · rw [if_pos hl] at hk' ⊢
        exact dltW_sound hG hkind hk'
      · rw [if_neg hl] at hk' ⊢
        rw [show det3 (g.dv (edE x y)) (g.dv (edE p q)) (leafU g kind view f) =
          -det3 (g.dv (edE p q)) (g.dv (edE x y)) (leafU g kind view f) by simp only [det3_expand]; ring]
        exact (dltW_sound hG hkind hk').neg
    simp only
    cases h1 : edP x y <;> cases h2 : edP p q
    · simpa using hr
    · simpa using hr.neg
    · simpa using hr.neg
    · simpa using hr

/-- The depth of `a` minus `b` at the leaf: `ordS` at the menu view (kind 0), `ordD` at the tie view (kind 1). -/
def depW (kind view f sd a b : Nat) : S3W := if kind = 0 then liftS (ordS view a b) else ordDW view f sd a b

/-- A row literal of a certificate: `p` (sg = 1) or `q` of `mul3(depth(j, c), Delta(i, i1; a, a1))`. -/
def rowL (kind view f sd sg : Nat) (j c i i1 a a1 : Nat) : LitW :=
  if sg = 1 then (mul3W (depW kind view f sd j c) (dDW kind view f i i1 a a1)).1
  else (mul3W (depW kind view f sd j c) (dDW kind view f i i1 a a1)).2

/-- The rows of the certificate `(a, cc, sg)` of the cycle `cyc` (split9.inc `splitFail`): `i != a`, `j in {i, i+1}`,
`j != cc`, in the encoder's order. -/
def certRows (kind view f sd a cc sg : Nat) (cyc : List Nat) : List LitW :=
  (List.range cyc.length).flatMap fun i =>
    if i = a then [] else
      ([i, (i + 1) % cyc.length].filter fun j => j != cc).map fun j =>
        rowL kind view f sd sg (cv cyc j) (cv cyc cc) (cv cyc i) (cv cyc ((i + 1) % cyc.length)) (cv cyc a)
          (cv cyc ((a + 1) % cyc.length))

/-- The table keys of the rows. -/
def certKeys (kind view a : Nat) (cyc : List Nat) : Bool :=
  (List.range cyc.length).all fun i => i == a ||
    dKey kind view (cv cyc i) (cv cyc ((i + 1) % cyc.length)) (cv cyc a) (cv cyc ((a + 1) % cyc.length))

/-- **The check of a split certificate row** (tag `41 sfv kind key side a cc sig : cyc`; `view = key` (kind 0) or
`key / 32` (kind 1), `f = 0` / `key % 32`, `sd = side`, `sg = 1` for `sig = +1`, else `0`): the clause covers `-sf` and the
negations of the recomputed rows. -/
def certOK (kind view f sd a cc sg : Nat) (cyc : List Nat) (cl : List LitW) : Bool :=
  decide (3 ≤ cyc.length ∧ a < cyc.length ∧ cc < cyc.length ∧ cc ≠ a ∧ cc ≠ (a + 1) % cyc.length ∧
      (kind = 0 ∨ (kind = 1 ∧ f < 21))) &&
    cyc.all (fun v => decide (v < 7)) && decide cyc.Nodup && certKeys kind view a cyc &&
    coversW cl ((false, W.sf kind view f sd cyc) :: (certRows kind view f sd a cc sg cyc).map LitW.neg)

theorem cv_lt7 {L : List Nat} (h : L.all (fun v => decide (v < 7)) = true) {i : Nat} (hi : i < L.length) :
    cv L i < 7 := by
  have := List.all_eq_true.mp h (L[i]) (List.getElem_mem hi)
  simp only [decide_eq_true_eq] at this
  rw [cv, List.getD_eq_getElem _ _ hi]
  exact this

theorem cv_ne {L : List Nat} (h : L.Nodup) {i j : Nat} (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    cv L i ≠ cv L j := by
  rw [cv, cv, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact fun e => hij ((h.getElem_inj_iff).mp e)

theorem mem_certRows {kind view f sd a cc sg : Nat} {cyc : List Nat} {i j : Nat} (hi : i < cyc.length) (hia : i ≠ a)
    (hj : j = i ∨ j = (i + 1) % cyc.length) (hjc : j ≠ cc) :
    rowL kind view f sd sg (cv cyc j) (cv cyc cc) (cv cyc i) (cv cyc ((i + 1) % cyc.length)) (cv cyc a)
      (cv cyc ((a + 1) % cyc.length)) ∈ certRows kind view f sd a cc sg cyc := by
  simp only [certRows, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  rw [if_neg hia]
  refine List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨?_, by simpa using hjc⟩, rfl⟩
  rcases hj with rfl | rfl <;> simp

/-- The product of a lex sign and a strict sign, as a lex statement. -/
theorem mul3W_lex {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) {a b : S3W} {A B r : ℝ}
    (ha : LexSg ρ a A B) (hb : SgW ρ b r) :
    (evalW ρ (mul3W a b).1 = true → (h21b_LP A B ∧ 0 < r) ∨ (h21b_LP (-A) (-B) ∧ r < 0)) ∧
    (evalW ρ (mul3W a b).2 = true → (h21b_LP A B ∧ r < 0) ∨ (h21b_LP (-A) (-B) ∧ 0 < r)) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  simp only [mul3W, evalW_orW hP hG, evalW_andW hP hG, Bool.or_eq_true, Bool.and_eq_true, a1, a2, b1, b2]
  constructor <;> intro h <;> tauto

theorem lp_scale {a b c : ℝ} (hc : 0 < c) (h : h21b_LP a (c * b)) : h21b_LP a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, pos_of_mul_pos_right h2 hc.le⟩

/-- **Soundness of family 41**: a certificate row that passes the check is true of the real data (any shape with
`GeoOK`): all its rows true give `SplitRows` / `LexRows` for `(a, cc, sigma)`, so the flag is false. -/
theorem certOK_sound {g : Geo} (hG : GeoOK g) {kind view f sd a cc sg : Nat} {cyc : List Nat} {cl : List LitW}
    (h : certOK kind view f sd a cc sg cyc cl = true) : HoldsW (rhoW g) cl := by
  by_contra hn
  unfold certOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hk3, ha, hcc, hca, hca1, hkind⟩, h7⟩, hnd⟩, hkeys⟩, hcov⟩ := h
  have hno := false_of_covers (rhoW_proper g) hcov hn
  have hrow : ∀ l ∈ certRows kind view f sd a cc sg cyc, evalW (rhoW g) l = true := fun l hl => by
    have := hno l.neg (List.mem_cons_of_mem _ (List.mem_map_of_mem hl))
    rw [evalW_neg] at this
    simpa using this
  have hsf : rhoW g (W.sf kind view f sd cyc) = true := by
    have := hno _ List.mem_cons_self
    simpa [evalW] using this
  rw [rhoW_sf] at hsf
  have hnc : ¬ SplitCert g kind view f sd cyc := by simpa using hsf
  apply hnc
  have : NeZero cyc.length := ⟨by omega⟩
  -- indices
  have vA : ((a : ZMod cyc.length)).val = a := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have vC : ((cc : ZMod cyc.length)).val = cc := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hcc]
  have v1 : ∀ i : ZMod cyc.length, (i + 1).val = (i.val + 1) % cyc.length := fun i => by
    have := val_add_nat i 1
    rwa [Nat.cast_one] at this
  have xv : ∀ i : ZMod cyc.length, cycX g cyc i = g.x (cv cyc i.val) := fun i => rfl
  have hkey : ∀ i < cyc.length, i ≠ a →
      dKey kind view (cv cyc i) (cv cyc ((i + 1) % cyc.length)) (cv cyc a) (cv cyc ((a + 1) % cyc.length)) = true := by
    intro i hi hia
    have := List.all_eq_true.mp hkeys i (List.mem_range.mpr hi)
    simpa [hia] using this
  have hmod : ∀ i, (i + 1) % cyc.length < cyc.length := fun i => Nat.mod_lt _ (by omega)
  have hne1 : ∀ i < cyc.length, i ≠ (i + 1) % cyc.length := by
    intro i hi
    by_cases hl : i + 1 < cyc.length
    · rw [Nat.mod_eq_of_lt hl]; omega
    · have : i + 1 = cyc.length := by omega
      rw [this, Nat.mod_self]; omega
  -- the common row facts
  have rowfacts : ∀ i j : ZMod cyc.length, i ≠ (a : ZMod cyc.length) → (j = i ∨ j = i + 1) →
      j ≠ (cc : ZMod cyc.length) →
      evalW (rhoW g) (rowL kind view f sd sg (cv cyc j.val) (cv cyc cc) (cv cyc i.val)
        (cv cyc ((i.val + 1) % cyc.length)) (cv cyc a) (cv cyc ((a + 1) % cyc.length))) = true ∧
      cv cyc j.val < 7 ∧ cv cyc cc < 7 ∧ cv cyc i.val < 7 ∧ cv cyc ((i.val + 1) % cyc.length) < 7 ∧
      cv cyc a < 7 ∧ cv cyc ((a + 1) % cyc.length) < 7 ∧ cv cyc j.val ≠ cv cyc cc ∧
      cv cyc i.val ≠ cv cyc ((i.val + 1) % cyc.length) ∧ cv cyc a ≠ cv cyc ((a + 1) % cyc.length) ∧
      dKey kind view (cv cyc i.val) (cv cyc ((i.val + 1) % cyc.length)) (cv cyc a)
        (cv cyc ((a + 1) % cyc.length)) = true := by
    intro i j hi hj hjc
    have hiv : i.val ≠ a := fun e => hi (by rw [← e, ZMod.natCast_zmod_val])
    have hjv : j.val ≠ cc := fun e => hjc (by rw [← e, ZMod.natCast_zmod_val])
    have hjj : j.val = i.val ∨ j.val = (i.val + 1) % cyc.length := by
      rcases hj with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (v1 i)
    have hil := ZMod.val_lt i
    have hjl := ZMod.val_lt j
    exact ⟨hrow _ (mem_certRows hil hiv hjj hjv), cv_lt7 h7 hjl, cv_lt7 h7 hcc, cv_lt7 h7 hil,
      cv_lt7 h7 (hmod _), cv_lt7 h7 ha, cv_lt7 h7 (hmod _), cv_ne hnd hjl hcc hjv,
      cv_ne hnd hil (hmod _) (hne1 _ hil), cv_ne hnd ha (hmod _) (hne1 _ ha), hkey _ hil hiv⟩
  refine ⟨(a : ZMod cyc.length), (cc : ZMod cyc.length), (if sg = 1 then 1 else -1), ?_, ?_, ?_, ?_⟩
  · intro e
    have := congrArg ZMod.val e
    rw [vA, vC] at this
    exact hca this
  · intro e
    have := congrArg ZMod.val e
    rw [vC, v1, vA] at this
    exact hca1 this
  · split_ifs <;> simp
  · rcases hkind with hk0 | ⟨hk1, hf⟩
    · -- kind 0: SplitRows at the menu view
      subst hk0
      rw [if_pos rfl]
      intro i j hi hj hjc
      obtain ⟨hl, hJ, hC, hI, hI1, hA, hA1, hJC, hII, hAA, hdk⟩ := rowfacts i j hi hj hjc
      have hD := dDW_sound (f := f) hG (Or.inl rfl) hI hI1 hA hA1 hII hAA hdk
      have hS : SgW (rhoW g) (depW 0 view f sd (cv cyc j.val) (cv cyc cc)) (g.z view (cv cyc j.val) (cv cyc cc)) := by
        have := Sg3_ordS g view _ _ (fun h => hG.hv view h) hJC hJ hC (fun a b hab hb => vv_EI g hab hb)
        simpa [depW] using sgW_rho_lift this
      have hM := mulW hS hD
      simp only [xv, v1, vA, vC, split_det3]
      have ez : g.z view (cv cyc j.val) (cv cyc cc) = ⟪g.x (cv cyc j.val) - g.x (cv cyc cc), g.vv view⟫ := by
        rw [Geo.z, real_inner_comm]
      have eU : leafU g 0 view f = g.vv view := by simp [leafU]
      rw [ez, eU] at hM
      unfold rowL at hl
      split_ifs at hl ⊢ with hs
      · rw [one_mul]; exact hM.1.mp hl
      · have := hM.2.mp hl; linarith
    · -- kind 1: LexRows at the tie view
      subst hk1
      rw [if_neg (by norm_num)]
      intro i j hi hj hjc
      obtain ⟨hl, hJ, hC, hI, hI1, hA, hA1, hJC, hII, hAA, hdk⟩ := rowfacts i j hi hj hjc
      have hD := dDW_sound (f := f) hG (Or.inr ⟨rfl, hf⟩) hI hI1 hA hA1 hII hAA hdk
      have hv := dv_ne hG hf
      have hL := ordDW_lex (t := view) hv sd hJ hC hJC
      have hM := mul3W_lex (rhoW_proper g) (rhoW_gateOK g) (a := depW 1 view f sd (cv cyc j.val) (cv cyc cc))
        (by simpa [depW] using hL) hD
      simp only [xv, v1, vA, vC, split_det3]
      have eU : leafU g 1 view f = wf g view f := by simp [leafU]
      rw [eU] at hM
      set r := det3 (g.x (cv cyc ((i.val + 1) % cyc.length)) - g.x (cv cyc i.val))
        (g.x (cv cyc ((a + 1) % cyc.length)) - g.x (cv cyc a)) (wf g view f) with hr
      set X := g.x (cv cyc j.val) - g.x (cv cyc cc) with hX
      by_cases hZ : Z0 g view f
      · -- under Z0 the rise vanishes: no row is true
        have r0 : r = 0 := by
          rw [hr, show wf g view f = 0 from hZ]; simp only [det3_expand]; simp
        exfalso
        unfold rowL at hl
        split_ifs at hl
        · rcases hM.1 hl with ⟨-, h⟩ | ⟨-, h⟩ <;> linarith
        · rcases hM.2 hl with ⟨-, h⟩ | ⟨-, h⟩ <;> linarith
      · have hGv : Gv g view f = dplus g view f := by simp [Gv, hZ]
        rw [hGv] at hM
        have hc := inv_pos.mpr (Rff_pos (t := view) hv)
        have eA : ⟪wf g view f, X⟫ = ⟪X, wf g view f⟫ := real_inner_comm _ _
        have eB : ⟪X, sdR sd • dplus g view f⟫ = sdR sd * ⟪dplus g view f, X⟫ := by
          rw [real_inner_smul_right, real_inner_comm]
        rw [eB]
        rw [eA] at hM
        have key : ∀ s : ℝ, (s = 1 ∨ s = -1) →
            h21b_LP (s * ⟪X, wf g view f⟫) (s * ((Rtie g view f f)⁻¹ * (sdR sd * ⟪dplus g view f, X⟫))) →
            h21b_LP (s * ⟪X, wf g view f⟫) (s * (sdR sd * ⟪dplus g view f, X⟫)) := by
          intro s _ h
          refine lp_scale hc ?_
          rw [show (Rtie g view f f)⁻¹ * (s * (sdR sd * ⟪dplus g view f, X⟫)) =
            s * ((Rtie g view f f)⁻¹ * (sdR sd * ⟪dplus g view f, X⟫)) by ring]
          exact h
        unfold rowL at hl
        split_ifs at hl ⊢ with hs
        · rcases hM.1 hl with ⟨hp, hr0⟩ | ⟨hp, hr0⟩
          · exact ⟨1, key 1 (Or.inl rfl) (by simpa using hp), by linarith⟩
          · exact ⟨-1, key (-1) (Or.inr rfl) (by simpa [neg_mul, one_mul] using hp), by linarith⟩
        · rcases hM.2 hl with ⟨hp, hr0⟩ | ⟨hp, hr0⟩
          · exact ⟨1, key 1 (Or.inl rfl) (by simpa using hp), by linarith⟩
          · exact ⟨-1, key (-1) (Or.inr rfl) (by simpa [neg_mul, one_mul] using hp), by linarith⟩

/-! ### Families 42 to 44: the `Q` zero sums (Binet-Cauchy) and the `Q` exclusion -/

/-- `Fd(t, e)` of split9.inc: the sign of `<N_t, d_e>`. -/
def FdW (t e : Nat) : S3W := liftS (fup3 t (EA e) (EB e))

theorem EAB_lt : ∀ e < 21, EA e < 7 ∧ EB e < 7 := by decide

theorem FdW_sound {g : Geo} (hG : GeoOK g) {t e : Nat} (he : e < 21) : SgW (rhoW g) (FdW t e) ⟪g.N t, g.dv e⟫ :=
  sgW_rho_lift (fup3_sound hG.hF t (EA e) (EB e) (EAB_lt e he).1 (EAB_lt e he).2)

/-- **Binet-Cauchy** in the form of the `Q` zero sums. -/
theorem binet_Q (d1 d2 a b : ℝ³) : det3 d1 d2 (cross a b) = ⟪a, d1⟫ * ⟪d2, b⟫ - ⟪d1, b⟫ * ⟪a, d2⟫ := by
  simp only [det3_expand, inn3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- The rows of the line `Q` zero sum (family 42, tag `42 key e1 e2`, `key` = line view `e`, `(A, B) = lines[e - 21]`):
`zsum{-Q, F_A(e1) F_B(e2), -F_B(e1) F_A(e2)}`. -/
def rows42 (key e1 e2 : Nat) : List (List LitW) :=
  let A := (lines.getD (key - 21) (0, 0)).1
  let B := (lines.getD (key - 21) (0, 0)).2
  z4W (negSW (QS 0 key e1 e2)) (mul3W (FdW A e1) (FdW B e2)) (negSW (mul3W (FdW B e1) (FdW A e2))) zeroSW

def chk42 (key e1 e2 : Nat) (cl : List LitW) : Bool :=
  decide (21 ≤ key ∧ e1 < 21 ∧ e2 < 21) && anyCovW cl (rows42 key e1 e2)

/-- **Soundness of family 42.** -/
theorem chk42_sound {g : Geo} (hG : GeoOK g) {key e1 e2 : Nat} {cl : List LitW} (h : chk42 key e1 e2 cl = true) :
    HoldsW (rhoW g) cl := by
  unfold chk42 at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, h1, h2⟩, hcov⟩ := h
  refine anyCovW_holds (rhoW_proper g) hcov ?_
  have hP := rhoW_proper g
  have hGt := rhoW_gateOK g
  have hv : g.vv key = cross (g.N (lines.getD (key - 21) (0, 0)).1) (g.N (lines.getD (key - 21) (0, 0)).2) := by
    simp [Geo.vv, show ¬ key < 21 by omega]
  have hQ := (SgW_Q g 0 key e1 e2).neg
  refine z4W_sound hQ
    ((FdW_sound (t := (lines.getD (key - 21) (0, 0)).1) hG h1).mul3 hP hGt
      (FdW_sound (t := (lines.getD (key - 21) (0, 0)).2) hG h2))
    ((FdW_sound (t := (lines.getD (key - 21) (0, 0)).2) hG h1).mul3 hP hGt
      (FdW_sound (t := (lines.getD (key - 21) (0, 0)).1) hG h2)).neg
    (SgW_zero hP) ?_
  rw [Qv, qvVec, if_pos rfl, hv, binet_Q, real_inner_comm (g.dv e1) (g.N (lines.getD (key - 21) (0, 0)).1),
    real_inner_comm (g.dv e1) (g.N (lines.getD (key - 21) (0, 0)).2),
    real_inner_comm (g.dv e2) (g.N (lines.getD (key - 21) (0, 0)).2)]
  ring

/-- The rows of the tie `Q` zero sum (family 43, tag `43 key e1 e2`, `key = 32 t + f`):
`zsum{-Q, F_t(e1) T(e2,f), -T(e1,f) F_t(e2)}`. -/
def rows43 (key e1 e2 : Nat) : List (List LitW) :=
  z4W (negSW (QS 1 key e1 e2)) (mul3W (FdW (key / 32) e1) (TW e2 (key % 32)))
    (negSW (mul3W (TW e1 (key % 32)) (FdW (key / 32) e2))) zeroSW

def chk43 (key e1 e2 : Nat) (cl : List LitW) : Bool :=
  decide (e1 < 21 ∧ e2 < 21 ∧ key % 32 < 21) && anyCovW cl (rows43 key e1 e2)

/-- **Soundness of family 43.** -/
theorem chk43_sound {g : Geo} (hG : GeoOK g) {key e1 e2 : Nat} {cl : List LitW} (h : chk43 key e1 e2 cl = true) :
    HoldsW (rhoW g) cl := by
  unfold chk43 at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, hf⟩, hcov⟩ := h
  refine anyCovW_holds (rhoW_proper g) hcov ?_
  have hP := rhoW_proper g
  have hGt := rhoW_gateOK g
  refine z4W_sound (SgW_Q g 1 key e1 e2).neg ((FdW_sound (t := key / 32) hG h1).mul3 hP hGt (TW_sound hG h2 hf))
    ((TW_sound hG h1 hf).mul3 hP hGt (FdW_sound (t := key / 32) hG h2)).neg (SgW_zero hP) ?_
  rw [Qv, qvVec, if_neg (by norm_num), if_pos rfl, wf, binet_Q, real_inner_comm (g.dv e2) (g.N (key / 32))]
  ring

/-- Family 44 (tag `44 kind key e1 e2`): `{-Q.p, -Q.q}`. -/
def chk44 (kind key e1 e2 : Nat) (cl : List LitW) : Bool :=
  coversW cl [(QS kind key e1 e2).1.neg, (QS kind key e1 e2).2.neg]

/-- **Soundness of family 44.** -/
theorem chk44_sound (g : Geo) {kind key e1 e2 : Nat} {cl : List LitW} (h : chk44 kind key e1 e2 cl = true) :
    HoldsW (rhoW g) cl := by
  refine HoldsW.of_covers (rhoW_proper g) h ?_
  obtain ⟨q1, q2⟩ := SgW_Q g kind key e1 e2
  by_cases hp : evalW (rhoW g) (QS kind key e1 e2).1 = true
  · refine ⟨(QS kind key e1 e2).2.neg, by simp, ?_⟩
    rw [evalW_neg]
    have : evalW (rhoW g) (QS kind key e1 e2).2 = false := by
      rw [← Bool.not_eq_true]; intro h2; linarith [q1.mp hp, q2.mp h2]
    simp [this]
  · exact ⟨(QS kind key e1 e2).1.neg, by simp, by rw [evalW_neg]; simpa using hp⟩

end Minimality.H16T.SAT
