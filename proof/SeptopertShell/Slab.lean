module

public import SeptopertShell.View
public import SeptopertShell.Poly
public import SeptopertShell.IPoly
public import Cayley

/-!
# Slab certificates

A computable checker for one slab of the shell (nopert229 `islandmap/bnd/shellcert4.cc`): all data are rational
polynomials in `(x₀, x₁, x₂)` (a box `|x₀| ≤ H₀, |x₁| ≤ H₁, D₀ ≤ x₂ ≤ D₁`), and the soundness theorem
`SlabData.isRupert_of_check` says that if `check` returns `true` then the Septopert-family shape
`(s, y, z)(x)` is Rupert for every `x` in the box.
-/

@[expose] public section

namespace SeptopertShell

namespace Poly

/-- Normalized sum, difference and product. -/
def nadd (p q : Poly) : Poly := normalize (add p q)
def nsub (p q : Poly) : Poly := normalize (sub p q)
def nmul (p q : Poly) : Poly := normalize (mul p q)

theorem eval_nadd (p q : Poly) (x : Fin 3 → ℝ) : (nadd p q).eval x = p.eval x + q.eval x := by
  rw [nadd, eval_normalize, eval_add]
theorem eval_nsub (p q : Poly) (x : Fin 3 → ℝ) : (nsub p q).eval x = p.eval x - q.eval x := by
  rw [nsub, eval_normalize, eval_sub]
theorem eval_nmul (p q : Poly) (x : Fin 3 → ℝ) : (nmul p q).eval x = p.eval x * q.eval x := by
  rw [nmul, eval_normalize, eval_mul]

end Poly

/-- A vector of three polynomials. -/
abbrev PV := Fin 3 → Poly

namespace PV

def add (u w : PV) : PV := fun i => Poly.nadd (u i) (w i)
def sub (u w : PV) : PV := fun i => Poly.nsub (u i) (w i)
def smul (p : Poly) (u : PV) : PV := fun i => Poly.nmul p (u i)
def cross (u w : PV) : PV :=
  ![Poly.nsub (Poly.nmul (u 1) (w 2)) (Poly.nmul (u 2) (w 1)),
    Poly.nsub (Poly.nmul (u 2) (w 0)) (Poly.nmul (u 0) (w 2)),
    Poly.nsub (Poly.nmul (u 0) (w 1)) (Poly.nmul (u 1) (w 0))]
def dot (u w : PV) : Poly :=
  Poly.nadd (Poly.nadd (Poly.nmul (u 0) (w 0)) (Poly.nmul (u 1) (w 1))) (Poly.nmul (u 2) (w 2))
/-- Apply a rational matrix. -/
def matApply (N : Fin 3 → Fin 3 → ℚ) (u : PV) : PV := fun i =>
  Poly.nadd (Poly.nadd (Poly.scale (N i 0) (u 0)) (Poly.scale (N i 1) (u 1))) (Poly.scale (N i 2) (u 2))

variable (x : Fin 3 → ℝ)

theorem eval_add (u w : PV) (i : Fin 3) : ((add u w) i).eval x = (u i).eval x + (w i).eval x := by
  simp [add, Poly.eval_nadd]
theorem eval_sub (u w : PV) (i : Fin 3) : ((sub u w) i).eval x = (u i).eval x - (w i).eval x := by
  simp [sub, Poly.eval_nsub]
theorem eval_smul (p : Poly) (u : PV) (i : Fin 3) :
    ((smul p u) i).eval x = p.eval x * (u i).eval x := by
  simp [smul, Poly.eval_nmul]
theorem eval_cross0 (u w : PV) :
    ((cross u w) 0).eval x = (u 1).eval x * (w 2).eval x - (u 2).eval x * (w 1).eval x := by
  simp [cross, Poly.eval_nsub, Poly.eval_nmul]
theorem eval_cross1 (u w : PV) :
    ((cross u w) 1).eval x = (u 2).eval x * (w 0).eval x - (u 0).eval x * (w 2).eval x := by
  simp [cross, Poly.eval_nsub, Poly.eval_nmul]
theorem eval_cross2 (u w : PV) :
    ((cross u w) 2).eval x = (u 0).eval x * (w 1).eval x - (u 1).eval x * (w 0).eval x := by
  simp [cross, Poly.eval_nsub, Poly.eval_nmul]
theorem eval_dot (u w : PV) :
    (dot u w).eval x = (u 0).eval x * (w 0).eval x + (u 1).eval x * (w 1).eval x +
      (u 2).eval x * (w 2).eval x := by
  simp [dot, Poly.eval_nadd, Poly.eval_nmul]
theorem eval_matApply (N : Fin 3 → Fin 3 → ℚ) (u : PV) (i : Fin 3) :
    ((matApply N u) i).eval x = (N i 0 : ℝ) * (u 0).eval x + (N i 1 : ℝ) * (u 1).eval x +
      (N i 2 : ℝ) * (u 2).eval x := by
  simp [matApply, Poly.eval_nadd, Poly.eval_scale]

/-- `denc • w + 2 • (c × w + c × (c × w))`. -/
def cn (c : PV) (denc : Poly) (w : PV) : PV :=
  add (smul denc w) (smul (Poly.const 2) (add (cross c w) (cross c (cross c w))))


theorem eval_cn (c : PV) (denc : Poly) (w : PV)
    (hd : denc.eval x = 1 + (c 0).eval x ^ 2 + (c 1).eval x ^ 2 + (c 2).eval x ^ 2) (i : Fin 3) :
    ((cn c denc w) i).eval x =
      Noperts.cayleyNumeratorMatrix ((c 0).eval x) ((c 1).eval x) ((c 2).eval x) i 0 * (w 0).eval x +
      Noperts.cayleyNumeratorMatrix ((c 0).eval x) ((c 1).eval x) ((c 2).eval x) i 1 * (w 1).eval x +
      Noperts.cayleyNumeratorMatrix ((c 0).eval x) ((c 1).eval x) ((c 2).eval x) i 2 * (w 2).eval x := by
  have h2 : (Poly.const 2).eval x = 2 := by simp [Poly.eval_const]
  fin_cases i <;>
    simp [cn, eval_add, eval_smul, h2, hd, eval_cross0, eval_cross1, eval_cross2,
      Noperts.cayleyNumeratorMatrix] <;> ring


end PV

/-- A certificate for one polynomial inequality: `p = x₂^m q`, and `q(x₀, x₁, dc + x₂) > 0` by `tree`. -/
structure Cert where
  m : ℕ
  dc : ℚ
  tree : SplitTree
  /-- `false`: monomial lower bounds (`checkTree`); `true`: centred form (`checkTreeC`, root box symmetric). -/
  centred : Bool := false

/-- The vertices of the shape `(s, y, z)`, as polynomial vectors. -/
def vertP (s y z : Poly) (k : Fin 7) : PV := fun j =>
  if k.val < 3 then (if j.val = k.val then Poly.const 0 else Poly.const 1)
  else if k.val < 6 then
    (if j.val + 3 = k.val then Poly.nadd (Poly.const 1) y else Poly.nadd (Poly.const 1) z)
  else s

/-- Check one certificate on the slab box `|x₀| ≤ H0, |x₁| ≤ H1, D0 ≤ x₂ ≤ D1`. -/
def checkCert (H0 H1 D0 D1 : ℚ) (p : Poly) (c : Cert) : Bool :=
  match Poly.divX2 p c.m with
  | none => false
  | some q =>
    if c.centred then
      decide (D0 + D1 = 2 * c.dc) &&
        checkTreeC (Poly.shiftX2 q c.dc) ![-H0, -H1, D0 - c.dc] ![H0, H1, D1 - c.dc] c.tree
    else
      checkTree (Poly.shiftX2 q c.dc)
        { lo := ![-H0, -H1, D0 - c.dc], hi := ![H0, H1, D1 - c.dc] } c.tree

/-- The data of one slab. `tri k = (a, b, c)`: the inner vertex `k` is seen inside the triangle of outer
vertices `a, b, c`. -/
structure SlabData where
  H0 : ℚ
  H1 : ℚ
  D0 : ℚ
  D1 : ℚ
  s : Poly
  y : Poly
  z : Poly
  v : PV
  cay : PV
  t0 : Poly
  t1 : Poly
  N0 : Fin 3 → Fin 3 → ℚ
  m0 : ℚ
  tri : Fin 7 → Fin 7 × Fin 7 × Fin 7
  vj : Fin 3
  vs : ℚ
  vcert : Cert
  tcert : Fin 7 → Fin 3 → Cert

/-! ### Integer form of the condition polynomials

The conditions are recomputed over `ℤ`, after clearing denominators (`Poly.clear`), with the merge product of
`IPoly`. With `c = ci / Dc`, `v = vi / Dv`, `t = ti / Dt`, `(s, y, z) = (si, yi, zi) / Dp`, `N0 = N0i / Dn`,
`m0 = m0n / m0d`, `dI = Dc² + ci·ci` and `Λ = Dc² Dn Dp m0d Dt`, `κ = Dn Dt m0n`: `Xo_b = κ dI Pi_b / Λ`,
`W_k = WI_k / Λ`, and `cond = condI / (Dv Λ²)` where
`condI = κ dI (κ dI vi·(Pi_b × Pi_c) − WI·(vi × (Pi_b − Pi_c)))`. -/

namespace Poly

/-- Multiply by the natural number `D` and take numerators (exact if `D` clears the denominators). -/
def clear (D : ℕ) (p : Poly) : IPoly := p.map fun t => (t.1, (t.2 * (D : ℚ)).num)

/-- Check that `D` clears all denominators. -/
def clearOk (D : ℕ) (p : Poly) : Bool := p.all fun t => decide ((t.2 * (D : ℚ)).den = 1)

theorem eval_clear {D : ℕ} {p : Poly} (h : clearOk D p = true) (x : Fin 3 → ℝ) :
    (clear D p).eval x = D * p.eval x := by
  induction p with
  | nil => simp [clear]
  | cons t p ih =>
    simp only [clearOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih' := ih (by simpa [clearOk] using h.2)
    have hn : (((t.2 * D).num : ℤ) : ℚ) = t.2 * D := Rat.coe_int_num_of_den_eq_one h.1
    have hnR : (((t.2 * D).num : ℤ) : ℝ) = (t.2 : ℝ) * D := by
      have := congrArg (Rat.cast : ℚ → ℝ) hn
      push_cast at this; exact this
    simp only [clear, List.map_cons, IPoly.eval_cons] at ih' ⊢
    rw [ih', hnR, eval_cons]
    simp only [termEval]; ring

end Poly

/-- Least common multiple of a list. -/
def lcmList (l : List ℕ) : ℕ := l.foldl Nat.lcm 1

def polyDens (p : Poly) : List ℕ := p.map fun t => t.2.den

/-- Shared data of the integer computation (computed once per slab). -/
structure ICore where
  ci : IV
  vi : IV
  dI : IPoly
  dK : IPoly
  dIt : IV
  si : IPoly
  yi : IPoly
  zi : IPoly
  N0i : Fin 3 → Fin 3 → ℤ

namespace SlabData

variable (D : SlabData)

def Dc : ℕ := lcmList ((List.finRange 3).flatMap fun j => polyDens (D.cay j))
def Dv : ℕ := lcmList ((List.finRange 3).flatMap fun j => polyDens (D.v j))
def Dt : ℕ := lcmList (polyDens D.t0 ++ polyDens D.t1)
def Dp : ℕ := lcmList (polyDens D.s ++ polyDens D.y ++ polyDens D.z)
def Dn : ℕ := lcmList ((List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => (D.N0 i j).den)
def m0n : ℤ := D.m0.num
def m0d : ℤ := D.m0.den
/-- `Λ`. -/
def Lam : ℤ := (D.Dc : ℤ) ^ 2 * D.Dn * D.Dp * D.m0d * D.Dt
/-- `κ`. -/
def kap : ℤ := (D.Dn : ℤ) * D.Dt * D.m0n

/-- The denominators are cleared exactly (`check` tests this). -/
def denomsOk : Prop :=
  0 < D.Dc ∧ 0 < D.Dv ∧ 0 < D.Dt ∧ 0 < D.Dp ∧ 0 < D.Dn ∧
  (∀ j : Fin 3, Poly.clearOk D.Dc (D.cay j) = true) ∧ (∀ j : Fin 3, Poly.clearOk D.Dv (D.v j) = true) ∧
  Poly.clearOk D.Dt D.t0 = true ∧ Poly.clearOk D.Dt D.t1 = true ∧
  Poly.clearOk D.Dp D.s = true ∧ Poly.clearOk D.Dp D.y = true ∧ Poly.clearOk D.Dp D.z = true ∧
  (∀ i j : Fin 3, (D.N0 i j * (D.Dn : ℚ)).den = 1)

instance : Decidable D.denomsOk := by unfold denomsOk; infer_instance

def core : ICore :=
  let ci : IV := fun j => Poly.clear D.Dc (D.cay j)
  let ti : IV := ![Poly.clear D.Dt D.t0, Poly.clear D.Dt D.t1, []]
  let dI := IPoly.madd (IPoly.const ((D.Dc : ℤ) ^ 2)) (IV.dot ci ci)
  { ci := ci
    vi := fun j => Poly.clear D.Dv (D.v j)
    dI := dI
    dK := IPoly.scale D.kap dI
    dIt := IV.smul dI ti
    si := Poly.clear D.Dp D.s
    yi := Poly.clear D.Dp D.y
    zi := Poly.clear D.Dp D.z
    N0i := fun i j => (D.N0 i j * (D.Dn : ℚ)).num }

/-- The integer vertex `k`, scaled by `Dp`. -/
def PiK (C : ICore) (k : Fin 7) : IV := fun j =>
  if k.val < 3 then (if j.val = k.val then [] else IPoly.const D.Dp)
  else if k.val < 6 then
    (if j.val + 3 = k.val then IPoly.madd (IPoly.const D.Dp) C.yi else IPoly.madd (IPoly.const D.Dp) C.zi)
  else C.si

def matApplyI (N : Fin 3 → Fin 3 → ℤ) (u : IV) : IV := fun i =>
  IPoly.madd (IPoly.madd (IPoly.scale (N i 0) (u 0)) (IPoly.scale (N i 1) (u 1))) (IPoly.scale (N i 2) (u 2))

/-- `Dc² · Cn w`. -/
def CnI (C : ICore) (w : IV) : IV :=
  IV.add (IV.smul C.dI w)
    (IV.add (IV.cscale (2 * (D.Dc : ℤ)) (IV.cross C.ci w)) (IV.cscale 2 (IV.cross C.ci (IV.cross C.ci w))))

/-- `Λ · W_k`. -/
def WI (C : ICore) (k : Fin 7) : IV :=
  IV.add (IV.cscale (D.m0d * D.Dt) (D.CnI C (matApplyI C.N0i (D.PiK C k))))
    (IV.cscale ((D.Dn : ℤ) * D.Dp * D.m0n) C.dIt)

/-- The vertex pair of the `e`-th triangle condition of vertex `k`. -/
def pairOf (k : Fin 7) (e : Fin 3) : Fin 7 × Fin 7 :=
  let a := (D.tri k).1
  let b := (D.tri k).2.1
  let c := (D.tri k).2.2
  if e = 0 then (b, c) else if e = 1 then (c, a) else (a, b)

/-- `Dv Λ² · cond k e`, from `WI k`. -/
def condI (C : ICore) (Wk : IV) (k : Fin 7) (e : Fin 3) : IPoly :=
  let X := D.PiK C (D.pairOf k e).1
  let Y := D.PiK C (D.pairOf k e).2
  let c1 := IV.dot C.vi (IV.cross X Y)
  let c2 := IV.cross C.vi (IV.sub X Y)
  IPoly.mul C.dK (IPoly.sub (IPoly.mul C.dK c1) (IV.dot Wk c2))

end SlabData

namespace SlabData

variable (D : SlabData)

def P (k : Fin 7) : PV := vertP D.s D.y D.z k
def denc : Poly := Poly.nadd (Poly.const 1) (PV.dot D.cay D.cay)
def S : Poly := Poly.nmul D.denc (Poly.const D.m0)
def tv : PV := ![D.t0, D.t1, []]
def W (k : Fin 7) : PV :=
  PV.add (PV.cn D.cay D.denc (PV.matApply D.N0 (D.P k))) (PV.smul D.S D.tv)
def Xo (k : Fin 7) : PV := PV.smul D.S (D.P k)

/-- The `e`-th triangle condition of inner vertex `k`. -/
def cond (k : Fin 7) (e : Fin 3) : Poly :=
  let a := (D.tri k).1
  let b := (D.tri k).2.1
  let c := (D.tri k).2.2
  if e = 0 then PV.dot D.v (PV.cross (PV.sub (D.Xo b) (D.W k)) (PV.sub (D.Xo c) (D.W k)))
  else if e = 1 then PV.dot D.v (PV.cross (PV.sub (D.Xo c) (D.W k)) (PV.sub (D.Xo a) (D.W k)))
  else PV.dot D.v (PV.cross (PV.sub (D.Xo a) (D.W k)) (PV.sub (D.Xo b) (D.W k)))

/-- The view condition polynomial `vs * v_vj`. -/
def vcond : Poly := Poly.scale D.vs (D.v D.vj)

def matOk : Prop :=
  (∀ i j : Fin 3, ∑ k : Fin 3, D.N0 i k * D.N0 j k = if i = j then D.m0 ^ 2 else 0) ∧
  D.N0 0 0 * D.N0 1 1 * D.N0 2 2 - D.N0 0 0 * D.N0 1 2 * D.N0 2 1 - D.N0 0 1 * D.N0 1 0 * D.N0 2 2 +
    D.N0 0 1 * D.N0 1 2 * D.N0 2 0 + D.N0 0 2 * D.N0 1 0 * D.N0 2 1 -
    D.N0 0 2 * D.N0 1 1 * D.N0 2 0 = D.m0 ^ 3

instance : Decidable D.matOk := by unfold matOk; infer_instance

def viewEncOk : Prop := (D.vs = 1 ∨ D.vs = -1) ∧ (D.vj = 2 → D.vs = 1)

instance : Decidable D.viewEncOk := by unfold viewEncOk; infer_instance

/-- The checker. The condition polynomials are recomputed over `ℤ` (`condI`). -/
def check : Bool :=
  decide (0 < D.D0 ∧ D.D0 ≤ D.D1 ∧ 0 ≤ D.H0 ∧ 0 ≤ D.H1 ∧ 0 < D.m0) && decide D.matOk &&
  decide D.viewEncOk && decide D.denomsOk &&
  checkCert D.H0 D.H1 D.D0 D.D1 D.vcond D.vcert &&
  (let C := D.core
   (List.finRange 7).all fun k =>
    let Wk := D.WI C k
    (List.finRange 3).all fun e =>
      checkCert D.H0 D.H1 D.D0 D.D1 (D.condI C Wk k e).toPoly (D.tcert k e))

end SlabData

theorem checkCert_pos {H0 H1 D0 D1 : ℚ} {p : Poly} {c : Cert}
    (h : checkCert H0 H1 D0 D1 p c = true) (x : Fin 3 → ℝ) (h0 : |x 0| ≤ H0) (h1 : |x 1| ≤ H1)
    (h2 : (D0 : ℝ) ≤ x 2) (h3 : x 2 ≤ D1) (hpos : 0 < x 2) : 0 < p.eval x := by
  unfold checkCert at h
  split at h
  · exact absurd h (by simp)
  · rename_i q hq
    have hp : 0 < (Poly.shiftX2 q c.dc).eval ![x 0, x 1, x 2 - c.dc] := by
      obtain ⟨a0, a1⟩ := abs_le.mp h0
      obtain ⟨b0, b1⟩ := abs_le.mp h1
      by_cases hc : c.centred = true
      · rw [ite_eq_left hc] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hs, h⟩ := h
        have hsR : (D0 : ℝ) + D1 = 2 * c.dc := by exact_mod_cast hs
        have := pos_of_checkTreeC h (x := ![x 0, x 1, x 2 - c.dc]) (by
          intro i
          fin_cases i <;> simp <;> constructor <;> linarith)
        convert this using 2
        ext i
        fin_cases i <;> simp; linarith
      · rw [ite_eq_right hc] at h
        have hb : Box.mem { lo := ![-H0, -H1, D0 - c.dc], hi := ![H0, H1, D1 - c.dc] }
            ![x 0, x 1, x 2 - c.dc] := by
          intro i
          fin_cases i <;> simp <;> constructor <;> linarith
        exact pos_of_checkTree h hb
    rw [Poly.eval_shiftX2] at hp
    have hx : (![x 0, x 1, (c.dc : ℝ) + (x 2 - c.dc)] : Fin 3 → ℝ) = x := by
      ext i; fin_cases i <;> simp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hp
    rw [show (c.dc : ℝ) + (x 2 - c.dc) = x 2 by ring] at hp
    rw [Poly.eval_divX2 hq x]
    refine mul_pos (pow_pos hpos _) ?_
    have hx' : (![x 0, x 1, x 2] : Fin 3 → ℝ) = x := by ext i; fin_cases i <;> simp
    rwa [hx'] at hp

namespace SlabData

variable (D : SlabData)

/-- The Septopert-family parameters at `x`. -/
noncomputable def point (x : Fin 3 → ℝ) : ℝ³ := !₂[D.s.eval x, D.y.eval x, D.z.eval x]

/-- Real inner vertex `k`. -/
noncomputable def Vr (x : Fin 3 → ℝ) (k : Fin 7) : ℝ³ := WithLp.toLp 2 fun i => (D.P k i).eval x
noncomputable def tE (x : Fin 3 → ℝ) : ℝ³ := WithLp.toLp 2 fun i => (D.tv i).eval x
noncomputable def vE (x : Fin 3 → ℝ) : ℝ³ := WithLp.toLp 2 fun i => (D.v i).eval x
noncomputable def M0 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (D.N0 i j : ℝ) / D.m0
noncomputable def Q (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Noperts.cayleyMatrix ((D.cay 0).eval x) ((D.cay 1).eval x) ((D.cay 2).eval x) * D.M0

theorem toEuclideanLin_apply' (A : Matrix (Fin 3) (Fin 3) ℝ) (w : ℝ³) (i : Fin 3) :
    A.toEuclideanLin w i = ∑ j, A i j * w j := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem denc_eval (x : Fin 3 → ℝ) : D.denc.eval x =
    Noperts.cayleyDenom ((D.cay 0).eval x) ((D.cay 1).eval x) ((D.cay 2).eval x) := by
  simp only [denc, Poly.eval_nadd, Poly.eval_const, PV.eval_dot, Noperts.cayleyDenom]
  push_cast; ring

theorem S_eval (x : Fin 3 → ℝ) : D.S.eval x =
    Noperts.cayleyDenom ((D.cay 0).eval x) ((D.cay 1).eval x) ((D.cay 2).eval x) * D.m0 := by
  simp only [S, Poly.eval_nmul, denc_eval, Poly.eval_const]


theorem Xo_eval' (x : Fin 3 → ℝ) (k : Fin 7) (i : Fin 3) :
    ((D.Xo k) i).eval x = D.S.eval x * D.Vr x k i := by
  simp [Xo, PV.eval_smul, Vr]

theorem W_eval (hm : D.m0 ≠ 0) (x : Fin 3 → ℝ) (k : Fin 7) (i : Fin 3) :
    ((D.W k) i).eval x = D.S.eval x * ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x) i := by
  have hd := D.denc_eval x
  rw [W, PV.eval_add, PV.eval_cn x _ _ _ (by rw [hd]; simp [Noperts.cayleyDenom]) i, PV.eval_smul,
    S_eval]
  simp only [PV.eval_matApply, PiLp.add_apply, toEuclideanLin_apply', Fin.sum_univ_three, Q, M0,
    Matrix.mul_apply, Vr, tE]
  rw [Noperts.cayleyMatrix_eq_div_numerator]
  have hpos := Noperts.cayleyDenom_ne ((D.cay 0).eval x) ((D.cay 1).eval x) ((D.cay 2).eval x)
  simp only [Matrix.of_apply]
  field_simp
  ring

theorem cond_eval (hm : D.m0 ≠ 0) (x : Fin 3 → ℝ) (k p q : Fin 7) :
    (PV.dot D.v (PV.cross (PV.sub (D.Xo p) (D.W k)) (PV.sub (D.Xo q) (D.W k)))).eval x =
      D.S.eval x ^ 2 * triple (D.vE x)
        (D.Vr x p - ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x))
        (D.Vr x q - ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x)) := by
  simp only [PV.eval_dot, PV.eval_cross0, PV.eval_cross1, PV.eval_cross2, PV.eval_sub, Xo_eval',
    W_eval D hm, triple, vE, PiLp.sub_apply]
  ring

theorem M0_mem (hmat : D.matOk) (hm : D.m0 ≠ 0) : D.M0 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  obtain ⟨ho, hd⟩ := hmat
  have hO : ∀ i j : Fin 3, ∑ k, (D.N0 i k : ℝ) * D.N0 j k = if i = j then (D.m0 : ℝ) ^ 2 else 0 := by
    intro i j
    have h' := congrArg (Rat.cast : ℚ → ℝ) (ho i j)
    split_ifs at h' ⊢ <;> push_cast at h' ⊢ <;> exact h'
  have hdR : (D.N0 0 0 : ℝ) * D.N0 1 1 * D.N0 2 2 - D.N0 0 0 * D.N0 1 2 * D.N0 2 1 -
      D.N0 0 1 * D.N0 1 0 * D.N0 2 2 + D.N0 0 1 * D.N0 1 2 * D.N0 2 0 +
      D.N0 0 2 * D.N0 1 0 * D.N0 2 1 - D.N0 0 2 * D.N0 1 1 * D.N0 2 0 = (D.m0 : ℝ) ^ 3 := by
    exact_mod_cast hd
  have hmR : (D.m0 : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · have key : ∀ i j, (D.M0 * D.M0.transpose) i j =
        (∑ k, (D.N0 i k : ℝ) * D.N0 j k) / (D.m0 : ℝ) ^ 2 := by
      intro i j
      simp only [M0, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    ext i j
    rw [key, hO, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij, hmR]
    · simp [hij]
  · rw [Matrix.det_fin_three]
    simp only [M0, Matrix.of_apply]
    field_simp
    linear_combination hdR

theorem Q_mem (hmat : D.matOk) (hm : D.m0 ≠ 0) (x : Fin 3 → ℝ) :
    D.Q x ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Submonoid.mul_mem _ (Noperts.cayleyMatrix_mem_SO3 _ _ _) (D.M0_mem hmat hm)

theorem Vr_eq (x : Fin 3 → ℝ) (k : Fin 7) : D.Vr x k =
    if k.val < 3 then !₂[if (0 : ℕ) = k.val then (0 : ℝ) else 1, if (1 : ℕ) = k.val then 0 else 1,
        if (2 : ℕ) = k.val then 0 else 1]
    else if k.val < 6 then
      !₂[if 0 + 3 = k.val then 1 + D.y.eval x else 1 + D.z.eval x,
        if 1 + 3 = k.val then 1 + D.y.eval x else 1 + D.z.eval x,
        if 2 + 3 = k.val then 1 + D.y.eval x else 1 + D.z.eval x]
    else !₂[D.s.eval x, D.s.eval x, D.s.eval x] := by
  ext j
  fin_cases j <;> by_cases h1 : k.val < 3 <;> by_cases h2 : k.val < 6 <;>
    simp [Vr, P, vertP, h1, h2] <;>
    split_ifs <;> simp [Poly.eval_nadd, Poly.eval_const]

theorem vert_mem (x : Fin 3 → ℝ) (k : Fin 7) : D.Vr x k ∈ shellVerts (D.point x) := by
  rw [Vr_eq]
  fin_cases k <;> simp [shellVerts, point]

theorem mem_vert (x : Fin 3 → ℝ) (w : ℝ³) (hw : w ∈ shellVerts (D.point x)) : ∃ k, w = D.Vr x k := by
  simp only [shellVerts, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with h | h | h | h | h | h | h
  · exact ⟨0, by rw [h, Vr_eq]; simp⟩
  · exact ⟨1, by rw [h, Vr_eq]; simp⟩
  · exact ⟨2, by rw [h, Vr_eq]; simp⟩
  · exact ⟨3, by rw [h, Vr_eq]; simp [point]⟩
  · exact ⟨4, by rw [h, Vr_eq]; simp [point]⟩
  · exact ⟨5, by rw [h, Vr_eq]; simp [point]⟩
  · exact ⟨6, by rw [h, Vr_eq]; simp [point]⟩

theorem cond_eq (hm : D.m0 ≠ 0) (x : Fin 3 → ℝ) (k : Fin 7) (e : Fin 3) :
    (D.cond k e).eval x = D.S.eval x ^ 2 * triple (D.vE x)
      (D.Vr x (if e = 0 then (D.tri k).2.1 else if e = 1 then (D.tri k).2.2 else (D.tri k).1) -
        ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x))
      (D.Vr x (if e = 0 then (D.tri k).2.2 else if e = 1 then (D.tri k).1 else (D.tri k).2.1) -
        ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x)) := by
  fin_cases e <;> simp [cond, cond_eval D hm]

theorem S_pos (hm : 0 < D.m0) (x : Fin 3 → ℝ) : 0 < D.S.eval x := by
  rw [S_eval]
  exact mul_pos (Noperts.cayleyDenom_pos _ _ _) (by exact_mod_cast hm)


/-! ### Soundness of the integer form -/

section IntForm

variable (x : Fin 3 → ℝ)

theorem S_ev' (x : Fin 3 → ℝ) : D.S.eval x = D.denc.eval x * D.m0 := by
  simp [S, Poly.eval_nmul, Poly.eval_const]

theorem denc_ev' (x : Fin 3 → ℝ) : D.denc.eval x =
    1 + (D.cay 0).eval x * (D.cay 0).eval x + (D.cay 1).eval x * (D.cay 1).eval x +
      (D.cay 2).eval x * (D.cay 2).eval x := by
  simp [denc, Poly.eval_nadd, Poly.eval_const, PV.eval_dot]
  ring

variable {D}

theorem core_ci (hd : D.denomsOk) (j : Fin 3) : (D.core.ci j).eval x = D.Dc * (D.cay j).eval x :=
  Poly.eval_clear (hd.2.2.2.2.2.1 j) x

theorem core_vi (hd : D.denomsOk) (j : Fin 3) : (D.core.vi j).eval x = D.Dv * (D.v j).eval x :=
  Poly.eval_clear (hd.2.2.2.2.2.2.1 j) x

theorem core_si (hd : D.denomsOk) : D.core.si.eval x = D.Dp * D.s.eval x :=
  Poly.eval_clear hd.2.2.2.2.2.2.2.2.2.1 x
theorem core_yi (hd : D.denomsOk) : D.core.yi.eval x = D.Dp * D.y.eval x :=
  Poly.eval_clear hd.2.2.2.2.2.2.2.2.2.2.1 x
theorem core_zi (hd : D.denomsOk) : D.core.zi.eval x = D.Dp * D.z.eval x :=
  Poly.eval_clear hd.2.2.2.2.2.2.2.2.2.2.2.1 x

theorem core_dI (hd : D.denomsOk) : D.core.dI.eval x = (D.Dc : ℝ) ^ 2 * D.denc.eval x := by
  have h1 := core_ci x hd
  simp only [core, IPoly.eval_madd, IPoly.eval_const, IV.eval_dot] at h1 ⊢
  rw [denc_ev']
  simp only [h1]
  push_cast; ring

theorem core_dIt (hd : D.denomsOk) (i : Fin 3) :
    (D.core.dIt i).eval x = (D.Dc : ℝ) ^ 2 * D.denc.eval x * (D.Dt * (D.tv i).eval x) := by
  have h1 := core_dI x hd
  have h2 : ((![Poly.clear D.Dt D.t0, Poly.clear D.Dt D.t1, []] : IV) i).eval x
      = D.Dt * (D.tv i).eval x := by
    fin_cases i
    · exact Poly.eval_clear hd.2.2.2.2.2.2.2.1 x
    · exact Poly.eval_clear hd.2.2.2.2.2.2.2.2.1 x
    · simp [tv]
  simp only [core, IV.eval_smul] at h1 ⊢
  rw [h1, h2]

theorem PiK_ev (hd : D.denomsOk) (k : Fin 7) (j : Fin 3) :
    (D.PiK D.core k j).eval x = D.Dp * (D.P k j).eval x := by
  have h1 := core_si x hd
  have h2 := core_yi x hd
  have h3 := core_zi x hd
  simp only [core] at h1 h2 h3
  unfold PiK SlabData.P vertP
  simp only [core]
  split_ifs <;> simp [IPoly.eval_madd, IPoly.eval_const, Poly.eval_nadd, Poly.eval_const, h1, h2, h3] <;> ring

theorem N0i_ev (hd : D.denomsOk) (i j : Fin 3) : (D.core.N0i i j : ℝ) = D.Dn * (D.N0 i j : ℝ) := by
  have hn : (((D.N0 i j * (D.Dn : ℚ)).num : ℤ) : ℚ) = D.N0 i j * D.Dn :=
    Rat.coe_int_num_of_den_eq_one (hd.2.2.2.2.2.2.2.2.2.2.2.2 i j)
  have := congrArg (Rat.cast : ℚ → ℝ) hn
  push_cast at this
  simp only [core]
  rw [this]; ring

theorem matApplyI_ev (hd : D.denomsOk) (u : IV) (w : PV) (lam : ℝ)
    (h : ∀ j, (u j).eval x = lam * (w j).eval x) (i : Fin 3) :
    ((matApplyI D.core.N0i u) i).eval x = D.Dn * lam * ((PV.matApply D.N0 w) i).eval x := by
  simp only [matApplyI, IPoly.eval_madd, IPoly.eval_scale, PV.eval_matApply, h, N0i_ev hd]
  ring

theorem m0_ev (_hm : 0 < D.m0) : (D.m0 : ℝ) = (D.m0n : ℝ) / D.m0d := by
  have h : D.m0 = (D.m0n : ℚ) / (D.m0d : ℚ) := by
    simp only [m0n, m0d]; push_cast
    exact (Rat.num_div_den D.m0).symm
  have := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at this; exact this

theorem m0d_pos : (0 : ℝ) < D.m0d := by simp only [m0d]; exact_mod_cast D.m0.den_pos
theorem m0n_pos (hm : 0 < D.m0) : (0 : ℝ) < D.m0n := by
  simp only [m0n]; exact_mod_cast Rat.num_pos.mpr hm

theorem Lam_ev : (D.Lam : ℝ) = (D.Dc : ℝ) ^ 2 * D.Dn * D.Dp * D.m0d * D.Dt := by
  simp [Lam]

theorem kap_ev : (D.kap : ℝ) = (D.Dn : ℝ) * D.Dt * D.m0n := by simp [kap]

theorem Lam_pos (hd : D.denomsOk) (_hm : 0 < D.m0) : (0 : ℝ) < D.Lam := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hd
  rw [Lam_ev]
  have := m0d_pos (D := D)
  have : (0 : ℝ) < D.Dc := by exact_mod_cast h1
  have : (0 : ℝ) < D.Dt := by exact_mod_cast h3
  have : (0 : ℝ) < D.Dp := by exact_mod_cast h4
  have : (0 : ℝ) < D.Dn := by exact_mod_cast h5
  positivity

theorem WI_ev (hd : D.denomsOk) (hm : 0 < D.m0) (k : Fin 7) (i : Fin 3) :
    ((D.WI D.core k) i).eval x = D.Lam * ((D.W k) i).eval x := by
  have hc := core_ci x hd
  have hdI := core_dI x hd
  have hdIt := core_dIt x hd
  have hmat := matApplyI_ev x hd (D.PiK D.core k) (D.P k) D.Dp (fun j => PiK_ev x hd k j)
  have h2 : (Poly.const 2).eval x = 2 := by simp [Poly.eval_const]
  have hm0 := m0_ev hm
  have hmd := m0d_pos (D := D)
  have hDc : (D.Dc : ℝ) ≠ 0 := by have := hd.1; positivity
  have hDt : (D.Dt : ℝ) ≠ 0 := by have := hd.2.2.1; positivity
  have hDn : (D.Dn : ℝ) ≠ 0 := by have := hd.2.2.2.2.1; positivity
  have hDp : (D.Dp : ℝ) ≠ 0 := by have := hd.2.2.2.1; positivity
  unfold WI W CnI PV.cn
  fin_cases i <;>
  · simp [IV.eval_add, IV.eval_cscale, IV.eval_smul, IV.eval_cross0, IV.eval_cross1, IV.eval_cross2,
      PV.eval_add, PV.eval_smul, PV.eval_cross0, PV.eval_cross1, PV.eval_cross2, hc, hdI, hdIt, hmat, h2,
      S_ev', Lam_ev, hm0, -Nat.cast_ofNat]
    field_simp

theorem condI_ev (hd : D.denomsOk) (hm : 0 < D.m0) (k : Fin 7) (e : Fin 3) :
    (D.condI D.core (D.WI D.core k) k e).eval x = D.Dv * (D.Lam : ℝ) ^ 2 * (D.cond k e).eval x := by
  have hcond : D.cond k e = PV.dot D.v (PV.cross (PV.sub (D.Xo (D.pairOf k e).1) (D.W k))
      (PV.sub (D.Xo (D.pairOf k e).2) (D.W k))) := by
    unfold cond pairOf; split_ifs <;> rfl
  rw [hcond]
  unfold condI
  generalize (D.pairOf k e) = pr
  have hLam := (Lam_pos hd hm).ne'
  have hDv : (D.Dv : ℝ) ≠ 0 := by have := hd.2.1; positivity
  have hdI := core_dI x hd
  have hdK : D.core.dK.eval x = D.kap * D.core.dI.eval x := by
    simp only [core]; exact IPoly.eval_scale _ _ _
  have hX : ∀ (p : Fin 7) (j : Fin 3), ((D.Xo p) j).eval x =
      D.kap * D.core.dI.eval x * (D.PiK D.core p j).eval x / D.Lam := by
    intro p j
    rw [Xo, PV.eval_smul, S_ev', PiK_ev x hd, hdI, m0_ev hm, Lam_ev, kap_ev]
    have hmd := m0d_pos (D := D)
    have hDc : (D.Dc : ℝ) ≠ 0 := by have := hd.1; positivity
    have hDt : (D.Dt : ℝ) ≠ 0 := by have := hd.2.2.1; positivity
    have hDn : (D.Dn : ℝ) ≠ 0 := by have := hd.2.2.2.2.1; positivity
    have hDp : (D.Dp : ℝ) ≠ 0 := by have := hd.2.2.2.1; positivity
    field_simp
  have hW : ∀ j, ((D.W k) j).eval x = ((D.WI D.core k) j).eval x / D.Lam := by
    intro j; rw [WI_ev x hd hm]; field_simp
  have hv : ∀ j, (D.v j).eval x = (D.core.vi j).eval x / D.Dv := by
    intro j; rw [core_vi x hd]; field_simp
  simp only [IPoly.eval_mul, IPoly.eval_sub, IV.eval_dot, IV.eval_cross0, IV.eval_cross1, IV.eval_cross2,
    IV.eval_sub, PV.eval_dot, PV.eval_cross0, PV.eval_cross1, PV.eval_cross2, PV.eval_sub, hX, hW, hv, hdK]
  field_simp
  ring

end IntForm

/-- **Soundness.** If the slab check succeeds then every shape `(s, y, z)(x)` of the slab is Rupert. -/
theorem isRupert_of_check (h : D.check = true) (x : Fin 3 → ℝ)
    (h0 : |x 0| ≤ D.H0) (h1 : |x 1| ≤ D.H1) (h2 : (D.D0 : ℝ) ≤ x 2) (h3 : x 2 ≤ D.D1) :
    IsRupert (shellVerts (D.point x)) := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨⟨⟨⟨⟨hD0, hD01, hH0, hH1, hm0⟩, hmat⟩, hve⟩, hden⟩, hvc⟩, ht⟩ := h
  have hDr : (0 : ℝ) < D.D0 := by exact_mod_cast hD0
  have hx2 : 0 < x 2 := lt_of_lt_of_le hDr h2
  have hm : D.m0 ≠ 0 := hm0.ne'
  have hview : ViewOk (D.vE x) := by
    have hv := checkCert_pos hvc x h0 h1 h2 h3 hx2
    rw [vcond, Poly.eval_scale] at hv
    obtain ⟨hs1, hs2⟩ := hve
    have e0 : D.vE x 0 = (D.v 0).eval x := rfl
    have e1 : D.vE x 1 = (D.v 1).eval x := rfl
    have e2 : D.vE x 2 = (D.v 2).eval x := rfl
    unfold ViewOk
    generalize D.vj = j at hv hs2
    fin_cases j
    · right; left
      intro h0'; rw [e0] at h0'; simp [h0'] at hv
    · right; right
      intro h0'; rw [e1] at h0'; simp [h0'] at hv
    · left
      have := hs2 rfl
      rw [e2]; simpa [this] using hv
  have hQ := D.Q_mem hmat hm x
  have hS2 : 0 < D.S.eval x ^ 2 := by have := D.S_pos hm0 x; positivity
  refine isRupert_of_view _ (D.vE x) hview hQ (D.tE x) ?_
  intro w hw
  obtain ⟨k, rfl⟩ := D.mem_vert x w hw
  have hcond : ∀ e : Fin 3, 0 < (D.cond k e).eval x := by
    intro e
    have h1 := checkCert_pos (ht k e) x h0 h1 h2 h3 hx2
    have h2' : 0 < (D.condI D.core (D.WI D.core k) k e).eval x := h1
    rw [condI_ev x hden hm0 k e] at h2'
    have hDv : (0 : ℝ) < D.Dv * (D.Lam : ℝ) ^ 2 := by
      have := Lam_pos hden hm0
      have hh : (0 : ℝ) < D.Dv := by have := hden.2.1; exact_mod_cast this
      positivity
    exact (mul_pos_iff_of_pos_left hDv).mp h2'
  have key : ∀ e : Fin 3, 0 < (D.cond k e).eval x → 0 < D.S.eval x ^ 2 * triple (D.vE x)
      (D.Vr x (if e = 0 then (D.tri k).2.1 else if e = 1 then (D.tri k).2.2 else (D.tri k).1) -
        ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x))
      (D.Vr x (if e = 0 then (D.tri k).2.2 else if e = 1 then (D.tri k).1 else (D.tri k).2.1) -
        ((D.Q x).toEuclideanLin (D.Vr x k) + D.tE x)) := by
    intro e he; rwa [cond_eq D hm] at he
  refine ⟨D.Vr x (D.tri k).1, D.vert_mem x _, D.Vr x (D.tri k).2.1, D.vert_mem x _,
    D.Vr x (D.tri k).2.2, D.vert_mem x _, ?_, ?_, ?_⟩
  · have := (mul_pos_iff_of_pos_left hS2).mp (key 0 (hcond 0))
    simpa using this
  · have := (mul_pos_iff_of_pos_left hS2).mp (key 1 (hcond 1))
    simpa using this
  · have := (mul_pos_iff_of_pos_left hS2).mp (key 2 (hcond 2))
    simpa using this

end SlabData

end SeptopertShell

end
