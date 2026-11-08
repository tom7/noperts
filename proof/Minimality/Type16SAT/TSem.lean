module

public import Minimality.Type16SAT.TCore
public import Minimality.Type16SAT.Ent3
public import Minimality.SplitLeaf

@[expose] public section

/-!
# L16T, T2: the real meaning of the tie variables (`rhoW`) and their sign facts

DESIGN sections 2 to 4 and 3 in particular.  For a facet `t` and a difference `f` (index of `Sem.edges`):
* `wf g t f = N_t x D_f` (the tie view `u_f`), `dplus g t f = |N_t|^2 D_f - <N_t, D_f> N_t = - N_t x wf`
  (the direction `d_+` of the perturbation, `u' = wf + eps * sigma * dplus`);
* `Pp g t f q = det(D_f, D_q, N_t) = <wf, D_q>` (the menu atom `kv t f q`), `Rr g t f q = <dplus, D_q>`,
  `Kk g t f s = <dplus, N_s>`, `Ls g t s x = det(N_t, N_s, D_x)` (the encoder's `lineS(t,s,x)`);
* `Z0 g t f`: `wf = 0` (`D_f // N_t`), the guard of the tie rules.
`rhoW g` extends `rho g` by the DESIGN convention: under `Z0`, `RH := sign <D_f, D_q>` and `KA := +`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical

namespace Minimality.H16T.SAT
open Minimality.H29.SAT Minimality.H16.SAT

/-! ### The vectors and numbers -/

/-- The tie view `u_f = N_t x D_f`. -/
noncomputable def wf (g : Geo) (t f : Nat) : ℝ³ := cross (g.N t) (g.dv f)
/-- The perturbation direction `d_+ = |N_t|^2 D_f - <N_t, D_f> N_t` (`= - N_t x wf`). -/
noncomputable def dplus (g : Geo) (t f : Nat) : ℝ³ := ⟪g.N t, g.N t⟫ • g.dv f - ⟪g.N t, g.dv f⟫ • g.N t
/-- `P(f,q) = det(D_f, D_q, N_t)`: the second argument of the depth of the pair `q` at `u'`, zero order term. -/
noncomputable def Pp (g : Geo) (t f q : Nat) : ℝ := det3 (g.dv f) (g.dv q) (g.N t)
/-- `R(f,q) = <dplus, D_q>`: the first order term of the depth of the pair `q`. -/
noncomputable def Rr (g : Geo) (t f q : Nat) : ℝ := ⟪dplus g t f, g.dv q⟫
/-- `K(s) = <dplus, N_s>`: the first order term of the facing of `s`. -/
noncomputable def Kk (g : Geo) (t f s : Nat) : ℝ := ⟪dplus g t f, g.N s⟫
/-- `L(s,x) = det(N_t, N_s, D_x)`: the encoder's `lineS(t,s,x)`. -/
noncomputable def Ls (g : Geo) (t s x : Nat) : ℝ := det3 (g.N t) (g.N s) (g.dv x)
/-- The guard: `D_f` is parallel to `N_t`, so there is no view. -/
def Z0 (g : Geo) (t f : Nat) : Prop := wf g t f = 0
/-- `Rr` with the `Z0` convention: `<D_f, D_q>` under `Z0`. -/
noncomputable def Rtie (g : Geo) (t f q : Nat) : ℝ := if Z0 g t f then ⟪g.dv f, g.dv q⟫ else Rr g t f q
/-- `Kk` with the `Z0` convention: `1` under `Z0`. -/
noncomputable def Ktie (g : Geo) (t f s : Nat) : ℝ := if Z0 g t f then 1 else Kk g t f s

macro "vec_ring" : tactic =>
  `(tactic| (simp only [det3_expand, inn3, cross_apply_zero, cross_apply_one, cross_apply_two,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.add_apply, smul_eq_mul]; ring))

/-! ### The expansions of DESIGN 2.1 (ring) -/

/-- `P(f,q)` is the depth difference `<wf, D_q>` at the tie view. -/
theorem P_eq (g : Geo) (t f q : Nat) : Pp g t f q = ⟪wf g t f, g.dv q⟫ := by
  unfold Pp wf; vec_ring

/-- `dplus = - N x wf`, in the form `<dplus, x> = - det(N, wf, x)` (for every vector `x`). -/
theorem inner_dplus_neg (g : Geo) (t f : Nat) (x : ℝ³) :
    ⟪dplus g t f, x⟫ = -det3 (g.N t) (wf g t f) x := by
  unfold dplus wf; vec_ring

/-- `<dplus, x> = <wf, N x x>` for every vector. -/
theorem inner_dplus (g : Geo) (t f : Nat) (x : ℝ³) : ⟪dplus g t f, x⟫ = ⟪wf g t f, cross (g.N t) x⟫ := by
  unfold dplus wf; vec_ring

/-- `R(f,q) = <wf, N x D_q>`. -/
theorem R_eq (g : Geo) (t f q : Nat) : Rr g t f q = ⟪wf g t f, cross (g.N t) (g.dv q)⟫ :=
  inner_dplus g t f _

/-- `R(f,q) = |N|^2 <D_f, D_q> - <N, D_f> <N, D_q>`. -/
theorem R_expand (g : Geo) (t f q : Nat) :
    Rr g t f q = ⟪g.N t, g.N t⟫ * ⟪g.dv f, g.dv q⟫ - ⟪g.N t, g.dv f⟫ * ⟪g.N t, g.dv q⟫ := by
  unfold Rr dplus; vec_ring

/-- `K(s) = |N|^2 <D_f, N_s> - <N, D_f> <N, N_s>`. -/
theorem K_expand (g : Geo) (t f s : Nat) :
    Kk g t f s = ⟪g.N t, g.N t⟫ * ⟪g.dv f, g.N s⟫ - ⟪g.N t, g.dv f⟫ * ⟪g.N t, g.N s⟫ := by
  unfold Kk dplus; vec_ring

/-- `K(s) = <wf, N x N_s>`. -/
theorem K_eq (g : Geo) (t f s : Nat) : Kk g t f s = ⟪wf g t f, cross (g.N t) (g.N s)⟫ :=
  inner_dplus g t f _

/-- The depth of `d_f` itself: `P(f,f) = 0`, `R(f,f) = |wf|^2`. -/
theorem P_self (g : Geo) (t f : Nat) : Pp g t f f = 0 := by unfold Pp; vec_ring
theorem R_self (g : Geo) (t f : Nat) : Rr g t f f = ⟪wf g t f, wf g t f⟫ := by
  unfold Rr dplus wf; vec_ring

/-- `P` is antisymmetric. -/
theorem P_swap (g : Geo) (t f q : Nat) : Pp g t q f = -Pp g t f q := by unfold Pp; vec_ring

/-- `P(f,q)` as the shape atom `kv t f q` (no hypotheses). -/
theorem atom_kv (g : Geo) (t f q : Nat) : g.atom (V.kv t f q) = Pp g t f q := rfl

/-- The facing of `s` at `wf` (zero order term): `<N_s, wf> = - L(s,f)`. -/
theorem facing_wf (g : Geo) (t s f : Nat) : ⟪g.N s, wf g t f⟫ = -Ls g t s f := by
  unfold wf Ls; vec_ring

/-- `t` is edge-on at every `eps`: `<N_t, wf> = 0` and `<N_t, dplus> = 0`. -/
theorem inner_N_wf (g : Geo) (t f : Nat) : ⟪g.N t, wf g t f⟫ = 0 := by unfold wf; vec_ring
theorem inner_N_dplus (g : Geo) (t f : Nat) : ⟪g.N t, dplus g t f⟫ = 0 := by unfold dplus; vec_ring
/-- `wf` and `dplus` are orthogonal. -/
theorem inner_wf_dplus (g : Geo) (t f : Nat) : ⟪wf g t f, dplus g t f⟫ = 0 := by unfold wf dplus; vec_ring
/-- `det(N_t, - wf, D_f) = |wf|^2`: the side `sigma` of `y_+ = - wf` (DESIGN 2.1). -/
theorem det3_N_negwf_D (g : Geo) (t f : Nat) :
    det3 (g.N t) (-wf g t f) (g.dv f) = ⟪wf g t f, wf g t f⟫ := by unfold wf; vec_ring

/-- **The master identity** (DESIGN 4.6), for all vectors:
`det(N,x,y) |N x D|^2 = det(N,x,D) R(y) + R(x) det(N,D,y)`, `R(z) = <N x D, N x z>`. -/
theorem master_id (N D x y : ℝ³) :
    det3 N x y * ⟪cross N D, cross N D⟫ =
      det3 N x D * ⟪cross N D, cross N y⟫ + ⟪cross N D, cross N x⟫ * det3 N D y := by
  vec_ring

/-- **Master identity, RH form** (x = D_b, y = D_q):
`P(b,q) |wf|^2 = P(b,f) R(f,q) + R(f,b) P(f,q)`. -/
theorem master_P (g : Geo) (t f b q : Nat) :
    Pp g t b q * ⟪wf g t f, wf g t f⟫ = Pp g t b f * Rr g t f q + Rr g t f b * Pp g t f q := by
  have h := master_id (g.N t) (g.dv f) (g.dv b) (g.dv q)
  have e1 : det3 (g.N t) (g.dv b) (g.dv q) = Pp g t b q := by unfold Pp; vec_ring
  have e2 : det3 (g.N t) (g.dv b) (g.dv f) = Pp g t b f := by unfold Pp; vec_ring
  have e3 : det3 (g.N t) (g.dv f) (g.dv q) = Pp g t f q := by unfold Pp; vec_ring
  have e4 : ⟪cross (g.N t) (g.dv f), cross (g.N t) (g.dv q)⟫ = Rr g t f q := (R_eq g t f q).symm
  have e5 : ⟪cross (g.N t) (g.dv f), cross (g.N t) (g.dv b)⟫ = Rr g t f b := (R_eq g t f b).symm
  rw [e1, e2, e3, e4, e5] at h
  exact h

/-- **Master identity, KA form** (x = N_s, y = D_b):
`L(s,b) |wf|^2 = L(s,f) R(f,b) + K(s) P(f,b)`. -/
theorem master_K (g : Geo) (t f s b : Nat) :
    Ls g t s b * ⟪wf g t f, wf g t f⟫ = Ls g t s f * Rr g t f b + Kk g t f s * Pp g t f b := by
  have h := master_id (g.N t) (g.dv f) (g.N s) (g.dv b)
  have e1 : det3 (g.N t) (g.N s) (g.dv b) = Ls g t s b := rfl
  have e2 : det3 (g.N t) (g.N s) (g.dv f) = Ls g t s f := rfl
  have e3 : det3 (g.N t) (g.dv f) (g.dv b) = Pp g t f b := by unfold Pp; vec_ring
  have e4 : ⟪cross (g.N t) (g.dv f), cross (g.N t) (g.dv b)⟫ = Rr g t f b := (R_eq g t f b).symm
  have e5 : ⟪cross (g.N t) (g.dv f), cross (g.N t) (g.N s)⟫ = Kk g t f s := (K_eq g t f s).symm
  rw [e1, e2, e3, e4, e5] at h
  exact h

/-- `Z0` kills `P`: `wf = 0` gives `P(f,q) = 0`. -/
theorem P_of_Z0 {g : Geo} {t f : Nat} (h : Z0 g t f) (q : Nat) : Pp g t f q = 0 := by
  rw [P_eq, h]; simp

/-- `Z0` kills `L(s,f)`. -/
theorem Ls_of_Z0 {g : Geo} {t f : Nat} (h : Z0 g t f) (s : Nat) : Ls g t s f = 0 := by
  have := facing_wf g t s f
  rw [h] at this; simpa using this.symm

/-- Off `Z0` the norm of `wf` is positive. -/
theorem wf_pos {g : Geo} {t f : Nat} (h : ¬ Z0 g t f) : 0 < ⟪wf g t f, wf g t f⟫ :=
  real_inner_self_pos.mpr h

/-! ### `rhoW` -/

/-- The side `sigma = +-1` of a tie rule (`sd = 1` is `+`). -/
def sdR (sd : Nat) : ℝ := if sd = 1 then 1 else -1

/-- `lexLt` at the tie view: the depth of `p` is lex less than that of `q` at `u' = wf + eps sigma dplus`. -/
noncomputable def lexLtT (g : Geo) (t f sd p q : Nat) : Prop :=
  ⟪wf g t f, g.x p - g.x q⟫ < 0 ∨
    (⟪wf g t f, g.x p - g.x q⟫ = 0 ∧ sdR sd * ⟪dplus g t f, g.x p - g.x q⟫ < 0)

/-- The four pairs of an alternation are not lex less-than at the tie view. -/
noncomputable def yT (g : Geo) (t f sd p1 p2 q1 q2 : Nat) : Bool :=
  decide (¬ lexLtT g t f sd p1 q1 ∧ ¬ lexLtT g t f sd p1 q2 ∧ ¬ lexLtT g t f sd p2 q1 ∧ ¬ lexLtT g t f sd p2 q2)

/-- The vector `v` of a `qv` variable: kind 0 (line view, `key` = the VIEW number `e` in `21 .. 35`, as the encoder's
`Qget(0, e, ..)` with `LA[e], LB[e]`): the view `vv e = N_A x N_B` for `lines[e - 21] = (A, B)` (J5 fix: J3a had the line
index); kind 1 (tie view, `key = 32 t + f`): `wf t f` (so `Q = 0` under `Z0`); other kinds: `0`. -/
noncomputable def qvVec (g : Geo) (kind key : Nat) : ℝ³ :=
  if kind = 0 then g.vv key
  else if kind = 1 then wf g (key / 32) (key % 32) else 0

/-- `Q = det(D_e1, D_e2, v)`. -/
noncomputable def Qv (g : Geo) (kind key e1 e2 : Nat) : ℝ := det3 (g.dv e1) (g.dv e2) (qvVec g kind key)

/-- The vertex cycle of a split flag, as a function on `ZMod cyc.length`. -/
noncomputable def cycX (g : Geo) (cyc : List Nat) : ZMod cyc.length → ℝ³ := fun i => g.x (cyc.getD i.val 0)

/-- **The split flag.**  A split certificate for the cycle `cyc` exists: `(a, cc, sigma)` with `cc != a, a + 1`,
`sigma = +-1`, and the rows `SplitRows` at the menu view `vv view` (kind 0), resp. `LexRows` at the tie view
`(wf t f, sdR sd * dplus t f)`, `t = view` (kind 1).  The flag `sf` is the negation: no certificate. -/
def SplitCert (g : Geo) (kind view f sd : Nat) (cyc : List Nat) : Prop :=
  ∃ (a cc : ZMod cyc.length) (σ : ℝ), cc ≠ a ∧ cc ≠ a + 1 ∧ (σ = 1 ∨ σ = -1) ∧
    (if kind = 0 then Minimality.Split.SplitRows (cycX g cyc) (g.vv view) a cc σ
     else Minimality.Split.LexRows (cycX g cyc) (wf g view f) (sdR sd • dplus g view f) a cc σ)

/-- **The truth assignment of the tie file.**  `base` is `Sem.rho`; under `Z0`: `RH := sign <D_f, D_q>`,
`KA := +`, `ty = tfail = false`. -/
noncomputable def rhoW (g : Geo) : W → Bool
  | .base v => rho g v
  | .rh t f q pos =>
    if Z0 g t f then (if pos then decide (0 < ⟪g.dv f, g.dv q⟫) else decide (⟪g.dv f, g.dv q⟫ < 0))
    else (if pos then decide (0 < Rr g t f q) else decide (Rr g t f q < 0))
  | .ka t f s pos =>
    if Z0 g t f then pos
    else (if pos then decide (0 < Kk g t f s) else decide (Kk g t f s < 0))
  | .z0 t f => decide (Z0 g t f)
  | .ty t f sd p1 p2 q1 q2 => !decide (Z0 g t f) && yT g t f sd p1 p2 q1 q2
  | .tfail t f sd c => !decide (Z0 g t f) && (alts c).any fun a => yT g t f sd a.1 a.2.1 a.2.2.1 a.2.2.2
  | .wgate sa a sb b => (sa == rhoW g a) && (sb == rhoW g b)
  | .qv kind key e1 e2 pos =>
    if pos then decide (0 < Qv g kind key e1 e2) else decide (Qv g kind key e1 e2 < 0)
  | .sf kind view f sd cyc => decide (¬ SplitCert g kind view f sd cyc)

theorem rhoW_base (g : Geo) (v : V) : rhoW g (W.base v) = rho g v := rfl
theorem rhoW_wgate (g : Geo) (sa : Bool) (a : W) (sb : Bool) (b : W) :
    rhoW g (W.wgate sa a sb b) = (evalW (rhoW g) (sa, a) && evalW (rhoW g) (sb, b)) := rfl
theorem rhoW_z0 (g : Geo) (t f : Nat) : rhoW g (W.z0 t f) = decide (Z0 g t f) := rfl

theorem rhoW_qv (g : Geo) (kind key e1 e2 : Nat) (pos : Bool) :
    rhoW g (W.qv kind key e1 e2 pos) =
      (if pos then decide (0 < Qv g kind key e1 e2) else decide (Qv g kind key e1 e2 < 0)) := rfl
theorem rhoW_sf (g : Geo) (kind view f sd : Nat) (cyc : List Nat) :
    rhoW g (W.sf kind view f sd cyc) = decide (¬ SplitCert g kind view f sd cyc) := rfl

/-- The signs of `Q`: a three valued sign built from the two `qv` variables. -/
def QS (kind key e1 e2 : Nat) : S3W := ((true, W.qv kind key e1 e2 true), (true, W.qv kind key e1 e2 false))

theorem SgW_Q (g : Geo) (kind key e1 e2 : Nat) : SgW (rhoW g) (QS kind key e1 e2) (Qv g kind key e1 e2) := by
  simp [SgW, QS, evalW, rhoW]

theorem rhoW_proper (g : Geo) : ProperW (rhoW g) := by simp [ProperW, rhoW, rho]

theorem rhoW_gateOK (g : Geo) : GateOKW (rhoW g) := by
  intro sa a sb b
  cases a <;> cases b <;> simp [gateW, rhoW, rho, evalW]

/-- Un-lifting: `rhoW g` restricted to `base` is `rho g`. -/
theorem rhoW_comp_base (g : Geo) : (fun v => rhoW g (W.base v)) = rho g := rfl

/-- **A lifted menu clause holds under `rhoW g` iff it holds under `rho g`.** -/
theorem holdsW_rho_lift (g : Geo) (c : List Lit) : HoldsW (rhoW g) (liftCl c) ↔ Holds (rho g) c :=
  holds_lift (rhoW g) c

/-- A menu `Sg3` fact lifts. -/
theorem sgW_rho_lift {g : Geo} {t : S3} {r : ℝ} (h : Sg3 (rho g) t r) : SgW (rhoW g) (liftS t) r := h

/-- The equations of `ty` and `tfail`. -/
theorem rhoW_ty (g : Geo) (t f sd p1 p2 q1 q2 : Nat) :
    rhoW g (W.ty t f sd p1 p2 q1 q2) = (!decide (Z0 g t f) && yT g t f sd p1 p2 q1 q2) := rfl
theorem rhoW_ty_Z0 {g : Geo} {t f : Nat} (h : Z0 g t f) (sd p1 p2 q1 q2 : Nat) :
    rhoW g (W.ty t f sd p1 p2 q1 q2) = false := by simp [rhoW, h]
theorem rhoW_tfail (g : Geo) (t f sd : Nat) (c : List Nat) :
    rhoW g (W.tfail t f sd c) =
      (!decide (Z0 g t f) && (alts c).any fun a => yT g t f sd a.1 a.2.1 a.2.2.1 a.2.2.2) := rfl
theorem rhoW_tfail_Z0 {g : Geo} {t f : Nat} (h : Z0 g t f) (sd : Nat) (c : List Nat) :
    rhoW g (W.tfail t f sd c) = false := by simp [rhoW, h]

/-! ### Sign facts: P, RH, KA, Z0 -/

/-- The three valued sign of `P(f,q)`: the atom `kv t f q` for `f < q`, its negation for `q < f`, zero for `f = q`. -/
def PS (t f q : Nat) : S3 :=
  if f < q then atomS (V.kv t f q) else if q < f then negS (atomS (V.kv t q f)) else zeroS

/-- **`P` has its sign**, no hypothesis (zero or not). -/
theorem Sg_P (g : Geo) (t f q : Nat) : Sg3 (rho g) (PS t f q) (Pp g t f q) := by
  unfold PS
  by_cases h1 : f < q
  · rw [if_pos h1]
    exact Sg3_atomG g (v := V.kv t f q) (by simp [rho])
  · rw [if_neg h1]
    by_cases h2 : q < f
    · rw [if_pos h2, P_swap]
      exact (Sg3_atomG g (v := V.kv t q f) (by simp [rho])).neg
    · rw [if_neg h2]
      have : f = q := by omega
      subst this
      rw [P_self]; exact Sg3_zeroG g

theorem SgW_P (g : Geo) (t f q : Nat) : SgW (rhoW g) (liftS (PS t f q)) (Pp g t f q) :=
  sgW_rho_lift (Sg_P g t f q)

/-- The two Booleans of `RH(t,f,q)` as a `W` three valued sign. -/
def RS (t f q : Nat) : S3W := ((true, W.rh t f q true), (true, W.rh t f q false))
/-- The two Booleans of `KA(t,f,s)`. -/
def KS (t f s : Nat) : S3W := ((true, W.ka t f s true), (true, W.ka t f s false))
/-- The literal of the guard `Z0(t,f)`. -/
def Z0L (t f : Nat) : LitW := (true, W.z0 t f)

/-- Off `Z0`: `RH` has the sign of `R(f,q)`. -/
theorem SgW_RH_off {g : Geo} {t f : Nat} (hz : ¬ Z0 g t f) (q : Nat) :
    SgW (rhoW g) (RS t f q) (Rr g t f q) := by
  simp [SgW, RS, evalW, rhoW, hz]

/-- Under `Z0`: `RH` has the sign of `<D_f, D_q>`. -/
theorem SgW_RH_on {g : Geo} {t f : Nat} (hz : Z0 g t f) (q : Nat) :
    SgW (rhoW g) (RS t f q) ⟪g.dv f, g.dv q⟫ := by
  simp [SgW, RS, evalW, rhoW, hz]

/-- `RH` with the convention, both branches in one statement. -/
theorem SgW_RH (g : Geo) (t f q : Nat) : SgW (rhoW g) (RS t f q) (Rtie g t f q) := by
  by_cases hz : Z0 g t f
  · simp only [Rtie, hz, if_true]; exact SgW_RH_on hz q
  · simp only [Rtie, hz, if_false]; exact SgW_RH_off hz q

/-- Off `Z0`: `KA` has the sign of `K(s)`. -/
theorem SgW_KA_off {g : Geo} {t f : Nat} (hz : ¬ Z0 g t f) (s : Nat) :
    SgW (rhoW g) (KS t f s) (Kk g t f s) := by
  simp [SgW, KS, evalW, rhoW, hz]

/-- Under `Z0`: `KA` is `+` (the sign of `1`). -/
theorem SgW_KA_on {g : Geo} {t f : Nat} (hz : Z0 g t f) (s : Nat) :
    SgW (rhoW g) (KS t f s) 1 := by
  simp [SgW, KS, evalW, rhoW, hz]

/-- `KA` with the convention, both branches in one statement. -/
theorem SgW_KA (g : Geo) (t f s : Nat) : SgW (rhoW g) (KS t f s) (Ktie g t f s) := by
  by_cases hz : Z0 g t f
  · simp only [Ktie, hz, if_true]; exact SgW_KA_on hz s
  · simp only [Ktie, hz, if_false]; exact SgW_KA_off hz s

/-- The guard literal is true iff `Z0`. -/
theorem evalW_Z0L (g : Geo) (t f : Nat) : evalW (rhoW g) (Z0L t f) = true ↔ Z0 g t f := by
  simp [Z0L, evalW, rhoW]

/-- The exclusion rows of `RH` and `KA` (family 35, kinds 3 and 4): not both signs. -/
theorem rh_excl (g : Geo) (t f q : Nat) :
    HoldsW (rhoW g) [(false, W.rh t f q true), (false, W.rh t f q false)] := by
  by_cases hz : Z0 g t f
  · have h := SgW_RH_on hz q
    by_cases h1 : 0 < ⟪g.dv f, g.dv q⟫
    · refine ⟨(false, W.rh t f q false), by simp, ?_⟩
      have : ¬ ⟪g.dv f, g.dv q⟫ < 0 := not_lt.mpr h1.le
      simp [evalW, rhoW, hz, this]
    · refine ⟨(false, W.rh t f q true), by simp, ?_⟩
      simp [evalW, rhoW, hz, h1]
  · by_cases h1 : 0 < Rr g t f q
    · refine ⟨(false, W.rh t f q false), by simp, ?_⟩
      have : ¬ Rr g t f q < 0 := not_lt.mpr h1.le
      simp [evalW, rhoW, hz, this]
    · refine ⟨(false, W.rh t f q true), by simp, ?_⟩
      simp [evalW, rhoW, hz, h1]

theorem ka_excl (g : Geo) (t f s : Nat) :
    HoldsW (rhoW g) [(false, W.ka t f s true), (false, W.ka t f s false)] := by
  by_cases hz : Z0 g t f
  · refine ⟨(false, W.ka t f s false), by simp, ?_⟩
    simp [evalW, rhoW, hz]
  · by_cases h1 : 0 < Kk g t f s
    · refine ⟨(false, W.ka t f s false), by simp, ?_⟩
      have : ¬ Kk g t f s < 0 := not_lt.mpr h1.le
      simp [evalW, rhoW, hz, this]
    · refine ⟨(false, W.ka t f s true), by simp, ?_⟩
      simp [evalW, rhoW, hz, h1]

/-! ### `lineS`: the encoder's `lineS(t,s,x) = k * T(view, x)` (FORMAT.md, vmap line `LS t s view k`) -/

/-- `lineS(t,s,x)` as the vmap line `LS t s view k` gives it: `k * T(view, x)`, `k = +-1`. -/
def lsS (view : Nat) (k : Int) (x : Nat) : S3 := if 0 < k then Tt view x else negS (Tt view x)

/-- Check of an `LS` line for a non-adjacent pair: `view = 21 + l`, `lines[l] = (t,s)` with `k = 1`, or `(s,t)` with `k = -1`. -/
def lsLineChk (t s view : Nat) (k : Int) : Bool :=
  decide (21 ≤ view) &&
    ((decide ((lines.getD (view - 21) (0, 0)) = (t, s)) && decide (k = 1)) ||
     (decide ((lines.getD (view - 21) (0, 0)) = (s, t)) && decide (k = -1)))

theorem Ls_eq_inner (g : Geo) (t s x : Nat) : Ls g t s x = ⟪cross (g.N t) (g.N s), g.dv x⟫ := rfl

/-- **`LS` for a non-adjacent pair** (line view): `lineS(t,s,x) = k T(view,x)`, for a difference `x < 21`. -/
theorem ls_line_sound (g : Geo) {t s view : Nat} {k : Int} (h : lsLineChk t s view k = true) {x : Nat} (hx : x < 21) :
    Sg3 (rho g) (lsS view k x) (Ls g t s x) := by
  simp only [lsLineChk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨h21, h⟩ := h
  have hvv : g.vv view = cross (g.N (lines.getD (view - 21) (0, 0)).1) (g.N (lines.getD (view - 21) (0, 0)).2) := by
    unfold Geo.vv; rw [if_neg (by omega)]
  have hx' : g.vv x = g.dv x := by unfold Geo.vv; rw [if_pos hx]
  have T := Sg3_Tt g view x (fun h' h'' => by omega)
  rw [hvv, hx'] at T
  unfold lsS
  rcases h with ⟨hp, hk⟩ | ⟨hp, hk⟩
  · rw [hp] at T
    have : (0 : Int) < k := by omega
    rw [if_pos this]
    simpa [Ls_eq_inner] using T
  · rw [hp] at T
    have : ¬ (0 : Int) < k := by omega
    rw [if_neg this]
    have T' := T.neg
    have e : -⟪cross (g.N s) (g.N t), g.dv x⟫ = Ls g t s x := by unfold Ls; vec_ring
    rw [e] at T'
    exact T'

theorem EA_EB_lt7 : ∀ e < 21, EA e < 7 ∧ EB e < 7 := by decide

/-- Check of an `LS` line for an adjacent pair sharing the edge `view < 21`: with `p = EA view`, `q = EB view`, there are
`r'` of `s` off `t` and `s'` of `t` off `s`, `D_view` is the difference of two points of both facets, and `k = 1` iff
`oriv t p q s' < 0` (so `k = sign det(N_t, N_s, D_view)`). -/
def lsAdjChk (t s view : Nat) (k : Int) : Bool :=
  decide (view < 21) &&
  (List.range 7).any fun r' => (List.range 7).any fun s' =>
    inF t (EA view) && inF t (EB view) && inF s (EA view) && inF s (EB view) && inF s r' && !inF t r' &&
    inF t s' && !inF s s' &&
    ((decide (k = 1) && decide (oriv t (EA view) (EB view) s' < 0)) ||
     (decide (k = -1) && decide (0 < oriv t (EA view) (EB view) s'))) &&
    (List.range 8).any fun f => inF f (EA view) && !inF f (EB view)

/-- **`LS` for an adjacent pair** (shared edge `view`): `lineS(t,s,x) = k T(view,x)`, `k = CE` of the encoder, for `x < 21`. -/
theorem ls_adj_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) {t s view : Nat} {k : Int}
    (h : lsAdjChk t s view k = true) {x : Nat} (hx : x < 21) :
    Sg3 (rho g) (lsS view k x) (Ls g t s x) := by
  simp only [lsAdjChk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range] at h
  obtain ⟨hv21, r', hr', s', hs', ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpt, hqt⟩, hps⟩, hqs⟩, hrs⟩, hrt⟩, hst⟩, hss⟩, hk⟩, f, hf9, hf⟩⟩ := h
  set p := EA view with hp
  set q := EB view with hq
  have hp7 : p < 7 := (EA_EB_lt7 view hv21).1
  have hq7 : q < 7 := (EA_EB_lt7 view hv21).2
  have hdq : g.x p - g.x q ≠ 0 := dne hF p q f hq7 (by simpa using hf.1) (by simpa using hf.2)
  have hDe : g.dv view = g.x p - g.x q := rfl
  have hvv : g.vv view = g.dv view := by unfold Geo.vv; rw [if_pos hv21]
  have hx' : g.vv x = g.dv x := by unfold Geo.vv; rw [if_pos hx]
  have hnz : g.vv view ≠ 0 := by rw [hvv, hDe]; exact hdq
  have T := Sg3_Tt g view x (fun _ _ => hnz)
  rw [hvv, hx'] at T
  have ha : ⟪g.dv view, g.N t⟫ = 0 := by
    rw [real_inner_comm, hDe]; exact hF.zero t p q hpt hqt
  have hb : ⟪g.dv view, g.N s⟫ = 0 := by
    rw [real_inner_comm, hDe]; exact hF.zero s p q hps hqs
  have dd : 0 < ⟪g.dv view, g.dv view⟫ := real_inner_self_pos.mpr (by rw [hDe]; exact hdq)
  have id := det_perp (g.N t) (g.N s) (g.dv x) (g.dv view) ha hb
  have e : Ls g t s x = (1 / ⟪g.dv view, g.dv view⟫) *
      (det3 (g.N t) (g.N s) (g.dv view) * ⟪g.dv view, g.dv x⟫) := by
    unfold Ls; field_simp; linarith [id]
  have K := kap_sound hF hO t s p q r' s' hpt hqt hps hqs hrs (by simpa using hrt) hst
    (by simpa using hss) (by omega) (by omega) (by rcases hk with ⟨_, h⟩ | ⟨_, h⟩ <;> omega) hdq
  unfold lsS
  rcases hk with ⟨hk1, ho⟩ | ⟨hk1, ho⟩
  · have hk0 : (0 : Int) < k := by omega
    rw [if_pos hk0]
    have hc : 0 < det3 (g.N t) (g.N s) (g.dv view) := by
      have : (0 : ℝ) < -(oriv t p q s' : ℝ) := by
        have : (oriv t p q s' : ℝ) < 0 := by exact_mod_cast ho
        linarith
      rw [hDe]
      exact (pos_iff_pos_of_mul_pos K).mp this
    rw [e]
    exact Sg3.scale (by positivity) (by
      have := T.scale hc
      simpa using this)
  · have hk0 : ¬ (0 : Int) < k := by omega
    rw [if_neg hk0]
    have hc : det3 (g.N t) (g.N s) (g.dv view) < 0 := by
      have h0 : (0 : ℝ) < oriv t p q s' := by exact_mod_cast ho
      rw [hDe]
      by_contra hn
      have hn' : 0 ≤ det3 (g.N t) (g.N s) (g.x p - g.x q) := not_lt.mp hn
      nlinarith
    rw [e]
    have T' := T.neg
    have := T'.scale (c := -det3 (g.N t) (g.N s) (g.dv view)) (by linarith)
    refine Sg3.scale (by positivity) ?_
    have e2 : -det3 (g.N t) (g.N s) (g.dv view) * -⟪g.dv view, g.dv x⟫ =
        det3 (g.N t) (g.N s) (g.dv view) * ⟪g.dv view, g.dv x⟫ := by ring
    rw [e2] at this
    exact this

/-- The union check: an `LS` line is a line-view line or an adjacent-edge line. -/
def lsOK (t s view : Nat) (k : Int) : Bool := lsLineChk t s view k || lsAdjChk t s view k

/-- **`LS` soundness** for any `LS t s view k` line that passes `lsOK`: `lineS(t,s,x) = k T(view,x)` as three valued signs
(for differences `x < 21`). -/
theorem ls_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) {t s view : Nat} {k : Int}
    (h : lsOK t s view k = true) {x : Nat} (hx : x < 21) :
    SgW (rhoW g) (liftS (lsS view k x)) (Ls g t s x) := by
  unfold lsOK at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
  · exact sgW_rho_lift (ls_line_sound g h1 hx)
  · exact sgW_rho_lift (ls_adj_sound hF hO h1 hx)

end Minimality.H16T.SAT
