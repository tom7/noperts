module

public import Minimality.Type29SAT.Core

@[expose] public section

/-!
# Type 16 bridge, Sem (copy of Type29SAT.Sem, J2a):  the real meaning of every variable, three valued schemas and their soundness

As L/B21Sem, but every entry is a three valued sign `S3` (no `Tm`, no `prod`, no `mux`) and no
row needs a nonzero hypothesis on an atom.  `tpv` (the tope variable) is read off a parameter
`Geo.tpv`, which the wiring sets to `TpSem` (B29Wit).  The tables are true only on the keys that
the rows use (`UsedTri`, `UsedNl`, `UsedFup`), since a table cannot be true at every key.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical

open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The real data: seven points and eight facet normals. -/
structure Geo where
  x : Nat → ℝ³
  N : Nat → ℝ³
  /-- the tope variable `Tp e mask sig`, set by the wiring to `TpSem` -/
  tpv : Nat → Nat → Nat → Bool

/-- The 21 differences: `edgeOf e = (a, b)` with `a < b`, in the order of the encoder. -/
def edges : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),
   (3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]
/-- First end of edge `e`. -/
def EA (e : Nat) : Nat := (edges.getD e (0, 0)).1
/-- Second end of edge `e`. -/
def EB (e : Nat) : Nat := (edges.getD e (0, 0)).2
/-- Index of the edge `a < b`. -/
def EI (a b : Nat) : Nat := edges.idxOf (a, b)
/-- The 15 pairs of facets without a common edge: the line views `21 .. 35` (type 16, facets A..H = 0..7
of `V2.fIdx`; the encoder's `initLines` order). -/
def lines : List (Nat × Nat) :=
  [(0,4),(0,5),(0,6),(1,2),(1,4),(1,7),(2,3),(2,5),(2,6),(3,5),(3,6),(3,7),(4,5),(4,7),(6,7)]

/-- The difference `x_a - x_b` of edge `e`. -/
def Geo.dv (g : Geo) (e : Nat) : ℝ³ := g.x (EA e) - g.x (EB e)
/-- View `e`: a difference, or the cross product of two facet normals. -/
noncomputable def Geo.vv (g : Geo) (e : Nat) : ℝ³ :=
  if e < 21 then g.dv e else
    cross (g.N (lines.getD (e - 21) (0, 0)).1) (g.N (lines.getD (e - 21) (0, 0)).2)
/-- Depth difference of points `a`, `b` at view `e`. -/
noncomputable def Geo.z (g : Geo) (e a b : Nat) : ℝ := ⟪g.vv e, g.x a - g.x b⟫

/-- The real number whose sign an atom names. -/
noncomputable def Geo.atom (g : Geo) : V → ℝ
  | .br a b c d => det3 (g.x b - g.x a) (g.x c - g.x a) (g.x d - g.x a)
  | .lv a b c p q => det3 (g.x b - g.x a) (g.x c - g.x a) (g.x p - g.x q)
  | .mv e f h => det3 (g.dv e) (g.dv f) (g.dv h)
  | .fv t p q => ⟪g.N t, g.x p - g.x q⟫
  | .nv r s t => det3 (g.N r) (g.N s) (g.N t)
  | .kv t e f => det3 (g.dv e) (g.dv f) (g.N t)
  | _ => 0

/-- The weak alternations along a cycle: positions `a < b < c < d`, both parities, as
`(p1, p2, q1, q2)` with `p` at least `q`.  The enumeration of `failVar` of the encoder. -/
def alts (c : List Nat) : List (Nat × Nat × Nat × Nat) :=
  let k := c.length
  (List.range k).flatMap fun a => (List.range k).flatMap fun b => (List.range k).flatMap fun e =>
    (List.range k).flatMap fun d =>
      if a < b ∧ b < e ∧ e < d then
        [(c.getD a 0, c.getD e 0, c.getD b 0, c.getD d 0),
         (c.getD b 0, c.getD d 0, c.getD a 0, c.getD e 0)]
      else []

/-- The four weak inequalities of an alternation at view `e`. -/
noncomputable def Geo.yB (g : Geo) (e p1 p2 q1 q2 : Nat) : Bool :=
  decide (0 ≤ g.z e p1 q1 ∧ 0 ≤ g.z e p1 q2 ∧ 0 ≤ g.z e p2 q1 ∧ 0 ≤ g.z e p2 q2)

/-- The sign `eps = +-1` of a lex row (`ep = 1` is `+1`). -/
def epR (ep : Nat) : ℝ := if ep = 1 then 1 else -1

/-- `lexLt`: the depth of `p` is lex less than that of `q`: `z e p q < 0`, or it is `0` and `eps * z d p q < 0`. -/
noncomputable def Geo.lexLt (g : Geo) (e d ep p q : Nat) : Prop :=
  g.z e p q < 0 ∨ (g.z e p q = 0 ∧ epR ep * g.z d p q < 0)

/-- The four pairs of an alternation are not lex less-than. -/
noncomputable def Geo.yL (g : Geo) (e d ep p1 p2 q1 q2 : Nat) : Bool :=
  decide (¬ g.lexLt e d ep p1 q1 ∧ ¬ g.lexLt e d ep p1 q2 ∧ ¬ g.lexLt e d ep p2 q1 ∧ ¬ g.lexLt e d ep p2 q2)

/-- **The truth assignment read off the real data.** -/
noncomputable def rho (g : Geo) : V → Bool
  | .tru => true
  | .gate sa a sb b => (sa == rho g a) && (sb == rho g b)
  | .ng a => decide (g.atom a < 0)
  | .tpv e m s => g.tpv e m s
  | .tp e f => decide (0 < ⟪g.vv e, g.vv f⟫)
  | .tq e f => decide (⟪g.vv e, g.vv f⟫ < 0)
  | .yv e p1 p2 q1 q2 => g.yB e p1 p2 q1 q2
  | .fail e c => (alts c).any fun t => g.yB e t.1 t.2.1 t.2.2.1 t.2.2.2
  | .ltl e d ep p q => decide (g.lexLt e d ep p q)
  | .yl e d ep _ p1 p2 q1 q2 => g.yL e d ep p1 p2 q1 q2
  | .faill e d ep c => (alts c).any fun t => g.yL e d ep t.1 t.2.1 t.2.2.1 t.2.2.2
  | v => decide (0 < g.atom v)

theorem rho_proper (g : Geo) : Proper (rho g) := by simp [Proper, rho]
theorem rho_gateOK (g : Geo) : GateOK (rho g) := fun sa a sb b => by simp [rho, evalL]

/-- **An atom has its three valued sign**, zero or not: no genericity hypothesis. -/
theorem Sg3_atomG (g : Geo) {v : V} (hv : rho g v = decide (0 < g.atom v)) :
    Sg3 (rho g) (atomS v) (g.atom v) := Sg3_atom hv (by simp [rho])

/-- The tables of the encoder: entries of sorted triples of edges and of facets, and the facing `Fup t p q`. -/
structure Tab where
  tri : Nat → Nat → Nat → S3
  nl : Nat → Nat → Nat → S3
  fup : Nat → Nat → Nat → S3

/-- `EntOK`: the three tables tell the truth about the real data on the keys that are used. -/
structure EntOK (T : Tab) (g : Geo) (ut un uf : Nat → Nat → Nat → Prop) where
  ent : ∀ a b c, ut a b c → Sg3 (rho g) (T.tri a b c) (det3 (g.dv a) (g.dv b) (g.dv c))
  nl : ∀ a b c, un a b c → Sg3 (rho g) (T.nl a b c) (det3 (g.N a) (g.N b) (g.N c))
  fup : ∀ t p q, uf t p q → Sg3 (rho g) (T.fup t p q) ⟪g.N t, g.x p - g.x q⟫

/-- Three valued sign of `⟪vv e, vv f⟫`. -/
def Tt (e f : Nat) : S3 :=
  if e = f then (if e < 21 then (ltrue, lfalse) else ((true, .tp e e), lfalse))
  else if e < f then ((true, .tp e f), (true, .tq e f)) else ((true, .tp f e), (true, .tq f e))

/-- `Tt` tells the truth at nonzero views. -/
theorem Sg3_Tt (g : Geo) (e f : Nat) (hv : e = f → e < 21 → g.vv e ≠ 0) : Sg3 (rho g) (Tt e f) ⟪g.vv e, g.vv f⟫ := by
  unfold Tt
  by_cases h1 : e = f
  · subst h1
    rw [ite_eq_left rfl]
    by_cases h21 : e < 21
    · rw [ite_eq_left h21]
      have : 0 < ⟪g.vv e, g.vv e⟫ := real_inner_self_pos.mpr (hv rfl h21)
      have h3 : ¬ ⟪g.vv e, g.vv e⟫ < 0 := not_lt.mpr this.le
      simp only [Sg3, ltrue, lfalse, evalL, rho, this, h3, iff_true, iff_false]
      simp
    · rw [ite_eq_right h21]
      have h3 : ¬ ⟪g.vv e, g.vv e⟫ < 0 := not_lt.mpr real_inner_self_nonneg
      simp [Sg3, lfalse, evalL, rho]
  · rw [ite_eq_right h1]
    by_cases h2 : e < f
    · rw [ite_eq_left h2]; simp [Sg3, evalL, rho]
    · rw [ite_eq_right h2]
      have := real_inner_comm (g.vv e) (g.vv f)
      simp [Sg3, evalL, rho, this]

/-- Zero as a three valued sign. -/
theorem Sg3_zeroG (g : Geo) : Sg3 (rho g) zeroS 0 := Sg3_zero (rho_proper g)

/-- Inner product in coordinates. -/
theorem inn3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- Four vectors of 3-space: the Cramer relation against any `w` (circuit orthogonality of a row, and
Cramer on four normals). -/
theorem four_dep (a b c d w : ℝ³) :
    det3 b c d * ⟪w, a⟫ + -det3 a c d * ⟪w, b⟫ + det3 a b d * ⟪w, c⟫ + -det3 a b c * ⟪w, d⟫ = 0 := by
  simp only [det3_expand, inn3]; ring

/-- Schema `row4`: row `e` of the sign matrix is orthogonal to the circuit of four differences. -/
def row4 (T : Tab) (e f0 f1 f2 f3 : Nat) : List (List Lit) :=
  z4 (mul3 (T.tri f1 f2 f3) (Tt e f0)) (mul3 (negS (T.tri f0 f2 f3)) (Tt e f1))
    (mul3 (T.tri f0 f1 f3) (Tt e f2)) (mul3 (negS (T.tri f0 f1 f2)) (Tt e f3))

/-- **Soundness of `row4`.** -/
theorem row4_sound {T : Tab} {g : Geo} {ut un uf : Nat → Nat → Nat → Prop} (h : EntOK T g ut un uf)
    (e f0 f1 f2 f3 : Nat) (hv : e < 21 → g.vv e ≠ 0)
    (hd : ∀ f < 21, g.vv f = g.dv f) (h0 : f0 < 21) (h1 : f1 < 21) (h2 : f2 < 21) (h3 : f3 < 21)
    (u1 : ut f1 f2 f3) (u2 : ut f0 f2 f3) (u3 : ut f0 f1 f3) (u4 : ut f0 f1 f2) :
    ∀ c ∈ row4 T e f0 f1 f2 f3, Holds (rho g) c := by
  have m := fun {t u a b} (x : Sg3 (rho g) t a) (y : Sg3 (rho g) u b) =>
    Sg3.mul3 (rho_proper g) (rho_gateOK g) x y
  have t := fun f (hf : f < 21) => Sg3_Tt g e f (fun h' _ => hv (h' ▸ hf))
  refine z4_sound (m (h.ent _ _ _ u1) (t f0 h0)) (m (h.ent _ _ _ u2).neg (t f1 h1))
    (m (h.ent _ _ _ u3) (t f2 h2)) (m (h.ent _ _ _ u4).neg (t f3 h3)) ?_
  rw [hd f0 h0, hd f1 h1, hd f2 h2, hd f3 h3]
  have := four_dep (g.dv f0) (g.dv f1) (g.dv f2) (g.dv f3) (g.vv e)
  simp only [real_inner_comm] at this ⊢
  linarith

/-- Three valued sign of depth at `a` minus depth at `b`, at view `e` (`ordS` of the encoder). -/
def ordS (e a b : Nat) : S3 := if a < b then Tt e (EI a b) else negS (Tt e (EI b a))

theorem EI_lt21 : ∀ a < 7, ∀ b < 7, a < b → EI a b < 21 := by decide

/-- `ordS` tells the truth.  The view is only required to be nonzero when it is an edge (`e < 21`). -/
theorem Sg3_ordS (g : Geo) (e a b : Nat) (hv : e < 21 → g.vv e ≠ 0) (hab : a ≠ b) (ha : a < 7) (hb : b < 7)
    (hd : ∀ a b, a < b → b < 7 → g.vv (EI a b) = g.x a - g.x b) :
    Sg3 (rho g) (ordS e a b) (g.z e a b) := by
  unfold ordS Geo.z
  split_ifs with h
  · have := Sg3_Tt g e (EI a b) (fun h' _ => hv (h' ▸ EI_lt21 a ha b hb h))
    rwa [hd a b h hb] at this
  · have hlt : b < a := by omega
    have := (Sg3_Tt g e (EI b a) (fun h' _ => hv (h' ▸ EI_lt21 b hb a ha hlt))).neg
    rw [hd b a hlt ha, ← inner_neg_right, neg_sub] at this
    exact this

/-- Schema `row3`: the three depth differences of `a, b, c` add to 0. -/
def row3 (e a b c : Nat) : List (List Lit) := z4 (ordS e a b) (ordS e b c) (ordS e c a) zeroS

/-- **Soundness of `row3`.** -/
theorem row3_sound {g : Geo} (e a b c : Nat) (hv : e < 21 → g.vv e ≠ 0)
    (hd : ∀ a b, a < b → b < 7 → g.vv (EI a b) = g.x a - g.x b)
    (ha : a < 7) (hb : b < 7) (hc : c < 7) (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ a) :
    ∀ cl ∈ row3 e a b c, Holds (rho g) cl := by
  refine z4_sound (Sg3_ordS g e a b hv h1 ha hb hd) (Sg3_ordS g e b c hv h2 hb hc hd)
    (Sg3_ordS g e c a hv h3 hc ha hd) (Sg3_zeroG g) ?_
  simp only [Geo.z, ← inner_add_right]
  simp

/-- Schema `cramer`: four normals against one difference. -/
def cramer (T : Tab) (a b c d p q : Nat) : List (List Lit) :=
  z4 (mul3 (T.nl b c d) (T.fup a p q)) (negS (mul3 (T.nl a c d) (T.fup b p q)))
    (mul3 (T.nl a b d) (T.fup c p q)) (negS (mul3 (T.nl a b c) (T.fup d p q)))

/-- **Soundness of `cramer`.** -/
theorem cramer_sound {T : Tab} {g : Geo} {ut un uf : Nat → Nat → Nat → Prop} (h : EntOK T g ut un uf)
    (a b c d p q : Nat) (u1 : un b c d) (u2 : un a c d) (u3 : un a b d) (u4 : un a b c)
    (f1 : uf a p q) (f2 : uf b p q) (f3 : uf c p q) (f4 : uf d p q) :
    ∀ cl ∈ cramer T a b c d p q, Holds (rho g) cl := by
  have m := fun {t u r s} (x : Sg3 (rho g) t r) (y : Sg3 (rho g) u s) =>
    Sg3.mul3 (rho_proper g) (rho_gateOK g) x y
  refine z4_sound (m (h.nl _ _ _ u1) (h.fup _ _ _ f1)) (m (h.nl _ _ _ u2) (h.fup _ _ _ f2)).neg
    (m (h.nl _ _ _ u3) (h.fup _ _ _ f3)) (m (h.nl _ _ _ u4) (h.fup _ _ _ f4)).neg ?_
  have := four_dep (g.N a) (g.N b) (g.N c) (g.N d) (g.x p - g.x q)
  simp only [real_inner_comm] at this ⊢
  linarith

/-- The line relation, real form: for `d1, d2` in the plane of the normal `A`, with
`D = det(d1, d2, A)`, the view `A × B` is a combination of `d1`, `d2`. -/
theorem line_id (A B d1 d2 w : ℝ³) (h1 : ⟪A, d1⟫ = 0) (h2 : ⟪A, d2⟫ = 0) :
    det3 d1 d2 A * ⟪w, cross A B⟫ = ⟪A, A⟫ * (⟪B, d1⟫ * ⟪w, d2⟫ - ⟪B, d2⟫ * ⟪w, d1⟫) := by
  have e := (-(⟪w, d2⟫ * ⟪A, B⟫ - ⟪w, A⟫ * ⟪d2, B⟫))
  simp only [det3_expand, inn3, cross_apply_zero, cross_apply_one, cross_apply_two] at h1 h2 ⊢
  linear_combination
    (-((w 0 * d2 0 + w 1 * d2 1 + w 2 * d2 2) * (A 0 * B 0 + A 1 * B 1 + A 2 * B 2) -
      (w 0 * A 0 + w 1 * A 1 + w 2 * A 2) * (d2 0 * B 0 + d2 1 * B 1 + d2 2 * B 2))) * h1 +
    ((w 0 * d1 0 + w 1 * d1 1 + w 2 * d1 2) * (A 0 * B 0 + A 1 * B 1 + A 2 * B 2) -
      (w 0 * A 0 + w 1 * A 1 + w 2 * A 2) * (d1 0 * B 0 + d1 1 * B 1 + d1 2 * B 2)) * h2

/-- Schema `line`: the line view `L` of facets `a`, `b` in terms of two differences `e1`, `e2` of
facet `a` (`addLineRel`).  `kp` is the sign `kap > 0` of the encoder. -/
def lineS (T : Tab) (r L b e1 e2 : Nat) (kp : Bool) : List (List Lit) :=
  z4 (if kp then negS (Tt r L) else Tt r L) (mul3 (T.fup b (EA e1) (EB e1)) (Tt r e2))
    (negS (mul3 (T.fup b (EA e2) (EB e2)) (Tt r e1))) zeroS

/-- **Soundness of `line`**: `σ = ±1` is the side, `vv L = σ (N a × N b)`, and `kp` says the sign of
`σ D`, `D = det(d1, d2, N a)` (a kappa of the facet `a`). -/
theorem line_sound {T : Tab} {g : Geo} {ut un uf : Nat → Nat → Nat → Prop} (h : EntOK T g ut un uf) {r L a b e1 e2 : Nat} {kp : Bool} {σ : ℝ}
    (hσ : σ * σ = 1) (hv : r < 21 → g.vv r ≠ 0) (hL21 : 21 ≤ L) (he1 : e1 < 21) (he2 : e2 < 21) (hL : g.vv L = σ • cross (g.N a) (g.N b))
    (hd1 : g.vv e1 = g.dv e1) (hd2 : g.vv e2 = g.dv e2)
    (h1 : ⟪g.N a, g.dv e1⟫ = 0) (h2 : ⟪g.N a, g.dv e2⟫ = 0) (hA : g.N a ≠ 0)
    (f1 : uf b (EA e1) (EB e1)) (f2 : uf b (EA e2) (EB e2))
    (hk : if kp then 0 < σ * det3 (g.dv e1) (g.dv e2) (g.N a)
      else σ * det3 (g.dv e1) (g.dv e2) (g.N a) < 0) :
    ∀ cl ∈ lineS T r L b e1 e2 kp, Holds (rho g) cl := by
  set D := det3 (g.dv e1) (g.dv e2) (g.N a) with hD
  set w := g.vv r with hw
  have AA : 0 < ⟪g.N a, g.N a⟫ := real_inner_self_pos.mpr hA
  have id0 := line_id (g.N a) (g.N b) (g.dv e1) (g.dv e2) w h1 h2
  have hX : ⟪w, g.vv L⟫ = σ * ⟪w, cross (g.N a) (g.N b)⟫ := by rw [hL, real_inner_smul_right]
  have sX := Sg3_Tt g r L (fun h' h21 => absurd (h' ▸ h21) (not_lt.mpr hL21))
  have m := fun {t u a b} (x : Sg3 (rho g) t a) (y : Sg3 (rho g) u b) =>
    Sg3.mul3 (rho_proper g) (rho_gateOK g) x y
  have sA := m (h.fup _ _ _ f1) (Sg3_Tt g r e2 (fun h' _ => hv (h' ▸ he2)))
  have sB := (m (h.fup _ _ _ f2) (Sg3_Tt g r e1 (fun h' _ => hv (h' ▸ he1)))).neg
  rw [hd2] at sA
  rw [hd1] at sB
  have dv1 : g.x (EA e1) - g.x (EB e1) = g.dv e1 := rfl
  have dv2 : g.x (EA e2) - g.x (EB e2) = g.dv e2 := rfl
  rw [dv1] at sA
  rw [dv2] at sB
  have key : D * (σ * ⟪w, g.vv L⟫) / ⟪g.N a, g.N a⟫ =
      ⟪g.N b, g.dv e1⟫ * ⟪w, g.dv e2⟫ + -(⟪g.N b, g.dv e2⟫ * ⟪w, g.dv e1⟫) := by
    rw [hX, show D * (σ * (σ * ⟪w, cross (g.N a) (g.N b)⟫)) =
      (σ * σ) * (D * ⟪w, cross (g.N a) (g.N b)⟫) by ring, hσ, one_mul, id0]
    field_simp
    ring
  have k2 := key
  rw [real_inner_self_eq_norm_sq, hw] at k2
  cases kp with
  | true =>
    have hp : 0 < σ * D := by simpa using hk
    have c0 : 0 < σ * D / ⟪g.N a, g.N a⟫ := div_pos hp AA
    refine z4_sound (by simpa using (sX.scale c0).neg) sA sB (Sg3_zeroG g) ?_
    linear_combination (-1 : ℝ) * k2
  | false =>
    have hp : σ * D < 0 := by simpa using hk
    have c0 : 0 < -(σ * D) / ⟪g.N a, g.N a⟫ := div_pos (by linarith) AA
    refine z4_sound (by simpa using sX.scale c0) sA sB (Sg3_zeroG g) ?_
    linear_combination (-1 : ℝ) * k2

end Minimality.H16.SAT
