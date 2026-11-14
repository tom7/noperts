module

public import Minimality.Type29SAT.Core

@[expose] public section

/-!
# Formal identities among P atoms as SAT rows

A *P atom* of face `X` is `P(X; d_ab, d_cd) = det3 (N_X) (G d_ab) (G d_cd)` with `d_ab = x_a - x_b`
and `G` a symmetric `3 x 3` matrix.  A *formal P identity* is a list of integer weighted P atoms
whose weighted sum vanishes identically in the points, the normals and `G`.  Then at a real
configuration the weighted values `w_i P_i` add to 0, so they are all `0` or some is `< 0` and some is
`> 0`: a clause on the three valued signs of the atoms (`zn_sound`).

* Real level: `sum_pos_neg`, `sum_neg_or_zero`.
* Sign level (the SAT clauses): `znPos`, `znNeg`, `zn_sound`, in the three valued `S3` of
  `Minimality.H29.SAT` (the layer of the `z4` relation lemma), with `scaleS` for integer weights.
* Semantics: `Cfg`, `pval`, `PTerm`, `FormalP`, and `formalP_sound` (the whole chain).
* Worked example `r646`: six literals, one face, proved by `ring`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality.H29.SAT

namespace Minimality.SATFormal

/-! ### Real level -/

/-- Reals that add to 0 and are all `>= 0` are all `0`. -/
theorem all_zero_of_sum_nonneg {n : ℕ} (r : Fin n → ℝ) (hs : ∑ i, r i = 0) (h : ∀ i, 0 ≤ r i) :
    ∀ i, r i = 0 := fun i =>
  (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h j)).mp hs i (Finset.mem_univ i)

/-- Reals that add to 0 with one `> 0` have one `< 0`. -/
theorem exists_neg_of_pos {n : ℕ} (r : Fin n → ℝ) (hs : ∑ i, r i = 0) {k : Fin n} (hk : 0 < r k) :
    ∃ i, r i < 0 := by
  by_contra hn
  push Not at hn
  have := all_zero_of_sum_nonneg r hs hn k
  linarith

/-- **Circuit form of the clause**: weighted values that add to 0 have a negative one, or all vanish. -/
theorem sum_neg_or_zero {n : ℕ} (r : Fin n → ℝ) (hs : ∑ i, r i = 0) :
    (∃ i, r i < 0) ∨ ∀ i, r i = 0 := by
  by_cases hn : ∃ i, r i < 0
  · exact Or.inl hn
  · push Not at hn
    exact Or.inr (all_zero_of_sum_nonneg r hs hn)

/-! ### Sign level -/

/-- Integer weight on a three valued sign. -/
def scaleS (w : ℤ) (t : S3) : S3 := if 0 < w then t else if w < 0 then negS t else zeroS

/-- The weighted real has the weighted sign. -/
theorem Sg3_scaleS {ρ : V → Bool} (hP : Proper ρ) (w : ℤ) {t : S3} {p : ℝ} (h : Sg3 ρ t p) :
    Sg3 ρ (scaleS w t) ((w : ℝ) * p) := by
  unfold scaleS
  by_cases h1 : 0 < w
  · simp only [h1, ↓reduceIte]
    exact Sg3.scale (by exact_mod_cast h1) h
  · simp only [h1, ↓reduceIte]
    by_cases h2 : w < 0
    · simp only [h2, ↓reduceIte]
      have := (Sg3.neg h).scale (c := (-(w : ℝ))) (by have : (w : ℝ) < 0 := by exact_mod_cast h2
                                                      linarith)
      simpa using this
    · simp only [h2, ↓reduceIte]
      have : w = 0 := by omega
      subst this
      simpa using Sg3_zero hP

/-- Clause "if term `k` is positive, some other term is negative". -/
def znPos {n : ℕ} (t : Fin n → S3) (k : Fin n) : List Lit :=
  List.ofFn fun i => if i = k then (t i).1.neg else (t i).2

/-- Clause "if term `k` is negative, some other term is positive". -/
def znNeg {n : ℕ} (t : Fin n → S3) (k : Fin n) : List Lit :=
  List.ofFn fun i => if i = k then (t i).2.neg else (t i).1

/-- **The n-ary relation lemma** (`z4_sound` for any number of terms): three valued terms whose
reals add to 0 satisfy every clause `znPos`, `znNeg`. -/
theorem zn_sound {ρ : V → Bool} {n : ℕ} (t : Fin n → S3) (r : Fin n → ℝ)
    (h : ∀ i, Sg3 ρ (t i) (r i)) (hs : ∑ i, r i = 0) (k : Fin n) :
    Holds ρ (znPos t k) ∧ Holds ρ (znNeg t k) := by
  constructor
  · by_contra hn
    have hf : ∀ i, evalL ρ (if i = k then (t i).1.neg else (t i).2) = false := by
      intro i
      by_contra e
      have e' : evalL ρ (if i = k then (t i).1.neg else (t i).2) = true := by simpa using e
      exact hn ⟨_, by simp [znPos], e'⟩
    have hk : 0 < r k := by
      have := hf k
      simp [evalL_neg] at this
      exact (h k).1.mp this
    have hr : ∀ i, 0 ≤ r i := by
      intro i
      by_cases hi : i = k
      · subst hi; exact hk.le
      · have := hf i
        simp only [hi, ite_false] at this
        exact not_lt.mp fun h' => by simpa [this] using (h i).2.mpr h'
    have := all_zero_of_sum_nonneg r hs hr k
    linarith
  · by_contra hn
    have hf : ∀ i, evalL ρ (if i = k then (t i).2.neg else (t i).1) = false := by
      intro i
      by_contra e
      have e' : evalL ρ (if i = k then (t i).2.neg else (t i).1) = true := by simpa using e
      exact hn ⟨_, by simp [znNeg], e'⟩
    have hk : r k < 0 := by
      have := hf k
      simp [evalL_neg] at this
      exact (h k).2.mp this
    have hr : ∀ i, r i ≤ 0 := by
      intro i
      by_cases hi : i = k
      · subst hi; exact hk.le
      · have := hf i
        simp only [hi, ite_false] at this
        exact not_lt.mp fun h' => by simpa [this] using (h i).1.mpr h'
    have := all_zero_of_sum_nonneg (fun i => -r i) (by simp [Finset.sum_neg_distrib, hs])
      (fun i => by linarith [hr i]) k
    linarith

/-! ### Semantics of P atoms -/

/-- The real data of a P row: points, normals, a `3 x 3` matrix `G` (symmetric in the application). -/
structure Cfg where
  x : ℕ → ℝ³
  N : ℕ → ℝ³
  G : Matrix (Fin 3) (Fin 3) ℝ

/-- `G v`. -/
noncomputable def Gv (G : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) : ℝ³ :=
  !₂[G 0 0 * v 0 + G 0 1 * v 1 + G 0 2 * v 2, G 1 0 * v 0 + G 1 1 * v 1 + G 1 2 * v 2,
    G 2 0 * v 0 + G 2 1 * v 1 + G 2 2 * v 2]

/-- The difference `x_a - x_b`. -/
def Cfg.d (c : Cfg) (a b : ℕ) : ℝ³ := c.x a - c.x b

/-- The normal of a P atom: a stored facet normal `N_X`, or the canonical normal
`d_pq x d_rs` of two edges of the face (for rows that couple faces: `N_X` is a positive multiple of it, see `pval_scale`). -/
inductive Face where
  | ofN (X : ℕ)
  | ofEdges (p q r s : ℕ)

/-- The normal vector of a face. -/
noncomputable def Cfg.nrm (c : Cfg) : Face → ℝ³
  | .ofN X => c.N X
  | .ofEdges p q r s => Minimality.cross (c.d p q) (c.d r s)

/-- One weighted P atom: `w * P(face; d_{ab}, d_{cd})`. -/
structure PTerm where
  w : ℤ
  face : Face
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

/-- **The P atom** `det3 (N_X) (G d_ab) (G d_cd)`. -/
noncomputable def pval (c : Cfg) (f : Face) (a b p q : ℕ) : ℝ :=
  Minimality.det3 (c.nrm f) (Gv c.G (c.d a b)) (Gv c.G (c.d p q))

/-- The weighted value of a term. -/
noncomputable def PTerm.val (c : Cfg) (t : PTerm) : ℝ := (t.w : ℝ) * pval c t.face t.a t.b t.c t.d

/-- **A formal P identity**: the weighted atoms add to 0 for every configuration with symmetric `G`
(the symmetry is only needed by rows that couple faces). -/
def FormalP (ts : List PTerm) : Prop :=
  ∀ c : Cfg, c.G.IsSymm → (ts.map (PTerm.val c)).sum = 0

/-- The positive multiple of the canonical normal: the P atom of `N_X` is that multiple of the canonical atom. -/
theorem pval_scale (c : Cfg) (X p q r s a b e f : ℕ) (lam : ℝ)
    (hN : c.N X = lam • Minimality.cross (c.d p q) (c.d r s)) :
    pval c (.ofN X) a b e f = lam * pval c (.ofEdges p q r s) a b e f := by
  unfold pval
  simp only [Cfg.nrm]
  rw [hN]
  simp only [Minimality.det3_expand]
  simp [PiLp.smul_apply]
  ring

theorem sum_get {α : Type*} (l : List α) (f : α → ℝ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l _ => simp [Fin.sum_univ_succ]

/-- **Soundness, real level**: a formal identity gives the circuit clause at every configuration. -/
theorem formalP_real (ts : List PTerm) (hF : FormalP ts) (c : Cfg) (hc : c.G.IsSymm) :
    (∃ i : Fin ts.length, (ts.get i).val c < 0) ∨ ∀ i : Fin ts.length, (ts.get i).val c = 0 := by
  apply sum_neg_or_zero
  have := hF c hc
  rw [sum_get]; exact this

/-- **Soundness, sign level (the SAT row).**  A formal P identity: if the three valued sign `S i` of
the `i`-th atom (without its weight) is the sign of `pval` of that atom, the clauses `znPos`/`znNeg`
of the weighted signs hold. -/
theorem formalP_sound {ρ : V → Bool} (hP : Proper ρ) (ts : List PTerm) (hF : FormalP ts) (c : Cfg)
    (hc : c.G.IsSymm) (S : Fin ts.length → S3)
    (hS : ∀ i, Sg3 ρ (S i) (pval c (ts.get i).face (ts.get i).a (ts.get i).b (ts.get i).c (ts.get i).d))
    (k : Fin ts.length) :
    Holds ρ (znPos (fun i => scaleS (ts.get i).w (S i)) k) ∧
    Holds ρ (znNeg (fun i => scaleS (ts.get i).w (S i)) k) := by
  refine zn_sound _ (fun i => (ts.get i).val c) (fun i => Sg3_scaleS hP _ (hS i)) ?_ k
  have := hF c hc
  rw [sum_get]; exact this

/-! ### Coordinates and the example -/

/-- Coordinates: the unfolding simp set used by the `ring` rows. -/
theorem pval_coord (c : Cfg) (f : Face) (a b p q : ℕ) :
    pval c f a b p q = Minimality.det3 (c.nrm f) (Gv c.G (c.x a - c.x b)) (Gv c.G (c.x p - c.x q)) := rfl

/-- **Worked example `r646`** (one face `X`, six atoms): in the notation `d_ab x d_cd` for
`P(X; d_ab, d_cd)`,
`-d12 x d14 - d13 x d56 + d15 x d16 + d15 x d23 + d16 x d34 + d26 x d45 = 0`. -/
def r646 (X : ℕ) : List PTerm :=
  [⟨-1, .ofN X, 1, 2, 1, 4⟩, ⟨-1, .ofN X, 1, 3, 5, 6⟩, ⟨1, .ofN X, 1, 5, 1, 6⟩,
   ⟨1, .ofN X, 1, 5, 2, 3⟩, ⟨1, .ofN X, 1, 6, 3, 4⟩, ⟨1, .ofN X, 2, 6, 4, 5⟩]

/-- Checked by `ring`. -/
theorem r646_formal (X : ℕ) : FormalP (r646 X) := by
  intro c _
  simp only [r646, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, PTerm.val, pval,
    Cfg.nrm, Cfg.d, Minimality.det3_expand, Gv, PiLp.sub_apply, Int.cast_neg, Int.cast_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Symmetric `G` is used by coupled rows**: the pair symmetry `R(e1,e2,a,b) = R(a,b,e1,e2)` of the
Gram 2-form: the canonical P atom of face `(p,q,r,s)` at edges `(a,b), (e,f)` is that of face
`(a,b,e,f)` at the edges `(p,q), (r,s)`.  (`FormalP` rows are proved the same way: `hc` rewrites
`G 1 0, G 2 0, G 2 1`, then `ring`.) -/
theorem pval_pair_sym (c : Cfg) (hc : c.G.IsSymm) (p q r s a b e f : ℕ) :
    pval c (.ofEdges p q r s) a b e f = pval c (.ofEdges a b e f) p q r s := by
  have h10 : c.G 1 0 = c.G 0 1 := by simpa using congrFun (congrFun hc.eq 0) 1
  have h20 : c.G 2 0 = c.G 0 2 := by simpa using congrFun (congrFun hc.eq 0) 2
  have h21 : c.G 2 1 = c.G 1 2 := by simpa using congrFun (congrFun hc.eq 1) 2
  simp only [pval, Cfg.nrm, Cfg.d, Minimality.det3_expand, Gv, Minimality.cross, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, h10, h20, h21]
  ring

/-- **The r646 clause** about the six P atoms of one face: for each `k`, if the weighted atom `k` is
positive some other weighted atom is negative, and if negative some other is positive. -/
theorem r646_sound {ρ : V → Bool} (hP : Proper ρ) (X : ℕ) (c : Cfg) (hc : c.G.IsSymm)
    (S : Fin (r646 X).length → S3)
    (hS : ∀ i, Sg3 ρ (S i) (pval c ((r646 X).get i).face ((r646 X).get i).a ((r646 X).get i).b
      ((r646 X).get i).c ((r646 X).get i).d)) (k : Fin (r646 X).length) :
    Holds ρ (znPos (fun i => scaleS ((r646 X).get i).w (S i)) k) ∧
    Holds ρ (znNeg (fun i => scaleS ((r646 X).get i).w (S i)) k) :=
  formalP_sound hP _ (r646_formal X) c hc S hS k

end Minimality.SATFormal
