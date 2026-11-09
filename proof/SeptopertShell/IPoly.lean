module

public import SeptopertShell.Poly

/-!
# Integer polynomials with a merge product

Sparse polynomials with integer coefficients, kept sorted by monomial (`monoLt`): the sum `madd` merges two sorted
lists linearly, and the product `imul` accumulates the shifted copies `a * q` of the smaller factor's terms by `madd`
(a shifted sorted list stays sorted). No sorting of a long raw list is needed. Soundness (`eval`) does not use the
order; sortedness only keeps the lists short (equal monomials merge, zero coefficients vanish).
-/

@[expose] public section

namespace SeptopertShell

/-- Integer sparse polynomials. -/
abbrev IPoly := List (Mono × ℤ)

namespace IPoly

def toPoly (p : IPoly) : Poly := p.map fun t => (t.1, (t.2 : ℚ))

/-- Real value. -/
def eval (p : IPoly) (x : Fin 3 → ℝ) : ℝ := (toPoly p).eval x

@[simp] theorem eval_nil (x : Fin 3 → ℝ) : eval [] x = 0 := by simp [eval, toPoly]

theorem eval_cons (t : Mono × ℤ) (p : IPoly) (x : Fin 3 → ℝ) :
    eval (t :: p) x = (t.2 : ℝ) * x 0 ^ t.1.1 * x 1 ^ t.1.2.1 * x 2 ^ t.1.2.2 + eval p x := by
  simp [eval, toPoly, Poly.termEval]

/-- Strict lexicographic order on monomials. -/
def monoLt (a b : Mono) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) &&
    (decide (a.2.1 < b.2.1) || (decide (a.2.1 = b.2.1) && decide (a.2.2 < b.2.2))))

/-- Merge of two sorted lists, adding the coefficients of equal monomials and dropping zeros. -/
def madd : IPoly → IPoly → IPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q =>
    if a.1 = b.1 then
      (if a.2 + b.2 = 0 then madd p q else (a.1, a.2 + b.2) :: madd p q)
    else if monoLt a.1 b.1 then a :: madd p (b :: q)
    else b :: madd (a :: p) q
termination_by p q => p.length + q.length

theorem eval_madd (p q : IPoly) (x : Fin 3 → ℝ) : eval (madd p q) x = eval p x + eval q x := by
  induction p, q using madd.induct with
  | case1 q => simp [madd]
  | case2 a p => simp [madd]
  | case3 a p b q h1 h2 ih =>
    rw [madd]; simp only [h1, ite_true, h2]
    have hc : (a.2 : ℝ) + b.2 = 0 := by exact_mod_cast h2
    rw [ih]; simp only [eval_cons]
    rw [← h1]
    linear_combination (-(x 0 ^ a.1.1 * x 1 ^ a.1.2.1 * x 2 ^ a.1.2.2)) * hc
  | case4 a p b q h1 h2 ih =>
    rw [madd]; simp only [h1, ite_true, h2, ite_false]
    simp only [eval_cons] at ih ⊢
    rw [ih, ← h1]; push_cast; ring
  | case5 a p b q h1 h2 ih =>
    rw [madd]; simp only [h1, ite_false, h2, ite_true]
    simp only [eval_cons] at ih ⊢
    rw [ih]; ring
  | case6 a p b q h1 h2 ih =>
    rw [madd]; simp only [h1, ite_false]
    rw [ite_eq_right (by simpa using h2)]
    simp only [eval_cons] at ih ⊢
    rw [ih]; ring

def neg (p : IPoly) : IPoly := p.map fun t => (t.1, -t.2)

theorem eval_neg (p : IPoly) (x : Fin 3 → ℝ) : eval (neg p) x = - eval p x := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

def sub (p q : IPoly) : IPoly := madd p (neg q)

theorem eval_sub (p q : IPoly) (x : Fin 3 → ℝ) : eval (sub p q) x = eval p x - eval q x := by
  rw [sub, eval_madd, eval_neg]; ring

/-- Multiply every term of `q` by the term `a`. -/
def mulTerm (a : Mono × ℤ) (q : IPoly) : IPoly := q.map fun b => (Poly.monoMul a.1 b.1, a.2 * b.2)

theorem eval_mulTerm (a : Mono × ℤ) (q : IPoly) (x : Fin 3 → ℝ) :
    eval (mulTerm a q) x = ((a.2 : ℝ) * x 0 ^ a.1.1 * x 1 ^ a.1.2.1 * x 2 ^ a.1.2.2) * eval q x := by
  induction q with
  | nil => simp [mulTerm]
  | cons b q ih =>
    simp only [mulTerm, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    simp only [Poly.monoMul]
    push_cast
    simp only [pow_add]
    ring

/-- `acc + p * q`. -/
def mulAcc (q : IPoly) : IPoly → IPoly → IPoly
  | acc, [] => acc
  | acc, a :: p => mulAcc q (madd acc (mulTerm a q)) p

theorem eval_mulAcc (q p acc : IPoly) (x : Fin 3 → ℝ) :
    eval (mulAcc q acc p) x = eval acc x + eval p x * eval q x := by
  induction p generalizing acc with
  | nil => simp [mulAcc]
  | cons a p ih =>
    rw [mulAcc, ih, eval_madd, eval_mulTerm, eval_cons]; ring

/-- Product (the shorter factor is the outer loop). -/
def mul (p q : IPoly) : IPoly := if p.length ≤ q.length then mulAcc q [] p else mulAcc p [] q

theorem eval_mul (p q : IPoly) (x : Fin 3 → ℝ) : eval (mul p q) x = eval p x * eval q x := by
  unfold mul
  split_ifs
  · rw [eval_mulAcc]; simp
  · rw [eval_mulAcc]; simp; ring

/-- Scale by an integer. -/
def scale (c : ℤ) (p : IPoly) : IPoly := if c = 0 then [] else p.map fun t => (t.1, c * t.2)

theorem eval_scale (c : ℤ) (p : IPoly) (x : Fin 3 → ℝ) : eval (scale c p) x = c * eval p x := by
  unfold scale
  split_ifs with h
  · simp [h]
  · induction p with
    | nil => simp
    | cons t p ih =>
      simp only [List.map_cons, eval_cons] at ih ⊢
      rw [ih]; push_cast; ring

def const (c : ℤ) : IPoly := if c = 0 then [] else [((0, 0, 0), c)]

theorem eval_const (c : ℤ) (x : Fin 3 → ℝ) : eval (const c) x = c := by
  unfold const; split_ifs with h
  · simp [h]
  · simp [eval_cons]

end IPoly

/-- Vectors of integer polynomials. -/
abbrev IV := Fin 3 → IPoly

namespace IV

def add (u w : IV) : IV := fun i => IPoly.madd (u i) (w i)
def smul (p : IPoly) (u : IV) : IV := fun i => IPoly.mul p (u i)
def cscale (c : ℤ) (u : IV) : IV := fun i => IPoly.scale c (u i)
def sub (u w : IV) : IV := fun i => IPoly.sub (u i) (w i)
def cross (u w : IV) : IV :=
  ![IPoly.sub (IPoly.mul (u 1) (w 2)) (IPoly.mul (u 2) (w 1)),
    IPoly.sub (IPoly.mul (u 2) (w 0)) (IPoly.mul (u 0) (w 2)),
    IPoly.sub (IPoly.mul (u 0) (w 1)) (IPoly.mul (u 1) (w 0))]
def dot (u w : IV) : IPoly :=
  IPoly.madd (IPoly.madd (IPoly.mul (u 0) (w 0)) (IPoly.mul (u 1) (w 1))) (IPoly.mul (u 2) (w 2))

variable (x : Fin 3 → ℝ)

theorem eval_add (u w : IV) (i : Fin 3) : ((add u w) i).eval x = (u i).eval x + (w i).eval x := by
  simp [add, IPoly.eval_madd]
theorem eval_sub (u w : IV) (i : Fin 3) : ((sub u w) i).eval x = (u i).eval x - (w i).eval x := by
  simp [sub, IPoly.eval_sub]
theorem eval_smul (p : IPoly) (u : IV) (i : Fin 3) :
    ((smul p u) i).eval x = p.eval x * (u i).eval x := by
  simp [smul, IPoly.eval_mul]
theorem eval_cscale (c : ℤ) (u : IV) (i : Fin 3) :
    ((cscale c u) i).eval x = c * (u i).eval x := by
  simp [cscale, IPoly.eval_scale]
theorem eval_cross0 (u w : IV) :
    ((cross u w) 0).eval x = (u 1).eval x * (w 2).eval x - (u 2).eval x * (w 1).eval x := by
  simp [cross, IPoly.eval_sub, IPoly.eval_mul]
theorem eval_cross1 (u w : IV) :
    ((cross u w) 1).eval x = (u 2).eval x * (w 0).eval x - (u 0).eval x * (w 2).eval x := by
  simp [cross, IPoly.eval_sub, IPoly.eval_mul]
theorem eval_cross2 (u w : IV) :
    ((cross u w) 2).eval x = (u 0).eval x * (w 1).eval x - (u 1).eval x * (w 0).eval x := by
  simp [cross, IPoly.eval_sub, IPoly.eval_mul]
theorem eval_dot (u w : IV) :
    (dot u w).eval x = (u 0).eval x * (w 0).eval x + (u 1).eval x * (w 1).eval x +
      (u 2).eval x * (w 2).eval x := by
  simp [dot, IPoly.eval_madd, IPoly.eval_mul]

end IV

end SeptopertShell

end
