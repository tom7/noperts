module

public import SeptopertShell.IPoly

/-!
# Bernstein lower bounds, and the centred split-tree checker

`Bern.bernOk p r m` certifies `m ≤ p` on the centred box `|h i| ≤ r i`: substitute `h = r (2t - 1)` (three
`shiftVar`s and a scaling), clear denominators, and convert to the tensor Bernstein basis
`t^k (1 - t)^(n - k)` one variable at a time (`bern1`, integer coefficients, from `t^e = t^e (t + (1 - t))^(n - e)`).
If every coefficient of `p - m` in that basis is `≥ 0`, then `p - m ≥ 0` on the box, since the basis functions are
nonnegative on `[0, 1]`. The certificate supplies `m > 0` (relative to the constant term in `checkTreeC`), so no completeness of the
coefficient grid is needed.

`checkTreeC` (centred subdivision certificates, moved here from `Poly`) accepts a `bern m` leaf where the centred
form bound would need a deep tree.
-/

@[expose] public section

namespace SeptopertShell

namespace Bern

open SeptopertShell.Poly (monoGet monoSet)

/-! ### Evaluation against a monomial evaluator -/

/-- `Σ c f(e)` over the terms `(e, c)`. -/
def evalWith (f : Mono → ℝ) (p : IPoly) : ℝ := (p.map fun t => (t.2 : ℝ) * f t.1).sum

@[simp] theorem evalWith_nil (f : Mono → ℝ) : evalWith f [] = 0 := by simp [evalWith]

@[simp] theorem evalWith_cons (f : Mono → ℝ) (t : Mono × ℤ) (p : IPoly) :
    evalWith f (t :: p) = (t.2 : ℝ) * f t.1 + evalWith f p := by simp [evalWith]

theorem evalWith_append (f : Mono → ℝ) (p q : IPoly) : evalWith f (p ++ q) = evalWith f p + evalWith f q := by
  simp [evalWith]

/-- Merge adjacent terms with equal monomials. -/
def mergeAdj : IPoly → IPoly
  | [] => []
  | [t] => [t]
  | t :: u :: rest =>
    if t.1 = u.1 then mergeAdj ((t.1, t.2 + u.2) :: rest) else t :: mergeAdj (u :: rest)
termination_by l => l.length

theorem evalWith_mergeAdj (f : Mono → ℝ) (l : IPoly) : evalWith f (mergeAdj l) = evalWith f l := by
  induction l using mergeAdj.induct with
  | case1 => simp [mergeAdj]
  | case2 t => simp [mergeAdj]
  | case3 t u rest h ih =>
    rw [mergeAdj, ite_eq_left h, ih]
    simp only [evalWith_cons]
    rw [← h]; push_cast; ring
  | case4 t u rest h ih =>
    rw [mergeAdj, ite_eq_right h]
    simp only [evalWith_cons, ih]

/-- Sort by monomial, merge equal monomials, drop zero coefficients. -/
def norm (p : IPoly) : IPoly :=
  (mergeAdj (p.mergeSort fun s t => Poly.monoLe s.1 t.1)).filter fun t => decide (t.2 ≠ 0)

theorem evalWith_norm (f : Mono → ℝ) (p : IPoly) : evalWith f (norm p) = evalWith f p := by
  have hz : ∀ l : IPoly, evalWith f (l.filter fun t => decide (t.2 ≠ 0)) = evalWith f l := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simp [h]), ih]; simp [h]
      · rw [List.filter_cons_of_pos (by simp [h])]; simp only [evalWith_cons, ih]
  rw [norm, hz, evalWith_mergeAdj]
  unfold evalWith
  exact ((List.mergeSort_perm p _).map _).sum_eq

/-! ### The mixed basis -/

/-- One variable's factor: `t^e`, or the Bernstein-type `t^e (1 - t)^(n - e)` once the variable is converted. -/
def fac (conv : Bool) (n e : ℕ) (t : ℝ) : ℝ := if conv then t ^ e * (1 - t) ^ (n - e) else t ^ e

/-- The monomial evaluator with the variables in `S` converted, degrees `n`. -/
def mono3 (S : Fin 3 → Bool) (n : Fin 3 → ℕ) (t : Fin 3 → ℝ) (e : Mono) : ℝ :=
  ∏ d : Fin 3, fac (S d) (n d) (monoGet e d) (t d)

theorem monoGet_monoSet_self (e : Mono) (d : Fin 3) (l : ℕ) : monoGet (monoSet e d l) d = l := by
  fin_cases d <;> simp [monoGet, monoSet]

theorem monoGet_monoSet_ne (e : Mono) {d d' : Fin 3} (h : d' ≠ d) (l : ℕ) :
    monoGet (monoSet e d l) d' = monoGet e d' := by
  fin_cases d <;> fin_cases d' <;> simp_all [monoGet, monoSet]

theorem evalWith_none (n : Fin 3 → ℕ) (p : IPoly) (t : Fin 3 → ℝ) :
    evalWith (mono3 (fun _ => false) n t) p = p.eval t := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [evalWith_cons, ih, IPoly.eval_cons]
    simp [mono3, fac, Fin.prod_univ_three, monoGet]
    ring

/-- One term converted in variable `d` (degree `n`): `t^e = Σ_l C(n-e, l) t^(e+l) (1-t)^(n-e-l)`. -/
def expandB (t : Mono × ℤ) (d : Fin 3) (n : ℕ) : IPoly :=
  (List.range (n - monoGet t.1 d + 1)).map fun l =>
    (monoSet t.1 d (monoGet t.1 d + l), t.2 * ((n - monoGet t.1 d).choose l : ℤ))

/-- Convert variable `d` (degree `n`) of every term. -/
def bern1 (p : IPoly) (d : Fin 3) (n : ℕ) : IPoly := norm (p.flatMap fun t => expandB t d n)

/-- All exponents of variable `d` are at most `n`. -/
def degOk (p : IPoly) (d : Fin 3) (n : ℕ) : Bool := p.all fun t => decide (monoGet t.1 d ≤ n)

theorem pow_eq_bern (x : ℝ) {e n : ℕ} (_h : e ≤ n) :
    x ^ e = ∑ l ∈ Finset.range (n - e + 1), ((n - e).choose l : ℝ) * (x ^ (e + l) * (1 - x) ^ (n - (e + l))) := by
  have h1 : (x + (1 - x)) ^ (n - e) = 1 := by simp
  calc x ^ e = x ^ e * (x + (1 - x)) ^ (n - e) := by rw [h1, mul_one]
    _ = _ := by
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l ≤ n - e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have : n - (e + l) = n - e - l := by omega
      rw [this, pow_add]; ring

theorem prod_split (g : Fin 3 → ℝ) (d : Fin 3) : ∏ i, g i = g d * ∏ i ∈ Finset.univ.erase d, g i :=
  (Finset.mul_prod_erase _ g (Finset.mem_univ d)).symm

theorem evalWith_expandB (S : Fin 3 → Bool) (N : Fin 3 → ℕ) (t : Fin 3 → ℝ) (a : Mono × ℤ) (d : Fin 3)
    (hS : S d = false) (hd : monoGet a.1 d ≤ N d) :
    evalWith (mono3 (Function.update S d true) N t) (expandB a d (N d)) = (a.2 : ℝ) * mono3 S N t a.1 := by
  unfold expandB evalWith
  rw [List.map_map, Poly.sum_range_list]
  have hrest : ∀ l, ∏ i ∈ Finset.univ.erase d,
      fac (Function.update S d true i) (N i) (monoGet (monoSet a.1 d (monoGet a.1 d + l)) i) (t i) =
      ∏ i ∈ Finset.univ.erase d, fac (S i) (N i) (monoGet a.1 i) (t i) := by
    intro l
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ≠ d := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hi', monoGet_monoSet_ne _ hi']
  simp only [Function.comp_def, mono3]
  simp_rw [prod_split _ d, hrest]
  simp only [Function.update_self, monoGet_monoSet_self, hS, fac, ite_true, Bool.false_eq_true, ite_false]
  rw [pow_eq_bern (t d) hd, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast; ring

theorem evalWith_bern1 (S : Fin 3 → Bool) (N : Fin 3 → ℕ) (t : Fin 3 → ℝ) (p : IPoly) (d : Fin 3)
    (hS : S d = false) (hdeg : degOk p d (N d) = true) :
    evalWith (mono3 (Function.update S d true) N t) (bern1 p d (N d)) = evalWith (mono3 S N t) p := by
  rw [bern1, evalWith_norm]
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [degOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hdeg
    rw [List.flatMap_cons, evalWith_append, evalWith_expandB S N t a d hS hdeg.1, ih (by simpa [degOk] using hdeg.2),
      evalWith_cons]

theorem evalWith_nonneg (N : Fin 3 → ℕ) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (p : IPoly)
    (hp : p.all (fun a => decide (0 ≤ a.2)) = true) : 0 ≤ evalWith (mono3 (fun _ => true) N t) p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [evalWith_cons]
    refine add_nonneg (mul_nonneg (by exact_mod_cast hp.1) ?_) (ih hp.2)
    unfold mono3
    refine Finset.prod_nonneg fun i _ => ?_
    simp only [fac, ite_true]
    exact mul_nonneg (pow_nonneg (ht i).1 _) (pow_nonneg (by linarith [(ht i).2]) _)

/-! ### The bound -/

/-- `p(c ∘ t)`: multiply each coefficient by `c₀^i c₁^j c₂^k`. -/
def scale (p : Poly) (c : Fin 3 → ℚ) : Poly :=
  p.map fun a => (a.1, a.2 * (c 0 ^ a.1.1 * c 1 ^ a.1.2.1 * c 2 ^ a.1.2.2))

theorem eval_scale (p : Poly) (c : Fin 3 → ℚ) (t : Fin 3 → ℝ) :
    (scale p c).eval t = p.eval fun i => (c i : ℝ) * t i := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    simp only [scale, List.map_cons, Poly.eval_cons] at ih ⊢
    rw [ih]
    simp only [Poly.termEval, mul_pow]
    push_cast; ring

/-- Largest exponent of variable `d`. -/
def maxDeg (p : IPoly) (d : Fin 3) : ℕ := p.foldl (fun a t => max a (monoGet t.1 d)) 0

/-- The scaled, shifted and cleared polynomial of `p - m` in `t ∈ [0, 1]³` (`h = r (2t - 1)`), and its common
denominator. -/
def prep (p : Poly) (r : Fin 3 → ℚ) (m : ℚ) : Poly :=
  let q1 := Poly.shiftVar (Poly.shiftVar (Poly.shiftVar (p ++ [((0, 0, 0), -m)]) 0 (-r 0)) 1 (-r 1)) 2 (-r 2)
  scale q1 fun i => 2 * r i

/-- The constant coefficient (the value at the box centre, in centred coordinates). The `bern m` leaf certifies
`p ≥ m · const0 p`, which is invariant under scaling `p` by a positive constant (the certifier works with a
multiple of the Lean polynomial). -/
def const0 (p : Poly) : ℚ := (p.map fun t => if t.1 = (0, 0, 0) then t.2 else 0).sum

/-- Bernstein certificate that `m ≤ p` on `|h i| ≤ r i`. -/
def bernOk (p : Poly) (r : Fin 3 → ℚ) (m : ℚ) : Bool :=
  let q := prep p r m
  let D := lcmList (polyDens q)
  let z := Poly.clear D q
  let N : Fin 3 → ℕ := fun d => maxDeg z d
  let z0 := bern1 z 0 (N 0)
  let z1 := bern1 z0 1 (N 1)
  let z2 := bern1 z1 2 (N 2)
  decide (0 < D) && Poly.clearOk D q && degOk z 0 (N 0) && degOk z0 1 (N 1) && degOk z1 2 (N 2) &&
    z2.all fun a => decide (0 ≤ a.2)

theorem eval_prep (p : Poly) (r : Fin 3 → ℚ) (m : ℚ) (t : Fin 3 → ℝ) :
    (prep p r m).eval t = p.eval (fun i => 2 * (r i : ℝ) * t i - r i) - m := by
  simp only [prep]
  rw [eval_scale, Poly.eval_shiftVar, Poly.eval_shiftVar, Poly.eval_shiftVar, Poly.eval_append]
  simp only [Poly.eval_cons, Poly.eval_nil, Poly.termEval]
  push_cast
  have : (fun i => 2 * (r i : ℝ) * t i - r i) =
      Function.update (Function.update (Function.update (fun i => (2 * (r i : ℝ)) * t i) 2
        ((2 * (r 2 : ℝ)) * t 2 + -(r 2 : ℝ))) 1
        (Function.update (fun i => (2 * (r i : ℝ)) * t i) 2 ((2 * (r 2 : ℝ)) * t 2 + -(r 2 : ℝ)) 1 + -(r 1 : ℝ))) 0
        (Function.update (Function.update (fun i => (2 * (r i : ℝ)) * t i) 2
          ((2 * (r 2 : ℝ)) * t 2 + -(r 2 : ℝ))) 1
          (Function.update (fun i => (2 * (r i : ℝ)) * t i) 2 ((2 * (r 2 : ℝ)) * t 2 + -(r 2 : ℝ)) 1 + -(r 1 : ℝ)) 0
          + -(r 0 : ℝ)) := by
    funext i; fin_cases i <;> simp <;> ring
  rw [← this]; ring

theorem le_of_bernOk {p : Poly} {r : Fin 3 → ℚ} {m : ℚ} (h : bernOk p r m = true) (hr : ∀ i, 0 < r i)
    {x : Fin 3 → ℝ} (hx : ∀ i, |x i| ≤ r i) : (m : ℝ) ≤ p.eval x := by
  simp only [bernOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hD, hc⟩, h0⟩, h1⟩, h2⟩, hpos⟩ := h
  set q := prep p r m
  set D := lcmList (polyDens q)
  set z := Poly.clear D q
  set N : Fin 3 → ℕ := fun d => maxDeg z d
  have hrR : ∀ i, (0 : ℝ) < r i := fun i => by exact_mod_cast hr i
  let t : Fin 3 → ℝ := fun i => (x i + r i) / (2 * r i)
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := fun i => by
    have := abs_le.mp (hx i)
    have h2r : (0 : ℝ) < 2 * r i := by linarith [hrR i]
    constructor
    · exact div_nonneg (by linarith) h2r.le
    · rw [div_le_one h2r]; linarith
  have hxt : (fun i => 2 * (r i : ℝ) * t i - r i) = x := by
    funext i; simp only [t]; field_simp [(hrR i).ne']; ring
  -- the chain of conversions
  let S0 : Fin 3 → Bool := fun _ => false
  have e0 : evalWith (mono3 (Function.update S0 0 true) N t) (bern1 z 0 (N 0)) = evalWith (mono3 S0 N t) z :=
    evalWith_bern1 S0 N t z 0 rfl h0
  have e1 := evalWith_bern1 (Function.update S0 0 true) N t (bern1 z 0 (N 0)) 1 (by simp [S0]) h1
  have e2 := evalWith_bern1 (Function.update (Function.update S0 0 true) 1 true) N t
    (bern1 (bern1 z 0 (N 0)) 1 (N 1)) 2 (by simp [S0]) h2
  have hS : Function.update (Function.update (Function.update S0 0 true) 1 true) 2 true = fun _ => true := by
    funext i; fin_cases i <;> simp [S0]
  rw [hS] at e2
  have hnn := evalWith_nonneg N t ht _ hpos
  rw [e2, e1, e0, evalWith_none, Poly.eval_clear hc, eval_prep, hxt] at hnn
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [hnn, hDR]

end Bern

/-! ### Centred subdivision certificates -/

/-- Subdivision certificate checker in centred form: `p` is the polynomial in the local coordinates
`h = x - (lo + hi)/2` of the box `[lo, hi]`. A `leaf` uses the centred form bound, a `bern m` leaf the Bernstein
bound with the claimed relative lower bound `m > 0` (`p ≥ m · const0 p`). -/
def checkTreeC (p : Poly) (lo hi : Fin 3 → ℚ) : SplitTree → Bool
  | .leaf => decide (0 < Poly.centredBound p fun i => (hi i - lo i) / 2)
  | .bern m => decide (0 < m) && decide (0 < Bern.const0 p) && decide (∀ i, lo i < hi i) &&
      Bern.bernOk p (fun i => (hi i - lo i) / 2) (m * Bern.const0 p)
  | .split d m l r =>
    decide (lo d ≤ m ∧ m ≤ hi d) &&
      checkTreeC (Poly.shiftVar p d ((m - hi d) / 2)) lo (Function.update hi d m) l &&
      checkTreeC (Poly.shiftVar p d ((m - lo d) / 2)) (Function.update lo d m) hi r

theorem pos_of_checkTreeC {t : SplitTree} : ∀ {p : Poly} {lo hi : Fin 3 → ℚ}, checkTreeC p lo hi t = true →
    ∀ {x : Fin 3 → ℝ}, (∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ hi i) →
      0 < p.eval (fun i => x i - (((lo i + hi i) / 2 : ℚ) : ℝ)) := by
  induction t with
  | leaf =>
    intro p lo hi h x hx
    simp only [checkTreeC, decide_eq_true_eq] at h
    have h' : (0 : ℝ) < Poly.centredBound p (fun i => (hi i - lo i) / 2) := by exact_mod_cast h
    refine lt_of_lt_of_le h' (Poly.centredBound_le _ _ _ fun i => ?_)
    obtain ⟨a, b⟩ := hx i
    push_cast
    rw [abs_le]; constructor <;> linarith
  | bern m =>
    intro p lo hi h x hx
    simp only [checkTreeC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hc⟩, hlh⟩, hb⟩ := h
    have hmR : (0 : ℝ) < ((m * Bern.const0 p : ℚ) : ℝ) := by exact_mod_cast mul_pos hm hc
    refine lt_of_lt_of_le hmR (Bern.le_of_bernOk hb (fun i => by linarith [hlh i]) fun i => ?_)
    obtain ⟨a, b⟩ := hx i
    push_cast
    rw [abs_le]; constructor <;> linarith
  | split d m l r ihl ihr =>
    intro p lo hi h x hx
    simp only [checkTreeC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, hl⟩, hr⟩ := h
    rcases le_total (x d) m with hd | hd
    · have := ihl hl (x := x) (fun i => by
        by_cases hi : i = d
        · subst hi; simp [hd, (hx i).1]
        · simp [Function.update_of_ne hi, hx i])
      rw [Poly.eval_shiftVar] at this
      convert this using 2
      ext i
      by_cases hi : i = d
      · subst hi; simp; ring
      · simp [Function.update_of_ne hi]
    · have := ihr hr (x := x) (fun i => by
        by_cases hi : i = d
        · subst hi; simp [hd, (hx i).2]
        · simp [Function.update_of_ne hi, hx i])
      rw [Poly.eval_shiftVar] at this
      convert this using 2
      ext i
      by_cases hi : i = d
      · subst hi; simp; ring
      · simp [Function.update_of_ne hi]

end SeptopertShell

end
