module

public import Mathlib

/-!
# Exact rational polynomials in three variables, with interval lower bounds

Computable exact arithmetic (to be run natively on large data) with soundness theorems: sparse polynomials
`Poly` (lists of rational-coefficient terms), evaluation homomorphism, `normalize`, substitution `compose`,
exact monomial lower bounds on a rational box, subdivision certificates `SplitTree` / `checkTree`, division by a
power of `x₂`, and the shift `x₂ ↦ dc + x₂`. Independent of any geometry.
-/

@[expose] public section

namespace SeptopertShell

/-- Exponents of the three variables `x0, x1, x2`. -/
abbrev Mono := ℕ × ℕ × ℕ

/-- A sparse sum of terms `(i, j, k), c ↦ c * x0^i * x1^j * x2^k` (duplicates allowed). -/
abbrev Poly := List (Mono × ℚ)

namespace Poly

/-- Real value of a term. -/
def termEval (t : Mono × ℚ) (x : Fin 3 → ℝ) : ℝ :=
  (t.2 : ℝ) * x 0 ^ t.1.1 * x 1 ^ t.1.2.1 * x 2 ^ t.1.2.2

/-- Evaluation. -/
def eval (p : Poly) (x : Fin 3 → ℝ) : ℝ := (p.map fun t => termEval t x).sum

@[simp] theorem eval_nil (x : Fin 3 → ℝ) : eval [] x = 0 := by simp [eval]

@[simp] theorem eval_cons (t : Mono × ℚ) (p : Poly) (x : Fin 3 → ℝ) :
    eval (t :: p) x = termEval t x + eval p x := by simp [eval]

theorem eval_append (p q : Poly) (x : Fin 3 → ℝ) : eval (p ++ q) x = eval p x + eval q x := by
  simp [eval]

def add (p q : Poly) : Poly := p ++ q

def neg (p : Poly) : Poly := p.map fun t => (t.1, -t.2)

def sub (p q : Poly) : Poly := add p (neg q)

/-- Product of monomials. -/
def monoMul (a b : Mono) : Mono := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- Multiply every term of `q` by the term `a`. -/
def mulTerm (a : Mono × ℚ) (q : Poly) : Poly := q.map fun b => (monoMul a.1 b.1, a.2 * b.2)

def mul (p q : Poly) : Poly := p.flatMap fun a => mulTerm a q

def const (c : ℚ) : Poly := [((0, 0, 0), c)]

def var (i : Fin 3) : Poly :=
  [(((if i = 0 then 1 else 0), (if i = 1 then 1 else 0), (if i = 2 then 1 else 0)), 1)]

theorem eval_add (p q : Poly) (x : Fin 3 → ℝ) : (add p q).eval x = p.eval x + q.eval x :=
  eval_append p q x

theorem eval_neg (p : Poly) (x : Fin 3 → ℝ) : (neg p).eval x = - p.eval x := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; simp [termEval]; ring

theorem eval_sub (p q : Poly) (x : Fin 3 → ℝ) : (sub p q).eval x = p.eval x - q.eval x := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_const (c : ℚ) (x : Fin 3 → ℝ) : (const c).eval x = c := by
  simp [const, termEval]

theorem eval_var (i : Fin 3) (x : Fin 3 → ℝ) : (var i).eval x = x i := by
  fin_cases i <;> simp [var, termEval]

theorem eval_mulTerm (a : Mono × ℚ) (q : Poly) (x : Fin 3 → ℝ) :
    (mulTerm a q).eval x = termEval a x * q.eval x := by
  induction q with
  | nil => simp [mulTerm]
  | cons b q ih =>
    simp only [mulTerm, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    simp only [termEval, monoMul]
    push_cast
    simp only [pow_add]
    ring

theorem eval_mul (p q : Poly) (x : Fin 3 → ℝ) : (mul p q).eval x = p.eval x * q.eval x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    have : mul (a :: p) q = mulTerm a q ++ mul p q := by simp [mul]
    rw [this, eval_append, ih, eval_mulTerm]; simp; ring

/-! ### Normalization -/

/-- A total lexicographic order on monomials, as a `Bool`. -/
def monoLe (a b : Mono) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) &&
    (decide (a.2.1 < b.2.1) || (decide (a.2.1 = b.2.1) && decide (a.2.2 ≤ b.2.2))))

/-- Merge adjacent terms with equal monomials. -/
def mergeAdj : Poly → Poly
  | [] => []
  | [t] => [t]
  | t :: u :: rest =>
    if t.1 = u.1 then mergeAdj ((t.1, t.2 + u.2) :: rest) else t :: mergeAdj (u :: rest)
termination_by l => l.length

theorem eval_mergeAdj (l : Poly) (x : Fin 3 → ℝ) : (mergeAdj l).eval x = l.eval x := by
  induction l using mergeAdj.induct with
  | case1 => simp [mergeAdj]
  | case2 t => simp [mergeAdj]
  | case3 t u rest h ih =>
    rw [mergeAdj, ite_eq_left h, ih]
    simp only [eval_cons, termEval]
    rw [← h]; push_cast; ring
  | case4 t u rest h ih =>
    rw [mergeAdj, ite_eq_right h]
    simp only [eval_cons, ih]

theorem eval_dropZero (l : Poly) (x : Fin 3 → ℝ) :
    eval (l.filter fun t => decide (t.2 ≠ 0)) x = l.eval x := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases h : t.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih]
      simp [termEval, h]
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [eval_cons, ih]

theorem eval_sortTerms (l : Poly) (x : Fin 3 → ℝ) :
    eval (l.mergeSort fun s t => monoLe s.1 t.1) x = l.eval x := by
  unfold eval
  exact ((List.mergeSort_perm l _).map _).sum_eq

/-- Sort by monomial, merge equal monomials, drop zero coefficients. -/
def normalize (p : Poly) : Poly :=
  (mergeAdj (p.mergeSort fun s t => monoLe s.1 t.1)).filter fun t => decide (t.2 ≠ 0)

theorem eval_normalize (p : Poly) (x : Fin 3 → ℝ) : (normalize p).eval x = p.eval x := by
  rw [normalize, eval_dropZero, eval_mergeAdj, eval_sortTerms]

/-! ### Substitution -/

/-- Iterates of `f` from `a`: `[a, f a, f (f a), …]` (`n` entries). -/
def iterList {α : Type} (f : α → α) (a : α) : ℕ → List α
  | 0 => []
  | n + 1 => a :: iterList f (f a) n

theorem iterList_getElem? {α : Type} (f : α → α) (n : ℕ) :
    ∀ (a : α) (i : ℕ), i < n → (iterList f a n)[i]? = some (f^[i] a) := by
  induction n with
  | zero => intro a i h; omega
  | succ n ih =>
    intro a i h
    cases i with
    | zero => simp [iterList]
    | succ i =>
      simp only [iterList, List.getElem?_cons_succ]
      rw [ih _ _ (by omega), Function.iterate_succ_apply]

def powStep (q r : Poly) : Poly := normalize (mul r q)

/-- `q ^ n`, normalized at each step. -/
def pow (q : Poly) (n : ℕ) : Poly := (powStep q)^[n] (const 1)

theorem eval_pow (q : Poly) (n : ℕ) (x : Fin 3 → ℝ) : (pow q n).eval x = (q.eval x) ^ n := by
  induction n with
  | zero => simp [pow, eval_const]
  | succ n ih =>
    have : pow q (n + 1) = powStep q (pow q n) := by
      simp only [pow]; rw [Function.iterate_succ_apply']
    rw [this, powStep, eval_normalize, eval_mul, ih]; ring

/-- Table of the powers `q^0, …, q^(n-1)`. -/
def powTab (q : Poly) (n : ℕ) : List Poly := iterList (powStep q) (const 1) n

/-- Lookup in the table with fallback to direct computation. -/
def powGet (q : Poly) (tab : List Poly) (i : ℕ) : Poly :=
  match tab[i]? with
  | some r => r
  | none => pow q i

theorem eval_powGet (q : Poly) (n i : ℕ) (x : Fin 3 → ℝ) :
    (powGet q (powTab q n) i).eval x = (q.eval x) ^ i := by
  unfold powGet
  by_cases h : i < n
  · rw [powTab, iterList_getElem? _ _ _ _ h]; exact eval_pow q i x
  · have : (powTab q n)[i]? = none := by
      rw [List.getElem?_eq_none_iff]
      have : (powTab q n).length = n := by
        unfold powTab
        suffices ∀ (a : Poly) m, (iterList (powStep q) a m).length = m from this _ _
        intro a m
        induction m generalizing a with
        | zero => rfl
        | succ m ih => simp [iterList, ih]
      omega
    rw [this]; exact eval_pow q i x

def maxExp (p : Poly) (f : Mono → ℕ) : ℕ := p.foldl (fun m t => max m (f t.1)) 0

/-- Scale a polynomial by a rational. -/
def scale (c : ℚ) (p : Poly) : Poly := mulTerm ((0, 0, 0), c) p

theorem eval_scale (c : ℚ) (p : Poly) (x : Fin 3 → ℝ) : (scale c p).eval x = c * p.eval x := by
  rw [scale, eval_mulTerm]; simp [termEval]

/-- Substitute `x_i := q_i`. -/
def compose (p q0 q1 q2 : Poly) : Poly :=
  let t0 := powTab q0 (maxExp p (·.1) + 1)
  let t1 := powTab q1 (maxExp p (·.2.1) + 1)
  let t2 := powTab q2 (maxExp p (·.2.2) + 1)
  normalize (p.flatMap fun t =>
    scale t.2 (mul (powGet q0 t0 t.1.1) (mul (powGet q1 t1 t.1.2.1) (powGet q2 t2 t.1.2.2))))

theorem eval_flatMapAux (p : Poly) (g0 g1 g2 : ℕ → Poly) (a b c : ℝ) (x : Fin 3 → ℝ)
    (h0 : ∀ i, (g0 i).eval x = a ^ i) (h1 : ∀ i, (g1 i).eval x = b ^ i)
    (h2 : ∀ i, (g2 i).eval x = c ^ i) :
    eval (p.flatMap fun t => scale t.2 (mul (g0 t.1.1) (mul (g1 t.1.2.1) (g2 t.1.2.2)))) x
      = p.eval ![a, b, c] := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.flatMap_cons, eval_append, ih, eval_cons, eval_scale, eval_mul, eval_mul, h0, h1, h2]
    simp [termEval]; ring

theorem eval_compose (p q0 q1 q2 : Poly) (x : Fin 3 → ℝ) :
    (compose p q0 q1 q2).eval x = p.eval ![q0.eval x, q1.eval x, q2.eval x] := by
  unfold compose
  simp only []
  rw [eval_normalize]
  exact eval_flatMapAux _ _ _ _ _ _ _ x (fun i => eval_powGet _ _ _ _) (fun i => eval_powGet _ _ _ _)
    (fun i => eval_powGet _ _ _ _)

/-! ### Division by a power of `x₂` and shift -/

/-- Lower the `x₂`-exponent of a term by `m`. -/
def lowerX2 (m : ℕ) (t : Mono × ℚ) : Mono × ℚ := ((t.1.1, t.1.2.1, t.1.2.2 - m), t.2)

/-- `some q` with `p = x₂^m * q` if every term has `x₂`-exponent `≥ m`. -/
def divX2 (p : Poly) (m : ℕ) : Option Poly :=
  if p.all (fun t => decide (m ≤ t.1.2.2)) then some (p.map (lowerX2 m)) else none

theorem eval_lowerX2 (p : Poly) (m : ℕ) (x : Fin 3 → ℝ) (h : ∀ t ∈ p, m ≤ t.1.2.2) :
    p.eval x = x 2 ^ m * eval (p.map (lowerX2 m)) x := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht := h t (by simp)
    have ih' := ih (fun u hu => h u (by simp [hu]))
    simp only [List.map_cons, eval_cons]
    rw [ih']
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    simp only [termEval, lowerX2, hd, Nat.add_sub_cancel_left, pow_add]
    ring

theorem eval_divX2 {p q : Poly} {m : ℕ} (h : divX2 p m = some q) (x : Fin 3 → ℝ) :
    p.eval x = x 2 ^ m * q.eval x := by
  unfold divX2 at h
  split_ifs at h with hc
  · cases h
    apply eval_lowerX2
    intro t ht
    simpa using (List.all_eq_true.mp hc t ht)

/-- Substitute `x₂ := dc + x₂`. -/
def shiftX2 (p : Poly) (dc : ℚ) : Poly := p.compose (var 0) (var 1) (add (const dc) (var 2))

theorem eval_shiftX2 (p : Poly) (dc : ℚ) (x : Fin 3 → ℝ) :
    (shiftX2 p dc).eval x = p.eval ![x 0, x 1, dc + x 2] := by
  rw [shiftX2, eval_compose, eval_var, eval_var, eval_add, eval_const, eval_var]

end Poly

/-! ### Boxes and exact monomial lower bounds -/

/-- A rational box. -/
structure Box where
  lo : Fin 3 → ℚ
  hi : Fin 3 → ℚ

def Box.mem (B : Box) (x : Fin 3 → ℝ) : Prop := ∀ i, (B.lo i : ℝ) ≤ x i ∧ x i ≤ B.hi i

/-- Exact range of `t^k` for `t ∈ [lo, hi]`. -/
def powRange (lo hi : ℚ) (k : ℕ) : ℚ × ℚ :=
  if k = 0 then (1, 1)
  else if k % 2 = 0 ∧ lo < 0 ∧ 0 < hi then (0, max (lo ^ k) (hi ^ k))
  else (min (lo ^ k) (hi ^ k), max (lo ^ k) (hi ^ k))

theorem pow_between_real (lo hi t : ℝ) (k : ℕ) (h1 : lo ≤ t) (h2 : t ≤ hi)
    (hs : ¬ (Even k ∧ lo < 0 ∧ 0 < hi)) :
    min (lo ^ k) (hi ^ k) ≤ t ^ k ∧ t ^ k ≤ max (lo ^ k) (hi ^ k) := by
  suffices h : (lo ^ k ≤ t ^ k ∧ t ^ k ≤ hi ^ k) ∨ (hi ^ k ≤ t ^ k ∧ t ^ k ≤ lo ^ k) by
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨le_trans (min_le_left _ _) a, le_trans b (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) a, le_trans b (le_max_left _ _)⟩
  rcases Nat.even_or_odd k with he | ho
  · have : 0 ≤ lo ∨ hi ≤ 0 := by
      by_contra hc
      push Not at hc
      exact hs ⟨he, hc.1, hc.2⟩
    rcases this with h0 | h0
    · exact Or.inl ⟨pow_le_pow_left₀ h0 h1 k, pow_le_pow_left₀ (le_trans h0 h1) h2 k⟩
    · right
      have e1 : lo ^ k = (-lo) ^ k := (he.neg_pow lo).symm
      have e2 : hi ^ k = (-hi) ^ k := (he.neg_pow hi).symm
      have e3 : t ^ k = (-t) ^ k := (he.neg_pow t).symm
      rw [e1, e2, e3]
      exact ⟨pow_le_pow_left₀ (by linarith) (by linarith) k,
        pow_le_pow_left₀ (by linarith) (by linarith) k⟩
  · exact Or.inl ⟨ho.strictMono_pow.monotone h1, ho.strictMono_pow.monotone h2⟩

theorem pow_straddle_real (lo hi t : ℝ) (k : ℕ) (h1 : lo ≤ t) (h2 : t ≤ hi) (he : Even k) :
    0 ≤ t ^ k ∧ t ^ k ≤ max (lo ^ k) (hi ^ k) := by
  refine ⟨he.pow_nonneg t, ?_⟩
  rcases le_total 0 t with h0 | h0
  · exact le_trans (pow_le_pow_left₀ h0 h2 k) (le_max_right _ _)
  · have e1 : lo ^ k = (-lo) ^ k := (he.neg_pow lo).symm
    have e3 : t ^ k = (-t) ^ k := (he.neg_pow t).symm
    rw [e3]
    have : (-t) ^ k ≤ (-lo) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    rw [← e1] at this
    exact le_trans this (le_max_left _ _)

theorem powRange_spec (lo hi : ℚ) (k : ℕ) (t : ℝ) (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    ((powRange lo hi k).1 : ℝ) ≤ t ^ k ∧ t ^ k ≤ ((powRange lo hi k).2 : ℝ) := by
  unfold powRange
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    by_cases hc : k % 2 = 0 ∧ lo < 0 ∧ 0 < hi
    · rw [ite_eq_left hc]
      have he : Even k := Nat.even_iff.mpr hc.1
      have := pow_straddle_real lo hi t k h1 h2 he
      simpa using this
    · rw [ite_eq_right hc]
      have hs : ¬ (Even k ∧ (lo : ℝ) < 0 ∧ 0 < (hi : ℝ)) := by
        rintro ⟨he, a, b⟩
        exact hc ⟨Nat.even_iff.mp he, by exact_mod_cast a, by exact_mod_cast b⟩
      have := pow_between_real lo hi t k h1 h2 hs
      simpa using this

theorem min_mid (t t1 t2 s : ℝ) (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    min (s * t1) (s * t2) ≤ s * t := by
  rcases le_total 0 s with h | h
  · exact le_trans (min_le_left _ _) (by nlinarith)
  · exact le_trans (min_le_right _ _) (by nlinarith)

theorem max_mid (t t1 t2 s : ℝ) (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    s * t ≤ max (s * t1) (s * t2) := by
  rcases le_total 0 s with h | h
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

/-- Minimum of the 8 corner products of `[a1,a2] × [b1,b2] × [e1,e2]`. -/
def cornerMin (a1 a2 b1 b2 e1 e2 : ℚ) : ℚ :=
  min (min (min (a1 * b1 * e1) (a1 * b1 * e2)) (min (a1 * b2 * e1) (a1 * b2 * e2)))
      (min (min (a2 * b1 * e1) (a2 * b1 * e2)) (min (a2 * b2 * e1) (a2 * b2 * e2)))

/-- Maximum of the 8 corner products. -/
def cornerMax (a1 a2 b1 b2 e1 e2 : ℚ) : ℚ :=
  max (max (max (a1 * b1 * e1) (a1 * b1 * e2)) (max (a1 * b2 * e1) (a1 * b2 * e2)))
      (max (max (a2 * b1 * e1) (a2 * b1 * e2)) (max (a2 * b2 * e1) (a2 * b2 * e2)))

theorem min4 (s b1 b2 e1 e2 b e : ℝ) (hb1 : b1 ≤ b) (hb2 : b ≤ b2) (he1 : e1 ≤ e) (he2 : e ≤ e2) :
    min (min (s * b1 * e1) (s * b1 * e2)) (min (s * b2 * e1) (s * b2 * e2)) ≤ s * b * e := by
  have k1 := min_mid e e1 e2 (s * b1) he1 he2
  have k2 := min_mid e e1 e2 (s * b2) he1 he2
  have k3 := min_mid b b1 b2 (s * e) hb1 hb2
  have r1 : s * e * b1 = s * b1 * e := by ring
  have r2 : s * e * b2 = s * b2 * e := by ring
  have r3 : s * e * b = s * b * e := by ring
  rw [r1, r2, r3] at k3
  exact le_trans (le_min (le_trans (min_le_left _ _) k1) (le_trans (min_le_right _ _) k2)) k3

theorem max4 (s b1 b2 e1 e2 b e : ℝ) (hb1 : b1 ≤ b) (hb2 : b ≤ b2) (he1 : e1 ≤ e) (he2 : e ≤ e2) :
    s * b * e ≤ max (max (s * b1 * e1) (s * b1 * e2)) (max (s * b2 * e1) (s * b2 * e2)) := by
  have k1 := max_mid e e1 e2 (s * b1) he1 he2
  have k2 := max_mid e e1 e2 (s * b2) he1 he2
  have k3 := max_mid b b1 b2 (s * e) hb1 hb2
  have r1 : s * e * b1 = s * b1 * e := by ring
  have r2 : s * e * b2 = s * b2 * e := by ring
  have r3 : s * e * b = s * b * e := by ring
  rw [r1, r2, r3] at k3
  exact le_trans k3 (max_le_max k1 k2)

theorem cornerMin_le (a1 a2 b1 b2 e1 e2 : ℚ) (a b e : ℝ) (ha1 : (a1 : ℝ) ≤ a) (ha2 : a ≤ a2)
    (hb1 : (b1 : ℝ) ≤ b) (hb2 : b ≤ b2) (he1 : (e1 : ℝ) ≤ e) (he2 : e ≤ e2) :
    (cornerMin a1 a2 b1 b2 e1 e2 : ℝ) ≤ a * b * e := by
  have k := min_mid a a1 a2 (b * e) ha1 ha2
  have r1 : b * e * a1 = a1 * b * e := by ring
  have r2 : b * e * a2 = a2 * b * e := by ring
  have r3 : b * e * a = a * b * e := by ring
  rw [r1, r2, r3] at k
  refine le_trans ?_ k
  have := min4 a1 b1 b2 e1 e2 b e hb1 hb2 he1 he2
  have := min4 a2 b1 b2 e1 e2 b e hb1 hb2 he1 he2
  simp only [cornerMin]
  push_cast
  exact min_le_min ‹_› ‹_›

theorem le_cornerMax (a1 a2 b1 b2 e1 e2 : ℚ) (a b e : ℝ) (ha1 : (a1 : ℝ) ≤ a) (ha2 : a ≤ a2)
    (hb1 : (b1 : ℝ) ≤ b) (hb2 : b ≤ b2) (he1 : (e1 : ℝ) ≤ e) (he2 : e ≤ e2) :
    a * b * e ≤ (cornerMax a1 a2 b1 b2 e1 e2 : ℝ) := by
  have k := max_mid a a1 a2 (b * e) ha1 ha2
  have r1 : b * e * a1 = a1 * b * e := by ring
  have r2 : b * e * a2 = a2 * b * e := by ring
  have r3 : b * e * a = a * b * e := by ring
  rw [r1, r2, r3] at k
  refine le_trans k ?_
  have := max4 a1 b1 b2 e1 e2 b e hb1 hb2 he1 he2
  have := max4 a2 b1 b2 e1 e2 b e hb1 hb2 he1 he2
  simp only [cornerMax]
  push_cast
  exact max_le_max ‹_› ‹_›

/-- Rational lower bound of the term `c * x0^i * x1^j * x2^k` on the box. -/
def termLower (B : Box) (m : Mono) (c : ℚ) : ℚ :=
  let r0 := powRange (B.lo 0) (B.hi 0) m.1
  let r1 := powRange (B.lo 1) (B.hi 1) m.2.1
  let r2 := powRange (B.lo 2) (B.hi 2) m.2.2
  if 0 < c then c * cornerMin r0.1 r0.2 r1.1 r1.2 r2.1 r2.2
  else c * cornerMax r0.1 r0.2 r1.1 r1.2 r2.1 r2.2

theorem termLower_le (B : Box) (m : Mono) (c : ℚ) (x : Fin 3 → ℝ) (hx : B.mem x) :
    (termLower B m c : ℝ) ≤ c * x 0 ^ m.1 * x 1 ^ m.2.1 * x 2 ^ m.2.2 := by
  have s0 := powRange_spec _ _ m.1 _ (hx 0).1 (hx 0).2
  have s1 := powRange_spec _ _ m.2.1 _ (hx 1).1 (hx 1).2
  have s2 := powRange_spec _ _ m.2.2 _ (hx 2).1 (hx 2).2
  have e : (c : ℝ) * x 0 ^ m.1 * x 1 ^ m.2.1 * x 2 ^ m.2.2
      = c * (x 0 ^ m.1 * x 1 ^ m.2.1 * x 2 ^ m.2.2) := by ring
  rw [e]
  unfold termLower
  simp only []
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left (cornerMin_le _ _ _ _ _ _ _ _ _ s0.1 s0.2 s1.1 s1.2 s2.1 s2.2)
      (by exact_mod_cast hc.le)
  · push_cast
    exact mul_le_mul_of_nonpos_left (le_cornerMax _ _ _ _ _ _ _ _ _ s0.1 s0.2 s1.1 s1.2 s2.1 s2.2)
      (by exact_mod_cast not_lt.mp hc)

/-- Rational lower bound of a polynomial on a box. -/
def lowerBound (p : Poly) (B : Box) : ℚ := (p.map fun t => termLower B t.1 t.2).sum

theorem lowerBound_le_eval (p : Poly) (B : Box) (x : Fin 3 → ℝ) (hx : B.mem x) :
    (lowerBound p B : ℝ) ≤ p.eval x := by
  induction p with
  | nil => simp [lowerBound]
  | cons t p ih =>
    simp only [lowerBound, List.map_cons, List.sum_cons] at ih ⊢
    rw [Poly.eval_cons, Rat.cast_add]
    exact add_le_add (termLower_le B t.1 t.2 x hx) ih

/-! ### Subdivision certificates -/

/-- Subdivision certificates. `bern m` is a Bernstein leaf (`Bern.bernOk`, centred trees only), with the lower
bound `m` the certificate claims. -/
inductive SplitTree
  | leaf
  | bern (m : ℚ)
  | split (dim : Fin 3) (mid : ℚ) (l r : SplitTree)

def Box.setHi (B : Box) (d : Fin 3) (m : ℚ) : Box := { B with hi := Function.update B.hi d m }
def Box.setLo (B : Box) (d : Fin 3) (m : ℚ) : Box := { B with lo := Function.update B.lo d m }

def checkTree (p : Poly) : Box → SplitTree → Bool
  | B, .leaf => decide (0 < lowerBound p B)
  | _, .bern _ => false
  | B, .split d m l r =>
    decide (B.lo d ≤ m ∧ m ≤ B.hi d) && checkTree p (B.setHi d m) l && checkTree p (B.setLo d m) r

theorem Box.mem_setHi {B : Box} {x : Fin 3 → ℝ} {d : Fin 3} {m : ℚ} (h : B.mem x)
    (hm : x d ≤ m) : (B.setHi d m).mem x := by
  intro i
  by_cases hi : i = d
  · subst hi; simp [Box.setHi, hm, (h i).1]
  · simp [Box.setHi, Function.update_of_ne hi, h i]

theorem Box.mem_setLo {B : Box} {x : Fin 3 → ℝ} {d : Fin 3} {m : ℚ} (h : B.mem x)
    (hm : (m : ℝ) ≤ x d) : (B.setLo d m).mem x := by
  intro i
  by_cases hi : i = d
  · subst hi; simp [Box.setLo, hm, (h i).2]
  · simp [Box.setLo, Function.update_of_ne hi, h i]

theorem pos_of_checkTree {p : Poly} {t : SplitTree} {B : Box} (h : checkTree p B t = true)
    {x : Fin 3 → ℝ} (hx : B.mem x) : 0 < p.eval x := by
  induction t generalizing B with
  | leaf =>
    simp only [checkTree, decide_eq_true_eq] at h
    have := lowerBound_le_eval p B x hx
    have h' : (0 : ℝ) < lowerBound p B := by exact_mod_cast h
    linarith
  | bern _ => simp [checkTree] at h
  | split d m l r ihl ihr =>
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, hl⟩, hr⟩ := h
    rcases le_total (x d) m with hd | hd
    · exact ihl hl (Box.mem_setHi hx hd)
    · exact ihr hr (Box.mem_setLo hx hd)

theorem pos_of_divX2 {p q : Poly} {m : ℕ} (hd : Poly.divX2 p m = some q) {t : SplitTree} {B : Box}
    (h : checkTree q B t = true) {x : Fin 3 → ℝ} (hx : B.mem x) (h2 : 0 < x 2) :
    0 < p.eval x := by
  rw [Poly.eval_divX2 hd]
  exact mul_pos (pow_pos h2 m) (pos_of_checkTree h hx)

/-! ### Centred form -/

namespace Poly

/-- Exponent of variable `d`. -/
def monoGet (m : Mono) (d : Fin 3) : ℕ := if d = 0 then m.1 else if d = 1 then m.2.1 else m.2.2

/-- Replace the exponent of variable `d`. -/
def monoSet (m : Mono) (d : Fin 3) (l : ℕ) : Mono :=
  if d = 0 then (l, m.2) else if d = 1 then (m.1, l, m.2.2) else (m.1, m.2.1, l)

/-- The binomial expansion of one term under `x_d ↦ h_d + a`. -/
def expandTerm (t : Mono × ℚ) (d : Fin 3) (a : ℚ) : Poly :=
  (List.range (monoGet t.1 d + 1)).map fun l =>
    (monoSet t.1 d l, t.2 * ((monoGet t.1 d).choose l : ℚ) * a ^ (monoGet t.1 d - l))

/-- `p(h + a e_d)`. -/
def shiftVar (p : Poly) (d : Fin 3) (a : ℚ) : Poly := normalize (p.flatMap fun t => expandTerm t d a)

theorem sum_range_list (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem eval_expandTerm (t : Mono × ℚ) (d : Fin 3) (a : ℚ) (h : Fin 3 → ℝ) :
    (expandTerm t d a).eval h = termEval t (Function.update h d (h d + a)) := by
  obtain ⟨⟨i, j, k⟩, c⟩ := t
  unfold expandTerm eval
  rw [List.map_map]
  rw [sum_range_list (fun l => _)]
  fin_cases d
  · simp only [monoGet, monoSet, Function.comp_def, termEval]
    simp only [Fin.zero_eta, ite_true]
    have e0 : Function.update h 0 (h 0 + a) 0 = h 0 + a := by simp
    have e1 : Function.update h 0 (h 0 + a) 1 = h 1 := by simp
    have e2 : Function.update h 0 (h 0 + a) 2 = h 2 := by simp
    rw [e0, e1, e2, add_pow, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  · simp only [monoGet, monoSet, Function.comp_def, termEval]
    simp only [Fin.mk_one, Fin.isValue, ite_true, one_ne_zero, ite_false]
    have e0 : Function.update h 1 (h 1 + a) 0 = h 0 := by simp
    have e1 : Function.update h 1 (h 1 + a) 1 = h 1 + a := by simp
    have e2 : Function.update h 1 (h 1 + a) 2 = h 2 := by simp
    rw [e0, e1, e2, add_pow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  · simp only [monoGet, monoSet, Function.comp_def, termEval]
    simp
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem eval_shiftVar (p : Poly) (d : Fin 3) (a : ℚ) (h : Fin 3 → ℝ) :
    (shiftVar p d a).eval h = p.eval (Function.update h d (h d + a)) := by
  unfold shiftVar
  rw [eval_normalize]
  induction p with
  | nil => simp
  | cons t p ih => rw [List.flatMap_cons, eval_append, ih, eval_expandTerm, eval_cons]

/-- Lower bound on `|h i| ≤ r i`, with the constant term kept exactly and every other term bounded by its
absolute value. -/
def centredBound (p : Poly) (r : Fin 3 → ℚ) : ℚ :=
  (p.map fun t => if t.1 = (0, 0, 0) then t.2 else -|t.2| * (r 0 ^ t.1.1 * r 1 ^ t.1.2.1 * r 2 ^ t.1.2.2)).sum

theorem centredBound_le (p : Poly) (r : Fin 3 → ℚ) (h : Fin 3 → ℝ) (hr : ∀ i, |h i| ≤ r i) :
    (centredBound p r : ℝ) ≤ p.eval h := by
  induction p with
  | nil => simp [centredBound]
  | cons t p ih =>
    simp only [centredBound, List.map_cons, List.sum_cons] at ih ⊢
    rw [eval_cons, Rat.cast_add]
    refine add_le_add ?_ ih
    obtain ⟨⟨i, j, k⟩, c⟩ := t
    by_cases h0 : (i, j, k) = (0, 0, 0)
    · obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 0 ∧ k = 0 := by simpa using h0
      simp [termEval]
    · simp only [h0, ite_false]
      push_cast
      have b0 : |h 0| ^ i ≤ (r 0 : ℝ) ^ i := pow_le_pow_left₀ (abs_nonneg _) (hr 0) i
      have b1 : |h 1| ^ j ≤ (r 1 : ℝ) ^ j := pow_le_pow_left₀ (abs_nonneg _) (hr 1) j
      have b2 : |h 2| ^ k ≤ (r 2 : ℝ) ^ k := pow_le_pow_left₀ (abs_nonneg _) (hr 2) k
      have hab : |termEval ((i, j, k), c) h| ≤ |(c : ℝ)| * ((r 0 : ℝ) ^ i * (r 1 : ℝ) ^ j * (r 2 : ℝ) ^ k) := by
        simp only [termEval, abs_mul, abs_pow]
        have p0 := abs_nonneg (h 0); have p1 := abs_nonneg (h 1); have p2 := abs_nonneg (h 2)
        have e : |(c : ℝ)| * |h 0| ^ i * |h 1| ^ j * |h 2| ^ k = |(c : ℝ)| * (|h 0| ^ i * |h 1| ^ j * |h 2| ^ k) := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul (mul_le_mul b0 b1 (by positivity) (le_trans (by positivity) b0)) b2 (by positivity)
          (by have := le_trans (abs_nonneg (h 0)) (hr 0); have := le_trans (abs_nonneg (h 1)) (hr 1); positivity)
      rw [neg_mul]
      linarith [neg_abs_le (termEval ((i, j, k), c) h)]

end Poly

end SeptopertShell


end
