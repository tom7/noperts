module

public import Pipeline.TribQ
public import Pipeline.BernsteinBound

@[expose] public section

/-!
# Nested polynomials over an exact scalar field

`KPoly K k` is a polynomial in k real variables with coefficients in `K`, an
exact representation of a real field (`ExactScalarOps`: the arithmetic, an
exact zero test and a rational lower bound, all computable;
`ExactScalarVal`: the real value and its compatibility, for the proofs):
`KPoly K 0 = K`, and `KPoly K (k + 1)` is the list of coefficients (in
`KPoly K k`) of the powers of the first variable. Evaluation is Horner's
rule. It is `NPoly` (whose scalars are `IcoQ`) made generic; the snub cube's
cap certificates use `K = TribQ`. Every operation is univariate in the first
variable and recursive in the rest, so its soundness is an induction on k
from the univariate facts.
-/

namespace Noperts.Pipeline

/-- The computable arithmetic of an exact scalar field. -/
class ExactScalarOps (K : Type) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  scale : ℚ → K → K
  /-- An exact zero test. -/
  isZero : K → Bool
  /-- A rational lower bound of the value. -/
  lo : K → ℚ

/-- The real value of an exact scalar field and its compatibility with the
arithmetic (for the proofs; the value need not be computable). -/
class ExactScalarVal (K : Type) [ExactScalarOps K] where
  val : K → ℝ
  val_zero : val ExactScalarOps.zero = 0
  val_one : val ExactScalarOps.one = 1
  val_add : ∀ a b, val (ExactScalarOps.add a b) = val a + val b
  val_mul : ∀ a b, val (ExactScalarOps.mul a b) = val a * val b
  val_scale : ∀ (q : ℚ) a, val (ExactScalarOps.scale q a) = q * val a
  val_of_isZero : ∀ a, ExactScalarOps.isZero a = true → val a = 0
  lo_le_val : ∀ a, (ExactScalarOps.lo a : ℝ) ≤ val a

instance : ExactScalarOps TribQ where
  zero := TribQ.zero
  one := TribQ.one
  add := TribQ.add
  mul := TribQ.mul
  scale := TribQ.scale
  isZero x := decide (x = TribQ.zero)
  lo := TribQ.lo

noncomputable instance : ExactScalarVal TribQ where
  val := TribQ.val
  val_zero := TribQ.val_zero
  val_one := TribQ.val_one
  val_add a b := TribQ.val_add a b
  val_mul a b := TribQ.val_mul a b
  val_scale q a := TribQ.val_scale q a
  val_of_isZero a h := by
    have : a = TribQ.zero := of_decide_eq_true h
    rw [this]; exact TribQ.val_zero
  lo_le_val := TribQ.lo_le_val

def KPoly (K : Type) : ℕ → Type
  | 0 => K
  | k + 1 => List (KPoly K k)

namespace KPoly

variable {K : Type} [ExactScalarOps K]

/-! ### Evaluation -/

/-- Horner evaluation of a coefficient list, given the coefficient values. -/
noncomputable def horner {α : Type} (v : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a :: as => v a + x * horner v x as

noncomputable def eval [ExactScalarVal K] : (k : ℕ) → KPoly K k → (Fin k → ℝ) → ℝ
  | 0, c, _ => @ExactScalarVal.val K _ _ c
  | k + 1, p, y => horner (fun q => eval k q (Fin.tail y)) (y 0) (p : List (KPoly K k))

@[simp] theorem horner_nil {α : Type} (v : α → ℝ) (x : ℝ) : horner v x [] = 0 := rfl
@[simp] theorem horner_cons {α : Type} (v : α → ℝ) (x : ℝ) (a : α) (as : List α) :
    horner v x (a :: as) = v a + x * horner v x as := rfl

/-- The j-th coefficient value (0 past the end). -/
noncomputable def cf {α : Type} (v : α → ℝ) (l : List α) (j : ℕ) : ℝ :=
  match l[j]? with
  | some a => v a
  | none => 0

theorem horner_eq_sum {α : Type} (v : α → ℝ) (x : ℝ) (l : List α) :
    horner v x l = ∑ j ∈ Finset.range l.length, cf v l j * x ^ j := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [horner_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [cf, List.getElem?_cons_succ, List.getElem?_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-! ### Zero, constants, linear operations -/

def zero : (k : ℕ) → KPoly K k
  | 0 => @ExactScalarOps.zero K _
  | _ + 1 => ([] : List _)

theorem eval_zero [ExactScalarVal K] (k : ℕ) (y : Fin k → ℝ) : eval k (zero (K := K) k) y = 0 := by
  cases k with
  | zero => exact @ExactScalarVal.val_zero K _ _
  | succ k => rfl

/-- Padded pointwise combination of coefficient lists. -/
def ladd {α : Type} (f : α → α → α) : List α → List α → List α
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => f x y :: ladd f xs ys

def add : (k : ℕ) → KPoly K k → KPoly K k → KPoly K k
  | 0, a, b => @ExactScalarOps.add K _ a b
  | k + 1, a, b => ladd (add k) (a : List (KPoly K k)) b

def scale : (k : ℕ) → ℚ → KPoly K k → KPoly K k
  | 0, q, a => @ExactScalarOps.scale K _ q a
  | k + 1, q, a => (a : List (KPoly K k)).map (scale k q)

theorem horner_ladd {α : Type} (v : α → ℝ) (x : ℝ) (f : α → α → α) (hf : ∀ a b, v (f a b) = v a + v b) :
    ∀ a b : List α, horner v x (ladd f a b) = horner v x a + horner v x b
  | [], b => by simp [ladd]
  | _ :: _, [] => by simp [ladd]
  | a :: as, b :: bs => by
    simp only [ladd, horner_cons, hf, horner_ladd v x f hf as bs]
    ring

theorem eval_add [ExactScalarVal K] : ∀ (k : ℕ) (a b : KPoly K k) (y : Fin k → ℝ), eval k (add k a b) y = eval k a y + eval k b y
  | 0, a, b, _ => @ExactScalarVal.val_add K _ _ a b
  | k + 1, a, b, y => horner_ladd _ _ _ (fun p q => eval_add k p q _) _ _

theorem eval_scale [ExactScalarVal K] : ∀ (k : ℕ) (q : ℚ) (a : KPoly K k) (y : Fin k → ℝ), eval k (scale k q a) y = q * eval k a y
  | 0, q, a, _ => @ExactScalarVal.val_scale K _ _ q a
  | k + 1, q, a, y => by
    show horner _ _ ((a : List (KPoly K k)).map (scale k q)) = _ * horner _ _ (a : List (KPoly K k))
    induction (a : List (KPoly K k)) with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, horner_cons, eval_scale k q p, ih]
      ring

/-- Σ_i q_i • p_i over a list of (weight, polynomial) pairs. -/
def lincomb (k : ℕ) : List (ℚ × KPoly K k) → KPoly K k
  | [] => zero k
  | (q, p) :: rest => add k (scale k q p) (lincomb k rest)

theorem eval_lincomb [ExactScalarVal K] (k : ℕ) (l : List (ℚ × KPoly K k)) (y : Fin k → ℝ) :
    eval k (lincomb k l) y = (l.map fun qp => (qp.1 : ℝ) * eval k qp.2 y).sum := by
  induction l with
  | nil => simp [lincomb, eval_zero]
  | cons qp rest ih =>
    obtain ⟨q, p⟩ := qp
    simp [lincomb, eval_add, eval_scale, ih]

theorem sum_map_range {β : Type} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-! ### Constants, variables, products -/

def const : (k : ℕ) → K → KPoly K k
  | 0, c => c
  | k + 1, c => [const k c]

theorem eval_const [ExactScalarVal K] [ExactScalarVal K] : ∀ (k : ℕ) (c : K) (y : Fin k → ℝ),
    eval k (const k c) y = ExactScalarVal.val c
  | 0, _, _ => rfl
  | k + 1, c, y => by
    show horner _ _ [const k c] = _
    simp [eval_const k c]

/-- The variable y_i. -/
def var : (k : ℕ) → Fin k → KPoly K k
  | k + 1, i => Fin.cases (motive := fun _ => KPoly K (k + 1))
      ([zero k, const k ExactScalarOps.one] : List (KPoly K k)) (fun j => ([var k j] : List (KPoly K k))) i

theorem eval_var [ExactScalarVal K] : ∀ (k : ℕ) (i : Fin k) (y : Fin k → ℝ), eval k (var (K := K) k i) y = y i
  | k + 1, i, y => by
    cases i using Fin.cases with
    | zero =>
      show horner _ _ [zero k, const k ExactScalarOps.one] = _
      simp [eval_zero, eval_const, ExactScalarVal.val_one]
    | succ j =>
      show horner _ _ [var k j] = _
      simp [eval_var k j, Fin.tail]

def mulL {α : Type} (addf mulf : α → α → α) (z : α) : List α → List α → List α
  | [], _ => []
  | x :: xs, b => ladd addf (b.map (mulf x)) (z :: mulL addf mulf z xs b)

def mul : (k : ℕ) → KPoly K k → KPoly K k → KPoly K k
  | 0, a, b => @ExactScalarOps.mul K _ a b
  | k + 1, a, b => mulL (add k) (mul k) (zero k) (a : List (KPoly K k)) b

theorem horner_map {α : Type} (v : α → ℝ) (x : ℝ) (f : α → α) (c : ℝ) (hf : ∀ a, v (f a) = c * v a)
    (l : List α) : horner v x (l.map f) = c * horner v x l := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, horner_cons, hf, ih]; ring

theorem horner_mulL {α : Type} (v : α → ℝ) (x : ℝ) (addf mulf : α → α → α) (z : α)
    (ha : ∀ a b, v (addf a b) = v a + v b) (hm : ∀ a b, v (mulf a b) = v a * v b) (hz : v z = 0) :
    ∀ a b : List α, horner v x (mulL addf mulf z a b) = horner v x a * horner v x b
  | [], b => by simp [mulL]
  | p :: ps, b => by
    rw [mulL, horner_ladd v x addf ha, horner_map v x (mulf p) (v p) (fun a => hm p a), horner_cons, hz,
      horner_mulL v x addf mulf z ha hm hz ps b, horner_cons]
    ring

theorem eval_mul [ExactScalarVal K] : ∀ (k : ℕ) (a b : KPoly K k) (y : Fin k → ℝ), eval k (mul k a b) y = eval k a y * eval k b y
  | 0, a, b, _ => @ExactScalarVal.val_mul K _ _ a b
  | k + 1, a, b, y =>
    horner_mulL _ _ _ _ _ (fun p q => eval_add k p q _) (fun p q => eval_mul k p q _) (eval_zero k _) _ _

def sub (k : ℕ) (a b : KPoly K k) : KPoly K k := add k a (scale k (-1) b)

theorem eval_sub [ExactScalarVal K] (k : ℕ) (a b : KPoly K k) (y : Fin k → ℝ) : eval k (sub k a b) y = eval k a y - eval k b y := by
  simp [sub, eval_add, eval_scale]; ring

/-! ### Exact division by a variable -/

def isZero : (k : ℕ) → KPoly K k → Bool
  | 0, c => @ExactScalarOps.isZero K _ c
  | k + 1, p => (p : List (KPoly K k)).all (isZero k)

theorem horner_zero_of_all {α : Type} (v : α → ℝ) (x : ℝ) (Z : α → Bool) (hZ : ∀ a, Z a = true → v a = 0) :
    ∀ l : List α, l.all Z = true → horner v x l = 0
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [horner_cons, hZ a h.1, horner_zero_of_all v x Z hZ as h.2]
    ring

theorem eval_of_isZero [ExactScalarVal K] : ∀ (k : ℕ) (p : KPoly K k) (y : Fin k → ℝ), isZero k p = true → eval k p y = 0
  | 0, c, _, h => @ExactScalarVal.val_of_isZero K _ _ c h
  | k + 1, p, y, h => horner_zero_of_all _ _ (isZero k) (fun a ha => eval_of_isZero k a _ ha) _ h

theorem horner_append {α : Type} (v : α → ℝ) (x : ℝ) (l₁ l₂ : List α) :
    horner v x (l₁ ++ l₂) = horner v x l₁ + x ^ l₁.length * horner v x l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, horner_cons, ih, List.length_cons, pow_succ]; ring

theorem horner_mapM {α : Type} (v : α → ℝ) (x : ℝ) (f : α → Option α) (c : ℝ)
    (hf : ∀ a b, f a = some b → v a = c * v b) :
    ∀ (l l' : List α), l.mapM f = some l' → horner v x l = c * horner v x l'
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h; simp
  | a :: as, l', h => by
    cases hfa : f a with
    | none => simp [List.mapM_cons, hfa] at h
    | some b =>
      cases hm : as.mapM f with
      | none => simp [List.mapM_cons, hfa, hm] at h
      | some bs =>
        simp only [List.mapM_cons, hfa, hm] at h
        cases h
        rw [horner_cons, horner_cons, hf a b hfa, horner_mapM v x f c hf as bs hm]
        ring

/-- p / y_i^m when every term of p has y_i-degree ≥ m. -/
def divVar : (k : ℕ) → Fin k → ℕ → KPoly K k → Option (KPoly K k)
  | k + 1, i, m, p => Fin.cases (motive := fun _ => Option (KPoly K (k + 1)))
      (if ((p : List (KPoly K k)).take m).all (isZero k) then some ((p : List (KPoly K k)).drop m) else none)
      (fun j => ((p : List (KPoly K k)).mapM (divVar k j m)).map fun l => (l : KPoly K (k + 1))) i

theorem eval_divVar [ExactScalarVal K] : ∀ (k : ℕ) (i : Fin k) (m : ℕ) (p q : KPoly K k) (y : Fin k → ℝ),
    divVar k i m p = some q → eval k p y = y i ^ m * eval k q y
  | k + 1, i, m, p, q, y, h => by
    cases i using Fin.cases with
    | zero =>
      simp only [divVar, Fin.cases_zero] at h
      split_ifs at h with hz
      cases h
      show horner _ _ (p : List (KPoly K k)) = _ * horner _ _ ((p : List (KPoly K k)).drop m)
      conv_lhs => rw [← List.take_append_drop m (p : List (KPoly K k))]
      rw [horner_append, horner_zero_of_all _ _ (isZero k) (fun a ha => eval_of_isZero k a _ ha) _ hz,
        zero_add]
      rcases Nat.lt_or_ge (p : List (KPoly K k)).length m with hl | hl
      · rw [List.drop_eq_nil_of_le hl.le]; simp
      · rw [List.length_take_of_le hl]
    | succ j =>
      simp only [divVar, Fin.cases_succ] at h
      cases hl : (p : List (KPoly K k)).mapM (divVar k j m) with
      | none => rw [hl] at h; cases h
      | some l =>
      rw [hl] at h
      cases h
      show horner _ _ (p : List (KPoly K k)) = y j.succ ^ m * horner _ _ (l : List (KPoly K k))
      exact horner_mapM (fun q => eval k q (Fin.tail y)) (y 0) (divVar k j m) (Fin.tail y j ^ m)
        (fun a b hab => eval_divVar k j m a b (Fin.tail y) hab) _ _ hl

/-! ### Taylor shift and Bernstein transform in the first variable -/

/-- The real identity behind `shift`: Σ_{f<L} a_f (lo + h t)^f =
Σ_{g<L} (Σ_{m<L-g} C(g+m, g) lo^m h^g a_{g+m}) t^g. -/
theorem taylor_shift (L : ℕ) (a : ℕ → ℝ) (lo h t : ℝ) :
    ∑ f ∈ Finset.range L, a f * (lo + h * t) ^ f =
      ∑ g ∈ Finset.range L,
        (∑ m ∈ Finset.range (L - g), ((g + m).choose g : ℝ) * lo ^ m * h ^ g * a (g + m)) * t ^ g := by
  have hin : ∀ g ∈ Finset.range L,
      (∑ m ∈ Finset.range (L - g), ((g + m).choose g : ℝ) * lo ^ m * h ^ g * a (g + m)) * t ^ g =
        ∑ f ∈ Finset.Ico g L, (f.choose g : ℝ) * lo ^ (f - g) * h ^ g * a f * t ^ g := by
    intro g _
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl hin]
  rw [Finset.sum_comm' (s' := fun f => Finset.range (f + 1)) (t' := Finset.range L)]
  · apply Finset.sum_congr rfl
    intro f _
    rw [add_comm lo, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_pow]
    ring
  · intro g f
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- Coefficient j of a coefficient list (zero past the end). -/
def coeffAt (k : ℕ) (p : List (KPoly K k)) (j : ℕ) : KPoly K k := p.getD j (zero k)

theorem cf_eq_eval [ExactScalarVal K] (k : ℕ) (p : List (KPoly K k)) (y : Fin k → ℝ) (j : ℕ) :
    cf (fun q => eval k q y) p j = eval k (coeffAt k p j) y := by
  unfold cf coeffAt
  rw [List.getD_eq_getElem?_getD]
  cases p[j]? with
  | none => simp [eval_zero]
  | some a => rfl

/-- The Taylor shift x = lo + h t of the first variable. -/
def shift (k : ℕ) (lo h : ℚ) (p : List (KPoly K k)) : List (KPoly K k) :=
  (List.range p.length).map fun g =>
    lincomb k ((List.range (p.length - g)).map fun m =>
      (((g + m).choose g : ℚ) * lo ^ m * h ^ g, coeffAt k p (g + m)))

theorem length_shift (k : ℕ) (lo h : ℚ) (p : List (KPoly K k)) : (shift k lo h p).length = p.length := by
  simp [shift]

theorem coeffAt_shift [ExactScalarVal K] (k : ℕ) (lo h : ℚ) (p : List (KPoly K k)) (y : Fin k → ℝ) (g : ℕ) (hg : g < p.length) :
    eval k (coeffAt k (shift k lo h p) g) y =
      ∑ m ∈ Finset.range (p.length - g),
        ((g + m).choose g : ℝ) * (lo : ℝ) ^ m * (h : ℝ) ^ g * eval k (coeffAt k p (g + m)) y := by
  have : coeffAt k (shift k lo h p) g = lincomb k ((List.range (p.length - g)).map fun m =>
      (((g + m).choose g : ℚ) * lo ^ m * h ^ g, coeffAt k p (g + m))) := by
    simp [coeffAt, shift, List.getD_eq_getElem?_getD, hg]
  rw [this, eval_lincomb, List.map_map, sum_map_range]
  apply Finset.sum_congr rfl
  intro m _
  simp

theorem horner_shift [ExactScalarVal K] (k : ℕ) (lo h : ℚ) (p : List (KPoly K k)) (y : Fin k → ℝ) (t : ℝ) :
    horner (fun q => eval k q y) ((lo : ℝ) + h * t) p = horner (fun q => eval k q y) t (shift k lo h p) := by
  rw [horner_eq_sum, horner_eq_sum, length_shift, taylor_shift]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.mem_range] at hg
  rw [cf_eq_eval, coeffAt_shift k lo h p y g hg]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [cf_eq_eval]

/-- The Bernstein coefficient i of a coefficient list of degree d = length - 1. -/
def bern (k : ℕ) (p : List (KPoly K k)) (i : ℕ) : KPoly K k :=
  lincomb k ((List.range (i + 1)).map fun j =>
    ((i.choose j : ℚ) / ((p.length - 1).choose j : ℚ), coeffAt k p j))

theorem eval_bern [ExactScalarVal K] (k : ℕ) (p : List (KPoly K k)) (y : Fin k → ℝ) (i : ℕ) :
    eval k (bern k p i) y = Bernstein.coeff (p.length - 1) (cf (fun q => eval k q y) p) i := by
  rw [bern, eval_lincomb, List.map_map, sum_map_range, Bernstein.coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp [cf_eq_eval]

/-! ### The box lower bound -/

def minList : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: rest => min a (minList (b :: rest))

theorem minList_le : ∀ (l : List ℚ), ∀ x ∈ l, minList l ≤ x
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; simp [minList, h]
  | a :: b :: rest, x, h => by
    rw [minList]
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (minList_le (b :: rest) x h)

/-- A lower bound of the polynomial on the box Π [lo_i, lo_i + h_i] (box i = (lo_i, h_i)):
shift the first variable to [0, 1], take its Bernstein coefficients (polynomials in the
remaining variables) and recurse; at the leaves, the rational lower enclosure. -/
def lower : (k : ℕ) → KPoly K k → (Fin k → ℚ × ℚ) → ℚ
  | 0, c, _ => @ExactScalarOps.lo K _ c
  | k + 1, p, box =>
    let q := shift k (box 0).1 (box 0).2 p
    minList ((List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box))

def InBox {k : ℕ} (box : Fin k → ℚ × ℚ) (y : Fin k → ℝ) : Prop :=
  ∀ i, ((box i).1 : ℝ) ≤ y i ∧ y i ≤ (box i).1 + (box i).2

theorem lower_le_eval [ExactScalarVal K] : ∀ (k : ℕ) (p : KPoly K k) (box : Fin k → ℚ × ℚ) (y : Fin k → ℝ),
    (∀ i, 0 ≤ (box i).2) → InBox box y → (lower k p box : ℝ) ≤ eval k p y
  | 0, c, _, _, _, _ => @ExactScalarVal.lo_le_val K _ _ c
  | k + 1, p, box, y, hh, hy => by
    set lo := (box 0).1
    set h := (box 0).2
    have h0 : (0 : ℝ) ≤ h := by exact_mod_cast hh 0
    obtain ⟨hlo, hhi⟩ := hy 0
    -- y 0 = lo + h t with t ∈ [0, 1].
    obtain ⟨t, ht0, ht1, hx⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y 0 = lo + h * t := by
      rcases h0.lt_or_eq with hp | hz
      · refine ⟨(y 0 - lo) / h, div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith), ?_⟩
        field_simp
        ring
      · exact ⟨0, le_refl _, zero_le_one, by rw [← hz] at hhi; linarith⟩
    have hyt : InBox (Fin.tail box) (Fin.tail y) := fun i => hy i.succ
    have hht : ∀ i, 0 ≤ (Fin.tail box i).2 := fun i => hh i.succ
    set q := shift k lo h (p : List (KPoly K k))
    show (minList ((List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box)) : ℝ) ≤
      horner (fun q => eval k q (Fin.tail y)) (y 0) (p : List (KPoly K k))
    rw [hx, horner_shift k lo h (p : List (KPoly K k)), horner_eq_sum]
    rcases Nat.eq_zero_or_pos q.length with hq | hq
    · rw [hq]
      simp [minList]
    obtain ⟨d, hd⟩ : ∃ d, q.length = d + 1 := ⟨q.length - 1, by omega⟩
    rw [hd]
    apply Bernstein.bernstein_lower d _ _ _ ht0 ht1
    intro i hi
    have hmem : lower k (bern k q i) (Fin.tail box) ∈
        (List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    have h1 := minList_le _ _ hmem
    rw [hd] at h1
    have h2 := lower_le_eval k (bern k q i) (Fin.tail box) (Fin.tail y) hht hyt
    rw [eval_bern, hd, Nat.add_sub_cancel] at h2
    calc _ ≤ ((lower k (bern k q i) (Fin.tail box) : ℚ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2

/-! ### Uniform degrees, padding, and the bound at given degrees -/

/-- The largest index with a nonzero coefficient plus one (0 for the zero list). -/
def trimLen {α : Type} (Z : α → Bool) : List α → ℕ
  | [] => 0
  | a :: as => let n := trimLen Z as; if n = 0 && Z a then 0 else n + 1

/-- The degree of p in variable i, ignoring zero coefficients (0 for the zero polynomial). -/
def degIn : (k : ℕ) → Fin k → KPoly K k → ℕ
  | k + 1, i, p => Fin.cases (motive := fun _ => ℕ)
      (trimLen (isZero k) (p : List (KPoly K k)) - 1)
      (fun j => ((p : List (KPoly K k)).map (degIn k j)).foldr max 0) i

/-- Pads a coefficient list with zeros to length n. -/
def pad (k : ℕ) (n : ℕ) (p : List (KPoly K k)) : List (KPoly K k) :=
  p ++ List.replicate (n - p.length) (zero k)

theorem horner_pad [ExactScalarVal K] (k : ℕ) (n : ℕ) (p : List (KPoly K k)) (y : Fin k → ℝ) (x : ℝ) :
    horner (fun q => eval k q y) x (pad k n p) = horner (fun q => eval k q y) x p := by
  rw [pad, horner_append]
  have : horner (fun q => eval k q y) x (List.replicate (n - p.length) (zero (K := K) k)) = 0 := by
    induction (n - p.length) with
    | zero => rfl
    | succ m ih => rw [List.replicate_succ, horner_cons, eval_zero, ih]; ring
  rw [this]; ring

/-- `lower` with every coefficient list padded to the given degrees (so that the
Bernstein degree in each variable is the same in every branch, as in capcert's
dense tensors). -/
def lowerDeg : (k : ℕ) → (Fin k → ℕ) → KPoly K k → (Fin k → ℚ × ℚ) → ℚ
  | 0, _, c, _ => @ExactScalarOps.lo K _ c
  | k + 1, deg, p, box =>
    let q := shift k (box 0).1 (box 0).2 (pad k (deg 0 + 1) (p : List (KPoly K k)))
    minList ((List.range q.length).map fun i => lowerDeg k (Fin.tail deg) (bern k q i) (Fin.tail box))

theorem lowerDeg_le_eval [ExactScalarVal K] : ∀ (k : ℕ) (deg : Fin k → ℕ) (p : KPoly K k) (box : Fin k → ℚ × ℚ) (y : Fin k → ℝ),
    (∀ i, 0 ≤ (box i).2) → InBox box y → (lowerDeg k deg p box : ℝ) ≤ eval k p y
  | 0, _, c, _, _, _, _ => @ExactScalarVal.lo_le_val K _ _ c
  | k + 1, deg, p, box, y, hh, hy => by
    set lo := (box 0).1
    set h := (box 0).2
    have h0 : (0 : ℝ) ≤ h := by exact_mod_cast hh 0
    obtain ⟨hlo, hhi⟩ := hy 0
    obtain ⟨t, ht0, ht1, hx⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y 0 = lo + h * t := by
      rcases h0.lt_or_eq with hp | hz
      · refine ⟨(y 0 - lo) / h, div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith), ?_⟩
        field_simp
        ring
      · exact ⟨0, le_refl _, zero_le_one, by rw [← hz] at hhi; linarith⟩
    have hyt : InBox (Fin.tail box) (Fin.tail y) := fun i => hy i.succ
    have hht : ∀ i, 0 ≤ (Fin.tail box i).2 := fun i => hh i.succ
    set q := shift k lo h (pad k (deg 0 + 1) (p : List (KPoly K k)))
    show (minList ((List.range q.length).map fun i => lowerDeg k (Fin.tail deg) (bern k q i) (Fin.tail box)) : ℝ) ≤
      horner (fun q => eval k q (Fin.tail y)) (y 0) (p : List (KPoly K k))
    rw [← horner_pad k (deg 0 + 1) (p : List (KPoly K k)), hx, horner_shift, horner_eq_sum]
    rcases Nat.eq_zero_or_pos q.length with hq | hq
    · rw [hq]
      simp [minList]
    obtain ⟨d, hd⟩ : ∃ d, q.length = d + 1 := ⟨q.length - 1, by omega⟩
    rw [hd]
    apply Bernstein.bernstein_lower d _ _ _ ht0 ht1
    intro i hi
    have hmem : lowerDeg k (Fin.tail deg) (bern k q i) (Fin.tail box) ∈
        (List.range q.length).map fun i => lowerDeg k (Fin.tail deg) (bern k q i) (Fin.tail box) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    have h1 := minList_le _ _ hmem
    rw [hd] at h1
    have h2 := lowerDeg_le_eval k (Fin.tail deg) (bern k q i) (Fin.tail box) (Fin.tail y) hht hyt
    rw [eval_bern, hd, Nat.add_sub_cancel] at h2
    calc _ ≤ ((lowerDeg k (Fin.tail deg) (bern k q i) (Fin.tail box) : ℚ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2

/-- Divides out the largest power of y_i (at most `fuel`) that divides p. -/
def divOut (k : ℕ) (i : Fin k) : ℕ → KPoly K k → KPoly K k
  | 0, p => p
  | fuel + 1, p => if isZero k p then p else
      match divVar k i 1 p with
      | some q => divOut k i fuel q
      | none => p

theorem eval_divOut [ExactScalarVal K] (k : ℕ) (i : Fin k) (y : Fin k → ℝ) :
    ∀ (fuel : ℕ) (p : KPoly K k), ∃ m : ℕ, eval k p y = y i ^ m * eval k (divOut k i fuel p) y
  | 0, p => ⟨0, by simp [divOut]⟩
  | fuel + 1, p => by
    unfold divOut
    split_ifs with hz
    · exact ⟨0, by simp⟩
    · split
      · next q hq =>
        obtain ⟨m, hm⟩ := eval_divOut k i y fuel q
        exact ⟨m + 1, by rw [eval_divVar k i 1 p q y hq, hm, pow_succ]; ring⟩
      · exact ⟨0, by simp⟩

end KPoly

end Noperts.Pipeline
