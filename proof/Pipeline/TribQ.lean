module

public import Basic

@[expose] public section

/-!
# The tribonacci constant and the field ℚ(t)

The tribonacci constant `t ≈ 1.83929` is the unique real root in [1, 2] of
`x³ − x² − x − 1` (`tribonacci`, defined without radicals; `tribonacci_enclosure`
to 10⁻³¹). The snub cube is the O-orbit of `(t, 1, −t²)` (Wikipedia's
chirality), so its exact coordinates lie in the field ℚ(t).

`TribQ` is `a + b t + c t²` with `a, b, c ∈ ℚ`; the product reduces
`t³ = t² + t + 1` and `t⁴ = 2t² + 2t + 1`. `val` is the real value; addition
and multiplication are compatible with it, and `lo`/`hi` are rational
enclosures. It is the exact arithmetic of the snub cube's cap certificates
(as `IcoQ`, over ℚ(√5, sin 72°), is the deltoidal hexecontahedron's).
-/

namespace Noperts.Pipeline

/-! ### The tribonacci constant -/

/-- The cubic whose root in [1, 2] is the tribonacci constant. -/
def tribonacciPolynomial (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - x - 1

theorem tribonacciPolynomial_continuous : Continuous tribonacciPolynomial := by
  unfold tribonacciPolynomial
  fun_prop

theorem tribonacciPolynomial_strictMonoOn :
    StrictMonoOn tribonacciPolynomial (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hxy_pos : 0 < y - x := sub_pos.mpr hxy
  have hfactor :
      tribonacciPolynomial y - tribonacciPolynomial x =
        (y - x) * (x ^ 2 + x * y + y ^ 2 - x - y - 1) := by
    simp only [tribonacciPolynomial]
    ring
  have hy1 : 1 < y := hx.trans_lt hxy
  have hxy0 : 0 ≤ x * y - 1 := by
    have hmul : 1 * 1 ≤ x * y := mul_le_mul hx hy (by norm_num) (by linarith)
    nlinarith
  have hsecond : 0 < x ^ 2 + x * y + y ^ 2 - x - y - 1 := by nlinarith
  have hdifference : 0 < tribonacciPolynomial y - tribonacciPolynomial x := by
    rw [hfactor]
    positivity
  linarith

theorem exists_unique_tribonacci :
    ∃! x : ℝ, x ∈ Set.Icc 1 2 ∧ tribonacciPolynomial x = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (tribonacciPolynomial 1) (tribonacciPolynomial 2) := by
    norm_num [tribonacciPolynomial]
  obtain ⟨x, hx, hroot⟩ :=
    intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num)
      tribonacciPolynomial_continuous.continuousOn hzero
  refine ⟨x, ⟨hx, hroot⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · have := tribonacciPolynomial_strictMonoOn hy.1.1 hx.1 hyx
    linarith [hroot, hy.2]
  · have := tribonacciPolynomial_strictMonoOn hx.1 hy.1.1 hxy
    linarith [hroot, hy.2]

/-- The tribonacci constant. -/
noncomputable def tribonacci : ℝ := Classical.choose exists_unique_tribonacci

theorem tribonacci_mem_Icc : tribonacci ∈ Set.Icc (1 : ℝ) 2 :=
  (Classical.choose_spec exists_unique_tribonacci).1.1

theorem tribonacci_root : tribonacciPolynomial tribonacci = 0 :=
  (Classical.choose_spec exists_unique_tribonacci).1.2

theorem tribonacci_cube : tribonacci ^ 3 = tribonacci ^ 2 + tribonacci + 1 := by
  have h := tribonacci_root
  simp only [tribonacciPolynomial] at h
  linarith

theorem tribonacci_pos : 0 < tribonacci := lt_of_lt_of_le zero_lt_one tribonacci_mem_Icc.1

/-- The rational enclosure of the tribonacci constant (width 10⁻³¹). -/
def tribLo : ℚ := 18392867552141611325518525646532 / 10 ^ 31
def tribHi : ℚ := 18392867552141611325518525646533 / 10 ^ 31

theorem tribonacci_enclosure : (tribLo : ℝ) ≤ tribonacci ∧ tribonacci ≤ tribHi := by
  constructor
  · by_contra h
    have ht : tribonacci < (tribLo : ℝ) := lt_of_not_ge h
    have hlo_mem : (tribLo : ℝ) ∈ Set.Ici 1 := by norm_num [tribLo]
    have hmono := tribonacciPolynomial_strictMonoOn tribonacci_mem_Icc.1 hlo_mem ht
    rw [tribonacci_root] at hmono
    have hlo : tribonacciPolynomial (tribLo : ℝ) < 0 := by
      norm_num [tribonacciPolynomial, tribLo]
    linarith
  · by_contra h
    have ht : (tribHi : ℝ) < tribonacci := lt_of_not_ge h
    have hhi_mem : (tribHi : ℝ) ∈ Set.Ici 1 := by norm_num [tribHi]
    have hmono := tribonacciPolynomial_strictMonoOn hhi_mem tribonacci_mem_Icc.1 ht
    rw [tribonacci_root] at hmono
    have hhi : 0 < tribonacciPolynomial (tribHi : ℝ) := by
      norm_num [tribonacciPolynomial, tribHi]
    linarith

/-! ### The field ℚ(t) -/

/-- `a + b t + c t²`, t the tribonacci constant. -/
structure TribQ where
  a : ℚ
  b : ℚ
  c : ℚ
deriving DecidableEq, Repr

namespace TribQ

def zero : TribQ := ⟨0, 0, 0⟩
def one : TribQ := ⟨1, 0, 0⟩
def ofRat (q : ℚ) : TribQ := ⟨q, 0, 0⟩
/-- The tribonacci constant itself. -/
def t : TribQ := ⟨0, 1, 0⟩

def add (x y : TribQ) : TribQ := ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩
def neg (x : TribQ) : TribQ := ⟨-x.a, -x.b, -x.c⟩
def sub (x y : TribQ) : TribQ := add x (neg y)
def scale (k : ℚ) (x : TribQ) : TribQ := ⟨k * x.a, k * x.b, k * x.c⟩

/-- The product, with `t³ = t² + t + 1` and `t⁴ = 2t² + 2t + 1`. -/
def mul (x y : TribQ) : TribQ :=
  let p3 := x.b * y.c + x.c * y.b
  let p4 := x.c * y.c
  ⟨x.a * y.a + p3 + p4,
   x.a * y.b + x.b * y.a + p3 + 2 * p4,
   x.a * y.c + x.b * y.b + x.c * y.a + p3 + 2 * p4⟩

instance : Add TribQ := ⟨add⟩
instance : Neg TribQ := ⟨neg⟩
instance : Sub TribQ := ⟨sub⟩
instance : Mul TribQ := ⟨mul⟩
instance : Zero TribQ := ⟨zero⟩
instance : One TribQ := ⟨one⟩

/-- The value in ℝ. -/
noncomputable def val (x : TribQ) : ℝ := x.a + x.b * tribonacci + x.c * tribonacci ^ 2

@[simp] theorem val_add (x y : TribQ) : val (x + y) = val x + val y := by
  show val (add x y) = _
  simp only [val, add]; push_cast; ring

@[simp] theorem val_neg (x : TribQ) : val (-x) = -val x := by
  show val (neg x) = _
  simp only [val, neg]; push_cast; ring

@[simp] theorem val_sub (x y : TribQ) : val (x - y) = val x - val y := by
  show val (add x (neg y)) = _
  simp only [val, add, neg]; push_cast; ring

@[simp] theorem val_scale (k : ℚ) (x : TribQ) : val (scale k x) = k * val x := by
  simp only [val, scale]; push_cast; ring

@[simp] theorem val_mul (x y : TribQ) : val (x * y) = val x * val y := by
  show val (mul x y) = _
  have h3 := tribonacci_cube
  simp only [val, mul]
  push_cast
  linear_combination (-((x.b : ℝ) * y.c + x.c * y.b + x.c * y.c + x.c * y.c * tribonacci)) * h3

@[simp] theorem val_zero : val 0 = 0 := by
  show val zero = 0
  simp [val, zero]

@[simp] theorem val_one : val 1 = 1 := by
  show val one = 1
  simp [val, one]

@[simp] theorem val_ofRat (q : ℚ) : val (ofRat q) = q := by simp [val, ofRat]

@[simp] theorem val_t : val t = tribonacci := by simp [val, t]

/-! ### Rational enclosures -/

def loMul (k l u : ℚ) : ℚ := if 0 ≤ k then k * l else k * u
def hiMul (k l u : ℚ) : ℚ := if 0 ≤ k then k * u else k * l

theorem loMul_le (k : ℚ) {l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ u) :
    ((loMul k l u : ℚ) : ℝ) ≤ k * x := by
  unfold loMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hu (by exact_mod_cast (le_of_lt (not_le.mp hk)))

theorem le_hiMul (k : ℚ) {l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ u) :
    k * x ≤ ((hiMul k l u : ℚ) : ℝ) := by
  unfold hiMul
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hu (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hl (by exact_mod_cast (le_of_lt (not_le.mp hk)))

theorem tribonacci_sq_enclosure :
    ((tribLo * tribLo : ℚ) : ℝ) ≤ tribonacci ^ 2 ∧ tribonacci ^ 2 ≤ ((tribHi * tribHi : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := tribonacci_enclosure
  have hl0 : (0 : ℝ) ≤ tribLo := by norm_num [tribLo]
  push_cast
  constructor <;> nlinarith

def lo (x : TribQ) : ℚ :=
  x.a + loMul x.b tribLo tribHi + loMul x.c (tribLo * tribLo) (tribHi * tribHi)

def hi (x : TribQ) : ℚ :=
  x.a + hiMul x.b tribLo tribHi + hiMul x.c (tribLo * tribLo) (tribHi * tribHi)

theorem lo_le_val (x : TribQ) : (lo x : ℝ) ≤ val x := by
  obtain ⟨hl, hu⟩ := tribonacci_enclosure
  obtain ⟨hl2, hu2⟩ := tribonacci_sq_enclosure
  have hb := loMul_le x.b hl hu
  have hc := loMul_le x.c hl2 hu2
  simp only [lo, val]
  push_cast at hb hc ⊢
  linarith

theorem val_le_hi (x : TribQ) : val x ≤ (hi x : ℝ) := by
  obtain ⟨hl, hu⟩ := tribonacci_enclosure
  obtain ⟨hl2, hu2⟩ := tribonacci_sq_enclosure
  have hb := le_hiMul x.b hl hu
  have hc := le_hiMul x.c hl2 hu2
  simp only [hi, val]
  push_cast at hb hc ⊢
  linarith

end TribQ

end Noperts.Pipeline

end
