module

public import Pipeline.KPoly

@[expose] public section

/-!
# Witness polynomials of balanced cap certificates

A chart of a cap certificate is a polynomial map y ↦ (u(y), w(y)) from a box
in ℝ⁵ to views u and Cayley vectors w (`Pipeline.CapPoly`, there over `IcoQ`;
here over any exact scalar field, `KPoly`). A balanced witness has contacts
k: an inner vertex `v_{i_k}`, a direction `c_k(μ) = c₀ + μ c₁` (μ the chart
variable 0) with `d_k = u × c_k`, and a weight `λ_k` (1 for a pair of
opposite directions; for three contacts the Cramer weight
`s (c_{k+1} × c_{k+2}) · u`). For a choice of outer vertices `v_{j_k}`, the
witness polynomial is

  P = Σ_k λ_k (N(w) v_{i_k} · d_k − D(w) (v_{j_k} · d_k)),
  N(w) v = (1 − |w|²) v + 2 (w·v) w + 2 w × v,  D(w) = 1 + |w|²,

(`balancedPoly`), and evaluating it gives the real expression
(`eval_balancedPoly`). N(w)/D(w) is the Cayley rotation, so P ≥ 0 with
λ_k ≥ 0 says Σ λ_k ((R v_{i_k}) · d_k − v_{j_k} · d_k) ≥ 0.
-/

namespace Noperts.Pipeline

namespace KCap

variable {K : Type} [ExactScalarOps K]

/-- Polynomial vectors in the 5 chart variables. -/
abbrev PVec (K : Type) := Fin 3 → KPoly K 5

/-- Exact vectors. -/
abbrev KVec (K : Type) := Fin 3 → K

/-- Real 3-vector helpers (on `Fin 3 → ℝ`). -/
def rdot (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def rcross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

namespace PVec

noncomputable def eval [ExactScalarVal K] (p : PVec K) (y : Fin 5 → ℝ) : Fin 3 → ℝ :=
  fun i => KPoly.eval 5 (p i) y

def const (v : KVec K) : PVec K := fun i => KPoly.const 5 (v i)
def add (p q : PVec K) : PVec K := fun i => KPoly.add 5 (p i) (q i)
def sub (p q : PVec K) : PVec K := fun i => KPoly.sub 5 (p i) (q i)
def smul (a : KPoly K 5) (p : PVec K) : PVec K := fun i => KPoly.mul 5 a (p i)
def dot (p q : PVec K) : KPoly K 5 :=
  KPoly.add 5 (KPoly.mul 5 (p 0) (q 0)) (KPoly.add 5 (KPoly.mul 5 (p 1) (q 1)) (KPoly.mul 5 (p 2) (q 2)))
def cross (p q : PVec K) : PVec K :=
  ![KPoly.sub 5 (KPoly.mul 5 (p 1) (q 2)) (KPoly.mul 5 (p 2) (q 1)),
    KPoly.sub 5 (KPoly.mul 5 (p 2) (q 0)) (KPoly.mul 5 (p 0) (q 2)),
    KPoly.sub 5 (KPoly.mul 5 (p 0) (q 1)) (KPoly.mul 5 (p 1) (q 0))]

noncomputable def kval [ExactScalarVal K] (v : KVec K) : Fin 3 → ℝ := fun i => ExactScalarVal.val (v i)

theorem eval_const [ExactScalarVal K] (v : KVec K) (y : Fin 5 → ℝ) : (const v).eval y = kval v := by
  funext i; simp [eval, const, kval, KPoly.eval_const]

theorem eval_add [ExactScalarVal K] (p q : PVec K) (y : Fin 5 → ℝ) :
    (add p q).eval y = p.eval y + q.eval y := by
  funext i; simp [eval, add, KPoly.eval_add]

theorem eval_sub [ExactScalarVal K] (p q : PVec K) (y : Fin 5 → ℝ) :
    (sub p q).eval y = p.eval y - q.eval y := by
  funext i; simp [eval, sub, KPoly.eval_sub]

theorem eval_smul [ExactScalarVal K] (a : KPoly K 5) (p : PVec K) (y : Fin 5 → ℝ) :
    (smul a p).eval y = KPoly.eval 5 a y • p.eval y := by
  funext i; simp [eval, smul, KPoly.eval_mul]

theorem eval_dot [ExactScalarVal K] (p q : PVec K) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (dot p q) y = rdot (p.eval y) (q.eval y) := by
  simp [dot, rdot, eval, KPoly.eval_add, KPoly.eval_mul]
  ring

theorem eval_cross [ExactScalarVal K] (p q : PVec K) (y : Fin 5 → ℝ) :
    (cross p q).eval y = rcross (p.eval y) (q.eval y) := by
  funext i
  fin_cases i <;> simp [cross, rcross, eval, KPoly.eval_sub, KPoly.eval_mul]

end PVec

open PVec

def kOne : KPoly K 5 := KPoly.const 5 ExactScalarOps.one
def kTwo : KPoly K 5 := KPoly.add 5 kOne kOne

theorem eval_kOne [ExactScalarVal K] (y : Fin 5 → ℝ) : KPoly.eval 5 (kOne (K := K)) y = 1 := by
  simp [kOne, KPoly.eval_const, ExactScalarVal.val_one]

theorem eval_kTwo [ExactScalarVal K] (y : Fin 5 → ℝ) : KPoly.eval 5 (kTwo (K := K)) y = 2 := by
  simp [kTwo, KPoly.eval_add, eval_kOne]; norm_num

/-- N(w) v = (1 − |w|²) v + 2 (w·v) w + 2 w × v. -/
def cayleyNum (w : PVec K) (v : KVec K) : PVec K :=
  let cv := PVec.const v
  PVec.add (PVec.smul (KPoly.sub 5 kOne (PVec.dot w w)) cv)
    (PVec.add (PVec.smul (KPoly.mul 5 kTwo (PVec.dot w cv)) w) (PVec.smul kTwo (PVec.cross w cv)))

/-- D(w) = 1 + |w|². -/
def cayleyDen (w : PVec K) : KPoly K 5 := KPoly.add 5 kOne (PVec.dot w w)

/-- The real numerator of the Cayley rotation. -/
def rcayleyNum (w v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 - rdot w w) • v + (2 * rdot w v) • w + (2 : ℝ) • rcross w v

theorem eval_cayleyNum [ExactScalarVal K] (w : PVec K) (v : KVec K) (y : Fin 5 → ℝ) :
    (cayleyNum w v).eval y = rcayleyNum (w.eval y) (kval v) := by
  simp only [cayleyNum, rcayleyNum, PVec.eval_add, PVec.eval_smul, KPoly.eval_sub, KPoly.eval_mul,
    PVec.eval_dot, PVec.eval_cross, PVec.eval_const, eval_kOne, eval_kTwo]
  rw [add_assoc]

theorem eval_cayleyDen [ExactScalarVal K] (w : PVec K) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (cayleyDen w) y = 1 + rdot (w.eval y) (w.eval y) := by
  simp [cayleyDen, KPoly.eval_add, eval_kOne, PVec.eval_dot]

/-- A contact: inner vertex index, direction `c0 + μ c1`, and the candidate
outer support set (vertex indices). -/
structure Contact (K : Type) where
  inner : ℕ
  c0 : KVec K
  c1 : KVec K
  support : List ℕ

/-- The direction polynomial vector `c0 + μ c1` (μ = chart variable 0). -/
def Contact.dir (c : Contact K) : PVec K :=
  PVec.add (PVec.const c.c0) (PVec.smul (KPoly.var 5 0) (PVec.const c.c1))

/-- `d = u × c(μ)`. -/
def Contact.d (c : Contact K) (u : PVec K) : PVec K := PVec.cross u c.dir

/-- The Cramer weight of contact `k` of three: `s (c_{k+1} × c_{k+2}) · u`. -/
def cramerWeight (cs : Fin 3 → Contact K) (s : ℚ) (u : PVec K) (k : Fin 3) : KPoly K 5 :=
  KPoly.scale 5 s (PVec.dot (PVec.cross (cs (k + 1)).dir (cs (k + 2)).dir) u)

/-- One term `λ (N(w) v_i · d − D(w) (v_j · d))`. -/
def contactTerm (lam : KPoly K 5) (u w : PVec K) (V : ℕ → KVec K) (c : Contact K) (j : ℕ) :
    KPoly K 5 :=
  let d := c.d u
  KPoly.mul 5 lam (KPoly.sub 5 (PVec.dot (cayleyNum w (V c.inner)) d)
    (KPoly.mul 5 (cayleyDen w) (PVec.dot (PVec.const (V j)) d)))

theorem eval_contactTerm [ExactScalarVal K] (lam : KPoly K 5) (u w : PVec K) (V : ℕ → KVec K)
    (c : Contact K) (j : ℕ) (y : Fin 5 → ℝ) :
    KPoly.eval 5 (contactTerm lam u w V c j) y =
      KPoly.eval 5 lam y *
        (rdot (rcayleyNum (w.eval y) (kval (V c.inner))) (rcross (u.eval y) ((c.dir).eval y)) -
          (1 + rdot (w.eval y) (w.eval y)) * rdot (kval (V j)) (rcross (u.eval y) ((c.dir).eval y))) := by
  simp only [contactTerm, Contact.d, KPoly.eval_mul, KPoly.eval_sub, PVec.eval_dot, PVec.eval_cross,
    eval_cayleyNum, eval_cayleyDen, PVec.eval_const]

end KCap

end Noperts.Pipeline

end
