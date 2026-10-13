module

public import Pipeline.KCapChart
public import Pipeline.KCapWitness

@[expose] public section

/-!
# Checking a leaf of a balanced cap certificate

A leaf of a chart's certificate (`search/sc/sccapcert.cc --export`) is a
balanced witness: contacts k < n (n = 2 or 3) with edge directions
c_k = v_{b_k} − v_{a_k}, outer candidate sets S_k, and per tuple of outer
choices the inner choices. `leafOk` checks on the leaf box, exactly:

* the shape: n = 2 with the second edge the first reversed (weights 1), or
  n = 3 with the Cramer weights λ_k = s (c_{k+1} × c_{k+2}) · u ≥ 0;
* strictness: Σ_k λ_k |d_k|² > 0, d_k = u × c_k;
* dominance: every vertex outside S_k is below S_k's first vertex along d_k;
* every tuple j ∈ S_0 × … × S_{n−1}, with its inner choices i:
  P = Σ_k λ_k (N(w) v_{i_k} · d_k − D(w) v_{j_k} · d_k), divided by the
  largest powers of μ (and of t in the tie cones, of p₀ in the identity
  cones) that divide it, has a nonnegative Bernstein bound.

`leafOk_sound`: then no pose whose view is a positive multiple of the chart's
u(y) and whose relative rotation is the Cayley rotation of w(y) is Rupert,
for every y of the box (`balanced_pose_not_rupert`).
-/

namespace Noperts.Pipeline

namespace KCap

open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K]

abbrev Box := Fin 5 → ℚ × ℚ

/-! ### Exact vectors -/

def ksub (a b : K) : K := ExactScalarOps.add a (ExactScalarOps.scale (-1) b)

def vsub (a b : KVec K) : KVec K := fun i => ksub (a i) (b i)

def vcross (a b : KVec K) : KVec K :=
  ![ksub (ExactScalarOps.mul (a 1) (b 2)) (ExactScalarOps.mul (a 2) (b 1)),
    ksub (ExactScalarOps.mul (a 2) (b 0)) (ExactScalarOps.mul (a 0) (b 2)),
    ksub (ExactScalarOps.mul (a 0) (b 1)) (ExactScalarOps.mul (a 1) (b 0))]

theorem val_ksub [ExactScalarVal K] (a b : K) :
    ExactScalarVal.val (ksub a b) = ExactScalarVal.val a - ExactScalarVal.val b := by
  simp [ksub, ExactScalarVal.val_add, ExactScalarVal.val_scale]; ring

theorem kval_vsub [ExactScalarVal K] (a b : KVec K) : kval (vsub a b) = kval a - kval b := by
  funext i; simp [kval, vsub, val_ksub]

theorem kval_vcross [ExactScalarVal K] (a b : KVec K) : kval (vcross a b) = rcross (kval a) (kval b) := by
  funext i
  fin_cases i <;> simp [kval, vcross, rcross, val_ksub, ExactScalarVal.val_mul]

def vertex (V : Array (KVec K)) (i : ℕ) : KVec K := V.getD i (fun _ => ExactScalarOps.zero)

theorem kval_vertex_mem [ExactScalarVal K] (V : Array (KVec K)) (i : ℕ) (h : i < V.size) :
    kval (vertex V i) ∈ V.toList.map kval := by
  simp only [vertex, Array.getD, h, dite_true]
  exact List.mem_map.mpr ⟨V[i], Array.mem_toList_iff.mpr (Array.getElem_mem h), rfl⟩

/-! ### Chart data and leaves -/

/-- The chart's view and Cayley vector, the Cayley denominator and the numerators N(w) v. -/
structure ChartData (K : Type) where
  u : PVec K
  w : PVec K
  D : KPoly K 5
  N : Array (PVec K)

def chartData (fr : Frame K) (pr : Params) (id : ChartId) (V : Array (KVec K)) : ChartData K :=
  let w := chartW fr pr id
  ⟨chartU fr pr id, w, cayleyDen w, V.map (cayleyNum w)⟩

/-- A leaf: the Cramer sign, the contact edges (a, b), the outer sets, and per tuple (in
`tuples` order) the inner choices. -/
structure Leaf where
  s : ℚ
  edges : List (ℕ × ℕ)
  outer : List (List ℕ)
  inner : List (List ℕ)
deriving Inhabited

def Leaf.n (l : Leaf) : ℕ := l.edges.length

/-- The tuples of S_0 × … × S_{n−1}, index 0 fastest. -/
def tuples : (n : ℕ) → (Fin n → List ℕ) → List (Fin n → ℕ)
  | 0, _ => [Fin.elim0]
  | n + 1, S => (tuples n (Fin.tail S)).flatMap fun t => (S 0).map fun j => Fin.cons j t

theorem mem_tuples : ∀ (n : ℕ) (S : Fin n → List ℕ) (j : Fin n → ℕ), (∀ k, j k ∈ S k) → j ∈ tuples n S
  | 0, _, j, _ => by simp [tuples]; funext k; exact k.elim0
  | n + 1, S, j, h => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    refine ⟨Fin.tail j, mem_tuples n (Fin.tail S) (Fin.tail j) (fun k => h k.succ), j 0, h 0, ?_⟩
    exact Fin.cons_self_tail j

variable (V : Array (KVec K)) (l : Leaf)

def Leaf.edge (k : ℕ) : ℕ × ℕ := l.edges.getD k (0, 0)

def Leaf.dir (k : ℕ) : KVec K := vsub (vertex V (l.edge k).2) (vertex V (l.edge k).1)

def Leaf.S (k : ℕ) : List ℕ := l.outer.getD k []

/-- The weight of contact k: 1 (pairs), the Cramer weight (triples). -/
def Leaf.lam (cd : ChartData K) (k : ℕ) : KPoly K 5 :=
  if l.n = 2 then kOne
  else KPoly.scale 5 l.s (PVec.dot (PVec.const (vcross (l.dir V ((k + 1) % 3)) (l.dir V ((k + 2) % 3)))) cd.u)

def Leaf.d (cd : ChartData K) (k : ℕ) : PVec K := PVec.cross cd.u (PVec.const (l.dir V k))

/-- λ_k d_k. -/
def Leaf.L (cd : ChartData K) (k : ℕ) : PVec K := PVec.smul (l.lam V cd k) (l.d V cd k)

def numAt (cd : ChartData K) (i : ℕ) : PVec K := cd.N.getD i (fun _ => KPoly.zero 5)

/-- The tuple's polynomial for outer choices j and inner choices i. -/
def Leaf.tuplePoly (cd : ChartData K) (Ls : List (PVec K)) (j i : ℕ → ℕ) : KPoly K 5 :=
  (List.range l.n).foldr (fun k acc =>
    KPoly.add 5 (KPoly.sub 5 (PVec.dot (numAt cd (i k)) (Ls.getD k (fun _ => KPoly.zero 5)))
      (KPoly.mul 5 cd.D (PVec.dot (PVec.const (vertex V (j k))) (Ls.getD k (fun _ => KPoly.zero 5))))) acc)
    (KPoly.zero 5)

def degs (q : KPoly K 5) : Fin 5 → ℕ := fun i => KPoly.degIn 5 i q

def nonnegOn (q : KPoly K 5) (box : Box) : Bool := decide (0 ≤ KPoly.lowerDeg 5 (degs q) q box)

def posOn (q : KPoly K 5) (box : Box) : Bool := decide (0 < KPoly.lowerDeg 5 (degs q) q box)

/-- Division by the chart's blow-up variables. -/
def reduce (id : ChartId) (q : KPoly K 5) : KPoly K 5 :=
  let q0 := KPoly.divOut 5 0 64 q
  match id.kind with
  | .cone => KPoly.divOut 5 2 64 q0
  | .tcone => KPoly.divOut 5 1 64 q0
  | _ => q0

/-- The shape: a reversed pair, or a triple. -/
def Leaf.shapeOk : Bool :=
  (l.n = 2 && l.edge 1 = ((l.edge 0).2, (l.edge 0).1)) || l.n = 3

def Leaf.indicesOk : Bool :=
  l.outer.length = l.n && l.edges.all (fun e => e.1 < V.size && e.2 < V.size) &&
    l.outer.all (fun S => !S.isEmpty && S.all (· < V.size)) &&
    l.inner.all (fun it => it.length = l.n && it.all (· < V.size))

def Leaf.check (cd : ChartData K) (id : ChartId) (box : Box) : Bool :=
  let n := l.n
  let Ls := (List.range n).map (l.L V cd)
  l.shapeOk && l.indicesOk V &&
  (n = 2 || (List.range 3).all fun k => nonnegOn (l.lam V cd k) box) &&
  posOn ((List.range n).foldr (fun k acc => KPoly.add 5 (PVec.dot (Ls.getD k (fun _ => KPoly.zero 5)) (l.d V cd k)) acc)
    (KPoly.zero 5)) box &&
  (List.range n).all (fun k => (List.range V.size).all fun j =>
    (l.S k).contains j || nonnegOn (PVec.dot (l.d V cd k) (PVec.const (vsub (vertex V ((l.S k).headD 0)) (vertex V j)))) box) &&
  let T := tuples n (fun k => l.S k)
  T.length = l.inner.length &&
  (T.zip l.inner).all fun (jt, it) =>
    nonnegOn (reduce id (l.tuplePoly V cd Ls (fun k => if h : k < n then jt ⟨k, h⟩ else 0) (fun k => it.getD k 0))) box

end KCap

end Noperts.Pipeline

namespace Noperts.Pipeline

namespace KCap

open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K] [ExactScalarVal K]

/-! ### Soundness -/

theorem rdot_smul_right (a d : Fin 3 → ℝ) (c : ℝ) : rdot a (c • d) = c * rdot a d := by
  simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring

theorem rdot_sub_left (a b d : Fin 3 → ℝ) : rdot (a - b) d = rdot a d - rdot b d := by
  simp only [rdot, Pi.sub_apply]; ring

theorem eval_lowerDeg_nonneg {q : KPoly K 5} {box : Box} (h : nonnegOn q box = true)
    (hw : ∀ i, 0 ≤ (box i).2) {y : Fin 5 → ℝ} (hy : KPoly.InBox box y) : 0 ≤ KPoly.eval 5 q y := by
  have hl := KPoly.lowerDeg_le_eval 5 (degs q) q box y hw hy
  have : (0 : ℚ) ≤ KPoly.lowerDeg 5 (degs q) q box := of_decide_eq_true h
  exact le_trans (by exact_mod_cast this) hl

theorem eval_lowerDeg_pos {q : KPoly K 5} {box : Box} (h : posOn q box = true)
    (hw : ∀ i, 0 ≤ (box i).2) {y : Fin 5 → ℝ} (hy : KPoly.InBox box y) : 0 < KPoly.eval 5 q y := by
  have hl := KPoly.lowerDeg_le_eval 5 (degs q) q box y hw hy
  have : (0 : ℚ) < KPoly.lowerDeg 5 (degs q) q box := of_decide_eq_true h
  exact lt_of_lt_of_le (by exact_mod_cast this) hl

theorem eval_reduce_nonneg (id : ChartId) (q : KPoly K 5) (y : Fin 5 → ℝ) (h0 : 0 ≤ y 0)
    (h1 : id.kind = .tcone → 0 ≤ y 1) (h2 : id.kind = .cone → 0 ≤ y 2)
    (h : 0 ≤ KPoly.eval 5 (reduce id q) y) : 0 ≤ KPoly.eval 5 q y := by
  obtain ⟨m, hm⟩ := KPoly.eval_divOut 5 0 y 64 q
  rw [hm]
  apply mul_nonneg (pow_nonneg h0 m)
  unfold reduce at h
  cases hk : id.kind <;> simp only [hk] at h
  · exact h
  · exact h
  · obtain ⟨m2, hm2⟩ := KPoly.eval_divOut 5 2 y 64 (KPoly.divOut 5 0 64 q)
    rw [hm2]; exact mul_nonneg (pow_nonneg (h2 hk) m2) h
  · obtain ⟨m1, hm1⟩ := KPoly.eval_divOut 5 1 y 64 (KPoly.divOut 5 0 64 q)
    rw [hm1]; exact mul_nonneg (pow_nonneg (h1 hk) m1) h

theorem eval_foldr_add_init (f : ℕ → KPoly K 5) (y : Fin 5 → ℝ) : ∀ (l : List ℕ) (a : KPoly K 5),
    KPoly.eval 5 (l.foldr (fun k acc => KPoly.add 5 (f k) acc) a) y =
      KPoly.eval 5 (l.foldr (fun k acc => KPoly.add 5 (f k) acc) (KPoly.zero 5)) y + KPoly.eval 5 a y
  | [], a => by simp [KPoly.eval_zero]
  | b :: l, a => by
    simp only [List.foldr_cons, KPoly.eval_add, eval_foldr_add_init f y l a]; ring

theorem eval_foldr_add (n : ℕ) (f : ℕ → KPoly K 5) (y : Fin 5 → ℝ) :
    KPoly.eval 5 ((List.range n).foldr (fun k acc => KPoly.add 5 (f k) acc) (KPoly.zero 5)) y =
      ∑ k : Fin n, KPoly.eval 5 (f k) y := by
  rw [Fin.sum_univ_eq_sum_range (fun k => KPoly.eval 5 (f k) y)]
  induction n with
  | zero => simp [KPoly.eval_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, eval_foldr_add_init, ih, Finset.sum_range_succ]
    simp [KPoly.eval_add, KPoly.eval_zero]

theorem kval_dir (V : Array (KVec K)) (l : Leaf) (k : ℕ) :
    kval (l.dir V k) = kval (vertex V (l.edge k).2) - kval (vertex V (l.edge k).1) := by
  simp [Leaf.dir, kval_vsub]

theorem eval_d (V : Array (KVec K)) (l : Leaf) (cd : ChartData K) (k : ℕ) (y : Fin 5 → ℝ) :
    (l.d V cd k).eval y = rcross (cd.u.eval y) (kval (l.dir V k)) := by
  simp [Leaf.d, PVec.eval_cross, PVec.eval_const]

theorem eval_L (V : Array (KVec K)) (l : Leaf) (cd : ChartData K) (k : ℕ) (y : Fin 5 → ℝ) :
    (l.L V cd k).eval y = KPoly.eval 5 (l.lam V cd k) y • (l.d V cd k).eval y := by
  simp [Leaf.L, PVec.eval_smul]

theorem eval_numAt (fr : Frame K) (pr : Params) (id : ChartId) (V : Array (KVec K)) (i : ℕ) (h : i < V.size)
    (y : Fin 5 → ℝ) :
    (numAt (chartData fr pr id V) i).eval y =
      rcayleyNum ((chartW fr pr id).eval y) (kval (vertex V i)) := by
  have : numAt (chartData fr pr id V) i = cayleyNum (chartW fr pr id) (vertex V i) := by
    simp [numAt, chartData, vertex, Array.getD, h]
  rw [this, eval_cayleyNum]

theorem Ls_getD (V : Array (KVec K)) (l : Leaf) (cd : ChartData K) (n k : ℕ) (hk : k < n) :
    ((List.range n).map (l.L V cd)).getD k (fun _ => KPoly.zero 5) = l.L V cd k := by
  rw [List.getD_eq_getElem?_getD]
  simp [hk]

theorem eval_tuplePoly (fr : Frame K) (pr : Params) (id : ChartId) (V : Array (KVec K)) (l : Leaf)
    (j i : ℕ → ℕ) (hi : ∀ k < l.n, i k < V.size) (y : Fin 5 → ℝ) :
    let cd := chartData fr pr id V
    KPoly.eval 5 (l.tuplePoly V cd ((List.range l.n).map (l.L V cd)) j i) y =
      ∑ k : Fin l.n, KPoly.eval 5 (l.lam V cd k) y *
        (rdot (rcayleyNum ((chartW fr pr id).eval y) (kval (vertex V (i k)))) (rcross ((chartU fr pr id).eval y) (kval (l.dir V k))) -
          (1 + rdot ((chartW fr pr id).eval y) ((chartW fr pr id).eval y)) *
            rdot (kval (vertex V (j k))) (rcross ((chartU fr pr id).eval y) (kval (l.dir V k)))) := by
  intro cd
  unfold Leaf.tuplePoly
  rw [eval_foldr_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Ls_getD V l cd l.n k k.isLt]
  simp only [KPoly.eval_sub, KPoly.eval_mul, PVec.eval_dot, PVec.eval_const, eval_L, eval_d,
    rdot_smul_right]
  rw [eval_numAt fr pr id V (i k) (hi k k.isLt)]
  have hD : KPoly.eval 5 cd.D y = 1 + rdot ((chartW fr pr id).eval y) ((chartW fr pr id).eval y) := by
    simp [cd, chartData, eval_cayleyDen]
  have hu : cd.u = chartU fr pr id := rfl
  rw [hD, hu]
  ring

/-- The Cramer weights balance any three directions: Σ_k s ((c_{k+1} × c_{k+2}) · u) (u × c_k) = 0. -/
theorem cramer_balance (s : ℝ) (u : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ) :
    ∑ k : Fin 3, (s * rdot (rcross (c (k + 1)) (c (k + 2))) u) • rcross u (c k) = 0 := by
  funext i
  simp only [Fin.sum_univ_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  fin_cases i <;>
    simp [rcross, rdot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> ring

theorem rcross_neg_right (u c : Fin 3 → ℝ) : rcross u (-c) = -rcross u c := by
  funext i; fin_cases i <;> simp [rcross] <;> ring

theorem cramer3 (s : ℝ) (u c0 c1 c2 : Fin 3 → ℝ) :
    (s * rdot (rcross c1 c2) u) • rcross u c0 + (s * rdot (rcross c2 c0) u) • rcross u c1 +
      (s * rdot (rcross c0 c1) u) • rcross u c2 = 0 := by
  funext i
  fin_cases i <;> simp [rcross, rdot] <;> ring

theorem Leaf.check_sound (fr : Frame K) (pr : Params) (id : ChartId) (V : Array (KVec K)) (l : Leaf)
    (box : Box) (h : l.check V (chartData fr pr id V) id box = true) (hw : ∀ i, 0 ≤ (box i).2)
    (y : Fin 5 → ℝ) (hy : KPoly.InBox box y) (h0 : 0 ≤ y 0)
    (h1 : id.kind = .tcone → 0 ≤ y 1) (h2 : id.kind = .cone → 0 ≤ y 2)
    (S : Set ℝ³) (hS : S = convexHull ℝ {v | ∃ vj ∈ V.toList.map kval, v = Cap.toEuc vj})
    (p : MatrixPose) (ξ : ℝ) (hview : p.view = ξ • (chartU fr pr id).eval y)
    (hR : p.relativeRotation = cayleyMatrix ((chartW fr pr id).eval y 0) ((chartW fr pr id).eval y 1)
      ((chartW fr pr id).eval y 2)) :
    ¬ RupertPose p S := by
  set cd := chartData fr pr id V with hcd
  unfold Leaf.check at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hshape, hind⟩, hlamck⟩, hposck⟩, hdom⟩, hlen, htup⟩ := h
  set n := l.n with hn
  set u := (chartU fr pr id).eval y with hu
  set w := (chartW fr pr id).eval y with hw'
  -- Index facts.
  unfold Leaf.indicesOk at hind
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at hind
  obtain ⟨⟨⟨hol, hedges⟩, hout⟩, hinn⟩ := hind
  have hSk : ∀ k < n, l.S k ∈ l.outer := by
    intro k hk
    unfold Leaf.S
    rw [List.getD_eq_getElem?_getD]
    have : k < l.outer.length := by rw [hol]; exact hk
    simp [this, List.getElem_mem]
  have hSne : ∀ k < n, l.S k ≠ [] := fun k hk => (hout _ (hSk k hk)).1
  have hSv : ∀ k < n, ∀ j ∈ l.S k, j < V.size := fun k hk => (hout _ (hSk k hk)).2
  -- Real data.
  let c : ℕ → Fin 3 → ℝ := fun k => kval (l.dir V k)
  let lamR : ℕ → ℝ := fun k => KPoly.eval 5 (l.lam V cd k) y
  let f : ℕ → ℕ → ℝ := fun k j => rdot (kval (vertex V j)) (rcross u (c k))
  -- The outer maxima.
  have hjm : ∀ k : Fin n, ∃ jm ∈ l.S k, ∀ j' ∈ l.S k, f k j' ≤ f k jm := by
    intro k
    classical
    obtain ⟨jm, hjm, hmax⟩ := (l.S k).toFinset.exists_max_image (f k)
      (by
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hSne k k.isLt)
        exact ⟨a, List.mem_toFinset.mpr ha⟩)
    exact ⟨jm, List.mem_toFinset.mp hjm, fun j' hj' => hmax j' (List.mem_toFinset.mpr hj')⟩
  choose jm hjmS hjmmax using hjm
  have hmaxV : ∀ k : Fin n, ∀ m < V.size, f k m ≤ f k (jm k) := by
    intro k m hm
    rcases hdom k (List.mem_range.mpr k.isLt) m (List.mem_range.mpr hm) with hc | hd
    · exact hjmmax k m (by simpa using hc)
    · have h := eval_lowerDeg_nonneg hd hw hy
      rw [PVec.eval_dot, PVec.eval_const, eval_d, kval_vsub] at h
      have h0' : (l.S k).headD 0 ∈ l.S k := by
        cases hS : l.S k with
        | nil => exact absurd hS (hSne k k.isLt)
        | cons a t => simp
      have := hjmmax k _ h0'
      rw [rdot_comm', rdot_sub_left] at h
      have e : cd.u.eval y = u := rfl
      rw [e] at h
      simp only [f, c] at this ⊢
      linarith
  -- The tuple of maxima and its inner choices.
  have hmem : (fun k : Fin n => jm k) ∈ tuples n (fun k => l.S k) :=
    mem_tuples n _ _ (fun k => hjmS k)
  obtain ⟨idx, hidx, hT⟩ := List.mem_iff_getElem.mp hmem
  have hidx' : idx < l.inner.length := by rw [← hlen]; exact hidx
  set it := l.inner[idx] with hit
  have hzip : ((tuples n fun k => l.S k).zip l.inner)[idx]'(by simp [hidx, hidx']) =
      ((tuples n fun k => l.S k)[idx], it) := by simp [hit]
  have htk := htup _ (List.getElem_mem (by simp [hidx, hidx'] : idx < ((tuples n fun k => l.S k).zip l.inner).length))
  rw [hzip, hT] at htk
  have hitv := hinn it (List.getElem_mem hidx')
  have hiv : ∀ k < n, it.getD k 0 < V.size := by
    intro k hk
    rw [List.getD_eq_getElem?_getD]
    have : k < it.length := by rw [hitv.1]; exact hk
    simp only [this, List.getElem?_eq_getElem, Option.getD_some]
    exact hitv.2 _ (List.getElem_mem this)
  have hP0 := eval_reduce_nonneg id _ y h0 h1 h2 (eval_lowerDeg_nonneg htk hw hy)
  rw [eval_tuplePoly fr pr id V l _ _ hiv y] at hP0
  -- The weights.
  have hlam : ∀ k : Fin n, 0 ≤ lamR k := by
    intro k
    simp only [lamR]
    rcases hlamck with h2' | h3
    · simp [Leaf.lam, ← hn, h2', eval_kOne]
    · exact eval_lowerDeg_nonneg (h3 k (List.mem_range.mpr (by
        unfold Leaf.shapeOk at hshape
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hshape
        rcases hshape with ⟨h2'', -⟩ | h3' <;> omega))) hw hy
  have hd_eval : ∀ k, (l.d V cd k).eval y = rcross u (c k) := fun k => by rw [eval_d]; rfl
  apply balanced_pose_not_rupert (ι := Fin n) (V.toList.map kval) S hS p u ξ hview w hR
    (fun k => c k) (fun k => lamR k) (fun k => kval (vertex V (it.getD k 0))) (fun k => kval (vertex V (jm k)))
    hlam
  · -- Balance.
    rw [Fin.sum_univ_eq_sum_range (fun k => lamR k • rcross u (c k)) n]
    unfold Leaf.shapeOk at hshape
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hshape
    rcases hshape with ⟨h2', he⟩ | h3'
    · have hl1 : ∀ k, lamR k = 1 := by
        intro k; simp only [lamR, Leaf.lam]; rw [if_pos (by omega)]; exact eval_kOne y
      have hc1 : c 1 = -c 0 := by
        simp only [c, kval_dir, he]; abel
      rw [← hn] at h2'
      rw [h2']
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hl1, one_smul, hc1, rcross_neg_right,
        add_neg_cancel]
    · have hl3 : ∀ k, lamR k = l.s * rdot (rcross (c ((k + 1) % 3)) (c ((k + 2) % 3))) u := by
        intro k
        have hn2 : ¬ l.n = 2 := by omega
        simp only [lamR, Leaf.lam, hn2, if_false, KPoly.eval_scale, PVec.eval_dot, PVec.eval_const, kval_vcross]
        rw [show cd.u.eval y = u from rfl]
      rw [← hn] at h3'
      rw [h3']
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hl3]
      have := cramer3 (l.s : ℝ) u (c 0) (c 1) (c 2)
      simpa using this
  · -- A positive weight on a nonzero direction.
    have hp := eval_lowerDeg_pos hposck hw hy
    rw [eval_foldr_add] at hp
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ k : Fin n, KPoly.eval 5 (PVec.dot (((List.range n).map (l.L V cd)).getD k
        (fun _ => KPoly.zero 5)) (l.d V cd k)) y = 0 := by
      intro k
      rw [Ls_getD V l cd n k k.isLt, PVec.eval_dot, eval_L, hd_eval, rdot_comm', rdot_smul_right]
      rcases (hlam k).lt_or_eq with hpos | hzero
      · rw [hcon k hpos]; simp [rdot]
      · simp only [lamR] at hzero; rw [← hzero]; ring
    rw [Finset.sum_eq_zero (fun k _ => hzero k)] at hp
    exact lt_irrefl _ hp
  · intro k
    exact kval_vertex_mem V _ (hiv k k.isLt)
  · intro k v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp ha
    have hm' : m < V.size := by simpa using hm
    have := hmaxV k m hm'
    have e : kval V.toList[m] = kval (vertex V m) := by
      simp [vertex, Array.getD, hm']
    rw [e]
    exact this
  · have e : ∀ k : Fin n, (if h : (k : ℕ) < n then jm ⟨k, h⟩ else 0) = jm k := fun k => by
      rw [dif_pos k.isLt]
    simp only [e] at hP0
    exact hP0

end KCap

end Noperts.Pipeline

end
