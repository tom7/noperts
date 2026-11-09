module

public import SeptopertShell.Slab
public import SeptopertShell.Watertight

/-!
# The closure certificate

A computable check `ClosureData.check` and the theorem `islandEnclosed_of_check`. The region
`D = B₀ ∩ {g_i ≤ δ_m}` has frontier inside the union of certified slabs: each face of `D` (a piece of
`{g_i = δ_m}`) is charted by polynomials `φ` in `(x₀, x₁, d)` (`x₀ = p_{i₀} − o₀`, `x₁ = p_{i₁} − o₁`,
`d = g_i(p)`), covered by a subdivision tree whose leaves are either slab boxes (in face coordinates) or
polynomial inequalities excluding the point (another `g_j > δ_m`, or outside `B₀`). The faces of `B₀` are
excluded the same way (some `g_j > δ_m` on them).
-/

@[expose] public section

namespace SeptopertShell

namespace Poly

/-- Evaluation in `ℚ`. -/
def evalQ (p : Poly) (x : Fin 3 → ℚ) : ℚ :=
  (p.map fun t => t.2 * x 0 ^ t.1.1 * x 1 ^ t.1.2.1 * x 2 ^ t.1.2.2).sum

theorem evalQ_cast (p : Poly) (x : Fin 3 → ℚ) :
    ((evalQ p x : ℚ) : ℝ) = eval p (fun i => (x i : ℝ)) := by
  induction p with
  | nil => simp [evalQ]
  | cons t p ih =>
    simp only [evalQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [eval_cons, Rat.cast_add, ih]
    simp [termEval]

theorem continuous_eval (g : Poly) : Continuous fun p : ℝ³ => g.eval (fun i => p i) := by
  have hc : ∀ i : Fin 3, Continuous fun p : ℝ³ => p i := fun i => (EuclideanSpace.proj i).continuous
  induction g with
  | nil => simp only [eval_nil]; exact continuous_const
  | cons t g ih =>
    simp only [eval_cons, termEval]
    exact ((((continuous_const.mul ((hc 0).pow _)).mul ((hc 1).pow _)).mul ((hc 2).pow _))).add ih

end Poly

/-! ### Cover trees -/

inductive CoverTree
  | slab (j : ℕ)
  | pos (k : ℕ)
  | split (dim : Fin 2) (mid : ℚ) (l r : CoverTree)

/-- Check a tree on the rectangle `[a0, b0] × [a1, b1]`. -/
def checkCover (slabOk posOk : ℕ → ℚ → ℚ → ℚ → ℚ → Bool) :
    CoverTree → ℚ → ℚ → ℚ → ℚ → Bool
  | .slab j, a0, b0, a1, b1 => slabOk j a0 b0 a1 b1
  | .pos k, a0, b0, a1, b1 => posOk k a0 b0 a1 b1
  | .split d m l r, a0, b0, a1, b1 =>
    if d = 0 then
      decide (a0 ≤ m ∧ m ≤ b0) && checkCover slabOk posOk l a0 m a1 b1 &&
        checkCover slabOk posOk r m b0 a1 b1
    else
      decide (a1 ≤ m ∧ m ≤ b1) && checkCover slabOk posOk l a0 b0 a1 m &&
        checkCover slabOk posOk r a0 b0 m b1

theorem checkCover_sound {slabOk posOk : ℕ → ℚ → ℚ → ℚ → ℚ → Bool} {S P : ℝ → ℝ → Prop}
    (hS : ∀ j a0 b0 a1 b1 (x0 x1 : ℝ), slabOk j a0 b0 a1 b1 = true → (a0 : ℝ) ≤ x0 → x0 ≤ b0 →
      (a1 : ℝ) ≤ x1 → x1 ≤ b1 → S x0 x1)
    (hP : ∀ k a0 b0 a1 b1 (x0 x1 : ℝ), posOk k a0 b0 a1 b1 = true → (a0 : ℝ) ≤ x0 → x0 ≤ b0 →
      (a1 : ℝ) ≤ x1 → x1 ≤ b1 → P x0 x1) :
    ∀ (t : CoverTree) a0 b0 a1 b1 (x0 x1 : ℝ), checkCover slabOk posOk t a0 b0 a1 b1 = true →
      (a0 : ℝ) ≤ x0 → x0 ≤ b0 → (a1 : ℝ) ≤ x1 → x1 ≤ b1 → S x0 x1 ∨ P x0 x1 := by
  intro t
  induction t with
  | slab j =>
    intro a0 b0 a1 b1 x0 x1 h h1 h2 h3 h4
    exact Or.inl (hS _ _ _ _ _ _ _ h h1 h2 h3 h4)
  | pos k =>
    intro a0 b0 a1 b1 x0 x1 h h1 h2 h3 h4
    exact Or.inr (hP _ _ _ _ _ _ _ h h1 h2 h3 h4)
  | split d m l r ihl ihr =>
    intro a0 b0 a1 b1 x0 x1 h h1 h2 h3 h4
    by_cases hd : d = 0
    · simp only [checkCover, hd, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨_, hl⟩, hr⟩ := h
      rcases le_total x0 (m : ℝ) with hm | hm
      · exact ihl _ _ _ _ _ _ hl h1 hm h3 h4
      · exact ihr _ _ _ _ _ _ hr hm h2 h3 h4
    · simp only [checkCover, hd, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨_, hl⟩, hr⟩ := h
      rcases le_total x1 (m : ℝ) with hm | hm
      · exact ihl _ _ _ _ _ _ hl h1 h2 h3 hm
      · exact ihr _ _ _ _ _ _ hr h1 h2 hm h4

/-- Leaf `slab j`: the rectangle lies in the box of slab `j` (in face coordinates). -/
def slabOkL (slabs : List (SlabData × ℚ × ℚ)) (j : ℕ) (a0 b0 a1 b1 : ℚ) : Bool :=
  match slabs[j]? with
  | some e => decide (e.2.1 - e.1.H0 ≤ a0 ∧ b0 ≤ e.2.1 + e.1.H0 ∧
      e.2.2 - e.1.H1 ≤ a1 ∧ b1 ≤ e.2.2 + e.1.H1)
  | none => false

/-- Leaf `pos k`: the `k`-th polynomial is positive on the rectangle. -/
def posOkL (hs : List Poly) (k : ℕ) (a0 b0 a1 b1 : ℚ) : Bool :=
  match hs[k]? with
  | some h => decide (0 < lowerBound h { lo := ![a0, a1, 0], hi := ![b0, b1, 0] })
  | none => false

def coverOk (slabs : List (SlabData × ℚ × ℚ)) (hs : List Poly) (t : CoverTree)
    (a0 b0 a1 b1 : ℚ) : Bool :=
  checkCover (slabOkL slabs) (posOkL hs) t a0 b0 a1 b1

theorem coverOk_sound (slabs : List (SlabData × ℚ × ℚ)) (hs : List Poly) (t : CoverTree)
    (a0 b0 a1 b1 : ℚ) (x0 x1 : ℝ) (h : coverOk slabs hs t a0 b0 a1 b1 = true)
    (h1 : (a0 : ℝ) ≤ x0) (h2 : x0 ≤ b0) (h3 : (a1 : ℝ) ≤ x1) (h4 : x1 ≤ b1) :
    (∃ e ∈ slabs, |x0 - e.2.1| ≤ e.1.H0 ∧ |x1 - e.2.2| ≤ e.1.H1) ∨
      ∃ h ∈ hs, 0 < h.eval ![x0, x1, 0] := by
  refine checkCover_sound (S := fun x0 x1 => ∃ e ∈ slabs, |x0 - e.2.1| ≤ e.1.H0 ∧ |x1 - e.2.2| ≤ e.1.H1)
    (P := fun x0 x1 => ∃ h ∈ hs, 0 < h.eval ![x0, x1, 0]) ?_ ?_ t a0 b0 a1 b1 x0 x1 h h1 h2 h3 h4
  · intro j a0 b0 a1 b1 x0 x1 hj h1 h2 h3 h4
    unfold slabOkL at hj
    cases hge : slabs[j]? with
    | none => rw [hge] at hj; simp at hj
    | some e =>
      rw [hge] at hj
      simp only [decide_eq_true_eq] at hj
      obtain ⟨j1, j2, j3, j4⟩ := hj
      refine ⟨e, List.mem_of_getElem? hge, ?_, ?_⟩
      · rw [abs_le]
        have a1' : ((e.2.1 - e.1.H0 : ℚ) : ℝ) ≤ a0 := by exact_mod_cast j1
        have a2' : (b0 : ℝ) ≤ ((e.2.1 + e.1.H0 : ℚ) : ℝ) := by exact_mod_cast j2
        push_cast at a1' a2'
        constructor <;> linarith
      · rw [abs_le]
        have a1' : ((e.2.2 - e.1.H1 : ℚ) : ℝ) ≤ a1 := by exact_mod_cast j3
        have a2' : (b1 : ℝ) ≤ ((e.2.2 + e.1.H1 : ℚ) : ℝ) := by exact_mod_cast j4
        push_cast at a1' a2'
        constructor <;> linarith
  · intro k a0 b0 a1 b1 x0 x1 hk h1 h2 h3 h4
    unfold posOkL at hk
    cases hge : hs[k]? with
    | none => rw [hge] at hk; simp at hk
    | some h =>
      rw [hge] at hk
      simp only [decide_eq_true_eq] at hk
      refine ⟨h, List.mem_of_getElem? hge, ?_⟩
      have hB : Box.mem { lo := ![a0, a1, 0], hi := ![b0, b1, 0] } ![x0, x1, 0] := by
        intro i
        fin_cases i <;> simp [h1, h2, h3, h4]
      have := lowerBound_le_eval h _ _ hB
      have h' : (0 : ℝ) < (lowerBound h { lo := ![a0, a1, 0], hi := ![b0, b1, 0] } : ℚ) := by
        exact_mod_cast hk
      linarith

/-! ### Data -/

/-- One face `{g_gi = δ_m}` of the region. -/
structure FaceData where
  gi : ℕ
  chart : PV
  i0 : Fin 3
  i1 : Fin 3
  o0 : ℚ
  o1 : ℚ
  lo0 : ℚ
  hi0 : ℚ
  lo1 : ℚ
  hi1 : ℚ
  slabs : List (SlabData × ℚ × ℚ)
  tree : CoverTree

structure ClosureData where
  B0lo : Fin 3 → ℚ
  B0hi : Fin 3 → ℚ
  dm : ℚ
  gs : List Poly
  faces : List FaceData
  b0trees : Fin 3 → Fin 2 → CoverTree

namespace ClosureData

variable (C : ClosureData)

/-- The region. -/
def D : Set ℝ³ :=
  {p | (∀ k : Fin 3, (C.B0lo k : ℝ) ≤ p k ∧ p k ≤ C.B0hi k) ∧
    ∀ g ∈ C.gs, g.eval (fun i => p i) ≤ C.dm}

/-- The slabs, as sets of shape parameters. -/
def W : Set ℝ³ :=
  {p | ∃ f ∈ C.faces, ∃ e ∈ f.slabs, ∃ x : Fin 3 → ℝ, |x 0| ≤ e.1.H0 ∧ |x 1| ≤ e.1.H1 ∧
    (e.1.D0 : ℝ) ≤ x 2 ∧ x 2 ≤ e.1.D1 ∧ p = e.1.point x}

def g (i : ℕ) : Poly := C.gs.getD i []

def phiM (f : FaceData) (k : Fin 3) : Poly :=
  Poly.compose (f.chart k) (Poly.var 0) (Poly.var 1) (Poly.const C.dm)

/-- The excluding polynomials of a face. -/
def hs (f : FaceData) : List Poly :=
  ((List.range C.gs.length).filter (fun j => decide (j ≠ f.gi))).map
    (fun j => Poly.sub (Poly.compose (C.g j) (C.phiM f 0) (C.phiM f 1) (C.phiM f 2)) (Poly.const C.dm))
  ++ [Poly.sub (Poly.const (C.B0lo 0)) (C.phiM f 0), Poly.sub (C.phiM f 0) (Poly.const (C.B0hi 0)),
      Poly.sub (Poly.const (C.B0lo 1)) (C.phiM f 1), Poly.sub (C.phiM f 1) (Poly.const (C.B0hi 1)),
      Poly.sub (Poly.const (C.B0lo 2)) (C.phiM f 2), Poly.sub (C.phiM f 2) (Poly.const (C.B0hi 2))]

/-- Parametrisation of a face of `B₀`: coordinate `k` constant `c`, the next two are `x₀, x₁`. -/
def b0param (k : Fin 3) (c : ℚ) : PV := fun i =>
  if i = k then Poly.const c else if i = k + 1 then Poly.var 0 else Poly.var 1

def b0c (k : Fin 3) (s : Fin 2) : ℚ := if s = 0 then C.B0lo k else C.B0hi k

def b0hs (k : Fin 3) (s : Fin 2) : List Poly :=
  (List.range C.gs.length).map fun j =>
    Poly.sub (Poly.compose (C.g j) (b0param k (C.b0c k s) 0) (b0param k (C.b0c k s) 1)
      (b0param k (C.b0c k s) 2)) (Poly.const C.dm)

def slabCheck (f : FaceData) : Bool :=
  f.slabs.all fun e =>
    e.1.check && decide (e.1.D0 ≤ C.dm ∧ C.dm ≤ e.1.D1) &&
    decide (∀ k : Fin 3, Poly.normalize (Poly.compose (![e.1.s, e.1.y, e.1.z] k)
      (Poly.sub (Poly.var 0) (Poly.const e.2.1)) (Poly.sub (Poly.var 1) (Poly.const e.2.2))
      (Poly.var 2)) = Poly.normalize (f.chart k))

def invCheck (f : FaceData) : Bool :=
  decide (∀ k : Fin 3, Poly.normalize (Poly.compose (f.chart k)
      (Poly.sub (Poly.var f.i0) (Poly.const f.o0)) (Poly.sub (Poly.var f.i1) (Poly.const f.o1))
      (C.g f.gi)) = Poly.normalize (Poly.var k))

def regCheck (f : FaceData) : Bool :=
  decide (f.lo0 ≤ C.B0lo f.i0 - f.o0 ∧ C.B0hi f.i0 - f.o0 ≤ f.hi0 ∧
    f.lo1 ≤ C.B0lo f.i1 - f.o1 ∧ C.B0hi f.i1 - f.o1 ≤ f.hi1)

def faceCheck (f : FaceData) : Bool :=
  decide (f.gi < C.gs.length) && C.slabCheck f && C.invCheck f && C.regCheck f &&
    coverOk f.slabs (C.hs f) f.tree f.lo0 f.hi0 f.lo1 f.hi1

def b0Check : Bool :=
  decide (∀ (k : Fin 3) (s : Fin 2), coverOk [] (C.b0hs k s) (C.b0trees k s)
    (C.B0lo (k + 1)) (C.B0hi (k + 1)) (C.B0lo (k + 2)) (C.B0hi (k + 2)) = true)

/-- The closure check. -/
def check : Bool :=
  decide (C.faces.map FaceData.gi = List.range C.gs.length) && C.faces.all C.faceCheck && C.b0Check

/-- The Classic is in `D` (checked in `ℚ`) and `(1, 0, 0)` is outside `B₀`. -/
def classicOk : Bool :=
  let q : Fin 3 → ℚ := ![426431 / 1268289, 376317 / 1268289, -279863 / 1268289]
  decide (∀ k : Fin 3, C.B0lo k ≤ q k ∧ q k ≤ C.B0hi k) &&
    C.gs.all (fun g => decide (g.evalQ q ≤ C.dm)) && decide (C.B0hi 0 < 1)

/-! ### Soundness -/

theorem isClosed_D : IsClosed C.D := by
  have hc : ∀ i : Fin 3, Continuous fun p : ℝ³ => p i := fun i => (EuclideanSpace.proj i).continuous
  have : C.D = (⋂ k : Fin 3, {p : ℝ³ | (C.B0lo k : ℝ) ≤ p k} ∩ {p : ℝ³ | p k ≤ C.B0hi k}) ∩
      ⋂ g ∈ C.gs, {p : ℝ³ | g.eval (fun i => p i) ≤ C.dm} := by
    ext p; simp [D, forall_and]
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun k => IsClosed.inter ?_ ?_)
    (isClosed_biInter fun g _ => ?_)
  · exact isClosed_le continuous_const (hc k)
  · exact isClosed_le (hc k) continuous_const
  · exact isClosed_le (Poly.continuous_eval g) continuous_const

theorem mem_g {i : ℕ} (hi : i < C.gs.length) : C.g i ∈ C.gs := by
  unfold g
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- Frontier points that avoid the faces of `B₀` lie on some `g = δ_m`. -/
theorem frontier_cases {p : ℝ³} (hp : p ∈ frontier C.D) :
    p ∈ C.D ∧ ((∃ k : Fin 3, (p k = C.B0lo k) ∨ (p k = C.B0hi k)) ∨
      ∃ g ∈ C.gs, g.eval (fun i => p i) = C.dm) := by
  have hpD : p ∈ C.D := C.isClosed_D.frontier_subset hp
  refine ⟨hpD, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  apply hp.2
  rw [mem_interior]
  have hc : ∀ i : Fin 3, Continuous fun p : ℝ³ => p i := fun i => (EuclideanSpace.proj i).continuous
  refine ⟨(⋂ k : Fin 3, {p : ℝ³ | (C.B0lo k : ℝ) < p k} ∩ {p : ℝ³ | p k < C.B0hi k}) ∩
      ⋂ g ∈ C.gs, {p : ℝ³ | g.eval (fun i => p i) < C.dm}, ?_, ?_, ?_⟩
  · intro q hq
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hq
    exact ⟨fun k => ⟨(hq.1 k).1.le, (hq.1 k).2.le⟩, fun g hg => (hq.2 g hg).le⟩
  · refine IsOpen.inter (isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_) ?_
    · exact isOpen_lt continuous_const (hc k)
    · exact isOpen_lt (hc k) continuous_const
    · exact (List.finite_toSet C.gs).isOpen_biInter fun g _ =>
        isOpen_lt (Poly.continuous_eval g) continuous_const
  · simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨?_, ?_⟩, fun g hg => ?_⟩
    · exact lt_of_le_of_ne (hpD.1 k).1 (fun h => hne1 k |>.1 h.symm)
    · exact lt_of_le_of_ne (hpD.1 k).2 (hne1 k).2
    · exact lt_of_le_of_ne (hpD.2 g hg) (hne2 g hg)

/-! #### Faces of `B₀` -/

theorem b0param_eval (k : Fin 3) (c : ℚ) (v : Fin 3 → ℝ) (i : Fin 3) :
    (b0param k c i).eval v = if i = k then (c : ℝ) else if i = k + 1 then v 0 else v 1 := by
  unfold b0param
  split_ifs <;> simp [Poly.eval_const, Poly.eval_var]

theorem b0param_vec (k : Fin 3) (s : Fin 2) (p : ℝ³) (hk : p k = C.b0c k s) :
    (![(b0param k (C.b0c k s) 0).eval ![p (k + 1), p (k + 2), 0],
       (b0param k (C.b0c k s) 1).eval ![p (k + 1), p (k + 2), 0],
       (b0param k (C.b0c k s) 2).eval ![p (k + 1), p (k + 2), 0]] : Fin 3 → ℝ) = fun i => p i := by
  funext i
  have : ∀ j : Fin 3, (b0param k (C.b0c k s) j).eval ![p (k + 1), p (k + 2), 0] = p j := by
    intro j
    rw [b0param_eval]
    fin_cases k <;> fin_cases j <;> simp_all
  fin_cases i <;> simp [this]

theorem b0_not_mem {p : ℝ³} (hpD : p ∈ C.D) (hcov : C.b0Check = true) (k : Fin 3) (s : Fin 2)
    (hk : p k = C.b0c k s) : False := by
  unfold b0Check at hcov
  simp only [decide_eq_true_eq] at hcov
  have hb := hcov k s
  have hr : ∀ j : Fin 3, (C.B0lo j : ℝ) ≤ p j ∧ p j ≤ C.B0hi j := hpD.1
  rcases coverOk_sound [] (C.b0hs k s) (C.b0trees k s) _ _ _ _ (p (k + 1)) (p (k + 2)) hb
    (hr _).1 (hr _).2 (hr _).1 (hr _).2 with ⟨e, he, _⟩ | ⟨h, hh, hpos⟩
  · simp at he
  · unfold b0hs at hh
    simp only [List.mem_map] at hh
    obtain ⟨j, hj, rfl⟩ := hh
    rw [Poly.eval_sub, Poly.eval_compose, Poly.eval_const, C.b0param_vec k s p hk] at hpos
    have := hpD.2 _ (C.mem_g (List.mem_range.mp hj))
    linarith

/-! #### Faces -/

section face
variable {C} {f : FaceData} {p : ℝ³}

theorem chart_inv (h : C.invCheck f = true) (k : Fin 3) :
    (f.chart k).eval ![p f.i0 - f.o0, p f.i1 - f.o1, (C.g f.gi).eval (fun i => p i)] = p k := by
  unfold invCheck at h
  simp only [decide_eq_true_eq] at h
  have := congrArg (fun q => Poly.eval q (fun i => p i)) (h k)
  simp only [Poly.eval_normalize, Poly.eval_compose, Poly.eval_sub, Poly.eval_var,
    Poly.eval_const] at this
  exact this

theorem phiM_eval (hinv : C.invCheck f = true) (hg : (C.g f.gi).eval (fun i => p i) = C.dm) (k : Fin 3) :
    (C.phiM f k).eval ![p f.i0 - f.o0, p f.i1 - f.o1, 0] = p k := by
  unfold phiM
  rw [Poly.eval_compose, Poly.eval_var, Poly.eval_var, Poly.eval_const]
  have := chart_inv (p := p) hinv k
  rw [hg] at this
  simpa using this

theorem phiM_vec (hinv : C.invCheck f = true) (hg : (C.g f.gi).eval (fun i => p i) = C.dm) :
    (![(C.phiM f 0).eval ![p f.i0 - f.o0, p f.i1 - f.o1, 0],
       (C.phiM f 1).eval ![p f.i0 - f.o0, p f.i1 - f.o1, 0],
       (C.phiM f 2).eval ![p f.i0 - f.o0, p f.i1 - f.o1, 0]] : Fin 3 → ℝ) = fun i => p i := by
  funext i
  fin_cases i <;> simp [phiM_eval hinv hg]

theorem hs_nonpos (hinv : C.invCheck f = true) (hg : (C.g f.gi).eval (fun i => p i) = C.dm)
    (hpD : p ∈ C.D) (h : Poly) (hh : h ∈ C.hs f) : h.eval ![p f.i0 - f.o0, p f.i1 - f.o1, 0] ≤ 0 := by
  have hr : ∀ j : Fin 3, (C.B0lo j : ℝ) ≤ p j ∧ p j ≤ C.B0hi j := hpD.1
  unfold hs at hh
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with ⟨j, ⟨hj, _⟩, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Poly.eval_sub, Poly.eval_compose, Poly.eval_const, phiM_vec hinv hg]
    have := hpD.2 _ (C.mem_g hj)
    linarith
  all_goals
    simp only [Poly.eval_sub, Poly.eval_const, phiM_eval hinv hg]
    linarith [hr 0, hr 1, hr 2]

theorem face_mem_W (hF : C.faceCheck f = true) (hf : f ∈ C.faces)
    (hg : (C.g f.gi).eval (fun i => p i) = C.dm) (hpD : p ∈ C.D) : p ∈ C.W := by
  unfold faceCheck at hF
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨⟨⟨⟨_, hsl⟩, hinv⟩, hreg⟩, hcov⟩ := hF
  have hr : ∀ j : Fin 3, (C.B0lo j : ℝ) ≤ p j ∧ p j ≤ C.B0hi j := hpD.1
  unfold regCheck at hreg
  simp only [decide_eq_true_eq] at hreg
  obtain ⟨r1, r2, r3, r4⟩ := hreg
  have q1 : (f.lo0 : ℝ) ≤ p f.i0 - f.o0 := by
    have : ((f.lo0 : ℚ) : ℝ) ≤ ((C.B0lo f.i0 - f.o0 : ℚ) : ℝ) := by exact_mod_cast r1
    push_cast at this; linarith [(hr f.i0).1]
  have q2 : p f.i0 - f.o0 ≤ f.hi0 := by
    have : ((C.B0hi f.i0 - f.o0 : ℚ) : ℝ) ≤ ((f.hi0 : ℚ) : ℝ) := by exact_mod_cast r2
    push_cast at this; linarith [(hr f.i0).2]
  have q3 : (f.lo1 : ℝ) ≤ p f.i1 - f.o1 := by
    have : ((f.lo1 : ℚ) : ℝ) ≤ ((C.B0lo f.i1 - f.o1 : ℚ) : ℝ) := by exact_mod_cast r3
    push_cast at this; linarith [(hr f.i1).1]
  have q4 : p f.i1 - f.o1 ≤ f.hi1 := by
    have : ((C.B0hi f.i1 - f.o1 : ℚ) : ℝ) ≤ ((f.hi1 : ℚ) : ℝ) := by exact_mod_cast r4
    push_cast at this; linarith [(hr f.i1).2]
  rcases coverOk_sound _ _ _ _ _ _ _ _ _ hcov q1 q2 q3 q4 with ⟨e, he, hx0, hx1⟩ | ⟨h, hh, hpos⟩
  · refine ⟨f, hf, e, he, ![p f.i0 - f.o0 - e.2.1, p f.i1 - f.o1 - e.2.2, C.dm], ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hx0
    · simpa using hx1
    · -- D0 ≤ dm
      unfold slabCheck at hsl
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsl
      have := (hsl e he).1.2
      simp only [Matrix.cons_val]
      exact_mod_cast this.1
    · unfold slabCheck at hsl
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsl
      have := (hsl e he).1.2
      simp only [Matrix.cons_val]
      exact_mod_cast this.2
    · unfold slabCheck at hsl
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsl
      have hid := (hsl e he).2
      have hk : ∀ k : Fin 3, ((![e.1.s, e.1.y, e.1.z] k).eval ![p f.i0 - f.o0 - e.2.1, p f.i1 - f.o1 - e.2.2, C.dm])
          = p k := by
        intro k
        have h1 := congrArg (fun q => Poly.eval q ![p f.i0 - f.o0, p f.i1 - f.o1, C.dm]) (hid k)
        simp only [Poly.eval_normalize, Poly.eval_compose, Poly.eval_sub, Poly.eval_var,
          Poly.eval_const] at h1
        have h2 := chart_inv (p := p) hinv k
        rw [hg] at h2
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, sub_sub] at h1 ⊢
        rw [h1, h2]
      ext i
      fin_cases i
      · simpa [SlabData.point] using (hk 0).symm
      · simpa [SlabData.point] using (hk 1).symm
      · simpa [SlabData.point] using (hk 2).symm
  · exact absurd hpos (not_lt.mpr (hs_nonpos hinv hg hpD h hh))

end face

theorem frontier_subset (h : C.check = true) : frontier C.D ⊆ C.W := by
  intro p hp
  obtain ⟨hpD, hcase⟩ := C.frontier_cases hp
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hfaces, hall⟩, hb0⟩ := h
  rcases hcase with ⟨k, hk | hk⟩ | ⟨g, hg, hge⟩
  · exact (C.b0_not_mem hpD hb0 k 0 (by simpa [b0c] using hk)).elim
  · exact (C.b0_not_mem hpD hb0 k 1 (by simpa [b0c] using hk)).elim
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hmem : i ∈ C.faces.map FaceData.gi := by
      rw [hfaces]; exact List.mem_range.mpr hi
    obtain ⟨f, hf, hfi⟩ := List.mem_map.mp hmem
    refine face_mem_W (hall f hf) hf ?_ hpD
    rw [hfi]
    unfold g
    rw [List.getD_eq_getElem _ _ hi]
    exact hge

end ClosureData

/-- **The Septopert island is enclosed**, from checked closure data. The conclusion is the body of
`IslandEnclosed` (defined in `SeptopertShell.lean`, which imports this file). -/
theorem islandEnclosed_of_check (C : ClosureData) (h : C.check = true) (hin : C.classicOk = true) :
    ∃ W : Set ℝ³, (∀ p ∈ W, IsRupert (shellVerts p)) ∧ Separates W classicParams outsideParams := by
  refine ⟨C.W, ?_, ?_⟩
  · rintro p ⟨f, hf, e, he, x, h0, h1, h2, h3, rfl⟩
    unfold ClosureData.check at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    have hF := h.1.2 f hf
    unfold ClosureData.faceCheck ClosureData.slabCheck at hF
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hF
    exact e.1.isRupert_of_check (hF.1.1.1.2 e he).1.1 x h0 h1 h2 h3
  · have hcl : classicParams ∈ C.D ∧ outsideParams ∉ C.D := by
      unfold ClosureData.classicOk at hin
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hin
      obtain ⟨⟨hb, hg⟩, ho⟩ := hin
      constructor
      · have cast : ∀ (a : ℚ), ((a : ℚ) : ℝ) = a := fun a => rfl
        have hq : (fun i => classicParams i) = fun i =>
            ((![426431 / 1268289, 376317 / 1268289, -279863 / 1268289] : Fin 3 → ℚ) i : ℝ) := by
          funext i; fin_cases i <;> simp [classicParams]
        refine ⟨fun k => ?_, fun g hg' => ?_⟩
        · have := hb k
          have e : classicParams k = (((![426431 / 1268289, 376317 / 1268289, -279863 / 1268289] :
              Fin 3 → ℚ) k : ℚ) : ℝ) := congrFun hq k
          rw [e]
          exact ⟨Rat.cast_le.mpr this.1, Rat.cast_le.mpr this.2⟩
        · have := hg g hg'
          rw [hq, ← Poly.evalQ_cast]
          exact_mod_cast this
      · intro hD
        have := (hD.1 0).2
        simp only [outsideParams] at this
        have h1 : ((C.B0hi 0 : ℚ) : ℝ) < 1 := by exact_mod_cast ho
        simp at this
        linarith
    exact separates_of_frontier_subset hcl.1 hcl.2 (C.frontier_subset h)

end SeptopertShell

end
