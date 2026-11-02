module

public import Minimality.SilS0XB

@[expose] public section


/-!
# S0X-C: type-free leaf interface (facet families, segment and line views)

`S0xFac m S x`: `m` facets of `x : Fin n → ℝ³` with vertex sets `S t` (the type-free `Fac8`).
A leaf is a view, a facing pattern `pat : Fin m → Bool` (true = up) and a silhouette cycle `c`;
its decidable side conditions are `Good` (checked by `decide`), its geometric hypotheses `Cond`
(facing literals of the free facets and `RobUni` of the depths).
* `s0x_seg_rupert`: segment view `x j - x i`; the facets through both `i` and `j` are edge-on and
  get their facing from the pattern via a tilt built from witness vertices (any number of edge-on
  facets, as long as each has a vertex off it lying on all the other edge-on ones).
* `s0x_lin_rupert`: line view `N_X × N_Y` (facets `X`, `Y` edge-on, tilt-chosen).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

/-- `m` facets of the points `x`, facet `t` with vertex set `S t`: `f t ≤ 0` on the points, `= 0`
exactly on `S t`, affine with gradient `N t`. -/
structure S0xFac {n : ℕ} (m : ℕ) (S : Fin m → Finset (Fin n)) (x : Fin n → ℝ³) where
  f : Fin m → ℝ³ → ℝ
  N : Fin m → ℝ³
  hN : ∀ t y z, f t y - f t z = ⟪N t, y - z⟫
  zero : ∀ t, ∀ i ∈ S t, f t (x i) = 0
  neg : ∀ t, ∀ i ∉ S t, f t (x i) < 0

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

theorem S0xFac.le (F : S0xFac m S x) (t : Fin m) (q : Fin n) : F.f t (x q) ≤ 0 := by
  by_cases h : q ∈ S t
  · rw [F.zero t q h]
  · exact (F.neg t q h).le

theorem S0xFac.inner_sub (F : S0xFac m S x) (t : Fin m) (a b : Fin n) :
    ⟪F.N t, x a - x b⟫ = F.f t (x a) - F.f t (x b) := (F.hN t _ _).symm

/-- The pattern `pat` (true = up) makes `c` an up/down silhouette: each edge `c i → c (i+1)` lies in
an up facet `a` and a down facet `b`, and every other vertex is off one of them. -/
def S0xCycOK {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (c : ZMod k → Fin n)
    (pat : Fin m → Bool) : Prop :=
  ∀ i, ∃ a b : Fin m, pat a = true ∧ pat b = false ∧ c i ∈ S a ∧ c i ∈ S b ∧
    c (i + 1) ∈ S a ∧ c (i + 1) ∈ S b ∧
    ∀ q : Fin n, q ≠ c i → q ≠ c (i + 1) → q ∉ S a ∨ q ∉ S b

instance {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (c : ZMod k → Fin n)
    (pat : Fin m → Bool) : Decidable (S0xCycOK S c pat) := by
  unfold S0xCycOK; infer_instance

/-- The lex facings of all facets at `(u, v)` follow the pattern. -/
def S0xFacOK (F : S0xFac m S x) (pat : Fin m → Bool) (u v : ℝ³) : Prop :=
  ∀ t, (pat t = true → h21b_LP ⟪F.N t, u⟫ ⟪F.N t, v⟫) ∧
    (pat t = false → h21b_LP (-⟪F.N t, u⟫) (-⟪F.N t, v⟫))

theorem s0x_silL {k : ℕ} [NeZero k] (F : S0xFac m S x) {c : ZMod k → Fin n}
    {pat : Fin m → Bool} {u v : ℝ³} (hcyc : S0xCycOK S c pat) (hfac : S0xFacOK F pat u v) :
    Nonempty (h21b_SilDataL k x c u v) := by
  choose ea eb hea heb h0a h0b h1a h1b hs using hcyc
  exact ⟨{
    A := fun i => F.N (ea i)
    B := fun i => F.N (eb i)
    fA := fun i => F.f (ea i)
    fB := fun i => F.f (eb i)
    hA := fun i => F.hN (ea i)
    hB := fun i => F.hN (eb i)
    zA0 := fun i => F.zero _ _ (h0a i)
    zA1 := fun i => F.zero _ _ (h1a i)
    zB0 := fun i => F.zero _ _ (h0b i)
    zB1 := fun i => F.zero _ _ (h1b i)
    nA := fun i q => F.le _ q
    nB := fun i q => F.le _ q
    strict := fun i q a b => by
      rcases hs i q a b with h | h
      · exact Or.inl (F.neg _ _ h)
      · exact Or.inr (F.neg _ _ h)
    up := fun i => (hfac (ea i)).1 (hea i)
    dn := fun i => (hfac (eb i)).2 (heb i) }⟩

/-! ### Segment views -/

/-- A segment-view leaf at `x j - x i`: pattern and cycle. -/
structure S0xSeg (n m k : ℕ) where
  i : Fin n
  j : Fin n
  pat : Fin m → Bool
  c : ZMod k → Fin n

/-- Decidable side conditions: facings forced for facets through exactly one endpoint, the cycle is a
silhouette of the pattern, and every edge-on facet (through both) has a witness vertex off it on all
the other edge-on facets (so the tilt realizes any edge-on facings). -/
def S0xSeg.Good {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (s : S0xSeg n m k) : Prop :=
  s.i ≠ s.j ∧ 3 ≤ k ∧ Function.Injective s.c ∧ S0xCycOK S s.c s.pat ∧
  (∀ t, s.j ∈ S t → s.i ∉ S t → s.pat t = true) ∧
  (∀ t, s.i ∈ S t → s.j ∉ S t → s.pat t = false) ∧
  (∀ Y, s.i ∈ S Y → s.j ∈ S Y →
    ∃ q, q ∉ S Y ∧ ∀ X, X ≠ Y → s.i ∈ S X → s.j ∈ S X → q ∈ S X)

instance {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (s : S0xSeg n m k) :
    Decidable (s.Good S) := by
  unfold S0xSeg.Good
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance inferInstance)))))

/-- Geometric hypotheses: the facings of the facets through neither endpoint
(`f_t(x j) - f_t(x i)`) and robust unimodality of the depths along the cycle. -/
def S0xSeg.Cond {k : ℕ} [NeZero k] (F : S0xFac m S x) (s : S0xSeg n m k) : Prop :=
  (∀ t, s.i ∉ S t → s.j ∉ S t →
    (s.pat t = true → 0 < F.f t (x s.j) - F.f t (x s.i)) ∧
    (s.pat t = false → F.f t (x s.j) - F.f t (x s.i) < 0)) ∧
  RobUni (fun a : ZMod k => ⟪x (s.c a), x s.j - x s.i⟫)

/-- **Segment-view leaf** (type-free). -/
theorem s0x_seg_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (s : S0xSeg n m k) (hg : s.Good S) (hC : s.Cond F) : IsRupert (univ.image x) := by
  classical
  obtain ⟨hij, hk, hc, hcyc, hup, hdn, htilt⟩ := hg
  obtain ⟨hlit, hU⟩ := hC
  set E := univ.filter (fun Y : Fin m => s.i ∈ S Y ∧ s.j ∈ S Y) with hE
  have memE : ∀ Y, Y ∈ E ↔ s.i ∈ S Y ∧ s.j ∈ S Y := fun Y => by
    simp only [hE, mem_filter, mem_univ, true_and]
  let q : Fin m → Fin n := fun Y =>
    if h : s.i ∈ S Y ∧ s.j ∈ S Y then (htilt Y h.1 h.2).choose else s.i
  have hq : ∀ Y ∈ E, q Y ∉ S Y ∧ ∀ X ∈ E, X ≠ Y → q Y ∈ S X := by
    intro Y hY
    rw [memE] at hY
    have := (htilt Y hY.1 hY.2).choose_spec
    simp only [q, hY]
    exact ⟨this.1, fun X hX hXY => this.2 X hXY ((memE X).1 hX).1 ((memE X).1 hX).2⟩
  let sg : Fin m → ℝ := fun Y => if s.pat Y = true then -1 else 1
  let v : ℝ³ := ∑ Y ∈ E, sg Y • (x (q Y) - x s.i)
  have hv : ∀ X ∈ E, ⟪F.N X, v⟫ = sg X * F.f X (x (q X)) := by
    intro X hX
    have hX' := (memE X).1 hX
    simp only [v, inner_sum, real_inner_smul_right]
    rw [Finset.sum_eq_single X]
    · rw [F.inner_sub, F.zero X _ hX'.1, sub_zero]
    · intro Y hY hYX
      rw [F.inner_sub, F.zero X _ ((hq Y hY).2 X hX (Ne.symm hYX)), F.zero X _ hX'.1]; ring
    · intro h; exact absurd hX h
  have hfac : S0xFacOK F s.pat (x s.j - x s.i) v := by
    intro t
    have hu : ⟪F.N t, x s.j - x s.i⟫ = F.f t (x s.j) - F.f t (x s.i) := F.inner_sub t _ _
    by_cases hi : s.i ∈ S t <;> by_cases hj : s.j ∈ S t
    · have ht : t ∈ E := (memE t).2 ⟨hi, hj⟩
      have h0 : ⟪F.N t, x s.j - x s.i⟫ = 0 := by rw [hu, F.zero t _ hi, F.zero t _ hj]; ring
      have hneg := F.neg t _ (hq t ht).1
      rw [h0, hv t ht]
      constructor
      · intro hp
        have : sg t = -1 := by simp only [sg, hp, ite_true]
        exact Or.inr ⟨rfl, by rw [this]; linarith⟩
      · intro hp
        have : sg t = 1 := by simp only [sg, hp]; rfl
        exact Or.inr ⟨neg_zero, by rw [this]; linarith⟩
    · have hp := hdn t hi hj
      have : ⟪F.N t, x s.j - x s.i⟫ < 0 := by rw [hu, F.zero t _ hi]; linarith [F.neg t _ hj]
      exact ⟨fun h => by rw [hp] at h; exact absurd h (by decide), fun _ => Or.inl (by linarith)⟩
    · have hp := hup t hj hi
      have : 0 < ⟪F.N t, x s.j - x s.i⟫ := by rw [hu, F.zero t _ hj]; linarith [F.neg t _ hi]
      exact ⟨fun _ => Or.inl this, fun h => by rw [hp] at h; exact absurd h (by decide)⟩
    · obtain ⟨l1, l2⟩ := hlit t hi hj
      exact ⟨fun h => Or.inl (by rw [hu]; exact l1 h),
        fun h => Or.inl (by rw [hu]; linarith [l2 h])⟩
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc hfac
  have hu0 : x s.j - x s.i ≠ 0 := fun h => hij (hx (sub_eq_zero.1 h)).symm
  exact s0x_sil_isRupert_lex hk hx hc hu0 D hU

/-! ### Line views -/

/-- A line-view leaf at `u = N_X × N_Y`: the edge-on facets `X`, `Y`, the pattern (for `X`, `Y` the
tilt-chosen facing) and the cycle. -/
structure S0xLin (n m k : ℕ) where
  X : Fin m
  Y : Fin m
  pat : Fin m → Bool
  c : ZMod k → Fin n

def S0xLin.Good {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (s : S0xLin n m k) : Prop :=
  s.X ≠ s.Y ∧ 3 ≤ k ∧ Function.Injective s.c ∧ S0xCycOK S s.c s.pat ∧
  ∃ t : Fin m, t ≠ s.X ∧ t ≠ s.Y

instance {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (s : S0xLin n m k) :
    Decidable (s.Good S) := by
  unfold S0xLin.Good; infer_instance

/-- Geometric hypotheses: the strict facings `⟪N_t, N_X × N_Y⟫` of the other facets and robust
unimodality of the depths `⟪x (c a), N_X × N_Y⟫`. -/
def S0xLin.Cond {k : ℕ} [NeZero k] (F : S0xFac m S x) (s : S0xLin n m k) : Prop :=
  (∀ t, t ≠ s.X → t ≠ s.Y →
    (s.pat t = true → 0 < ⟪F.N t, cross (F.N s.X) (F.N s.Y)⟫) ∧
    (s.pat t = false → ⟪F.N t, cross (F.N s.X) (F.N s.Y)⟫ < 0)) ∧
  RobUni (fun a : ZMod k => ⟪x (s.c a), cross (F.N s.X) (F.N s.Y)⟫)

/-- **Line-view leaf** (type-free). -/
theorem s0x_lin_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (s : S0xLin n m k) (hg : s.Good S) (hC : s.Cond F) : IsRupert (univ.image x) := by
  obtain ⟨hXY, hk, hc, hcyc, t0, ht0X, ht0Y⟩ := hg
  obtain ⟨hstr, hU⟩ := hC
  set u := cross (F.N s.X) (F.N s.Y) with hu
  have hu0 : u ≠ 0 := by
    intro h0
    obtain ⟨a, b⟩ := hstr t0 ht0X ht0Y
    rw [h0] at a b
    cases hp : s.pat t0
    · have := b hp; simp at this
    · have := a hp; simp at this
  let sg : Fin m → ℝ := fun Y => if s.pat Y = true then 1 else -1
  obtain ⟨v, hvX, hvY⟩ := s0x_exists_tilt_signs hu0 (sg s.X) (sg s.Y)
  have eX : ⟪F.N s.X, u⟫ = 0 := by
    simp only [hu, inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have eY : ⟪F.N s.Y, u⟫ = 0 := by
    simp only [hu, inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have edge : ∀ t, ⟪F.N t, u⟫ = 0 → ⟪F.N t, v⟫ = sg t →
      (s.pat t = true → h21b_LP ⟪F.N t, u⟫ ⟪F.N t, v⟫) ∧
      (s.pat t = false → h21b_LP (-⟪F.N t, u⟫) (-⟪F.N t, v⟫)) := by
    intro t h0 h1
    rw [h0, h1]
    refine ⟨fun hp => Or.inr ⟨rfl, ?_⟩, fun hp => Or.inr ⟨neg_zero, ?_⟩⟩
    · simp only [sg, hp, ite_true]; norm_num
    · simp only [sg, hp]; norm_num
  have hfac : S0xFacOK F s.pat u v := by
    intro t
    by_cases htX : t = s.X
    · subst htX; exact edge _ eX hvX
    by_cases htY : t = s.Y
    · subst htY; exact edge _ eY hvY
    obtain ⟨a, b⟩ := hstr t htX htY
    exact ⟨fun h => Or.inl (a h), fun h => Or.inl (by linarith [b h])⟩
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc hfac
  exact s0x_sil_isRupert_lex hk hx hc hu0 D hU

end H21
end Minimality

