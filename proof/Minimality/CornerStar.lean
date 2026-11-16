module

public import Minimality.CornerFarkas

/-!
# The obtuse covector cone `K(d)` and the tier-1 / tier-2 corner leaves

Frame `e_a, e_b, e_c` (a `Corner`) with pairwise inner products `≤ 0`.  For a view `d` (frame
coordinates) put `l_k = ⟪e_k, view d⟫` (the covector `G d`).

* **Lemma OBL (inside).**  `obl_coord_nonpos`: `ν_k l_k ≤ 0` whenever `ν_k d_k ≤ 0` and
  `ν_k d_j ≥ 0` for the other two `j` (the coordinate facets of `K(d)`); `obl_wall_ge`:
  `l · d_{ij} = ⟪view d_{ij}, view d⟫ ≥ ‖view d_{ij}‖² ≥ 0` whenever `d_k d_i ≤ 0`, `d_k d_j ≤ 0`
  (the wedge facet; `d_{ij}` is `d` with the `k`-th coordinate set to `0`).  Only the signs of the
  inner products enter, not definiteness.
* **Lemma OS (tier 1).**  `OsCert`/`OsStrict`: a failure pattern of a test at the frame-fixed view `d`
  is refuted at every obtuse metric when a nonnegative combination `x` of its rows equals
  `ν − Σ β_k d_{(k)} − γ d`, with `ν`, `β`, `γ` obeying the facet sign conditions (shape-only data).
  `exists_formRow_neg_of_os`, `isRupert_corner_os`.
* **Lemma P2-OB (tier 2).**  `isRupert_corner_cells2`: two cells with their own rims and views and a
  joint `ObfCert` on the eight rows of any two failure patterns: Rupert.
-/

@[expose] public section

open Finset
open scoped RealInnerProductSpace

namespace Minimality
namespace CornerSnap

variable {ι : Type*}

/-- The `k`-th frame axis. -/
def Corner.axis (C : Corner ι) : Fin 3 → ℝ³ := ![C.ea, C.eb, C.ec]

/-- The covector `l_k = ⟪e_k, view d⟫` (the `k`-th entry of `G d`). -/
noncomputable def Corner.cov (C : Corner ι) (d : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  ⟪C.axis k, C.view d⟫

/-- `d` with the `k`-th coordinate set to `0` (the projection to the wall `ij` along `e_k`). -/
def dwall (d : Fin 3 → ℝ) (k : Fin 3) : Fin 3 → ℝ := fun i => if i = k then 0 else d i

theorem Corner.cov_zero (C : Corner ι) (d : Fin 3 → ℝ) :
    C.cov d 0 = ‖C.ea‖ ^ 2 * d 0 + ⟪C.ea, C.eb⟫ * d 1 + ⟪C.ea, C.ec⟫ * d 2 := by
  simp only [Corner.cov, Corner.axis, Corner.view, Matrix.cons_val_zero, inner_add_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem Corner.cov_one (C : Corner ι) (d : Fin 3 → ℝ) :
    C.cov d 1 = ⟪C.ea, C.eb⟫ * d 0 + ‖C.eb‖ ^ 2 * d 1 + ⟪C.eb, C.ec⟫ * d 2 := by
  simp only [Corner.cov, Corner.axis, Corner.view, Matrix.cons_val_one,
    Matrix.cons_val_zero, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm C.ea C.eb]
  ring

theorem Corner.cov_two (C : Corner ι) (d : Fin 3 → ℝ) :
    C.cov d 2 = ⟪C.ea, C.ec⟫ * d 0 + ⟪C.eb, C.ec⟫ * d 1 + ‖C.ec‖ ^ 2 * d 2 := by
  simp only [Corner.cov, Corner.axis, Corner.view, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm C.ea C.ec, real_inner_comm C.eb C.ec]
  ring

/-- `formRow W d = Σ_k W_k l_k`. -/
theorem Corner.formRow_eq_cov (C : Corner ι) (W d : Fin 3 → ℝ) :
    C.formRow W d = W 0 * C.cov d 0 + W 1 * C.cov d 1 + W 2 * C.cov d 2 := by
  rw [C.cov_zero, C.cov_one, C.cov_two]
  simp only [Corner.formRow]
  ring

/-- `⟪view u, view d⟫ = Σ_k u_k l_k`. -/
theorem Corner.inner_view_view (C : Corner ι) (u d : Fin 3 → ℝ) :
    ⟪C.view u, C.view d⟫ = u 0 * C.cov d 0 + u 1 * C.cov d 1 + u 2 * C.cov d 2 := by
  simp only [Corner.cov, Corner.axis, Corner.view, inner_add_left, inner_smul_left,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, conj_trivial]

theorem Corner.formRow_self (C : Corner ι) (d : Fin 3 → ℝ) :
    C.formRow d d = ‖C.view d‖ ^ 2 := by
  rw [C.norm_view_sq]; simp only [Corner.formRow]; ring

/-! ### Lemma OBL, inside direction -/

/-- **OBL, coordinate facets.**  If `ν d_k ≤ 0` and `ν d_j ≥ 0` for `j ≠ k`, then
`ν l_k ≤ ‖e_k‖² ν d_k ≤ 0` (so `l_k` has the sign of `d_k`: `K(d) ⊆ {l_k ≥ 0}` for `d_k ≥ 0 ≥ d_j`,
and the reverse; the first inequality is the strict margin). -/
theorem obl_coord_le (C : Corner ι) (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0)
    (hbc : ⟪C.eb, C.ec⟫ ≤ 0) (d : Fin 3 → ℝ) (k : Fin 3) (ν : ℝ)
    (hj : ∀ j, j ≠ k → 0 ≤ ν * d j) : ν * C.cov d k ≤ ‖C.axis k‖ ^ 2 * (ν * d k) := by
  fin_cases k
  · have h1 := hj 1 (by decide)
    have h2 := hj 2 (by decide)
    simp only [Corner.axis, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    rw [C.cov_zero]
    nlinarith [mul_nonneg (neg_nonneg.2 hab) h1, mul_nonneg (neg_nonneg.2 hac) h2]
  · have h1 := hj 0 (by decide)
    have h2 := hj 2 (by decide)
    simp only [Corner.axis, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
    rw [C.cov_one]
    nlinarith [mul_nonneg (neg_nonneg.2 hab) h1, mul_nonneg (neg_nonneg.2 hbc) h2]
  · have h1 := hj 0 (by decide)
    have h2 := hj 1 (by decide)
    simp only [Corner.axis, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Fin.reduceFinMk, Fin.isValue]
    rw [C.cov_two]
    nlinarith [mul_nonneg (neg_nonneg.2 hac) h1, mul_nonneg (neg_nonneg.2 hbc) h2]

/-- `Σ_i (dwall d k)_i l_i = ⟪view (dwall d k), view d⟫`. -/
theorem Corner.wall_dot (C : Corner ι) (d : Fin 3 → ℝ) (k : Fin 3) :
    dwall d k 0 * C.cov d 0 + dwall d k 1 * C.cov d 1 + dwall d k 2 * C.cov d 2 =
      ⟪C.view (dwall d k), C.view d⟫ := (C.inner_view_view _ _).symm

/-- **OBL, wedge facets (scaled).**  If `β d_k d_i ≤ 0` and `β d_k d_j ≤ 0` (the third coordinate has
the opposite sign to both others, or vanishes), then
`β l · d_{ij} = β ⟪view d_{ij}, view d⟫ ≥ β ‖view d_{ij}‖²`; with `β = 1` and `‖·‖² ≥ 0` this is
`l · d_{ij} ≥ 0`, the wedge facet of `K(d)`.  No sign of `β` is needed. -/
theorem obl_wall_ge (C : Corner ι) (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0)
    (hbc : ⟪C.eb, C.ec⟫ ≤ 0) (d : Fin 3 → ℝ) (k : Fin 3) (β : ℝ)
    (hk : ∀ j, j ≠ k → β * (d k * d j) ≤ 0) :
    β * ‖C.view (dwall d k)‖ ^ 2 ≤ β * ⟪C.view (dwall d k), C.view d⟫ := by
  rw [C.inner_view_view, C.norm_view_sq, C.cov_zero, C.cov_one, C.cov_two]
  fin_cases k
  · have h1 := hk 1 (by decide)
    have h2 := hk 2 (by decide)
    simp [dwall] at h1 h2 ⊢
    nlinarith [mul_nonneg (neg_nonneg.2 hab) (neg_nonneg.2 h1),
      mul_nonneg (neg_nonneg.2 hac) (neg_nonneg.2 h2)]
  · have h1 := hk 0 (by decide)
    have h2 := hk 2 (by decide)
    simp [dwall] at h1 h2 ⊢
    nlinarith [mul_nonneg (neg_nonneg.2 hab) (neg_nonneg.2 h1),
      mul_nonneg (neg_nonneg.2 hbc) (neg_nonneg.2 h2)]
  · have h1 := hk 0 (by decide)
    have h2 := hk 1 (by decide)
    simp [dwall] at h1 h2 ⊢
    nlinarith [mul_nonneg (neg_nonneg.2 hac) (neg_nonneg.2 h1),
      mul_nonneg (neg_nonneg.2 hbc) (neg_nonneg.2 h2)]

/-! ### Lemma OS: the tier-1 certificate -/

/-- Shape-only side of a tier-1 (obtuse star) certificate for the rows `W` at the view `d`:
`lam ≥ 0`, `Σ lam_i W_i = ν − Σ_k β_k d_{(k)} − γ d` with `β, γ ≥ 0`, where `ν_k` obeys the
coordinate-facet signs (`ν_k d_k ≤ 0 ≤ ν_k d_j`) and `β_k` the wedge-facet signs
(`β_k d_k d_j ≤ 0`).  It is the dual-cone statement `x ∈ −K(d)*` of Lemma OS, with `K(d)*` spanned by
the coordinate vectors `±e_k`, the wall projections `d_{(k)}` and `d`. -/
def OsCert {κ : Type*} [Fintype κ] (W : κ → Fin 3 → ℝ) (d : Fin 3 → ℝ) (lam : κ → ℝ)
    (ν β : Fin 3 → ℝ) (γ : ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ k, 0 ≤ β k) ∧ 0 ≤ γ ∧
  (∀ j, ∑ i, lam i * W i j = ν j - ∑ k, β k * dwall d k j - γ * d j) ∧
  (∀ k, ν k * d k ≤ 0 ∧ ∀ j, j ≠ k → 0 ≤ ν k * d j) ∧
  (∀ k j, j ≠ k → β k * (d k * d j) ≤ 0)

/-- Strictness of an `OsCert`: some term is strictly negative on the interior of `K(d)`. -/
def OsStrict (d ν β : Fin 3 → ℝ) (γ : ℝ) : Prop :=
  (0 < γ ∧ d ≠ 0) ∨ (∃ k, 0 < β k ∧ dwall d k ≠ 0) ∨ (∃ k, ν k * d k < 0)

/-- **Lemma OS (soundness).**  Obtuse frame, tier-1 certificate: some row `⟨G, sym(W_i dᵀ)⟩` is
negative.  Equivalently the test `d` is good at every obtuse metric of the frame once all failure
patterns are refuted this way.  (Carathéodory: `lam` can be taken with at most 3 nonzero entries;
not needed for soundness.) -/
theorem exists_formRow_neg_of_os {C : Corner ι} (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    {κ : Type*} [Fintype κ] {W : κ → Fin 3 → ℝ} {d : Fin 3 → ℝ} {lam : κ → ℝ}
    {ν β : Fin 3 → ℝ} {γ : ℝ} (h : OsCert W d lam ν β γ) (hs : OsStrict d ν β γ) :
    ∃ i, C.formRow (W i) d < 0 := by
  obtain ⟨hl, hβ, hγ, heq, hν, hw⟩ := h
  by_contra hcon
  push Not at hcon
  have hsum : 0 ≤ ∑ i, lam i * C.formRow (W i) d :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hcon i)
  have key : ∑ i, lam i * C.formRow (W i) d =
      (∑ i, lam i * W i 0) * C.cov d 0 + (∑ i, lam i * W i 1) * C.cov d 1 +
        (∑ i, lam i * W i 2) * C.cov d 2 := by
    simp only [C.formRow_eq_cov, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq 0, heq 1, heq 2] at key
  simp only [Fin.sum_univ_three] at key
  -- the three families of facet inequalities
  have hc : ∀ k, ν k * C.cov d k ≤ ‖C.axis k‖ ^ 2 * (ν k * d k) := fun k =>
    obl_coord_le C hab hac hbc d k (ν k) (hν k).2
  have hq : ∀ k, β k * ‖C.view (dwall d k)‖ ^ 2 ≤ β k * ⟪C.view (dwall d k), C.view d⟫ :=
    fun k => obl_wall_ge C hab hac hbc d k (β k) (hw k)
  have hqe : ∀ k, ⟪C.view (dwall d k), C.view d⟫ =
      dwall d k 0 * C.cov d 0 + dwall d k 1 * C.cov d 1 + dwall d k 2 * C.cov d 2 :=
    fun k => C.inner_view_view _ _
  have hde : ‖C.view d‖ ^ 2 = d 0 * C.cov d 0 + d 1 * C.cov d 1 + d 2 * C.cov d 2 := by
    rw [← C.inner_view_view, real_inner_self_eq_norm_sq]
  have hcn : ∀ k, ‖C.axis k‖ ^ 2 * (ν k * d k) ≤ 0 := fun k =>
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hν k).1
  have hax : ∀ k, 0 < ‖C.axis k‖ ^ 2 := fun k => by
    have := hli.ne_zero k
    exact pow_pos (norm_pos_iff.2 this) 2
  have hq0 : ∀ k, 0 ≤ β k * ‖C.view (dwall d k)‖ ^ 2 := fun k =>
    mul_nonneg (hβ k) (sq_nonneg _)
  have hd0 : 0 ≤ γ * ‖C.view d‖ ^ 2 := mul_nonneg hγ (sq_nonneg _)
  have hexp : (ν 0 - (β 0 * dwall d 0 0 + β 1 * dwall d 1 0 + β 2 * dwall d 2 0) - γ * d 0) *
        C.cov d 0 +
      (ν 1 - (β 0 * dwall d 0 1 + β 1 * dwall d 1 1 + β 2 * dwall d 2 1) - γ * d 1) *
        C.cov d 1 +
      (ν 2 - (β 0 * dwall d 0 2 + β 1 * dwall d 1 2 + β 2 * dwall d 2 2) - γ * d 2) *
        C.cov d 2 =
      (ν 0 * C.cov d 0 + ν 1 * C.cov d 1 + ν 2 * C.cov d 2) -
        (β 0 * ⟪C.view (dwall d 0), C.view d⟫ + β 1 * ⟪C.view (dwall d 1), C.view d⟫ +
          β 2 * ⟪C.view (dwall d 2), C.view d⟫) - γ * ‖C.view d‖ ^ 2 := by
    rw [hqe, hqe, hqe, hde]; ring
  rw [hexp] at key
  rw [key] at hsum
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have n0 := hcn 0
  have n1 := hcn 1
  have n2 := hcn 2
  have q0 := hq 0
  have q1 := hq 1
  have q2 := hq 2
  have z0 := hq0 0
  have z1 := hq0 1
  have z2 := hq0 2
  rcases hs with ⟨hg, hd⟩ | ⟨k, hk, hk0⟩ | ⟨k, hk⟩
  · have : 0 < ‖C.view d‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (Corner.view_ne_zero hli hd)) 2
    linarith [mul_pos hg this]
  · have : 0 < β k * ‖C.view (dwall d k)‖ ^ 2 :=
      mul_pos hk (pow_pos (norm_pos_iff.2 (Corner.view_ne_zero hli hk0)) 2)
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at this <;>
      linarith
  · have := mul_neg_of_pos_of_neg (hax k) hk
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at this <;>
      linarith


/-! ### Corner closed-cell leaves from row refutations -/

section Leaves
open Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- The four rows of a `RobUni` failure pattern are nonnegative depth-difference forms. -/
theorem patternRows_nonneg {k : ℕ} [NeZero k] {C : Corner (Fin n)} (hC : C.Rep x)
    (c : ZMod k → Fin n) (d₀ : Fin 3 → ℝ) (B : ZMod k) (b₁ b₂ b₃ : ℕ)
    (h : ⟪x (c (B + b₁)), C.view d₀⟫ ≤ ⟪x (c B), C.view d₀⟫ ∧
      ⟪x (c (B + b₁)), C.view d₀⟫ ≤ ⟪x (c (B + b₂)), C.view d₀⟫ ∧
      ⟪x (c (B + b₃)), C.view d₀⟫ ≤ ⟪x (c B), C.view d₀⟫ ∧
      ⟪x (c (B + b₃)), C.view d₀⟫ ≤ ⟪x (c (B + b₂)), C.view d₀⟫) :
    ∀ j, 0 ≤ C.formRow (C.xdiff (c (patternPairs B b₁ b₂ b₃ j).1) (c (patternPairs B b₁ b₂ b₃ j).2))
      d₀ := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  have key : ∀ p q : ZMod k, C.formRow (C.xdiff (c p) (c q)) d₀ =
      ⟪x (c p), C.view d₀⟫ - ⟪x (c q), C.view d₀⟫ := fun p q =>
    (hC.depth_sub_formRow d₀ (c p) (c q)).symm
  intro j
  fin_cases j <;> simp only [patternPairs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val_three, key] <;> linarith

/-- If every failure pattern has a negative row at the frame-fixed view `d₀`, the rim is robustly
unimodal at `C.view d₀`. -/
theorem robUni_of_rows {k : ℕ} [NeZero k] {C : Corner (Fin n)} (hC : C.Rep x)
    (c : ZMod k → Fin n) (d₀ : Fin 3 → ℝ)
    (hrows : ∀ (B : ZMod k) (b₁ b₂ b₃ : ℕ), 0 < b₁ → b₁ < b₂ → b₂ < b₃ → b₃ < k →
      ∃ j : Fin 4, C.formRow (C.xdiff (c (patternPairs B b₁ b₂ b₃ j).1)
        (c (patternPairs B b₁ b₂ b₃ j).2)) d₀ < 0) :
    RobUni (fun i => ⟪x (c i), C.view d₀⟫) := by
  intro B b₁ b₂ b₃ h1 h2 h3 h4 hh
  obtain ⟨j, hj⟩ := hrows B b₁ b₂ b₃ h1 h2 h3 h4
  exact absurd (patternRows_nonneg hC c d₀ B b₁ b₂ b₃ hh j) (not_le.2 hj)

/-- **Tier-1 corner leaf (Lemma OS).**  As `isRupert_corner_cell`, with the Farkas certificate of
each failure pattern given in the star form `OsCert`/`OsStrict` (coordinate and wedge facets of
`K(d₀)`); the fibre is the whole obtuse cone of the frame. -/
theorem isRupert_corner_os {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    {C : Corner (Fin n)} (hC : C.Rep x) (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    (d₀ : Fin 3 → ℝ) (hu : CellLe F U Dn (C.view d₀))
    (hcert : ∀ (B : ZMod k) (b₁ b₂ b₃ : ℕ), 0 < b₁ → b₁ < b₂ → b₂ < b₃ → b₃ < k →
      ∃ (lam : Fin 4 → ℝ) (ν β : Fin 3 → ℝ) (γ : ℝ),
        OsCert (fun j => C.xdiff (c (patternPairs B b₁ b₂ b₃ j).1) (c (patternPairs B b₁ b₂ b₃ j).2))
          d₀ lam ν β γ ∧ OsStrict d₀ ν β γ) :
    IsRupert (univ.image x) := by
  refine isRupert_of_closedCell hk F hx hc hcyc ha hu (robUni_of_rows hC c d₀ ?_)
  intro B b₁ b₂ b₃ h1 h2 h3 h4
  obtain ⟨lam, ν, β, γ, h, hs⟩ := hcert B b₁ b₂ b₃ h1 h2 h3 h4
  exact exists_formRow_neg_of_os hli hab hac hbc h hs

/-- **Two-cell corner leaf (Lemma P2-OB).**  Two cells of the same arrangement, each with a rim
cycle (`c₁` of length `k₁`, `c₂` of length `k₂`), a strict point and a frame-fixed closure view
(`d₁`, `d₂`).  If for every pair of failure patterns (one per cell) the eight rows
`⟨G, sym(W D ᵀ)⟩` (each row with its own cell's view) have an `ObfCert` (a joint Farkas
certificate: the cone combination `x` of the first pattern, `y` of the second, and a positive semidefinite term `Σ_j U_j U_jᵀ` of any rank), then
`x` is Rupert: at every obtuse metric one of the two tests is good. -/
theorem isRupert_corner_cells2 {k₁ k₂ : ℕ} [NeZero k₁] [NeZero k₂] (hk₁ : 4 ≤ k₁) (hk₂ : 4 ≤ k₂)
    (F : S0xFac m S x) (hx : Function.Injective x)
    {c₁ : ZMod k₁ → Fin n} (hc₁ : Function.Injective c₁)
    {c₂ : ZMod k₂ → Fin n} (hc₂ : Function.Injective c₂)
    {U₁ Dn₁ U₂ Dn₂ : Finset (Fin m)} (hcyc₁ : S0xCycUD S c₁ U₁ Dn₁)
    (hcyc₂ : S0xCycUD S c₂ U₂ Dn₂) {a₁ a₂ : ℝ³} (ha₁ : CellAt F U₁ Dn₁ a₁)
    (ha₂ : CellAt F U₂ Dn₂ a₂)
    {C : Corner (Fin n)} (hC : C.Rep x) (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec])
    (hab : ⟪C.ea, C.eb⟫ ≤ 0) (hac : ⟪C.ea, C.ec⟫ ≤ 0) (hbc : ⟪C.eb, C.ec⟫ ≤ 0)
    (d₁ d₂ : Fin 3 → ℝ) (hu₁ : CellLe F U₁ Dn₁ (C.view d₁)) (hu₂ : CellLe F U₂ Dn₂ (C.view d₂))
    (hcert : ∀ (B : ZMod k₁) (b₁ b₂ b₃ : ℕ), 0 < b₁ → b₁ < b₂ → b₂ < b₃ → b₃ < k₁ →
      ∀ (B' : ZMod k₂) (b₁' b₂' b₃' : ℕ), 0 < b₁' → b₁' < b₂' → b₂' < b₃' → b₃' < k₂ →
      ∃ (lam : Fin 4 ⊕ Fin 4 → ℝ) (r : ℕ) (V : Fin r → Fin 3 → ℝ),
        ObfCert (Sum.elim
            (fun j => C.xdiff (c₁ (patternPairs B b₁ b₂ b₃ j).1) (c₁ (patternPairs B b₁ b₂ b₃ j).2))
            (fun j => C.xdiff (c₂ (patternPairs B' b₁' b₂' b₃' j).1)
              (c₂ (patternPairs B' b₁' b₂' b₃' j).2)))
          (Sum.elim (fun _ => d₁) (fun _ => d₂)) lam V) :
    IsRupert (univ.image x) := by
  by_cases h₁ : RobUni (fun i => ⟪x (c₁ i), C.view d₁⟫)
  · exact isRupert_of_closedCell hk₁ F hx hc₁ hcyc₁ ha₁ hu₁ h₁
  by_cases h₂ : RobUni (fun i => ⟪x (c₂ i), C.view d₂⟫)
  · exact isRupert_of_closedCell hk₂ F hx hc₂ hcyc₂ ha₂ hu₂ h₂
  exfalso
  unfold RobUni at h₁ h₂
  push Not at h₁ h₂
  obtain ⟨B, b₁, b₂, b₃, g1, g2, g3, g4, hh⟩ := h₁
  obtain ⟨B', b₁', b₂', b₃', g1', g2', g3', g4', hh'⟩ := h₂
  obtain ⟨lam, r, V, hv⟩ := hcert B b₁ b₂ b₃ g1 g2 g3 g4 B' b₁' b₂' b₃' g1' g2' g3' g4'
  obtain ⟨i, hi⟩ := obtuse_farkas_cert hli hab hac hbc hv
  have r1 := patternRows_nonneg hC c₁ d₁ B b₁ b₂ b₃ hh
  have r2 := patternRows_nonneg hC c₂ d₂ B' b₁' b₂' b₃' hh'
  rcases i with j | j
  · exact absurd (r1 j) (not_le.2 hi)
  · exact absurd (r2 j) (not_le.2 hi)

end Leaves

end CornerSnap
end Minimality
