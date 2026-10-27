module

public import Minimality.SameView
public import Minimality.RimHDN

@[expose] public section


/-!
# The Arc Lemma and arc certificates (`FEWER-FACES-PROOFS.md` §33)

* `EndsPos`, `InCone`, `cone_pos`, `cone_neg_near`: the cone step (a linear function that is
  `≥ 0` at both ends and not both `0` is `> 0` on the open cone; negative at an end means
  negative near that end).
* `middle_over_side`: a middle in the plane of the face, over the chord, is `c + s (c' - c) + δ u`
  with `0 < s < 1`, `δ ≠ 0`, from three linear tests in `u`.
* `Arc V`: the data of an arc (a 4-corner polygon between two oriented end views), all
  hypotheses being determinant inequalities at the two ends.
* **Lemma 33.1** `Arc.isRupert_of_row_neg`.
* **Corollary 33.2** (linear form, `μ = 0`) `arc_certificate`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The cone step -/

/-- The open cone `{s da + t db : s, t > 0}` spanned by the oriented end views. -/
def InCone (da db u : ℝ³) : Prop := ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ u = s • da + t • db

/-- A function is `≥ 0` at both ends of the arc and positive at (at least) one of them. -/
def EndsPos (f : ℝ³ → ℝ) (da db : ℝ³) : Prop :=
  0 ≤ f da ∧ 0 ≤ f db ∧ (0 < f da ∨ 0 < f db)

/-- **Cone lemma (positive).**  A function that is linear along the cone, `≥ 0` at both ends and
not zero at both, is `> 0` on the open cone. -/
theorem cone_pos {f : ℝ³ → ℝ} {da db : ℝ³}
    (hf : ∀ s t : ℝ, f (s • da + t • db) = s * f da + t * f db) (h : EndsPos f da db)
    {u : ℝ³} (hu : InCone da db u) : 0 < f u := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hu
  rw [hf]
  obtain ⟨h1, h2, h3 | h3⟩ := h
  · nlinarith [mul_pos hs h3, mul_nonneg ht.le h2]
  · nlinarith [mul_pos ht h3, mul_nonneg hs.le h1]

/-- **Cone lemma (negative).**  A function linear along the cone that is negative at the end
`d` is negative at `d + ε e` for all small `ε > 0`. -/
theorem cone_neg_near {f : ℝ³ → ℝ} {d e : ℝ³} (hf : ∀ ε : ℝ, f (d + ε • e) = f d + ε * f e)
    (h : f d < 0) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (d + ε • e) < 0 := by
  have hc : Continuous fun ε : ℝ => f d + ε * f e := by fun_prop
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), f d + ε * f e < 0 :=
    (hc.tendsto 0).eventually (eventually_lt_nhds (by simpa using h))
  exact (h1.filter_mono nhdsWithin_le_nhds).mono fun ε hε => by rw [hf]; exact hε

/-- `d + ε e` is in the open cone for `ε > 0`. -/
theorem inCone_end (da db : ℝ³) {ε : ℝ} (hε : 0 < ε) : InCone da db (da + ε • db) :=
  ⟨1, ε, one_pos, hε, by simp⟩

/-- Determinant tests are linear in the view. -/
theorem det3_cone (a b da db : ℝ³) (s t : ℝ) :
    det3 a b (s • da + t • db) = s * det3 a b da + t * det3 a b db := by
  simp only [det3, inner_add_right, real_inner_smul_right]

theorem det3_cone_mid (a da db n : ℝ³) (s t : ℝ) :
    det3 a (s • da + t • db) n = s * det3 a da n + t * det3 a db n := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Depths are linear in the view. -/
theorem inner_cone (x da db : ℝ³) (s t : ℝ) :
    ⟪x, s • da + t • db⟫ = s * ⟪x, da⟫ + t * ⟪x, db⟫ := by
  simp only [inner_add_right, real_inner_smul_right]

/-! ### Middles over a side -/

/-- **A middle over a side from three linear tests.**  The face plane has normal `n`; the view
`u`, the chord `c c'` and the middle `m` (in the plane of the face through the chord ends) all lie
in it.  Writing `σ = ±1` for the orientation, if `σ [c' - c, u, n] > 0`, `σ [m - c, u, n] > 0`,
`σ [c' - m, u, n] > 0` (all linear in `u`) and `m` is off the chord line, then `m = c + s (c' - c)
+ δ u` with `0 < s < 1`, `δ ≠ 0`:  `s = [m - c, u, n] / [c' - c, u, n]`,
`δ = [c' - c, m - c, n] / [c' - c, u, n]`. -/
theorem middle_over_side {m c c' u n : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hm : ⟪m - c, n⟫ = 0) (hc : ⟪c' - c, n⟫ = 0) (hu : ⟪u, n⟫ = 0)
    (hE : det3 (c' - c) (m - c) n ≠ 0)
    (hB : 0 < σ * det3 (c' - c) u n) (hA : 0 < σ * det3 (m - c) u n)
    (hAB : 0 < σ * det3 (c' - m) u n) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c + s • (c' - c) + δ • u := by
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set v := c' - c with hv
  set w := m - c with hw
  have cram := det3_cramer v w u n
  have hnn : det3 v w u * ⟪n, n⟫ = 0 := by
    have := congrArg (fun z => ⟪z, n⟫) cram
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at this
    rw [hc, hm, hu] at this
    linarith
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hE
    simp [det3]
  have hvwu : det3 v w u = 0 :=
    (mul_eq_zero.mp hnn).resolve_right (real_inner_self_pos.mpr hn0).ne'
  set B := det3 v u n with hBdef
  set A := det3 w u n with hAdef
  have hB' : B ≠ 0 := by
    intro h; rw [h] at hB; simp at hB
  have e2 : det3 (c' - m) u n = B - A := by
    simp only [hBdef, hAdef, hv, hw, det3_expand, PiLp.sub_apply]; ring
  rw [e2] at hAB
  refine ⟨A / B, det3 v w n / B, ?_, ?_, ?_, ?_⟩
  · have := div_pos hA hB
    rwa [mul_div_mul_left _ _ hσ0] at this
  · have := div_pos hAB hB
    rw [mul_div_mul_left _ _ hσ0] at this
    have h3 : (B - A) / B = 1 - A / B := by field_simp
    linarith
  · exact div_ne_zero hE hB'
  · rw [hvwu, zero_smul] at cram
    have h5 : B • w = A • v + det3 v w n • u := by
      rw [← sub_eq_zero]
      calc B • w - (A • v + det3 v w n • u) = -(A • v - B • w + det3 v w n • u) := by abel
        _ = 0 := by rw [cram]; simp
    have h6 : w = (A / B) • v + (det3 v w n / B) • u := by
      have := congrArg (fun z => B⁻¹ • z) h5
      simp only [smul_smul, smul_add, inv_mul_cancel₀ hB', one_smul] at this
      rw [div_eq_inv_mul, div_eq_inv_mul]; exact this
    have hmw : m = c + w := by simp [hw]
    rw [add_assoc, ← h6, hmw]

/-! ### Arcs -/

/-- **An arc (§33).**  The open cone between consecutive oriented events `da`, `db` of the face
circle of a face with normal `n` (both ends are views parallel to the face), on which the corner
polygon is the fixed 4-cycle `x` with front diagonal `{x 0, x 2}` and back diagonal `{x 1, x 3}`
(rotate the labels so that this holds).  Every hypothesis is a determinant inequality at the two
ends, so the cone lemma makes it strict inside:
* `hcyc`, `hrest`: the polygon is strictly convex, counterclockwise, and every other point of
  `V` except the face's middles `M` is strictly inside, at every view of the cone;
* `hfront`: `Γ = [x2 - x0, x3 - x1, x0 - x1] > 0` (non-coplanar; Lemma 20.26's Cramer form
  gives `FrontDiag` at every view of the cone);
* `hmid`: each middle lies in the face plane through a chord and over its open side at every
  view of the cone (three linear tests, `middle_over_side`).
There are no doubles: the only boundary non-corners are the middles (§33 definition). -/
structure Arc (V : Finset ℝ³) where
  x : ZMod 4 → ℝ³
  da : ℝ³
  db : ℝ³
  M : Finset ℝ³
  n : ℝ³
  hxV : ∀ i, x i ∈ V
  hxM : ∀ i, x i ∉ M
  hn_a : ⟪da, n⟫ = 0
  hn_b : ⟪db, n⟫ = 0
  hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
    EndsPos (fun u => det3 (x (i + 1) - x i) (x j - x i) u) da db
  hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
    EndsPos (fun u => det3 (x (i + 1) - x i) (y - x i) u) da db
  hfront : 0 < det3 (x 2 - x 0) (x 3 - x 1) (x 0 - x 1)
  hmid : ∀ m ∈ M, ∃ i : ZMod 4, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
    ⟪m - x i, n⟫ = 0 ∧ ⟪x (i + 1) - x i, n⟫ = 0 ∧ det3 (x (i + 1) - x i) (m - x i) n ≠ 0 ∧
    EndsPos (fun u => σ * det3 (x (i + 1) - x i) u n) da db ∧
    EndsPos (fun u => σ * det3 (m - x i) u n) da db ∧
    EndsPos (fun u => σ * det3 (x (i + 1) - m) u n) da db

/-- The 8 rows of the arc: `⟪x p - x q, d⟫` with `p` in the front diagonal `{x 0, x 2}`,
`q` in the back diagonal `{x 1, x 3}`, `d ∈ {da, db}` (Lemma 33.1). -/
noncomputable def Arc.row {V : Finset ℝ³} (A : Arc V) (r : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  ⟪A.x (![0, 2] r.1) - A.x (![1, 3] r.2.1), ![A.da, A.db] r.2.2⟫

/-- **(E2)** The exceptional set of Lemma 33.1 that is not codimension 2: the rim has no
horizontal double normal at the views `da + ε db` and `db + ε da` for all small `ε > 0`
(a persistent HDN is the paper's (E2); non-persistent ones occur at finitely many views,
Lemma 7.4, `exists_pairDir_of_hdn`).  (E1), the whole-arc tie, is not needed in Lean: the
closing is `QuadTestR.isRupert`, which allows ties. -/
def Arc.NoHDNNearEnds {V : Finset ℝ³} (A : Arc V) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), NoHDNAt (univ.image A.x) (A.da + ε • A.db)) ∧
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), NoHDNAt (univ.image A.x) (A.db + ε • A.da))

/-- Every view of the cone: the determinant tests hold strictly. -/
theorem Arc.det_pos {V : Finset ℝ³} (A : Arc V) {u : ℝ³} (hu : InCone A.da A.db u) :
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (A.x (i + 1) - A.x i) (A.x j - A.x i) u) ∧
    (∀ y ∈ V, y ∉ A.M → (∀ j, y ≠ A.x j) → ∀ i, 0 < det3 (A.x (i + 1) - A.x i) (y - A.x i) u) := by
  refine ⟨fun i j hi hj => ?_, fun y hy hyM hyx i => ?_⟩
  · exact cone_pos (fun s t => det3_cone _ _ _ _ s t) (A.hcyc i j hi hj) hu
  · exact cone_pos (fun s t => det3_cone _ _ _ _ s t) (A.hrest y hy hyM hyx i) hu

/-- Lemma 20.26 on the whole cone: `FrontDiag` at every view (`frontDiag_of_rim`, with
`det3 (c - y) (b - a) (y - a) = Γ` independent of the view). -/
theorem Arc.frontDiag {V : Finset ℝ³} (A : Arc V) {u : ℝ³} (hu : InCone A.da A.db u) :
    FrontDiag (A.x 0) (A.x 2) (A.x 1) (A.x 3) u := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨h1, h2⟩ := A.det_pos hu
  have q₁ := h1 0 2 (by decide) (by decide)
  have q₂ := h1 1 3 (by decide) (by decide)
  have q₃ := h1 2 0 (by decide) (by decide)
  have q₄ := h1 3 1 (by decide) (by decide)
  simp only [a0, a1, a2, a3] at q₁ q₂ q₃ q₄
  exact (frontDiag_of_rim q₁ q₂ q₃ q₄).1 A.hfront

/-- The middles lie over the sides at every view of the cone (`middle_over_side`). -/
theorem Arc.middles {V : Finset ℝ³} (A : Arc V) {u : ℝ³} (hu : InCone A.da A.db u) :
    ∀ m ∈ A.M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = A.x i + s • (A.x (i + 1) - A.x i) + δ • u := by
  intro m hm
  obtain ⟨i, σ, hσ, h1, h2, h3, h4, h5, h6⟩ := A.hmid m hm
  obtain ⟨s, t, hs, ht, rfl⟩ := hu
  have hf : ∀ a : ℝ³, ∀ s' t' : ℝ, σ * det3 a (s' • A.da + t' • A.db) A.n =
      s' * (σ * det3 a A.da A.n) + t' * (σ * det3 a A.db A.n) := by
    intro a s' t'; rw [det3_cone_mid]; ring
  have hc : InCone A.da A.db (s • A.da + t • A.db) := ⟨s, t, hs, ht, rfl⟩
  have hun : ⟪s • A.da + t • A.db, A.n⟫ = 0 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, A.hn_a, A.hn_b]; ring
  obtain ⟨s', δ, hs0, hs1, hδ, hm'⟩ := middle_over_side hσ h1 h2 hun h3
    (cone_pos (fun s t => hf _ s t) h4 hc) (cone_pos (fun s t => hf _ s t) h5 hc)
    (cone_pos (fun s t => hf _ s t) h6 hc)
  exact ⟨i, s', δ, hs0, hs1, hδ, hm'⟩

/-- The arc's cycle as a `quad`. -/
theorem quad_eq_arc {V : Finset ℝ³} (A : Arc V) : quad (A.x 0) (A.x 1) (A.x 2) (A.x 3) = A.x := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- **Lemma 33.1 at one view of the cone.**  If `u` is in the cone, the rim has no horizontal
double normal at `u`, and some front corner is strictly below some back corner at `u`, then `V`
is Rupert (`FrontDiag.fails4`, `QuadTestR.isRupert`; ties are allowed). -/
theorem Arc.isRupert_of_view {V : Finset ℝ³} (A : Arc V) {u : ℝ³} (hu : InCone A.da A.db u)
    (hnd : NoHDNAt (univ.image A.x) u)
    (hneg : ∃ p q : ZMod 4, (p = 0 ∨ p = 2) ∧ (q = 1 ∨ q = 3) ∧ ⟪A.x p - A.x q, u⟫ < 0) :
    IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨h1, h2⟩ := A.det_pos hu
  have q₁ := h1 0 2 (by decide) (by decide)
  have q₂ := h1 1 3 (by decide) (by decide)
  have q₃ := h1 2 0 (by decide) (by decide)
  have q₄ := h1 3 1 (by decide) (by decide)
  simp only [a0, a1, a2, a3] at q₁ q₂ q₃ q₄
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [det3] at q₁
  have hfd := A.frontDiag hu
  have hF : ¬ Fails4 (A.x 0) (A.x 2) (A.x 1) (A.x 3) u := by
    intro hF
    have hle := hfd.fails4 hu0 hF
    obtain ⟨p, q, hp, hq, hlt⟩ := hneg
    rw [inner_sub_left] at hlt
    simp only [max_le_iff, le_min_iff] at hle
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hle
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> linarith
  have hT : QuadTestR V u (A.x 0) (A.x 1) (A.x 2) (A.x 3) := by
    refine ⟨A.M, ∅, univ.image A.x, hu0, A.hxV 0, A.hxV 1, A.hxV 3, A.hxV 2, A.hxM 0, A.hxM 1,
      A.hxM 3, A.hxM 2, q₁, q₂, q₃, q₄, ?_, ?_, ?_, hnd, ?_, ?_, ?_, ?_⟩
    · intro z hz hzM _ z0 z1 z2 z3
      have r := h2 z hz hzM (by
        intro j
        rcases zmod4_cases j with rfl | rfl | rfl | rfl
        exacts [z0, z1, z2, z3])
      have r0 := r 0
      have r1 := r 1
      have r2 := r 2
      have r3 := r 3
      simp only [a0, a1, a2, a3] at r0 r1 r2 r3
      exact ⟨r0, r1, r2, r3⟩
    · rw [quad_eq_arc]; exact A.middles hu
    · simp
    all_goals simp
  exact hT.isRupert hF

/-- **Lemma 33.1 (Arc Lemma), Euclidean form.**  If one of the 8 rows of the arc is negative
(front corner `x p` below back corner `x q` at an end view), then `V` is Rupert, provided the rim
has no persistent horizontal double normal (E2).  Proof: at `u = d_end + ε d_other`, small
`ε > 0`, the row is still negative, so by `FrontDiag.fails4` the diagonals are not weakly
separated; all determinant tests hold (`Arc.det_pos`), the middles are over sides
(`Arc.middles`), and `QuadTestR.isRupert` closes. -/
theorem Arc.isRupert_of_row_neg {V : Finset ℝ³} (A : Arc V) (hnd : A.NoHDNNearEnds)
    (hneg : ∃ r, A.row r < 0) : IsRupert V := by
  obtain ⟨⟨p, q, d⟩, hr⟩ := hneg
  have hp : (![0, 2] p : ZMod 4) = 0 ∨ (![0, 2] p : ZMod 4) = 2 := by
    fin_cases p <;> simp
  have hq : (![1, 3] q : ZMod 4) = 1 ∨ (![1, 3] q : ZMod 4) = 3 := by
    fin_cases q <;> simp
  fin_cases d
  · -- d = da
    have hr' : ⟪A.x (![0, 2] p) - A.x (![1, 3] q), A.da⟫ < 0 := hr
    have hev := cone_neg_near (f := fun u => ⟪A.x (![0, 2] p) - A.x (![1, 3] q), u⟫)
      (d := A.da) (e := A.db) (fun ε => by simp only [inner_add_right, real_inner_smul_right])
      hr'
    obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := ((hev.and hnd.1).and self_mem_nhdsWithin).exists
    exact A.isRupert_of_view (inCone_end _ _ (Set.mem_Ioi.mp hε)) h2
      ⟨_, _, hp, hq, h1⟩
  · have hr' : ⟪A.x (![0, 2] p) - A.x (![1, 3] q), A.db⟫ < 0 := hr
    have hev := cone_neg_near (f := fun u => ⟪A.x (![0, 2] p) - A.x (![1, 3] q), u⟫)
      (d := A.db) (e := A.da) (fun ε => by simp only [inner_add_right, real_inner_smul_right])
      hr'
    obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := ((hev.and hnd.2).and self_mem_nhdsWithin).exists
    have hc := inCone_end A.db A.da (Set.mem_Ioi.mp hε)
    obtain ⟨s, t, hs, ht, he⟩ := hc
    exact A.isRupert_of_view ⟨t, s, ht, hs, by rw [he]; abel⟩ h2
      ⟨_, _, hp, hq, h1⟩

/-- **Lemma 33.1, the contrapositive (the 8 rows).**  If `V` is not Rupert and the rim has no
persistent HDN, every row of the arc is `≥ 0`. -/
theorem Arc.row_nonneg {V : Finset ℝ³} (A : Arc V) (hnd : A.NoHDNNearEnds)
    (hV : ¬ IsRupert V) (r : Fin 2 × Fin 2 × Fin 2) : 0 ≤ A.row r := by
  by_contra h
  exact hV (A.isRupert_of_row_neg hnd ⟨r, not_le.mp h⟩)

/-- **Corollary 33.2 (arc certificates), linear form (`μ = 0`).**  Arcs `A k`, weights
`lam k r ≥ 0` on their rows (not all zero) and `nu t ≥ 0` on the sign constraints, where
`w t = s_ij G_ij ≥ 0` is the signed Gram entry of the realization on the region.  If
`Σ λ row = - Σ ν w`, then `V` is Rupert, or every row with `λ > 0` vanishes (the tie
hyperplanes) and every `w` with `ν > 0` vanishes.  Arcs with a positive weight need (E2). -/
theorem arc_certificate {V : Finset ℝ³} {ι τ : Type*} [Fintype ι] [Fintype τ]
    (A : ι → Arc V) (lam : ι → Fin 2 × Fin 2 × Fin 2 → ℝ) (nu w : τ → ℝ)
    (hlam : ∀ k r, 0 ≤ lam k r) (_hlam0 : 0 < ∑ k, ∑ r, lam k r)
    (hnu : ∀ t, 0 ≤ nu t) (hw : ∀ t, 0 ≤ w t)
    (hcert : ∑ k, ∑ r, lam k r * (A k).row r = -∑ t, nu t * w t)
    (hnd : ∀ k, (∃ r, 0 < lam k r) → (A k).NoHDNNearEnds) :
    IsRupert V ∨ ((∀ k r, 0 < lam k r → (A k).row r = 0) ∧ ∀ t, 0 < nu t → w t = 0) := by
  by_cases hV : IsRupert V
  · exact Or.inl hV
  right
  have hterm : ∀ k r, 0 ≤ lam k r * (A k).row r := by
    intro k r
    rcases (hlam k r).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_nonneg (hlam k r) ((A k).row_nonneg (hnd k ⟨r, h⟩) hV r)
  have hs1 : 0 ≤ ∑ k, ∑ r, lam k r * (A k).row r :=
    sum_nonneg fun k _ => sum_nonneg fun r _ => hterm k r
  have hs2 : 0 ≤ ∑ t, nu t * w t := sum_nonneg fun t _ => mul_nonneg (hnu t) (hw t)
  have h1 : ∑ k, ∑ r, lam k r * (A k).row r = 0 := by linarith
  have h2 : ∑ t, nu t * w t = 0 := by linarith
  constructor
  · intro k r hk
    have hk0 := (sum_eq_zero_iff_of_nonneg fun k _ => sum_nonneg fun r _ => hterm k r).mp h1 k
      (mem_univ k)
    have := (sum_eq_zero_iff_of_nonneg fun r _ => hterm k r).mp hk0 r (mem_univ r)
    exact (mul_eq_zero.mp this).resolve_left hk.ne'
  · intro t ht
    have := (sum_eq_zero_iff_of_nonneg fun t _ => mul_nonneg (hnu t) (hw t)).mp h2 t (mem_univ t)
    exact (mul_eq_zero.mp this).resolve_left ht.ne'

end Minimality
