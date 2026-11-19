module

public import Minimality.TorqueLeaves
public import Minimality.RimCellClosed
public import Minimality.Type21Sl2C
public import Minimality.Forces
public import Minimality.FrontDiag
public import Minimality.TheoremP24
public import Minimality.EdgeViewLink

@[expose] public section

/-!
# Edge-view tilts with the torque route (Lemma EV-Tilt) and the back diagonal (Lemma BD)

From the Carbon consult A10 (nopert229 scratch `carbon/CARBON-RESPONSES.md`, "A10 to Q10", Rank 1),
checked and corrected here.

**Theorem 8.10 on a cell, torque form (type-free).**
* `cell_rim_dets`: at a view `u` of an open rim cell (`CellAt F U Dn u`, rim `c` with
  `S0xCycUD`), all rim determinants `det3 (x (c (i+1)) - x (c i)) (x q - x (c i)) u`, `q` off the
  edge, have one common strict sign.
* `isRupert_of_cellAt_depthSep_torque`: a depth-separated pair `(a, b)` of the rim at a cell view
  `u` whose torque vector `W = Wv E V` is not orthogonal to `u`: Rupert.  No horizontal-double-
  normal hypothesis and no orientation bookkeeping (a clockwise rim is seen from `-u`).
* `isRupert_of_cellTilt_depthSep_torque`: the same along a tilt `u₀ + ε d` (cell, pair eventually),
  `W` not orthogonal to `u₀` or to `d`.

**Lemma EV-Tilt** (edge view `u₀ = x J - x p` of a polyhedron edge `pJ = F₁ ∩ F₂`, `v₁ ∈ F₂ \ F₁`,
`v₂ ∉ F₂` (Carbon: `v₂ ∈ F₁ \ F₂`; `v₂ ∈ F₁` is never used), tilt
`d λ = λ (x v₁ - x p) + (x v₂ - x p)`, `λ > 0`):
* `evTilt_back₁`, `evTilt_back₂`: `F₁` and `F₂` are strictly back along `d λ` (no Cauchy-Schwarz
  hypothesis on the two normals).
* `eq_zero_of_perp_edgeFrame`: `{u₀, x v₁ - x p, x v₂ - x p}` is a frame: a vector orthogonal to all
  three is zero (only the two facet normals are used, no collinearity hypothesis).
* `Wv_ne_zero_of_parPairAt`: the torque vector of a parallel pair is nonzero.
* `exists_tilt_Wv_ne`: so some `λ ∈ {1, 2}` has `⟪W, u₀⟫ ≠ 0 ∨ ⟪W, d λ⟫ ≠ 0`.
* `isRupert_edgeView_link_torque` (**edge-view 8.10 leaf in the link chamber, no `NoHDNRim`, no
  foot, no torque hypothesis**): a rim cell whose facets other than `F₁`, `F₂` face strictly at `u₀`
  (up facets up, down facets down), and a parallel pair of the rim at `u₀` that the depths at `u₀`
  separate: Rupert.
* `isRupert_edgeView_link_torque_tilt`: the same with weak facings of the other facets at `u₀`
  (each edge-on one strictly signed along the tilt) and the pair eventually along the tilt, for a
  given `λ > 0` with `⟪W, u₀⟫ ≠ 0 ∨ ⟪W, d λ⟫ ≠ 0`.
* `isRupert_edgeView23_ds`: type 24 instance, Lemma E23's view `x 3 - x 2` and rim (the link of
  `2`) with a depth-separated pair in place of unimodal depths.

**Lemma BD** (back diagonal, the twin of Lemma FD): `back_diag`: if the diagonal `c 0, c 2` of a
4-rim lies on a facet facing *away* from the cell, every nonzero closure point has a strictly
*negative* diagonal form.  It is Lemma FD (`FrontDiag.front_diag`) for the antipodal cell
(`U`, `Dn` swapped, view `-g`).  Type 24: `back_diag_0526` (diagonal `0 2` on the back facet `025`),
`back_diag_6402` (diagonal `6 0` on the back facet `046`), and the one-form Q4 leaves
`isRupert_q4_0526_of_pos`, `isRupert_q4_6402_of_pos`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.EdgeTilt
open Minimality Minimality.H21 Minimality.RimCell

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-! ### Theorem 8.10 on a rim cell, torque form -/

/-- At a view of an open rim cell all rim determinants (edge `i`, a vertex `q` off the edge) have
one common strict sign. -/
theorem cell_rim_dets {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) :
    (∀ i q, q ≠ c i → q ≠ c (i + 1) → 0 < det3 (x (c (i + 1)) - x (c i)) (x q - x (c i)) u) ∨
      (∀ i q, q ≠ c i → q ≠ c (i + 1) → det3 (x (c (i + 1)) - x (c i)) (x q - x (c i)) u < 0) := by
  obtain ⟨D⟩ := silL_of_cell F hcyc hu.cellLe hu
  choose μ hμ0 hd using h21b_exists_mu hk hx hc D
  have hQ : ∀ i q, q ≠ c i → q ≠ c (i + 1) →
      0 < D.fA i (x q) * ⟪D.B i, u⟫ - D.fB i (x q) * ⟪D.A i, u⟫ := by
    intro i q h0 h1
    rcases h21b_Q_pos D i q h0 h1 with h | ⟨_, h⟩
    · exact h
    · exact h
  rcases h21b_sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · left; intro i q h0 h1
    rw [h21b_det_eq D i (μ i) (hd i) q u]; exact mul_pos (hp i) (hQ i q h0 h1)
  · right; intro i q h0 h1
    rw [h21b_det_eq D i (μ i) (hd i) q u]; exact mul_neg_of_neg_of_pos (hn i) (hQ i q h0 h1)

/-- **Theorem 8.10 at a cell view, torque form.**  A rim cell (`S0xCycUD`), a view `u` in the open
cell, a depth-separated pair `(a, b)` of the rim at `u` whose torque vector is not orthogonal to `u`:
Rupert.  Either orientation of the rim. -/
theorem isRupert_of_cellAt_depthSep_torque (F : S0xFac m S x) (hx : Function.Injective x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u)
    {a b : ZMod k} (hds : DepthSepAt (fun i => x (c i)) u a b)
    (hW : ⟪Wv (x (c (a + 1)) - x (c a)) (x (c b) - x (c a)), u⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hW
  have hpV : ∀ i, x (c i) ∈ univ.image x := fun i => mem_image_of_mem _ (mem_univ _)
  have hoff : ∀ v ∈ univ.image x, (∀ j, v ≠ x (c j)) → ∃ q, v = x q ∧ ∀ j, q ≠ c j := by
    intro v hv hvp
    obtain ⟨q, -, rfl⟩ := mem_image.1 hv
    exact ⟨q, rfl, fun j h => hvp j (by rw [h])⟩
  have hne : ∀ i j : ZMod k, j ≠ i → c j ≠ c i := fun i j h e => h (hc e)
  rcases cell_rim_dets hk F hx hc hcyc hu with hp | hn
  · refine isRupert_of_rimView_depthSeparated_torque _ u hu0 hk (fun i => x (c i)) hpV
      (fun i j hj hj' => hp i (c j) (hne i j hj) (hne (i + 1) j hj')) ?_ hds hW
    intro v hv hvp i
    obtain ⟨q, rfl, hq⟩ := hoff v hv hvp
    exact hp i q (hq i) (hq (i + 1))
  · refine isRupert_of_rimView_depthSeparated_torque _ (-u) (neg_ne_zero.2 hu0) hk
      (fun i => x (c i)) hpV (fun i j hj hj' => ?_) ?_ hds.neg ?_
    · rw [det3_neg_right']; exact neg_pos.2 (hn i (c j) (hne i j hj) (hne (i + 1) j hj'))
    · intro v hv hvp i
      obtain ⟨q, rfl, hq⟩ := hoff v hv hvp
      rw [det3_neg_right']; exact neg_pos.2 (hn i q (hq i) (hq (i + 1)))
    · rwa [inner_neg_right, neg_ne_zero]

/-- Weak facings at `u₀`, each facet edge-on at `u₀` strictly signed along `d`: the tilt `u₀ + ε d`
is eventually in the open cell. -/
theorem ev_cellAt_tilt (F : S0xFac m S x) {U Dn : Finset (Fin m)} {u₀ d : ℝ³}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u₀⟫ ∨ (⟪F.N t, u₀⟫ = 0 ∧ 0 < ⟪F.N t, d⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, u₀⟫ < 0 ∨ (⟪F.N t, u₀⟫ = 0 ∧ ⟪F.N t, d⟫ < 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u₀ + ε • d) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ t ∈ U, 0 < ⟪F.N t, u₀ + ε • d⟫) ∧
      ∀ t ∈ Dn, ⟪F.N t, u₀ + ε • d⟫ < 0 := by
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · rcases hU t ht with h | ⟨h0, h1⟩
      · have hc : Continuous fun ε : ℝ => ⟪F.N t, u₀ + ε • d⟫ := by fun_prop
        exact nhdsWithin_le_nhds (hc.continuousAt (x := 0) |>.eventually
          (lt_mem_nhds (by simpa using h)))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [inner_add_right, inner_smul_right, h0, zero_add]
        exact mul_pos hε h1
    · rcases hD t ht with h | ⟨h0, h1⟩
      · have hc : Continuous fun ε : ℝ => ⟪F.N t, u₀ + ε • d⟫ := by fun_prop
        exact nhdsWithin_le_nhds (hc.continuousAt (x := 0) |>.eventually
          (gt_mem_nhds (by simpa using h)))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [inner_add_right, inner_smul_right, h0, zero_add]
        exact mul_neg_of_pos_of_neg hε h1
  exact hev

/-- **Theorem 8.10 along a tilt, torque form.**  The tilt `u₀ + ε d` is eventually in the open rim
cell and the pair is eventually depth-separated; the torque vector is not orthogonal to `u₀` or
to `d`. -/
theorem isRupert_of_cellTilt_depthSep_torque (F : S0xFac m S x) (hx : Function.Injective x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u₀ d : ℝ³}
    (hcell : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u₀ + ε • d)) {a b : ZMod k}
    (hds : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepAt (fun i => x (c i)) (u₀ + ε • d) a b)
    (hW : ⟪Wv (x (c (a + 1)) - x (c a)) (x (c b) - x (c a)), u₀⟫ ≠ 0 ∨
      ⟪Wv (x (c (a + 1)) - x (c a)) (x (c b) - x (c a)), d⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  obtain ⟨ε, h1, h2, h3⟩ := (hcell.and (hds.and (ev_Wv_ne hW))).exists
  exact isRupert_of_cellAt_depthSep_torque F hx hk hc hcyc h1 h2 h3

/-! ### Lemma EV-Tilt -/

/-- `F₁` (through `p`, not `v₁`) is strictly back along `λ (x v₁ - x p) + (x v₂ - x p)`, `λ > 0`,
for any vertex `v₂` (Carbon takes `v₂ ∈ F₁`; not needed). -/
theorem evTilt_back₁ (F : S0xFac m S x) {t : Fin m} {p v₁ : Fin n} (hp : p ∈ S t)
    (hv₁ : v₁ ∉ S t) (v₂ : Fin n) {l : ℝ} (hl : 0 < l) :
    ⟪F.N t, l • (x v₁ - x p) + (x v₂ - x p)⟫ < 0 := by
  rw [inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub, F.zero t p hp]
  have := F.neg t v₁ hv₁
  have := F.le t v₂
  nlinarith

/-- `F₂` (through `p`, not `v₂`) is strictly back along `λ (x v₁ - x p) + (x v₂ - x p)`, `λ ≥ 0`,
for any vertex `v₁`. -/
theorem evTilt_back₂ (F : S0xFac m S x) {t : Fin m} {p v₂ : Fin n} (hp : p ∈ S t)
    (v₁ : Fin n) (hv₂ : v₂ ∉ S t) {l : ℝ} (hl : 0 ≤ l) :
    ⟪F.N t, l • (x v₁ - x p) + (x v₂ - x p)⟫ < 0 := by
  rw [inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub, F.zero t p hp]
  have := F.neg t v₂ hv₂
  have := F.le t v₁
  nlinarith

/-- `⟪a × b, c × d⟫ = ⟪a, c⟫ ⟪b, d⟫ - ⟪a, d⟫ ⟪b, c⟫` (Binet-Cauchy). -/
theorem inner_cross_cross (a b c d : ℝ³) :
    ⟪cross a b, cross c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  ring

/-- **The edge frame.**  `n₁` vanishes on `u` but not on `b₁`; `n₂` vanishes on `u`, `b₁` but not
on `b₂`; `u ≠ 0`.  Then a vector orthogonal to `u`, `b₁`, `b₂` is zero (`n₁` need not vanish on
`b₂`: `u ≠ 0`, `b₁ ∉ ℝ u`, `b₂ ∉ span (u, b₁)` is all that is used). -/
theorem eq_zero_of_perp_frame {W u b₁ b₂ n₁ n₂ : ℝ³} (hu : u ≠ 0)
    (h1u : ⟪n₁, u⟫ = 0) (h1b₁ : ⟪n₁, b₁⟫ ≠ 0)
    (h2u : ⟪n₂, u⟫ = 0) (h2b₁ : ⟪n₂, b₁⟫ = 0) (h2b₂ : ⟪n₂, b₂⟫ ≠ 0)
    (hWu : ⟪W, u⟫ = 0) (hW₁ : ⟪W, b₁⟫ = 0) (hW₂ : ⟪W, b₂⟫ = 0) : W = 0 := by
  have hD : det3 u b₁ b₂ ≠ 0 := by
    intro hD0
    have e := det3_smul_eq u b₁ b₂ n₂
    rw [hD0, zero_smul, h2u, h2b₁, zero_smul, zero_smul, zero_add, zero_add] at e
    have hx : cross u b₁ = 0 := by
      rcases smul_eq_zero.1 e.symm with h | h
      · exact absurd h h2b₂
      · exact h
    have hbc := inner_cross_cross u b₁ u n₁
    rw [hx, inner_zero_left, real_inner_comm n₁ b₁, real_inner_comm n₁ u, h1u, zero_mul,
      sub_zero] at hbc
    have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu
    rcases mul_eq_zero.1 hbc.symm with h | h
    · exact huu.ne' h
    · exact h1b₁ h
  have e := det3_smul_eq u b₁ b₂ W
  rw [hWu, hW₁, hW₂, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at e
  exact (smul_eq_zero.1 e).resolve_left hD

/-- At a parallel pair the edge and the corner are not collinear (`k ≥ 2`). -/
theorem det_ne_zero_of_parPairAt {k : ℕ} [NeZero k] (hk : 2 ≤ k) {p : ZMod k → ℝ³} {u : ℝ³}
    {a b : ZMod k} (h : ParPairAt p u a b) : det3 (p (a + 1) - p a) (p b - p a) u ≠ 0 := by
  intro h0
  have hb : b + 1 ≠ b := by
    intro e
    have h1 : (1 : ZMod k) = 0 := by linear_combination e
    have : Fact (1 < k) := ⟨by omega⟩
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at h2; omega
  have := h (b + 1) hb
  rw [h0, mul_zero] at this
  exact lt_irrefl _ this

/-- The torque vector of a non-collinear pair is nonzero. -/
theorem Wv_ne_zero {E V u : ℝ³} (h : det3 E V u ≠ 0) : Wv E V ≠ 0 := by
  intro hW
  have hE : E ≠ 0 := by rintro rfl; simp [det3_expand] at h
  have hEE : 0 < ⟪E, E⟫ := real_inner_self_pos.2 hE
  have e : ⟪E, E⟫ • V = ⟪V, E⟫ • E := by
    unfold Wv at hW; exact (sub_eq_zero.1 hW).symm
  have k1 : det3 E (⟪E, E⟫ • V) u = ⟪E, E⟫ * det3 E V u := by
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have k2 : det3 E (⟪V, E⟫ • E) u = 0 := by
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, k2] at k1
  exact h ((mul_eq_zero.1 k1.symm).resolve_left hEE.ne')

/-- The torque vector of a parallel pair is nonzero. -/
theorem Wv_ne_zero_of_parPairAt {k : ℕ} [NeZero k] (hk : 2 ≤ k) {p : ZMod k → ℝ³} {u : ℝ³}
    {a b : ZMod k} (h : ParPairAt p u a b) : Wv (p (a + 1) - p a) (p b - p a) ≠ 0 :=
  Wv_ne_zero (det_ne_zero_of_parPairAt hk h)

/-- A nonzero `W` that is zero only if orthogonal to `u`, `b₁`, `b₂` is not orthogonal to `u` or to
`λ b₁ + b₂`, for `λ = 1` or `λ = 2`. -/
theorem exists_tilt_Wv_ne {W u b₁ b₂ : ℝ³} (hW : W ≠ 0)
    (hfr : ⟪W, u⟫ = 0 → ⟪W, b₁⟫ = 0 → ⟪W, b₂⟫ = 0 → W = 0) :
    ∃ l : ℝ, (l = 1 ∨ l = 2) ∧ (⟪W, u⟫ ≠ 0 ∨ ⟪W, l • b₁ + b₂⟫ ≠ 0) := by
  by_cases hu : ⟪W, u⟫ = 0
  · by_cases h1 : ⟪W, (1 : ℝ) • b₁ + b₂⟫ = 0
    · refine ⟨2, Or.inr rfl, Or.inr fun h2 => hW (hfr hu ?_ ?_)⟩
      · rw [inner_add_right, real_inner_smul_right] at h1 h2; linarith
      · rw [inner_add_right, real_inner_smul_right] at h1 h2; linarith
    · exact ⟨1, Or.inl rfl, Or.inr h1⟩
  · exact ⟨1, Or.inl rfl, Or.inl hu⟩

/-- **Lemma EV-Tilt, frame form.**  At the edge `pJ = F₁ ∩ F₂` with `v₁ ∈ F₂ \ F₁` and `v₂ ∉ F₂`
(`v₂ ∈ F₁` is not needed here), a vector orthogonal to `x J - x p`, `x v₁ - x p`, `x v₂ - x p` is
zero. -/
theorem eq_zero_of_perp_edgeFrame (F : S0xFac m S x) {F₁ F₂ : Fin m} {p J v₁ v₂ : Fin n}
    (hJp : x J ≠ x p) (hp₁ : p ∈ S F₁) (hp₂ : p ∈ S F₂) (hJ₁ : J ∈ S F₁) (hJ₂ : J ∈ S F₂)
    (hv₁ : v₁ ∈ S F₂) (hv₁' : v₁ ∉ S F₁) (hv₂' : v₂ ∉ S F₂) {W : ℝ³}
    (hWu : ⟪W, x J - x p⟫ = 0) (hW₁ : ⟪W, x v₁ - x p⟫ = 0) (hW₂ : ⟪W, x v₂ - x p⟫ = 0) :
    W = 0 := by
  refine eq_zero_of_perp_frame (sub_ne_zero.2 hJp) (n₁ := F.N F₁) (n₂ := F.N F₂) ?_ ?_ ?_ ?_ ?_
    hWu hW₁ hW₂
  · rw [F.inner_sub, F.zero _ _ hJ₁, F.zero _ _ hp₁, sub_zero]
  · rw [F.inner_sub, F.zero _ _ hp₁, sub_zero]; exact (F.neg _ _ hv₁').ne
  · rw [F.inner_sub, F.zero _ _ hJ₂, F.zero _ _ hp₂, sub_zero]
  · rw [F.inner_sub, F.zero _ _ hv₁, F.zero _ _ hp₂, sub_zero]
  · rw [F.inner_sub, F.zero _ _ hp₂, sub_zero]; exact (F.neg _ _ hv₂').ne

/-- **Edge-view 8.10 leaf in the link chamber, tilt form.**  Edge view `u₀ = x J - x p` of the edge
`pJ = F₁ ∩ F₂` (`v₁ ∉ F₁`, `v₂ ∉ F₂`), tilt `d = λ (x v₁ - x p) + (x v₂ - x p)`, `λ > 0`
(both `F₁`, `F₂` back: the chamber hiding `p`).  The other facets of the rim cell face weakly at
`u₀`, each edge-on one strictly along `d`; the pair is eventually depth-separated along the tilt
and its torque vector is not orthogonal to `u₀` or to `d`. -/
theorem isRupert_edgeView_link_torque_tilt (F : S0xFac m S x) (hx : Function.Injective x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {F₁ F₂ : Fin m} {p J v₁ v₂ : Fin n}
    (hp₁ : p ∈ S F₁) (hp₂ : p ∈ S F₂) (hJ₁ : J ∈ S F₁) (hJ₂ : J ∈ S F₂)
    (hv₁' : v₁ ∉ S F₁) (hv₂' : v₂ ∉ S F₂) {l : ℝ} (hl : 0 < l)
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, x J - x p⟫ ∨
      (⟪F.N t, x J - x p⟫ = 0 ∧ 0 < ⟪F.N t, l • (x v₁ - x p) + (x v₂ - x p)⟫))
    (hD : ∀ t ∈ Dn, t ≠ F₁ → t ≠ F₂ → ⟪F.N t, x J - x p⟫ < 0 ∨
      (⟪F.N t, x J - x p⟫ = 0 ∧ ⟪F.N t, l • (x v₁ - x p) + (x v₂ - x p)⟫ < 0))
    {a b : ZMod k}
    (hds : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      DepthSepAt (fun i => x (c i)) (x J - x p + ε • (l • (x v₁ - x p) + (x v₂ - x p))) a b)
    (hW : ⟪Wv (x (c (a + 1)) - x (c a)) (x (c b) - x (c a)), x J - x p⟫ ≠ 0 ∨
      ⟪Wv (x (c (a + 1)) - x (c a)) (x (c b) - x (c a)), l • (x v₁ - x p) + (x v₂ - x p)⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  refine isRupert_of_cellTilt_depthSep_torque F hx hk hc hcyc (ev_cellAt_tilt F hU ?_) hds hW
  intro t ht
  by_cases h1 : t = F₁
  · subst h1
    refine Or.inr ⟨?_, evTilt_back₁ F hp₁ hv₁' v₂ hl⟩
    rw [F.inner_sub, F.zero _ _ hJ₁, F.zero _ _ hp₁, sub_zero]
  by_cases h2 : t = F₂
  · subst h2
    refine Or.inr ⟨?_, evTilt_back₂ F hp₂ v₁ hv₂' hl.le⟩
    rw [F.inner_sub, F.zero _ _ hJ₂, F.zero _ _ hp₂, sub_zero]
  exact hD t ht h1 h2

/-- **Edge-view 8.10 leaf in the link chamber (Lemma EV-Tilt).**  Edge view `u₀ = x J - x p` of the
edge `pJ = F₁ ∩ F₂` with `v₁ ∈ F₂ \ F₁` and `v₂ ∉ F₂`.  A rim cell (`S0xCycUD S c U Dn`) whose
up facets face strictly up at `u₀` and whose down facets other than `F₁`, `F₂` face strictly down,
and a parallel pair `(a, b)` of the rim at `u₀` that the depths at `u₀` separate: Rupert.  No
horizontal-double-normal (`NoHDNRim`), foot, torque or Cauchy-Schwarz hypothesis: the tilt
`λ (x v₁ - x p) + (x v₂ - x p)` turns `F₁` and `F₂` back for every `λ > 0`, and as
`x J - x p, x v₁ - x p, x v₂ - x p` is a frame, `λ = 1` or `λ = 2` makes the (nonzero) torque vector
non-orthogonal to the view or the tilt. -/
theorem isRupert_edgeView_link_torque (F : S0xFac m S x) (hx : Function.Injective x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {F₁ F₂ : Fin m} {p J v₁ v₂ : Fin n}
    (hp₁ : p ∈ S F₁) (hp₂ : p ∈ S F₂) (hJ₁ : J ∈ S F₁) (hJ₂ : J ∈ S F₂)
    (hv₁ : v₁ ∈ S F₂) (hv₁' : v₁ ∉ S F₁) (hv₂' : v₂ ∉ S F₂)
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, x J - x p⟫)
    (hD : ∀ t ∈ Dn, t ≠ F₁ → t ≠ F₂ → ⟪F.N t, x J - x p⟫ < 0)
    {a b : ZMod k} (hpp : ParPairAt (fun i => x (c i)) (x J - x p) a b)
    (hz : DepthSepZ (fun i => ⟪x (c i), x J - x p⟫) a b) : IsRupert (univ.image x) := by
  have hJp : x J ≠ x p := by
    intro h
    obtain ⟨t, ht, -⟩ := hcyc 0
    have := hU t ht
    rw [h, sub_self, inner_zero_right] at this
    exact lt_irrefl _ this
  have hW0 := Wv_ne_zero_of_parPairAt (by omega) hpp
  obtain ⟨l, hl, hW⟩ := exists_tilt_Wv_ne hW0
    (eq_zero_of_perp_edgeFrame F hJp hp₁ hp₂ hJ₁ hJ₂ hv₁ hv₁' hv₂')
  have hl0 : 0 < l := by rcases hl with rfl | rfl <;> norm_num
  set d := l • (x v₁ - x p) + (x v₂ - x p)
  exact isRupert_edgeView_link_torque_tilt F hx hk hc hcyc hp₁ hp₂ hJ₁ hJ₂ hv₁' hv₂' hl0
    (fun t ht => Or.inl (hU t ht)) (fun t ht h1 h2 => Or.inl (hD t ht h1 h2))
    (((FaceCircle.ev_parPairAt d hpp).and (FaceCircle.ev_depthSepZ d hz)).mono fun _ h => depthSepAt_of h.1 h.2) hW

/-- **Type 24, view `x 3 - x 2`, rim `1 6 3 5 0` (the link of `2`), depth-separated form.**  As
`EdgeViewLink.isRupert_edgeView23` (`016`, `046` front), with a parallel pair of the rim that the
depths at `x 3 - x 2` separate in place of unimodal depths.  Edge `23 = 235 ∩ 236`, `v₁ = 6`,
`v₂ = 5`. -/
theorem isRupert_edgeView23_ds {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x)
    (hB : 0 < ⟪F.N 1, x 3 - x 2⟫) (hE : 0 < ⟪F.N 4, x 3 - x 2⟫) {a b : ZMod 5}
    (hpp : ParPairAt (fun i => x (EdgeViewLink.cLink i)) (x 3 - x 2) a b)
    (hz : DepthSepZ (fun i => ⟪x (EdgeViewLink.cLink i), x 3 - x 2⟫) a b) :
    IsRupert (univ.image x) := by
  have up3 : ∀ t, (3 : Fin 7) ∈ T24.SAT.s0x_S24 t → (2 : Fin 7) ∉ T24.SAT.s0x_S24 t →
      0 < ⟪F.N t, x 3 - x 2⟫ := fun t h3 h2 => by
    rw [F.inner_sub, F.zero t 3 h3]; have := F.neg t 2 h2; linarith
  have dn2 : ∀ t, (2 : Fin 7) ∈ T24.SAT.s0x_S24 t → (3 : Fin 7) ∉ T24.SAT.s0x_S24 t →
      ⟪F.N t, x 3 - x 2⟫ < 0 := fun t h2 h3 => by
    rw [F.inner_sub, F.zero t 2 h2]; have := F.neg t 3 h3; linarith
  refine isRupert_edgeView_link_torque F (EdgeViewLink.inj_of_fac24 F) (by norm_num)
    EdgeViewLink.inj_cLink EdgeViewLink.cyc_cLink (F₁ := 6) (F₂ := 7) (p := 2) (J := 3) (v₁ := 6)
    (v₂ := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun t ht => ?_) (fun t ht h6 h7 => ?_) hpp hz
  · simp only [EdgeViewLink.ULink, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hB
    · exact up3 3 (by decide) (by decide)
    · exact hE
    · exact up3 8 (by decide) (by decide)
  · simp only [EdgeViewLink.DLink, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact dn2 0 (by decide) (by decide)
    · exact dn2 2 (by decide) (by decide)
    · exact dn2 5 (by decide) (by decide)
    · exact absurd rfl h6
    · exact absurd rfl h7

/-! ### Lemma BD: the back diagonal -/

theorem S0xCycUD.swap {k : ℕ} [NeZero k] {c : ZMod k → Fin n} {U Dn : Finset (Fin m)}
    (h : S0xCycUD S c U Dn) : S0xCycUD S c Dn U := by
  intro i
  obtain ⟨a, ha, b, hb, h0a, h0b, h1a, h1b, hs⟩ := h i
  exact ⟨b, hb, a, ha, h0b, h0a, h1b, h1a, fun q h0 h1 => (hs q h0 h1).symm⟩

theorem CellAt.neg {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u : ℝ³} (h : CellAt F U Dn u) :
    CellAt F Dn U (-u) :=
  ⟨fun t ht => by rw [inner_neg_right]; linarith [h.2 t ht],
    fun t ht => by rw [inner_neg_right]; linarith [h.1 t ht]⟩

theorem CellLe.neg {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u : ℝ³} (h : CellLe F U Dn u) :
    CellLe F Dn U (-u) :=
  ⟨fun t ht => by rw [inner_neg_right]; linarith [h.2 t ht],
    fun t ht => by rw [inner_neg_right]; linarith [h.1 t ht]⟩

/-- **Lemma BD** (back diagonal), metric-free.  Rim `c` of four vertices of a closed cell (`a` in
the open cell, `g` a nonzero point of the closed cell): if the diagonal `c 0, c 2` lies on a facet
`t` facing away from the view (`t` down) and `c 1`, `c 3` are not both on `t`, then some diagonal
form `⟪x (c i) - x (c j), g⟫` (`i` even, `j` odd) is negative.  Lemma FD for the antipodal cell. -/
theorem back_diag (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a g : ℝ³}
    (ha : CellAt F U Dn a) (hg : CellLe F U Dn g) (hg0 : g ≠ 0) {t : Fin m} (ht : t ∈ Dn)
    (h0 : c 0 ∈ S t) (h2 : c 2 ∈ S t) (h13 : c 1 ∉ S t ∨ c 3 ∉ S t) :
    ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0 := by
  obtain ⟨p, hp, h⟩ := T24.FrontDiag.front_diag F hx hc (S0xCycUD.swap hcyc) (CellAt.neg ha) (CellLe.neg hg)
    (neg_ne_zero.2 hg0) ht h0 h2 h13
  exact ⟨p, hp, by rw [inner_neg_right] at h; linarith⟩

/-- **Q4 from one positive form** (twin of `RimCellClosed.isRupert_of_closedCell_q4` with Lemma BD
supplying the negative form): back diagonal `c 0, c 2` on a down facet, one closure point with a
positive diagonal form. -/
theorem isRupert_q4_of_backDiag (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a g : ℝ³} (ha : CellAt F U Dn a) (hg : CellLe F U Dn g)
    {t : Fin m} (ht : t ∈ Dn) (h0 : c 0 ∈ S t) (h2 : c 2 ∈ S t) (h13 : c 1 ∉ S t ∨ c 3 ∉ S t)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g⟫) : IsRupert (univ.image x) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨p, -, hp⟩ := hp
    simp at hp
  exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg (back_diag F hx hc hcyc ha hg hg0 ht h0 h2 h13)
    hp

section Type24
open Minimality.T24.SAT Minimality.T24.TheoremP

theorem diagPairs_cases : ∀ p ∈ diagPairs, p = (0, 1) ∨ p = (0, 3) ∨ p = (2, 1) ∨ p = (2, 3) := by
  decide

/-- **Lemma BD on the cell 0526** (rim `0 5 2 6`): the diagonal `0 2` lies on the back facet `025`,
so at every nonzero point of the closed cell some diagonal form is negative: `z0 < z5`, `z0 < z6`,
`z2 < z5` or `z2 < z6` (`z = ⟪x ·, g⟫`), for every metric. -/
theorem back_diag_0526 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a g : ℝ³}
    (ha : CellAt F U0526 D0526 a) (hg : CellLe F U0526 D0526 g) (hg0 : g ≠ 0) :
    ⟪x 0, g⟫ < ⟪x 5, g⟫ ∨ ⟪x 0, g⟫ < ⟪x 6, g⟫ ∨ ⟪x 2, g⟫ < ⟪x 5, g⟫ ∨ ⟪x 2, g⟫ < ⟪x 6, g⟫ := by
  obtain ⟨p, hp, h⟩ := back_diag F (Minimality.H24.SAT.inj_of_fac F) inj_c0526 cyc0526 ha hg hg0
    (t := 2) (by decide) (by decide) (by decide) (Or.inr (by decide))
  rcases diagPairs_cases p hp with rfl | rfl | rfl | rfl <;>
    simp only [c0526, Matrix.cons_val, inner_sub_left] at h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **Q4 on 0526 from one positive form**: one point `g` of the closed cell with `z5 < z0`,
`z6 < z0`, `z5 < z2` or `z6 < z2` gives `IsRupert`; the negative form comes from Lemma BD. -/
theorem isRupert_q4_0526_of_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a g : ℝ³}
    (ha : CellAt F U0526 D0526 a) (hg : CellLe F U0526 D0526 g)
    (hp : ⟪x 5, g⟫ < ⟪x 0, g⟫ ∨ ⟪x 6, g⟫ < ⟪x 0, g⟫ ∨ ⟪x 5, g⟫ < ⟪x 2, g⟫ ∨
      ⟪x 6, g⟫ < ⟪x 2, g⟫) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_q4_of_backDiag F (Minimality.H24.SAT.inj_of_fac F) inj_c0526 cyc0526 ha hg
    (t := 2) (by decide) (by decide) (by decide) (Or.inr (by decide)) ?_
  rcases hp with h | h | h | h
  · exact ⟨(0, 1), by decide, by simp only [c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(0, 3), by decide, by simp only [c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(2, 1), by decide, by simp only [c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(2, 3), by decide, by simp only [c0526, Matrix.cons_val, inner_sub_left]; linarith⟩

/-- **Lemma BD on the cell 6402** (rim `6 4 0 2`, the cell 0264): the diagonal `6 0` lies on the
back facet `046`, so at every nonzero point of the closed cell `z6 < z4`, `z6 < z2`, `z0 < z4` or
`z0 < z2`, for every metric. -/
theorem back_diag_6402 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a g : ℝ³}
    (ha : CellAt F U6402 D6402 a) (hg : CellLe F U6402 D6402 g) (hg0 : g ≠ 0) :
    ⟪x 6, g⟫ < ⟪x 4, g⟫ ∨ ⟪x 6, g⟫ < ⟪x 2, g⟫ ∨ ⟪x 0, g⟫ < ⟪x 4, g⟫ ∨ ⟪x 0, g⟫ < ⟪x 2, g⟫ := by
  obtain ⟨p, hp, h⟩ := back_diag F (Minimality.H24.SAT.inj_of_fac F) inj_c6402 cyc6402 ha hg hg0
    (t := 4) (by decide) (by decide) (by decide) (Or.inr (by decide))
  rcases diagPairs_cases p hp with rfl | rfl | rfl | rfl <;>
    simp only [c6402, Matrix.cons_val, inner_sub_left] at h
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **Q4 on 6402 from one positive form**: `z4 < z6`, `z2 < z6`, `z4 < z0` or `z2 < z0` at one
point of the closed cell gives `IsRupert`. -/
theorem isRupert_q4_6402_of_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {a g : ℝ³}
    (ha : CellAt F U6402 D6402 a) (hg : CellLe F U6402 D6402 g)
    (hp : ⟪x 4, g⟫ < ⟪x 6, g⟫ ∨ ⟪x 2, g⟫ < ⟪x 6, g⟫ ∨ ⟪x 4, g⟫ < ⟪x 0, g⟫ ∨
      ⟪x 2, g⟫ < ⟪x 0, g⟫) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_q4_of_backDiag F (Minimality.H24.SAT.inj_of_fac F) inj_c6402 cyc6402 ha hg
    (t := 4) (by decide) (by decide) (by decide) (Or.inr (by decide)) ?_
  rcases hp with h | h | h | h
  · exact ⟨(0, 1), by decide, by simp only [c6402, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(0, 3), by decide, by simp only [c6402, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(2, 1), by decide, by simp only [c6402, Matrix.cons_val, inner_sub_left]; linarith⟩
  · exact ⟨(2, 3), by decide, by simp only [c6402, Matrix.cons_val, inner_sub_left]; linarith⟩

end Type24

end Minimality.EdgeTilt
