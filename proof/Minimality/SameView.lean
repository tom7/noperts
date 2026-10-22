module

public import Minimality.Type24Circle
public import Minimality.RobustEdge

@[expose] public section

/-!
# The front diagonal and the same-view pair (Lemmas 20.25–20.27)

`FEWER-FACES-PROOFS.md` §20, continued (4), §38 and §42 (cu15 and its referee, 2026-10-22,
scratch `referee_cu15/`), at `K`'s own metric: the depth at a view `u` is `⟪·, u⟫`.  Since the
hypotheses are affine (rims, determinant signs, a segment through a triangle), this is the
paper's "at every metric" (§14.0: a metric `G` is the own metric of an affine image).

* **Lemma 20.26 (the front diagonal)** (`FrontDiag`, `FrontDiag.not_back`, `FrontDiag.fails4`):
  if over the crossing of the diagonals of a 4-corner rim the point of `[d₀, d₁]` lies in front
  of the point of `[e₀, e₁]` (their difference is `γ u` with `γ > 0`), the rim can fail only by
  `{d₀, d₁}` weakly above `{e₀, e₁}`.  No exclusion: the depth chain
  `z(Q_e) ≥ min e ≥ max d ≥ z(Q_d)` contradicts `z(Q_d) − z(Q_e) = γ ‖u‖² > 0` even at ties.
  The coplanar case `γ = 0` (`fails4_eq_of_meet`): a failure forces the four depths equal (this is
  Corollary 20.19 in crossing form; `planarQuad_fails4` is the coefficient form).
  The Cramer form (`frontDiag_of_rim`, `QuadTestR'.frontDiag`): for a strictly convex rim
  `(y, a, c, b)`, `{y, c}` is the front diagonal iff `[c − y, b − a, y − a]` has the sign of
  `[c − y, b − a, u]` (which is positive for a counterclockwise rim).
* **4-corner tests with ties** (`QuadTestR`, `QuadTestR'`, `QuadTestR'.isRupert`): `QuadTest`
  without the distinct depths; a test whose diagonals are not weakly separated (`¬ Fails4`,
  i.e. `NWS4`) is robustly unimodal (Theorem 18.3), so it certifies `V`.  `QuadTest` gives
  `QuadTestR` (`QuadTest'.toR`).
* **Lemma 20.26, Rupert form** (`isRupert_frontDiag`): a test with front diagonal `{y, c}`
  certifies `V` as soon as the forced order `{y, c} ≥ {a, b}` is violated.
* **Lemma 20.27 (the same-view pair)** (`isRupert_sameView_robust`, `isRupert_sameView`): two
  4-corner tests at one view `u` with front diagonals `F`, `F′` and back diagonals `B`, `B′`, with
  `p ∈ F ∩ B′` and `q ∈ B ∩ F′`: one of them does not fail, so `V` is Rupert.  With ties the only
  exclusion is `z_p = z_q`; with distinct rim depths (`QuadTest'`) there is none.  No metric
  hypothesis, no octant, no LP.
* **Corollary 20.27′ (the piercing form) is Lemma E** (§14, `isRupert_edgePair_robust`).  The two
  closings `K_v`, `K_w` of an edge crossing along `v w` have the same view `w − v` and the rims
  `(v, a, c, b)`, `(w, a, c, b)`; 20.27′'s rims `(y, a, b, c)`, `(x, a, b, c)` are these with
  `(x, y, a, b, c) ↦ (w, v, a, c, b)`, and "the segment `ac` pierces the triangle `xyb`" is Lemma
  E (ii), "`[a, b]` meets the triangle `(v, w, c)`".  Lemma E with ties (`edgePair_nws`) is
  stronger than 20.27′: the closed triangle, and only the three far depths equal excluded.
  Here: the piercing hypothesis as stated (`SegMeetsTri`, `isRupert_pierce`), either orientation
  of the rim (`isRupert_pierce'`).
* **Type 24** (§42's commonest pairs): **`isRupert_type24_pierce36`**, the edge crossing along
  `36` (faces `236`, `346`; closings `236/346-3` with the rim `(6, 4, 0, 2)` and `236/346-6` with
  the rim `(3, 4, 0, 2)`): if the segment `42` meets the triangle `360`, `K` is Rupert (census
  4,584 classes); its mirror **`isRupert_type24_pierce23`** (`2 ↔ 6`, `4 ↔ 5`: edge `23`, faces
  `236`, `235`, rims `(2, 5, 0, 6)`, `(3, 5, 0, 6)`, the segment `56` through the triangle `320`;
  census 2,707).  The rims (with `1` and `5`, resp. `1` and `4`, hidden) are hypotheses, as for
  every type-24 test; no `Type24` hypothesis is needed.  Exclusions: the three far depths equal,
  and a horizontal double normal of either closing.

Not formalized: Lemma 20.25 (the obtuse covectors), Theorem 20.21 and Lemmas 20.22–20.24, the
four piercing instances along the edges `34`, `35`, `05`, `04` of the quad `0345` (whose
closings have middles), the counts.  Ties and HDNs are explicit (the limit machinery of
`LimitRim.lean` is not used).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Lemma 20.26: the front diagonal -/

/-- **The diagonal `[d₀, d₁]` passes in front of `[e₀, e₁]` along `u`**: a point of `[d₀, d₁]`
minus a point of `[e₀, e₁]` is a positive multiple `γ u` of the view (Lemma 20.26: `γ > 0`,
`Q₁₃ − Q₂₄ = γ d`). -/
def FrontDiag (d₀ d₁ e₀ e₁ u : ℝ³) : Prop :=
  ∃ s t γ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ 0 < γ ∧
    (d₀ + s • (d₁ - d₀)) - (e₀ + t • (e₁ - e₀)) = γ • u

theorem FrontDiag.swap_e {d₀ d₁ e₀ e₁ u : ℝ³} (h : FrontDiag d₀ d₁ e₀ e₁ u) :
    FrontDiag d₀ d₁ e₁ e₀ u := by
  obtain ⟨s, t, γ, hs0, hs1, ht0, ht1, hγ, he⟩ := h
  refine ⟨s, 1 - t, γ, hs0, hs1, by linarith, by linarith, hγ, ?_⟩
  rw [← he]; module

theorem FrontDiag.swap_d {d₀ d₁ e₀ e₁ u : ℝ³} (h : FrontDiag d₀ d₁ e₀ e₁ u) :
    FrontDiag d₁ d₀ e₀ e₁ u := by
  obtain ⟨s, t, γ, hs0, hs1, ht0, ht1, hγ, he⟩ := h
  refine ⟨1 - s, t, γ, by linarith, by linarith, ht0, ht1, hγ, ?_⟩
  rw [← he]; module

/-- **Lemma 20.26, depth form.**  If `[d₀, d₁]` passes in front of `[e₀, e₁]` along `u ≠ 0`,
then `{d₀, d₁}` is never weakly below `{e₀, e₁}` at `u`, whatever the ties. -/
theorem FrontDiag.not_back {d₀ d₁ e₀ e₁ u : ℝ³} (h : FrontDiag d₀ d₁ e₀ e₁ u) (hu : u ≠ 0) :
    ¬ (max ⟪d₀, u⟫ ⟪d₁, u⟫ ≤ min ⟪e₀, u⟫ ⟪e₁, u⟫) := by
  obtain ⟨s, t, γ, hs0, hs1, ht0, ht1, hγ, he⟩ := h
  intro hle
  simp only [max_le_iff, le_min_iff] at hle
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hle
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have i5 := congrArg (fun x => ⟪x, u⟫) he
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at i5
  set D0 := ⟪d₀, u⟫
  set D1 := ⟪d₁, u⟫
  set E0 := ⟪e₀, u⟫
  set E1 := ⟪e₁, u⟫
  have k0 : D0 + s * (D1 - D0) ≤ E0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h1),
      mul_nonneg hs0 (sub_nonneg.mpr h2)]
  have k1 : D0 + s * (D1 - D0) ≤ E1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h3),
      mul_nonneg hs0 (sub_nonneg.mpr h4)]
  have k2 : D0 + s * (D1 - D0) ≤ E0 + t * (E1 - E0) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr k0),
      mul_nonneg ht0 (sub_nonneg.mpr k1)]
  nlinarith [mul_pos hγ huu]

/-- **Lemma 20.26, failure form**: a closed failure of a 4-corner rim with front diagonal
`{d₀, d₁}` is `{d₀, d₁}` weakly above `{e₀, e₁}` (the forced orders hold even at ties). -/
theorem FrontDiag.fails4 {d₀ d₁ e₀ e₁ u : ℝ³} (h : FrontDiag d₀ d₁ e₀ e₁ u) (hu : u ≠ 0)
    (hF : Fails4 d₀ d₁ e₀ e₁ u) : max ⟪e₀, u⟫ ⟪e₁, u⟫ ≤ min ⟪d₀, u⟫ ⟪d₁, u⟫ :=
  hF.resolve_left (h.not_back hu)

/-- **Lemma 20.26, the coplanar case `γ = 0`**: if the diagonals meet in space at interior
points, a closed failure forces the four depths to be equal. -/
theorem fails4_eq_of_meet {d₀ d₁ e₀ e₁ u : ℝ³} {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (he : d₀ + s • (d₁ - d₀) = e₀ + t • (e₁ - e₀))
    (hF : Fails4 d₀ d₁ e₀ e₁ u) :
    ⟪d₀, u⟫ = ⟪e₀, u⟫ ∧ ⟪d₁, u⟫ = ⟪e₀, u⟫ ∧ ⟪e₁, u⟫ = ⟪e₀, u⟫ := by
  have i5 := congrArg (fun x => ⟪x, u⟫) he
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at i5
  set D0 := ⟪d₀, u⟫
  set D1 := ⟪d₁, u⟫
  set E0 := ⟪e₀, u⟫
  set E1 := ⟪e₁, u⟫
  -- a convex combination at interior weights equal to a point weakly beyond both ends
  have key : ∀ {A0 A1 B0 B1 σ τ : ℝ}, 0 < σ → σ < 1 → 0 < τ → τ < 1 →
      A0 + σ * (A1 - A0) = B0 + τ * (B1 - B0) → A0 ≤ B0 → A0 ≤ B1 → A1 ≤ B0 → A1 ≤ B1 →
      A0 = B0 ∧ A1 = B0 ∧ B1 = B0 := by
    intro A0 A1 B0 B1 σ τ hσ0 hσ1 hτ0 hτ1 hE k1 k2 k3 k4
    have hA : 0 ≤ B0 - (A0 + σ * (A1 - A0)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hσ1.le) (sub_nonneg.mpr k1),
        mul_nonneg hσ0.le (sub_nonneg.mpr k3)]
    have hB : 0 ≤ B1 - (A0 + σ * (A1 - A0)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hσ1.le) (sub_nonneg.mpr k2),
        mul_nonneg hσ0.le (sub_nonneg.mpr k4)]
    have hsum : (1 - τ) * (B0 - (A0 + σ * (A1 - A0))) + τ * (B1 - (A0 + σ * (A1 - A0))) = 0 := by
      linear_combination (-1 : ℝ) * hE
    have z0 : (1 - τ) * (B0 - (A0 + σ * (A1 - A0))) = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hτ1.le) hA, mul_nonneg hτ0.le hB]
    have z1 : τ * (B1 - (A0 + σ * (A1 - A0))) = 0 := by linarith
    have e0 : B0 = A0 + σ * (A1 - A0) := by
      rcases mul_eq_zero.mp z0 with h | h
      · linarith
      · linarith
    have e1 : B1 = A0 + σ * (A1 - A0) := by
      rcases mul_eq_zero.mp z1 with h | h
      · linarith
      · linarith
    -- now `(1 − σ)(B0 − A0) + σ (B0 − A1) = 0` with both terms `≥ 0`
    have w0 : (1 - σ) * (B0 - A0) = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hσ1.le) (sub_nonneg.mpr k1),
        mul_nonneg hσ0.le (sub_nonneg.mpr k3)]
    have f0 : A0 = B0 := by
      rcases mul_eq_zero.mp w0 with h | h
      · linarith
      · linarith
    refine ⟨f0, ?_, by linarith⟩
    have : σ * (A1 - A0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  rcases hF with h | h
  · simp only [max_le_iff, le_min_iff] at h
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := h
    exact key hs0 hs1 ht0 ht1 i5 k1 k3 k2 k4
  · simp only [max_le_iff, le_min_iff] at h
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := h
    obtain ⟨f1, f2, f3⟩ := key ht0 ht1 hs0 hs1 i5.symm k1 k3 k2 k4
    exact ⟨by linarith, by linarith, by linarith⟩

/-- **Lemma 20.26, Cramer form** (`γ` as a determinant quotient).  For a strictly convex
counterclockwise rim `(y, a, c, b)` at `u`, the diagonal `[y, c]` is in front if
`[c − y, b − a, y − a] > 0` and `[a, b]` is in front if it is `< 0`.  (Over the crossing,
`(a + t (b − a)) − (y + s (c − y)) = μ u` with `μ [c − y, b − a, u] = −[c − y, b − a, y − a]`,
and `[c − y, b − a, u] > 0` is the rim's area.) -/
theorem frontDiag_of_rim {y a c b u : ℝ³}
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u) :
    (0 < det3 (c - y) (b - a) (y - a) → FrontDiag y c a b u) ∧
      (det3 (c - y) (b - a) (y - a) < 0 → FrontDiag a b y c u) := by
  have i1 : det3 (c - y) (a - y) u = -det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (c - y) (b - y) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i3 : det3 (b - a) (y - a) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (b - a) (c - a) u = -det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hsm : SegMeet y c a b u := by
    refine segMeet_of_sides ?_ ?_
    · rw [i1, i2]; nlinarith
    · rw [i3, i4]; nlinarith
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := hsm
  have hΔ : det3 (c - y) (b - a) u = det3 (a - y) (c - y) u + det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hΔ0 : 0 < det3 (c - y) (b - a) u := by rw [hΔ]; linarith
  have key : μ * det3 (c - y) (b - a) u = -det3 (c - y) (b - a) (y - a) := by
    have e := congrArg (fun X => det3 (c - y) (b - a) X) h
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination -e
  constructor
  · intro hΓ
    have hμ : μ < 0 := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hn hΔ0.le]
    refine ⟨s, t, -μ, hs0, hs1, ht0, ht1, by linarith, ?_⟩
    rw [neg_smul, ← h]; abel
  · intro hΓ
    have hμ : 0 < μ := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg (neg_nonneg.mpr hn) hΔ0.le]
    exact ⟨t, s, μ, ht0, ht1, hs0, hs1, hμ, h⟩

/-! ### 4-corner tests with ties -/

/-- **A 4-corner test with ties allowed**: `QuadTest` without the distinct depths.  The rim
`(y, a, c, b)` at the view `u` is strictly convex and counterclockwise, every point of `V` other
than the corners, the middles `M` and the doubles `D` is strictly inside, the middles lie over
sides of the rim and the doubles over its corners, and the rim has no horizontal double
normal. -/
def QuadTestR (V : Finset ℝ³) (u y a c b : ℝ³) : Prop :=
  ∃ M D Wn : Finset ℝ³, u ≠ 0 ∧ y ∈ V ∧ a ∈ V ∧ b ∈ V ∧ c ∈ V ∧ y ∉ M ∧ a ∉ M ∧ b ∉ M ∧
    c ∉ M ∧ 0 < det3 (a - y) (c - y) u ∧ 0 < det3 (c - a) (b - a) u ∧
    0 < det3 (b - c) (y - c) u ∧ 0 < det3 (y - b) (a - b) u ∧
    (∀ z ∈ V, z ∉ M → z ∉ D → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z) ∧
    (∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u) ∧
    (∀ d ∈ D, ∃ i : ZMod 4, ∃ h : ℝ, h ≠ 0 ∧ d = quad y a c b i - h • u) ∧
    NoHDNAt Wn u ∧ y ∈ Wn ∧ a ∈ Wn ∧ c ∈ Wn ∧ b ∈ Wn

/-- A 4-corner test with ties allowed, with the rim `(y, a, c, b)` in either orientation. -/
def QuadTestR' (V : Finset ℝ³) (u y a c b : ℝ³) : Prop :=
  QuadTestR V u y a c b ∨ QuadTestR V u y b c a

theorem QuadTest.toR {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest V u y a c b) :
    QuadTestR V u y a c b := by
  obtain ⟨M, D, Wn, hu, hyV, haV, hbV, hcV, hyM, haM, hbM, hcM, q₁, q₂, q₃, q₄, hrest, -, hM,
    hD, hnd, hW⟩ := h
  exact ⟨M, D, Wn, hu, hyV, haV, hbV, hcV, hyM, haM, hbM, hcM, q₁, q₂, q₃, q₄, hrest, hM, hD,
    hnd, hW⟩

theorem QuadTest'.toR {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest' V u y a c b) :
    QuadTestR' V u y a c b :=
  h.imp QuadTest.toR QuadTest.toR

theorem QuadTestR.ne_zero {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR V u y a c b) :
    u ≠ 0 := by
  obtain ⟨-, -, -, hu, -⟩ := h
  exact hu

theorem QuadTestR'.ne_zero {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR' V u y a c b) :
    u ≠ 0 := by
  rcases h with h | h
  exacts [h.ne_zero, h.ne_zero]

/-- A 4-corner rim whose diagonals are not weakly separated (`¬ Fails4`) is `NWS4`. -/
theorem nws4_of_not_fails4 {y a c b u : ℝ³} (hF : ¬ Fails4 y c a b u) :
    NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  refine ⟨?_, ?_⟩
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨k1, k2, k3, k4⟩ := hc
    exact hF (Or.inr (by
      simp only [max_le_iff, le_min_iff]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩))
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨k1, k2, k3, k4⟩ := hc
    exact hF (Or.inl (by
      simp only [max_le_iff, le_min_iff]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩))

/-- **A 4-corner test with ties certifies `V`** when its diagonals are not weakly separated
(Theorem 8.9 / Proposition 8.8 / Lemma 17.15 with Theorem 18.3 and Lemma 16.27′). -/
theorem QuadTestR.isRupert {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR V u y a c b)
    (hF : ¬ Fails4 y c a b u) : IsRupert V := by
  obtain ⟨M, D, Wn, hu, hyV, haV, hbV, hcV, hyM, haM, hbM, hcM, q₁, q₂, q₃, q₄, hrest, hM, hD,
    hnd, hW⟩ := h
  have hN := nws4_of_not_fails4 hF
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_uniform_robust V M D Wn u hu (k := 4) (by norm_num)
    (quad y a c b) ?_ ?_ ?_ ?_ ?_ hnd ?_ hM hD
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, haV, hcV, hbV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, haM, hcM, hbM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [q₁, by rw [i2]; exact q₄, q₂, by rw [i4]; exact q₁, q₃, by rw [i6]; exact q₂, q₄,
      by rw [i8]; exact q₃]
  · intro z hz hzM hzD hzx i
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzD (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact hN.isRobustUnimodal
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hW.1, hW.2.1, hW.2.2.1, hW.2.2.2]

/-- **A test with ties that does not fail certifies `V`** (either orientation). -/
theorem QuadTestR'.isRupert {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR' V u y a c b)
    (hF : ¬ Fails4 y c a b u) : IsRupert V := by
  rcases h with h | h
  · exact h.isRupert hF
  · exact h.isRupert (fun h' => hF (fails4_swap.mp h'))

/-- **Lemma 20.26, Cramer form, either orientation**: for a 4-corner test `(y, a, c, b)`,
`{y, c}` is the front diagonal when `[c − y, b − a, y − a]` and `[c − y, b − a, u]` have the
same sign (both products flip with the orientation). -/
theorem QuadTestR'.frontDiag {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR' V u y a c b)
    (hΓ : 0 < det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) u) :
    FrontDiag y c a b u := by
  rcases h with ⟨-, -, -, -, -, -, -, -, -, -, -, -, q₁, q₂, q₃, q₄, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, q₁, q₂, q₃, q₄, -⟩
  · have hΔ : det3 (c - y) (b - a) u = det3 (a - y) (c - y) u + det3 (b - c) (y - c) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have hΔ0 : 0 < det3 (c - y) (b - a) u := by rw [hΔ]; linarith
    exact (frontDiag_of_rim q₁ q₂ q₃ q₄).1 (pos_of_mul_pos_left hΓ hΔ0.le)
  · have hΔ : det3 (c - y) (a - b) u = det3 (b - y) (c - y) u + det3 (a - c) (y - c) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have hΔ0 : 0 < det3 (c - y) (a - b) u := by rw [hΔ]; linarith
    have e1 : det3 (c - y) (a - b) u = -det3 (c - y) (b - a) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (c - y) (a - b) (y - b) = -det3 (c - y) (b - a) (y - a) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have hΓ' : 0 < det3 (c - y) (a - b) (y - b) := by
      rw [e2]; rw [e1] at hΔ0; nlinarith
    exact ((frontDiag_of_rim q₁ q₂ q₃ q₄).1 hΓ').swap_e

/-- **Lemma 20.26, Rupert form.**  A 4-corner test (ties allowed) with front diagonal `{y, c}`
certifies `V` as soon as the order it forces, `{y, c}` weakly above `{a, b}`, is violated. -/
theorem isRupert_frontDiag {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTestR' V u y a c b)
    (hf : FrontDiag y c a b u) (hlt : min ⟪y, u⟫ ⟪c, u⟫ < max ⟪a, u⟫ ⟪b, u⟫) : IsRupert V :=
  h.isRupert fun hF => absurd (hf.fails4 h.ne_zero hF) (not_le.mpr hlt)

/-! ### Lemma 20.27: the same-view pair -/

/-- **Lemma 20.27 (the same-view pair), with ties.**  Two 4-corner tests at the same view `u`,
`τ` with the rim `(y, a, c, b)` and `τ′` with the rim `(y′, a′, c′, b′)` (either orientation),
with front diagonals `{y, c}` and `{y′, c′}` (Lemma 20.26).  If some `p` is on the front diagonal
of `τ` and the back diagonal of `τ′`, and some `q` on the back diagonal of `τ` and the front
diagonal of `τ′` (conflicting forced orders `p ≥ q` and `q ≥ p`), and `z_p ≠ z_q`, then one of
the tests does not fail, so `V` is Rupert.  No metric hypothesis: this holds at every metric
(both octants), with no LP. -/
theorem isRupert_sameView_robust {V : Finset ℝ³} {u y a c b y' a' c' b' p q : ℝ³}
    (h₁ : QuadTestR' V u y a c b) (h₂ : QuadTestR' V u y' a' c' b')
    (hf₁ : FrontDiag y c a b u) (hf₂ : FrontDiag y' c' a' b' u)
    (hp : (p = y ∨ p = c) ∧ (p = a' ∨ p = b')) (hq : (q = a ∨ q = b) ∧ (q = y' ∨ q = c'))
    (hpq : ⟪p, u⟫ ≠ ⟪q, u⟫) : IsRupert V := by
  have hu := h₁.ne_zero
  by_cases F1 : Fails4 y c a b u
  · by_cases F2 : Fails4 y' c' a' b' u
    · exfalso
      have k1 := hf₁.fails4 hu F1
      have k2 := hf₂.fails4 hu F2
      have lq : ⟪q, u⟫ ≤ max ⟪a, u⟫ ⟪b, u⟫ := by
        rcases hq.1 with e | e
        · rw [e]; exact le_max_left _ _
        · rw [e]; exact le_max_right _ _
      have lp : min ⟪y, u⟫ ⟪c, u⟫ ≤ ⟪p, u⟫ := by
        rcases hp.1 with e | e
        · rw [e]; exact min_le_left _ _
        · rw [e]; exact min_le_right _ _
      have lp' : ⟪p, u⟫ ≤ max ⟪a', u⟫ ⟪b', u⟫ := by
        rcases hp.2 with e | e
        · rw [e]; exact le_max_left _ _
        · rw [e]; exact le_max_right _ _
      have lq' : min ⟪y', u⟫ ⟪c', u⟫ ≤ ⟪q, u⟫ := by
        rcases hq.2 with e | e
        · rw [e]; exact min_le_left _ _
        · rw [e]; exact min_le_right _ _
      exact hpq (le_antisymm (by linarith) (by linarith))
    · exact h₂.isRupert F2
  · exact h₁.isRupert F1

/-- **Lemma 20.27 (the same-view pair).**  As `isRupert_sameView_robust`, for tests certified
with distinct rim depths (`QuadTest'`): then `z_p ≠ z_q` is automatic (`p` and `q` lie on
different diagonals of `τ`), so the only exclusions are those of the tests (their ties and
horizontal double normals). -/
theorem isRupert_sameView {V : Finset ℝ³} {u y a c b y' a' c' b' p q : ℝ³}
    (h₁ : QuadTest' V u y a c b) (h₂ : QuadTest' V u y' a' c' b')
    (hf₁ : FrontDiag y c a b u) (hf₂ : FrontDiag y' c' a' b' u)
    (hp : (p = y ∨ p = c) ∧ (p = a' ∨ p = b')) (hq : (q = a ∨ q = b) ∧ (q = y' ∨ q = c')) :
    IsRupert V := by
  obtain ⟨-, n1, n2, n3, n4⟩ := h₁.cross_ne
  refine isRupert_sameView_robust h₁.toR h₂.toR hf₁ hf₂ hp hq ?_
  rcases hp.1 with e | e <;> rcases hq.1 with f | f <;> rw [e, f]
  exacts [n1, n2, n3, n4]

/-! ### Corollary 20.27′ (the piercing form) = Lemma E -/

/-- The segment `[a, b]` meets the closed triangle `(v, w, c)` iff `[b, a]` does. -/
theorem SegMeetsTri.swap {a b v w c : ℝ³} (h : SegMeetsTri a b v w c) : SegMeetsTri b a v w c := by
  obtain ⟨t, α, β, γ, ht0, ht1, hα, hβ, hγ, hsum, he⟩ := h
  refine ⟨1 - t, α, β, γ, by linarith, by linarith, hα, hβ, hγ, hsum, ?_⟩
  rw [← he]; module

/-- **The piercing condition is Lemma E (iii)**: at an edge crossing along `v w` with the
strictly convex counterclockwise shadow `(q, P a, P c, P b)`, if the segment `[a, b]` meets the
triangle `(v, w, c)`, then `v`, `w` lie weakly on opposite sides of the plane `abc`. -/
theorem det_le_of_pierce {v w a b c : ℝ³}
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hP : SegMeetsTri a b v w c) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0 := by
  have e2 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hsm : SegMeet v c a b (w - v) := by
    refine segMeet_of_sides ?_ ?_
    · have e1 : det3 (c - v) (a - v) (w - v) = -det3 (a - v) (c - v) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e3 : det3 (c - v) (b - v) (w - v) = det3 (b - c) (v - c) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e3]; nlinarith
    · have e1 : det3 (b - a) (v - a) (w - v) = det3 (v - b) (a - b) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e2]; nlinarith
  have hL : det3 (b - a) (c - a) (w - v) ≠ 0 := by rw [e2]; linarith
  exact (edgePair_tri_iff hsm hL).mp hP

/-- **Corollary 20.27′ (the piercing form), Rupert, with ties.**  Faces at the edge `v w`, view
`u = w − v`; the closings `K_v`, `K_w` have the rims `(v, a, c, b)`, `(w, a, c, b)` (the shadow
strictly convex and counterclockwise, every other point a middle or hidden).  If the segment
`[a, b]` meets the triangle `(v, w, c)` (20.27′: "`ac` pierces `xyb`", with
`(x, y, a, b, c) ↦ (w, v, a, c, b)`), one closing is robustly unimodal, so `V` is Rupert unless
`z_a = z_c = z_b` or the closing has a horizontal double normal.  This is Lemma E
(`isRupert_edgePair_robust`) with (ii) for (iii). -/
theorem isRupert_pierce {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hP : SegMeetsTri a b v w c)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V :=
  isRupert_edgePair_robust V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄
    (det_le_of_pierce q₁ q₂ q₃ q₄ hP) h3 hV hnd₁ hnd₂

/-- The four triple tests of a strictly convex counterclockwise quadrilateral `(y, a, c, b)` at
`u`. -/
def Ccw4 (u y a c b : ℝ³) : Prop :=
  0 < det3 (a - y) (c - y) u ∧ 0 < det3 (c - a) (b - a) u ∧ 0 < det3 (b - c) (y - c) u ∧
    0 < det3 (y - b) (a - b) u

/-- **Corollary 20.27′, either orientation, with no middles**: the shadow `(q, P a, P c, P b)` is
strictly convex in either orientation, and every point other than `v, w, a, b, c` is strictly
inside it. -/
theorem isRupert_pierce' {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hrim : (Ccw4 (w - v) v a c b ∧ ∀ z ∈ V, z ≠ v → z ≠ w → z ≠ a → z ≠ b → z ≠ c →
        EdgeHidden (w - v) v a c b z) ∨
      (Ccw4 (w - v) v b c a ∧ ∀ z ∈ V, z ≠ v → z ≠ w → z ≠ a → z ≠ b → z ≠ c →
        EdgeHidden (w - v) v b c a z))
    (hP : SegMeetsTri a b v w c)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  classical
  rcases hrim with ⟨⟨q₁, q₂, q₃, q₄⟩, hin⟩ | ⟨⟨q₁, q₂, q₃, q₄⟩, hin⟩
  · refine isRupert_pierce V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄ hP h3 ?_ hnd₁ hnd₂
    intro z hz
    by_cases e1 : z = v; · exact Or.inl e1
    by_cases e2 : z = w; · exact Or.inr (Or.inl e2)
    by_cases e3 : z = a; · exact Or.inr (Or.inr (Or.inl e3))
    by_cases e4 : z = b; · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
    by_cases e5 : z = c; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e5))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hin z hz e1 e2 e3 e4 e5))))))
  · refine isRupert_pierce V hvV hwV hbV haV hcV q₁ q₂ q₃ q₄ hP.swap
      (fun ⟨k1, k2⟩ => h3 ⟨k2.symm, k1.symm⟩) ?_ hnd₁ hnd₂
    intro z hz
    by_cases e1 : z = v; · exact Or.inl e1
    by_cases e2 : z = w; · exact Or.inr (Or.inl e2)
    by_cases e3 : z = b; · exact Or.inr (Or.inr (Or.inl e3))
    by_cases e4 : z = a; · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
    by_cases e5 : z = c; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e5))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hin z hz e1 e2 e4 e3 e5))))))

/-! ### Type 24: the pairs along `36` and `23` -/

/-- **Lemma 20.27 for type 24, the commonest pair: "`42` pierces `360`"** (census 4,584
classes).  The edge crossing along `36` (faces `236`, `346`), view `x 3 − x 6`: the closings
`236/346-3` (keep `6`) and `236/346-6` (keep `3`) have the rims `(6, 4, 0, 2)` and
`(3, 4, 0, 2)` (either orientation), with `1` and `5` hidden.  If the segment `[x 4, x 2]` meets
the triangle `(x 6, x 3, x 0)`, the point set is Rupert, unless `4, 0, 2` have equal depths at
the view or the closing found has a horizontal double normal. -/
theorem isRupert_type24_pierce36 {x : Fin 7 → ℝ³}
    (hrim : (Ccw4 (x 3 - x 6) (x 6) (x 4) (x 0) (x 2) ∧
        EdgeHidden (x 3 - x 6) (x 6) (x 4) (x 0) (x 2) (x 1) ∧
        EdgeHidden (x 3 - x 6) (x 6) (x 4) (x 0) (x 2) (x 5)) ∨
      (Ccw4 (x 3 - x 6) (x 6) (x 2) (x 0) (x 4) ∧
        EdgeHidden (x 3 - x 6) (x 6) (x 2) (x 0) (x 4) (x 1) ∧
        EdgeHidden (x 3 - x 6) (x 6) (x 2) (x 0) (x 4) (x 5)))
    (hP : SegMeetsTri (x 4) (x 2) (x 6) (x 3) (x 0))
    (h3 : ¬ (⟪x 4, x 3 - x 6⟫ = ⟪x 0, x 3 - x 6⟫ ∧ ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫))
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 3)) (x 3 - x 6))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 6)) (x 3 - x 6)) :
    IsRupert (univ.image x) := by
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hid : ∀ {P : ℝ³ → Prop}, P (x 1) → P (x 5) → ∀ z ∈ univ.image x, z ≠ x 6 → z ≠ x 3 →
      z ≠ x 4 → z ≠ x 2 → z ≠ x 0 → P z := by
    intro P h1 h5 z hz n6 n3 n4 n2 n0
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    fin_cases i
    · exact absurd rfl n0
    · exact h1
    · exact absurd rfl n2
    · exact absurd rfl n3
    · exact absurd rfl n4
    · exact h5
    · exact absurd rfl n6
  refine isRupert_pierce' _ (mem 6) (mem 3) (mem 4) (mem 2) (mem 0) ?_ hP h3 hnd₁ hnd₂
  rcases hrim with ⟨hc, h1, h5⟩ | ⟨hc, h1, h5⟩
  · exact Or.inl ⟨hc, hid h1 h5⟩
  · exact Or.inr ⟨hc, hid h1 h5⟩

/-- **Lemma 20.27 for type 24, the mirror pair: "`56` pierces `320`"** (`2 ↔ 6`, `4 ↔ 5`;
census 2,707 classes).  The edge crossing along `23` (faces `236`, `235`), view `x 3 − x 2`:
the closings `236/235-3` (keep `2`) and `236/235-2` (keep `3`) have the rims `(2, 5, 0, 6)` and
`(3, 5, 0, 6)` (either orientation), with `1` and `4` hidden.  If the segment `[x 5, x 6]` meets
the triangle `(x 2, x 3, x 0)`, the point set is Rupert, unless `5, 0, 6` have equal depths at
the view or the closing found has a horizontal double normal. -/
theorem isRupert_type24_pierce23 {x : Fin 7 → ℝ³}
    (hrim : (Ccw4 (x 3 - x 2) (x 2) (x 5) (x 0) (x 6) ∧
        EdgeHidden (x 3 - x 2) (x 2) (x 5) (x 0) (x 6) (x 1) ∧
        EdgeHidden (x 3 - x 2) (x 2) (x 5) (x 0) (x 6) (x 4)) ∨
      (Ccw4 (x 3 - x 2) (x 2) (x 6) (x 0) (x 5) ∧
        EdgeHidden (x 3 - x 2) (x 2) (x 6) (x 0) (x 5) (x 1) ∧
        EdgeHidden (x 3 - x 2) (x 2) (x 6) (x 0) (x 5) (x 4)))
    (hP : SegMeetsTri (x 5) (x 6) (x 2) (x 3) (x 0))
    (h3 : ¬ (⟪x 5, x 3 - x 2⟫ = ⟪x 0, x 3 - x 2⟫ ∧ ⟪x 0, x 3 - x 2⟫ = ⟪x 6, x 3 - x 2⟫))
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 3)) (x 3 - x 2))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 2)) (x 3 - x 2)) :
    IsRupert (univ.image x) := by
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hid : ∀ {P : ℝ³ → Prop}, P (x 1) → P (x 4) → ∀ z ∈ univ.image x, z ≠ x 2 → z ≠ x 3 →
      z ≠ x 5 → z ≠ x 6 → z ≠ x 0 → P z := by
    intro P h1 h4 z hz n2 n3 n5 n6 n0
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    fin_cases i
    · exact absurd rfl n0
    · exact h1
    · exact absurd rfl n2
    · exact absurd rfl n3
    · exact h4
    · exact absurd rfl n5
    · exact absurd rfl n6
  refine isRupert_pierce' _ (mem 2) (mem 3) (mem 5) (mem 6) (mem 0) ?_ hP h3 hnd₁ hnd₂
  rcases hrim with ⟨hc, h1, h4⟩ | ⟨hc, h1, h4⟩
  · exact Or.inl ⟨hc, hid h1 h4⟩
  · exact Or.inr ⟨hc, hid h1 h4⟩

end Minimality

end
