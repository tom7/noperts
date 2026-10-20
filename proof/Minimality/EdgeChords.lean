module

public import Minimality.Chords

@[expose] public section

/-!
# Edge crossings: Theorem 8.9 (Lemma T over an edge with any far chain)

FEWER-FACES-PROOFS.md, Theorem 8.9 with Lemma F. Two faces share the edge `vw`
and `u₀` is the view along it: `w = v − h u₀`, `h ≠ 0`, so `v` and `w` have
one screen position `p`. The faces project to the sides `[p, a]` and `[b, p]`
of the shadow (counterclockwise `p, a, …, b`); `A`, `B` are their *far ends*
(the vertices over `a`, `b`). Every other vertex of a face is a *middle*
(`EdgeMiddle`): on the face over `[p, a]` it is `c + s (A − c) + δ u₀`, on the
other `B + s (c − B) + δ u₀` (`0 < s < 1`, `δ ≠ 0`), where `c` is the axle end
of its chain: `v`, or `w` with `δ h < 0` (the chain of `w` lies beyond the
chord from `w`, on the side away from `v`).

`K_v` (the hull without the middles and `w`) is first-order free at `u₀`: in
certificate form, every point other than the middles, `v` and `w` has a local
certificate `TiltCert` at `u₀`, and `v` is the corner between `B` and `A`
moving strictly inward; the far ends also move strictly inward across the face
sides (`0 < det3 (A − v) (vel A) u₀`, `0 < det3 (v − B) (vel B) u₀`, with
`vel X = ω × X + τ`). Then some tilt `u₀ + ε d` is first-order free for all
small `ε > 0` (`exists_tilt_edgeChords`), and the point set is Rupert
(`isRupert_of_edgeChords`). The same statement with `v` and `w` exchanged
(`h ↦ −h`) is the case "`K_w` free".

The proof is Lemma F in determinant form. Write `ψ₁(X) = det3 (A − v) (vel X) u₀`,
`ψ₂(X) = det3 (v − B) (vel X) u₀` (positive: strictly inward across the face
sides; they do not change when `v` is replaced by `w` in the first slot), and
`G_j = ψ_j(X + u₀) − ψ_j(X)` (the depth derivative, `n_j · g` up to a negative
factor). The velocity is affine, so `ψ_j(w) = ψ_j(v) − h G_j` and at a middle
`ψ_j` is the chord ends' values interpolated plus `δ G_j` (`det3_vel_middle`).
The face `j` is *switched* (its `w`-chain is shown) when `h G_j < 0`; then
`ψ_j(w) > ψ_j(v) > 0` (Lemma F (ii)). The tilt `d` is chosen so that
`e_j(d) := det3 (·) u₀ d` (the exposure sign of face `j`'s middles) has
`e_j(d) G_j ≤ 0`: the exposed middles then have `δ G_j ≥ 0`, so their chord
tests are positive (Lemma F (i)). The four cases:
* no face switched (sector `S+` of `v`): `d = h ((A − v) + (B − v))`, `w` hidden
  in the triangle `v A B`;
* both switched (sector `S−`): `d = −h ((A − v) + (B − v))`, `w` the corner
  between `B` and `A` (`v` keeps its certificate: local tests survive tilts);
* one switched (a mixed sector): `d = h ((A − v) − η (B − v))` (or with `A`, `B`
  exchanged), close to the common boundary ray `h (A − v)` of the two sectors,
  with `w` the corner between `v` and `A` (the apex edge `vw` is a silhouette
  edge); its apex test is `ε · h² (ψ₁(w) + η Q)` (Lemma F (iii)).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

section Algebra

variable (A B v X Y u d ω τ : ℝ³) (h k ε η : ℝ)

theorem det3_shift_left : det3 (A - (v - h • u)) Y u = det3 (A - v) Y u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_shift_right : det3 ((v - h • u) - B) Y u = det3 (v - B) Y u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_shift_left' : det3 (A - (v - h • u)) u d = det3 (A - v) u d := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_shift_right' : det3 ((v - h • u) - B) u d = det3 (v - B) u d := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The velocity is affine: shifting the point along the view. -/
theorem det3_vel_shift :
    det3 X (cross ω (v - h • u) + τ) u = det3 X (cross ω v + τ) u - h * det3 X (cross ω u) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_shift_corner : det3 (A - (v - h • u)) (B - (v - h • u)) u = det3 (A - v) (B - v) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_shift_corner' : det3 ((v - h • u) - B) (A - B) u = det3 (A - v) (B - v) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_far_side : det3 (B - A) ((v - h • u) - A) u = det3 (A - v) (B - v) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_A : det3 (A - v) ((v - h • u) - v) (u + ε • d) = -(h * ε) * det3 (A - v) u d := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_B :
    det3 (v - B) ((v - h • u) - B) (u + ε • d) = -(h * ε) * det3 (v - B) u d := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_after :
    det3 (A - (v - h • u)) (v - (v - h • u)) (u + ε • d) = ε * (h * det3 (A - v) u d) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_after_vel : det3 ((v - h • u) - v) Y (u + ε • d) = ε * -(h * det3 u Y d) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_before :
    det3 (v - (v - h • u)) (B - (v - h • u)) (u + ε • d) = ε * (h * det3 (v - B) u d) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_axle_before_vel : det3 (v - (v - h • u)) Y (u + ε • d) = ε * (h * det3 u Y d) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_sym_A : det3 (A - v) u (h • ((A - v) + (B - v))) = -(h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_sym_B : det3 (v - B) u (h • ((A - v) + (B - v))) = -(h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixA_A :
    det3 (A - v) u (h • ((A - v) - η • (B - v))) = η * (h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixA_B :
    det3 (v - B) u (h • ((A - v) - η • (B - v))) = -(h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixA_vel : det3 u Y (h • ((A - v) - η • (B - v))) =
    h * (-det3 (A - v) Y u - η * det3 u Y (B - v)) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixB_B :
    det3 (v - B) u (h • ((B - v) - η • (A - v))) = η * (h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixB_A :
    det3 (A - v) u (h • ((B - v) - η • (A - v))) = -(h * det3 (A - v) (B - v) u) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mixB_vel : det3 u Y (h • ((B - v) - η • (A - v))) =
    h * (det3 (v - B) Y u - η * det3 u Y (A - v)) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

end Algebra

/-! ### The removed axle vertex `w = v − h u₀` at the tilt -/

section Axle

variable {V : Finset ℝ³} {u₀ ω τ v A B d : ℝ³} {h : ℝ}

/-- Sector `S+` of `v`: `w` is hidden in the triangle `v A B`. -/
theorem eventually_tiltCert_axle_hidden (hv : v ∈ V) (hA : A ∈ V) (hB : B ∈ V)
    (hC : 0 < det3 (A - v) (B - v) u₀) (h1 : h * det3 (A - v) u₀ d < 0)
    (h2 : h * det3 (v - B) u₀ d < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ (v - h • u₀) := by
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (A - v) ((v - h • u₀) - v) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_A]; nlinarith [mul_pos hε (neg_pos.mpr h1)]
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (v - B) ((v - h • u₀) - B) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_B]; nlinarith [mul_pos hε (neg_pos.mpr h2)]
  have e2 := eventually_det3_pos (a := B - A) (b := (v - h • u₀) - A) d
    (by rw [det3_far_side]; exact hC)
  filter_upwards [eventually_det3_pos d hC, e1, e2, e3] with ε f0 f1 f2 f3
  exact Or.inr ⟨v, hv, A, hA, B, hB, f0, f1, f2, f3⟩

/-- Sector `S−` of `v` (and any tilt): `w` is the corner between `B` and `A`. -/
theorem eventually_tiltCert_axle_corner (hA : A ∈ V) (hB : B ∈ V)
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (h1 : 0 < det3 (A - v) (cross ω (v - h • u₀) + τ) u₀)
    (h2 : 0 < det3 (v - B) (cross ω (v - h • u₀) + τ) u₀) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ (v - h • u₀) := by
  have e0 := eventually_det3_pos (a := A - (v - h • u₀)) (b := B - (v - h • u₀)) d
    (by rw [det3_shift_corner]; exact hC)
  have e1 := eventually_det3_pos (a := A - (v - h • u₀)) d (by rw [det3_shift_left]; exact h1)
  have e2 := eventually_det3_pos (a := (v - h • u₀) - B) d (by rw [det3_shift_right]; exact h2)
  filter_upwards [e0, e1, e2] with ε f0 f1 f2
  exact Or.inl ⟨B, hB, A, hA, f0, f1, f2⟩

/-- A mixed sector: `w` is the corner between `v` (the apex edge) and `A`. -/
theorem eventually_tiltCert_axle_after (hv : v ∈ V) (hA : A ∈ V)
    (h0 : 0 < h * det3 (A - v) u₀ d)
    (h1 : 0 < det3 (A - v) (cross ω (v - h • u₀) + τ) u₀)
    (h2 : h * det3 u₀ (cross ω (v - h • u₀) + τ) d < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ (v - h • u₀) := by
  have e0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < det3 (A - (v - h • u₀)) (v - (v - h • u₀)) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_after]; exact mul_pos hε h0
  have e1 := eventually_det3_pos (a := A - (v - h • u₀)) d (by rw [det3_shift_left]; exact h1)
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < det3 ((v - h • u₀) - v) (cross ω (v - h • u₀) + τ) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_after_vel]; exact mul_pos hε (by linarith)
  filter_upwards [e0, e1, e2] with ε f0 f1 f2
  exact Or.inl ⟨v, hv, A, hA, f0, f1, f2⟩

/-- A mixed sector: `w` is the corner between `B` and `v` (the apex edge). -/
theorem eventually_tiltCert_axle_before (hv : v ∈ V) (hB : B ∈ V)
    (h0 : 0 < h * det3 (v - B) u₀ d)
    (h1 : 0 < det3 (v - B) (cross ω (v - h • u₀) + τ) u₀)
    (h2 : 0 < h * det3 u₀ (cross ω (v - h • u₀) + τ) d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ (v - h • u₀) := by
  have e0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < det3 (v - (v - h • u₀)) (B - (v - h • u₀)) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_before]; exact mul_pos hε h0
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < det3 (v - (v - h • u₀)) (cross ω (v - h • u₀) + τ) (u₀ + ε • d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [det3_axle_before_vel]; exact mul_pos hε h2
  have e2 := eventually_det3_pos (a := (v - h • u₀) - B) d (by rw [det3_shift_right]; exact h1)
  filter_upwards [e0, e1, e2] with ε f0 f1 f2
  exact Or.inl ⟨B, hB, v, hv, f0, f1, f2⟩

end Axle

/-! ### The middles -/

/-- Lemma F (i), arithmetic: with the exposure sign `e` chosen against `G`, an
exposed middle (`δ e < 0`) has `δ G ≥ 0`, and its chord end (`v`: `k = 0`;
`w` on its own side: `k = h`, `δ h < 0`) moves strictly inward. -/
theorem edge_middle_sign {e G P h k δ : ℝ} (hδ : δ ≠ 0) (he : e ≠ 0) (heG : e * G ≤ 0)
    (hP : 0 < P) (hk : k = 0 ∨ (k = h ∧ δ * h < 0)) :
    0 < δ * e ∨ (δ * e < 0 ∧ 0 ≤ δ * G ∧ 0 < P - k * G) := by
  rcases lt_or_gt_of_ne (mul_ne_zero hδ he) with hn | hp
  · refine Or.inr ⟨hn, ?_, ?_⟩
    · have h0 : 0 ≤ (δ * e) * (e * G) := mul_nonneg_of_nonpos_of_nonpos hn.le heG
      have he2 : 0 < e * e := mul_self_pos.mpr he
      by_contra hneg
      push Not at hneg
      have : (δ * G) * (e * e) < 0 := mul_neg_of_neg_of_pos hneg he2
      nlinarith
    · have hG : 0 ≤ δ * G := by
        have h0 : 0 ≤ (δ * e) * (e * G) := mul_nonneg_of_nonpos_of_nonpos hn.le heG
        have he2 : 0 < e * e := mul_self_pos.mpr he
        by_contra hneg
        push Not at hneg
        have : (δ * G) * (e * e) < 0 := mul_neg_of_neg_of_pos hneg he2
        nlinarith
      rcases hk with rfl | ⟨rfl, hkh⟩
      · simpa using hP
      · have : (δ * k) * (δ * G) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hkh.le hG
        have hδ2 : 0 < δ * δ := mul_self_pos.mpr hδ
        have hkG : k * G ≤ 0 := by
          by_contra hpos
          push Not at hpos
          have : 0 < (k * G) * (δ * δ) := mul_pos hpos hδ2
          nlinarith
        linarith
  · exact Or.inl hp

/-- A middle of an edge crossing (FEWER-FACES-PROOFS.md Theorem 8.9): on the face
over `[p, a]` (far end `A`) it is `c + s (A − c) + δ u₀`, on the face over
`[b, p]` (far end `B`) it is `B + s (c − B) + δ u₀`, where `c` is the axle end of
its chain: `v`, or `w` with `δ h < 0` (`w = v − h u₀`). -/
def EdgeMiddle (u₀ v w A B : ℝ³) (h : ℝ) (m : ℝ³) : Prop :=
  ∃ c : ℝ³, ∃ s δ : ℝ, (c = v ∨ (c = w ∧ δ * h < 0)) ∧ 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    (m = c + s • (A - c) + δ • u₀ ∨ m = B + s • (c - B) + δ • u₀)

section Middle

variable {V : Finset ℝ³} {u₀ ω τ v A B d : ℝ³} {h k s δ : ℝ}

/-- A middle on the face over `[p, a]`, over the chord from `c = v − k u₀` to `A`. -/
theorem eventually_tiltCert_middleA (hc : v - k • u₀ ∈ V) (hA : A ∈ V) (hB : B ∈ V)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ : δ ≠ 0) (hk : k = 0 ∨ (k = h ∧ δ * h < 0))
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hAA : 0 < det3 (A - v) (cross ω A + τ) u₀)
    (he : det3 (A - v) u₀ d ≠ 0) (heG : det3 (A - v) u₀ d * det3 (A - v) (cross ω u₀) u₀ ≤ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ
      ((v - k • u₀) + s • (A - (v - k • u₀)) + δ • u₀) := by
  refine eventually_tiltCert_middle hc hA hB hs0 hs1 (by rw [det3_shift_corner]; exact hC) ?_
  rw [det3_shift_left', det3_vel_middle, det3_shift_left, det3_shift_left, det3_shift_left,
    det3_vel_shift]
  rcases edge_middle_sign hδ he heG hvA hk with h1 | ⟨h1, h2, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    nlinarith [mul_pos (show 0 < 1 - s by linarith) h3, mul_pos hs0 hAA]

/-- A middle on the face over `[b, p]`, over the chord from `B` to `c = v − k u₀`. -/
theorem eventually_tiltCert_middleB (hc : v - k • u₀ ∈ V) (hA : A ∈ V) (hB : B ∈ V)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ : δ ≠ 0) (hk : k = 0 ∨ (k = h ∧ δ * h < 0))
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀) (hBB : 0 < det3 (v - B) (cross ω B + τ) u₀)
    (he : det3 (v - B) u₀ d ≠ 0) (heG : det3 (v - B) u₀ d * det3 (v - B) (cross ω u₀) u₀ ≤ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ
      (B + s • ((v - k • u₀) - B) + δ • u₀) := by
  refine eventually_tiltCert_middle hB hc hA hs0 hs1 (by rw [det3_shift_corner']; exact hC) ?_
  rw [det3_shift_right', det3_vel_middle, det3_shift_right, det3_shift_right, det3_shift_right,
    det3_vel_shift]
  rcases edge_middle_sign hδ he heG hvB hk with h1 | ⟨h1, h2, h3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    nlinarith [mul_pos (show 0 < 1 - s by linarith) hBB, mul_pos hs0 h3]

/-- Every middle gets a certificate at a tilt with the exposure signs chosen
against the depth derivatives `G_j` (Lemma F (i)). -/
theorem eventually_tiltCert_edgeMiddle {w m : ℝ³} (hv : v ∈ V) (hwV : w ∈ V) (hA : A ∈ V)
    (hB : B ∈ V) (hw : w = v - h • u₀) (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀)
    (hAA : 0 < det3 (A - v) (cross ω A + τ) u₀) (hBB : 0 < det3 (v - B) (cross ω B + τ) u₀)
    (he1 : det3 (A - v) u₀ d ≠ 0) (heG1 : det3 (A - v) u₀ d * det3 (A - v) (cross ω u₀) u₀ ≤ 0)
    (he2 : det3 (v - B) u₀ d ≠ 0) (heG2 : det3 (v - B) u₀ d * det3 (v - B) (cross ω u₀) u₀ ≤ 0)
    (hm : EdgeMiddle u₀ v w A B h m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ m := by
  obtain ⟨c, s, δ, hc, hs0, hs1, hδ, hm⟩ := hm
  obtain ⟨k, rfl, hk, hcV⟩ : ∃ k : ℝ, c = v - k • u₀ ∧ (k = 0 ∨ (k = h ∧ δ * h < 0)) ∧
      v - k • u₀ ∈ V := by
    rcases hc with rfl | ⟨rfl, hδh⟩
    · exact ⟨0, by simp, Or.inl rfl, by simpa using hv⟩
    · exact ⟨h, hw, Or.inr ⟨rfl, hδh⟩, by rw [← hw]; exact hwV⟩
  rcases hm with rfl | rfl
  · exact eventually_tiltCert_middleA hcV hA hB hs0 hs1 hδ hk hC hvA hAA he1 heG1
  · exact eventually_tiltCert_middleB hcV hA hB hs0 hs1 hδ hk hC hvB hBB he2 heG2

end Middle

/-! ### The choice of tilt -/

/-- **The choice of tilt (Lemma F).** There is a tilt `d` whose exposure signs
`e_j(d)` are nonzero and opposite to the depth derivatives `G_j`, at which `w`
has a certificate for all small `ε`. -/
theorem exists_tilt_axle (V : Finset ℝ³) (u₀ ω τ v A B : ℝ³) (h : ℝ) (hh : h ≠ 0)
    (hv : v ∈ V) (hA : A ∈ V) (hB : B ∈ V) (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀) :
    ∃ d : ℝ³, (det3 (A - v) u₀ d ≠ 0 ∧ det3 (A - v) u₀ d * det3 (A - v) (cross ω u₀) u₀ ≤ 0) ∧
      (det3 (v - B) u₀ d ≠ 0 ∧ det3 (v - B) u₀ d * det3 (v - B) (cross ω u₀) u₀ ≤ 0) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ (v - h • u₀) := by
  set G1 := det3 (A - v) (cross ω u₀) u₀
  set G2 := det3 (v - B) (cross ω u₀) u₀
  set C := det3 (A - v) (B - v) u₀
  have hhC : 0 < h * h * C := mul_pos (mul_self_pos.mpr hh) hC
  -- `ψ_j(w) = ψ_j(v) − h G_j`
  have hψ1 : det3 (A - v) (cross ω (v - h • u₀) + τ) u₀ = det3 (A - v) (cross ω v + τ) u₀ - h * G1 :=
    det3_vel_shift _ _ _ _ _ _
  have hψ2 : det3 (v - B) (cross ω (v - h • u₀) + τ) u₀ = det3 (v - B) (cross ω v + τ) u₀ - h * G2 :=
    det3_vel_shift _ _ _ _ _ _
  by_cases s1 : 0 ≤ h * G1 <;> by_cases s2 : 0 ≤ h * G2
  · -- sector `S+` of `v`: `w` hidden
    refine ⟨h • ((A - v) + (B - v)), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [det3_sym_A]; exact neg_ne_zero.mpr (mul_ne_zero hh hC.ne')
    · rw [det3_sym_A]; nlinarith
    · rw [det3_sym_B]; exact neg_ne_zero.mpr (mul_ne_zero hh hC.ne')
    · rw [det3_sym_B]; nlinarith
    · refine eventually_tiltCert_axle_hidden hv hA hB hC ?_ ?_
      · rw [det3_sym_A]; nlinarith
      · rw [det3_sym_B]; nlinarith
  · -- a mixed sector: face 2 switched, `d` near the ray `h (B − v)`
    push Not at s2
    have hw2 : 0 < det3 (v - B) (cross ω (v - h • u₀) + τ) u₀ := by rw [hψ2]; linarith
    set Q := det3 u₀ (cross ω (v - h • u₀) + τ) (A - v)
    obtain ⟨η, hη, hηQ⟩ := ((show ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η from self_mem_nhdsWithin).and
      (eventually_pos_affine (B := -Q) (Or.inl hw2))).exists
    have hη' : (0 : ℝ) < η := hη
    refine ⟨h • ((B - v) - η • (A - v)), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [det3_mixB_A]; exact neg_ne_zero.mpr (mul_ne_zero hh hC.ne')
    · rw [det3_mixB_A]; nlinarith
    · rw [det3_mixB_B]; exact mul_ne_zero hη'.ne' (mul_ne_zero hh hC.ne')
    · rw [det3_mixB_B]; nlinarith [mul_pos hη' hC]
    · refine eventually_tiltCert_axle_before hv hB ?_ hw2 ?_
      · rw [det3_mixB_B]; nlinarith [mul_pos hη' hhC]
      · rw [det3_mixB_vel]; nlinarith [mul_self_pos.mpr hh]
  · -- a mixed sector: face 1 switched, `d` near the ray `h (A − v)`
    push Not at s1
    have hw1 : 0 < det3 (A - v) (cross ω (v - h • u₀) + τ) u₀ := by rw [hψ1]; linarith
    set Q := det3 u₀ (cross ω (v - h • u₀) + τ) (B - v)
    obtain ⟨η, hη, hηQ⟩ := ((show ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η from self_mem_nhdsWithin).and
      (eventually_pos_affine (B := Q) (Or.inl hw1))).exists
    have hη' : (0 : ℝ) < η := hη
    refine ⟨h • ((A - v) - η • (B - v)), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [det3_mixA_A]; exact mul_ne_zero hη'.ne' (mul_ne_zero hh hC.ne')
    · rw [det3_mixA_A]; nlinarith [mul_pos hη' hC]
    · rw [det3_mixA_B]; exact neg_ne_zero.mpr (mul_ne_zero hh hC.ne')
    · rw [det3_mixA_B]; nlinarith
    · refine eventually_tiltCert_axle_after hv hA ?_ hw1 ?_
      · rw [det3_mixA_A]; nlinarith [mul_pos hη' hhC]
      · rw [det3_mixA_vel]; nlinarith [mul_self_pos.mpr hh]
  · -- sector `S−` of `v`: both faces switched, `w` the corner between `B` and `A`
    push Not at s1 s2
    refine ⟨(-h) • ((A - v) + (B - v)), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [det3_sym_A]; exact neg_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hh) hC.ne')
    · rw [det3_sym_A]; nlinarith
    · rw [det3_sym_B]; exact neg_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hh) hC.ne')
    · rw [det3_sym_B]; nlinarith
    · exact eventually_tiltCert_axle_corner hA hB hC (by rw [hψ1]; linarith) (by rw [hψ2]; linarith)

/-! ### Theorem 8.9 -/

/-- **Theorem 8.9, tilt form (Lemma T over an edge with any far chain).** Two
faces share the edge `vw`, `w = v − h u₀` (`h ≠ 0`; `u₀` along the edge), with
far ends `A`, `B` and middles `M` (`EdgeMiddle`). If `K_v` is first-order free
at `u₀` (every point other than the middles, `v` and `w` has a local
certificate; `v` is the corner between `B` and `A` moving strictly inward; the
far ends move strictly inward across the face sides), then some tilt
`u₀ + ε d` is first-order free (with the same motion) for all small `ε > 0`. -/
theorem exists_tilt_edgeChords (V M : Finset ℝ³) (u₀ ω τ v w A B : ℝ³) (h : ℝ)
    (hv : v ∈ V) (hwV : w ∈ V) (hA : A ∈ V) (hB : B ∈ V) (hw : w = v - h • u₀) (hh : h ≠ 0)
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀)
    (hAA : 0 < det3 (A - v) (cross ω A + τ) u₀) (hBB : 0 < det3 (v - B) (cross ω B + τ) u₀)
    (hK : ∀ x ∈ V, x ∉ M → x ≠ v → x ≠ w → TiltCert V u₀ ω τ x)
    (hM : ∀ m ∈ M, EdgeMiddle u₀ v w A B h m) :
    ∃ d : ℝ³, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ V, TiltCert V (u₀ + ε • d) ω τ x := by
  classical
  obtain ⟨d, ⟨he1, heG1⟩, ⟨he2, heG2⟩, hwc⟩ := exists_tilt_axle V u₀ ω τ v A B h hh hv hA hB hC hvA hvB
  refine ⟨d, (eventually_all_finset V).mpr fun x hx => ?_⟩
  by_cases hxM : x ∈ M
  · exact eventually_tiltCert_edgeMiddle hv hwV hA hB hw hC hvA hvB hAA hBB he1 heG1 he2 heG2
      (hM x hxM)
  by_cases hxv : x = v
  · subst hxv
    have hcert : TiltCert V u₀ ω τ x := Or.inl ⟨B, hB, A, hA, hC, hvA, hvB⟩
    exact hcert.eventually_tilt d
  by_cases hxw : x = w
  · subst hxw; rw [hw]; exact hwc
  exact (hK x hx hxM hxv hxw).eventually_tilt d

/-- **Theorem 8.9 (edge crossings; Lemma T over an edge with any far chain).**
In certificate form: if `K_v` (the hull without the faces' middles and `w`) is
first-order free at the view `u₀` along the edge `vw`, the point set is
Rupert. (For `K_w`, exchange `v` and `w` and replace `h` by `−h`.) -/
theorem isRupert_of_edgeChords (V M : Finset ℝ³) (u₀ ω τ v w A B : ℝ³) (h : ℝ) (hu₀ : u₀ ≠ 0)
    (hv : v ∈ V) (hwV : w ∈ V) (hA : A ∈ V) (hB : B ∈ V) (hw : w = v - h • u₀) (hh : h ≠ 0)
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀)
    (hAA : 0 < det3 (A - v) (cross ω A + τ) u₀) (hBB : 0 < det3 (v - B) (cross ω B + τ) u₀)
    (hK : ∀ x ∈ V, x ∉ M → x ≠ v → x ≠ w → TiltCert V u₀ ω τ x)
    (hM : ∀ m ∈ M, EdgeMiddle u₀ v w A B h m) : IsRupert V := by
  obtain ⟨d, hd⟩ := exists_tilt_edgeChords V M u₀ ω τ v w A B h hv hwV hA hB hw hh hC hvA hvB
    hAA hBB hK hM
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • d ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • d := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hall⟩ := (hne.and hd).exists
  exact isRupert_of_tiltCert V (u₀ + ε • d) hε ω τ hall

end Minimality

end
