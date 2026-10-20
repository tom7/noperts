module

public import Minimality.Tilt
public import Mathlib.GroupTheory.CosetCover

@[expose] public section

/-!
# Faces seen edge-on cost nothing: Proposition 8.8 (the flat-corner lemma)

FEWER-FACES-PROOFS.md, Proposition 8.8. At a view `u₀` along some faces' planes,
each face projects to a segment (its *chord*, between two points `a`, `b`); its
other points (the *middles*) project into the open chord. A middle `m` is
`a + s (b − a) + δ u₀` with `0 < s < 1`: it differs from the point of the 3D
segment `[a, b]` over it by a depth offset `δ ≠ 0`. If the polytope without
its middles is first-order free at `u₀` (here: local certificates `TiltCert` at
`u₀` for every other point, with the chord ends moving strictly to the inner side
of their chord), then the whole point set is Rupert (`isRupert_of_chords`).

The proof tilts the view to `u₀ + ε v`. A middle with `δ · det3 (b − a) u₀ v > 0`
falls strictly inside the triangle `a b r` (`r` any point strictly on the inner
side of the chord); one with the opposite sign becomes a corner between `a` and
`b`, and moves inward iff `det3 (b − a) (ω × m + τ) u₀ > 0`. The velocity is
affine in the point: this determinant is the chord ends' values interpolated,
plus `δ · det3 (b − a) (ω × u₀) u₀` (`det3_vel_middle`). The tilt
`v = ω × u₀ + η v′` (`v′` off finitely many planes, `η` small) exposes exactly
the middles for which that extra term is `≥ 0` (`exists_tilt_chords`). This
replaces the paper's choice of quadrant, and needs no face structure: any set of
middles over chords works.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A strict determinant test at `u₀` survives small tilts. -/
theorem eventually_det3_pos {a b u₀ : ℝ³} (v : ℝ³) (h : 0 < det3 a b u₀) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (u₀ + ε • v) := by
  simp only [det3_add_smul]; exact eventually_pos_affine (Or.inl h)

/-- Local certificates (strict tests) survive small tilts. -/
theorem TiltCert.eventually_tilt {V : Finset ℝ³} {u₀ ω τ x : ℝ³} (v : ℝ³)
    (h : TiltCert V u₀ ω τ x) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • v) ω τ x := by
  rcases h with ⟨y₀, hy₀, y₁, hy₁, h0, h1, h2⟩ | ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩
  · filter_upwards [eventually_det3_pos v h0, eventually_det3_pos v h1,
      eventually_det3_pos v h2] with ε e0 e1 e2
    exact Or.inl ⟨y₀, hy₀, y₁, hy₁, e0, e1, e2⟩
  · filter_upwards [eventually_det3_pos v h0, eventually_det3_pos v h1,
      eventually_det3_pos v h2, eventually_det3_pos v h3] with ε e0 e1 e2 e3
    exact Or.inr ⟨a, ha, b, hb, c, hc, e0, e1, e2, e3⟩

section Algebra

variable (a b r u w X ω τ : ℝ³) (s δ : ℝ)

theorem det3_middle_side :
    det3 (b - a) (a + s • (b - a) + δ • u - a) w = δ * det3 (b - a) u w := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_middle_corner :
    det3 (b - (a + s • (b - a) + δ • u)) (a - (a + s • (b - a) + δ • u)) w =
      -(δ * det3 (b - a) u w) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_middle_r_b :
    det3 (r - b) (a + s • (b - a) + δ • u - b) u = (1 - s) * det3 (b - a) (r - a) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_middle_a_r :
    det3 (a - r) (a + s • (b - a) + δ • u - r) u = s * det3 (b - a) (r - a) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_middle_b_vel :
    det3 (b - (a + s • (b - a) + δ • u)) X u = (1 - s) * det3 (b - a) X u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_middle_a_vel :
    det3 (a + s • (b - a) + δ • u - a) X u = s * det3 (b - a) X u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- **The velocity is affine in the point**: at a middle, the chord test is the
chord ends' tests interpolated plus the depth offset times `det3 (b − a) (ω × u) u`. -/
theorem det3_vel_middle :
    det3 (b - a) (cross ω (a + s • (b - a) + δ • u) + τ) u =
      (1 - s) * det3 (b - a) (cross ω a + τ) u + s * det3 (b - a) (cross ω b + τ) u +
        δ * det3 (b - a) (cross ω u) u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_swap23 : det3 a u w = -det3 a w u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

end Algebra

/-- Finitely many nonzero vectors: some `v` is orthogonal to none of them. -/
theorem exists_inner_ne_zero {ι : Type*} (I : Finset ι) (n : ι → ℝ³) (hn : ∀ i ∈ I, n i ≠ 0) :
    ∃ v : ℝ³, ∀ i ∈ I, ⟪n i, v⟫ ≠ 0 := by
  classical
  let K : ι → Subspace ℝ ℝ³ := fun i => LinearMap.ker (innerₛₗ ℝ (n i))
  have htop : (⊤ : Subspace ℝ ℝ³) ∉ I.image K := by
    intro h
    obtain ⟨i, hi, hK⟩ := mem_image.mp h
    have : n i ∈ K i := by rw [hK]; trivial
    simp only [K, LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at this
    exact hn i hi this
  obtain ⟨v, hv⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp (Subspace.biUnion_ne_univ_of_top_notMem htop)
  refine ⟨v, fun i hi h => hv ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨K i, mem_image_of_mem K hi, by simp [K, h]⟩

/-- The data of a middle `m` over the chord `[a, b]` at the view `u₀`, with `r`
strictly on the inner side and the chord ends moving strictly to that side. -/
def ChordMiddle (V : Finset ℝ³) (u₀ ω τ m : ℝ³) : Prop :=
  ∃ a ∈ V, ∃ b ∈ V, ∃ r ∈ V, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    m = a + s • (b - a) + δ • u₀ ∧ 0 < det3 (b - a) (r - a) u₀ ∧
    0 < det3 (b - a) (cross ω a + τ) u₀ ∧ 0 < det3 (b - a) (cross ω b + τ) u₀

/-- One middle at a tilt `v`: hidden (inside the triangle `a b r`) when
`δ · det3 (b − a) u₀ v > 0`; exposed (a corner between `a` and `b`, moving
inward) when it is `< 0` and the chord test at `m` is positive. -/
theorem eventually_tiltCert_middle {V : Finset ℝ³} {u₀ v ω τ a b r : ℝ³} {s δ : ℝ}
    (ha : a ∈ V) (hb : b ∈ V) (hr : r ∈ V) (hs0 : 0 < s) (hs1 : s < 1)
    (hrin : 0 < det3 (b - a) (r - a) u₀)
    (hcase : 0 < δ * det3 (b - a) u₀ v ∨
      (δ * det3 (b - a) u₀ v < 0 ∧ 0 < det3 (b - a) (cross ω (a + s • (b - a) + δ • u₀) + τ) u₀)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • v) ω τ (a + s • (b - a) + δ • u₀) := by
  set m := a + s • (b - a) + δ • u₀ with hm
  have hu : det3 (b - a) u₀ u₀ = 0 := by
    simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring
  rcases hcase with hh | ⟨he, hvel⟩
  · -- hidden: strictly inside the triangle a b r
    have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - a) (m - a) (u₀ + ε • v) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [hm, det3_middle_side, det3_add_smul, hu, zero_add]
      have : 0 < ε * (δ * det3 (b - a) u₀ v) := mul_pos hε hh
      linarith
    have e2 := eventually_det3_pos v (show 0 < det3 (r - b) (m - b) u₀ by
      rw [hm, det3_middle_r_b]; exact mul_pos (by linarith) hrin)
    have e3 := eventually_det3_pos v (show 0 < det3 (a - r) (m - r) u₀ by
      rw [hm, det3_middle_a_r]; exact mul_pos hs0 hrin)
    filter_upwards [eventually_det3_pos v hrin, e1, e2, e3] with ε f0 f1 f2 f3
    exact Or.inr ⟨a, ha, b, hb, r, hr, f0, f1, f2, f3⟩
  · -- exposed: a corner between a (before) and b (after)
    have e0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - m) (a - m) (u₀ + ε • v) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [hm, det3_middle_corner, det3_add_smul, hu, zero_add]
      have : ε * (δ * det3 (b - a) u₀ v) < 0 := mul_neg_of_pos_of_neg hε he
      nlinarith
    have e1 := eventually_det3_pos v (show 0 < det3 (b - m) (cross ω m + τ) u₀ by
      rw [hm, det3_middle_b_vel]; exact mul_pos (by linarith) hvel)
    have e2 := eventually_det3_pos v (show 0 < det3 (m - a) (cross ω m + τ) u₀ by
      rw [hm, det3_middle_a_vel]; exact mul_pos hs0 hvel)
    filter_upwards [e0, e1, e2] with ε f0 f1 f2
    exact Or.inl ⟨a, ha, b, hb, f0, f1, f2⟩

/-- **The choice of tilt.** For finitely many middles there is a tilt `v` that
hides each middle or exposes it with a positive chord test. -/
theorem exists_tilt_chords {ι : Type*} (I : Finset ι) (u₀ ω τ : ℝ³) (a b : ι → ℝ³)
    (s δ : ι → ℝ) (hs0 : ∀ i ∈ I, 0 < s i) (hs1 : ∀ i ∈ I, s i < 1) (hδ : ∀ i ∈ I, δ i ≠ 0)
    (hn : ∀ i ∈ I, cross (b i - a i) u₀ ≠ 0)
    (ha : ∀ i ∈ I, 0 < det3 (b i - a i) (cross ω (a i) + τ) u₀)
    (hb : ∀ i ∈ I, 0 < det3 (b i - a i) (cross ω (b i) + τ) u₀) :
    ∃ v : ℝ³, ∀ i ∈ I, 0 < δ i * det3 (b i - a i) u₀ v ∨
      (δ i * det3 (b i - a i) u₀ v < 0 ∧
        0 < det3 (b i - a i) (cross ω (a i + s i • (b i - a i) + δ i • u₀) + τ) u₀) := by
  obtain ⟨v', hv'⟩ := exists_inner_ne_zero I (fun i => cross (b i - a i) u₀) hn
  set g := cross ω u₀
  -- for each middle, the property holds for all small η > 0 with v = g + η v'
  have key : ∀ i ∈ I, ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < δ i * det3 (b i - a i) u₀ (g + η • v') ∨
      (δ i * det3 (b i - a i) u₀ (g + η • v') < 0 ∧
        0 < det3 (b i - a i) (cross ω (a i + s i • (b i - a i) + δ i • u₀) + τ) u₀) := by
    intro i hi
    have hc : det3 (b i - a i) u₀ v' ≠ 0 := hv' i hi
    set A := δ i * det3 (b i - a i) u₀ g
    set B := δ i * det3 (b i - a i) u₀ v'
    have hB : B ≠ 0 := mul_ne_zero (hδ i hi) hc
    have hexp : A ≤ 0 →
        0 < det3 (b i - a i) (cross ω (a i + s i • (b i - a i) + δ i • u₀) + τ) u₀ := by
      intro hA
      rw [det3_vel_middle]
      have hsw : δ i * det3 (b i - a i) g u₀ = -A := by
        simp only [A]; rw [det3_swap23 (b i - a i) u₀ g]; ring
      have := ha i hi; have := hb i hi; have := hs0 i hi; have := hs1 i hi
      nlinarith [mul_pos (show 0 < 1 - s i by linarith) (ha i hi), mul_pos (hs0 i hi) (hb i hi)]
    have hlin : ∀ η : ℝ, δ i * det3 (b i - a i) u₀ (g + η • v') = A + η * B := by
      intro η; simp only [A, B, det3_add_smul]; ring
    rcases lt_trichotomy A 0 with hA | hA | hA
    · -- exposed for small η
      have hc' : Continuous fun η : ℝ => A + η * B := by fun_prop
      have hev : ∀ᶠ η in 𝓝 (0 : ℝ), A + η * B < 0 :=
        hc'.continuousAt.eventually (gt_mem_nhds (by simpa using hA))
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with η hη
      rw [hlin]; exact Or.inr ⟨hη, hexp hA.le⟩
    · -- tie: the sign of B decides, and either way the chord test is positive
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [hlin, hA, zero_add]
      rcases lt_or_gt_of_ne hB with hB' | hB'
      · exact Or.inr ⟨mul_neg_of_pos_of_neg hη hB', hexp hA.le⟩
      · exact Or.inl (mul_pos hη hB')
    · -- hidden for small η
      have hc' : Continuous fun η : ℝ => A + η * B := by fun_prop
      have hev : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < A + η * B :=
        hc'.continuousAt.eventually (lt_mem_nhds (by simpa using hA))
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with η hη
      rw [hlin]; exact Or.inl hη
  obtain ⟨η, hη⟩ := ((eventually_all_finset I).mpr key).exists
  exact ⟨g + η • v', hη⟩

/-- **Proposition 8.8 (faces seen edge-on cost nothing).** Let `M ⊆ V` be the
middles at the view `u₀` (each over a chord `[a, b]` with a depth offset
`δ ≠ 0`, `ChordMiddle`), and suppose every other point has a local certificate
of strict inward motion at `u₀` under `(ω, τ)` (the polytope without its middles
is first-order free there). Then `V` is Rupert. -/
theorem isRupert_of_chords (V M : Finset ℝ³) (u₀ ω τ : ℝ³) (hu₀ : u₀ ≠ 0)
    (hK : ∀ x ∈ V, x ∉ M → TiltCert V u₀ ω τ x)
    (hM : ∀ m ∈ M, ChordMiddle V u₀ ω τ m) : IsRupert V := by
  classical
  choose! a ha b hb r hr s δ hs0 hs1 hδ hm hrin hva hvb using hM
  have hn : ∀ m ∈ M, cross (b m - a m) u₀ ≠ 0 := by
    intro m hmM h
    have := hrin m hmM
    rw [show det3 (b m - a m) (r m - a m) u₀ = -⟪cross (b m - a m) u₀, r m - a m⟫ by
      rw [det3_swap23]; rfl, h, inner_zero_left, neg_zero] at this
    exact lt_irrefl _ this
  obtain ⟨v, hv⟩ := exists_tilt_chords M u₀ ω τ a b s δ hs0 hs1 hδ hn hva hvb
  have hcert : ∀ x ∈ V, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • v) ω τ x := by
    intro x hx
    by_cases hxM : x ∈ M
    · rw [hm x hxM]
      exact eventually_tiltCert_middle (ha x hxM) (hb x hxM) (hr x hxM) (hs0 x hxM)
        (hs1 x hxM) (hrin x hxM) (hv x hxM)
    · exact (hK x hx hxM).eventually_tilt v
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • v ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • v := by fun_prop
    have := hc.continuousAt.eventually (isOpen_ne.mem_nhds (show u₀ + (0 : ℝ) • v ≠ 0 by simpa using hu₀))
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hall⟩ := (hne.and ((eventually_all_finset V).mpr hcert)).exists
  exact isRupert_of_tiltCert V (u₀ + ε • v) hε ω τ hall

end Minimality

end
