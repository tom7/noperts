module

public import Minimality.UnimodalCert
public import Minimality.EdgePair

@[expose] public section

/-!
# The uniform tilt: Lemmas 16.27 and 16.27′ (`FEWER-FACES-PROOFS.md` §16, part K)

Theorems 8.8 and 8.9 with the single tilt `ω × u₀`.  An edge crossing along `vw`
(`w = v − h u₀`, far ends `A`, `B`) whose reduced polytope `K_v` is first-order free at `u₀`
under a motion `(ω, τ)`, together with any finite set `M` of middles over chords
(`ChordMiddle`: the chord ends move strictly inward across the chord; this covers the middles
of the two faces at `vw`, over the chords from `v`, and the middles of further faces seen
edge-on, e.g. a far face parallel to the view).  Then one tilt works for everything:
`d = g + η v′` with `g = ω × u₀`, `v′` generic and `η > 0` small.  With this `d` a middle is
exposed only when its depth offset helps it (`Chords.lean`), and the removed axle vertex `w`
gets a certificate in each of the four sectors of Lemma F (`EdgeChords.lean`'s axle lemmas).
The apex test in a mixed sector is the screen Plücker identity `det3_plucker_screen`.

* **Lemma 16.27** — `isRupert_of_edgeChords_uniform` (local certificates), with Theorem 7.3
  `isRupert_of_edgeChords_uniform_unimodal` (`K_v`'s silhouette a unimodal polygon, each middle
  over one of its sides).  The pieces: `eventually_chord_choice` (one middle),
  `eventually_axle_uniform` (the axle, four sectors), the identities `det3_plucker_screen`,
  `det3_side_tilt`, `det3_apex_tilt`.
* **Lemma 16.27′ (doubles; referee)** — the axle argument uses of `v` only its corner
  certificate, so any finite set `D` of vertices over certified corners costs nothing:
  `isRupert_of_uniform_doubles`, `isRupert_of_uniform_doubles_unimodal`.  16.27 is the case
  `D = {w}`.
* **Determinant-test forms** (for the type-21 switch surface, `Type21Switch.lean`):
  `isRupert_of_edgeView_uniform` (any strictly convex rim given by triple tests, middles over
  any side, doubles over corners), `isRupert_quad_uniform` (a 4-corner rim whose diagonals are
  not depth-separated), and **Corollary 14.1 with the uniform tilt**
  (`isRupert_edgePair_uniform`): Lemma E (`edgePair_not_both`) picks the closing, and the
  middles may lie over any side of the shadow, not only over the sides at the axle.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

section Algebra

variable (a b X x u A B v ω τ v' : ℝ³) (h η : ℝ)

/-- The screen bracket `det3 · · u` is an alternating form on a plane (Plücker). -/
theorem det3_plucker_screen :
    det3 a b u * det3 X x u = det3 a X u * det3 b x u - det3 a x u * det3 b X u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The exposure sign of a side under the tilt `g + η v′`. -/
theorem det3_side_tilt :
    h * det3 A u (cross ω u + η • v') = -(h * det3 A (cross ω u) u) + η * (h * det3 A u v') := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The apex test of a mixed sector, multiplied by the corner determinant `C`:
`C · h · det3 u (vel w) d = (ψ₁ c₂ − ψ₂ c₁) + η ((ψ₁ + c₁) k₂ − (ψ₂ + c₂) k₁)`. -/
theorem det3_apex_tilt :
    det3 (A - v) (B - v) u * (h * det3 u (cross ω (v - h • u) + τ) (cross ω u + η • v')) =
      (det3 (A - v) (cross ω v + τ) u * -(h * det3 (v - B) (cross ω u) u) -
          det3 (v - B) (cross ω v + τ) u * -(h * det3 (A - v) (cross ω u) u)) +
        η * ((det3 (A - v) (cross ω v + τ) u + -(h * det3 (A - v) (cross ω u) u)) *
              (h * det3 (v - B) u v') -
            (det3 (v - B) (cross ω v + τ) u + -(h * det3 (v - B) (cross ω u) u)) *
              (h * det3 (A - v) u v')) := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

end Algebra

/-- One chord middle under the tilt `ω × u₀ + η v′`, for all small `η > 0`: hidden,
or exposed with a positive chord test (the body of `exists_tilt_chords`). -/
theorem eventually_chord_choice (u₀ ω τ a b v' : ℝ³) (s δ : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hδ : δ ≠ 0) (hc : det3 (b - a) u₀ v' ≠ 0)
    (ha : 0 < det3 (b - a) (cross ω a + τ) u₀) (hb : 0 < det3 (b - a) (cross ω b + τ) u₀) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < δ * det3 (b - a) u₀ (cross ω u₀ + η • v') ∨
      (δ * det3 (b - a) u₀ (cross ω u₀ + η • v') < 0 ∧
        0 < det3 (b - a) (cross ω (a + s • (b - a) + δ • u₀) + τ) u₀) := by
  set g := cross ω u₀
  set A := δ * det3 (b - a) u₀ g
  set B := δ * det3 (b - a) u₀ v'
  have hB : B ≠ 0 := mul_ne_zero hδ hc
  have hexp : A ≤ 0 → 0 < det3 (b - a) (cross ω (a + s • (b - a) + δ • u₀) + τ) u₀ := by
    intro hA
    rw [det3_vel_middle]
    have hsw : δ * det3 (b - a) g u₀ = -A := by
      simp only [A]; rw [det3_swap23 (b - a) u₀ g]; ring
    nlinarith [mul_pos (show 0 < 1 - s by linarith) ha, mul_pos hs0 hb]
  have hlin : ∀ η : ℝ, δ * det3 (b - a) u₀ (g + η • v') = A + η * B := by
    intro η; simp only [A, B, det3_add_smul]; ring
  rcases lt_trichotomy A 0 with hA | hA | hA
  · have hc' : Continuous fun η : ℝ => A + η * B := by fun_prop
    have hev : ∀ᶠ η in 𝓝 (0 : ℝ), A + η * B < 0 :=
      hc'.continuousAt.eventually (gt_mem_nhds (by simpa using hA))
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with η hη
    rw [hlin]; exact Or.inr ⟨hη, hexp hA.le⟩
  · filter_upwards [self_mem_nhdsWithin] with η hη
    rw [hlin, hA, zero_add]
    rcases lt_or_gt_of_ne hB with hB' | hB'
    · exact Or.inr ⟨mul_neg_of_pos_of_neg hη hB', hexp hA.le⟩
    · exact Or.inl (mul_pos hη hB')
  · have hc' : Continuous fun η : ℝ => A + η * B := by fun_prop
    have hev : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < A + η * B :=
      hc'.continuousAt.eventually (lt_mem_nhds (by simpa using hA))
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with η hη
    rw [hlin]; exact Or.inl hη

/-- `c + η k` is eventually positive (`η → 0⁺`) when `c > 0`, or `c = 0` and `k > 0`. -/
theorem eventually_pos_lin {c k : ℝ} (h : 0 < c ∨ (c = 0 ∧ 0 < k)) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < c + η * k := eventually_pos_affine h

/-- **The axle under the uniform tilt.** With `d = ω × u₀ + η v′` (`v′` generic for the two
face sides), the removed axle vertex `w = v − h u₀` has a certificate at `u₀ + ε d` for
all small `ε`, for all small `η > 0`. -/
theorem eventually_axle_uniform (V : Finset ℝ³) (u₀ ω τ v A B v' : ℝ³) (h : ℝ) (hh : h ≠ 0)
    (hv : v ∈ V) (hA : A ∈ V) (hB : B ∈ V) (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀)
    (he1 : det3 (A - v) u₀ v' ≠ 0) (he2 : det3 (v - B) u₀ v' ≠ 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      TiltCert V (u₀ + ε • (cross ω u₀ + η • v')) ω τ (v - h • u₀) := by
  set g := cross ω u₀ with hg
  set ψ1 := det3 (A - v) (cross ω v + τ) u₀
  set ψ2 := det3 (v - B) (cross ω v + τ) u₀
  set C := det3 (A - v) (B - v) u₀
  set c1 := -(h * det3 (A - v) g u₀) with hc1
  set c2 := -(h * det3 (v - B) g u₀) with hc2
  set k1 := h * det3 (A - v) u₀ v' with hk1
  set k2 := h * det3 (v - B) u₀ v' with hk2
  have hk1ne : k1 ≠ 0 := mul_ne_zero hh he1
  have hk2ne : k2 ≠ 0 := mul_ne_zero hh he2
  -- exposure signs of the two sides, and the axle tests, as functions of η
  have hs1 : ∀ η : ℝ, h * det3 (A - v) u₀ (g + η • v') = c1 + η * k1 := fun η =>
    det3_side_tilt _ _ _ _ _ η
  have hs2 : ∀ η : ℝ, h * det3 (v - B) u₀ (g + η • v') = c2 + η * k2 := fun η =>
    det3_side_tilt _ _ _ _ _ η
  have hw1 : det3 (A - v) (cross ω (v - h • u₀) + τ) u₀ = ψ1 + c1 := by
    rw [det3_vel_shift]; simp only [ψ1, c1, g]; ring
  have hw2 : det3 (v - B) (cross ω (v - h • u₀) + τ) u₀ = ψ2 + c2 := by
    rw [det3_vel_shift]; simp only [ψ2, c2, g]; ring
  have hap : ∀ η : ℝ, C * (h * det3 u₀ (cross ω (v - h • u₀) + τ) (g + η • v')) =
      (ψ1 * c2 - ψ2 * c1) + η * ((ψ1 + c1) * k2 - (ψ2 + c2) * k1) := fun η =>
    det3_apex_tilt _ _ _ _ _ _ _ _ _
  -- the sign of each side's exposure for small η
  have dich : ∀ c k : ℝ, k ≠ 0 →
      ((0 < c ∨ (c = 0 ∧ 0 < k)) ∨ (0 < -c ∨ (-c = 0 ∧ 0 < -k))) := by
    intro c k hk
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exact Or.inr (Or.inl (by linarith))
    · rcases lt_or_gt_of_ne hk with hk' | hk'
      · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
      · exact Or.inl (Or.inr ⟨hc, hk'⟩)
    · exact Or.inl (Or.inl hc)
  have nonneg_of_pos : ∀ c k : ℝ, (0 < c ∨ (c = 0 ∧ 0 < k)) → 0 ≤ c := by
    intro c k hc; rcases hc with hc | ⟨hc, _⟩
    · exact hc.le
    · exact hc.ge
  rcases dich c1 k1 hk1ne with p1 | n1 <;> rcases dich c2 k2 hk2ne with p2 | n2
  · -- both sides switched (sector S− of v): w is the corner between B and A
    have c1n := nonneg_of_pos _ _ p1
    have c2n := nonneg_of_pos _ _ p2
    filter_upwards [self_mem_nhdsWithin] with η _
    exact eventually_tiltCert_axle_corner hA hB hC (by rw [hw1]; linarith) (by rw [hw2]; linarith)
  · -- face 1 switched (a mixed sector): w is the corner between v and A
    have c1n := nonneg_of_pos _ _ p1
    have c2n := nonneg_of_pos _ _ n2
    have hneg : 0 < -(ψ1 * c2 - ψ2 * c1) ∨
        (-(ψ1 * c2 - ψ2 * c1) = 0 ∧ 0 < -((ψ1 + c1) * k2 - (ψ2 + c2) * k1)) := by
      rcases p1 with p1 | ⟨p1, pk1⟩ <;> rcases n2 with n2 | ⟨n2, nk2⟩
      · left; nlinarith [mul_pos hvA n2, mul_pos hvB p1]
      · left; nlinarith [mul_pos hvB p1]
      · left; nlinarith [mul_pos hvA n2]
      · right
        have e1 : c1 = 0 := p1
        have e2 : c2 = 0 := by linarith
        refine ⟨by rw [e1, e2]; ring, ?_⟩
        rw [e1, e2]; nlinarith [mul_pos hvA nk2, mul_pos hvB pk1]
    filter_upwards [eventually_pos_lin p1, eventually_pos_lin hneg] with η h1 h2
    refine eventually_tiltCert_axle_after hv hA (by rw [hs1]; exact h1) (by rw [hw1]; linarith) ?_
    have := hap η
    have hneg' : C * (h * det3 u₀ (cross ω (v - h • u₀) + τ) (g + η • v')) < 0 := by
      rw [this]; linarith
    exact neg_of_mul_neg_right hneg' hC.le
  · -- face 2 switched (a mixed sector): w is the corner between B and v
    have c1n := nonneg_of_pos _ _ n1
    have c2n := nonneg_of_pos _ _ p2
    have hpos : 0 < ψ1 * c2 - ψ2 * c1 ∨
        (ψ1 * c2 - ψ2 * c1 = 0 ∧ 0 < (ψ1 + c1) * k2 - (ψ2 + c2) * k1) := by
      rcases n1 with n1 | ⟨n1, nk1⟩ <;> rcases p2 with p2 | ⟨p2, pk2⟩
      · left; nlinarith [mul_pos hvA p2, mul_pos hvB n1]
      · left; nlinarith [mul_pos hvB n1]
      · left; nlinarith [mul_pos hvA p2]
      · right
        have e1 : c1 = 0 := by linarith
        have e2 : c2 = 0 := p2
        refine ⟨by rw [e1, e2]; ring, ?_⟩
        rw [e1, e2]; nlinarith [mul_pos hvA pk2, mul_pos hvB nk1]
    filter_upwards [eventually_pos_lin p2, eventually_pos_lin hpos] with η h1 h2
    refine eventually_tiltCert_axle_before hv hB (by rw [hs2]; exact h1) (by rw [hw2]; linarith) ?_
    have := hap η
    have hpos' : 0 < C * (h * det3 u₀ (cross ω (v - h • u₀) + τ) (g + η • v')) := by
      rw [this]; linarith
    exact pos_of_mul_pos_right hpos' hC.le
  · -- no side switched (sector S+ of v): w is hidden in the triangle v A B
    filter_upwards [eventually_pos_lin n1, eventually_pos_lin n2] with η h1 h2
    exact eventually_tiltCert_axle_hidden hv hA hB hC (by rw [hs1]; linarith)
      (by rw [hs2]; linarith)

/-- **Lemma 16.27 (the uniform tilt).** An edge crossing along `vw` (`w = v − h u₀`,
`h ≠ 0`, far ends `A`, `B`, `p, a, …, b` counterclockwise) with any finite set `M` of
middles over chords whose ends move strictly inward across the chord (`ChordMiddle`:
the faces at `vw` with chords from `v`, and any further faces seen edge-on). If every
other point except `v`, `w` has a local certificate at `u₀` and `v` moves strictly into
its corner, the point set is Rupert. -/
theorem isRupert_of_edgeChords_uniform (V M : Finset ℝ³) (u₀ ω τ v w A B : ℝ³) (h : ℝ)
    (hu₀ : u₀ ≠ 0) (hv : v ∈ V) (hA : A ∈ V) (hB : B ∈ V) (hw : w = v - h • u₀) (hh : h ≠ 0)
    (hC : 0 < det3 (A - v) (B - v) u₀)
    (hvA : 0 < det3 (A - v) (cross ω v + τ) u₀) (hvB : 0 < det3 (v - B) (cross ω v + τ) u₀)
    (hK : ∀ x ∈ V, x ∉ M → x ≠ v → x ≠ w → TiltCert V u₀ ω τ x)
    (hM : ∀ m ∈ M, ChordMiddle V u₀ ω τ m) : IsRupert V := by
  classical
  choose! a ha b hb r hr s δ hs0 hs1 hδ hm hrin hva hvb using hM
  -- a generic v′: no chord and neither face side is parallel to it in the screen
  set I : Finset (ℝ³ ⊕ Fin 2) := M.disjSum Finset.univ
  set n : ℝ³ ⊕ Fin 2 → ℝ³ := Sum.elim (fun m => cross (b m - a m) u₀)
    (fun i => if i = 0 then cross (A - v) u₀ else cross (v - B) u₀)
  have hcr : ∀ x y : ℝ³, 0 < det3 x y u₀ → cross x u₀ ≠ 0 := by
    intro x y hxy h0
    rw [show det3 x y u₀ = -⟪cross x u₀, y⟫ by rw [det3_swap23]; rfl, h0, inner_zero_left,
      neg_zero] at hxy
    exact lt_irrefl _ hxy
  have hn : ∀ i ∈ I, n i ≠ 0 := by
    intro i hi
    rcases i with m | i
    · exact hcr _ _ (hrin m (by simpa [I] using hi))
    · simp only [n, Sum.elim_inr]
      split_ifs
      · exact hcr _ _ hC
      · refine hcr (v - B) (A - B) ?_
        rw [show det3 (v - B) (A - B) u₀ = det3 (A - v) (B - v) u₀ by
          simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring]
        exact hC
  obtain ⟨v', hv'⟩ := exists_inner_ne_zero I n hn
  have hcm : ∀ m ∈ M, det3 (b m - a m) u₀ v' ≠ 0 := fun m hmM =>
    hv' (Sum.inl m) (by simp [I, hmM])
  have he1 : det3 (A - v) u₀ v' ≠ 0 := by
    have := hv' (Sum.inr 0) (by simp [I]); simpa [n, det3] using this
  have he2 : det3 (v - B) u₀ v' ≠ 0 := by
    have := hv' (Sum.inr 1) (by simp [I]); simpa [n, det3] using this
  -- one η for every middle and the axle
  have hchord : ∀ m ∈ M, ∀ᶠ η in 𝓝[>] (0 : ℝ),
      0 < δ m * det3 (b m - a m) u₀ (cross ω u₀ + η • v') ∨
        (δ m * det3 (b m - a m) u₀ (cross ω u₀ + η • v') < 0 ∧
          0 < det3 (b m - a m) (cross ω (a m + s m • (b m - a m) + δ m • u₀) + τ) u₀) :=
    fun m hmM => eventually_chord_choice u₀ ω τ (a m) (b m) v' (s m) (δ m) (hs0 m hmM)
      (hs1 m hmM) (hδ m hmM) (hcm m hmM) (hva m hmM) (hvb m hmM)
  obtain ⟨η, hη⟩ := (((eventually_all_finset M).mpr hchord).and
    (eventually_axle_uniform V u₀ ω τ v A B v' h hh hv hA hB hC hvA hvB he1 he2)).exists
  set d := cross ω u₀ + η • v'
  have hcert : ∀ x ∈ V, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ x := by
    intro x hx
    by_cases hxM : x ∈ M
    · rw [hm x hxM]
      exact eventually_tiltCert_middle (ha x hxM) (hb x hxM) (hr x hxM) (hs0 x hxM)
        (hs1 x hxM) (hrin x hxM) (hη.1 x hxM)
    by_cases hxv : x = v
    · subst hxv
      have hc : TiltCert V u₀ ω τ x := Or.inl ⟨B, hB, A, hA, hC, hvA, hvB⟩
      exact hc.eventually_tilt d
    by_cases hxw : x = w
    · subst hxw; rw [hw]; exact hη.2
    exact (hK x hx hxM hxv hxw).eventually_tilt d
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • d ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • d := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hall⟩ := (hne.and ((eventually_all_finset V).mpr hcert)).exists
  exact isRupert_of_tiltCert V (u₀ + ε • d) hε ω τ hall

/-- **Lemma 16.27 with a unimodal `K_v` (Theorem 7.3).** The view `u₀` (`R u₀ = r e_z`,
`r > 0`) runs along the edge `vw`, `v = x i₀`, `w = v − h u₀`. The silhouette of `K_v`
(the hull without the middles and `w`) is the strictly convex counterclockwise polygon
`x` (every other point of `K_v` strictly inside), with cyclically unimodal depths and no
horizontal double normal. Each middle lies over a side `[x i, x (i + 1)]` of that polygon,
at a depth offset `δ ≠ 0`: the sides at `v` carry the middles of the two faces at `vw`
(chords from `v`), the other sides those of further faces seen edge-on. Then `V` is
Rupert. -/
theorem isRupert_of_edgeChords_uniform_unimodal (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  have hu₀ := ne_zero_of_rot_eq hr hRu
  have hxw : ∀ i, x i ≠ w := corner_ne_axle hr hRu hp hw hh
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_unimodal ((V \ M).erase w) R hR hr hRu x
    (fun i => mem_erase.mpr ⟨hxw i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
    (fun v hv hvx => by
      obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
      exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hz hnd
  have hB := hedge (i₀ - 1)
  rw [sub_add_cancel] at hB
  refine isRupert_of_edgeChords_uniform V M u₀ ω τ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h hu₀
    (hxV _) (hxV _) (hxV _) hw hh (det3_corner_pos hR hr hRu hp i₀) (hedge i₀).1 hB.2
    (fun y hy hyM _ hyw => (hcert y (mem_erase.mpr ⟨hyw, mem_sdiff.mpr ⟨hy, hyM⟩⟩)).mono
      ((erase_subset _ _).trans sdiff_subset)) fun m hm => ?_
  obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
  exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, s, δ, hs0, hs1, hδ, rfl,
    det3_corner_pos hR hr hRu hp i, (hedge i).1, (hedge i).2⟩


/-! ### Referee addition (Lemma 16.27′): doubles over any certified corner

The axle argument of `eventually_axle_uniform` uses of `v` only its corner certificate
at `u₀`. So every vertex `y = x − h u₀` lying over a vertex `x` that moves strictly into
its corner (between `B` and `A`) gets a certificate at the uniform tilt, for any finite
set `D` of such *doubles* at once. The axle `w` of 16.27 is the double over `v`. -/

/-- **Lemma 16.27′ (doubles).** Middles over chords (`M`) and doubles over corners (`D`)
cost nothing at the uniform tilt `u₀ + ε (ω × u₀ + η v′)`. -/
theorem isRupert_of_uniform_doubles (V M D : Finset ℝ³) (u₀ ω τ : ℝ³) (hu₀ : u₀ ≠ 0)
    (hD : ∀ y ∈ D, ∃ x ∈ V, ∃ A ∈ V, ∃ B ∈ V, ∃ h : ℝ, h ≠ 0 ∧ y = x - h • u₀ ∧
      0 < det3 (A - x) (B - x) u₀ ∧ 0 < det3 (A - x) (cross ω x + τ) u₀ ∧
      0 < det3 (x - B) (cross ω x + τ) u₀)
    (hK : ∀ x ∈ V, x ∉ M → x ∉ D → TiltCert V u₀ ω τ x)
    (hM : ∀ m ∈ M, ChordMiddle V u₀ ω τ m) : IsRupert V := by
  classical
  choose! a ha b hb r hr s δ hs0 hs1 hδ hm hrin hva hvb using hM
  choose! x hx A hA B hB h hh hy hC hvA hvB using hD
  set I : Finset (ℝ³ ⊕ (ℝ³ ⊕ ℝ³)) := M.disjSum (D.disjSum D)
  set n : ℝ³ ⊕ (ℝ³ ⊕ ℝ³) → ℝ³ := Sum.elim (fun m => cross (b m - a m) u₀)
    (Sum.elim (fun y => cross (A y - x y) u₀) (fun y => cross (x y - B y) u₀))
  have hcr : ∀ p q : ℝ³, 0 < det3 p q u₀ → cross p u₀ ≠ 0 := by
    intro p q hpq h0
    rw [show det3 p q u₀ = -⟪cross p u₀, q⟫ by rw [det3_swap23]; rfl, h0, inner_zero_left,
      neg_zero] at hpq
    exact lt_irrefl _ hpq
  have hn : ∀ i ∈ I, n i ≠ 0 := by
    intro i hi
    rcases i with m | y | y
    · exact hcr _ _ (hrin m (by simpa [I] using hi))
    · have hyD : y ∈ D := by simpa [I] using hi
      exact hcr _ _ (hC y hyD)
    · have hyD : y ∈ D := by simpa [I] using hi
      refine hcr (x y - B y) (A y - B y) ?_
      rw [show det3 (x y - B y) (A y - B y) u₀ = det3 (A y - x y) (B y - x y) u₀ by
        simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring]
      exact hC y hyD
  obtain ⟨v', hv'⟩ := exists_inner_ne_zero I n hn
  have hcm : ∀ m ∈ M, det3 (b m - a m) u₀ v' ≠ 0 := fun m hmM =>
    hv' (Sum.inl m) (by simp [I, hmM])
  have he1 : ∀ y ∈ D, det3 (A y - x y) u₀ v' ≠ 0 := by
    intro y hyD
    have := hv' (Sum.inr (Sum.inl y)) (by simp [I, hyD]); simpa [n, det3] using this
  have he2 : ∀ y ∈ D, det3 (x y - B y) u₀ v' ≠ 0 := by
    intro y hyD
    have := hv' (Sum.inr (Sum.inr y)) (by simp [I, hyD]); simpa [n, det3] using this
  have hchord : ∀ m ∈ M, ∀ᶠ η in 𝓝[>] (0 : ℝ),
      0 < δ m * det3 (b m - a m) u₀ (cross ω u₀ + η • v') ∨
        (δ m * det3 (b m - a m) u₀ (cross ω u₀ + η • v') < 0 ∧
          0 < det3 (b m - a m) (cross ω (a m + s m • (b m - a m) + δ m • u₀) + τ) u₀) :=
    fun m hmM => eventually_chord_choice u₀ ω τ (a m) (b m) v' (s m) (δ m) (hs0 m hmM)
      (hs1 m hmM) (hδ m hmM) (hcm m hmM) (hva m hmM) (hvb m hmM)
  have hdouble : ∀ y ∈ D, ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      TiltCert V (u₀ + ε • (cross ω u₀ + η • v')) ω τ y := by
    intro y hyD
    have := eventually_axle_uniform V u₀ ω τ (x y) (A y) (B y) v' (h y) (hh y hyD) (hx y hyD)
      (hA y hyD) (hB y hyD) (hC y hyD) (hvA y hyD) (hvB y hyD) (he1 y hyD) (he2 y hyD)
    rwa [← hy y hyD] at this
  obtain ⟨η, hη⟩ := (((eventually_all_finset M).mpr hchord).and
    ((eventually_all_finset D).mpr hdouble)).exists
  set d := cross ω u₀ + η • v'
  have hcert : ∀ z ∈ V, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ z := by
    intro z hz
    by_cases hzM : z ∈ M
    · rw [hm z hzM]
      exact eventually_tiltCert_middle (ha z hzM) (hb z hzM) (hr z hzM) (hs0 z hzM)
        (hs1 z hzM) (hrin z hzM) (hη.1 z hzM)
    by_cases hzD : z ∈ D
    · exact hη.2 z hzD
    exact (hK z hz hzM hzD).eventually_tilt d
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • d ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • d := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hall⟩ := (hne.and ((eventually_all_finset V).mpr hcert)).exists
  exact isRupert_of_tiltCert V (u₀ + ε • d) hε ω τ hall

/-- **Lemma 16.27′ with a unimodal reduced polytope (Theorem 7.3).** The silhouette of
`V ∖ (M ∪ D)` at `u₀` is the strictly convex counterclockwise polygon `x` with cyclically
unimodal depths and no horizontal double normal; each middle lies over a side of `x`, and
each double lies over a corner of `x` (the axle of an edge crossing is one of them). -/
theorem isRupert_of_uniform_doubles_unimodal (V M D : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : IsRupert V := by
  classical
  have hu₀ := ne_zero_of_rot_eq hr hRu
  have hxD : ∀ i, x i ∉ D := by
    intro i hiD
    obtain ⟨j, h, hh, hy⟩ := hD (x i) hiD
    exact corner_ne_axle hr hRu hp hy hh i rfl
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_unimodal ((V \ M) \ D) R hR hr hRu x
    (fun i => mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxV i, hxM i⟩, hxD i⟩) hp
    (fun v hv hvx => by
      obtain ⟨hv1, hvD⟩ := mem_sdiff.mp hv
      exact hin v (mem_sdiff.mp hv1).1 (mem_sdiff.mp hv1).2 hvD hvx) hz hnd
  refine isRupert_of_uniform_doubles V M D u₀ ω τ hu₀ ?_
    (fun y hy hyM hyD => (hcert y (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hy, hyM⟩, hyD⟩)).mono
      (sdiff_subset.trans sdiff_subset)) ?_
  · intro y hyD
    obtain ⟨i, h, hh, rfl⟩ := hD y hyD
    have hB := hedge (i - 1)
    rw [sub_add_cancel] at hB
    exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, h, hh, rfl,
      det3_corner_pos hR hr hRu hp i, (hedge i).1, hB.2⟩
  · intro m hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
    exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, s, δ, hs0, hs1, hδ, rfl,
      det3_corner_pos hR hr hRu hp i, (hedge i).1, (hedge i).2⟩

/-! ### Determinant-test forms -/

/-- **Lemma 16.27′ at an edge view given by determinant tests.**  The cycle `x` passes all
triple tests at `u₀` (strictly convex, counterclockwise), every other point except the middles
`M` and the doubles `D` is strictly inside, the depths `⟪x i, u₀⟫` are cyclically unimodal and
there is no horizontal double normal (`NoHDNAt W u₀` for a set `W` containing the rim).  Each
middle lies over a side of `x` at a depth offset `δ ≠ 0`, each double over a corner.  Then `V`
is Rupert. -/
theorem isRupert_of_edgeView_uniform (V M D W : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ∉ D → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt W u₀) (hxW : ∀ i, x i ∈ W)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : IsRupert V := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u₀ hu₀
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_uniform_doubles_unimodal V M D R hR hr hRu x hxV hxM hp ?_ ?_ ?_ hM hD
  · intro y hy hyM hyD hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyD hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x hxW hp

/-- **A 4-corner closing with the uniform tilt** (Lemma 16.27′ with Theorem 7.3).  At the view
`u` the rim `(y, a, c, b)` is a strictly convex counterclockwise quadrilateral (`q₁`–`q₄`), the
other axle end is `o = y − h u`, every other point not in `M` is strictly inside, the depths are
distinct and the diagonals `[y, c]`, `[a, b]` are not depth-separated.  The middles `M` lie
over any sides of the rim.  Then `V` is Rupert. -/
theorem isRupert_quad_uniform (V M : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ} (hh : h ≠ 0)
    (ho : o = y - h • u) (hu : u ≠ 0) (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hz : [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup) (hsep : ¬ DepthSep y c a b u)
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u)
    (hnd : NoHDNAt (V.erase o) u) : IsRupert V := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  have hov := overlap4_of_not_depthSep hsep z1 z2 z3 z4 z5 z6
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not the other axle end
  have hoy : y ≠ o := by
    intro e
    have h2 : y - h • u = y := by rw [ho] at e; exact e.symm
    have : h • u = 0 := by
      calc h • u = y - (y - h • u) := by abel
        _ = 0 := by rw [h2, sub_self]
    exact (smul_ne_zero hh hu) this
  have hoa : a ≠ o := by
    intro e
    have : det3 (a - y) (c - y) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hoc : c ≠ o := by
    intro e
    have : det3 (b - c) (y - c) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hob : b ≠ o := by
    intro e
    have : det3 (y - b) (a - b) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_uniform V M {o} (V.erase o) u hu (k := 4) (by norm_num)
    (quad y a c b) ?_ ?_ ?_ ?_ ?_ hnd ?_ hM ?_
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
    have hzo : z ≠ o := fun e => hzD (by rw [e]; exact mem_singleton_self o)
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzo (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]
    refine isCyclicUnimodal_of_NWS4 (quad_injective z1 z2 z3 z4 z5 z6) ?_
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
    exact ⟨hov.1, hov.2.1⟩
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_erase]
    exacts [⟨hoy, hyV⟩, ⟨hoa, haV⟩, ⟨hoc, hcV⟩, ⟨hob, hbV⟩]
  · intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨0, h, hh, by rw [quad_0]; exact ho⟩

/-- **Corollary 14.1 with the uniform tilt (Lemma E with Lemma 16.27).**  An edge crossing
along `v w` at the view `u = w − v`: the shadow is the strictly convex counterclockwise
quadrilateral `(q, P a, P c, P b)` (`q = P v = P w`; the triple tests `q₁`–`q₄`), and every
point of `V` is `v`, `w`, `a`, `b`, `c`, strictly inside the shadow (`EdgeHidden`), or one of
the middles `M`, which lie over sides of the shadow: over any side, at a nonzero depth offset
from the rim `(v, a, c, b)` (`hM₁`) and from the rim `(w, a, c, b)` (`hM₂`) — the sides at `q`
are faces at `v w`, the far sides faces seen edge-on.  If `v` and `w` lie weakly on opposite
sides of the plane `abc` (Lemma E (iii)), both rims have distinct depths and neither closing
has a horizontal double normal at `u`, then `V` is Rupert. -/
theorem isRupert_edgePair_uniform {v w a b c : ℝ³} (V M : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hvM : v ∉ M) (hwM : w ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (hz₁ : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hz₂ : [⟪w, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hV : ∀ z ∈ V, z ∉ M → z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨
      EdgeHidden (w - v) v a c b z)
    (hM₁ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad v a c b i + s • (quad v a c b (i + 1) - quad v a c b i) + δ • (w - v))
    (hM₂ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad w a c b i + s • (quad w a c b (i + 1) - quad w a c b i) + δ • (w - v))
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  have hsm : SegMeet v c a b (w - v) := by
    refine segMeet_of_sides ?_ ?_
    · have e1 : det3 (c - v) (a - v) (w - v) = -det3 (a - v) (c - v) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e2 : det3 (c - v) (b - v) (w - v) = det3 (b - c) (v - c) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e2]; nlinarith
    · have e1 : det3 (b - a) (v - a) (w - v) = det3 (v - b) (a - b) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e2 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e2]; nlinarith
  have hL : det3 (b - a) (c - a) (w - v) ≠ 0 := by
    have e2 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e2]; linarith
  have nb := edgePair_not_both hsm hL hE
  by_cases h1 : DepthSep v c a b (w - v)
  · -- `K_w` is unimodal
    have h2 : ¬ DepthSep w c a b (w - v) := fun h2 => nb ⟨h1, h2⟩
    refine isRupert_quad_uniform V M (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hwV haV hbV hcV hwM haM hbM hcM
      (by rw [det3_vw_both]; exact q₁) q₂ (by rw [det3_vw_right]; exact q₃)
      (by rw [det3_vw_left]; exact q₄) ?_ hz₂ h2 hM₂ hnd₂
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid.shift
  · -- `K_v` is unimodal
    refine isRupert_quad_uniform V M (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hvV haV hbV hcV hvM haM hbM hcM q₁ q₂
      q₃ q₄ ?_ hz₁ h1 hM₁ hnd₁
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h2
    · exact absurd e h1
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid

end Minimality

end
