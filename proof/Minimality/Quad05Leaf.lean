module

public import Minimality.FaceCircleClosed
public import Minimality.SlideE
public import Minimality.EdgeSlide
public import Minimality.Octahedron
public import Minimality.OctaTools
public import Minimality.BadViews
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# Type 24: the quad-chord leaf on the face circle of `4350` (Lemma AS of `T2SC24.md`)

The view `u = (x 5 - x 0) + η (x 4 - x 0)` (`η ≥ 0`) lies in the plane of the quad facet `0345`
(facet `3` of `s0x_S24`), next to the end-on view `x 5 - x 0` of the edge `05`.  At `u` the rim of
`K'' = {1, 2, 4, 5, 6}` is the strictly convex 4-cycle `6 4 5 2` with `1` strictly inside, and the
other two vertices of the quad are chord middles over the rim edge `4 5`: `0` automatically (for every
`η ≥ 0` and along the slide), `3` with `0 < s₃ < 1`, `δ₃ ≠ 0`.  With rim depths `z6 < z4 < z5`
(`z2` distinct from the other three) the rim is strictly unimodal.

The certificate is the slide `isRupert_of_slideP` along the circle of `0345` (`u + τ (x 4 - x 0)`,
`τ → 0⁺`, i.e. increasing `η`): the facet stays edge-on, `0` and `3` stay chord middles, and the only
horizontal double normal that can survive is a persistent one along the facet normal, which Lemma H
(`noPersistHDN_of_far_offChord`) excludes when the rim vertex farthest from the facet plane (`2` on
the census) has its foot off the chord `[4, 5]`.  The face-circle closed-cell route
(`H21.isRupert_faceCircleClosed`) does not fit: its cell rim is `6 4 0 5 2` or `6 4 3 5 2` and needs
`z4 < z0` or `z3 < z5`, both false on every census sample.

* `injective24`: an `S0xFac 9 s0x_S24 x` has injective vertices.
* `isRupert_quadChord`: the leaf with generic labels (view `x B - x o + η (x A - x o)`, rim
  `P A B Q`, inside point `I`, middles `o`, `t` over `A B`, farthest rim vertex `w`).
* `isRupert_q05`: the census instance (`o t A B P Q I = 0 3 4 5 6 2 1`, `w = 2`).
* `isRupert_q05_mirror`: the instance in the mirror frame `(2 6)(4 5)`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.T24.Quad05
open Minimality Minimality.H21 Minimality.T24.SAT

theorem q5ip (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

theorem sep24 : ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- The vertices of a type-24 facet structure are distinct (each pair is separated by a facet). -/
theorem injective24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Function.Injective x := by
  intro i j h
  by_contra hij
  obtain ⟨t, hi, hj⟩ := sep24 i j hij
  have h1 := F.zero t i hi
  have h2 := F.neg t j hj
  rw [h] at h1
  linarith

/-- **The quad-chord leaf, generic labels.**  Facet `3` (`0345`) of type 24 contains `o, t, A, B`
and not `P, Q, I`.  At the view `u = (x B - x o) + η (x A - x o)` (`η ≥ 0`, in the facet's plane):
the rim `P A B Q` is strictly convex with orientation `ρ` and `I` strictly inside (`hcyc`, `hI`);
`t` is a chord middle over `B A` (`h3`, `0 < s₃ < 1`, `δ₃ ≠ 0`); the depths are `zP < zA < zB` with
`zQ` distinct from them; the rim vertex `w ∈ {P, Q}` is strictly farther from the facet plane than
the other one `w'` (`hfar`, affine), and its foot is off the chord `[A, B]` (`hoff`: off the line, or
beyond `A`, or beyond `B`).  Then the hull is Rupert.  (`o` is a chord middle automatically.) -/
theorem isRupert_quadChord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {o t A B P Q I : Fin 7}
    (hcov : ∀ j : Fin 7, j = o ∨ j = t ∨ j = A ∨ j = B ∨ j = P ∨ j = Q ∨ j = I)
    (hlab : [o, t, A, B, P, Q].Nodup)
    (hoS : o ∈ s0x_S24 3) (hAS : A ∈ s0x_S24 3) (hBS : B ∈ s0x_S24 3)
    (hPS : P ∉ s0x_S24 3) (hQS : Q ∉ s0x_S24 3) (hIS : I ∉ s0x_S24 3)
    {η : ℝ} (hη : 0 ≤ η) {u : ℝ³} (hu : u = (x B - x o) + η • (x A - x o)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
        (quad (x P) (x A) (x B) (x Q) j - quad (x P) (x A) (x B) (x Q) i) u)
    (hI : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
        (x I - quad (x P) (x A) (x B) (x Q) i) u)
    {s₃ δ₃ : ℝ} (h3 : x t = x B + s₃ • (x A - x B) + δ₃ • u) (hs₀ : 0 < s₃) (hs₁ : s₃ < 1)
    (hδ : δ₃ ≠ 0)
    (hPA : ⟪x P, u⟫ < ⟪x A, u⟫) (hAB : ⟪x A, u⟫ < ⟪x B, u⟫)
    (hQP : ⟪x Q, u⟫ ≠ ⟪x P, u⟫) (hQA : ⟪x Q, u⟫ ≠ ⟪x A, u⟫) (hQB : ⟪x Q, u⟫ ≠ ⟪x B, u⟫)
    {w w' : Fin 7} (hw : (w = Q ∧ w' = P) ∨ (w = P ∧ w' = Q))
    (hfar : 0 < det3 (x B - x o) (x A - x o) (x w - x w') *
      det3 (x B - x o) (x A - x o) (x I - x o))
    (hoff : det3 (x B - x o) (x A - x o) (cross (x B - x A) (x w - x A)) ≠ 0 ∨
      ⟪x w - x A, x B - x A⟫ < 0 ∨ ⟪x w - x B, x A - x B⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  have hx := injective24 F
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hlab
  obtain ⟨⟨-, hoA, hoB, hoP, hoQ⟩, ⟨htA, htB, htP, htQ⟩, ⟨hAB', hAP, hAQ⟩, ⟨hBP, hBQ⟩, hPQ⟩ :=
    hlab
  set c : ZMod 4 → ℝ³ := quad (x P) (x A) (x B) (x Q) with hc
  set e : ℝ³ := x A - x o with he
  -- facet `3`
  have fo := F.zero 3 o hoS
  have fA := F.zero 3 A hAS
  have fB := F.zero 3 B hBS
  have fP := F.neg 3 P hPS
  have fQ := F.neg 3 Q hQS
  have fI := F.neg 3 I hIS
  have Nsub : ∀ a b : Fin 7, ⟪F.N 3, x a - x b⟫ = F.f 3 (x a) - F.f 3 (x b) := F.inner_sub 3
  have hNu : ⟪F.N 3, u⟫ = 0 := by
    rw [hu, inner_add_right, real_inner_smul_right, Nsub, Nsub, fB, fo, fA]; ring
  have hNe : ⟪F.N 3, e⟫ = 0 := by rw [he, Nsub, fA, fo]; ring
  have hN0 : F.N 3 ≠ 0 := by
    intro h0
    have := Nsub I o
    rw [h0, inner_zero_left, fo] at this
    linarith
  -- the edge `A B` of the rim and the facet's plane
  have key : ∀ Y : ℝ³, det3 (x B - x A) Y u = -(1 + η) * ⟪cross u e, Y⟫ := by
    intro Y
    rw [hu, he]
    simp only [det3_expand, q5ip, cross_apply_zero, cross_apply_one, cross_apply_two,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hc2 : ∀ Z : ℝ³, det3 (x B - x o) (x A - x o) Z = ⟪cross u e, Z⟫ := by
    intro Z
    rw [hu, he]
    simp only [det3_expand, q5ip, cross_apply_zero, cross_apply_one, cross_apply_two,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hcross : cross u e ≠ 0 := by
    intro h0
    have := hcyc 1 3 (by decide) (by decide)
    rw [show (1 : ZMod 4) + 1 = 2 by decide] at this
    change 0 < ρ * det3 (x B - x A) (x Q - x A) u at this
    rw [key, h0, inner_zero_left, mul_zero, mul_zero] at this
    exact lt_irrefl _ this
  have hu0 : u ≠ 0 := by
    intro h0
    apply hcross
    rw [h0]
    ext j; fin_cases j <;> simp [cross]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, cross u e = r • F.N 3 :=
    ⟨_, eq_smul_of_cross_eq_zero hN0 (cross_eq_zero_of_perp2 hNu hNe (inner_cross_left u e)
      (inner_cross_right u e) hcross)⟩
  -- the farthest rim vertex from the facet plane
  have hfarN : F.f 3 (x w) < F.f 3 (x w') := by
    rw [hc2, hc2, hr, real_inner_smul_left, real_inner_smul_left, Nsub, Nsub, fo] at hfar
    by_contra hcon
    push Not at hcon
    have h1 : 0 ≤ r ^ 2 * (F.f 3 (x w) - F.f 3 (x w')) :=
      mul_nonneg (sq_nonneg r) (by linarith)
    have h2 : r * (F.f 3 (x w) - F.f 3 (x w')) * (r * (F.f 3 (x I) - 0)) =
        r ^ 2 * (F.f 3 (x w) - F.f 3 (x w')) * F.f 3 (x I) := by ring
    rw [h2] at hfar
    linarith [mul_nonpos_of_nonneg_of_nonpos h1 fI.le]
  have hwneg : F.f 3 (x w) < 0 := by
    rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact fQ
    · exact fP
  -- the rim cycle
  have hcinj : Function.Injective c :=
    quad_injective (hx.ne (Ne.symm hAP)) (hx.ne (Ne.symm hBP)) (hx.ne hPQ)
      (hx.ne hAB') (hx.ne hAQ) (hx.ne hBQ)
  have hxV : ∀ i, c i ∈ univ.image x := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact mem_image_of_mem x (mem_univ P)
    · exact mem_image_of_mem x (mem_univ A)
    · exact mem_image_of_mem x (mem_univ B)
    · exact mem_image_of_mem x (mem_univ Q)
  have hxM : ∀ i, c i ∉ ({x o, x t} : Finset ℝ³) := by
    intro i
    simp only [mem_insert, mem_singleton, not_or]
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact ⟨hx.ne (Ne.symm hoP), hx.ne (Ne.symm htP)⟩
    · exact ⟨hx.ne (Ne.symm hoA), hx.ne (Ne.symm htA)⟩
    · exact ⟨hx.ne (Ne.symm hoB), hx.ne (Ne.symm htB)⟩
    · exact ⟨hx.ne (Ne.symm hoQ), hx.ne (Ne.symm htQ)⟩
  have hrest : ∀ y ∈ univ.image x, y ∉ ({x o, x t} : Finset ℝ³) → (∀ j, y ≠ c j) →
      ∀ i, SlideTest ρ (c (i + 1) - c i) (y - c i) u e := by
    intro y hy hyM hyc i
    obtain ⟨j, -, rfl⟩ := mem_image.mp hy
    rcases hcov j with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp) hyM
    · exact absurd (by simp) hyM
    · exact absurd rfl (hyc 1)
    · exact absurd rfl (hyc 2)
    · exact absurd rfl (hyc 0)
    · exact absurd rfl (hyc 3)
    · exact Or.inl (hI i)
  -- the middles along the slide `u + τ e`
  have hM : ∀ m ∈ ({x o, x t} : Finset ℝ³), ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ i : ZMod 4, ∃ s δ : ℝ,
      0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c i + s • (c (i + 1) - c i) + δ • (u + τ • e) := by
    intro m hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
      have hD : 0 < 1 + η + τ := by linarith
      refine ⟨1, 1 / (1 + η + τ), -1 / (1 + η + τ), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one hD]; linarith
      · exact div_ne_zero (by norm_num) hD.ne'
      · change x o = x A + (1 / (1 + η + τ)) • (x B - x A) + (-1 / (1 + η + τ)) • (u + τ • e)
        rw [hu, he]
        ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp
        ring
    · have hcont : ContinuousAt (fun τ : ℝ => 1 - s₃ + δ₃ * τ / (1 + η + τ)) 0 := by
        refine continuousAt_const.add (ContinuousAt.div (continuousAt_const.mul continuousAt_id)
          (continuousAt_const.add continuousAt_id) ?_)
        simp only [add_zero]; linarith
      have hlim : Tendsto (fun τ : ℝ => 1 - s₃ + δ₃ * τ / (1 + η + τ)) (𝓝[>] 0)
          (𝓝 (1 - s₃)) := by
        have := hcont.tendsto
        simp only [mul_zero, zero_div, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,
        hlim.eventually (Ioo_mem_nhds (by linarith : (0 : ℝ) < 1 - s₃)
          (by linarith : 1 - s₃ < 1))] with τ (hτ : 0 < τ) hg
      have hD : 0 < 1 + η + τ := by linarith
      refine ⟨1, 1 - s₃ + δ₃ * τ / (1 + η + τ), δ₃ * (1 + η) / (1 + η + τ), hg.1, hg.2, ?_, ?_⟩
      · exact div_ne_zero (mul_ne_zero hδ (by linarith)) hD.ne'
      · change x t = x A + (1 - s₃ + δ₃ * τ / (1 + η + τ)) • (x B - x A) +
          (δ₃ * (1 + η) / (1 + η + τ)) • (u + τ • e)
        rw [h3, hu, he]
        ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp
        ring
  -- the depths
  have hz4 : (fun i => ⟪c i, u⟫) = quad ⟪x P, u⟫ ⟪x A, u⟫ ⟪x B, u⟫ ⟪x Q, u⟫ := by
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hinj0 : Function.Injective (fun i => ⟪c i, u⟫) := by
    rw [hz4]
    exact quad_injective (ne_of_lt hPA) (ne_of_lt (hPA.trans hAB)) (Ne.symm hQP) (ne_of_lt hAB)
      (Ne.symm hQA) (Ne.symm hQB)
  have hz : UniOrSep c u :=
    Or.inl (strictUnimodal_of_cyclic (by norm_num)
      (isCyclicUnimodal_four (z := fun i => ⟪c i, u⟫) hinj0
        ⟨Or.inl hPA, Or.inr (Or.inr (Or.inl hAB)), ne_of_lt (hPA.trans hAB), Ne.symm hQA⟩))
  -- no persistent double normal (Lemma H with the facet normal)
  have hbad : NoPersistHDN c u e := by
    refine noPersistHDN_of_far_offChord (V := univ.image x) (by norm_num) c hcinj hxV
      (n := F.N 3) (κ := ⟪F.N 3, x A⟫) (A := x A) (B := x B) (w := x w) ?_ rfl ?_ ⟨1, rfl⟩ ?_
      ?_ ?_ hNu hNe hcross ?_
    · intro z hz
      obtain ⟨j, -, rfl⟩ := mem_image.mp hz
      have h1 := Nsub j A
      rw [inner_sub_right, fA] at h1
      linarith [F.le 3 j]
    · have h1 := Nsub B A
      rw [inner_sub_right, fB, fA] at h1
      linarith
    · intro m hm
      have hlt : ∀ j : Fin 7, F.f 3 (x j) < 0 → ⟪F.N 3, x j⟫ ≠ ⟪F.N 3, x A⟫ := by
        intro j hj heq
        have h1 := Nsub j A
        rw [inner_sub_right, fA, heq] at h1
        linarith
      rcases zmod4_cases m with rfl | rfl | rfl | rfl
      · exact absurd hm (hlt P fP)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hm (hlt Q fQ)
    · rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨3, rfl⟩
      · exact ⟨0, rfl⟩
    · have hlt : ∀ j : Fin 7, F.f 3 (x w) < F.f 3 (x j) → ⟪F.N 3, x w⟫ < ⟪F.N 3, x j⟫ := by
        intro j hj
        have h1 := Nsub w j
        rw [inner_sub_right] at h1
        linarith
      intro m hm
      rcases zmod4_cases m with rfl | rfl | rfl | rfl
      · change x P ≠ x w at hm
        rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
        · exact hlt _ hfarN
        · exact absurd rfl hm
      · exact hlt A (by rw [fA]; exact hwneg)
      · exact hlt B (by rw [fB]; exact hwneg)
      · change x Q ≠ x w at hm
        rcases hw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hm
        · exact hlt _ hfarN
    · rcases hoff with h | h | h
      · left
        intro h0
        apply h
        rw [hc2, hr, real_inner_smul_left, h0, mul_zero]
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  exact isRupert_of_slideP (univ.image x) {x o, x t} u e hu0 c hxV hxM (by norm_num) ρ hρ
    (fun i j h1 h2 => Or.inl (hcyc i j h1 h2)) hrest hM hinj0 hz hbad

/-- **Leaf Q05** (type 24, `T2SC24.md` "Lemma AS"): at `u = (x 5 - x 0) + η (x 4 - x 0)`
(`η ≥ 0`) on the circle of the quad facet `0345`, the rim `6 4 5 2` strictly convex (orientation
`ρ`) with `1` strictly inside, `3` a chord middle over `5 4` (`0 < s₃ < 1`, `δ₃ ≠ 0`; `0` is one
automatically), depths `z6 < z4 < z5` with `z2` distinct from them, `2` strictly farther from the
plane of `0345` than `6` (`hfar`), and the foot of `2` on that plane off the chord `[4, 5]`
(`hoff`).  Then `K` is Rupert. -/
theorem isRupert_q05 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {η : ℝ} (hη : 0 ≤ η) {u : ℝ³}
    (hu : u = (x 5 - x 0) + η • (x 4 - x 0)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
        (quad (x 6) (x 4) (x 5) (x 2) j - quad (x 6) (x 4) (x 5) (x 2) i) u)
    (h1 : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
        (x 1 - quad (x 6) (x 4) (x 5) (x 2) i) u)
    {s₃ δ₃ : ℝ} (h3 : x 3 = x 5 + s₃ • (x 4 - x 5) + δ₃ • u) (hs₀ : 0 < s₃) (hs₁ : s₃ < 1)
    (hδ₃ : δ₃ ≠ 0)
    (h64 : ⟪x 6, u⟫ < ⟪x 4, u⟫) (h45 : ⟪x 4, u⟫ < ⟪x 5, u⟫)
    (h26 : ⟪x 2, u⟫ ≠ ⟪x 6, u⟫) (h24 : ⟪x 2, u⟫ ≠ ⟪x 4, u⟫) (h25 : ⟪x 2, u⟫ ≠ ⟪x 5, u⟫)
    (hfar : 0 < det3 (x 5 - x 0) (x 4 - x 0) (x 2 - x 6) *
      det3 (x 5 - x 0) (x 4 - x 0) (x 1 - x 0))
    (hoff : det3 (x 5 - x 0) (x 4 - x 0) (cross (x 5 - x 4) (x 2 - x 4)) ≠ 0 ∨
      ⟪x 2 - x 4, x 5 - x 4⟫ < 0 ∨ ⟪x 2 - x 5, x 4 - x 5⟫ < 0) :
    IsRupert (univ.image x) :=
  isRupert_quadChord F (o := 0) (t := 3) (A := 4) (B := 5) (P := 6) (Q := 2) (I := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hη hu hρ hcyc h1 h3 hs₀ hs₁ hδ₃ h64 h45 h26 h24 h25 (w := 2) (w' := 6)
    (Or.inl ⟨rfl, rfl⟩) hfar hoff

/-- **Leaf Q05, mirror frame** (labels `(2 6)(4 5)`): at `u = (x 4 - x 0) + η (x 5 - x 0)`, rim
`2 5 4 6`, `3` a chord middle over `4 5`, depths `z2 < z5 < z4` with `z6` distinct, `6` strictly
farther from the plane of `0345` than `2`, its foot off the chord `[5, 4]`. -/
theorem isRupert_q05_mirror {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {η : ℝ} (hη : 0 ≤ η)
    {u : ℝ³} (hu : u = (x 4 - x 0) + η • (x 5 - x 0)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x 2) (x 5) (x 4) (x 6) (i + 1) - quad (x 2) (x 5) (x 4) (x 6) i)
        (quad (x 2) (x 5) (x 4) (x 6) j - quad (x 2) (x 5) (x 4) (x 6) i) u)
    (h1 : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x 2) (x 5) (x 4) (x 6) (i + 1) - quad (x 2) (x 5) (x 4) (x 6) i)
        (x 1 - quad (x 2) (x 5) (x 4) (x 6) i) u)
    {s₃ δ₃ : ℝ} (h3 : x 3 = x 4 + s₃ • (x 5 - x 4) + δ₃ • u) (hs₀ : 0 < s₃) (hs₁ : s₃ < 1)
    (hδ₃ : δ₃ ≠ 0)
    (h25 : ⟪x 2, u⟫ < ⟪x 5, u⟫) (h54 : ⟪x 5, u⟫ < ⟪x 4, u⟫)
    (h62 : ⟪x 6, u⟫ ≠ ⟪x 2, u⟫) (h65 : ⟪x 6, u⟫ ≠ ⟪x 5, u⟫) (h64 : ⟪x 6, u⟫ ≠ ⟪x 4, u⟫)
    (hfar : 0 < det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 2) *
      det3 (x 4 - x 0) (x 5 - x 0) (x 1 - x 0))
    (hoff : det3 (x 4 - x 0) (x 5 - x 0) (cross (x 4 - x 5) (x 6 - x 5)) ≠ 0 ∨
      ⟪x 6 - x 5, x 4 - x 5⟫ < 0 ∨ ⟪x 6 - x 4, x 5 - x 4⟫ < 0) :
    IsRupert (univ.image x) :=
  isRupert_quadChord F (o := 0) (t := 3) (A := 5) (B := 4) (P := 2) (Q := 6) (I := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hη hu hρ hcyc h1 h3 hs₀ hs₁ hδ₃ h25 h54 h62 h65 h64 (w := 6) (w' := 2)
    (Or.inl ⟨rfl, rfl⟩) hfar hoff

end Minimality.T24.Quad05

end
