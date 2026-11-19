module

public import Minimality.FaceCircleClosed
public import Minimality.SlideE
public import Minimality.EdgeSlide
public import Minimality.OctaTools
public import Minimality.BadViews
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# The on-face-circle chord-middle leaf (generic)

A view `u` on the face circle of a facet `X` (`⟪n, u⟫ = 0`, `n` the facet's normal): `X` is edge-on
and projects onto a rim edge `A B = c a, c (a + 1)`; the points of `X` strictly between `A` and `B`
are chord middles `m = A + s (B - A) + δ u` (`0 < s < 1`, `δ ≠ 0`).  If the rim `c` of the rest is
strictly convex at `u` with every other point strictly inside, the rim depths are distinct and
strictly unimodal (or have a depth-separated pair, `UniOrSep`), and the rim vertex `w` farthest from
the facet plane is unique with its foot (along `n`) off the chord `[A, B]` (Lemma H), then the hull
is Rupert (`ONCIRC24.md`, `T2SC24.md` Lemma AS).

Route: the slide `isRupert_of_slideP` along the facet circle, `u + τ (B - A)` (`τ → 0⁺`): every test
is strict at `u`, the middles stay over `A B` (`s - δ τ`), and the only persistent horizontal double
normal would be along `n`, which `noPersistHDN_of_far_offChord` (Lemma H) excludes.

* `isRupert_faceChord`: the core, for any `V`, any rim length `k ≥ 3`, any supporting plane
  `⟪n, ·⟫ ≤ κ` (generalizes `Minimality.T24.Quad05.isRupert_quadChord`).
* `isRupert_faceChord_cyc`: the same with a cyclically unimodal rim.
* `isRupert_faceChord_tri`: the leaf on a triangle facet `P Q R` of any `S0xFac` solid, view
  `u = α (x R - x P) + β (x R - x Q)`, middle `P`: the middle condition is `α β < 0 < α (α + β)`
  (no shape literal), Lemma H is two shape-only literals, the rest are the rim tests at `u`.
* Type 24 (`ONCIRC24.md` families `235 {2-5, 3-5}`, `126 {1-2, 1-6}`, their most frequent rims):
  `isRupert_f235_m2` (rim `0 1 6 3 5`), `isRupert_f235_m5` (rim `0 2 3 4`), `isRupert_f126_m1`
  (rim `0 4 6 2 5`), `isRupert_f126_m2` (rim `0 1 6 3 5`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.FaceChord
open Minimality Minimality.H21

theorem fcip (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- Three vectors orthogonal to a nonzero `n` are coplanar. -/
theorem det3_eq_zero_of_perp {n X Y Z : ℝ³} (hn : n ≠ 0) (hX : ⟪n, X⟫ = 0) (hY : ⟪n, Y⟫ = 0)
    (hZ : ⟪n, Z⟫ = 0) : det3 X Y Z = 0 := by
  by_contra hD
  apply hn
  rw [fcip] at hX hY hZ
  ext i
  fin_cases i
  · have : det3 X Y Z * n 0 = 0 := by
      rw [det3_expand]
      linear_combination (Y 1 * Z 2 - Y 2 * Z 1) * hX + (Z 1 * X 2 - Z 2 * X 1) * hY +
        (X 1 * Y 2 - X 2 * Y 1) * hZ
    simpa [hD] using this
  · have : det3 X Y Z * n 1 = 0 := by
      rw [det3_expand]
      linear_combination (Y 2 * Z 0 - Y 0 * Z 2) * hX + (Z 2 * X 0 - Z 0 * X 2) * hY +
        (X 2 * Y 0 - X 0 * Y 2) * hZ
    simpa [hD] using this
  · have : det3 X Y Z * n 2 = 0 := by
      rw [det3_expand]
      linear_combination (Y 0 * Z 1 - Y 1 * Z 0) * hX + (Z 0 * X 1 - Z 1 * X 0) * hY +
        (X 0 * Y 1 - X 1 * Y 0) * hZ
    simpa [hD] using this

theorem det3_e_u (e u Y : ℝ³) : det3 e Y u = ⟪cross u e, Y⟫ := by
  simp only [det3_expand, fcip, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

theorem cross_comb (u e : ℝ³) (s δ : ℝ) : cross u (s • e + δ • u) = s • cross u e := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- **The on-face-circle chord-middle leaf.**  `⟪n, ·⟫ ≤ κ` on `V` with equality at the rim edge
`A = c a`, `B = c (a + 1)`; the view `u` is in the face's direction plane (`⟪n, u⟫ = 0`).  At `u`:
the rim `c` is strictly convex with orientation `ρ` (`hcyc`), every point of `V` off `M` and off the
rim is strictly inside (`hin`), each `m ∈ M` is a chord middle over `A B` (`hM`), the rim depths are
distinct (`hinj`) and strictly unimodal or have a depth-separated pair (`hz`), the rim vertex `c w`
uniquely minimizes `⟪n, ·⟫` on the rim (`hfar`), and its foot along `n` is off the chord `[A, B]`
(`hoff`, Lemma H).  Then `V` is Rupert. -/
theorem isRupert_faceChord {V M : Finset ℝ³} {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → ℝ³)
    (hcV : ∀ i, c i ∈ V) {n : ℝ³} {κ : ℝ} (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) {a : ZMod k}
    (hA : ⟪n, c a⟫ = κ) (hB : ⟪n, c (a + 1)⟫ = κ) {u : ℝ³} (hnu : ⟪n, u⟫ = 0) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u)
    (hin : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ c j) → ∀ i,
      0 < ρ * det3 (c (i + 1) - c i) (y - c i) u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c a + s • (c (a + 1) - c a) + δ • u)
    (hinj : Function.Injective fun i => ⟪c i, u⟫) (hz : UniOrSep c u) {w : ZMod k}
    (hfar : ∀ m, m ≠ w → ⟪n, c w⟫ < ⟪n, c m⟫)
    (hoff : ⟪n, cross (c (a + 1) - c a) (c w - c a)⟫ ≠ 0 ∨
      ⟪c w - c a, c (a + 1) - c a⟫ < 0 ∨ ⟪c w - c (a + 1), c a - c (a + 1)⟫ < 0) :
    IsRupert V := by
  classical
  have hk2 : 2 ≤ k := by omega
  set e : ℝ³ := c (a + 1) - c a with he
  have hcinj : Function.Injective c := fun i j h => hinj (by simp only [h])
  have hu0 : u ≠ 0 := by
    intro h0
    apply zmod_ne_add_one hk2 0
    exact hinj (by simp [h0])
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfar (w + 1) (fun h => zmod_ne_add_one hk2 w h.symm)
    simp at this
  have hne : ⟪n, e⟫ = 0 := by rw [he, inner_sub_right, hA, hB, sub_self]
  -- the third rim vertex after `a`
  have ha2 : a + 2 ≠ a := by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) a
    simpa using this
  have ha21 : a + 2 ≠ a + 1 := by
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) a
    simpa using this
  have hcross : cross u e ≠ 0 := by
    intro h0
    have := hcyc a (a + 2) ha2 ha21
    rw [← he, det3_e_u, h0, inner_zero_left, mul_zero] at this
    exact lt_irrefl _ this
  -- the rim meets the face only in `A`, `B`
  have htop : ∀ m, ⟪n, c m⟫ = κ → c m = c a ∨ c m = c (a + 1) := by
    intro m hm
    by_contra hcon
    push Not at hcon
    have hma : m ≠ a := fun h => hcon.1 (by rw [h])
    have hma1 : m ≠ a + 1 := fun h => hcon.2 (by rw [h])
    have := hcyc a m hma hma1
    rw [det3_eq_zero_of_perp hn0 hne (by rw [inner_sub_right, hm, hA, sub_self]) hnu,
      mul_zero] at this
    exact lt_irrefl _ this
  -- no rim vertex is a middle
  have hcM : ∀ i, c i ∉ M := by
    intro i hi
    obtain ⟨s, δ, hs0, hs1, -, hm⟩ := hM _ hi
    by_cases hia : i = a
    · rw [hia] at hm
      have h1 : s • e + δ • u = 0 := by
        have : s • e + δ • u = (c a + s • e + δ • u) - c a := by abel
        rw [this, ← hm, sub_self]
      have := cross_comb u e s δ
      rw [h1] at this
      have h2 : s • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      exact hs0.ne' ((smul_eq_zero.mp h2).resolve_right hcross)
    by_cases hia1 : i = a + 1
    · have h2 : c (a + 1) = c a + e := by rw [he]; abel
      rw [hia1, h2] at hm
      have h1 : (s - 1) • e + δ • u = 0 := by
        have : (s - 1) • e + δ • u = (c a + s • e + δ • u) - (c a + e) := by module
        rw [this, ← hm, sub_self]
      have := cross_comb u e (s - 1) δ
      rw [h1] at this
      have h2 : (s - 1) • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      have := (smul_eq_zero.mp h2).resolve_right hcross
      linarith
    · have := hcyc a i hia hia1
      rw [← he, hm, show c a + s • e + δ • u - c a = s • e + δ • u by abel, det3_e_u,
        inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_cross_left,
        inner_cross_right] at this
      simp at this
  -- the middles along the slide `u + τ e`
  have hM' : ∀ m ∈ M, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ,
      0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c i + s • (c (i + 1) - c i) + δ • (u + τ • e) := by
    intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
    have hlim : Tendsto (fun τ : ℝ => s - δ * τ) (𝓝[>] 0) (𝓝 s) := by
      have : Continuous (fun τ : ℝ => s - δ * τ) := by fun_prop
      have h := this.tendsto 0
      simp only [mul_zero, sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (Ioo_mem_nhds hs0 hs1)] with τ hτ
    refine ⟨a, s - δ * τ, δ, hτ.1, hτ.2, hδ, ?_⟩
    rw [← he, smul_add, smul_smul, sub_smul]
    abel
  have hbad : NoPersistHDN c u e :=
    noPersistHDN_of_far_offChord (V := V) hk2 c hcinj hcV hle hA hB ⟨a, rfl⟩ htop ⟨w, rfl⟩
      (fun m hm => hfar m fun h => hm (by rw [h])) hnu hne hcross hoff
  exact isRupert_of_slideP V M u e hu0 c hcV hcM hk ρ hρ
    (fun i j h1 h2 => Or.inl (hcyc i j h1 h2)) (fun y hy hyM hyc i => Or.inl (hin y hy hyM hyc i))
    hM' hinj hz hbad

/-- `isRupert_faceChord` with a cyclically unimodal rim (distinct depths, one peak). -/
theorem isRupert_faceChord_cyc {V M : Finset ℝ³} {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → ℝ³) (hcV : ∀ i, c i ∈ V) {n : ℝ³} {κ : ℝ} (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ)
    {a : ZMod k} (hA : ⟪n, c a⟫ = κ) (hB : ⟪n, c (a + 1)⟫ = κ) {u : ℝ³} (hnu : ⟪n, u⟫ = 0)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u)
    (hin : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ c j) → ∀ i,
      0 < ρ * det3 (c (i + 1) - c i) (y - c i) u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c a + s • (c (a + 1) - c a) + δ • u)
    (hz : IsCyclicUnimodal fun i => ⟪c i, u⟫) {w : ZMod k}
    (hfar : ∀ m, m ≠ w → ⟪n, c w⟫ < ⟪n, c m⟫)
    (hoff : ⟪n, cross (c (a + 1) - c a) (c w - c a)⟫ ≠ 0 ∨
      ⟪c w - c a, c (a + 1) - c a⟫ < 0 ∨ ⟪c w - c (a + 1), c a - c (a + 1)⟫ < 0) :
    IsRupert V :=
  isRupert_faceChord hk c hcV hle hA hB hnu hρ hcyc hin hM hz.1
    (Or.inl (strictUnimodal_of_cyclic (by omega) hz)) hfar hoff

/-- `det3 e u ·` is proportional to `⟪n, ·⟫` when `e, u ⟂ n` (the identity, for all vectors). -/
theorem det3_perp_ratio (n e u Y Z : ℝ³) :
    det3 e u Y * ⟪n, Z⟫ - det3 e u Z * ⟪n, Y⟫ = ⟪n, e⟫ * det3 Y Z u - ⟪n, u⟫ * det3 Y Z e := by
  simp only [det3_expand, fcip]; ring

/-- **The chord leaf on a triangle facet, for any `S0xFac` solid.**  `P, Q, R` are vertices of facet
`t`; the view `u = α (x R - x P) + β (x R - x Q)` with `α β < 0 < α (α + β)` (the arc of the facet
circle on which `P` projects strictly between `Q` and `R`).  The rim `r` (labels) contains the
chord edge `Q R` as an edge (either orientation), is strictly convex at `u` (`hcyc`), every label
other than `P` and the rim is strictly inside (`hin`), the rim depths are distinct and strictly
unimodal or depth-separated (`hinj`, `hz`).  Lemma H: the rim vertex `r w` is off the facet and
strictly farther from its plane than every other off-facet rim vertex (`hfar`, as determinants
against the facet's orientation `det3 (x R - x Q) (x R - x P) ·`), and its foot is off the chord
(`hoff`).  Then the hull is Rupert.  (`P` is the only middle.) -/
theorem isRupert_faceChord_tri {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {P Q R : Fin N} (hP : P ∈ S t) (hQ : Q ∈ S t)
    (hR : R ∈ S t) {α β : ℝ} (hαβ : α * β < 0) (hαβ' : 0 < α * (α + β)) {u : ℝ³}
    (hu : u = α • (x R - x P) + β • (x R - x Q)) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (r : ZMod k → Fin N) {a : ZMod k}
    (hQR : (r a = Q ∧ r (a + 1) = R) ∨ (r a = R ∧ r (a + 1) = Q)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hin : ∀ q, q ≠ P → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u)
    (hinj : Function.Injective fun i => ⟪x (r i), u⟫) (hz : UniOrSep (fun i => x (r i)) u)
    {w : ZMod k} (hwS : r w ∉ S t)
    (hfar : ∀ m, m ≠ w → r m ∉ S t →
      det3 (x R - x Q) (x R - x P) (x (r m) - x (r w)) *
        det3 (x R - x Q) (x R - x P) (x (r w) - x Q) < 0)
    (hoff : det3 (x R - x Q) (x R - x P) (cross (x R - x Q) (x (r w) - x Q)) ≠ 0 ∨
      ⟪x (r w) - x Q, x R - x Q⟫ < 0 ∨ ⟪x (r w) - x R, x Q - x R⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  set n := F.N t with hn
  have Nsub : ∀ i j : Fin N, ⟪n, x i - x j⟫ = F.f t (x i) - F.f t (x j) := F.inner_sub t
  have fP := F.zero t P hP
  have fQ := F.zero t Q hQ
  have fR := F.zero t R hR
  have fw := F.neg t _ hwS
  have hα : α ≠ 0 := by rintro rfl; simp at hαβ
  set E : ℝ³ := x R - x Q with hE
  set U : ℝ³ := x R - x P with hU
  have hnE : ⟪n, E⟫ = 0 := by rw [hE, Nsub, fR, fQ, sub_self]
  have hnU : ⟪n, U⟫ = 0 := by rw [hU, Nsub, fR, fP, sub_self]
  have hnu : ⟪n, u⟫ = 0 := by
    rw [hu, inner_add_right, real_inner_smul_right, real_inner_smul_right, hnE, hnU]
    ring
  set Zw : ℝ³ := x (r w) - x Q with hZw
  have hζ : ⟪n, Zw⟫ < 0 := by rw [hZw, Nsub, fQ, sub_zero]; exact fw
  have key : ∀ Y, det3 E U Y * ⟪n, Zw⟫ = det3 E U Zw * ⟪n, Y⟫ := by
    intro Y
    linear_combination det3_perp_ratio n E U Y Zw + det3 Y Zw U * hnE - det3 Y Zw E * hnU
  have hle : ∀ z ∈ univ.image x, ⟪n, z⟫ ≤ ⟪n, x Q⟫ := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    have := Nsub j Q
    rw [inner_sub_right, fQ] at this
    linarith [F.le t j]
  have hface : ∀ j, j ∈ S t → ⟪n, x j⟫ = ⟪n, x Q⟫ := by
    intro j hj
    have := Nsub j Q
    rw [inner_sub_right, F.zero t j hj, fQ] at this
    linarith
  -- the chord ends and the middle `P`
  have hfar' : ∀ m, m ≠ w → ⟪n, x (r w)⟫ < ⟪n, x (r m)⟫ := by
    intro m hm
    by_cases hmS : r m ∈ S t
    · rw [hface _ hmS]
      have := Nsub (r w) Q
      rw [inner_sub_right, fQ] at this
      linarith
    · have h := hfar m hm hmS
      set Y := x (r m) - x (r w)
      have h1 : 0 < det3 E U Y * det3 E U Zw * ⟪n, Zw⟫ := mul_pos_of_neg_of_neg h hζ
      have h2 : det3 E U Y * det3 E U Zw * ⟪n, Zw⟫ = det3 E U Zw ^ 2 * ⟪n, Y⟫ := by
        linear_combination det3 E U Zw * key Y
      rw [h2] at h1
      have h3 := pos_of_mul_pos_right h1 (sq_nonneg _)
      rw [inner_sub_right] at h3
      linarith
  have hchi : det3 E U (cross E Zw) ≠ 0 → ⟪n, cross E Zw⟫ ≠ 0 := by
    intro h h0
    apply h
    have := key (cross E Zw)
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hζ.ne
  have hPmid : ∀ A B : Fin N, (A = Q ∧ B = R) ∨ (A = R ∧ B = Q) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧
      δ ≠ 0 ∧ x P = x A + s • (x B - x A) + δ • u := by
    intro A B h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨(α + β) / α, -1 / α, ?_, ?_, div_ne_zero (by norm_num) hα, ?_⟩
      · have : (α + β) / α = α * (α + β) / (α * α) := by field_simp
        rw [this]; exact div_pos hαβ' (mul_self_pos.mpr hα)
      · have : (α + β) / α = 1 + α * β / (α * α) := by field_simp
        rw [this]
        have := div_neg_of_neg_of_pos hαβ (mul_self_pos.mpr hα)
        linarith
      · rw [hu, hU, hE]; ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp; ring
    · refine ⟨-β / α, -1 / α, ?_, ?_, div_ne_zero (by norm_num) hα, ?_⟩
      · have : -β / α = -(α * β) / (α * α) := by field_simp
        rw [this]; exact div_pos (by linarith) (mul_self_pos.mpr hα)
      · have : -β / α = 1 - α * (α + β) / (α * α) := by field_simp; ring
        rw [this]
        have := div_pos hαβ' (mul_self_pos.mpr hα)
        linarith
      · rw [hu, hU, hE]; ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp; ring
  obtain ⟨hA, hB, hoff'⟩ : ⟪n, x (r a)⟫ = ⟪n, x Q⟫ ∧ ⟪n, x (r (a + 1))⟫ = ⟪n, x Q⟫ ∧
      (⟪n, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
        ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0) := by
    rcases hQR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      refine ⟨rfl, hface R hR, ?_⟩
      rcases hoff with h | h | h
      · exact Or.inl (hchi h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [h1, h2]
      refine ⟨hface R hR, rfl, ?_⟩
      rcases hoff with h | h | h
      · left
        have e1 : cross (x Q - x R) (x (r w) - x R) = -cross E Zw := by
          rw [hE, hZw]; ext j; fin_cases j <;> simp [cross] <;> ring
        rw [e1, inner_neg_right, neg_ne_zero]
        exact hchi h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have hmid : ∀ m ∈ ({x P} : Finset ℝ³), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u := by
    intro m hm
    rw [mem_singleton] at hm
    subst hm
    exact hPmid _ _ (by rcases hQR with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])
  refine isRupert_faceChord (M := {x P}) hk (fun i => x (r i))
    (fun i => mem_image_of_mem x (mem_univ _)) hle hA hB hnu hρ hcyc ?_ hmid hinj hz hfar' hoff'
  intro y hy hyM hyc i
  obtain ⟨q, -, rfl⟩ := mem_image.mp hy
  exact hin q (fun h => hyM (by rw [h, mem_singleton])) (fun j h => hyc j (by rw [h])) i

end Minimality.FaceChord

/-! ## Type-24 instances (`ONCIRC24.md` families `235 {2-5, 3-5}` and `126 {1-2, 1-6}`) -/

namespace Minimality.T24.FaceChord
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT

/-- Rim `0 1 6 3 5` (chord `3 5`). -/
def rim01635 : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
/-- Rim `0 2 3 4` (chord `2 3`). -/
def rim0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
/-- Rim `0 4 6 2 5` (chord `6 2`). -/
def rim04625 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

/-- **Leaf `235`, middle `2`** (the most frequent pattern of the family `235 {2-5, 3-5}`): at
`u = α (x 5 - x 2) + β (x 5 - x 3)` with `α β < 0 < α (α + β)` (vertex `2` projects strictly inside the
chord `3 5`), the rim `0 1 6 3 5` is strictly convex (orientation `ρ`) with `4` strictly inside, the
rim depths are cyclically unimodal; the rim vertex `r w` (`w ∈ {0, 1, 6}`, i.e. `w ∉ {3, 4}` as
indices) is strictly farther from the plane of `235` than the other two of `0, 1, 6`, with its foot
off the chord `[3, 5]`.  Then `K` is Rupert. -/
theorem isRupert_f235_m2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hαβ : α * β < 0)
    (hαβ' : 0 < α * (α + β)) {u : ℝ³} (hu : u = α • (x 5 - x 2) + β • (x 5 - x 3)) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rim01635 (i + 1)) - x (rim01635 i)) (x (rim01635 j) - x (rim01635 i)) u)
    (h4 : ∀ i : ZMod 5,
      0 < ρ * det3 (x (rim01635 (i + 1)) - x (rim01635 i)) (x 4 - x (rim01635 i)) u)
    (hz : IsCyclicUnimodal fun i => ⟪x (rim01635 i), u⟫) {w : ZMod 5} (hw3 : w ≠ 3)
    (hw4 : w ≠ 4)
    (hfar : ∀ m : ZMod 5, m ≠ w → m ≠ 3 → m ≠ 4 →
      det3 (x 5 - x 3) (x 5 - x 2) (x (rim01635 m) - x (rim01635 w)) *
        det3 (x 5 - x 3) (x 5 - x 2) (x (rim01635 w) - x 3) < 0)
    (hoff : det3 (x 5 - x 3) (x 5 - x 2) (cross (x 5 - x 3) (x (rim01635 w) - x 3)) ≠ 0 ∨
      ⟪x (rim01635 w) - x 3, x 5 - x 3⟫ < 0 ∨ ⟪x (rim01635 w) - x 5, x 3 - x 5⟫ < 0) :
    IsRupert (univ.image x) := by
  have hS : ∀ m : ZMod 5, rim01635 m ∈ s0x_S24 6 ↔ m = 3 ∨ m = 4 := by decide
  refine isRupert_faceChord_tri F 6 (P := 2) (Q := 3) (R := 5) (by decide) (by decide)
    (by decide) hαβ hαβ' hu (by norm_num) rim01635 (a := 3) (Or.inl ⟨rfl, rfl⟩) hρ hcyc ?_
    hz.1 (Or.inl (strictUnimodal_of_cyclic (by norm_num) hz)) (w := w) ?_ ?_ hoff
  · intro q hq2 hqr i
    have : q = 4 := by revert q hq2 hqr; decide
    subst this
    exact h4 i
  · rw [hS]; tauto
  · intro m hm hmS
    rw [hS] at hmS
    push Not at hmS
    exact hfar m hm hmS.1 hmS.2

/-- **Leaf `235`, middle `5`**: at `u = α (x 5 - x 2) + β (x 5 - x 3)` with `0 < α (α + β)` and
`0 < β (α + β)` (vertex `5` strictly inside the chord `2 3`), the rim `0 2 3 4` strictly convex with
`1`, `6` strictly inside, cyclically unimodal depths, the off-facet rim vertex `r w` (`w ∈ {0, 3}`,
i.e. vertex `0` or `4`) strictly farther from the plane of `235` than the other one, its foot off
the chord `[3, 2]`.  Then `K` is Rupert. -/
theorem isRupert_f235_m5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {α β : ℝ}
    (hα : 0 < α * (α + β)) (hβ : 0 < β * (α + β)) {u : ℝ³}
    (hu : u = α • (x 5 - x 2) + β • (x 5 - x 3)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rim0234 (i + 1)) - x (rim0234 i)) (x (rim0234 j) - x (rim0234 i)) u)
    (h1 : ∀ i : ZMod 4, 0 < ρ * det3 (x (rim0234 (i + 1)) - x (rim0234 i)) (x 1 - x (rim0234 i)) u)
    (h6 : ∀ i : ZMod 4, 0 < ρ * det3 (x (rim0234 (i + 1)) - x (rim0234 i)) (x 6 - x (rim0234 i)) u)
    (hz : IsCyclicUnimodal fun i => ⟪x (rim0234 i), u⟫) {w : ZMod 4} (hw1 : w ≠ 1)
    (hw2 : w ≠ 2)
    (hfar : ∀ m : ZMod 4, m ≠ w → m ≠ 1 → m ≠ 2 →
      det3 (x 2 - x 3) (x 2 - x 5) (x (rim0234 m) - x (rim0234 w)) *
        det3 (x 2 - x 3) (x 2 - x 5) (x (rim0234 w) - x 3) < 0)
    (hoff : det3 (x 2 - x 3) (x 2 - x 5) (cross (x 2 - x 3) (x (rim0234 w) - x 3)) ≠ 0 ∨
      ⟪x (rim0234 w) - x 3, x 2 - x 3⟫ < 0 ∨ ⟪x (rim0234 w) - x 2, x 3 - x 2⟫ < 0) :
    IsRupert (univ.image x) := by
  have hS : ∀ m : ZMod 4, rim0234 m ∈ s0x_S24 6 ↔ m = 1 ∨ m = 2 := by decide
  refine isRupert_faceChord_tri F 6 (P := 5) (Q := 3) (R := 2) (α := -(α + β)) (β := β)
    (by decide) (by decide) (by decide) (by nlinarith) (by nlinarith)
    (by rw [hu]; module) (by norm_num) rim0234 (a := 1) (Or.inr ⟨rfl, rfl⟩) hρ hcyc ?_
    hz.1 (Or.inl (strictUnimodal_of_cyclic (by norm_num) hz)) (w := w) ?_ ?_ hoff
  · intro q hq5 hqr i
    have : q = 1 ∨ q = 6 := by revert q hq5 hqr; decide
    rcases this with rfl | rfl
    exacts [h1 i, h6 i]
  · rw [hS]; tauto
  · intro m hm hmS
    rw [hS] at hmS
    push Not at hmS
    exact hfar m hm hmS.1 hmS.2

/-- **Leaf `126`, middle `1`** (the most frequent pattern of the family `126 {1-2, 1-6}`): at
`u = α (x 2 - x 1) + β (x 6 - x 1)` with `0 < α (α + β)` and `0 < β (α + β)` (vertex `1` strictly
inside the chord `6 2`), the rim `0 4 6 2 5` strictly convex with `3` strictly inside, cyclically
unimodal depths, the off-facet rim vertex `r w` (`w ∈ {0, 1, 4}`) strictly farther from the plane of
`126` than the other two, its foot off the chord `[6, 2]`.  Then `K` is Rupert. -/
theorem isRupert_f126_m1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {α β : ℝ}
    (hα : 0 < α * (α + β)) (hβ : 0 < β * (α + β)) {u : ℝ³}
    (hu : u = α • (x 2 - x 1) + β • (x 6 - x 1)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rim04625 (i + 1)) - x (rim04625 i)) (x (rim04625 j) - x (rim04625 i)) u)
    (h3 : ∀ i : ZMod 5,
      0 < ρ * det3 (x (rim04625 (i + 1)) - x (rim04625 i)) (x 3 - x (rim04625 i)) u)
    (hz : IsCyclicUnimodal fun i => ⟪x (rim04625 i), u⟫) {w : ZMod 5} (hw2 : w ≠ 2)
    (hw3 : w ≠ 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → m ≠ 2 → m ≠ 3 →
      det3 (x 2 - x 6) (x 2 - x 1) (x (rim04625 m) - x (rim04625 w)) *
        det3 (x 2 - x 6) (x 2 - x 1) (x (rim04625 w) - x 6) < 0)
    (hoff : det3 (x 2 - x 6) (x 2 - x 1) (cross (x 2 - x 6) (x (rim04625 w) - x 6)) ≠ 0 ∨
      ⟪x (rim04625 w) - x 6, x 2 - x 6⟫ < 0 ∨ ⟪x (rim04625 w) - x 2, x 6 - x 2⟫ < 0) :
    IsRupert (univ.image x) := by
  have hS : ∀ m : ZMod 5, rim04625 m ∈ s0x_S24 5 ↔ m = 2 ∨ m = 3 := by decide
  refine isRupert_faceChord_tri F 5 (P := 1) (Q := 6) (R := 2) (α := α + β) (β := -β)
    (by decide) (by decide) (by decide) (by nlinarith) (by nlinarith)
    (by rw [hu]; module) (by norm_num) rim04625 (a := 2) (Or.inl ⟨rfl, rfl⟩) hρ hcyc ?_
    hz.1 (Or.inl (strictUnimodal_of_cyclic (by norm_num) hz)) (w := w) ?_ ?_ hoff
  · intro q hq1 hqr i
    have : q = 3 := by revert q hq1 hqr; decide
    subst this
    exact h3 i
  · rw [hS]; tauto
  · intro m hm hmS
    rw [hS] at hmS
    push Not at hmS
    exact hfar m hm hmS.1 hmS.2

/-- **Leaf `126`, middle `2`**: at `u = α (x 2 - x 1) + β (x 6 - x 1)` with `α β < 0 < α (α + β)`
(vertex `2` strictly inside the chord `1 6`), the rim `0 1 6 3 5` strictly convex with `4` strictly
inside, cyclically unimodal depths, the off-facet rim vertex `r w` (`w ∈ {0, 3, 4}`) strictly
farther from the plane of `126` than the other two, its foot off the chord `[6, 1]`.  Then `K` is
Rupert. -/
theorem isRupert_f126_m2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {α β : ℝ} (hαβ : α * β < 0)
    (hαβ' : 0 < α * (α + β)) {u : ℝ³} (hu : u = α • (x 2 - x 1) + β • (x 6 - x 1)) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rim01635 (i + 1)) - x (rim01635 i)) (x (rim01635 j) - x (rim01635 i)) u)
    (h4 : ∀ i : ZMod 5,
      0 < ρ * det3 (x (rim01635 (i + 1)) - x (rim01635 i)) (x 4 - x (rim01635 i)) u)
    (hz : IsCyclicUnimodal fun i => ⟪x (rim01635 i), u⟫) {w : ZMod 5} (hw1 : w ≠ 1)
    (hw2 : w ≠ 2)
    (hfar : ∀ m : ZMod 5, m ≠ w → m ≠ 1 → m ≠ 2 →
      det3 (x 1 - x 6) (x 1 - x 2) (x (rim01635 m) - x (rim01635 w)) *
        det3 (x 1 - x 6) (x 1 - x 2) (x (rim01635 w) - x 6) < 0)
    (hoff : det3 (x 1 - x 6) (x 1 - x 2) (cross (x 1 - x 6) (x (rim01635 w) - x 6)) ≠ 0 ∨
      ⟪x (rim01635 w) - x 6, x 1 - x 6⟫ < 0 ∨ ⟪x (rim01635 w) - x 1, x 6 - x 1⟫ < 0) :
    IsRupert (univ.image x) := by
  have hS : ∀ m : ZMod 5, rim01635 m ∈ s0x_S24 5 ↔ m = 1 ∨ m = 2 := by decide
  refine isRupert_faceChord_tri F 5 (P := 2) (Q := 6) (R := 1) (α := -α) (β := -β)
    (by decide) (by decide) (by decide) (by nlinarith) (by nlinarith)
    (by rw [hu]; module) (by norm_num) rim01635 (a := 1) (Or.inr ⟨rfl, rfl⟩) hρ hcyc ?_
    hz.1 (Or.inl (strictUnimodal_of_cyclic (by norm_num) hz)) (w := w) ?_ ?_ hoff
  · intro q hq2 hqr i
    have : q = 4 := by revert q hq2 hqr; decide
    subst this
    exact h4 i
  · rw [hS]; tauto
  · intro m hm hmS
    rw [hS] at hmS
    push Not at hmS
    exact hfar m hm hmS.1 hmS.2

end Minimality.T24.FaceChord

end
