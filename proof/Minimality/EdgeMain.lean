module

public import Minimality.EdgeClassD

@[expose] public section

/-!
# The horizontal-double-normal item of a four-corner edge closing (`FEWER-FACES-PROOFS.md` §22)

`EdgeConf.isRupert_edgeClosing`: in an `EdgeConf` (an edge view with two faces, at most one
middle each, and the closing `K_v` with the rim `v a c b`), a robustly unimodal `K_v` makes the
set Rupert under the codimension-2 conditions of §22.4: all depths at `u` distinct, at most one
direction of horizontal double normals at `u` (`OneHDNDir`), no double normal perpendicular to a
face from an end of its side (`FootA`, `FootB`), and Lemma E strict where a far edge is parallel
to a face.  The cases:
* realized on both circles: Proposition 22.2 (`isRupert_twoCircle`, no condition at all);
* realized on one circle: the slide of `K_v` (Lemma 22.3); a persistent double normal is of
  class `c` (Lemma 22.4) or `d` (Theorem 22.8);
* realized on no circle (both faces quadrilaterals with their far ends next to `w`): the
  partner `K_w` is realized on both circles (22.2); otherwise one slide rim is strictly
  unimodal (Lemma 22.7), and its persistent double normals are of class `c` or `d`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- No double normal perpendicular to `F_a` from an end of its side `[v, a]` to the minimal set
of the far corners: a far corner with its foot on the face at `v` or `a`, or a far edge parallel
to the face whose foot passes through `v` or `a` (two conditions on the shape). -/
def FootA (v a c b Na : ℝ³) : Prop :=
  ∀ F ∈ segment ℝ c b, ⟪Na, F⟫ = min ⟪Na, c⟫ ⟪Na, b⟫ → ∀ r : ℝ, r ≠ 0 →
    F - v ≠ r • Na ∧ F - a ≠ r • Na

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

/-- A vector perpendicular to `u` and to the chord `a − v` is a multiple of `N_a`. -/
theorem eq_smul_Na (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {X : ℝ³}
    (hXu : ⟪X, u⟫ = 0) (hXa : ⟪X, a - v⟫ = 0) : ∃ r : ℝ, X = r • Na := by
  set C := cross (a - v) u with hC
  have hC0 : C ≠ 0 := E.cross_av
  have h1 : cross C X = 0 := by
    rw [hC, cross_cross_eq, real_inner_comm, hXa, real_inner_comm, hXu, zero_smul, zero_smul,
      sub_zero]
  have h2 : cross C Na = 0 := by
    rw [hC, cross_cross_eq, real_inner_comm, E.Na_av, real_inner_comm, E.Na_u, zero_smul,
      zero_smul, sub_zero]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, X = t • C := ⟨_, eq_smul_of_cross_eq_zero hC0 h1⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℝ, Na = t' • C := ⟨_, eq_smul_of_cross_eq_zero hC0 h2⟩
  have ht'0 : t' ≠ 0 := by rintro rfl; rw [zero_smul] at ht'; exact E.Na_ne ht'
  refine ⟨t / t', ?_⟩
  rw [ht, ht', smul_smul, div_mul_cancel₀ _ ht'0]

/-- The middle of `F_a` is on `w`'s side of the chord (`δ h > 0`) or on the far side. -/
theorem midA_side (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma) :
    (∃ k : ℝ, 0 < k ∧ cross (a - v) (m - v) = k • cross (a - v) (w - v)) ∨ OppA v w a m := by
  obtain ⟨s, δ, hs0, hs1, hmeq⟩ := E.midA_coords hm
  have hδ := E.midA_delta_ne hm hs0 hs1 hmeq
  have e1 : cross (a - v) (m - v) = δ • cross (a - v) u := by
    rw [hmeq, show v + s • (a - v) + δ • u - v = s • (a - v) + δ • u by abel,
      cross_sub_smul_eq]
  have e2 : cross (a - v) (w - v) = h • cross (a - v) u := by
    rw [E.hw, add_sub_cancel_left, cross_smul_right']
  have key : cross (a - v) (m - v) = (δ / h) • cross (a - v) (w - v) := by
    rw [e1, e2, smul_smul, div_mul_cancel₀ _ E.hh]
  rcases lt_or_gt_of_ne (div_ne_zero hδ E.hh) with hk | hk
  · exact Or.inr ⟨δ / h, hk, key⟩
  · exact Or.inl ⟨δ / h, hk, key⟩

theorem midB_side (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Mb) :
    (∃ k : ℝ, 0 < k ∧ cross (v - b) (m - b) = k • cross (v - b) (w - b)) ∨
      OppA v w b m := by
  rcases E.mirror.midA_side hm with ⟨k, hk, hk'⟩ | ⟨k, hk, hk'⟩
  · left
    refine ⟨k, hk, ?_⟩
    have e1 : cross (v - b) (m - b) = -cross (b - v) (m - v) := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    have e2 : cross (v - b) (w - b) = -cross (b - v) (w - v) := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [e1, e2, hk', smul_neg]
  · exact Or.inr ⟨k, hk, hk'⟩

/-- **(H1) of the configuration** (Theorem 22.8's depths, in the orientation `v − w`): with
`F_a`'s middle `m` on the far side of its chord, distinct depths, `K_v` without and `K_w` with a
weak saddle, and the slide rim `v m a c b` not strictly unimodal. -/
theorem h1_of_config (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma)
    (hopp : OppA v w a m) (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hKw : ¬ NWS4 (quad ⟪w, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (h5 : ¬ StrictUnimodal (fun i => ⟪quint v m a c b i, u⟫)) :
    ⟪v, v - w⟫ < ⟪m, v - w⟫ ∧ ⟪v, v - w⟫ < ⟪b, v - w⟫ ∧ ⟪a, v - w⟫ < ⟪v, v - w⟫ ∧
      ⟪c, v - w⟫ < ⟪v, v - w⟫ := by
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hopp
  have hinj := E.quint_inj_of_dist hm hdist
  have hh := E.hh
  have hw := E.hw
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr E.hu
  have hvw : v - w = (-h) • u := by rw [hw]; module
  have hζ : ∀ X : ℝ³, ⟪X, v - w⟫ = -h * ⟪X, u⟫ := by
    intro X; rw [hvw, real_inner_smul_right]
  have hq : ∀ k, quint ⟪v, v - w⟫ ⟪m, v - w⟫ ⟪a, v - w⟫ ⟪c, v - w⟫ ⟪b, v - w⟫ k =
      -h * ⟪quint v m a c b k, u⟫ := by
    intro k; rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, hζ]
  have hinjζ : Function.Injective (quint ⟪v, v - w⟫ ⟪m, v - w⟫ ⟪a, v - w⟫ ⟪c, v - w⟫
      ⟪b, v - w⟫) := by
    intro i j hij
    rw [hq, hq] at hij
    exact hinj (mul_left_cancel₀ (neg_ne_zero.mpr hh) hij)
  refine h1_core (zv := ⟪v, v - w⟫) (zm := ⟪m, v - w⟫) (zf := ⟪a, v - w⟫)
    (zgf := ⟪c, v - w⟫) (zgv := ⟪b, v - w⟫) (zw := ⟪w, v - w⟫) hs0 hs1 ?_ ?_ ?_ ?_ hinjζ ?_
  · rw [hζ, hζ, hζ, hmeq]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    nlinarith [mul_pos (neg_pos.mpr hδh) huu]
  · rw [hζ, hζ, hw]
    simp only [inner_add_left, real_inner_smul_left]
    nlinarith [mul_pos (mul_self_pos.mpr hh) huu]
  · simp only [hζ]; exact nws4_quad_scale (neg_ne_zero.mpr hh) hz
  · intro hc
    apply hKw
    simp only [hζ] at hc
    have := nws4_quad_scale (inv_ne_zero (neg_ne_zero.mpr hh)) hc
    simp only [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hh), one_mul] at this
    exact this
  · refine two_peaks hinjζ fun hs => h5 ?_
    have hq' : (fun i => -h * ⟪quint v m a c b i, u⟫) =
        quint ⟪v, v - w⟫ ⟪m, v - w⟫ ⟪a, v - w⟫ ⟪c, v - w⟫ ⟪b, v - w⟫ := by
      funext k; rw [hq]
    exact strictUnimodal_of_scaled (by norm_num) hinj (neg_ne_zero.mpr hh) (hq' ▸ hs)

/-- **A persistent double normal perpendicular to `F_a`** (on any rim `R` with `v`, `a` its only
vertices on `F_a` and `c`, `b` its lowest) is of class `c` (Lemma 22.4) or `d` (Theorem 22.8);
an end at `v` or `a` is excluded by `FootA`. -/
theorem isRupert_persistA (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfoot : FootA v a c b Na)
    (hE : ⟪Na, c⟫ = ⟪Na, b⟫ → det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0)
    {k : ℕ} (hk : 2 ≤ k) (R : ZMod k → ℝ³) (hRinj : Function.Injective R) (hRV : ∀ i, R i ∈ V)
    (hsupp : ∀ z ∈ V, SuppIn u R z) (hvR : ∃ i, R i = v)
    (htop : ∀ i, ⟪Na, R i⟫ = κa → R i = v ∨ R i = a) (hcR : ∃ i, R i = c) (hbR : ∃ i, R i = b)
    (hlow : ∀ i, R i ≠ c → R i ≠ b → min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, R i⟫)
    {i j : ZMod k} {Y Y' : ℝ³} (hY : Y ∈ segment ℝ (R i) (R (i + 1)))
    (hY' : Y' ∈ segment ℝ (R j) (R (j + 1))) (hne : Y' ≠ Y) (hu : ⟪Y' - Y, u⟫ = 0)
    (hea : ⟪Y' - Y, a - v⟫ = 0)
    (hext : ∀ m, ⟪Y' - Y, R m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', R m - Y⟫ ≤ 0) : IsRupert V := by
  obtain ⟨r, hr⟩ := E.eq_smul_Na hu hea
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [zero_smul] at hr; exact hne (sub_eq_zero.mp hr)
  have hdir := hdnDir_of_rim R hRV hsupp hY hY' hne hu hext
  have hℓa : cross (Y' - Y) Na = 0 := by rw [hr, cross_smul_left'', cross_self, smul_zero]
  obtain ⟨Z, hZ, F, hF, r', hr', hFZ, hFmin⟩ := classify_face (V := V) (v := v) (a := a)
    (c := c) (b := b) hk R hRinj hRV E.faceA_le E.inner_Na_v hvR htop hcR hbR hlow hY hY' hr0 hr
    hext
  have hZv : Z ≠ v := fun e => (hfoot F hF hFmin r' hr').1 (by rw [← e]; exact hFZ)
  have hZa : Z ≠ a := fun e => (hfoot F hF hFmin r' hr').2 (by rw [← e]; exact hFZ)
  rcases lt_trichotomy ⟪Na, c⟫ ⟪Na, b⟫ with hcb | hcb | hcb
  · have hFc : F = c := by
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hF
      rw [min_eq_left hcb.le] at hFmin
      simp only [inner_add_right, real_inner_smul_right] at hFmin
      have hβ0 : β = 0 := by
        rw [show α = 1 - β by linarith] at hFmin
        by_contra hβ0
        have : β * (⟪Na, b⟫ - ⟪Na, c⟫) = 0 := by linarith
        exact hβ0 ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hcb.ne'))
      rw [hβ0, show α = 1 by linarith]; simp
    exact E.isRupert_classC hMa hopp hdist hz hone hZ hZv hZa (Or.inl ⟨hFc, hcb⟩) hFZ hdir hℓa
  · exact E.isRupert_classD hMa hopp hdist hz hone hZ hZv hZa hF hcb hFZ hdir hℓa (hE hcb)
  · have hFb : F = b := by
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hF
      rw [min_eq_right hcb.le] at hFmin
      simp only [inner_add_right, real_inner_smul_right] at hFmin
      have hα0 : α = 0 := by
        rw [show β = 1 - α by linarith] at hFmin
        by_contra hα0
        have : α * (⟪Na, c⟫ - ⟪Na, b⟫) = 0 := by linarith
        exact hα0 ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hcb.ne'))
      rw [hα0, show β = 1 by linarith]; simp
    exact E.isRupert_classC hMa hopp hdist hz hone hZ hZv hZa (Or.inr ⟨hFb, hcb⟩) hFZ hdir hℓa

/-- A failed `NoPersistHDN`: a rim double normal in space normal to the circle's plane. -/
theorem exists_of_not_noPersist {k : ℕ} {R : ZMod k → ℝ³} {u e : ℝ³}
    (hbad : ¬ NoPersistHDN R u e) :
    ∃ i j : ZMod k, ∃ Y ∈ segment ℝ (R i) (R (i + 1)), ∃ Y' ∈ segment ℝ (R j) (R (j + 1)),
      Y' ≠ Y ∧ ⟪Y' - Y, u⟫ = 0 ∧ ⟪Y' - Y, e⟫ = 0 ∧
      ∀ m, ⟪Y' - Y, R m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', R m - Y⟫ ≤ 0 := by
  by_contra hc
  push Not at hc
  exact hbad fun i j Y hY Y' hY' hne hu he hall => by
    obtain ⟨k, hk⟩ := hc i j Y hY Y' hY' hne hu he
    exact absurd (hall k).2 (not_le.mpr (hk (hall k).1))

theorem inner_chord_of_slide {X : ℝ³} {h : ℝ} (hh : h ≠ 0) {p q : ℝ³}
    (he : ⟪X, h • (p - q)⟫ = 0) : ⟪X, q - p⟫ = 0 := by
  rw [real_inner_smul_right] at he
  have := (mul_eq_zero.mp he).resolve_left hh
  rw [show q - p = -(p - q) by abel, inner_neg_right, this, neg_zero]

/-- **One realizing circle** (`F_a`'s): `F_a`'s single middle on the far side of its chord, the
middles of `F_b` on `w`'s side.  Lemma 22.3 (the slide of `K_v`), and for a persistent double
normal Lemma 22.4 (class `c`) or Theorem 22.8 (class `d`, with Lemma E). -/
theorem isRupert_caseB (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m) (hRB : RealB v w b Mb)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfoot : FootA v a c b Na)
    (hE : ⟪Na, c⟫ = ⟪Na, b⟫ → det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0) :
    IsRupert V := by
  classical
  have hinj : Function.Injective (fun i => ⟪quad v a c b i, u⟫) := by
    intro i j hij
    by_contra hne
    exact hdist _ (E.quad_mem i) _ (E.quad_mem j) (E.quad_injective.ne hne) hij
  by_cases hbad : NoPersistHDN (quad v a c b) u (h • (v - a))
  · exact E.isRupert_slideA hRB hinj hz hbad
  obtain ⟨i, j, Y, hY, Y', hY', hne, hu, he, hext⟩ := exists_of_not_noPersist hbad
  have hcN : ⟪Na, c⟫ < κa := E.Na_lt E.hc E.hcA.1 E.hcA.2.1 E.hcA.2.2.1 E.hcA.2.2.2
  have hbN : ⟪Na, b⟫ < κa := E.Na_lt E.hb E.hbA.1 E.hbA.2.1 E.hbA.2.2.1 E.hbA.2.2.2
  refine E.isRupert_persistA hMa hopp hz hdist hone hfoot hE (by norm_num) (quad v a c b)
    E.quad_injective E.quad_mem E.supp ⟨0, rfl⟩ ?_ ⟨2, rfl⟩ ⟨3, rfl⟩ ?_ hY hY' hne hu
    (inner_chord_of_slide E.hh he) hext
  · intro k hk
    rcases zmod4_cases k with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hk hcN.ne
    · exact absurd hk hbN.ne
  · intro k hkc hkb
    rcases zmod4_cases k with rfl | rfl | rfl | rfl
    · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, v⟫
      rw [E.inner_Na_v]; exact lt_of_le_of_lt (min_le_left _ _) hcN
    · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, a⟫
      rw [E.inner_Na_a]; exact lt_of_le_of_lt (min_le_left _ _) hcN
    · exact absurd rfl hkc
    · exact absurd rfl hkb

set_option maxHeartbeats 1000000 in
/-- **No circle** (both faces quadrilaterals, both middles on the far side of their chords).
`K_w` is realized on both circles (22.2); otherwise one of the two slide rims is strictly
unimodal (Lemma 22.7) and its slide works, or its persistent double normal is of class `c` or
`d` for its face. -/
theorem isRupert_caseC (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m m' : ℝ³}
    (hMa : Ma = {m}) (hMb : Mb = {m'}) (hoppA : OppA v w a m) (hoppB : OppA v w b m')
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfootA : FootA v a c b Na) (hfootB : FootA v b c a Nb)
    (hEa : ⟪Na, c⟫ = ⟪Na, b⟫ → det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0)
    (hEb : ⟪Nb, c⟫ = ⟪Nb, a⟫ → det3 (c - b) (a - b) (v - b) * det3 (c - b) (a - b) (w - b) < 0) :
    IsRupert V := by
  classical
  have hm : m ∈ Ma := by rw [hMa]; exact mem_singleton_self m
  have hm' : m' ∈ Mb := by rw [hMb]; exact mem_singleton_self m'
  have E' := E.mirror
  have hdist' : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, -u⟫ ≠ ⟪y', -u⟫ := by
    intro y hy y' hy' hne e
    simp only [inner_neg_right, neg_inj] at e
    exact hdist y hy y' hy' hne e
  have hz' : NWS4 (quad ⟪v, -u⟫ ⟪b, -u⟫ ⟪c, -u⟫ ⟪a, -u⟫) := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, inner_neg_right, neg_lt_neg_iff] at hz ⊢
    obtain ⟨h1, h2⟩ := hz
    refine ⟨?_, ?_⟩
    · rcases h2 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
    · rcases h1 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
  have hone' := hone.neg_u
  have hh := E.hh
  have hcN : ⟪Na, c⟫ < κa := E.Na_lt E.hc E.hcA.1 E.hcA.2.1 E.hcA.2.2.1 E.hcA.2.2.2
  have hbN : ⟪Na, b⟫ < κa := E.Na_lt E.hb E.hbA.1 E.hbA.2.1 E.hbA.2.2.1 E.hbA.2.2.2
  have hcNb : ⟪Nb, c⟫ < κb := E.Nb_lt E.hc E.hcA.1 E.hcA.2.1 E.hcB.1 E.hcB.2
  have haNb : ⟪Nb, a⟫ < κb := E.Nb_lt E.ha E.haB.1 E.haB.2.1 (fun e => E.hbA.2.2.1 e.symm)
    E.haB.2.2
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hoppA
  obtain ⟨s', δ', hs0', hs1', hδh', hmeq'⟩ := E'.opp_coords hm' hoppB
  -- the partner `K_w` is realized on both circles
  by_cases hKw : NWS4 (quad ⟪w, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)
  · have hw := E.hw
    refine E.swap.isRupert_twoCircle ?_ ?_ ?_
    · intro x hx
      rw [hMa, mem_singleton] at hx
      subst hx
      refine ⟨(h * (1 - s) - δ) / h, ?_, ?_⟩
      · have e : (h * (1 - s) - δ) / h = (1 - s) + (-δ * h) / (h * h) := by field_simp; ring
        rw [e]
        have : 0 < (-δ * h) / (h * h) := div_pos (by linarith) (mul_self_pos.mpr hh)
        linarith
      · rw [hmeq, hw]
        have e1 : cross (a - (v + h • u)) (v + s • (a - v) + δ • u - (v + h • u)) =
            (δ - h * (1 - s)) • cross (a - v) u := by
          ext j; fin_cases j <;> simp [cross] <;> ring
        have e2 : cross (a - (v + h • u)) (v - (v + h • u)) = (-h) • cross (a - v) u := by
          ext j; fin_cases j <;> simp [cross] <;> ring
        rw [e1, e2, smul_smul]
        congr 1
        field_simp
        ring
    · intro x hx
      rw [hMb, mem_singleton] at hx
      subst hx
      refine ⟨(h * (1 - s') + δ') / h, ?_, ?_⟩
      · have e : (h * (1 - s') + δ') / h = (1 - s') + (δ' * h) / (h * h) := by
          field_simp
        rw [e]
        have hp : 0 < δ' * h := by nlinarith
        have : 0 < (δ' * h) / (h * h) := div_pos hp (mul_self_pos.mpr hh)
        linarith
      · rw [hmeq', hw]
        have e1 : cross (v + h • u - b) (v + s' • (b - v) + δ' • -u - b) =
            (-δ' - h * (1 - s')) • cross (v - b) u := by
          ext j; fin_cases j <;> simp [cross] <;> ring
        have e2 : cross (v + h • u - b) (v - b) = (-h) • cross (v - b) u := by
          ext j; fin_cases j <;> simp [cross] <;> ring
        rw [e1, e2, smul_smul]
        congr 1
        field_simp
        ring
    · have hinj : Function.Injective (fun i => ⟪quad w a c b i, u⟫) := by
        intro i j hij
        by_contra hne
        exact hdist _ (E.swap.quad_mem i) _ (E.swap.quad_mem j)
          (E.swap.quad_injective.ne hne) hij
      rw [quad_inner'] at hinj ⊢
      exact (isCyclicUnimodal_of_NWS4 hinj hKw).isRobustUnimodal
  -- one of the slide rims is strictly unimodal
  have hKw' : ¬ NWS4 (quad ⟪w, -u⟫ ⟪b, -u⟫ ⟪c, -u⟫ ⟪a, -u⟫) := by
    intro hc; apply hKw
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, inner_neg_right, neg_lt_neg_iff] at hc ⊢
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, ?_⟩
    · rcases h2 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
    · rcases h1 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
  have suppB : ∀ z ∈ V, SuppIn (-u) (quint v m a c b) z := by
    intro z hz ℓ hℓ
    rw [inner_neg_right, neg_eq_zero] at hℓ
    exact suppIn_quint (E.supp z hz) ℓ hℓ
  have suppA : ∀ z ∈ V, SuppIn u (quint v m' b c a) z := by
    intro z hz ℓ hℓ
    obtain ⟨i, hi⟩ := E.supp z hz ℓ hℓ
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [⟨0, hi⟩, ⟨4, hi⟩, ⟨3, hi⟩, ⟨2, hi⟩]
  by_cases hXb : StrictUnimodal (fun i => ⟪quint v m a c b i, u⟫)
  · by_cases hbad : NoPersistHDN (quint v m a c b) u (h • (v - b))
    · exact E.isRupert_slide5 hMa hoppA (E.quint_inj_of_dist hm hdist) (Or.inl hXb) hbad
    obtain ⟨i, j, Y, hY, Y', hY', hne, hu, he, hext⟩ := exists_of_not_noPersist hbad
    have hinjR : Function.Injective (quint v m a c b) := fun i j e =>
      E.quint_inj_of_dist hm hdist (by simp only [e])
    refine E'.isRupert_persistA hMb hoppB hz' hdist' hone' hfootB hEb (by norm_num)
      (quint v m a c b) hinjR (E.quint_mem hm) suppB ⟨0, rfl⟩ ?_ ⟨3, rfl⟩ ⟨2, rfl⟩ ?_ hY hY'
      hne (by rw [inner_neg_right, hu, neg_zero]) (inner_chord_of_slide hh he) hext
    · intro k hk
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exfalso
        have hmB : m ∉ Mb := E.midA_not_midB hm
        have := E.Nb_lt (E.hMa hm) (E.hMa' m hm).1 (E.hMa' m hm).2.1
          (fun e => E.hbA.2.2.2 (e ▸ hm)) hmB
        exact absurd hk this.ne
      · exact absurd hk haNb.ne
      · exact absurd hk hcNb.ne
      · exact Or.inr rfl
    · intro k hkc hka
      have hmNb : ⟪Nb, m⟫ = (1 - s) * κb + s * ⟪Nb, a⟫ := by
        rw [hmeq]; simp only [inner_add_right, inner_sub_right, real_inner_smul_right, E.Nb_u,
          E.inner_Nb_v]; ring
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      · show min ⟪Nb, c⟫ ⟪Nb, a⟫ < ⟪Nb, v⟫
        rw [E.inner_Nb_v]; exact lt_of_le_of_lt (min_le_left _ _) hcNb
      · show min ⟪Nb, c⟫ ⟪Nb, a⟫ < ⟪Nb, m⟫
        rw [hmNb]
        have : ⟪Nb, a⟫ < (1 - s) * κb + s * ⟪Nb, a⟫ := by nlinarith
        exact lt_of_le_of_lt (min_le_right _ _) this
      · exact absurd rfl hka
      · exact absurd rfl hkc
      · show min ⟪Nb, c⟫ ⟪Nb, a⟫ < ⟪Nb, b⟫
        rw [E.inner_Nb_b]; exact lt_of_le_of_lt (min_le_left _ _) hcNb
  by_cases hXa : StrictUnimodal (fun i => ⟪quint v m' b c a i, -u⟫)
  · by_cases hbad : NoPersistHDN (quint v m' b c a) (-u) ((-h) • (v - a))
    · exact E'.isRupert_slide5 hMb hoppB (E'.quint_inj_of_dist hm' hdist') (Or.inl hXa) hbad
    obtain ⟨i, j, Y, hY, Y', hY', hne, hu, he, hext⟩ := exists_of_not_noPersist hbad
    have hinjR : Function.Injective (quint v m' b c a) := fun i j e =>
      E'.quint_inj_of_dist hm' hdist' (by simp only [e])
    refine E.isRupert_persistA hMa hoppA hz hdist hone hfootA hEa (by norm_num)
      (quint v m' b c a) hinjR (E'.quint_mem hm') suppA ⟨0, rfl⟩ ?_ ⟨3, rfl⟩ ⟨2, rfl⟩ ?_ hY hY'
      hne (by rw [inner_neg_right, neg_eq_zero] at hu; exact hu)
      (inner_chord_of_slide (neg_ne_zero.mpr hh) he) hext
    · intro k hk
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exfalso
        have hmA : m' ∉ Ma := E'.midA_not_midB hm'
        have := E.Na_lt (E.hMb hm') (E.hMb' m' hm').1 (E.hMb' m' hm').2.1
          (fun e => E.haB.2.2 (e ▸ hm')) hmA
        exact absurd hk this.ne
      · exact absurd hk hbN.ne
      · exact absurd hk hcN.ne
      · exact Or.inr rfl
    · intro k hkc hkb
      have hmNa : ⟪Na, m'⟫ = (1 - s') * κa + s' * ⟪Na, b⟫ := by
        rw [hmeq']; simp only [inner_add_right, inner_sub_right, real_inner_smul_right,
          inner_neg_right, E.Na_u, E.inner_Na_v]; ring
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, v⟫
        rw [E.inner_Na_v]; exact lt_of_le_of_lt (min_le_left _ _) hcN
      · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, m'⟫
        rw [hmNa]
        have : ⟪Na, b⟫ < (1 - s') * κa + s' * ⟪Na, b⟫ := by nlinarith
        exact lt_of_le_of_lt (min_le_right _ _) this
      · exact absurd rfl hkb
      · exact absurd rfl hkc
      · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, a⟫
        rw [E.inner_Na_a]; exact lt_of_le_of_lt (min_le_left _ _) hcN
  -- Lemma 22.7: both slide rims two-peaked is impossible
  exfalso
  have k1 := E.h1_of_config hm hoppA hdist hz hKw hXb
  have k2 := E'.h1_of_config hm' hoppB hdist' hz' hKw' hXa
  linarith [k1.2.1, k2.2.2.1]

/-- The mirror of `RealA` is the mirror's `RealB`. -/
theorem realB_mirror {v w a : ℝ³} {Ma : Finset ℝ³} (h : RealA v w a Ma) : RealB v w a Ma := by
  intro m hm
  obtain ⟨k, hk, hk'⟩ := h m hm
  refine ⟨k, hk, ?_⟩
  have e1 : cross (v - a) (m - a) = -cross (a - v) (m - v) := by
    ext j; fin_cases j <;> simp [cross] <;> ring
  have e2 : cross (v - a) (w - a) = -cross (a - v) (w - v) := by
    ext j; fin_cases j <;> simp [cross] <;> ring
  rw [e1, e2, hk', smul_neg]

/-- **The horizontal-double-normal item of a four-corner edge closing** (§22): with at most one
middle per face, a robustly unimodal `K_v` makes the set Rupert under §22.4's conditions:
distinct depths at `u`, at most one direction of horizontal double normals, no double normal
perpendicular to a face from an end of its side (`FootA` for both faces), and Lemma E strict
where a far edge is parallel to a face (`hEa`, `hEb`).  (With two realizing circles no
condition is used.) -/
theorem isRupert_edgeClosing (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb)
    (hMa1 : ∀ m ∈ Ma, ∀ m' ∈ Ma, m = m') (hMb1 : ∀ m ∈ Mb, ∀ m' ∈ Mb, m = m')
    (hrob : IsRobustUnimodal (fun i => ⟪quad v a c b i, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfootA : FootA v a c b Na) (hfootB : FootA v b c a Nb)
    (hEa : ⟪Na, c⟫ = ⟪Na, b⟫ → det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0)
    (hEb : ⟪Nb, c⟫ = ⟪Nb, a⟫ → det3 (c - b) (a - b) (v - b) * det3 (c - b) (a - b) (w - b) < 0) :
    IsRupert V := by
  classical
  have hinj : Function.Injective (fun i => ⟪quad v a c b i, u⟫) := by
    intro i j hij
    by_contra hne
    exact hdist _ (E.quad_mem i) _ (E.quad_mem j) (E.quad_injective.ne hne) hij
  have hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫) := by
    rw [quad_inner'] at hinj hrob
    have hc := hrob.isCyclicUnimodal_of_order (by norm_num) (fun i j h => h) hinj
    unfold NWS4
    set z := quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫ with hzdef
    have two : ∀ i j : ZMod 4, i ≠ j → (z (i - 1) < z i ∧ z (i + 1) < z i) →
        (z (j - 1) < z j ∧ z (j + 1) < z j) → False := by
      intro i j hij hi hj
      exact hij (Finset.card_le_one.mp hc.2.le i
        (by simp only [mem_filter, mem_univ, true_and]; exact hi)
        j (by simp only [mem_filter, mem_univ, true_and]; exact hj))
    have z0 : z 0 = ⟪v, u⟫ := rfl
    have z1 : z 1 = ⟪a, u⟫ := rfl
    have z2 : z 2 = ⟪c, u⟫ := rfl
    have z3 : z 3 = ⟪b, u⟫ := rfl
    have m0 : (0 : ZMod 4) - 1 = 3 := by decide
    have m1 : (1 : ZMod 4) - 1 = 0 := by decide
    have m2 : (2 : ZMod 4) - 1 = 1 := by decide
    have m3 : (3 : ZMod 4) - 1 = 2 := by decide
    have p0 : (0 : ZMod 4) + 1 = 1 := by decide
    have p1 : (1 : ZMod 4) + 1 = 2 := by decide
    have p2 : (2 : ZMod 4) + 1 = 3 := by decide
    have p3 : (3 : ZMod 4) + 1 = 0 := by decide
    have d01 : z 0 ≠ z 1 := fun e => absurd (hinj e) (by decide)
    have d03 : z 0 ≠ z 3 := fun e => absurd (hinj e) (by decide)
    have d21 : z 2 ≠ z 1 := fun e => absurd (hinj e) (by decide)
    have d23 : z 2 ≠ z 3 := fun e => absurd (hinj e) (by decide)
    constructor
    · by_contra hc'
      push Not at hc'
      apply two 0 2 (by decide)
      · rw [m0, p0]
        exact ⟨lt_of_le_of_ne hc'.2.1 (fun e => d03 e.symm),
          lt_of_le_of_ne hc'.1 (fun e => d01 e.symm)⟩
      · rw [m2, p2]
        exact ⟨lt_of_le_of_ne hc'.2.2.1 (fun e => d21 e.symm),
          lt_of_le_of_ne hc'.2.2.2 (fun e => d23 e.symm)⟩
    · by_contra hc'
      push Not at hc'
      apply two 1 3 (by decide)
      · rw [m1, p1]
        exact ⟨lt_of_le_of_ne hc'.1 d01, lt_of_le_of_ne hc'.2.2.1 d21⟩
      · rw [m3, p3]
        exact ⟨lt_of_le_of_ne hc'.2.2.2 d23, lt_of_le_of_ne hc'.2.1 d03⟩
  have hdist' : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, -u⟫ ≠ ⟪y', -u⟫ := by
    intro y hy y' hy' hne e
    simp only [inner_neg_right, neg_inj] at e
    exact hdist y hy y' hy' hne e
  have hz' : NWS4 (quad ⟪v, -u⟫ ⟪b, -u⟫ ⟪c, -u⟫ ⟪a, -u⟫) := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, inner_neg_right, neg_lt_neg_iff] at hz ⊢
    obtain ⟨h1, h2⟩ := hz
    refine ⟨?_, ?_⟩
    · rcases h2 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
    · rcases h1 with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
  -- the middles on the far side
  have oppA : ¬ RealA v w a Ma → ∃ m, Ma = {m} ∧ OppA v w a m := by
    intro hRA
    simp only [RealA, not_forall] at hRA
    obtain ⟨m, hm, hno⟩ := hRA
    refine ⟨m, ?_, ?_⟩
    · ext x; simp only [mem_singleton]
      exact ⟨fun hx => hMa1 x hx m hm, fun hx => hx ▸ hm⟩
    · rcases E.midA_side hm with h1 | h1
      · exact absurd h1 hno
      · exact h1
  have oppB : ¬ RealB v w b Mb → ∃ m, Mb = {m} ∧ OppA v w b m := by
    intro hRB
    simp only [RealB, not_forall] at hRB
    obtain ⟨m, hm, hno⟩ := hRB
    refine ⟨m, ?_, ?_⟩
    · ext x; simp only [mem_singleton]
      exact ⟨fun hx => hMb1 x hx m hm, fun hx => hx ▸ hm⟩
    · rcases E.midB_side hm with h1 | h1
      · exact absurd h1 hno
      · exact h1
  by_cases hRA : RealA v w a Ma
  · by_cases hRB : RealB v w b Mb
    · exact E.isRupert_twoCircle hRA hRB hrob
    · obtain ⟨m, hMb, hopp⟩ := oppB hRB
      exact E.mirror.isRupert_caseB hMb hopp (realB_mirror hRA) hz' hdist' hone.neg_u hfootB hEb
  · obtain ⟨m, hMa, hopp⟩ := oppA hRA
    by_cases hRB : RealB v w b Mb
    · exact E.isRupert_caseB hMa hopp hRB hz hdist hone hfootA hEa
    · obtain ⟨m', hMb, hopp'⟩ := oppB hRB
      exact E.isRupert_caseC hMa hMb hopp hopp' hz hdist hone hfootA hfootB hEa hEb

end EdgeConf

end Minimality

end
