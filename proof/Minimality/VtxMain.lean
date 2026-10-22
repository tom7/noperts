module

public import Minimality.VtxClassD
public import Minimality.EdgeMain

@[expose] public section

/-!
# The horizontal-double-normal item of a vertex closing (`FEWER-FACES-PROOFS.md` §22)

`VtxConf.isRupert_vtxClosing`: in a `VtxConf` (a vertex view with the quadrilateral `F_a`, its
apex and far end opposite, and the triangle `F_b`), a robustly unimodal closing makes the set
Rupert under §22.4's conditions: distinct depths at `u`, at most one direction of horizontal
double normals (`OneHDNDir`), no double normal perpendicular to `F_a` from an end of its side
(`FootA`), and, where the far edge is parallel to `F_a`, (H4) or the coplanarity of Lemma 22.10
in each sense.  The closing is realized on `F_a`'s circle (Lemma 22.3); a persistent double
normal is of class `c` (Lemma 22.4) or `d` (Lemmas 22.9, 22.10, Theorem 22.8).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem quint_inner' (p₀ p₁ p₂ p₃ p₄ u : ℝ³) :
    (fun i => ⟪quint p₀ p₁ p₂ p₃ p₄ i, u⟫) = quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A unimodal 4-cycle has no weak saddle. -/
theorem nws4_of_cyclic {z : ZMod 4 → ℝ} (hc : IsCyclicUnimodal z) : NWS4 z := by
  classical
  unfold NWS4
  have hinj := hc.1
  have two : ∀ i j : ZMod 4, i ≠ j → (z (i - 1) < z i ∧ z (i + 1) < z i) →
      (z (j - 1) < z j ∧ z (j + 1) < z j) → False := by
    intro i j hij hi hj
    exact hij (Finset.card_le_one.mp hc.2.le i
      (by simp only [mem_filter, mem_univ, true_and]; exact hi)
      j (by simp only [mem_filter, mem_univ, true_and]; exact hj))
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

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- (H4) of Theorem 22.8 at the vertex view in the sense `ε u`, or the coplanarity of Lemma 22.10
for the middle `m` shown in that sense. -/
def H4orCopl (u v a c b m : ℝ³) (ε : ℝ) : Prop :=
  0 < det3 (c - a) (b - a) (v - a) * (ε * det3 (c - a) (b - a) u) ∨
    det3 (a - m) (c - m) (b - m) = 0

/-- (H4) or Lemma 22.10's coplanarity for the middle `m` shown in the sense `ε u`, or the
residual pattern of Lemma 22.9 for `m` is impossible (as for type 21's `V` with the middle `6`,
Lemma 22.14: there `V′` closes instead). -/
def H4orEsc (u v a c b m : ℝ³) (ε : ℝ) : Prop :=
  H4orCopl u v a c b m ε ∨
    ¬ (ε * ⟪v, u⟫ < ε * ⟪m, u⟫ ∧ ε * ⟪v, u⟫ < ε * ⟪b, u⟫ ∧ ε * ⟪a, u⟫ < ε * ⟪v, u⟫ ∧
      ε * ⟪c, u⟫ < ε * ⟪v, u⟫)

/-- **(H4) from the other middle in the plane `a c b`** (type 16's `T_a`: `3` on the facet
`1356 ∋ 5, 1, 6`): if the lower middle `q` lies in the plane of `a, c, b`, then (H4) holds in the
sense of `u` (where `p` shows).  Along the chord, `Π(q) = (1 − s) Π(v) + δ Π'(u)` for the plane's
functional `Π`, and `Π'(u) = det3 (c − a) (b − a) u > 0` (the rim is convex). -/
theorem h4_of_coplQ (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (h : det3 (a - q) (c - q) (b - q) = 0) : H4orCopl u v a c b p 1 := by
  left
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, -⟩ := E.ne7
  obtain ⟨s, δ, hs0, hs1, hδ, hqeq⟩ := E.q_coords
  have hDu := E.det_ac_pos E.hb hab.symm (Ne.symm (E.ne7.2.2.2.2.2.2.2.2.2.2.2.1))
  have key : (1 - s) * det3 (c - a) (b - a) (v - a) + δ * det3 (c - a) (b - a) u = 0 := by
    have e : det3 (a - q) (c - q) (b - q) =
        -((1 - s) * det3 (c - a) (b - a) (v - a) + δ * det3 (c - a) (b - a) u) := by
      rw [hqeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    linarith [e, h]
  have hs : 0 < 1 - s := by linarith
  have hDv : det3 (c - a) (b - a) (v - a) = -δ * det3 (c - a) (b - a) u / (1 - s) := by
    field_simp; linarith
  rw [hDv, one_mul]
  have : -δ * det3 (c - a) (b - a) u / (1 - s) * det3 (c - a) (b - a) u =
      (-δ) * (det3 (c - a) (b - a) u * det3 (c - a) (b - a) u) / (1 - s) := by ring
  rw [this]
  exact div_pos (mul_pos (neg_pos.mpr hδ) (mul_self_pos.mpr hDu.ne')) hs

/-- As `h4_of_coplQ` with the upper middle `p` in the plane `a c b`: (H4) in the sense `−u`. -/
theorem h4_of_coplP (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (h : det3 (a - p) (c - p) (b - p) = 0) : H4orCopl u v a c b q (-1) := by
  left
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, -⟩ := E.ne7
  obtain ⟨s, δ, hs0, hs1, hδ, hpeq⟩ := E.p_coords
  have hDu := E.det_ac_pos E.hb hab.symm (Ne.symm (E.ne7.2.2.2.2.2.2.2.2.2.2.2.1))
  have key : (1 - s) * det3 (c - a) (b - a) (v - a) + δ * det3 (c - a) (b - a) u = 0 := by
    have e : det3 (a - p) (c - p) (b - p) =
        -((1 - s) * det3 (c - a) (b - a) (v - a) + δ * det3 (c - a) (b - a) u) := by
      rw [hpeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    linarith [e, h]
  have hs : 0 < 1 - s := by linarith
  have hDv : det3 (c - a) (b - a) (v - a) = -δ * det3 (c - a) (b - a) u / (1 - s) := by
    field_simp; linarith
  rw [hDv]
  have : -δ * det3 (c - a) (b - a) u / (1 - s) * (-1 * det3 (c - a) (b - a) u) =
      δ * (det3 (c - a) (b - a) u * det3 (c - a) (b - a) u) / (1 - s) := by ring
  rw [this]
  exact div_pos (mul_pos hδ (mul_self_pos.mpr hDu.ne')) hs

/-- **One middle of `F_a` in the plane `a c b`** gives (H4) or Lemma 22.10's coplanarity in both
senses. -/
theorem hD_of_copl (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (h : det3 (a - p) (c - p) (b - p) = 0 ∨ det3 (a - q) (c - q) (b - q) = 0) :
    H4orCopl u v a c b p 1 ∧ H4orCopl u v a c b q (-1) := by
  rcases h with h | h
  · exact ⟨Or.inr h, E.h4_of_coplP h⟩
  · exact ⟨E.h4_of_coplQ h, Or.inr h⟩

/-- **Class `d` at a vertex view.** -/
theorem isRupert_classD (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) (hone : OneHDNDir V u)
    {Z F : ℝ³} (hZ : Z ∈ segment ℝ v a) (hZv : Z ≠ v) (hZa : Z ≠ a) (hF : F ∈ segment ℝ c b)
    (hpar : ⟪Na, c⟫ = ⟪Na, b⟫) {r : ℝ} (hFZ : F - Z = r • Na) {ℓ₀ : ℝ³}
    (hdir : HDNDir V u ℓ₀) (hℓa : cross ℓ₀ Na = 0)
    (hDp : H4orEsc u v a c b p 1) (hDq : H4orEsc u v a c b q (-1)) : IsRupert V := by
  classical
  obtain ⟨sp, δp, hsp0, hsp1, hδp, hpeq⟩ := E.p_coords
  obtain ⟨sq, δq, hsq0, hsq1, hδq, hqeq⟩ := E.q_coords
  have hinjp := E.quint_inj_of_dist (Or.inl rfl) hdist
  have hinjq := E.quint_inj_of_dist (Or.inr rfl) hdist
  have hbad : ∀ m, m ∈ V → NoPersistHDN (quint v m a c b) u (b - v) := fun m hm =>
    noPersist_of_one _ (E.quint_mem hm) (fun z hz => suppIn_quint (E.supp z hz)) hone
      hdir (N := Na) hℓa E.Na_bv.ne
  by_cases h5p : StrictUnimodal (fun i => ⟪quint v p a c b i, u⟫)
  · exact E.isRupert_slide5 (Or.inl ⟨rfl, rfl⟩) hsp0 hsp1 hsq0 hsq1 hpeq hqeq (lam := 1)
      (by linarith) (by linarith) hinjp (Or.inl h5p) (hbad p E.hp)
  by_cases h5q : StrictUnimodal (fun i => ⟪quint v q a c b i, u⟫)
  · exact E.isRupert_slide5 (Or.inr ⟨rfl, rfl⟩) hsq0 hsq1 hsp0 hsp1 hqeq hpeq (lam := -1)
      (by linarith) (by linarith) hinjq (Or.inl h5q) (hbad q E.hq)
  -- the residual: Lemma 22.9
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr E.hu
  have cp : ⟪p, u⟫ = ⟪v, u⟫ + sp * (⟪a, u⟫ - ⟪v, u⟫) + δp * ⟪u, u⟫ := by
    rw [hpeq]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have cq : ⟪q, u⟫ = ⟪v, u⟫ + sq * (⟪a, u⟫ - ⟪v, u⟫) + δq * ⟪u, u⟫ := by
    rw [hqeq]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [quint_inner'] at hinjp hinjq h5p h5q
  have hH := h1_vtx hsp0 hsp1 hsq0 hsq1 (by rw [cp]; nlinarith [mul_pos hδp huu])
    (by rw [cq]; nlinarith [mul_neg_of_neg_of_pos hδq huu]) hz hinjp hinjq h5p h5q
  -- the foot of the double normal
  have hfeet : ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
      ⟪v + lam • (a - v) - (b + mu • (c - b)), u⟫ = 0 ∧
      ⟪v + lam • (a - v) - (b + mu • (c - b)), a - v⟫ = 0 := by
    obtain ⟨p₁, p₂, hp₁, hp₂, hp₁₂, hZeq⟩ := hZ
    obtain ⟨q₁, q₂, hq₁, hq₂, hq₁₂, hFeq⟩ := hF
    have hp₂0 : 0 < p₂ := by
      rcases hp₂.eq_or_lt with h0 | h0
      · exfalso; apply hZv; rw [← hZeq, ← h0, show p₁ = 1 by linarith]; simp
      · exact h0
    have hp₂1 : p₂ < 1 := by
      rcases hp₁.eq_or_lt with h0 | h0
      · exfalso; apply hZa; rw [← hZeq, ← h0, show p₂ = 1 by linarith]; simp
      · linarith
    have hdiff : v + p₂ • (a - v) - (b + q₁ • (c - b)) = -(r • Na) := by
      rw [← hFZ, ← hZeq, ← hFeq, show p₁ = 1 - p₂ by linarith,
        show q₂ = 1 - q₁ by linarith]
      module
    refine ⟨p₂, q₁, hp₂0, hp₂1, ?_, ?_⟩
    · rw [hdiff, inner_neg_left, real_inner_smul_left, E.Na_u]; ring
    · rw [hdiff, inner_neg_left, real_inner_smul_left, E.Na_av]; ring
  rcases hH with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
  · -- (H1) for `p` along `u`
    replace hDp : H4orCopl u v a c b p 1 := hDp.resolve_right fun h => h
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    obtain ⟨L', hL', hsg, hR⟩ := E.rdRimG_vtx hsp0 hsp1 hpeq one_ne_zero (by linarith) hpar
      ⟨by linarith, by linarith, by linarith, by linarith⟩ hfeet hDp
    have hL'0 : 0 < L' := hsg.mpr one_pos
    exact E.isRupert_rdUp (Or.inl ⟨rfl, rfl⟩) hsp0 hsp1 hpeq hsq0 hqeq hL'
      (mul_neg_of_pos_of_neg hL'0 hδq) hR
  · -- (H1) for `q` along `−u`
    replace hDq : H4orCopl u v a c b q (-1) := hDq.resolve_right fun h => h
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    obtain ⟨L', hL', hsg, hR⟩ := E.rdRimG_vtx hsq0 hsq1 hqeq (by norm_num : (-1 : ℝ) ≠ 0)
      (by linarith) hpar ⟨by linarith, by linarith, by linarith, by linarith⟩ hfeet hDq
    have hL'0 : L' < 0 := by
      rcases lt_or_gt_of_ne hL' with h | h
      · exact h
      · exact absurd (hsg.mp h) (by norm_num)
    exact E.isRupert_rdUp (Or.inr ⟨rfl, rfl⟩) hsq0 hsq1 hqeq hsp0 hpeq hL'
      (mul_neg_of_neg_of_pos hL'0 hδp) hR

/-- **A persistent double normal perpendicular to `F_a`** (on `F_a`'s circle) is of class `c`
(Lemma 22.4) or `d` (Lemmas 22.9, 22.10); an end at `v` or `a` is excluded by `FootA`. -/
theorem isRupert_persistA (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfoot : FootA v a c b Na)
    (hD : ⟪Na, c⟫ = ⟪Na, b⟫ → H4orEsc u v a c b p 1 ∧ H4orEsc u v a c b q (-1))
    {i j : ZMod 4} {Y Y' : ℝ³} (hY : Y ∈ segment ℝ (quad v a c b i) (quad v a c b (i + 1)))
    (hY' : Y' ∈ segment ℝ (quad v a c b j) (quad v a c b (j + 1))) (hne : Y' ≠ Y)
    (hu : ⟪Y' - Y, u⟫ = 0) (hea : ⟪Y' - Y, a - v⟫ = 0)
    (hext : ∀ m, ⟪Y' - Y, quad v a c b m - Y'⟫ ≤ 0 ∧ ⟪Y - Y', quad v a c b m - Y⟫ ≤ 0) :
    IsRupert V := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, -⟩ := E.ne7
  obtain ⟨r, hr⟩ := E.eq_smul_Na hu hea
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [zero_smul] at hr; exact hne (sub_eq_zero.mp hr)
  have hdir := hdnDir_of_rim (quad v a c b) E.quad_mem E.supp hY hY' hne hu hext
  have hℓa : cross (Y' - Y) Na = 0 := by rw [hr, EdgeConf.cross_smul_left'', cross_self, smul_zero]
  have hcN : ⟪Na, c⟫ < κa := E.Na_lt E.hc hvc.symm hac.symm hcp hcq
  have hbN : ⟪Na, b⟫ < κa := E.Na_lt E.hb hvb.symm hab.symm hbp hbq
  have hle : ∀ z ∈ V, ⟪Na, z⟫ ≤ κa := E.faceA_le
  obtain ⟨Z, hZ, F, hF, r', hr', hFZ, hFmin⟩ := classify_face (V := V) (v := v) (a := a)
    (c := c) (b := b) (by norm_num) (quad v a c b) E.quad_injective E.quad_mem hle E.inner_Na_v
    ⟨0, rfl⟩ (by
      intro k hk
      rcases zmod4_cases k with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hk hcN.ne
      · exact absurd hk hbN.ne) ⟨2, rfl⟩ ⟨3, rfl⟩ (by
      intro k hkc hkb
      rcases zmod4_cases k with rfl | rfl | rfl | rfl
      · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, v⟫
        rw [E.inner_Na_v]; exact lt_of_le_of_lt (min_le_left _ _) hcN
      · show min ⟪Na, c⟫ ⟪Na, b⟫ < ⟪Na, a⟫
        rw [E.inner_Na_a]; exact lt_of_le_of_lt (min_le_left _ _) hcN
      · exact absurd rfl hkc
      · exact absurd rfl hkb) hY hY' hr0 hr hext
  have hZv : Z ≠ v := fun e => (hfoot F hF hFmin r' hr').1 (by rw [← e]; exact hFZ)
  have hZa : Z ≠ a := fun e => (hfoot F hF hFmin r' hr').2 (by rw [← e]; exact hFZ)
  rcases lt_trichotomy ⟪Na, c⟫ ⟪Na, b⟫ with hcb' | hcb' | hcb'
  · have hFc : F = c := seg_min_eq hF hFmin hcb'
    exact E.isRupert_classC hdist hz hone hZ hZv hZa (Or.inl ⟨hFc, hcb'⟩) hFZ hdir hℓa
  · obtain ⟨hDp, hDq⟩ := hD hcb'
    exact E.isRupert_classD hdist hz hone hZ hZv hZa hF hcb' hFZ hdir hℓa hDp hDq
  · have hFb : F = b := by
      rw [segment_symm] at hF
      exact seg_min_eq hF (by rw [min_comm]; exact hFmin) hcb'
    exact E.isRupert_classC hdist hz hone hZ hZv hZa (Or.inr ⟨hFb, hcb'⟩) hFZ hdir hℓa

/-- **The horizontal-double-normal item of a vertex closing** (§22): a robustly unimodal closing
`v a c b` at the vertex view (`VtxConf`) makes the set Rupert under the codimension-2 conditions:
distinct depths, at most one direction of horizontal double normals, no double normal
perpendicular to `F_a` from an end of its side, and (H4) or Lemma 22.10's coplanarity in both
senses where the far edge is parallel to `F_a` (or, for a middle, the impossibility of Lemma
22.9's residual pattern for it, `H4orEsc`). -/
theorem isRupert_vtxClosing (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (hrob : IsRobustUnimodal (fun i => ⟪quad v a c b i, u⟫))
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) (hone : OneHDNDir V u)
    (hfoot : FootA v a c b Na)
    (hD : ⟪Na, c⟫ = ⟪Na, b⟫ → H4orEsc u v a c b p 1 ∧ H4orEsc u v a c b q (-1)) :
    IsRupert V := by
  classical
  have hinj : Function.Injective (fun i => ⟪quad v a c b i, u⟫) := by
    intro i j hij
    by_contra hne
    exact hdist _ (E.quad_mem i) _ (E.quad_mem j) (E.quad_injective.ne hne) hij
  have hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫) := by
    rw [quad_inner'] at hinj hrob
    have hc := hrob.isCyclicUnimodal_of_order (by norm_num) (fun i j h => h) hinj
    exact nws4_of_cyclic hc
  by_cases hbad : NoPersistHDN (quad v a c b) u (a - v)
  · exact E.isRupert_slideA hinj hz hbad
  obtain ⟨i, j, Y, hY, Y', hY', hne, hu, he, hext⟩ := EdgeConf.exists_of_not_noPersist hbad
  exact E.isRupert_persistA hz hdist hone hfoot hD hY hY' hne hu he hext

end VtxConf

end Minimality

end
