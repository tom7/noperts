module

public import Minimality.EdgeFive

@[expose] public section

/-!
# Class `c` is never an exception (`FEWER-FACES-PROOFS.md` Lemma 22.4)

A horizontal double normal of class `c_a`: a far corner `F` (`c` or `b`) strictly farthest from
`F_a`, with `F − Z ∥ N_a` for a point `Z` of the open side `(v, a)`.  On `F_b`'s circle the
slide rim `v m a c b` (with `F_a`'s middle `m` poked out) has the depth-separated pair (the edge
of the chain `v m a` that crosses the depth of `F`, and `F`): the side and `F` are a parallel
pair of the unimodal rim `K_v`, so the corners on either side of `F` lie on either side of its
depth (Theorem 8.10 along the slide).  With at most one direction of horizontal double normals
at `u` (`OneHDNDir`), the slide rim has no persistent double normal on `F_b`'s circle.

* `noPersist_of_one`: a second double normal direction is excluded by `OneHDNDir`.
* `depthSepAt_quint`: the depth-separated pairs of a five-corner rim from explicit inequalities.
* `EdgeConf.isRupert_classC` (Lemma 22.4).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Only one double-normal direction**: if `ℓ₀ ∥ N` is a shadow double normal at `u` and
`⟪N, e⟫ ≠ 0`, no rim with `SuppIn` has a persistent double normal along the circle of `u`,
`e` (its direction would be normal to `u` and `e`, hence not parallel to `ℓ₀`). -/
theorem noPersist_of_one {V : Finset ℝ³} {u : ℝ³} {k : ℕ} (R : ZMod k → ℝ³)
    (hRV : ∀ i, R i ∈ V) (hsupp : ∀ z ∈ V, SuppIn u R z) (hone : OneHDNDir V u)
    {ℓ₀ N e : ℝ³} (hℓ₀ : HDNDir V u ℓ₀) (hpar : cross ℓ₀ N = 0) (hNe : ⟪N, e⟫ ≠ 0) :
    NoPersistHDN R u e := by
  intro i j Y hY Y' hY' hne hu he hext
  have hd := hdnDir_of_rim R hRV hsupp hY hY' hne hu hext
  have hc := hone ℓ₀ _ hℓ₀ hd
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Y' - Y = t • ℓ₀ := ⟨_, eq_smul_of_cross_eq_zero hℓ₀.1 hc⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℝ, N = t' • ℓ₀ := ⟨_, eq_smul_of_cross_eq_zero hℓ₀.1 hpar⟩
  have hℓe : ⟪ℓ₀, e⟫ ≠ 0 := by
    intro h0; apply hNe; rw [ht', real_inner_smul_left, h0, mul_zero]
  rw [ht, real_inner_smul_left] at he
  have : t = 0 := (mul_eq_zero.mp he).resolve_right hℓe
  apply hne
  rw [← sub_eq_zero, ht, this, zero_smul]

theorem suppIn_quint {u v m a c b z : ℝ³} (h : SuppIn u (quad v a c b) z) :
    SuppIn u (quint v m a c b) z := by
  intro ℓ hℓ
  obtain ⟨i, hi⟩ := h ℓ hℓ
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  exacts [⟨0, hi⟩, ⟨2, hi⟩, ⟨3, hi⟩, ⟨4, hi⟩]

theorem suppIn_quint' {u v m a c b z : ℝ³} (h : SuppIn u (quad v a c b) z) :
    SuppIn u (quint v a c b m) z := by
  intro ℓ hℓ
  obtain ⟨i, hi⟩ := h ℓ hℓ
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  exacts [⟨0, hi⟩, ⟨1, hi⟩, ⟨2, hi⟩, ⟨3, hi⟩]

/-- The depth part of a depth-separated pair of a five-corner rim, read off at explicit
positions: `c'` the vertex, the corners `c' + 1, …, a'` on one side of its depth, the others
on the other side. -/
theorem depthSep_part {x : ZMod 5 → ℝ³} {u : ℝ³} {a' c' : ZMod 5}
    (h : (∀ s : ℕ, 0 < s → s ≤ (a' - c').val → ⟪x c', u⟫ < ⟪x (c' + s), u⟫) ∧
      ∀ s : ℕ, (a' - c').val < s → s < 5 → ⟪x (c' + s), u⟫ < ⟪x c', u⟫) :
    ((∀ s : ℕ, 0 < s → s ≤ (a' - c').val → ⟪x c', u⟫ < ⟪x (c' + s), u⟫) ∧
      ∀ s : ℕ, (a' - c').val < s → s < 5 → ⟪x (c' + s), u⟫ < ⟪x c', u⟫) ∨
    ((∀ s : ℕ, 0 < s → s ≤ (a' - c').val → ⟪x (c' + s), u⟫ < ⟪x c', u⟫) ∧
      ∀ s : ℕ, (a' - c').val < s → s < 5 → ⟪x c', u⟫ < ⟪x (c' + s), u⟫) := Or.inl h

/-- **Depth-separated pairs of `v m a c b`** at the vertex `c'` (`3` or `4`) and the edge `a'`
(`0` or `1`), from the four or five depth comparisons. -/
theorem depthSepAt_quint {x : ZMod 5 → ℝ³} {u : ℝ³} {a' c' : ZMod 5}
    (hdet : ∀ j, j ≠ c' →
      det3 (x (a' + 1) - x a') (x j - x c') u * det3 (x (a' + 1) - x a') (x c' - x a') u < 0)
    (hz : (∀ j : ZMod 5, j ≠ c' → (j - c').val ≤ (a' - c').val → ⟪x c', u⟫ < ⟪x j, u⟫) ∧
        (∀ j : ZMod 5, j ≠ c' → (a' - c').val < (j - c').val → ⟪x j, u⟫ < ⟪x c', u⟫) ∨
      (∀ j : ZMod 5, j ≠ c' → (j - c').val ≤ (a' - c').val → ⟪x j, u⟫ < ⟪x c', u⟫) ∧
        (∀ j : ZMod 5, j ≠ c' → (a' - c').val < (j - c').val → ⟪x c', u⟫ < ⟪x j, u⟫)) :
    DepthSepAt x u a' c' := by
  refine ⟨hdet, ?_⟩
  have hval : ∀ s : ℕ, 0 < s → s < 5 → (c' + (s : ZMod 5)) ≠ c' ∧
      ((c' + (s : ZMod 5)) - c').val = s := by
    intro s hs0 hs5
    refine ⟨?_, ?_⟩
    · intro h0
      have : ((s : ℕ) : ZMod 5) = 0 := by linear_combination h0
      interval_cases s <;> exact absurd this (by decide)
    · rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hs5]
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨fun s hs0 hs => ?_, fun s hs hs5 => ?_⟩
    · obtain ⟨hne, hv⟩ := hval s hs0 (by
        have := ZMod.val_lt (a' - c'); omega)
      exact h1 _ hne (by rw [hv]; exact hs)
    · obtain ⟨hne, hv⟩ := hval s (by omega) hs5
      exact h2 _ hne (by rw [hv]; exact hs)
  · right
    refine ⟨fun s hs0 hs => ?_, fun s hs hs5 => ?_⟩
    · obtain ⟨hne, hv⟩ := hval s hs0 (by
        have := ZMod.val_lt (a' - c'); omega)
      exact h1 _ hne (by rw [hv]; exact hs)
    · obtain ⟨hne, hv⟩ := hval s (by omega) hs5
      exact h2 _ hne (by rw [hv]; exact hs)

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

theorem quint_inj_of_dist (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hm : m ∈ Ma) (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) :
    Function.Injective (fun i => ⟪quint v m a c b i, u⟫) := by
  intro i j hij
  by_contra hne
  have hmem := E.quint_mem hm
  have hinjq : Function.Injective (quint v m a c b) := by
    obtain ⟨hmv, hmw, hma⟩ := E.hMa' m hm
    have hcm : c ≠ m := fun e => E.hcA.2.2.2 (e ▸ hm)
    have hbm : b ≠ m := fun e => E.hbA.2.2.2 (e ▸ hm)
    have hav : a ≠ v := E.haB.1
    have hcv : c ≠ v := E.hcA.1
    have hbv : b ≠ v := E.hbA.1
    have hca : c ≠ a := E.hcA.2.2.1
    have hba : b ≠ a := E.hbA.2.2.1
    have hcb : c ≠ b := E.hcB.1
    intro i j hij
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at hij <;>
      first | rfl | (exfalso; simp_all)
  exact hdist _ (hmem i) _ (hmem j) (hinjq.ne hne) hij

/-- **Lemma 22.4 (class `c` is never an exception).**  Let `F_a` have the single middle `m` on
the far side of the chord (`OppA`), all depths at `u` distinct, `K_v` without a weak saddle, and
at most one direction of horizontal double normals at `u`.  A horizontal double normal
`F − Z ∥ N_a` from the open side `(v, a)` to a far corner `F` strictly farthest from `F_a` makes
the set Rupert (the slide rim `v m a c b` on `F_b`'s circle has a depth-separated pair). -/
theorem isRupert_classC (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m)
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) (hone : OneHDNDir V u)
    {Z F : ℝ³} (hZ : Z ∈ segment ℝ v a) (hZv : Z ≠ v) (hZa : Z ≠ a)
    (hF : (F = c ∧ ⟪Na, c⟫ < ⟪Na, b⟫) ∨ (F = b ∧ ⟪Na, b⟫ < ⟪Na, c⟫))
    {r : ℝ} (hFZ : F - Z = r • Na) {ℓ₀ : ℝ³} (hdir : HDNDir V u ℓ₀) (hℓa : cross ℓ₀ Na = 0) :
    IsRupert V := by
  classical
  have hm : m ∈ Ma := by rw [hMa]; exact mem_singleton_self m
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hopp
  have hinj := E.quint_inj_of_dist hm hdist
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  -- no persistent double normal on `F_b`'s circle
  have hbad : NoPersistHDN (quint v m a c b) u (h • (v - b)) := by
    refine noPersist_of_one _ (E.quint_mem hm) (fun z hz => suppIn_quint (E.supp z hz)) hone
      hdir (N := Na) hℓa ?_
    rw [real_inner_smul_right, show v - b = -(b - v) by abel, inner_neg_right]
    exact mul_ne_zero E.hh (neg_ne_zero.mpr E.Na_bv.ne)
  refine E.isRupert_slide5 hMa hopp hinj (Or.inr ?_) hbad
  -- the depths
  obtain ⟨p₁, p₂, hq₁, hq₂, hp₁₂, hZeq⟩ := hZ
  have hp₂0 : 0 < p₂ := by
    rcases hq₂.eq_or_lt with h0 | h0
    · exfalso; apply hZv; rw [← hZeq, ← h0, show p₁ = 1 by linarith]; simp
    · exact h0
  have hp₁0 : 0 < p₁ := by
    rcases hq₁.eq_or_lt with h0 | h0
    · exfalso; apply hZa; rw [← hZeq, ← h0, show p₂ = 1 by linarith]; simp
    · exact h0
  have hFu : ⟪F, u⟫ = p₁ * ⟪v, u⟫ + p₂ * ⟪a, u⟫ := by
    have h1 : ⟪F - Z, u⟫ = 0 := by rw [hFZ, real_inner_smul_left, E.Na_u]; ring
    rw [inner_sub_left, ← hZeq, inner_add_left, real_inner_smul_left,
      real_inner_smul_left] at h1
    linarith
  have hmu : ⟪m, u⟫ = ⟪v, u⟫ + s * (⟪a, u⟫ - ⟪v, u⟫) + δ * ⟪u, u⟫ := by
    rw [hmeq]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have hFV : F ∈ V := by
    rcases hF with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]; exact E.hc
    · rw [e]; exact E.hb
  have hmF : ⟪m, u⟫ ≠ ⟪F, u⟫ := by
    refine hdist m (E.hMa hm) F hFV ?_
    rintro rfl; rcases hF with ⟨e, -⟩ | ⟨e, -⟩
    · exact E.hcA.2.2.2 (e ▸ hm)
    · exact E.hbA.2.2.2 (e ▸ hm)
  have hva : ⟪v, u⟫ ≠ ⟪a, u⟫ := hdist v E.hv a E.ha E.haB.1.symm
  obtain ⟨hz1, hz2⟩ := hz
  simp only [quad_0, quad_1, quad_2, quad_3] at hz1 hz2
  have dcb : ⟪c, u⟫ ≠ ⟪b, u⟫ := hdist c E.hc b E.hb E.hcB.1
  -- the screen tests along the chain: multiples of the test along `v a`
  have hP : 0 < det3 (a - v) (F - v) u := by
    rcases hF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact E.det_a_pos E.hc E.hcA.1 E.hcA.2.1 E.hcA.2.2.1 E.hcA.2.2.2
    · exact E.det_a_pos E.hb E.hbA.1 E.hbA.2.1 E.hbA.2.2.1 E.hbA.2.2.2
  have hG : ∀ G, (G = c ∨ G = b) → G ≠ F → det3 (a - v) (G - v) u < det3 (a - v) (F - v) u := by
    intro G hG hGF
    have key1 := E.det_a_rel (G - v)
    have key2 := E.det_a_rel (F - v)
    have hlt : ⟪Na, F⟫ < ⟪Na, G⟫ := by
      rcases hF with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hG with rfl | rfl
      exacts [absurd rfl hGF, h1, h1, absurd rfl hGF]
    have hD := E.Na_bv
    have hdab := E.dab_pos
    have hdiff : (det3 (a - v) (G - v) u - det3 (a - v) (F - v) u) * ⟪Na, b - v⟫ =
        det3 (a - v) (b - v) u * (⟪Na, G⟫ - ⟪Na, F⟫) := by
      have k1 : det3 (a - v) (G - v) u * ⟪Na, b - v⟫ =
          det3 (a - v) (b - v) u * (⟪Na, G⟫ - ⟪Na, v⟫) := by rw [key1, inner_sub_right]
      have k2 : det3 (a - v) (F - v) u * ⟪Na, b - v⟫ =
          det3 (a - v) (b - v) u * (⟪Na, F⟫ - ⟪Na, v⟫) := by rw [key2, inner_sub_right]
      linear_combination k1 - k2
    have hpos : 0 < det3 (a - v) (b - v) u * (⟪Na, G⟫ - ⟪Na, F⟫) :=
      mul_pos hdab (sub_pos.mpr hlt)
    rw [← hdiff] at hpos
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (sub_nonneg.mpr hcon) (neg_nonneg.mpr hD.le)]
  have hdet : ∀ (a' : ZMod 5) (κ : ℝ), κ ≠ 0 →
      (∀ X, det3 (quint v m a c b (a' + 1) - quint v m a c b a') X u = κ * det3 (a - v) X u) →
      det3 (a - v) (quint v m a c b a' - v) u = 0 →
      ∀ j : ZMod 5, quint v m a c b j ≠ F →
        det3 (quint v m a c b (a' + 1) - quint v m a c b a') (quint v m a c b j - F) u *
          det3 (quint v m a c b (a' + 1) - quint v m a c b a') (F - quint v m a c b a') u < 0 := by
    intro a' κ hκ hlin hon j hj
    rw [hlin, hlin]
    have e1 : det3 (a - v) (F - quint v m a c b a') u = det3 (a - v) (F - v) u := by
      have : det3 (a - v) (F - quint v m a c b a') u =
          det3 (a - v) (F - v) u - det3 (a - v) (quint v m a c b a' - v) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this, hon, sub_zero]
    have e2 : det3 (a - v) (quint v m a c b j - F) u =
        det3 (a - v) (quint v m a c b j - v) u - det3 (a - v) (F - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e1, e2]
    have hj' : det3 (a - v) (quint v m a c b j - v) u < det3 (a - v) (F - v) u := by
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at hj ⊢
      · have : det3 (a - v) (v - v) u = 0 := by
          rw [sub_self]; simp only [det3_expand, PiLp.zero_apply]; ring
        rw [this]; exact hP
      · rw [hmeq]
        have : det3 (a - v) (v + s • (a - v) + δ • u - v) u = 0 := by
          simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        rw [this]; exact hP
      · have : det3 (a - v) (a - v) u = 0 := by simp only [det3_expand]; ring
        rw [this]; exact hP
      · exact hG c (Or.inl rfl) hj
      · exact hG b (Or.inr rfl) hj
    have hκ2 : 0 < κ * κ := mul_self_pos.mpr hκ
    nlinarith [mul_pos hκ2 hP]
  have lin0 : ∀ X, det3 (quint v m a c b (0 + 1) - quint v m a c b 0) X u =
      s * det3 (a - v) X u := by
    intro X; rw [b0, quint_0, quint_1, hmeq]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have lin1 : ∀ X, det3 (quint v m a c b (1 + 1) - quint v m a c b 1) X u =
      (1 - s) * det3 (a - v) X u := by
    intro X; rw [b1, quint_1, quint_2, hmeq]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have on0 : det3 (a - v) (quint v m a c b 0 - v) u = 0 := by
    rw [quint_0, sub_self]; simp only [det3_expand, PiLp.zero_apply]; ring
  have on1 : det3 (a - v) (quint v m a c b 1 - v) u = 0 := by
    rw [quint_1, hmeq]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hs1' : (1 - s) ≠ 0 := by linarith
  -- the case analysis
  have vals : (0 - 3 : ZMod 5).val = 2 ∧ (1 - 3 : ZMod 5).val = 3 ∧ (0 - 4 : ZMod 5).val = 1 ∧
      (1 - 4 : ZMod 5).val = 2 := by decide
  have v3 : (4 - 3 : ZMod 5).val = 1 ∧ (0 - 3 : ZMod 5).val = 2 ∧ (1 - 3 : ZMod 5).val = 3 ∧
      (2 - 3 : ZMod 5).val = 4 := by decide
  have v4 : (0 - 4 : ZMod 5).val = 1 ∧ (1 - 4 : ZMod 5).val = 2 ∧ (2 - 4 : ZMod 5).val = 3 ∧
      (3 - 4 : ZMod 5).val = 4 := by decide
  have hp1 : p₁ = 1 - p₂ := by linarith
  have hFv : ⟪F, u⟫ - ⟪v, u⟫ = p₂ * (⟪a, u⟫ - ⟪v, u⟫) := by rw [hFu, hp1]; ring
  have hFa : ⟪a, u⟫ - ⟪F, u⟫ = p₁ * (⟪a, u⟫ - ⟪v, u⟫) := by rw [hFu, hp1]; ring
  have hbetween : (⟪v, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪a, u⟫) ∨ (⟪a, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪v, u⟫) := by
    rcases lt_or_gt_of_ne hva with h1 | h1
    · left
      have e1 := mul_pos hp₂0 (sub_pos.mpr h1)
      have e2 := mul_pos hp₁0 (sub_pos.mpr h1)
      constructor <;> linarith
    · right
      have e1 := mul_neg_of_pos_of_neg hp₂0 (sub_neg.mpr h1)
      have e2 := mul_neg_of_pos_of_neg hp₁0 (sub_neg.mpr h1)
      constructor <;> linarith
  have hqinj : Function.Injective (quint v m a c b) := fun i j e => hinj (by simp only [e])
  have det0 := hdet 0 s hs0.ne' lin0 on0
  have det1 := hdet 1 (1 - s) hs1' lin1 on1
  rcases hF with ⟨hFc, hcb⟩ | ⟨hFb, hbc⟩
  · -- `F = c`, the vertex `3`
    subst hFc
    have hj : ∀ j : ZMod 5, j ≠ 3 → quint v m a F b j ≠ F := fun j hj e =>
      hj (hqinj (e.trans (quint_3 v m a F b).symm))
    have hbF : (⟪v, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪a, u⟫ → ⟪b, u⟫ < ⟪F, u⟫) ∧
        (⟪a, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪v, u⟫ → ⟪F, u⟫ < ⟪b, u⟫) := by
      constructor
      · rintro ⟨h1, h2⟩
        rcases hz2 with h | h | h | h <;> linarith
      · rintro ⟨h1, h2⟩
        rcases hz1 with h | h | h | h <;> linarith
    rcases hbetween with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> rcases lt_or_gt_of_ne hmF with l3 | l3
    · have l4 := hbF.1 ⟨l1, l2⟩
      refine ⟨1, 3, depthSepAt_quint (fun j hj' => det1 j (hj j hj'))
        (Or.inr ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v3.1, v3.2.1, v3.2.2.1,
          v3.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hbF.1 ⟨l1, l2⟩
      refine ⟨0, 3, depthSepAt_quint (fun j hj' => det0 j (hj j hj'))
        (Or.inr ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v3.1, v3.2.1, v3.2.2.1,
          v3.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hbF.2 ⟨l1, l2⟩
      refine ⟨0, 3, depthSepAt_quint (fun j hj' => det0 j (hj j hj'))
        (Or.inl ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v3.1, v3.2.1, v3.2.2.1,
          v3.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hbF.2 ⟨l1, l2⟩
      refine ⟨1, 3, depthSepAt_quint (fun j hj' => det1 j (hj j hj'))
        (Or.inl ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v3.1, v3.2.1, v3.2.2.1,
          v3.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
  · -- `F = b`, the vertex `4`
    subst hFb
    have hj : ∀ j : ZMod 5, j ≠ 4 → quint v m a c F j ≠ F := fun j hj e =>
      hj (hqinj (e.trans (quint_4 v m a c F).symm))
    have hcF : (⟪v, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪a, u⟫ → ⟪F, u⟫ < ⟪c, u⟫) ∧
        (⟪a, u⟫ < ⟪F, u⟫ ∧ ⟪F, u⟫ < ⟪v, u⟫ → ⟪c, u⟫ < ⟪F, u⟫) := by
      constructor
      · rintro ⟨h1, h2⟩
        rcases hz2 with h | h | h | h <;> linarith
      · rintro ⟨h1, h2⟩
        rcases hz1 with h | h | h | h <;> linarith
    rcases hbetween with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> rcases lt_or_gt_of_ne hmF with l3 | l3
    · have l4 := hcF.1 ⟨l1, l2⟩
      refine ⟨1, 4, depthSepAt_quint (fun j hj' => det1 j (hj j hj'))
        (Or.inr ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v4.1, v4.2.1, v4.2.2.1,
          v4.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hcF.1 ⟨l1, l2⟩
      refine ⟨0, 4, depthSepAt_quint (fun j hj' => det0 j (hj j hj'))
        (Or.inr ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v4.1, v4.2.1, v4.2.2.1,
          v4.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hcF.2 ⟨l1, l2⟩
      refine ⟨0, 4, depthSepAt_quint (fun j hj' => det0 j (hj j hj'))
        (Or.inl ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v4.1, v4.2.1, v4.2.2.1,
          v4.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith
    · have l4 := hcF.2 ⟨l1, l2⟩
      refine ⟨1, 4, depthSepAt_quint (fun j hj' => det1 j (hj j hj'))
        (Or.inl ⟨fun j hj' hv => ?_, fun j hj' hv => ?_⟩)⟩ <;>
        rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
        simp only [quint_0, quint_1, quint_2, quint_3, quint_4, v4.1, v4.2.1, v4.2.2.1,
          v4.2.2.2] at hv hj' ⊢ <;>
        first | exact absurd rfl hj' | omega | linarith

end EdgeConf

end Minimality

end
