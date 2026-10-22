module

public import Minimality.EdgeClassC
public import Minimality.EdgeRd

@[expose] public section

/-!
# Class `d`: Theorem 22.8 for an edge crossing (`FEWER-FACES-PROOFS.md` §22.5, §22.6, §22.8)

A horizontal double normal of class `d_a`: the far edge `g = [c, b]` parallel to the quadrilateral
`F_a`, with the double normal from the open side `(v, a)` to `g`.  Three ways out:
* the partner closing `K_w` has no weak saddle: it is realized on `F_b`'s circle (its chord
  `w a` is an edge of `F_a`), and its slide there has no persistent double normal
  (`OneHDNDir`; Lemma 22.5);
* the slide rim `v m a c b` on `F_b`'s circle is strictly unimodal (Lemma 22.6 (a));
* otherwise (H1) holds (`h1_core`), (H4) follows from Lemma E (`v`, `w` strictly on opposite
  sides of the plane `a c b`), and A.10's Theorem R applies (`rdRim_of_H`, `isRupert_of_rdRim`).

* `quad_hidden`: a point strictly inside the convex quadrilateral `v a c b` lies strictly
  inside one of the triangles `v c b`, `v a c`, `v a b`, `a c b`, `m c b` (`m` over the open
  side `(v, a)`).
* `EdgeConf.isRupert_partner` (Lemma 22.5), `EdgeConf.isRupert_classD` (Theorem 22.8).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The Plücker relation of the screen determinants. -/
theorem det3_plucker (A B C X u : ℝ³) :
    det3 B C u * det3 A X u + det3 C A u * det3 B X u + det3 A B u * det3 C X u = 0 := by
  simp only [det3_expand]; ring

/-- **A hidden point lies strictly inside a triangle of the rim** (with the middle `m` over the
open side `(v, a)` for the crossing of the diagonals). -/
theorem quad_hidden {v a c b m x u : ℝ³} {s δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hmeq : m = v + s • (a - v) + δ • u)
    (q1 : 0 < det3 (a - v) (c - v) u) (q2 : 0 < det3 (c - a) (b - a) u)
    (q3 : 0 < det3 (b - c) (v - c) u) (q4 : 0 < det3 (v - b) (a - b) u)
    (h1 : 0 < det3 (a - v) (x - v) u) (h2 : 0 < det3 (c - a) (x - a) u)
    (h3 : 0 < det3 (b - c) (x - c) u) (h4 : 0 < det3 (v - b) (x - b) u) :
    ∃ P Q R : ℝ³, (P = v ∨ P = a ∨ P = c ∨ P = b ∨ P = m) ∧
      (Q = v ∨ Q = a ∨ Q = c ∨ Q = b ∨ Q = m) ∧ (R = v ∨ R = a ∨ R = c ∨ R = b ∨ R = m) ∧
      0 < det3 (Q - P) (R - P) u ∧ 0 < det3 (Q - P) (x - P) u ∧
      0 < det3 (R - Q) (x - Q) u ∧ 0 < det3 (P - R) (x - R) u := by
  -- the screen determinants relative to `v`
  set A := a - v
  set B := b - v
  set C := c - v
  set X := x - v
  have e1 : det3 (c - a) (b - a) u = det3 C B u + det3 A C u - det3 A B u := by
    simp only [A, B, C, det3_expand, PiLp.sub_apply]; ring
  have e3 : det3 (b - c) (v - c) u = det3 C B u := by
    simp only [B, C, det3_expand, PiLp.sub_apply]; ring
  have e4 : det3 (v - b) (a - b) u = det3 A B u := by
    simp only [A, B, det3_expand, PiLp.sub_apply]; ring
  have f2 : det3 (c - a) (x - a) u = det3 C X u + det3 A C u - det3 A X u := by
    simp only [A, C, X, det3_expand, PiLp.sub_apply]; ring
  have f3 : det3 (b - c) (x - c) u = det3 B X u + det3 C B u - det3 C X u := by
    simp only [B, C, X, det3_expand, PiLp.sub_apply]; ring
  have f4 : det3 (v - b) (x - b) u = -det3 B X u := by
    simp only [B, X, det3_expand, PiLp.sub_apply]; ring
  rw [e1] at q2
  rw [e3] at q3
  rw [e4] at q4
  rw [f2] at h2
  rw [f3] at h3
  rw [f4] at h4
  have hmem : ∀ P, P = v ∨ P = a ∨ P = c ∨ P = b ∨ P = m → P = v ∨ P = a ∨ P = c ∨ P = b ∨ P = m :=
    fun _ h => h
  rcases lt_trichotomy (det3 C X u) 0 with s1 | s1 | s1
  · -- `v a c`
    refine ⟨v, a, c, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), q1, h1,
      ?_, ?_⟩
    · rw [f2]; linarith
    · have : det3 (v - c) (x - c) u = -det3 C X u := by
        simp only [C, X, det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
  · rcases lt_trichotomy (det3 B X u + det3 A B u - det3 A X u) 0 with s2 | s2 | s2
    · -- `a c b`
      refine ⟨a, c, b, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
        Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [e1]; exact q2, by rw [f2]; exact h2,
        by rw [f3]; exact h3, ?_⟩
      have : det3 (a - b) (x - b) u = -(det3 B X u + det3 A B u - det3 A X u) := by
        simp only [A, B, X, det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    · -- the crossing of the diagonals: `m c b`
      have pl := det3_plucker A B C X u
      have hCA : det3 C A u = -det3 A C u := by simp only [det3_expand]; ring
      have hBC : det3 B C u = -det3 C B u := by simp only [det3_expand]; ring
      rw [hCA, hBC, s1, mul_zero, add_zero] at pl
      -- `α = D(A, X)`, `β = −D(B, X)`: `q3 α = q1 β`, `α + β = q4`
      have hα : det3 A X u < det3 A C u := by
        by_contra hc
        push Not at hc
        nlinarith
      have hM : ∀ Y : ℝ³, det3 (m - v) Y u = s * det3 A Y u := by
        intro Y; rw [hmeq]
        simp only [A, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have hM' : ∀ Y : ℝ³, det3 Y (m - v) u = s * det3 Y A u := by
        intro Y; rw [hmeq]
        simp only [A, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      refine ⟨m, c, b, Or.inr (Or.inr (Or.inr (Or.inr rfl))), Or.inr (Or.inr (Or.inl rfl)),
        Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_, ?_, by rw [f3]; exact h3, ?_⟩
      · have : det3 (c - m) (b - m) u =
            det3 C B u - det3 C (m - v) u - det3 (m - v) B u := by
          simp only [C, B, det3_expand, PiLp.sub_apply]; ring
        rw [this, hM, hM', hCA]
        nlinarith [mul_pos (sub_pos.mpr hs1) q3, mul_pos hs0 q2]
      · have : det3 (c - m) (x - m) u =
            det3 C X u - det3 C (m - v) u - det3 (m - v) X u := by
          simp only [C, X, det3_expand, PiLp.sub_apply]; ring
        rw [this, hM, hM', hCA, s1]
        nlinarith [mul_pos hs0 (sub_pos.mpr hα)]
      · have : det3 (m - b) (x - b) u =
            det3 (m - v) X u - det3 (m - v) B u - det3 B X u := by
          simp only [B, X, det3_expand, PiLp.sub_apply]; ring
        rw [this, hM, hM]
        have hβ : det3 A B u = det3 A X u - det3 B X u := by linarith
        have : s * det3 A X u - s * det3 A B u - det3 B X u = (1 - s) * (-det3 B X u) := by
          rw [hβ]; ring
        rw [this]; exact mul_pos (sub_pos.mpr hs1) h4
    · -- `v a b`
      refine ⟨v, a, b, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        by rw [← e4]; simpa only [e4] using q4, h1, ?_, by rw [f4]; exact h4⟩
      have : det3 (b - a) (x - a) u = det3 B X u + det3 A B u - det3 A X u := by
        simp only [A, B, X, det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact s2
  · -- `v c b`
    refine ⟨v, c, b, Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_, s1, by rw [f3]; exact h3,
      by rw [f4]; exact h4⟩
    have : det3 (c - v) (b - v) u = det3 C B u := rfl
    rw [this]; exact q3


theorem HDNDir.neg_u {V : Finset ℝ³} {u ℓ : ℝ³} (h : HDNDir V u ℓ) : HDNDir V (-u) ℓ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [inner_neg_right, h2, neg_zero], h3⟩

theorem OneHDNDir.neg_u {V : Finset ℝ³} {u : ℝ³} (h : OneHDNDir V u) : OneHDNDir V (-u) := by
  intro ℓ ℓ' h1 h2
  have e1 : HDNDir V u ℓ := by have := h1.neg_u; rwa [neg_neg] at this
  have e2 : HDNDir V u ℓ' := by have := h2.neg_u; rwa [neg_neg] at this
  exact h ℓ ℓ' e1 e2

theorem nws4_quad_scale {z₀ z₁ z₂ z₃ t : ℝ} (ht : t ≠ 0) (h : NWS4 (quad z₀ z₁ z₂ z₃)) :
    NWS4 (quad (t * z₀) (t * z₁) (t * z₂) (t * z₃)) := by
  have := h.mul ht
  have e : (fun i => t * quad z₀ z₁ z₂ z₃ i) = quad (t * z₀) (t * z₁) (t * z₂) (t * z₃) := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  rwa [e] at this

theorem strictUnimodal_of_scaled {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) {t : ℝ} (ht : t ≠ 0)
    (h : StrictUnimodal (fun i => t * z i)) : StrictUnimodal z := by
  have hinj' : Function.Injective (fun i => t * z i) := fun i j e => hinj (mul_left_cancel₀ ht e)
  have hc : IsCyclicUnimodal (fun i => t * z i) := ⟨hinj', h.2⟩
  rcases lt_or_gt_of_ne ht with htn | htp
  · have := (hc.neg' hk).smul (c := -t⁻¹) (by simp [htn])
    refine strictUnimodal_of_cyclic hk ?_
    convert this using 2 with i
    field_simp
  · have := hc.smul (c := t⁻¹) (inv_pos.mpr htp)
    refine strictUnimodal_of_cyclic hk ?_
    convert this using 2 with i
    field_simp

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

/-- **Lemma 22.5 (the partner closing).**  If `F_a`'s single middle lies on the far side of the
chord `v a` (`OppA`), the closing `K_w` is realized on `F_b`'s circle.  With a horizontal double
normal `ℓ₀ ∥ N_a` at `u` and at most one direction of them, a `K_w` without a weak saddle makes
the set Rupert (its slide on `F_b`'s circle). -/
theorem isRupert_partner (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m)
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hKw : NWS4 (quad ⟪w, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) (hone : OneHDNDir V u) {ℓ₀ : ℝ³}
    (hℓ₀ : HDNDir V u ℓ₀) (hℓa : cross ℓ₀ Na = 0) : IsRupert V := by
  classical
  have hm : m ∈ Ma := by rw [hMa]; exact mem_singleton_self m
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hopp
  have E' := E.swap.mirror
  have hw := E.hw
  refine E'.isRupert_slideA ?_ ?_ ?_ ?_
  · -- `F_a`'s middle lies on `v`'s side of the chord `a w`
    intro m' hm'
    rw [hMa, mem_singleton] at hm'
    subst hm'
    have hh2 : 0 < h * h := mul_self_pos.mpr E.hh
    refine ⟨(-δ + h * (1 - s)) / h, ?_, ?_⟩
    · have hh := E.hh
      have e : (-δ + h * (1 - s)) / h = -δ * h / (h * h) + (1 - s) := by
        field_simp
      rw [e]
      have : 0 < -δ * h / (h * h) := div_pos (by linarith) hh2
      linarith
    · rw [hmeq, hw]
      have e1 : cross (v + h • u - a) (v + s • (a - v) + δ • u - a) =
          (-δ + h * (1 - s)) • cross (a - v) u := by
        ext j; fin_cases j <;> simp [cross] <;> ring
      have e2 : cross (v + h • u - a) (v - a) = h • cross (a - v) u := by
        ext j; fin_cases j <;> simp [cross] <;> ring
      rw [e1, e2, smul_smul, div_mul_cancel₀ _ E.hh]
  · intro i j hij
    have hq : ∀ i : ZMod 4, quad w b c a i ∈ V := E'.quad_mem
    by_contra hne
    have hinjq : Function.Injective (quad w b c a) := E'.quad_injective
    apply hdist _ (hq i) _ (hq j) (hinjq.ne hne)
    have := hij
    simp only [inner_neg_right, neg_inj] at this
    exact this
  · simp only [NWS4, quad_0, quad_1, quad_2, quad_3, inner_neg_right, neg_lt_neg_iff] at hKw ⊢
    exact ⟨by tauto, by tauto⟩
  · refine noPersist_of_one _ E'.quad_mem E'.supp hone.neg_u hℓ₀.neg_u (N := Na) hℓa ?_
    rw [neg_neg, real_inner_smul_right, inner_sub_right, E.inner_Na_w]
    refine mul_ne_zero E.hh ?_
    have := E.Na_lt E.hb E.hbA.1 E.hbA.2.1 E.hbA.2.2.1 E.hbA.2.2.2
    linarith


/-- **Theorem 22.8 (class `d` at an edge crossing).**  `F_a` has the single middle `m` on the far
side of its chord (`OppA`), all depths at `u` are distinct, `K_v` has no weak saddle, at most one
direction of horizontal double normals at `u`, and Lemma E holds strictly (`v`, `w` on opposite
sides of the plane `a c b`) where the partner `K_w` has a weak saddle.  A horizontal double
normal `F − Z ∥ N_a` from the open side
`(v, a)` to the far edge `[c, b] ∥ F_a` makes the set Rupert: by the partner closing (Lemma 22.5),
by the slide rim on `F_b`'s circle (Lemma 22.6 (a)), or by A.10's Theorem R. -/
theorem isRupert_classD (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m)
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) (hone : OneHDNDir V u)
    {Z F : ℝ³} (hZ : Z ∈ segment ℝ v a) (hZv : Z ≠ v) (hZa : Z ≠ a) (hF : F ∈ segment ℝ c b)
    (hpar : ⟪Na, c⟫ = ⟪Na, b⟫) {r : ℝ} (hFZ : F - Z = r • Na) {ℓ₀ : ℝ³}
    (hdir : HDNDir V u ℓ₀) (hℓa : cross ℓ₀ Na = 0)
    (hE : ¬ NWS4 (quad ⟪w, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫) →
      det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0) : IsRupert V := by
  classical
  have hm : m ∈ Ma := by rw [hMa]; exact mem_singleton_self m
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hopp
  have hinj := E.quint_inj_of_dist hm hdist
  have hbad : NoPersistHDN (quint v m a c b) u (h • (v - b)) := by
    refine noPersist_of_one _ (E.quint_mem hm) (fun z hz => suppIn_quint (E.supp z hz)) hone
      hdir (N := Na) hℓa ?_
    rw [real_inner_smul_right, show v - b = -(b - v) by abel, inner_neg_right]
    exact mul_ne_zero E.hh (neg_ne_zero.mpr E.Na_bv.ne)
  by_cases h5 : StrictUnimodal (fun i => ⟪quint v m a c b i, u⟫)
  · exact E.isRupert_slide5 hMa hopp hinj (Or.inl h5) hbad
  by_cases hKw : NWS4 (quad ⟪w, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)
  · exact E.isRupert_partner hMa hopp hdist hKw hone hdir hℓa
  -- the residual: Theorem R
  have hh := E.hh
  have hw := E.hw
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr E.hu
  have hvw : v - w = (-h) • u := by rw [hw]; module
  have hζ : ∀ X : ℝ³, ⟪X, v - w⟫ = -h * ⟪X, u⟫ := by
    intro X; rw [hvw, real_inner_smul_right]
  -- (H1)
  have hq : ∀ k, quint ⟪v, v - w⟫ ⟪m, v - w⟫ ⟪a, v - w⟫ ⟪c, v - w⟫ ⟪b, v - w⟫ k =
      -h * ⟪quint v m a c b k, u⟫ := by
    intro k; rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, hζ]
  have hinjζ : Function.Injective (quint ⟪v, v - w⟫ ⟪m, v - w⟫ ⟪a, v - w⟫ ⟪c, v - w⟫
      ⟪b, v - w⟫) := by
    intro i j hij
    rw [hq, hq] at hij
    exact hinj (mul_left_cancel₀ (neg_ne_zero.mpr hh) hij)
  have hH1 := h1_core (zv := ⟪v, v - w⟫) (zm := ⟪m, v - w⟫) (zf := ⟪a, v - w⟫)
    (zgf := ⟪c, v - w⟫) (zgv := ⟪b, v - w⟫) (zw := ⟪w, v - w⟫) hs0 hs1 ?_ ?_ ?_ ?_ hinjζ ?_
  rotate_left
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
  obtain ⟨H1m, H1b, H1a, H1c⟩ := hH1
  have hH1' : 0 < ⟪m - v, v - w⟫ ∧ 0 < ⟪b - v, v - w⟫ ∧ ⟪a - v, v - w⟫ < 0 ∧
      ⟪c - v, v - w⟫ < 0 := by
    simp only [inner_sub_left]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hm' : m = v + s • (a - v) + (-δ / h) • (v - w) := by
    rw [hmeq, hvw, smul_smul]
    congr 2
    field_simp
  have hδ' : 0 < -δ / h := by
    rw [show -δ / h = -δ * h / (h * h) by field_simp]
    exact div_pos (by linarith) (mul_self_pos.mpr hh)
  have q1 := E.det_a_pos E.hc E.hcA.1 E.hcA.2.1 E.hcA.2.2.1 E.hcA.2.2.2
  have q2 := E.det_ac_pos E.hb E.hbA.2.2.1 E.hcB.1.symm
  have q3 := E.det_cb_pos E.hv E.hcA.1.symm E.hbA.1.symm
  have q4 : 0 < det3 (v - b) (a - b) u := by
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact E.dba_pos
  have hsm : ∀ X Y : ℝ³, det3 X Y (v - w) = -h * det3 X Y u := by
    intro X Y; rw [hvw, det3_smul_right]
  have hoff : det3 (v - w) (a - v) (b - v) ≠ 0 := by
    have : det3 (v - w) (a - v) (b - v) = det3 (a - v) (b - v) (v - w) := by
      simp only [det3_expand]; ring
    rw [this, hsm]
    exact mul_ne_zero (neg_ne_zero.mpr hh) E.dab_pos.ne'
  have horient : 0 < det3 (a - v) (c - v) (v - w) * det3 (b - c) (v - c) (v - w) := by
    rw [hsm, hsm]
    have : -h * det3 (a - v) (c - v) u * (-h * det3 (b - c) (v - c) u) =
        (h * h) * (det3 (a - v) (c - v) u * det3 (b - c) (v - c) u) := by ring
    rw [this]
    exact mul_pos (mul_self_pos.mpr hh) (mul_pos q1 q3)
  have hpar' : det3 (v - w) (a - v) (c - b) = 0 := by
    have : det3 (v - w) (a - v) (c - b) = det3 (a - v) (c - b) (v - w) := by
      simp only [det3_expand]; ring
    rw [this, hsm]
    have key := E.det_a_rel (c - b)
    rw [inner_sub_right Na c b, hpar, sub_self, mul_zero] at key
    have := (mul_eq_zero.mp key).resolve_right E.Na_bv.ne
    rw [this, mul_zero]
  have hfeet : ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
      ⟪v + lam • (a - v) - (b + mu • (c - b)), v - w⟫ = 0 ∧
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
    · rw [hdiff, inner_neg_left, real_inner_smul_left, hvw, real_inner_smul_right, E.Na_u]
      ring
    · rw [hdiff, inner_neg_left, real_inner_smul_left, E.Na_av]; ring
  have hR := rdRim_of_H hm' hs0 hs1 hδ' hoff horient hpar' (hE hKw) hH1' hfeet
  have hne : v - w ≠ 0 := by rw [hvw]; exact smul_ne_zero (neg_ne_zero.mpr hh) E.hu
  refine isRupert_of_rdRim V (insert w Mb) hR hne E.hv (E.hMa hm) E.ha E.hc E.hb ?_ ?_
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨0, -1, by module, by norm_num, Or.inr ⟨rfl, by norm_num⟩⟩
    · obtain ⟨sb, δb, hsb0, hsb1, hxeq⟩ := E.midB_coords hx
      have hδb := E.midB_delta_ne hx hsb0 hsb1 hxeq
      refine ⟨sb, -δb / h, ?_, div_ne_zero (neg_ne_zero.mpr hδb) hh, Or.inl ⟨hsb0, hsb1⟩⟩
      rw [hxeq, hvw, smul_smul]
      congr 2
      field_simp
  · intro x hx hxM
    simp only [mem_insert, not_or] at hxM
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxa : x = a
    · exact Or.inr (Or.inr (Or.inl hxa))
    by_cases hxm : x ∈ Ma
    · rw [hMa, mem_singleton] at hxm; exact Or.inr (Or.inl hxm)
    by_cases hxc : x = c
    · exact Or.inr (Or.inr (Or.inr (Or.inl hxc)))
    by_cases hxb : x = b
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxb))))
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have h1 := E.det_a_pos hx hxv hxM.1 hxa hxm
    have h2 := E.det_ac_pos hx hxa hxc
    have h3 := E.det_cb_pos hx hxc hxb
    have h4 := E.det_b_pos hx hxv hxM.1 hxb hxM.2
    obtain ⟨P, Q, R, hP, hQ, hR', d0, d1, d2, d3⟩ :=
      quad_hidden hs0 hs1 hmeq q1 q2 q3 q4 h1 h2 h3 h4
    have memV : ∀ X, (X = v ∨ X = a ∨ X = c ∨ X = b ∨ X = m) → X ∈ V := by
      rintro X (rfl | rfl | rfl | rfl | rfl)
      exacts [E.hv, E.ha, E.hc, E.hb, E.hMa hm]
    have pos : ∀ X Y : ℝ³, 0 < det3 X Y u → 0 < -h * det3 X Y (v - w) := by
      intro X Y hXY
      rw [hsm, ← mul_assoc, neg_mul_neg]
      exact mul_pos (mul_self_pos.mpr hh) hXY
    exact rdHidden_of_sign (memV P hP) (memV Q hQ) (memV R hR') (pos _ _ d0) (pos _ _ d1)
      (pos _ _ d2) (pos _ _ d3)

end EdgeConf

end Minimality

end
