module

public import Minimality.VtxSlide
public import Minimality.EdgeClassC

@[expose] public section

/-!
# Class `c` at a vertex view (`FEWER-FACES-PROOFS.md` Lemma 22.4)

As `EdgeConf.isRupert_classC`: a horizontal double normal `F − Z ∥ N_a` from the open side
`(v, a)` of the quadrilateral `F_a` to a far corner `F` strictly farthest from `F_a` makes the set
Rupert: on `F_b`'s circle the slide rim `v p a c b` (the upper middle `p` poked out, `q` hidden)
has a depth-separated pair.

* `VtxConf.quint_inj_of_dist`, `VtxConf.isRupert_classC`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- The slide rim `v m a c b` (`m` a middle of `F_a`) has distinct depths if `V` has. -/
theorem quint_inj_of_dist (E : VtxConf V u v a c b p q n Na Nb κa κb) {m : ℝ³}
    (hm : m = p ∨ m = q) (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) :
    Function.Injective (fun i => ⟪quint v m a c b i, u⟫) := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, hpq, hpn, hqn⟩ := E.ne7
  have hmV : m ∈ V := by rcases hm with rfl | rfl; exacts [E.hp, E.hq]
  have hmv : m ≠ v := by rcases hm with rfl | rfl; exacts [hvp.symm, hvq.symm]
  have hma : m ≠ a := by rcases hm with rfl | rfl; exacts [hap.symm, haq.symm]
  have hmc : m ≠ c := by rcases hm with rfl | rfl; exacts [hcp.symm, hcq.symm]
  have hmb : m ≠ b := by rcases hm with rfl | rfl; exacts [hbp.symm, hbq.symm]
  have hinjq : Function.Injective (quint v m a c b) := by
    intro i j hij
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at hij <;>
      first | rfl | (exfalso; simp_all)
  intro i j hij
  by_contra hne
  exact hdist _ (E.quint_mem hmV i) _ (E.quint_mem hmV j) (hinjq.ne hne) hij

/-- **Lemma 22.4 at a vertex view (class `c` is never an exception).**  All depths at `u` distinct, `K_v` without a weak saddle, and
at most one direction of horizontal double normals at `u`.  A horizontal double normal
`F − Z ∥ N_a` from the open side `(v, a)` to a far corner `F` strictly farthest from `F_a` makes
the set Rupert (the slide rim `v m a c b` on `F_b`'s circle has a depth-separated pair). -/
theorem isRupert_classC (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (hdist : ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫)) (hone : OneHDNDir V u)
    {Z F : ℝ³} (hZ : Z ∈ segment ℝ v a) (hZv : Z ≠ v) (hZa : Z ≠ a)
    (hF : (F = c ∧ ⟪Na, c⟫ < ⟪Na, b⟫) ∨ (F = b ∧ ⟪Na, b⟫ < ⟪Na, c⟫))
    {r : ℝ} (hFZ : F - Z = r • Na) {ℓ₀ : ℝ³} (hdir : HDNDir V u ℓ₀) (hℓa : cross ℓ₀ Na = 0) :
    IsRupert V := by
  classical
  obtain ⟨hva', hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, hpq, hpn, hqn⟩ := E.ne7
  set m := p with hmdef
  obtain ⟨s, δ, hs0, hs1, hδ, hmeq⟩ := E.p_coords
  obtain ⟨s', δ', hs0', hs1', hδ', hmeq'⟩ := E.q_coords
  have hinj := E.quint_inj_of_dist (Or.inl rfl) hdist
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  -- no persistent double normal on `F_b`'s circle
  have hbad : NoPersistHDN (quint v m a c b) u (b - v) := by
    refine noPersist_of_one _ (E.quint_mem E.hp) (fun z hz => suppIn_quint (E.supp z hz)) hone
      hdir (N := Na) hℓa E.Na_bv.ne
  refine E.isRupert_slide5 (m := p) (m' := q) (Or.inl ⟨rfl, rfl⟩) hs0 hs1 hs0' hs1' hmeq hmeq'
    (lam := 1) (by linarith) (by linarith) hinj (Or.inr ?_) hbad
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
    refine hdist m E.hp F hFV ?_
    rcases hF with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]; exact hcp.symm
    · rw [e]; exact hbp.symm
  have hva : ⟪v, u⟫ ≠ ⟪a, u⟫ := hdist v E.hv a E.ha hva'
  obtain ⟨hz1, hz2⟩ := hz
  simp only [quad_0, quad_1, quad_2, quad_3] at hz1 hz2
  have dcb : ⟪c, u⟫ ≠ ⟪b, u⟫ := hdist c E.hc b E.hb hcb
  -- the screen tests along the chain: multiples of the test along `v a`
  have hP : 0 < det3 (a - v) (F - v) u := by
    rcases hF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact E.det_a_pos E.hc hvc.symm hac.symm hcp hcq
    · exact E.det_a_pos E.hb hvb.symm hab.symm hbp hbq
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

end VtxConf

end Minimality

end
