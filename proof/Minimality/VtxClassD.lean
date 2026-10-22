module

public import Minimality.VtxClassC
public import Minimality.RdGen
public import Minimality.EdgeClassD

@[expose] public section

/-!
# Class `d` at a vertex view (`FEWER-FACES-PROOFS.md` Lemmas 22.9, 22.10, Theorem 22.8)

A horizontal double normal of class `d_a`: the far edge `g = [c, b]` parallel to the
quadrilateral `F_a`, with the double normal from the open side `(v, a)` to `g`.  On `F_b`'s circle
either middle of `F_a` can show (`p` for one sense of the slide, `q` for the other):
* if one of the two slide rims `v p a c b`, `v q a c b` is strictly unimodal, its slide works
  (Lemma 22.6 (a); its persistent double normals would be a second direction);
* otherwise the rim's maximum and minimum are `c`, `b` (Lemma 22.9, `h1_vtx`): (H1) holds for
  `p` along `u` (maximum `b`) or for `q` along `−u` (maximum `c`), and Theorem 22.8 applies
  when (H4) holds for that sense (A.10's Theorem R, `rdRim_of_H` with a virtual second axle
  end), Lemma 22.10 when `m, a, c, b` are coplanar (`rdRimG0_of_H`).  The other middle is hidden
  at first order along the tilt (`RdSlideHidden`).

* `peak_half`, `h1_vtx`: the depth patterns.
* `VtxConf.isRupert_rdUp`: Theorem R at a vertex view from a certificate.
* `VtxConf.isRupert_classD`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Half of Lemma 22.9**: inserting `m` above the chord `[v, a]` into the unimodal rim
`v a c b` (distinct depths) gives a two-peaked rim only if `m` is a peak and the rim's maximum
is `c` or `b`. -/
theorem peak_half {zv zm za zc zb s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hchord : zv + s * (za - zv) < zm) (hNv : NWS4 (quad zv za zc zb))
    (hinj : Function.Injective (quint zv zm za zc zb))
    (h2 : ∃ i j : ZMod 5, i ≠ j ∧
      (quint zv zm za zc zb (i - 1) < quint zv zm za zc zb i ∧
        quint zv zm za zc zb (i + 1) < quint zv zm za zc zb i) ∧
      (quint zv zm za zc zb (j - 1) < quint zv zm za zc zb j ∧
        quint zv zm za zc zb (j + 1) < quint zv zm za zc zb j)) :
    zv < zm ∧ za < zm ∧ ((zv < zc ∧ za < zc ∧ zb < zc) ∨ (zv < zb ∧ za < zb ∧ zc < zb)) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hNv
  have hva : zv ≠ za := fun e => absurd (@hinj 0 2 e) (by decide)
  have hvc : zv ≠ zc := fun e => absurd (@hinj 0 3 e) (by decide)
  have hab : za ≠ zb := fun e => absurd (@hinj 2 4 e) (by decide)
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨c0, c1, c2, c3, c4⟩ := zmod5_sub_one
  rcases lt_or_gt_of_ne hva with hva' | hva'
  · have hm : zv < zm := by nlinarith [mul_pos hs0 (sub_pos.mpr hva')]
    rcases lt_or_gt_of_ne hvc with hvc' | hvc' <;> rcases lt_or_gt_of_ne hab with hab' | hab' <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi hj <;>
    first
    | exact absurd rfl hij
    | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases hNv.1 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases hNv.2 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (refine ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
        Or.inl ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
          by linarith [hi.1, hi.2, hj.1, hj.2]⟩⟩)
    | (refine ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
        Or.inr ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
          by linarith [hi.1, hi.2, hj.1, hj.2]⟩⟩)
  · have hm : za < zm := by nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hva')]
    rcases lt_or_gt_of_ne hvc with hvc' | hvc' <;> rcases lt_or_gt_of_ne hab with hab' | hab' <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi hj <;>
    first
    | exact absurd rfl hij
    | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases hNv.1 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases hNv.2 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (refine ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
        Or.inl ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
          by linarith [hi.1, hi.2, hj.1, hj.2]⟩⟩)
    | (refine ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
        Or.inr ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
          by linarith [hi.1, hi.2, hj.1, hj.2]⟩⟩)

theorem quint_neg (a b c d e : ℝ) :
    (fun i => -quint a b c d e i) = quint (-a) (-b) (-c) (-d) (-e) := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Lemma 22.9 (the depth pattern)**: the unimodal rim `v a c b` with distinct depths, `p`
above and `q` below the chord `[v, a]`, both slide rims `v p a c b`, `v q a c b` two-peaked.
Then the rim's maximum and minimum are `b`, `c`: (H1) for `p` along `u`, or (H1) for `q` along
`−u`. -/
theorem h1_vtx {zv zp zq za zc zb sp sq : ℝ} (hsp0 : 0 < sp) (hsp1 : sp < 1) (hsq0 : 0 < sq)
    (hsq1 : sq < 1) (hp : zv + sp * (za - zv) < zp) (hq : zq < zv + sq * (za - zv))
    (hNv : NWS4 (quad zv za zc zb)) (hinjp : Function.Injective (quint zv zp za zc zb))
    (hinjq : Function.Injective (quint zv zq za zc zb))
    (h5p : ¬ StrictUnimodal (quint zv zp za zc zb))
    (h5q : ¬ StrictUnimodal (quint zv zq za zc zb)) :
    (zv < zp ∧ zv < zb ∧ za < zv ∧ zc < zv) ∨ (zq < zv ∧ zb < zv ∧ zv < za ∧ zv < zc) := by
  obtain ⟨P1, -, P3⟩ := peak_half hsp0 hsp1 hp hNv hinjp (two_peaks hinjp h5p)
  have hinjq' : Function.Injective (quint (-zv) (-zq) (-za) (-zc) (-zb)) := by
    rw [← quint_neg]; exact fun i j e => hinjq (neg_injective e)
  have h5q' : ¬ StrictUnimodal (quint (-zv) (-zq) (-za) (-zc) (-zb)) := by
    intro hs
    apply h5q
    have hc : IsCyclicUnimodal (quint (-zv) (-zq) (-za) (-zc) (-zb)) := ⟨hinjq', hs.2⟩
    have := hc.neg' (by norm_num)
    rw [← quint_neg] at this
    simp only [neg_neg] at this
    exact strictUnimodal_of_cyclic (by norm_num) this
  have hNv' : NWS4 (quad (-zv) (-za) (-zc) (-zb)) := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, neg_lt_neg_iff] at hNv ⊢
    exact ⟨hNv.2, hNv.1⟩
  obtain ⟨Q1, -, Q3⟩ := peak_half (zm := -zq) hsq0 hsq1 (by linarith) hNv' hinjq'
    (two_peaks hinjq' h5q')
  have hva : zv ≠ za := fun e => absurd (@hinjp 0 2 e) (by decide)
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hNv
  rcases lt_or_gt_of_ne hva with hva' | hva' <;>
  rcases P3 with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩ <;> rcases Q3 with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3⟩ <;>
  first
  | (exfalso; linarith)
  | (left; refine ⟨by linarith, by linarith, ?_, by linarith⟩
     rcases hNv.2 with h | h | h | h <;> linarith)
  | (right; refine ⟨by linarith, by linarith, ?_, by linarith⟩
     rcases hNv.1 with h | h | h | h <;> linarith)
  | (left; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
  | (right; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- **Theorem R at a vertex view, from a certificate** (Theorem 22.8 / Lemma 22.10): the
five-corner rim `v m a c b` with `m` one middle of `F_a` and the view `L u` along the axle
(`RdRimG`), the other middle `m'` hidden at first order along `F_b`'s circle (`L δ_{m'} < 0`).
Then the set is Rupert. -/
theorem isRupert_rdUp (E : VtxConf V u v a c b p q n Na Nb κa κb) {m m' : ℝ³}
    (hmm : (m = p ∧ m' = q) ∨ (m = q ∧ m' = p)) {s δ s' δ' L : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hmeq : m = v + s • (a - v) + δ • u)
    (hs0' : 0 < s') (hmeq' : m' = v + s' • (a - v) + δ' • u) (hL : L ≠ 0) (hLδ' : L * δ' < 0)
    (hR : RdRimG v m a c b (L • u)) : IsRupert V := by
  classical
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, hpq, hpn, hqn⟩ := E.ne7
  have hmV : m ∈ V := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [E.hp, E.hq]
  have hm'V : m' ∈ V := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [E.hq, E.hp]
  obtain ⟨sn, δn, hsn0, hsn1, hδn, hneq⟩ := E.n_coords
  have q1 := E.det_a_pos E.hc hvc.symm hac.symm hcp hcq
  have q2 := E.det_ac_pos E.hb hab.symm hcb.symm
  have q3 := E.det_cb_pos E.hv hvc hvb
  have q4 : 0 < det3 (v - b) (a - b) u := by
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact E.dba_pos
  have hsL : ∀ X Y : ℝ³, det3 X Y (L • u) = L * det3 X Y u := fun X Y => det3_smul_right X Y u L
  have hLL : 0 < L * L := mul_self_pos.mpr hL
  have pos : ∀ X Y : ℝ³, 0 < det3 X Y u → 0 < L * det3 X Y (L • u) := by
    intro X Y h; rw [hsL, ← mul_assoc]; exact mul_pos hLL h
  refine isRupert_of_rdRimG V {n} hR (smul_ne_zero hL E.hu) E.hv hmV E.ha E.hc E.hb ?_ ?_
  · intro x hx
    rw [mem_singleton] at hx
    subst hx
    refine ⟨sn, δn / L, ?_, div_ne_zero hδn hL, Or.inl ⟨hsn0, hsn1⟩⟩
    rw [hneq, smul_smul, div_mul_cancel₀ _ hL]
  · intro x hx hxM
    rw [mem_singleton] at hxM
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxm : x = m
    · exact Or.inr (Or.inl hxm)
    by_cases hxa : x = a
    · exact Or.inr (Or.inr (Or.inl hxa))
    by_cases hxc : x = c
    · exact Or.inr (Or.inr (Or.inr (Or.inl hxc)))
    by_cases hxb : x = b
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxb))))
    by_cases hxm' : x = m'
    · -- the other middle: hidden at first order in the triangle `v a c`
      subst hxm'
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨L, hL, v, E.hv, a, E.ha, c, E.hc,
        Or.inl (pos _ _ q1), Or.inr ⟨?_, ?_⟩, Or.inl (pos _ _ ?_), Or.inl (pos _ _ ?_)⟩)))))
      · rw [hsL, hmeq']
        have : det3 (a - v) (v + s' • (a - v) + δ' • u - v) u = 0 := by
          simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        rw [this, mul_zero]
      · rw [hmeq']
        have : det3 (a - v) (v + s' • (a - v) + δ' • u - v) (b - v) =
            -δ' * det3 (a - v) (b - v) u := by
          simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        rw [this]
        nlinarith [mul_pos (neg_pos.mpr hLδ') E.dab_pos]
      · exact E.det_ac_pos hm'V (by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [haq.symm, hap.symm])
          (by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [hcq.symm, hcp.symm])
      · rw [hmeq']
        have : det3 (v - c) (v + s' • (a - v) + δ' • u - c) u = s' * det3 (a - v) (c - v) u := by
          simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        rw [this]; exact mul_pos hs0' q1
    · -- strictly inside the rim: inside a triangle of `v, a, c, b, m`
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
      have hxp : x ≠ p := by rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hxm, hxm']
      have hxq : x ≠ q := by rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hxm', hxm]
      have h1 := E.det_a_pos hx hxv hxa hxp hxq
      have h2 := E.det_ac_pos hx hxa hxc
      have h3 := E.det_cb_pos hx hxc hxb
      have h4 := E.det_b_pos hx hxv hxb hxM
      obtain ⟨P, Q, R, hP, hQ, hR', d0, d1, d2, d3⟩ :=
        quad_hidden hs0 hs1 hmeq q1 q2 q3 q4 h1 h2 h3 h4
      have memV : ∀ X, (X = v ∨ X = a ∨ X = c ∨ X = b ∨ X = m) → X ∈ V := by
        rintro X (rfl | rfl | rfl | rfl | rfl)
        exacts [E.hv, E.ha, E.hc, E.hb, hmV]
      exact rdHidden_of_sign (memV P hP) (memV Q hQ) (memV R hR') (pos _ _ d0) (pos _ _ d1)
        (pos _ _ d2) (pos _ _ d3)

/-- **Theorem 22.8 / Lemma 22.10 in one sense** (the shown middle `m`, the view `L u`): (H1) for
`m` along `L u`, the far edge parallel to `F_a`, the double normal's foot on the open chord,
and (H4) in that sense or `m, a, c, b` coplanar.  Then `RdRimG`. -/
theorem rdRimG_vtx (E : VtxConf V u v a c b p q n Na Nb κa κb) {m : ℝ³} {s δ L : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hmeq : m = v + s • (a - v) + δ • u) (hL : L ≠ 0)
    (hLδ : 0 < L * δ) (hpar : ⟪Na, c⟫ = ⟪Na, b⟫)
    (hH1 : 0 < L * (⟪m, u⟫ - ⟪v, u⟫) ∧ 0 < L * (⟪b, u⟫ - ⟪v, u⟫) ∧
      L * (⟪a, u⟫ - ⟪v, u⟫) < 0 ∧ L * (⟪c, u⟫ - ⟪v, u⟫) < 0)
    (hfeet : ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
      ⟪v + lam • (a - v) - (b + mu • (c - b)), u⟫ = 0 ∧
      ⟪v + lam • (a - v) - (b + mu • (c - b)), a - v⟫ = 0)
    (hD : 0 < det3 (c - a) (b - a) (v - a) * (L * det3 (c - a) (b - a) u) ∨
      det3 (a - m) (c - m) (b - m) = 0) :
    ∃ L' : ℝ, L' ≠ 0 ∧ (0 < L' ↔ 0 < L) ∧ RdRimG v m a c b (L' • u) := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, -⟩ := E.ne7
  have q1 := E.det_a_pos E.hc hvc.symm hac.symm hcp hcq
  have q3 := E.det_cb_pos E.hv hvc hvb
  -- the facts in the sense `L' u` (any `L'` of the sign of `L`)
  have facts : ∀ L' : ℝ, L' ≠ 0 → (0 < L' ↔ 0 < L) →
      m = v + s • (a - v) + (δ / L') • (v - (v - L' • u)) ∧ 0 < δ / L' ∧
      det3 (v - (v - L' • u)) (a - v) (b - v) ≠ 0 ∧
      0 < det3 (a - v) (c - v) (v - (v - L' • u)) * det3 (b - c) (v - c) (v - (v - L' • u)) ∧
      det3 (v - (v - L' • u)) (a - v) (c - b) = 0 ∧
      (0 < ⟪m - v, v - (v - L' • u)⟫ ∧ 0 < ⟪b - v, v - (v - L' • u)⟫ ∧
        ⟪a - v, v - (v - L' • u)⟫ < 0 ∧ ⟪c - v, v - (v - L' • u)⟫ < 0) ∧
      (∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
        ⟪v + lam • (a - v) - (b + mu • (c - b)), v - (v - L' • u)⟫ = 0 ∧
        ⟪v + lam • (a - v) - (b + mu • (c - b)), a - v⟫ = 0) := by
    intro L' hL' hsg
    rw [sub_sub_cancel]
    have hsg' : 0 < L' * L := by
      rcases lt_or_gt_of_ne hL with h | h
      · have : L' < 0 := by
          rcases lt_or_gt_of_ne hL' with h' | h'
          · exact h'
          · exact absurd (hsg.mp h') (not_lt.mpr h.le)
        exact mul_pos_of_neg_of_neg this h
      · exact mul_pos (hsg.mpr h) h
    have hLL : 0 < L' * L' := mul_self_pos.mpr hL'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmeq, smul_smul, div_mul_cancel₀ _ hL']
    · have : δ / L' = (L * δ) * (L' * L) / ((L' * L') * (L * L)) := by
        field_simp
      rw [this]; exact div_pos (mul_pos hLδ hsg') (mul_pos hLL (mul_self_pos.mpr hL))
    · rw [det3_cyc', det3_smul_right]
      exact mul_ne_zero hL' E.dab_pos.ne'
    · rw [det3_smul_right, det3_smul_right]
      have : L' * det3 (a - v) (c - v) u * (L' * det3 (b - c) (v - c) u) =
          (L' * L') * (det3 (a - v) (c - v) u * det3 (b - c) (v - c) u) := by ring
      rw [this]; exact mul_pos hLL (mul_pos q1 q3)
    · rw [det3_cyc', det3_smul_right]
      have key := E.det_a_rel (c - b)
      rw [inner_sub_right Na c b, hpar, sub_self, mul_zero] at key
      have := (mul_eq_zero.mp key).resolve_right E.Na_bv.ne
      rw [this, mul_zero]
    · obtain ⟨k1, k2, k3, k4⟩ := hH1
      simp only [real_inner_smul_right, inner_sub_left]
      have hLL' : 0 < L * L := mul_self_pos.mpr hL
      have e1 : ∀ t : ℝ, 0 < L * t → 0 < L' * t := by
        intro t ht
        have e : (L' * t) * (L * L) = (L' * L) * (L * t) := by ring
        have : 0 < (L' * t) * (L * L) := by rw [e]; exact mul_pos hsg' ht
        exact pos_of_mul_pos_left this hLL'.le
      have e2 : ∀ t : ℝ, L * t < 0 → L' * t < 0 := by
        intro t ht
        have e : (L' * t) * (L * L) = (L' * L) * (L * t) := by ring
        have : (L' * t) * (L * L) < 0 := by rw [e]; exact mul_neg_of_pos_of_neg hsg' ht
        exact neg_of_mul_neg_left this hLL'.le
      have f1 := e1 _ k1; have f2 := e1 _ k2; have f3 := e2 _ k3; have f4 := e2 _ k4
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · obtain ⟨lam, mu, h0, h1, h2, h3⟩ := hfeet
      exact ⟨lam, mu, h0, h1, by rw [real_inner_smul_right, h2, mul_zero], h3⟩
  rcases hD with hD | hD
  · -- (H4): Theorem 22.8 with a virtual second axle end
    set Dv := det3 (c - a) (b - a) (v - a)
    set Du := det3 (c - a) (b - a) u
    have hDu : Du ≠ 0 := by intro h0; rw [h0, mul_zero, mul_zero] at hD; exact lt_irrefl _ hD
    have hDv : Dv ≠ 0 := by intro h0; rw [h0, zero_mul] at hD; exact lt_irrefl _ hD
    set L' := 2 * Dv / Du with hL'
    have hL'0 : L' ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hDv) hDu
    have hsg : 0 < L' ↔ 0 < L := by
      have e : L' = 2 * (Dv * (L * Du)) / (L * (Du * Du)) := by
        rw [hL']; field_simp
      have hp : 0 < 2 * (Dv * (L * Du)) := by linarith
      constructor
      · intro h
        rw [e] at h
        have := (div_pos_iff.mp h)
        rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact pos_of_mul_pos_left h2 (mul_self_nonneg Du)
        · linarith
      · intro h
        rw [e]; exact div_pos hp (mul_pos h (mul_self_pos.mpr hDu))
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := facts L' hL'0 hsg
    have hE : det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) ((v - L' • u) - a) < 0 := by
      have e : det3 (c - a) (b - a) ((v - L' • u) - a) = Dv - L' * Du := by
        simp only [Dv, Du, det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [e, hL', div_mul_cancel₀ _ hDu]
      nlinarith [mul_self_pos.mpr hDv]
    have hR := rdRim_of_H f1 hs0 hs1 f2 f3 f4 f5 hE f6 f7
    rw [sub_sub_cancel] at hR
    exact ⟨L', hL'0, hsg, hR.toG⟩
  · -- Lemma 22.10
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := facts L hL Iff.rfl
    have hR := rdRimG0_of_H f1 hs0 hs1 f2 f3 f4 f5 hD f6 f7
    rw [sub_sub_cancel] at hR
    exact ⟨L, hL, Iff.rfl, hR⟩

end VtxConf

end Minimality

end
