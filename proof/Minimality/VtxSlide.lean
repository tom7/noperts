module

public import Minimality.VtxConf
public import Minimality.EdgeFive

@[expose] public section

/-!
# Slides along the two face circles at a vertex view (`FEWER-FACES-PROOFS.md` §22.1, §22.3)

In a `VtxConf` (the quadrilateral `F_a` with its middles `p` above and `q` below the chord
`v a`, the triangle `F_b` with its middle `n`):
* along `F_a`'s circle (`u + t λ (a − v)`, `λ = −δ_n`) `F_a` stays edge-on with `p`, `q` over the
  open side `(v, a)`, and `n` is hidden at first order: the closing is realized there
  (Lemma 22.1), and with distinct depths and a unimodal rim only a double normal in space
  perpendicular to `F_a` is left (`VtxConf.isRupert_slideA`, Lemma 22.3);
* along `F_b`'s circle (`u + t λ (b − v)`) the middle `m` of `F_a` with `λ δ_m > 0` pokes out
  and the other is hidden at first order: the rim is the five-corner *slide rim* `v m a c b`
  (`VtxConf.isRupert_slide5`, Lemmas 22.4, 22.6 (a)).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `NoPersistHDN` depends on the direction of the slide only up to a nonzero factor. -/
theorem NoPersistHDN.smul {k : ℕ} {x : ZMod k → ℝ³} {u e : ℝ³} (h : NoPersistHDN x u e) {lam : ℝ}
    (hlam : lam ≠ 0) : NoPersistHDN x u (lam • e) := by
  intro i j Y hY Y' hY' hne hu he
  rw [real_inner_smul_right] at he
  exact h i j Y hY Y' hY' hne hu ((mul_eq_zero.mp he).resolve_left hlam)

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- **Lemma 22.3 at a vertex view (the slide on `F_a`'s circle).**  With distinct depths of
`v, a, c, b`, the rim without a weak saddle, and no double normal of the rim in space
perpendicular to `F_a` (`NoPersistHDN` along the chord `a − v`), the set is Rupert. -/
theorem isRupert_slideA (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (hinj : Function.Injective (fun i => ⟪quad v a c b i, u⟫))
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hbad : NoPersistHDN (quad v a c b) u (a - v)) : IsRupert V := by
  classical
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, hpq, hpn, hqn⟩ := E.ne7
  obtain ⟨sn, δn, hsn0, hsn1, hδn, hneq⟩ := E.n_coords
  set e := (-δn) • (a - v) with he
  have hcyc := E.cyc
  refine isRupert_of_slideP V {p, q} u e E.hu (quad v a c b) E.quad_mem ?_
    (by norm_num) 1 one_ne_zero
    (fun i j hi hj => Or.inl (by rw [one_mul]; exact hcyc i j hi hj)) ?_ ?_ hinj ?_
    (hbad.smul (neg_ne_zero.mpr hδn))
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
    exacts [⟨hvp, hvq⟩, ⟨hap, haq⟩, ⟨hcp, hcq⟩, ⟨hbp, hbq⟩]
  · intro y hy hyM hyx i
    simp only [mem_insert, mem_singleton, not_or] at hyM
    have hyv : y ≠ v := hyx 0
    have hya : y ≠ a := hyx 1
    have hyc : y ≠ c := hyx 2
    have hyb : y ≠ b := hyx 3
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    · exact Or.inl (by rw [one_mul]; exact E.det_a_pos hy hyv hya hyM.1 hyM.2)
    · exact Or.inl (by rw [one_mul]; exact E.det_ac_pos hy hya hyc)
    · exact Or.inl (by rw [one_mul]; exact E.det_cb_pos hy hyc hyb)
    · by_cases hyn : y = n
      · subst hyn
        right
        constructor
        · rw [hneq]
          simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        · rw [one_mul, hneq, he]
          have e1 : det3 (v - b) (v + sn • (b - v) + δn • u - b) ((-δn) • (a - v)) =
              (δn * δn) * det3 (v - b) (a - v) u := by
            simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
              PiLp.neg_apply, smul_eq_mul]; ring
          rw [e1]
          exact mul_pos (mul_self_pos.mpr hδn) E.dba_pos
      · exact Or.inl (by rw [one_mul]; exact E.det_b_pos hy hyv hyb hyn)
  · intro m hm
    have key : ∀ s δ : ℝ, 0 < s → s < 1 → δ ≠ 0 → m = v + s • (a - v) + δ • u →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
          m = quad v a c b i + s • (quad v a c b (i + 1) - quad v a c b i) + δ • (u + t • e) := by
      intro s₀ δ₀ hs0 hs1 hδ hmeq
      filter_upwards [eventually_mem_Ioo_affine (B := δ₀ * δn) hs0 hs1] with t ht
      refine ⟨0, s₀ + t * (δ₀ * δn), δ₀, ht.1, ht.2, hδ, ?_⟩
      simp only [a0, quad_0, quad_1]
      rw [hmeq, he]; module
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, hmeq⟩ := E.p_coords
      exact key s δ hs0 hs1 hδ.ne' hmeq
    · obtain ⟨s, δ, hs0, hs1, hδ, hmeq⟩ := E.q_coords
      exact key s δ hs0 hs1 hδ.ne hmeq
  · left
    rw [quad_inner'] at hinj ⊢
    exact strictUnimodal_of_cyclic (by norm_num) (isCyclicUnimodal_of_NWS4 hinj hz)

theorem quint_mem (E : VtxConf V u v a c b p q n Na Nb κa κb) {m : ℝ³} (hm : m ∈ V)
    (i : ZMod 5) : quint v m a c b i ∈ V := by
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  exacts [E.hv, hm, E.ha, E.hc, E.hb]

/-- **The five-corner slide on `F_b`'s circle** (Lemmas 22.4, 22.6 (a)).  Along
`u + t λ (b − v)` the middle `m = v + s (a − v) + δ u` of `F_a` with `λ δ > 0` pokes out and the
other middle `m' = v + s' (a − v) + δ' u` (`λ δ' < 0`) is hidden at first order.  If the slide
rim `v m a c b` has distinct depths, is strictly unimodal or has a depth-separated pair at `u`,
and has no double normal in space perpendicular to `F_b` (`NoPersistHDN` along `b − v`), the set
is Rupert. -/
theorem isRupert_slide5 (E : VtxConf V u v a c b p q n Na Nb κa κb) {m m' : ℝ³}
    (hmm : (m = p ∧ m' = q) ∨ (m = q ∧ m' = p)) {s δ s' δ' lam : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hs0' : 0 < s') (hs1' : s' < 1)
    (hmeq : m = v + s • (a - v) + δ • u) (hmeq' : m' = v + s' • (a - v) + δ' • u)
    (hlamδ : 0 < lam * δ) (hlamδ' : lam * δ' < 0)
    (hinj : Function.Injective (fun i => ⟪quint v m a c b i, u⟫))
    (hz : UniOrSep (quint v m a c b) u)
    (hbad : NoPersistHDN (quint v m a c b) u (b - v)) : IsRupert V := by
  classical
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, hpq, hpn, hqn⟩ := E.ne7
  have hmV : m ∈ V := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [E.hp, E.hq]
  have hm'V : m' ∈ V := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [E.hq, E.hp]
  have hmv : m ≠ v := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hvp.symm, hvq.symm]
  have hma : m ≠ a := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hap.symm, haq.symm]
  have hmc : m ≠ c := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hcp.symm, hcq.symm]
  have hmb : m ≠ b := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hbp.symm, hbq.symm]
  have hmn : m ≠ n := by rcases hmm with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hpn, hqn]
  have hm'v : m' ≠ v := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [hvq.symm, hvp.symm]
  have hm'a : m' ≠ a := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [haq.symm, hap.symm]
  have hm'c : m' ≠ c := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [hcq.symm, hcp.symm]
  have hm'b : m' ≠ b := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [hbq.symm, hbp.symm]
  have hm'n : m' ≠ n := by rcases hmm with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [hqn, hpn]
  have hmm' : m ≠ m' := by rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hpq, hpq.symm]
  have hlam : lam ≠ 0 := by rintro rfl; simp at hlamδ
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have Dab := E.dab_pos
  have Dba := E.dba_pos
  have Dac := E.det_a_pos E.hc hvc.symm hac.symm hcp hcq
  have Dcav := E.det_ac_pos E.hv hva hvc
  have Dcab := E.det_ac_pos E.hb hab.symm hcb.symm
  have Dbcv := E.det_cb_pos E.hv hvc hvb
  have Dbca := E.det_cb_pos E.ha hac hab
  have Dbvc := E.det_b_pos E.hc hvc.symm hcb hcn
  have Dbva : 0 < det3 (v - b) (a - b) u := by
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact Dba
  set e := lam • (b - v) with he
  have T : ∀ X Y : ℝ³, SlideTest 1 X Y u e ↔
      (0 < det3 X Y u ∨ (det3 X Y u = 0 ∧ 0 < det3 X Y e)) := by
    intro X Y; simp only [SlideTest, one_mul]
  have hmv' : m - v = s • (a - v) + δ • u := by rw [hmeq]; abel
  have t01a : SlideTest 1 (m - v) (a - v) u e := by
    rw [T]; right; constructor
    · rw [hmv']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    · have : det3 (m - v) (a - v) e = (lam * δ) * det3 (a - v) (b - v) u := by
        rw [hmv', he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_pos hlamδ Dab
  have t01c : SlideTest 1 (m - v) (c - v) u e := by
    rw [T]; left
    have : det3 (m - v) (c - v) u = s * det3 (a - v) (c - v) u := by
      rw [hmv']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]; exact mul_pos hs0 Dac
  have t01b : SlideTest 1 (m - v) (b - v) u e := by
    rw [T]; left
    have : det3 (m - v) (b - v) u = s * det3 (a - v) (b - v) u := by
      rw [hmv']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]; exact mul_pos hs0 Dab
  have t12c : SlideTest 1 (a - m) (c - m) u e := by
    rw [T]; left
    have : det3 (a - m) (c - m) u = (1 - s) * det3 (a - v) (c - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]; exact mul_pos (by linarith) Dac
  have t12b : SlideTest 1 (a - m) (b - m) u e := by
    rw [T]; left
    have : det3 (a - m) (b - m) u = (1 - s) * det3 (a - v) (b - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]; exact mul_pos (by linarith) Dab
  have t12v : SlideTest 1 (a - m) (v - m) u e := by
    rw [T]; right; constructor
    · rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    · have : det3 (a - m) (v - m) e = (lam * δ) * det3 (a - v) (b - v) u := by
        rw [hmeq, he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_pos hlamδ Dab
  have t23m : SlideTest 1 (c - a) (m - a) u e := by
    rw [T]; left
    have : det3 (c - a) (m - a) u = (1 - s) * det3 (c - a) (v - a) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]; exact mul_pos (by linarith) Dcav
  have t34m : SlideTest 1 (b - c) (m - c) u e := by
    rw [T]; left
    have : det3 (b - c) (m - c) u =
        (1 - s) * det3 (b - c) (v - c) u + s * det3 (b - c) (a - c) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]; nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - s) Dbcv, mul_pos hs0 Dbca]
  have t40m : SlideTest 1 (v - b) (m - b) u e := by
    rw [T]; left
    have : det3 (v - b) (m - b) u = s * det3 (v - b) (a - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]; exact mul_pos hs0 Dba
  have st : ∀ {X Y : ℝ³}, 0 < det3 X Y u → SlideTest 1 X Y u e := fun h' => Or.inl (by
    rw [one_mul]; exact h')
  refine isRupert_of_slideP V {n} u e E.hu (quint v m a c b) (E.quint_mem hmV) ?_
    (by norm_num) 1 one_ne_zero ?_ ?_ ?_ hinj hz (hbad.smul hlam)
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_singleton]
    exacts [hvn, hmn, han, hcn, hbn]
  · intro i j hi hj
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4] at hi hj ⊢ <;>
    first
    | exact absurd rfl hi | exact absurd rfl hj
    | exact t01a | exact t01c | exact t01b | exact t12c | exact t12b | exact t12v
    | exact t23m | exact t34m | exact t40m
    | exact st Dcab | exact st Dcav | exact st Dbcv | exact st Dbca | exact st Dbva
    | exact st Dbvc
  · intro y hy hyM hyx i
    simp only [mem_singleton] at hyM
    have hyv : y ≠ v := hyx 0
    have hym : y ≠ m := hyx 1
    have hya : y ≠ a := hyx 2
    have hyc : y ≠ c := hyx 3
    have hyb : y ≠ b := hyx 4
    by_cases hy' : y = m'
    · -- the other middle: hidden at first order along the two sides on `F_a`
      subst hy'
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
      · rw [T]; right; constructor
        · rw [hmeq, hmeq']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
            PiLp.smul_apply, smul_eq_mul]; ring
        · have : det3 (m - v) (y - v) e =
              (lam * δ * s' - lam * δ' * s) * det3 (a - v) (b - v) u := by
            rw [hmeq, hmeq', he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
              PiLp.smul_apply, smul_eq_mul]; ring
          rw [this]
          exact mul_pos (by nlinarith [mul_pos hlamδ hs0', mul_neg_of_neg_of_pos hlamδ' hs0]) Dab
      · rw [T]; right; constructor
        · rw [hmeq, hmeq']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
            PiLp.smul_apply, smul_eq_mul]; ring
        · have : det3 (a - m) (y - m) e =
              (lam * δ * (1 - s') - lam * δ' * (1 - s)) * det3 (a - v) (b - v) u := by
            rw [hmeq, hmeq', he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply,
              PiLp.smul_apply, smul_eq_mul]; ring
          rw [this]
          exact mul_pos (by nlinarith [mul_pos hlamδ (by linarith : (0:ℝ) < 1 - s'),
            mul_neg_of_neg_of_pos hlamδ' (by linarith : (0:ℝ) < 1 - s)]) Dab
      · exact st (E.det_ac_pos hy hya hyc)
      · exact st (E.det_cb_pos hy hyc hyb)
      · exact st (E.det_b_pos hy hyv hyb hyM)
    · have hyp : y ≠ p := by rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hym, hy']
      have hyq : y ≠ q := by rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hy', hym]
      have hA := E.det_a_pos hy hyv hya hyp hyq
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
      · refine st ?_
        have : det3 (m - v) (y - v) u = s * det3 (a - v) (y - v) u := by
          rw [hmv']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        rw [this]; exact mul_pos hs0 hA
      · refine st ?_
        have : det3 (a - m) (y - m) u = (1 - s) * det3 (a - v) (y - v) u := by
          rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        rw [this]; exact mul_pos (by linarith) hA
      · exact st (E.det_ac_pos hy hya hyc)
      · exact st (E.det_cb_pos hy hyc hyb)
      · exact st (E.det_b_pos hy hyv hyb hyM)
  · intro y hy
    rw [mem_singleton] at hy
    subst hy
    obtain ⟨sn, δn, hsn0, hsn1, hδn, hneq⟩ := E.n_coords
    filter_upwards [eventually_mem_Ioo_affine (s₀ := 1 - sn) (B := δn * lam) (by linarith)
      (by linarith)] with t ht
    refine ⟨4, 1 - sn + t * (δn * lam), δn, ht.1, ht.2, hδn, ?_⟩
    simp only [b4, quint_0, quint_4]
    rw [hneq, he]; module

end VtxConf

end Minimality

end
