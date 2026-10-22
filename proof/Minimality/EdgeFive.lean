module

public import Minimality.EdgeHDN

@[expose] public section

/-!
# The five-corner slide rim on the other circle (`FEWER-FACES-PROOFS.md` §22.1, §22.4, §22.6)

In an `EdgeConf` where `F_a` is a quadrilateral whose middle `m` lies on the other side of the
chord `v a` from `w` (`OppA`: the closing is not realized on `F_b`'s circle), the views
`u + t h (v − b)` of `F_b`'s circle show `m`: the rim is the five-corner *slide rim*
`v m a c b` (`m` pokes out at first order), `F_b` stays edge-on with `w` and its middles over
the side `(b, v)`.  If the slide rim is strictly unimodal or has a depth-separated pair at `u`
(`UniOrSep`, Lemmas 22.4 and 22.6 (a)) and has no double normal in space perpendicular to `F_b`,
the set is Rupert.

* `OppA`, `EdgeConf.opp_coords`: the middle on the far side of the chord.
* `EdgeConf.isRupert_slide5` (Lemmas 22.4, 22.6 (a)).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The middle `m` of `F_a` lies on the other side of the chord `v a` from `w`. -/
def OppA (v w a m : ℝ³) : Prop :=
  ∃ k : ℝ, k < 0 ∧ cross (a - v) (m - v) = k • cross (a - v) (w - v)

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

theorem cross_sub_smul_eq (A U : ℝ³) (s δ : ℝ) :
    cross A (s • A + δ • U) = δ • cross A U := by
  ext j; fin_cases j <;> simp [cross] <;> ring

/-- Coordinates of a middle on the far side: `m = v + s (a − v) + δ u`, `0 < s < 1`,
`δ h < 0`. -/
theorem opp_coords (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma)
    (hopp : OppA v w a m) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ * h < 0 ∧ m = v + s • (a - v) + δ • u := by
  obtain ⟨s, δ, hs0, hs1, hmeq⟩ := E.midA_coords hm
  obtain ⟨k, hk, hk'⟩ := hopp
  refine ⟨s, δ, hs0, hs1, ?_, hmeq⟩
  have e1 : cross (a - v) (m - v) = δ • cross (a - v) u := by
    rw [hmeq, show v + s • (a - v) + δ • u - v = s • (a - v) + δ • u by abel,
      cross_sub_smul_eq]
  have e2 : cross (a - v) (w - v) = h • cross (a - v) u := by
    rw [E.hw, add_sub_cancel_left, cross_smul_right']
  rw [e1, e2, smul_smul] at hk'
  have hδ : δ = k * h := by
    by_contra hne
    apply E.cross_av
    have : (δ - k * h) • cross (a - v) u = 0 := by rw [sub_smul, hk', sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  rw [hδ]
  have := mul_self_pos.mpr E.hh
  nlinarith

/-- The middles of the two faces are distinct (a point of both faces lies on the axle line). -/
theorem midA_not_midB (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma) :
    m ∉ Mb := by
  intro hmB
  obtain ⟨s, δ, hs0, hs1, hmeq⟩ := E.midA_coords hm
  have hmV := E.hMa hm
  have hNb : ⟪Nb, m⟫ = κb := (E.faceB m hmV).mp (Or.inr (Or.inr (Or.inr hmB)))
  rw [hmeq, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    E.Nb_u, E.inner_Nb_v] at hNb
  nlinarith [mul_neg_of_pos_of_neg hs0 E.Nb_av]

theorem quint_mem (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma)
    (i : ZMod 5) : quint v m a c b i ∈ V := by
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  exacts [E.hv, E.hMa hm, E.ha, E.hc, E.hb]

theorem quint_not_midB (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma)
    (i : ZMod 5) : quint v m a c b i ∉ insert w Mb := by
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, not_or]
  · exact ⟨E.v_ne_w, fun hv => (E.hMb' v hv).1 rfl⟩
  · exact ⟨(E.hMa' m hm).2.1, E.midA_not_midB hm⟩
  · exact ⟨E.haB.2.1, E.haB.2.2⟩
  · exact ⟨E.hcA.2.1, E.hcB.2⟩
  · exact ⟨E.hbA.2.1, fun hb => (E.hMb' b hb).2.2 rfl⟩

/-- The middles of `F_b` (and `w`) lie over the open side `(b, v)` at the views `u + t e` of
`F_b`'s circle, `e = h (v − b)`, for small `t > 0`. -/
theorem eventually_midB (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    ∀ m ∈ insert w Mb, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = b + s • (v - b) + δ • (u + t • (h • (v - b))) := by
  intro m hm
  rcases mem_insert.mp hm with rfl | hm
  · have hh2 : 0 < h * h := mul_self_pos.mpr E.hh
    filter_upwards [eventually_pos_affine (A := 0) (B := h * h) (Or.inr ⟨rfl, hh2⟩),
      eventually_pos_affine (A := 1) (B := -(h * h)) (Or.inl one_pos)] with t ht1 ht2
    refine ⟨1 + t * -(h * h), h, by linarith, by linarith, E.hh, ?_⟩
    rw [E.hw]; module
  · obtain ⟨s₀, δ₀, hs0, hs1, hmeq⟩ := E.midB_coords hm
    have hδ := E.midB_delta_ne hm hs0 hs1 hmeq
    filter_upwards [eventually_mem_Ioo_affine (s₀ := 1 - s₀) (B := -(δ₀ * h)) (by linarith)
      (by linarith)] with t ht
    refine ⟨1 - s₀ + t * -(δ₀ * h), δ₀, ht.1, ht.2, hδ, ?_⟩
    rw [hmeq]; module

/-- **The five-corner slide on `F_b`'s circle** (Lemmas 22.4, 22.6 (a)).  `F_a` has the single
middle `m` on the far side of its chord (`OppA`); the slide rim `v m a c b` has distinct depths
and is strictly unimodal or has a depth-separated pair at `u`; it has no double normal in space
perpendicular to `F_b` (`NoPersistHDN` along `e = h (v − b)`).  Then the set is Rupert. -/
theorem isRupert_slide5 (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³}
    (hMa : Ma = {m}) (hopp : OppA v w a m)
    (hinj : Function.Injective (fun i => ⟪quint v m a c b i, u⟫))
    (hz : UniOrSep (quint v m a c b) u)
    (hbad : NoPersistHDN (quint v m a c b) u (h • (v - b))) : IsRupert V := by
  classical
  have hm : m ∈ Ma := by rw [hMa]; exact mem_singleton_self m
  obtain ⟨s, δ, hs0, hs1, hδh, hmeq⟩ := E.opp_coords hm hopp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have Dab := E.dab_pos
  have Dba := E.dba_pos
  have Dac := E.det_a_pos E.hc E.hcA.1 E.hcA.2.1 E.hcA.2.2.1 E.hcA.2.2.2
  have Dcav := E.det_ac_pos E.hv E.haB.1.symm E.hcA.1.symm
  have Dcab := E.det_ac_pos E.hb E.hbA.2.2.1 E.hcB.1.symm
  have Dbcv := E.det_cb_pos E.hv E.hcA.1.symm E.hbA.1.symm
  have Dbca := E.det_cb_pos E.ha E.hcA.2.2.1.symm E.hbA.2.2.1.symm
  have Dbvc := E.det_b_pos E.hc E.hcA.1 E.hcA.2.1 E.hcB.1 E.hcB.2
  have Dbva : 0 < det3 (v - b) (a - b) u := by
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact Dba
  set e := h • (v - b) with he
  -- the tests involving `m`, as functions of the coordinates
  have T : ∀ X Y : ℝ³, SlideTest 1 X Y u e ↔ (0 < det3 X Y u ∨ (det3 X Y u = 0 ∧ 0 < det3 X Y e)) := by
    intro X Y; simp only [SlideTest, one_mul]
  have hmv : m - v = s • (a - v) + δ • u := by rw [hmeq]; abel
  -- the ten tests at the poked-out vertex
  have t01a : SlideTest 1 (m - v) (a - v) u e := by
    rw [T]; right; constructor
    · rw [hmv]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    · have : det3 (m - v) (a - v) e = -(δ * h) * det3 (a - v) (b - v) u := by
        rw [hmv, he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_pos (by linarith) Dab
  have t01c : SlideTest 1 (m - v) (c - v) u e := by
    rw [T]; left
    have : det3 (m - v) (c - v) u = s * det3 (a - v) (c - v) u := by
      rw [hmv]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]; exact mul_pos hs0 Dac
  have t01b : SlideTest 1 (m - v) (b - v) u e := by
    rw [T]; left
    have : det3 (m - v) (b - v) u = s * det3 (a - v) (b - v) u := by
      rw [hmv]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
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
    · have : det3 (a - m) (v - m) e = -(δ * h) * det3 (a - v) (b - v) u := by
        rw [hmeq, he]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_pos (by linarith) Dab
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
  refine isRupert_of_slideP V (insert w Mb) u e E.hu (quint v m a c b) (E.quint_mem hm)
    (E.quint_not_midB hm) (by norm_num) 1 one_ne_zero ?_ ?_ ?_ hinj hz hbad
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
    simp only [mem_insert, not_or] at hyM
    have hyv : y ≠ v := hyx 0
    have hym : y ≠ m := hyx 1
    have hya : y ≠ a := hyx 2
    have hyc : y ≠ c := hyx 3
    have hyb : y ≠ b := hyx 4
    have hyMa : y ∉ Ma := by rw [hMa, mem_singleton]; exact hym
    have hA := E.det_a_pos hy hyv hyM.1 hya hyMa
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    · refine st ?_
      have : det3 (m - v) (y - v) u = s * det3 (a - v) (y - v) u := by
        rw [hmv]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [this]; exact mul_pos hs0 hA
    · refine st ?_
      have : det3 (a - m) (y - m) u = (1 - s) * det3 (a - v) (y - v) u := by
        rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_pos (by linarith) hA
    · exact st (E.det_ac_pos hy hya hyc)
    · exact st (E.det_cb_pos hy hyc hyb)
    · exact st (E.det_b_pos hy hyv hyM.1 hyb hyM.2)
  · intro m' hm'
    filter_upwards [E.eventually_midB m' hm'] with t ⟨s', δ', hs0', hs1', hδ', hmeq'⟩
    exact ⟨4, s', δ', hs0', hs1', hδ', by simpa only [b4, quint_0, quint_4] using hmeq'⟩

end EdgeConf

end Minimality

end
