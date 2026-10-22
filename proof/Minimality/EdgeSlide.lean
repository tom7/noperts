module

public import Minimality.EdgeConf

@[expose] public section

/-!
# One realizing circle: the slide of `K_v` (`FEWER-FACES-PROOFS.md` §22.1, §22.3)

In an `EdgeConf` whose closing is realized on `F_a`'s circle (`RealB`: the middles of `F_b` lie
on `w`'s side of the chord `b v`), the views `u + t h (v − a)` (`t → 0⁺`) stay in `F_a`'s plane:
`F_a` stays edge-on with `w` and its middles over the open side `(v, a)`, and the middles of
`F_b` are hidden at first order (Lemma 22.1).  With distinct depths and `K_v` unimodal at `u`,
the set is Rupert unless the rim has a double normal in space perpendicular to `F_a`
(`NoPersistHDN`, Lemma 22.3: only class `H_a` is left).

* `EdgeConf.isRupert_slideA` (Lemma 22.3).
* `strictUnimodal_of_cyclic`, `EdgeConf.strict_of_NWS4`: unimodality forms.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem strictUnimodal_of_cyclic {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (h : IsCyclicUnimodal z) : StrictUnimodal z :=
  ⟨fun i e => zmod_ne_add_one hk i (h.1 e), h.2⟩

theorem quad_inner' (p₀ p₁ p₂ p₃ u : ℝ³) :
    (fun i => ⟪quad p₀ p₁ p₂ p₃ i, u⟫) = quad ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- Eventually along `t → 0⁺`, an affine function of `t` positive at `0` stays in `(0, 1)` if
its value at `0` is. -/
theorem eventually_mem_Ioo_affine {s₀ B : ℝ} (h0 : 0 < s₀) (h1 : s₀ < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < s₀ + t * B ∧ s₀ + t * B < 1 := by
  filter_upwards [eventually_pos_affine (A := s₀) (B := B) (Or.inl h0),
    eventually_pos_affine (A := 1 - s₀) (B := -B) (Or.inl (by linarith))] with t ht1 ht2
  exact ⟨ht1, by linarith⟩

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

theorem quad_mem (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) (i : ZMod 4) :
    quad v a c b i ∈ V := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  exacts [E.hv, E.ha, E.hc, E.hb]

/-- A middle of `F_a` is off the segment `[v, a]` (`δ ≠ 0`). -/
theorem midA_delta_ne (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma)
    {s δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hmeq : m = v + s • (a - v) + δ • u) : δ ≠ 0 := by
  rintro rfl
  rw [zero_smul, add_zero] at hmeq
  obtain ⟨hmv, -, hma⟩ := E.hMa' m hm
  exact E.noSeg v E.hv a E.ha m (E.hMa hm) hmv hma s hs0 hs1 hmeq

theorem midB_delta_ne (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Mb)
    {s δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hmeq : m = v + s • (b - v) + δ • u) : δ ≠ 0 := by
  rintro rfl
  rw [zero_smul, add_zero] at hmeq
  obtain ⟨hmv, -, hmb⟩ := E.hMb' m hm
  exact E.noSeg v E.hv b E.hb m (E.hMb hm) hmv hmb s hs0 hs1 hmeq

/-- The middles of `F_a` (and `w`) lie over the open side `(v, a)` at the views
`u + t e` of `F_a`'s circle, `e = h (v − a)`, for small `t > 0`. -/
theorem eventually_midA (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    ∀ m ∈ insert w Ma, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = v + s • (a - v) + δ • (u + t • (h • (v - a))) := by
  intro m hm
  rcases mem_insert.mp hm with rfl | hm
  · have hh2 : 0 < h * h := mul_self_pos.mpr E.hh
    filter_upwards [eventually_pos_affine (A := 0) (B := h * h) (Or.inr ⟨rfl, hh2⟩),
      eventually_pos_affine (A := 1) (B := -(h * h)) (Or.inl one_pos)] with t ht1 ht2
    refine ⟨t * (h * h), h, by linarith, by linarith, E.hh, ?_⟩
    rw [E.hw]; module
  · obtain ⟨s₀, δ₀, hs0, hs1, hmeq⟩ := E.midA_coords hm
    have hδ := E.midA_delta_ne hm hs0 hs1 hmeq
    filter_upwards [eventually_mem_Ioo_affine (B := δ₀ * h) hs0 hs1] with t ht
    refine ⟨s₀ + t * (δ₀ * h), δ₀, ht.1, ht.2, hδ, ?_⟩
    rw [hmeq]; module

/-- **Lemma 22.3 (the slide of `K_v` on `F_a`'s circle).**  If the closing is realized on
`F_a`'s circle (`RealB`), the depths of `v, a, c, b` are distinct and `K_v` has no weak saddle,
and the rim has no double normal in space perpendicular to `F_a` (`NoPersistHDN`), then the
set is Rupert. -/
theorem v_ne_w (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : v ≠ w := by
  intro e
  have : h • u = 0 := by
    have := E.hw; rw [← e] at this
    have h2 : v + h • u - v = 0 := by rw [← this, sub_self]
    simpa using h2
  exact smul_ne_zero E.hh E.hu this

theorem quad_not_midA (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) (i : ZMod 4) :
    quad v a c b i ∉ insert w Ma := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, not_or]
  · exact ⟨E.v_ne_w, fun hm => (E.hMa' v hm).1 rfl⟩
  · exact ⟨E.haB.2.1, fun hm => (E.hMa' a hm).2.2 rfl⟩
  · exact ⟨E.hcA.2.1, E.hcA.2.2.2⟩
  · exact ⟨E.hbA.2.1, E.hbA.2.2.2⟩

/-- A middle of `F_b`, realized on `F_a`'s circle, is hidden at first order along
`e = h (v − a)`. -/
theorem slideTest_midB (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb)
    (hRB : RealB v w b Mb) {y : ℝ³} (hy : y ∈ Mb) :
    SlideTest 1 (v - b) (y - b) u (h • (v - a)) := by
  obtain ⟨k, hk, hk'⟩ := hRB y hy
  have hd : ∀ X, det3 (v - b) (y - b) X = k * det3 (v - b) (w - b) X := by
    intro X; rw [det3, hk', real_inner_smul_left]; rfl
  have hw := E.hw
  right
  constructor
  · rw [hd, hw]
    have : det3 (v - b) (v + h • u - b) u = 0 := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, mul_zero]
  · rw [one_mul, hd, hw]
    have e : det3 (v - b) (v + h • u - b) (h • (v - a)) = (h * h) * det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_pos hk (mul_pos (mul_self_pos.mpr E.hh) E.dba_pos)

/-- **Lemma 22.3 (the slide of `K_v` on `F_a`'s circle).**  If the closing is realized on
`F_a`'s circle (`RealB`), the depths of `v, a, c, b` are distinct and `K_v` has no weak saddle,
and the rim has no double normal in space perpendicular to `F_a` (`NoPersistHDN`), then the
set is Rupert. -/
theorem isRupert_slideA (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb)
    (hRB : RealB v w b Mb) (hinj : Function.Injective (fun i => ⟪quad v a c b i, u⟫))
    (hz : NWS4 (quad ⟪v, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hbad : NoPersistHDN (quad v a c b) u (h • (v - a))) : IsRupert V := by
  classical
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hcyc := E.cyc
  refine isRupert_of_slideP V (insert w Ma) u (h • (v - a)) E.hu (quad v a c b) E.quad_mem
    E.quad_not_midA (by norm_num) 1 one_ne_zero
    (fun i j hi hj => Or.inl (by rw [one_mul]; exact hcyc i j hi hj)) ?_ ?_ hinj ?_ hbad
  · intro y hy hyM hyx i
    simp only [mem_insert, not_or] at hyM
    have hyv : y ≠ v := hyx 0
    have hya : y ≠ a := hyx 1
    have hyc : y ≠ c := hyx 2
    have hyb : y ≠ b := hyx 3
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    · exact Or.inl (by rw [one_mul]; exact E.det_a_pos hy hyv hyM.1 hya hyM.2)
    · exact Or.inl (by rw [one_mul]; exact E.det_ac_pos hy hya hyc)
    · exact Or.inl (by rw [one_mul]; exact E.det_cb_pos hy hyc hyb)
    · by_cases hyB : y ∈ Mb
      · exact E.slideTest_midB hRB hyB
      · exact Or.inl (by rw [one_mul]; exact E.det_b_pos hy hyv hyM.1 hyb hyB)
  · intro m hm
    filter_upwards [E.eventually_midA m hm] with t ⟨s, δ, hs0, hs1, hδ, hmeq⟩
    exact ⟨0, s, δ, hs0, hs1, hδ, by simpa only [a0, quad_0, quad_1] using hmeq⟩
  · left
    rw [quad_inner'] at hinj ⊢
    exact strictUnimodal_of_cyclic (by norm_num) (isCyclicUnimodal_of_NWS4 hinj hz)

end EdgeConf

end Minimality

end
