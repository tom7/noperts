module

public import Minimality.HFrame
public import Minimality.UniformTilt

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

theorem sgn_pos (t d : ℝ) (h : 0 < t * d) : 0 < (if 0 < t then (1 : ℝ) else -1) * d := by
  split_ifs with ht
  · rw [one_mul]; nlinarith
  · have : t < 0 := by
      rcases lt_or_gt_of_ne (show t ≠ 0 from fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h)
        with h1 | h1
      · exact h1
      · exact absurd h1 ht
    nlinarith

theorem sgn_sq (t : ℝ) : (if 0 < t then (1 : ℝ) else -1) * (if 0 < t then (1 : ℝ) else -1) = 1 := by
  split_ifs <;> norm_num

theorem sgn_cases (t : ℝ) : (if 0 < t then (1 : ℝ) else -1) = 1 ∨ (if 0 < t then (1 : ℝ) else -1) = -1 := by
  split_ifs <;> simp

/-- A unimodal sequence stays unimodal under `z ↦ ε z + K` for `ε = ±1`. -/
theorem IsCyclicUnimodal.affine_sign {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (K : ℝ) :
    IsCyclicUnimodal (fun i => ε * z i + K) := by
  rcases hε with rfl | rfl
  · -- a shift
    have hinj : Function.Injective (fun i => 1 * z i + K) := by
      intro i j hij; exact hz.1 (by simpa using hij)
    refine ⟨hinj, ?_⟩
    have := hz.2
    convert this using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · have h1 := hz.neg' hk
    have hinj : Function.Injective (fun i => -1 * z i + K) := by
      intro i j hij; exact hz.1 (by simpa using hij)
    refine ⟨hinj, ?_⟩
    have := h1.2
    convert this using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]


namespace HFrame
variable {v g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame v g u0 N fG)
include Fr

/-- The depth at the view `e − δ u₀` in frame coordinates. -/
theorem inner_uδ (δ : ℝ) (P : ℝ³) :
    ⟪P, hfE v g u0 - δ • u0⟫ = (hfΦ v g u0 fG P).x - δ * (hfΦ v g u0 fG P).z +
      (⟪v, hfE v g u0 - δ • u0⟫ - δ * ⟪g - v, u0⟫) := by
  have h1 : ⟪P, hfE v g u0 - δ • u0⟫ = ⟪P - v, hfE v g u0 - δ • u0⟫ + ⟪v, hfE v g u0 - δ • u0⟫ := by
    rw [← inner_add_left]; congr 1; abel
  have h2 : ⟪P - v, u0⟫ = ⟪P - g, u0⟫ + ⟪g - v, u0⟫ := by
    rw [← inner_add_left]; congr 1; abel
  rw [h1, inner_sub_right, real_inner_smul_right, h2]
  simp only [hfΦ]
  ring


/-- **The final assembly of a horizontal-end rim.**  If, for small `δ > 0`, the frame images of the
rim `x` pass all tests (with a common sign `σ`), the other points of `V` are strictly inside, the
rim depths are cyclically unimodal and every middle lies over a side, and the rim has no horizontal
double normal at the views `e − δ u₀` for arbitrarily small `δ`, then `V` is Rupert. -/
theorem rim_final {k : ℕ} [NeZero k] (hk : 3 ≤ k) (V M W : Finset ℝ³) (x : ZMod k → ℝ³)
    (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hxW : ∀ i, x i ∈ W) (σ : ℝ)
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
        0 < σ * tst (vw ⟪hfE v g u0, hfE v g u0⟫ ⟪u0, u0⟫ δ) (hfΦ v g u0 fG (x i))
          (hfΦ v g u0 fG (x (i + 1))) (hfΦ v g u0 fG (x j))) ∧
      (∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
        0 < σ * tst (vw ⟪hfE v g u0, hfE v g u0⟫ ⟪u0, u0⟫ δ) (hfΦ v g u0 fG (x i))
          (hfΦ v g u0 fG (x (i + 1))) (hfΦ v g u0 fG y)) ∧
      IsCyclicUnimodal (dep (fun i => hfΦ v g u0 fG (x i)) δ) ∧
      (∀ m ∈ M, ∃ i : ZMod k, ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
        m = x i + s • (x (i + 1) - x i) + δ' • (hfE v g u0 - δ • u0)))
    (hnd : ∃ᶠ δ in 𝓝[>] (0 : ℝ), NoHDNAt W (hfE v g u0 - δ • u0)) : IsRupert V := by
  obtain ⟨δ, hndδ, htest, hrest, huni, hmid⟩ := (hnd.and_eventually hev).exists
  set e := hfE v g u0 with he
  set uδ := e - δ • u0 with huδ
  set D0 := det3 e (-N) u0 with hD0
  set t := σ * D0 with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hconv : ∀ P Q S : ℝ³, 0 < σ * tst (vw ⟪e, e⟫ ⟪u0, u0⟫ δ) (hfΦ v g u0 fG P)
      (hfΦ v g u0 fG Q) (hfΦ v g u0 fG S) → 0 < det3 (Q - P) (S - P) (ε • uδ) := by
    intro P Q S h
    rw [HFrame.tst_hfΦ Fr, ← mul_assoc] at h
    rw [det3_smul_right]
    exact sgn_pos t _ h
  have hu : ε • uδ ≠ 0 := by
    intro h0
    have h1 : ⟪e, ε • uδ⟫ = 0 := by rw [h0]; simp
    have h2 : ⟪e, uδ⟫ = ⟪e, e⟫ := by
      rw [huδ, inner_sub_right, real_inner_smul_right, Fr.inner_e_u]; ring
    rw [real_inner_smul_right, h2] at h1
    have hE : 0 < ⟪e, e⟫ := Fr.hee
    rcases hεs with h | h <;> rw [h] at h1 <;> linarith
  refine isRupert_of_edgeView_uniform V M ∅ W (ε • uδ) hu hk x hxV hxM ?_ ?_ ?_ ?_ hxW ?_ ?_
  · intro i j hi hj
    exact hconv _ _ _ (htest i j hi hj)
  · intro y hy hyM hyD hyx i
    exact hconv _ _ _ (hrest y hy hyM hyx i)
  · have h1 : (fun i => ⟪x i, ε • uδ⟫) = fun i => ε * dep (fun i => hfΦ v g u0 fG (x i)) δ i +
        ε * (⟪v, e - δ • u0⟫ - δ * ⟪g - v, u0⟫) := by
      funext i
      rw [real_inner_smul_right, Fr.inner_uδ δ (x i)]
      simp only [dep]; ring
    rw [h1]
    exact huni.affine_sign (by omega) hεs _
  · have h2 : NoHDNAt W (ε • uδ) := by
      rcases hεs with h | h
      · rw [h, one_smul]; exact hndδ
      · rw [h, neg_one_smul]; exact hndδ.neg
    exact h2
  · intro m hm
    obtain ⟨i, s, δ', hs0, hs1, hδ', hmeq⟩ := hmid m hm
    refine ⟨i, s, ε * δ', hs0, hs1, ?_, ?_⟩
    · exact mul_ne_zero (by rcases hεs with h | h <;> rw [h] <;> norm_num) hδ'
    · rw [hmeq, smul_smul, show ε * δ' * ε = δ' by linear_combination δ' * hεε]
  · intro y hy
    exact absurd hy (Finset.notMem_empty y)

end HFrame

/-- **A middle over a chord, for small tilts.**  In the plane of `G`, a point `m` whose projection
along the circle direction at `δ = 0` lies strictly inside the chord `P Q` (at a nonzero distance
`δ'` from it) lies, for small `δ > 0`, over the chord at the view `e − δ u₀`: the coordinates
`x` and `z` solve `x_m = x_P + s (x_Q − x_P) + δ' E`, `z_m = z_P + s (z_Q − z_P) − δ' δ U`. -/
theorem chord_mid_ev {xP zP xQ zQ xm zm E U : ℝ} (hE : 0 < E) (hz : zQ ≠ zP)
    (h0 : 0 < (zm - zP) / (zQ - zP)) (h1 : (zm - zP) / (zQ - zP) < 1)
    (hd : xm - xP - ((zm - zP) / (zQ - zP)) * (xQ - xP) ≠ 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
      xm = xP + s * (xQ - xP) + δ' * E ∧ zm = zP + s * (zQ - zP) - δ' * δ * U := by
  set den : ℝ → ℝ := fun δ => (zQ - zP) + (U / E) * δ * (xQ - xP) with hden
  set num : ℝ → ℝ := fun δ => (zm - zP) + (U / E) * δ * (xm - xP) with hnum
  set sf : ℝ → ℝ := fun δ => num δ / den δ with hsf
  set df : ℝ → ℝ := fun δ => (xm - xP - sf δ * (xQ - xP)) / E with hdf
  have hden0 : den 0 ≠ 0 := by simp [hden]; exact sub_ne_zero.mpr hz
  have hcden : ContinuousAt den 0 := by fun_prop
  have hcnum : ContinuousAt num 0 := by fun_prop
  have hcs : ContinuousAt sf 0 := hcnum.div hcden hden0
  have hcd : ContinuousAt df 0 := by
    have : ContinuousAt (fun δ => xm - xP - sf δ * (xQ - xP)) 0 := by fun_prop
    exact this.div_const E
  have hs0 : sf 0 = (zm - zP) / (zQ - zP) := by simp [hsf, hnum, hden]
  have hd0 : df 0 = (xm - xP - ((zm - zP) / (zQ - zP)) * (xQ - xP)) / E := by
    simp only [hdf, hs0]
  have hdne : df 0 ≠ 0 := by rw [hd0]; exact div_ne_zero hd hE.ne'
  have ev1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < sf δ := hcs.eventually (lt_mem_nhds (by rw [hs0]; exact h0))
  have ev2 : ∀ᶠ δ in 𝓝 (0 : ℝ), sf δ < 1 := hcs.eventually (gt_mem_nhds (by rw [hs0]; exact h1))
  have ev3 : ∀ᶠ δ in 𝓝 (0 : ℝ), df δ ≠ 0 := hcd.eventually_ne hdne
  have ev4 : ∀ᶠ δ in 𝓝 (0 : ℝ), den δ ≠ 0 := hcden.eventually_ne hden0
  filter_upwards [nhdsWithin_le_nhds (ev1.and (ev2.and (ev3.and ev4)))] with δ ⟨h1', h2', h3', h4'⟩
  refine ⟨sf δ, df δ, h1', h2', h3', ?_, ?_⟩
  · simp only [hdf]; field_simp; ring
  · simp only [hdf, hsf, hnum] at *
    have hE' := hE.ne'
    field_simp
    simp only [hden] at h4' ⊢
    field_simp
    ring

namespace HFrame
variable {v g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame v g u0 N fG)
include Fr

/-- **A vertex of `G` over a chord of `G`, for small tilts.** -/
theorem mid_ev {P Q m : ℝ³} (hP : fG P = 0) (hQ : fG Q = 0) (hm : fG m = 0)
    (hz : (hfΦ v g u0 fG Q).z ≠ (hfΦ v g u0 fG P).z)
    (h0 : 0 < ((hfΦ v g u0 fG m).z - (hfΦ v g u0 fG P).z) /
      ((hfΦ v g u0 fG Q).z - (hfΦ v g u0 fG P).z))
    (h1 : ((hfΦ v g u0 fG m).z - (hfΦ v g u0 fG P).z) /
      ((hfΦ v g u0 fG Q).z - (hfΦ v g u0 fG P).z) < 1)
    (hd : (hfΦ v g u0 fG m).x - (hfΦ v g u0 fG P).x -
      (((hfΦ v g u0 fG m).z - (hfΦ v g u0 fG P).z) /
        ((hfΦ v g u0 fG Q).z - (hfΦ v g u0 fG P).z)) *
      ((hfΦ v g u0 fG Q).x - (hfΦ v g u0 fG P).x) ≠ 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ s δ' : ℝ, 0 < s ∧ s < 1 ∧ δ' ≠ 0 ∧
      m = P + s • (Q - P) + δ' • (hfE v g u0 - δ • u0) := by
  have hE : 0 < ⟪hfE v g u0, hfE v g u0⟫ := Fr.hee
  have hz' : (hfΦ v g u0 fG Q).z - (hfΦ v g u0 fG P).z ≠ 0 := sub_ne_zero.mpr hz
  filter_upwards [chord_mid_ev (U := ⟪u0, u0⟫) hE hz h0 h1 hd] with δ ⟨s, δ', hs0, hs1, hδ', hx, hz2⟩
  exact ⟨s, δ', hs0, hs1, hδ', Fr.mid_of_coords s δ' δ hP hQ hm hx hz2⟩

end HFrame

end Minimality
end
