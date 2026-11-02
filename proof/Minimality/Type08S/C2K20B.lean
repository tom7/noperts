module

public import Minimality.Type08S.C2K20A

@[expose] public section


/-!
# K20 / B: the generalized Theorem 8.1 (`k20_truncPrism_gen`)

Copy of `isRupert_rightPrism_gen` (`Minimality/RightPrism.lean`) with: per-vertex top heights `hz j > 0`; the tilt
direction `v` given (generic for `p`); extra points certified only for the motion used (`hex`: for every spin `ψ` and
centre `M`, eventually in `λ`, for every `κ`, eventually in `ε`).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The rotation part of the motion: tilt `κ` about `rot90 v`-axis, spin `ψ` about `e_z`. -/
noncomputable def k20ω (κ ψ : ℝ) (v : ℝ²) : ℝ³ := !₂[-(κ * v 1), κ * v 0, ψ]
/-- The translation part: spin centre `M`, drift `-λ v`. -/
noncomputable def k20τ (ψ lam : ℝ) (M v : ℝ²) : ℝ³ := !₂[ψ * M 1 - lam * v 0, -(ψ * M 0) - lam * v 1, 0]

theorem k20_truncPrism_gen {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (hp : IsCcwPolygon p)
    (hz : ZMod k → ℝ) (hzp : ∀ j, 0 < hz j) (V : Finset ℝ³)
    (hVb : ∀ j, liftPt (p j) 0 ∈ V) (hVt : ∀ j, liftPt (p j) (hz j) ∈ V)
    (v : ℝ²) (hv1 : ∀ i, cross2 (p (i + 1) - p i) v ≠ 0) (hv2 : ∀ i j, i ≠ j → ⟪v, p i - p j⟫ ≠ 0)
    (hex : ∀ (ψ : ℝ) (M : ℝ²), ∀ᶠ lam in atTop, ∀ κ : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V,
      (∀ j, y ≠ liftPt (p j) 0) → (∀ j, y ≠ liftPt (p j) (hz j)) →
      TiltCert V (ez + ε • liftPt v 0) (k20ω κ ψ v) (k20τ ψ lam M v) y) : IsRupert V := by
  classical
  have hk := hp.1
  have hsm : ∀ j, cross2 (p j - p (j - 1)) v ≠ 0 := fun j => by
    simpa using hv1 (j - 1)
  set m : ℝ² := rot90 v with hm
  have hme : ∀ q : ℝ², ⟪m, q⟫ = -cross2 q v := by
    intro q; simp [hm, rot90, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hv0 : v ≠ 0 := by rintro rfl; exact hv1 0 (by simp [cross2])
  have hm0 : m ≠ 0 := by
    intro h0; apply hv0
    have e0 := congrArg (· 0) h0; have e1 := congrArg (· 1) h0
    simp [hm, rot90] at e0 e1
    ext i; fin_cases i <;> simp [e0, e1]
  obtain ⟨a, -, ha⟩ := exists_max_image univ (fun i => ⟪m, p i⟫) ⟨0, mem_univ _⟩
  obtain ⟨b, -, hb⟩ := exists_min_image univ (fun i => ⟪m, p i⟫) ⟨0, mem_univ _⟩
  have hloc : ∀ j, cross2 (p j - p (j - 1)) v < 0 → 0 < cross2 (p (j + 1) - p j) v →
      ∀ l, l ≠ j → ⟪m, p l⟫ < ⟪m, p j⟫ := by
    intro j h1 h2 l hl
    have i1 : 0 < ⟪m, p j - p (j - 1)⟫ := by rw [hme]; linarith
    have i2 : ⟪m, p (j + 1) - p j⟫ < 0 := by rw [hme]; linarith
    by_cases l1 : l = j - 1
    · subst l1; rw [inner_sub_right] at i1; linarith
    by_cases l3 : l = j + 1
    · subst l3; rw [inner_sub_right] at i2; linarith
    exact hp.lt_of_localMax hm0 i1.le i2.le l1 hl l3
  have hloc' : ∀ j, 0 < cross2 (p j - p (j - 1)) v → cross2 (p (j + 1) - p j) v < 0 →
      ∀ l, l ≠ j → ⟪m, p j⟫ < ⟪m, p l⟫ := by
    intro j h1 h2 l hl
    have i1 : 0 ≤ ⟪-m, p j - p (j - 1)⟫ := by rw [inner_neg_left, hme]; linarith
    have i2 : ⟪-m, p (j + 1) - p j⟫ ≤ 0 := by rw [inner_neg_left, hme]; linarith
    have hm0' : -m ≠ 0 := neg_ne_zero.mpr hm0
    by_cases l1 : l = j - 1
    · subst l1; rw [inner_neg_left, hme] at i1
      have := hme (p j - p (j - 1)); rw [inner_sub_right] at this; linarith
    by_cases l3 : l = j + 1
    · subst l3
      have := hme (p (j + 1) - p j); rw [inner_sub_right] at this; linarith
    have := hp.lt_of_localMax hm0' i1 i2 l1 hl l3
    rw [inner_neg_left, inner_neg_left] at this; linarith
  have hX : ∀ j, cross2 (p j - p (j - 1)) v < 0 → 0 < cross2 (p (j + 1) - p j) v → j = a := by
    intro j h1 h2; by_contra hne
    linarith [hloc j h1 h2 a (Ne.symm hne), ha j (mem_univ _)]
  have hY : ∀ j, 0 < cross2 (p j - p (j - 1)) v → cross2 (p (j + 1) - p j) v < 0 → j = b := by
    intro j h1 h2; by_contra hne
    linarith [hloc' j h1 h2 b (Ne.symm hne), hb j (mem_univ _)]
  have hab : a ≠ b := by
    intro hab
    have h1 := ha 1 (mem_univ _); have h2 := hb 1 (mem_univ _)
    have h3 := ha 0 (mem_univ _); have h4 := hb 0 (mem_univ _)
    rw [← hab] at h2 h4
    apply hv1 0
    have := hme (p (0 + 1) - p 0)
    rw [inner_sub_right, zero_add] at this
    simp only [zero_add]; linarith
  set X := p a with hXdef
  set Y := p b with hYdef
  have hXY : ⟪v, Y - X⟫ ≠ 0 := hv2 b a hab.symm
  set ψ : ℝ := if 0 < ⟪v, Y - X⟫ then 1 else -1 with hψ
  have hψT : 0 < ψ * ⟪v, Y - X⟫ := by
    rw [hψ]; split_ifs with hc
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp hc) hXY; linarith
  have hψ2 : ψ * ψ = 1 := by rw [hψ]; split_ifs <;> norm_num
  set M : ℝ² := (1 / 2 : ℝ) • (X + Y) with hM
  set A : ZMod k → ZMod k → ℝ := fun i j => ψ * cross2 (p (i + 1) - p i) (rot90 (p j - M))
  set s : ZMod k → ℝ := fun i => cross2 (p (i + 1) - p i) v
  obtain ⟨lam, hlam, hexl⟩ := ((show ∀ᶠ t in atTop, ∀ i j, s i < 0 → 0 < A i j + t * (-s i) from
    eventually_all.2 fun i => eventually_all.2 fun j => by
      by_cases hi : s i < 0
      · exact (eventually_atTop_pos _ _ (by linarith)).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => absurd h hi).and (hex ψ M)).exists
  obtain ⟨κ, hκ⟩ := (show ∀ᶠ t in atTop, ∀ i j, 0 < s i →
      0 < (A i j - lam * s i) + t * (hz j * s i) from
    eventually_all.2 fun i => eventually_all.2 fun j => by
      by_cases hi : 0 < s i
      · exact (eventually_atTop_pos _ _ (mul_pos (hzp j) hi)).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => absurd h hi).exists
  set ω : ℝ³ := k20ω κ ψ v with hω
  set τ : ℝ³ := k20τ ψ lam M v with hτ
  have hν : ∀ q z, proj_xy (cross ω (liftPt q z) + τ) =
      ψ • rot90 (q - M) - lam • v + (z * κ) • v := by
    intro q z; ext i; fin_cases i <;> simp [cross, liftPt, proj_xy, rot90, ω, τ, k20ω, k20τ] <;> ring
  have hνe : ∀ i j z, cross2 (p (i + 1) - p i) (proj_xy (cross ω (liftPt (p j) z) + τ)) =
      A i j + (z * κ - lam) * s i := by
    intro i j z; rw [hν]
    simp only [A, s, cross2_add_right, cross2_sub_right, cross2_smul_right]; ring
  have hνv : ∀ q z, cross2 (proj_xy (cross ω (liftPt q z) + τ)) v = -(ψ * ⟪q - M, v⟫) := by
    intro q z; rw [hν]; simp [cross2, rot90, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hνX : ∀ z, 0 < cross2 (proj_xy (cross ω (liftPt X z) + τ)) v := by
    intro z; rw [hνv]
    have : ⟪X - M, v⟫ = -(1 / 2) * ⟪v, Y - X⟫ := by
      rw [hM, real_inner_comm]; simp only [inner_sub_right, inner_smul_right, inner_add_right]
      simp; ring
    rw [this]; nlinarith
  have hνY : ∀ z, cross2 (proj_xy (cross ω (liftPt Y z) + τ)) v < 0 := by
    intro z; rw [hνv]
    have : ⟪Y - M, v⟫ = (1 / 2) * ⟪v, Y - X⟫ := by
      rw [hM, real_inner_comm]; simp only [inner_sub_right, inner_smul_right, inner_add_right]
      simp; ring
    rw [this]; nlinarith
  have hbot : ∀ i j, s i < 0 →
      0 < cross2 (p (i + 1) - p i) (proj_xy (cross ω (liftPt (p j) 0) + τ)) := by
    intro i j hi; rw [hνe]; have := hlam i j hi; nlinarith
  have htop : ∀ i j, 0 < s i →
      0 < cross2 (p (i + 1) - p i) (proj_xy (cross ω (liftPt (p j) (hz j)) + τ)) := by
    intro i j hi; rw [hνe]; have := hκ i j hi
    have e : A i j + (hz j * κ - lam) * s i = (A i j - lam * s i) + κ * (hz j * s i) := by ring
    rw [e]; exact this
  have hmemt' : ∀ j, liftPt (p j) (0 + hz j) ∈ V := fun j => by
    rw [zero_add]; exact hVt j
  have hmemb' : ∀ j, liftPt (p j) (hz j + -hz j) ∈ V := fun j => by
    rw [add_neg_cancel]; exact hVb j
  have hsj : ∀ j, s (j - 1) = cross2 (p j - p (j - 1)) v := fun j => by simp [s]
  have key : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt (p j) 0) ∧
      TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt (p j) (hz j)) := by
    intro j
    have hE := hp.cross2_edge_pos j
    have hzj := hzp j
    have bm : ∀ z, cross2 (p j - p (j - 1)) (proj_xy (cross ω (liftPt (p j) z) + τ)) =
        A (j - 1) j + (z * κ - lam) * s (j - 1) := by
      intro z; rw [← hνe]; simp
    have hbm : cross2 (p j - p (j - 1)) v < 0 →
        0 < cross2 (p j - p (j - 1)) (proj_xy (cross ω (liftPt (p j) 0) + τ)) := by
      intro hc; rw [bm]; have := hlam (j - 1) j (by rw [hsj]; exact hc); nlinarith
    have htm : 0 < cross2 (p j - p (j - 1)) v →
        0 < cross2 (p j - p (j - 1)) (proj_xy (cross ω (liftPt (p j) (hz j)) + τ)) := by
      intro hc; rw [bm]; have := hκ (j - 1) j (by rw [hsj]; exact hc)
      have e : A (j - 1) j + (hz j * κ - lam) * s (j - 1) =
          (A (j - 1) j - lam * s (j - 1)) + κ * (hz j * s (j - 1)) := by ring
      rw [e]; exact this
    have hrev : cross2 (p (j - 1) - p j) v = -cross2 (p j - p (j - 1)) v := by
      simp [cross2]; ring
    rcases lt_or_gt_of_ne (hsm j) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hv1 j) with h2 | h2
    · -- both edges in `B⁺`
      refine (k20_cert_flat V v ω τ (hVb _) (hVb _) hE (hbot j j h2) (hbm h1)).and ?_
      refine k20_cert_hidden V v ω τ (hVb _) (hmemb' _) (hVb _) hE ?_ ?_
      · nlinarith
      · nlinarith
    · -- `X`: the maximum of `⟪m, ·⟫`
      have hj := hX j h1 h2
      refine (k20_cert_up V v ω τ (hVb _) (hmemt' _) ?_ ?_ (hbm h1)).and
        (k20_cert_down V v ω τ (hmemb' _) (hVt _) ?_ (htop j j h2) ?_)
      · rw [hrev]; nlinarith
      · rw [hj, ← hXdef]; exact mul_pos (hzp a) (hνX 0)
      · nlinarith
      · rw [hj, ← hXdef]; nlinarith [mul_pos (hzp a) (hνX (hz a))]
    · -- `Y`: the minimum of `⟪m, ·⟫`
      have hj := hY j h1 h2
      refine (k20_cert_down V v ω τ (hmemt' _) (hVb _) ?_ (hbot j j h2) ?_).and
        (k20_cert_up V v ω τ (hVt _) (hmemb' _) ?_ ?_ (htm h1))
      · nlinarith
      · rw [hj, ← hYdef]; nlinarith [mul_pos (hzp b) (neg_pos.2 (hνY 0))]
      · rw [hrev]; nlinarith
      · rw [hj, ← hYdef]; nlinarith [mul_pos (hzp b) (neg_pos.2 (hνY (hz b)))]
    · -- both edges in `B⁻`
      refine (k20_cert_hidden V v ω τ (hVt _) (hmemt' _) (hVt _) hE ?_ ?_).and
        (k20_cert_flat V v ω τ (hVt _) (hVt _) hE (htop j j h2) (htm h1))
      · nlinarith
      · nlinarith
  obtain ⟨ε, hε, hεy⟩ := ((eventually_all.2 key).and (hexl κ)).exists
  refine isRupert_of_tiltCert _ (ez + ε • liftPt v 0) ?_ ω τ fun x hx => ?_
  · intro h0
    have := congrArg (· 2) h0
    simp [ez, liftPt] at this
  · by_cases hb0 : ∃ j, x = liftPt (p j) 0
    · obtain ⟨j, rfl⟩ := hb0; exact (hε j).1
    by_cases ht0 : ∃ j, x = liftPt (p j) (hz j)
    · obtain ⟨j, rfl⟩ := ht0; exact (hε j).2
    push Not at hb0 ht0
    exact hεy x hx hb0 ht0

end C2
end Type08Sp
end Minimality
