module

public import Minimality.Type21SAT.Lex2

@[expose] public section

/-!
# Type 21 three valued bridge (L3), part 1: the geometric leaves, free of the CNF

Standalone statements about facets `S0xFac` (no `V`, no `rho`).  They are what the rule rows
(family 17) and the witness rows (family 19) of the cores A and B need:

* `TopeEx F M sg`: a tilt `v` realizing the sign vector `sg` on the facets of the mask `M`.
* `rule_leaf` (Lemma Tilt): state of a rule + a tope + a robust cycle give Rupert.  `u != 0` comes from
  one strict facing.
* `tope_of_lex2` and `witness0/1/2`: the witness lemma (a difference `d` zero on the facets of `Z`
  and signed on the rest gives the tope `+-d + delta w`), three kinds.
* `neg_of_parallel`: two distinct facets of the polytope with proportional normals have a negative
  proportionality constant (so `<N t1, N t0> < 0`), needed by `witness2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- A tope on the mask `M`: some tilt `v` has the signs `sg` (true = positive) on every facet of `M`. -/
def TopeEx (F : S0xFac m S x) (M sg : Fin m → Bool) : Prop :=
  ∃ v : ℝ³, ∀ t, M t = true →
    (sg t = true → 0 < ⟪F.N t, v⟫) ∧ (sg t = false → ⟪F.N t, v⟫ < 0)

/-- **Lemma Tilt, as the rule rows use it.**  At a view `u` whose facings are strict off the mask `M`
(up if `pp` says up) and zero on `M` (where `pp` is the tilt sign `sg`), with a tope `sg` on `M`, with
at least one strict facing (so `u != 0`), and a cycle that is a silhouette of `pp` with robustly
unimodal depths, the point set is Rupert. -/
theorem rule_leaf {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} {pp M sg : Fin m → Bool} {u : ℝ³} (hc : Function.Injective c)
    (hk : 3 ≤ k) (hcyc : S0xCycOK S c pp)
    (hoff : ∀ t, M t = false → (pp t = true → 0 < ⟪F.N t, u⟫) ∧ (pp t = false → ⟪F.N t, u⟫ < 0))
    (hon : ∀ t, M t = true → ⟪F.N t, u⟫ = 0 ∧ pp t = sg t)
    (hstrict : ∃ t, M t = false) (ht : TopeEx F M sg)
    (hU : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨v, hv⟩ := ht
  obtain ⟨t0, ht0⟩ := hstrict
  have hu : u ≠ 0 := by
    intro h0
    have := hoff t0 ht0
    cases hp : pp t0 <;> simp [hp, h0] at this
  refine s0x_tope_rupert F hx v hc hk hcyc hu ?_ hU
  intro t
  by_cases hM : M t = true
  · obtain ⟨h0, hps⟩ := hon t hM
    obtain ⟨h1, h2⟩ := hv t hM
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have : sg t = true := hps ▸ hp
      exact Or.inr ⟨h0, h1 this⟩
    · have : sg t = false := hps ▸ hp
      exact Or.inr ⟨by rw [h0]; ring, by linarith [h2 this]⟩
  · have hM' : M t = false := by simpa using hM
    obtain ⟨h1, h2⟩ := hoff t hM'
    exact ⟨fun hp => Or.inl (h1 hp), fun hp => Or.inl (by linarith [h2 hp])⟩

/-- **Witness lemma, general form.**  If `(a, b)` has the lexicographic signs `sg` on the facets of `M`,
then `a + delta b` has them strictly for small `delta > 0`: the tope exists. -/
theorem tope_of_lex2 (F : S0xFac m S x) (M sg : Fin m → Bool) (a b : ℝ³)
    (h : ∀ t, M t = true →
      (sg t = true → h21b_LP ⟪F.N t, a⟫ ⟪F.N t, b⟫) ∧
      (sg t = false → h21b_LP (-⟪F.N t, a⟫) (-⟪F.N t, b⟫))) : TopeEx F M sg := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t, M t = true →
      (sg t = true → 0 < ⟪F.N t, a + δ • b⟫) ∧ (sg t = false → ⟪F.N t, a + δ • b⟫ < 0) := by
    refine eventually_all.2 fun t => ?_
    by_cases hM : M t = true
    · obtain ⟨h1, h2⟩ := h t hM
      by_cases hs : sg t = true
      · filter_upwards [eventually_pos_affine (h1 hs)] with δ hδ
        refine fun _ => ⟨fun _ => ?_, fun h' => absurd hs (by simp [h'])⟩
        rw [inner_add_right, inner_smul_right]; exact hδ
      · have hs' : sg t = false := by simpa using hs
        filter_upwards [eventually_pos_affine (h2 hs')] with δ hδ
        refine fun _ => ⟨fun h' => absurd h' hs, fun _ => ?_⟩
        rw [inner_add_right, inner_smul_right]; linarith
    · exact Eventually.of_forall fun δ h' => absurd h' hM
  obtain ⟨δ, hδ⟩ := hev.exists
  exact ⟨a + δ • b, hδ⟩

/-- Witness kind 0 (all facets of `M` strict at `d`, `k = 2` with different signs, or any strict
`d`): `v = eps d`. -/
theorem witness0 (F : S0xFac m S x) (M sg : Fin m → Bool) (d : ℝ³) (eps : ℝ)
    (hs : ∀ t, M t = true →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TopeEx F M sg := by
  refine tope_of_lex2 F M sg (eps • d) 0 fun t ht => ?_
  obtain ⟨h1, h2⟩ := hs t ht
  simp only [inner_smul_right, inner_zero_right, neg_zero]
  exact ⟨fun hp => Or.inl (h1 hp), fun hp => Or.inl (by linarith [h2 hp])⟩

/-- Witness kind 1 (zero on one facet `t0`): `d` is zero on `t0`, signed `eps * sg` on the other facets
of `M`; the tilt is `eps d + delta (+-N t0)`. -/
theorem witness1 (F : S0xFac m S x) (M sg : Fin m → Bool) (d : ℝ³) (eps : ℝ) (t0 : Fin m)
    (h0 : M t0 = true) (hN : ⟪F.N t0, F.N t0⟫ ≠ 0) (hz : ⟪F.N t0, d⟫ = 0)
    (hs : ∀ t, M t = true → t ≠ t0 →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TopeEx F M sg := by
  have hpos : 0 < ⟪F.N t0, F.N t0⟫ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hN)
  refine tope_of_lex2 F M sg (eps • d) (if sg t0 then F.N t0 else -F.N t0) fun t ht => ?_
  by_cases e : t = t0
  · subst e
    cases hs0 : sg t with
    | true =>
      simp only [inner_smul_right, hz, hs0, if_true, mul_zero, neg_zero]
      exact ⟨fun _ => Or.inr ⟨rfl, hpos⟩, fun h => absurd h (by simp)⟩
    | false =>
      simp only [inner_smul_right, hz, hs0, Bool.false_eq_true, if_false, inner_neg_right, mul_zero,
        neg_zero, neg_neg]
      exact ⟨fun h => absurd h (by simp), fun _ => Or.inr ⟨rfl, hpos⟩⟩
  · obtain ⟨h1, h2⟩ := hs t ht e
    simp only [inner_smul_right]
    exact ⟨fun hp => Or.inl (h1 hp), fun hp => Or.inl (by linarith [h2 hp])⟩

/-- Witness kind 2 (zero on two facets `t0, t1` with different signs): when `<N t1, N t0> < 0` the
tilt `+-N t0` has the two signs. -/
theorem witness2 (F : S0xFac m S x) (M sg : Fin m → Bool) (d : ℝ³) (eps : ℝ) (t0 t1 : Fin m)
    (h0 : M t0 = true) (h1 : M t1 = true) (hne : t0 ≠ t1) (hsg : sg t0 ≠ sg t1)
    (hN : 0 < ⟪F.N t0, F.N t0⟫) (hneg : ⟪F.N t1, F.N t0⟫ < 0)
    (hz0 : ⟪F.N t0, d⟫ = 0) (hz1 : ⟪F.N t1, d⟫ = 0)
    (hs : ∀ t, M t = true → t ≠ t0 → t ≠ t1 →
      (sg t = true → 0 < eps * ⟪F.N t, d⟫) ∧ (sg t = false → eps * ⟪F.N t, d⟫ < 0)) :
    TopeEx F M sg := by
  refine tope_of_lex2 F M sg (eps • d) (if sg t0 then F.N t0 else -F.N t0) fun t ht => ?_
  by_cases e0 : t = t0
  · subst e0
    cases hs0 : sg t with
    | true =>
      simp only [inner_smul_right, hz0, hs0, if_true, mul_zero, neg_zero]
      exact ⟨fun _ => Or.inr ⟨rfl, hN⟩, fun h => absurd h (by simp)⟩
    | false =>
      simp only [inner_smul_right, hz0, hs0, Bool.false_eq_true, if_false, inner_neg_right, mul_zero,
        neg_zero, neg_neg]
      exact ⟨fun h => absurd h (by simp), fun _ => Or.inr ⟨rfl, hN⟩⟩
  by_cases e1 : t = t1
  · subst e1
    have h1' : sg t0 = !sg t := by cases a : sg t0 <;> cases b : sg t <;> simp_all
    cases hs0 : sg t0 with
    | true =>
      have : sg t = false := by simpa [hs0] using h1'
      simp only [inner_smul_right, hz1, hs0, if_true, mul_zero, neg_zero]
      exact ⟨fun h => absurd h (by simp [this]), fun _ => Or.inr ⟨rfl, by linarith⟩⟩
    | false =>
      have : sg t = true := by simpa [hs0] using h1'
      simp only [inner_smul_right, hz1, hs0, Bool.false_eq_true, if_false, inner_neg_right,
        mul_zero, neg_zero, neg_neg]
      exact ⟨fun _ => Or.inr ⟨rfl, by linarith⟩, fun h => absurd h (by simp [this])⟩
  · obtain ⟨q1, q2⟩ := hs t ht e0 e1
    simp only [inner_smul_right]
    exact ⟨fun hp => Or.inl (q1 hp), fun hp => Or.inl (by linarith [q2 hp])⟩

/-- **Convexity.**  A facet `t1` with a vertex outside the facet `t0` cannot have a normal that is a
positive multiple of the normal of `t0` (`S t0` nonempty): the maximum of `f t0` over the points
would be attained on all of `S t1`. -/
theorem no_same_dir (F : S0xFac m S x) {t0 t1 : Fin m} {c : ℝ} (hc : 0 < c)
    (hN : F.N t1 = c • F.N t0) (hne : (S t0).Nonempty) (hsub : ¬ S t1 ⊆ S t0) : False := by
  apply hsub
  intro i hi
  obtain ⟨j, hj⟩ := hne
  by_contra hni
  have e1 : F.f t0 (x j) = 0 := F.zero t0 j hj
  have e2 : F.f t0 (x i) < 0 := F.neg t0 i hni
  have a1 := F.hN t1 (x i) (x j)
  rw [hN, inner_smul_left] at a1
  have a2 := F.hN t0 (x i) (x j)
  have z1 : F.f t1 (x i) = 0 := F.zero t1 i hi
  have l1 := F.le t1 j
  simp only [conj_trivial] at a1
  nlinarith

/-- **Opposite normals.**  If `N t1 = r N t0` with both normals nonzero, `S t0` nonempty and `S t1` not inside
`S t0`, then `r < 0`, so `<N t1, N t0> < 0`. -/
theorem neg_of_parallel (F : S0xFac m S x) {t0 t1 : Fin m} {r : ℝ}
    (hN : F.N t1 = r • F.N t0) (h0 : ⟪F.N t0, F.N t0⟫ ≠ 0) (h1 : ⟪F.N t1, F.N t1⟫ ≠ 0)
    (hne : (S t0).Nonempty) (hsub : ¬ S t1 ⊆ S t0) : ⟪F.N t1, F.N t0⟫ < 0 := by
  have hpos : 0 < ⟪F.N t0, F.N t0⟫ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm h0)
  have hr : r ≠ 0 := by
    intro hr0
    apply h1
    rw [hN, hr0, zero_smul, inner_zero_left]
  rw [hN, inner_smul_left]
  simp only [conj_trivial]
  rcases lt_or_gt_of_ne hr with h | h
  · nlinarith
  · exact absurd (no_same_dir F h hN hne hsub) id

end H21
end Minimality

