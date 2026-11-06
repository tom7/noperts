module

public import Mathlib
public import MinimalityExtra
public import MinimalityExtra.MetricUniform

/-!
# Face-normal views (Lemma FN (iii)): proof

A face `F` perpendicular to the view `u` at the minimum depth, every other point at positive
depth over the polygon `P(F)`, and a tilt `d` with `N_i · d > 0` on all sides touched by the
positives: at `u + ε d` the positives are hidden and the rim is `F`, whose depths `ε⟪d, ·⟫`
are cyclically unimodal (`coplanarRimDepthUnimodal`).
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra
open scoped RealInnerProductSpace
open Filter Topology

lemma fn_inner (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- For `e, d ⊥ u`: `det(e, w, d) |u|² = det(e, u, d) ⟪w, u⟫`. -/
lemma fn_key (e w d u : ℝ³) (he : ⟪e, u⟫ = 0) (hd : ⟪d, u⟫ = 0) :
    det3 e w d * ⟪u, u⟫ = det3 e u d * ⟪w, u⟫ := by
  have id : det3 e w d * ⟪u, u⟫ = det3 e u d * ⟪w, u⟫ + det3 u w d * ⟪e, u⟫ +
      det3 e w u * ⟪d, u⟫ := by
    simp only [det3, fn_inner]; ring
  rw [he, hd] at id; linarith

lemma fn_cross_perp (u d : ℝ³) : ⟪cross u d, u⟫ = 0 := by
  simp only [fn_inner, cross]; simp; ring

/-- A vector orthogonal to `u`, `d`, `u × d` (with `u ⊥ d`, both nonzero) is zero. -/
lemma fn_zero (u d g : ℝ³) (hu : u ≠ 0) (hd : d ≠ 0) (hud : ⟪u, d⟫ = 0)
    (hgu : ⟪g, u⟫ = 0) (hgd : ⟪g, d⟫ = 0) (hgw : ⟪g, cross u d⟫ = 0) : g = 0 := by
  have gram : (det3 u d g) ^ 2 = ⟪g, g⟫ * (⟪u, u⟫ * ⟪d, d⟫ - ⟪u, d⟫ ^ 2) -
      ⟪g, u⟫ * (⟪g, u⟫ * ⟪d, d⟫ - ⟪u, d⟫ * ⟪g, d⟫) +
      ⟪g, d⟫ * (⟪g, u⟫ * ⟪u, d⟫ - ⟪u, u⟫ * ⟪g, d⟫) := by
    simp only [det3, fn_inner]; ring
  have hdet : det3 u d g = 0 := by
    have : ⟪g, cross u d⟫ = det3 u d g := by simp only [det3, fn_inner, cross]; simp; ring
    rw [← this]; exact hgw
  rw [hdet, hud, hgu, hgd] at gram
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu
  have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.2 hd
  have hgg : ⟪g, g⟫ = 0 := by
    have : ⟪g, g⟫ * (⟪u, u⟫ * ⟪d, d⟫) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_pos huu hdd).ne'
  exact inner_self_eq_zero.1 hgg

lemma fn_ev (D E : ℝ) (hD : 0 < D) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D + ε * E := by
  have hc : Continuous (fun ε : ℝ => D + ε * E) := by fun_prop
  have := (hc.tendsto 0).eventually (lt_mem_nhds (show (0:ℝ) < D + 0 * E by simpa using hD))
  exact (nhdsWithin_le_nhds this)

lemma fn_zmod (k : ℕ) [NeZero k] (hk : 3 ≤ k) : (2 : ZMod k) ≠ 0 ∧ (2 : ZMod k) ≠ 1 := by
  have h2 : ((2 : ℕ) : ZMod k) = ((2 : ℕ) : ZMod k) := rfl
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod k) = ((0 : ℕ) : ZMod k) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at h'
    omega
  · intro h
    have h' : ((2 : ℕ) : ZMod k) = ((1 : ℕ) : ZMod k) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    omega

theorem faceNormalHalfPlane : FaceNormalHalfPlane := by
  intro x k _ lab u d hk hinj hplane hF hpos hd0 hdu hN
  -- basic facts
  obtain ⟨h20, h21⟩ := fn_zmod k hk
  have hu0 : u ≠ 0 := by
    intro h
    have := hF 0 2 h20 (by simpa using h21)
    simp [det3, h] at this
  have heu : ∀ i, ⟪x (lab (i + 1)) - x (lab i), u⟫ = 0 := by
    intro i; rw [inner_sub_left, hplane, hplane]; simp
  set w : ℝ³ := cross u d with hw
  have hwu : ⟪w, u⟫ = 0 := fn_cross_perp u d
  have hud : ⟪u, d⟫ = 0 := by rw [real_inner_comm]; exact hdu
  let dt : ℝ → ℝ³ := fun t => d + t • w
  have hdtu : ∀ t, ⟪dt t, u⟫ = 0 := by
    intro t; simp only [dt, inner_add_left, inner_smul_left, hdu, hwu]; simp
  -- the tilt conditions persist for small t
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, (∃ m, (∀ j, m ≠ lab j) ∧
        det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u = 0) →
      0 < det3 (x (lab (i + 1)) - x (lab i)) u (dt t) := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : ∃ m, (∀ j, m ≠ lab j) ∧
        det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u = 0
    · have h0 := hN i hi
      have e : ∀ t : ℝ, det3 (x (lab (i + 1)) - x (lab i)) u (dt t) =
          det3 (x (lab (i + 1)) - x (lab i)) u d + t * det3 (x (lab (i + 1)) - x (lab i)) u w := by
        intro t; simp only [dt, det3]; simp; ring
      simp only [e]
      exact (fn_ev _ _ h0).mono fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hi
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev1
  -- genericity: injective depths
  let root : ZMod k × ZMod k → ℝ := fun p =>
    -⟪x (lab p.1) - x (lab p.2), d⟫ / ⟪x (lab p.1) - x (lab p.2), w⟫
  obtain ⟨t, htI, htS⟩ := (Set.Ioo_infinite hδ).exists_notMem_finset
    (Finset.univ.image root)
  have ht0 : 0 < t := htI.1
  have hinj' : ∀ a b : ZMod k, a ≠ b → ⟪x (lab a), dt t⟫ ≠ ⟪x (lab b), dt t⟫ := by
    intro a b hab heq
    have hg : x (lab a) - x (lab b) ≠ 0 := by
      intro h
      have hxe : x (lab a) = x (lab b) := sub_eq_zero.1 h
      have ha2 : a + 2 ≠ a := fun h' => h20 (by simpa using h')
      have ha21 : a + 2 ≠ a + 1 := fun h' => h21 (by simpa using h')
      by_cases hb : b = a + 1
      · have := hF a (a + 2) ha2 ha21
        rw [← hb, hxe] at this
        simp [det3] at this
      · have := hF a b (Ne.symm hab) hb
        rw [hxe] at this
        simp [det3] at this
    have h1 : ⟪x (lab a) - x (lab b), d⟫ + t * ⟪x (lab a) - x (lab b), w⟫ = 0 := by
      have : ⟪x (lab a) - x (lab b), dt t⟫ = 0 := by
        rw [inner_sub_left]; exact sub_eq_zero.2 heq
      simpa only [dt, inner_add_right, inner_smul_right] using this
    by_cases hgw : ⟪x (lab a) - x (lab b), w⟫ = 0
    · rw [hgw] at h1
      have hgd : ⟪x (lab a) - x (lab b), d⟫ = 0 := by linarith
      have hgu : ⟪x (lab a) - x (lab b), u⟫ = 0 := by
        rw [inner_sub_left, hplane, hplane]; simp
      exact hg (fn_zero u d _ hu0 hd0 hud hgu hgd hgw)
    · apply htS
      rw [Finset.mem_image]
      refine ⟨(a, b), Finset.mem_univ _, ?_⟩
      simp only [root]
      field_simp
      linarith
  have hN' := hsub htI
  -- smallness of ε
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (i : ZMod k) (m : Fin 7), m ≠ lab i → m ≠ lab (i + 1) →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (u + ε • dt t) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun m => ?_
    have e : ∀ ε : ℝ, det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (u + ε • dt t) =
        det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u +
          ε * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (dt t) := by
      intro ε; simp only [det3]; simp; ring
    simp only [e]
    by_cases hm : ∃ j, m = lab j
    · obtain ⟨j, rfl⟩ := hm
      by_cases hc : lab j = lab i ∨ lab j = lab (i + 1)
      · exact Filter.Eventually.of_forall fun ε h1 h2 => by
          rcases hc with h | h
          · exact absurd h h1
          · exact absurd h h2
      · refine (fn_ev _ _ (hF i j (fun h => hc (Or.inl (by rw [h])))
          (fun h => hc (Or.inr (by rw [h]))))).mono fun ε hε _ _ => hε
    · push Not at hm
      obtain ⟨hpd, hge⟩ := hpos m hm
      rcases (hge i).lt_or_eq with hlt | heq
      · exact (fn_ev _ _ hlt).mono fun ε hε _ _ => hε
      · have hE := hN' i ⟨m, hm, heq.symm⟩
        have hk := fn_key (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (dt t) u (heu i)
          (hdtu t)
        have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu0
        have hwp : 0 < ⟪x m - x (lab i), u⟫ := by
          rw [inner_sub_left, hplane]; simpa using hpd
        have : 0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (dt t) := by
          have h3 : 0 < det3 (x (lab (i + 1)) - x (lab i)) u (dt t) * ⟪x m - x (lab i), u⟫ :=
            mul_pos hE hwp
          have : 0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (dt t) * ⟪u, u⟫ := by
            rw [hk]; exact h3
          exact (mul_pos_iff_of_pos_right huu).1 this
        refine Filter.Eventually.mono self_mem_nhdsWithin fun ε hε _ _ => ?_
        rw [← heq]
        have : 0 < ε := hε
        positivity
  obtain ⟨ε, hε, hεpos⟩ := (hev2.and (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))).exists
  have hεp : 0 < ε := hεpos
  refine ⟨u + ε • dt t, k, inferInstance, lab, hk, hinj, ?_, ?_⟩
  · intro m i h1 h2
    exact hε i m h1 h2
  · let q : ZMod k → Fin 3 → ℝ := fun i j => x (lab i) j
    let n : Fin 3 → ℝ := fun j => u j
    let l : Fin 3 → ℝ := fun j => ε * dt t j
    have hqn : ∀ i, n ⬝ᵥ q i = 0 := by
      intro i
      have := hplane i
      rw [fn_inner] at this
      simp only [n, q, dotProduct, Fin.sum_univ_three]; linarith
    have hqc : IsStrictConvexPlanarCycle q n := by
      refine ⟨fun i => by rw [hqn, hqn], ?_⟩
      intro i m hmi hmi1
      have := hF i m hmi hmi1
      simp only [det3, tripleProduct, q, n] at this ⊢
      simpa using this
    have hlq : ∀ i, l ⬝ᵥ q i = ε * ⟪x (lab i), dt t⟫ := by
      intro i
      rw [fn_inner]
      simp only [l, q, dotProduct, Fin.sum_univ_three]; ring
    have hli : Function.Injective (fun i => l ⬝ᵥ q i) := by
      intro a b hab
      by_contra hne
      simp only [hlq] at hab
      exact hinj' a b hne (mul_left_cancel₀ hεp.ne' hab)
    have := coplanarRimDepthUnimodal k hk q n hqc l hli
    have e : (fun i => ⟪x (lab i), u + ε • dt t⟫) = fun i => l ⬝ᵥ q i := by
      funext i
      rw [hlq, inner_add_right, inner_smul_right, hplane]; simp
    rw [e]; exact this

end MinimalityExtra
