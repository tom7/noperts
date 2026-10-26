module

public import Minimality.Type29Cert

@[expose] public section

/-!
# Type 29: ties in the pair tests (`FEWER-FACES-PROOFS.md` §28, §18.4, §21.15)

* `pair_core`: **Corollary 13.3 with ties** for the pairs of K3a / K4a.  Two four-corner rims
  `Q₂` (the partner, at `v`) and `Q₁` (at `u`) whose diagonals cross along both views, with the
  signs `det(u, ·) det(v, ·) > 0` for `Q₁` and `< 0` for `Q₂`.  With at most one tie at each of
  `u`, `v` and no tie at one of them, either `Q₂` is robustly unimodal, or `Q₁` is and
  `⟪u, v⟫ ≤ 0` (the partner is preferred, so `Q₁`'s certificate carries the closed fact, as
  type 21's `VQuadCone`).
* `robust_of_view_nhds`: a rim with at most one tie is robustly unimodal if the unimodality
  criterion holds for all views near the given one (the tie is broken both ways by perturbing
  the view).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A weak separation of the two diagonals of a rim of distinct depths is strict. -/
theorem strict_sep_of_nodup {z₀ z₁ z₂ z₃ : ℝ} (hd : [z₀, z₁, z₂, z₃].Nodup)
    (h : max z₁ z₃ ≤ min z₀ z₂ ∨ max z₀ z₂ ≤ min z₁ z₃) :
    max z₁ z₃ < min z₀ z₂ ∨ max z₀ z₂ < min z₁ z₃ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hd
  rcases h with h | h
  · left
    refine lt_of_le_of_ne h fun e => ?_
    rcases max_choice z₁ z₃ with m | m <;> rcases min_choice z₀ z₂ with n | n <;> rw [m, n] at e
    exacts [h01 e.symm, h12 e, h03 e.symm, h23 e.symm]
  · right
    refine lt_of_le_of_ne h fun e => ?_
    rcases max_choice z₀ z₂ with m | m <;> rcases min_choice z₁ z₃ with n | n <;> rw [m, n] at e
    exacts [h01 e, h03 e, h12 e.symm, h23 e]

/-- The diagonals of the rim do not meet in space: from a crossing along `v` with `l ≠ 0` and
the nonvanishing `det(v, d̄, ē)`. -/
theorem hS_of_smul {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : K ≠ 0)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) (hl : l ≠ 0)
    (hdet : det3 v (d₁ - d₀) (e₁ - e₀) ≠ 0) : det3 (e₀ - d₀) (d₁ - d₀) (e₁ - e₀) ≠ 0 := by
  intro h0
  have e := congrArg (fun w => det3 w (d₁ - d₀) (e₁ - e₀)) h
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e h0
  simp only [det3_expand, PiLp.sub_apply] at hdet
  apply hdet
  have : l * (v 0 * ((d₁ 1 - d₀ 1) * (e₁ 2 - e₀ 2) - (d₁ 2 - d₀ 2) * (e₁ 1 - e₀ 1)) -
      v 1 * ((d₁ 0 - d₀ 0) * (e₁ 2 - e₀ 2) - (d₁ 2 - d₀ 2) * (e₁ 0 - e₀ 0)) +
      v 2 * ((d₁ 0 - d₀ 0) * (e₁ 1 - e₀ 1) - (d₁ 1 - d₀ 1) * (e₁ 0 - e₀ 0))) = 0 := by
    linear_combination (-1 : ℝ) * e + K * h0
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hl
  · linarith

/-- **Corollary 13.3 with ties, preferring the partner** (§18.4, §21.15; the pairs `P14`, `P11`,
`{Xa, T2}`, `P13`).  `Q₁ = (d₀, e₀, d₁, e₁)` at `u` and `Q₂ = (f₀, g₀, f₁, g₁)` at `v`, with
diagonals `[d₀, d₁], [e₀, e₁]` resp. `[f₀, f₁], [g₀, g₁]` crossing along both views, and the
signs of the four determinants of Corollary 13.3.  At most one tie at each view and none at
one of them: `Q₂` is robustly unimodal, or `Q₁` is and `⟪u, v⟫ ≤ 0`. -/
theorem pair_core {K : Finset ℝ³} {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³}
    (hd₀ : d₀ ∈ K) (hd₁ : d₁ ∈ K) (he₀ : e₀ ∈ K) (he₁ : e₁ ∈ K)
    (hf₀ : f₀ ∈ K) (hf₁ : f₁ ∈ K) (hg₀ : g₀ ∈ K) (hg₁ : g₁ ∈ K)
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2u : SegMeet f₀ f₁ g₀ g₁ u) (m2v : SegMeet f₀ f₁ g₀ g₁ v)
    (hS1 : det3 (e₀ - d₀) (d₁ - d₀) (e₁ - e₀) ≠ 0)
    (hS2 : det3 (g₀ - f₀) (f₁ - f₀) (g₁ - g₀) ≠ 0)
    (hp1 : 0 < det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀))
    (hn2 : det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀) < 0)
    (o1 : OneTieAt K u) (o2 : OneTieAt K v) (hno : NoTieAt K u ∨ NoTieAt K v) :
    IsRobustUnimodal (quad ⟪f₀, v⟫ ⟪g₀, v⟫ ⟪f₁, v⟫ ⟪g₁, v⟫) ∨
      (IsRobustUnimodal (quad ⟪d₀, u⟫ ⟪e₀, u⟫ ⟪d₁, u⟫ ⟪e₁, u⟫) ∧ ⟪u, v⟫ ≤ 0) := by
  by_cases hR2 : IsRobustUnimodal (quad ⟪f₀, v⟫ ⟪g₀, v⟫ ⟪f₁, v⟫ ⟪g₁, v⟫)
  · exact Or.inl hR2
  right
  have W2 := weakSep_of_not_robust (o2.oneTie4 hf₀ hg₀ hf₁ hg₁ n2) hR2
  -- the partner failing: `⟪u, v⟫ ≤ 0`
  have huv : ⟪u, v⟫ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hne : ⟪v, u⟫ ≠ 0 := by rw [real_inner_comm]; exact hpos.ne'
    have B := weakSep_det_sign (a' := f₀) (a := f₁) (b := g₀) (b' := g₁) (u := v) (v := u)
      W2.symm m2v m2u hne hS2
    rw [real_inner_comm] at B
    nlinarith [mul_pos hpos (neg_pos.mpr hn2), mul_comm (det3 u (f₁ - f₀) (g₁ - g₀))
      (det3 v (f₁ - f₀) (g₁ - g₀))]
  refine ⟨?_, huv⟩
  by_contra hR1
  have W1 := weakSep_of_not_robust (o1.oneTie4 hd₀ he₀ hd₁ he₁ n1) hR1
  rcases hno with hnu | hnv
  · -- no tie at `u`: `Q₁` is strictly separated
    have hs1 : DepthSep d₀ d₁ e₀ e₁ u := by
      have := strict_sep_of_nodup (hnu.nodup4 hd₀ he₀ hd₁ he₁ n1) W1
      rcases this with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨A, hne⟩ := depthSep_det_sign hs1 m1u m1v
    have hneg : ⟪u, v⟫ < 0 := lt_of_le_of_ne huv hne
    nlinarith [mul_pos (neg_pos.mpr hneg) hp1]
  · -- no tie at `v`: `Q₂` is strictly separated, so `⟪u, v⟫ ≠ 0`
    have hs2 : DepthSep f₀ f₁ g₀ g₁ v := by
      have := strict_sep_of_nodup (hnv.nodup4 hf₀ hg₀ hf₁ hg₁ n2) W2
      rcases this with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨-, hne'⟩ := depthSep_det_sign hs2 m2v m2u
    have hne : ⟪u, v⟫ ≠ 0 := by rw [real_inner_comm]; exact hne'
    have A := weakSep_det_sign (a' := d₀) (a := d₁) (b := e₀) (b' := e₁) (u := u) (v := v)
      W1.symm m1u m1v hne hS1
    have hneg : ⟪u, v⟫ < 0 := lt_of_le_of_ne huv hne
    nlinarith [mul_pos (neg_pos.mpr hneg) hp1]

/-- **Robust unimodality by perturbing the view**: a rim of distinct points with at most one tie
at the view `u` is robustly unimodal if there is an open set `P` of views around `u` on which
every injective depth sequence is unimodal. -/
theorem robust_of_view_nhds {k : ℕ} [NeZero k] {K : Finset ℝ³} {pts : ZMod k → ℝ³}
    (hpts : ∀ i, pts i ∈ K) (hinj : Function.Injective pts) {u : ℝ³} (ho : OneTieAt K u)
    (P : ℝ³ → Prop) (hP : ∀ᶠ w in 𝓝 u, P w)
    (huni : ∀ w, P w → Function.Injective (fun i => ⟪pts i, w⟫) →
      IsCyclicUnimodal (fun i => ⟪pts i, w⟫)) :
    IsRobustUnimodal (fun i => ⟪pts i, u⟫) := by
  refine isRobustUnimodal_of_perturb (ho.rim hpts hinj) (huni u hP.self_of_nhds) ?_
  intro a b hab _
  refine ⟨fun i => ⟪pts i, pts a - pts b⟫, ?_, ?_⟩
  · intro h
    have h' : ⟪pts a - pts b, pts a - pts b⟫ = 0 := by
      rw [inner_sub_left]; exact sub_eq_zero.mpr h
    exact sub_ne_zero.mpr (hinj.ne hab) (inner_self_eq_zero.mp h')
  · have hT : Tendsto (fun ε : ℝ => u + ε • (pts a - pts b)) (𝓝[≠] (0 : ℝ)) (𝓝 u) := by
      have : Tendsto (fun ε : ℝ => u + ε • (pts a - pts b)) (𝓝 0) (𝓝 (u + (0 : ℝ) • (pts a - pts
          b))) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    filter_upwards [hT.eventually hP] with ε hε hi
    have e : (fun i => ⟪pts i, u⟫ + ε * ⟪pts i, pts a - pts b⟫) =
        fun i => ⟪pts i, u + ε • (pts a - pts b)⟫ := by
      funext i; rw [inner_add_right, real_inner_smul_right]
    rw [e] at hi ⊢
    exact huni _ hε hi

/-- No two ties at a view: three distinct points are not all at one depth. -/
theorem OneTieAt.not_three {K : Finset ℝ³} {w : ℝ³} (h : OneTieAt K w) {a b c : ℝ³}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ¬ (⟪a, w⟫ = ⟪b, w⟫ ∧ ⟪b, w⟫ = ⟪c, w⟫) := by
  rintro ⟨e1, e2⟩
  rcases h a ha b hb b hb c hc hab hbc e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hab h1
  · exact hac h1

/-- Ties at a multiple of a view are ties at the view. -/
theorem OneTieAt.of_smul {K : Finset ℝ³} {w : ℝ³} (h : OneTieAt K w) {c : ℝ} (hc : c ≠ 0) :
    OneTieAt K (c • w) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  simp only [real_inner_smul_right] at e1 e2
  exact h s hs t ht s' hs' t' ht' hst hst' (mul_left_cancel₀ hc e1) (mul_left_cancel₀ hc e2)

theorem NoTieAt.of_smul {K : Finset ℝ³} {w : ℝ³} (h : NoTieAt K w) {c : ℝ} (hc : c ≠ 0) :
    NoTieAt K (c • w) := by
  intro s hs t ht hst e
  simp only [real_inner_smul_right] at e
  exact h s hs t ht hst (mul_left_cancel₀ hc e)

/-- **Corollary 13.3 with ties for two tests sharing a diagonal** `[a', a]` (`B2`: `W` and `Z`).
Test 1 at `u` has rim `(a', b, a, b')`, test 2 at `v` has rim `(a', c', a, c)`; at most one tie at
each view and none at one of them: one of the two rims is robustly unimodal. -/
theorem shared_core {K : Finset ℝ³} {a a' b b' c c' u v : ℝ³}
    (ha' : a' ∈ K) (ha : a ∈ K) (hb : b ∈ K) (hb' : b' ∈ K) (hc : c ∈ K) (hc' : c' ∈ K)
    (n1 : [a', b, a, b'].Nodup) (n2 : [a', c', a, c].Nodup)
    (m1u : SegMeet a' a b b' u) (m1v : SegMeet a' a b b' v)
    (m2u : SegMeet a' a c c' u) (m2v : SegMeet a' a c c' v)
    (hS1 : det3 (b - a') (a - a') (b' - b) ≠ 0) (hS2 : det3 (c - a') (a - a') (c' - c) ≠ 0)
    (hdet : det3 u (a - a') (b' - b) * det3 v (a - a') (b' - b) *
      (det3 u (a - a') (c' - c) * det3 v (a - a') (c' - c)) < 0)
    (o1 : OneTieAt K u) (o2 : OneTieAt K v) (hno : NoTieAt K u ∨ NoTieAt K v) :
    IsRobustUnimodal (quad ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫) ∨
      IsRobustUnimodal (quad ⟪a', v⟫ ⟪c', v⟫ ⟪a, v⟫ ⟪c, v⟫) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR1, hR2⟩ := hcon
  have W1 := weakSep_of_not_robust (o1.oneTie4 ha' hb ha hb' n1) hR1
  have W2 := weakSep_of_not_robust (o2.oneTie4 ha' hc' ha hc n2) hR2
  have W2' : max ⟪a', v⟫ ⟪a, v⟫ ≤ min ⟪c, v⟫ ⟪c', v⟫ ∨ max ⟪c, v⟫ ⟪c', v⟫ ≤ min ⟪a', v⟫ ⟪a, v⟫ := by
    rw [max_comm ⟪c, v⟫, min_comm ⟪c, v⟫]; exact W2.symm
  rcases hno with hnu | hnv
  · have hs1 : DepthSep a' a b b' u := by
      rcases strict_sep_of_nodup (hnu.nodup4 ha' hb ha hb' n1) W1 with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨A, hne⟩ := depthSep_det_sign hs1 m1u m1v
    have hne' : ⟪v, u⟫ ≠ 0 := by rw [real_inner_comm]; exact hne
    have B := weakSep_det_sign (a' := a') (a := a) (b := c) (b' := c') (u := v) (v := u)
      W2' m2v m2u hne' hS2
    exact not_both_of_signs A B hne hdet
  · have hs2 : DepthSep a' a c c' v := by
      rcases strict_sep_of_nodup (hnv.nodup4 ha' hc' ha hc n2) W2 with h | h
      · rw [max_comm ⟪c', v⟫] at h; exact Or.inr h
      · rw [min_comm ⟪c', v⟫] at h; exact Or.inl h
    obtain ⟨B, hne'⟩ := depthSep_det_sign hs2 m2v m2u
    have hne : ⟪u, v⟫ ≠ 0 := by rw [real_inner_comm]; exact hne'
    have A := weakSep_det_sign (a' := a') (a := a) (b := b) (b' := b') (u := u) (v := v)
      W1.symm m1u m1v hne hS1
    exact not_both_of_signs A B hne hdet

/-- `segMeet_of_smul` (Type29K4, strict positivity) also gives that the diagonals do not meet. -/
theorem segMeet_hS_of_smul {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : 0 < K) (hs : 0 < s)
    (hs' : 0 < K - s) (ht : 0 < t) (ht' : 0 < K - t)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) (hl : l ≠ 0)
    (hdet : det3 v (d₁ - d₀) (e₁ - e₀) ≠ 0) : det3 (e₀ - d₀) (d₁ - d₀) (e₁ - e₀) ≠ 0 :=
  hS_of_smul hK.ne' h hl hdet

theorem OneTieAt.of_eq_smul {K : Finset ℝ³} {w u : ℝ³} (h : OneTieAt K w) {c : ℝ}
    (e : u = c • w) (hc : c ≠ 0) : OneTieAt K u := e ▸ h.of_smul hc

theorem NoTieAt.of_eq_smul {K : Finset ℝ³} {w u : ℝ³} (h : NoTieAt K w) {c : ℝ}
    (e : u = c • w) (hc : c ≠ 0) : NoTieAt K u := e ▸ h.of_smul hc

/-- `segMeet_of_smul'` (Type29K3) also gives that the diagonals do not meet in space. -/
theorem segMeet_hS_of_smul' {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : 0 < K) (hs : 0 ≤ s)
    (hs' : 0 ≤ K - s) (ht : 0 ≤ t) (ht' : 0 ≤ K - t)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) (hl : l ≠ 0)
    (hdet : det3 v (d₁ - d₀) (e₁ - e₀) ≠ 0) : det3 (e₀ - d₀) (d₁ - d₀) (e₁ - e₀) ≠ 0 :=
  hS_of_smul hK.ne' h hl hdet

theorem prod_pos_of_eq {a b P Q D : ℝ} (hD : D ≠ 0) (ha : a = P * D) (hb : b = Q * D)
    (hP : 0 < P) (hQ : 0 < Q) : 0 < a * b := by
  rw [ha, hb]
  have := mul_pos (mul_pos hP hQ) (mul_self_pos.mpr hD)
  nlinarith [this]

theorem prod_neg_of_eq {a b P Q D : ℝ} (hD : D ≠ 0) (ha : a = P * D) (hb : b = Q * D)
    (hP : P < 0) (hQ : 0 < Q) : a * b < 0 := by
  rw [ha, hb]
  have := mul_pos (mul_pos (neg_pos.mpr hP) hQ) (mul_self_pos.mpr hD)
  nlinarith [this]

theorem List.nodup4_img {x : Fin 7 → ℝ³} (hx : Function.Injective x) {a b c d : Fin 7}
    (h : [a, b, c, d].Nodup) : [x a, x b, x c, x d].Nodup := by
  have := h.map hx
  simpa using this

theorem OneTieAt.neg {K : Finset ℝ³} {w : ℝ³} (h : OneTieAt K w) : OneTieAt K (-w) :=
  h.of_eq_smul (neg_one_smul ℝ w).symm (by norm_num)

theorem NoTieAt.neg {K : Finset ℝ³} {w : ℝ³} (h : NoTieAt K w) : NoTieAt K (-w) :=
  h.of_eq_smul (neg_one_smul ℝ w).symm (by norm_num)

variable {x : Fin 7 → ℝ³}

theorem NF29.hDi (N : NF29 x) : N.D⁻¹ ≠ 0 := inv_ne_zero (show N.D ≠ 0 from N.hD)

theorem NF29.hDni (N : NF29 x) : (-N.D)⁻¹ ≠ 0 :=
  inv_ne_zero (neg_ne_zero.mpr (show N.D ≠ 0 from N.hD))

/-- `P14`: `⟪vT1, vT2⟫ ≤ 0` is `⟪w₀, w₁⟫ ≥ 0` for the named views. -/
theorem NF29.dot_T1T2 (N : NF29 x) (h : ⟪N.vT1, N.vT2⟫ ≤ 0) :
    0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫ := by
  rw [N.vT1_eq, N.vT2_eq, real_inner_smul_left, real_inner_smul_right, inv_neg] at h
  have hp : 0 < N.D⁻¹ * N.D⁻¹ := mul_self_pos.mpr N.hDi
  by_contra hz
  push Not at hz
  nlinarith [mul_pos hp (neg_pos.mpr hz)]

/-- `P11`: `⟪vT1, vT3⟫ ≤ 0` is `⟪w₀, w₃⟫ ≤ 0` for the named views. -/
theorem NF29.dot_T1T3 (N : NF29 x) (h : ⟪N.vT1, N.vT3⟫ ≤ 0) :
    ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0 := by
  rw [N.vT1_eq, N.vT3_eq, real_inner_smul_left, real_inner_smul_right] at h
  have hp : 0 < N.D⁻¹ * N.D⁻¹ := mul_self_pos.mpr N.hDi
  by_contra hz
  push Not at hz
  nlinarith [mul_pos hp hz]

/-! ### The tie hypothesis of the covers -/

/-- The pairs of named views whose tests are combined (Corollary 13.3): `P14 = (T1, T2)`,
`P11 = (T1, T3)`, `{Xa, T2}`, `P13 = (T3, T2)`, `{Y1, Y2}`, tier (A) `(V, Y)`, its `σ`-image
`(T2, Y')` and tier (B2) `(W, Z)`. -/
def pairViews29 : Finset (View29 × View29) :=
  {(.inr 0, .inr 1), (.inr 0, .inr 3), (.inl (0, 5), .inr 1), (.inr 3, .inr 1),
    (.inr 4, .inl (4, 6)), (.inr 2, .inl (3, 5)), (.inr 1, .inl (3, 4)), (.inl (0, 3), .inr 6)}

/-- **The ties allowed in the covers** (the codimension-2 hypothesis): at most one tied pair at
each nonzero named view, and no tie at one of the two views of each combined pair (a second tie
is a second equation on the shape). -/
structure Tie29 (x : Fin 7 → ℝ³) : Prop where
  one : OneTie29 x
  pair : ∀ p ∈ pairViews29, view29 x p.1 ≠ 0 → view29 x p.2 ≠ 0 →
    NoTieAt (univ.image x) (view29 x p.1) ∨ NoTieAt (univ.image x) (view29 x p.2)

theorem Tie29.edge {x : Fin 7 → ℝ³} (hx : Function.Injective x) (ht : Tie29 x) {i j : Fin 7}
    (hij : i ≠ j) : OneTieAt (univ.image x) (x j - x i) :=
  ht.one (.inl (i, j)) (sub_ne_zero.mpr (hx.ne hij.symm))

variable {x : Fin 7 → ℝ³}

theorem NF29.view_T1_ne (N : NF29 x) : view29 x (.inr 0) ≠ 0 := by
  show vtxView29 x 0 ≠ 0
  rw [N.vtxView29_0]
  exact smul_ne_zero (mul_ne_zero one_ne_zero N.hD)
    (nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5)))

theorem NF29.view_T2_ne (N : NF29 x) : view29 x (.inr 1) ≠ 0 := by
  show vtxView29 x 1 ≠ 0
  rw [N.vtxView29_1]
  exact smul_ne_zero (mul_ne_zero (by norm_num) N.hD)
    (nfV_ne_zero N.hD (Or.inr (Or.inl (ne_of_gt (by linarith [N.hb2])))))

theorem NF29.view_V_ne (N : NF29 x) : view29 x (.inr 2) ≠ 0 := by
  show vtxView29 x 2 ≠ 0
  rw [N.vtxView29_2]
  exact smul_ne_zero (mul_ne_zero (by norm_num) N.hD)
    (nfV_ne_zero N.hD (Or.inl (neg_pos.mpr N.ha0).ne'))

theorem NF29.view_T3_ne (N : NF29 x) : view29 x (.inr 3) ≠ 0 := by
  show vtxView29 x 3 ≠ 0
  rw [N.vtxView29_3]
  exact smul_ne_zero (mul_ne_zero one_ne_zero N.hD)
    (nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hh2)))))

theorem NF29.view_Y1_ne (N : NF29 x) : view29 x (.inr 4) ≠ 0 := by
  show vtxView29 x 4 ≠ 0
  rw [N.vtxView29_4]
  exact smul_ne_zero (mul_ne_zero (by norm_num) N.hD)
    (nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hs)))))

theorem NF29.view_Z_ne (N : NF29 x) : view29 x (.inr 6) ≠ 0 := by
  show vtxView29 x 6 ≠ 0
  rw [N.vtxView29_6]
  exact smul_ne_zero (mul_ne_zero one_ne_zero N.hD)
    (nfV_ne_zero N.hD (Or.inl (ne_of_gt (by
      nlinarith [mul_pos (neg_pos.mpr N.ha0)
        (show 0 < -N.b2 - (N.a2 + N.h2 - 1) by linarith [N.t345_2])]))))

theorem NF29.seg_ne (N : NF29 x) {i j : Fin 7} (hij : i ≠ j) : view29 x (.inl (i, j)) ≠ 0 :=
  sub_ne_zero.mpr (N.inj.ne hij.symm)

/-- Three distinct points of `x` are not all at one depth when there is at most one tie. -/
theorem NF29.edge_weak (N : NF29 x) {u : ℝ³} (o : OneTieAt (univ.image x) u) {a c b : Fin 7}
    (hac : a ≠ c) (hcb : c ≠ b) (hab : a ≠ b) :
    ¬ (⟪x a, u⟫ = ⟪x c, u⟫ ∧ ⟪x c, u⟫ = ⟪x b, u⟫) :=
  o.not_three (mem_image_of_mem x (mem_univ a)) (mem_image_of_mem x (mem_univ c))
    (mem_image_of_mem x (mem_univ b)) (N.inj.ne hac) (N.inj.ne hcb) (N.inj.ne hab)

/-- The weak hypothesis of an edge-pair test along `x j − x i` from the tie hypothesis. -/
theorem NF29.edgeW (N : NF29 x) (ht : Tie29 x) {i j a c b : Fin 7} (hij : i ≠ j) (hac : a ≠ c)
    (hcb : c ≠ b) (hab : a ≠ b) :
    ¬ (⟪x a, x j - x i⟫ = ⟪x c, x j - x i⟫ ∧ ⟪x c, x j - x i⟫ = ⟪x b, x j - x i⟫) :=
  N.edge_weak (ht.edge N.inj hij) hac hcb hab

/-- A planar rim `(1, 4, 6, 5)` in `H` is robustly unimodal when `1, 4, 5` are not all at one
depth (`nws4_of_planar_quad_tie`; at most one tie suffices). -/
theorem NF29.planar_robust (N : NF29 x) {u : ℝ³} (o : OneTieAt (univ.image x) u) :
    IsRobustUnimodal (quad ⟪x 1, u⟫ ⟪x 4, u⟫ ⟪x 6, u⟫ ⟪x 5, u⟫) := by
  have v6 : x 6 = x 1 + N.s • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
  refine (nws4_of_planar_quad_tie N.hs N.ht N.hst v6 ?_).isRobustUnimodal
  rintro ⟨h1, h2⟩
  exact o.not_three (mem_image_of_mem x (mem_univ 4)) (mem_image_of_mem x (mem_univ 1))
    (mem_image_of_mem x (mem_univ 5)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
    (N.inj.ne (by decide)) ⟨h1.symm, h2⟩

end Minimality

end
