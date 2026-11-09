module

public import Mathlib
public import MinimalityExtra
public import MinimalityExtra.MetricUniform

/-!
# Flat metrics are unimodal (Lemma FL) and the defeat set of a view cell (Lemma DC)

Proofs of `FlatMetricsUnimodal` and `DefeatCellCriterion` (statements in `MinimalityExtra.lean`).
-/

@[expose] public section

open Matrix Filter Topology

namespace MinimalityExtra

lemma tp_add3 (a b c d : Fin 3 → ℝ) :
    tripleProduct a b (c + d) = tripleProduct a b c + tripleProduct a b d := by
  simp [tripleProduct]; ring

lemma tp_smul3 (a b c : Fin 3 → ℝ) (t : ℝ) :
    tripleProduct a b (t • c) = t * tripleProduct a b c := by
  simp [tripleProduct]; ring

lemma tp_sub_w (a b w : Fin 3 → ℝ) (α β : ℝ) :
    tripleProduct (a - α • w) (b - β • w) w = tripleProduct a b w := by
  simp [tripleProduct]; ring

lemma tp_w_left (a w : Fin 3 → ℝ) (t : ℝ) : tripleProduct (t • w) a w = 0 := by
  simp [tripleProduct]; ring

lemma tp_w_mid (a w : Fin 3 → ℝ) (t : ℝ) : tripleProduct a (t • w) w = 0 := by
  simp [tripleProduct]; ring

lemma order_unimodal {k : ℕ} [NeZero k] {z z' : ZMod k → ℝ}
    (h : ∀ i j, z i < z j ↔ z' i < z' j) (hz' : IsCyclicUnimodal z') : IsCyclicUnimodal z := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_contra hne
    have : z' i ≠ z' j := fun e => hne (hz'.1 e)
    rcases lt_or_gt_of_ne this with h1 | h1
    · have := (h i j).2 h1; linarith
    · have := (h j i).2 h1; linarith
  · have : Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i) =
        Finset.univ.filter (fun i : ZMod k => z' (i - 1) < z' i ∧ z' (i + 1) < z' i) :=
      Finset.filter_congr (fun i _ => by rw [h, h])
    rw [this]; exact hz'.2

lemma eventually_order {k : ℕ} [NeZero k] {ι : Type*} (zs : ι → ZMod k → ℝ) (l : Filter ι)
    (zst : ZMod k → ℝ) (hinj : Function.Injective zst)
    (ht : ∀ i, Tendsto (fun m => zs m i) l (𝓝 (zst i))) :
    ∀ᶠ m in l, ∀ i j, zs m i < zs m j ↔ zst i < zst j := by
  have h1 : ∀ᶠ m in l, ∀ i j, zst i < zst j → zs m i < zs m j := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases h : zst i < zst j
    · exact ((ht i).eventually_lt (ht j) h).mono (fun m hm _ => hm)
    · exact Filter.Eventually.of_forall (fun m hm => absurd hm h)
  refine h1.mono (fun m hm i j => ⟨fun h => ?_, hm i j⟩)
  by_contra hn
  rcases lt_trichotomy (zst i) (zst j) with h2 | h2 | h2
  · exact hn h2
  · have := hinj h2; subst this; exact lt_irrefl _ h
  · have := hm j i h2; linarith

theorem flatMetricsUnimodal : FlatMetricsUnimodal := by
  intro x w k _ lab hw hk hinj hrim G Gs hG hlim hGw hker
  have hk1 : Fact (1 < k) := ⟨by omega⟩
  have hk2 : (2 : ZMod k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- traces and symmetry
  have htr : ∀ m, 0 < (G m).trace := fun m => (hG m).trace_pos
  have hsymm : Gsᵀ = Gs := by
    have h1 : Tendsto (fun m => ((G m).trace⁻¹ • G m)ᵀ) atTop (𝓝 Gsᵀ) :=
      ((continuous_id.matrix_transpose).tendsto Gs).comp hlim
    have h2 : (fun m => ((G m).trace⁻¹ • G m)ᵀ) = fun m => (G m).trace⁻¹ • G m := by
      funext m; rw [Matrix.transpose_smul, pd_symm _ (hG m)]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hlim
  have hww : w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.mp h)
  -- differences of rim points are not in the kernel
  have hdiff : ∀ a b : ZMod k, a ≠ b → Gs *ᵥ (x (lab a) - x (lab b)) ≠ 0 := by
    intro a b hab h0
    obtain ⟨t, ht⟩ := hker _ h0
    by_cases hb : b = a + 1
    · have hm1 : lab (a + 2) ≠ lab a := by
        intro e; have := hinj e
        apply hk2; have : (a + 2) - a = 0 := by rw [this]; ring
        simpa using this
      have hm2 : lab (a + 2) ≠ lab (a + 1) := by
        intro e; have := hinj e
        have : (1 : ZMod k) = 0 := by
          have h3 : (a + 2) - (a + 1) = 0 := by rw [this]; ring
          simpa [show (a + 2) - (a + 1) = 1 by ring] using h3
        exact one_ne_zero this
      have := hrim (lab (a + 2)) a hm1 hm2
      have e : x (lab (a + 1)) - x (lab a) = (-t) • w := by
        rw [← hb] at *
        rw [neg_smul, ← ht]; abel
      rw [e, tp_w_left] at this
      exact lt_irrefl _ this
    · have hm1 : lab b ≠ lab a := fun e => hab (hinj e).symm
      have hm2 : lab b ≠ lab (a + 1) := fun e => hb (hinj e)
      have := hrim (lab b) a hm1 hm2
      have e : x (lab b) - x (lab a) = (-t) • w := by
        rw [neg_smul, ← ht]; abel
      rw [e, tp_w_mid] at this
      exact lt_irrefl _ this
  -- choose a generic s
  obtain ⟨s, hs⟩ : ∃ s : Fin 3 → ℝ, ∀ a b : ZMod k, a ≠ b →
      (Gs *ᵥ (x (lab a) - x (lab b))) ⬝ᵥ s ≠ 0 := by
    classical
    let φ : ZMod k × ZMod k → Subspace ℝ (Fin 3 → ℝ) := fun p =>
      { carrier := {s | (Gs *ᵥ (x (lab p.1) - x (lab p.2))) ⬝ᵥ s = 0}
        add_mem' := by intro a b ha hb; simp_all [dotProduct_add]
        zero_mem' := by simp
        smul_mem' := by intro c a ha; simp_all [dotProduct_smul] }
    let T : Finset (Subspace ℝ (Fin 3 → ℝ)) :=
      ((Finset.univ : Finset (ZMod k × ZMod k)).filter (fun p => p.1 ≠ p.2)).image φ
    have hT : (⊤ : Subspace ℝ (Fin 3 → ℝ)) ∉ T := by
      intro hmem
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
      have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      set c := Gs *ᵥ (x (lab p.1) - x (lab p.2)) with hc
      have hc0 : c ≠ 0 := hdiff _ _ hp'
      have : c ∈ (φ p) := by rw [hpe]; trivial
      have h2 : c ⬝ᵥ c = 0 := this
      exact hc0 (dotProduct_self_eq_zero.mp h2)
    have := Subspace.biUnion_ne_univ_of_top_notMem hT
    obtain ⟨s, hs⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp this
    refine ⟨s, fun a b hab h => hs ?_⟩
    simp only [Set.mem_iUnion]
    refine ⟨φ (a, b), ?_, ?_⟩
    · exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
    · exact h
  -- the generic tilt
  have hT3 : ∀ᶠ e : ℝ in 𝓝 0, ∀ (m : Fin 7) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
      0 < tripleProduct (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (w + e • s) := by
    rw [Filter.eventually_all]; intro m
    rw [Filter.eventually_all]; intro i
    by_cases h1 : m ≠ lab i
    · by_cases h2 : m ≠ lab (i + 1)
      · have h0 := hrim m i h1 h2
        have hc : Continuous (fun e : ℝ => tripleProduct (x (lab (i + 1)) - x (lab i))
            (x m - x (lab i)) (w + e • s)) := by
          simp only [tripleProduct]; fun_prop
        have := (hc.tendsto 0).eventually (lt_mem_nhds (show 0 < _ by simpa using h0))
        exact this.mono (fun e he _ _ => he)
      · exact Filter.Eventually.of_forall (fun e a b => absurd b h2)
    · exact Filter.Eventually.of_forall (fun e a b => absurd a h1)
  obtain ⟨ε, hε, hεpos⟩ : ∃ ε : ℝ, (∀ (m : Fin 7) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
      0 < tripleProduct (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) (w + ε • s)) ∧ 0 < ε := by
    have := (hT3.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).and
      (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))
    obtain ⟨e, he1, he2⟩ := this.exists
    exact ⟨e, he1, he2⟩
  set u := w + ε • s with hu
  -- the limit functional
  set l : Fin 3 → ℝ := Gs *ᵥ s with hl
  have hlw : l ⬝ᵥ w = 0 := by
    rw [hl, dotProduct_comm, sym_dot Gs hsymm w s, hGw]; simp
  have hGu : Gs *ᵥ u = ε • l := by
    rw [hu, mulVec_add, mulVec_smul, hGw, zero_add]
  have hzinj : Function.Injective (fun i : ZMod k => l ⬝ᵥ x (lab i)) := by
    intro a b hab
    by_contra hne
    apply hs a b hne
    have h1 : l ⬝ᵥ x (lab a) - l ⬝ᵥ x (lab b) = 0 := by simp only at hab; linarith
    rw [← dotProduct_sub] at h1
    have e : (Gs *ᵥ (x (lab a) - x (lab b))) ⬝ᵥ s = l ⬝ᵥ (x (lab a) - x (lab b)) := by
      rw [dotProduct_comm, sym_dot Gs hsymm s, hl, dotProduct_comm]
    rw [e]; exact h1
  -- the limit is unimodal
  set α : ZMod k → ℝ := fun i => (w ⬝ᵥ x (lab i)) / (w ⬝ᵥ w) with hα
  set q : ZMod k → Fin 3 → ℝ := fun i => x (lab i) - α i • w with hq
  have hqc : IsStrictConvexPlanarCycle q w := by
    refine ⟨?_, ?_⟩
    · intro i
      have : ∀ j, w ⬝ᵥ q j = 0 := by
        intro j
        simp only [hq, dotProduct_sub, dotProduct_smul, smul_eq_mul, hα]
        field_simp; ring
      rw [this, this]
    · intro i m hmi hmi1
      have h0 := hrim (lab m) i (fun e => hmi (hinj e)) (fun e => hmi1 (hinj e))
      have e1 : q (i + 1) - q i = (x (lab (i + 1)) - x (lab i)) - (α (i + 1) - α i) • w := by
        simp only [hq]; ext j; simp; ring
      have e2 : q m - q i = (x (lab m) - x (lab i)) - (α m - α i) • w := by
        simp only [hq]; ext j; simp; ring
      rw [e1, e2, tp_sub_w]; exact h0
  have hlq : ∀ i, l ⬝ᵥ q i = l ⬝ᵥ x (lab i) := by
    intro i; simp only [hq, dotProduct_sub, dotProduct_smul, hlw]; simp
  have hzst : IsCyclicUnimodal (fun i : ZMod k => l ⬝ᵥ x (lab i)) := by
    have := coplanarRimDepthUnimodal k hk q w hqc l (by
      intro a b hab; apply hzinj; simpa only [hlq] using hab)
    simpa only [hlq] using this
  -- positive scaling
  have hord : ∀ (c : ℝ), 0 < c → ∀ (y : ZMod k → ℝ), IsCyclicUnimodal y →
      IsCyclicUnimodal (fun i => c * y i) := by
    intro c hc y hy
    exact order_unimodal (fun i j => by simp only [mul_lt_mul_iff_right₀ hc]) hy
  set ystar : ZMod k → ℝ := fun i => ε * (l ⬝ᵥ x (lab i)) with hys
  have hystar : IsCyclicUnimodal ystar := hord ε hεpos _ hzst
  have hyinj : Function.Injective ystar := hystar.1
  -- convergence of depths
  set ys : ℕ → ZMod k → ℝ := fun m i => (((G m).trace⁻¹ • G m) *ᵥ u) ⬝ᵥ x (lab i) with hysdef
  have ht : ∀ i, Tendsto (fun m => ys m i) atTop (𝓝 (ystar i)) := by
    intro i
    have hc : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => (M *ᵥ u) ⬝ᵥ x (lab i)) := by
      simp only [dotProduct, mulVec]; fun_prop
    have := (hc.tendsto Gs).comp hlim
    have e : (Gs *ᵥ u) ⬝ᵥ x (lab i) = ystar i := by
      rw [hGu, smul_dotProduct]; rfl
    rw [e] at this
    exact this
  have hev := eventually_order ys atTop ystar hyinj ht
  refine hev.mono (fun m hm => ?_)
  refine ⟨u, k, inferInstance, lab, hk, hinj, ?_, ?_⟩
  · intro m' i h1 h2
    have := hε m' i h1 h2
    exact this
  · have hord' : IsCyclicUnimodal (fun i => ys m i) :=
      order_unimodal (fun i j => hm i j) hystar
    have e : (fun i => depth (G m) u (x (lab i))) = fun i => (G m).trace * ys m i := by
      funext i
      simp only [depth, hysdef, smul_mulVec, smul_dotProduct, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (htr m).ne', one_mul]
    rw [e]
    exact hord _ (htr m) _ hord'

lemma depth_cell (G : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → Fin 3 → ℝ) (a y : Fin 3 → ℝ) :
    depth G (∑ i, a i • u i) y = (∑ i, a i • (G *ᵥ u i)) ⬝ᵥ y := by
  simp [depth, mulVec_sum, mulVec_smul]

lemma same_order {k : ℕ} [NeZero k] {z z' : ZMod k → ℝ} (hz' : Function.Injective z')
    (h : ∀ i j, z' i < z' j → z i < z j) : ∀ i j, z i < z j ↔ z' i < z' j := by
  intro i j
  refine ⟨fun h1 => ?_, h i j⟩
  by_contra hn
  rcases lt_trichotomy (z' i) (z' j) with h2 | h2 | h2
  · exact hn h2
  · have := hz' h2; subst this; exact lt_irrefl _ h1
  · have := h j i h2; linarith

theorem defeatCellCriterion : DefeatCellCriterion := by
  intro x k _ lab u G hk hinj hrim
  set X : ZMod k → Fin 3 → ℝ := fun j => x (lab j) with hX
  set g : Fin 3 → Fin 3 → ℝ := fun i => G *ᵥ u i with hg
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, hun⟩
    exact ⟨_, k, inferInstance, lab, hk, hinj, hrim a ha, hun⟩
  · constructor
    · -- no view  ->  separating functionals
      intro hno l0 hl0
      set Q : Set (Fin 3 → ℝ) := {l | ∀ i j, l0 ⬝ᵥ X i < l0 ⬝ᵥ X j → l ⬝ᵥ X i < l ⬝ᵥ X j} with hQ
      set C : Set (Fin 3 → ℝ) := {l | ∃ a : Fin 3 → ℝ, (∀ i, 0 < a i) ∧ l = ∑ i, a i • g i} with hC
      have hQconv : Convex ℝ Q := by
        intro l1 h1 l2 h2 s t hs ht hst i j hij
        have a1 := h1 i j hij
        have a2 := h2 i j hij
        show (s • l1 + t • l2) ⬝ᵥ X i < (s • l1 + t • l2) ⬝ᵥ X j
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rcases hs.eq_or_lt with rfl | hs'
        · have : t = 1 := by linarith
          subst this; simpa using a2
        · nlinarith
      have hQopen : IsOpen Q := by
        rw [isOpen_iff_mem_nhds]
        intro l hl
        have : ∀ᶠ l' in 𝓝 l, ∀ i j, l0 ⬝ᵥ X i < l0 ⬝ᵥ X j → l' ⬝ᵥ X i < l' ⬝ᵥ X j := by
          rw [Filter.eventually_all]; intro i
          rw [Filter.eventually_all]; intro j
          by_cases h : l0 ⬝ᵥ X i < l0 ⬝ᵥ X j
          · have hc : Continuous (fun l' : Fin 3 → ℝ => l' ⬝ᵥ X j - l' ⬝ᵥ X i) := by
              simp only [dotProduct]; fun_prop
            have h0 := hl i j h
            have := (hc.tendsto l).eventually (lt_mem_nhds (show 0 < l ⬝ᵥ X j - l ⬝ᵥ X i by linarith))
            exact this.mono (fun l' hl' _ => by linarith)
          · exact Filter.Eventually.of_forall (fun l' h' => absurd h' h)
        exact this
      have hCconv : Convex ℝ C := by
        rintro l1 ⟨a, ha, rfl⟩ l2 ⟨b, hb, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * a i + t * b i, fun i => ?_, ?_⟩
        · rcases hs.eq_or_lt with rfl | hs'
          · have : t = 1 := by linarith
            subst this; simpa using hb i
          · have := ha i; have := hb i; nlinarith [mul_pos hs' (ha i), mul_nonneg ht (hb i).le]
        · simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [add_smul, mul_smul, mul_smul]
      have hdisj : Disjoint Q C := by
        rw [Set.disjoint_left]
        rintro l hlQ ⟨a, ha, rfl⟩
        apply hno
        refine ⟨a, ha, ?_⟩
        have hz : IsCyclicUnimodal (fun j => (∑ i, a i • g i) ⬝ᵥ X j) :=
          order_unimodal (same_order hl0.1 (fun i j h => hlQ i j h)) hl0
        simpa only [depth_cell] using hz
      obtain ⟨f, c, hfQ, hfC⟩ := geometric_hahn_banach_open hQconv hQopen hCconv hdisj
      have hlin : ∀ l : Fin 3 → ℝ, f l = -(l ⬝ᵥ (fun i => -f (fun j => if i = j then 1 else 0))) := by
        intro l
        have := LinearMap.pi_apply_eq_sum_univ (f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) l
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [this]; simp [dotProduct]
      set w : Fin 3 → ℝ := fun i => -f (fun j => if i = j then 1 else 0) with hw
      have hQscale : ∀ l ∈ Q, ∀ t : ℝ, 0 < t → t • l ∈ Q := by
        intro l hl t ht i j hij
        have := hl i j hij
        simp only [smul_dotProduct, smul_eq_mul]
        exact mul_lt_mul_of_pos_left this ht
      have hCscale : ∀ l ∈ C, ∀ t : ℝ, 0 < t → t • l ∈ C := by
        rintro l ⟨a, ha, rfl⟩ t ht
        refine ⟨fun i => t * a i, fun i => mul_pos ht (ha i), ?_⟩
        simp only [Finset.smul_sum, mul_smul]
      have hfQ0 : ∀ l ∈ Q, f l ≤ 0 := by
        intro l hl
        by_contra hpos; push Not at hpos
        have := hfQ _ (hQscale l hl ((|c| + 1) / f l) (by positivity))
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
        linarith [le_abs_self c]
      have hfC0 : ∀ l ∈ C, 0 ≤ f l := by
        intro l hl
        by_contra hneg; push Not at hneg
        have := hfC _ (hCscale l hl ((|c| + 1) / (-f l)) (by have := neg_pos.2 hneg; positivity))
        rw [map_smul, smul_eq_mul] at this
        have e : (|c| + 1) / (-f l) * f l = -(|c| + 1) := by
          rw [div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hneg.ne)]; ring
        rw [e] at this
        linarith [neg_abs_le c]
      have hl0Q : l0 ∈ Q := fun i j h => h
      have hone : (∑ i, (1 : ℝ) • g i) ∈ C := ⟨fun _ => 1, fun _ => one_pos, rfl⟩
      have hwne : w ≠ 0 := by
        intro h0
        have hf0 : ∀ l, f l = 0 := by intro l; rw [hlin l, h0]; simp
        have h1 := hfQ _ hl0Q
        have h2 := hfC _ hone
        rw [hf0] at h1 h2; linarith
      refine ⟨w, hwne, ?_, ?_⟩
      · intro l hl
        have := hfQ0 l hl
        rw [hlin l] at this
        linarith
      · intro i
        -- g_i is a limit of points of C
        by_contra hpos; push Not at hpos
        have hfg : f (g i) < 0 := by
          rw [hlin (g i)]; linarith
        set S := ∑ j, g j with hS
        set δ : ℝ := (-f (g i)) / (2 * (|f S| + 1)) with hδ
        have hδpos : 0 < δ := by
          have := neg_pos.2 hfg
          positivity
        have hmem : (g i + δ • S) ∈ C := by
          refine ⟨fun j => (if j = i then 1 else 0) + δ, fun j => ?_, ?_⟩
          · show 0 < (if j = i then (1:ℝ) else 0) + δ
            split_ifs <;> linarith
          · symm
            simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
              Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.smul_sum, hS]
        have := hfC0 _ hmem
        rw [map_add, map_smul, smul_eq_mul] at this
        have h3 : δ * f S ≤ δ * |f S| := mul_le_mul_of_nonneg_left (le_abs_self _) hδpos.le
        have h4 : 2 * (δ * |f S|) + 2 * δ = -f (g i) := by
          have : (|f S| + 1) ≠ 0 := by positivity
          rw [hδ]; field_simp; ring
        linarith
    · -- separating functionals  ->  no view
      intro hall ⟨a, ha, hun⟩
      set l : Fin 3 → ℝ := ∑ i, a i • g i with hl
      have hl0 : IsCyclicUnimodal (fun j => l ⬝ᵥ X j) := by simpa only [depth_cell] using hun
      obtain ⟨w, hw0, hQ, hgw⟩ := hall l hl0
      have hlw : l ⬝ᵥ w ≤ 0 := by
        rw [hl, sum_dotProduct]
        refine Finset.sum_nonpos (fun i _ => ?_)
        rw [smul_dotProduct, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (ha i).le (hgw i)
      -- l - δ w lies in the chamber of l for small δ
      have hev : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i j, l ⬝ᵥ X i < l ⬝ᵥ X j →
          (l - δ • w) ⬝ᵥ X i < (l - δ • w) ⬝ᵥ X j := by
        rw [Filter.eventually_all]; intro i
        rw [Filter.eventually_all]; intro j
        by_cases h : l ⬝ᵥ X i < l ⬝ᵥ X j
        · have hc : Continuous (fun δ : ℝ => (l - δ • w) ⬝ᵥ X j - (l - δ • w) ⬝ᵥ X i) := by
            simp only [dotProduct]; fun_prop
          have := (hc.tendsto 0).eventually (lt_mem_nhds
            (show 0 < (l - (0:ℝ) • w) ⬝ᵥ X j - (l - (0:ℝ) • w) ⬝ᵥ X i by simpa using sub_pos.2 h))
          exact this.mono (fun δ hδ _ => by linarith)
        · exact Filter.Eventually.of_forall (fun δ h' => absurd h' h)
      obtain ⟨δ, hδ, hδpos⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).and
        (self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0))).exists
      have h1 := hQ (l - δ • w) hδ
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul] at h1
      have : 0 < w ⬝ᵥ w := by
        rcases (dotProduct_self_star_nonneg w).eq_or_lt with h | h
        · exact absurd (dotProduct_self_eq_zero.mp (by simpa using h.symm)) hw0
        · simpa using h
      have : 0 < δ * (w ⬝ᵥ w) := mul_pos hδpos this
      linarith

end MinimalityExtra
