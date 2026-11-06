module

public import Mathlib
public import MinimalityExtra

/-!
# Pairs of tests: the angle lemma, invisibility signs, two interior far corners
-/

@[expose] public section

open Matrix

namespace MinimalityExtra

/-- Key step: if `v = Σ c q (x q.1 - x q.2)` over pairs with `z q.2 < z q.1`, where
`z i = l ⬝ᵥ x i`, `c ≥ 0`, then `l ⬝ᵥ v ≥ 0`, and `> 0` when `v ≠ 0`. -/
theorem cone_pos {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (l v : Fin 3 → ℝ) (hv : v ≠ 0)
    (c : ZMod k × ZMod k → ℝ) (hc : ∀ q, 0 ≤ c q)
    (hsum : v = ∑ q ∈ Finset.univ.filter (fun q : ZMod k × ZMod k => l ⬝ᵥ x q.2 < l ⬝ᵥ x q.1),
            c q • (x q.1 - x q.2)) :
    0 < l ⬝ᵥ v := by
  have h : l ⬝ᵥ v = ∑ q ∈ Finset.univ.filter
      (fun q : ZMod k × ZMod k => l ⬝ᵥ x q.2 < l ⬝ᵥ x q.1),
        c q * (l ⬝ᵥ x q.1 - l ⬝ᵥ x q.2) := by
    rw [hsum, dotProduct_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [dotProduct_smul, dotProduct_sub, smul_eq_mul]
  rw [h]
  have hnn : 0 ≤ ∑ q ∈ Finset.univ.filter
      (fun q : ZMod k × ZMod k => l ⬝ᵥ x q.2 < l ⬝ᵥ x q.1),
        c q * (l ⬝ᵥ x q.1 - l ⬝ᵥ x q.2) :=
    Finset.sum_nonneg fun q hq => mul_nonneg (hc q) (by
      have := (Finset.mem_filter.1 hq).2; linarith)
  rcases hnn.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    apply hv
    rw [hsum]
    apply Finset.sum_eq_zero
    intro q hq
    have hq' := (Finset.mem_filter.1 hq).2
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun q hq => mul_nonneg (hc q) (by
      have := (Finset.mem_filter.1 hq).2; linarith))).1 h1.symm q hq
    have : c q = 0 := by
      rcases mul_eq_zero.1 hterm with h | h
      · exact h
      · linarith
    simp [this]

theorem angleLemma : AngleLemma := by
  intro k₁ k₂ _ _ x₁ x₂ u₁ u₂ hu₁ hu₂ H G hG i1 i2
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have n1 : ¬ _ := h1
  have n2 : ¬ _ := h2
  obtain ⟨ε, hε, ⟨c1, hc1, hs1⟩, ⟨c2, hc2, hs2⟩⟩ :=
    H _ _ i1 (fun h => h1 h) i2 (fun h => h2 h)
  have e1 : ε • u₂ ≠ 0 := by
    rcases hε with rfl | rfl <;> simpa using hu₂
  have e2 : -ε • u₁ ≠ 0 := by
    rcases hε with rfl | rfl <;> simpa using hu₁
  have p1 := cone_pos x₁ (G *ᵥ u₁) _ e1 c1 hc1 hs1
  have p2 := cone_pos x₂ (G *ᵥ u₂) _ e2 c2 hc2 hs2
  have hs : G.transpose = G := hG.isHermitian.eq
  have sym : (G *ᵥ u₁) ⬝ᵥ u₂ = (G *ᵥ u₂) ⬝ᵥ u₁ := by
    have h10 : G 1 0 = G 0 1 := by simpa using congrFun (congrFun hs 0) 1
    have h20 : G 2 0 = G 0 2 := by simpa using congrFun (congrFun hs 0) 2
    have h21 : G 2 1 = G 1 2 := by simpa using congrFun (congrFun hs 1) 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
    ring
  rw [dotProduct_smul, smul_eq_mul] at p1 p2
  rw [sym] at p1
  rcases hε with rfl | rfl <;> linarith

theorem invisibilitySign : InvisibilitySign := by
  intro W u v hinv φ₁ h₁ φ₂ h₂
  by_contra hcon
  have ha := hinv φ₁ h₁
  have hb := hinv φ₂ h₂
  have hneg : (φ₁ ⬝ᵥ v) * (φ₂ ⬝ᵥ v) < 0 := by
    rcases lt_or_gt_of_ne (mul_ne_zero ha hb) with h | h
    · exact h
    · exact absurd h hcon
  set a := φ₁ ⬝ᵥ v
  set b := φ₂ ⬝ᵥ v
  have hapos : 0 < |a| := abs_pos.2 ha
  have hbpos : 0 < |b| := abs_pos.2 hb
  have hz : (|b| • φ₁ + |a| • φ₂) ⬝ᵥ v = 0 := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    change |b| * a + |a| * b = 0
    rcases lt_or_gt_of_ne ha with h | h <;> rcases lt_or_gt_of_ne hb with h' | h'
    · nlinarith
    · rw [abs_of_neg h, abs_of_pos h']; ring
    · rw [abs_of_pos h, abs_of_neg h']; ring
    · nlinarith
  have hmem : |b| • φ₁ + |a| • φ₂ ∈ FailCone W u := by
    refine ⟨?_, fun w hw => ?_⟩
    · rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      have := h₁.1; have := h₂.1; positivity
    · rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      have := h₁.2 w hw; have := h₂.2 w hw; positivity
  exact hinv _ hmem hz

theorem invisibilitySignPair : InvisibilitySignPair := by
  intro 𝒲₁ 𝒲₂ u₁ u₂ _ _ hsign G hG W₁ hW₁ W₂ hW₂ ⟨h1, h2⟩
  apply hsign W₁ hW₁ _ h1 W₂ hW₂ _ h2
  have hs : G.transpose = G := hG.isHermitian.eq
  have h10 : G 1 0 = G 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h20 : G 2 0 = G 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h21 : G 2 1 = G 1 2 := by simpa using congrFun (congrFun hs 1) 2
  have : (G *ᵥ u₁) ⬝ᵥ u₂ = (G *ᵥ u₂) ⬝ᵥ u₁ := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
    ring
  rw [this]

theorem invisibilityEdge : InvisibilityEdge := by
  intro W u v e c he hec φ hφ
  have := hφ.2 e he
  rw [hec, dotProduct_smul, smul_eq_mul] at this
  exact this

lemma convpos {t A B : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hA : 0 < A) (hB : 0 < B) :
    0 < (1 - t) * A + t * B := by
  rcases ht0.eq_or_lt with h | h
  · subst h; simpa using hA
  · nlinarith [mul_pos h hB, mul_nonneg (sub_nonneg.2 ht1) hA.le]

theorem invisibilityFlat : InvisibilityFlat := by
  intro W u v x y z t κ ht0 ht1 hx
  have key : ∀ φ : Fin 3 → ℝ, φ ⬝ᵥ (x - ((1 - t) • y + t • z)) =
      (1 - t) * (φ ⬝ᵥ (x - y)) + t * (φ ⬝ᵥ (x - z)) := by
    intro φ
    have : x - ((1 - t) • y + t • z) = (1 - t) • (x - y) + t • (x - z) := by
      ext j; simp; ring
    rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have key' : ∀ φ : Fin 3 → ℝ, φ ⬝ᵥ (x - ((1 - t) • y + t • z)) =
      -((1 - t) * (φ ⬝ᵥ (y - x)) + t * (φ ⬝ᵥ (z - x))) := by
    intro φ
    rw [key]; simp only [dotProduct_sub]; ring
  have kv : ∀ φ : Fin 3 → ℝ, φ ⬝ᵥ (x - ((1 - t) • y + t • z)) = κ * (φ ⬝ᵥ v) := by
    intro φ; rw [hx, dotProduct_smul, smul_eq_mul]
  refine ⟨fun ⟨hy, hz⟩ φ hφ => ?_, fun ⟨hy, hz⟩ φ hφ => ?_⟩
  · rw [← kv, key]
    exact convpos ht0 ht1 (hφ.2 _ hy) (hφ.2 _ hz)
  · rw [← kv, key']
    have := convpos ht0 ht1 (hφ.2 _ hy) (hφ.2 _ hz)
    linarith

theorem thmF (v l : Fin 3 → ℝ) (hl : 0 < l ⬝ᵥ v) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ v = l := by
  set s := l ⬝ᵥ v with hs
  have hs0 : s ≠ 0 := hl.ne'
  set P : Matrix (Fin 3) (Fin 3) ℝ := 1 - (1/s) • vecMulVec v l with hP
  have hPx : ∀ x, P *ᵥ x = x - ((l ⬝ᵥ x)/s) • v := by
    intro x
    simp [hP, sub_mulVec, smul_mulVec, vecMulVec_mulVec]
    ext i; simp; ring
  have hPv : P *ᵥ v = 0 := by rw [hPx]; simp [← hs, div_self hs0]
  refine ⟨(1/s) • vecMulVec l l + Pᵀ * P, ?_, ?_⟩
  · have hq : ∀ x : Fin 3 → ℝ, x ⬝ᵥ (((1/s) • vecMulVec l l + Pᵀ * P) *ᵥ x)
        = (l ⬝ᵥ x)^2 / s + (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
      intro x
      have h2 : x ⬝ᵥ (Pᵀ *ᵥ (P *ᵥ x)) = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
        rw [dotProduct_mulVec, vecMul_transpose]
      rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, h2]
      simp [smul_mulVec, vecMulVec_mulVec, dotProduct_smul]
      rw [dotProduct_comm x l]; ring
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp [Matrix.conjTranspose, transpose_add, Matrix.transpose_mul, vecMulVec, mul_comm]
    · intro x hx
      simp only [star_trivial]
      rw [hq]
      have h1 : 0 ≤ (l ⬝ᵥ x)^2 / s := by positivity
      by_cases hlx : l ⬝ᵥ x = 0
      · have : P *ᵥ x = x := by rw [hPx, hlx]; simp
        rw [this, hlx]
        have : 0 < x ⬝ᵥ x := by
          rcases (dotProduct_self_eq_zero (v := x)).not.mpr hx |> fun h => lt_of_le_of_ne (dotProduct_self_star_nonneg x) (Ne.symm h) with h
          exact h
        simpa using this
      · have : 0 < (l ⬝ᵥ x)^2 / s := by positivity
        have h2 : 0 ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := dotProduct_self_star_nonneg _
        linarith
  · rw [add_mulVec, ← mulVec_mulVec, hPv]
    simp [smul_mulVec, vecMulVec_mulVec, ← hs]
    ext i; simp; field_simp


lemma tp_eq_zero (e w y n : Fin 3 → ℝ) (hn : n ≠ 0) (he : n ⬝ᵥ e = 0) (hw : n ⬝ᵥ w = 0)
    (hy : n ⬝ᵥ y = 0) : tripleProduct e w y = 0 := by
  simp only [dotProduct, Fin.sum_univ_three] at he hw hy
  have h : ∀ j, tripleProduct e w y * n j = 0 := by
    intro j
    fin_cases j
    · simp only [tripleProduct, Fin.zero_eta]
      linear_combination (w 1 * y 2 - w 2 * y 1) * he + (y 1 * e 2 - y 2 * e 1) * hw +
        (e 1 * w 2 - e 2 * w 1) * hy
    · simp only [tripleProduct, Fin.mk_one]
      linear_combination (w 2 * y 0 - w 0 * y 2) * he + (y 2 * e 0 - y 0 * e 2) * hw +
        (e 2 * w 0 - e 0 * w 2) * hy
    · simp only [tripleProduct, Fin.reduceFinMk]
      linear_combination (w 0 * y 1 - w 1 * y 0) * he + (y 0 * e 1 - y 1 * e 0) * hw +
        (e 0 * w 1 - e 1 * w 0) * hy
  by_contra hne
  apply hn
  ext j
  have := h j
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hne
  · simpa using h1

lemma zmod_num_ne {k : ℕ} [NeZero k] (n : ℕ) (h0 : 0 < n) (hn : n < k) :
    ((n : ℕ) : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd h0 h
  omega

lemma two_peaks {k : ℕ} [NeZero k] (hk : 4 ≤ k) (z : ZMod k → ℝ) (hz : Function.Injective z)
    (p0 q : ZMod k) (c : ℝ) (h1 : z (p0 - 1) < c) (h2 : z (p0 + 1) < c) (h3 : c < z p0)
    (hq : c < z q) (hq1 : q ≠ p0 - 1) (hq2 : q ≠ p0) (hq3 : q ≠ p0 + 1) :
    2 ≤ (Finset.univ.filter (fun j : ZMod k => z (j - 1) < z j ∧ z (j + 1) < z j)).card := by
  haveI : Nontrivial (ZMod k) := ZMod.nontrivial_iff.2 (by omega)
  set S : Finset (ZMod k) := Finset.univ.filter (fun j => j ≠ p0 - 1 ∧ j ≠ p0 ∧ j ≠ p0 + 1)
    with hS
  have hqS : q ∈ S := by simp [hS, hq1, hq2, hq3]
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S z ⟨q, hqS⟩
  have hm : m ≠ p0 - 1 ∧ m ≠ p0 ∧ m ≠ p0 + 1 := by simpa [hS] using hmS
  have hzm : c < z m := lt_of_lt_of_le hq (hmax q hqS)
  have n1 : ∀ x : ZMod k, x - 1 ≠ x := fun x h => by simp at h
  have n2 : ∀ x : ZMod k, x + 1 ≠ x := fun x h => by simp at h
  have hmloc : z (m - 1) < z m ∧ z (m + 1) < z m := by
    constructor
    · by_cases hj : m - 1 ∈ S
      · exact lt_of_le_of_ne (hmax _ hj) (fun h => n1 m (hz h))
      · have : m - 1 = p0 - 1 ∨ m - 1 = p0 ∨ m - 1 = p0 + 1 := by
          by_contra hh
          push Not at hh
          exact hj (by simp [hS, hh.1, hh.2.1, hh.2.2])
        rcases this with h | h | h
        · rw [h]; linarith
        · exfalso; apply hm.2.2; rw [← sub_eq_zero] at h ⊢; rw [← h]; ring
        · rw [h]; linarith
    · by_cases hj : m + 1 ∈ S
      · exact lt_of_le_of_ne (hmax _ hj) (fun h => n2 m (hz h))
      · have : m + 1 = p0 - 1 ∨ m + 1 = p0 ∨ m + 1 = p0 + 1 := by
          by_contra hh
          push Not at hh
          exact hj (by simp [hS, hh.1, hh.2.1, hh.2.2])
        rcases this with h | h | h
        · rw [h]; linarith
        · exfalso; apply hm.1; rw [← sub_eq_zero] at h ⊢; rw [← h]; ring
        · rw [h]; linarith
  have hp0 : z (p0 - 1) < z p0 ∧ z (p0 + 1) < z p0 := ⟨by linarith, by linarith⟩
  have hne : p0 ≠ m := fun h => hm.2.1 h.symm
  calc 2 = ({p0, m} : Finset (ZMod k)).card := (Finset.card_pair hne).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [*]

lemma perturb {ι κ : Type} [Finite ι] [Finite κ] (ψ u : Fin 3 → ℝ) (v : ι → Fin 3 → ℝ)
    (d : κ → Fin 3 → ℝ) (hd : ∀ q, d q ≠ 0) (hψ : ∀ m, 0 < ψ ⬝ᵥ v m) :
    ∃ φ : Fin 3 → ℝ, (∀ m, 0 < φ ⬝ᵥ v m) ∧ ∀ q, φ ⬝ᵥ d q ≠ 0 := by
  haveI := Fintype.ofFinite κ
  let f : κ → Module.Dual ℝ (Fin 3 → ℝ) := fun q =>
    { toFun := fun w => d q ⬝ᵥ w
      map_add' := fun a b => by simp [dotProduct_add]
      map_smul' := fun r a => by simp [dotProduct_smul] }
  obtain ⟨w, hw⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (fun q => by
    by_contra hh
    push Not at hh
    apply hd q
    ext j
    have := hh (Pi.single j 1)
    simpa [f, dotProduct_single] using this)
  have hw' : ∀ q, d q ⬝ᵥ w ≠ 0 := hw
  have hc : ∀ᶠ t in nhds (0:ℝ), ∀ m, 0 < ψ ⬝ᵥ v m + t * (w ⬝ᵥ v m) := by
    rw [Filter.eventually_all]
    intro m
    have : ContinuousAt (fun t : ℝ => ψ ⬝ᵥ v m + t * (w ⬝ᵥ v m)) 0 := by fun_prop
    exact this.eventually (lt_mem_nhds (by simpa using hψ m))
  obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.1 hc
  let B : Finset ℝ := Finset.univ.image (fun q => -(ψ ⬝ᵥ d q) / (d q ⬝ᵥ w))
  obtain ⟨t, ht, htB⟩ := (Set.Ioo_infinite hε).exists_notMem_finset B
  have ht0 : 0 < t := ht.1
  refine ⟨ψ + t • w, fun m => ?_, fun q => ?_⟩
  · have := hεt (y := t) (by rw [Real.dist_eq]; simp [abs_of_pos ht0]; exact ht.2) m
    simpa [add_dotProduct, smul_dotProduct, mul_comm] using this
  · intro h
    apply htB
    simp only [B, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨q, ?_⟩
    have hq := hw' q
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm w (d q)] at h
    field_simp
    linarith

lemma core {k : ℕ} [NeZero k] (hk : 4 ≤ k) (p : ZMod k → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (hinj : Function.Injective p) (ψ : Fin 3 → ℝ) (p0 q : ZMod k) (hψu : 0 < ψ ⬝ᵥ u)
    (a1 : 0 < ψ ⬝ᵥ (p p0 - p (p0 - 1))) (a2 : 0 < ψ ⬝ᵥ (p p0 - p (p0 + 1)))
    (a3 : 0 < ψ ⬝ᵥ (p q - p (p0 - 1))) (a4 : 0 < ψ ⬝ᵥ (p q - p (p0 + 1)))
    (hq1 : q ≠ p0 - 1) (hq2 : q ≠ p0) (hq3 : q ≠ p0 + 1) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
        Function.Injective (fun j => (G *ᵥ u) ⬝ᵥ p j) ∧
        2 ≤ (Finset.univ.filter (fun j : ZMod k =>
          (G *ᵥ u) ⬝ᵥ p (j - 1) < (G *ᵥ u) ⬝ᵥ p j ∧
          (G *ᵥ u) ⬝ᵥ p (j + 1) < (G *ᵥ u) ⬝ᵥ p j)).card := by
  let v : Fin 5 → Fin 3 → ℝ := ![u, p p0 - p (p0 - 1), p p0 - p (p0 + 1),
    p q - p (p0 - 1), p q - p (p0 + 1)]
  let d : {r : ZMod k × ZMod k // r.1 ≠ r.2} → Fin 3 → ℝ := fun r => p r.1.1 - p r.1.2
  haveI : Finite {r : ZMod k × ZMod k // r.1 ≠ r.2} := inferInstance
  obtain ⟨φ, hφ, hφd⟩ := perturb ψ u v d (fun r h => by
      apply r.2; apply hinj; exact sub_eq_zero.1 h) (fun m => by
    fin_cases m
    · simpa [v] using hψu
    · simpa [v] using a1
    · simpa [v] using a2
    · simpa [v] using a3
    · simpa [v] using a4)
  have b0 : 0 < φ ⬝ᵥ u := by simpa [v] using hφ 0
  have b1 : 0 < φ ⬝ᵥ (p p0 - p (p0 - 1)) := by simpa [v] using hφ 1
  have b2 : 0 < φ ⬝ᵥ (p p0 - p (p0 + 1)) := by simpa [v] using hφ 2
  have b3 : 0 < φ ⬝ᵥ (p q - p (p0 - 1)) := by simpa [v] using hφ 3
  have b4 : 0 < φ ⬝ᵥ (p q - p (p0 + 1)) := by simpa [v] using hφ 4
  rw [dotProduct_sub] at b1 b2 b3 b4
  obtain ⟨G, hG, hGu⟩ := thmF u φ b0
  refine ⟨G, hG, ?_⟩
  simp only [hGu]
  have hinj' : Function.Injective (fun j => φ ⬝ᵥ p j) := by
    intro a b hab
    by_contra hne
    apply hφd ⟨(a, b), hne⟩
    simp only [d, dotProduct_sub]
    exact sub_eq_zero.2 hab
  refine ⟨hinj', ?_⟩
  have hm : max (φ ⬝ᵥ p (p0 - 1)) (φ ⬝ᵥ p (p0 + 1)) < min (φ ⬝ᵥ p p0) (φ ⬝ᵥ p q) := by
    apply max_lt <;> apply lt_min <;> linarith
  obtain ⟨c, hc1, hc2⟩ := exists_between hm
  exact two_peaks hk (fun j => φ ⬝ᵥ p j) hinj' p0 q c
    (lt_of_le_of_lt (le_max_left _ _) hc1) (lt_of_le_of_lt (le_max_right _ _) hc1)
    (lt_of_lt_of_le hc2 (min_le_left _ _)) (lt_of_lt_of_le hc2 (min_le_right _ _)) hq1 hq2 hq3

theorem twoInteriorCornersNeverMetricFree : TwoInteriorCornersNeverMetricFree := by
  intro k _ hk p u i hinj hcop hnu
  have c1 : ((1 : ℕ) : ZMod k) ≠ 0 := zmod_num_ne 1 (by omega) (by omega)
  have c2 : ((2 : ℕ) : ZMod k) ≠ 0 := zmod_num_ne 2 (by omega) (by omega)
  have c3 : ((3 : ℕ) : ZMod k) ≠ 0 := zmod_num_ne 3 (by omega) (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at c1 c2 c3
  set nv : Fin 3 → ℝ := ![(p (i+2) - p i) 1 * (p (i+3) - p (i+1)) 2 -
      (p (i+2) - p i) 2 * (p (i+3) - p (i+1)) 1,
    (p (i+2) - p i) 2 * (p (i+3) - p (i+1)) 0 - (p (i+2) - p i) 0 * (p (i+3) - p (i+1)) 2,
    (p (i+2) - p i) 0 * (p (i+3) - p (i+1)) 1 - (p (i+2) - p i) 1 * (p (i+3) - p (i+1)) 0]
    with hnv
  have htp : ∀ y, tripleProduct (p (i + 2) - p i) (p (i + 3) - p (i + 1)) y = nv ⬝ᵥ y := by
    intro y
    simp [tripleProduct, hnv, dotProduct, Fin.sum_univ_three]
  have hnu' : nv ⬝ᵥ u ≠ 0 := by rw [← htp]; exact hnu
  have hn0 : nv ≠ 0 := fun h => hnu' (by rw [h]; simp)
  have e1 : nv ⬝ᵥ (p (i + 2) - p i) = 0 := by
    simp [hnv, dotProduct, Fin.sum_univ_three]; ring
  have e2 : nv ⬝ᵥ (p (i + 3) - p (i + 1)) = 0 := by
    simp [hnv, dotProduct, Fin.sum_univ_three]; ring
  -- a functional ψ with ψ·u > 0, ψ ⊥ the diagonals, ψ·(b - a) ≠ 0
  have key : ∃ ψ : Fin 3 → ℝ, 0 < ψ ⬝ᵥ u ∧ ψ ⬝ᵥ (p (i + 2) - p i) = 0 ∧
      ψ ⬝ᵥ (p (i + 3) - p (i + 1)) = 0 ∧ ψ ≠ 0 := by
    rcases lt_or_gt_of_ne hnu' with h | h
    · exact ⟨-nv, by rw [neg_dotProduct]; linarith, by rw [neg_dotProduct, e1]; simp,
        by rw [neg_dotProduct, e2]; simp, neg_ne_zero.2 hn0⟩
    · exact ⟨nv, h, e1, e2, hn0⟩
  obtain ⟨ψ, hψu, f1, f2, hψ0⟩ := key
  have hba : ψ ⬝ᵥ (p (i + 1) - p i) ≠ 0 := by
    intro h0
    apply hcop
    apply tp_eq_zero _ _ _ ψ hψ0 h0 f1
    have : p (i + 3) - p i = (p (i + 3) - p (i + 1)) + (p (i + 1) - p i) := by abel
    rw [this, dotProduct_add, f2, h0]; simp
  -- notation
  have d1 : ψ ⬝ᵥ (p (i + 1) - p i) = ψ ⬝ᵥ p (i + 1) - ψ ⬝ᵥ p i := dotProduct_sub _ _ _
  have d2 : ψ ⬝ᵥ (p (i + 2) - p i) = ψ ⬝ᵥ p (i + 2) - ψ ⬝ᵥ p i := dotProduct_sub _ _ _
  have d3 : ψ ⬝ᵥ (p (i + 3) - p (i + 1)) = ψ ⬝ᵥ p (i + 3) - ψ ⬝ᵥ p (i + 1) :=
    dotProduct_sub _ _ _
  have ne : ∀ a b : ZMod k, a - b = 0 → a = b := fun a b h => sub_eq_zero.1 h
  rcases lt_or_gt_of_ne hba with h | h
  · -- b < a : peak at i+2 (c), valleys i+1 and i+3, q = i
    apply core hk p u hinj ψ (i + 2) i hψu
    · have : i + 2 - 1 = i + 1 := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 2 + 1 = i + 3 := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 2 - 1 = i + 1 := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 2 + 1 = i + 3 := by ring
      rw [this, dotProduct_sub]; linarith
    · intro hh; apply c1; linear_combination -hh
    · intro hh; apply c2; linear_combination -hh
    · intro hh; apply c3; linear_combination -hh
  · -- b > a : peak at i+1 (b), valleys i and i+2, q = i+3
    apply core hk p u hinj ψ (i + 1) (i + 3) hψu
    · have : i + 1 - 1 = i := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 1 + 1 = i + 2 := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 1 - 1 = i := by ring
      rw [this, dotProduct_sub]; linarith
    · have : i + 1 + 1 = i + 2 := by ring
      rw [this, dotProduct_sub]; linarith
    · intro hh; apply c3; linear_combination hh
    · intro hh; apply c2; linear_combination hh
    · intro hh; apply c1; linear_combination hh

#print axioms angleLemma
#print axioms twoInteriorCornersNeverMetricFree
#print axioms invisibilitySign
#print axioms invisibilitySignPair
#print axioms invisibilityEdge
#print axioms invisibilityFlat

end MinimalityExtra
