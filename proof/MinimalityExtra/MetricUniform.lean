module

public import MinimalityExtra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# Metric-uniform unimodality: proofs

Proofs of the metric-uniform statements of `MinimalityExtra.lean` (Mathlib only; `MinimalityExtra` is used for
`IsCyclicUnimodal`).
-/

open Matrix

namespace MinimalityExtra


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

lemma cramer_neg (l n e w y : Fin 3 → ℝ) (hn : n ≠ 0) (he : n ⬝ᵥ e = 0) (hw : n ⬝ᵥ w = 0)
    (hy : n ⬝ᵥ y = 0) (hD : 0 < tripleProduct e w n) (hB : 0 < tripleProduct e y n)
    (hA : 0 < tripleProduct y w n) (hle : l ⬝ᵥ e < 0) (hlw : l ⬝ᵥ w < 0) : l ⬝ᵥ y < 0 := by
  have h0 := tp_eq_zero e w y n hn he hw hy
  have key : tripleProduct e w n * (l ⬝ᵥ y) =
      tripleProduct y w n * (l ⬝ᵥ e) + tripleProduct e y n * (l ⬝ᵥ w) +
        tripleProduct e w y * (l ⬝ᵥ n) := by
    simp only [tripleProduct, dotProduct, Fin.sum_univ_three]; ring
  rw [h0, zero_mul, add_zero] at key
  have : tripleProduct e w n * (l ⬝ᵥ y) < 0 := by
    rw [key]; nlinarith [mul_neg_of_pos_of_neg hA hle, mul_neg_of_pos_of_neg hB hlw]
  by_contra hh
  push Not at hh
  nlinarith [mul_nonneg hD.le hh]

/-- a local maximum of an affine function on a strictly convex planar cycle is the global
strict maximum -/
lemma peak_is_max {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → Fin 3 → ℝ) (n : Fin 3 → ℝ)
    (hx : IsStrictConvexPlanarCycle x n) (l : Fin 3 → ℝ) (i : ZMod k)
    (h1 : l ⬝ᵥ x (i - 1) < l ⬝ᵥ x i) (h2 : l ⬝ᵥ x (i + 1) < l ⬝ᵥ x i) :
    ∀ m, m ≠ i → l ⬝ᵥ x m < l ⬝ᵥ x i := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hk2 : (2 : ZMod k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hne1 : i - 1 ≠ i := by intro h; simp at h
  have hne2 : i - 1 ≠ i + 1 := by
    intro h
    apply hk2
    have : (i + 1) - (i - 1) = 0 := by rw [h]; ring
    simpa [sub_sub_eq_add_sub, two_mul, add_assoc, one_add_one_eq_two] using (by
      calc (2 : ZMod k) = (i + 1) - (i - 1) := by ring
        _ = 0 := this)
  intro m hm
  by_cases hm1 : m = i + 1
  · rw [hm1]; exact h2
  by_cases hm2 : m = i - 1
  · rw [hm2]; exact h1
  obtain ⟨hpl, hrim⟩ := hx
  have hnpl : ∀ a b, n ⬝ᵥ (x a - x b) = 0 := by
    intro a b; rw [dotProduct_sub, hpl a, hpl b]; ring
  have hD := hrim i (i - 1) hne1 hne2
  have hB := hrim i m hm hm1
  have hA := hrim (i - 1) m hm2 (by rw [sub_add_cancel]; exact hm)
  rw [sub_add_cancel] at hA
  have hn : n ≠ 0 := by
    intro h; rw [h] at hD; simp [tripleProduct] at hD
  have hle : l ⬝ᵥ (x (i + 1) - x i) < 0 := by rw [dotProduct_sub]; linarith
  have hlw : l ⬝ᵥ (x (i - 1) - x i) < 0 := by rw [dotProduct_sub]; linarith
  have hA' : 0 < tripleProduct (x m - x i) (x (i - 1) - x i) n := by
    have : tripleProduct (x i - x (i - 1)) (x m - x (i - 1)) n =
        tripleProduct (x m - x i) (x (i - 1) - x i) n := by
      simp only [tripleProduct, Pi.sub_apply]; ring
    rw [← this]; exact hA
  have := cramer_neg l n _ _ _ hn (hnpl _ _) (hnpl _ _) (hnpl _ _) hD hB hA' hle hlw
  rw [dotProduct_sub] at this
  linarith


theorem coplanarRimDepthUnimodal : CoplanarRimDepthUnimodal := by
  intro k _ hk x n hx l hinj
  refine ⟨hinj, ?_⟩
  have : Fact (1 < k) := ⟨by omega⟩
  have hk2 : (2 : ZMod k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod k))
    (fun j => l ⬝ᵥ x j) ⟨0, Finset.mem_univ _⟩
  have hpeak : ∀ j, j ≠ i → l ⬝ᵥ x j < l ⬝ᵥ x i := fun j hj =>
    lt_of_le_of_ne (hi j (Finset.mem_univ _)) (fun h => hj (hinj h))
  have hi1 : i - 1 ≠ i := by intro h; simp at h
  have hi2 : i + 1 ≠ i := by intro h; simp at h
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hj
    have := peak_is_max hk x n hx l j h1 h2 i (Ne.symm hj)
    have := hi j (Finset.mem_univ _)
    linarith
  · rintro rfl
    exact ⟨hpeak _ hi1, hpeak _ hi2⟩

theorem coplanarConvexQuadrilateralNeverTwoPeaked : CoplanarConvexQuadrilateralNeverTwoPeaked := by
  intro x n hx l h
  have e1 : (0 : ZMod 4) - 1 = 3 := by decide
  have e2 : (1 : ZMod 4) - 1 = 0 := by decide
  have e3 : (2 : ZMod 4) - 1 = 1 := by decide
  have e4 : (3 : ZMod 4) - 1 = 2 := by decide
  have f1 : (0 : ZMod 4) + 1 = 1 := by decide
  have f2 : (1 : ZMod 4) + 1 = 2 := by decide
  have f3 : (2 : ZMod 4) + 1 = 3 := by decide
  have f4 : (3 : ZMod 4) + 1 = 0 := by decide
  have pm := fun i => peak_is_max (by norm_num : 3 ≤ 4) x n hx l i
  simp only [TwoCyclicPeaks4, max_lt_iff, lt_min_iff] at h
  rcases h with ⟨⟨h1, h3⟩, ⟨h0', h2'⟩⟩ | ⟨⟨h1, h3⟩, ⟨h0', h2'⟩⟩
  · have a := pm 0 (by rw [e1]; linarith) (by rw [f1]; linarith) 2 (by decide)
    have b := pm 2 (by rw [e3]; linarith) (by rw [f3]; linarith) 0 (by decide)
    linarith
  · have a := pm 1 (by rw [e2]; linarith) (by rw [f2]; linarith) 3 (by decide)
    have b := pm 3 (by rw [e4]; linarith) (by rw [f4]; linarith) 1 (by decide)
    linarith



lemma exists_functional (a b c d : Fin 3 → ℝ) (h : LinearIndependent ℝ ![b - a, c - a, d - a])
    (y : Fin 3 → ℝ) : ∃ l : Fin 3 → ℝ, (b - a) ⬝ᵥ l = y 0 ∧ (c - a) ⬝ᵥ l = y 1 ∧
      (d - a) ⬝ᵥ l = y 2 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![b - a, c - a, d - a] with hM
  have hu : IsUnit M := by
    rw [← Matrix.linearIndependent_row_iff_isUnit]
    exact h
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  refine ⟨M⁻¹ *ᵥ y, ?_⟩
  have : M *ᵥ (M⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
  have h0 := congrFun this 0
  have h1 := congrFun this 1
  have h2 := congrFun this 2
  exact ⟨h0, h1, h2⟩

lemma two_neg (z : ZMod 4 → ℝ) (h : TwoCyclicPeaks4 z) : TwoCyclicPeaks4 (fun i => - z i) := by
  unfold TwoCyclicPeaks4 at h ⊢
  simp only [max_lt_iff, lt_min_iff, neg_lt_neg_iff] at h ⊢
  tauto

lemma not_unimodal_of_two (z : ZMod 4 → ℝ) (h : TwoCyclicPeaks4 z) : ¬ IsCyclicUnimodal z := by
  rintro ⟨-, hc⟩
  have e1 : (0 : ZMod 4) - 1 = 3 := by decide
  have e2 : (1 : ZMod 4) - 1 = 0 := by decide
  have e3 : (2 : ZMod 4) - 1 = 1 := by decide
  have e4 : (3 : ZMod 4) - 1 = 2 := by decide
  have f1 : (0 : ZMod 4) + 1 = 1 := by decide
  have f2 : (1 : ZMod 4) + 1 = 2 := by decide
  have f3 : (2 : ZMod 4) + 1 = 3 := by decide
  have f4 : (3 : ZMod 4) + 1 = 0 := by decide
  simp only [TwoCyclicPeaks4, max_lt_iff, lt_min_iff] at h
  have key : ∀ p q : ZMod 4, p ≠ q →
      (z (p - 1) < z p ∧ z (p + 1) < z p) → (z (q - 1) < z q ∧ z (q + 1) < z q) →
        2 ≤ (Finset.univ.filter (fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i)).card := by
    intro p q hpq hp hq
    have : ({p, q} : Finset (ZMod 4)) ⊆
        Finset.univ.filter (fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> simp [*]
    have := Finset.card_le_card this
    rwa [Finset.card_pair hpq] at this
  rcases h with ⟨⟨h1, h3⟩, ⟨h0', h2'⟩⟩ | ⟨⟨h1, h3⟩, ⟨h0', h2'⟩⟩
  · have := key 0 2 (by decide) ⟨by rw [e1]; linarith, by rw [f1]; linarith⟩
      ⟨by rw [e3]; linarith, by rw [f3]; linarith⟩
    omega
  · have := key 1 3 (by decide) ⟨by rw [e2]; linarith, by rw [f2]; linarith⟩
      ⟨by rw [e4]; linarith, by rw [f4]; linarith⟩
    omega


lemma exists_two_peak_functional (x : ZMod 4 → Fin 3 → ℝ) (v : Fin 3 → ℝ)
    (hli : LinearIndependent ℝ ![x 1 - x 0, x 2 - x 0, x 3 - x 0]) (hv : v ≠ 0) :
    ∃ L : Fin 3 → ℝ, L ⬝ᵥ v ≠ 0 ∧ TwoCyclicPeaks4 (fun i => L ⬝ᵥ x i) := by
  obtain ⟨l0, h1, h2, h3⟩ := exists_functional (x 0) (x 1) (x 2) (x 3) hli ![-2, 0, -2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2 h3
  rw [sub_dotProduct] at h1 h2 h3
  rw [dotProduct_comm (x 1) l0, dotProduct_comm (x 0) l0] at h1
  rw [dotProduct_comm (x 2) l0, dotProduct_comm (x 0) l0] at h2
  rw [dotProduct_comm (x 3) l0, dotProduct_comm (x 0) l0] at h3
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hh; push Not at hh; exact hv (funext hh)
  set S : ℝ := |x 1 j - x 0 j| + |x 2 j - x 0 j| + |x 3 j - x 0 j| with hS
  have hS0 : 0 ≤ S := by positivity
  set δ : ℝ := 1 / (4 * (1 + S)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hb : ∀ p : ZMod 4, p = 1 ∨ p = 2 ∨ p = 3 → δ * |x p j - x 0 j| < 1 / 4 := by
    intro p hp
    have hle : |x p j - x 0 j| ≤ S := by
      rcases hp with rfl | rfl | rfl <;> simp only [hS] <;> linarith [abs_nonneg (x 1 j - x 0 j),
        abs_nonneg (x 2 j - x 0 j), abs_nonneg (x 3 j - x 0 j)]
    calc δ * |x p j - x 0 j| ≤ δ * S := by gcongr
      _ < 1 / 4 := by
        rw [hδ, div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]; nlinarith
  -- the perturbed functional
  have hpert : ∀ ε : ℝ, |ε| = δ → (l0 + ε • Pi.single j 1) ⬝ᵥ v = l0 ⬝ᵥ v + ε * v j := by
    intro ε _; simp [mul_comm]
  have hval : ∀ (ε : ℝ) (p : ZMod 4), (l0 + ε • Pi.single j 1) ⬝ᵥ x p =
      l0 ⬝ᵥ x p + ε * x p j := by
    intro ε p; simp [mul_comm]
  have hε : ∃ ε : ℝ, |ε| = δ ∧ l0 ⬝ᵥ v + ε * v j ≠ 0 := by
    by_cases hc : l0 ⬝ᵥ v + δ * v j = 0
    · refine ⟨-δ, by rw [abs_neg, abs_of_pos hδ0], ?_⟩
      intro h; apply hj
      have : 2 * δ * v j = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exfalso; linarith
      · exact h
    · exact ⟨δ, abs_of_pos hδ0, hc⟩
  obtain ⟨ε, hεδ, hne⟩ := hε
  refine ⟨l0 + ε • Pi.single j 1, by rw [hpert ε hεδ]; exact hne, ?_⟩
  left
  have hbd : ∀ p : ZMod 4, (p = 1 ∨ p = 2 ∨ p = 3) → |ε * (x p j - x 0 j)| < 1 / 4 := by
    intro p hp; rw [abs_mul, hεδ]; exact hb p hp
  have b1 := abs_lt.mp (hbd 1 (by simp)); have b2 := abs_lt.mp (hbd 2 (by simp))
  have b3 := abs_lt.mp (hbd 3 (by simp))
  simp only [hval, max_lt_iff, lt_min_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, h1, h2, h3, mul_sub ε (x 1 j) (x 0 j), mul_sub ε (x 2 j) (x 0 j), mul_sub ε (x 3 j) (x 0 j)]


theorem existsMetricWithPrescribedDepth : ExistsMetricWithPrescribedDepth :=
  fun v l hl => thmF v l hl

theorem twoPeakedDepthsAtSomeMetric : TwoPeakedDepthsAtSomeMetric := by
  intro x v hli hv
  obtain ⟨L, hL, hpk⟩ := exists_two_peak_functional x v hli hv
  have fin : ∀ (l : Fin 3 → ℝ), 0 < l ⬝ᵥ v → TwoCyclicPeaks4 (fun i => l ⬝ᵥ x i) →
      ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧
        TwoCyclicPeaks4 (fun i => depth G v (x i)) ∧
        ¬ IsCyclicUnimodal (fun i => depth G v (x i)) := by
    intro l hl hp
    obtain ⟨G, hG, hGv⟩ := thmF v l hl
    have : (fun i => depth G v (x i)) = fun i => l ⬝ᵥ x i := by
      funext i; simp only [depth, hGv]
    refine ⟨G, hG, ?_, ?_⟩ <;> rw [this]
    · exact hp
    · exact not_unimodal_of_two _ hp
  rcases lt_or_gt_of_ne hL with h | h
  · apply fin (-L)
    · rw [neg_dotProduct]; linarith
    · have := two_neg _ hpk
      simpa only [neg_dotProduct] using this
  · exact fin L h hpk

end MinimalityExtra

#print axioms MinimalityExtra.existsMetricWithPrescribedDepth
#print axioms MinimalityExtra.twoPeakedDepthsAtSomeMetric
#print axioms MinimalityExtra.coplanarRimDepthUnimodal
#print axioms MinimalityExtra.coplanarConvexQuadrilateralNeverTwoPeaked
