module

public import Mathlib
public import MinimalityExtra
public import Minimality.Generic.PV.PVMain
public import Minimality.OctaTools

/-!
# Lemma Q (two disjoint faces), from Lemma PV

`lemmaQ_twoDisjointFaces : LemmaQTwoDisjointFaces`.  The shadow of `V` along `u₀` is the quadrilateral
`xa₁ xa₂ xb₂ xb₁`; in the coordinates `(⟪n₁,·⟫, ⟪n₂,·⟫)` the corners are `(h₁, α₁), (h₁, α₂),
(β₂, h₂), (β₁, h₂)` and the orientation `σ c` (where `u₀ = c • (n₁ × n₂)`) decides which end of each
face is near the other plane.  Then `Minimality.lemmaPV` applies; the sign condition rules out both
mixed cases.
-/

@[expose] public section


namespace MinimalityExtra

open scoped RealInnerProductSpace
open Finset

theorem q_det3_eq (a b c : ℝ³) : MinimalityExtra.det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.det3_expand]; rfl

theorem q_det3_smul (a b d : ℝ³) (c : ℝ) :
    Minimality.det3 a b (c • d) = c * Minimality.det3 a b d := by
  simp only [Minimality.det3_expand, PiLp.smul_apply, smul_eq_mul]; ring

/-- A vector orthogonal to `n₁`, `n₂` is a multiple of `n₁ × n₂`. -/
theorem q_u0_eq {n₁ n₂ u : ℝ³} (hd : Minimality.cross n₁ n₂ ≠ 0)
    (h1 : ⟪n₁, u⟫ = 0) (h2 : ⟪n₂, u⟫ = 0) :
    u = (⟪Minimality.cross n₁ n₂, u⟫ / ⟪Minimality.cross n₁ n₂, Minimality.cross n₁ n₂⟫) •
      Minimality.cross n₁ n₂ := by
  set d := Minimality.cross n₁ n₂ with hdd
  have hn1 : n₁ ≠ 0 := by intro h; apply hd; ext i; fin_cases i <;> simp [hdd, h, Minimality.cross]
  have hpos : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd
  set w := u - (⟪d, u⟫ / ⟪d, d⟫) • d with hw
  have e1 : ⟪n₁, d⟫ = 0 := Minimality.inner_d1 n₁ n₂
  have e2 : ⟪n₂, d⟫ = 0 := Minimality.inner_d2 n₁ n₂
  have w1 : ⟪n₁, w⟫ = 0 := by rw [hw, inner_sub_right, inner_smul_right, e1, h1]; ring
  have w2 : ⟪n₂, w⟫ = 0 := by rw [hw, inner_sub_right, inner_smul_right, e2, h2]; ring
  have wd : ⟪d, w⟫ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right]; field_simp; ring
  have w3 : ⟪Minimality.cross n₁ d, w⟫ = 0 := by
    have : ⟪Minimality.cross n₁ d, w⟫ = ⟪n₁, n₂⟫ * ⟪n₁, w⟫ - ⟪n₁, n₁⟫ * ⟪n₂, w⟫ := by
      simp only [hdd, Minimality.cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring
    rw [this, w1, w2]; ring
  have := Minimality.eq_zero_of_orth hn1 hd e1 w1 wd w3
  have h0 : u - (⟪d, u⟫ / ⟪d, d⟫) • d = 0 := this
  exact sub_eq_zero.mp h0

/-- The linear chart of the plane of a face along `d`. -/
noncomputable def qChartL (n d : ℝ³) : ℝ³ →ₗ[ℝ] ℝ² where
  toFun p := Minimality.planeChart n d p
  map_add' x y := by
    ext i; fin_cases i <;> simp [Minimality.planeChart, inner_add_right]
  map_smul' c x := by
    ext i; fin_cases i <;> simp [Minimality.planeChart, inner_smul_right]

theorem q_convPos {V F : Finset ℝ³} {n : ℝ³} {h : ℝ} (hn : n ≠ 0)
    {d : ℝ³} (hd : d ≠ 0) (hnd : ⟪n, d⟫ = 0)
    (hconv : ∀ p ∈ V, p ∉ convexHull ℝ ((V.erase p : Finset ℝ³) : Set ℝ³))
    (hFV : F ⊆ V) (hF : ∀ p ∈ F, ⟪n, p⟫ = h) :
    Minimality.ConvPos (F.image (Minimality.planeChart n d)) := by
  classical
  intro t ht hmem
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
  have hinj : ∀ q ∈ F, Minimality.planeChart n d q = Minimality.planeChart n d p → q = p := by
    intro q hq e
    rw [Minimality.planeChart_eq] at e
    exact Minimality.chartS_injOn (Or.inl rfl) hn hd hnd (hF q hq) (hF p hp) e
  have e : (((F.image (Minimality.planeChart n d)).erase (Minimality.planeChart n d p) :
      Finset ℝ²) : Set ℝ²) = qChartL n d '' ((F.erase p : Finset ℝ³) : Set ℝ³) := by
    ext y
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hne⟩
      exact ⟨z, ⟨hz, fun e => hne (by rw [e])⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzp⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, fun e => hzp (hinj z hz e)⟩
  rw [e, ← LinearMap.image_convexHull] at hmem
  obtain ⟨q, hq, hqe⟩ := hmem
  have hplane : ∀ x ∈ convexHull ℝ ((F.erase p : Finset ℝ³) : Set ℝ³), ⟪n, x⟫ = h := by
    intro x hx
    have hc : Convex ℝ {x : ℝ³ | ⟪n, x⟫ = h} := by
      intro a ha b hb s t hs ht hst
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      rw [inner_add_right, inner_smul_right, inner_smul_right, ha, hb, ← add_mul, hst, one_mul]
    refine convexHull_min ?_ hc hx
    intro y hy
    exact hF y (Finset.mem_of_mem_erase (by exact_mod_cast hy))
  have hqp : q = p := by
    have e' : Minimality.planeChart n d q = Minimality.planeChart n d p := hqe
    rw [Minimality.planeChart_eq] at e'
    exact Minimality.chartS_injOn (Or.inl rfl) hn hd hnd (hplane q hq) (hF p hp) e'
  rw [hqp] at hq
  apply hconv p (hFV hp)
  refine convexHull_mono ?_ hq
  intro x hx
  simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at hx ⊢
  exact ⟨hFV hx.1, hx.2⟩

theorem q_det3_rev (a b p d : ℝ³) :
    Minimality.det3 (a - b) (p - b) d = - Minimality.det3 (b - a) (p - a) d := by
  simp only [Minimality.det3_expand, PiLp.sub_apply]; ring

theorem q_n_ne {n₁ n₂ : ℝ³} (hd : Minimality.cross n₁ n₂ ≠ 0) : n₁ ≠ 0 ∧ n₂ ≠ 0 := by
  constructor
  · intro h; apply hd; ext i; fin_cases i <;> simp [h, Minimality.cross]
  · intro h; apply hd; ext i; fin_cases i <;> simp [h, Minimality.cross]

theorem q_ends {F : Finset ℝ³} {n a b u : ℝ³} (hnu : ⟪n, u⟫ = 0) (ha : a ∈ F) (hb : b ∈ F)
    (hm : ∀ y ∈ F, y ≠ a → y ≠ b → ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ y = a + t • (b - a) + s • u) :
    (⟪n, a⟫ < ⟪n, b⟫ →
      (∀ y ∈ F, y ≠ a → ⟪n, a⟫ < ⟪n, y⟫) ∧ (∀ y ∈ F, y ≠ b → ⟪n, y⟫ < ⟪n, b⟫)) ∧
    (⟪n, b⟫ < ⟪n, a⟫ →
      (∀ y ∈ F, y ≠ a → ⟪n, y⟫ < ⟪n, a⟫) ∧ (∀ y ∈ F, y ≠ b → ⟪n, b⟫ < ⟪n, y⟫)) := by
  have key : ∀ y ∈ F, y ≠ a → y ≠ b → ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ⟪n, y⟫ = ⟪n, a⟫ + t * (⟪n, b⟫ - ⟪n, a⟫) := by
    intro y hy h1 h2
    obtain ⟨t, s, ht0, ht1, rfl⟩ := hm y hy h1 h2
    refine ⟨t, ht0, ht1, ?_⟩
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, hnu, inner_sub_right]
    ring
  constructor
  · intro hlt
    constructor
    · intro y hy h1
      by_cases h2 : y = b
      · subst h2; exact hlt
      · obtain ⟨t, ht0, ht1, e⟩ := key y hy h1 h2
        rw [e]; nlinarith
    · intro y hy h2
      by_cases h1 : y = a
      · subst h1; exact hlt
      · obtain ⟨t, ht0, ht1, e⟩ := key y hy h1 h2
        rw [e]; nlinarith
  · intro hgt
    constructor
    · intro y hy h1
      by_cases h2 : y = b
      · subst h2; exact hgt
      · obtain ⟨t, ht0, ht1, e⟩ := key y hy h1 h2
        rw [e]; nlinarith
    · intro y hy h2
      by_cases h1 : y = a
      · subst h1; exact hgt
      · obtain ⟨t, ht0, ht1, e⟩ := key y hy h1 h2
        rw [e]; nlinarith

theorem q_sgn_neg {k x : ℝ} (hk : k < 0) (h : 0 < k * x) : x < 0 := by
  by_contra hx; push Not at hx; nlinarith

theorem q_sgn_pos {k x : ℝ} (hk : 0 < k) (h : 0 < k * x) : 0 < x := by
  by_contra hx; push Not at hx; nlinarith

theorem q_ord_neg {k x m : ℝ} (hk : k < 0) (hm : 0 < m) (h : 0 < k * (x * m)) : x < 0 := by
  by_contra hx; push Not at hx; nlinarith [mul_nonneg hx hm.le]

theorem q_ord_pos {k x m : ℝ} (hk : 0 < k) (hm : 0 < m) (h : 0 < k * (x * m)) : 0 < x := by
  by_contra hx; push Not at hx; nlinarith [mul_nonneg (neg_nonneg.2 hx) hm.le]

theorem q_pcA {a b c e : ℝ} (hp : 0 < (a - b) * (c - e)) (h1 : c < e) (h2 : b < a) : False := by
  nlinarith

theorem q_pcB {a b c e : ℝ} (hp : 0 < (a - b) * (c - e)) (h1 : e < c) (h2 : a < b) : False := by
  nlinarith

theorem lemmaQ_twoDisjointFaces : LemmaQTwoDisjointFaces := by
  classical
  intro V F₁ F₂ n₁ n₂ u₀ h₁ h₂ σ xa₁ xa₂ xb₁ xb₂ hconv hF₁V hF₂V hdisj hc₁ hc₂ hf₁ hf₂ hd hu hu1 hu2
    ha₁ ha₂ hb₁ hb₂ hm₁ hm₂ hσ hq hh hinj hprod
  have hd' : Minimality.cross n₁ n₂ ≠ 0 := hd
  obtain ⟨c, hu0⟩ : ∃ c : ℝ, u₀ = c • Minimality.cross n₁ n₂ := ⟨_, q_u0_eq hd' hu1 hu2⟩
  subst hu0
  have hc0 : c ≠ 0 := by intro h; apply hu; rw [h, zero_smul]
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hn1, hn2⟩ := q_n_ne hd'
  set d : ℝ³ := Minimality.cross n₁ n₂ with hdd
  set κ := σ * c with hκdef
  have hκ : κ ≠ 0 := mul_ne_zero hσ0 hc0
  -- membership facts
  have V₁ : ∀ p ∈ F₁, p ∈ V := fun p hp => hF₁V hp
  have V₂ : ∀ p ∈ F₂, p ∈ V := fun p hp => hF₂V hp
  have on₁ : ∀ p ∈ F₁, ⟪n₁, p⟫ = h₁ := fun p hp => ((hf₁ p (V₁ p hp)).2).mpr hp
  have on₂ : ∀ p ∈ F₂, ⟪n₂, p⟫ = h₂ := fun p hp => ((hf₂ p (V₂ p hp)).2).mpr hp
  have str₁ : ∀ p ∈ F₂, ⟪n₁, p⟫ < h₁ := fun p hp =>
    lt_of_le_of_ne (hf₁ p (V₂ p hp)).1 (fun h => Finset.disjoint_left.mp hdisj
      (((hf₁ p (V₂ p hp)).2).mp h) hp)
  have str₂ : ∀ p ∈ F₁, ⟪n₂, p⟫ < h₂ := fun p hp =>
    lt_of_le_of_ne (hf₂ p (V₁ p hp)).1 (fun h => Finset.disjoint_left.mp hdisj
      hp (((hf₂ p (V₁ p hp)).2).mp h))
  -- the rows in coordinates
  have rowC : ∀ a b p : ℝ³, σ * MinimalityExtra.det3 (b - a) (p - a) (c • d) =
      κ * Minimality.det3 (b - a) (p - a) d := by
    intro a b p
    rw [q_det3_eq, q_det3_smul]; ring
  have rowF : ∀ a b p : ℝ³, Minimality.det3 (b - a) (p - a) d =
      (⟪n₁, b⟫ - ⟪n₁, a⟫) * (⟪n₂, p⟫ - ⟪n₂, a⟫) - (⟪n₂, b⟫ - ⟪n₂, a⟫) * (⟪n₁, p⟫ - ⟪n₁, a⟫) := by
    intro a b p
    rw [hdd, Minimality.det3_pair]
    simp only [real_inner_comm n₁, real_inner_comm n₂, inner_sub_right]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  simp only [rowC, rowF] at q1 q2 q3 q4 q5 q6 q7 q8
  have a1₁ := on₁ _ ha₁
  have a2₁ := on₁ _ ha₂
  have b1₂ := on₂ _ hb₁
  have b2₂ := on₂ _ hb₂
  have a1₂ := str₂ _ ha₁
  have a2₂ := str₂ _ ha₂
  have b1₁ := str₁ _ hb₁
  have b2₁ := str₁ _ hb₂
  simp only [a1₁, a2₁, b1₂, b2₂] at q1 q2 q3 q4 q5 q6 q7 q8
  -- hidden points, rows in d form
  have hH : ∀ p ∈ V.filter (fun p => p ∉ F₁ ∧ p ∉ F₂),
      0 < κ * Minimality.det3 (xa₂ - xa₁) (p - xa₁) d ∧
      0 < κ * Minimality.det3 (xb₂ - xa₂) (p - xa₂) d ∧
      0 < κ * Minimality.det3 (xb₁ - xb₂) (p - xb₂) d ∧
      0 < κ * Minimality.det3 (xa₁ - xb₁) (p - xb₁) d := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨r1, r2, r3, r4⟩ := hh p hp.1 hp.2.1 hp.2.2
    rw [rowC] at r1 r2 r3 r4
    exact ⟨r1, r2, r3, r4⟩
  -- prism pair
  set H := V.filter (fun p => p ∉ F₁ ∧ p ∉ F₂) with hHdef
  have P : Minimality.IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂ :=
    { union := by
        ext p
        simp only [Finset.mem_union, hHdef, Finset.mem_filter]
        constructor
        · intro hp
          by_cases h1 : p ∈ F₁
          · exact Or.inl (Or.inl h1)
          · by_cases h2 : p ∈ F₂
            · exact Or.inl (Or.inr h2)
            · exact Or.inr ⟨hp, h1, h2⟩
        · rintro ((h | h) | h)
          · exact hF₁V h
          · exact hF₂V h
          · exact h.1
      disj := hdisj
      card₁ := hc₁
      card₂ := hc₂
      on₁ := on₁
      on₂ := on₂
      le₁ := fun p hp => (hf₁ p hp).1
      le₂ := fun p hp => (hf₂ p hp).1
      strict₁ := str₁
      strict₂ := str₂
      d_ne := hd'
      conv₁ := q_convPos hn1 hd' (Minimality.inner_d1 n₁ n₂) hconv hF₁V on₁
      conv₂ := q_convPos hn2 hd' (Minimality.inner_d2 n₁ n₂) hconv hF₂V on₂ }
  -- depths
  have hdep : ∀ x, ⟪c • d, x⟫ = c * Minimality.pvDepth n₁ n₂ x := by
    intro x; rw [real_inner_smul_left]; rfl
  have hinjPV : Set.InjOn (Minimality.pvDepth n₁ n₂) (V : Set ℝ³) := by
    intro x hx y hy hxy
    apply hinj hx hy
    show ⟪c • d, x⟫ = ⟪c • d, y⟫
    rw [hdep, hdep, hxy]
  have hprod' : 0 < (Minimality.pvDepth n₁ n₂ xa₁ - Minimality.pvDepth n₁ n₂ xb₁) *
      (Minimality.pvDepth n₁ n₂ xa₂ - Minimality.pvDepth n₁ n₂ xb₂) := by
    simp only [hdep] at hprod
    have hc2 : 0 < c ^ 2 := by positivity
    have : (c * Minimality.pvDepth n₁ n₂ xa₁ - c * Minimality.pvDepth n₁ n₂ xb₁) *
        (c * Minimality.pvDepth n₁ n₂ xa₂ - c * Minimality.pvDepth n₁ n₂ xb₂) =
        c ^ 2 * ((Minimality.pvDepth n₁ n₂ xa₁ - Minimality.pvDepth n₁ n₂ xb₁) *
          (Minimality.pvDepth n₁ n₂ xa₂ - Minimality.pvDepth n₁ n₂ xb₂)) := by ring
    rw [this] at hprod
    exact (mul_pos_iff_of_pos_left hc2).mp hprod
  have e1 := (q_ends (n := n₂) (hnu := hu2) ha₁ ha₂ hm₁)
  have e2 := (q_ends (n := n₁) (hnu := hu1) hb₁ hb₂ hm₂)
  have key : ∃ E : Minimality.PVEnds F₁ F₂ n₁ n₂ h₁ h₂, (∀ p ∈ H, Minimality.PVHidden E p) ∧
      ¬ Minimality.PVMixedMinus E ∧ ¬ Minimality.PVMixedPlus E := by
    rcases lt_or_gt_of_ne hκ with hneg | hpos
    · have q1' : 0 < κ * ((⟪n₂, xa₂⟫ - ⟪n₂, xa₁⟫) * (h₁ - ⟪n₁, xb₂⟫)) := by linarith [q1]
      have q5' : 0 < κ * ((⟪n₁, xb₂⟫ - ⟪n₁, xb₁⟫) * (h₂ - ⟪n₂, xa₁⟫)) := by linarith [q5]
      have hα : ⟪n₂, xa₂⟫ < ⟪n₂, xa₁⟫ :=
        sub_neg.1 (q_ord_neg hneg (sub_pos.2 b2₁) q1')
      have hβ : ⟪n₁, xb₂⟫ < ⟪n₁, xb₁⟫ :=
        sub_neg.1 (q_ord_neg hneg (sub_pos.2 a1₂) q5')
      refine ⟨⟨xa₁, xa₂, xb₁, xb₂, ha₁, ha₂, hb₁, hb₂, (e1.2 hα).1, (e1.2 hα).2, (e2.2 hβ).1,
        (e2.2 hβ).2⟩, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨r1, r2, r3, r4⟩ := hH p hp
        exact ⟨q_sgn_neg hneg r1, q_sgn_neg hneg r2, q_sgn_neg hneg r3, q_sgn_neg hneg r4⟩
      · rintro ⟨h1, h2, -⟩
        exact q_pcA hprod' h1 h2
      · rintro ⟨h1, h2, -⟩
        exact q_pcB hprod' h1 h2
    · have q1' : 0 < κ * ((⟪n₂, xa₂⟫ - ⟪n₂, xa₁⟫) * (h₁ - ⟪n₁, xb₂⟫)) := by linarith [q1]
      have q5' : 0 < κ * ((⟪n₁, xb₂⟫ - ⟪n₁, xb₁⟫) * (h₂ - ⟪n₂, xa₁⟫)) := by linarith [q5]
      have hα : ⟪n₂, xa₁⟫ < ⟪n₂, xa₂⟫ :=
        sub_pos.1 (q_ord_pos hpos (sub_pos.2 b2₁) q1')
      have hβ : ⟪n₁, xb₁⟫ < ⟪n₁, xb₂⟫ :=
        sub_pos.1 (q_ord_pos hpos (sub_pos.2 a1₂) q5')
      refine ⟨⟨xa₂, xa₁, xb₂, xb₁, ha₂, ha₁, hb₂, hb₁, (e1.1 hα).2, (e1.1 hα).1, (e2.1 hβ).2,
        (e2.1 hβ).1⟩, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨r1, r2, r3, r4⟩ := hH p hp
        have s1 := q_sgn_pos hpos r1
        have s2 := q_sgn_pos hpos r2
        have s3 := q_sgn_pos hpos r3
        have s4 := q_sgn_pos hpos r4
        refine ⟨?_, ?_, ?_, ?_⟩
        · show Minimality.det3 (xa₁ - xa₂) (p - xa₂) d < 0
          rw [q_det3_rev]; linarith
        · show Minimality.det3 (xb₁ - xa₁) (p - xa₁) d < 0
          have := q_det3_rev xb₁ xa₁ p d
          linarith
        · show Minimality.det3 (xb₂ - xb₁) (p - xb₁) d < 0
          have := q_det3_rev xb₂ xb₁ p d
          linarith
        · show Minimality.det3 (xa₂ - xb₂) (p - xb₂) d < 0
          have := q_det3_rev xa₂ xb₂ p d
          linarith
      · rintro ⟨h1, h2, -⟩
        exact q_pcB hprod' h2 h1
      · rintro ⟨h1, h2, -⟩
        exact q_pcA hprod' h2 h1
  obtain ⟨E, hEH, hM1, hM2⟩ := key
  exact Minimality.lemmaPV P E hinjPV hEH hM1 hM2

end MinimalityExtra
