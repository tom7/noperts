module

public import SmallRupert.OctahedronAll
public import SmallRupert.L8T3
public import SmallRupert.L8T4
public import SmallRupert.RightPrism
public import SmallRupert.Witnesses

@[expose] public section

/-!
# Six points in convex position: dependencies, Gale signs, splits, prisms (LEMMAS.md L10)

Setting (S) of L10 (`Six V`): six points, none in the hull of the others,
not coplanar, no five coplanar.  Affine dependencies are functions
`ℝ³ → ℝ` (`IsDepOn V l`); two of them, `l` and `m`, give the Gale vectors
`(l t, m t)` and the determinants `galeD l m s t`.

* §10.1: the vertex lemma, no three collinear points, no three parallel Gale
  vectors, and facets (triangles, quadrilaterals) and independent tetrahedra
  from signs of `galeD`;
* Lemma 10.1 (`exists_split_of_no_partner`): a point without an O-partner
  gives a 2+4 split (a dependency positive at exactly two points);
* Proposition 10.2 (`isRupert_of_all_partners`): three O-pairs form a prism
  (frustum, parallel or translation prism).
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `l` is an affine dependency of the points of `V`. -/
def IsDepOn (V : Finset ℝ³) (l : ℝ³ → ℝ) : Prop :=
  ∑ t ∈ V, l t = 0 ∧ ∑ t ∈ V, l t • t = 0

/-- Setting (S) of LEMMAS.md L10. -/
structure Six (V : Finset ℝ³) : Prop where
  card : V.card = 6
  vert : ∀ v ∈ V, v ∉ convexHull ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)
  noncop : ¬ Coplanar ℝ (V : Set ℝ³)
  no5 : ∀ v ∈ V, ¬ Coplanar ℝ ((V.erase v : Finset ℝ³) : Set ℝ³)

/-! ### Sums over six listed points -/

theorem sum_six {M : Type*} [AddCommMonoid M] {a b c d e f : ℝ³}
    (hnd : [a, b, c, d, e, f].Nodup) (g : ℝ³ → M) :
    ∑ t ∈ ({a, b, c, d, e, f} : Finset ℝ³), g t = g a + g b + g c + g d + g e + g f := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.mem_singleton] at hnd
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef, -⟩ := hnd
  rw [Finset.sum_insert (by simp [hab, hac, had, hae, haf]),
    Finset.sum_insert (by simp [hbc, hbd, hbe, hbf]), Finset.sum_insert (by simp [hcd, hce, hcf]),
    Finset.sum_insert (by simp [hde, hdf]), Finset.sum_pair hef]
  simp only [add_assoc]

/-! ### Dependencies -/

theorem IsDepOn.comb {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (α β : ℝ) : IsDepOn V (fun t => α * l t + β * m t) := by
  constructor
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hl.1, hm.1]; ring
  · calc ∑ t ∈ V, (α * l t + β * m t) • t = ∑ t ∈ V, (α • (l t • t) + β • (m t • t)) :=
          Finset.sum_congr rfl (fun t _ => by rw [add_smul, mul_smul, mul_smul])
      _ = α • ∑ t ∈ V, l t • t + β • ∑ t ∈ V, m t • t := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = 0 := by rw [hl.2, hm.2, smul_zero, smul_zero, add_zero]

theorem IsDepOn.neg {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) :
    IsDepOn V (fun t => -l t) := by
  constructor
  · rw [Finset.sum_neg_distrib, hl.1, neg_zero]
  · simp only [neg_smul, Finset.sum_neg_distrib, hl.2, neg_zero]

/-- A dependency applied to an affine function. -/
theorem IsDepOn.apply {V : Finset ℝ³} {l : ℝ³ → ℝ} (hl : IsDepOn V l) (f : ℝ³ →ᵃ[ℝ] ℝ) :
    ∑ t ∈ V, l t * f t = 0 := by
  have hf : ∀ x, f x = f.linear x + f 0 := fun x => by
    have := f.map_vadd 0 x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  calc ∑ t ∈ V, l t * f t = ∑ t ∈ V, (l t * f.linear t + l t * f 0) :=
        Finset.sum_congr rfl (fun t _ => by rw [hf t, mul_add])
    _ = f.linear (∑ t ∈ V, l t • t) + (∑ t ∈ V, l t) * f 0 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, map_sum]
        simp only [map_smul, smul_eq_mul]
    _ = 0 := by rw [hl.1, hl.2, map_zero, zero_mul, add_zero]

theorem IsDepOn.galeD {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (galeD l m s) := by
  have := hl.comb hm (-m s) (l s)
  convert this using 2 with t
  simp only [SmallRupert.galeD]; ring

/-- The dependency `t ↦ -⟨g_s, g_t⟩`. -/
theorem IsDepOn.nu {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hl : IsDepOn V l) (hm : IsDepOn V m)
    (s : ℝ³) : IsDepOn V (fun t => -(l s * l t + m s * m t)) := by
  have := hl.comb hm (-l s) (-m s)
  convert this using 2 with t
  ring

/-! ### §10.1 (a)–(d) -/

/-- **(a) Vertex lemma.**  No dependency is negative at exactly one point and
nonnegative elsewhere. -/
theorem Six.not_single_neg {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    {v : ℝ³} (hv : v ∈ V) (hneg : μ v < 0) (hrest : ∀ t ∈ V, t ≠ v → 0 ≤ μ t) : False := by
  classical
  apply hS.vert v hv
  have hsplit := Finset.add_sum_erase V μ hv
  have hsplit' := Finset.add_sum_erase V (fun t => μ t • t) hv
  rw [hμ.1] at hsplit
  rw [hμ.2] at hsplit'
  rw [Finset.mem_convexHull']
  refine ⟨fun t => μ t / (-μ v), fun t ht => ?_, ?_, ?_⟩
  · exact div_nonneg (hrest t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht))
      (by linarith)
  · rw [← Finset.sum_div, div_eq_one_iff_eq (by linarith)]; linarith
  · simp only [div_eq_mul_inv, mul_comm _ (-μ v)⁻¹, ← smul_smul, ← Finset.smul_sum]
    have h2 : ∑ x ∈ V.erase v, μ x • x = -(μ v • v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsplit'
    rw [h2, ← neg_smul, smul_smul, inv_mul_cancel₀ (by linarith : -μ v ≠ 0), one_smul]

/-- A dependency that is nonnegative (or nonpositive) everywhere vanishes. -/
theorem IsDepOn.eq_zero_of_nonpos {V : Finset ℝ³} {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (h : ∀ t ∈ V, μ t ≤ 0) : ∀ t ∈ V, μ t = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonpos h).mp hμ.1

/-- **(b)** No three points of `V` are collinear. -/
theorem Six.cross_ne_zero {V : Finset ℝ³} (hS : Six V) {P Q R : ℝ³} (hP : P ∈ V) (hQ : Q ∈ V)
    (hR : R ∈ V) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : cross (Q - P) (R - P) ≠ 0 := by
  intro h0
  have ha : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have haa : 0 < ⟪Q - P, Q - P⟫ := real_inner_self_pos.mpr ha
  have key : ⟪Q - P, Q - P⟫ • (R - P) = ⟪Q - P, R - P⟫ • (Q - P) := by
    have c0 := congrArg (fun v : ℝ³ => v 0) h0
    have c1 := congrArg (fun v : ℝ³ => v 1) h0
    have c2 := congrArg (fun v : ℝ³ => v 2) h0
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.zero_apply] at c0 c1 c2
    ext i; fin_cases i <;>
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      simp only [PiLp.sub_apply] at c0 c1 c2 ⊢
    · linear_combination (-(Q 1 - P 1)) * c2 + (Q 2 - P 2) * c1
    · linear_combination (Q 0 - P 0) * c2 - (Q 2 - P 2) * c0
    · linear_combination (-(Q 0 - P 0)) * c1 + (Q 1 - P 1) * c0
  set t := ⟪Q - P, R - P⟫ / ⟪Q - P, Q - P⟫ with ht
  have hR' : R = P + t • (Q - P) := by
    have : R - P = t • (Q - P) := by
      rw [ht, div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ haa.ne', one_smul]
    rw [← this]; abel
  rcases lt_or_ge t 0 with h | h
  · apply hS.vert P hP
    have hs : segment ℝ Q R ⊆ convexHull ℝ ((V.erase P : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPQ.symm, hQ⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPR.symm, hR⟩))
    have h1 : (1 - t) ≠ 0 := by linarith
    refine hs ⟨-t / (1 - t), 1 / (1 - t), by
      apply div_nonneg <;> linarith, by apply div_nonneg <;> linarith, by
      rw [← add_div, div_eq_one_iff_eq h1]; ring, ?_⟩
    rw [hR', show -t / (1 - t) = (1 / (1 - t)) * (-t) by ring, ← smul_smul, ← smul_add]
    have : (-t) • Q + (P + t • (Q - P)) = (1 - t) • P := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ h1, one_smul]
  rcases le_or_gt t 1 with h' | h'
  · apply hS.vert R hR
    have hs : segment ℝ P Q ⊆ convexHull ℝ ((V.erase R : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPR, hP⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hQR, hQ⟩))
    exact hs ⟨1 - t, t, by linarith, h, by ring, by rw [hR']; module⟩
  · apply hS.vert Q hQ
    have hs : segment ℝ P R ⊆ convexHull ℝ ((V.erase Q : Finset ℝ³) : Set ℝ³) :=
      segment_subset_convexHull (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hPQ, hP⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hQR.symm, hR⟩))
    have ht0 : t ≠ 0 := by linarith
    refine hs ⟨1 - 1 / t, 1 / t, by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith, by positivity, by ring, ?_⟩
    rw [hR', smul_add, smul_smul, one_div, inv_mul_cancel₀ ht0, one_smul]
    module

/-- A nonzero dependency vanishes at no three points (support at least 4). -/
theorem Six.no_three_zeros {V : Finset ℝ³} (hS : Six V) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ)
    (hne : ∃ t ∈ V, μ t ≠ 0) {a b c : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h0a : μ a = 0) (h0b : μ b = 0) (h0c : μ c = 0) : False := by
  classical
  have hc3 : (((V.erase a).erase b).erase c).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), Finset.card_erase_of_mem ha,
      hS.card]
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.mp hc3
  have hmemx : ∀ w, w ∈ ({x, y, z} : Finset ℝ³) ↔ w ≠ c ∧ w ≠ b ∧ w ≠ a ∧ w ∈ V := by
    intro w; rw [← hxyz, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
  have hx := (hmemx x).mp (by simp)
  have hy := (hmemx y).mp (by simp)
  have hz := (hmemx z).mp (by simp)
  have mem : ∀ t ∈ V, t = a ∨ t = b ∨ t = c ∨ t = x ∨ t = y ∨ t = z := by
    intro t ht
    by_cases h1 : t = a; · exact Or.inl h1
    by_cases h2 : t = b; · exact Or.inr (Or.inl h2)
    by_cases h3 : t = c; · exact Or.inr (Or.inr (Or.inl h3))
    have := (hmemx t).mpr ⟨h3, h2, h1, ht⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  -- the sum over the remaining three points
  have hsum : μ x + μ y + μ z = 0 := by
    have e1 := Finset.add_sum_erase V μ ha
    have e2 := Finset.add_sum_erase (V.erase a) μ (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    have e3 := Finset.add_sum_erase ((V.erase a).erase b) μ
      (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩)
    rw [hxyz, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz] at e3
    rw [hμ.1] at e1
    linarith
  have hne' : μ x ≠ 0 ∨ μ y ≠ 0 ∨ μ z ≠ 0 := by
    obtain ⟨t, ht, htne⟩ := hne
    rcases mem t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h0a htne
    · exact absurd h0b htne
    · exact absurd h0c htne
    · exact Or.inl htne
    · exact Or.inr (Or.inl htne)
    · exact Or.inr (Or.inr htne)
  -- a dependency negative at exactly one of `x, y, z` and nonnegative at the others
  have lone : ∀ ν : ℝ³ → ℝ, IsDepOn V ν → ν a = 0 → ν b = 0 → ν c = 0 →
      ∀ v, (v = x ∨ v = y ∨ v = z) → ν v < 0 → (x ≠ v → 0 ≤ ν x) → (y ≠ v → 0 ≤ ν y) →
        (z ≠ v → 0 ≤ ν z) → False := by
    intro ν hν na nb nc v hv hneg h1 h2 h3
    have hvV : v ∈ V := by rcases hv with rfl | rfl | rfl <;> simp_all
    refine hS.not_single_neg hν hvV hneg (fun t ht htv => ?_)
    rcases mem t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [na]
    · rw [nb]
    · rw [nc]
    · exact h1 htv
    · exact h2 htv
    · exact h3 htv
  have hn := hμ.neg
  rcases lt_or_ge (μ x) 0 with hx0 | hx0 <;> rcases lt_or_ge (μ y) 0 with hy0 | hy0 <;>
    rcases lt_or_ge (μ z) 0 with hz0 | hz0
  · linarith
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) z (by simp)
      (by linarith) (fun _ => by linarith) (fun _ => by linarith) (fun h => absurd rfl h)
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) y (by simp)
      (by linarith) (fun _ => by linarith) (fun h => absurd rfl h) (fun _ => by linarith)
  · exact lone μ hμ h0a h0b h0c x (by simp) hx0 (fun h => absurd rfl h) (fun _ => hy0)
      (fun _ => hz0)
  · exact lone (fun t => -μ t) hn (by simp [h0a]) (by simp [h0b]) (by simp [h0c]) x (by simp)
      (by linarith) (fun h => absurd rfl h) (fun _ => by linarith) (fun _ => by linarith)
  · exact lone μ hμ h0a h0b h0c y (by simp) hy0 (fun _ => hx0) (fun h => absurd rfl h)
      (fun _ => hz0)
  · exact lone μ hμ h0a h0b h0c z (by simp) hz0 (fun _ => hx0) (fun _ => hy0)
      (fun h => absurd rfl h)
  · rcases hne' with h | h | h <;> apply h <;> linarith

/-- A Gale frame: two dependencies, with nonzero Gale vectors, and two points
where they take the values of barycentric dependencies. -/
structure GaleFrame (V : Finset ℝ³) (l m : ℝ³ → ℝ) : Prop where
  hl : IsDepOn V l
  hm : IsDepOn V m
  ne : ∀ t ∈ V, l t ≠ 0 ∨ m t ≠ 0
  base : ∃ D₀ ∈ V, ∃ E₀ ∈ V, l D₀ = -1 ∧ m D₀ = 0 ∧ l E₀ = 0 ∧ m E₀ = -1

/-- Six distinct listed points. -/
theorem exists_six_of_card {V : Finset ℝ³} (h : V.card = 6) :
    ∃ a b c d e f : ℝ³, [a, b, c, d, e, f].Nodup ∧ V = {a, b, c, d, e, f} := by
  classical
  obtain ⟨a, V₁, ha, rfl, h₁⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, V₂, hb, rfl, h₂⟩ := Finset.card_eq_succ.mp h₁
  obtain ⟨c, V₃, hc, rfl, h₃⟩ := Finset.card_eq_succ.mp h₂
  obtain ⟨d, e, f, hde, hdf, hef, rfl⟩ := Finset.card_eq_three.mp h₃
  refine ⟨a, b, c, d, e, f, ?_, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.mem_singleton]
  tauto

/-- An affine functional constant on three of four frame points, with zero
weight on the fourth. -/
theorem inner_bary_eq {N A B C T X : ℝ³} {a b c d k : ℝ}
    (hX : X = a • A + b • B + c • C + d • T) (hs : a + b + c + d = 1)
    (hA : a = 0 ∨ ⟪N, A⟫ = k) (hB : b = 0 ∨ ⟪N, B⟫ = k) (hC : c = 0 ∨ ⟪N, C⟫ = k)
    (hT : d = 0 ∨ ⟪N, T⟫ = k) : ⟪N, X⟫ = k := by
  rw [hX]
  simp only [inner_add_right, real_inner_smul_right]
  have eA : a * (⟪N, A⟫ - k) = 0 := by rcases hA with h | h <;> simp [h]
  have eB : b * (⟪N, B⟫ - k) = 0 := by rcases hB with h | h <;> simp [h]
  have eC : c * (⟪N, C⟫ - k) = 0 := by rcases hC with h | h <;> simp [h]
  have eT : d * (⟪N, T⟫ - k) = 0 := by rcases hT with h | h <;> simp [h]
  linear_combination eA + eB + eC + eT + k * hs

/-- A Gale frame from an independent tetrahedron `ABCT` and the two other points. -/
theorem galeFrame_of_det4 {V : Finset ℝ³} (hS : Six V) {A B C T D₀ E₀ : ℝ³}
    (hV : V = {A, B, C, T, D₀, E₀}) (hnd : [A, B, C, T, D₀, E₀].Nodup)
    (hdet : det4 A B C T ≠ 0) : ∃ l m, GaleFrame V l m := by
  classical
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.mem_singleton] at hnd'
  obtain ⟨⟨hAB, hAC, hAT, hAD, hAE⟩, ⟨hBC, hBT, hBD, hBE⟩, ⟨hCT, hCD, hCE⟩, ⟨hTD, hTE⟩, hDE, -⟩ :=
    hnd'
  have hind : AffineIndependent ℝ ![A, B, C, T] := affineIndependent_of_det3 hdet
  obtain ⟨bA, bB, bC, bT, hbs, hbD⟩ := exists_bary hind D₀
  obtain ⟨cA, cB, cC, cT, hcs, hcE⟩ := exists_bary hind E₀
  set l : ℝ³ → ℝ := fun t => if t = A then bA else if t = B then bB else if t = C then bC
    else if t = T then bT else if t = D₀ then -1 else 0 with hl
  set m : ℝ³ → ℝ := fun t => if t = A then cA else if t = B then cB else if t = C then cC
    else if t = T then cT else if t = D₀ then 0 else -1 with hm
  have lA : l A = bA := by simp [hl]
  have lB : l B = bB := by simp [hl, (Ne.symm hAB)]
  have lC : l C = bC := by simp [hl, (Ne.symm hAC), (Ne.symm hBC)]
  have lT : l T = bT := by simp [hl, (Ne.symm hAT), (Ne.symm hBT), (Ne.symm hCT)]
  have lD : l D₀ = -1 := by simp [hl, (Ne.symm hAD), (Ne.symm hBD), (Ne.symm hCD), (Ne.symm hTD)]
  have lE : l E₀ = 0 := by simp [hl, (Ne.symm hAE), (Ne.symm hBE), (Ne.symm hCE), (Ne.symm hTE), (Ne.symm hDE)]
  have mA : m A = cA := by simp [hm]
  have mB : m B = cB := by simp [hm, (Ne.symm hAB)]
  have mC : m C = cC := by simp [hm, (Ne.symm hAC), (Ne.symm hBC)]
  have mT : m T = cT := by simp [hm, (Ne.symm hAT), (Ne.symm hBT), (Ne.symm hCT)]
  have mD : m D₀ = 0 := by simp [hm, (Ne.symm hAD), (Ne.symm hBD), (Ne.symm hCD), (Ne.symm hTD)]
  have mE : m E₀ = -1 := by simp [hm, (Ne.symm hAE), (Ne.symm hBE), (Ne.symm hCE), (Ne.symm hTE), (Ne.symm hDE)]
  have hsl : ∀ g : ℝ³ → ℝ³, ∑ t ∈ V, g t = g A + g B + g C + g T + g D₀ + g E₀ := fun g => by
    rw [hV]; exact sum_six hnd g
  have hsr : ∀ g : ℝ³ → ℝ, ∑ t ∈ V, g t = g A + g B + g C + g T + g D₀ + g E₀ := fun g => by
    rw [hV]; exact sum_six hnd g
  have hmemV : ∀ x ∈ V, x = A ∨ x = B ∨ x = C ∨ x = T ∨ x = D₀ ∨ x = E₀ := by
    intro x hx; rw [hV] at hx; simpa using hx
  -- a frame point with vanishing Gale vector makes the other five coplanar
  have plane : ∀ X Y Z W : ℝ³, X ∈ V → Y ∈ V → Z ∈ V → X ≠ Y → X ≠ Z → Y ≠ Z →
      (∀ x ∈ V, x ≠ W → x = X ∨ x = Y ∨ x = Z ∨ x = D₀ ∨ x = E₀) → W ∈ V →
      ⟪cross (Y - X) (Z - X), D₀⟫ = ⟪cross (Y - X) (Z - X), X⟫ →
      ⟪cross (Y - X) (Z - X), E₀⟫ = ⟪cross (Y - X) (Z - X), X⟫ → False := by
    intro X Y Z W hX hY hZ hXY hXZ hYZ hsub hW hD hE
    have hN := hS.cross_ne_zero hX hY hZ hXY hXZ hYZ
    apply hS.no5 W hW
    refine coplanar_of_plane hN (c := ⟪cross (Y - X) (Z - X), X⟫) (fun x hx => ?_)
    have hx' := Finset.mem_erase.mp hx
    rcases hsub x hx'.2 hx'.1 with rfl | rfl | rfl | rfl | rfl
    · rfl
    · have := inner_cross_left (x - X) (Z - X); rw [inner_sub_right] at this; linarith
    · have := inner_cross_right (Y - X) (x - X); rw [inner_sub_right] at this; linarith
    · exact hD
    · exact hE
  have hAV : A ∈ V := by rw [hV]; simp
  have hBV : B ∈ V := by rw [hV]; simp
  have hCV : C ∈ V := by rw [hV]; simp
  have hTV : T ∈ V := by rw [hV]; simp
  have hDV : D₀ ∈ V := by rw [hV]; simp
  have hEV : E₀ ∈ V := by rw [hV]; simp
  have kB : ∀ N : ℝ³, ⟪cross (C - B) (T - B), N⟫ = ⟪cross (C - B) (T - B), N⟫ := fun _ => rfl
  refine ⟨l, m, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, D₀, hDV, E₀, hEV, lD, mD, lE, mE⟩
  · rw [hsr, lA, lB, lC, lT, lD, lE]; linarith
  · rw [hsl, lA, lB, lC, lT, lD, lE, hbD]; module
  · rw [hsr, mA, mB, mC, mT, mD, mE]; linarith
  · rw [hsl, mA, mB, mC, mT, mD, mE, hcE]; module
  · intro t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases hmemV t ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [lA] at h1; rw [mA] at h2
      have iC := inner_cross_left (C - B) (T - B)
      have iT := inner_cross_right (C - B) (T - B)
      simp only [inner_sub_right] at iC iT
      refine plane B C T t hBV hCV hTV hBC hBT hCT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inl h1) (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)))
        (inner_bary_eq hcE hcs (Or.inl h2) (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lB] at h1; rw [mB] at h2
      have iC := inner_cross_left (C - A) (T - A)
      have iT := inner_cross_right (C - A) (T - A)
      simp only [inner_sub_right] at iC iT
      refine plane A C T t hAV hCV hTV hAC hAT hCT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inl h1) (Or.inr (by linarith)) (Or.inr (by linarith)))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inl h2) (Or.inr (by linarith)) (Or.inr (by linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lC] at h1; rw [mC] at h2
      have iB := inner_cross_left (B - A) (T - A)
      have iT := inner_cross_right (B - A) (T - A)
      simp only [inner_sub_right] at iB iT
      refine plane A B T t hAV hBV hTV hAB hAT hBT (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inr (by linarith)) (Or.inl h1) (Or.inr (by linarith)))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inr (by linarith)) (Or.inl h2) (Or.inr (by linarith)))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lT] at h1; rw [mT] at h2
      have iB := inner_cross_left (B - A) (C - A)
      have iC := inner_cross_right (B - A) (C - A)
      simp only [inner_sub_right] at iB iC
      refine plane A B C t hAV hBV hCV hAB hAC hBC (fun x hx hxt => ?_) ht
        (inner_bary_eq hbD hbs (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl h1))
        (inner_bary_eq hcE hcs (Or.inr rfl) (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl h2))
      rcases hmemV x hx with h | h | h | h | h | h <;>
        first | exact absurd h hxt | (subst h; simp only [true_or, or_true])
    · rw [lD] at h1; norm_num at h1
    · rw [mE] at h2; norm_num at h2

/-- Every six-point set in setting (S) has a Gale frame. -/
theorem Six.exists_galeFrame {V : Finset ℝ³} (hS : Six V) : ∃ l m, GaleFrame V l m := by
  obtain ⟨a, b, c, d, e, f, hnd, hV⟩ := exists_six_of_card hS.card
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.mem_singleton] at hnd'
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef, -⟩ :=
    hnd'
  have hN := hS.cross_ne_zero (P := a) (Q := b) (R := c) (by rw [hV]; simp) (by rw [hV]; simp)
    (by rw [hV]; simp) hab hac hbc
  by_cases h4 : det4 a b c d ≠ 0
  · exact galeFrame_of_det4 hS hV hnd h4
  by_cases h5 : det4 a b c e ≠ 0
  · refine galeFrame_of_det4 hS (A := a) (B := b) (C := c) (T := e) (D₀ := d) (E₀ := f)
      (by rw [hV]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_ h5
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, List.mem_singleton]
    tauto
  by_cases h6 : det4 a b c f ≠ 0
  · refine galeFrame_of_det4 hS (A := a) (B := b) (C := c) (T := f) (D₀ := d) (E₀ := e)
      (by rw [hV]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_ h6
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, List.mem_singleton]
    tauto
  push Not at h4 h5 h6
  exfalso
  apply hS.noncop
  refine coplanar_of_plane hN (c := ⟪cross (b - a) (c - a), a⟫) (fun x hx => ?_)
  rw [hV] at hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  have ib := inner_cross_left (b - a) (c - a)
  have ic := inner_cross_right (b - a) (c - a)
  simp only [det4] at h4 h5 h6
  simp only [inner_sub_right] at ib ic h4 h5 h6
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

/-- `galeD l m s ·` is nonzero somewhere. -/
theorem GaleFrame.exists_galeD_ne {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hF : GaleFrame V l m)
    {s : ℝ³} (hs : s ∈ V) : ∃ t ∈ V, galeD l m s t ≠ 0 := by
  obtain ⟨D₀, hD, E₀, hE, lD, mD, lE, mE⟩ := hF.base
  rcases hF.ne s hs with h | h
  · exact ⟨E₀, hE, by simp only [galeD, lE, mE]; intro h0; apply h; linarith⟩
  · exact ⟨D₀, hD, by simp only [galeD, lD, mD]; intro h0; apply h; linarith⟩

/-- **(d)** No three Gale vectors are pairwise parallel. -/
theorem GaleFrame.no_three_parallel {V : Finset ℝ³} {l m : ℝ³ → ℝ} (hS : Six V)
    (hF : GaleFrame V l m) {s t u : ℝ³} (hs : s ∈ V) (ht : t ∈ V) (hu : u ∈ V) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u) (h1 : galeD l m s t = 0) (h2 : galeD l m s u = 0) : False := by
  exact hS.no_three_zeros (hF.hl.galeD hF.hm s) (hF.exists_galeD_ne hs) hs ht hu hst hsu htu
    (galeD_self l m s) h1 h2

/-! ### §10.1 (e): facets from Gale signs -/

/-- A triangle facet from three negative Gale determinants of its complement. -/
theorem isFacetTriangle_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R X Y Z : ℝ³} (hV : V = {P, Q, R, X, Y, Z})
    (hnd : [P, Q, R, X, Y, Z].Nodup) (h₁ : galeD l m X Y < 0) (h₂ : galeD l m Y Z < 0)
    (h₃ : galeD l m Z X < 0) : IsFacetTriangle V P Q R := by
  sorry

/-- A quadrilateral facet from a parallel opposite complementary pair. -/
theorem isFacet_quad_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {P Q R Z X Y : ℝ³} (hV : V = {P, Q, R, Z, X, Y})
    (hnd : [P, Q, R, Z, X, Y].Nodup) (h₀ : galeD l m X Y = 0)
    (h₁ : galeD l m X Z * galeD l m Y Z < 0) : IsFacet V {P, Q, R, Z} := by
  sorry

/-- The complement of a non-parallel pair is an independent tetrahedron. -/
theorem affineIndependent_of_gale {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hl : IsDepOn V l) (hm : IsDepOn V m) {A B C T X Y : ℝ³} (hV : V = {A, B, C, T, X, Y})
    (hnd : [A, B, C, T, X, Y].Nodup) (h : galeD l m X Y ≠ 0) :
    AffineIndependent ℝ ![A, B, C, T] := by
  sorry

/-! ### Lemma 10.1: a 2+4 split -/

/-- `s, t` are an O-pair: antiparallel Gale vectors. -/
def IsOPair (l m : ℝ³ → ℝ) (s t : ℝ³) : Prop :=
  s ≠ t ∧ galeD l m s t = 0 ∧ l s * l t + m s * m t < 0

/-- **Lemma 10.1.** A point without an O-partner gives a 2+4 split. -/
theorem exists_split_of_no_partner {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) {i : ℝ³} (hi : i ∈ V) (hno : ∀ j ∈ V, ¬ IsOPair l m i j) :
    ∃ D ∈ V, ∃ E ∈ V, D ≠ E ∧ ∃ μ : ℝ³ → ℝ, IsDepOn V μ ∧ 0 < μ D ∧ 0 < μ E ∧
      ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0 := by
  sorry

/-! ### Proposition 10.2: prisms -/

/-- **Proposition 10.2.** If every point has an O-partner, `V` is a prism and
Rupert. -/
theorem isRupert_of_all_partners {V : Finset ℝ³} (hS : Six V) {l m : ℝ³ → ℝ}
    (hF : GaleFrame V l m) (hall : ∀ i ∈ V, ∃ j ∈ V, IsOPair l m i j) : IsRupert V := by
  sorry

end SmallRupert

end
