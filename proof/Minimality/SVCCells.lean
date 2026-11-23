module

public import Minimality.SVC

@[expose] public section

/-!
# SVC cells: generic layer (Job SVCCELLS)

Helpers so that a sign-closed SIGCHECK cell becomes an instance of `SVC.single_view_closure`
with data only:
* `exists_dep`: a nonzero affine dependency on any 5 (or more) points;
* `facet_pair`, `facet_zero`: facet relations with weights known to vanish allowed;
* `step`, `dep_of_chain`: sign propagation along a decidable chain of facet relations, giving
  the `hdeps` input of `single_view_closure` from a Bool computation;
* `tilt2`, `hR_two`: a tilt realizing any sign pattern on two edge-on facets with a common vertex;
* `edge_zero`, `edge_pos`, `edge_neg`, `forced_edge`: facings and the forced pair at an edge view.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.SVCC

variable {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-! ### Dependencies -/

/-- A nonzero affine dependency supported on any set `Q` of at least 5 of the points. -/
theorem exists_dep (P : Fin p → Fin n) (hP : Function.Injective (fun i => x (P i)))
    (Q : Finset (Fin p)) (hQ : 5 ≤ Q.card) :
    ∃ mu : Fin p → ℝ, (∀ i ∉ Q, mu i = 0) ∧ ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∃ i, mu i ≠ 0 := by
  classical
  have hinj : ∀ a ∈ Q, ∀ b ∈ Q, x (P a) = x (P b) → a = b := fun a _ b _ h => hP h
  have hcard : (Q.image fun i => x (P i)).card = Q.card := Finset.card_image_of_injOn hinj
  have hfr : Module.finrank ℝ ℝ³ = 3 := finrank_euclideanSpace_fin
  obtain ⟨f, h1, h2, e, he, hfe⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card (R := ℝ)
      (t := Q.image fun i => x (P i)) (by omega)
  rw [Finset.sum_image hinj] at h1 h2
  refine ⟨fun i => if i ∈ Q then f (x (P i)) else 0, fun i hi => by simp [hi], ?_, ?_, ?_⟩
  · rw [Finset.sum_ite_mem, Finset.univ_inter]; exact h2
  · simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]; exact h1
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i, by simp [hi, hfe]⟩

theorem facet_sum (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ)
    (hsum : ∑ i, mu i = 0) (hdep : ∑ i, mu i • x (P i) = 0) (t : Fin m) :
    ∑ l, mu l * F.f t (x (P l)) = 0 := by
  have hf : ∀ y, F.f t y = F.f t 0 + ⟪F.N t, y⟫ := by
    intro y; have := F.hN t y 0; rw [sub_zero] at this; linarith
  have hf' : ∀ l, mu l * F.f t (x (P l)) = mu l * F.f t 0 + mu l * ⟪F.N t, x (P l)⟫ := by
    intro l; rw [hf (x (P l)), mul_add]
  simp only [hf']
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add]
  have := SVC.dep_depth mu (fun l => x (P l)) hdep (F.N t)
  simpa [real_inner_comm] using this

/-- Facet pairing: `i ≠ j` off facet `t`, every other point on `t` or of weight 0. -/
theorem facet_pair (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ)
    (hsum : ∑ i, mu i = 0) (hdep : ∑ i, mu i • x (P i) = 0) (t : Fin m) {i j : Fin p}
    (hij : i ≠ j) (hi : P i ∉ S t) (hj : P j ∉ S t)
    (hon : ∀ l, l ≠ i → l ≠ j → P l ∈ S t ∨ mu l = 0) :
    SignType.sign (mu i) = -SignType.sign (mu j) := by
  have hs := facet_sum F P mu hsum hdep t
  rw [Fintype.sum_eq_add i j hij (fun l hl => by
    rcases hon l hl.1 hl.2 with h | h
    · rw [F.zero t _ h, mul_zero]
    · rw [h, zero_mul])] at hs
  have fi := F.neg t _ hi
  have fj := F.neg t _ hj
  rcases lt_trichotomy (mu j) 0 with h | h | h
  · have : 0 < mu i := by
      by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos hc fi.le]
    rw [sign_pos this, sign_neg h]; rfl
  · have : mu i = 0 := by
      rw [h, zero_mul, add_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_right fi.ne
    rw [this, h, sign_zero]; rfl
  · have : mu i < 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos hc fi.le]
    rw [sign_neg this, sign_pos h]

/-- Facet with a single point off it (among the points of nonzero weight): that weight is 0. -/
theorem facet_zero (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ)
    (hsum : ∑ i, mu i = 0) (hdep : ∑ i, mu i • x (P i) = 0) (t : Fin m) {i : Fin p}
    (hi : P i ∉ S t) (hon : ∀ l, l ≠ i → P l ∈ S t ∨ mu l = 0) : mu i = 0 := by
  have hs := facet_sum F P mu hsum hdep t
  rw [Fintype.sum_eq_single i (fun l hl => by
    rcases hon l hl with h | h
    · rw [F.zero t _ h, mul_zero]
    · rw [h, zero_mul])] at hs
  exact (mul_eq_zero.mp hs).resolve_right (F.neg t _ hi).ne

/-! ### Sign propagation -/

/-- A facet relation `(t, i, j)` is usable given the set `K` of points with known sign: `i`, `j`
off `t`, every other point on `t` or known of weight 0, and the target signs agree
(`i = j`: a single point off, target sign 0). -/
def relOK (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (s : Fin p → SignType)
    (K : Finset (Fin p)) (t : Fin m) (i j : Fin p) : Bool :=
  decide (P i ∉ S t ∧ P j ∉ S t ∧ (∀ l, l ≠ i → l ≠ j → P l ∈ S t ∨ (l ∈ K ∧ s l = 0)) ∧
    (if i = j then s i = 0 else s i = -s j))

def step (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (s : Fin p → SignType)
    (K : Finset (Fin p)) (e : Fin m × Fin p × Fin p) : Finset (Fin p) :=
  if relOK S P s K e.1 e.2.1 e.2.2 then
    (if e.2.1 = e.2.2 then insert e.2.1 K
      else if e.2.1 ∈ K then insert e.2.2 K else if e.2.2 ∈ K then insert e.2.1 K else K)
  else K

/-- Invariant: on `K` the signs are `s` times the sign `σ` of the root. -/
def Inv (mu : Fin p → ℝ) (s : Fin p → SignType) (σ : SignType) (K : Finset (Fin p)) : Prop :=
  ∀ k ∈ K, SignType.sign (mu k) = s k * σ

theorem step_inv (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ)
    (hsum : ∑ i, mu i = 0) (hdep : ∑ i, mu i • x (P i) = 0) (s : Fin p → SignType)
    (σ : SignType) (K : Finset (Fin p)) (hK : Inv mu s σ K) (e : Fin m × Fin p × Fin p) :
    Inv mu s σ (step S P s K e) := by
  obtain ⟨t, i, j⟩ := e
  unfold step
  simp only
  by_cases hok : relOK S P s K t i j = true
  · rw [ite_eq_left hok]
    simp only [relOK, decide_eq_true_eq] at hok
    obtain ⟨hi, hj, hon, hsg⟩ := hok
    have hon' : ∀ l, l ≠ i → l ≠ j → P l ∈ S t ∨ mu l = 0 := by
      intro l h1 h2
      rcases hon l h1 h2 with h | ⟨hl, h0⟩
      · exact Or.inl h
      · right; have := hK l hl; rw [h0, zero_mul] at this; exact sign_eq_zero_iff.mp this
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      rw [ite_eq_left rfl] at hsg
      have h0 : mu i = 0 := facet_zero F P mu hsum hdep t hi (fun l hl => hon' l hl hl)
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [h0, sign_zero, hsg, zero_mul]
      · exact hK k hk
    · rw [ite_eq_right hij] at hsg ⊢
      have hp := facet_pair F P mu hsum hdep t hij hi hj hon'
      by_cases hiK : i ∈ K
      · rw [ite_eq_left hiK]
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · have := hK i hiK
          rw [hsg] at this
          rw [show SignType.sign (mu k) = -SignType.sign (mu i) by rw [hp, neg_neg], this,
            neg_mul, neg_neg]
        · exact hK k hk
      · rw [ite_eq_right hiK]
        by_cases hjK : j ∈ K
        · rw [ite_eq_left hjK]
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · rw [hp, hK j hjK, hsg, neg_mul]
          · exact hK k hk
        · rw [ite_eq_right hjK]; exact hK
  · rw [ite_eq_right hok]; exact hK

theorem foldl_inv (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ)
    (hsum : ∑ i, mu i = 0) (hdep : ∑ i, mu i • x (P i) = 0) (s : Fin p → SignType)
    (σ : SignType) (l : List (Fin m × Fin p × Fin p)) :
    ∀ K, Inv mu s σ K → Inv mu s σ (l.foldl (step S P s) K) := by
  induction l with
  | nil => intro K hK; exact hK
  | cons e l ih => intro K hK; exact ih _ (step_inv F P mu hsum hdep s σ K hK e)

/-- **Signed dependency from a chain of facet relations.** `Q` (at least 5 points) is the
support, `r` the root (`s r = 1`), `s` vanishes off `Q`, and the chain reaches every index. -/
theorem dep_of_chain (F : S0xFac m S x) (P : Fin p → Fin n)
    (hP : Function.Injective (fun i => x (P i))) (Q : Finset (Fin p)) (hQ : 5 ≤ Q.card)
    (s : Fin p → SignType) (r : Fin p) (hr : s r = 1) (hQs : ∀ l, l ∉ Q → s l = 0)
    (chain : List (Fin m × Fin p × Fin p))
    (hch : ∀ k, k ∈ chain.foldl (step S P s) (insert r Qᶜ)) :
    ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
  obtain ⟨mu, hQ0, hsum, hdep, i0, hi0⟩ := exists_dep P hP Q hQ
  set σ := SignType.sign (mu r)
  have h0 : Inv mu s σ (insert r Qᶜ) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rw [hr, one_mul]
    · have hk' : k ∉ Q := Finset.mem_compl.mp hk
      rw [hQ0 k hk', sign_zero, hQs k hk', zero_mul]
  have hall := foldl_inv F P mu hsum hdep s σ chain _ h0
  have hall' : ∀ k, SignType.sign (mu k) = s k * σ := fun k => hall k (hch k)
  rcases hσ : σ with _ | _ | _
  · exfalso; apply hi0; have h := hall' i0; rw [hσ] at h
    have h' : SignType.sign (mu i0) = 0 := by rw [h]; cases s i0 <;> rfl
    exact sign_eq_zero_iff.mp h'
  · refine ⟨fun i => -mu i, by rw [Finset.sum_neg_distrib, hsum, neg_zero], ?_, fun i => ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib, hdep, neg_zero]
    · rw [Left.sign_neg, hall' i, hσ]; cases s i <;> rfl
  · refine ⟨mu, hsum, hdep, fun i => ?_⟩
    rw [hall' i, hσ]; cases s i <;> rfl

/-! ### Tilts for two edge-on facets -/

theorem sign_neg_mul_of_neg {a : ℝ} (ha : a < 0) (σ : SignType) (hσ : σ ≠ 0) :
    SignType.sign (-(σ : ℝ) * a) = σ := by
  rcases σ with _ | _ | _
  · exact absurd rfl hσ
  · have e : ((SignType.neg : SignType) : ℝ) = -1 := rfl
    rw [e, neg_neg, one_mul]; exact sign_neg ha
  · have e : ((SignType.pos : SignType) : ℝ) = 1 := rfl
    rw [e]; exact sign_pos (by linarith)

/-- Any sign pattern on two facets `t1`, `t2` with a common vertex `o` is realized by a tilt
built from vertices (`v1` on `t2` only, `v2` on `t1` only). -/
theorem tilt2 (F : S0xFac m S x) (t1 t2 : Fin m) (o v1 v2 : Fin n) (ho1 : o ∈ S t1)
    (ho2 : o ∈ S t2) (hv1a : v1 ∉ S t1) (hv1b : v1 ∈ S t2) (hv2a : v2 ∈ S t1)
    (hv2b : v2 ∉ S t2) (σ1 σ2 : SignType) (h1 : σ1 ≠ 0) (h2 : σ2 ≠ 0) :
    ∃ d : ℝ³, SignType.sign ⟪F.N t1, d⟫ = σ1 ∧ SignType.sign ⟪F.N t2, d⟫ = σ2 := by
  refine ⟨(-(σ1 : ℝ)) • (x v1 - x o) + (-(σ2 : ℝ)) • (x v2 - x o), ?_, ?_⟩
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN t1 (x v1) (x o), ← F.hN t1 (x v2) (x o), F.zero t1 o ho1, F.zero t1 v2 hv2a]
    simp only [sub_self, sub_zero, mul_zero, add_zero]
    exact sign_neg_mul_of_neg (F.neg t1 v1 hv1a) σ1 h1
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN t2 (x v1) (x o), ← F.hN t2 (x v2) (x o), F.zero t2 o ho2, F.zero t2 v1 hv1b]
    simp only [sub_self, sub_zero, mul_zero, zero_add]
    exact sign_neg_mul_of_neg (F.neg t2 v2 hv2b) σ2 h2

/-- The `hR` input of `single_view_closure` when exactly `t1`, `t2` are edge-on. -/
theorem hR_two (F : S0xFac m S x) (sw : Fin m → SignType) (R : List (SVC.Rim m p))
    (t1 t2 : Fin m) (o v1 v2 : Fin n) (ho1 : o ∈ S t1)
    (ho2 : o ∈ S t2) (hv1a : v1 ∉ S t1) (hv1b : v1 ∈ S t2) (hv2a : v2 ∈ S t1)
    (hv2b : v2 ∉ S t2) (hz : ∀ t, sw t = 0 → t = t1 ∨ t = t2)
    (hsd : R.all (fun ρ => decide (ρ.sd t1 ≠ 0 ∧ ρ.sd t2 ≠ 0)) = true) :
    ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t := by
  intro ρ hρ
  simp only [List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨a1, a2⟩ := hsd ρ hρ
  obtain ⟨d, hd1, hd2⟩ := tilt2 F t1 t2 o v1 v2 ho1 ho2 hv1a hv1b hv2a hv2b _ _ a1 a2
  refine ⟨d, fun t ht => ?_⟩
  rcases hz t ht with rfl | rfl
  · exact hd1
  · exact hd2


theorem sign_coe_self (σ : SignType) : SignType.sign (σ : ℝ) = σ := by
  rcases σ with _ | _ | _
  · exact sign_zero
  · exact sign_neg (by norm_num)
  · exact sign_pos (by norm_num)

/-- Any sign pattern on two facets with linearly independent normals (Gram determinant `≠ 0`);
used for disjoint facets, where `tilt2` has no common vertex. -/
theorem tilt_gram (F : S0xFac m S x) (t1 t2 : Fin m)
    (hD : ⟪F.N t1, F.N t1⟫ * ⟪F.N t2, F.N t2⟫ - ⟪F.N t1, F.N t2⟫ ^ 2 ≠ 0)
    (σ1 σ2 : SignType) : ∃ d : ℝ³, SignType.sign ⟪F.N t1, d⟫ = σ1 ∧
      SignType.sign ⟪F.N t2, d⟫ = σ2 := by
  set g11 := ⟪F.N t1, F.N t1⟫
  set g22 := ⟪F.N t2, F.N t2⟫
  set g12 := ⟪F.N t1, F.N t2⟫
  set D := g11 * g22 - g12 ^ 2
  have g21 : ⟪F.N t2, F.N t1⟫ = g12 := real_inner_comm _ _
  refine ⟨(((σ1 : ℝ) * g22 - (σ2 : ℝ) * g12) / D) • F.N t1 +
    (((σ2 : ℝ) * g11 - (σ1 : ℝ) * g12) / D) • F.N t2, ?_, ?_⟩
  · have : ⟪F.N t1, (((σ1 : ℝ) * g22 - (σ2 : ℝ) * g12) / D) • F.N t1 +
        (((σ2 : ℝ) * g11 - (σ1 : ℝ) * g12) / D) • F.N t2⟫ = σ1 := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      field_simp; ring
    rw [this, sign_coe_self]
  · have : ⟪F.N t2, (((σ1 : ℝ) * g22 - (σ2 : ℝ) * g12) / D) • F.N t1 +
        (((σ2 : ℝ) * g11 - (σ1 : ℝ) * g12) / D) • F.N t2⟫ = σ2 := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, g21]
      field_simp; ring
    rw [this, sign_coe_self]

/-- The `hR` input when exactly `t1`, `t2` are edge-on and their normals are independent. -/
theorem hR_gram (F : S0xFac m S x) (sw : Fin m → SignType) (R : List (SVC.Rim m p))
    (t1 t2 : Fin m) (hD : ⟪F.N t1, F.N t1⟫ * ⟪F.N t2, F.N t2⟫ - ⟪F.N t1, F.N t2⟫ ^ 2 ≠ 0)
    (hz : ∀ t, sw t = 0 → t = t1 ∨ t = t2) :
    ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t := by
  intro ρ _
  obtain ⟨d, hd1, hd2⟩ := tilt_gram F t1 t2 hD (ρ.sd t1) (ρ.sd t2)
  refine ⟨d, fun t ht => ?_⟩
  rcases hz t ht with rfl | rfl
  · exact hd1
  · exact hd2

/-! ### Edge views -/

theorem edge_inner (F : S0xFac m S x) (t : Fin m) (i j : Fin n) :
    ⟪F.N t, x i - x j⟫ = F.f t (x i) - F.f t (x j) := (F.hN t (x i) (x j)).symm

theorem edge_zero (F : S0xFac m S x) (t : Fin m) {i j : Fin n} (hi : i ∈ S t) (hj : j ∈ S t) :
    ⟪F.N t, x i - x j⟫ = 0 := by
  rw [edge_inner, F.zero t i hi, F.zero t j hj, sub_self]

theorem edge_pos (F : S0xFac m S x) (t : Fin m) {i j : Fin n} (hi : i ∈ S t) (hj : j ∉ S t) :
    0 < ⟪F.N t, x i - x j⟫ := by
  rw [edge_inner, F.zero t i hi, zero_sub]; exact neg_pos.mpr (F.neg t j hj)

theorem edge_neg (F : S0xFac m S x) (t : Fin m) {i j : Fin n} (hi : i ∉ S t) (hj : j ∈ S t) :
    ⟪F.N t, x i - x j⟫ < 0 := by
  rw [edge_inner, F.zero t j hj, sub_zero]; exact F.neg t i hi

/-- The forced pair of an edge view `w = x i - x j`. -/
theorem forced_edge {i j : Fin n} (hne : x i ≠ x j) : ⟪x j, x i - x j⟫ < ⟪x i, x i - x j⟫ := by
  have : 0 < ⟪x i - x j, x i - x j⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  rw [inner_sub_left] at this; linarith

end Minimality.SVCC

namespace Minimality.SVCC

open Minimality Minimality.H21

/-- `SVC.single_view_closure` with the facings needed only on the rim facets (`U ∪ Dn` of each
rim): a facet that bounds no rim edge of any tope need not have a known sign at the view. -/
theorem svc_local {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (SVC.Rim m p))
    (hsw : ∀ ρ ∈ R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t)
    (hR : ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (hgen : ∀ i j, i ≠ j → ⟪x (P i), w⟫ ≠ ⟪x (P j), w⟫)
    (hcheck : SVC.check S P sw forced deps R = true) : Minimality.Gen.LexAny F := by
  classical
  set z : Fin p → ℝ := fun i => ⟪x (P i), w⟫ with hzdef
  have hzinj : Function.Injective z := fun i j h => by
    by_contra hne; exact hgen i j hne h
  obtain ⟨L, hL, hrk⟩ := SVC.exists_order z hzinj
  simp only [SVC.check, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hval, hperm⟩ := hcheck
  have hL' := hperm L hL
  simp only [Bool.or_eq_true, List.any_eq_true] at hL'
  rcases hL' with (⟨ij, hij, hlt⟩ | ⟨s, hs, hsep⟩) | ⟨ρ, hρ, hok⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hforced ij hij) (not_lt.mpr (hrk _ _ hlt).le)
  · exfalso
    obtain ⟨mu, hsum, hdep, hsg⟩ := hdeps s hs
    have hz : ∑ i, mu i * z i = 0 := SVC.dep_depth mu (fun i => x (P i)) hdep w
    rcases hsep with h | h
    · exact SVC.sepR_sound hrk hsg hsum hz h
    · refine SVC.sepR_sound (mu := fun i => -mu i) hrk (fun i => ?_) ?_ ?_ h
      · rw [Left.sign_neg, hsg]
      · rw [Finset.sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_mul, Finset.sum_neg_distrib, hz, neg_zero]
  · have hv := hval ρ hρ
    simp only [SVC.rimValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨hk, hinj⟩, hcyc⟩, hU⟩, hD⟩ := hv
    obtain ⟨d1, hd1⟩ := hR ρ hρ
    refine Minimality.GenQuad.lexAny_of_clauses F hk hinj hcyc w d1 0 ?_ ?_ ?_
    · intro t ht
      have hs := hsw ρ hρ t (Or.inl ht)
      rw [inner_zero_right]
      rcases hU t ht with h | ⟨h0, h1⟩
      · exact Or.inl (sign_eq_one_iff.mp (hs.trans h))
      · refine Or.inr ⟨sign_eq_zero_iff.mp (hs.trans h0), Or.inl ?_⟩
        exact sign_eq_one_iff.mp ((hd1 t h0).trans h1)
    · intro t ht
      have hs := hsw ρ hρ t (Or.inr ht)
      rw [inner_zero_right, neg_zero]
      rcases hD t ht with h | ⟨h0, h1⟩
      · exact Or.inl (neg_pos.mpr (sign_eq_neg_one_iff.mp (hs.trans h)))
      · refine Or.inr ⟨neg_eq_zero.mpr (sign_eq_zero_iff.mp (hs.trans h0)), Or.inl ?_⟩
        exact neg_pos.mpr (sign_eq_neg_one_iff.mp ((hd1 t h0).trans h1))
    · exact SVC.rimOK_sound hrk (y := fun i => x (P i)) (fun i => rfl) ρ hok

end Minimality.SVCC
