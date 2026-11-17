module

public import Minimality.Type24Z0
public import Minimality.TentZ0
public import Minimality.RimCellVertex

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Matrix

namespace Minimality.T24.NC
open Minimality Minimality.RimCell Minimality.H21 Minimality.T24.SAT Minimality.T24.Z0

/-! ### Euclidean part, in coordinates `Fin 3 → ℝ` (frame `E = 1`) -/

/-- Real core of the apex step: a positive combination identity forces positivity. -/
theorem pos_of_comb {c0 c1 c2 f0 f1 f2 fp : ℝ} (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2)
    (g0 : 0 ≤ f0) (g1 : 0 ≤ f1) (g2 : 0 ≤ f2) (hs : 0 < f0 ∨ 0 < f1 ∨ 0 < f2)
    (h : fp * (c0 + c1 + c2) = c0 * f0 + c1 * f1 + c2 * f2) : 0 < fp := by
  have hS : 0 < c0 + c1 + c2 := by positivity
  have : 0 < c0 * f0 + c1 * f1 + c2 * f2 := by
    rcases hs with hs | hs | hs <;>
      nlinarith [mul_nonneg h0.le g0, mul_nonneg h1.le g1, mul_nonneg h2.le g2,
        mul_pos h0 hs, mul_pos h1 hs, mul_pos h2 hs]
  rw [← h] at this
  exact pos_of_mul_pos_left this hS.le

/-- **The apex is inside the cell.** A view `ρ` that is a positive combination of three edges `z a - p`
(`z` injective, in `O`) and lies in the cell of the rim `y` of `O` lies in the cell of `insert p O`: the
apex `p` needs no test of its own (this is "`x₆` is hidden" of Root T0). -/
theorem cellSet_insert_apex {k : ℕ} [NeZero k] (O : Finset (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (y : ZMod k → Fin 3 → ℝ) (z : Fin 3 → Fin 3 → ℝ) (hz : Function.Injective z)
    (hzO : ∀ a, z a ∈ O) (c : Fin 3 → ℝ) (hc : ∀ a, 0 < c a) {ρ : Fin 3 → ℝ}
    (hρ : ρ = ∑ a, c a • (z a - p)) (hcell : ρ ∈ cellSet O y) : ρ ∈ cellSet (insert p O) y := by
  intro i v hv hvi hvi1
  rcases Finset.mem_insert.1 hv with hvp | hvO
  · rw [hvp]
    set d := y (i + 1) - y i with hd
    have hf : ∀ a, 0 ≤ (Matrix.of ![d, z a - y i, ρ]).det := by
      intro a
      by_cases h1 : z a = y i
      · rw [h1]; simp [Matrix.det_fin_three]
      by_cases h2 : z a = y (i + 1)
      · rw [h2, ← hd]; simp [Matrix.det_fin_three]; ring_nf; rfl
      · exact (hcell i (z a) (hzO a) h1 h2).le
    have hs : ∃ a, z a ≠ y i ∧ z a ≠ y (i + 1) := by
      by_contra hn
      push Not at hn
      have e0 := hn 0; have e1 := hn 1; have e2 := hn 2
      have n01 : z 0 ≠ z 1 := fun h => absurd (hz h) (by decide)
      have n02 : z 0 ≠ z 2 := fun h => absurd (hz h) (by decide)
      have n12 : z 1 ≠ z 2 := fun h => absurd (hz h) (by decide)
      by_cases a0 : z 0 = y i <;> by_cases a1 : z 1 = y i <;> by_cases a2 : z 2 = y i
      all_goals try first
        | exact n01 (by rw [a0, a1]) | exact n02 (by rw [a0, a2]) | exact n12 (by rw [a1, a2])
      all_goals simp_all
    have hρj : ∀ j, ρ j = c 0 * (z 0 j - p j) + c 1 * (z 1 j - p j) + c 2 * (z 2 j - p j) := by
      intro j; rw [hρ]; simp [Fin.sum_univ_three]
    have key : (Matrix.of ![d, p - y i, ρ]).det * (c 0 + c 1 + c 2) =
        c 0 * (Matrix.of ![d, z 0 - y i, ρ]).det + c 1 * (Matrix.of ![d, z 1 - y i, ρ]).det +
        c 2 * (Matrix.of ![d, z 2 - y i, ρ]).det := by
      simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.sub_apply]
      rw [hρj 0, hρj 1, hρj 2]
      ring
    obtain ⟨a, ha1, ha2⟩ := hs
    refine pos_of_comb (hc 0) (hc 1) (hc 2) (hf 0) (hf 1) (hf 2) ?_ key
    fin_cases a
    · exact Or.inl (hcell i _ (hzO 0) ha1 ha2)
    · exact Or.inr (Or.inl (hcell i _ (hzO 1) ha1 ha2))
    · exact Or.inr (Or.inr (hcell i _ (hzO 2) ha1 ha2))
  · exact hcell i v hvO hvi hvi1


/-- The normal-cone pairing: `σ` with `⟪σ, e a⟫ ≤ 0` for three independent edges, `σ ≠ 0`, pairs negatively
with every positive combination of the edges. -/
theorem pairing_neg (e : Fin 3 → Fin 3 → ℝ) (hdet : (Matrix.of e).det ≠ 0) (c : Fin 3 → ℝ)
    (hc : ∀ a, 0 < c a) {σ : Fin 3 → ℝ} (hσ : σ ≠ 0) (hn : ∀ a, σ ⬝ᵥ e a ≤ 0) :
    σ ⬝ᵥ (∑ a, c a • e a) < 0 := by
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, Fin.sum_univ_three]
  have t : ∀ a, c a * (σ ⬝ᵥ e a) ≤ 0 := fun a => mul_nonpos_of_nonneg_of_nonpos (hc a).le (hn a)
  by_contra hge
  push Not at hge
  have h0 : ∀ a, σ ⬝ᵥ e a = 0 := by
    intro a
    have : c a * (σ ⬝ᵥ e a) = 0 := by
      have h3 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
      rcases h3 with rfl | rfl | rfl <;> linarith [t 0, t 1, t 2]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc a).ne'
    · exact h
  apply hσ
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  ext a
  simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
  rw [dotProduct_comm]
  exact h0 a

/-- **Lemma NC at the solid's own apex** (Euclidean form).  `O` a finite set of points, `p` the apex, `z a`
three of the points of `O` with independent edges `z a - p`; `y` a rim in `O` whose cell contains a positive
combination `ρ` of the edges; if the closed cone `cl Conv(y)` contains a nonzero `σ` of the apex normal cone
(`⟪σ, z a - p⟫ ≤ 0`) then `insert p O` is Rupert.  No lift, no obtuseness, no metric. -/
theorem rupert_of_nc {k : ℕ} [NeZero k] (hk : 3 ≤ k) (O : Finset (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (z : Fin 3 → Fin 3 → ℝ) (hz : Function.Injective z) (hzO : ∀ a, z a ∈ O)
    (hdet : (Matrix.of fun a => z a - p).det ≠ 0)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (hyO : ∀ i, y i ∈ O)
    (c : Fin 3 → ℝ) (hc : ∀ a, 0 < c a)
    (hcell : (∑ a, c a • (z a - p)) ∈ cellSet O y)
    {σ : Fin 3 → ℝ} (hσ : σ ∈ closure (convSet y)) (hσ0 : σ ≠ 0)
    (hn : ∀ a, σ ⬝ᵥ (z a - p) ≤ 0) :
    IsRupert ((insert p O).image (emb 1)) := by
  have hcell' := cellSet_insert_apex O p y z hz hzO c hc rfl hcell
  refine isRupert_of_conv_pair_closure hk 1 (by simp) y hy (insert p O)
    (fun i => Finset.mem_insert_of_mem (hyO i)) (subset_closure hcell') hσ ?_
  simpa using pairing_neg (fun a => z a - p) hdet c hc hσ0 hn

/-- **Root T0 at the solid's own apex** (Euclidean form): a 3-rim cell of `O` containing a positive
combination of three independent... edges of the apex makes `insert p O` Rupert. -/
theorem rupert_of_cell3 (O : Finset (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (z : Fin 3 → Fin 3 → ℝ) (hz : Function.Injective z) (hzO : ∀ a, z a ∈ O)
    (y : ZMod 3 → Fin 3 → ℝ) (hy : Function.Injective y) (hyO : ∀ i, y i ∈ O)
    (c : Fin 3 → ℝ) (hc : ∀ a, 0 < c a)
    (hcell : (∑ a, c a • (z a - p)) ∈ cellSet O y) :
    IsRupert ((insert p O).image (emb 1)) := by
  have hcell' := cellSet_insert_apex O p y z hz hzO c hc rfl hcell
  have hyY : ∀ i, y i ∈ insert p O := fun i => Finset.mem_insert_of_mem (hyO i)
  obtain ⟨q, hq, hinj⟩ := Minimality.TentApex.Frame.exists_injective_depth (1 : Matrix (Fin 3) (Fin 3) ℝ)
    (by simp) y hy (insert p O) hcell'
  exact isRupert_of_rimCell_zmod (by norm_num) 1 (by simp) y hy (insert p O) hyY q
    (ne_zero_of_edge (by norm_num) y q (edge_of_cell hy hyY hq)) hq
    (Minimality.isCyclicUnimodal_three _ hinj)


/-! ### Type 24: the apex is vertex `1` (facets `A = 012`, `B = 016`, `C = 126`), neighbours `0, 2, 6` -/

variable {x : Fin 7 → ℝ³}

/-- Plain coordinates of a point. -/
def co (v : ℝ³) : Fin 3 → ℝ := WithLp.ofLp v

/-- The neighbours of the apex `1`. -/
def nbr : Fin 3 → Fin 7 := ![0, 2, 6]

/-- The six points other than the apex, as coordinate vectors. -/
noncomputable def Opts (x : Fin 7 → ℝ³) : Finset (Fin 3 → ℝ) := (univ.erase (1 : Fin 7)).image fun i => co (x i)

/-- The solid in coordinates is `insert (co x1) (Opts x)`. -/
theorem image_insert_Opts (x : Fin 7 → ℝ³) :
    (insert (co (x 1)) (Opts x)).image (emb 1) = univ.image x := by
  have e : ∀ v : ℝ³, emb 1 (co v) = v := fun v => by ext j; simp [emb_apply, co]
  have hu : (insert (1 : Fin 7) (univ.erase 1) : Finset (Fin 7)) = univ := Finset.insert_erase (Finset.mem_univ _)
  rw [Finset.image_insert, Opts, Finset.image_image, e]
  conv_rhs => rw [← hu, Finset.image_insert]
  congr 1
  apply Finset.image_congr
  intro i _; exact e _

theorem co_injective : Function.Injective co := fun _ _ h => WithLp.ofLp_injective 2 h

theorem nbr_injective : Function.Injective nbr := by decide

/-- The three edges at the apex are independent (the apex lies on facet `A = 012`, vertex `6` is off it). -/
theorem edges_det (F : S0xFac 9 s0x_S24 x) :
    (Matrix.of fun a => co (x (nbr a)) - co (x 1)).det ≠ 0 := by
  have hB := Minimality.T24.fne24 F 0 6 (fA 0) (fB 0) (fC 0) (by decide) rfl rfl rfl
  have h3 : (fA 0, fB 0, fC 0) = ((0 : Fin 7), (1 : Fin 7), (2 : Fin 7)) := by decide
  simp only [Prod.mk.injEq] at h3
  obtain ⟨h1, h2, h4⟩ := h3
  rw [h1, h2, h4] at hB
  intro h
  apply hB
  rw [Bk, det3_expand]
  simp only [Matrix.det_fin_three, Matrix.of_apply, nbr, co] at h
  simp at h ⊢
  linear_combination (-1 : ℝ) * h


theorem x_injective (F : S0xFac 9 s0x_S24 x) : Function.Injective fun i => co (x i) :=
  co_injective.comp (Minimality.H24.SAT.inj_of_fac F)

theorem nbr_mem : ∀ a, nbr a ∈ univ.erase (1 : Fin 7) := by decide

theorem co_mem_Opts {i : Fin 7} (hi : i ≠ 1) : co (x i) ∈ Opts x :=
  Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩, rfl⟩

/-- **Root T0 for type 24** (own apex `1`, neighbours `0, 2, 6`): a 3-rim `r` of the six other vertices whose
cell contains a positive combination of the three apex edges.  (A facet cell `FacetCell24` of a triangular facet is
a case; the rim need not be a facet.) -/
def T024 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (r : ZMod 3 → Fin 7) (c : Fin 3 → ℝ), Function.Injective r ∧ (∀ i, r i ≠ 1) ∧ (∀ a, 0 < c a) ∧
    (∑ a, c a • (co (x (nbr a)) - co (x 1))) ∈ cellSet (Opts x) (fun i => co (x (r i)))

/-- **Lemma NC for type 24** (own apex `1`, neighbours `0, 2, 6`): a rim `r` among the six other vertices whose
cell contains a positive combination of the three apex edges, and a nonzero `σ` in the closed cone `cl Conv(r)`
that lies in the apex normal cone (`⟪σ, x a - x 1⟫ ≤ 0` for `a = 0, 2, 6`). -/
def NC24 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7) (c : Fin 3 → ℝ) (σ : Fin 3 → ℝ),
    3 ≤ k ∧ Function.Injective r ∧ (∀ i, r i ≠ 1) ∧ (∀ a, 0 < c a) ∧
    (∑ a, c a • (co (x (nbr a)) - co (x 1))) ∈ cellSet (Opts x) (fun i => co (x (r i))) ∧
    σ ∈ closure (convSet fun i => co (x (r i))) ∧ σ ≠ 0 ∧
    ∀ a, σ ⬝ᵥ (co (x (nbr a)) - co (x 1)) ≤ 0

theorem isRupert_of_T024 (F : S0xFac 9 s0x_S24 x) (h : T024 x) : IsRupert (univ.image x) := by
  obtain ⟨r, c, hr, hr1, hc, hcell⟩ := h
  rw [← image_insert_Opts x]
  exact rupert_of_cell3 (Opts x) (co (x 1)) (fun a => co (x (nbr a)))
    ((x_injective F).comp nbr_injective) (fun a => co_mem_Opts (by simpa using (Finset.mem_erase.1 (nbr_mem a)).1))
    (fun i => co (x (r i))) ((x_injective F).comp hr) (fun i => co_mem_Opts (hr1 i)) c hc hcell

theorem isRupert_of_NC24 (F : S0xFac 9 s0x_S24 x) (h : NC24 x) : IsRupert (univ.image x) := by
  obtain ⟨k, hk0, r, c, σ, hk, hr, hr1, hc, hcell, hσ, hσ0, hn⟩ := h
  rw [← image_insert_Opts x]
  exact rupert_of_nc hk (Opts x) (co (x 1)) (fun a => co (x (nbr a)))
    ((x_injective F).comp nbr_injective) (fun a => co_mem_Opts (by simpa using (Finset.mem_erase.1 (nbr_mem a)).1))
    (edges_det F) (fun i => co (x (r i))) ((x_injective F).comp hr) (fun i => co_mem_Opts (hr1 i))
    c hc hcell hσ hσ0 hn

/-- **The type 24 branch, closed off the residual, the facet cells, Root T0 and Lemma NC**: Rupert, or `Resid24 x`
holds and none of `FacetCell24`, `T024`, `NC24` does. -/
theorem rupert_or_resid24_noFacetCell_noNC {x : Fin 7 → ℝ³}
    (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨
      (Resid24 x ∧ ¬ FacetCell24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ∧ ¬ T024 x ∧ ¬ NC24 x) := by
  have hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
      (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0) := by
    intro t i
    fin_cases t
    exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]
  rcases rupert_or_resid24_noFacetCell fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with h | ⟨h, hz⟩
  · exact Or.inl h
  · let F := Minimality.T24.mkFac24 _ hh
    by_cases h0 : T024 x
    · exact Or.inl (isRupert_of_T024 F h0)
    by_cases h1 : NC24 x
    · exact Or.inl (isRupert_of_NC24 F h1)
    exact Or.inr ⟨h, hz, h0, h1⟩

end Minimality.T24.NC
