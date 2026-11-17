module

public import Minimality.Type24NC
public import Minimality.CornerKernel

@[expose] public section

/-!
# Type 24: the Adjacency Lemma at the solid's own apex (Kernel Lemma, 4-rim instance)

Source: `nopert229/notes/RESIDUE-DESIGN.md` sections 1-2.1 and 4.  Two 4-rim cells `A`, `A'` of the cone of the apex
`1` that share two independent closed points `ρ₁, ρ₂`, whose diagonals are `F | B` resp. `B' | F'` with `F = B' = {0, 3}`
and a vertex `b` in `B ∩ F'`: `w_f = x_f - x_b` (`f ∈ F`) lies in `cl Conv(y)` and `-w_f` in `cl Conv(y')`.  Two planes in
`ℝ³` meet, so the Kernel Lemma closes the case (no metric, no obtuseness).

Frame (RESIDUE-DESIGN, "here") to Lean labels: `0↦4, 1↦3, 2↦5, 3↦0, 4↦2, 5↦6`, apex `6↦1`.
* star 2 `R0341 | edge 24 R1234`, `b = 4`: rims `(4,0,2,3)`, `(3,5,0,2)`, `b = 2`;
* star 0 `R1532 | edge 05 R0153`, `b = 5`: rims `(3,6,0,5)`, `(4,3,6,0)`, `b = 6`.
`Adj24` also allows the mirror (both rims reversed), since the chirality of the Lean frame was not checked.

The cell membership of `ρ_i` and the membership of `w_f` are explicit hypotheses of `AdjAt` (closed `cellSet` of the
whole solid `insert x₁ (Opts x)` and closed `convSet` of the rim); deriving them from the facet signs is open.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Matrix

namespace Minimality.T24.Adj
open Minimality Minimality.RimCell Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0 Minimality.CornerEQ

variable {x : Fin 7 → ℝ³}

/-- Two planes in `ℝ³` meet: a nonzero common combination. -/
theorem two_planes (ρ1 ρ2 w1 w2 : Fin 3 → ℝ) (hρ : LinearIndependent ℝ ![ρ1, ρ2])
    (hw : LinearIndependent ℝ ![w1, w2]) :
    ∃ a b : Fin 2 → ℝ, ∑ i, a i • ![ρ1, ρ2] i = ∑ j, b j • ![w1, w2] j ∧
      ∑ i, a i • ![ρ1, ρ2] i ≠ 0 := by
  have hnl : ¬ LinearIndependent ℝ ![ρ1, ρ2, w1, w2] := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hnl
  obtain ⟨g, hg, i0, hi0⟩ := hnl
  simp only [Fin.sum_univ_four] at hg
  refine ⟨![g 0, g 1], ![-g 2, -g 3], ?_, ?_⟩
  · simp only [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
    linear_combination (norm := module) hg
  · intro ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    have h2 := Fintype.linearIndependent_iff.1 hρ ![g 0, g 1]
      (by simpa [Fin.sum_univ_two] using ht)
    have e0 : g 0 = 0 := by simpa using h2 0
    have e1 : g 1 = 0 := by simpa using h2 1
    simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
    rw [e0, e1] at hg
    have h3 := Fintype.linearIndependent_iff.1 hw ![g 2, g 3] (by simpa [Fin.sum_univ_two] using hg)
    have e2 : g 2 = 0 := by simpa using h3 0
    have e3 : g 3 = 0 := by simpa using h3 1
    fin_cases i0 <;> simp_all

/-- The points of a rim, as coordinate vectors. -/
def rimPts (x : Fin 7 → ℝ³) (r : ZMod 4 → Fin 7) : ZMod 4 → Fin 3 → ℝ := fun i => co (x (r i))

/-- The vectors `w_f = x_f - x_b`, `f ∈ {0, 3}`. -/
def wv (x : Fin 7 → ℝ³) (b : Fin 7) : Fin 2 → Fin 3 → ℝ := fun j => co (x (![0, 3] j)) - co (x b)

/-- **Adjacency data** for the rims `r`, `r'` (4-cycles of vertices) and the vertex `b`: two independent views
`ρ₁, ρ₂` in the closed cells of both rims (of the whole solid), `w_f ∈ cl Conv(r)`, `-w_f ∈ cl Conv(r')`. -/
def AdjAt (x : Fin 7 → ℝ³) (r r' : ZMod 4 → Fin 7) (b : Fin 7) : Prop :=
  ∃ ρ : Fin 2 → Fin 3 → ℝ, LinearIndependent ℝ ρ ∧
    (∀ i, ρ i ∈ closure (cellSet (insert (co (x 1)) (Opts x)) (rimPts x r))) ∧
    (∀ i, ρ i ∈ closure (cellSet (insert (co (x 1)) (Opts x)) (rimPts x r'))) ∧
    (∀ j, wv x b j ∈ closure (convSet (rimPts x r))) ∧
    (∀ j, -wv x b j ∈ closure (convSet (rimPts x r')))

theorem adj_core (F : S0xFac 9 s0x_S24 x) {r r' : ZMod 4 → Fin 7} {b : Fin 7}
    (hr : Function.Injective r) (hr1 : ∀ i, r i ≠ 1) (hr' : Function.Injective r')
    (hr1' : ∀ i, r' i ≠ 1) (hw : LinearIndependent ℝ (wv x b)) (h : AdjAt x r r' b) :
    IsRupert (univ.image x) := by
  obtain ⟨ρ, hρi, hρ, hρ', hw1, hw2⟩ := h
  have e1 : ρ = ![ρ 0, ρ 1] := by ext i : 1; fin_cases i <;> rfl
  have e2 : wv x b = ![wv x b 0, wv x b 1] := by ext i : 1; fin_cases i <;> rfl
  rw [e1] at hρi; rw [e2] at hw
  obtain ⟨a, c, ht, ht0⟩ := two_planes _ _ _ _ hρi hw
  rw [← e1] at ht ht0; rw [← e2] at ht
  rw [← image_insert_Opts x]
  have hyY : ∀ (s : ZMod 4 → Fin 7), (∀ i, s i ≠ 1) → ∀ i, rimPts x s i ∈ insert (co (x 1)) (Opts x) :=
    fun s hs i => Finset.mem_insert_of_mem (co_mem_Opts (hs i))
  exact isRupert_of_kernel (k := 4) (k' := 4) (by norm_num) (by norm_num) (rimPts x r) (rimPts x r')
    ((x_injective F).comp hr) (hyY r hr1) ((x_injective F).comp hr') (hyY r' hr1')
    ρ hρ hρ' (wv x b) hw1 hw2 a c ht ht0 1 (by simp)

/-- Independence of `x_0 - x_b`, `x_3 - x_b` when a facet `t` contains `0` and `b` but not `3`. -/
theorem wv_indep (F : S0xFac 9 s0x_S24 x) {t : Fin 9} {b : Fin 7} (hb0 : b ≠ 0) (h0 : 0 ∈ s0x_S24 t)
    (hb : b ∈ s0x_S24 t) (h3 : 3 ∉ s0x_S24 t) : LinearIndependent ℝ (wv x b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • (x 0 - x b) + g 1 • (x 3 - x b) = 0 := by
    have := congrArg (fun v : Fin 3 → ℝ => WithLp.toLp 2 v) hg
    simpa [Fin.sum_univ_two, wv, co] using this
  have hn := congrArg (fun v => ⟪F.N t, v⟫) hg'
  simp only [inner_add_right, inner_smul_right, F.inner_sub, F.zero t 0 h0, F.zero t b hb,
    inner_zero_right] at hn
  have hneg := F.neg t 3 h3
  have g1 : g 1 = 0 := by
    have : g 1 * F.f t (x 3) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hneg.ne
  rw [g1, zero_smul, add_zero] at hg'
  have hne : x 0 - x b ≠ 0 := sub_ne_zero.2 fun h => hb0 ((Minimality.H24.SAT.inj_of_fac F h).symm)
  have g0 : g 0 = 0 := by
    rcases smul_eq_zero.1 hg' with h | h
    · exact h
    · exact absurd h hne
  intro i; fin_cases i
  · exact g0
  · exact g1

/-- **The adjacency condition**: star 2 | edge 24 or star 0 | edge 05 (or their mirrors). -/
def Adj24 (x : Fin 7 → ℝ³) : Prop :=
  AdjAt x ![4, 0, 2, 3] ![3, 5, 0, 2] 2 ∨ AdjAt x ![3, 2, 0, 4] ![2, 0, 5, 3] 2 ∨
  AdjAt x ![3, 6, 0, 5] ![4, 3, 6, 0] 6 ∨ AdjAt x ![5, 0, 6, 3] ![0, 6, 3, 4] 6


theorem inj4 (a b c d : Fin 7) (h : (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)) :
    Function.Injective (![a, b, c, d] : ZMod 4 → Fin 7) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro i j; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem ne1_4 (a b c d : Fin 7) (h : a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ d ≠ 1) :
    ∀ i, (![a, b, c, d] : ZMod 4 → Fin 7) i ≠ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro i; fin_cases i <;> simpa

theorem isRupert_of_adj24 (F : S0xFac 9 s0x_S24 x) (h : Adj24 x) : IsRupert (univ.image x) := by
  have w2 : LinearIndependent ℝ (wv x 2) := wv_indep (t := 2) F (by decide) (by decide) (by decide) (by decide)
  have w6 : LinearIndependent ℝ (wv x 6) := wv_indep (t := 4) F (by decide) (by decide) (by decide) (by decide)
  rcases h with h | h | h | h
  · refine adj_core F (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) w2 h
  · refine adj_core F (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) w2 h
  · refine adj_core F (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) w6 h
  · refine adj_core F (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) w6 h

/-- **The type 24 branch, closed off the residual, the facet cells, Root T0, Lemma NC and the Adjacency Lemma**. -/
theorem rupert_or_resid24_noFacetCell_noNC_noAdj {x : Fin 7 → ℝ³}
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
      (Resid24 x ∧ ¬ FacetCell24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ∧ ¬ T024 x ∧ ¬ NC24 x ∧ ¬ Adj24 x) := by
  have hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
      (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0) := by
    intro t i
    fin_cases t
    exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]
  rcases rupert_or_resid24_noFacetCell_noNC fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with h | ⟨h, h1, h2, h3⟩
  · exact Or.inl h
  · by_cases ha : Adj24 x
    · exact Or.inl (isRupert_of_adj24 (Minimality.T24.mkFac24 _ hh) ha)
    · exact Or.inr ⟨h, h1, h2, h3, ha⟩

end Minimality.T24.Adj
