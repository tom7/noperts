module

public import Minimality.Type24Adj
public import Minimality.CornerKernel

@[expose] public section

/-!
# Type 24: the face-pair certificate (Lemma E2) at the solid's own apex

Source: `nopert229/notes/CASE2-E2-PROOF.md` section 7.  Two 4-rim cells `r`, `r'` of the cone of the apex `1`, closed
points `ρ ∈ cl cell(r)`, `ρ' ∈ cl cell(r')` with `ρ = f₁ + κ f₂` (`f_i ∈ cl Conv(r')`, `κ ≥ 0`) and a dependency
`l₁ g₁ + l₂ g₂ + l₃ ρ + l₄ ρ' = 0` (`l₁, l₂, l₄ ≥ 0 < l₃`, `g_i ∈ cl Conv(r)`) give the EQ pairs `(ρ, -(ρ + c ρ'))` on `r`
and `(ρ', ρ)` on `r'` (`c = l₄ / l₃`), with certificate matrix `ρ ρᵀ`: `isRupert_of_face_pair` (CornerKernel).
Instances (frame `0↦4, 1↦3, 2↦5, 3↦0, 4↦2, 5↦6`, apex `6↦1`): A star 2 `(4,0,2,3)` | edge 14 `(3,5,2,6)`;
B star 0 `(3,6,0,5)` | edge 15 `(4,3,2,6)`.  `Face24` also allows both rims reversed, which negates `convSet`, so the
vectors `g`, `f` are negated (chirality of the Lean frame unchecked).  Memberships are hypotheses (as in `AdjAt`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Matrix

namespace Minimality.T24.Face
open Minimality Minimality.RimCell Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0
  Minimality.CornerEQ Minimality.T24.Adj

variable {x : Fin 7 → ℝ³}

/-- **Face-pair data** for rims `r`, `r'` and generators `g₁ g₂` (of `Conv r`), `f₁ f₂` (of `Conv r'`). -/
def FaceAt (x : Fin 7 → ℝ³) (r r' : ZMod 4 → Fin 7) (g₁ g₂ f₁ f₂ : Fin 3 → ℝ) : Prop :=
  ∃ ρ ρ' : Fin 3 → ℝ, ∃ l₁ l₂ l₃ l₄ κ : ℝ, 0 ≤ l₁ ∧ 0 ≤ l₂ ∧ 0 < l₃ ∧ 0 ≤ l₄ ∧ 0 ≤ κ ∧ ρ ≠ 0 ∧
    ρ ∈ closure (cellSet (insert (co (x 1)) (Opts x)) (rimPts x r)) ∧
    ρ' ∈ closure (cellSet (insert (co (x 1)) (Opts x)) (rimPts x r')) ∧
    g₁ ∈ closure (convSet (rimPts x r)) ∧ g₂ ∈ closure (convSet (rimPts x r)) ∧
    f₁ ∈ closure (convSet (rimPts x r')) ∧ f₂ ∈ closure (convSet (rimPts x r')) ∧
    ρ = f₁ + κ • f₂ ∧ l₁ • g₁ + l₂ • g₂ + l₃ • ρ + l₄ • ρ' = 0

/-- Core: `FaceAt` for injective rims avoiding the apex gives Rupert.  No independence of `g₁, g₂` is needed:
only `-(ρ + cρ') = (l₁/l₃) g₁ + (l₂/l₃) g₂` in the closed cone. -/
theorem face_core {r r' : ZMod 4 → Fin 7} {g₁ g₂ f₁ f₂ : Fin 3 → ℝ}
    (F : S0xFac 9 s0x_S24 x) (hr : Function.Injective r) (hr1 : ∀ i, r i ≠ 1)
    (hr' : Function.Injective r') (hr1' : ∀ i, r' i ≠ 1) (h : FaceAt x r r' g₁ g₂ f₁ f₂) :
    IsRupert (univ.image x) := by
  obtain ⟨ρ, ρ', l₁, l₂, l₃, l₄, κ, h1, h2, h3, h4, hκ, hρ0, hρ, hρ', hg₁, hg₂, hf₁, hf₂, hρe, hrel⟩ := h
  have hy : ∀ (s : ZMod 4 → Fin 7), (∀ i, s i ≠ 1) →
      ∀ i, rimPts x s i ∈ insert (co (x 1)) (Opts x) :=
    fun s hs i => Finset.mem_insert_of_mem (co_mem_Opts (hs i))
  have hσ : -((1 : ℝ) • ρ + (l₄ / l₃) • ρ') ∈ closure (convSet (rimPts x r)) := by
    have e : -((1 : ℝ) • ρ + (l₄ / l₃) • ρ') = (l₁ / l₃) • g₁ + (l₂ / l₃) • g₂ := by
      have h3' : l₃ ≠ 0 := h3.ne'
      have : l₃ • (-((1 : ℝ) • ρ + (l₄ / l₃) • ρ')) = l₃ • ((l₁ / l₃) • g₁ + (l₂ / l₃) • g₂) := by
        simp only [smul_add, smul_neg, smul_smul, one_smul]
        rw [mul_div_cancel₀ _ h3', mul_div_cancel₀ _ h3', mul_div_cancel₀ _ h3']
        have : l₃ • ρ = -(l₁ • g₁ + l₂ • g₂ + l₄ • ρ') := by
          rw [eq_neg_iff_add_eq_zero]; rw [← hrel]; abel
        rw [neg_add, this]; abel
      exact smul_right_injective _ h3' this
    rw [e]
    exact closure_convSet_add _ (closure_convSet_smul _ (div_nonneg h1 h3.le) hg₁)
      (closure_convSet_smul _ (div_nonneg h2 h3.le) hg₂)
  have hσ' : ρ ∈ closure (convSet (rimPts x r')) := by
    rw [hρe]
    exact closure_convSet_add _ hf₁ (closure_convSet_smul _ hκ hf₂)
  rw [← image_insert_Opts x]
  exact isRupert_of_face_pair (k := 4) (k' := 4) (by norm_num) (by norm_num) (rimPts x r) (rimPts x r')
    ((x_injective F).comp hr) (hy r hr1) ((x_injective F).comp hr') (hy r' hr1')
    ρ ρ' 1 (l₄ / l₃) one_pos (div_nonneg h4 h3.le) hρ0 hρ hρ' hσ hσ' 1 (by simp)

/-- **The face-pair condition** (Lemma E2): family A (star 2 | edge 14), family B (star 0 | edge 15), and the
mirrors (both rims reversed, generators negated). -/
def Face24 (x : Fin 7 → ℝ³) : Prop :=
  FaceAt x ![4, 0, 2, 3] ![3, 5, 2, 6] (co (x 0) - co (x 4)) (co (x 0) - co (x 2))
    (co (x 3) - co (x 6)) (co (x 2) - co (x 6)) ∨
  FaceAt x ![3, 2, 0, 4] ![6, 2, 5, 3] (co (x 4) - co (x 0)) (co (x 2) - co (x 0))
    (co (x 6) - co (x 3)) (co (x 6) - co (x 2)) ∨
  FaceAt x ![3, 6, 0, 5] ![4, 3, 2, 6] (co (x 0) - co (x 5)) (co (x 0) - co (x 6))
    (co (x 3) - co (x 2)) (co (x 6) - co (x 2)) ∨
  FaceAt x ![5, 0, 6, 3] ![6, 2, 3, 4] (co (x 5) - co (x 0)) (co (x 6) - co (x 0))
    (co (x 2) - co (x 3)) (co (x 2) - co (x 6))

theorem isRupert_of_face24 (F : S0xFac 9 s0x_S24 x) (h : Face24 x) : IsRupert (univ.image x) := by
  rcases h with h | h | h | h <;>
  exact face_core F (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide))
    (inj4 _ _ _ _ (by decide)) (ne1_4 _ _ _ _ (by decide)) h

/-- **The type 24 branch, closed off the residual, the facet cells, Root T0, Lemma NC, the Adjacency Lemma and
the face-pair Lemma E2**. -/
theorem rupert_or_resid24_noFacetCell_noNC_noAdj_noFace {x : Fin 7 → ℝ³}
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
      (Resid24 x ∧ ¬ FacetCell24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ∧ ¬ T024 x ∧ ¬ NC24 x ∧
        ¬ Adj24 x ∧ ¬ Face24 x) := by
  have hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
      (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0) := by
    intro t i
    fin_cases t
    exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]
  rcases rupert_or_resid24_noFacetCell_noNC_noAdj fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI
    with h | ⟨h, h1, h2, h3, h4⟩
  · exact Or.inl h
  · by_cases hf : Face24 x
    · exact Or.inl (isRupert_of_face24 (Minimality.T24.mkFac24 _ hh) hf)
    · exact Or.inr ⟨h, h1, h2, h3, h4, hf⟩

end Minimality.T24.Face
