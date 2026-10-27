module

public import Minimality.ParDichotomy
public import Minimality.Cases
public import Minimality.SevenTypes

@[expose] public section

/-!
# Type 10: the three edge rectangles force a right prism

Type 10 has the faces `012`, `013`, `023`, `1245`, `1346`, `2356`, `456`: an apex `0` over the
triangle `123` of a prism `123`-`456`.  The face set is invariant under the simultaneous cyclic
relabelling `ρ` (`1 → 2 → 3 → 1`, `4 → 5 → 6 → 4`, `0` fixed).  The edge `14` of the
quadrilaterals `1245`, `1346` is the only place where `not_type10_of_isNopert_sv` leaves a
special position (the edge rectangle `EdgeRect`); applying the same result to `x ∘ ρ`, `x ∘ ρ²`
gives the edge rectangles at `25` and `36` as well.  Together they force a **right prism**
(`RightPrism10`): the lateral edges `14`, `25`, `36` are translates of one vector `e`, and the
triangle `123` is orthogonal to `e`.
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- The cyclic relabelling `1 → 2 → 3 → 1`, `4 → 5 → 6 → 4` (as a function `i ↦ ρ i`). -/
def ρ10 : Fin 7 → Fin 7 := ![0, 2, 3, 1, 5, 6, 4]

theorem ρ10_inj : Function.Injective ρ10 := by decide

theorem ρ10_surj : Finset.univ.image ρ10 = Finset.univ := by decide

/-- The residual of type 10: a right triangular prism `123`-`456`. -/
def RightPrism10 (x : Fin 7 → ℝ³) : Prop :=
  x 4 - x 1 = x 5 - x 2 ∧ x 4 - x 1 = x 6 - x 3 ∧
    ⟪x 2 - x 1, x 4 - x 1⟫ = 0 ∧ ⟪x 3 - x 1, x 4 - x 1⟫ = 0

/-- Type 10 is closed except for the edge rectangle at `14`. -/
theorem type10_edgeRect (x : Fin 7 → ℝ³) (hN : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 9)) :
    EdgeRect (Finset.univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) := by
  classical
  by_contra hE'
  obtain ⟨fA, hfA⟩ := hR {1, 2, 4, 5} (by decide)
  obtain ⟨fB, hfB⟩ := hR {1, 3, 4, 6} (by decide)
  obtain ⟨fC, hfC⟩ := hR {2, 3, 5, 6} (by decide)
  obtain ⟨fD, hfD⟩ := hR {0, 2, 3} (by decide)
  have hgen := noThreeCollinear_seven x hN hx
  have hT := triGenPar_or_farP_idx hx hgen {0, 2, 3} {1, 2, 4, 5} 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases edgeTieR_or_farP_rect_idx hx hgen {1, 2, 4, 5} {1, 3, 4, 6} 1 4
    (by decide) (by decide) (by decide) (by decide) with hE | hE | hE
  · exact not_type10_of_isNopert_sv x hN hx fA fB fC fD hfA hfB hfC hfD (fun _ => Or.inl hE)
      (fun _ => hT)
  · exact not_type10_of_isNopert_sv x hN hx fA fB fC fD hfA hfB hfC hfD (fun _ => Or.inr hE)
      (fun _ => hT)
  · exact hE' hE

/-- The consequences of the edge rectangle at `14`: the far edges `25`, `36` are equal vectors,
and `2`, `3` are at the same depth along the edge `14`. -/
theorem type10_rect_facts (x : Fin 7 → ℝ³) (hN : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 9)) :
    x 5 - x 2 = x 6 - x 3 ∧ ⟪x 2, x 4 - x 1⟫ = ⟪x 3, x 4 - x 1⟫ := by
  classical
  have hE := type10_edgeRect x hN hx hR
  obtain ⟨fD, hfD⟩ := hR {0, 2, 3} (by decide)
  obtain ⟨i, hiA, i', hi'A, j, hjB, j', hj'B, hiB, hi'B, hjA, hj'A, hii, hjj, hrel, t1, t2⟩ :=
    EdgeRect.labels hx {1, 2, 4, 5} {1, 3, 4, 6} 1 4 (by decide) (by decide) (by decide)
      (by decide) hE
  have key := aff_parallelogram fD hrel
  have hA : ∀ i ∈ ({1, 2, 4, 5} : Finset (Fin 7)), i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) →
      i = 2 ∨ i = 5 := by decide
  have hB : ∀ i ∈ ({1, 3, 4, 6} : Finset (Fin 7)), i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) →
      i = 3 ∨ i = 6 := by decide
  have f2 : fD (x 2) = 0 := (hfD 2).1 (by decide)
  have f3 : fD (x 3) = 0 := (hfD 3).1 (by decide)
  have f5 : fD (x 5) < 0 := (hfD 5).2 (by decide)
  have f6 : fD (x 6) < 0 := (hfD 6).2 (by decide)
  rcases hA i hiA hiB with rfl | rfl <;> rcases hA i' hi'A hi'B with rfl | rfl <;>
    rcases hB j hjB hjA with rfl | rfl <;> rcases hB j' hj'B hj'A with rfl | rfl <;>
    first | exact absurd rfl hii | exact absurd rfl hjj | linarith |
    skip
  · exact ⟨hrel, t1⟩
  · refine ⟨(neg_sub (x 2) (x 5)).symm.trans ((congrArg Neg.neg hrel).trans (neg_sub _ _)), ?_⟩
    have h := congrArg (fun v => ⟪v, x 4 - x 1⟫) hrel
    simp only [inner_sub_left] at h
    linarith

/-- The relabelled points `x ∘ ρ10` again realize the type-10 faces. -/
theorem realizes_comp_ρ10 {x : Fin 7 → ℝ³} (hR : RealizesFaces x (sevenTypeFaces 9)) :
    RealizesFaces (x ∘ ρ10) (sevenTypeFaces 9) := by
  classical
  have hinv : ∀ f ∈ sevenTypeFaces 9, f.image ρ10 ∈ sevenTypeFaces 9 := by decide +kernel
  intro f hf
  obtain ⟨φ, hφ⟩ := hR _ (hinv f hf)
  refine ⟨φ, fun i => ?_⟩
  have hiff : ρ10 i ∈ f.image ρ10 ↔ i ∈ f := by
    constructor
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      rwa [← ρ10_inj hji]
    · exact fun h => Finset.mem_image_of_mem _ h
  exact ⟨fun h => (hφ (ρ10 i)).1 (hiff.2 h), fun h => (hφ (ρ10 i)).2 (fun h' => h (hiff.1 h'))⟩

theorem isNopert_comp_ρ10 {x : Fin 7 → ℝ³} (hN : IsNopert (Finset.univ.image x)) :
    IsNopert (Finset.univ.image (x ∘ ρ10)) := by
  rw [← Finset.image_image, ρ10_surj]
  exact hN

/-- **Type 10 is a right prism**: the three edge rectangles (at `14`, and via the cyclic
relabelling at `25`, `36`) force `x4 - x1 = x5 - x2 = x6 - x3` and the triangle `123`
orthogonal to this vector. -/
theorem type10_rightPrism (x : Fin 7 → ℝ³) (hN : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x) (hR : RealizesFaces x (sevenTypeFaces 9)) :
    RightPrism10 x := by
  have h0 := type10_rect_facts x hN hx hR
  have hN1 := isNopert_comp_ρ10 hN
  have hx1 : Function.Injective (x ∘ ρ10) := hx.comp ρ10_inj
  have h1 := type10_rect_facts (x ∘ ρ10) hN1 hx1 (realizes_comp_ρ10 hR)
  have hN2 := isNopert_comp_ρ10 hN1
  have hx2 : Function.Injective (x ∘ ρ10 ∘ ρ10) := hx1.comp ρ10_inj
  have h2 := type10_rect_facts (x ∘ ρ10 ∘ ρ10) hN2 hx2 (realizes_comp_ρ10 (realizes_comp_ρ10 hR))
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have a1' : x 6 - x 3 = x 4 - x 1 := a1
  have b1' : ⟪x 3, x 5 - x 2⟫ = ⟪x 1, x 5 - x 2⟫ := b1
  have a2' : x 4 - x 1 = x 5 - x 2 := a2
  have b2' : ⟪x 1, x 6 - x 3⟫ = ⟪x 2, x 6 - x 3⟫ := b2
  have e5 : x 5 - x 2 = x 4 - x 1 := a2'.symm
  have e6 : x 6 - x 3 = x 4 - x 1 := a1'
  rw [e5] at b1'
  rw [e6] at b2'
  refine ⟨a2', a1'.symm, ?_, ?_⟩
  · rw [inner_sub_left]; linarith
  · rw [inner_sub_left]; linarith

end Minimality
