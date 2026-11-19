module

public import Minimality.Crossing
public import Minimality.Type24Z0

@[expose] public section

/-!
# Lemma Q0435 (type 24): a face-on quadrilateral facet cell closes the case, at every metric

* `isRupert_of_planar_face_inside`: Theorem 5 in the form "a non-collinear subset `W` of `V` (e.g. a planar
  convex quadrilateral face), a view `u` not parallel to the plane of `W`, every other point of `V` projecting along `u`
  into the relative interior of `conv W`": `IsRupert V`.  Affine: no metric, no obtuseness, no PD.
* `Minimality.T24.Q0435.isRupert_of_cell0435`: type 24, facet `0345` (index 3 of `s0x_S24`, rim `0 4 3 5`)
  facing `u` strictly, the four facets across its edges (`nb 3 = {4, 8, 6, 2}`) facing away strictly: Rupert.
  This is the closed cell `Q0435` of LEAFCELL24 section B.  It was already proved in `Type24Z0` as `rupert_of_quadG`
  (via the closed-cell leaf and `robUni_quad`, not via Theorem 5); the statement here spells the cell out and the
  proof is that theorem.  The Theorem 5 route needs "other vertices project strictly inside the quad", which is
  not stated as a hypothesis here because the facings already give it (they are exactly the cell determinants).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality

/-- **Theorem 5, planar face form.**  `W ⊆ V` not collinear (so planar if some view is admissible), `u` not parallel
to the plane of `W`, every other point of `V` meets `relint conv W` along `u`. -/
theorem isRupert_of_planar_face_inside (V W : Finset ℝ³) (hWV : W ⊆ V)
    (hW : ¬ Collinear ℝ (W : Set ℝ³)) (u : ℝ³)
    (hu : u ∉ (affineSpan ℝ (W : Set ℝ³)).direction)
    (hin : ∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))) :
    IsRupert V :=
  isRupert_of_admissibleViews_nonempty V W hWV hW ⟨u, hu, hin⟩

end Minimality

namespace Minimality.T24.Q0435
open Minimality Minimality.H21 Minimality.T24.SAT

/-- **Lemma Q0435.**  Facet `0345` of a type 24 solid faces the view `u` and the facets `0 4 6`, `3 4 6`, `2 3 5`,
`0 2 5` across its four edges face away (the facing cell of the rim `0 4 3 5`): Rupert, at every metric. -/
theorem isRupert_of_cell0435 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : 0 < ⟪F.N 3, u⟫) (h2 : ⟪F.N 2, u⟫ < 0) (h4 : ⟪F.N 4, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0)
    (h8 : ⟪F.N 8, u⟫ < 0) : IsRupert (Finset.univ.image x) := by
  refine Minimality.T24.Z0.rupert_of_quadG F (a := u) ⟨?_, ?_⟩
  · intro t ht; rw [Finset.mem_singleton.1 ht]; exact hu
  · intro t ht
    have : t ∈ ({4, 8, 6, 2} : Finset (Fin 9)) := by simpa [Minimality.T24.Z0.nb] using ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl <;> assumption

end Minimality.T24.Q0435
