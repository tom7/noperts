module

public import Minimality.CaseC20ST
public import Minimality.CaseC20Bridge

@[expose] public section

/-!
# Type 20: non-realizable crossings at a view in a face plane

The strict screen tests (`PS`) of a four-corner rim cycle (`PCyc4`, `PRest4`), their persistence
under a perturbation of the view (`PCyc4.ev`), and the vertex bridge `Frame7.vertex4`
(`Frame7.rupert_vertex` for a four-corner rim): used for `V` of class `N4` at its own view and for
`T_A` at the slid views of the circle of the face `0135`.
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-- The eight strict tests of a four-corner rim cycle. -/
def PCyc4 (σ : ℝ) (u P0 P1 P2 P3 : C3) : Prop :=
  PS σ u (P1.sub P0) (P2.sub P0) ∧ PS σ u (P1.sub P0) (P3.sub P0) ∧
  PS σ u (P2.sub P1) (P3.sub P1) ∧ PS σ u (P2.sub P1) (P0.sub P1) ∧
  PS σ u (P3.sub P2) (P0.sub P2) ∧ PS σ u (P3.sub P2) (P1.sub P2) ∧
  PS σ u (P0.sub P3) (P1.sub P3) ∧ PS σ u (P0.sub P3) (P2.sub P3)

/-- The four strict tests of a point against a four-corner rim. -/
def PRest4 (σ : ℝ) (u P0 P1 P2 P3 m : C3) : Prop :=
  PS σ u (P1.sub P0) (m.sub P0) ∧ PS σ u (P2.sub P1) (m.sub P1) ∧
  PS σ u (P3.sub P2) (m.sub P2) ∧ PS σ u (P0.sub P3) (m.sub P3)

theorem PCyc4.all {σ : ℝ} {u P0 P1 P2 P3 : C3} (h : PCyc4 σ u P0 P1 P2 P3) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      PS σ u ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((quad P0 P1 P2 P3 j).sub (quad P0 P1 P2 P3 i)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j hi hj
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hi
    | exact absurd (by decide) hj
    | skip
  all_goals
    simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    assumption

theorem PRest4.all {σ : ℝ} {u P0 P1 P2 P3 m : C3} (h : PRest4 σ u P0 P1 P2 P3 m) :
    ∀ i : ZMod 4, PS σ u ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        (m.sub (quad P0 P1 P2 P3 i)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    assumption

/-- The view `u + η e`. -/
def C3.slide (u e : C3) (η : ℝ) : C3 := ⟨u.x + η * e.x, u.y + η * e.y, u.z + η * e.z⟩

theorem Frame20.dep_slide {x : Fin 7 → ℝ³} (F : Frame20 x) (u e : C3) (η : ℝ) (j : Fin 7) :
    F.dep (C3.slide u e η) j = F.dep u j + η * F.dep e j := by
  simp only [Frame20.dep, Frame7.GG, Gf, C3.slide]
  ring

theorem PS_ev (σ : ℝ) (u e a b : C3) (h : PS σ u a b) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS σ (C3.slide u e η) a b := by
  have := eventually_pos_affine (A := σ * Dc a b u) (B := σ * Dc a b e) (Or.inl h)
  filter_upwards [this] with η hη
  have : σ * Dc a b (C3.slide u e η) = σ * Dc a b u + η * (σ * Dc a b e) := by
    simp only [Dc, C3.slide]; ring
  unfold PS
  rw [this]; exact hη

theorem PCyc4.ev {σ : ℝ} {u P0 P1 P2 P3 : C3} (e : C3) (h : PCyc4 σ u P0 P1 P2 P3) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PCyc4 σ (C3.slide u e η) P0 P1 P2 P3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  filter_upwards [PS_ev σ u e _ _ h1, PS_ev σ u e _ _ h2, PS_ev σ u e _ _ h3, PS_ev σ u e _ _ h4,
    PS_ev σ u e _ _ h5, PS_ev σ u e _ _ h6, PS_ev σ u e _ _ h7, PS_ev σ u e _ _ h8] with η a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

theorem PRest4.ev {σ : ℝ} {u P0 P1 P2 P3 m : C3} (e : C3) (h : PRest4 σ u P0 P1 P2 P3 m) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PRest4 σ (C3.slide u e η) P0 P1 P2 P3 m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  filter_upwards [PS_ev σ u e _ _ h1, PS_ev σ u e _ _ h2, PS_ev σ u e _ _ h3,
    PS_ev σ u e _ _ h4] with η a1 a2 a3 a4
  exact ⟨a1, a2, a3, a4⟩

end Minimality.CaseC20

namespace Minimality.CaseC18.Frame7
open Minimality.CaseC20 Minimality.CaseC09 Filter
open scoped Topology
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

end Minimality.CaseC18.Frame7

end
