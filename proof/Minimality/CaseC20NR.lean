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

/-- **The vertex bridge for four-corner rims** (Theorem 18.1 in its tie form at a view in frame
coordinates, `Frame7.rupert_vertex`), from the explicit strict tests. -/
theorem vertex4 (hx : Function.Injective x) (c0 c1 c2 c3 : Fin 7) (P0 P1 P2 P3 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (M : Finset (Fin 7)) (hMc : ∀ m ∈ M, m ≠ c0 ∧ m ≠ c1 ∧ m ≠ c2 ∧ m ≠ c3)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hc : PCyc4 σ u P0 P1 P2 P3)
    (hr : ∀ j' : Fin 7, j' ∉ M → j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 →
      PRest4 σ u P0 P1 P2 P3 (F.ptC j'))
    (hz : IsRobustUnimodal (quad (F.GG P0 u) (F.GG P1 u) (F.GG P2 u) (F.GG P3 u)))
    (hnd : NoHDNAt (Finset.univ.image x) (F.fvC u))
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (quad P0 P1 P2 P3 i).x + s * ((quad P0 P1 P2 P3 (i + 1)).x -
        (quad P0 P1 P2 P3 i).x) + δ * u.x ∧
      (F.ptC m).y = (quad P0 P1 P2 P3 i).y + s * ((quad P0 P1 P2 P3 (i + 1)).y -
        (quad P0 P1 P2 P3 i).y) + δ * u.y ∧
      (F.ptC m).z = (quad P0 P1 P2 P3 i).z + s * ((quad P0 P1 P2 P3 (i + 1)).z -
        (quad P0 P1 P2 P3 i).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) := by
  have hc' : ∀ i, F.ptC (quad c0 c1 c2 c3 i) = quad P0 P1 P2 P3 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
  refine F.rupert_vertex hx (k := 4) (by norm_num) (quad c0 c1 c2 c3) M σ hσ u hu ?_ ?_ ?_ ?_ hnd ?_
  · intro m hm i
    obtain ⟨a0, a1, a2, a3⟩ := hMc m hm
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, a0, a1, a2, a3]
  · intro i j h1 h2
    simp only [hc']
    exact hc.all i j h1 h2
  · intro j' hj' hjc i
    simp only [hc']
    refine (hr j' hj' ?_ ?_ ?_ ?_).all i
    · exact fun h => hjc 0 (by simp [quad_0, h])
    · exact fun h => hjc 1 (by simp [quad_1, h])
    · exact fun h => hjc 2 (by simp [quad_2, h])
    · exact fun h => hjc 3 (by simp [quad_3, h])
  · have : (fun i : ZMod 4 => F.GG (F.ptC (quad c0 c1 c2 c3 i)) u) =
        quad (F.GG P0 u) (F.GG P1 u) (F.GG P2 u) (F.GG P3 u) := by
      funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
    rw [this]; exact hz
  · intro m hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hM m hm
    refine ⟨i, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩
    · rw [hc' i, hc' (i + 1)]; exact ex
    · rw [hc' i, hc' (i + 1)]; exact ey
    · rw [hc' i, hc' (i + 1)]; exact ez

end Minimality.CaseC18.Frame7

end
