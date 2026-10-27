module

public import Minimality.CaseC18Vertex

@[expose] public section

/-!
# Type 20: the screen-test layer for rim cycles

`Cyc4`/`Rest4` (`Cyc5`/`Rest5`): the explicit screen tests (`ST`) of a four- (five-) corner rim
cycle and of one hidden point, as conjunctions of the individual determinant facts, together with
the conversion to the quantified form of the `Frame7` bridges.  The individual facts are generated
(one `linarith` with a product hint list each).
-/

namespace Minimality.CaseC20

open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

theorem pos_of_pos_mul {M T : ℝ} (hM : 0 < M) (h : 0 < M * T) : 0 < T :=
  (mul_pos_iff_of_pos_left hM).mp h


/-- The three tests of a triangle rim cycle. -/
def Cyc3 (σ : ℝ) (u v P0 P1 P2 : C3) : Prop :=
  ST σ u v (P1.sub P0) (P2.sub P0) ∧ ST σ u v (P2.sub P1) (P0.sub P1) ∧
  ST σ u v (P0.sub P2) (P1.sub P2)

/-- The three tests of a hidden point against a triangle rim. -/
def Rest3 (σ : ℝ) (u v P0 P1 P2 m : C3) : Prop :=
  ST σ u v (P1.sub P0) (m.sub P0) ∧ ST σ u v (P2.sub P1) (m.sub P1) ∧
  ST σ u v (P0.sub P2) (m.sub P2)

theorem Cyc3.all {σ : ℝ} {u v P0 P1 P2 : C3} (h : Cyc3 σ u v P0 P1 P2) :
    ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      ST σ u v ((tri P0 P1 P2 (i + 1)).sub (tri P0 P1 P2 i))
        ((tri P0 P1 P2 j).sub (tri P0 P1 P2 i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  intro i j hi hj
  rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hi
    | exact absurd (by decide) hj
    | skip
  all_goals
    simp only [b0, b1, b2, tri_0, tri_1, tri_2]
    assumption

theorem Rest3.all {σ : ℝ} {u v P0 P1 P2 m : C3} (h : Rest3 σ u v P0 P1 P2 m) :
    ∀ i : ZMod 3, ST σ u v ((tri P0 P1 P2 (i + 1)).sub (tri P0 P1 P2 i))
        (m.sub (tri P0 P1 P2 i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  intro i
  rcases zmod3_cases i with rfl | rfl | rfl <;>
  · simp only [b0, b1, b2, tri_0, tri_1, tri_2]
    assumption

/-- The eight tests of a four-corner rim cycle. -/
def Cyc4 (σ : ℝ) (u v P0 P1 P2 P3 : C3) : Prop :=
  ST σ u v (P1.sub P0) (P2.sub P0) ∧ ST σ u v (P1.sub P0) (P3.sub P0) ∧
  ST σ u v (P2.sub P1) (P3.sub P1) ∧ ST σ u v (P2.sub P1) (P0.sub P1) ∧
  ST σ u v (P3.sub P2) (P0.sub P2) ∧ ST σ u v (P3.sub P2) (P1.sub P2) ∧
  ST σ u v (P0.sub P3) (P1.sub P3) ∧ ST σ u v (P0.sub P3) (P2.sub P3)

/-- The four tests of a hidden point against a four-corner rim. -/
def Rest4 (σ : ℝ) (u v P0 P1 P2 P3 m : C3) : Prop :=
  ST σ u v (P1.sub P0) (m.sub P0) ∧ ST σ u v (P2.sub P1) (m.sub P1) ∧
  ST σ u v (P3.sub P2) (m.sub P2) ∧ ST σ u v (P0.sub P3) (m.sub P3)

theorem Cyc4.all {σ : ℝ} {u v P0 P1 P2 P3 : C3} (h : Cyc4 σ u v P0 P1 P2 P3) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
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

theorem Rest4.all {σ : ℝ} {u v P0 P1 P2 P3 m : C3} (h : Rest4 σ u v P0 P1 P2 P3 m) :
    ∀ i : ZMod 4, ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        (m.sub (quad P0 P1 P2 P3 i)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    assumption

/-- The ten tests of a five-corner rim cycle. -/
def Cyc5 (σ : ℝ) (u v P0 P1 P2 P3 P4 : C3) : Prop :=
  ST σ u v (P1.sub P0) (P2.sub P0) ∧ ST σ u v (P1.sub P0) (P3.sub P0) ∧
  ST σ u v (P1.sub P0) (P4.sub P0) ∧
  ST σ u v (P2.sub P1) (P3.sub P1) ∧ ST σ u v (P2.sub P1) (P4.sub P1) ∧
  ST σ u v (P2.sub P1) (P0.sub P1) ∧
  ST σ u v (P3.sub P2) (P4.sub P2) ∧ ST σ u v (P3.sub P2) (P0.sub P2) ∧
  ST σ u v (P3.sub P2) (P1.sub P2) ∧
  ST σ u v (P4.sub P3) (P0.sub P3) ∧ ST σ u v (P4.sub P3) (P1.sub P3) ∧
  ST σ u v (P4.sub P3) (P2.sub P3) ∧
  ST σ u v (P0.sub P4) (P1.sub P4) ∧ ST σ u v (P0.sub P4) (P2.sub P4) ∧
  ST σ u v (P0.sub P4) (P3.sub P4)

/-- The five tests of a hidden point against a five-corner rim. -/
def Rest5 (σ : ℝ) (u v P0 P1 P2 P3 P4 m : C3) : Prop :=
  ST σ u v (P1.sub P0) (m.sub P0) ∧ ST σ u v (P2.sub P1) (m.sub P1) ∧
  ST σ u v (P3.sub P2) (m.sub P2) ∧ ST σ u v (P4.sub P3) (m.sub P3) ∧
  ST σ u v (P0.sub P4) (m.sub P4)

theorem Cyc5.all {σ : ℝ} {u v P0 P1 P2 P3 P4 : C3} (h : Cyc5 σ u v P0 P1 P2 P3 P4) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j hi hj
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hi
    | exact absurd (by decide) hj
    | skip
  all_goals
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    assumption

theorem Rest5.all {σ : ℝ} {u v P0 P1 P2 P3 P4 m : C3} (h : Rest5 σ u v P0 P1 P2 P3 P4 m) :
    ∀ i : ZMod 5, ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        (m.sub (quint P0 P1 P2 P3 P4 i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    assumption

/-- `Q4` eventually from the two strict disjunctions. -/
theorem Q4_ev_strict {z w : ZMod 4 → ℝ}
    (hA : z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3)
    (hB : z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => z i + s * w i := by
  refine Q4_eventually ?_ ?_
  · rcases hA with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hB with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))


/-- `Q5p` eventually from the five strict disjunctions. -/
theorem Q5p_ev_strict {z w : ZMod 5 → ℝ}
    (h0 : z 0 < z 4 ∨ z 0 < z 1 ∨ z 2 < z 1 ∨ z 2 < z 3)
    (h1 : z 1 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2 ∨ z 3 < z 4)
    (h2 : z 2 < z 1 ∨ z 2 < z 3 ∨ z 4 < z 3 ∨ z 4 < z 0)
    (h3 : z 3 < z 2 ∨ z 3 < z 4 ∨ z 0 < z 4 ∨ z 0 < z 1)
    (h4 : z 4 < z 3 ∨ z 4 < z 0 ∨ z 1 < z 0 ∨ z 1 < z 2) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5p fun i => z i + s * w i := by
  have m : ∀ {a b c d e f g h : ZMod 5},
      (z a < z b ∨ z c < z d ∨ z e < z f ∨ z g < z h) →
      ((z a < z b ∨ (z a = z b ∧ w a < w b)) ∨ (z c < z d ∨ (z c = z d ∧ w c < w d)) ∨
        (z e < z f ∨ (z e = z f ∧ w e < w f)) ∨ (z g < z h ∨ (z g = z h ∧ w g < w h))) := by
    intro a b c d e f g h h'
    rcases h' with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  exact Q5p_eventually (m h0) (m h1) (m h2) (m h3) (m h4)

end Minimality.CaseC20

namespace Minimality.CaseC18.Frame7
open Minimality.CaseC20 Minimality.CaseC09 Filter
open scoped Topology
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- The four-corner bridge from the explicit screen tests and the two strict depth
disjunctions. -/
theorem rim4 (c0 c1 c2 c3 : Fin 7) (P0 P1 P2 P3 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hc : Cyc4 σ u v P0 P1 P2 P3)
    (hr : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 →
      Rest4 σ u v P0 P1 P2 P3 (F.ptC j'))
    (hA : F.GG P0 u < F.GG P1 u ∨ F.GG P0 u < F.GG P3 u ∨ F.GG P2 u < F.GG P1 u ∨
      F.GG P2 u < F.GG P3 u)
    (hB : F.GG P1 u < F.GG P0 u ∨ F.GG P3 u < F.GG P0 u ∨ F.GG P1 u < F.GG P2 u ∨
      F.GG P3 u < F.GG P2 u) :
    IsRupert (Finset.univ.image x) := by
  refine F.rupert_rim4 c0 c1 c2 c3 P0 P1 P2 P3 e0 e1 e2 e3 σ hσ u v hu hc.all
    (fun j' h0 h1 h2 h3 => (hr j' h0 h1 h2 h3).all) ?_
  have := Q4_ev_strict (z := fun i => F.GG (quad P0 P1 P2 P3 i) u)
    (w := fun i => F.GG (quad P0 P1 P2 P3 i) v)
    (by simpa only [quad_0, quad_1, quad_2, quad_3] using hA)
    (by simpa only [quad_0, quad_1, quad_2, quad_3] using hB)
  exact this

/-- The five-corner bridge (condition `Q5p`) from the explicit screen tests and the five strict
depth disjunctions. -/
theorem rim5p (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hc : Cyc5 σ u v P0 P1 P2 P3 P4)
    (hr : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 →
      Rest5 σ u v P0 P1 P2 P3 P4 (F.ptC j'))
    (h0 : F.GG P0 u < F.GG P4 u ∨ F.GG P0 u < F.GG P1 u ∨ F.GG P2 u < F.GG P1 u ∨
      F.GG P2 u < F.GG P3 u)
    (h1 : F.GG P1 u < F.GG P0 u ∨ F.GG P1 u < F.GG P2 u ∨ F.GG P3 u < F.GG P2 u ∨
      F.GG P3 u < F.GG P4 u)
    (h2 : F.GG P2 u < F.GG P1 u ∨ F.GG P2 u < F.GG P3 u ∨ F.GG P4 u < F.GG P3 u ∨
      F.GG P4 u < F.GG P0 u)
    (h3 : F.GG P3 u < F.GG P2 u ∨ F.GG P3 u < F.GG P4 u ∨ F.GG P0 u < F.GG P4 u ∨
      F.GG P0 u < F.GG P1 u)
    (h4 : F.GG P4 u < F.GG P3 u ∨ F.GG P4 u < F.GG P0 u ∨ F.GG P1 u < F.GG P0 u ∨
      F.GG P1 u < F.GG P2 u) :
    IsRupert (Finset.univ.image x) := by
  refine F.rupert_rim5p c0 c1 c2 c3 c4 P0 P1 P2 P3 P4 e0 e1 e2 e3 e4 σ hσ u v hu hc.all
    (fun j' h0 h1 h2 h3 h4 => (hr j' h0 h1 h2 h3 h4).all) ?_
  have := Q5p_ev_strict (z := fun i => F.GG (quint P0 P1 P2 P3 P4 i) u)
    (w := fun i => F.GG (quint P0 P1 P2 P3 P4 i) v)
    (by simpa only [quint_0, quint_1, quint_2, quint_3, quint_4] using h0)
    (by simpa only [quint_0, quint_1, quint_2, quint_3, quint_4] using h1)
    (by simpa only [quint_0, quint_1, quint_2, quint_3, quint_4] using h2)
    (by simpa only [quint_0, quint_1, quint_2, quint_3, quint_4] using h3)
    (by simpa only [quint_0, quint_1, quint_2, quint_3, quint_4] using h4)
  exact this

/-- The triangle bridge: no depth condition is needed (a triangle of distinct depths is
unimodal). -/
theorem rim3 (c0 c1 c2 : Fin 7) (P0 P1 P2 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hc : Cyc3 σ u v P0 P1 P2)
    (hr : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → Rest3 σ u v P0 P1 P2 (F.ptC j')) :
    IsRupert (Finset.univ.image x) := by
  have hc' : ∀ i, F.ptC (tri c0 c1 c2 i) = tri P0 P1 P2 i := by
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;> simp [tri_0, tri_1, tri_2, e0, e1, e2]
  refine F.rupert_rim (k := 3) (by norm_num) (tri c0 c1 c2) σ hσ u v hu ?_ ?_ (fun _ => True)
    isOpen_univ (fun _ _ _ _ => trivial) (fun _ _ _ => trivial) ?_
    (fun z hz _ => isCyclicUnimodal_three hz)
  · intro i j h1 h2
    simp only [hc']
    exact hc.all i j h1 h2
  · intro j' hj' i
    simp only [hc']
    refine (hr j' ?_ ?_ ?_).all i
    · exact fun h => hj' 0 (by simp [tri_0, h])
    · exact fun h => hj' 1 (by simp [tri_1, h])
    · exact fun h => hj' 2 (by simp [tri_2, h])
  · exact Filter.Eventually.of_forall (fun _ => trivial)

end Minimality.CaseC18.Frame7

end
