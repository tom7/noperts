module

public import Minimality.Type08S.P2Defs

@[expose] public section

set_option relaxedAutoImplicit true

/-! # P1a: `CoT2'` (= `CoT2` without the `H2` item `det3 (a-d) (b'-c) (b-d) = 0`) and `close_T2_final'`. -/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `CoT2` minus the `H2` item (D3: that item is exactly `H2`). -/
def CoT2' (a a' b b' c c' d : ℝ³) : Prop :=
  (H1 b b' c c' d ∧ H2 a b b' c d) ∨ FootEnd1 b b' c c' d ∨ FootEnd2 a b b' c c' d ∨
    PolyHDN2 a' b b' c c' d ∨ TwoTies a' b b' c c' d ∨ (Tie6 a' b b' c c' d ∧ PolyHDN a' b b' c c' d) ∨
    (PolyHDN a' b b' c c' d ∧ ¬ (ClassD1 b b' c c' d ∨ ClassD2 a b b' c c' d)) ∨
    (⟪a - d, b - d⟫ = 0 ∧ ⟪c - d, b - d⟫ = 0)

theorem H2_iff_det3 (a b b' c d : ℝ³) : H2 a b b' c d ↔ det3 (a - d) (b' - c) (b - d) = 0 := by
  unfold H2
  rw [det3_swap (c - b') (a - d), ← neg_sub b' c, det3_neg_mid, neg_neg]

/-- From `¬CoT2'` and `¬H2` get `¬CoT2`. -/
theorem not_CoT2_of_not_CoT2' {a a' b b' c c' d : ℝ³} (h : ¬ CoT2' a a' b b' c c' d)
    (hH2 : ¬ H2 a b b' c d) : ¬ CoT2 a a' b b' c c' d := by
  intro hc
  unfold CoT2 at hc
  rcases hc with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact h (Or.inl h1)
  · exact h (Or.inr (Or.inl h1))
  · exact h (Or.inr (Or.inr (Or.inl h1)))
  · exact h (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
  · exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))
  · exact hH2 ((H2_iff_det3 _ _ _ _ _).mpr h1)
  · exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))))

set_option maxHeartbeats 1000000 in
theorem close_T_H2'' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H2 a b b' c d) (hco : ¬ CoT2' a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hbc', hbb', hbc, hb'c, ha'b, ha'b', ha'c, ha'c', hcc'⟩ := norm08_ne N
  obtain ⟨hcd, hbd, hsel⟩ := h2_select N hT hH
  have hb'c' : b' ≠ c' := by
    have hnd := N.F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    exact hnd.2.2.2.1.2
  have hP2 : ¬ PolyHDN2 a' b b' c c' d := fun h => hco (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hTT : ¬ TwoTies a' b b' c c' d := fun h => hco (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have key : ∀ {x0 x0' y0 y0' : ℝ³}, ((x0 = b ∧ x0' = d) ∨ (x0 = d ∧ x0' = b)) →
      ((y0 = c ∧ y0' = a') ∨ (y0 = a' ∧ y0' = c)) →
      ¬ Sep ⟪x0, b - d⟫ ⟪b', b - d⟫ ⟪y0, b - d⟫ ⟪c', b - d⟫ →
      NoHDNAt ({x0, c', b', y0} : Finset ℝ³) (b - d) →
      IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
    fun hx hy hr hn => poly_rupert_H2 N hT hH hx hy hr hn
  have hx1 : (b = b ∧ d = d) ∨ (b = d ∧ d = b) := Or.inl ⟨rfl, rfl⟩
  have hx2 : (d = b ∧ b = d) ∨ (d = d ∧ b = b) := Or.inr ⟨rfl, rfl⟩
  have hy1 : (c = c ∧ a' = a') ∨ (c = a' ∧ a' = c) := Or.inl ⟨rfl, rfl⟩
  have hy2 : (a' = c ∧ c = a') ∨ (a' = a' ∧ c = c) := Or.inr ⟨rfl, rfl⟩
  -- the four polygons and their distinctness
  have m1 : ({b, c', b', c} : Finset ℝ³) ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) := by simp
  have m2 : ({d, c', b', c} : Finset ℝ³) ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) := by simp
  have m3 : ({b, c', b', a'} : Finset ℝ³) ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) := by simp
  have m4 : ({d, c', b', a'} : Finset ℝ³) ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) := by simp
  have n12 : ({b, c', b', c} : Finset ℝ³) ≠ {d, c', b', c} := by
    intro h; have : b ∈ ({d, c', b', c} : Finset ℝ³) := h ▸ (by simp)
    simp [hbd, hbc', hbb', hbc] at this
  have n13 : ({b, c', b', c} : Finset ℝ³) ≠ {b, c', b', a'} := by
    intro h; have : c ∈ ({b, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
    simp [hbc.symm, hcc', hb'c.symm, ha'c.symm] at this
  have n14 : ({b, c', b', c} : Finset ℝ³) ≠ {d, c', b', a'} := by
    intro h; have : b ∈ ({d, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
    simp [hbd, hbc', hbb', ha'b.symm] at this
  have n23 : ({d, c', b', c} : Finset ℝ³) ≠ {b, c', b', a'} := by
    intro h; have : b ∈ ({d, c', b', c} : Finset ℝ³) := h ▸ (by simp)
    simp [hbd, hbc', hbb', hbc] at this
  have n24 : ({d, c', b', c} : Finset ℝ³) ≠ {d, c', b', a'} := by
    intro h; have : c ∈ ({d, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
    simp [hcd, hcc', hb'c.symm, ha'c.symm] at this
  have n34 : ({b, c', b', a'} : Finset ℝ³) ≠ {d, c', b', a'} := by
    intro h; have : b ∈ ({d, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
    simp [hbd, hbc', hbb', ha'b.symm] at this
  have two : ∀ {S T : Finset ℝ³}, S ≠ T → S ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) → T ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'},
      {d, c', b', a'}} : Finset (Finset ℝ³)) → NoHDNAt S (b - d) ∨ NoHDNAt T (b - d) := by
    intro S T hST hS hT'
    by_contra h
    push_neg at h
    exact hP2 ⟨S, T, hST, hS, hT', h.1, h.2⟩
  -- ties are excluded
  have mem6 : ∀ p : ℝ³, (p = d ∨ p = b ∨ p = c ∨ p = a' ∨ p = b' ∨ p = c') →
      p ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  rcases hsel with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨t1, t2⟩
  · -- R1, R2'
    rcases two n12 m1 m2 with h | h
    · exact key hx1 hy1 r1 h
    · exact key hx2 hy1 r2 h
  · rcases two n13 m1 m3 with h | h
    · exact key hx1 hy1 r1 h
    · exact key hx1 hy2 r2 h
  · rcases two n14 m1 m4 with h | h
    · exact key hx1 hy1 r1 h
    · exact key hx2 hy2 r2 h
  · rcases two n23 m2 m3 with h | h
    · exact key hx2 hy1 r1 h
    · exact key hx1 hy2 r2 h
  · rcases two n24 m2 m4 with h | h
    · exact key hx2 hy1 r1 h
    · exact key hx2 hy2 r2 h
  · rcases two n34 m3 m4 with h | h
    · exact key hx1 hy2 r1 h
    · exact key hx2 hy2 r2 h
  · exfalso
    apply hTT
    have m_d : d ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    have m_b : b ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    have m_c : c ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    have m_a : a' ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    have m_b' : b' ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    have m_c' : c' ∈ ({d, b, c, a', b', c'} : Finset ℝ³) := by simp
    rcases t2 with t2 | t2 | t2
    · refine ⟨b', m_b', c', m_c', b', m_b', c, m_c, hb'c', hb'c, ?_, t1, t2⟩
      intro h
      have : c ∈ ({b', c'} : Finset ℝ³) := h ▸ (by simp)
      simp [hb'c.symm, hcc'] at this
    · refine ⟨b', m_b', c', m_c', b', m_b', a', m_a, hb'c', ha'b'.symm, ?_, t1, t2⟩
      intro h
      have : a' ∈ ({b', c'} : Finset ℝ³) := h ▸ (by simp)
      simp [ha'b', ha'c'] at this
    · refine ⟨b', m_b', c', m_c', c', m_c', b, m_b, hb'c', hbc'.symm, ?_, t1, t2⟩
      intro h
      have : b ∈ ({b', c'} : Finset ℝ³) := h ▸ (by simp)
      simp [hbb', hbc'] at this


theorem close_T2_final' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hco : ¬ CoT2' a a' b b' c c' d) (hnt : ¬ RTouch a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  by_cases h1 : H1 b b' c c' d
  · have hnH2 : ¬ H2 a b b' c d := fun h => hco (Or.inl ⟨h1, h⟩)
    exact close_T_H1 N hT h1 (not_CoT2_of_not_CoT2' hco hnH2) hnt
  · by_cases h2 : H2 a b b' c d
    · exact close_T_H2'' N hT h2 hco
    · exact close_T_off' N hT h1 h2 (not_CoT2_of_not_CoT2' hco h2)

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T2_final'
