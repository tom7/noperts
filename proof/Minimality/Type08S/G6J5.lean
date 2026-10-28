module

public import Minimality.Type08S.G6J4
public import Minimality.Type08S.G6p
public import Minimality.Type08S.G6F1

@[expose] public section

set_option autoImplicit true

/-!
# G6' : `close_T_off'` (T off H1 ∪ H2: Theorem 18.1 on the four corner polygons, general frame)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The order Claim of 29.12 off `H1 ∪ H2`: the four corner polygons cannot all be weakly two-peaked. -/
theorem allsep4_false {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d)
    (h1 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫)
    (h2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫)
    (h3 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫)
    (h4 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫) : False := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα, hα4, hγ4, hb1, hb6, hE⟩ :=
    norm08_coords3 N hT
  have hu : 0 < ⟪b - d, b - d⟫ := by
    apply real_inner_self_pos.mpr
    intro h
    apply hdet
    have : b - d = 0 := h
    simp [det3_expand, this]
  have e : ∀ x : ℝ³, ⟪x, b - d⟫ = ⟪d, b - d⟫ + ⟪x - d, b - d⟫ := by
    intro x; rw [← inner_add_left]; congr 1; abel
  have ec' : ⟪c', b - d⟫ = ⟪d, b - d⟫ + α1 * ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    rw [hc']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    rw [hb']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have ea' : ⟪a', b - d⟫ = ⟪d, b - d⟫ + β6 * ⟪b - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb : ⟪b, b - d⟫ = ⟪d, b - d⟫ + ⟪b - d, b - d⟫ := e b
  have ec : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := e c
  rw [eb, eb', ec, ec'] at h1
  rw [eb', ec, ec'] at h2
  rw [eb, eb', ea', ec'] at h3
  rw [eb', ea', ec'] at h4
  generalize ⟪d, b - d⟫ = z0 at *
  generalize ⟪b - d, b - d⟫ = n at *
  generalize ⟪c - d, b - d⟫ = q at *
  generalize ⟪a - d, b - d⟫ = p at *
  have sh : ∀ {x y u v : ℝ}, Sep (z0 + x) (z0 + y) (z0 + u) (z0 + v) → Sep x y u v :=
    fun h => (sep_shift z0 _ _ _ _).1 h
  have r1 := sh (x := n) (y := α4 * p + γ4 * q) (u := q) (v := α1 * p + β1 * n)
    (by simpa only [add_assoc] using h1)
  have r2 := sh (x := 0) (y := α4 * p + γ4 * q) (u := q) (v := α1 * p + β1 * n)
    (by simpa only [add_assoc, add_zero] using h2)
  have r3 := sh (x := n) (y := α4 * p + γ4 * q) (u := β6 * n + q) (v := α1 * p + β1 * n)
    (by simpa only [add_assoc] using h3)
  have r4 := sh (x := 0) (y := α4 * p + γ4 * q) (u := β6 * n + q) (v := α1 * p + β1 * n)
    (by simpa only [add_assoc, add_zero] using h4)
  exact allsep4_real hu hα hα4 hγ4 hb1 hb6 hE (by ring) r1 r2 r3 r4

/-- **T off H1 ∪ H2** (29.12 A1, A2(c), B1, B2(c)), Theorem 18.1 form: under `¬CoT2` and off `H1 ∪ H2`
no corner polygon has a horizontal double normal (`PolyHDN` would force a class-(d) HDN, which
needs `H1` or `H2`), and not all four are weakly two-peaked (`allsep4_false`). -/
theorem close_T_off' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH1 : ¬ H1 b b' c c' d) (hH2 : ¬ H2 a b b' c d)
    (hco : ¬ CoT2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hP6 : ¬ (PolyHDN a' b b' c c' d ∧ ¬ (ClassD1 b b' c c' d ∨ ClassD2 a b b' c c' d)) :=
    fun h => hco (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have hnP : ¬ PolyHDN a' b b' c c' d := by
    intro h
    apply hP6 ⟨h, ?_⟩
    rintro (h' | h')
    · exact hH1 h'.1
    · exact hH2 h'.1
  unfold PolyHDN at hnP
  simp only [not_or, not_not] at hnP
  obtain ⟨n1, n2, n3, n4⟩ := hnP
  by_cases r1 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
  · by_cases r2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
    · by_cases r3 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
      · by_cases r4 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
        · exact (allsep4_false N hT r1 r2 r3 r4).elim
        · exact poly_rupert_off N hT (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) r4 n4
      · exact poly_rupert_off N hT (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) r3 n3
    · exact poly_rupert_off N hT (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) r2 n2
  · exact poly_rupert_off N hT (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) r1 n1

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T_off'
