module

public import Minimality.Type08S.G6E7
public import Minimality.Type08S.G6F1
public import Minimality.Type08S.G6p

@[expose] public section

set_option autoImplicit true

/-!
# G6' : the closing theorems at `T` and `T'` (wired)

* `close_T_H1`: PROVED modulo the explicit residual `OpenB` (below): case A is `closeT_H1_caseA`
  (G6B7); case B is `poly_rupert_H1` (G6E5: Theorem 18.1 on a robust HDN-free corner polygon at
  `ℓ`); HDN-freeness of the other polygons comes from `¬ CoT2` (`PolyHDN2`, `PolyHDN`) and
  `classD1_hdn` (G6E7: a class-(d) HDN of R1 is a horizontal double normal of `{b, c', b', c}`).
* (stubs removed 2026-10-28: the final T/T' closings are in `G6Z.lean`.)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The four corner polygons at `ℓ` (R1, R2', X_ba', X_2a'): each is `Sep` (weakly two-peaked,
not robust) or has a horizontal double normal.  This is the one configuration of `T ∩ H1` that
the 18.1 route does not reach (it needs the paper's order Claim for `X_2a'` / Theorem 29.15 on a
non-robust polygon). -/
def OpenB (a' b b' c c' d : ℝ³) : Prop :=
  (¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) ∨ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫) ∧
  (¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) ∨ Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫) ∧
  (¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) ∨ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫) ∧
  (¬ NoHDNAt ({d, c', b', a'} : Finset ℝ³) (b - d) ∨ Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫)

/-- Case A of `T ∩ H1` (Theorem 08.T'): R1 with a class-(d) HDN, robust; R2', X_ba' not robust. -/
def CaseA (b b' c c' d a' : ℝ³) : Prop :=
  ClassD1 b b' c c' d ∧ ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫ ∧
  Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪c, b - d⟫ ∧ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪a', b - d⟫

theorem b_ne_d {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H1 b b' c c' d) : b ≠ d := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α, β1, γ4, β6, hF, hν, -, -, -, -, -, -, hu, -⟩ :=
    h1_setup N hT hH
  intro h
  rw [h, sub_self] at hu
  have := congrArg (fun v => ⟪v, e3⟫) hu.symm
  simp only [real_inner_smul_left, hF.n33, inner_zero_left] at this
  linarith

theorem norm08_ne {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    b ≠ c' ∧ b ≠ b' ∧ b ≠ c ∧ b' ≠ c ∧ a' ≠ b ∧ a' ≠ b' ∧ a' ≠ c ∧ a' ≠ c' ∧ c ≠ c' := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  exact ⟨hbc', hbb', hbc, hb'c, ha'b, ha'b', ha'c, ha'c', hcc'⟩

/-- **T on H1** (no extra hypothesis: the order Claim is `allsep_false`, G6F1). -/
theorem close_T_H1 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H1 b b' c c' d) (hco : ¬ CoT2 a a' b b' c c' d)
    (hnt : ¬ RTouch a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hbc', hbb', hbc, hb'c, ha'b, ha'b', ha'c, ha'c', hcc'⟩ := norm08_ne N
  have hbd := b_ne_d N hT hH
  have hnH2 : ¬ H2 a b b' c d := fun h => hco (Or.inl ⟨hH, h⟩)
  have hP2 : ¬ PolyHDN2 a' b b' c c' d := fun h => hco (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hP6 : ¬ (PolyHDN a' b b' c c' d ∧ ¬ (ClassD1 b b' c c' d ∨ ClassD2 a b b' c c' d)) :=
    fun h => hco (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have hnD2 : ¬ ClassD2 a b b' c c' d := fun h => hnH2 h.1
  have key : ∀ {x0 x0' y0 y0' : ℝ³}, ((x0 = b ∧ x0' = d) ∨ (x0 = d ∧ x0' = b)) →
      ((y0 = c ∧ y0' = a') ∨ (y0 = a' ∧ y0' = c)) →
      ¬ Sep ⟪x0, b - d⟫ ⟪b', b - d⟫ ⟪y0, b - d⟫ ⟪c', b - d⟫ →
      NoHDNAt ({x0, c', b', y0} : Finset ℝ³) (b - d) →
      IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
    fun hx hy hr hn => poly_rupert_H1 N hT hH hx hy hr hn
  have hx1 : (b = b ∧ d = d) ∨ (b = d ∧ d = b) := Or.inl ⟨rfl, rfl⟩
  have hx2 : (d = b ∧ b = d) ∨ (d = d ∧ b = b) := Or.inr ⟨rfl, rfl⟩
  have hy1 : (c = c ∧ a' = a') ∨ (c = a' ∧ a' = c) := Or.inl ⟨rfl, rfl⟩
  have hy2 : (a' = c ∧ c = a') ∨ (a' = a' ∧ c = c) := Or.inr ⟨rfl, rfl⟩
  by_cases hD : ClassD1 b b' c c' d
  · have hN1 := classD1_hdn N hT hD
    have hne12 : ({b, c', b', c} : Finset ℝ³) ≠ {d, c', b', c} := by
      intro h
      have : b ∈ ({d, c', b', c} : Finset ℝ³) := h ▸ (by simp)
      simp [hbd, hbc', hbb', hbc] at this
    have hne1X : ({b, c', b', c} : Finset ℝ³) ≠ {b, c', b', a'} := by
      intro h
      have : c ∈ ({b, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
      simp [hbc.symm, hcc', hb'c.symm, ha'c.symm] at this
    have hne12a : ({b, c', b', c} : Finset ℝ³) ≠ {d, c', b', a'} := by
      intro h
      have : b ∈ ({d, c', b', a'} : Finset ℝ³) := h ▸ (by simp)
      simp [hbd, hbc', hbb', ha'b.symm] at this
    have mem4 : ∀ S : Finset ℝ³, S ∈ ({{b, c', b', c}, {d, c', b', c}, {b, c', b', a'}, {d, c', b', a'}} :
        Finset (Finset ℝ³)) ∨ True := fun _ => Or.inr trivial
    have f2 : NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) := by
      by_contra h
      exact hP2 ⟨_, _, hne12, by simp, by simp, hN1, h⟩
    have fX : NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) := by
      by_contra h
      exact hP2 ⟨_, _, hne1X, by simp, by simp, hN1, h⟩
    have f2a : NoHDNAt ({d, c', b', a'} : Finset ℝ³) (b - d) := by
      by_contra h
      exact hP2 ⟨_, _, hne12a, by simp, by simp, hN1, h⟩
    by_cases h2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
    · by_cases hX : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
      · by_cases h1 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
        · by_cases h2a : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
          · exact (allsep_false N hT hH h1 h2 hX).elim
          · exact key hx2 hy2 h2a f2a
        · exact closeT_H1_caseA N hT hD h1 ((sep_swap _ _ _ _).mp h2) ((sep_swap _ _ _ _).mp hX)
      · exact key hx1 hy2 hX fX
    · exact key hx2 hy1 h2 f2
  · have hnP : ¬ PolyHDN a' b b' c c' d := fun h => hP6 ⟨h, fun h' => h'.elim hD hnD2⟩
    simp only [PolyHDN, not_or, not_not] at hnP
    obtain ⟨n1, n2, nX, n2a⟩ := hnP
    by_cases h1 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
    · by_cases h2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫
      · by_cases hX : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
        · by_cases h2a : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫
          · exact (allsep_false N hT hH h1 h2 hX).elim
          · exact key hx2 hy2 h2a n2a
        · exact key hx1 hy2 hX nX
      · exact key hx2 hy1 h2 n2
    · exact key hx1 hy1 h1 n1


#print axioms Minimality.Type08Sp.close_T_H1
#print axioms Minimality.Type08Sp.classD1_hdn
#print axioms Minimality.Type08Sp.poly_rupert_H1
