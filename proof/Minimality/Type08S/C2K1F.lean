module

public import Minimality.Type08S.C2K1E

@[expose] public section

/-!
# C2 / K1F: `S4TRK2 ∧ s ≠ 0` has a lex cell, and the shrunk residual `Resid08FinalK3`
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **`S4TRK2` off the slice `s = ⟪a' - b, a - d⟫ = 0` has a lex cell** at the edge view `a - d`:
`s > 0` the 5-cycle `(d, b, a', b', c)`, `s < 0` the 6-cycle `(a, c', b, a', c, d)`. -/
theorem k1_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : S4TRK2 a a' b b' c c' d)
    (hs : ⟪a' - b, a - d⟫ ≠ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT, hL, hγ⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hα4, hγ4, hβ1, hβ6, hE⟩ := norm08_coords3 N hT
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have eA : det3 (c - b') (a - d) (b - d) = -(1 - γ4) * D := by
    rw [hb']; simp only [hD, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hγ41 : γ4 = 1 := by
    have := (mul_eq_zero.mp (by rw [← eA]; exact hγ : -(1 - γ4) * D = 0)).resolve_right hD0
    linarith
  subst hγ41
  have hβ11 : β1 < 1 := by nlinarith
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hΔ : det3 p q r ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 p q r := by simp only [hp, hq, hr, det3_expand]; ring
    rw [e, h]
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hB : 0 ≤ ⟪a - d, b - d⟫ := by
    have ha1 : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) := by rw [ha', one_smul]
    refine k1_B_nonneg hp0 hc' hb' ha1 hα4 hβ6 ?_
    rcases hL with ⟨hK, hN, -, -⟩ | ⟨hK, hX, -, hE', -, -⟩
    · exact Or.inl ⟨hK, hN⟩
    · exact Or.inr ⟨hK, hX, hE'⟩
  have hB' : 0 ≤ ⟪p, r⟫ := by rw [real_inner_comm]; exact hB
  have es : ⟪a' - b, a - d⟫ = (β6 - 1) * ⟪p, r⟫ + ⟪q, r⟫ := by
    have : a' - b = (β6 - 1) • (b - d) + (c - d) := by rw [ha']; module
    rw [this, inner_add_left, real_inner_smul_left]
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint p q r d (1, 0, 0) = b := by simp only [fpoint, fcomb, hp]; module
  have eC : fpoint p q r d (0, 1, 0) = c := by simp only [fpoint, fcomb, hq]; module
  have eA1 : fpoint p q r d (0, 0, 1) = a := by simp only [fpoint, fcomb, hr]; module
  have eA' : fpoint p q r d (β6, 1, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hp, hq]; module
  have eC' : fpoint p q r d (β1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hr]; module
  have eB' : fpoint p q r d (0, 1, α4) = b' := by rw [hb']; simp only [fpoint, fcomb, hq, hr]; module
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, 1, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (β1, 0, α1) := by
    intro y hy
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl eO.symm)
    · exact Or.inl eA1.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl eA'.symm)))
    · exact Or.inr (Or.inr (Or.inl eB.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eB'.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eC.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eC'.symm)))))
  have hne : a - d ≠ 0 := by
    intro had; apply hdet
    have h0 : r = 0 := had
    rw [h0]; simp [det3_expand]
  refine ⟨a - d, hne, ?_⟩
  rw [es] at hs
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · refine k1x2_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα1 hβ1 hβ11 hα4 hβ6 hB' hlt ?_ hVall
    intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k1Cyc6, six_0, eA1]; simp [V8]
    · simp only [k1Cyc6, six_1, eC']; simp [V8]
    · simp only [k1Cyc6, six_2, eB]; simp [V8]
    · simp only [k1Cyc6, six_3, eA']; simp [V8]
    · simp only [k1Cyc6, six_4, eC]; simp [V8]
    · simp only [k1Cyc6, six_5, eO]; simp [V8]
  · refine k1x1_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (lt_trans one_pos hα1) hβ1 hβ11 hα4 hβ6 hB' hgt ?_ hVall
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k1Cyc, pc5_0, eO]; simp [V8]
    · simp only [k1Cyc, pc5_1, eB]; simp [V8]
    · simp only [k1Cyc, pc5_2, eA']; simp [V8]
    · simp only [k1Cyc, pc5_3, eB']; simp [V8]
    · simp only [k1Cyc, pc5_4, eC]; simp [V8]

end C2

/-- `S4TRK2` on the slice `s = ⟪a' - b, a - d⟫ = 0` (codimension 6). -/
def S4TRK3 (a a' b b' c c' d : ℝ³) : Prop :=
  S4TRK2 a a' b b' c c' d ∧ ⟪a' - b, a - d⟫ = 0

def ResNK3 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK3 a a' b b' c c' d ∨ S4TpRK a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d) ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK3 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK3 N

/-- **`Resid08FinalK3`**: `Resid08FinalK2` with `S4TRK2` cut down to the slice `⟪a' - b, a - d⟫ = 0`. -/
def Resid08FinalK3 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK3 a a' b b' c c' d ∨ ResidNK3 b b' a a' c c' d ∨ ResidNK3 a a' c c' b b' d ∨
  ResidNK3 c c' a a' b b' d ∨ ResidNK3 b b' c c' a a' d ∨ ResidNK3 c c' b b' a a' d

theorem resNK2_imp_K3 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK2 N) : ResNK3 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with h | h | h
  · refine Or.inl ⟨h, ?_⟩
    by_contra hne
    exact h3 (C2.k1_hasLexCell N h hne)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem resid08FinalK2_imp_K3 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK2 a a' b b' c c' d) :
    Resid08FinalK3 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK2 p p' q q' r r' d → ResidNK3 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK2_imp_K3 hN⟩
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (g h))
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h))))))

/-- `K3 ⊆ K2` (for the record). -/
theorem resid08FinalK3_imp_K2 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK3 a a' b b' c c' d) :
    Resid08FinalK2 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK3 p p' q q' r r' d → ResidNK2 p p' q q' r r' d := by
    rintro p p' q q' r r' ⟨N, h1, h2, h3⟩
    refine ⟨N, h1, ?_, h3⟩
    rcases h2 with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (g h))
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h))))))

end Type08Sp
end Minimality

