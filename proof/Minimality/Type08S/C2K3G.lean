module

public import Minimality.Type08S.C2K3F

@[expose] public section

/-!
# C2 / K3G: the wrapper for `TpA1ii` (package K3), the leftover `TpA1iiK`, and the composition `Resid08FinalK5`

`tpA1ii_hasLexCell`: with `E = det3 (b - d) (c - d) (a - d)` and `X = det3 (a' - b) (c - d) (a - d) = (β6 - 1) E`
(so `X * E` has the sign of `β6 - 1`), `TpA1ii` has a lex cell at the edge view `c - d` unless
* `X = 0` (`β6 = 1`), or
* `0 < X * E` and `⟪a' - c', c - d⟫ = 0` (`β6 > 1`, `s₁ = 0`), or
* `X * E < 0` and `⟪b - c', c - d⟫ = 0` (`β6 < 1`, `s₂ = 0`).
Cells: `C > 0`: Q1⁺, Q1⁻ (`s > 0`), Q4⁺, Q4⁻ (`s < 0`); `C = 0`: Q2⁺, Q2⁻ (`s > 0`), Q4⁺, Q4⁻ (`s < 0`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **K3 leftover**: `TpA1ii` with `β6 = 1` or the sign `s = ⟪t - c', c - d⟫` zero. -/
def TpA1iiK (a a' b b' c c' d : ℝ³) : Prop :=
  TpA1ii a a' b b' c c' d ∧
    (det3 (a' - b) (c - d) (a - d) = 0 ∨
     (0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) ∧ ⟪a' - c', c - d⟫ = 0) ∨
     (det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 ∧ ⟪b - c', c - d⟫ = 0))

namespace C2

set_option maxHeartbeats 3200000 in
theorem tpA1ii_hasLexCell {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1ii a a' b b' c c' d) (hX : det3 (a' - b) (c - d) (a - d) ≠ 0)
    (h1 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) → ⟪a' - c', c - d⟫ ≠ 0)
    (h2 : det3 (a' - b) (c - d) (a - d) * det3 (b - d) (c - d) (a - d) < 0 → ⟪b - c', c - d⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', -, hAl, hCnn, -, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6p, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  set D := det3 (a - d) (c - d) (b - d) with hD
  have hD0 : D ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -D := by simp only [hD, det3_expand]; ring
    rw [e, h0, neg_zero]
  have hα41 : α4 = 1 := by
    have e1 := det_alpha (b := b) hb'
    have : (α4 - 1) * D = 0 := by rw [hD]; rw [hAl] at e1; linarith
    have := (mul_eq_zero.mp this).resolve_right hD0
    linarith
  subst hα41
  set E := det3 (b - d) (c - d) (a - d) with hE
  have hE' : E = -D := by simp only [hE, hD, det3_expand]; ring
  have eB6 : det3 (a' - b) (c - d) (a - d) = (β6 - 1) * E := by
    rw [ha']; simp only [hE, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hE0 : E ≠ 0 := by rw [hE']; exact neg_ne_zero.2 hD0
  have hEE : 0 < E * E := mul_self_pos.2 hE0
  have hXE : det3 (a' - b) (c - d) (a - d) * E = (β6 - 1) * (E * E) := by rw [eB6]; ring
  have hb61 : β6 ≠ 1 := by intro h; apply hX; rw [eB6, h]; ring
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hΔ : det3 p q r ≠ 0 := hdet
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (1, 0, γ4) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, γ6) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  -- membership
  have hm : ∀ t : ℝ × ℝ × ℝ, (t = (0, 0, 1) ∨ t = (0, 0, 0) ∨ t = (1, 0, 0) ∨ t = (1, β1, 0) ∨
      t = (0, β6, γ6) ∨ t = (0, 1, 0) ∨ t = (1, 0, γ4)) → fpoint p q r d t ∈ V8 a a' b b' c c' d := by
    intro t ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [eO, eA, eB, eC, eC', eB', eA'] <;> simp [V8]
  have hVall : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4) := by
    intro y hy
    simp only [eO, eA, eB, eC, eC', eB', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  -- the sign data
  have hCC : ⟪q, r⟫ = ⟪c - d, b - d⟫ := real_inner_comm _ _
  have hC : 0 ≤ ⟪q, r⟫ := by rw [hCC]; exact hCnn
  have es1 : ⟪a' - c', r⟫ = (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫ := by
    have : a' - c' = (β6 - β1) • q + γ6 • r - p := by rw [ha', hc']; simp only [hp, hq, hr]; module
    rw [this, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
  have es2 : ⟪b - c', r⟫ = (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫ := by
    have : b - c' = (1 - β1) • q - p := by rw [hc']; simp only [hp, hq]; module
    rw [this, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
  refine ⟨r, hr0, ?_⟩
  have hs : 1 < β6 + γ6 := hcv
  rcases lt_or_gt_of_ne hb61 with hlt | hgt
  · have hneg : det3 (a' - b) (c - d) (a - d) * E < 0 := by rw [hXE]; nlinarith
    have hs2 := h2 hneg
    rw [es2] at hs2
    have hs2' := hs2
    rcases lt_or_gt_of_ne hs2' with hn | hp'
    · exact k3q4m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hlt hγ6 hs hC hn
        (fun i => by
          rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k3q4mCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
    · rcases hC.lt_or_eq with hCp | hC0
      · exact k3q1m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hlt hγ6 hs hCp hp'
          (fun i => by
            rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q1mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
      · exact k3q2m_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hβ6p hlt hγ6 hγ61 hs hC0.symm hp'
          (fun i => by
            rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q2mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
  · have hpos : 0 < det3 (a' - b) (c - d) (a - d) * E := by rw [hXE]; nlinarith
    have hs1 := h1 hpos
    rw [es1] at hs1
    have hs1' := hs1
    rcases lt_or_gt_of_ne hs1' with hn | hp'
    · exact k3q4p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hgt hγ6 hs hC hn
        (fun i => by
          rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
            simp [k3q4pCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5]) hVall
    · rcases hC.lt_or_eq with hCp | hC0
      · exact k3q1p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hgt hγ6 hs hCp hp'
          (fun i => by
            rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q1pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall
      · exact k3q2p_hasLexCellAt _ p q r d hΔ hβ1 hγ4 hgt hγ6 hγ61 hs hC0.symm hp'
          (fun i => by
            rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> apply hm <;>
              simp [k3q2pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4]) hVall

end C2

/-- `TpA1ii` off `TpA1iiK` has a lex cell. -/
theorem tpA1ii_hasLexCell' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : TpA1ii a a' b b' c c' d) (hn : ¬ TpA1iiK a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  refine C2.tpA1ii_hasLexCell N h ?_ ?_ ?_
  · intro e; exact hn ⟨h, Or.inl e⟩
  · intro hp e; exact hn ⟨h, Or.inr (Or.inl ⟨hp, e⟩)⟩
  · intro hp e; exact hn ⟨h, Or.inr (Or.inr ⟨hp, e⟩)⟩

def ResNK5 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TRK3 a a' b b' c c' d ∨ TpA1iiK a a' b b' c c' d) ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNK5 (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNK5 N

/-- **`Resid08FinalK5`**: `Resid08FinalK4` with `TpA1ii` cut down to `TpA1iiK` (package K3). -/
def Resid08FinalK5 (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNK5 a a' b b' c c' d ∨ ResidNK5 b b' a a' c c' d ∨ ResidNK5 a a' c c' b b' d ∨
  ResidNK5 c c' a a' b b' d ∨ ResidNK5 b b' c c' a a' d ∨ ResidNK5 c c' b b' a a' d

theorem resNK4_imp_K5 {a a' b b' c c' d : ℝ³} {N : Norm08 a a' b b' c c' d} (h : ResNK4 N) : ResNK5 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, h3⟩
  rcases h2 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    by_contra hn
    exact h3 (tpA1ii_hasLexCell' N h hn)

theorem resid08FinalK4_imp_K5 {a a' b b' c c' d : ℝ³} (h : Resid08FinalK4 a a' b b' c c' d) :
    Resid08FinalK5 a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNK4 p p' q q' r r' d → ResidNK5 p p' q q' r r' d :=
    fun ⟨N, hN⟩ => ⟨N, resNK4_imp_K5 hN⟩
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

