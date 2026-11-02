module

public import Minimality.Type08S.C2K22X1B
public import Minimality.Type08S.C2K22X2B
public import Minimality.Type08S.C2K22X3B
public import Minimality.Type08S.C2K22T1B
public import Minimality.Type08S.C2K22T2B

@[expose] public section


/-!
# Pc C2: composition of the cells X1, X2, X3 (strict) and the ties T1 (β1 = 1), T2 (a' on c'b').
Split on β1 vs 1 and, for β1 > 1, on the sign of β1γ4 - β1γ6 - γ4 (frame of `k17gc_pc_frame`).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
namespace C2

theorem k22c2_coord_uniq {u v w : ℝ³} {x y : ℝ} (hw : w ≠ 0) (h1 : u = v + x • w) (h2 : u = v + y • w) :
    x = y := by
  have h : (x - y) • w = 0 := by
    rw [sub_smul, add_left_cancel (h1.symm.trans h2), sub_self]
  rcases smul_eq_zero.1 h with h | h
  · linarith
  · exact absurd h hw

theorem k22c2_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d)
    (hC2 : 0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0 ∧ ⟪b' - c, d - b⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', -⟩ := k17gc_pc_frame W h.1
  have hq : b - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hr : c - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have uβ : ∀ β : ℝ, c' = d + (1:ℝ) • (a - d) + β • (b - d) → β = β1 := fun β e => k22c2_coord_uniq hq e hc'
  have uγ4 : ∀ γ : ℝ, b' = d + (1:ℝ) • (a - d) + γ • (c - d) → γ = γ4 := fun γ e => k22c2_coord_uniq hr e hb'
  have uγ6 : ∀ γ : ℝ, a' = d + (1:ℝ) • (b - d) + γ • (c - d) → γ = γ6 := fun γ e => k22c2_coord_uniq hr e ha'
  rcases lt_trichotomy β1 1 with hl | he | hg
  · exact k22x3_cell W h hC2 (fun β e => by rw [uβ β e]; exact hl)
  · exact k22t1_cell W h hC2 (by rw [hc', he])
  · have hβ : ∀ β : ℝ, c' = d + (1:ℝ) • (a - d) + β • (b - d) → 1 < β := fun β e => by rw [uβ β e]; exact hg
    rcases lt_trichotomy 0 (β1 * γ4 - β1 * γ6 - γ4) with s | s | s
    · exact k22x1_cell W h hC2 hβ (fun x y z e1 e2 e3 => by rw [uβ x e1, uγ4 y e2, uγ6 z e3]; exact s)
    · exact k22t2_cell W h hC2 hβ (fun x y z e1 e2 e3 => by rw [uβ x e1, uγ4 y e2, uγ6 z e3]; linarith)
    · exact k22x2_cell W h hC2 hβ (fun x y z e1 e2 e3 => by rw [uβ x e1, uγ4 y e2, uγ6 z e3]; linarith)

end C2
end Type08Sp
end Minimality
