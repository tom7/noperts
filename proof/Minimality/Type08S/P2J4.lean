module

public import Minimality.Type08S.P2I5b
public import Minimality.Type08S.P2I7b
public import Minimality.Type08S.P2TpX

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- At the level face of `Q_ac` at `T'`, `X_bc' = (b, c', b', c)` is robustly unimodal at `ℓ = b - d`
(depths `(1, β1, 0, 0)` up to shift and scale, `β1 > 0`). -/
theorem level_robust_Xbc {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hlev : LevelQac a b c d) :
    IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨hla, hlc⟩ := hlev
  have hbb : 0 < ⟪b - d, b - d⟫ := by
    rw [real_inner_self_eq_norm_sq]
    have : b - d ≠ 0 := sub_ne_zero.mpr (N.hd.ne.2.2.1.symm)
    positivity
  have e1 : ⟪c', b - d⟫ = ⟪d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    have : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) := hc'
    rw [this, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hla]; ring
  have e2 : ⟪b', b - d⟫ = ⟪d, b - d⟫ := by
    rw [hb', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hla, hlc]; ring
  have e3 : ⟪c, b - d⟫ = ⟪d, b - d⟫ := by
    have : ⟪c - d, b - d⟫ = 0 := hlc
    rw [inner_sub_left] at this; linarith
  have e0 : ⟪b, b - d⟫ = ⟪d, b - d⟫ + ⟪b - d, b - d⟫ := by
    have := inner_sub_left (𝕜 := ℝ) b d (b - d)
    linarith
  have hf : (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫) =
      quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ := by
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad]
  rw [hf]
  refine CaseC18.robust_quad_of_nws ?_ ?_
  · right; right; left; rw [e2, e1]; linarith [mul_pos hβ1 hbb]
  · right; left; rw [e0, e3]; linarith

/-- **Level case with `a` hidden** (`α4 > 1`): the slide of `K_b` (R4h) applies, `X_bc'` being automatically robust. -/
theorem Tp_level_hid {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hlev : LevelQac a b c d) {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : 1 < α4)
    (hR1 : NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  close_Tp_R4h_hdn N hT' hb'rep hα (level_robust_Xbc N hT' hlev) hR1

end Type08Sp
end Minimality
#print axioms Minimality.Type08Sp.Tp_level_hid
