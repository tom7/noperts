module

public import Minimality.Type08S.P2S5

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {a a' b b' c c' d : ℝ³}

theorem quad_inner_fun (p0 p1 p2 p3 v : ℝ³) :
    (fun i : ZMod 4 => ⟪quad p0 p1 p2 p3 i, v⟫) = quad ⟪p0, v⟫ ⟪p1, v⟫ ⟪p2, v⟫ ⟪p3, v⟫ := by
  funext i; fin_cases i <;> rfl

/-- **Depth lemma** (draft §3): at the tie, the separation holds.  (The weak-far alternative
`D(c') = D(b') = D(c)` is excluded by robustness of `X_bc'` (no three equal depths), so only the
separation remains.) -/
theorem Tp_tie_sep (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d))
    (hq : QacTop a b b' c d)
    (hrob : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫))
    (h2 : ¬ IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫)) :
    max (max ⟪d, b - d⟫ ⟪a, b - d⟫) (max ⟪b', b - d⟫ ⟪c, b - d⟫)
      < min ⟪b, b - d⟫ ⟪c', b - d⟫ := by
  obtain ⟨β1, β6, γ6, hne, hc', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ := Tp_frame N hT' hb'rep
  have hdb : d ≠ b := N.hd.ne.2.2.1
  have hn : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  have e1 : ⟪a - d, b - d⟫ = ⟪a, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e2 : ⟪c - d, b - d⟫ = ⟪c, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e3 : ⟪b - d, b - d⟫ = ⟪b, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e4 : ⟪b' - d, b - d⟫ = ⟪b', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e5 : ⟪c' - d, b - d⟫ = ⟪c', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e6 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb'rep]; module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e7 : ⟪c' - d, b - d⟫ = ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    have : c' - d = (a - d) + β1 • (b - d) := by rw [hc']; module
    rw [this, inner_add_left, real_inner_smul_left]
  rw [quad_inner_fun] at hrob h2
  exact Tp_depth_sep hα4 hγ4 hαγ hβ1 (by linarith) (by rw [← e4, e6, e1, e2]) (by rw [← e5, e7, e1, e3]) hq hrob h2

/-- `Tp_poked'`: with `QacTop` and `X_2c'` not robust, the poked case is Rupert (no `hnd`, no `R4ppEnd`). -/
theorem Tp_poked' (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : α4 < 1)
    (hq : QacTop a b b' c d)
    (hrob : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫))
    (h2 : ¬ IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  Tp_sep N hT' hb'rep hα (Tp_tie_sep N hT' hb'rep hq hrob h2)

/-- The wrapper in the residual's form: `TpPokedH N` plus the two facts the residual does not carry
(`QacTop` and `¬ robust X_2c'`; both are in the context at the call site, see status.md). -/
theorem Tp_poked_of_H (N : Norm08 a a' b b' c c' d) (h : TpPokedH N) (hq : QacTop a b b' c d)
    (h2 : ¬ IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hT', α4, γ4, hrep, hα, hrob, -⟩ := h
  exact Tp_poked' N hT' hrep hα hq hrob h2

/-- Level face: separation is automatic, so `TpPokedH N` alone closes it. -/
theorem Tp_poked_of_H_level (N : Norm08 a a' b b' c c' d) (h : TpPokedH N)
    (hlev : LevelQac a b c d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hT', α4, γ4, hrep, hα, hrob, -⟩ := h
  obtain ⟨β1, β6, γ6, hne, hc', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ := Tp_frame N hT' hrep
  have hdb : d ≠ b := N.hd.ne.2.2.1
  have hn : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  obtain ⟨l1, l2⟩ := hlev
  have e1 : ⟪a - d, b - d⟫ = ⟪a, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e2 : ⟪c - d, b - d⟫ = ⟪c, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e3 : ⟪b - d, b - d⟫ = ⟪b, b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e4 : ⟪b' - d, b - d⟫ = ⟪b', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e5 : ⟪c' - d, b - d⟫ = ⟪c', b - d⟫ - ⟪d, b - d⟫ := inner_sub_left _ _ _
  have e6 : ⟪b' - d, b - d⟫ = α4 * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    have : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hrep]; module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e7 : ⟪c' - d, b - d⟫ = ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    have : c' - d = (a - d) + β1 • (b - d) := by rw [hc']; module
    rw [this, inner_add_left, real_inner_smul_left]
  refine Tp_sep N hT' hrep hα ?_
  simp only [max_lt_iff, lt_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [mul_pos hβ1 hn]

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.Tp_poked'
#print axioms Minimality.Type08Sp.Tp_poked_of_H
#print axioms Minimality.Type08Sp.Tp_poked_of_H_level
#print axioms Minimality.Tp_sep_core_any
