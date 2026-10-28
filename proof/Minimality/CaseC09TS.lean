module

public import Minimality.CaseC09Special

@[expose] public section

/-!
# Type 09, acute case (c), `t- = s-` with `d+ < a-` (`FEWER-FACES-PROOFS.md` §34.4.2, 09.5, part A)

Theorem 5 with `W` the quad `3456` (27.57) at `t- = s-`: the nine comparisons `t N < M` hold
(`Shape09.tm_N57_lt_M57` takes `t- ≤ s-`), and the quad is then solved by `w1 + w2` just below `M`.
-/

namespace Minimality.CaseC09

open Finset

/-- 09.5, case `d+ < a-`: `Q3456` at `t- = s-`. -/
theorem Shape09.q3456_of_eq (S : Shape09) (hts : S.tm = S.sm) (had : S.dp < S.am) : S.Q3456 := by
  have hkey := S.tm_N57_lt_M57 hts.le had
  have htm := S.tm_pos; have hM := S.M57_pos
  set M := S.M57
  set N := S.N57
  set ε := min (M / 4) ((M - S.tm * N) / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by linarith)
  have hε1 : ε ≤ M / 4 := min_le_left _ _
  have hε2 : ε ≤ (M - S.tm * N) / 2 := min_le_right _ _
  refine ⟨M - 2 * ε, ε, by linarith, hε0, by linarith, ?_⟩
  rw [← hts, ← add_div, lt_div_iff₀ htm]
  nlinarith

/-- **09.5, part A** (`t- = s-`, `d+ < a-`): Theorem 5 with `W = 3456` holds. -/
theorem Frame09.rupert_of_tm_eq_sm_lt {x : Fin 7 → ℝ³} (F : Frame09 x)
    (hx : Function.Injective x) (hA : F.a12 < F.a22) (hts : F.S.tm = F.S.sm)
    (hda : F.S.dp < F.S.am) : IsRupert (Finset.univ.image x) :=
  F.rupert_of_Q3456 hx (F.S.q3456_of_eq hts hda)

end Minimality.CaseC09
