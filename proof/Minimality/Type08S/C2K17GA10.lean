module

public import Minimality.Type08S.C2K17GA9

@[expose] public section


/-!
# K17GA / GA10: S1.2b wrappers (Zdb(ii), both regimes)
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **S1.2b, Tc regime**: Zdb(ii) (`⟪a-d,a-b'⟫ = 0`) with `ζ_{a-c'}(a,d) = ⟪a-d,a-c'⟫ < 0`: cell `(a,d,c,a',c')@a-b'`. -/
theorem k17ga_s12b_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : ⟪a - d, a - c'⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hpl, hE0⟩ :=
    k17ga_tc_coords W h
  have hb61 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (sub_nonneg.2 hh)]
  have hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6) := by
    have : (-γ4 / (α4 - 1)) * (1 - β6) = 1 := by
      have hne : β6 - 1 ≠ 0 := (sub_pos.2 hb61).ne'
      rw [hpl]; field_simp; ring
    have e : (-γ4 / (α4 - 1)) * α1 * (1 - β6) = α1 := by
      calc (-γ4 / (α4 - 1)) * α1 * (1 - β6) = ((-γ4 / (α4 - 1)) * (1 - β6)) * α1 := by ring
        _ = α1 := by rw [this]; ring
    rw [e]; linarith
  exact k17ga_s12b_core hdet hc' hb' ha' hα11 hα41 hβ1 hγ4 hb6 hbc0 hE0 hζ0 hZ hlit

/-- **S1.2b, Ta regime**. -/
theorem k17ga_s12b_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : ⟪a - d, a - c'⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hbc0, hE0⟩ :=
    k17ga_ta_coords W h
  exact k17ga_s12b_core hdet hc' hb' ha' hα11 hα41 (by linarith) hγ4 hb6 hbc0 hE0 hζ0 hZ hlit

end C2
end Type08Sp
end Minimality
