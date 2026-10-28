module

public import Minimality.Type08S.GT_Wrap27

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 28: `gt_far_N2''`, the far triple tie N2 with no residual (S2 `zv = 0` included)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- **The far triple tie, N2** (`z_w < tie <= z_v`): Rupert, no residual. -/
theorem gt_far_N2'' (N : Norm08 a a' b b' c c' d)
    (hfar : N.F.abc'.f a' < N.F.abc'.f c) (hq₂ : N.F.ab'c'.f a' < N.F.ab'c'.f c)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (hzw0 : ⟪a', c - a'⟫ < ⟪b', c - a'⟫) (hzv0 : ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3, P, hE⟩ :=
    n2_pic N.F N.hd hfar hq₂ htouch hzw0 hzv0
  have Fr := n2_frame N.F
  by_cases hnb : NotBeyondW E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 A 0
  · exact n2_sminus N.F N.hd P hE hnb
  · have hwb : WeakBeyond E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases P.cfg.hzv.lt_or_eq with hz | hz
    · rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
      · exact n2_lt N.F N.hd P hE hz hwb hrb
      · exact n2_eq N.F N.hd P hE hz hwb hrb
      · exact n2_gt N.F N.hd P hE hz hwb hrb
    · rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
      · exact n2_lt0 N.F N.hd P hE hz.symm hwb hrb
      · exact n2_eq0 N.F N.hd P hE hz.symm hwb hrb
      · exact n2_gt0 N.F N.hd P hE hz.symm hwb hrb

end Type08Sp
end Minimality
