module

public import Minimality.Type08S.GT_Wrap21

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 22: `gt_far_N2'` with the residual `PicFailN2'` (only `zv = 0`, S2)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- The residual picture failure of the far triple tie, N2: only the S2 position `zv = 0`
(`Q_ac ∥ e`, `c, 2, a` screen-collinear), `r` weakly beyond. -/
def PicFailN2' (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  ∃ (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ) (FH FQab FQac FT1 FT2 FT3 : Fc),
    N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3 ∧
    E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫ ∧
    WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2 ∧ zv = 0

/-- **The far triple tie, N2** (`z_w < tie <= z_v`): Rupert, or the residual `PicFailN2'` (`z_v = 0`). -/
theorem gt_far_N2' (N : Norm08 a a' b b' c c' d)
    (hfar : N.F.abc'.f a' < N.F.abc'.f c) (hq₂ : N.F.ab'c'.f a' < N.F.ab'c'.f c)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (hzw0 : ⟪a', c - a'⟫ < ⟪b', c - a'⟫) (hzv0 : ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ PicFailN2' N.F d := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3, P, hE⟩ :=
    n2_pic N.F N.hd hfar hq₂ htouch hzw0 hzv0
  have Fr := n2_frame N.F
  by_cases hnb : NotBeyondW E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 A 0
  · exact Or.inl (n2_sminus N.F N.hd P hE hnb)
  · have hwb : WeakBeyond E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases P.cfg.hzv.lt_or_eq with hz | hz
    · rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
      · exact Or.inl (n2_lt N.F N.hd P hE hz hwb hrb)
      · exact Or.inl (n2_eq N.F N.hd P hE hz hwb hrb)
      · exact Or.inl (n2_gt N.F N.hd P hE hz hwb hrb)
    · exact Or.inr ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3,
        P, hE, hwb, hz.symm⟩

end Type08Sp
end Minimality
