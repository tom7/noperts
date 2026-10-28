module

public import Minimality.Type08S.GT_Wrap8

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 9: `gt_far_N2`, `gt_far_T4` with the explicit residual `PicFail`

`PicFailN2 F d`: the extracted N2 picture (`N2Pic`, all facts of the face lattice) with `r` weakly
beyond and either `zv = 0` (S2: the facet `Q_ac` is parallel to the base view, `a, 2, c` are
collinear on the screen, so the strict hypotheses of `propH_n2_lt/ge` fail) or `b2 <= r2`
(the `hcv` pentagon / special-position cores are not yet derived from the face lattice).
`PicFailT4 F d`: the T4 picture, weakly beyond, with `r2 = b2` (`gt_far_T4` is in `GT_Wrap11`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- The residual picture failures of the far triple tie, N2. -/
def PicFailN2 (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  ∃ (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ) (FH FQab FQac FT1 FT2 FT3 : Fc),
    N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3 ∧
    E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫ ∧
    WeakBeyond E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2 ∧ (zv = 0 ∨ b2 ≤ r2)

/-- The residual picture failures of the far triple tie, T4. -/
def PicFailT4 (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop :=
  ∃ (E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ) (FH FQac FT1 FT2 FT3 FT4 : Fc),
    T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t FH FQac FT1 FT2 FT3 FT4 ∧
    E = ⟪hfE b c (b - d), hfE b c (b - d)⟫ ∧
    WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2 ∧ r2 = b2

/-- **The far triple tie, N2** (`z_w < tie <= z_v`): Rupert, or the residual `PicFailN2`. -/
theorem gt_far_N2 (N : Norm08 a a' b b' c c' d)
    (hfar : N.F.abc'.f a' < N.F.abc'.f c) (hq₂ : N.F.ab'c'.f a' < N.F.ab'c'.f c)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (hzw0 : ⟪a', c - a'⟫ < ⟪b', c - a'⟫) (hzv0 : ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ PicFailN2 N.F d := by
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
    · by_cases hrb : r2 < b2
      · exact Or.inl (n2_lt N.F N.hd P hE hz hwb hrb)
      · exact Or.inr ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3,
          P, hE, hwb, Or.inr (not_lt.mp hrb)⟩
    · exact Or.inr ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3,
        P, hE, hwb, Or.inl hz.symm⟩

end Type08Sp
end Minimality
