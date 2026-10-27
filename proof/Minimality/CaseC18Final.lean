module

public import Minimality.CaseC18Vertex
public import Minimality.CaseC18Reduce

@[expose] public section

/-!
# Type 18, acute case (c): Theorem 27.59 in the frame, off the special positions
(`FEWER-FACES-PROOFS.md` §27, continued (4))

`CaseC18Special x`: the special positions of the proof.  Off them, a type-18 frame
(`Frame18 x`, from `TriGenPar ∧ ¬TriGenTieO`) is Rupert at its own metric:
`Frame18.isRupert_of_not_special`.

* edge crossings `B`, `B^Z` (27.32), 27.31, the families `A`, `A^Z` (27.27) and Theorem 5 with
  `W = F2` (27.17) are used as in `rupert_or_V` (the equalities `a∓ = b±`, `a± = c±` and the right
  angles are excluded);
* the vertex crossings `V`, `V^Z` (27.51) close the rest at their own views
  (`Frame18.Vside`; `T_A` is the pair partner of `V` with 4-corner rim): the border
  `D2 = 0` (27.42 (i)), `φ(m1∓) = 0` (the far-end switch, 27.42 (ii)) and a horizontal double
  normal of `V` at its view are excluded (the paper's 27.41 removes the last; it is a special
  position here).  Three equal depths of `V`'s triangle rim are not special: a level triangle
  always has a horizontal double normal (`hasHorizontalDoubleNormal_of_level_triangle`).
-/

namespace Minimality.CaseC18

open Finset
open scoped RealInnerProductSpace

/-- **The special positions of type 18's acute case (c)** (on `x`, for some frame): the strict
inequalities of the proof of `Frame18.isRupert_of_not_special` become equalities, or `V`/`V^Z`
has a horizontal double normal at its view. -/
def CaseC18Special (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame18 x, F.a12 = F.a11 ∨ F.a12 = F.a22 ∨ F.S.am = F.S.bp ∨ F.S.ap = F.S.bm ∨
    F.S.ap = F.S.cp ∨ F.S.am = F.S.cm ∨ F.S.dp = F.S.A1 * F.S.tp ∨ F.S.dm = F.S.A1 * F.S.tm ∨
    F.S.D2p = 0 ∨
    ¬ NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.uV) ∨
    ¬ NoHDNAt (Finset.univ.image (x ∘ zperm)) (F.zFrame.toFrame7.fvC F.zFrame.S.uV)

namespace Frame18
variable {x : Fin 7 → ℝ³}

/-- **Off the special positions, a type-18 frame (acute case (c)) is Rupert.** -/
theorem isRupert_of_not_special (F : Frame18 x) (hx : Function.Injective x) (h : ¬ CaseC18Special x) :
    IsRupert (Finset.univ.image x) := by
  have hF : ¬ (F.a12 = F.a11 ∨ F.a12 = F.a22 ∨ F.S.am = F.S.bp ∨ F.S.ap = F.S.bm ∨
      F.S.ap = F.S.cp ∨ F.S.am = F.S.cm ∨ F.S.dp = F.S.A1 * F.S.tp ∨
      F.S.dm = F.S.A1 * F.S.tm ∨ F.S.D2p = 0 ∨
      ¬ NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.uV) ∨
      ¬ NoHDNAt (Finset.univ.image (x ∘ zperm)) (F.zFrame.toFrame7.fvC F.zFrame.S.uV)) :=
    fun h' => h ⟨F, h'⟩
  simp only [not_or, not_not] at hF
  obtain ⟨nα, nβ, n1, n2, n3, n4, nVp, nVm, nD, hnd, hndZ⟩ := hF
  have hα : F.a12 < F.a11 := lt_of_le_of_ne F.A12_le_A11 nα
  have hβ : F.a12 < F.a22 := lt_of_le_of_ne F.A12_le_A22 nβ
  rcases F.rupert_or_V hx hα hβ n1 n2 n3 n4 with h | ⟨h1, h2, hV⟩
  · exact h
  rcases hV with hV | hV
  · exact F.Vside hx (lt_of_le_of_ne hV nVp) h1 h2 nD hnd
  · apply rupert_of_z
    have hxz : Function.Injective (x ∘ zperm) := hx.comp zperm_bijective.1
    refine F.zFrame.Vside hxz ?_ h2 h1 ?_ hndZ
    · have : F.zFrame.S.dp = F.S.dm := rfl
      have hA : F.zFrame.S.A1 = F.S.A1 := by
        show F.S.am + F.S.ap = F.S.ap + F.S.am
        ring
      show F.S.dm < F.zFrame.S.A1 * F.S.tm
      rw [hA]
      exact lt_of_le_of_ne hV nVm
    · intro h0
      apply nD
      have e : F.zFrame.S = F.S.swap := rfl
      rw [e] at h0
      simp only [Shape18.D2p, Shape18.swap] at h0 ⊢
      linarith

end Frame18

end Minimality.CaseC18

end
