module

public import Minimality.Type08S.GT_Wrap16
public import Minimality.Type08S.P2TpSetup
public import Minimality.Type08S.P2J1

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
variable {a a' b b' c c' d : ℝ³}

/-- The two facts of `T'` that `t4_pic_Tp` needs: `c'` and `a` at the same distance from `G`'s plane,
and `γ6 < 1`. -/
theorem Tp_far_hyps (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d) :
    N.F.a'bc.f c' = N.F.a'bc.f a ∧ N.F.abc'.f c < N.F.abc'.f a' := by
  have hTT := norm08_tieTT' N
  obtain ⟨F, hd, G, hκa, hκb, hκc, hU⟩ := N
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  obtain ⟨r, hr⟩ := hT'
  have hfa : F.a'bc.f c' = F.a'bc.f a := by
    have h1 := F.a'bc.hN c' a
    have h2 := F.a'bc.hN b d
    rw [hr, real_inner_smul_right, ← h2, F.a'bc.hQ, hd.a'bc] at h1
    linarith
  have hTne : F.abc'.f a' ≠ F.abc'.f c := by
    intro h
    exact hTT ⟨hd.tieT_geom h, ⟨r, hr⟩⟩
  exact ⟨hfa, type08_T'_far F G hκb hκc hU hfa hTne⟩

end Type08Sp
end Minimality
