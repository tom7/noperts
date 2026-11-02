module

public import Minimality.Type21SilD

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ : ℝ³}

/-- **S0, the silhouette cell** at the view `u₀`.  The cycle `c` (injective, `k ≥ 3`) has, for each
edge `c i → c (i+1)`, an up facet `fA i` and a down facet `fB i` through it (everything else
`≤ 0`, strictly `< 0` at one of the two off the edge) and the depths `⟪x (c i), u₀⟫` are strictly
unimodal: then there is a lex cell at `u₀` (the tilt only breaks depth ties). -/
theorem h21_sil_cell (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (hU : Uni (fun i => ⟪x (c i), u₀⟫)) :
    HasLexCellAt (univ.image x) u₀ := by
  obtain ⟨v, hv⟩ := exists_tilt hx hc
  have hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫) :=
    lexUni_of_uni hU _ (fun i j _ h => by_contra fun hij => hv i j hij h)
  choose μ hμ0 hd using exists_mu hk hx hc D
  rcases sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · exact core_pos hc hk D μ hp hd v hL
  · refine core_pos (c := fun i => c (-i)) (fun i j h => neg_injective (hc h)) hk D.rev
      (fun i => - μ (-i - 1)) (fun i => by linarith [hn (-i - 1)]) ?_ v (Type08Sp.lexUni_neg hL)
    intro i
    have := hd (-i - 1)
    rw [sub_add_cancel] at this
    show x (c (-(i + 1))) - x (c (-i)) = (-μ (-i - 1)) • cross (D.A (-i - 1)) (D.B (-i - 1))
    rw [show -(i + 1) = -i - 1 by ring, neg_smul, ← this]
    abel

theorem h21_sil_isRupert (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (hU : Uni (fun i => ⟪x (c i), u₀⟫)) :
    IsRupert (univ.image x) := by
  have hu : u₀ ≠ 0 := by
    intro h; have := D.up 0; subst h; simp at this
  exact isRupert_of_hasLexCell _ ⟨u₀, hu, h21_sil_cell hk hx hc D hU⟩

end H21
end Minimality
