module

public import MinimalityExtra
public import Minimality.Stieltjes

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MinimalityExtra

theorem stieltjesDecomposition : StieltjesDecomposition := by
  refine ⟨fun n G hG hoff => ?_, fun n μ ξ lam hμ hξ hlam => ?_⟩
  · exact ⟨Minimality.Stieltjes.stieltjes_inv_nonneg G hG hoff,
      Minimality.Stieltjes.stieltjes_decomp G hG hoff⟩
  · exact Minimality.Stieltjes.posDef_of_stieltjes_sum μ ξ lam hμ hξ hlam

end MinimalityExtra
