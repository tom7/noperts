module

public import Minimality.Type24SAT.K24.LratPppppPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PppppPqC0 : List Step := PppppPqS0 ++ PppppPqS1 ++ PppppPqS2 ++ PppppPqS3
def PppppPqC1 : List Step := PppppPqS4 ++ PppppPqS5 ++ PppppPqS6
theorem PppppPqok0 : chkChunk 15 PppppPqCnf ([]) PppppPqC0 = true := by decide +kernel
theorem PppppPqok1 : chkChunk 15 PppppPqCnf (PppppPqC0) PppppPqC1 = true := by decide +kernel
theorem PppppPqfinal : OKs 15 PppppPqCnf [] [PppppPqC0,PppppPqC1] :=
  ⟨PppppPqok0, ⟨PppppPqok1, trivial⟩⟩
theorem PppppPqempty : [PppppPqC0,PppppPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PppppPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PppppPqCnf, SatCl ρ c := chunks_sound 15 PppppPqCnf _ PppppPqfinal PppppPqempty
end Minimality.H24.SAT.K24
