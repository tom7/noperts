module

public import Minimality.Type24SAT.K24.LratZpppp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZppppC0 : List Step := ZppppS0 ++ ZppppS1 ++ ZppppS2 ++ ZppppS3
def ZppppC1 : List Step := ZppppS4 ++ ZppppS5 ++ ZppppS6 ++ ZppppS7
def ZppppC2 : List Step := ZppppS8 ++ ZppppS9
theorem Zppppok0 : chkChunk 15 ZppppCnf ([]) ZppppC0 = true := by decide +kernel
theorem Zppppok1 : chkChunk 15 ZppppCnf (ZppppC0) ZppppC1 = true := by decide +kernel
theorem Zppppok2 : chkChunk 15 ZppppCnf (ZppppC0 ++ ZppppC1) ZppppC2 = true := by decide +kernel
theorem Zppppfinal : OKs 15 ZppppCnf [] [ZppppC0,ZppppC1,ZppppC2] :=
  ⟨Zppppok0, ⟨Zppppok1, ⟨Zppppok2, trivial⟩⟩⟩
theorem Zppppempty : [ZppppC0,ZppppC1,ZppppC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zppppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZppppCnf, SatCl ρ c := chunks_sound 15 ZppppCnf _ Zppppfinal Zppppempty
end Minimality.H24.SAT.Lrat
