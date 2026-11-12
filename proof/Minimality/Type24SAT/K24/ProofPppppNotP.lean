module

public import Minimality.Type24SAT.K24.LratPppppNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PppppNotPC0 : List Step := PppppNotPS0 ++ PppppNotPS1 ++ PppppNotPS2 ++ PppppNotPS3
def PppppNotPC1 : List Step := PppppNotPS4 ++ PppppNotPS5 ++ PppppNotPS6 ++ PppppNotPS7
def PppppNotPC2 : List Step := PppppNotPS8 ++ PppppNotPS9 ++ PppppNotPS10 ++ PppppNotPS11
def PppppNotPC3 : List Step := PppppNotPS12
theorem PppppNotPok0 : chkChunk 15 PppppNotPCnf ([]) PppppNotPC0 = true := by decide +kernel
theorem PppppNotPok1 : chkChunk 15 PppppNotPCnf (PppppNotPC0) PppppNotPC1 = true := by decide +kernel
theorem PppppNotPok2 : chkChunk 15 PppppNotPCnf (PppppNotPC0 ++ PppppNotPC1) PppppNotPC2 = true := by decide +kernel
theorem PppppNotPok3 : chkChunk 15 PppppNotPCnf (PppppNotPC0 ++ PppppNotPC1 ++ PppppNotPC2) PppppNotPC3 = true := by decide +kernel
theorem PppppNotPfinal : OKs 15 PppppNotPCnf [] [PppppNotPC0,PppppNotPC1,PppppNotPC2,PppppNotPC3] :=
  ⟨PppppNotPok0, ⟨PppppNotPok1, ⟨PppppNotPok2, ⟨PppppNotPok3, trivial⟩⟩⟩⟩
theorem PppppNotPempty : [PppppNotPC0,PppppNotPC1,PppppNotPC2,PppppNotPC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PppppNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PppppNotPCnf, SatCl ρ c := chunks_sound 15 PppppNotPCnf _ PppppNotPfinal PppppNotPempty
end Minimality.H24.SAT.K24
