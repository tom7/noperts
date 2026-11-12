module

public import Minimality.Type24SAT.K24.LratPmpppNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def PmpppNotPC0 : List Step := PmpppNotPS0 ++ PmpppNotPS1 ++ PmpppNotPS2 ++ PmpppNotPS3
def PmpppNotPC1 : List Step := PmpppNotPS4 ++ PmpppNotPS5 ++ PmpppNotPS6 ++ PmpppNotPS7
def PmpppNotPC2 : List Step := PmpppNotPS8 ++ PmpppNotPS9
theorem PmpppNotPok0 : chkChunk 15 PmpppNotPCnf ([]) PmpppNotPC0 = true := by decide +kernel
theorem PmpppNotPok1 : chkChunk 15 PmpppNotPCnf (PmpppNotPC0) PmpppNotPC1 = true := by decide +kernel
theorem PmpppNotPok2 : chkChunk 15 PmpppNotPCnf (PmpppNotPC0 ++ PmpppNotPC1) PmpppNotPC2 = true := by decide +kernel
theorem PmpppNotPfinal : OKs 15 PmpppNotPCnf [] [PmpppNotPC0,PmpppNotPC1,PmpppNotPC2] :=
  ⟨PmpppNotPok0, ⟨PmpppNotPok1, ⟨PmpppNotPok2, trivial⟩⟩⟩
theorem PmpppNotPempty : [PmpppNotPC0,PmpppNotPC1,PmpppNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PmpppNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PmpppNotPCnf, SatCl ρ c := chunks_sound 15 PmpppNotPCnf _ PmpppNotPfinal PmpppNotPempty
end Minimality.H24.SAT.K24
