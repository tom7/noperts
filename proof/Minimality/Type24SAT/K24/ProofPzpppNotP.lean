module

public import Minimality.Type24SAT.K24.LratPzpppNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PzpppNotPC0 : List Step := PzpppNotPS0 ++ PzpppNotPS1 ++ PzpppNotPS2 ++ PzpppNotPS3
def PzpppNotPC1 : List Step := PzpppNotPS4 ++ PzpppNotPS5 ++ PzpppNotPS6 ++ PzpppNotPS7
def PzpppNotPC2 : List Step := PzpppNotPS8 ++ PzpppNotPS9 ++ PzpppNotPS10
theorem PzpppNotPok0 : chkChunk 15 PzpppNotPCnf ([]) PzpppNotPC0 = true := by decide +kernel
theorem PzpppNotPok1 : chkChunk 15 PzpppNotPCnf (PzpppNotPC0) PzpppNotPC1 = true := by decide +kernel
theorem PzpppNotPok2 : chkChunk 15 PzpppNotPCnf (PzpppNotPC0 ++ PzpppNotPC1) PzpppNotPC2 = true := by decide +kernel
theorem PzpppNotPfinal : OKs 15 PzpppNotPCnf [] [PzpppNotPC0,PzpppNotPC1,PzpppNotPC2] :=
  ⟨PzpppNotPok0, ⟨PzpppNotPok1, ⟨PzpppNotPok2, trivial⟩⟩⟩
theorem PzpppNotPempty : [PzpppNotPC0,PzpppNotPC1,PzpppNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PzpppNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PzpppNotPCnf, SatCl ρ c := chunks_sound 15 PzpppNotPCnf _ PzpppNotPfinal PzpppNotPempty
end Minimality.H24.SAT.K24
