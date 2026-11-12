module

public import Minimality.Type24SAT.K24.LratMpmmmNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpmmmNotPC0 : List Step := MpmmmNotPS0 ++ MpmmmNotPS1 ++ MpmmmNotPS2 ++ MpmmmNotPS3
def MpmmmNotPC1 : List Step := MpmmmNotPS4 ++ MpmmmNotPS5 ++ MpmmmNotPS6 ++ MpmmmNotPS7
def MpmmmNotPC2 : List Step := MpmmmNotPS8 ++ MpmmmNotPS9 ++ MpmmmNotPS10
theorem MpmmmNotPok0 : chkChunk 15 MpmmmNotPCnf ([]) MpmmmNotPC0 = true := by decide +kernel
theorem MpmmmNotPok1 : chkChunk 15 MpmmmNotPCnf (MpmmmNotPC0) MpmmmNotPC1 = true := by decide +kernel
theorem MpmmmNotPok2 : chkChunk 15 MpmmmNotPCnf (MpmmmNotPC0 ++ MpmmmNotPC1) MpmmmNotPC2 = true := by decide +kernel
theorem MpmmmNotPfinal : OKs 15 MpmmmNotPCnf [] [MpmmmNotPC0,MpmmmNotPC1,MpmmmNotPC2] :=
  ⟨MpmmmNotPok0, ⟨MpmmmNotPok1, ⟨MpmmmNotPok2, trivial⟩⟩⟩
theorem MpmmmNotPempty : [MpmmmNotPC0,MpmmmNotPC1,MpmmmNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmmmNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmmmNotPCnf, SatCl ρ c := chunks_sound 15 MpmmmNotPCnf _ MpmmmNotPfinal MpmmmNotPempty
end Minimality.H24.SAT.K24
