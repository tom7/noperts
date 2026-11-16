module

public import Minimality.Type24SAT.K24.LratMpmzmNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def MpmzmNotPC0 : List Step := MpmzmNotPS0 ++ MpmzmNotPS1 ++ MpmzmNotPS2 ++ MpmzmNotPS3
def MpmzmNotPC1 : List Step := MpmzmNotPS4 ++ MpmzmNotPS5 ++ MpmzmNotPS6 ++ MpmzmNotPS7
def MpmzmNotPC2 : List Step := MpmzmNotPS8 ++ MpmzmNotPS9 ++ MpmzmNotPS10
theorem MpmzmNotPok0 : chkChunk 15 MpmzmNotPCnf ([]) MpmzmNotPC0 = true := by decide +kernel
theorem MpmzmNotPok1 : chkChunk 15 MpmzmNotPCnf (MpmzmNotPC0) MpmzmNotPC1 = true := by decide +kernel
theorem MpmzmNotPok2 : chkChunk 15 MpmzmNotPCnf (MpmzmNotPC0 ++ MpmzmNotPC1) MpmzmNotPC2 = true := by decide +kernel
theorem MpmzmNotPfinal : OKs 15 MpmzmNotPCnf [] [MpmzmNotPC0,MpmzmNotPC1,MpmzmNotPC2] :=
  ⟨MpmzmNotPok0, ⟨MpmzmNotPok1, ⟨MpmzmNotPok2, trivial⟩⟩⟩
theorem MpmzmNotPempty : [MpmzmNotPC0,MpmzmNotPC1,MpmzmNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmzmNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmzmNotPCnf, SatCl ρ c := chunks_sound 15 MpmzmNotPCnf _ MpmzmNotPfinal MpmzmNotPempty
end Minimality.H24.SAT.Lrat
