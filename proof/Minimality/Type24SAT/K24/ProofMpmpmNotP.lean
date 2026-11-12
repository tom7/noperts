module

public import Minimality.Type24SAT.K24.LratMpmpmNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.H29.SAT.K29
namespace Minimality.H24.SAT.K24
def MpmpmNotPC0 : List Step := MpmpmNotPS0 ++ MpmpmNotPS1 ++ MpmpmNotPS2 ++ MpmpmNotPS3
def MpmpmNotPC1 : List Step := MpmpmNotPS4 ++ MpmpmNotPS5 ++ MpmpmNotPS6 ++ MpmpmNotPS7
def MpmpmNotPC2 : List Step := MpmpmNotPS8 ++ MpmpmNotPS9 ++ MpmpmNotPS10 ++ MpmpmNotPS11
theorem MpmpmNotPok0 : chkChunk 15 MpmpmNotPCnf ([]) MpmpmNotPC0 = true := by decide +kernel
theorem MpmpmNotPok1 : chkChunk 15 MpmpmNotPCnf (MpmpmNotPC0) MpmpmNotPC1 = true := by decide +kernel
theorem MpmpmNotPok2 : chkChunk 15 MpmpmNotPCnf (MpmpmNotPC0 ++ MpmpmNotPC1) MpmpmNotPC2 = true := by decide +kernel
theorem MpmpmNotPfinal : OKs 15 MpmpmNotPCnf [] [MpmpmNotPC0,MpmpmNotPC1,MpmpmNotPC2] :=
  ⟨MpmpmNotPok0, ⟨MpmpmNotPok1, ⟨MpmpmNotPok2, trivial⟩⟩⟩
theorem MpmpmNotPempty : [MpmpmNotPC0,MpmpmNotPC1,MpmpmNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmpmNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmpmNotPCnf, SatCl ρ c := chunks_sound 15 MpmpmNotPCnf _ MpmpmNotPfinal MpmpmNotPempty
end Minimality.H24.SAT.K24
