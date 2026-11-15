module

public import Minimality.Type24SAT.K24.LratMpzpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def MpzpzNotPC0 : List Step := MpzpzNotPS0 ++ MpzpzNotPS1 ++ MpzpzNotPS2 ++ MpzpzNotPS3
def MpzpzNotPC1 : List Step := MpzpzNotPS4 ++ MpzpzNotPS5 ++ MpzpzNotPS6 ++ MpzpzNotPS7
def MpzpzNotPC2 : List Step := MpzpzNotPS8 ++ MpzpzNotPS9 ++ MpzpzNotPS10 ++ MpzpzNotPS11
def MpzpzNotPC3 : List Step := MpzpzNotPS12 ++ MpzpzNotPS13 ++ MpzpzNotPS14 ++ MpzpzNotPS15
theorem MpzpzNotPok0 : chkChunk 15 MpzpzNotPCnf ([]) MpzpzNotPC0 = true := by decide +kernel
theorem MpzpzNotPok1 : chkChunk 15 MpzpzNotPCnf (MpzpzNotPC0) MpzpzNotPC1 = true := by decide +kernel
theorem MpzpzNotPok2 : chkChunk 15 MpzpzNotPCnf (MpzpzNotPC0 ++ MpzpzNotPC1) MpzpzNotPC2 = true := by decide +kernel
theorem MpzpzNotPok3 : chkChunk 15 MpzpzNotPCnf (MpzpzNotPC0 ++ MpzpzNotPC1 ++ MpzpzNotPC2) MpzpzNotPC3 = true := by decide +kernel
theorem MpzpzNotPfinal : OKs 15 MpzpzNotPCnf [] [MpzpzNotPC0,MpzpzNotPC1,MpzpzNotPC2,MpzpzNotPC3] :=
  ⟨MpzpzNotPok0, ⟨MpzpzNotPok1, ⟨MpzpzNotPok2, ⟨MpzpzNotPok3, trivial⟩⟩⟩⟩
theorem MpzpzNotPempty : [MpzpzNotPC0,MpzpzNotPC1,MpzpzNotPC2,MpzpzNotPC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpzpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpzpzNotPCnf, SatCl ρ c := chunks_sound 15 MpzpzNotPCnf _ MpzpzNotPfinal MpzpzNotPempty
end Minimality.H24.SAT.K24
