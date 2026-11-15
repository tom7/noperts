module

public import Minimality.Type24SAT.K24.LratPpzpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PpzpzNotPC0 : List Step := PpzpzNotPS0 ++ PpzpzNotPS1 ++ PpzpzNotPS2 ++ PpzpzNotPS3
def PpzpzNotPC1 : List Step := PpzpzNotPS4 ++ PpzpzNotPS5 ++ PpzpzNotPS6 ++ PpzpzNotPS7
def PpzpzNotPC2 : List Step := PpzpzNotPS8 ++ PpzpzNotPS9 ++ PpzpzNotPS10 ++ PpzpzNotPS11
def PpzpzNotPC3 : List Step := PpzpzNotPS12 ++ PpzpzNotPS13 ++ PpzpzNotPS14 ++ PpzpzNotPS15
theorem PpzpzNotPok0 : chkChunk 15 PpzpzNotPCnf ([]) PpzpzNotPC0 = true := by decide +kernel
theorem PpzpzNotPok1 : chkChunk 15 PpzpzNotPCnf (PpzpzNotPC0) PpzpzNotPC1 = true := by decide +kernel
theorem PpzpzNotPok2 : chkChunk 15 PpzpzNotPCnf (PpzpzNotPC0 ++ PpzpzNotPC1) PpzpzNotPC2 = true := by decide +kernel
theorem PpzpzNotPok3 : chkChunk 15 PpzpzNotPCnf (PpzpzNotPC0 ++ PpzpzNotPC1 ++ PpzpzNotPC2) PpzpzNotPC3 = true := by decide +kernel
theorem PpzpzNotPfinal : OKs 15 PpzpzNotPCnf [] [PpzpzNotPC0,PpzpzNotPC1,PpzpzNotPC2,PpzpzNotPC3] :=
  ⟨PpzpzNotPok0, ⟨PpzpzNotPok1, ⟨PpzpzNotPok2, ⟨PpzpzNotPok3, trivial⟩⟩⟩⟩
theorem PpzpzNotPempty : [PpzpzNotPC0,PpzpzNotPC1,PpzpzNotPC2,PpzpzNotPC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpzpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpzpzNotPCnf, SatCl ρ c := chunks_sound 15 PpzpzNotPCnf _ PpzpzNotPfinal PpzpzNotPempty
end Minimality.H24.SAT.K24
