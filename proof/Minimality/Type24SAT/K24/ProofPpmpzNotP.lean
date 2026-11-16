module

public import Minimality.Type24SAT.K24.LratPpmpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PpmpzNotPC0 : List Step := PpmpzNotPS0 ++ PpmpzNotPS1 ++ PpmpzNotPS2 ++ PpmpzNotPS3
def PpmpzNotPC1 : List Step := PpmpzNotPS4 ++ PpmpzNotPS5 ++ PpmpzNotPS6 ++ PpmpzNotPS7
def PpmpzNotPC2 : List Step := PpmpzNotPS8 ++ PpmpzNotPS9 ++ PpmpzNotPS10 ++ PpmpzNotPS11
def PpmpzNotPC3 : List Step := PpmpzNotPS12
theorem PpmpzNotPok0 : chkChunk 15 PpmpzNotPCnf ([]) PpmpzNotPC0 = true := by decide +kernel
theorem PpmpzNotPok1 : chkChunk 15 PpmpzNotPCnf (PpmpzNotPC0) PpmpzNotPC1 = true := by decide +kernel
theorem PpmpzNotPok2 : chkChunk 15 PpmpzNotPCnf (PpmpzNotPC0 ++ PpmpzNotPC1) PpmpzNotPC2 = true := by decide +kernel
theorem PpmpzNotPok3 : chkChunk 15 PpmpzNotPCnf (PpmpzNotPC0 ++ PpmpzNotPC1 ++ PpmpzNotPC2) PpmpzNotPC3 = true := by decide +kernel
theorem PpmpzNotPfinal : OKs 15 PpmpzNotPCnf [] [PpmpzNotPC0,PpmpzNotPC1,PpmpzNotPC2,PpmpzNotPC3] :=
  ⟨PpmpzNotPok0, ⟨PpmpzNotPok1, ⟨PpmpzNotPok2, ⟨PpmpzNotPok3, trivial⟩⟩⟩⟩
theorem PpmpzNotPempty : [PpmpzNotPC0,PpmpzNotPC1,PpmpzNotPC2,PpmpzNotPC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpmpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpmpzNotPCnf, SatCl ρ c := chunks_sound 15 PpmpzNotPCnf _ PpmpzNotPfinal PpmpzNotPempty
end Minimality.H24.SAT.Lrat
