module

public import Minimality.Type24SAT.K24.LratMpmpzDw

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def MpmpzDwC0 : List Step := MpmpzDwS0 ++ MpmpzDwS1 ++ MpmpzDwS2 ++ MpmpzDwS3
def MpmpzDwC1 : List Step := MpmpzDwS4 ++ MpmpzDwS5 ++ MpmpzDwS6 ++ MpmpzDwS7
def MpmpzDwC2 : List Step := MpmpzDwS8 ++ MpmpzDwS9 ++ MpmpzDwS10
theorem MpmpzDwok0 : chkChunk 15 MpmpzDwCnf ([]) MpmpzDwC0 = true := by decide +kernel
theorem MpmpzDwok1 : chkChunk 15 MpmpzDwCnf (MpmpzDwC0) MpmpzDwC1 = true := by decide +kernel
theorem MpmpzDwok2 : chkChunk 15 MpmpzDwCnf (MpmpzDwC0 ++ MpmpzDwC1) MpmpzDwC2 = true := by decide +kernel
theorem MpmpzDwfinal : OKs 15 MpmpzDwCnf [] [MpmpzDwC0,MpmpzDwC1,MpmpzDwC2] :=
  ⟨MpmpzDwok0, ⟨MpmpzDwok1, ⟨MpmpzDwok2, trivial⟩⟩⟩
theorem MpmpzDwempty : [MpmpzDwC0,MpmpzDwC1,MpmpzDwC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmpzDwunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmpzDwCnf, SatCl ρ c := chunks_sound 15 MpmpzDwCnf _ MpmpzDwfinal MpmpzDwempty
end Minimality.H24.SAT.K24
