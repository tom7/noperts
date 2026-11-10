module

public import Minimality.Type16SAT.LratMZMMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZMMUC0 : List Step := MZMMUS0 ++ MZMMUS1 ++ MZMMUS2 ++ MZMMUS3
def MZMMUC1 : List Step := MZMMUS4 ++ MZMMUS5 ++ MZMMUS6 ++ MZMMUS7
def MZMMUC2 : List Step := MZMMUS8 ++ MZMMUS9 ++ MZMMUS10
theorem MZMMUok0 : chkChunk 15 MZMMUCnf ([]) MZMMUC0 = true := by decide +kernel
theorem MZMMUok1 : chkChunk 15 MZMMUCnf (MZMMUC0) MZMMUC1 = true := by decide +kernel
theorem MZMMUok2 : chkChunk 15 MZMMUCnf (MZMMUC0 ++ MZMMUC1) MZMMUC2 = true := by decide +kernel
theorem MZMMUfinal : OKs 15 MZMMUCnf [] [MZMMUC0,MZMMUC1,MZMMUC2] :=
  ⟨MZMMUok0, ⟨MZMMUok1, ⟨MZMMUok2, trivial⟩⟩⟩
theorem MZMMUempty : [MZMMUC0,MZMMUC1,MZMMUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZMMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZMMUCnf, SatCl ρ c := chunks_sound 15 MZMMUCnf _ MZMMUfinal MZMMUempty
end Minimality.H29.SAT.K29
