module

public import Minimality.Type16SAT.LratMZMPZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZMPZC0 : List Step := MZMPZS0 ++ MZMPZS1 ++ MZMPZS2 ++ MZMPZS3
def MZMPZC1 : List Step := MZMPZS4 ++ MZMPZS5 ++ MZMPZS6 ++ MZMPZS7
def MZMPZC2 : List Step := MZMPZS8 ++ MZMPZS9 ++ MZMPZS10 ++ MZMPZS11
theorem MZMPZok0 : chkChunk 15 MZMPZCnf ([]) MZMPZC0 = true := by decide +kernel
theorem MZMPZok1 : chkChunk 15 MZMPZCnf (MZMPZC0) MZMPZC1 = true := by decide +kernel
theorem MZMPZok2 : chkChunk 15 MZMPZCnf (MZMPZC0 ++ MZMPZC1) MZMPZC2 = true := by decide +kernel
theorem MZMPZfinal : OKs 15 MZMPZCnf [] [MZMPZC0,MZMPZC1,MZMPZC2] :=
  ⟨MZMPZok0, ⟨MZMPZok1, ⟨MZMPZok2, trivial⟩⟩⟩
theorem MZMPZempty : [MZMPZC0,MZMPZC1,MZMPZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZMPZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZMPZCnf, SatCl ρ c := chunks_sound 15 MZMPZCnf _ MZMPZfinal MZMPZempty
end Minimality.H29.SAT.K29
