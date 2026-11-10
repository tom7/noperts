module

public import Minimality.Type16SAT.LratPZMPZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMPZC0 : List Step := PZMPZS0 ++ PZMPZS1 ++ PZMPZS2 ++ PZMPZS3
def PZMPZC1 : List Step := PZMPZS4 ++ PZMPZS5 ++ PZMPZS6 ++ PZMPZS7
def PZMPZC2 : List Step := PZMPZS8 ++ PZMPZS9 ++ PZMPZS10
theorem PZMPZok0 : chkChunk 15 PZMPZCnf ([]) PZMPZC0 = true := by decide +kernel
theorem PZMPZok1 : chkChunk 15 PZMPZCnf (PZMPZC0) PZMPZC1 = true := by decide +kernel
theorem PZMPZok2 : chkChunk 15 PZMPZCnf (PZMPZC0 ++ PZMPZC1) PZMPZC2 = true := by decide +kernel
theorem PZMPZfinal : OKs 15 PZMPZCnf [] [PZMPZC0,PZMPZC1,PZMPZC2] :=
  ⟨PZMPZok0, ⟨PZMPZok1, ⟨PZMPZok2, trivial⟩⟩⟩
theorem PZMPZempty : [PZMPZC0,PZMPZC1,PZMPZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMPZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMPZCnf, SatCl ρ c := chunks_sound 15 PZMPZCnf _ PZMPZfinal PZMPZempty
end Minimality.H29.SAT.K29
