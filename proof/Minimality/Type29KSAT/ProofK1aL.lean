module

public import Minimality.Type29KSAT.LratK1aL

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def K1aLC0 : List Step := K1aLS0 ++ K1aLS1 ++ K1aLS2 ++ K1aLS3
def K1aLC1 : List Step := K1aLS4 ++ K1aLS5 ++ K1aLS6 ++ K1aLS7
theorem K1aLok0 : chkChunk 15 K1aLCnf ([]) K1aLC0 = true := by decide +kernel
theorem K1aLok1 : chkChunk 15 K1aLCnf (K1aLC0) K1aLC1 = true := by decide +kernel
theorem K1aLfinal : OKs 15 K1aLCnf [] [K1aLC0,K1aLC1] :=
  ⟨K1aLok0, ⟨K1aLok1, trivial⟩⟩
theorem K1aLempty : [K1aLC0,K1aLC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem K1aLunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ K1aLCnf, SatCl ρ c := chunks_sound 15 K1aLCnf _ K1aLfinal K1aLempty
end Minimality.H29.SAT.K29
