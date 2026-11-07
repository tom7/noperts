module

public import Minimality.Type29SAT.LratK4a

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def K4aC0 : List Step := K4aS0 ++ K4aS1 ++ K4aS2 ++ K4aS3
def K4aC1 : List Step := K4aS4 ++ K4aS5 ++ K4aS6 ++ K4aS7
def K4aC2 : List Step := K4aS8 ++ K4aS9 ++ K4aS10 ++ K4aS11
def K4aC3 : List Step := K4aS12
theorem K4aok0 : chkChunk 15 K4aCnf ([]) K4aC0 = true := by decide +kernel
theorem K4aok1 : chkChunk 15 K4aCnf (K4aC0) K4aC1 = true := by decide +kernel
theorem K4aok2 : chkChunk 15 K4aCnf (K4aC0 ++ K4aC1) K4aC2 = true := by decide +kernel
theorem K4aok3 : chkChunk 15 K4aCnf (K4aC0 ++ K4aC1 ++ K4aC2) K4aC3 = true := by decide +kernel
theorem K4afinal : OKs 15 K4aCnf [] [K4aC0,K4aC1,K4aC2,K4aC3] :=
  ⟨K4aok0, ⟨K4aok1, ⟨K4aok2, ⟨K4aok3, trivial⟩⟩⟩⟩
theorem K4aempty : [K4aC0,K4aC1,K4aC2,K4aC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem K4aunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ K4aCnf, SatCl ρ c := chunks_sound 15 K4aCnf _ K4afinal K4aempty
end Minimality.H29.SAT.K29
