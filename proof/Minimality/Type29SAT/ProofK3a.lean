module

public import Minimality.Type29SAT.LratK3a

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def K3aC0 : List Step := K3aS0 ++ K3aS1 ++ K3aS2 ++ K3aS3
def K3aC1 : List Step := K3aS4 ++ K3aS5 ++ K3aS6 ++ K3aS7
def K3aC2 : List Step := K3aS8 ++ K3aS9 ++ K3aS10 ++ K3aS11
def K3aC3 : List Step := K3aS12 ++ K3aS13 ++ K3aS14 ++ K3aS15
def K3aC4 : List Step := K3aS16 ++ K3aS17 ++ K3aS18 ++ K3aS19
theorem K3aok0 : chkChunk 15 K3aCnf ([]) K3aC0 = true := by decide +kernel
theorem K3aok1 : chkChunk 15 K3aCnf (K3aC0) K3aC1 = true := by decide +kernel
theorem K3aok2 : chkChunk 15 K3aCnf (K3aC0 ++ K3aC1) K3aC2 = true := by decide +kernel
theorem K3aok3 : chkChunk 15 K3aCnf (K3aC0 ++ K3aC1 ++ K3aC2) K3aC3 = true := by decide +kernel
theorem K3aok4 : chkChunk 15 K3aCnf (K3aC0 ++ K3aC1 ++ K3aC2 ++ K3aC3) K3aC4 = true := by decide +kernel
theorem K3afinal : OKs 15 K3aCnf [] [K3aC0,K3aC1,K3aC2,K3aC3,K3aC4] :=
  ⟨K3aok0, ⟨K3aok1, ⟨K3aok2, ⟨K3aok3, ⟨K3aok4, trivial⟩⟩⟩⟩⟩
theorem K3aempty : [K3aC0,K3aC1,K3aC2,K3aC3,K3aC4].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem K3aunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ K3aCnf, SatCl ρ c := chunks_sound 15 K3aCnf _ K3afinal K3aempty
end Minimality.H29.SAT.K29
