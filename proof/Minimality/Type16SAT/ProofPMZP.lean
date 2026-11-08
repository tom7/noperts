module

public import Minimality.Type16SAT.LratPMZP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMZPC0 : List Step := PMZPS0 ++ PMZPS1 ++ PMZPS2 ++ PMZPS3
def PMZPC1 : List Step := PMZPS4 ++ PMZPS5
theorem PMZPok0 : chkChunk 15 PMZPCnf ([]) PMZPC0 = true := by decide +kernel
theorem PMZPok1 : chkChunk 15 PMZPCnf (PMZPC0) PMZPC1 = true := by decide +kernel
theorem PMZPfinal : OKs 15 PMZPCnf [] [PMZPC0,PMZPC1] :=
  ⟨PMZPok0, ⟨PMZPok1, trivial⟩⟩
theorem PMZPempty : [PMZPC0,PMZPC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMZPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMZPCnf, SatCl ρ c := chunks_sound 15 PMZPCnf _ PMZPfinal PMZPempty
end Minimality.H29.SAT.K29
