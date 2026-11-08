module

public import Minimality.Type16SAT.LratPMMP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMMPC0 : List Step := PMMPS0 ++ PMMPS1 ++ PMMPS2 ++ PMMPS3
def PMMPC1 : List Step := PMMPS4 ++ PMMPS5 ++ PMMPS6 ++ PMMPS7
def PMMPC2 : List Step := PMMPS8 ++ PMMPS9
theorem PMMPok0 : chkChunk 15 PMMPCnf ([]) PMMPC0 = true := by decide +kernel
theorem PMMPok1 : chkChunk 15 PMMPCnf (PMMPC0) PMMPC1 = true := by decide +kernel
theorem PMMPok2 : chkChunk 15 PMMPCnf (PMMPC0 ++ PMMPC1) PMMPC2 = true := by decide +kernel
theorem PMMPfinal : OKs 15 PMMPCnf [] [PMMPC0,PMMPC1,PMMPC2] :=
  ⟨PMMPok0, ⟨PMMPok1, ⟨PMMPok2, trivial⟩⟩⟩
theorem PMMPempty : [PMMPC0,PMMPC1,PMMPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMMPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMMPCnf, SatCl ρ c := chunks_sound 15 PMMPCnf _ PMMPfinal PMMPempty
end Minimality.H29.SAT.K29
