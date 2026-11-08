module

public import Minimality.Type16SAT.LratPPMP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PPMPC0 : List Step := PPMPS0 ++ PPMPS1 ++ PPMPS2 ++ PPMPS3
def PPMPC1 : List Step := PPMPS4 ++ PPMPS5 ++ PPMPS6 ++ PPMPS7
def PPMPC2 : List Step := PPMPS8 ++ PPMPS9 ++ PPMPS10
theorem PPMPok0 : chkChunk 15 PPMPCnf ([]) PPMPC0 = true := by decide +kernel
theorem PPMPok1 : chkChunk 15 PPMPCnf (PPMPC0) PPMPC1 = true := by decide +kernel
theorem PPMPok2 : chkChunk 15 PPMPCnf (PPMPC0 ++ PPMPC1) PPMPC2 = true := by decide +kernel
theorem PPMPfinal : OKs 15 PPMPCnf [] [PPMPC0,PPMPC1,PPMPC2] :=
  ⟨PPMPok0, ⟨PPMPok1, ⟨PPMPok2, trivial⟩⟩⟩
theorem PPMPempty : [PPMPC0,PPMPC1,PPMPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PPMPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PPMPCnf, SatCl ρ c := chunks_sound 15 PPMPCnf _ PPMPfinal PPMPempty
end Minimality.H29.SAT.K29
