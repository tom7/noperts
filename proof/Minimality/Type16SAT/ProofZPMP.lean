module

public import Minimality.Type16SAT.LratZPMP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZPMPC0 : List Step := ZPMPS0 ++ ZPMPS1 ++ ZPMPS2 ++ ZPMPS3
def ZPMPC1 : List Step := ZPMPS4 ++ ZPMPS5 ++ ZPMPS6 ++ ZPMPS7
theorem ZPMPok0 : chkChunk 15 ZPMPCnf ([]) ZPMPC0 = true := by decide +kernel
theorem ZPMPok1 : chkChunk 15 ZPMPCnf (ZPMPC0) ZPMPC1 = true := by decide +kernel
theorem ZPMPfinal : OKs 15 ZPMPCnf [] [ZPMPC0,ZPMPC1] :=
  ⟨ZPMPok0, ⟨ZPMPok1, trivial⟩⟩
theorem ZPMPempty : [ZPMPC0,ZPMPC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZPMPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZPMPCnf, SatCl ρ c := chunks_sound 15 ZPMPCnf _ ZPMPfinal ZPMPempty
end Minimality.H29.SAT.K29
