module

public import Minimality.Type29TSAT.LratV0

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def V0C0 : List Step := V0S0 ++ V0S1 ++ V0S2 ++ V0S3
def V0C1 : List Step := V0S4 ++ V0S5 ++ V0S6 ++ V0S7
def V0C2 : List Step := V0S8 ++ V0S9 ++ V0S10 ++ V0S11
def V0C3 : List Step := V0S12 ++ V0S13 ++ V0S14 ++ V0S15
def V0C4 : List Step := V0S16 ++ V0S17 ++ V0S18 ++ V0S19
def V0C5 : List Step := V0S20 ++ V0S21
theorem V0ok0 : chkChunk 15 V0Cnf ([]) V0C0 = true := by decide +kernel
theorem V0ok1 : chkChunk 15 V0Cnf (V0C0) V0C1 = true := by decide +kernel
theorem V0ok2 : chkChunk 15 V0Cnf (V0C0 ++ V0C1) V0C2 = true := by decide +kernel
theorem V0ok3 : chkChunk 15 V0Cnf (V0C0 ++ V0C1 ++ V0C2) V0C3 = true := by decide +kernel
theorem V0ok4 : chkChunk 15 V0Cnf (V0C0 ++ V0C1 ++ V0C2 ++ V0C3) V0C4 = true := by decide +kernel
theorem V0ok5 : chkChunk 15 V0Cnf (V0C0 ++ V0C1 ++ V0C2 ++ V0C3 ++ V0C4) V0C5 = true := by decide +kernel
theorem V0final : OKs 15 V0Cnf [] [V0C0,V0C1,V0C2,V0C3,V0C4,V0C5] :=
  ⟨V0ok0, ⟨V0ok1, ⟨V0ok2, ⟨V0ok3, ⟨V0ok4, ⟨V0ok5, trivial⟩⟩⟩⟩⟩⟩
theorem V0empty : [V0C0,V0C1,V0C2,V0C3,V0C4,V0C5].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem V0unsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ V0Cnf, SatCl ρ c := chunks_sound 15 V0Cnf _ V0final V0empty
end Minimality.H29.SAT.K29
