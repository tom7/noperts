module

public import Minimality.Type29TSAT.LratB0

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def B0C0 : List Step := B0S0 ++ B0S1 ++ B0S2 ++ B0S3
def B0C1 : List Step := B0S4 ++ B0S5 ++ B0S6 ++ B0S7
def B0C2 : List Step := B0S8 ++ B0S9 ++ B0S10 ++ B0S11
def B0C3 : List Step := B0S12 ++ B0S13 ++ B0S14 ++ B0S15
def B0C4 : List Step := B0S16 ++ B0S17
theorem B0ok0 : chkChunk 15 B0Cnf ([]) B0C0 = true := by decide +kernel
theorem B0ok1 : chkChunk 15 B0Cnf (B0C0) B0C1 = true := by decide +kernel
theorem B0ok2 : chkChunk 15 B0Cnf (B0C0 ++ B0C1) B0C2 = true := by decide +kernel
theorem B0ok3 : chkChunk 15 B0Cnf (B0C0 ++ B0C1 ++ B0C2) B0C3 = true := by decide +kernel
theorem B0ok4 : chkChunk 15 B0Cnf (B0C0 ++ B0C1 ++ B0C2 ++ B0C3) B0C4 = true := by decide +kernel
theorem B0final : OKs 15 B0Cnf [] [B0C0,B0C1,B0C2,B0C3,B0C4] :=
  ⟨B0ok0, ⟨B0ok1, ⟨B0ok2, ⟨B0ok3, ⟨B0ok4, trivial⟩⟩⟩⟩⟩
theorem B0empty : [B0C0,B0C1,B0C2,B0C3,B0C4].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem B0unsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ B0Cnf, SatCl ρ c := chunks_sound 15 B0Cnf _ B0final B0empty
end Minimality.H29.SAT.K29
