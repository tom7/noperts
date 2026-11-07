module

public import Minimality.Type29KSAT.LratK2

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def K2C0 : List Step := K2S0 ++ K2S1 ++ K2S2 ++ K2S3
def K2C1 : List Step := K2S4 ++ K2S5 ++ K2S6 ++ K2S7
def K2C2 : List Step := K2S8 ++ K2S9 ++ K2S10 ++ K2S11
def K2C3 : List Step := K2S12 ++ K2S13 ++ K2S14 ++ K2S15
def K2C4 : List Step := K2S16 ++ K2S17 ++ K2S18 ++ K2S19
def K2C5 : List Step := K2S20 ++ K2S21 ++ K2S22 ++ K2S23
def K2C6 : List Step := K2S24 ++ K2S25 ++ K2S26 ++ K2S27
def K2C7 : List Step := K2S28 ++ K2S29 ++ K2S30 ++ K2S31
def K2C8 : List Step := K2S32 ++ K2S33 ++ K2S34 ++ K2S35
def K2C9 : List Step := K2S36 ++ K2S37 ++ K2S38 ++ K2S39
def K2C10 : List Step := K2S40 ++ K2S41 ++ K2S42 ++ K2S43
def K2C11 : List Step := K2S44 ++ K2S45 ++ K2S46 ++ K2S47
def K2C12 : List Step := K2S48
theorem K2ok0 : chkChunk 15 K2Cnf ([]) K2C0 = true := by decide +kernel
theorem K2ok1 : chkChunk 15 K2Cnf (K2C0) K2C1 = true := by decide +kernel
theorem K2ok2 : chkChunk 15 K2Cnf (K2C0 ++ K2C1) K2C2 = true := by decide +kernel
theorem K2ok3 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2) K2C3 = true := by decide +kernel
theorem K2ok4 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3) K2C4 = true := by decide +kernel
theorem K2ok5 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4) K2C5 = true := by decide +kernel
theorem K2ok6 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5) K2C6 = true := by decide +kernel
theorem K2ok7 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6) K2C7 = true := by decide +kernel
theorem K2ok8 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6 ++ K2C7) K2C8 = true := by decide +kernel
theorem K2ok9 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6 ++ K2C7 ++ K2C8) K2C9 = true := by decide +kernel
theorem K2ok10 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6 ++ K2C7 ++ K2C8 ++ K2C9) K2C10 = true := by decide +kernel
theorem K2ok11 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6 ++ K2C7 ++ K2C8 ++ K2C9 ++ K2C10) K2C11 = true := by decide +kernel
theorem K2ok12 : chkChunk 15 K2Cnf (K2C0 ++ K2C1 ++ K2C2 ++ K2C3 ++ K2C4 ++ K2C5 ++ K2C6 ++ K2C7 ++ K2C8 ++ K2C9 ++ K2C10 ++ K2C11) K2C12 = true := by decide +kernel
theorem K2final : OKs 15 K2Cnf [] [K2C0,K2C1,K2C2,K2C3,K2C4,K2C5,K2C6,K2C7,K2C8,K2C9,K2C10,K2C11,K2C12] :=
  ⟨K2ok0, ⟨K2ok1, ⟨K2ok2, ⟨K2ok3, ⟨K2ok4, ⟨K2ok5, ⟨K2ok6, ⟨K2ok7, ⟨K2ok8, ⟨K2ok9, ⟨K2ok10, ⟨K2ok11, ⟨K2ok12, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem K2empty : [K2C0,K2C1,K2C2,K2C3,K2C4,K2C5,K2C6,K2C7,K2C8,K2C9,K2C10,K2C11,K2C12].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem K2unsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ K2Cnf, SatCl ρ c := chunks_sound 15 K2Cnf _ K2final K2empty
end Minimality.H29.SAT.K29
