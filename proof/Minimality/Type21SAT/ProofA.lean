module

public import Minimality.Type21SAT.LratAS0
public import Minimality.Type21SAT.LratAS1
public import Minimality.Type21SAT.LratAS2
public import Minimality.Type21SAT.LratAS3
public import Minimality.Type21SAT.LratAS4
public import Minimality.Type21SAT.LratACnf

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H21.SAT.K3
def AC0 : List Step := AS0 ++ AS1 ++ AS2 ++ AS3 ++ AS4 ++ AS5 ++ AS6
def AC1 : List Step := AS7 ++ AS8 ++ AS9 ++ AS10 ++ AS11 ++ AS12 ++ AS13
def AC2 : List Step := AS14 ++ AS15 ++ AS16 ++ AS17 ++ AS18 ++ AS19 ++ AS20
def AC3 : List Step := AS21 ++ AS22 ++ AS23 ++ AS24 ++ AS25 ++ AS26 ++ AS27
def AC4 : List Step := AS28 ++ AS29 ++ AS30 ++ AS31 ++ AS32 ++ AS33 ++ AS34
def AC5 : List Step := AS35 ++ AS36 ++ AS37 ++ AS38 ++ AS39 ++ AS40 ++ AS41
def AC6 : List Step := AS42 ++ AS43 ++ AS44 ++ AS45 ++ AS46 ++ AS47 ++ AS48
def AC7 : List Step := AS49 ++ AS50 ++ AS51 ++ AS52 ++ AS53 ++ AS54 ++ AS55
def AC8 : List Step := AS56 ++ AS57 ++ AS58 ++ AS59 ++ AS60 ++ AS61 ++ AS62
def AC9 : List Step := AS63 ++ AS64 ++ AS65 ++ AS66 ++ AS67 ++ AS68 ++ AS69
def AC10 : List Step := AS70 ++ AS71 ++ AS72 ++ AS73 ++ AS74 ++ AS75 ++ AS76
def AC11 : List Step := AS77 ++ AS78 ++ AS79 ++ AS80 ++ AS81 ++ AS82 ++ AS83
theorem Aok0 : chkChunk 15 ACnf ([]) AC0 = true := by decide +kernel
theorem Aok1 : chkChunk 15 ACnf (AC0) AC1 = true := by decide +kernel
theorem Aok2 : chkChunk 15 ACnf (AC0 ++ AC1) AC2 = true := by decide +kernel
theorem Aok3 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2) AC3 = true := by decide +kernel
theorem Aok4 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3) AC4 = true := by decide +kernel
theorem Aok5 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4) AC5 = true := by decide +kernel
theorem Aok6 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5) AC6 = true := by decide +kernel
theorem Aok7 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5 ++ AC6) AC7 = true := by decide +kernel
theorem Aok8 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5 ++ AC6 ++ AC7) AC8 = true := by decide +kernel
theorem Aok9 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5 ++ AC6 ++ AC7 ++ AC8) AC9 = true := by decide +kernel
theorem Aok10 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5 ++ AC6 ++ AC7 ++ AC8 ++ AC9) AC10 = true := by decide +kernel
theorem Aok11 : chkChunk 15 ACnf (AC0 ++ AC1 ++ AC2 ++ AC3 ++ AC4 ++ AC5 ++ AC6 ++ AC7 ++ AC8 ++ AC9 ++ AC10) AC11 = true := by decide +kernel
theorem Afinal : OKs 15 ACnf [] [AC0,AC1,AC2,AC3,AC4,AC5,AC6,AC7,AC8,AC9,AC10,AC11] :=
  ⟨Aok0, ⟨Aok1, ⟨Aok2, ⟨Aok3, ⟨Aok4, ⟨Aok5, ⟨Aok6, ⟨Aok7, ⟨Aok8, ⟨Aok9, ⟨Aok10, ⟨Aok11, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem Aempty : [AC0,AC1,AC2,AC3,AC4,AC5,AC6,AC7,AC8,AC9,AC10,AC11].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Aunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ACnf, SatCl ρ c := chunks_sound 15 ACnf _ Afinal Aempty
end Minimality.H21.SAT.K3
