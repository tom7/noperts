module

public import Minimality.Type29QPencil

@[expose] public section

/-!
# Type 29: Sub-pencil syzygy and `C_Q5+` ring identities (`A32-REFEREE` specs `S1`, `S3`)

Formalizes in `Minimality.NF29`:
- **`S1`**: `syz_012_14_Q` (`-G4 * v012 + (h2 - h0) * D0 * v14 + P4 * vQ = 0` componentwise) and the six
  ring identities of `A32-REFEREE` §(1), using Carbon's `P4/P5` naming mapped to Lean's `N.P5/N.P4`.
- **`S3`**: `cert_FB_CQ5_pos_eta5_pos` (`C_Q5+` identity for `eta5 > 0` with the A32 referee's
  corrected constant `S^3`), using `B_1^(6)` and `B_2` from `CARBON-A32-1122.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Minimality.NF29

section SubPencil

variable {R : Type*} [CommRing R]

def S_sp (s t : R) : R := s + t - 1
def D0_sp (a0 b0 a2 b2 : R) : R := a0 * b2 - a2 * b0
def G4_sp (b0 h0 b2 h2 : R) : R := b0 * (1 - h2) - b2 * (1 - h0)
def G5_sp (a0 h0 a2 h2 : R) : R := a2 * (1 - h0) - a0 * (1 - h2)
def DG4_sp (a0 b0 h0 a2 b2 h2 : R) : R := D0_sp a0 b0 a2 b2 + G4_sp b0 h0 b2 h2
def DG5_sp (a0 b0 h0 a2 b2 h2 : R) : R := D0_sp a0 b0 a2 b2 + G5_sp a0 h0 a2 h2
def D023_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  D0_sp a0 b0 a2 b2 + s * G4_sp b0 h0 b2 h2 + t * G5_sp a0 h0 a2 h2
def U4_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  D023_sp a0 b0 h0 a2 b2 h2 s t - DG5_sp a0 b0 h0 a2 b2 h2
def U5_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  DG4_sp a0 b0 h0 a2 b2 h2 - D023_sp a0 b0 h0 a2 b2 h2 s t
-- Carbon P4 = Lean N.P5 = b0 * h2 - b2 * h0; Carbon P5 = Lean N.P4 = a2 * h0 - a0 * h2
def P4C_sp (b0 h0 b2 h2 : R) : R := b0 * h2 - b2 * h0
def P5C_sp (a0 h0 a2 h2 : R) : R := a2 * h0 - a0 * h2
def qA4_sp (a2 b2 s t : R) : R := -a2 * (1 - t) - b2 * s
def qA5_sp (a2 b2 s t : R) : R := -a2 * t - b2 * (1 - s)
def D035_sp (a0 b0 h0 s t : R) : R := a0 * (1 - s) + b0 * t - (1 - h0) * t
def D234_sp (a2 b2 h2 s t : R) : R := -a2 * s - b2 * (1 - t) + (1 - h2) * s
def P0_sp (a0 b0 h0 s t : R) : R := b0 * (s - 1) + (1 - a0 - h0) * t
def P2_sp (a2 b2 h2 s t : R) : R := a2 * t - a2 - b2 * s - h2 * s + s

section S1

variable (a0 b0 h0 a2 b2 h2 s t : R)

theorem u4_u5_G4_id :
    t * U4_sp a0 b0 h0 a2 b2 h2 s t - (1 - t) * U5_sp a0 b0 h0 a2 b2 h2 s t =
      S_sp s t * G4_sp b0 h0 b2 h2 := by
  dsimp only [U4_sp, U5_sp, DG4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, S_sp]; ring

theorem u5_u4_G5_id :
    s * U5_sp a0 b0 h0 a2 b2 h2 s t + (s - 1) * U4_sp a0 b0 h0 a2 b2 h2 s t =
      -S_sp s t * G5_sp a0 h0 a2 h2 := by
  dsimp only [U4_sp, U5_sp, DG4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, S_sp]; ring

theorem P4_G5_sub_P5_G4_id :
    P4C_sp b0 h0 b2 h2 * G5_sp a0 h0 a2 h2 - P5C_sp a0 h0 a2 h2 * G4_sp b0 h0 b2 h2 =
      -(h2 - h0) * D0_sp a0 b0 a2 b2 := by
  dsimp only [P4C_sp, P5C_sp, G4_sp, G5_sp, D0_sp]; ring

theorem D035_D234_sub_P0_P2_id :
    D035_sp a0 b0 h0 s t * D234_sp a2 b2 h2 s t -
        P0_sp a0 b0 h0 s t * P2_sp a2 b2 h2 s t =
      -S_sp s t * D023_sp a0 b0 h0 a2 b2 h2 s t := by
  dsimp only [D035_sp, D234_sp, P0_sp, P2_sp, D023_sp, D0_sp, G4_sp, G5_sp, S_sp]; ring

theorem qA5_U4_sub_qA4_U5_id :
    qA5_sp a2 b2 s t * U4_sp a0 b0 h0 a2 b2 h2 s t -
        qA4_sp a2 b2 s t * U5_sp a0 b0 h0 a2 b2 h2 s t =
      -S_sp s t * (h2 - 1) * D0_sp a0 b0 a2 b2 := by
  dsimp only [qA4_sp, qA5_sp, U4_sp, U5_sp, DG4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, S_sp]
  ring

theorem P0_eq_p0_id :
    P0_sp a0 b0 h0 s t = (1 - a0 - b0 - h0) * t + b0 * (s + t - 1) := by
  dsimp only [P0_sp]; ring

theorem P2_eq_p2_id :
    P2_sp a2 b2 h2 s t = a2 * (s + t - 1) + (1 - a2 - b2 - h2) * s := by
  dsimp only [P2_sp]; ring

/-- **S1**: `Identity Syz-012-14-Q` componentwise:
`-G4 * v012 + (h2 - h0) * D0 * v14 + P4 * vQ = 0`. -/
theorem syz_012_14_Q :
    (-G4_sp b0 h0 b2 h2 * ((1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2) +
        (h2 - h0) * D0_sp a0 b0 a2 b2 * (1 - t) +
        P4C_sp b0 h0 b2 h2 * (-U4_sp a0 b0 h0 a2 b2 h2 s t) = 0) ∧
    (-G4_sp b0 h0 b2 h2 * (t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2) +
        (h2 - h0) * D0_sp a0 b0 a2 b2 * t +
        P4C_sp b0 h0 b2 h2 * (-U5_sp a0 b0 h0 a2 b2 h2 s t) = 0) := by
  dsimp only [U4_sp, U5_sp, DG4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, P4C_sp, P5C_sp]
  constructor <;> ring

end S1

section S3

variable (a0 b0 h0 a2 b2 h2 s t G44 G55 g45 : R)

/-- **`S3`**: `Cert-FB-CQ5+` (`eta5 > 0` branch) polynomial identity with the A32 referee's
corrected constant `S^3`. -/
theorem cert_FB_CQ5_pos_eta5_pos :
    let S := S_sp s t
    let D0 := D0_sp a0 b0 a2 b2
    let G4 := G4_sp b0 h0 b2 h2
    let P4 := P4C_sp b0 h0 b2 h2
    let U4 := U4_sp a0 b0 h0 a2 b2 h2 s t
    let U5 := U5_sp a0 b0 h0 a2 b2 h2 s t
    let qA4 := qA4_sp a2 b2 s t
    let qA5 := qA5_sp a2 b2 s t
    let B1_6 := P4 * (-s * U4 * G44 - t * U5 * G55 - (s * U5 + t * U4) * g45)
    let B2_diff := (h2 - h0) * D0 * (qA4 * (1 - t) * G44 + qA5 * t * G55 + (qA4 * t + qA5 * (1 - t)) * g45)
    let Q5_pos := -S * U5 * G55 - S * U4 * g45
    let eta5 := s * U4 * qA5 - (1 - t) * U5 * qA4
    (h2 - h0) * D0 * S * U5 * qA4 * (1 - t) * B1_6 +
      s * P4 * U4 * S * U5 * B2_diff +
      (h2 - h0) * D0 * P4 * t * eta5 * Q5_pos =
      S ^ 3 * s * (h2 - 1) * (h2 - h0) * D0 ^ 2 * P4 * G4 * g45 := by
  intro S D0 G4 P4 U4 U5 qA4 qA5 B1_6 B2_diff Q5_pos eta5
  have hG := u4_u5_G4_id a0 b0 h0 a2 b2 h2 s t
  have hQ := qA5_U4_sub_qA4_U5_id a0 b0 h0 a2 b2 h2 s t
  change t * U4 - (1 - t) * U5 = S * G4 at hG
  change qA5 * U4 - qA4 * U5 = -S * (h2 - 1) * D0 at hQ
  linear_combination
    -((h2 - h0) * D0 * P4 * S * s * g45 * (qA5 * U4 - qA4 * U5)) * hG -
      (h2 - h0) * D0 * P4 * S ^ 2 * s * G4 * g45 * hQ

end S3

end SubPencil

end Minimality.NF29
