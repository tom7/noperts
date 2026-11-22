module

public import Minimality.Type29QPencil
public import Minimality.Type29Exact

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
def D035_sp (a0 b0 h0 s t : R) : R := -((b0 - 1 + h0) * s - a0 * t + a0)
def D234_sp (a2 b2 h2 s t : R) : R := b2 * s + (1 - h2 - a2) * t - b2
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

/-! ### `S2`: `C_Q1 × W14 × F-B` certificate on `G*`

Reference point: all depths are relative to `x 6`, using the `q`-table
`(S q_i, Y_i)` (`i = 0..6`):
- `i = 0`: `(D035, P0, h0)`
- `i = 1`: `(s, t, 0)`
- `i = 2`: `(P2, D234, h2)`
- `i = 3`: `(0, 0, 1)`
- `i = 4`: `(S, 0, 0)`
- `i = 5`: `(0, S, 0)`
- `i = 6`: `(0, 0, 0)`

For `v = v4 • (x 4 - x 6) + v5 • (x 5 - x 6)` in plane `Q`,
`Row_sp (q4_i - q4_j) (q5_i - q5_j) (Y_i - Y_j) v4 v5 G44 G55 g45 g34 g35 S = S * ⟪x i - x j, v⟫`.
(`del12 < 0` occurs on 0 of the 310 data shapes in `A32-REFEREE`, so `cert_FB_CQ1_lt`
is included for completeness of the general algebraic statement.) -/

section S2

variable {R : Type*} [CommRing R]

def Row_sp (dq4 dq5 dY v4 v5 G44 G55 g45 g34 g35 S : R) : R :=
  dq4 * v4 * G44 + dq5 * v5 * G55 + (dq4 * v5 + dq5 * v4) * g45 +
    S * dY * (v4 * g34 + v5 * g35)

def del12_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  (h2 - h0) * D0_sp a0 b0 a2 b2 * qA4_sp a2 b2 s t -
    (h2 - 1) * P4C_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t

set_option maxHeartbeats 400000 in
/-- **`S2` (`del12 ≥ 0`)**: `C_Q1 × W14 × F-B` polynomial identity. -/
theorem cert_FB_CQ1_ge (a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : R) :
    let S := S_sp s t
    let D0 := D0_sp a0 b0 a2 b2
    let G4 := G4_sp b0 h0 b2 h2
    let P4 := P4C_sp b0 h0 b2 h2
    let P5 := P5C_sp a0 h0 a2 h2
    let U4 := U4_sp a0 b0 h0 a2 b2 h2 s t
    let U5 := U5_sp a0 b0 h0 a2 b2 h2 s t
    let qA4 := qA4_sp a2 b2 s t
    let P2 := P2_sp a2 b2 h2 s t
    let D234 := D234_sp a2 b2 h2 s t
    let R24 := Row_sp (P2 - S) D234 h2 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let Q5n := Row_sp 0 (-S) 0 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let R21 := Row_sp (P2 - s) (D234 - t) h2 (1 - t) t G44 G55 g45 g34 g35 S
    let R23 := Row_sp P2 D234 (h2 - 1) (1 - t) t G44 G55 g45 g34 g35 S
    let R12 := Row_sp (s - P2) (t - D234) (-h2) ((1 - t) * P5 - s * P4)
      (t * P5 + (s - 1) * P4) G44 G55 g45 g34 g35 S
    let del12 := del12_sp a0 b0 h0 a2 b2 h2 s t
    P4 * U4 * qA4 * R24 + (h2 - 1) * D0 * P4 * (1 - t) * Q5n +
      U4 * del12 * R21 + h2 * P4 * U4 ^ 2 * R23 + G4 * U4 * qA4 * R12 =
      -S ^ 2 * (h2 - 1) * D0 * P4 * G4 * G55 := by
  intro S D0 G4 P4 P5 U4 U5 qA4 P2 D234 R24 Q5n R21 R23 R12 del12
  have cG44 : P4 * U4 * qA4 * ((P2 - S) * (-U4)) + U4 * del12 * ((P2 - s) * (1 - t)) +
      h2 * P4 * U4 ^ 2 * (P2 * (1 - t)) +
      G4 * U4 * qA4 * ((s - P2) * ((1 - t) * P5 - s * P4)) = 0 := by
    dsimp only [S, D0, G4, P4, P5, U4, qA4, P2, del12, del12_sp, S_sp, D0_sp, G4_sp, G5_sp,
      DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, qA4_sp, P2_sp]; ring
  have cG55 : P4 * U4 * qA4 * (D234 * (-U5)) + (h2 - 1) * D0 * P4 * (1 - t) * ((-S) * (-U5)) +
      U4 * del12 * ((D234 - t) * t) + h2 * P4 * U4 ^ 2 * (D234 * t) +
      G4 * U4 * qA4 * ((t - D234) * (t * P5 + (s - 1) * P4)) =
      -S ^ 2 * (h2 - 1) * D0 * P4 * G4 := by
    dsimp only [S, D0, G4, P4, P5, U4, U5, qA4, D234, del12, del12_sp, S_sp, D0_sp, G4_sp, G5_sp,
      DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, qA4_sp, D234_sp]; ring
  have cg45 : P4 * U4 * qA4 * ((P2 - S) * (-U5) + D234 * (-U4)) +
      (h2 - 1) * D0 * P4 * (1 - t) * ((-S) * (-U4)) +
      U4 * del12 * ((P2 - s) * t + (D234 - t) * (1 - t)) +
      h2 * P4 * U4 ^ 2 * (P2 * t + D234 * (1 - t)) +
      G4 * U4 * qA4 * ((s - P2) * (t * P5 + (s - 1) * P4) +
        (t - D234) * ((1 - t) * P5 - s * P4)) = 0 := by
    dsimp only [S, D0, G4, P4, P5, U4, U5, qA4, P2, D234, del12, del12_sp, S_sp, D0_sp, G4_sp,
      G5_sp, DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, qA4_sp, P2_sp, D234_sp]; ring
  have cg34 : P4 * U4 * qA4 * (S * h2 * (-U4)) + U4 * del12 * (S * h2 * (1 - t)) +
      h2 * P4 * U4 ^ 2 * (S * (h2 - 1) * (1 - t)) +
      G4 * U4 * qA4 * (S * (-h2) * ((1 - t) * P5 - s * P4)) = 0 := by
    dsimp only [S, D0, G4, P4, P5, U4, qA4, del12, del12_sp, S_sp, D0_sp, G4_sp, G5_sp,
      DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, qA4_sp]; ring
  have cg35 : P4 * U4 * qA4 * (S * h2 * (-U5)) + U4 * del12 * (S * h2 * t) +
      h2 * P4 * U4 ^ 2 * (S * (h2 - 1) * t) +
      G4 * U4 * qA4 * (S * (-h2) * (t * P5 + (s - 1) * P4)) = 0 := by
    dsimp only [S, D0, G4, P4, P5, U4, U5, qA4, del12, del12_sp, S_sp, D0_sp, G4_sp, G5_sp,
      DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, qA4_sp]; ring
  dsimp only [R24, Q5n, R21, R23, R12, Row_sp]
  linear_combination G44 * cG44 + G55 * cG55 + g45 * cg45 + g34 * cg34 + g35 * cg35

/-- **`S2` (`del12 < 0` variant)**: eliminates `R21` via `S B1 = -P4 [(1 - t) Q4n + t Q5n]`,
with `m = -U4 * del12` and `K = S * (h2 - h0) * D0`. -/
theorem cert_FB_CQ1_lt (a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : R) :
    let S := S_sp s t
    let D0 := D0_sp a0 b0 a2 b2
    let G4 := G4_sp b0 h0 b2 h2
    let P4 := P4C_sp b0 h0 b2 h2
    let P5 := P5C_sp a0 h0 a2 h2
    let U4 := U4_sp a0 b0 h0 a2 b2 h2 s t
    let U5 := U5_sp a0 b0 h0 a2 b2 h2 s t
    let qA4 := qA4_sp a2 b2 s t
    let P2 := P2_sp a2 b2 h2 s t
    let D234 := D234_sp a2 b2 h2 s t
    let R24 := Row_sp (P2 - S) D234 h2 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let Q4n := Row_sp (-S) 0 0 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let Q5n := Row_sp 0 (-S) 0 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let R23 := Row_sp P2 D234 (h2 - 1) (1 - t) t G44 G55 g45 g34 g35 S
    let R12 := Row_sp (s - P2) (t - D234) (-h2) ((1 - t) * P5 - s * P4)
      (t * P5 + (s - 1) * P4) G44 G55 g45 g34 g35 S
    let del12 := del12_sp a0 b0 h0 a2 b2 h2 s t
    let m := -U4 * del12
    let K := S * (h2 - h0) * D0
    (K * P4 * U4 * qA4 + S * P4 * m) * R24 +
      (m * P4 * (1 - t)) * Q4n +
      (K * (h2 - 1) * D0 * P4 * (1 - t) + m * P4 * t) * Q5n +
      (K * h2 * P4 * U4 ^ 2) * R23 +
      (K * G4 * U4 * qA4 + S * G4 * m) * R12 =
      -K * S ^ 2 * (h2 - 1) * D0 * P4 * G4 * G55 := by
  intro S D0 G4 P4 P5 U4 U5 qA4 P2 D234 R24 Q4n Q5n R23 R12 del12 m K
  let R21 := Row_sp (P2 - s) (D234 - t) h2 (1 - t) t G44 G55 g45 g34 g35 S
  have hge := cert_FB_CQ1_ge a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35
  have hB1 : S * P4 * R24 + P4 * (1 - t) * Q4n + P4 * t * Q5n + S * G4 * R12 + K * R21 = 0 := by
    have bG44 : S * P4 * ((P2 - S) * (-U4)) + P4 * (1 - t) * ((-S) * (-U4)) +
        S * G4 * ((s - P2) * ((1 - t) * P5 - s * P4)) + K * ((P2 - s) * (1 - t)) = 0 := by
      dsimp only [S, K, D0, G4, P4, P5, U4, P2, S_sp, D0_sp, G4_sp, G5_sp, DG5_sp, D023_sp,
        P4C_sp, P5C_sp, U4_sp, P2_sp]; ring
    have bG55 : S * P4 * (D234 * (-U5)) + P4 * t * ((-S) * (-U5)) +
        S * G4 * ((t - D234) * (t * P5 + (s - 1) * P4)) + K * ((D234 - t) * t) = 0 := by
      dsimp only [S, K, D0, G4, P4, P5, U5, D234, S_sp, D0_sp, G4_sp, G5_sp, DG4_sp, DG5_sp,
        D023_sp, P4C_sp, P5C_sp, U5_sp, D234_sp]; ring
    have bg45 : S * P4 * ((P2 - S) * (-U5) + D234 * (-U4)) + P4 * (1 - t) * ((-S) * (-U5)) +
        P4 * t * ((-S) * (-U4)) +
        S * G4 * ((s - P2) * (t * P5 + (s - 1) * P4) + (t - D234) * ((1 - t) * P5 - s * P4)) +
        K * ((P2 - s) * t + (D234 - t) * (1 - t)) = 0 := by
      dsimp only [S, K, D0, G4, P4, P5, U4, U5, P2, D234, S_sp, D0_sp, G4_sp, G5_sp, DG4_sp,
        DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, P2_sp, D234_sp]; ring
    have bg34 : S * P4 * (S * h2 * (-U4)) + S * G4 * (S * (-h2) * ((1 - t) * P5 - s * P4)) +
        K * (S * h2 * (1 - t)) = 0 := by
      dsimp only [S, K, D0, G4, P4, P5, U4, S_sp, D0_sp, G4_sp, G5_sp, DG5_sp, D023_sp,
        P4C_sp, P5C_sp, U4_sp]; ring
    have bg35 : S * P4 * (S * h2 * (-U5)) + S * G4 * (S * (-h2) * (t * P5 + (s - 1) * P4)) +
        K * (S * h2 * t) = 0 := by
      dsimp only [S, K, D0, G4, P4, P5, U5, S_sp, D0_sp, G4_sp, G5_sp, DG4_sp, DG5_sp, D023_sp,
        P4C_sp, P5C_sp, U5_sp]; ring
    dsimp only [R24, Q4n, Q5n, R12, R21, Row_sp]
    linear_combination G44 * bG44 + G55 * bG55 + g45 * bg45 + g34 * bg34 + g35 * bg35
  linear_combination K * hge + m * hB1

end S2

section S2Close

/-- **`S2` closing `Prop` (`del12 ≥ 0`)** on `G*`. -/
theorem cert_FB_CQ1_ge_false
    {a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : ℝ}
    (hh2 : 1 < h2) (_ht0 : 0 < t) (ht1 : t < 1)
    (hU4 : 0 < U4_sp a0 b0 h0 a2 b2 h2 s t)
    (hG4 : 0 < G4_sp b0 h0 b2 h2)
    (hqA4 : 0 < qA4_sp a2 b2 s t)
    (hD0 : 0 < D0_sp a0 b0 a2 b2)
    (hP4 : 0 < P4C_sp b0 h0 b2 h2)
    (hS : 0 < S_sp s t) (hG55 : 0 < G55)
    (hdel : 0 ≤ del12_sp a0 b0 h0 a2 b2 h2 s t)
    (hR24 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - S_sp s t) (D234_sp a2 b2 h2 s t) h2
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ5n : 0 ≤ Row_sp 0 (-S_sp s t) 0
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hR21 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) h2
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hR23 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) (h2 - 1)
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hR12 : 0 ≤ Row_sp (s - P2_sp a2 b2 h2 s t) (t - D234_sp a2 b2 h2 s t) (-h2)
      ((1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2)
      (t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2) G44 G55 g45 g34 g35 (S_sp s t)) :
    False := by
  have hid := cert_FB_CQ1_ge a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35
  dsimp only at hid
  have c1 : 0 ≤ P4C_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t * qA4_sp a2 b2 s t :=
    by positivity
  have c2 : 0 ≤ (h2 - 1) * D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 * (1 - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hh2.le) hD0.le) hP4.le) (sub_nonneg.mpr ht1.le)
  have c3 : 0 ≤ U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t :=
    mul_nonneg hU4.le hdel
  have c4 : 0 ≤ h2 * P4C_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t ^ 2 := by positivity
  have c5 : 0 ≤ G4_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t * qA4_sp a2 b2 s t :=
    by positivity
  have hrhs : -(S_sp s t ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 *
      G4_sp b0 h0 b2 h2 * G55) < 0 := by
    have hp : 0 < S_sp s t ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 *
        G4_sp b0 h0 b2 h2 * G55 :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (sq_pos_of_pos hS) (sub_pos.mpr hh2)) hD0) hP4) hG4) hG55
    linarith
  have h1 := mul_nonneg c1 hR24
  have h2' := mul_nonneg c2 hQ5n
  have h3 := mul_nonneg c3 hR21
  have h4 := mul_nonneg c4 hR23
  have h5 := mul_nonneg c5 hR12
  linarith

/-- **`S2` closing `Prop` (`del12 < 0`)** on `G*`. -/
theorem cert_FB_CQ1_lt_false
    {a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : ℝ}
    (hh2 : 1 < h2) (hh0 : h0 < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hU4 : 0 < U4_sp a0 b0 h0 a2 b2 h2 s t)
    (hG4 : 0 < G4_sp b0 h0 b2 h2)
    (hqA4 : 0 < qA4_sp a2 b2 s t)
    (hD0 : 0 < D0_sp a0 b0 a2 b2)
    (hP4 : 0 < P4C_sp b0 h0 b2 h2)
    (hS : 0 < S_sp s t) (hG55 : 0 < G55)
    (hdel : del12_sp a0 b0 h0 a2 b2 h2 s t < 0)
    (hR24 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - S_sp s t) (D234_sp a2 b2 h2 s t) h2
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ4n : 0 ≤ Row_sp (-S_sp s t) 0 0
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ5n : 0 ≤ Row_sp 0 (-S_sp s t) 0
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hR23 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) (h2 - 1)
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hR12 : 0 ≤ Row_sp (s - P2_sp a2 b2 h2 s t) (t - D234_sp a2 b2 h2 s t) (-h2)
      ((1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2)
      (t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2) G44 G55 g45 g34 g35 (S_sp s t)) :
    False := by
  have hid := cert_FB_CQ1_lt a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35
  dsimp only at hid
  have hm : 0 < -U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t := by
    nlinarith
  have hh20 : 0 < h2 - h0 := by linarith
  have hh21 : 0 < h2 - 1 := by linarith
  have ht1' : 0 < 1 - t := by linarith
  have hK : 0 < S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 := by positivity
  have c1 : 0 ≤ S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 *
      U4_sp a0 b0 h0 a2 b2 h2 s t * qA4_sp a2 b2 s t +
      S_sp s t * P4C_sp b0 h0 b2 h2 * (-U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t) := by
    positivity
  have c2 : 0 ≤ -U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t *
      P4C_sp b0 h0 b2 h2 * (1 - t) := by
    positivity
  have c3 : 0 ≤ S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 * (h2 - 1) * D0_sp a0 b0 a2 b2 *
      P4C_sp b0 h0 b2 h2 * (1 - t) +
      -U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t * P4C_sp b0 h0 b2 h2 * t := by
    positivity
  have c4 : 0 ≤ S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 * h2 * P4C_sp b0 h0 b2 h2 *
      U4_sp a0 b0 h0 a2 b2 h2 s t ^ 2 := by
    positivity
  have c5 : 0 ≤ S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 * G4_sp b0 h0 b2 h2 *
      U4_sp a0 b0 h0 a2 b2 h2 s t * qA4_sp a2 b2 s t +
      S_sp s t * G4_sp b0 h0 b2 h2 * (-U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t) := by
    positivity
  have hrhs : -(S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2 * S_sp s t ^ 2 * (h2 - 1) *
      D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 * G4_sp b0 h0 b2 h2 * G55) < 0 := by
    have hp : 0 < (S_sp s t * (h2 - h0) * D0_sp a0 b0 a2 b2) * S_sp s t ^ 2 * (h2 - 1) *
        D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2 * G4_sp b0 h0 b2 h2 * G55 :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hK (sq_pos_of_pos hS))
        (sub_pos.mpr hh2)) hD0) hP4) hG4) hG55
    linarith
  have h1 := mul_nonneg c1 hR24
  have h2' := mul_nonneg c2 hQ4n
  have h3 := mul_nonneg c3 hQ5n
  have h4 := mul_nonneg c4 hR23
  have h5 := mul_nonneg c5 hR12
  linarith

/-- **`S2` combined closing `Prop`** on `G*` for both signs of `del12`. -/
theorem cert_FB_CQ1_false
    {a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : ℝ}
    (hh2 : 1 < h2) (hh0 : h0 < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hU4 : 0 < U4_sp a0 b0 h0 a2 b2 h2 s t)
    (_hU5 : 0 < U5_sp a0 b0 h0 a2 b2 h2 s t)
    (hG4 : 0 < G4_sp b0 h0 b2 h2)
    (_hb0h0 : 0 < 1 - b0 - h0)
    (hqA4 : 0 < qA4_sp a2 b2 s t)
    (hD0 : 0 < D0_sp a0 b0 a2 b2)
    (hP4 : 0 < P4C_sp b0 h0 b2 h2)
    (hS : 0 < S_sp s t) (hG55 : 0 < G55)
    (hR24 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - S_sp s t) (D234_sp a2 b2 h2 s t) h2
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ4n : 0 ≤ Row_sp (-S_sp s t) 0 0
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ5n : 0 ≤ Row_sp 0 (-S_sp s t) 0
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hR21 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) h2
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hR23 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) (h2 - 1)
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hR12 : 0 ≤ Row_sp (s - P2_sp a2 b2 h2 s t) (t - D234_sp a2 b2 h2 s t) (-h2)
      ((1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2)
      (t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2) G44 G55 g45 g34 g35 (S_sp s t)) :
    False := by
  by_cases hdel : 0 ≤ del12_sp a0 b0 h0 a2 b2 h2 s t
  · exact cert_FB_CQ1_ge_false hh2 ht0 ht1 hU4 hG4 hqA4 hD0 hP4 hS hG55 hdel hR24 hQ5n hR21 hR23 hR12
  · exact cert_FB_CQ1_lt_false hh2 hh0 ht0 ht1 hU4 hG4 hqA4 hD0 hP4 hS hG55 (lt_of_not_ge hdel)
      hR24 hQ4n hQ5n hR23 hR12

end S2Close

section S2Geometry

open scoped RealInnerProductSpace

private theorem nf29_q_coords {x : Fin 7 → ℝ³} (N : NF29 x) :
    let S := S_sp N.s N.t
    (S • (x 0 - x 6) = D035_sp N.a0 N.b0 N.h0 N.s N.t • (x 4 - x 6) +
      P0_sp N.a0 N.b0 N.h0 N.s N.t • (x 5 - x 6) + (S * N.h0) • (x 3 - x 6)) ∧
    (S • (x 1 - x 6) = N.s • (x 4 - x 6) + N.t • (x 5 - x 6)) ∧
    (S • (x 2 - x 6) = P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S * N.h2) • (x 3 - x 6)) := by
  dsimp only [S_sp, D035_sp, P0_sp, P2_sp, D234_sp]
  rw [N.x0, N.x1, N.x2, N.x3, N.x4, N.x5, N.x6]
  simp only [nfP]
  refine ⟨?_, ?_, ?_⟩ <;> module

/-- **Geometry bridge**: for `v = v4 • (x 4 - x 6) + v5 • (x 5 - x 6)` in plane `Q`,
`Row_sp` equals `S * ⟪x i - x j, v⟫` via `qpencil_depth_split`. -/
theorem nf29_row_eq_inner {x : Fin 7 → ℝ³} (N : NF29 x) (v4 v5 : ℝ)
    {i j : Fin 7} {q4i q5i Yi q4j q5j Yj : ℝ}
    (hi : S_sp N.s N.t • (x i - x 6) = q4i • (x 4 - x 6) + q5i • (x 5 - x 6) +
      (S_sp N.s N.t * Yi) • (x 3 - x 6))
    (hj : S_sp N.s N.t • (x j - x 6) = q4j • (x 4 - x 6) + q5j • (x 5 - x 6) +
      (S_sp N.s N.t * Yj) • (x 3 - x 6)) :
    let v := v4 • (x 4 - x 6) + v5 • (x 5 - x 6)
    Row_sp (q4i - q4j) (q5i - q5j) (Yi - Yj) v4 v5
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) =
      S_sp N.s N.t * ⟪x i - x j, v⟫ := by
  intro v
  have hsub : S_sp N.s N.t • (x i - x j) =
      (S_sp N.s N.t * (Yi - Yj)) • (x 3 - x 6) +
      (q4i - q4j) • (x 4 - x 6) + (q5i - q5j) • (x 5 - x 6) := by
    have h0 : S_sp N.s N.t • (x i - x j) =
        S_sp N.s N.t • (x i - x 6) - S_sp N.s N.t • (x j - x 6) := by module
    rw [h0, hi, hj]; module
  have hsp := qpencil_depth_split (x 3) (x 4) (x 5) (x 6)
    (S_sp N.s N.t * (Yi - Yj)) (q4i - q4j) (q5i - q5j) v4 v5
  dsimp only at hsp
  have h1 : S_sp N.s N.t * ⟪x i - x j, v⟫ = ⟪S_sp N.s N.t • (x i - x j), v⟫ := by
    rw [real_inner_smul_left]
  rw [h1, hsub]
  change _ = ⟪(S_sp N.s N.t * (Yi - Yj)) • (x 3 - x 6) + (q4i - q4j) • (x 4 - x 6) +
      (q5i - q5j) • (x 5 - x 6), v⟫
  rw [hsp]
  dsimp only [Row_sp]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (x 5 - x 6) (x 4 - x 6)]
  ring

/-- **Geometric `C_Q1 × W14 × F-B` closure on `G*`** for `NF29 x` (`K1a` branch `N.a2 < 0`). -/
theorem cert_FB_CQ1_NF29_false {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0)
    (hh2 : 1 < N.h2) (hh0 : N.h0 < 1) (ht1 : N.t < 1)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hG4 : 0 < G4_sp N.b0 N.h0 N.b2 N.h2)
    (hb0h0 : 0 < 1 - N.b0 - N.h0)
    (hQ24 : ⟪x 4 - x 6, (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 4 - x 6) +
        (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 5 - x 6)⟫ ≤
      ⟪x 2 - x 6, (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 4 - x 6) +
        (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 5 - x 6)⟫)
    (hQ40 : ⟪x 4 - x 6, (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 4 - x 6) +
        (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 5 - x 6)⟫ ≤ 0)
    (hQ50 : ⟪x 5 - x 6, (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 4 - x 6) +
        (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 5 - x 6)⟫ ≤ 0)
    (hW12 : ⟪x 1 - x 6, (1 - N.t) • (x 4 - x 6) + N.t • (x 5 - x 6)⟫ ≤
      ⟪x 2 - x 6, (1 - N.t) • (x 4 - x 6) + N.t • (x 5 - x 6)⟫)
    (hW32 : ⟪x 3 - x 6, (1 - N.t) • (x 4 - x 6) + N.t • (x 5 - x 6)⟫ ≤
      ⟪x 2 - x 6, (1 - N.t) • (x 4 - x 6) + N.t • (x 5 - x 6)⟫)
    (hFB : ⟪x 2 - x 6, ((1 - N.t) * P5C_sp N.a0 N.h0 N.a2 N.h2 - N.s * P4C_sp N.b0 N.h0 N.b2 N.h2) • (x 4 - x 6) +
        (N.t * P5C_sp N.a0 N.h0 N.a2 N.h2 + (N.s - 1) * P4C_sp N.b0 N.h0 N.b2 N.h2) • (x 5 - x 6)⟫ ≤
      ⟪x 1 - x 6, ((1 - N.t) * P5C_sp N.a0 N.h0 N.a2 N.h2 - N.s * P4C_sp N.b0 N.h0 N.b2 N.h2) • (x 4 - x 6) +
        (N.t * P5C_sp N.a0 N.h0 N.a2 N.h2 + (N.s - 1) * P4C_sp N.b0 N.h0 N.b2 N.h2) • (x 5 - x 6)⟫) :
    False := by
  have hS : 0 < S_sp N.s N.t := sub_pos.mpr N.hst
  have hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2 := N.hDD
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by
    dsimp [P4C_sp]; linarith [N.hF4]
  have hqA4 : 0 < qA4_sp N.a2 N.b2 N.s N.t := by
    dsimp [qA4_sp]
    have ht1' : 0 < 1 - N.t := sub_pos.mpr ht1
    nlinarith [mul_pos (neg_pos.mpr ha2) ht1', mul_pos (neg_pos.mpr N.hb2) N.hs]
  have hG55 : 0 < ⟪x 5 - x 6, x 5 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide)))
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h3c : S_sp N.s N.t • (x 3 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 1) • (x 3 - x 6) := by module
  have h6c : S_sp N.s N.t • (x 6 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h1c : S_sp N.s N.t • (x 1 - x 6) =
      N.s • (x 4 - x 6) + N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by
    rw [hqc.2.1]; module
  have h4c : S_sp N.s N.t • (x 4 - x 6) =
      S_sp N.s N.t • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by
    module
  have h5c : S_sp N.s N.t • (x 5 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + S_sp N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by
    module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have e24 := nf29_row_eq_inner N (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (i := 2) (j := 4)
    (q4j := S_sp N.s N.t) (q5j := 0) (Yj := 0) h2c h4c
  have e64 := nf29_row_eq_inner N (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (i := 6) (j := 4)
    (q4i := 0) (q5i := 0) (Yi := 0) (q4j := S_sp N.s N.t) (q5j := 0) (Yj := 0) h6c h4c
  have e65 := nf29_row_eq_inner N (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (i := 6) (j := 5)
    (q4i := 0) (q5i := 0) (Yi := 0) (q4j := 0) (q5j := S_sp N.s N.t) (Yj := 0) h6c h5c
  have e21 := nf29_row_eq_inner N (1 - N.t) N.t (i := 2) (j := 1)
    (q4j := N.s) (q5j := N.t) (Yj := 0) h2c h1c
  have e23 := nf29_row_eq_inner N (1 - N.t) N.t (i := 2) (j := 3)
    (q4j := 0) (q5j := 0) (Yj := 1) h2c h3c
  have e12 := nf29_row_eq_inner N
    ((1 - N.t) * P5C_sp N.a0 N.h0 N.a2 N.h2 - N.s * P4C_sp N.b0 N.h0 N.b2 N.h2)
    (N.t * P5C_sp N.a0 N.h0 N.a2 N.h2 + (N.s - 1) * P4C_sp N.b0 N.h0 N.b2 N.h2)
    (i := 1) (j := 2) (q4i := N.s) (q5i := N.t) (Yi := 0) h1c h2c
  simp only [sub_zero, zero_sub] at e24 e64 e65 e21 e23 e12
  have r24 : 0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - S_sp N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) N.h2
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e24, show x 2 - x 4 = (x 2 - x 6) - (x 4 - x 6) by abel, inner_sub_left]
    exact mul_nonneg hS.le (sub_nonneg.mpr hQ24)
  have q4n : 0 ≤ Row_sp (-S_sp N.s N.t) 0 0
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e64, show x 6 - x 4 = -(x 4 - x 6) by abel, inner_neg_left]
    exact mul_nonneg hS.le (neg_nonneg.mpr hQ40)
  have q5n : 0 ≤ Row_sp 0 (-S_sp N.s N.t) 0
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e65, show x 6 - x 5 = -(x 5 - x 6) by abel, inner_neg_left]
    exact mul_nonneg hS.le (neg_nonneg.mpr hQ50)
  have r21 : 0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) N.h2
      (1 - N.t) N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e21, show x 2 - x 1 = (x 2 - x 6) - (x 1 - x 6) by abel, inner_sub_left]
    exact mul_nonneg hS.le (sub_nonneg.mpr hW12)
  have r23 : 0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) (N.h2 - 1)
      (1 - N.t) N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e23, show x 2 - x 3 = (x 2 - x 6) - (x 3 - x 6) by abel, inner_sub_left]
    exact mul_nonneg hS.le (sub_nonneg.mpr hW32)
  have r12 : 0 ≤ Row_sp (N.s - P2_sp N.a2 N.b2 N.h2 N.s N.t) (N.t - D234_sp N.a2 N.b2 N.h2 N.s N.t) (-N.h2)
      ((1 - N.t) * P5C_sp N.a0 N.h0 N.a2 N.h2 - N.s * P4C_sp N.b0 N.h0 N.b2 N.h2)
      (N.t * P5C_sp N.a0 N.h0 N.a2 N.h2 + (N.s - 1) * P4C_sp N.b0 N.h0 N.b2 N.h2)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
    rw [e12, show x 1 - x 2 = (x 1 - x 6) - (x 2 - x 6) by abel, inner_sub_left]
    exact mul_nonneg hS.le (sub_nonneg.mpr hFB)
  exact cert_FB_CQ1_false hh2 hh0 N.ht ht1 hU4 hU5 hG4 hb0h0 hqA4 hD0 hP4 hS hG55
    r24 q4n q5n r21 r23 r12

end S2Geometry

section DB

section DBSpec

variable {R : Type*} [CommRing R]

def v4_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  (1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2

def v5_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2

def Kstar_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  P4C_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t * qA4_sp a2 b2 s t +
    (1 - t) * (h2 - 1) * D0_sp a0 b0 a2 b2 * v4_sp a0 b0 h0 a2 b2 h2 s t

def m20_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  h2 * (h2 - 1) * (1 - t) ^ 2 * D0_sp a0 b0 a2 b2 * P4C_sp b0 h0 b2 h2

def m24_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  P4C_sp b0 h0 b2 h2 * Kstar_sp a0 b0 h0 a2 b2 h2 s t

def m23_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  h2 * P4C_sp b0 h0 b2 h2 ^ 2 * U4_sp a0 b0 h0 a2 b2 h2 s t ^ 2

def m12_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  G4_sp b0 h0 b2 h2 *
    (Kstar_sp a0 b0 h0 a2 b2 h2 s t + (1 - t) ^ 2 * (h2 - 1) * (h2 - h0) * D0_sp a0 b0 a2 b2)

def m21_sp (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  P4C_sp b0 h0 b2 h2 * U4_sp a0 b0 h0 a2 b2 h2 s t * del12_sp a0 b0 h0 a2 b2 h2 s t +
    (1 - t) * (h2 - 1) * (h2 - h0) * D0_sp a0 b0 a2 b2 ^ 2 *
      (v4_sp a0 b0 h0 a2 b2 h2 s t + (1 - t) * (h2 - h0))

def As_sp (a0 b0 h0 a2 b2 h2 : R) : R :=
  -b2 * (h2 - h0) * D0_sp a0 b0 a2 b2 - (h2 - 1) * P4C_sp b0 h0 b2 h2 * G4_sp b0 h0 b2 h2

def g2c_sp (a0 b0 h0 a2 b2 h2 : R) : R :=
  (1 - a2 - h2) * P4C_sp b0 h0 b2 h2 - b2 * P5C_sp a0 h0 a2 h2

def E24_sp (a0 b0 h0 a2 b2 h2 : R) : R :=
  a0 * b2 + (1 - h2 - a2) * b0 - b2 * (1 - h0)

/-- `A35-REFEREE` L1: block `B20` eliminates `g34, g35`. -/
theorem block_B20 (a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : R) :
    let S := S_sp s t
    let D0 := D0_sp a0 b0 a2 b2
    let G4 := G4_sp b0 h0 b2 h2
    let P4 := P4C_sp b0 h0 b2 h2
    let U4 := U4_sp a0 b0 h0 a2 b2 h2 s t
    let U5 := U5_sp a0 b0 h0 a2 b2 h2 s t
    let v4 := v4_sp a0 b0 h0 a2 b2 h2 s t
    let v5 := v5_sp a0 b0 h0 a2 b2 h2 s t
    let P2 := P2_sp a2 b2 h2 s t
    let D234 := D234_sp a2 b2 h2 s t
    let P0 := P0_sp a0 b0 h0 s t
    let D035 := D035_sp a0 b0 h0 s t
    let Q20 := Row_sp (P2 - D035) (D234 - P0) (h2 - h0) (-U4) (-U5) G44 G55 g45 g34 g35 S
    let W21 := Row_sp (P2 - s) (D234 - t) h2 (1 - t) t G44 G55 g45 g34 g35 S
    let F12 := Row_sp (s - P2) (t - D234) (-h2) v4 v5 G44 G55 g45 g34 g35 S
    h2 * P4 * Q20 + (h2 - h0) ^ 2 * D0 * W21 + (h2 - h0) * G4 * F12 =
      P4 * (v4 * U4 * G44 + v5 * U5 * G55 + (v4 * U5 + v5 * U4) * g45) := by
  intro S D0 G4 P4 U4 U5 v4 v5 P2 D234 P0 D035 Q20 W21 F12
  have cG44 : h2 * P4 * ((P2 - D035) * (-U4)) + (h2 - h0) ^ 2 * D0 * ((P2 - s) * (1 - t)) +
      (h2 - h0) * G4 * ((s - P2) * v4) = P4 * (v4 * U4) := by
    dsimp only [S, D0, G4, P4, U4, v4, v4_sp, P2, D035, S_sp, D0_sp, G4_sp, G5_sp, DG5_sp, D023_sp,
      P4C_sp, P5C_sp, U4_sp, P2_sp, D035_sp]; ring
  have cG55 : h2 * P4 * ((D234 - P0) * (-U5)) + (h2 - h0) ^ 2 * D0 * ((D234 - t) * t) +
      (h2 - h0) * G4 * ((t - D234) * v5) = P4 * (v5 * U5) := by
    dsimp only [S, D0, G4, P4, U5, v5, v5_sp, D234, P0, S_sp, D0_sp, G4_sp, G5_sp, DG4_sp, D023_sp,
      P4C_sp, P5C_sp, U5_sp, D234_sp, P0_sp]; ring
  have cg45 : h2 * P4 * ((P2 - D035) * (-U5) + (D234 - P0) * (-U4)) +
      (h2 - h0) ^ 2 * D0 * ((P2 - s) * t + (D234 - t) * (1 - t)) +
      (h2 - h0) * G4 * ((s - P2) * v5 + (t - D234) * v4) = P4 * (v4 * U5 + v5 * U4) := by
    dsimp only [S, D0, G4, P4, U4, U5, v4, v5, v4_sp, v5_sp, P2, D234, P0, D035, S_sp, D0_sp,
      G4_sp, G5_sp, DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, P2_sp, D234_sp, P0_sp,
      D035_sp]; ring
  have cg34 : h2 * P4 * (S * (h2 - h0) * (-U4)) + (h2 - h0) ^ 2 * D0 * (S * h2 * (1 - t)) +
      (h2 - h0) * G4 * (S * (-h2) * v4) = 0 := by
    dsimp only [S, D0, G4, P4, U4, v4, v4_sp, S_sp, D0_sp, G4_sp, G5_sp, DG5_sp, D023_sp, P4C_sp,
      P5C_sp, U4_sp]; ring
  have cg35 : h2 * P4 * (S * (h2 - h0) * (-U5)) + (h2 - h0) ^ 2 * D0 * (S * h2 * t) +
      (h2 - h0) * G4 * (S * (-h2) * v5) = 0 := by
    dsimp only [S, D0, G4, P4, U5, v5, v5_sp, S_sp, D0_sp, G4_sp, G5_sp, DG4_sp, D023_sp, P4C_sp,
      P5C_sp, U5_sp]; ring
  dsimp only [Q20, W21, F12, Row_sp]
  linear_combination G44 * cG44 + G55 * cG55 + g45 * cg45 + g34 * cg34 + g35 * cg35

/-- `A35-REFEREE` L2: sum-of-positives form of `Kstar_sp`. -/
theorem Kstar_sos (a0 b0 h0 a2 b2 h2 s t : R) :
    Kstar_sp a0 b0 h0 a2 b2 h2 s t =
      s * P4C_sp b0 h0 b2 h2 * G4_sp b0 h0 b2 h2 * qA4_sp a2 b2 s t +
        (1 - t) * P4C_sp b0 h0 b2 h2 * (-a2) *
          (s * G4_sp b0 h0 b2 h2 + (1 - t) * (h2 - 1) * (-a0) + (1 - t) * (1 - h0) * (-a2)) +
        (1 - t) ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 * P5C_sp a0 h0 a2 h2 := by
  dsimp only [Kstar_sp, v4_sp, qA4_sp, U4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, P4C_sp, P5C_sp]
  ring

set_option maxHeartbeats 1200000 in
/-- `A35-REFEREE` L3: common polynomial certificate for `C_Q3 × W14 × F-B` and `C_Q4 × W14 × F-B`. -/
theorem cert_FB_CQ34_common (a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : R) :
    let S := S_sp s t
    let D0 := D0_sp a0 b0 a2 b2
    let G4 := G4_sp b0 h0 b2 h2
    let P4 := P4C_sp b0 h0 b2 h2
    let U4 := U4_sp a0 b0 h0 a2 b2 h2 s t
    let U5 := U5_sp a0 b0 h0 a2 b2 h2 s t
    let v4 := v4_sp a0 b0 h0 a2 b2 h2 s t
    let v5 := v5_sp a0 b0 h0 a2 b2 h2 s t
    let P2 := P2_sp a2 b2 h2 s t
    let D234 := D234_sp a2 b2 h2 s t
    let P0 := P0_sp a0 b0 h0 s t
    let D035 := D035_sp a0 b0 h0 s t
    let Q20 := Row_sp (P2 - D035) (D234 - P0) (h2 - h0) (-U4) (-U5) G44 G55 g45 g34 g35 S
    let Q24 := Row_sp (P2 - S) D234 h2 (-U4) (-U5) G44 G55 g45 g34 g35 S
    let W21 := Row_sp (P2 - s) (D234 - t) h2 (1 - t) t G44 G55 g45 g34 g35 S
    let W23 := Row_sp P2 D234 (h2 - 1) (1 - t) t G44 G55 g45 g34 g35 S
    let F12 := Row_sp (s - P2) (t - D234) (-h2) v4 v5 G44 G55 g45 g34 g35 S
    m20_sp a0 b0 h0 a2 b2 h2 s t * Q20 + m24_sp a0 b0 h0 a2 b2 h2 s t * Q24 +
      m21_sp a0 b0 h0 a2 b2 h2 s t * W21 + m23_sp a0 b0 h0 a2 b2 h2 s t * W23 +
      m12_sp a0 b0 h0 a2 b2 h2 s t * F12 =
      -S ^ 2 * (h2 - 1) * D0 * P4 ^ 2 * G4 * G55 := by
  intro S D0 G4 P4 U4 U5 v4 v5 P2 D234 P0 D035 Q20 Q24 W21 W23 F12
  let m20 := m20_sp a0 b0 h0 a2 b2 h2 s t
  let m24 := m24_sp a0 b0 h0 a2 b2 h2 s t
  let m21 := m21_sp a0 b0 h0 a2 b2 h2 s t
  let m23 := m23_sp a0 b0 h0 a2 b2 h2 s t
  let m12 := m12_sp a0 b0 h0 a2 b2 h2 s t
  have cG44 : m20 * ((P2 - D035) * (-U4)) + m24 * ((P2 - S) * (-U4)) +
      m21 * ((P2 - s) * (1 - t)) + m23 * (P2 * (1 - t)) + m12 * ((s - P2) * v4) = 0 := by
    dsimp only [m20, m24, m21, m23, m12, m20_sp, m24_sp, m21_sp, m23_sp, m12_sp, Kstar_sp,
      del12_sp, qA4_sp, v4, v4_sp, S, D0, G4, P4, U4, P2, D035, S_sp, D0_sp, G4_sp, G5_sp,
      DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, P2_sp, D035_sp]; ring
  have cG55 : m20 * ((D234 - P0) * (-U5)) + m24 * (D234 * (-U5)) +
      m21 * ((D234 - t) * t) + m23 * (D234 * t) + m12 * ((t - D234) * v5) =
      -S ^ 2 * (h2 - 1) * D0 * P4 ^ 2 * G4 := by
    dsimp only [m20, m24, m21, m23, m12, m20_sp, m24_sp, m21_sp, m23_sp, m12_sp, Kstar_sp,
      del12_sp, qA4_sp, v4_sp, v5, v5_sp, S, D0, G4, P4, U4, U5, D234, P0, S_sp, D0_sp, G4_sp,
      G5_sp, DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, D234_sp, P0_sp]; ring
  have cg45 : m20 * ((P2 - D035) * (-U5) + (D234 - P0) * (-U4)) +
      m24 * ((P2 - S) * (-U5) + D234 * (-U4)) +
      m21 * ((P2 - s) * t + (D234 - t) * (1 - t)) +
      m23 * (P2 * t + D234 * (1 - t)) +
      m12 * ((s - P2) * v5 + (t - D234) * v4) = 0 := by
    dsimp only [m20, m24, m21, m23, m12, m20_sp, m24_sp, m21_sp, m23_sp, m12_sp, Kstar_sp,
      del12_sp, qA4_sp, v4, v5, v4_sp, v5_sp, S, D0, G4, P4, U4, U5, P2, D234, P0, D035, S_sp,
      D0_sp, G4_sp, G5_sp, DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp, P2_sp, D234_sp,
      P0_sp, D035_sp]; ring
  have cg34 : m20 * (S * (h2 - h0) * (-U4)) + m24 * (S * h2 * (-U4)) +
      m21 * (S * h2 * (1 - t)) + m23 * (S * (h2 - 1) * (1 - t)) +
      m12 * (S * (-h2) * v4) = 0 := by
    dsimp only [m20, m24, m21, m23, m12, m20_sp, m24_sp, m21_sp, m23_sp, m12_sp, Kstar_sp,
      del12_sp, qA4_sp, v4, v4_sp, S, D0, G4, P4, U4, S_sp, D0_sp, G4_sp, G5_sp, DG5_sp, D023_sp,
      P4C_sp, P5C_sp, U4_sp]; ring
  have cg35 : m20 * (S * (h2 - h0) * (-U5)) + m24 * (S * h2 * (-U5)) +
      m21 * (S * h2 * t) + m23 * (S * (h2 - 1) * t) +
      m12 * (S * (-h2) * v5) = 0 := by
    dsimp only [m20, m24, m21, m23, m12, m20_sp, m24_sp, m21_sp, m23_sp, m12_sp, Kstar_sp,
      del12_sp, qA4_sp, v4_sp, v5, v5_sp, S, D0, G4, P4, U4, U5, S_sp, D0_sp, G4_sp, G5_sp,
      DG4_sp, DG5_sp, D023_sp, P4C_sp, P5C_sp, U4_sp, U5_sp]; ring
  dsimp only [Q20, Q24, W21, W23, F12, Row_sp]
  linear_combination G44 * cG44 + G55 * cG55 + g45 * cg45 + g34 * cg34 + g35 * cg35

/-- `A35-REFEREE` L6: `del12_sp` split in quadrant II. -/
theorem del12_split (a0 b0 h0 a2 b2 h2 s t : R) :
    P4C_sp b0 h0 b2 h2 * del12_sp a0 b0 h0 a2 b2 h2 s t =
      (-v4_sp a0 b0 h0 a2 b2 h2 s t) * As_sp a0 b0 h0 a2 b2 h2 +
        (1 - t) * (h2 - h0) * D0_sp a0 b0 a2 b2 * g2c_sp a0 b0 h0 a2 b2 h2 ∧
    g2c_sp a0 b0 h0 a2 b2 h2 =
      h2 * E24_sp a0 b0 h0 a2 b2 h2 + b2 * (h2 - h0) := by
  constructor <;>
    · dsimp only [del12_sp, v4_sp, As_sp, g2c_sp, E24_sp, qA4_sp, U4_sp, DG5_sp, D023_sp, D0_sp,
        G4_sp, G5_sp, P4C_sp, P5C_sp]
      ring

end DBSpec

/-- `A35-REFEREE` L4: positivity of `K*`, `m20`, `m24`, `m23`, `m12` from `G*` + `K1a` region facts only. -/
theorem cert_FB_CQ34_mults_pos {a0 b0 h0 a2 b2 h2 s t : ℝ}
    (ha0 : a0 < 0) (ha2 : a2 < 0) (hb2 : b2 < 0) (hs : 0 < s) (ht : t < 1)
    (hh2 : 1 < h2) (hh0 : h0 < 1)
    (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hP5 : 0 < P5C_sp a0 h0 a2 h2)
    (hD0 : 0 < D0_sp a0 b0 a2 b2) (hG4 : 0 < G4_sp b0 h0 b2 h2)
    (hU4 : 0 < U4_sp a0 b0 h0 a2 b2 h2 s t) :
    0 < Kstar_sp a0 b0 h0 a2 b2 h2 s t ∧
      0 < m20_sp a0 b0 h0 a2 b2 h2 s t ∧
      0 < m24_sp a0 b0 h0 a2 b2 h2 s t ∧
      0 < m23_sp a0 b0 h0 a2 b2 h2 s t ∧
      0 < m12_sp a0 b0 h0 a2 b2 h2 s t := by
  have ht1 : 0 < 1 - t := sub_pos.mpr ht
  have hh21 : 0 < h2 - 1 := sub_pos.mpr hh2
  have hh20 : 0 < h2 - h0 := by linarith
  have hh01 : 0 < 1 - h0 := sub_pos.mpr hh0
  have hh2pos : 0 < h2 := by linarith
  have hqA4 : 0 < qA4_sp a2 b2 s t := by
    dsimp [qA4_sp]; nlinarith [mul_pos (neg_pos.mpr ha2) ht1, mul_pos (neg_pos.mpr hb2) hs]
  have hK : 0 < Kstar_sp a0 b0 h0 a2 b2 h2 s t := by
    rw [Kstar_sos]
    have t1 : 0 < s * P4C_sp b0 h0 b2 h2 * G4_sp b0 h0 b2 h2 * qA4_sp a2 b2 s t := by positivity
    have t2 : 0 ≤ (1 - t) * P4C_sp b0 h0 b2 h2 * (-a2) *
        (s * G4_sp b0 h0 b2 h2 + (1 - t) * (h2 - 1) * (-a0) + (1 - t) * (1 - h0) * (-a2)) := by
      have : 0 < -a2 := neg_pos.mpr ha2
      have : 0 < -a0 := neg_pos.mpr ha0
      positivity
    have t3 : 0 ≤ (1 - t) ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 * P5C_sp a0 h0 a2 h2 := by positivity
    linarith
  have hm20 : 0 < m20_sp a0 b0 h0 a2 b2 h2 s t := by dsimp [m20_sp]; positivity
  have hm24 : 0 < m24_sp a0 b0 h0 a2 b2 h2 s t := by dsimp [m24_sp]; positivity
  have hm23 : 0 < m23_sp a0 b0 h0 a2 b2 h2 s t := by dsimp [m23_sp]; positivity
  have hm12 : 0 < m12_sp a0 b0 h0 a2 b2 h2 s t := by dsimp [m12_sp]; positivity
  exact ⟨hK, hm20, hm24, hm23, hm12⟩

/-- `A35-REFEREE` L5: closing `Prop` for `C_Q3 × W14 × F-B` and `C_Q4 × W14 × F-B`.
Note: `hm21 : 0 ≤ m21_sp ...` is a SAMPLE fact (holds on 165/165 `G*` data shapes and in
`9.36M` `G* ∩ Q2` samples, but is FALSE on `G*` outside quadrant II, e.g. `neg21_0`). -/
theorem cert_FB_CQ34_false {a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35 : ℝ}
    (ha0 : a0 < 0) (ha2 : a2 < 0) (hb2 : b2 < 0) (hs : 0 < s) (ht : t < 1)
    (hh2 : 1 < h2) (hh0 : h0 < 1)
    (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hP5 : 0 < P5C_sp a0 h0 a2 h2)
    (hD0 : 0 < D0_sp a0 b0 a2 b2) (hG4 : 0 < G4_sp b0 h0 b2 h2)
    (hU4 : 0 < U4_sp a0 b0 h0 a2 b2 h2 s t)
    (hm21 : 0 ≤ m21_sp a0 b0 h0 a2 b2 h2 s t)
    (hS : 0 < S_sp s t) (hG55 : 0 < G55)
    (hQ20 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - D035_sp a0 b0 h0 s t)
      (D234_sp a2 b2 h2 s t - P0_sp a0 b0 h0 s t) (h2 - h0)
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hQ24 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - S_sp s t) (D234_sp a2 b2 h2 s t) h2
      (-U4_sp a0 b0 h0 a2 b2 h2 s t) (-U5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t))
    (hW21 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) h2
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hW23 : 0 ≤ Row_sp (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) (h2 - 1)
      (1 - t) t G44 G55 g45 g34 g35 (S_sp s t))
    (hF12 : 0 ≤ Row_sp (s - P2_sp a2 b2 h2 s t) (t - D234_sp a2 b2 h2 s t) (-h2)
      (v4_sp a0 b0 h0 a2 b2 h2 s t) (v5_sp a0 b0 h0 a2 b2 h2 s t) G44 G55 g45 g34 g35 (S_sp s t)) :
    False := by
  obtain ⟨_, hm20, hm24, hm23, hm12⟩ :=
    cert_FB_CQ34_mults_pos ha0 ha2 hb2 hs ht hh2 hh0 hP4 hP5 hD0 hG4 hU4
  have hid := cert_FB_CQ34_common a0 b0 h0 a2 b2 h2 s t G44 G55 g45 g34 g35
  dsimp only at hid
  have hh21 : 0 < h2 - 1 := sub_pos.mpr hh2
  have hrhs : -S_sp s t ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 *
      P4C_sp b0 h0 b2 h2 ^ 2 * G4_sp b0 h0 b2 h2 * G55 < 0 := by
    have : 0 < S_sp s t ^ 2 * (h2 - 1) * D0_sp a0 b0 a2 b2 *
        P4C_sp b0 h0 b2 h2 ^ 2 * G4_sp b0 h0 b2 h2 * G55 := by positivity
    linarith
  nlinarith [mul_nonneg hm20.le hQ20, mul_nonneg hm24.le hQ24, mul_nonneg hm21 hW21,
    mul_nonneg hm23.le hW23, mul_nonneg hm12.le hF12]

/-- Positivity corollary of `del12_split` in quadrant II. -/
theorem del12_pos_of_split {a0 b0 h0 a2 b2 h2 s t : ℝ}
    (hP4 : 0 < P4C_sp b0 h0 b2 h2) (hv4 : v4_sp a0 b0 h0 a2 b2 h2 s t < 0)
    (ht : t < 1) (hAs : 0 ≤ As_sp a0 b0 h0 a2 b2 h2) (hg2c : 0 < g2c_sp a0 b0 h0 a2 b2 h2)
    (hhD : 0 < (h2 - h0) * D0_sp a0 b0 a2 b2) :
    0 < del12_sp a0 b0 h0 a2 b2 h2 s t := by
  have hsp := (del12_split a0 b0 h0 a2 b2 h2 s t).1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht
  have hv4' : 0 < -v4_sp a0 b0 h0 a2 b2 h2 s t := neg_pos.mpr hv4
  have hprod : 0 < P4C_sp b0 h0 b2 h2 * del12_sp a0 b0 h0 a2 b2 h2 s t := by
    rw [hsp]
    have t1 : 0 ≤ (-v4_sp a0 b0 h0 a2 b2 h2 s t) * As_sp a0 b0 h0 a2 b2 h2 := by positivity
    have t2 : 0 < (1 - t) * (h2 - h0) * D0_sp a0 b0 a2 b2 * g2c_sp a0 b0 h0 a2 b2 h2 := by
      have : 0 < (1 - t) * ((h2 - h0) * D0_sp a0 b0 a2 b2) * g2c_sp a0 b0 h0 a2 b2 h2 := by
        positivity
      linarith
    linarith
  exact pos_of_mul_pos_right hprod hP4.le

end DB

section DBLeaves

open scoped RealInnerProductSpace
open _root_.Minimality.H21 (s0x_fac29)
open Minimality.GenQuad (FrontDet LexClause lexClause_of_frontOf lexClause_of_notM)

variable {x : Fin 7 → ℝ³}

theorem nf29_vQ_eq_u23Q (N : NF29 x) :
    (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 4 - x 6) +
      (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) • (x 5 - x 6) =
      S_sp N.s N.t • N.u23Q x := by
  dsimp only [u23Q]
  rw [N.x4, N.x5, N.x6, N.x0, N.x2, N.x3]
  dsimp only [U4_sp, U5_sp, DG4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, S_sp]
  simp only [nfP]
  have c1 : (-((N.a0 * N.b2 - N.a2 * N.b0 + N.s * (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) +
          N.t * (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))) -
          (N.a0 * N.b2 - N.a2 * N.b0 + (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))))) * (1 - N.s) +
      (-(N.a0 * N.b2 - N.a2 * N.b0 + (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) -
          (N.a0 * N.b2 - N.a2 * N.b0 + N.s * (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) +
            N.t * (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))))) * (-N.s) =
      (N.s + N.t - 1) * ((1 - N.h2) * N.a0 - (1 - N.h0) * N.a2) := by ring
  have c2 : (-((N.a0 * N.b2 - N.a2 * N.b0 + N.s * (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) +
          N.t * (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))) -
          (N.a0 * N.b2 - N.a2 * N.b0 + (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))))) * (-N.t) +
      (-(N.a0 * N.b2 - N.a2 * N.b0 + (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) -
          (N.a0 * N.b2 - N.a2 * N.b0 + N.s * (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)) +
            N.t * (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2))))) * (1 - N.t) =
      (N.s + N.t - 1) * ((1 - N.h2) * N.b0 - (1 - N.h0) * N.b2) := by ring
  have c3 : (1 - N.h2) * (-N.h0 - -1) - (1 - N.h0) * (-N.h2 - -1) = (0 : ℝ) := by ring
  simp only [smul_add, smul_sub, smul_smul, sub_zero, zero_smul, add_zero]
  module

theorem nf29_v14_eq (N : NF29 x) :
    (1 - N.t) • (x 4 - x 6) + N.t • (x 5 - x 6) = S_sp N.s N.t • (x 1 - x 4) := by
  rw [N.x1, N.x4, N.x5, N.x6]
  dsimp only [S_sp]
  simp only [nfP]
  module

theorem nf29_v012_eq_bLine (N : NF29 x) :
    v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) =
      S_sp N.s N.t • N.bLine x := by
  dsimp only [bLine]
  rw [N.x0, N.x1, N.x2, N.x4, N.x5, N.x6]
  dsimp only [v4_sp, v5_sp, P4C_sp, P5C_sp, S_sp]
  simp only [nfP]
  module

private theorem row_of_dir_le {N : NF29 x} {i j : Fin 7}
    {q4i q5i Yi q4j q5j Yj v4 v5 : ℝ} {u : ℝ³}
    (hu : v4 • (x 4 - x 6) + v5 • (x 5 - x 6) = S_sp N.s N.t • u)
    (hi : S_sp N.s N.t • (x i - x 6) =
      q4i • (x 4 - x 6) + q5i • (x 5 - x 6) + (S_sp N.s N.t * Yi) • (x 3 - x 6))
    (hj : S_sp N.s N.t • (x j - x 6) =
      q4j • (x 4 - x 6) + q5j • (x 5 - x 6) + (S_sp N.s N.t * Yj) • (x 3 - x 6))
    (hle : ⟪x j, u⟫ ≤ ⟪x i, u⟫) :
    0 ≤ Row_sp (q4i - q4j) (q5i - q5j) (Yi - Yj) v4 v5
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  rw [nf29_row_eq_inner N v4 v5 hi hj, hu, real_inner_smul_right]
  have hdiff : 0 ≤ ⟪x i - x j, u⟫ := by
    rw [inner_sub_left]
    exact sub_nonneg.mpr hle
  have hS : 0 ≤ S_sp N.s N.t := (sub_pos.mpr N.hst).le
  exact mul_nonneg hS (mul_nonneg hS hdiff)

/-- `W14` 4-rim bridge: `¬ LexAny29` + `K1a` + `G*` gives `0 ≤ W21` and `0 ≤ W23` (no extra rim clauses). -/
theorem w14_of_not_lexAny29 (N : NF29 x)
    (ha2 : N.a2 < 0) (ht : N.t < 1) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - N.s) (D234_sp N.a2 N.b2 N.h2 N.s N.t - N.t) N.h2
      (1 - N.t) N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) ∧
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) (N.h2 - 1)
      (1 - N.t) N.t ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  have hM : ⟪x 1, x 1 - x 4⟫ ≤ ⟪x 2, x 1 - x 4⟫ ∧ ⟪x 3, x 1 - x 4⟫ ≤ ⟪x 2, x 1 - x 4⟫ ∧
      ⟪x 1, x 1 - x 4⟫ ≤ ⟪x 5, x 1 - x 4⟫ ∧ ⟪x 3, x 1 - x 4⟫ ≤ ⟪x 5, x 1 - x 4⟫ := by
    by_contra hnot
    exact hnf (lexAny29_W14 N ha2 ht hdG4 hA hnot)
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h1c : S_sp N.s N.t • (x 1 - x 6) =
      N.s • (x 4 - x 6) + N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by
    rw [hqc.2.1]; module
  have h3c : S_sp N.s N.t • (x 3 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 1) • (x 3 - x 6) := by module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have rw21 := row_of_dir_le (nf29_v14_eq N) h2c h1c hM.1
  have rw23 := row_of_dir_le (nf29_v14_eq N) h2c h3c hM.2.1
  simp only [sub_zero] at rw21 rw23
  exact ⟨rw21, rw23⟩

private theorem u23Q_params_of_Gstar (N : NF29 x)
    (ha2 : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1)
    (hdG4 : 0 < N.dG4) (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) :
    N.dG < 0 ∧ 0 < (-N.dG) * N.P5 + N.dG4 * N.P4 ∧
      0 < N.D023 - N.DG5 ∧ 0 < N.DG4 - N.D023 := by
  have hdG : N.dG < 0 := by
    dsimp [NF29.dG]
    have ha0 : N.a0 < 0 := N.ha0
    have hh21 : 0 < N.h2 - 1 := sub_pos.mpr hh2
    have hh01 : 0 < 1 - N.h0 := sub_pos.mpr hh0
    nlinarith [mul_pos (neg_pos.mpr ha2) hh01, mul_pos (neg_pos.mpr ha0) hh21]
  have hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4 := by
    have hP4 : 0 < N.P4 := by dsimp [NF29.P4]; linarith [N.hF5]
    have hP5 : 0 < N.P5 := by dsimp [NF29.P5]; linarith [N.hF4]
    nlinarith [mul_pos (neg_pos.mpr hdG) hP5, mul_pos hdG4 hP4]
  have h4 : 0 < N.D023 - N.DG5 := by
    have : N.D023 - N.DG5 = U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
      dsimp [U4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, NF29.D023, NF29.DG5, NF29.dG4,
        NF29.dG]; ring
    linarith
  have h5 : 0 < N.DG4 - N.D023 := by
    have : N.DG4 - N.D023 = U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
      dsimp [U5_sp, DG4_sp, D023_sp, D0_sp, G4_sp, G5_sp, NF29.DG4, NF29.D023, NF29.dG4,
        NF29.dG]; ring
    linarith
  exact ⟨hdG, hK, h4, h5⟩

private theorem u23Q_ne_zero (N : NF29 x)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) : N.u23Q x ≠ 0 := by
  intro h0
  have h1 : N.f356.f (x 3 + N.u23Q x) - N.f356.f (x 3) = 0 := by rw [h0, add_zero, sub_self]
  rw [f356_u23Q N] at h1
  have h4 : 0 < N.D023 - N.DG5 := by
    dsimp [U4_sp, DG5_sp, D023_sp, D0_sp, G4_sp, G5_sp, NF29.D023, NF29.DG5, NF29.dG4,
      NF29.dG] at *
    linarith
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have : 0 < (N.D023 - N.DG5) * N.D ^ 2 := mul_pos h4 hD2
  linarith

/-- `U023Q` 5-rim case split on `![0, 2, 4, 6, 5]`: under `G*` + `K1a` and the five `FrontDet`
diagonals (all checked on `N_star_pert` and `N_counter`), `¬ LexAny29` forces one of the five
`M` cones `C_Q3`, `C_Q4`, `C_Q5+`, `C_Q2`, `C_Q1`. -/
theorem u23Q_cones_of_not_lexAny29 (N : NF29 x)
    (ha2 : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1)
    (hdG4 : 0 < N.dG4) (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hF0123 : FrontDet (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (hF0124 : FrontDet (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (hF0134 : FrontDet (x 2) (x 5) (x 0) (x 6) (N.u23Q x))
    (hF0234 : FrontDet (x 0) (x 6) (x 4) (x 5) (N.u23Q x))
    (hF1234 : FrontDet (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    (⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫) ∨
    (⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ ∧
      ⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫) ∨
    (⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ ∧
      ⟪x 6, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 6, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫) ∨
    (⟪x 4, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 5, N.u23Q x⟫ ≤ ⟪x 0, N.u23Q x⟫ ∧ ⟪x 5, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫) ∨
    (⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 5, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 5, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫) := by
  by_contra hnot
  rcases not_or.mp hnot with ⟨hM3, hnot⟩
  rcases not_or.mp hnot with ⟨hM4, hnot⟩
  rcases not_or.mp hnot with ⟨hM5, hnot⟩
  rcases not_or.mp hnot with ⟨hM2, hM1⟩
  obtain ⟨hdG, hK, h4, h5⟩ := u23Q_params_of_Gstar N ha2 hh2 hh0 hdG4 hU4 hU5
  have hu_ne : N.u23Q x ≠ 0 := u23Q_ne_zero N hU4
  exact hnf (lexAny29_U023Qx_clauses N hdG hdG4 hh0 N.hE35 hK hh2.le h4 h5
    (lexClause_of_frontOf hu_ne hF0123.frontOf) (lexClause_of_notM hM3)
    (lexClause_of_frontOf hu_ne hF0124.frontOf) (lexClause_of_notM hM4)
    (lexClause_of_frontOf hu_ne hF0134.frontOf) (lexClause_of_notM hM5)
    (lexClause_of_notM hM2) (lexClause_of_frontOf hu_ne hF0234.frontOf)
    (lexClause_of_notM hM1) (lexClause_of_frontOf hu_ne hF1234.frontOf))

/-- `C_Q1` rim bridge at `vQ = S • u23Q`. -/
theorem cq1_of_not_lexAny29 (N : NF29 x)
    (ha2 : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1)
    (hdG4 : 0 < N.dG4) (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hA0123 : LexClause (x 2) (x 6) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0123 : LexClause (x 0) (x 4) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hA0124 : LexClause (x 2) (x 5) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0124 : LexClause (x 0) (x 4) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hF1234 : FrontDet (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - S_sp N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) N.h2
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) ∧
    0 ≤ Row_sp (-S_sp N.s N.t) 0 0
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) ∧
    0 ≤ Row_sp 0 (-S_sp N.s N.t) 0
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  have hM : ⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 5, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 5, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ := by
    by_contra hnot
    obtain ⟨hdG, hK, h4, h5⟩ := u23Q_params_of_Gstar N ha2 hh2 hh0 hdG4 hU4 hU5
    have hu_ne : N.u23Q x ≠ 0 := u23Q_ne_zero N hU4
    exact hnf (lexAny29_U023Qx_clauses N hdG hdG4 hh0 N.hE35 hK hh2.le h4 h5
      hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234
      (lexClause_of_notM hnot) (lexClause_of_frontOf hu_ne hF1234.frontOf))
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h6c : S_sp N.s N.t • (x 6 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h4c : S_sp N.s N.t • (x 4 - x 6) =
      S_sp N.s N.t • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h5c : S_sp N.s N.t • (x 5 - x 6) =
      (0 : ℝ) • (x 4 - x 6) + S_sp N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have r24 := row_of_dir_le (nf29_vQ_eq_u23Q N) h2c h4c hM.1
  have q4n := row_of_dir_le (nf29_vQ_eq_u23Q N) h6c h4c hM.2.1
  have q5n := row_of_dir_le (nf29_vQ_eq_u23Q N) h6c h5c hM.2.2.2
  simp only [sub_zero, zero_sub] at r24 q4n q5n
  exact ⟨r24, q4n, q5n⟩

/-- `C_Q3` rim bridge at `vQ = S • u23Q`: yields `0 ≤ Q20 ∧ 0 ≤ Q24`. -/
theorem cq3_of_not_lexAny29 (N : NF29 x)
    (ha2 : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1)
    (hdG4 : 0 < N.dG4) (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hF0123 : FrontDet (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (hA0124 : LexClause (x 2) (x 5) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0124 : LexClause (x 0) (x 4) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA1234 : LexClause (x 4) (x 5) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB1234 : LexClause (x 2) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - D035_sp N.a0 N.b0 N.h0 N.s N.t)
      (D234_sp N.a2 N.b2 N.h2 N.s N.t - P0_sp N.a0 N.b0 N.h0 N.s N.t) (N.h2 - N.h0)
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) ∧
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - S_sp N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) N.h2
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  have hM : ⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ ∧
      ⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 6, N.u23Q x⟫ := by
    by_contra hnot
    obtain ⟨hdG, hK, h4, h5⟩ := u23Q_params_of_Gstar N ha2 hh2 hh0 hdG4 hU4 hU5
    have hu_ne : N.u23Q x ≠ 0 := u23Q_ne_zero N hU4
    exact hnf (lexAny29_U023Qx_clauses N hdG hdG4 hh0 N.hE35 hK hh2.le h4 h5
      (lexClause_of_frontOf hu_ne hF0123.frontOf) (lexClause_of_notM hnot)
      hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234)
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h0c : S_sp N.s N.t • (x 0 - x 6) =
      D035_sp N.a0 N.b0 N.h0 N.s N.t • (x 4 - x 6) +
      P0_sp N.a0 N.b0 N.h0 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h0) • (x 3 - x 6) := hqc.1
  have h4c : S_sp N.s N.t • (x 4 - x 6) =
      S_sp N.s N.t • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have r20 := row_of_dir_le (nf29_vQ_eq_u23Q N) h2c h0c hM.1
  have r24 := row_of_dir_le (nf29_vQ_eq_u23Q N) h2c h4c hM.2.2.1
  simp only [sub_zero] at r24
  exact ⟨r20, r24⟩

/-- `C_Q4` rim bridge at `vQ = S • u23Q`: yields `0 ≤ Q20 ∧ 0 ≤ Q24`. -/
theorem cq4_of_not_lexAny29 (N : NF29 x)
    (ha2 : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1)
    (hdG4 : 0 < N.dG4) (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hA0123 : LexClause (x 2) (x 6) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0123 : LexClause (x 0) (x 4) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hF0124 : FrontDet (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA1234 : LexClause (x 4) (x 5) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB1234 : LexClause (x 2) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - D035_sp N.a0 N.b0 N.h0 N.s N.t)
      (D234_sp N.a2 N.b2 N.h2 N.s N.t - P0_sp N.a0 N.b0 N.h0 N.s N.t) (N.h2 - N.h0)
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) ∧
    0 ≤ Row_sp (P2_sp N.a2 N.b2 N.h2 N.s N.t - S_sp N.s N.t) (D234_sp N.a2 N.b2 N.h2 N.s N.t) N.h2
      (-U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) (-U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  have hM : ⟪x 0, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 0, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ ∧
      ⟪x 4, N.u23Q x⟫ ≤ ⟪x 2, N.u23Q x⟫ ∧ ⟪x 4, N.u23Q x⟫ ≤ ⟪x 5, N.u23Q x⟫ := by
    by_contra hnot
    obtain ⟨hdG, hK, h4, h5⟩ := u23Q_params_of_Gstar N ha2 hh2 hh0 hdG4 hU4 hU5
    have hu_ne : N.u23Q x ≠ 0 := u23Q_ne_zero N hU4
    exact hnf (lexAny29_U023Qx_clauses N hdG hdG4 hh0 N.hE35 hK hh2.le h4 h5
      hA0123 hB0123 (lexClause_of_frontOf hu_ne hF0124.frontOf) (lexClause_of_notM hnot)
      hA0134 hB0134 hA0234 hB0234 hA1234 hB1234)
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h0c : S_sp N.s N.t • (x 0 - x 6) =
      D035_sp N.a0 N.b0 N.h0 N.s N.t • (x 4 - x 6) +
      P0_sp N.a0 N.b0 N.h0 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h0) • (x 3 - x 6) := hqc.1
  have h4c : S_sp N.s N.t • (x 4 - x 6) =
      S_sp N.s N.t • (x 4 - x 6) + (0 : ℝ) • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have r20 := row_of_dir_le (nf29_vQ_eq_u23Q N) h2c h0c hM.1
  have r24 := row_of_dir_le (nf29_vQ_eq_u23Q N) h2c h4c hM.2.2.1
  simp only [sub_zero] at r24
  exact ⟨r20, r24⟩

/-- `F-B` rim bridge at `v012 = S • bLine`: requires the four `bLine` facet signs (`0 < v035`,
`v234 < 0`, `v346 < 0`, `0 < v356`), the four `{0124, 0134, 0234, 1234}` clauses on `![1, 2, 3, 6, 5]`,
and the `F-B` front diagonal `FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x)`. -/
theorem fb_of_not_lexAny29 (N : NF29 x)
    (hh : N.h0 < N.h2) (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123 : FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x))
    (hF0124 : FrontDet (x 2) (x 5) (x 1) (x 3) (N.bLine x))
    (hM0124 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0134 : FrontDet (x 2) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0134 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0234 : FrontDet (x 3) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0234 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF1234 : FrontDet (x 3) (x 5) (x 2) (x 6) (N.bLine x))
    (hM1234 : ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    0 ≤ Row_sp (N.s - P2_sp N.a2 N.b2 N.h2 N.s N.t) (N.t - D234_sp N.a2 N.b2 N.h2 N.s N.t) (-N.h2)
      (v4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      (v5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
      ⟪x 4 - x 6, x 4 - x 6⟫ ⟪x 5 - x 6, x 5 - x 6⟫ ⟪x 4 - x 6, x 5 - x 6⟫
      ⟪x 3 - x 6, x 4 - x 6⟫ ⟪x 3 - x 6, x 5 - x 6⟫ (S_sp N.s N.t) := by
  have hM : ⟪x 2, N.bLine x⟫ ≤ ⟪x 1, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧
      ⟪x 6, N.bLine x⟫ ≤ ⟪x 1, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ := by
    by_contra hnot
    exact hnf (lexAny29_F012F1456 N hh h035 h234 h346 h356 (Or.inr ⟨hF0123, hnot⟩)
      hF0124 hM0124 hF0134 hM0134 hF0234 hM0234 hF1234 hM1234)
  have hqc := nf29_q_coords N
  dsimp only at hqc
  have h1c : S_sp N.s N.t • (x 1 - x 6) =
      N.s • (x 4 - x 6) + N.t • (x 5 - x 6) + (S_sp N.s N.t * 0) • (x 3 - x 6) := by
    rw [hqc.2.1]; module
  have h2c : S_sp N.s N.t • (x 2 - x 6) =
      P2_sp N.a2 N.b2 N.h2 N.s N.t • (x 4 - x 6) +
      D234_sp N.a2 N.b2 N.h2 N.s N.t • (x 5 - x 6) + (S_sp N.s N.t * N.h2) • (x 3 - x 6) := hqc.2.2
  have r12 := row_of_dir_le (nf29_v012_eq_bLine N) h1c h2c hM.1
  rw [zero_sub] at r12
  exact r12

/-- Leaf corollary for `C_Q1 × W14 × F-B` on `G*`. -/
theorem cert_FB_CQ1_leaf (N : NF29 x)
    (hk : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1) (ht1 : N.t < 1)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hG4 : 0 < G4_sp N.b0 N.h0 N.b2 N.h2) (hb0h0 : 0 < 1 - N.b0 - N.h0)
    (hA0123 : LexClause (x 2) (x 6) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0123 : LexClause (x 0) (x 4) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hA0124 : LexClause (x 2) (x 5) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0124 : LexClause (x 0) (x 4) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hF1234Q : FrontDet (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123F : FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x))
    (hF0124F : FrontDet (x 2) (x 5) (x 1) (x 3) (N.bLine x))
    (hM0124F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0134F : FrontDet (x 2) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0134F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0234F : FrontDet (x 3) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0234F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF1234F : FrontDet (x 3) (x 5) (x 2) (x 6) (N.bLine x))
    (hM1234F : ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  have hdG4 : 0 < N.dG4 := by
    dsimp [NF29.dG4]
    exact hG4
  have hS : 0 < S_sp N.s N.t := sub_pos.mpr N.hst
  have hD0 : 0 < D0_sp N.a0 N.b0 N.a2 N.b2 := N.hDD
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
  have hqA4 : 0 < qA4_sp N.a2 N.b2 N.s N.t := by
    dsimp [qA4_sp]
    nlinarith [mul_pos (neg_pos.mpr hk) (sub_pos.mpr ht1), mul_pos (neg_pos.mpr N.hb2) N.hs]
  have hG55 : 0 < ⟪x 5 - x 6, x 5 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide)))
  obtain ⟨r24, q4n, q5n⟩ := cq1_of_not_lexAny29 N hk hh2 hh0 hdG4 hU4 hU5
    hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hF1234Q hnf
  obtain ⟨r21, r23⟩ := w14_of_not_lexAny29 N hk ht1 hdG4 hb0h0 hnf
  have r12 := fb_of_not_lexAny29 N (by linarith) h035 h234 h346 h356
    hF0123F hF0124F hM0124F hF0134F hM0134F hF0234F hM0234F hF1234F hM1234F hnf
  exact cert_FB_CQ1_false hh2 hh0 N.ht ht1 hU4 hU5 hG4 hb0h0 hqA4 hD0 hP4 hS hG55
    r24 q4n q5n r21 r23 r12

/-- Leaf corollary for `C_Q3 × W14 × F-B` on `G*` with explicit `hm21`. -/
theorem cert_FB_CQ3_leaf (N : NF29 x)
    (hk : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1) (ht1 : N.t < 1)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hG4 : 0 < G4_sp N.b0 N.h0 N.b2 N.h2) (hb0h0 : 0 < 1 - N.b0 - N.h0)
    (hm21 : 0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hF0123Q : FrontDet (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (hA0124 : LexClause (x 2) (x 5) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0124 : LexClause (x 0) (x 4) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA1234 : LexClause (x 4) (x 5) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB1234 : LexClause (x 2) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123F : FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x))
    (hF0124F : FrontDet (x 2) (x 5) (x 1) (x 3) (N.bLine x))
    (hM0124F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0134F : FrontDet (x 2) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0134F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0234F : FrontDet (x 3) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0234F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF1234F : FrontDet (x 3) (x 5) (x 2) (x 6) (N.bLine x))
    (hM1234F : ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  have hdG4 : 0 < N.dG4 := by
    dsimp [NF29.dG4]
    exact hG4
  have hG55 : 0 < ⟪x 5 - x 6, x 5 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide)))
  obtain ⟨q20, q24⟩ := cq3_of_not_lexAny29 N hk hh2 hh0 hdG4 hU4 hU5
    hF0123Q hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234 hnf
  obtain ⟨r21, r23⟩ := w14_of_not_lexAny29 N hk ht1 hdG4 hb0h0 hnf
  have r12 := fb_of_not_lexAny29 N (by linarith) h035 h234 h346 h356
    hF0123F hF0124F hM0124F hF0134F hM0134F hF0234F hM0234F hF1234F hM1234F hnf
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
  have hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := by dsimp [P5C_sp]; linarith [N.hF5]
  exact cert_FB_CQ34_false N.ha0 hk N.hb2 N.hs ht1 hh2 hh0 hP4 hP5 N.hDD hG4 hU4
    hm21 (sub_pos.mpr N.hst) hG55 q20 q24 r21 r23 r12

/-- Leaf corollary for `C_Q4 × W14 × F-B` on `G*` with explicit `hm21`. -/
theorem cert_FB_CQ4_leaf (N : NF29 x)
    (hk : N.a2 < 0) (hh2 : 1 < N.h2) (hh0 : N.h0 < 1) (ht1 : N.t < 1)
    (hU4 : 0 < U4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hU5 : 0 < U5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hG4 : 0 < G4_sp N.b0 N.h0 N.b2 N.h2) (hb0h0 : 0 < 1 - N.b0 - N.h0)
    (hm21 : 0 ≤ m21_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t)
    (hA0123 : LexClause (x 2) (x 6) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0123 : LexClause (x 0) (x 4) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hF0124Q : FrontDet (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (hA0134 : LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA1234 : LexClause (x 4) (x 5) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB1234 : LexClause (x 2) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123F : FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x))
    (hF0124F : FrontDet (x 2) (x 5) (x 1) (x 3) (N.bLine x))
    (hM0124F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0134F : FrontDet (x 2) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0134F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0234F : FrontDet (x 3) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0234F : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF1234F : FrontDet (x 3) (x 5) (x 2) (x 6) (N.bLine x))
    (hM1234F : ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                  ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  have hdG4 : 0 < N.dG4 := by
    dsimp [NF29.dG4]
    exact hG4
  have hG55 : 0 < ⟪x 5 - x 6, x 5 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide)))
  obtain ⟨q20, q24⟩ := cq4_of_not_lexAny29 N hk hh2 hh0 hdG4 hU4 hU5
    hA0123 hB0123 hF0124Q hA0134 hB0134 hA0234 hB0234 hA1234 hB1234 hnf
  obtain ⟨r21, r23⟩ := w14_of_not_lexAny29 N hk ht1 hdG4 hb0h0 hnf
  have r12 := fb_of_not_lexAny29 N (by linarith) h035 h234 h346 h356
    hF0123F hF0124F hM0124F hF0134F hM0134F hF0234F hM0234F hF1234F hM1234F hnf
  have hP4 : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp [P4C_sp]; linarith [N.hF4]
  have hP5 : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := by dsimp [P5C_sp]; linarith [N.hF5]
  exact cert_FB_CQ34_false N.ha0 hk N.hb2 N.hs ht1 hh2 hh0 hP4 hP5 N.hDD hG4 hU4
    hm21 (sub_pos.mpr N.hst) hG55 q20 q24 r21 r23 r12

end DBLeaves

end Minimality.NF29
