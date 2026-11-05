module

public import MinimalityExtra

/-!
# The chirotope does not determine the silhouette: proof (Result B)

The witness is found by `witness.py` (small integer points, verified by `verify_witness.py`).
The sign equalities are checked by brute force over all index quadruples in `Fin 5`.
-/

@[expose] public section

namespace MinimalityExtra

open Matrix

/-- Integer witness configuration `x` (five points in `ℝ³`). -/
def chiWitnessX : Fin 5 → Fin 3 → ℝ :=
  ![![1, 0, 1], ![1, -2, -2], ![0, 1, 0], ![1, -1, 0], ![-2, 0, 2]]

/-- Integer witness configuration `y`, with the same chirotope as `chiWitnessX`. -/
def chiWitnessY : Fin 5 → Fin 3 → ℝ :=
  ![![0, -1, -1], ![0, -1, 2], ![-1, 0, 0], ![2, 0, 1], ![-1, 2, 0]]

/-- Two reals with the same positivity and the same negativity have the same sign. -/
theorem sign_eq_of_iff_pos_neg {a b : ℝ} (h1 : 0 < a ↔ 0 < b) (h2 : a < 0 ↔ b < 0) :
    SignType.sign a = SignType.sign b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hb : b < 0 := h2.1 ha
    rw [sign_neg ha, sign_neg hb]
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have := h2.2 hb
      linarith
    · simp [ha, hb]
    · have := h1.2 hb
      linarith
  · have hb : 0 < b := h1.1 ha
    rw [sign_pos ha, sign_pos hb]

set_option maxHeartbeats 4000000 in
theorem chiWitnessX_generic : ChirotopeGeneric chiWitnessX := by
  intro i j k l hij hik hil hjk hjl hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hil
    | exact absurd rfl hjk | exact absurd rfl hjl | exact absurd rfl hkl
    | norm_num [tripleProduct, chiWitnessX]

set_option maxHeartbeats 4000000 in
theorem chiWitnessY_generic : ChirotopeGeneric chiWitnessY := by
  intro i j k l hij hik hil hjk hjl hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hil
    | exact absurd rfl hjk | exact absurd rfl hjl | exact absurd rfl hkl
    | norm_num [tripleProduct, chiWitnessY]

set_option maxHeartbeats 4000000 in
theorem chiWitness_same : SameChirotope chiWitnessX chiWitnessY := by
  intro i j k l
  apply sign_eq_of_iff_pos_neg <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tripleProduct, chiWitnessX, chiWitnessY]

/-- The chirotope does not determine the silhouette (see the statement in `Statements.lean`). -/
theorem chirotopeDoesNotDetermineSilhouette : ChirotopeDoesNotDetermineSilhouette := by
  refine ⟨chiWitnessX, chiWitnessY, chiWitnessX_generic, chiWitnessY_generic, chiWitness_same,
    0, 2, by decide, by decide, by decide, ?_, ?_⟩
  · intro m hm0 hm2 hm4
    fin_cases m
    all_goals first
      | exact absurd rfl hm0 | exact absurd rfl hm2 | exact absurd rfl hm4
      | norm_num [tripleProduct, chiWitnessX]
  · intro h
    have := h 1 (by decide) (by decide) (by decide)
    norm_num [tripleProduct, chiWitnessY] at this

end MinimalityExtra

#print axioms MinimalityExtra.chirotopeDoesNotDetermineSilhouette
