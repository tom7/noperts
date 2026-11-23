module

public import Minimality.SVCCells
public import Minimality.SilS0XD
public import Minimality.Type29Hole

@[expose] public section

/-!
# Type 29: the dominant SIGCHECK29 line pair F012xF015 + F124xF234 (PAIRLEAN29)

On the hole census (hl29 shapes) every closure of this line pair at the level of actual circuit
signs is already a SINGLE-view closure (no Gram coupling needed): the edge view `x 0 - x 1`
(line F012xF015) or the edge view `x 2 - x 4` (line F124xF234), each with one 5-point circuit
that is not facet-forced. Each circuit is stated as a determinant-sign hypothesis (two points on
the same / opposite sides of a plane through three vertices); in the normal form `NF29` they are
`a2 < 0` and `0 < b0`, i.e. the K1a sign pattern.

* `lexAny_e01`: facings `F234 -`, `F356 -` at `x 0 - x 1`, `Sep123_05`, distinct depths of
  `0, 1, 2, 3, 5` at `x 0 - x 1`  =>  `Gen.LexAny`.
* `lexAny_e24`: facings `F015 -`, `F035 -` at `x 2 - x 4`, `Sep013_24`, distinct depths of
  `0, 1, 2, 3, 4` at `x 2 - x 4`  =>  `Gen.LexAny`.
* `lexAny29_K1a_e01`, `lexAny29_K1a_e24`: the same for `s0x_fac29 N.facets` with the circuit
  hypothesis replaced by `N.a2 < 0` resp. `0 < N.b0`, conclusion `LexAny29`.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC

namespace Minimality.PL29

/-! ### Generic helpers -/

/-- The facets of type 29 separate the vertices, so the vertices are distinct. -/
theorem inj29 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) : Function.Injective x := by
  intro i j h
  by_contra hne
  have key : ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 9, i ∈ s0x_S29 t ∧ j ∉ s0x_S29 t := by decide
  obtain ⟨t, hi, hj⟩ := key i j hne
  have h1 := F.zero t i hi
  have h2 := F.neg t j hj
  rw [h] at h1; linarith

/-- An affine dependency evaluated on the affine function `det3 u v (· - z)`. -/
theorem det3_dep_sum {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (u v z : ℝ³) :
    ∑ i, mu i * det3 u v (y i - z) = 0 := by
  have h1 : ∀ i, mu i * det3 u v (y i - z) =
      mu i * ⟪cross u v, y i⟫ - mu i * ⟪cross u v, z⟫ := by
    intro i; simp only [det3, inner_sub_right]; ring
  simp only [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  have := congrArg (fun w => ⟪cross u v, w⟫) hdep
  simp only [inner_sum, real_inner_smul_right, inner_zero_right] at this
  exact this

/-- Plane relation: all weighted points but `i`, `j` on the plane `det3 u v (· - z) = 0`. -/
theorem plane_rel {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (u v z : ℝ³) {i j : Fin p} (hij : i ≠ j)
    (hon : ∀ l, l ≠ i → l ≠ j → det3 u v (y l - z) = 0) :
    mu i * det3 u v (y i - z) + mu j * det3 u v (y j - z) = 0 := by
  have h := det3_dep_sum y mu hsum hdep u v z
  rwa [Fintype.sum_eq_add i j hij (fun l hl => by rw [hon l hl.1 hl.2, mul_zero])] at h

theorem sign_rel_same {a b ga gb : ℝ} (h : a * ga + b * gb = 0) (hg : 0 < ga * gb) :
    SignType.sign a = -SignType.sign b := by
  have hgb : gb ≠ 0 := by rintro rfl; simp at hg
  have hsq : 0 < gb ^ 2 := by positivity
  have e : a * (ga * gb) = -(b * gb ^ 2) := by linear_combination gb * h
  have h1 : SignType.sign (a * (ga * gb)) = SignType.sign a := by
    rw [sign_mul, sign_pos hg, mul_one]
  have h2 : SignType.sign (-(b * gb ^ 2)) = -SignType.sign b := by
    rw [Left.sign_neg, sign_mul, sign_pos hsq, mul_one]
  rw [← h1, e, h2]

theorem sign_rel_opp {a b ga gb : ℝ} (h : a * ga + b * gb = 0) (hg : ga * gb < 0) :
    SignType.sign a = SignType.sign b := by
  have hgb : gb ≠ 0 := by rintro rfl; simp at hg
  have hsq : 0 < gb ^ 2 := by positivity
  have e : a * (ga * gb) = -(b * gb ^ 2) := by linear_combination gb * h
  have h1 : SignType.sign (a * (ga * gb)) = -SignType.sign a := by
    rw [sign_mul, sign_neg hg]; cases SignType.sign a <;> rfl
  have h2 : SignType.sign (-(b * gb ^ 2)) = -SignType.sign b := by
    rw [Left.sign_neg, sign_mul, sign_pos hsq, mul_one]
  have := h1.symm.trans (e ▸ h2)
  rw [neg_inj] at this
  exact this

theorem sgn_cases : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a * b = 1 ∨ a * b = -1 := by decide

/-- A nonzero dependency whose signs are `s` up to a common sign gives one with signs `s`. -/
theorem dep_normalize {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (hne : ∃ i, mu i ≠ 0) (s : Fin p → SignType) (k : Fin p)
    (hk : s k ≠ 0) (hrel : ∀ i, SignType.sign (mu i) = s i * s k * SignType.sign (mu k)) :
    ∃ mu' : Fin p → ℝ, ∑ i, mu' i = 0 ∧ ∑ i, mu' i • y i = 0 ∧
      ∀ i, SignType.sign (mu' i) = s i := by
  obtain ⟨i0, hi0⟩ := hne
  have hσ0 : SignType.sign (mu k) ≠ 0 := by
    intro h0; apply hi0; have := hrel i0; rw [h0, mul_zero] at this
    exact sign_eq_zero_iff.mp this
  rcases sgn_cases _ _ hk hσ0 with hc | hc
  · exact ⟨mu, hsum, hdep, fun i => by rw [hrel i, mul_assoc, hc, mul_one]⟩
  · refine ⟨fun i => -mu i, by rw [Finset.sum_neg_distrib, hsum, neg_zero],
      by simp only [neg_smul, Finset.sum_neg_distrib, hdep, neg_zero], fun i => ?_⟩
    rw [Left.sign_neg, hrel i, mul_assoc, hc]; cases s i <;> rfl

/-! ### The two circuit hypotheses -/

/-- `x 0` and `x 5` strictly on the same side of the plane through `x 1, x 2, x 3`
(circuit `{0,1,2,3,5}` with signs `0 1 3 +`, `2 5 -`; in `NF29`: `a2 < 0`). -/
def Sep123_05 (x : Fin 7 → ℝ³) : Prop :=
  0 < det3 (x 2 - x 1) (x 3 - x 1) (x 0 - x 1) * det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1)

/-- `x 2` and `x 4` strictly on opposite sides of the plane through `x 0, x 1, x 3`
(circuit `{0,1,2,3,4}` with signs `0 2 4 +`, `1 3 -`; in `NF29`: `0 < b0`). -/
def Sep013_24 (x : Fin 7 → ℝ³) : Prop :=
  det3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) * det3 (x 0 - x 1) (x 3 - x 1) (x 4 - x 1) < 0

def PA : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]
def sA : Fin 5 → SignType := ![1, 1, -1, 1, -1]
def PB : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]
def sB : Fin 5 → SignType := ![1, -1, 1, -1, 1]

theorem depA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) (hS : Sep123_05 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (PA i) = 0 ∧
      ∀ i, SignType.sign (mu i) = sA i := by
  have hP : Function.Injective (fun i => x (PA i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, -, hsum, hdep, hne⟩ := exists_dep PA hP Finset.univ (by simp)
  -- facet relations (012: 3|5, 023: 1|5, 035: 1|2)
  have r34 := facet_pair F PA mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 3 → l ≠ 4 → PA l ∈ s0x_S29 0) l h1 h2))
  have r14 := facet_pair F PA mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 1 → l ≠ 4 → PA l ∈ s0x_S29 2) l h1 h2))
  have r12 := facet_pair F PA mu hsum hdep 3 (i := 1) (j := 2) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 1 → l ≠ 2 → PA l ∈ s0x_S29 3) l h1 h2))
  -- the plane through 1, 2, 3: 0 and 5 on the same side
  have hpl := plane_rel (fun i => x (PA i)) mu hsum hdep (x 2 - x 1) (x 3 - x 1) (x 1)
    (i := 0) (j := 4) (by decide) (by
      intro l h1 h2
      fin_cases l
      · exact absurd rfl h1
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 1 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 2 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 3 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h2)
  have r04 := sign_rel_same hpl hS
  have e0 : SignType.sign (mu 0) = sA 0 * sA 4 * SignType.sign (mu 4) := by
    rw [r04]; cases SignType.sign (mu 4) <;> rfl
  have e1 : SignType.sign (mu 1) = sA 1 * sA 4 * SignType.sign (mu 4) := by
    rw [r14]; cases SignType.sign (mu 4) <;> rfl
  have e2 : SignType.sign (mu 2) = sA 2 * sA 4 * SignType.sign (mu 4) := by
    rw [← neg_neg (SignType.sign (mu 2)), ← r12, r14]; cases SignType.sign (mu 4) <;> rfl
  have e3 : SignType.sign (mu 3) = sA 3 * sA 4 * SignType.sign (mu 4) := by
    rw [r34]; cases SignType.sign (mu 4) <;> rfl
  have e4 : SignType.sign (mu 4) = sA 4 * sA 4 * SignType.sign (mu 4) := by
    cases SignType.sign (mu 4) <;> rfl
  exact dep_normalize _ mu hsum hdep hne sA 4 (by decide)
    (fun i => by fin_cases i <;> assumption)

theorem depB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) (hS : Sep013_24 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (PB i) = 0 ∧
      ∀ i, SignType.sign (mu i) = sB i := by
  have hP : Function.Injective (fun i => x (PB i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, -, hsum, hdep, hne⟩ := exists_dep PB hP Finset.univ (by simp)
  -- facet relations (012: 3|4, 234: 0|1, 124: 0|3)
  have r34 := facet_pair F PB mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 3 → l ≠ 4 → PB l ∈ s0x_S29 0) l h1 h2))
  have r01 := facet_pair F PB mu hsum hdep 6 (i := 0) (j := 1) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 0 → l ≠ 1 → PB l ∈ s0x_S29 6) l h1 h2))
  have r03 := facet_pair F PB mu hsum hdep 4 (i := 0) (j := 3) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 0 → l ≠ 3 → PB l ∈ s0x_S29 4) l h1 h2))
  -- the plane through 0, 1, 3: 2 and 4 on opposite sides
  have hpl := plane_rel (fun i => x (PB i)) mu hsum hdep (x 0 - x 1) (x 3 - x 1) (x 1)
    (i := 2) (j := 4) (by decide) (by
      intro l h1 h2
      fin_cases l
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 0 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 1 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h1
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 3 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h2)
  have r24 := sign_rel_opp hpl hS
  have e3 : SignType.sign (mu 3) = sB 3 * sB 4 * SignType.sign (mu 4) := by
    rw [r34]; cases SignType.sign (mu 4) <;> rfl
  have e0 : SignType.sign (mu 0) = sB 0 * sB 4 * SignType.sign (mu 4) := by
    rw [r03, r34]; cases SignType.sign (mu 4) <;> rfl
  have e1 : SignType.sign (mu 1) = sB 1 * sB 4 * SignType.sign (mu 4) := by
    rw [← neg_neg (SignType.sign (mu 1)), ← r01, r03, r34]
    cases SignType.sign (mu 4) <;> rfl
  have e2 : SignType.sign (mu 2) = sB 2 * sB 4 * SignType.sign (mu 4) := by
    rw [r24]; cases SignType.sign (mu 4) <;> rfl
  have e4 : SignType.sign (mu 4) = sB 4 * sB 4 * SignType.sign (mu 4) := by
    cases SignType.sign (mu 4) <;> rfl
  exact dep_normalize _ mu hsum hdep hne sB 4 (by decide)
    (fun i => by fin_cases i <;> assumption)

/-! ### View `x 0 - x 1` (line F012xF015, facings `00++--?--`, F346 free) -/

def A_sw : Fin 9 → SignType := ![0, 0, 1, 1, -1, -1, -1, -1, -1]
def A_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 2, 3, 4], U := {2, 3}, Dn := {0, 1, 6, 8},
     sd := ![-1, -1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 5, c := ![0, 1, 2, 3, 4], U := {0, 2, 3}, Dn := {1, 4, 6, 8},
     sd := ![1, -1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 5, c := ![0, 1, 4, 3, 2], U := {1, 2, 3}, Dn := {0, 5, 6, 8},
     sd := ![-1, 1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![1, 1, 0, 0, 0, 0, 0, 0, 0] }]
def A_D : List (Fin 5 → SignType) := [sA]

theorem A_check : SVC.check s0x_S29 PA A_sw [(0, 1)] A_D A_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 1`** (the F012xF015 half of the dominant pair). -/
theorem lexAny_e01 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h234 : ⟪F.N 6, x 0 - x 1⟫ < 0) (h356 : ⟪F.N 8, x 0 - x 1⟫ < 0) (hS : Sep123_05 x)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 1⟫ = A_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg h356
  have hP : ∀ i, PA i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective PA := by decide
  refine svc_local F PA (x 0 - x 1) A_sw A_R hsw
    (hR_two F A_sw A_R 0 1 0 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [(0, 1)] ?_ A_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) A_check
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [A_D, List.mem_singleton] at hs
    subst hs
    exact depA F hS

/-! ### View `x 2 - x 4` (line F124xF234, facings `+-+-0-0-?`, F356 free) -/

def B_sw : Fin 9 → SignType := ![1, -1, 1, -1, 0, -1, 0, -1, -1]
def B_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 2, 3], U := {0, 2}, Dn := {1, 3, 4, 6},
     sd := ![0, 0, 0, 0, -1, 0, -1, 0, 0] },
   { k := 5, c := ![0, 1, 4, 2, 3], U := {0, 2, 4}, Dn := {1, 3, 5, 6},
     sd := ![0, 0, 0, 0, 1, 0, -1, 0, 0] },
   { k := 5, c := ![0, 1, 2, 4, 3], U := {0, 2, 6}, Dn := {1, 3, 4, 7},
     sd := ![0, 0, 0, 0, -1, 0, 1, 0, 0] },
   { k := 4, c := ![0, 1, 4, 3], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, 0, 0, 0, 1, 0, 1, 0, 0] }]
def B_D : List (Fin 5 → SignType) := [sB]

theorem B_check : SVC.check s0x_S29 PB B_sw [(2, 4)] B_D B_R = true := by
  decide +kernel

/-- **Single view `x 2 - x 4`** (the F124xF234 half of the dominant pair). -/
theorem lexAny_e24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : ⟪F.N 1, x 2 - x 4⟫ < 0) (h035 : ⟪F.N 3, x 2 - x 4⟫ < 0) (hS : Sep013_24 x)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 4⟫ = B_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_neg h015
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_neg h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
  have hP : ∀ i, PB i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective PB := by decide
  refine svc_local F PB (x 2 - x 4) B_sw B_R hsw
    (hR_two F B_sw B_R 4 6 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [(2, 4)] ?_ B_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) B_check
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [B_D, List.mem_singleton] at hs
    subst hs
    exact depB F hS

/-! ### In the normal form: the circuit hypotheses are the K1a signs -/

theorem sep123_05_of_nf {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) : Sep123_05 x := by
  have e1 : det3 (x 2 - x 1) (x 3 - x 1) (x 0 - x 1) =
      -(N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x2, N.x3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have e2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) = N.a2 * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x1, N.x2, N.x3, N.x5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have hD := N.hD
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 := by positivity
  unfold Sep123_05
  rw [e1, e2, show -(N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ *
      (N.a2 * det3 N.E₁ N.E₂ N.E₃) =
      (-(N.a0 * N.b2 - N.a2 * N.b0) * N.a2) * det3 N.E₁ N.E₂ N.E₃ ^ 2 by ring]
  exact mul_pos (by nlinarith [N.hDD]) hD2

theorem sep013_24_of_nf {x : Fin 7 → ℝ³} (N : NF29 x) (hb0 : 0 < N.b0) : Sep013_24 x := by
  have e1 : det3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) =
      (N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x2, N.x3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have e2 : det3 (x 0 - x 1) (x 3 - x 1) (x 4 - x 1) = -N.b0 * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x3, N.x4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have hD := N.hD
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 := by positivity
  unfold Sep013_24
  rw [e1, e2, show (N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ *
      (-N.b0 * det3 N.E₁ N.E₂ N.E₃) =
      (-((N.a0 * N.b2 - N.a2 * N.b0) * N.b0)) * det3 N.E₁ N.E₂ N.E₃ ^ 2 by ring]
  have : 0 < (N.a0 * N.b2 - N.a2 * N.b0) * N.b0 := mul_pos N.hDD hb0
  nlinarith

/-- **K1a, view `x 0 - x 1`.** -/
theorem lexAny29_K1a_e01 {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0)
    (h234 : ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0)
    (h356 : ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e01 _ h234 h356 (sep123_05_of_nf N ha2) hgen

/-- **K1a, view `x 2 - x 4`.** -/
theorem lexAny29_K1a_e24 {x : Fin 7 → ℝ³} (N : NF29 x) (hb0 : 0 < N.b0)
    (h015 : ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0)
    (h035 : ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e24 _ h015 h035 (sep013_24_of_nf N hb0) hgen

/-- **Hole exclusion.** On `Hole29` in class K1a, neither single view of the dominant pair has
the facings of `lexAny_e01` / `lexAny_e24` with distinct depths. -/
theorem hole29_K1a_not_e01_e24 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Minimality.H29.Hole29 x N)
    (hK1a : N.a2 < 0 ∧ 0 < N.b0) :
    ¬ ((⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0 ∧
        ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
          i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∨
      (⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0 ∧
        ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
          i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫)) := by
  have hnl := h.2.2.2.2.2.1
  rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
  · exact hnl (lexAny29_K1a_e01 N hK1a.1 a b c)
  · exact hnl (lexAny29_K1a_e24 N hK1a.2 a b c)

end Minimality.PL29
