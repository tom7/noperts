module

public import Minimality.CaseC18Sp
public import Minimality.CaseC09Rims

@[expose] public section

/-!
# Type 18, acute case (c): PROOFS section 36 (Theorems M, M', R, Lemma LV)

Theorems M, M', R, Lemma LV, the sector tests and the assembly.  Plan, templates and risks: `nopert229/out/bottleneck/sp18b/handoff_lean.md`.  Paper:
`FEWER-FACES-PROOFS.md` "## 36." (referee fixes at its top override the text).

The special set `CaseC18Special'` (five disjuncts: codim-3 R1' residual, `L_M'` and its
`Z`-image, the codim-4 corners and their `Z`-image) and `Frame18.isRupert_of_not_special'`
(replacing the section 35 versions that were in `CaseC18Sp`).  All groups are proved.

View `u0 = m1- = (tm, 0, -hm)` in frame coordinates; screen map `(x, y, z) -> (y, hm x + tm z)`;
tilt `d` with `P = d.y`, `Q = hm d.x + tm d.z`; rim points `ptC`: m1+ 0, m2+ 1, m2- 2, xa 3, xb 4,
v 5, m1- 6.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-! ### Group A: infrastructure (robust depth predicate, 6-cycles are plain `ZMod 6 = Fin 6`) -/

/-- Robust unimodality as an *open* condition: every sufficiently close injective perturbation is
unimodal.  Open, positively homogeneous, shift invariant. -/
def QRob {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  ∃ δ > 0, ∀ z' : ZMod k → ℝ, (∀ i, |z' i - z i| < δ) → Function.Injective z' →
    IsCyclicUnimodal z'

theorem sup_lt_iff_aux {k : ℕ} [NeZero k] (z z' : ZMod k → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∀ i, |z' i - z i| < δ) ↔ dist z' z < δ := by
  rw [dist_pi_lt_iff hδ]; simp [Real.dist_eq]

theorem QRob_open {k : ℕ} [NeZero k] : IsOpen {z : ZMod k → ℝ | QRob z} := by
  rw [Metric.isOpen_iff]
  rintro z ⟨δ, hδ, h⟩
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [Metric.mem_ball] at hy
  refine ⟨δ - dist y z, by linarith, fun z' hz' hinj => h z' (fun i => ?_) hinj⟩
  have h1 := hz' i
  have h2 : |y i - z i| ≤ dist y z := by
    have := dist_le_pi_dist y z i
    rwa [Real.dist_eq] at this
  calc |z' i - z i| = |(z' i - y i) + (y i - z i)| := by ring_nf
    _ ≤ |z' i - y i| + |y i - z i| := abs_add_le _ _
    _ < δ := by linarith

theorem IsCyclicUnimodal.comp_strictMono_aux {k : ℕ} [NeZero k] {w : ZMod k → ℝ}
    (hw : IsCyclicUnimodal w) {f : ℝ → ℝ} (hf : StrictMono f) :
    IsCyclicUnimodal (fun i => f (w i)) := by
  refine ⟨hf.injective.comp hw.1, ?_⟩
  rw [← hw.2]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [hf.lt_iff_lt]

theorem QRob_smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {a : ℝ} (ha : 0 < a) (h : QRob z) :
    QRob fun i => a * z i := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨a * δ, mul_pos ha hδ, fun z' hz' hinj => ?_⟩
  have hu := h (fun i => z' i / a) (fun i => by
    have := hz' i
    have e : z' i / a - z i = (z' i - a * z i) / a := by field_simp
    rw [e, abs_div, abs_of_pos ha, div_lt_iff₀ ha]; linarith)
    (fun i j hij => hinj (by
      have := congrArg (· * a) hij
      simpa [div_mul_cancel₀ _ ha.ne'] using this))
  have := IsCyclicUnimodal.comp_strictMono_aux hu (f := fun y => a * y)
    (fun x y hxy => by simpa using mul_lt_mul_of_pos_left hxy ha)
  have e : (fun i => a * (z' i / a)) = z' := by funext i; field_simp
  rw [e] at this; exact this

theorem QRob_shift {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (a : ℝ) (h : QRob z) : QRob fun i => z i + a := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun z' hz' hinj => ?_⟩
  have hu := h (fun i => z' i - a) (fun i => by
      have := hz' i
      have e : z' i - a - z i = z' i - (z i + a) := by ring
      show |z' i - a - z i| < δ
      rw [e]; exact this)
    (fun i j hij => hinj (by simpa using hij))
  have := IsCyclicUnimodal.comp_strictMono_aux hu (f := fun y => y + a) (fun x y hxy => by simpa using hxy)
  have e : (fun i => z' i - a + a) = z' := by funext i; ring
  rw [e] at this; exact this

theorem QRob_unimodal {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hinj : Function.Injective z) (h : QRob z) :
    IsCyclicUnimodal z := by
  obtain ⟨δ, hδ, h⟩ := h
  exact h z (fun i => by simpa using hδ) hinj

theorem rob_levelL {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    {P0 P1 P2 P3 : ZMod k}
    (hP : ∃ (B : ZMod k) (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧ d < k ∧
      P0 = B + a ∧ P1 = B + b ∧ P2 = B + c ∧ P3 = B + d)
    (heq : z P1 = z P2)
    (h : (z P0 ≤ z P1 ∧ z P2 ≤ z P3) ∨ (z P1 ≤ z P0 ∧ z P3 ≤ z P2)) : False := by
  obtain ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ := hP
  have n01 : B + (a : ZMod k) ≠ B + b := zmod_add_ne (by omega) (by omega) hab.ne B
  have n02 : B + (a : ZMod k) ≠ B + c := zmod_add_ne (by omega) (by omega) (by omega) B
  have n12 : B + (b : ZMod k) ≠ B + c := zmod_add_ne (by omega) (by omega) hbc.ne B
  have n13 : B + (b : ZMod k) ≠ B + d := zmod_add_ne (by omega) (by omega) (by omega) B
  have n23 : B + (c : ZMod k) ≠ B + d := zmod_add_ne (by omega) (by omega) hcd.ne B
  have R3 := hz.noLevelRun B a b c d hab hbc hcd hdk heq
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact R3.1 ⟨h1, h2⟩
      · exact hz.noTriple _ _ _ n12 n23 n13 heq h2
    · exact hz.noTriple _ _ _ n01 n12 n02 h1 heq
  · rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact R3.2 ⟨h1, h2⟩
      · exact hz.noTriple _ _ _ n12 n23 n13 heq h2.symm
    · exact hz.noTriple _ _ _ n01 n12 n02 h1.symm heq

theorem rob_quad_rot {k : ℕ} [NeZero k] {P0 P1 P2 P3 : ZMod k}
    (hP : ∃ (B : ZMod k) (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧ d < k ∧
      P0 = B + a ∧ P1 = B + b ∧ P2 = B + c ∧ P3 = B + d) :
    ∃ (B : ZMod k) (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧ d < k ∧
      P1 = B + a ∧ P2 = B + b ∧ P3 = B + c ∧ P0 = B + d := by
  obtain ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ := hP
  refine ⟨B + b, 0, c - b, d - b, k - b + a, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · simp
  · exact (zmod_add_natCast_sub B hbc.le).symm
  · exact (zmod_add_natCast_sub B (hbc.trans hcd).le).symm
  · exact (zmod_add_natCast_wrap B hab (by omega)).symm

/-- Four positions in cyclic order cannot have both "low" ones weakly below both "high" ones. -/
theorem rob_weak4 {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    {P0 P1 P2 P3 : ZMod k}
    (hP : ∃ (B : ZMod k) (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧ d < k ∧
      P0 = B + a ∧ P1 = B + b ∧ P2 = B + c ∧ P3 = B + d)
    (h10 : z P1 ≤ z P0) (h12 : z P1 ≤ z P2) (h30 : z P3 ≤ z P0) (h32 : z P3 ≤ z P2) : False := by
  have hP1 := rob_quad_rot hP
  have hP2 := rob_quad_rot hP1
  have hP3 := rob_quad_rot hP2
  by_cases hs : z P1 < z P0 ∧ z P1 < z P2 ∧ z P3 < z P0 ∧ z P3 < z P2
  · obtain ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ := hP
    exact hz.noPeaks B a b c d hab hbc hcd hdk hs
  · rcases h10.lt_or_eq with e1 | e1
    · rcases h12.lt_or_eq with e2 | e2
      · rcases h30.lt_or_eq with e3 | e3
        · rcases h32.lt_or_eq with e4 | e4
          · exact hs ⟨e1, e2, e3, e4⟩
          · exact rob_levelL hz hP1 e4.symm (Or.inl ⟨h12, h30⟩)
        · exact rob_levelL hz hP2 e3 (Or.inr ⟨h32, h10⟩) 
      · exact rob_levelL hz hP e2 (Or.inr ⟨h10, h32⟩)
    · exact rob_levelL hz hP3 e1.symm (Or.inl ⟨h30, h12⟩)

/-- The combinatorial core (PROOFS section 18.0, converse direction): (R1)-(R3) imply that all small
injective perturbations are unimodal.  The hypothesis `2 ≤ k` was added to the skeleton statement
(for `k = 1` the statement is false: `IsRobustUnimodal` holds trivially but a one-point cycle has no
local maximum). -/
theorem QRob_of_robust {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (h : IsRobustUnimodal z) : QRob z := by
  have hS : IsOpen {z' : ZMod k → ℝ | ∀ x y, z y < z x → z' y < z' x} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun y => ?_
    by_cases hlt : z y < z x
    · simp only [hlt, Set.iInter_true]
      exact isOpen_lt (continuous_apply y) (continuous_apply x)
    · simp [hlt]
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hS z (fun x y h => h)
  refine ⟨δ, hδ, fun z' hz' hinj => ?_⟩
  have hmem := hb (Metric.mem_ball.2 ((sup_lt_iff_aux z z' hδ).1 hz'))
  have hw : ∀ x y, z' x < z' y → z x ≤ z y := fun x y hxy => by
    by_contra hc
    have := hmem x y (not_le.1 hc)
    linarith
  refine isCyclicUnimodal_of_atMostOne hk hinj fun i j hi hj => ?_
  by_contra hne
  set m := (j - i).val with hm
  have hjm : j = i + (m : ZMod k) := by rw [hm, ZMod.natCast_zmod_val]; ring
  have hm0 : 0 < m := ZMod.val_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hmk : m < k := ZMod.val_lt _
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have h1 : m = 1 := by omega
    rw [h1] at hjm
    simp only [Nat.cast_one] at hjm
    have h2 : j - 1 = i := by rw [hjm]; ring
    rw [h2] at hj
    rw [← hjm] at hi
    linarith [hi.2, hj.1]
  have hm3 : m + 2 ≤ k := by
    by_contra hlt
    have h1 : m = k - 1 := by omega
    have hj1 : j + 1 = i := by
      rw [hjm, h1, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    have h2 : i - 1 = j := by rw [← hj1]; ring
    rw [hj1] at hj
    rw [h2] at hi
    linarith [hi.1, hj.2]
  obtain ⟨b, hbm, hbmin⟩ := Finset.exists_min_image (Finset.Icc 1 (m - 1))
    (fun n : ℕ => z' (i + (n : ZMod k))) ⟨1, by simp; omega⟩
  obtain ⟨d, hdm, hdmin⟩ := Finset.exists_min_image (Finset.Icc (m + 1) (k - 1))
    (fun n : ℕ => z' (i + (n : ZMod k))) ⟨m + 1, by simp; omega⟩
  rw [Finset.mem_Icc] at hbm hdm
  have e1 : z' (i + (b : ZMod k)) ≤ z' (i + 1) := by
    have := hbmin 1 (by simp; omega)
    simpa using this
  have e2 : z' (i + (b : ZMod k)) ≤ z' (j - 1) := by
    have := hbmin (m - 1) (by simp; omega)
    have h3 : i + ((m - 1 : ℕ) : ZMod k) = j - 1 := by
      rw [Nat.cast_sub (by omega), hjm]; simp; ring
    simpa [h3] using this
  have e3 : z' (i + (d : ZMod k)) ≤ z' (j + 1) := by
    have h3 : i + ((m + 1 : ℕ) : ZMod k) = j + 1 := by
      rw [Nat.cast_add, hjm]; simp; ring
    calc z' (i + (d : ZMod k)) ≤ z' (i + ((m + 1 : ℕ) : ZMod k)) := hdmin (m + 1) (by simp; omega)
      _ = z' (j + 1) := by rw [h3]
  have e4 : z' (i + (d : ZMod k)) ≤ z' (i - 1) := by
    have := hdmin (k - 1) (by simp; omega)
    have h3 : i + ((k - 1 : ℕ) : ZMod k) = i - 1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    simpa [h3] using this
  refine rob_weak4 h (P0 := i) (P1 := i + b) (P2 := j) (P3 := i + d)
    ⟨i, 0, b, m, d, by omega, by omega, by omega, by omega, by simp, rfl, hjm, rfl⟩
    (hw _ _ (lt_of_le_of_lt e1 hi.2)) (hw _ _ (lt_of_le_of_lt e2 hj.1))
    (hw _ _ (lt_of_le_of_lt e4 hi.1)) (hw _ _ (lt_of_le_of_lt e3 hj.2))


namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- `rupert_rim` with a *robustly unimodal* limit depth cycle: no depth predicate, no tilt-tie
bookkeeping (the tilt enters only through the determinant tests `ST`). -/
theorem rupert_rim_rob {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (hz : IsRobustUnimodal fun i => F.GG (F.ptC (c i)) u) :
    IsRupert (Finset.univ.image x) := by
  refine F.rupert_rim hk c σ hσ u v hu hcyc hrest QRob QRob_open (fun z a ha => QRob_smul ha)
    (fun z a => QRob_shift a) ?_ (fun z hz hq => QRob_unimodal hz hq)
  have hQ : QRob fun i => F.GG (F.ptC (c i)) u := QRob_of_robust (by omega) hz
  have hcont : Continuous fun s : ℝ =>
      (fun i : ZMod k => F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v) := by
    refine continuous_pi fun i => ?_
    fun_prop
  have h0 : (0 : ℝ) ∈ (fun s : ℝ => (fun i : ZMod k => F.GG (F.ptC (c i)) u +
      s * F.GG (F.ptC (c i)) v)) ⁻¹' {z | QRob z} := by
    simpa using hQ
  exact nhdsWithin_le_nhds ((QRob_open.preimage hcont).mem_nhds h0)

end Frame7

/-! Pure real lemmas: the robust cycles of the sectors (checked on all weak orders, `rob.cc`).
Proved by exhaustive case analysis (`interval_cases` on the four positions, `linarith`). -/

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycC {R Z2 X Z1 T : ℝ} (hXT : X < T) (hZ1 : Z1 < T) (hR : min Z2 T < R)
    (h : X < Z2 ∨ (Z2 = X ∧ X < Z1)) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![R, Z2, X, Z1, T] i) := by
  rw [min_lt_iff] at hR
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> rcases h with h | ⟨h1, h2⟩ <;> rcases hR with hR | hR <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> rcases h with h | ⟨h1, h2⟩ <;> rcases hR with hR | hR <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> rcases h with h | ⟨h1, h2⟩ <;> rcases hR with hR | hR <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycCp {R Z2 X Zp Z1 T : ℝ} (hXT : X < T) (hZ1 : Z1 < T) (hZp : Zp < X)
    (hR : min Z2 T < R) (h : X < Z2) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![R, Z2, X, Zp, Z1, T] i) := by
  rw [min_lt_iff] at hR
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> rcases hR with hR | hR <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> rcases hR with hR | hR <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> rcases hR with hR | hR <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycBp {V Z2 X T Z1 : ℝ} (h1 : V < Z2) (h2 : Z2 < X) (h3 : X < T) (h4 : Z1 < T) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![V, Z2, X, T, Z1] i) := by
  skip
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
theorem robust_cycS2 {V Z2 T Z1 : ℝ} (h1 : V < Z2) (h2 : Z2 < T) (h4 : Z1 < T) :
    IsRobustUnimodal (k := 5) (fun i : ZMod 5 => ![V, Z2, T, T, Z1] i) := by
  skip
  have hB : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> skip <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> skip <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> skip <;> constructor <;> intro hh <;> linarith


def Q5s (z : ZMod 5 → ℝ) : Prop := z 1 < z 0 ∧ z 2 < z 0 ∧ z 3 < z 4 ∧ z 2 < z 4 ∧ z 2 < z 3

theorem Q5s_open : IsOpen {z : ZMod 5 → ℝ | Q5s z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5s, Set.ofPred_and]
  exact (hlt 1 0).inter ((hlt 2 0).inter ((hlt 3 4).inter ((hlt 2 4).inter (hlt 2 3))))

theorem Q5s_smul {z : ZMod 5 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q5s z) : Q5s fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha, mul_lt_mul_of_pos_left h5 ha⟩

theorem Q5s_shift {z : ZMod 5 → ℝ} (a : ℝ) (h : Q5s z) : Q5s fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem Q5s_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5s z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have h04 : z 0 ≠ z 4 := hinj.ne (by decide)
  rcases lt_or_gt_of_ne h04 with h6 | h6
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 4 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; rw [b0]; exact h6
    · left; rw [b1]; exact h1
    · right; rw [a2]; exact h5
    · right; rw [a3]; exact h3
    · exact absurd rfl hi
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 0 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [b1]; exact h1
    · right; rw [a2]; exact h5
    · right; rw [a3]; exact h3
    · right; rw [a4]; exact h6

theorem Q5s_eventually {z w : ZMod 5 → ℝ}
    (h1 : z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) (h2 : z 2 < z 0 ∨ (z 2 = z 0 ∧ w 2 < w 0))
    (h3 : z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4)) (h4 : z 2 < z 4 ∨ (z 2 = z 4 ∧ w 2 < w 4))
    (h5 : z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5s fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h2, ev_lt h3, ev_lt h4, ev_lt h5] with s a b c d e
  exact ⟨a, b, c, d, e⟩

def Q6m (z : ZMod 6 → ℝ) : Prop :=
  z 2 < z 1 ∧ z 2 < z 3 ∧ z 3 < z 4 ∧ z 4 < z 5 ∧ z 5 < z 0

theorem Q6m_open : IsOpen {z : ZMod 6 → ℝ | Q6m z} := by
  have hlt : ∀ i j : ZMod 6, IsOpen {z : ZMod 6 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q6m, Set.ofPred_and]
  exact (hlt 2 1).inter ((hlt 2 3).inter ((hlt 3 4).inter ((hlt 4 5).inter (hlt 5 0))))

theorem Q6m_smul {z : ZMod 6 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q6m z) : Q6m fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha, mul_lt_mul_of_pos_left h5 ha⟩

theorem Q6m_shift {z : ZMod 6 → ℝ} (a : ℝ) (h : Q6m z) : Q6m fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem zmod6_add_one : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

theorem zmod6_sub_one : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

theorem Q6m_unimodal {z : ZMod 6 → ℝ} (hinj : Function.Injective z) (h : Q6m z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : ∀ i : ZMod 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := zmod6_add_one
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_sub_one
  have h01 : z 0 ≠ z 1 := hinj.ne (by decide)
  rcases lt_or_gt_of_ne h01 with h6 | h6
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 1 ?_
    intro i hi
    rcases hc i with rfl | rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h6
    · exact absurd rfl hi
    · right; rw [a2]; exact h2
    · right; rw [a3]; exact h3
    · right; rw [a4]; exact h4
    · right; rw [a5]; exact h5
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 0 ?_
    intro i hi
    rcases hc i with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [b1]; exact h6
    · right; rw [a2]; exact h2
    · right; rw [a3]; exact h3
    · right; rw [a4]; exact h4
    · right; rw [a5]; exact h5

theorem Q6m_eventually {z w : ZMod 6 → ℝ}
    (h1 : z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1)) (h2 : z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3))
    (h3 : z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4)) (h4 : z 4 < z 5 ∨ (z 4 = z 5 ∧ w 4 < w 5))
    (h5 : z 5 < z 0 ∨ (z 5 = z 0 ∧ w 5 < w 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q6m fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h2, ev_lt h3, ev_lt h4, ev_lt h5] with s a b c d e
  exact ⟨a, b, c, d, e⟩


/-! ### Group A2: the depths at `u0 = m1-` and Lemma W -/

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- The depths `GG(·, u0)` of the seven points at `u0 = (tm, 0, -hm)` (v has depth `0`). -/
noncomputable def u0R : ℝ := F.a11 * F.S.tm ^ 2 + F.gg * F.S.hm ^ 2
noncomputable def u0T : ℝ := F.a11 * F.S.tm
noncomputable def u0X : ℝ := F.a12 * F.S.tm
noncomputable def u0Z1 : ℝ := F.a11 * F.S.tp * F.S.tm - F.gg * F.S.hp * F.S.hm
noncomputable def u0Z2 : ℝ := F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km
noncomputable def u0Z2p : ℝ := F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp

/-- `GG` of each point against `u0` (the identification used by every test of this file). -/
theorem GG_u0 :
    F.toFrame7.GG (F.toFrame7.ptC 6) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0R ∧
    F.toFrame7.GG (F.toFrame7.ptC 3) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0T ∧
    F.toFrame7.GG (F.toFrame7.ptC 4) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0X ∧
    F.toFrame7.GG (F.toFrame7.ptC 0) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z1 ∧
    F.toFrame7.GG (F.toFrame7.ptC 2) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z2 ∧
    F.toFrame7.GG (F.toFrame7.ptC 1) ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z2p ∧
    F.toFrame7.GG (F.toFrame7.ptC 5) ⟨F.S.tm, 0, -F.S.hm⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [F.GG_eq, F.ptC_6, u0R]; ring
  · simp only [F.GG_eq, F.ptC_3, u0T]; ring
  · simp only [F.GG_eq, F.ptC_4, u0X]; ring
  · simp only [F.GG_eq, F.ptC_0, u0Z1]; ring
  · simp only [F.GG_eq, F.ptC_2, u0Z2]; ring
  · simp only [F.GG_eq, F.ptC_1, u0Z2p]; ring
  · simp only [F.GG_eq, F.ptC_5]; ring

/-- `Z2 - X = (1 - sm) tm (g am dm - a12)`. -/
theorem u0Z2_sub_X : F.u0Z2 - F.u0X = (1 - F.S.sm) * F.S.tm * (F.gg * F.S.am * F.S.dm - F.a12) := by
  have h1 := F.S.am_mul
  have h2 := F.S.dm_mul
  unfold u0Z2 u0X
  linear_combination (-(F.gg * F.S.km)) * h1 - (F.gg * F.S.am * F.S.tm) * h2

/-- `Z1 - X = tm (a11 tp - g am hp - a12)`. -/
theorem u0Z1_sub_X : F.u0Z1 - F.u0X = F.S.tm * (F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp - F.a12) := by
  have h1 := F.S.am_mul
  unfold u0Z1 u0X
  linear_combination (F.gg * F.S.hp) * h1

theorem u0X_lt_T (hα : F.a12 < F.a11) : F.u0X < F.u0T := by
  unfold u0X u0T
  exact mul_lt_mul_of_pos_right hα F.S.tm_pos

theorem u0Z1_lt_T : F.u0Z1 < F.u0T := by
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have h1 := mul_pos (mul_pos F.g_pos F.S.hp_pos) F.S.hm_pos
  have h2 : F.a11 * F.S.tp * F.S.tm < F.a11 * F.S.tm := by
    have := mul_lt_mul_of_pos_left F.S.tp_lt hA11
    nlinarith [F.S.tm_pos]
  unfold u0Z1 u0T
  linarith

theorem u0Z2_pos : 0 < F.u0Z2 := by
  have hA12 : 0 < F.a12 := F.A12_pos
  have h1 := mul_pos (mul_pos hA12 F.S.tm_pos) F.S.sm_pos
  have h2 := mul_pos (mul_pos F.g_pos F.S.hm_pos) F.S.km_pos
  unfold u0Z2
  linarith

theorem u0Z2p_lt_X : F.u0Z2p < F.u0X := by
  have h1 := mul_pos (mul_pos F.g_pos F.S.hm_pos) F.S.kp_pos
  have h2 : F.a12 * F.S.tm * F.S.sp < F.a12 * F.S.tm := by
    have hA12 : 0 < F.a12 := F.A12_pos
    have := mul_pos hA12 F.S.tm_pos
    nlinarith [F.S.sp_lt]
  unfold u0Z2p u0X
  linarith

/-- **Lemma W** (the roof at `u0`): `Z2 ≥ X` forces `R > min(Z2, T)` (uses only `dm < bm`). -/
theorem u0_W1 (h : F.u0X ≤ F.u0Z2) : min F.u0Z2 F.u0T < F.u0R := by
  by_contra hc
  rw [not_lt, le_min_iff] at hc
  obtain ⟨hRZ, hRT⟩ := hc
  have hsub := F.u0Z2_sub_X
  have hpos : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (by linarith [F.S.sm_lt]) F.S.tm_pos
  have hB : F.a12 ≤ F.gg * F.S.am * F.S.dm := by
    have h0 : 0 ≤ (1 - F.S.sm) * F.S.tm * (F.gg * F.S.am * F.S.dm - F.a12) := by
      rw [← hsub]; linarith
    have := nonneg_of_mul_nonneg_right h0 hpos
    linarith
  have h1 := F.S.am_mul
  have h2 := F.S.dm_mul
  have h3 := F.S.bm_mul
  have hroof := F.S.dm_lt_bm
  have ht1 : 0 < 1 - F.S.tm := by linarith [F.S.tm_lt]
  unfold u0R u0Z2 at hRZ
  unfold u0R u0T at hRT
  have e0 := mul_le_mul_of_nonneg_right hB (mul_pos F.S.tm_pos F.S.sm_pos).le
  have e1 : F.a12 * (F.S.tm * F.S.sm) ≤ F.gg * F.S.hm * F.S.dm * F.S.sm := by
    calc F.a12 * (F.S.tm * F.S.sm) ≤ F.gg * F.S.am * F.S.dm * (F.S.tm * F.S.sm) := e0
      _ = F.gg * (F.S.am * F.S.tm) * F.S.dm * F.S.sm := by ring
      _ = F.gg * F.S.hm * F.S.dm * F.S.sm := by rw [h1]
  have e2 : F.gg * F.S.hm * F.S.km = F.gg * F.S.hm * F.S.dm * (1 - F.S.sm) := by
    rw [← h2]; ring
  have hA : F.a11 * F.S.tm ^ 2 + F.gg * F.S.hm ^ 2 ≤ F.gg * F.S.hm * F.S.dm := by
    nlinarith
  have e3 : F.gg * F.S.hm * F.S.dm * (1 - F.S.tm) < F.gg * F.S.hm * F.S.bm * (1 - F.S.tm) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hroof (mul_pos F.g_pos F.S.hm_pos)) ht1
  have e4 : F.gg * F.S.hm * F.S.bm * (1 - F.S.tm) = F.gg * F.S.hm * F.S.hm := by
    calc F.gg * F.S.hm * F.S.bm * (1 - F.S.tm) = F.gg * F.S.hm * (F.S.bm * (1 - F.S.tm)) := by ring
      _ = F.gg * F.S.hm * F.S.hm := by rw [h3]
  have hA' := mul_le_mul_of_nonneg_right hA ht1.le
  have hg : F.gg * F.S.hm ^ 2 ≤ F.a11 * F.S.tm * (1 - F.S.tm) := by nlinarith
  have hg' := mul_le_mul_of_nonneg_left hg F.S.tm_pos.le
  nlinarith

/-- Face `C1` (`a12 = a11`, `X = T`): `ζ- = Z2 - T > 0` forces `R > T`; `ζ- = 0` forces `R > T`. -/
theorem u0_R_gt_T_of_ge (heq : F.a12 = F.a11) (h : F.u0T ≤ F.u0Z2) : F.u0T < F.u0R := by
  have hX : F.u0X = F.u0T := by unfold u0X u0T; rw [heq]
  have := F.u0_W1 (by rw [hX]; exact h)
  rwa [min_eq_right h] at this

end Frame18

/-! ### Group B: Theorem M, the sector tests at `u0` (a- < b+)

Common hypotheses: `hα : a12 < a11` (`A12 ≤ A22` is `F.A12_le_A22`), `hab : am < bp`.
Rim indices: m1+ 0, m2+ 1, m2- 2, xa 3, xb 4, v 5, m1- 6.  `σ = 1`. -/

namespace Shape18
variable (S : Shape18)

/-- `am < bp` cleared: `hm (1 - tp) < tm hp`. -/
theorem hX_of_ab (hab : S.am < S.bp) : S.hm * (1 - S.tp) < S.tm * S.hp := by
  have h1 := S.am_mul
  have h2 := S.bp_mul
  have : 0 < 1 - S.tp := by linarith [S.tp_lt]
  have h3 : S.am * (1 - S.tp) < S.bp * (1 - S.tp) := mul_lt_mul_of_pos_right hab this
  nlinarith [S.tm_pos]

/-- `dp ≤ A1 tp` cleared: `tm kp ≤ (hm tp + tm hp)(1 - sp)`. -/
theorem hV_of_le (hV : S.dp ≤ S.A1 * S.tp) : S.tm * S.kp ≤ (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) := by
  have h1 := S.dp_mul
  have h2 := S.ap_mul
  have h3 := S.am_mul
  have hs : 0 < 1 - S.sp := by linarith [S.sp_lt]
  have : S.dp * (1 - S.sp) ≤ S.A1 * S.tp * (1 - S.sp) := mul_le_mul_of_nonneg_right hV hs.le
  unfold Shape18.A1 at this
  have e : (S.ap + S.am) * S.tp * (1 - S.sp) * S.tm = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) := by
    have : (S.ap + S.am) * S.tp * S.tm = S.hm * S.tp + S.tm * S.hp := by
      linear_combination S.tm * h2 + S.tp * h3
    calc (S.ap + S.am) * S.tp * (1 - S.sp) * S.tm
        = ((S.ap + S.am) * S.tp * S.tm) * (1 - S.sp) := by ring
      _ = _ := by rw [this]
  nlinarith [S.tm_pos]


theorem H_eq : S.hm * S.tp + S.tm * S.hp = S.tm * (S.A1 * S.tp) := by
  have h2 := S.ap_mul
  have h3 := S.am_mul
  unfold Shape18.A1
  linear_combination (-S.tm) * h2 - S.tp * h3

theorem hV_of_lt (hV : S.dp < S.A1 * S.tp) : S.tm * S.kp < (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) := by
  have h1 := S.dp_mul
  have h2 := S.ap_mul
  have h3 := S.am_mul
  have hs : 0 < 1 - S.sp := by linarith [S.sp_lt]
  have : S.dp * (1 - S.sp) < S.A1 * S.tp * (1 - S.sp) := mul_lt_mul_of_pos_right hV hs
  unfold Shape18.A1 at this
  have e : (S.ap + S.am) * S.tp * (1 - S.sp) * S.tm = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) := by
    have : (S.ap + S.am) * S.tp * S.tm = S.hm * S.tp + S.tm * S.hp := by
      linear_combination S.tm * h2 + S.tp * h3
    calc (S.ap + S.am) * S.tp * (1 - S.sp) * S.tm
        = ((S.ap + S.am) * S.tp * S.tm) * (1 - S.sp) := by ring
      _ = _ := by rw [this]
  nlinarith [S.tm_pos]

end Shape18


/-! rim B: `(v, m2-, xb, m1+)` -/
set_option maxHeartbeats 1000000 in
theorem rimB_cyc (S : Shape18) (P q : ℝ) (hP : P < 0) (hV1 : S.sm * S.hm * q + S.tm * S.km * P < 0) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a8 := mul_pos S.sm_pos (add_pos (mul_pos S.hm_pos S.tp_pos) (mul_pos S.tm_pos S.hp_pos))
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7])
    | (right; refine ⟨by ring, by nlinarith [mul_pos a1 (neg_pos.2 hP), mul_pos a9 (neg_pos.2 hP)]⟩)

set_option maxHeartbeats 1000000 in
theorem rimB_rest (S : Shape18) (P q : ℝ) (hP : P < 0) (hV1 : S.sm * S.hm * q + S.tm * S.km * P < 0)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp)
    (hV : S.tm * S.kp ≤ (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp))
    (hM2 : S.tm * S.kp = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) →
      S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P < 0) (w : C3)
    (hw : w = ⟨0, S.sp, S.kp⟩ ∨ w = ⟨1, 0, 0⟩ ∨ w = ⟨S.tm, 0, -S.hm⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i))
        (w.sub (quad (⟨0, 0, 0⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a12 := sub_pos.2 S.sp_lt
  have a13 := S.kp_pos
  have a14 := sub_pos.2 hX
  have a15 := S.sp_pos
  have HH := add_pos a10 a9
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a3 a13, mul_pos a5 (mul_pos a3 a13), mul_pos a7 a15, mul_pos a14 a3, mul_pos HH a15, mul_pos a14 a15])
    | (right; refine ⟨by ring, by nlinarith [mul_pos a1 (neg_pos.2 hP), mul_pos a9 (neg_pos.2 hP), mul_pos a2 (neg_pos.2 hP), mul_pos a10 (neg_pos.2 hP), mul_pos a7 (neg_pos.2 hP)]⟩)
    | (rcases hV.lt_or_eq with hVl | hVe
       · left; nlinarith [sub_pos.2 hVl]
       · have hm2 := hM2 hVe
         right
         refine ⟨by linear_combination (-1 : ℝ) * hVe, ?_⟩
         have key : S.tm * (q * (S.hp * (1 - S.sp) - S.kp) - S.tp * S.kp * P) =
             (1 - S.sp) * S.tp * (-(S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P)) := by
           linear_combination (-q - S.tp * P) * hVe
         have k2 := mul_pos (mul_pos a12 a6) (neg_pos.2 hm2)
         by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])


set_option maxHeartbeats 1000000 in
theorem rimC_cyc (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : 0 < S.sm * S.hm * q + S.tm * S.km * P)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a14 := sub_pos.2 hX
  have HH := add_pos a10 a9
  have a12 := sub_pos.2 S.tm_lt
  have a13 := sub_pos.2 S.tp_lt
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a14 a3, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14, mul_pos a14 a2])
    | (right; refine ⟨by ring, by nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a12) hP, mul_pos (mul_pos a2 a13) hP]⟩)

set_option maxHeartbeats 1000000 in
theorem rimC_rest (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : 0 < S.sm * S.hm * q + S.tm * S.km * P)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp)
    (hV : S.tm * S.kp ≤ (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp))
    (hM2 : S.tm * S.kp = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp) →
      S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P < 0) (w : C3)
    (hw : w = ⟨0, S.sp, S.kp⟩ ∨ w = ⟨0, 0, 0⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        (w.sub (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a12 := sub_pos.2 S.sp_lt
  have a13 := S.kp_pos
  have a14 := sub_pos.2 hX
  have a15 := S.sp_pos
  have a16 := sub_pos.2 S.tm_lt
  have a17 := sub_pos.2 S.tp_lt
  have HH := add_pos a10 a9
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a3 a13, mul_pos a5 (mul_pos a3 a13), mul_pos a7 a15, mul_pos a14 a3, mul_pos HH a15, mul_pos a14 a15, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14])
    | (right; refine ⟨by ring, by nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a16) hP, mul_pos (mul_pos a2 a17) hP]⟩)
    | (rcases hV.lt_or_eq with hVl | hVe
       · left; nlinarith [sub_pos.2 hVl]
       · have hm2 := hM2 hVe
         right
         refine ⟨by linear_combination (-1 : ℝ) * hVe, ?_⟩
         have key : S.tm * (q * (S.hp * (1 - S.sp) - S.kp) - S.tp * S.kp * P) =
             (1 - S.sp) * S.tp * (-(S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P)) := by
           linear_combination (-q - S.tp * P) * hVe
         have k2 := mul_pos (mul_pos a12 a6) (neg_pos.2 hm2)
         by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])


def hex6 {α : Type*} (p₀ p₁ p₂ p₃ p₄ p₅ : α) : ZMod 6 → α := ![p₀, p₁, p₂, p₃, p₄, p₅]
section hex6
variable {α : Type*} (p₀ p₁ p₂ p₃ p₄ p₅ : α)
theorem hex6_0 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 0 = p₀ := rfl
theorem hex6_1 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 1 = p₁ := rfl
theorem hex6_2 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 2 = p₂ := rfl
theorem hex6_3 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 3 = p₃ := rfl
theorem hex6_4 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 4 = p₄ := rfl
theorem hex6_5 : hex6 p₀ p₁ p₂ p₃ p₄ p₅ 5 = p₅ := rfl
end hex6

theorem zmod6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

/-! rim (C+) `(m1-, m2-, xb, m2+, m1+, xa)` at `u0`, `dp = A1 tp`, tilt `(q, P, 0)` -/
set_option maxHeartbeats 2000000 in
theorem rimCp_cyc (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : 0 < S.sm * S.hm * q + S.tm * S.km * P)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp)
    (hVe : S.tm * S.kp = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp))
    (hM2 : 0 < S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ j).sub
          (hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a14 := sub_pos.2 hX
  have HH := add_pos a10 a9
  have a12 := sub_pos.2 S.tm_lt
  have a13 := sub_pos.2 S.tp_lt
  have a15 := S.kp_pos
  have a16 := S.sp_pos
  have a17 := sub_pos.2 S.sp_lt
  have key : S.tm * (q * (S.kp - S.hp * (1 - S.sp)) + S.tp * S.kp * P) =
      (1 - S.sp) * S.tp * (S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P) := by
    linear_combination (q + S.tp * P) * hVe
  have k2 := mul_pos (mul_pos a17 a6) hM2
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a14 a3, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14, mul_pos a14 a2, mul_pos a15 a3, mul_pos a16 a3, mul_pos a16 a2])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a12) hP, mul_pos (mul_pos a2 a13) hP])
    | (right; constructor
       · linear_combination hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])
    | (right; constructor
       · linear_combination (-1 : ℝ) * hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])

set_option maxHeartbeats 2000000 in
theorem rimCp_rest (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : 0 < S.sm * S.hm * q + S.tm * S.km * P)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp) :
    ∀ i : ZMod 6,
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (hex6 (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a14 := sub_pos.2 hX
  have HH := add_pos a10 a9
  have a12 := sub_pos.2 S.tm_lt
  have a13 := sub_pos.2 S.tp_lt
  have a15 := S.kp_pos
  have a16 := S.sp_pos
  have a17 := sub_pos.2 S.sp_lt
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a14 a3, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14, mul_pos a14 a2, mul_pos a15 a3, mul_pos a16 a3, mul_pos a16 a2])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a12) hP, mul_pos (mul_pos a2 a13) hP, mul_pos a3 hP, mul_pos a15 hP])


/-! rim (mixed) `(xa, m1-, v, m2-, xb, m1+)` at `u0`, `dp = A1 tp`, tilt `(q, P, 0)`, `P > 0`, `V1 < 0`, `M2 < 0` -/
set_option maxHeartbeats 2000000 in
theorem rimM_cyc (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : S.sm * S.hm * q + S.tm * S.km * P < 0)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp)
    (hVe : S.tm * S.kp = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp))
    (hM2 : S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ (i + 1)).sub
          (hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i))
        ((hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ j).sub
          (hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a14 := sub_pos.2 hX
  have HH := add_pos a10 a9
  have a12 := sub_pos.2 S.tm_lt
  have a13 := sub_pos.2 S.tp_lt
  have a15 := S.kp_pos
  have a16 := S.sp_pos
  have a17 := sub_pos.2 S.sp_lt
  have nV := neg_pos.2 hV1
  have nM := neg_pos.2 hM2
  have key : S.tm * (q * (S.hp * (1 - S.sp) - S.kp) - S.tp * S.kp * P) =
      (1 - S.sp) * S.tp * (-(S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P)) := by
    linear_combination (-q - S.tp * P) * hVe
  have k2 := mul_pos (mul_pos a17 a6) nM
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a14 a3, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14, mul_pos a15 a3, mul_pos a16 a3, mul_pos a16 a2, mul_pos a11 nV, mul_pos a2 nV, mul_pos a3 nV, mul_pos a1 nV])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a12) hP, mul_pos (mul_pos a2 a13) hP, mul_pos a3 hP, mul_pos a15 hP, mul_pos a2 nV, mul_pos a11 nV, mul_pos a3 nV, mul_pos a5 nV, mul_pos a10 nV])
    | (right; constructor
       · linear_combination (-1 : ℝ) * hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])
    | (right; constructor
       · linear_combination hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])

set_option maxHeartbeats 2000000 in
theorem rimM_rest (S : Shape18) (P q : ℝ) (hP : 0 < P) (hV1 : S.sm * S.hm * q + S.tm * S.km * P < 0)
    (hX : S.hm * (1 - S.tp) < S.tm * S.hp)
    (hVe : S.tm * S.kp = (S.hm * S.tp + S.tm * S.hp) * (1 - S.sp))
    (hM2 : S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P < 0) :
    ∀ i : ZMod 6,
      ST 1 ⟨S.tm, 0, -S.hm⟩ ⟨q, P, 0⟩
        ((hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ (i + 1)).sub
          (hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i))
        ((⟨0, S.sp, S.kp⟩ : C3).sub
          (hex6 (⟨1, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 0, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := S.hm_pos
  have a3 := S.tm_pos
  have a4 := S.km_pos
  have a5 := S.sm_pos
  have a6 := S.tp_pos
  have a7 := mul_pos S.tm_pos S.km_pos
  have a9 := mul_pos S.tm_pos S.hp_pos
  have a10 := mul_pos S.hm_pos S.tp_pos
  have a11 := sub_pos.2 S.sm_lt
  have a14 := sub_pos.2 hX
  have HH := add_pos a10 a9
  have a12 := sub_pos.2 S.tm_lt
  have a13 := sub_pos.2 S.tp_lt
  have a15 := S.kp_pos
  have a16 := S.sp_pos
  have a17 := sub_pos.2 S.sp_lt
  have nV := neg_pos.2 hV1
  have nM := neg_pos.2 hM2
  have key : S.tm * (q * (S.hp * (1 - S.sp) - S.kp) - S.tp * S.kp * P) =
      (1 - S.sp) * S.tp * (-(S.hm * q + (S.hm * S.tp + S.tm * S.hp) * P)) := by
    linear_combination (-q - S.tp * P) * hVe
  have k2 := mul_pos (mul_pos a17 a6) nM
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos a11 a9, mul_pos a11 a10, mul_pos a5 a9, mul_pos a5 a7, mul_pos a14 a3, mul_pos a14 a5, mul_pos a2 a5, mul_pos a2 a14, mul_pos a15 a3, mul_pos a16 a3, mul_pos a16 a2, mul_pos a11 nV, mul_pos a2 nV, mul_pos a3 nV, mul_pos a1 nV])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a1 hP, mul_pos a9 hP, mul_pos a2 hP, mul_pos a10 hP, mul_pos a7 hP, mul_pos a14 hP, mul_pos (mul_pos a1 a12) hP, mul_pos (mul_pos a2 a13) hP, mul_pos a3 hP, mul_pos a15 hP, mul_pos a2 nV, mul_pos a11 nV, mul_pos a3 nV, mul_pos a5 nV, mul_pos a10 nV])
    | (right; constructor
       · linear_combination (-1 : ℝ) * hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])
    | (right; constructor
       · linear_combination hVe
       · by_contra hc
         push_neg at hc
         nlinarith [mul_nonneg a3.le (neg_nonneg.2 hc)])

/-! ### Group C helpers: rims at `am = bp` (the double `m1+ = xa + h u0`), pure real lemmas -/

set_option maxHeartbeats 1000000 in
theorem rimBp_cyc (sm km tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0)
    (hQ : q + P < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a13 := neg_pos.2 hP
  have a14 := neg_pos.2 hQ
  have a15 := neg_pos.2 hV1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 a13, mul_pos htm a13, mul_pos hhm a13])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 a13, mul_pos (mul_pos a12 hhm) a13, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) a13])

set_option maxHeartbeats 1000000 in
theorem rimBp_rest (sm km sp kp tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0)
    (hQ : q + P < 0) (w : C3) (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨tm, 0, -hm⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ i))
        (w.sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a13 := neg_pos.2 hP
  have a14 := neg_pos.2 hQ
  have a15 := neg_pos.2 hV1
  have a16 := sub_pos.2 hV
  have a17 := sub_pos.2 hsp1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 a13, mul_pos htm a13, mul_pos hhm a13, mul_pos a16 a13, mul_pos a17 a13, mul_pos hsp a13, mul_pos htm (mul_pos hsm hkp), mul_pos htm (mul_pos hkm hsp), mul_pos htm (mul_pos a11 hkp), mul_pos htm (mul_pos hkm a17)])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 a13, mul_pos (mul_pos a12 hhm) a13, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) a13, mul_pos hsp (mul_pos a12 a14), mul_pos (mul_pos a12 hsp) a13, mul_pos (mul_pos a12 a16) a13, mul_pos (mul_pos a12 hhm) (mul_pos a17 a13)])

set_option maxHeartbeats 1000000 in
theorem rimCe_cyc (sm km tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P)
    (hQ : 0 < q + P) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a14 := hQ
  have a15 := hV1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos htp hP, mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a14, mul_pos htp a14, mul_pos hhm a14, mul_pos a12 a15, mul_pos htm a14, mul_pos hhm a14])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) hP, mul_pos (mul_pos a12 htm) hP, mul_pos (mul_pos a12 htm) a14])

set_option maxHeartbeats 1000000 in
theorem rimCe_rest (sm km sp kp tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P)
    (hQ : 0 < q + P) (w : C3) (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨0, 0, 0⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ i))
        (w.sub (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1 + h * tm, 0, -h * hm⟩ ⟨1, 0, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a14 := hQ
  have a15 := hV1
  have a16 := sub_pos.2 hV
  have a17 := sub_pos.2 hsp1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos htp hP, mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a14, mul_pos htp a14, mul_pos hhm a14, mul_pos a12 a15, mul_pos htm a14, mul_pos a16 hP, mul_pos a17 hP, mul_pos hsp hP, mul_pos htm (mul_pos hsm hkp), mul_pos htm (mul_pos hkm hsp), mul_pos htm (mul_pos a11 hkp), mul_pos htm (mul_pos hkm a17)])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) hP, mul_pos (mul_pos a12 htm) hP, mul_pos (mul_pos a12 htm) a14, mul_pos hsp (mul_pos a12 a14), mul_pos (mul_pos a12 hsp) hP, mul_pos (mul_pos a12 a16) hP, mul_pos (mul_pos a12 hhm) (mul_pos a17 hP)])

set_option maxHeartbeats 1000000 in
theorem rimDp_cyc (sm km tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : 0 < P) (hV1 : sm * hm * q + tm * km * P < 0)
    (hQ : q + P < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ j).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a14 := neg_pos.2 hQ
  have a15 := neg_pos.2 hV1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos htp hP, mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a14, mul_pos htp a14, mul_pos hhm a14, mul_pos a12 a15, mul_pos htm a14, mul_pos hhm a14])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) hP, mul_pos (mul_pos a12 htm) hP, mul_pos (mul_pos a12 htm) a14])

set_option maxHeartbeats 1000000 in
theorem rimDp_rest (sm km sp kp tm hm h q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hh : h < 0) (htp : 0 < 1 + h * tm) (hP : 0 < P) (hV1 : sm * hm * q + tm * km * P < 0)
    (hQ : q + P < 0) (w : C3) (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨1 + h * tm, 0, -h * hm⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        (w.sub (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a12 := neg_pos.2 hh
  have a14 := neg_pos.2 hQ
  have a15 := neg_pos.2 hV1
  have a16 := sub_pos.2 hV
  have a17 := sub_pos.2 hsp1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos htp hP, mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a14, mul_pos htp a14, mul_pos hhm a14, mul_pos a12 a15, mul_pos htm a14, mul_pos a16 hP, mul_pos a17 hP, mul_pos hsp hP, mul_pos htm (mul_pos hsm hkp), mul_pos htm (mul_pos hkm hsp), mul_pos htm (mul_pos a11 hkp), mul_pos htm (mul_pos hkm a17)])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos a12 hP, mul_pos (mul_pos a12 hhm) hP, mul_pos (mul_pos a12 hhm) a14, mul_pos a12 a14, mul_pos (mul_pos a12 hhm) a15,mul_pos a12 a15, mul_pos (mul_pos a12 a11) a14, mul_pos (mul_pos a12 hhm) a11, mul_pos (mul_pos a12 a7) hP, mul_pos (mul_pos a12 htm) hP, mul_pos (mul_pos a12 htm) a14, mul_pos hsp (mul_pos a12 a14), mul_pos (mul_pos a12 hsp) hP, mul_pos (mul_pos a12 a16) hP, mul_pos (mul_pos a12 hhm) (mul_pos a17 hP)])

theorem exists_h_of_double {tm hm tp hp : ℝ} (htm : 0 < tm) (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp)
    (hE : hm * (1 - tp) = tm * hp) :
    ∃ h : ℝ, h < 0 ∧ 0 < 1 + h * tm ∧ (⟨tp, 0, hp⟩ : C3) = ⟨1 + h * tm, 0, -h * hm⟩ := by
  have hm0 : hm ≠ 0 := hhm.ne'
  have h1 : tp = 1 + (-hp / hm) * tm := by
    field_simp
    linarith
  refine ⟨-hp / hm, ?_, by rw [← h1]; exact htp, ?_⟩
  · rw [neg_div]; exact neg_neg_of_pos (div_pos hhp hhm)
  · have h2 : hp = -(-hp / hm) * hm := by field_simp
    rw [← h1, ← h2]

theorem rimBp_cyc' (sm km tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0) (hQ : q + P < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  rw [e]
  exact rimBp_cyc sm km tm hm h q P hsm hsm1 hkm htm hhm hh htp' hP hV1 hQ

theorem rimBp_rest' (sm km sp kp tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0) (hQ : q + P < 0) (w : C3)
    (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨tm, 0, -hm⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        (w.sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  rw [e]
  exact rimBp_rest sm km sp kp tm hm h q P hsm hsm1 hkm htm hsp hsp1 hkp hV hhm hh htp' hP hV1 hQ w hw

theorem rimCe_cyc' (sm km tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P) (hQ : 0 < q + P) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  rw [e]
  exact rimCe_cyc sm km tm hm h q P hsm hsm1 hkm htm hhm hh htp' hP hV1 hQ

theorem rimCe_rest' (sm km sp kp tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P) (hQ : 0 < q + P) (w : C3)
    (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨0, 0, 0⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        (w.sub (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  rw [e]
  exact rimCe_rest sm km sp kp tm hm h q P hsm hsm1 hkm htm hsp hsp1 hkp hV hhm hh htp' hP hV1 hQ w hw

theorem rimDp_cyc' (sm km tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : 0 < P) (hV1 : sm * hm * q + tm * km * P < 0) (hQ : q + P < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ j).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  exact rimDp_cyc sm km tm hm h q P hsm hsm1 hkm htm hhm hh htp' hP hV1 hQ

theorem rimDp_rest' (sm km sp kp tm hm tp hp q P : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hV : tm * kp < hm * (1 - sp))
    (hhm : 0 < hm) (hhp : 0 < hp) (htp : 0 < tp) (hE : hm * (1 - tp) = tm * hp)
    (hP : 0 < P) (hV1 : sm * hm * q + tm * km * P < 0) (hQ : q + P < 0) (w : C3)
    (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨tp, 0, hp⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        (w.sub (quint (⟨1, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  obtain ⟨h, hh, htp', e⟩ := exists_h_of_double htm hhm hhp htp hE
  rw [e] at hw
  exact rimDp_rest sm km sp kp tm hm h q P hsm hsm1 hkm htm hsp hsp1 hkp hV hhm hh htp' hP hV1 hQ w hw

namespace Shape18
variable (S : Shape18)

/-- `am = bp` cleared: `hm (1 - tp) = tm hp` (`m1+ = xa + h u0`). -/
theorem hE_of_eq (hab : S.am = S.bp) : S.hm * (1 - S.tp) = S.tm * S.hp := by
  have h1 := S.am_mul
  have h2 := S.bp_mul
  rw [hab] at h1
  calc S.hm * (1 - S.tp) = (S.bp * S.tm) * (1 - S.tp) := by rw [h1]
    _ = S.tm * (S.bp * (1 - S.tp)) := by ring
    _ = S.tm * S.hp := by rw [h2]

/-- At `am = bp`, `m2+` is strictly inside: `tm kp < hm (1 - sp)` (`dp < bp = A1 tp`). -/
theorem hVs_of_eq (hab : S.am = S.bp) : S.tm * S.kp < S.hm * (1 - S.sp) := by
  have hE := S.hE_of_eq hab
  have h3 : S.am * (1 - S.tp) = S.hp := by
    apply mul_left_cancel₀ S.tm_pos.ne'
    linear_combination (1 - S.tp) * S.am_mul + hE
  have hA : S.A1 * S.tp = S.am := by
    unfold Shape18.A1
    linear_combination S.ap_mul - h3
  have hlt : S.dp < S.A1 * S.tp := by rw [hA, hab]; exact S.dp_lt_bp
  have h4 := S.hV_of_lt hlt
  have h5 : S.hm * S.tp + S.tm * S.hp = S.hm := by linarith [hE]
  rw [h5] at h4
  exact h4

end Shape18

theorem Q5t_eventually_lex {z w : ZMod 5 → ℝ} (h1 : z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1))
    (h2 : z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)) (h3 : z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4))
    (h4 : z 4 < z 0 ∨ (z 4 = z 0 ∧ w 4 < w 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5t fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h2, ev_lt h3, ev_lt h4] with s a b c d
  exact ⟨a, b, c, d⟩



/-! ### Group D: sector tests for Theorem R and Lemma LV -/

set_option maxHeartbeats 1000000 in
theorem rimS1_cyc (sm km tm hm P q : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm)
    (hhm : 0 < hm) (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i))
        ((quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ j).sub
          (quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos a11 hP, mul_pos a11 (mul_pos htm hP), mul_pos a11 (mul_pos hhm hP)])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hhm hP, mul_pos htm hP, mul_pos a11 hP, mul_pos (mul_pos hhm a11) hP, mul_pos (mul_pos htm hhm) hP, mul_pos hhm hV1, mul_pos htm hV1, mul_pos a11 hV1])

set_option maxHeartbeats 1000000 in
theorem rimS1_rest (sm km sp kp tm hm tp hp P q : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hhm : 0 < hm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htp : 0 < tp)
    (htp1 : tp < 1) (hhp : 0 < hp) (hB : tm * hp < hm * (1 - tp)) (hV : tm * kp < hm * (1 - sp))
    (hP : 0 < P) (hV1 : 0 < sm * hm * q + tm * km * P) (w : C3)
    (hw : w = ⟨0, 0, 0⟩ ∨ w = ⟨tp, 0, hp⟩ ∨ w = ⟨0, sp, kp⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i))
        (w.sub (quad (⟨tm, 0, -hm⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a14 := sub_pos.2 hB
  have a16 := sub_pos.2 hV
  have a17 := sub_pos.2 hsp1
  have a18 := sub_pos.2 htp1
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos a11 (mul_pos hhm htp), mul_pos a11 (mul_pos htm hhp), mul_pos a11 a7, mul_pos htm a8, mul_pos a7 hP, mul_pos htm hP, mul_pos hhm hP, mul_pos a11 hP, mul_pos a14 hP, mul_pos a16 hP, mul_pos a14 htm, mul_pos a16 htm, mul_pos hhm hhp, mul_pos htm hhp, mul_pos hP hhp, mul_pos (mul_pos a14 htm) hP, mul_pos hkp htm, mul_pos hkp hsm, mul_pos hsp hkm, mul_pos a17 hkm, mul_pos a17 hkp])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hhm hP, mul_pos htm hP, mul_pos a11 hP, mul_pos (mul_pos hhm a11) hP, mul_pos (mul_pos htm hhm) hP, mul_pos hhm hV1, mul_pos htm hV1, mul_pos a11 hV1, mul_pos hhp hP, mul_pos hhp hV1, mul_pos hhp htm, mul_pos htp hP, mul_pos a14 hP, mul_pos a16 hP])


set_option maxHeartbeats 1000000 in
theorem rimS2_cyc (sm km tm hm tp hp P q : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hhm : 0 < hm) (htp : 0 < tp) (hhp : 0 < hp)
    (hB : tm * hp < hm * (1 - tp)) (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a14 := sub_pos.2 hB
  have a13 := neg_pos.2 hP
  have a15 := neg_pos.2 hV1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 a13, mul_pos htm a13, mul_pos hhm a13, mul_pos a14 a13, mul_pos a14 htm, mul_pos a11 (mul_pos hhm htp), mul_pos a11 (mul_pos htm hhp), mul_pos hhp a13, mul_pos htp a13, mul_pos a14 a15])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hhm a13, mul_pos htm a13, mul_pos a11 a13, mul_pos (mul_pos hhm a11) a13, mul_pos hhm a15, mul_pos htm a15, mul_pos a11 a15, mul_pos hhp a13, mul_pos hhp a15, mul_pos a14 a13, mul_pos a14 a15, mul_pos htp a13, mul_pos htp a15, mul_pos a7 a13])

set_option maxHeartbeats 1000000 in
theorem rimS2_rest (sm km sp kp tm hm tp hp P q : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htm : 0 < tm) (hhm : 0 < hm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htp : 0 < tp)
    (hhp : 0 < hp) (hB : tm * hp < hm * (1 - tp)) (hV : tm * kp < hm * (1 - sp))
    (hP : P < 0) (hV1 : sm * hm * q + tm * km * P < 0) (w : C3)
    (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨tm, 0, -hm⟩) :
    ∀ i : ZMod 5,
      ST 1 ⟨tm, 0, -hm⟩ ⟨q, P, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        (w.sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have a7 := mul_pos htm hkm
  have a8 := mul_pos hsm hhm
  have a11 := sub_pos.2 hsm1
  have a14 := sub_pos.2 hB
  have a13 := neg_pos.2 hP
  have a15 := neg_pos.2 hV1
  have a16 := sub_pos.2 hV
  have a17 := sub_pos.2 hsp1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases hw with rfl | rfl <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith [mul_pos a11 a7, mul_pos htm a8, mul_pos a7 a13, mul_pos htm a13, mul_pos hhm a13, mul_pos a14 a13, mul_pos a14 htm, mul_pos a11 (mul_pos hhm htp), mul_pos a11 (mul_pos htm hhp), mul_pos hhp a13, mul_pos htp a13, mul_pos a16 a13, mul_pos a17 a13, mul_pos hsp a13, mul_pos htm (mul_pos hsm hkp), mul_pos htm (mul_pos hkm hsp), mul_pos htm (mul_pos a11 hkp), mul_pos htm (mul_pos hkm a17), mul_pos a14 a15])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos hhm a13, mul_pos htm a13, mul_pos a11 a13, mul_pos (mul_pos hhm a11) a13, mul_pos hhm a15, mul_pos htm a15, mul_pos a11 a15, mul_pos hhp a13, mul_pos hhp a15, mul_pos a14 a13, mul_pos a14 a15, mul_pos htp a13, mul_pos htp a15, mul_pos a7 a13, mul_pos hsp a15, mul_pos (mul_pos hsp hhm) a13, mul_pos a16 a13, mul_pos a17 a13, mul_pos (mul_pos a17 hhm) a13])


set_option maxHeartbeats 1000000 in
theorem rimLV_cyc (tp hp tm hm T : ℝ) (htp : 0 < tp) (hhp : 0 < hp) (htm : 0 < tm) (hhm : 0 < hm)
    (h1 : 0 < hp - T * tp) (h2 : 0 < hm + T * tm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, 0, T⟩ ⟨0, -1, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ i))
        ((quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ j).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ i)) := by
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j hi hj
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hi
    | exact absurd (by decide) hj
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos htp hhm, mul_pos htm hhp, mul_pos h1 h2, mul_pos htp htm, mul_pos hhp hhm, mul_pos htp h2, mul_pos htm h1, mul_pos hhp h2, mul_pos hhm h1])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos htp hhm, mul_pos htm hhp, mul_pos h1 h2, mul_pos htp htm, mul_pos hhp hhm, mul_pos htp h2, mul_pos htm h1, mul_pos hhp h2, mul_pos hhm h1])

set_option maxHeartbeats 1000000 in
theorem rimLV_rest (sm km sp kp tp hp tm hm T : ℝ) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htp : 0 < tp) (hhp : 0 < hp) (htm : 0 < tm)
    (hhm : 0 < hm)
    (h1 : 0 < hp - T * tp) (h2 : 0 < hm + T * tm) (hx1 : 0 < hp - T * tp + T) (hx2 : 0 < hm + T * tm - T)
    (hp2 : kp < (hp - T * tp) * (1 - sp)) (hm2 : km < (hm + T * tm) * (1 - sm)) (w : C3)
    (hw : w = ⟨0, sp, kp⟩ ∨ w = ⟨0, sm, -km⟩ ∨ w = ⟨1, 0, 0⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, 0, T⟩ ⟨0, -1, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ i))
        (w.sub (quad (⟨0, 1, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨tm, 0, -hm⟩ i)) := by
  have a16 := sub_pos.2 hp2
  have a17 := sub_pos.2 hm2
  have a18 := sub_pos.2 hsp1
  have a19 := sub_pos.2 hsm1
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases hw with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith [mul_pos htp hhm, mul_pos htm hhp, mul_pos h1 h2, mul_pos htp htm, mul_pos hhp hhm, mul_pos htp h2, mul_pos htm h1, mul_pos hhp h2, mul_pos hhm h1, mul_pos hx1 hx2, mul_pos hx1 h2, mul_pos hx2 h1, mul_pos hx1 htm, mul_pos hx2 htp, mul_pos a16 h2, mul_pos a17 h1, mul_pos a16 htm, mul_pos a17 htp, mul_pos hsp h2, mul_pos hsm h1, mul_pos hkp h2, mul_pos hkm h1, mul_pos a16 hx2, mul_pos a17 hx1, mul_pos hkp htm, mul_pos hkm htp, mul_pos hsp hhm, mul_pos hsm hhp])
    | (right; constructor
       · ring1
       · nlinarith [mul_pos htp hhm, mul_pos htm hhp, mul_pos h1 h2, mul_pos htp htm, mul_pos hhp hhm, mul_pos htp h2, mul_pos htm h1, mul_pos hhp h2, mul_pos hhm h1, mul_pos hx1 hx2, mul_pos hx1 h2, mul_pos hx2 h1, mul_pos hx1 htm, mul_pos hx2 htp])

namespace Shape18
variable (S : Shape18)

/-- `bp < am` cleared: `tm hp < hm (1 - tp)` (`m1+` on the open segment `(E1, xa)`). -/
theorem hB_of_lt (hb : S.bp < S.am) : S.tm * S.hp < S.hm * (1 - S.tp) := by
  have h1 := S.am_mul
  have h2 := S.bp_mul
  have : 0 < 1 - S.tp := by linarith [S.tp_lt]
  have h3 : S.bp * (1 - S.tp) < S.am * (1 - S.tp) := mul_lt_mul_of_pos_right hb this
  nlinarith [S.tm_pos]

/-- For `bp < am`, `m2+` is strictly inside: `tm kp < hm (1 - sp)` (`dp < bp < am`). -/
theorem hVs_of_lt (hb : S.bp < S.am) : S.tm * S.kp < S.hm * (1 - S.sp) := by
  have h1 := S.am_mul
  have h2 := S.dp_mul
  have h3 : S.dp < S.am := lt_trans S.dp_lt_bp hb
  have hs : 0 < 1 - S.sp := by linarith [S.sp_lt]
  have := mul_lt_mul_of_pos_right h3 hs
  nlinarith [S.tm_pos]

/-- `D2p = tp tm (1-sp)(1-sm)(A1 - μ+ - μ-)`. -/
theorem D2p_eq :
    S.D2p = S.tp * S.tm * (1 - S.sp) * (1 - S.sm) * (S.A1 - S.mup - S.mum) := by
  have e1 := S.am_mul; have e2 := S.ap_mul; have e3 := S.dm_mul; have e4 := S.dp_mul
  have e5 := S.mum_mul; have e6 := S.mup_mul
  have hm : S.hm = S.am * S.tm := e1.symm
  have hp : S.hp = S.ap * S.tp := e2.symm
  have hkm : S.km = S.mum * S.tm * (1 - S.sm) := by rw [e5, e3]
  have hkp : S.kp = S.mup * S.tp * (1 - S.sp) := by rw [e6, e4]
  unfold Shape18.D2p Shape18.A1
  rw [hm, hp, hkm, hkp]
  ring

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- Depths at `u0` of explicit coordinates (avoids `ptC` rewriting). -/
theorem GGc_u0 :
    F.toFrame7.GG ⟨F.S.tm, 0, -F.S.hm⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0R ∧
    F.toFrame7.GG ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0T ∧
    F.toFrame7.GG ⟨0, 1, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0X ∧
    F.toFrame7.GG ⟨F.S.tp, 0, F.S.hp⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z1 ∧
    F.toFrame7.GG ⟨0, F.S.sm, -F.S.km⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z2 ∧
    F.toFrame7.GG ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = F.u0Z2p ∧
    F.toFrame7.GG ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ = 0 := by
  have h := F.GG_u0
  rw [F.ptC_6, F.ptC_3, F.ptC_4, F.ptC_0, F.ptC_2, F.ptC_1, F.ptC_5] at h
  exact h

/-- The tilted depth of explicit coordinates. -/
theorem GGc_tilt (a b c q P : ℝ) :
    F.toFrame7.GG ⟨a, b, c⟩ ⟨q, P, 0⟩ = F.a11 * (a * q) + F.a12 * (a * P + q * b) + F.a22 * (b * P) := by
  rw [F.GG_eq]; ring

/-- Rim (B) `(v, m2-, xb, m1+)` at `u0` with tilt `(q, P, 0)`: the generic bridge. -/
theorem rimB_rupert (P q : ℝ) (hP : P < 0) (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0)
    (hX : F.S.hm * (1 - F.S.tp) < F.S.tm * F.S.hp)
    (hV : F.S.tm * F.S.kp ≤ (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp))
    (hM2 : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp) →
      F.S.hm * q + (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * P < 0)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => F.toFrame7.GG
        (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim4 5 2 4 0 ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
    F.ptC_5 F.ptC_2 F.ptC_4 F.ptC_0 1 (Or.inl rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
    (Or.inl F.S.tm_pos.ne') (rimB_cyc F.S P q hP hV1) ?_ hQe
  intro j' h0 h1 h2 h3 i
  rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h3
  · rw [F.ptC_1]; exact rimB_rest F.S P q hP hV1 hX hV hM2 _ (Or.inl rfl) i
  · exact absurd rfl h1
  · rw [F.ptC_3]; exact rimB_rest F.S P q hP hV1 hX hV hM2 _ (Or.inr (Or.inl rfl)) i
  · exact absurd rfl h2
  · exact absurd rfl h0
  · rw [F.ptC_6]; exact rimB_rest F.S P q hP hV1 hX hV hM2 _ (Or.inr (Or.inr rfl)) i



/-- Rim (C) `(m1-, m2-, xb, m1+, xa)` at `u0` with tilt `(q, P, 0)`, robust depths. -/
theorem rimC_rupert (P q : ℝ) (hP : 0 < P) (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P)
    (hX : F.S.hm * (1 - F.S.tp) < F.S.tm * F.S.hp)
    (hV : F.S.tm * F.S.kp ≤ (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp))
    (hM2 : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp) →
      F.S.hm * q + (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * P < 0)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z1, F.u0T] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hc : ∀ i, F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i) =
      quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_3]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (6 : Fin 7) 2 4 0 3) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact rimC_cyc F.S P q hP hV1 hX i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · rw [F.ptC_1]; exact rimC_rest F.S P q hP hV1 hX hV hM2 _ (Or.inl rfl) i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · rw [F.ptC_5]; exact rimC_rest F.S P q hP hV1 hX hV hM2 _ (Or.inr rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)
  · have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)) ⟨F.S.tm, 0, -F.S.hm⟩) =
        fun i : ZMod 5 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z1, F.u0T] i := by
      funext i
      rw [hc]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp [quint_0, quint_1, quint_2, quint_3, quint_4, gR, gZ2, gX, gZ1, gT]
    rw [this]; exact hz




/-- Rim (C+) `(m1-, m2-, xb, m2+, m1+, xa)` at `u0` with tilt `(q, P, 0)`, robust depths. -/
theorem rimCp_rupert (P q : ℝ) (hP : 0 < P) (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P)
    (hX : F.S.hm * (1 - F.S.tp) < F.S.tm * F.S.hp)
    (hVe : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp))
    (hM2 : 0 < F.S.hm * q + (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * P)
    (hz : IsRobustUnimodal (k := 6) fun i : ZMod 6 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z2p, F.u0Z1, F.u0T] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  let c : ZMod 6 → Fin 7 := ![6, 2, 4, 1, 0, 3]
  have hc : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_1, F.ptC_0, F.ptC_3]
  refine F.toFrame7.rupert_rim_rob (k := 6) (by norm_num) c 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact rimCp_cyc F.S P q hP hV1 hX hVe hM2 i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 3)
    · exact absurd rfl (hj' 1)
    · exact absurd rfl (hj' 5)
    · exact absurd rfl (hj' 2)
    · rw [F.ptC_5]; exact rimCp_rest F.S P q hP hV1 hX i
    · exact absurd rfl (hj' 0)
  · have : (fun i : ZMod 6 => F.toFrame7.GG (F.toFrame7.ptC (c i)) ⟨F.S.tm, 0, -F.S.hm⟩) =
        fun i : ZMod 6 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z2p, F.u0Z1, F.u0T] i := by
      funext i
      rw [hc]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, gR, gZ2, gX, gZp, gZ1, gT]
    rw [this]; exact hz



/-- Mixed rim `(xa, m1-, v, m2-, xb, m1+)` = `(3,6,5,2,4,0)` at `u0`, tilt `(q, P, 0)`, with `Q6m`
at the tilted depths of the hex coordinates. -/
theorem rimM_rupert (P q : ℝ) (hP : 0 < P) (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0)
    (hX : F.S.hm * (1 - F.S.tp) < F.S.tm * F.S.hp)
    (hVe : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp))
    (hM2 : F.S.hm * q + (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * P < 0)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q6m fun i : ZMod 6 =>
      F.toFrame7.GG (hex6 (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩
        ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (hex6 (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩
        ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  let c : ZMod 6 → Fin 7 := ![3, 6, 5, 2, 4, 0]
  have hc : ∀ i, F.toFrame7.ptC (c i) =
      hex6 (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_5, F.ptC_0, F.ptC_3]
  refine F.toFrame7.rupert_rim (k := 6) (by norm_num) c 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') ?_ ?_ Q6m Q6m_open
    (fun z a ha => Q6m_smul ha) (fun z a => Q6m_shift a) ?_ (fun z hz hq => Q6m_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact rimM_cyc F.S P q hP hV1 hX hVe hM2 i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hj' 5)
    · rw [F.ptC_1]; exact rimM_rest F.S P q hP hV1 hX hVe hM2 i
    · exact absurd rfl (hj' 3)
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 2)
    · exact absurd rfl (hj' 1)
  · simp only [hc]; exact hQe


/-- Sector (B): rim `(v, m2-, xb, m1+)` = `(5,2,4,0)`, tilt `(P, Q) = (-1, -1)`, i.e.
`d = (-1/hm, -1, 0)`; `m2+` strictly inside or hidden (`M2 = Q + H P < 0`).  Lemma Q: robust iff
`min(Z1, Z2) < X`.  Covers `Z2 < X` and `Z2 = X, Z1 < X` (Theorem M steps 1, 3). -/
theorem tM_B (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp ≤ F.S.A1 * F.S.tp)
    (h : F.gg * F.S.am * F.S.dm < F.a12 ∨ F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp < F.a12) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have htp := F.S.tp_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hH : 0 < F.S.hm * F.S.tp + F.S.tm * F.S.hp := by positivity
  refine F.rimB_rupert (-1) (-1) (by norm_num) (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm])
    (F.S.hX_of_ab hab) (F.S.hV_of_le hV) (fun _ => by linarith) ?_
  have hZ2 := F.u0Z2_pos
  refine Q4_eventually (z := fun i => F.toFrame7.GG
        (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨-1, -1, 0⟩)
    (Or.inl (Or.inl ?_)) ?_
  · simp only [quad_0, quad_1, g0, gZ2]; exact hZ2
  · have h1 := F.u0Z2_sub_X
    have h2 := F.u0Z1_sub_X
    have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
    rcases h with h | h
    · refine Or.inr (Or.inr (Or.inl (Or.inl ?_)))
      simp only [quad_1, quad_2, gZ2, gX]
      nlinarith [mul_pos hs (sub_pos.2 h)]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      simp only [quad_2, quad_3, gZ1, gX]
      nlinarith [mul_pos htm (sub_pos.2 h)]

/-- Sector (C): rim `(m1-, m2-, xb, m1+, xa)` = `(6,2,4,0,3)`, tilt `(P, Q) = (1, 1)`, `m2+`
strictly inside.  Robust by `robust_cycC` (needs Lemma W).  Steps 2, 4 for `dp < A1 tp`. -/
theorem tM_C (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp < F.S.A1 * F.S.tp)
    (h : F.a12 < F.gg * F.S.am * F.S.dm ∨
      (F.gg * F.S.am * F.S.dm = F.a12 ∧ F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp)) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  refine F.rimC_rupert 1 1 one_pos (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm])
    (F.S.hX_of_ab hab) (F.S.hV_of_le hV.le) (fun hE => absurd hE ?_) ?_
  · exact (F.S.hV_of_lt hV).ne
  · have hXZ : F.u0X ≤ F.u0Z2 := by
      rcases h with h | ⟨h, _⟩
      · nlinarith [mul_pos hs (sub_pos.2 h)]
      · nlinarith
    refine robust_cycC (F.u0X_lt_T hα) F.u0Z1_lt_T (F.u0_W1 hXZ) ?_
    rcases h with h | ⟨h, h'⟩
    · left; nlinarith [mul_pos hs (sub_pos.2 h)]
    · right
      refine ⟨by rw [h] at e1; linarith, by nlinarith [mul_pos htm (sub_pos.2 h')]⟩

/-- Step 5 (`Z2 = Z1 = X`): sector (B) with the tilt `P = -1`, `Q` very negative so that
`L2 = <d, xb - m1+>_G > 0` (metric dependent: `Q = -(1 + tm (|a22 - a12 tp| + 1)/(gg hp))`);
`Q4` with the lex alternative `w(m1+) < w(xb)`.  Covers `dp ≤ A1 tp`. -/
theorem tM_B_tie (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp ≤ F.S.A1 * F.S.tp)
    (h2 : F.gg * F.S.am * F.S.dm = F.a12) (h1 : F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp = F.a12) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have htp := F.S.tp_pos; have hg := F.g_pos
  have ham := F.S.am_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hH : 0 < F.S.hm * F.S.tp + F.S.tm * F.S.hp := by positivity
  set c := F.a22 - F.a12 * F.S.tp with hc
  set q : ℝ := -(1 + (|c| + 1) / (F.gg * F.S.am * F.S.hp)) with hq
  have hd : 0 < F.gg * F.S.am * F.S.hp := by positivity
  have hq0 : q < 0 := by
    have : 0 < (|c| + 1) / (F.gg * F.S.am * F.S.hp) := div_pos (by positivity) hd
    rw [hq]; linarith
  have hL : 0 < F.a12 * q + F.a22 * (-1) - (F.a11 * (F.S.tp * q) + F.a12 * (F.S.tp * (-1) + q * 0)) := by
    have e1 : F.a12 - F.a11 * F.S.tp = - (F.gg * F.S.am * F.S.hp) := by linarith
    have e2 : q * (F.gg * F.S.am * F.S.hp) = -(F.gg * F.S.am * F.S.hp) - (|c| + 1) := by
      rw [hq]; field_simp; ring
    have : F.a12 * q + F.a22 * (-1) - (F.a11 * (F.S.tp * q) + F.a12 * (F.S.tp * (-1) + q * 0)) =
        q * (F.a12 - F.a11 * F.S.tp) - c := by rw [hc]; ring
    rw [this, e1]
    nlinarith [le_abs_self c, neg_abs_le c, e2]
  refine F.rimB_rupert (-1) q (by norm_num) (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm, mul_neg_of_pos_of_neg (mul_pos hsm hhm) hq0])
    (F.S.hX_of_ab hab) (F.S.hV_of_le hV) (fun _ => by nlinarith [mul_neg_of_pos_of_neg hhm hq0]) ?_
  have hZ2 := F.u0Z2_pos
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  refine Q4_eventually (z := fun i => F.toFrame7.GG
        (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, -1, 0⟩)
    (Or.inl (Or.inl ?_)) (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
  · simp only [quad_0, quad_1, g0, gZ2]; exact hZ2
  · simp only [quad_2, quad_3, gZ1, gX]
    have : F.u0Z1 - F.u0X = 0 := by rw [e2, h1]; ring
    linarith
  · simp only [quad_2, quad_3, F.GGc_tilt]
    linarith

/-- Step 6, `c- > d+`: sector (C) with `m2+` hidden: tilt `P = 1`, `Q = -(H + tm cm)/2`
(`H = hm tp + tm hp`; `V1 > 0` and `M2 < 0` solvable iff `H < tm cm` iff `dp < cm`). -/
theorem tM_C_hid (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp = F.S.A1 * F.S.tp)
    (hc : F.S.dp < F.S.cm)
    (h : F.a12 < F.gg * F.S.am * F.S.dm ∨
      (F.gg * F.S.am * F.S.dm = F.a12 ∧ F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp)) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  have hH := F.S.H_eq
  have hcm := F.S.cm_mul
  set H := F.S.hm * F.S.tp + F.S.tm * F.S.hp with hHdef
  have hHc : H < F.S.tm * F.S.cm := by
    rw [hH, ← hV]; exact mul_lt_mul_of_pos_left hc htm
  set q : ℝ := -(H + F.S.tm * F.S.cm) / (2 * F.S.hm) with hq
  have hmq : F.S.hm * q = -(H + F.S.tm * F.S.cm) / 2 := by
    rw [hq]; field_simp
  refine F.rimC_rupert 1 q one_pos ?_ (F.S.hX_of_ab hab) (F.S.hV_of_le hV.le) (fun _ => ?_) ?_
  · have : F.S.sm * F.S.hm * q = F.S.sm * (-(H + F.S.tm * F.S.cm) / 2) := by rw [← hmq]; ring
    rw [this]
    have : F.S.km = F.S.cm * F.S.sm := hcm.symm
    rw [this]
    nlinarith [mul_pos hsm (sub_pos.2 hHc)]
  · rw [hmq]; linarith
  · have hXZ : F.u0X ≤ F.u0Z2 := by
      rcases h with h | ⟨h, _⟩
      · nlinarith [mul_pos hs (sub_pos.2 h)]
      · nlinarith
    refine robust_cycC (F.u0X_lt_T hα) F.u0Z1_lt_T (F.u0_W1 hXZ) ?_
    rcases h with h | ⟨h, h'⟩
    · left; nlinarith [mul_pos hs (sub_pos.2 h)]
    · right
      refine ⟨by rw [h] at e1; linarith, by nlinarith [mul_pos htm (sub_pos.2 h')]⟩

/-- Step 6, `a22 am < a12 cm`: sector (B), `m2+` hidden, with the level edge `(m2-, xb)` broken
by `L1 > 0` (`A22 hm/A12 < Q' < min(H, tm cm)` for `P = -1`, `Q = Q'`): `Q4` lex. -/
theorem tM_B_L1 (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp = F.S.A1 * F.S.tp)
    (h2 : F.gg * F.S.am * F.S.dm = F.a12) (h1 : F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp)
    (hL : F.a22 * F.S.am < F.a12 * F.S.cm) (hL' : F.a22 * F.S.am < F.a12 * F.S.dp) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hA12 : 0 < F.a12 := F.A12_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hH := F.S.H_eq
  have hcm := F.S.cm_mul
  have ham := F.S.am_mul
  set H := F.S.hm * F.S.tp + F.S.tm * F.S.hp with hHdef
  set Mn := min H (F.S.tm * F.S.cm) with hMn
  have hM1 : Mn ≤ H := min_le_left _ _
  have hM2' : Mn ≤ F.S.tm * F.S.cm := min_le_right _ _
  have hr : F.a22 * F.S.hm < F.a12 * Mn := by
    rw [hMn, mul_min_of_nonneg _ _ hA12.le]
    refine lt_min ?_ ?_
    · have := mul_lt_mul_of_pos_right hL' htm
      rw [hH, ← hV]
      have e : F.a22 * F.S.hm = F.a22 * F.S.am * F.S.tm := by rw [← ham]; ring
      linarith
    · have := mul_lt_mul_of_pos_right hL htm
      have e : F.a22 * F.S.hm = F.a22 * F.S.am * F.S.tm := by rw [← ham]; ring
      linarith
  set q : ℝ := (F.a22 / F.a12 + Mn / F.S.hm) / 2 with hq
  have hmq : F.S.hm * q = (F.a22 / F.a12 * F.S.hm + Mn) / 2 := by
    rw [hq]; field_simp
  have hr' : F.a22 / F.a12 * F.S.hm < Mn := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hA12]; linarith
  have hqlow : F.a22 < F.a12 * q := by
    have h1' : F.a22 / F.a12 < q := by
      have : F.a22 / F.a12 < Mn / F.S.hm := by
        rw [lt_div_iff₀ hhm]; exact hr'
      rw [hq]; linarith
    have := mul_lt_mul_of_pos_left h1' hA12
    rwa [mul_div_cancel₀ _ hA12.ne'] at this
  have hqhm : F.S.hm * q < Mn := by rw [hmq]; linarith
  refine F.rimB_rupert (-1) q (by norm_num) ?_ (F.S.hX_of_ab hab) (F.S.hV_of_le hV.le)
    (fun _ => by linarith) ?_
  · have : F.S.km = F.S.cm * F.S.sm := hcm.symm
    have h3 : F.S.sm * (F.S.hm * q) < F.S.sm * (F.S.tm * F.S.cm) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hqhm hM2') hsm
    nlinarith
  have hZ2 := F.u0Z2_pos
  have e1 := F.u0Z2_sub_X
  refine Q4_eventually (z := fun i => F.toFrame7.GG
        (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG (quad (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, -1, 0⟩)
    (Or.inl (Or.inl ?_)) (Or.inr (Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩))))
  · simp only [quad_0, quad_1, g0, gZ2]; exact hZ2
  · simp only [quad_1, quad_2, gZ2, gX]
    rw [h2] at e1; linarith
  · simp only [quad_1, quad_2, F.GGc_tilt]
    have := mul_pos (sub_pos.2 F.S.sm_lt) (sub_pos.2 hqlow)
    linarith

/-- The Remark (mixed sector, `P > 0`, `V1 < 0`): rim `(xa, m1-, v, m2-, xb, m1+)` = `(3,6,5,2,4,0)`,
`M2 < 0`, `L1 > 0`: `-(a22 hm/a12) P < Q < -max(tm cm, H) P`; depths `(T, R, 0, X, X+, Z1)`
rising from `v` (6-cycle lex pattern). -/
theorem tM_mixed (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp = F.S.A1 * F.S.tp)
    (h2 : F.gg * F.S.am * F.S.dm = F.a12) (h1 : F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp)
    (hL : F.a12 * F.S.cm < F.a22 * F.S.am) (hL' : F.a12 * F.S.dp < F.a22 * F.S.am) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hA12 : 0 < F.a12 := F.A12_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hH := F.S.H_eq
  have hcm := F.S.cm_mul
  have ham := F.S.am_mul
  have hVe : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp) := by
    have h2' := F.S.dp_mul
    rw [hH, ← hV, ← h2']; ring
  set H := F.S.hm * F.S.tp + F.S.tm * F.S.hp with hHdef
  set Mx := max H (F.S.tm * F.S.cm) with hMx
  have hM1 : H ≤ Mx := le_max_left _ _
  have hM2' : F.S.tm * F.S.cm ≤ Mx := le_max_right _ _
  have hr : F.a12 * Mx < F.a22 * F.S.hm := by
    rw [hMx, mul_max_of_nonneg _ _ hA12.le]
    refine max_lt ?_ ?_
    · have := mul_lt_mul_of_pos_right hL' htm
      rw [hH, ← hV]
      have e : F.a22 * F.S.hm = F.a22 * F.S.am * F.S.tm := by rw [← ham]; ring
      linarith
    · have := mul_lt_mul_of_pos_right hL htm
      have e : F.a22 * F.S.hm = F.a22 * F.S.am * F.S.tm := by rw [← ham]; ring
      linarith
  set q : ℝ := -(F.a22 / F.a12 + Mx / F.S.hm) / 2 with hq
  have hmq : F.S.hm * q = -(F.a22 / F.a12 * F.S.hm + Mx) / 2 := by
    rw [hq]; field_simp
  have hr' : Mx < F.a22 / F.a12 * F.S.hm := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hA12]; linarith
  have hr'' : Mx / F.S.hm < F.a22 / F.a12 := by
    rw [div_lt_iff₀ hhm]; exact hr'
  have hqlow : -F.a22 < F.a12 * q := by
    have h1' : -(F.a22 / F.a12) < q := by rw [hq]; linarith
    have := mul_lt_mul_of_pos_left h1' hA12
    have e : F.a12 * -(F.a22 / F.a12) = -F.a22 := by field_simp
    linarith
  have hqhm : F.S.hm * q < -Mx := by rw [hmq]; linarith
  have hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * 1 < 0 := by
    have : F.S.km = F.S.cm * F.S.sm := hcm.symm
    have h3 : F.S.sm * (F.S.hm * q) < F.S.sm * (-(F.S.tm * F.S.cm)) :=
      mul_lt_mul_of_pos_left (by linarith) hsm
    rw [this]; nlinarith
  have hZ2 := F.u0Z2_pos
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  have hR : 0 < F.u0R := by
    have hA11 : 0 < F.a11 := lt_of_lt_of_le hA12 F.A12_le_A11
    unfold u0R
    have := F.g_pos
    positivity
  refine F.rimM_rupert 1 q one_pos hV1 (F.S.hX_of_ab hab) hVe (by linarith) ?_
  refine Q6m_eventually (z := fun i : ZMod 6 => F.toFrame7.GG
      (hex6 (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩
        ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i : ZMod 6 => F.toFrame7.GG
      (hex6 (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩
        ⟨F.S.tp, 0, F.S.hp⟩ i) ⟨q, 1, 0⟩) (Or.inl ?_) (Or.inl ?_) (Or.inr ⟨?_, ?_⟩) (Or.inl ?_) (Or.inl ?_)
  · simp only [hex6_2, hex6_1, g0, gR]; exact hR
  · simp only [hex6_2, hex6_3, g0, gZ2]; exact hZ2
  · simp only [hex6_3, hex6_4, gZ2, gX]
    rw [h2] at e1; linarith
  · simp only [hex6_3, hex6_4, F.GGc_tilt]
    have := mul_pos (sub_pos.2 F.S.sm_lt) (show 0 < F.a12 * q + F.a22 by linarith)
    linarith
  · simp only [hex6_4, hex6_5, gX, gZ1]
    have := mul_pos htm (show 0 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp - F.a12 by linarith)
    linarith
  · simp only [hex6_5, hex6_0, gZ1, gT]
    exact F.u0Z1_lt_T

/-- Sector (C+) (`dp = A1 tp`, `m2+` shown over the side `(xb, m1+)`, `M2 > 0`): rim
`(m1-, m2-, xb, m2+, m1+, xa)` = `(6,2,4,1,0,3)`, tilt `(1, 1)`; robust by `robust_cycCp`. -/
theorem tM_Cp (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp = F.S.A1 * F.S.tp)
    (h : F.a12 < F.gg * F.S.am * F.S.dm) : IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have hH : 0 < F.S.hm * F.S.tp + F.S.tm * F.S.hp := by
    have := F.S.hp_pos; have := F.S.tp_pos; positivity
  have e1 := F.u0Z2_sub_X
  have hVe : F.S.tm * F.S.kp = (F.S.hm * F.S.tp + F.S.tm * F.S.hp) * (1 - F.S.sp) := by
    have := F.S.hV_of_le hV.le
    have h2 := F.S.dp_mul
    have h3 := F.S.H_eq
    rw [h3, ← hV, ← h2]; ring
  refine F.rimCp_rupert 1 1 one_pos (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm])
    (F.S.hX_of_ab hab) hVe (by linarith) ?_
  have hXZ : F.u0X ≤ F.u0Z2 := by nlinarith [mul_pos hs (sub_pos.2 h)]
  exact robust_cycCp (F.u0X_lt_T hα) F.u0Z1_lt_T F.u0Z2p_lt_X (F.u0_W1 hXZ)
    (by nlinarith [mul_pos hs (sub_pos.2 h)])

/-- **Theorem M** (`a- < b+`, `d+ ≤ A1 t+`; `A12 < A11`, `A12 ≤ A22`), with the Remark: Rupert
except on `L_M'` (the `d- ≥ A1 t-` part is added in the assembly). -/
theorem thmM (hα : F.a12 < F.a11) (hab : F.S.am < F.S.bp) (hV : F.S.dp ≤ F.S.A1 * F.S.tp) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.dp = F.S.A1 * F.S.tp ∧ F.gg * F.S.am * F.S.dm = F.a12 ∧
        F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp ∧
        F.a12 * F.S.cm ≤ F.a22 * F.S.am ∧ F.a22 * F.S.am ≤ F.a12 * F.S.dp) := by
  have hA12 : 0 < F.a12 := F.A12_pos
  rcases lt_trichotomy (F.gg * F.S.am * F.S.dm) F.a12 with hZ | hZ | hZ
  · exact Or.inl (F.tM_B hα hab hV (Or.inl hZ))
  · rcases lt_trichotomy (F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp) F.a12 with hY | hY | hY
    · exact Or.inl (F.tM_B hα hab hV (Or.inr hY))
    · exact Or.inl (F.tM_B_tie hα hab hV hZ hY)
    · rcases hV.lt_or_eq with hV' | hV'
      · exact Or.inl (F.tM_C hα hab hV' (Or.inr ⟨hZ, hY⟩))
      · rcases lt_or_ge F.S.dp F.S.cm with hc | hc
        · exact Or.inl (F.tM_C_hid hα hab hV' hc (Or.inr ⟨hZ, hY⟩))
        · have hmul : F.a12 * F.S.cm ≤ F.a12 * F.S.dp := mul_le_mul_of_nonneg_left hc hA12.le
          rcases lt_or_ge (F.a22 * F.S.am) (F.a12 * F.S.cm) with hL | hL
          · exact Or.inl (F.tM_B_L1 hα hab hV' hZ hY hL (lt_of_lt_of_le hL hmul))
          · rcases lt_or_ge (F.a12 * F.S.dp) (F.a22 * F.S.am) with hL' | hL'
            · exact Or.inl (F.tM_mixed hα hab hV' hZ hY (lt_of_le_of_lt hmul hL') hL')
            · exact Or.inr ⟨hV', hZ, hY, hL, hL'⟩
  · rcases hV.lt_or_eq with hV' | hV'
    · exact Or.inl (F.tM_C hα hab hV' (Or.inl hZ))
    · exact Or.inl (F.tM_Cp hα hab hV' hZ)

/-! ### Group C: Theorem M' (`a- = b+`, corner `cm ≤ am`) -/

/-- ST data of the rim (B') `(v, m2-, xb, xa, m1+)` = `(5,2,4,3,0)` at `am = bp`. -/
theorem rimBp_st (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : P < 0)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0) (hQ : q + P < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 (i + 1))).sub (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)))
        ((F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 j)).sub (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)))) ∧
    (∀ j' : Fin 7, (∀ jj, j' ≠ quint (5 : Fin 7) 2 4 3 0 jj) → ∀ i : ZMod 5,
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 (i + 1))).sub (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)))
        ((F.toFrame7.ptC j').sub (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)))) := by
  have hE := F.S.hE_of_eq hab
  have hV := F.S.hVs_of_eq hab
  have hc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i) =
      quint (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_2, F.ptC_4, F.ptC_3, F.ptC_0]
  refine ⟨fun i j h1 h2 => ?_, fun j' hj' i => ?_⟩
  · simp only [hc]
    exact rimBp_cyc' F.S.sm F.S.km F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt F.S.km_pos
      F.S.tm_pos F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ i j h1 h2
  · simp only [hc]
    have R := rimBp_rest' F.S.sm F.S.km F.S.sp F.S.kp F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt
      F.S.km_pos F.S.tm_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos hV F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_1]; exact R _ (Or.inl rfl) i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · rw [F.ptC_6]; exact R _ (Or.inr rfl) i

/-- Rim (B') `(v, m2-, xb, xa, m1+)` at `am = bp`, robust depths. -/
theorem rimBp_rupert (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : P < 0)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0) (hQ : q + P < 0)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 => ![0, F.u0Z2, F.u0X, F.u0T, F.u0Z1] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i) =
      quint (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_2, F.ptC_4, F.ptC_3, F.ptC_0]
  obtain ⟨hcyc, hrest⟩ := F.rimBp_st hab P q hP hV1 hQ
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 2 4 3 0) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') hcyc hrest ?_
  have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)) ⟨F.S.tm, 0, -F.S.hm⟩) =
      fun i : ZMod 5 => ![0, F.u0Z2, F.u0X, F.u0T, F.u0Z1] i := by
    funext i
    rw [hc]
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, g0, gZ2, gX, gT, gZ1]
  rw [this]; exact hz

/-- ST data of the rim (C) `(m1-, m2-, xb, m1+, xa)` = `(6,2,4,0,3)` at `am = bp`. -/
theorem rimCe_st (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : 0 < P)
    (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P) (hQ : 0 < q + P) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 (i + 1))).sub (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)))
        ((F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 j)).sub (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)))) ∧
    (∀ j' : Fin 7, (∀ jj, j' ≠ quint (6 : Fin 7) 2 4 0 3 jj) → ∀ i : ZMod 5,
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 (i + 1))).sub (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)))
        ((F.toFrame7.ptC j').sub (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)))) := by
  have hE := F.S.hE_of_eq hab
  have hV := F.S.hVs_of_eq hab
  have hc : ∀ i, F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i) =
      quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_3]
  refine ⟨fun i j h1 h2 => ?_, fun j' hj' i => ?_⟩
  · simp only [hc]
    exact rimCe_cyc' F.S.sm F.S.km F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt F.S.km_pos
      F.S.tm_pos F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ i j h1 h2
  · simp only [hc]
    have R := rimCe_rest' F.S.sm F.S.km F.S.sp F.S.kp F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt
      F.S.km_pos F.S.tm_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos hV F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_3]) (hj' 3)
    · rw [F.ptC_1]; exact R _ (Or.inl rfl) i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · rw [F.ptC_5]; exact R _ (Or.inr rfl) i
    · exact absurd (by simp [quint_0]) (hj' 0)

/-- Rim (C) at `am = bp`, robust depths. -/
theorem rimCe_rupert (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : 0 < P)
    (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P) (hQ : 0 < q + P)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z1, F.u0T] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hc : ∀ i, F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i) =
      quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_3]
  obtain ⟨hcyc, hrest⟩ := F.rimCe_st hab P q hP hV1 hQ
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (6 : Fin 7) 2 4 0 3) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') hcyc hrest ?_
  have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i)) ⟨F.S.tm, 0, -F.S.hm⟩) =
      fun i : ZMod 5 => ![F.u0R, F.u0Z2, F.u0X, F.u0Z1, F.u0T] i := by
    funext i
    rw [hc]
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, gR, gZ2, gX, gZ1, gT]
  rw [this]; exact hz

/-- Rim (C) at `am = bp`, depth pattern `Q5s` (lex). -/
theorem rimCe_rupert_Q5s (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : 0 < P)
    (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P) (hQ : 0 < q + P)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5s fun i : ZMod 5 =>
      F.toFrame7.GG (quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i)
        ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i)
        ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.toFrame7.ptC (quint (6 : Fin 7) 2 4 0 3 i) =
      quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_0, F.ptC_3]
  obtain ⟨hcyc, hrest⟩ := F.rimCe_st hab P q hP hV1 hQ
  refine F.toFrame7.rupert_rim (k := 5) (by norm_num) (quint (6 : Fin 7) 2 4 0 3) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') hcyc hrest Q5s Q5s_open
    (fun z a ha => Q5s_smul ha) (fun z a => Q5s_shift a) ?_ (fun z hz hq => Q5s_unimodal hz hq)
  simp only [hc]; exact hQe

/-- ST data of the rim (D') `(xa, m1-, v, m2-, xb)` = `(3,6,5,2,4)` at `am = bp`. -/
theorem rimDp_st (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : 0 < P)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0) (hQ : q + P < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 (i + 1))).sub (F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i)))
        ((F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 j)).sub (F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i)))) ∧
    (∀ j' : Fin 7, (∀ jj, j' ≠ quint (3 : Fin 7) 6 5 2 4 jj) → ∀ i : ZMod 5,
      ST 1 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
        ((F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 (i + 1))).sub (F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i)))
        ((F.toFrame7.ptC j').sub (F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i)))) := by
  have hE := F.S.hE_of_eq hab
  have hV := F.S.hVs_of_eq hab
  have hc : ∀ i, F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i) =
      quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_3, F.ptC_6, F.ptC_5, F.ptC_2, F.ptC_4]
  refine ⟨fun i j h1 h2 => ?_, fun j' hj' i => ?_⟩
  · simp only [hc]
    exact rimDp_cyc' F.S.sm F.S.km F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt F.S.km_pos
      F.S.tm_pos F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ i j h1 h2
  · simp only [hc]
    have R := rimDp_rest' F.S.sm F.S.km F.S.sp F.S.kp F.S.tm F.S.hm F.S.tp F.S.hp q P F.S.sm_pos F.S.sm_lt
      F.S.km_pos F.S.tm_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos hV F.S.hm_pos F.S.hp_pos F.S.tp_pos hE hP hV1 hQ
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [F.ptC_0]; exact R _ (Or.inr rfl) i
    · rw [F.ptC_1]; exact R _ (Or.inl rfl) i
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · exact absurd (by simp [quint_4]) (hj' 4)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_1]) (hj' 1)

/-- Rim (D') at `am = bp`, depth pattern `Q5t` (lex). -/
theorem rimDp_rupert (hab : F.S.am = F.S.bp) (P q : ℝ) (hP : 0 < P)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0) (hQ : q + P < 0)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5t fun i : ZMod 5 =>
      F.toFrame7.GG (quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i)
        ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i)
        ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.toFrame7.ptC (quint (3 : Fin 7) 6 5 2 4 i) =
      quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_3, F.ptC_6, F.ptC_5, F.ptC_2, F.ptC_4]
  obtain ⟨hcyc, hrest⟩ := F.rimDp_st hab P q hP hV1 hQ
  refine F.toFrame7.rupert_rim (k := 5) (by norm_num) (quint (3 : Fin 7) 6 5 2 4) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') hcyc hrest Q5t Q5t_open
    (fun z a ha => Q5t_smul ha) (fun z a => Q5t_shift a) ?_ (fun z hz hq => Q5t_unimodal hz hq)
  simp only [hc]; exact hQe


/-- Sector (B'): rim `(v, m2-, xb, xa, m1+)` = `(5,2,4,3,0)`, tilt `(P, Q) = (-1, -1)`
(`P < 0, V1 < 0, Q + hm P < 0`); `Z2 < X`; robust by `robust_cycBp`. -/
theorem tMp_Bp (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp)
    (h : F.gg * F.S.am * F.S.dm < F.a12) : IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have e1 := F.u0Z2_sub_X
  refine F.rimBp_rupert hab (-1) (-1) (by norm_num) (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm])
    (by norm_num) ?_
  exact robust_cycBp F.u0Z2_pos (by nlinarith [mul_pos hs (sub_pos.2 h)]) (F.u0X_lt_T hα) F.u0Z1_lt_T

/-- Sector (C) at `a- = b+` (`m1+`, `xa` doubles over the corner): rim `(6,2,4,0,3)`, tilt
`(1, 1)`.  `Z2 > X` or `Z2 = X < Z1`; robust by `robust_cycC`. -/
theorem tMp_C (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp)
    (h : F.a12 < F.gg * F.S.am * F.S.dm ∨
      (F.gg * F.S.am * F.S.dm = F.a12 ∧ F.a12 < F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp)) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  refine F.rimCe_rupert hab 1 1 one_pos (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm]) (by norm_num) ?_
  have hXZ : F.u0X ≤ F.u0Z2 := by
    rcases h with h | ⟨h, _⟩
    · nlinarith [mul_pos hs (sub_pos.2 h)]
    · nlinarith
  refine robust_cycC (F.u0X_lt_T hα) F.u0Z1_lt_T (F.u0_W1 hXZ) ?_
  rcases h with h | ⟨h, h'⟩
  · left; nlinarith [mul_pos hs (sub_pos.2 h)]
  · right
    refine ⟨by rw [h] at e1; linarith, by nlinarith [mul_pos htm (sub_pos.2 h')]⟩

/-- `Z2 = Z1 = X` at `a- = b+`: sector (C), `P = 1`, `Q` large so that `L2 < 0` (metric
dependent), depth pattern `Q5s` (`z1<z0, z2<z0, z3<z4, z2<z4, z2<z3` with lex alternative). -/
theorem tMp_C_tie (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp)
    (h2 : F.gg * F.S.am * F.S.dm = F.a12) (h1 : F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp = F.a12) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have htp := F.S.tp_pos; have hg := F.g_pos
  have ham := F.S.am_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hd : 0 < F.gg * F.S.am * F.S.hp := by positivity
  set c := F.a22 - F.a12 * F.S.tp with hc
  set q : ℝ := 1 + (|c| + 1) / (F.gg * F.S.am * F.S.hp) with hq
  have hq0 : 0 < q := by
    have : 0 < (|c| + 1) / (F.gg * F.S.am * F.S.hp) := div_pos (by positivity) hd
    rw [hq]; linarith
  have e1 := F.u0Z2_sub_X
  have e2 := F.u0Z1_sub_X
  have hXZ : F.u0X ≤ F.u0Z2 := by rw [h2] at e1; linarith
  have hW := F.u0_W1 hXZ
  have hXT := F.u0X_lt_T hα
  have hZ2X : F.u0Z2 = F.u0X := by rw [h2] at e1; linarith
  have hZ1X : F.u0Z1 = F.u0X := by rw [h1] at e2; linarith
  have hXR : F.u0X < F.u0R ∧ F.u0Z2 < F.u0R := by
    rcases min_lt_iff.1 hW with a | a
    · exact ⟨by linarith, a⟩
    · exact ⟨by linarith, by linarith⟩
  refine F.rimCe_rupert_Q5s hab 1 q one_pos
    (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm, mul_pos (mul_pos hsm hhm) hq0]) (by linarith) ?_
  refine Q5s_eventually (z := fun i => F.toFrame7.GG
      (quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i)
        ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG
      (quint (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ i)
        ⟨q, 1, 0⟩) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) (Or.inr ⟨?_, ?_⟩)
  · simp only [quint_1, quint_0, gZ2, gR]; exact hXR.2
  · simp only [quint_2, quint_0, gX, gR]; exact hXR.1
  · simp only [quint_3, quint_4, gZ1, gT]; exact F.u0Z1_lt_T
  · simp only [quint_2, quint_4, gX, gT]; exact hXT
  · simp only [quint_2, quint_3, gX, gZ1]; exact hZ1X.symm
  · simp only [quint_2, quint_3, F.GGc_tilt]
    have e3 : q * (F.gg * F.S.am * F.S.hp) = F.gg * F.S.am * F.S.hp + (|c| + 1) := by
      rw [hq]; field_simp
    have e4 : q * (F.a12 - F.a11 * F.S.tp) = -(F.gg * F.S.am * F.S.hp + (|c| + 1)) := by
      have : F.a12 - F.a11 * F.S.tp = -(F.gg * F.S.am * F.S.hp) := by linarith
      rw [this]; linarith
    nlinarith [le_abs_self c]

/-- Sector (D'): rim `(xa, m1-, v, m2-, xb)` = `(3,6,5,2,4)` (`P > 0`, `Q + hm P < 0`, `V1 < 0`,
`m1+` hidden), `Z2 = X`, `L1 > 0` (needs `a12 < a22`, `cm ≤ am`); depth pattern `Q5t` lex. -/
theorem tMp_Dp (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp) (hc : F.S.cm ≤ F.S.am)
    (hne : F.a12 < F.a22) (h2 : F.gg * F.S.am * F.S.dm = F.a12) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hA12 : 0 < F.a12 := F.A12_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hcm := F.S.cm_mul
  have ham := F.S.am_mul
  have hr : 1 < F.a22 / F.a12 := by rw [lt_div_iff₀ hA12]; linarith
  have hmul : F.a12 * (F.a22 / F.a12) = F.a22 := by field_simp
  set q : ℝ := -(1 + F.a22 / F.a12) / 2 with hq
  have hq1 : q + 1 < 0 := by rw [hq]; linarith
  have hpos : 0 < F.a12 * q + F.a22 := by
    have : F.a12 * q = -(F.a12 + F.a12 * (F.a22 / F.a12)) / 2 := by rw [hq]; ring
    rw [this, hmul]; linarith
  have hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * 1 < 0 := by
    have h3 : F.S.tm * F.S.cm ≤ F.S.hm := by
      have := mul_le_mul_of_nonneg_left hc htm.le
      rw [← ham]; linarith
    have h4 : F.S.hm * q + F.S.tm * F.S.cm < 0 := by nlinarith [mul_pos hhm (neg_pos.2 hq1)]
    have : F.S.km = F.S.cm * F.S.sm := hcm.symm
    have h5 := mul_pos hsm (neg_pos.2 h4)
    rw [this]; nlinarith
  have e1 := F.u0Z2_sub_X
  have hZ2X : F.u0Z2 = F.u0X := by rw [h2] at e1; linarith
  have hR : 0 < F.u0R := by
    have hA11 : 0 < F.a11 := lt_of_lt_of_le hA12 F.A12_le_A11
    unfold u0R
    have := F.g_pos
    positivity
  refine F.rimDp_rupert hab 1 q one_pos hV1 (by linarith) ?_
  refine Q5t_eventually_lex (z := fun i => F.toFrame7.GG
      (quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i)
        ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG
      (quint (⟨1, 0, 0⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i)
        ⟨q, 1, 0⟩) (Or.inl ?_) (Or.inl ?_) (Or.inr ⟨?_, ?_⟩) (Or.inl ?_)
  · simp only [quint_2, quint_1, g0, gR]; exact hR
  · simp only [quint_2, quint_3, g0, gZ2]; exact F.u0Z2_pos
  · simp only [quint_3, quint_4, gZ2, gX]; exact hZ2X
  · simp only [quint_3, quint_4, F.GGc_tilt]
    have := mul_pos (sub_pos.2 F.S.sm_lt) hpos
    nlinarith
  · simp only [quint_4, quint_0, gX, gT]; exact F.u0X_lt_T hα

/-- **Theorem M'** (`a- = b+ ≥ c-`): Rupert except `A12 = A22`, `Z2 = X`, `Z1 < X`. -/
theorem thmMp (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp) (hc : F.S.cm ≤ F.S.am) :
    IsRupert (Finset.univ.image x) ∨
      (F.a12 = F.a22 ∧ F.gg * F.S.am * F.S.dm = F.a12 ∧
        F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp < F.a12) := by
  rcases lt_trichotomy (F.gg * F.S.am * F.S.dm) F.a12 with hZ | hZ | hZ
  · exact Or.inl (F.tMp_Bp hα hab hZ)
  · rcases lt_trichotomy (F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp) F.a12 with hY | hY | hY
    · rcases lt_or_eq_of_le F.A12_le_A22 with hne | hne
      · exact Or.inl (F.tMp_Dp hα hab hc hne hZ)
      · exact Or.inr ⟨hne, hZ, hY⟩
    · exact Or.inl (F.tMp_C_tie hα hab hZ hY)
    · exact Or.inl (F.tMp_C hα hab (Or.inr ⟨hZ, hY⟩))
  · exact Or.inl (F.tMp_C hα hab (Or.inl hZ))


/-! ### Group D: Theorem R (`A12 = A11`, `bp < am`) and Lemma LV -/

/-- Rim (S1) `(m1-, m2-, xb, xa)` = `(6,2,4,3)` at `u0`, tilt `(q, P, 0)` with `P > 0`, `V1 > 0`: the
bridge, with a `Q4` hypothesis on the tilted depths. -/
theorem rimS1_rupert (hb : F.S.bp < F.S.am) (P q : ℝ) (hP : 0 < P)
    (hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => F.toFrame7.GG
        (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩ +
      s * F.toFrame7.GG (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨q, P, 0⟩) :
    IsRupert (Finset.univ.image x) := by
  refine F.toFrame7.rupert_rim4 6 2 4 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩
    F.ptC_6 F.ptC_2 F.ptC_4 F.ptC_3 1 (Or.inl rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩
    (Or.inl F.S.tm_pos.ne') (rimS1_cyc F.S.sm F.S.km F.S.tm F.S.hm P q F.S.sm_pos F.S.sm_lt F.S.km_pos
      F.S.tm_pos F.S.hm_pos hP hV1) ?_ hQe
  intro j' h0 h1 h2 h3 i
  have R := rimS1_rest F.S.sm F.S.km F.S.sp F.S.kp F.S.tm F.S.hm F.S.tp F.S.hp P q F.S.sm_pos F.S.sm_lt
    F.S.km_pos F.S.tm_pos F.S.hm_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos F.S.tp_pos F.S.tp_lt F.S.hp_pos
    (F.S.hB_of_lt hb) (F.S.hVs_of_lt hb) hP hV1
  rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [F.ptC_0]; exact R _ (Or.inr (Or.inl rfl)) i
  · rw [F.ptC_1]; exact R _ (Or.inr (Or.inr rfl)) i
  · exact absurd rfl h1
  · exact absurd rfl h3
  · exact absurd rfl h2
  · rw [F.ptC_5]; exact R _ (Or.inl rfl) i
  · exact absurd rfl h0

/-- Rim (S2) `(v, m2-, xb, xa, m1+)` = `(5,2,4,3,0)` at `u0`, tilt `P < 0`, `V1 < 0`, robust depths. -/
theorem rimS2_rupert (hb : F.S.bp < F.S.am) (P q : ℝ) (hP : P < 0)
    (hV1 : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * P < 0)
    (hz : IsRobustUnimodal (k := 5) fun i : ZMod 5 => ![0, F.u0Z2, F.u0X, F.u0T, F.u0Z1] i) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hc : ∀ i, F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i) =
      quint (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, F.ptC_5, F.ptC_2, F.ptC_4, F.ptC_3, F.ptC_0]
  refine F.toFrame7.rupert_rim_rob (k := 5) (by norm_num) (quint (5 : Fin 7) 2 4 3 0) 1 (Or.inl rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨q, P, 0⟩ (Or.inl F.S.tm_pos.ne') ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact rimS2_cyc F.S.sm F.S.km F.S.tm F.S.hm F.S.tp F.S.hp P q F.S.sm_pos F.S.sm_lt F.S.km_pos
      F.S.tm_pos F.S.hm_pos F.S.tp_pos F.S.hp_pos (F.S.hB_of_lt hb) hP hV1 i j h1 h2
  · intro j' hj' i
    simp only [hc]
    have R := rimS2_rest F.S.sm F.S.km F.S.sp F.S.kp F.S.tm F.S.hm F.S.tp F.S.hp P q F.S.sm_pos F.S.sm_lt
      F.S.km_pos F.S.tm_pos F.S.hm_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos F.S.tp_pos F.S.hp_pos
      (F.S.hB_of_lt hb) (F.S.hVs_of_lt hb) hP hV1
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quint_4]) (hj' 4)
    · rw [F.ptC_1]; exact R _ (Or.inl rfl) i
    · exact absurd (by simp [quint_1]) (hj' 1)
    · exact absurd (by simp [quint_3]) (hj' 3)
    · exact absurd (by simp [quint_2]) (hj' 2)
    · exact absurd (by simp [quint_0]) (hj' 0)
    · rw [F.ptC_6]; exact R _ (Or.inr rfl) i
  · have : (fun i : ZMod 5 => F.toFrame7.GG (F.toFrame7.ptC (quint (5 : Fin 7) 2 4 3 0 i)) ⟨F.S.tm, 0, -F.S.hm⟩) =
        fun i : ZMod 5 => ![0, F.u0Z2, F.u0X, F.u0T, F.u0Z1] i := by
      funext i
      rw [hc]
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp [quint_0, quint_1, quint_2, quint_3, quint_4, g0, gZ2, gX, gT, gZ1]
    rw [this]; exact hz

theorem u0X_eq_T (heq : F.a12 = F.a11) : F.u0X = F.u0T := by unfold u0X u0T; rw [heq]


/-- (S1): rim `(m1-, m2-, xb, xa)` = `(6,2,4,3)`, tilt `(1,1)`, `ζ- > 0`: depths `(R, Z2, T, T)`,
`R > T` (`u0_R_gt_T_of_ge`); `Q4` (strict diagonals, no lex needed). -/
theorem tR_S1 (heq : F.a12 = F.a11) (hb : F.S.bp < F.S.am) (h : F.a11 < F.gg * F.S.am * F.S.dm) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hX := F.u0X_eq_T heq
  have e1 := F.u0Z2_sub_X
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have hZ : F.u0T < F.u0Z2 := by
    rw [← hX]; rw [heq] at e1
    nlinarith [mul_pos hs (sub_pos.2 h)]
  have hR := F.u0_R_gt_T_of_ge heq hZ.le
  refine F.rimS1_rupert hb 1 1 one_pos (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm]) ?_
  refine Q4_eventually (z := fun i => F.toFrame7.GG
      (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG
      (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨1, 1, 0⟩)
    (Or.inr (Or.inr (Or.inl (Or.inl ?_)))) (Or.inr (Or.inl (Or.inl ?_)))
  · simp only [quad_2, quad_1, gX, gZ2]; rw [hX]; exact hZ
  · simp only [quad_3, quad_0, gT, gR]; exact hR

/-- (S2): rim `(v, m2-, xb, xa, m1+)` = `(5,2,4,3,0)`, tilt `(-1,-1)`, `ζ- < 0`: depths
`(0, Z2, T, T, Z1)`; robust by `robust_cycS2`. -/
theorem tR_S2 (heq : F.a12 = F.a11) (hb : F.S.bp < F.S.am) (h : F.gg * F.S.am * F.S.dm < F.a11) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have hX := F.u0X_eq_T heq
  have e1 := F.u0Z2_sub_X
  have hs : 0 < (1 - F.S.sm) * F.S.tm := mul_pos (sub_pos.2 F.S.sm_lt) htm
  have hZ : F.u0Z2 < F.u0T := by
    rw [← hX]; rw [heq] at e1
    nlinarith [mul_pos hs (sub_pos.2 h)]
  refine F.rimS2_rupert hb (-1) (-1) (by norm_num) (by nlinarith [mul_pos hsm hhm, mul_pos htm hkm]) ?_
  rw [hX]
  exact robust_cycS2 F.u0Z2_pos hZ F.u0Z1_lt_T

/-- `ζ- = 0`, `a22 am < a11 cm`: sector (S1) with `L > 0`: `P = 1`, `q = -(a22/a11 + cm/am)/2`
(so `V1 > 0` and `L > 0`); `Q4` with lex alternative `w(xb) < w(m2-)`. -/
theorem tR_tie (heq : F.a12 = F.a11) (hb : F.S.bp < F.S.am) (h : F.gg * F.S.am * F.S.dm = F.a11)
    (hL : F.a22 * F.S.am < F.a11 * F.S.cm) : IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have ham := F.S.am_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  obtain ⟨gR, gT, gX, gZ1, gZ2, gZp, g0⟩ := F.GGc_u0
  have hX := F.u0X_eq_T heq
  have e1 := F.u0Z2_sub_X
  have hZ : F.u0Z2 = F.u0T := by
    rw [heq, h] at e1; rw [← hX]; linarith
  have hR := F.u0_R_gt_T_of_ge heq hZ.ge
  have hcm := F.S.cm_mul
  have ham' := F.S.am_mul
  -- q = -(a22/a11 + cm/am)/2
  set q : ℝ := -(F.a22 / F.a11 + F.S.cm / F.S.am) / 2 with hq
  have hlt : F.a22 / F.a11 < F.S.cm / F.S.am := by
    rw [div_lt_div_iff₀ hA11 ham]; linarith
  have hq1 : 0 < F.S.am * q + F.S.cm := by
    have : F.S.am * q = -(F.S.am * (F.a22 / F.a11) + F.S.cm) / 2 := by
      rw [hq]; field_simp
    rw [this]
    have h2 : F.S.am * (F.a22 / F.a11) < F.S.cm := by
      have := mul_lt_mul_of_pos_left hlt ham
      rwa [mul_div_cancel₀ _ ham.ne'] at this
    linarith
  have hV1 : 0 < F.S.sm * F.S.hm * q + F.S.tm * F.S.km * 1 := by
    have : F.S.sm * F.S.hm * q + F.S.tm * F.S.km * 1 = F.S.sm * F.S.tm * (F.S.am * q + F.S.cm) := by
      rw [← ham', ← hcm]; ring
    rw [this]; exact mul_pos (mul_pos hsm htm) hq1
  have hL1 : F.a12 * q + F.a22 < 0 := by
    rw [heq]
    have : F.a11 * q = -(F.a22 + F.a11 * (F.S.cm / F.S.am)) / 2 := by
      rw [hq]; field_simp
    rw [this]
    have h3 : F.a22 < F.a11 * (F.S.cm / F.S.am) := by
      have := mul_lt_mul_of_pos_left hlt hA11
      rwa [mul_div_cancel₀ _ hA11.ne'] at this
    linarith
  refine F.rimS1_rupert hb 1 q one_pos hV1 ?_
  refine Q4_eventually (z := fun i => F.toFrame7.GG
      (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨F.S.tm, 0, -F.S.hm⟩)
    (w := fun i => F.toFrame7.GG
      (quad (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ i) ⟨q, 1, 0⟩)
    (Or.inr (Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩)))) (Or.inl (Or.inl ?_))
  · simp only [quad_2, quad_1, gX, gZ2]; rw [hX, hZ]
  · simp only [quad_2, quad_1, F.GGc_tilt]
    have := mul_pos (sub_pos.2 F.S.sm_lt) (neg_pos.2 hL1)
    nlinarith
  · simp only [quad_1, quad_0, gZ2, gR]; rw [hZ]; exact hR

/-- **Theorem R**. -/
theorem thmR (heq : F.a12 = F.a11) (hb : F.S.bp < F.S.am) :
    IsRupert (Finset.univ.image x) ∨
      (F.gg * F.S.am * F.S.dm = F.a11 ∧ F.a11 * F.S.cm ≤ F.a22 * F.S.am) := by
  rcases lt_trichotomy (F.gg * F.S.am * F.S.dm) F.a11 with h | h | h
  · exact Or.inl (F.tR_S2 heq hb h)
  · by_cases hL : F.a22 * F.S.am < F.a11 * F.S.cm
    · exact Or.inl (F.tR_tie heq hb h hL)
    · exact Or.inr ⟨h, not_lt.1 hL⟩
  · exact Or.inl (F.tR_S1 heq hb h)


set_option maxHeartbeats 1000000 in
/-- **Lemma LV at the view `(1, 0, T)`**: rim `(xb, m1+, v, m1-)` (v over the open side
`(m1+, m1-)`, `xa` hidden), tilt `-e_y` (`P = -1`), `T` in the interval `I`; robust by Lemma Q
(`robust_quad_of_nws`), no lex needed. -/
theorem tLV (heq : F.a12 = F.a11) (T : ℝ) (h1 : F.S.mum - F.S.am < T) (h2 : -F.S.bp < T)
    (h3 : T < F.S.ap - F.S.mup) (h4 : T < F.S.bm) : IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have hhm := F.S.hm_pos; have hkm := F.S.km_pos; have hsm := F.S.sm_pos
  have htp := F.S.tp_pos; have hhp := F.S.hp_pos; have hg := F.g_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hmum := F.S.mum_mul; have hmup := F.S.mup_mul
  have hdm := F.S.dm_mul; have hdp := F.S.dp_mul
  have hap := F.S.ap_mul; have ham := F.S.am_mul
  have hbp := F.S.bp_mul; have hbm := F.S.bm_mul
  have hmum0 : 0 < F.S.mum := div_pos F.S.dm_pos htm
  have hmup0 : 0 < F.S.mup := div_pos F.S.dp_pos htp
  -- polynomial forms
  have hs1 : 0 < 1 - F.S.sp := by linarith [F.S.sp_lt]
  have hs2 : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
  have m1 : T * F.S.tp < (F.S.ap - F.S.mup) * F.S.tp := mul_lt_mul_of_pos_right h3 htp
  have m2 : (F.S.mum - F.S.am) * F.S.tm < T * F.S.tm := mul_lt_mul_of_pos_right h1 htm
  have m3 : -F.S.bp * (1 - F.S.tp) < T * (1 - F.S.tp) :=
    mul_lt_mul_of_pos_right h2 (by linarith [F.S.tp_lt])
  have m4 : T * (1 - F.S.tm) < F.S.bm * (1 - F.S.tm) :=
    mul_lt_mul_of_pos_right h4 (by linarith [F.S.tm_lt])
  have dpp := F.S.dp_pos
  have dmp := F.S.dm_pos
  have p1d : F.S.dp < F.S.hp - T * F.S.tp := by linarith
  have p2d : F.S.dm < F.S.hm + T * F.S.tm := by linarith
  have p1 : 0 < F.S.hp - T * F.S.tp := by linarith
  have p2 : 0 < F.S.hm + T * F.S.tm := by linarith
  have px1 : 0 < F.S.hp - T * F.S.tp + T := by linarith
  have px2 : 0 < F.S.hm + F.S.tm * T - T := by linarith
  have q1 : F.S.kp < (F.S.hp - T * F.S.tp) * (1 - F.S.sp) := by
    calc F.S.kp = F.S.dp * (1 - F.S.sp) := hdp.symm
      _ < _ := mul_lt_mul_of_pos_right p1d hs1
  have q2 : F.S.km < (F.S.hm + T * F.S.tm) * (1 - F.S.sm) := by
    calc F.S.km = F.S.dm * (1 - F.S.sm) := hdm.symm
      _ < _ := mul_lt_mul_of_pos_right p2d hs2
  have hc : ∀ i, F.toFrame7.ptC (quad (4 : Fin 7) 0 5 6 i) =
      quad (⟨0, 1, 0⟩ : C3) ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, F.ptC_4, F.ptC_0, F.ptC_5, F.ptC_6]
  refine F.toFrame7.rupert_rim_rob (k := 4) (by norm_num) (quad (4 : Fin 7) 0 5 6) 1 (Or.inl rfl)
    ⟨1, 0, T⟩ ⟨0, -1, 0⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · intro i j hi hj
    simp only [hc]
    exact rimLV_cyc F.S.tp F.S.hp F.S.tm F.S.hm T htp hhp htm hhm p1 p2 i j hi hj
  · intro j' hj' i
    simp only [hc]
    have R := rimLV_rest F.S.sm F.S.km F.S.sp F.S.kp F.S.tp F.S.hp F.S.tm F.S.hm T F.S.sm_pos F.S.sm_lt
      F.S.km_pos F.S.sp_pos F.S.sp_lt F.S.kp_pos htp hhp htm hhm p1 p2 px1 (by linarith) q1 q2
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_1]) (hj' 1)
    · rw [F.ptC_1]; exact R _ (Or.inl rfl) i
    · rw [F.ptC_2]; exact R _ (Or.inr (Or.inl rfl)) i
    · rw [F.ptC_3]; exact R _ (Or.inr (Or.inr rfl)) i
    · exact absurd (by simp [quad_0]) (hj' 0)
    · exact absurd (by simp [quad_2]) (hj' 2)
    · exact absurd (by simp [quad_3]) (hj' 3)
  · have : (fun i : ZMod 4 => F.toFrame7.GG (F.toFrame7.ptC (quad (4 : Fin 7) 0 5 6 i)) ⟨1, 0, T⟩) =
        quad F.a11 (F.a11 * F.S.tp + F.gg * T * F.S.hp) 0 (F.a11 * F.S.tm - F.gg * T * F.S.hm) := by
      funext i
      rw [hc]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, F.GG_eq] <;> first | (rw [heq]; ring) | ring
    rw [this]
    rcases le_or_gt 0 T with hT | hT
    · refine robust_quad_of_nws (Or.inr (Or.inr (Or.inl ?_))) (Or.inr (Or.inl ?_))
      · nlinarith [mul_nonneg (mul_nonneg hg.le hT) hhp.le]
      · nlinarith [mul_nonneg (mul_nonneg hg.le hT) hhm.le, F.S.tm_lt]
    · refine robust_quad_of_nws (Or.inr (Or.inr (Or.inr ?_))) (Or.inl ?_)
      · nlinarith [mul_pos (mul_pos hg (neg_pos.2 hT)) hhm]
      · nlinarith [mul_pos (mul_pos hg (neg_pos.2 hT)) hhp, F.S.tp_lt]


/-- **Lemma LV**: on `C1`, `D2p > 0` gives Rupert (picks `T ∈ I`; `I ≠ ∅` is `D2p > 0` and the roofs). -/
theorem lemmaLV (heq : F.a12 = F.a11) (hD : 0 < F.S.D2p) : IsRupert (Finset.univ.image x) := by
  have e := F.S.D2p_eq
  have hpos : 0 < F.S.tp * F.S.tm * (1 - F.S.sp) * (1 - F.S.sm) := by
    have := F.S.tp_pos; have := F.S.tm_pos
    have : 0 < 1 - F.S.sp := by linarith [F.S.sp_lt]
    have : 0 < 1 - F.S.sm := by linarith [F.S.sm_lt]
    positivity
  rw [e] at hD
  have hA : 0 < F.S.A1 - F.S.mup - F.S.mum := pos_of_mul_pos_right hD hpos.le
  unfold Shape18.A1 at hA
  have l1 := F.S.mum_lt; have l2 := F.S.mup_lt
  have r1 := F.S.dm_lt_bm; have r2 := F.S.dp_lt_bp
  have b1 := F.S.bm_pos; have b2 := F.S.bp_pos
  have dpp := F.S.dp_pos
  have hLU : max (F.S.mum - F.S.am) (-F.S.bp) < min (F.S.ap - F.S.mup) F.S.bm := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨T, hT1, hT2⟩ := exists_between hLU
  rw [max_lt_iff] at hT1
  rw [lt_min_iff] at hT2
  exact F.tLV heq T hT1.1 hT1.2 hT2.1 hT2.2

end Frame18

/-! ### Group E: `Z`-images and the assembly -/

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

theorem zFrame_gg : F.zFrame.gg = F.gg := by
  show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
  exact inner_neg_neg _ _

theorem zFrame_A1 : F.zFrame.S.A1 = F.S.A1 := by
  show F.S.am + F.S.ap = F.S.ap + F.S.am
  ring

theorem zFrame_a12 : F.zFrame.a12 = F.a12 := rfl
theorem zFrame_a11 : F.zFrame.a11 = F.a11 := rfl
theorem zFrame_a22 : F.zFrame.a22 = F.a22 := rfl

theorem thmMz (hα : F.a12 < F.a11) (hab : F.S.ap < F.S.bm) (hV : F.S.dm ≤ F.S.A1 * F.S.tm) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.dm = F.S.A1 * F.S.tm ∧ F.gg * F.S.ap * F.S.dp = F.a12 ∧
        F.a12 < F.a11 * F.S.tm - F.gg * F.S.ap * F.S.hm ∧
        F.a12 * F.S.cp ≤ F.a22 * F.S.ap ∧ F.a22 * F.S.ap ≤ F.a12 * F.S.dm) := by
  have hV' : F.zFrame.S.dp ≤ F.zFrame.S.A1 * F.zFrame.S.tp := by
    rw [F.zFrame_A1]; exact hV
  rcases F.zFrame.thmM hα hab hV' with h | ⟨e1, e2, e3, e4, e5⟩
  · exact Or.inl (rupert_of_z h)
  · right
    rw [F.zFrame_A1, F.zFrame_gg] at *
    exact ⟨e1, e2, e3, e4, e5⟩

theorem thmMpz (hα : F.a12 < F.a11) (hab : F.S.ap = F.S.bm) (hc : F.S.cp ≤ F.S.ap) :
    IsRupert (Finset.univ.image x) ∨
      (F.a12 = F.a22 ∧ F.gg * F.S.ap * F.S.dp = F.a12 ∧
        F.a11 * F.S.tm - F.gg * F.S.ap * F.S.hm < F.a12) := by
  rcases F.zFrame.thmMp hα hab hc with h | ⟨e1, e2, e3⟩
  · exact Or.inl (rupert_of_z h)
  · right
    rw [F.zFrame_gg] at *
    exact ⟨e1, e2, e3⟩

theorem thmRz (heq : F.a12 = F.a11) (hb : F.S.bm < F.S.ap) :
    IsRupert (Finset.univ.image x) ∨
      (F.gg * F.S.ap * F.S.dp = F.a11 ∧ F.a11 * F.S.cp ≤ F.a22 * F.S.ap) := by
  rcases F.zFrame.thmR heq hb with h | ⟨e1, e2⟩
  · exact Or.inl (rupert_of_z h)
  · right
    rw [F.zFrame_gg] at *
    exact ⟨e1, e2⟩

end Frame18

/-- **The special positions of type 18 after section 36**. -/
def CaseC18Special' (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame18 x,
    (F.a12 = F.a11 ∧ F.S.bp ≤ F.S.am ∧ F.S.bm ≤ F.S.ap ∧ ¬ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am) ∧
        F.S.D2p ≤ 0 ∧
        (F.S.am = F.S.bp ∨ (F.gg * F.S.am * F.S.dm = F.a11 ∧ F.a22 * F.S.am ≥ F.a11 * F.S.cm)) ∧
        (F.S.ap = F.S.bm ∨ (F.gg * F.S.ap * F.S.dp = F.a11 ∧ F.a22 * F.S.ap ≥ F.a11 * F.S.cp)))
    ∨ (F.S.dp = F.S.A1 * F.S.tp ∧ F.S.A1 * F.S.tm ≤ F.S.dm ∧ F.S.ap < F.S.cp ∧ F.S.am < F.S.cm ∧
        F.gg * F.S.am * F.S.dm = F.a12 ∧ F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp > F.a12 ∧
        F.a12 * F.S.cm ≤ F.a22 * F.S.am ∧ F.a22 * F.S.am ≤ F.a12 * F.S.dp)
    ∨ (F.S.dm = F.S.A1 * F.S.tm ∧ F.S.A1 * F.S.tp ≤ F.S.dp ∧ F.S.ap < F.S.cp ∧ F.S.am < F.S.cm ∧
        F.gg * F.S.ap * F.S.dp = F.a12 ∧ F.a11 * F.S.tm - F.gg * F.S.ap * F.S.hm > F.a12 ∧
        F.a12 * F.S.cp ≤ F.a22 * F.S.ap ∧ F.a22 * F.S.ap ≤ F.a12 * F.S.dm)
    ∨ (F.S.am = F.S.bp ∧ F.S.am = F.S.cm ∧ F.a12 = F.a22 ∧ F.gg * F.S.am * F.S.dm = F.a12 ∧
        F.a11 * F.S.tp - F.gg * F.S.am * F.S.hp < F.a12)
    ∨ (F.S.ap = F.S.bm ∧ F.S.ap = F.S.cp ∧ F.a12 = F.a22 ∧ F.gg * F.S.ap * F.S.dp = F.a12 ∧
        F.a11 * F.S.tm - F.gg * F.S.ap * F.S.hm < F.a12)

/-- **Off the special positions of section 36, a frame is Rupert.**  `A12 = A11`: Theorem 4
(`rupert_of_a12_eq_a11`), then Lemma LV and Theorem R (and `Z`); `A12 < A11`: the corners by
Theorem M' (and `Z`), then `rupert_or_V'`, whose V case is closed by Theorem M (and `Z`). -/
theorem Frame18.isRupert_of_not_special' {x : Fin 7 → ℝ³} (F : Frame18 x)
    (hx : Function.Injective x) (h : ¬ CaseC18Special' x) :
    IsRupert (Finset.univ.image x) := by
  by_cases heq : F.a12 = F.a11
  · -- the face `C1`
    by_cases hr : F.S.am < F.S.bp ∨ F.S.ap < F.S.bm ∨ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am)
    · exact F.rupert_of_a12_eq_a11 heq hr
    push Not at hr
    obtain ⟨n1, n2, n3⟩ := hr
    have n3' : ¬ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am) :=
      fun hh => absurd (n3 hh.1) (not_le.2 hh.2)
    by_cases hD : 0 < F.S.D2p
    · exact F.lemmaLV heq hD
    have hD' : F.S.D2p ≤ 0 := not_lt.1 hD
    have A : IsRupert (Finset.univ.image x) ∨
        (F.S.am = F.S.bp ∨ (F.gg * F.S.am * F.S.dm = F.a11 ∧ F.a22 * F.S.am ≥ F.a11 * F.S.cm)) := by
      rcases n1.lt_or_eq with hb | hb
      · rcases F.thmR heq hb with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl hb.symm)
    have B : IsRupert (Finset.univ.image x) ∨
        (F.S.ap = F.S.bm ∨ (F.gg * F.S.ap * F.S.dp = F.a11 ∧ F.a22 * F.S.ap ≥ F.a11 * F.S.cp)) := by
      rcases n2.lt_or_eq with hb | hb
      · rcases F.thmRz heq hb with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl hb.symm)
    rcases A with A | A
    · exact A
    rcases B with B | B
    · exact B
    exact absurd ⟨F, Or.inl ⟨heq, n1, n2, n3', hD', A, B⟩⟩ h
  · have hα : F.a12 < F.a11 := lt_of_le_of_ne F.A12_le_A11 heq
    by_cases c1 : F.S.am = F.S.bp ∧ F.S.am = F.S.cm
    · rcases F.thmMp hα c1.1 c1.2.ge with h' | ⟨e1, e2, e3⟩
      · exact h'
      · exact absurd ⟨F, Or.inr (Or.inr (Or.inr (Or.inl ⟨c1.1, c1.2, e1, e2, e3⟩)))⟩ h
    by_cases c2 : F.S.ap = F.S.bm ∧ F.S.ap = F.S.cp
    · rcases F.thmMpz hα c2.1 c2.2.ge with h' | ⟨e1, e2, e3⟩
      · exact h'
      · exact absurd ⟨F, Or.inr (Or.inr (Or.inr (Or.inr ⟨c2.1, c2.2, e1, e2, e3⟩)))⟩ h
    rcases F.rupert_or_V' hx hα c1 c2 with h' | ⟨h1, h2, hcp, hcm, hV⟩
    · exact h'
    rcases hV with hV | hV
    · rcases F.thmM hα h1 hV with hr | ⟨e1, e2, e3, e4, e5⟩
      · exact hr
      by_cases hd : F.S.dm < F.S.A1 * F.S.tm
      · rcases F.thmMz hα h2 hd.le with hr | ⟨f1, -⟩
        · exact hr
        · exact absurd f1 hd.ne
      · exact absurd ⟨F, Or.inr (Or.inl ⟨e1, not_lt.1 hd, hcp, hcm, e2, e3, e4, e5⟩)⟩ h
    · rcases F.thmMz hα h2 hV with hr | ⟨e1, e2, e3, e4, e5⟩
      · exact hr
      by_cases hd : F.S.dp < F.S.A1 * F.S.tp
      · rcases F.thmM hα h1 hd.le with hr | ⟨f1, -⟩
        · exact hr
        · exact absurd f1 hd.ne
      · exact absurd ⟨F, Or.inr (Or.inr (Or.inl ⟨e1, not_lt.1 hd, hcp, hcm, e2, e3, e4, e5⟩))⟩ h

end Minimality.CaseC18

end
