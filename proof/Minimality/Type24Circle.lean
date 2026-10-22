module

public import Minimality.Type24Circle236
public import Minimality.Type24Lambda
public import Minimality.Type24DS

@[expose] public section

/-!
# Type 24: the circle of 236 (Theorem 20.13) and the uniform statements 20.14, 20.9″, 20.9‴

`FEWER-FACES-PROOFS.md` §20, continued (2) and (3) (subagents UU and cu14, refereed 2026-10-22,
scratch `referee_UU/`, `referee_cu14/`), at `K`'s own metric.

* **Gram entries and X-only depths** (`Gram3`, `Gram3.depth`, `Gram3.cut`, `Type24.gram`,
  `Type24.inner_gram`): a view `d = d_a e_a + d_b e_b + d_c e_c` has the covector `u = G d`
  and the depths `z(v) = z(1) + u · X(v)`; the view cut is `dᵀ G d = ‖d‖² > 0`.  Failure
  patterns as strict rows (`SFails`).
* **Edge crossings with a general axle** (`EdgeRim`, `isRupert_edgeRim`): the rim data of
  `CapRim0` for any edge `r 0 — d` along the view; certified when unimodal or with a
  depth-separated parallel pair (Theorems 7.3, 8.10 with 8.9).
* **E23's three cases** (`e23_good`): with the rim `(3, 6, 1, 0, 5)` and
  (*) `z6 > z1, z0, z5`, `z3 > z0, z5`, the rim is unimodal (`z1 > z3`) or depth-separated by
  `(6; 1 0 5 | 3)` (`z3 > z6`) or `(3; 6 | 5 0 1)` (`z6 > z3 > z1`).
* **Theorem 20.13 with (K̄236)** (`K236bar`, X-only: the ten LPs as one implication;
  `isRupert_circle236_octant`): on the closed obtuse octant `c_ab, c_ac, c_bc ≤ 0`, `T′(6,2)`
  or `S_6` does not fail, or `E23` is DS-good; so `K` is Rupert.  With (K236) on the open octant
  (`K236`, `isRupert_circle236_open`): `T′(6,2)`'s second pattern is excluded by Lemma 20.12
  (S1) (`Cu13.S1`, `Type24.s1_pattern`), with `c5 < ω3 a5` read off `T′(6,2)`'s rim
  (`Type24.c5_lt_of_rimT62`: the geometric half of (S1), from the rim's determinant tests).
* **Corollary 20.14** (`isRupert_type24_obtuse_octant`): the window chain (20.5, 20.11) or
  20.13 with (K̄236) covers the closed obtuse octant.
* **Theorem 20.9″** (`isRupert_type24_uniform_circle`): side-safety (20.8′) and 20.14's
  hypotheses give Rupert at every metric.  **Theorem 20.9‴** (`isRupert_type24_uniform_ds`): the
  same with DS side-safety (20.16), or with the regions of 20.17 (`DSRegionsCovered`,
  `isRupert_type24_uniform_dsRegions`), or with the acute side by 20.17, 20.18 and 20.19
  (`AcuteCovered`, `isRupert_type24_uniform_acute`).

The views are those of §20.22 up to positive factors: `d6 = (1 + ω4) d(s6)` (`view6`) and
`d23 = a3 d(s23) = X3 − X2`; the X-only hypotheses are homogeneous in the views.  The (K236)
LPs are hypotheses (`K236`, `K236bar`), as (H_h), (H_l) are for the window chain; Lemma 20.12
(S2, S4, S5) explains six of them in closed form (`Cu13.S2`, `S4`, `S5`) and is not needed here.
Not formalized: (S3), the four LPs `z3 > z0, z5` in closed form, the per-class certificates of
§20.20 (Proposition 20.7′), the class counts.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Gram entries and depths at a view -/

/-- The six Gram entries of the axes at the cap `1`: `g_x = ‖e_x‖²`, `h_xy = ⟪e_x, e_y⟫`. -/
structure Gram3 where
  ga : ℝ
  gb : ℝ
  gc : ℝ
  hab : ℝ
  hac : ℝ
  hbc : ℝ

namespace Gram3

/-- The covector `u = G d`, first entry. -/
def ua (G : Gram3) (d : Fin 3 → ℝ) : ℝ := G.ga * d 0 + G.hab * d 1 + G.hac * d 2
/-- The covector `u = G d`, second entry. -/
def ub (G : Gram3) (d : Fin 3 → ℝ) : ℝ := G.hab * d 0 + G.gb * d 1 + G.hbc * d 2
/-- The covector `u = G d`, third entry. -/
def uc (G : Gram3) (d : Fin 3 → ℝ) : ℝ := G.hac * d 0 + G.hbc * d 1 + G.gc * d 2

/-- The depth of `v` at the view `d` (relative to the cap `1`), in oblique coordinates. -/
def depth (G : Gram3) (Xa Xb Xc : Fin 7 → ℝ) (d : Fin 3 → ℝ) (v : Fin 7) : ℝ :=
  covDepth Xa Xb Xc (G.ua d) (G.ub d) (G.uc d) v

/-- The view cut `dᵀ G d`. -/
def cut (G : Gram3) (d : Fin 3 → ℝ) : ℝ := d 0 * G.ua d + d 1 * G.ub d + d 2 * G.uc d

end Gram3

/-- A strict failure pattern of a 4-corner rim with diagonals `{d₀, d₁}`, `{e₀, e₁}`: the four
rows `z d < z e`, or the four reversed rows. -/
def SFails (z : Fin 7 → ℝ) (d₀ d₁ e₀ e₁ : Fin 7) : Prop :=
  (z d₀ < z e₀ ∧ z d₀ < z e₁ ∧ z d₁ < z e₀ ∧ z d₁ < z e₁) ∨
    (z e₀ < z d₀ ∧ z e₁ < z d₀ ∧ z e₀ < z d₁ ∧ z e₁ < z d₁)

/-- A closed failure with distinct cross-diagonal depths is strict. -/
theorem sFails_of_fails4 {x : Fin 7 → ℝ³} {w o : ℝ³} {f : Fin 7 → ℝ}
    (hf : ∀ v, ⟪x v, w⟫ = ⟪o, w⟫ + f v) {d₀ d₁ e₀ e₁ : Fin 7}
    (hF : Fails4 (x d₀) (x d₁) (x e₀) (x e₁) w)
    (n1 : ⟪x d₀, w⟫ ≠ ⟪x e₀, w⟫) (n2 : ⟪x d₀, w⟫ ≠ ⟪x e₁, w⟫) (n3 : ⟪x d₁, w⟫ ≠ ⟪x e₀, w⟫)
    (n4 : ⟪x d₁, w⟫ ≠ ⟪x e₁, w⟫) : SFails f d₀ d₁ e₀ e₁ := by
  simp only [Fails4, max_le_iff, le_min_iff] at hF
  rw [hf, hf] at n1 n2 n3 n4
  simp only [ne_eq, add_right_inj] at n1 n2 n3 n4
  rcases hF with ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ <;> rw [hf, hf] at a b c d <;>
    simp only [add_le_add_iff_left] at a b c d
  · exact Or.inl ⟨lt_of_le_of_ne a n1, lt_of_le_of_ne c n2, lt_of_le_of_ne b n3,
      lt_of_le_of_ne d n4⟩
  · exact Or.inr ⟨lt_of_le_of_ne a (Ne.symm n1), lt_of_le_of_ne b (Ne.symm n2),
      lt_of_le_of_ne c (Ne.symm n3), lt_of_le_of_ne d (Ne.symm n4)⟩

/-- The depths of a certified 4-corner test, in either orientation, are distinct across the
diagonals, and its view is nonzero. -/
theorem QuadTest'.cross_ne {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest' V u y a c b) :
    u ≠ 0 ∧ ⟪y, u⟫ ≠ ⟪a, u⟫ ∧ ⟪y, u⟫ ≠ ⟪b, u⟫ ∧ ⟪c, u⟫ ≠ ⟪a, u⟫ ∧ ⟪c, u⟫ ≠ ⟪b, u⟫ := by
  rcases h with ⟨-, -, -, hu, -, -, -, -, -, -, -, -, -, -, -, -, -, hz, -⟩ |
    ⟨-, -, -, hu, -, -, -, -, -, -, -, -, -, -, -, -, -, hz, -⟩ <;>
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
    first
    | exact ⟨hu, z1, z3, Ne.symm z4, z6⟩
    | exact ⟨hu, z3, z1, z6, Ne.symm z4⟩

namespace Type24

/-- The Gram entries of a type-24 point set at its cap. -/
noncomputable def gram (x : Fin 7 → ℝ³) : Gram3 :=
  ⟨⟪x 0 - x 1, x 0 - x 1⟫, ⟪x 2 - x 1, x 2 - x 1⟫, ⟪x 6 - x 1, x 6 - x 1⟫,
    ⟪x 0 - x 1, x 2 - x 1⟫, ⟪x 0 - x 1, x 6 - x 1⟫, ⟪x 2 - x 1, x 6 - x 1⟫⟩

/-- The space view of oblique view coordinates `d`. -/
noncomputable def viewOf (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) : ℝ³ :=
  d 0 • (x 0 - x 1) + d 1 • (x 2 - x 1) + d 2 • (x 6 - x 1)

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- **Depths at a view from the Gram entries** (`z(v) = z(1) + u · X(v)`, `u = G d`). -/
theorem inner_gram (d : Fin 3 → ℝ) (v : Fin 7) :
    ⟪x v, viewOf x d⟫ = ⟪x 1, viewOf x d⟫ +
      (gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) d v := by
  rw [inner_covDepth T.rep]
  simp only [Gram3.depth, Gram3.ua, Gram3.ub, Gram3.uc, gram, viewOf, inner_add_right,
    real_inner_smul_right, real_inner_comm (x 0 - x 1) (x 2 - x 1),
    real_inner_comm (x 0 - x 1) (x 6 - x 1), real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  ring_nf

omit T in
/-- **The view cut**: `dᵀ G d = ‖d‖²`. -/
theorem cut_gram (d : Fin 3 → ℝ) : (gram x).cut d = ⟪viewOf x d, viewOf x d⟫ := by
  simp only [Gram3.cut, Gram3.ua, Gram3.ub, Gram3.uc, gram, viewOf, inner_add_right,
    inner_add_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_comm (x 0 - x 1) (x 2 - x 1), real_inner_comm (x 0 - x 1) (x 6 - x 1),
    real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  ring

end Type24

/-! ### Edge crossings with a general axle -/

/-- **The rim of an edge crossing at the view `u`** (as `CapRim0`, for any axle): the rim
`x ∘ r` is strictly convex and counterclockwise at `u`, the other end `x d = x (r 0) − h u`
(`h ≠ 0`) of the axle is a double over the corner `r 0`, every other point is strictly inside,
the rim depths are distinct and the rim has no horizontal double normal. -/
def EdgeRim (x : Fin 7 → ℝ³) (u : ℝ³) (d : Fin 7) (h : ℝ) (k : ℕ) [NeZero k]
    (r : ZMod k → Fin 7) : Prop :=
  3 ≤ k ∧ h ≠ 0 ∧ x d = x (r 0) - h • u ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ v, v ≠ d → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) u) ∧
    Function.Injective (fun i => ⟪x (r i), u⟫) ∧
    NoHDNAt (univ.image fun i => x (r i)) u

/-- **An edge crossing that is DS-good certifies `K`** (Theorem 7.3 with 8.9 if unimodal,
Theorem 8.10 with 8.9 for a depth-separated parallel pair). -/
theorem isRupert_edgeRim {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0) {d : Fin 7} {h : ℝ} {k : ℕ}
    [NeZero k] {r : ZMod k → Fin 7} (hR : EdgeRim x u d h k r)
    (hg : DSGood (fun i => x (r i)) u (fun i => ⟪x (r i), u⟫)) : IsRupert (univ.image x) := by
  classical
  obtain ⟨hk, hh, hd, hcyc, hrest, -, hnd⟩ := hR
  rcases hg with hz | ⟨a, c, hpp, hds⟩
  · refine isRupert_of_edgeView_uniform (univ.image x) ∅ {x d} (univ.image fun i => x (r i)) u hu
      hk (fun i => x (r i)) (fun i => mem_image_of_mem x (mem_univ _))
      (fun _ => Finset.notMem_empty _) hcyc ?_ hz hnd (fun i => mem_image_of_mem _ (mem_univ _))
      (fun m hm => absurd hm (Finset.notMem_empty _)) ?_
    · intro v hv _ hvD hvx i
      obtain ⟨w, -, rfl⟩ := mem_image.mp hv
      exact hrest w (fun e => hvD (by rw [e]; exact mem_singleton_self _))
        (fun j e => hvx j (by rw [e])) i
    · intro y hy
      rw [mem_singleton.mp hy]
      exact ⟨0, h, hh, hd⟩
  · refine isRupert_of_edgeView_depthSeparated (univ.image x) ∅ _ u hu hk (fun i => x (r i)) 0
      (x d) h (mem_image_of_mem x (mem_univ _)) hd hh (fun i => mem_image_of_mem x (mem_univ _))
      (fun _ => Finset.notMem_empty _) hcyc ?_ (depthSepAt_of hpp hds) hnd
      (fun i => mem_image_of_mem _ (mem_univ _)) (fun m hm => absurd hm (Finset.notMem_empty _))
    intro v hv _ hvw hvp i
    obtain ⟨v', -, rfl⟩ := mem_image.mp hv
    exact hrest v' (fun e => hvw (by rw [e])) (fun j e => hvp j (by rw [e])) i

/-! ### E23 and its three cases -/

/-- The rim `(3, 6, 1, 0, 5)` of `E23 = 236/235-2`. -/
def rimE23 : ZMod 5 → Fin 7 := ![3, 6, 1, 0, 5]

/-- **E23's case split (§20.22).**  For depths `z` of the rim `(3, 6, 1, 0, 5)` (indices
`0, …, 4`) with (*) `z6 > z1, z0, z5` and `z3 > z0, z5`, distinct: if `z1 > z3` the rim is
unimodal (single peak `6`); if `z3 > z6`, `(6; 1 0 5 | 3)` is depth-separated (`e = 53`); if
`z6 > z3 > z1`, `(3; 6 | 5 0 1)` is (`e = 61`). -/
theorem e23_cases {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h61 : z 2 < z 1)
    (h60 : z 3 < z 1) (h65 : z 4 < z 1) (h30 : z 3 < z 0) (h35 : z 4 < z 0) :
    IsCyclicUnimodal z ∨ DepthSepZ z 4 1 ∨ DepthSepZ z 1 0 := by
  have v41 : ((4 : ZMod 5) - 1).val = 3 := rfl
  have v10 : ((1 : ZMod 5) - 0).val = 1 := rfl
  rcases lt_trichotomy (z 1) (z 0) with h | h | h
  · -- `z3 > z6`
    right; left
    right
    refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
    · rw [v41] at hs2
      interval_cases s
      · exact h61
      · exact h60
      · exact h65
    · rw [v41] at hs1
      interval_cases s
      exact h
  · exact absurd (hinj h) (by decide)
  · rcases lt_trichotomy (z 0) (z 2) with h' | h' | h'
    · -- `z1 > z3`: unimodal, the only peak is `6`
      left
      refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
      have hmax : ∀ i : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i → i = 1 := by
        intro i hi
        rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
        · exact absurd hi.2 (by simp only [zero_add]; exact not_lt.mpr h.le)
        · rfl
        · exact absurd hi.1 (by
            show ¬ z 1 < z 2; exact not_lt.mpr h61.le)
        · exact absurd hi.1 (by
            show ¬ z 2 < z 3; exact not_lt.mpr (by linarith))
        · exact absurd hi.2 (by
            show ¬ z 0 < z 4; exact not_lt.mpr h35.le)
      rw [hmax i hi, hmax j hj]
    · exact absurd (hinj h') (by decide)
    · -- `z6 > z3 > z1`
      right; right
      left
      refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [v10] at hs2
        interval_cases s
        exact h
      · rw [v10] at hs1
        interval_cases s
        · exact h'
        · exact h30
        · exact h35

/-! ### Theorem 20.13 -/

/-- (*) of §20.22, weak, on depths `z` at E23's view: `z6 ≥ z1, z0, z5` and `z3 ≥ z0, z5`. -/
def Star236 (z : Fin 7 → ℝ) : Prop :=
  z 1 ≤ z 6 ∧ z 0 ≤ z 6 ∧ z 5 ≤ z 6 ∧ z 0 ≤ z 3 ∧ z 5 ≤ z 3

/-- **(K̄236), X-only** (§20.22): the ten LPs of Theorem 20.13 on the closed obtuse octant, as
one implication.  For every `G` with `g > 0`, `h ≤ 0` and the three view cuts positive, if
`T′(6,2)` (rim `(0, 6, 2, 5)`) fails strictly at `d0` by either pattern and `S_6` (rim
`(0, 6, 2, 5)`) fails strictly at `d6` by either pattern, then (*) holds weakly at `d23`.  (Each
of the ten systems "patterns, the reversed inequality of (*)" is infeasible iff this holds.) -/
def K236bar (Xa Xb Xc : Fin 7 → ℝ) (d0 d6 d23 : Fin 3 → ℝ) : Prop :=
  ∀ G : Gram3, 0 < G.ga → 0 < G.gb → 0 < G.gc → G.hab ≤ 0 → G.hac ≤ 0 → G.hbc ≤ 0 →
    0 < G.cut d0 → 0 < G.cut d6 → 0 < G.cut d23 →
    SFails (G.depth Xa Xb Xc d0) 0 2 6 5 → SFails (G.depth Xa Xb Xc d6) 0 2 6 5 →
    Star236 (G.depth Xa Xb Xc d23)

/-- **(K236), X-only** (§20.22): the ten LPs on the open obtuse octant (`h < 0`), with `T′(6,2)`
failing by its pattern `{6, 5} ≥ {0, 2}` only. -/
def K236 (Xa Xb Xc : Fin 7 → ℝ) (d0 d6 d23 : Fin 3 → ℝ) : Prop :=
  ∀ G : Gram3, 0 < G.ga → 0 < G.gb → 0 < G.gc → G.hab < 0 → G.hac < 0 → G.hbc < 0 →
    0 < G.cut d0 → 0 < G.cut d6 → 0 < G.cut d23 →
    (G.depth Xa Xb Xc d0 0 < G.depth Xa Xb Xc d0 6 ∧ G.depth Xa Xb Xc d0 0 < G.depth Xa Xb Xc d0 5 ∧
      G.depth Xa Xb Xc d0 2 < G.depth Xa Xb Xc d0 6 ∧ G.depth Xa Xb Xc d0 2 < G.depth Xa Xb Xc d0 5) →
    SFails (G.depth Xa Xb Xc d6) 0 2 6 5 → Star236 (G.depth Xa Xb Xc d23)

namespace Type24

/-- The view `d0 = (1, 0, ω3)` of `T′(6,2) = 016/236`. -/
noncomputable def d0 (x : Fin 7 → ℝ³) : Fin 3 → ℝ := ![1, 0, omega3 x]
/-- The view `(1 + ω4) d(s6) = (1 + ω4, 1 + ω3, ω4 ω3 − 1)` of `S_6 = 046/236` (`view6`). -/
noncomputable def d6 (x : Fin 7 → ℝ³) : Fin 3 → ℝ :=
  ![1 + omega4 x, 1 + omega3 x, omega4 x * omega3 x - 1]
/-- The view `a3 d(s23) = X3 − X2` of `E23 = 236/235-2` (the edge `23`). -/
noncomputable def d23 (x : Fin 7 → ℝ³) : Fin 3 → ℝ := ![oblX0 x 3, oblX2 x 3 - 1, oblX6 x 3]

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

omit T in
theorem viewOf_d0 : viewOf x (d0 x) = viewT62 x := by
  rw [viewT62_eq]; simp [viewOf, d0]

omit T in
theorem viewOf_d6 : viewOf x (d6 x) = view6 x := by
  rw [view6_eq]; simp [viewOf, d6]

theorem viewOf_d23 : viewOf x (d23 x) = x 3 - x 2 := by
  rw [T.diff_frame 3 2]
  simp [viewOf, d23, Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two]

/-- **Theorem 20.13 with (K̄236), the core**: on the closed obtuse octant, if `T′(6,2)` and `S_6`
both fail (their depths distinct across the diagonals), (*) holds weakly at E23's view. -/
theorem star_of_K236bar
    (hK : K236bar (oblX0 x) (oblX2 x) (oblX6 x) (d0 x) (d6 x) (d23 x))
    (hT' : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5))
    (hS6 : QuadTest' (univ.image x) (view6 x) (x 0) (x 6) (x 2) (x 5))
    (hFT : Fails4 (x 0) (x 2) (x 6) (x 5) (viewT62 x))
    (hFS : Fails4 (x 0) (x 2) (x 6) (x 5) (view6 x))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    Star236 ((gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d23 x)) := by
  obtain ⟨hu0, a1, a2, a3, a4⟩ := hT'.cross_ne
  obtain ⟨hu6, b1, b2, b3, b4⟩ := hS6.cross_ne
  have e0 := T.inner_gram (d0 x)
  have e6 := T.inner_gram (d6 x)
  rw [viewOf_d0] at e0
  rw [viewOf_d6] at e6
  have h23 : x 3 - x 2 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
  refine hK (gram x) T.ga_pos T.gb_pos T.gc_pos hab hac hbc ?_ ?_ ?_
    (sFails_of_fails4 e0 hFT a1 a2 a3 a4)
    (sFails_of_fails4 e6 hFS b1 b2 b3 b4)
  · rw [cut_gram, viewOf_d0]; exact real_inner_self_pos.mpr hu0
  · rw [cut_gram, viewOf_d6]; exact real_inner_self_pos.mpr hu6
  · rw [cut_gram, T.viewOf_d23]; exact real_inner_self_pos.mpr h23

/-- **E23 is DS-good under (*)** (with the parallel pairs (b) and distinct rim depths). -/
theorem e23_good (hE : EdgeRim x (x 3 - x 2) 2 1 5 rimE23)
    (hb1 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 4 1)
    (hb2 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 1 0)
    (hst : Star236 ((gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d23 x))) :
    DSGood (fun i => x (rimE23 i)) (x 3 - x 2) (fun i => ⟪x (rimE23 i), x 3 - x 2⟫) := by
  have e := T.inner_gram (d23 x)
  rw [T.viewOf_d23] at e
  obtain ⟨s1, s2, s3, s4, s5⟩ := hst
  have hinj := hE.2.2.2.2.2.1
  have r0 : rimE23 0 = 3 := rfl
  have r1 : rimE23 1 = 6 := rfl
  have r2 : rimE23 2 = 1 := rfl
  have r3 : rimE23 3 = 0 := rfl
  have r4 : rimE23 4 = 5 := rfl
  have ne : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimE23 i), x 3 - x 2⟫ ≠ ⟪x (rimE23 j), x 3 - x 2⟫ := fun i j hij h => hij (hinj h)
  have lt : ∀ i j : ZMod 5, i ≠ j →
      (gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d23 x) (rimE23 i) ≤
        (gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d23 x) (rimE23 j) →
      ⟪x (rimE23 i), x 3 - x 2⟫ < ⟪x (rimE23 j), x 3 - x 2⟫ := by
    intro i j hij hle
    have hn := ne i j hij
    rw [e (rimE23 i), e (rimE23 j)] at hn ⊢
    exact lt_of_le_of_ne (by linarith) hn
  rcases e23_cases hinj (lt 2 1 (by decide) (by rw [r2, r1]; exact s1))
      (lt 3 1 (by decide) (by rw [r3, r1]; exact s2)) (lt 4 1 (by decide) (by rw [r4, r1]; exact s3))
      (lt 3 0 (by decide) (by rw [r3, r0]; exact s4)) (lt 4 0 (by decide) (by rw [r4, r0]; exact s5))
    with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨4, 1, hb1, h⟩
  · exact Or.inr ⟨1, 0, hb2, h⟩

end Type24

/-- **Theorem 20.13 with (K̄236), Rupert form (the closed obtuse octant).**  Let `T′(6,2) = 016/236`
and `S_6 = 046/236` have the rim `(0, 6, 2, 5)` (certified up to their depth patterns,
`QuadTest'`), `E23 = 236/235-2` the rim `(3, 6, 1, 0, 5)` at the view `x 3 − x 2` (`EdgeRim`:
distinct depths, no horizontal double normal), (b) `(6; 1 0 5 | 3)` and `(3; 6 | 5 0 1)` parallel
pairs of E23's rim (`ParPairAt`), and (K̄236).  Then at every metric with `c_ab, c_ac, c_bc ≤ 0`
the point set is Rupert: `T′(6,2)` or `S_6` does not fail, or E23 is unimodal or depth-separated.
The exclusions are the ties and horizontal double normals carried by the three tests' data. -/
theorem isRupert_circle236_octant {x : Fin 7 → ℝ³} (T : Type24 x)
    (hT' : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5))
    (hS6 : QuadTest' (univ.image x) (view6 x) (x 0) (x 6) (x 2) (x 5))
    (hE : EdgeRim x (x 3 - x 2) 2 1 5 rimE23)
    (hb1 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 4 1)
    (hb2 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 1 0)
    (hK : K236bar (oblX0 x) (oblX2 x) (oblX6 x) (Type24.d0 x) (Type24.d6 x) (Type24.d23 x))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    IsRupert (univ.image x) := by
  by_cases hFT : Fails4 (x 0) (x 2) (x 6) (x 5) (viewT62 x)
  · by_cases hFS : Fails4 (x 0) (x 2) (x 6) (x 5) (view6 x)
    · exact isRupert_edgeRim (sub_ne_zero.mpr (T.inj.ne (by decide))) hE
        (T.e23_good hE hb1 hb2 (T.star_of_K236bar hK hT' hS6 hFT hFS hab hac hbc))
    · exact hS6.isRupert hFS
  · exact hT'.isRupert hFT

/-! ### Theorem 20.13 with (K236) on the open octant -/

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- A determinant test at `T′(6,2)`'s view in oblique coordinates (`d0 = (1, 0, ω3)`). -/
theorem det3_viewT62 (v w v' : Fin 7) :
    det3 (x v - x w) (x v' - x w) (viewT62 x) =
      ((oblX0 x v - oblX0 x w) * ((oblX2 x v' - oblX2 x w) * omega3 x - (oblX6 x v' - oblX6 x w) * 0) -
        (oblX2 x v - oblX2 x w) * ((oblX0 x v' - oblX0 x w) * omega3 x - (oblX6 x v' - oblX6 x w) * 1) +
        (oblX6 x v - oblX6 x w) * ((oblX0 x v' - oblX0 x w) * 0 - (oblX2 x v' - oblX2 x w) * 1)) *
      vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  rw [T.diff_frame v w, T.diff_frame v' w, viewT62_eq, det3_comb]

/-- **`c5 < ω3 a5` from `T′(6,2)`'s rim** (the geometric fact behind Lemma 20.12 (S1)): if the rim
of `T′(6,2) = 016/236` at `d0` is the strictly convex quadrilateral `(0, 6, 2, 5)` (either
orientation), then `5` lies strictly below the line through `1` and `2` in the screen of `d0`.
(With `D = [e_a, e_b, e_c]`, the tests give `−(1 + ω3) D`, `(b5 + c5 − 1 − ω3 a5) D` and
`(c5 − ω3 (a5 + b5 − 1)) D` of one sign.) -/
theorem c5_lt_of_rimT62 (h3 : 0 ≤ omega3 x)
    (hT' : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5)) :
    oblX6 x 5 < omega3 x * oblX0 x 5 := by
  have o0 := T.oblX0_zero'; have o2 := T.oblX2_two; have o6 := T.oblX6_six
  have z1 := Type24.oblX0_two (x := x); have z2 := Type24.oblX0_six (x := x)
  have z3 := Type24.oblX2_zero (x := x); have z4 := Type24.oblX2_six (x := x)
  have z5 := Type24.oblX6_zero (x := x); have z6 := Type24.oblX6_two (x := x)
  set D := vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  set a5 := oblX0 x 5; set b5 := oblX2 x 5; set c5 := oblX6 x 5; set w := omega3 x
  -- the two conditions, from `D` of either sign
  suffices key : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * ((-1 - w) * D) ∧
      0 < ε * ((b5 + c5 - 1 - a5 * w) * D) ∧ 0 < ε * ((c5 - w * (a5 + b5 - 1)) * D) by
    obtain ⟨ε, hε, k1, k2, k3⟩ := key
    have hεD : ε * D < 0 := by
      by_contra hc; push Not at hc
      have : ε * ((-1 - w) * D) = (-1 - w) * (ε * D) := by ring
      rw [this] at k1
      nlinarith
    have e2 : b5 + c5 - 1 - a5 * w < 0 := by
      by_contra hc; push Not at hc
      have : ε * ((b5 + c5 - 1 - a5 * w) * D) = (b5 + c5 - 1 - a5 * w) * (ε * D) := by ring
      rw [this] at k2
      nlinarith
    have e3 : c5 - w * (a5 + b5 - 1) < 0 := by
      by_contra hc; push Not at hc
      have : ε * ((c5 - w * (a5 + b5 - 1)) * D) = (c5 - w * (a5 + b5 - 1)) * (ε * D) := by ring
      rw [this] at k3
      nlinarith
    rcases le_or_gt b5 1 with hb | hb
    · nlinarith [mul_nonneg h3 (by linarith : (0:ℝ) ≤ 1 - b5)]
    · linarith
  rcases hT' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, q₁, q₂, q₃, -, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, q₁, q₂, q₃, -, -⟩
  · -- the rim `(0, 6, 2, 5)`
    refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · rw [T.det3_viewT62] at q₁; rw [o0, o6, z3, z5, z1, o2, z2, z4, z6] at q₁
      linarith [show ((0 - 1) * ((1 - 0) * w - (0 - 0) * 0) - (0 - 0) * ((0 - 1) * w - (0 - 0) * 1) +
        (1 - 0) * ((0 - 1) * 0 - (1 - 0) * 1)) * D = (-1 - w) * D by ring]
    · rw [T.det3_viewT62] at q₂; rw [z1, z2, o2, z4, z6, o6] at q₂
      linarith [show ((0 - 0) * ((b5 - 0) * w - (c5 - 1) * 0) - (1 - 0) * ((a5 - 0) * w - (c5 - 1) * 1) +
        (0 - 1) * ((a5 - 0) * 0 - (b5 - 0) * 1)) * D = (b5 + c5 - 1 - a5 * w) * D by ring]
    · rw [T.det3_viewT62] at q₃; rw [z1, o2, z6, o0, z3, z5] at q₃
      linarith [show ((a5 - 0) * ((0 - 1) * w - (0 - 0) * 0) - (b5 - 1) * ((1 - 0) * w - (0 - 0) * 1) +
        (c5 - 0) * ((1 - 0) * 0 - (0 - 1) * 1)) * D = (c5 - w * (a5 + b5 - 1)) * D by ring]
  · -- the rim `(0, 5, 2, 6)`
    refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · rw [T.det3_viewT62] at q₃; rw [z2, o6, z4, z1, o0, z3, o2, z5, z6] at q₃
      linarith [show ((0 - 0) * ((0 - 1) * w - (0 - 0) * 0) - (0 - 1) * ((1 - 0) * w - (0 - 0) * 1) +
        (1 - 0) * ((1 - 0) * 0 - (0 - 1) * 1)) * D = -((-1 - w) * D) by ring]
    · rw [T.det3_viewT62] at q₂; rw [z1, o2, z6, z2, z4, o6] at q₂
      linarith [show ((0 - a5) * ((0 - b5) * w - (1 - c5) * 0) - (1 - b5) * ((0 - a5) * w - (1 - c5) * 1) +
        (0 - c5) * ((0 - a5) * 0 - (0 - b5) * 1)) * D = -((b5 + c5 - 1 - a5 * w) * D) by ring]
    · rw [T.det3_viewT62] at q₁; rw [o0, z3, z5, z1, o2, z6] at q₁
      linarith [show ((a5 - 1) * ((1 - 0) * w - (0 - 0) * 0) - (b5 - 0) * ((0 - 1) * w - (0 - 0) * 1) +
        (c5 - 0) * ((0 - 1) * 0 - (1 - 0) * 1)) * D = -((c5 - w * (a5 + b5 - 1)) * D) by ring]

/-- **Lemma 20.12 (S1) at `K`'s metric**: with `ω3 ≥ 0`, `T′(6,2)`'s rim, `h_ab + ω3 h_bc ≤ 0`
(`z2 ≤ z1` at `d0`) and distinct depths, `T′(6,2)` fails only by `{6, 5} ≥ {0, 2}`. -/
theorem s1_pattern (h3 : 0 ≤ omega3 x)
    (hT' : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5))
    (hq : ⟪x 0 - x 1, x 2 - x 1⟫ + omega3 x * ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hF : SFails ((gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d0 x)) 0 2 6 5) :
    let z := (gram x).depth (oblX0 x) (oblX2 x) (oblX6 x) (d0 x)
    z 0 < z 6 ∧ z 0 < z 5 ∧ z 2 < z 6 ∧ z 2 < z 5 := by
  intro z
  rcases hF with h | ⟨-, -, h62, h52⟩
  · exact h
  exfalso
  have hu0 := hT'.cross_ne.1
  have hcut : 0 < (gram x).cut (d0 x) := by
    rw [cut_gram, viewOf_d0]; exact real_inner_self_pos.mpr hu0
  have o0 := T.oblX0_zero'; have o2 := T.oblX2_two; have o6 := T.oblX6_six
  have z1 := Type24.oblX0_two (x := x); have z2 := Type24.oblX0_six (x := x)
  have z3 := Type24.oblX2_zero (x := x); have z4 := Type24.oblX2_six (x := x)
  have z5 := Type24.oblX6_zero (x := x); have z6 := Type24.oblX6_two (x := x)
  simp only [Gram3.depth, covDepth, Gram3.ua, Gram3.ub, Gram3.uc, d0, o2, o6, z1, z2, z4,
    z6] at h62 h52
  simp only [Gram3.cut, Gram3.ua, Gram3.ub, Gram3.uc, d0] at hcut
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h62 h52 hcut
  refine Cu13.S1 (omega3 x) (oblX0 x 5) (oblX2 x 5) (oblX6 x 5)
    ((gram x).ga * 1 + (gram x).hab * 0 + (gram x).hac * omega3 x)
    ((gram x).hab * 1 + (gram x).gb * 0 + (gram x).hbc * omega3 x)
    ((gram x).hac * 1 + (gram x).hbc * 0 + (gram x).gc * omega3 x)
    (T.X0_pos (by decide)) (T.c5_lt_of_rimT62 h3 hT').le ?_ ?_ ?_ ?_ ?_
  · have := T.le236 5; linarith
  · linarith
  · simp only [gram]; linarith
  · linarith
  · linarith

end Type24

/-- **Theorem 20.13 with (K236), Rupert form (the open obtuse octant).**  As
`isRupert_circle236_octant`, with (K236) in place of (K̄236) (`T′(6,2)`'s second pattern is
excluded by Lemma 20.12 (S1), `ω3 ≥ 0`), at every metric with `c_ab, c_ac, c_bc < 0`. -/
theorem isRupert_circle236_open {x : Fin 7 → ℝ³} (T : Type24 x) (h3 : 0 ≤ omega3 x)
    (hT' : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5))
    (hS6 : QuadTest' (univ.image x) (view6 x) (x 0) (x 6) (x 2) (x 5))
    (hE : EdgeRim x (x 3 - x 2) 2 1 5 rimE23)
    (hb1 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 4 1)
    (hb2 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 1 0)
    (hK : K236 (oblX0 x) (oblX2 x) (oblX6 x) (Type24.d0 x) (Type24.d6 x) (Type24.d23 x))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ < 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ < 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ < 0) :
    IsRupert (univ.image x) := by
  by_cases hFT : Fails4 (x 0) (x 2) (x 6) (x 5) (viewT62 x)
  · by_cases hFS : Fails4 (x 0) (x 2) (x 6) (x 5) (view6 x)
    · refine isRupert_edgeRim (sub_ne_zero.mpr (T.inj.ne (by decide))) hE (T.e23_good hE hb1 hb2 ?_)
      obtain ⟨hu0, a1, a2, a3, a4⟩ := hT'.cross_ne
      obtain ⟨hu6, b1, b2, b3, b4⟩ := hS6.cross_ne
      have e0 := T.inner_gram (Type24.d0 x)
      have e6 := T.inner_gram (Type24.d6 x)
      rw [Type24.viewOf_d0] at e0
      rw [Type24.viewOf_d6] at e6
      have h23 : x 3 - x 2 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
      have hq : ⟪x 0 - x 1, x 2 - x 1⟫ + omega3 x * ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h3 hbc.le]
      refine hK (Type24.gram x) T.ga_pos T.gb_pos T.gc_pos hab hac hbc ?_ ?_ ?_
        (T.s1_pattern h3 hT' hq (sFails_of_fails4 e0 hFT a1 a2 a3 a4))
        (sFails_of_fails4 e6 hFS b1 b2 b3 b4)
      · rw [Type24.cut_gram, Type24.viewOf_d0]; exact real_inner_self_pos.mpr hu0
      · rw [Type24.cut_gram, Type24.viewOf_d6]; exact real_inner_self_pos.mpr hu6
      · rw [Type24.cut_gram, T.viewOf_d23]; exact real_inner_self_pos.mpr h23
    · exact hS6.isRupert hFS
  · exact hT'.isRupert hFT

/-! ### Corollary 20.14 and the uniform statements -/

/-- **The data of Theorem 20.13 with (K̄236)** (X-only except for the certificates of the three
tests). -/
structure Circle236 (x : Fin 7 → ℝ³) : Prop where
  testT : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 2) (x 5)
  testS : QuadTest' (univ.image x) (view6 x) (x 0) (x 6) (x 2) (x 5)
  testE : EdgeRim x (x 3 - x 2) 2 1 5 rimE23
  pair1 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 4 1
  pair2 : ParPairAt (fun i => x (rimE23 i)) (x 3 - x 2) 1 0
  lp : K236bar (oblX0 x) (oblX2 x) (oblX6 x) (Type24.d0 x) (Type24.d6 x) (Type24.d23 x)

/-- **The hypotheses of Corollary 20.14**: the window chain on arc 2 or arc 6 (Corollary 20.5,
with `c4 ≤ 1` or (H⁺)), or with (Λ) (Corollary 20.11), or Theorem 20.13 with (K̄236). -/
def Type24.ObtuseCovered (x : Fin 7 → ℝ³) : Prop :=
  Nonempty (WindowChain x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
    Nonempty (WindowChain x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)) ∨
    Nonempty (WindowChainΛ x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
    Nonempty (WindowChainΛ x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)) ∨
    Circle236 x

/-- **Corollary 20.14 (B_DS on the closed obtuse octant), Rupert form.**  Under the hypotheses of
20.5 or 20.11 on an arc, or of 20.13 with (K̄236), `K` is Rupert at every metric with
`c_ab, c_ac, c_bc ≤ 0`. -/
theorem isRupert_type24_obtuse_octant {x : Fin 7 → ℝ³} (T : Type24 x)
    (hO : Type24.ObtuseCovered x) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    IsRupert (univ.image x) := by
  rcases hO with h | h | h | h | C
  · exact isRupert_windowChain_octant T (Or.inl h) hab hac hbc
  · exact isRupert_windowChain_octant T (Or.inr h) hab hac hbc
  · exact isRupert_windowChainΛ_octant T (Or.inl h) hab hac hbc
  · exact isRupert_windowChainΛ_octant T (Or.inr h) hab hac hbc
  · exact isRupert_circle236_octant T C.testT C.testS C.testE C.pair1 C.pair2 C.lp hab hac hbc

/-- **Theorem 20.9″ (uniform, every metric).**  Side-safety (20.8′: each cosine seen on a safe
side) and the hypotheses of Corollary 20.14 make `K` Rupert at every metric: some `c_ij > 0` by
20.8′, otherwise the closed obtuse octant by 20.14.  (G1, G2, N1, N2 satisfy 20.8′ and 20.13 with
(K̄236).)  The exclusions are carried by the data. -/
theorem isRupert_type24_uniform_circle {x : Fin 7 → ℝ³} (T : Type24 x)
    (hside : Type24.SideCovered x) (hO : Type24.ObtuseCovered x) : IsRupert (univ.image x) := by
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · exact isRupert_type24_side_safe T hside h
  · simp only [not_or, not_lt] at h
    exact isRupert_type24_obtuse_octant T hO h.1 h.2.1 h.2.2

/-- **Theorem 20.9‴ (20.9″ with DS side-safety), in the region form.**  If the seven regions
`R_S` are covered by DS-safe cap edges (Theorem 20.17; e.g. 20.16, `DSSideCovered.regions`) and
the hypotheses of Corollary 20.14 hold, `K` is Rupert at every metric. -/
theorem isRupert_type24_uniform_dsRegions {x : Fin 7 → ℝ³} (T : Type24 x)
    (hcov : Type24.DSRegionsCovered x) (hO : Type24.ObtuseCovered x) : IsRupert (univ.image x) := by
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · exact isRupert_type24_dsRegions T hcov h
  · simp only [not_or, not_lt] at h
    exact isRupert_type24_obtuse_octant T hO h.1 h.2.1 h.2.2

/-- **Theorem 20.9‴ (20.9″ with DS side-safety).**  Let `X` satisfy 20.16 (each cosine seen on a
DS-safe side) and either the window chain (20.5 or 20.11) or Theorem 20.13 with (K̄236).  Then `K`
is Rupert at every metric.  (All 611 known pocket classes satisfy these hypotheses, §20.31.) -/
theorem isRupert_type24_uniform_ds {x : Fin 7 → ℝ³} (T : Type24 x)
    (hside : Type24.DSSideCovered x) (hO : Type24.ObtuseCovered x) : IsRupert (univ.image x) :=
  isRupert_type24_uniform_dsRegions T hside.regions hO

/-- **The uniform statement with the acute side from 20.17, 20.18, 20.19**: `AcuteCovered` (a
planar-quad test, or the regions `R_S` by DS-safe cap edges and Lemma 20.18 on `R_bc`) and the
hypotheses of Corollary 20.14 make `K` Rupert at every metric. -/
theorem isRupert_type24_uniform_acute {x : Fin 7 → ℝ³} (T : Type24 x)
    (hA : Type24.AcuteCovered x) (hO : Type24.ObtuseCovered x) : IsRupert (univ.image x) := by
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · exact isRupert_type24_acute T hA h
  · simp only [not_or, not_lt] at h
    exact isRupert_type24_obtuse_octant T hO h.1 h.2.1 h.2.2

end Minimality

end
