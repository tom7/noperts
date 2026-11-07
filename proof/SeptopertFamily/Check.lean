module

public import SeptopertFamily.Basic
public import SeptopertFamily.Geometry
public import Std.Data.HashMap

/-!
# The certificate check for the Septopert family of height below 7

A table maps integer parameter tuples `y` (as lists) to certificates
(`Cert`), checked in integer arithmetic by `certOk`:

* `coplanar n`: all 7 points satisfy `n · v = n · v₀`, `n ≠ 0`;
* `hull i D w`: point `i` is `∑ₖ wₖ vₖ / D` with `wₖ ≥ 0`, `wᵢ = 0`, `∑ wₖ = D > 0`;
* `passage qo qi t₀ t₁ T tri`: the outer rotation `R(qo)`, the inner rotation
  `R(qi)` and the offset `(t₀, t₁) / T` form a Rupert passage: inner shadow point
  `k` lies strictly inside the outer shadow triangle `tri k` (all three areas
  positive). The numbers are scaled by `T |qi|² |qo|²` to stay integral.

`checkAll` runs over every tuple in `[0, 12]⁵` with a zero entry, divides it by
a common divisor `g ∈ [1, 12]` and looks up either the result `z` or its
reflection `max z − z`; `checkAll_sound` turns a passing check into the
theorem for all integer tuples with `max − min ≤ 12`, by translation,
scaling and reflection (`not_isNopert_affine`).
-/

@[expose] public section

namespace SeptopertFamily

open scoped RealInnerProductSpace

/-! ### Integer data -/

/-- The integer coordinates of the 7 points (`familyVerts_eq`). -/
def vtx (y : Fin 5 → ℤ) : Fin 7 → Fin 3 → ℤ :=
  ![![y 0, y 1, y 1], ![y 1, y 0, y 1], ![y 1, y 1, y 0],
    ![y 2, y 3, y 3], ![y 3, y 2, y 3], ![y 3, y 3, y 2], ![y 4, y 4, y 4]]

/-- `vtx` for the compiler: vector literals `![…]` evaluate slowly (`Fin.cases`). -/
def vtxImpl (y : Fin 5 → ℤ) (k : Fin 7) (c : Fin 3) : ℤ :=
  if k.val < 3 then (if c.val = k.val then y 0 else y 1)
  else if k.val < 6 then (if c.val + 3 = k.val then y 2 else y 3)
  else y 4

@[csimp] theorem vtx_eq_vtxImpl : @vtx = @vtxImpl := by
  funext y k c
  fin_cases k <;> fin_cases c <;> rfl

/-- The tuple `(a, b, c, d, e)`. -/
def mk5 (a b c d e : ℤ) : Fin 5 → ℤ := ![a, b, c, d, e]

def mk5Impl (a b c d e : ℤ) (i : Fin 5) : ℤ :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else
    if i.val = 3 then d else e

@[csimp] theorem mk5_eq_mk5Impl : @mk5 = @mk5Impl := by
  funext a b c d e i
  fin_cases i <;> rfl

theorem mk5_self (y : Fin 5 → ℤ) : mk5 (y 0) (y 1) (y 2) (y 3) (y 4) = y := by
  funext i
  fin_cases i <;> rfl

noncomputable def toR3 (v : Fin 3 → ℤ) : ℝ³ := WithLp.toLp 2 fun j => (v j : ℝ)

noncomputable def toR2 (v : Fin 2 → ℤ) : ℝ² := WithLp.toLp 2 fun j => (v j : ℝ)

@[simp] theorem toR3_apply (v : Fin 3 → ℤ) (j : Fin 3) : toR3 v j = v j := rfl

@[simp] theorem toR2_apply (v : Fin 2 → ℤ) (j : Fin 2) : toR2 v j = v j := rfl

theorem familyVerts_eq (y : Fin 5 → ℤ) :
    familyVerts y = Finset.univ.image fun k => toR3 (vtx y k) := by
  have e : ∀ a b c : ℤ, (!₂[(a : ℝ), b, c] : ℝ³) = toR3 ![a, b, c] := by
    intro a b c; ext j; fin_cases j <;> simp
  ext v
  simp only [familyVerts, e, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp only [vtx, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ]
  constructor
  · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp
  · rintro (h | h | h | h | h | h | h | h) <;> first | (subst h; simp) | exact h.elim

/-- The tuple `m + g z` gives the image of the points of `z` under `v ↦ m (1,1,1) + g v`. -/
theorem familyVerts_affine (z : Fin 5 → ℤ) (m g : ℤ) :
    familyVerts (fun i => m + g * z i) =
      (familyVerts z).image fun v => (!₂[(m : ℝ), m, m] : ℝ³) + (g : ℝ) • v := by
  rw [familyVerts_eq, familyVerts_eq, Finset.image_image]
  congr 1
  funext k
  ext j
  fin_cases k <;> fin_cases j <;> simp [vtx]

/-- Not being a nopert passes from `z` to `m + g z`, `g ≠ 0`. -/
theorem not_isNopert_affine {z : Fin 5 → ℤ} (h : ¬ IsNopert (familyVerts z)) (m g : ℤ)
    (hg : g ≠ 0) : ¬ IsNopert (familyVerts fun i => m + g * z i) := by
  intro hN
  rw [familyVerts_affine] at hN
  exact h (isNopert_of_isNopert_image _ _ _ (by exact_mod_cast hg) hN)

/-! ### Certificates -/

/-- A certificate that a tuple is not a nopert (see the module doc). -/
inductive Cert where
  | coplanar (n0 n1 n2 : ℤ)
  | hull (i : ℕ) (D : ℤ) (w : Array ℤ)
  | passage (qo qi : Array ℤ) (t0 t1 T : ℤ) (tri : Array ℕ)
  deriving Inhabited, Repr

def dot3 (n v : Fin 3 → ℤ) : ℤ := n 0 * v 0 + n 1 * v 1 + n 2 * v 2

def coplanarOk (y : Fin 5 → ℤ) (n : Fin 3 → ℤ) : Bool :=
  (n 0 != 0 || n 1 != 0 || n 2 != 0) &&
    (List.finRange 7).all fun k => dot3 n (vtx y k) == dot3 n (vtx y 0)

def sum7 (f : Fin 7 → ℤ) : ℤ := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

def hullOk (y : Fin 5 → ℤ) (i : Fin 7) (D : ℤ) (w : Fin 7 → ℤ) : Bool :=
  0 < D && w i == 0 && (List.finRange 7).all (fun k => 0 ≤ w k) && sum7 w == D &&
    (List.finRange 3).all fun c => sum7 (fun k => w k * vtx y k c) == D * vtx y i c

/-- Row `r` of the matrix `M` applied to `v`. -/
def rowDot (M : Matrix (Fin 3) (Fin 3) ℤ) (r : Fin 3) (v : Fin 3 → ℤ) : ℤ :=
  M r 0 * v 0 + M r 1 * v 1 + M r 2 * v 2

def crossZ (u v : Fin 2 → ℤ) : ℤ := u 0 * v 1 - u 1 * v 0

/-- `p` strictly inside the triangle `A B C` (counterclockwise). -/
def inTriZ (A B C p : Fin 2 → ℤ) : Bool :=
  0 < crossZ (B - p) (C - p) && 0 < crossZ (C - p) (A - p) && 0 < crossZ (A - p) (B - p)

/-- The outer shadow point of `v`, times `T |qi|² |qo|²`. -/
def outerPt (qo qi : Fin 4 → ℤ) (T : ℤ) (v : Fin 3 → ℤ) : Fin 2 → ℤ :=
  ![T * quatNorm qi * rowDot (quatMat qo) 0 v, T * quatNorm qi * rowDot (quatMat qo) 1 v]

/-- The inner shadow point of `v` (offset `(t₀, t₁) / T`), times `T |qi|² |qo|²`. -/
def innerPt (qo qi : Fin 4 → ℤ) (t0 t1 T : ℤ) (v : Fin 3 → ℤ) : Fin 2 → ℤ :=
  ![quatNorm qo * (T * rowDot (quatMat qi) 0 v + quatNorm qi * t0),
    quatNorm qo * (T * rowDot (quatMat qi) 1 v + quatNorm qi * t1)]

def outerPtImpl (qo qi : Fin 4 → ℤ) (T : ℤ) (v : Fin 3 → ℤ) (r : Fin 2) : ℤ :=
  if r.val = 0 then T * quatNorm qi * rowDot (quatMat qo) 0 v
  else T * quatNorm qi * rowDot (quatMat qo) 1 v

@[csimp] theorem outerPt_eq_outerPtImpl : @outerPt = @outerPtImpl := by
  funext qo qi T v r
  fin_cases r <;> rfl

def innerPtImpl (qo qi : Fin 4 → ℤ) (t0 t1 T : ℤ) (v : Fin 3 → ℤ) (r : Fin 2) : ℤ :=
  if r.val = 0 then quatNorm qo * (T * rowDot (quatMat qi) 0 v + quatNorm qi * t0)
  else quatNorm qo * (T * rowDot (quatMat qi) 1 v + quatNorm qi * t1)

@[csimp] theorem innerPt_eq_innerPtImpl : @innerPt = @innerPtImpl := by
  funext qo qi t0 t1 T v r
  fin_cases r <;> rfl

def passageOk (y : Fin 5 → ℤ) (qo qi : Fin 4 → ℤ) (t0 t1 T : ℤ)
    (tri : Fin 7 → Fin 7 × Fin 7 × Fin 7) : Bool :=
  0 < T && quatNorm qo != 0 && quatNorm qi != 0 &&
    (List.finRange 7).all fun k =>
      inTriZ (outerPt qo qi T (vtx y (tri k).1)) (outerPt qo qi T (vtx y (tri k).2.1))
        (outerPt qo qi T (vtx y (tri k).2.2)) (innerPt qo qi t0 t1 T (vtx y k))

/-- The triangle of inner point `k`: digits `3k, 3k+1, 3k+2` of `tri`. -/
def decodeTri (tri : Array ℕ) (k : Fin 7) : Fin 7 × Fin 7 × Fin 7 :=
  (Fin.ofNat 7 (tri.getD (3 * k.val) 0), Fin.ofNat 7 (tri.getD (3 * k.val + 1) 0),
    Fin.ofNat 7 (tri.getD (3 * k.val + 2) 0))

def certOk (y : Fin 5 → ℤ) : Cert → Bool
  | .coplanar n0 n1 n2 => coplanarOk y ![n0, n1, n2]
  | .hull i D w => if h : i < 7 then hullOk y ⟨i, h⟩ D (fun k => w.getD k 0) else false
  | .passage qo qi t0 t1 T tri =>
      passageOk y (fun k => qo.getD k 0) (fun k => qi.getD k 0) t0 t1 T (decodeTri tri)

/-- The certificate table, keyed by the tuple as a list. -/
abbrev Table := Std.HashMap (List ℤ) Cert

def lookupOk (tbl : Table) (y : Fin 5 → ℤ) : Bool :=
  -- evaluate `y` once
  let y' := mk5 (y 0) (y 1) (y 2) (y 3) (y 4)
  match tbl.get? (List.ofFn y') with
  | some c => certOk y' c
  | none => false

/-- The reflection `max y − y` (any constant would do for soundness). -/
def flipT (y : Fin 5 → ℤ) : Fin 5 → ℤ :=
  let M := max (max (max (max (y 0) (y 1)) (y 2)) (y 3)) (y 4)
  fun i => M - y i

/-- Some `g ∈ [1, 12]` divides `y`, and `y / g` or its reflection has a valid certificate. -/
def reducedOk (tbl : Table) (y : Fin 5 → ℤ) : Bool :=
  (List.range 12).any fun g' =>
    (List.finRange 5).all (fun i => y i % ((g' : ℤ) + 1) == 0) &&
      (lookupOk tbl (fun i => y i / ((g' : ℤ) + 1)) ||
        lookupOk tbl (flipT fun i => y i / ((g' : ℤ) + 1)))

/-- Tuples without a zero entry are translates of others and are skipped. -/
def tupleOk (tbl : Table) (y : Fin 5 → ℤ) : Bool :=
  (List.finRange 5).all (fun i => y i != 0) || reducedOk tbl y

/-- The full check: every tuple in `[0, 12]⁵`. -/
def checkAll (tbl : Table) : Bool :=
  (List.range 13).all fun a => (List.range 13).all fun b => (List.range 13).all fun c =>
    (List.range 13).all fun d => (List.range 13).all fun e =>
      tupleOk tbl (mk5 a b c d e)

/-! ### Soundness -/

theorem coplanar_of_coplanarOk {y : Fin 5 → ℤ} {n : Fin 3 → ℤ} (h : coplanarOk y n = true) :
    Coplanar ℝ (familyVerts y : Set ℝ³) := by
  simp only [coplanarOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  obtain ⟨hn, hall⟩ := h
  have hinner : ∀ v : Fin 3 → ℤ, ⟪toR3 n, toR3 v⟫ = (dot3 n v : ℝ) := by
    intro v
    simp [PiLp.inner_apply, Fin.sum_univ_three, dot3]
    ring
  apply Minimality.coplanar_of_plane (N := toR3 n) (c := (dot3 n (vtx y 0) : ℝ))
  · intro h0
    have h0' : ∀ j, (n j : ℝ) = 0 := fun j => by
      have := congrArg (fun u : ℝ³ => u j) h0
      simpa using this
    rcases hn with (h | h) | h
    · exact h (by exact_mod_cast h0' 0)
    · exact h (by exact_mod_cast h0' 1)
    · exact h (by exact_mod_cast h0' 2)
  · intro x hx
    rw [familyVerts_eq, Finset.coe_image] at hx
    obtain ⟨k, -, rfl⟩ := hx
    rw [hinner, hall k]

theorem sum7_eq (f : Fin 7 → ℤ) : sum7 f = ∑ k, f k := by
  simp [sum7, Fin.sum_univ_succ]
  ring

theorem not_isNopert_of_hullOk {y : Fin 5 → ℤ} {i : Fin 7} {D : ℤ} {w : Fin 7 → ℤ}
    (h : hullOk y i D w = true) : ¬ IsNopert (familyVerts y) := by
  simp only [hullOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨hD, hwi⟩, hw0⟩, hsum⟩, hcomb⟩ := h
  rw [familyVerts_eq]
  apply not_isNopert_of_mem_convexHull_erase _ i
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let W : Fin 7 → ℝ := fun k => (w k : ℝ) / D
  have hWi : W i = 0 := by simp [W, hwi]
  have hconv := convex_convexHull ℝ
    ((((Finset.univ.erase i).image fun k => toR3 (vtx y k)) : Finset ℝ³) : Set ℝ³)
  have := hconv.sum_mem (t := Finset.univ.erase i) (w := W) (z := fun k => toR3 (vtx y k))
    (fun k _ => div_nonneg (by exact_mod_cast hw0 k) hDR.le)
    (by
      rw [Finset.sum_erase _ hWi]
      simp only [W, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hDR.ne']
      rw [sum7_eq] at hsum
      exact_mod_cast hsum)
    (fun k hk => subset_convexHull ℝ _ (by
      rw [Finset.mem_coe]; exact Finset.mem_image_of_mem _ hk))
  convert this using 1
  rw [Finset.sum_erase _ (by simp [hWi])]
  ext j
  have hj := hcomb j
  rw [sum7_eq] at hj
  have hj' : ∑ k, (w k : ℝ) * (vtx y k j : ℝ) = (D : ℝ) * (vtx y i j : ℝ) := by
    exact_mod_cast hj
  simp only [toR3_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, W]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, hj']
  field_simp

theorem quatNorm_cast (q : Fin 4 → ℤ) :
    quatNorm (fun k => (q k : ℝ)) = ((quatNorm q : ℤ) : ℝ) := by
  simp [quatNorm]

theorem quatMat_cast (q : Fin 4 → ℤ) (r c : Fin 3) :
    quatMat (fun k => (q k : ℝ)) r c = ((quatMat q r c : ℤ) : ℝ) := by
  fin_cases r <;> fin_cases c <;> simp [quatMat]

theorem proj_quatRot (q : Fin 4 → ℤ) (v : Fin 3 → ℤ) (r : Fin 2) :
    proj_xy ((quatRot fun k => (q k : ℝ)).toEuclideanLin (toR3 v)) r =
      ((quatNorm q : ℤ) : ℝ)⁻¹ * (rowDot (quatMat q) (Fin.castSucc r) v : ℝ) := by
  have e : ∀ r' : Fin 3, ((quatRot fun k => (q k : ℝ)).toEuclideanLin (toR3 v)) r' =
      ((quatNorm q : ℤ) : ℝ)⁻¹ * (rowDot (quatMat q) r' v : ℝ) := by
    intro r'
    simp [Matrix.toLpLin_apply, quatRot, quatNorm_cast, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, quatMat_cast, rowDot]
  fin_cases r
  · simpa [proj_xy] using e 0
  · simpa [proj_xy] using e 1

theorem mem_interior_of_inTriZ {K : ℝ} (hK : 0 < K) {A B C p : Fin 2 → ℤ}
    (h : inTriZ A B C p = true) :
    K⁻¹ • toR2 p ∈ interior (convexHull ℝ
      ({K⁻¹ • toR2 A, K⁻¹ • toR2 B, K⁻¹ • toR2 C} : Set ℝ²)) := by
  simp only [inTriZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e : ∀ P Q : Fin 2 → ℤ, cross2 (K⁻¹ • toR2 P - K⁻¹ • toR2 p) (K⁻¹ • toR2 Q - K⁻¹ • toR2 p) =
      K⁻¹ ^ 2 * (crossZ (P - p) (Q - p) : ℝ) := by
    intro P Q
    simp [cross2, crossZ]
    ring
  have hK2 : 0 < K⁻¹ ^ 2 := by positivity
  apply mem_interior_convexHull_triangle
  · rw [e]; exact mul_pos hK2 (by exact_mod_cast h1)
  · rw [e]; exact mul_pos hK2 (by exact_mod_cast h2)
  · rw [e]; exact mul_pos hK2 (by exact_mod_cast h3)

theorem isRupert_of_passageOk {y : Fin 5 → ℤ} {qo qi : Fin 4 → ℤ} {t0 t1 T : ℤ}
    {tri : Fin 7 → Fin 7 × Fin 7 × Fin 7} (h : passageOk y qo qi t0 t1 T tri = true) :
    IsRupert (familyVerts y) := by
  simp only [passageOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨hT, hNo⟩, hNi⟩, hall⟩ := h
  set No : ℝ := ((quatNorm qo : ℤ) : ℝ)
  set Ni : ℝ := ((quatNorm qi : ℤ) : ℝ)
  have hNo' : No ≠ 0 := by simpa [No] using hNo
  have hNi' : Ni ≠ 0 := by simpa [Ni] using hNi
  have hnn : ∀ q : Fin 4 → ℤ, (0 : ℝ) ≤ ((quatNorm q : ℤ) : ℝ) := fun q => by
    have : (0 : ℤ) ≤ quatNorm q := by
      unfold quatNorm
      nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1), mul_self_nonneg (q 2),
        mul_self_nonneg (q 3)]
    exact_mod_cast this
  have hNoP : 0 < No := lt_of_le_of_ne (hnn qo) (Ne.symm hNo')
  have hNiP : 0 < Ni := lt_of_le_of_ne (hnn qi) (Ne.symm hNi')
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set K : ℝ := T * Ni * No
  have hK : 0 < K := by positivity
  let o : ℝ² := !₂[(t0 : ℝ) / T, (t1 : ℝ) / T]
  have hRo := quatRot_mem_SO3 (fun k => (qo k : ℝ)) (by rw [quatNorm_cast]; exact hNo')
  have hRi := quatRot_mem_SO3 (fun k => (qi k : ℝ)) (by rw [quatNorm_cast]; exact hNi')
  have hout : ∀ v : Fin 3 → ℤ, proj_xy ((quatRot fun k => (qo k : ℝ)).toEuclideanLin (toR3 v)) =
      K⁻¹ • toR2 (outerPt qo qi T v) := by
    intro v; ext r
    rw [proj_quatRot]
    fin_cases r <;> simp [outerPt, K, No, Ni] <;> field_simp
  have hin : ∀ v : Fin 3 → ℤ, o + proj_xy ((quatRot fun k => (qi k : ℝ)).toEuclideanLin (toR3 v)) =
      K⁻¹ • toR2 (innerPt qo qi t0 t1 T v) := by
    intro v; ext r
    rw [PiLp.add_apply, proj_quatRot]
    fin_cases r <;> simp [innerPt, o, K, No, Ni] <;> field_simp <;> ring
  rw [familyVerts_eq]
  apply isRupert_of_forall_mem_interior _ hRi hRo o
  intro v hv
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
  rw [hin]
  refine interior_mono (convexHull_mono ?_) (mem_interior_of_inTriZ hK (hall k))
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rw [Finset.coe_image]
  rcases hu with rfl | rfl | rfl <;>
    exact ⟨_, ⟨_, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩, hout _⟩

theorem not_isNopert_of_certOk {y : Fin 5 → ℤ} {c : Cert} (h : certOk y c = true) :
    ¬ IsNopert (familyVerts y) := by
  cases c with
  | coplanar n0 n1 n2 => exact fun hN => hN.1 (coplanar_of_coplanarOk h)
  | hull i D w =>
      simp only [certOk] at h
      split at h
      · exact not_isNopert_of_hullOk h
      · exact absurd h (by simp)
  | passage qo qi t0 t1 T tri => exact fun hN => hN.2 (isRupert_of_passageOk h)

theorem not_isNopert_of_lookupOk {tbl : Table} {y : Fin 5 → ℤ} (h : lookupOk tbl y = true) :
    ¬ IsNopert (familyVerts y) := by
  unfold lookupOk at h
  simp only at h
  split at h
  · rw [← mk5_self y]; exact not_isNopert_of_certOk h
  · exact absurd h (by simp)

theorem not_isNopert_of_reducedOk {tbl : Table} {y : Fin 5 → ℤ} (h : reducedOk tbl y = true) :
    ¬ IsNopert (familyVerts y) := by
  simp only [reducedOk, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, true_implies, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨g', -, hdiv, hz⟩ := h
  set g : ℤ := (g' : ℤ) + 1
  have hg : g ≠ 0 := by omega
  set z : Fin 5 → ℤ := fun i => y i / g
  have hz' : ¬ IsNopert (familyVerts z) := by
    rcases hz with hz | hz
    · exact not_isNopert_of_lookupOk hz
    · have h1 := not_isNopert_affine (not_isNopert_of_lookupOk hz)
        (max (max (max (max (z 0) (z 1)) (z 2)) (z 3)) (z 4)) (-1) (by norm_num)
      convert h1 using 3
      funext i
      simp [flipT, z]
  have h2 := not_isNopert_affine hz' 0 g hg
  convert h2 using 3
  funext i
  simp only [z, zero_add]
  exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (hdiv i))).symm

/-- **Soundness of the check.** -/
theorem checkAll_sound {tbl : Table} (h : checkAll tbl = true) (x : Fin 5 → ℤ)
    (hx : ∀ i j, x i - x j ≤ 12) : ¬ IsNopert (familyVerts x) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  have hm : ∀ i, x i₀ ≤ x i := fun i => hi₀ ▸ Finset.inf'_le x (Finset.mem_univ i)
  set y : Fin 5 → ℤ := fun i => x i - x i₀ with hy
  have hy0 : ∀ i, 0 ≤ y i := fun i => by simp only [y]; linarith [hm i]
  have hy12 : ∀ i, y i ≤ 12 := fun i => by simp only [y]; exact hx i i₀
  have hyz : y i₀ = 0 := by simp only [y]; ring
  have hok : tupleOk tbl y = true := by
    simp only [checkAll, List.all_eq_true, List.mem_range] at h
    have := h (y 0).toNat (by have := hy12 0; omega) (y 1).toNat (by have := hy12 1; omega)
      (y 2).toNat (by have := hy12 2; omega) (y 3).toNat (by have := hy12 3; omega)
      (y 4).toNat (by have := hy12 4; omega)
    convert this using 2
    funext i
    fin_cases i <;> simp [mk5, Int.toNat_of_nonneg (hy0 _)]
  have hred : reducedOk tbl y = true := by
    simp only [tupleOk, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      bne_iff_ne, ne_eq] at hok
    rcases hok with hok | hok
    · exact absurd hyz (hok i₀)
    · exact hok
  have := not_isNopert_affine (not_isNopert_of_reducedOk hred) (x i₀) 1 one_ne_zero
  convert this using 3
  funext i
  simp [y]

end SeptopertFamily

end
