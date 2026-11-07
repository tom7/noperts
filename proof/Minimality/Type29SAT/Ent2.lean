module

public import Minimality.Type29SAT.Ori

@[expose] public section

/-!
# L3, part 6: constants, the facing, and the routes of the triple table, three valued

Port of L/B21Ent3, Ent4, Ent5, Ent6 to `S3`: no `AtomsNZ`, no nonzero hypothesis.  The facing `fup3`,
the facet route `facS = mul3 (A term) (facing)`, and the key lemmas `fac_key3`, `zq_key3`, `at_key3`, `b4_key3`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical

namespace Minimality.H29.SAT

/-- Cyclic rotation of the three arguments of `det3`. -/
theorem det3_cyc (a b c : ℝ³) : det3 a b c = det3 b c a := by simp only [det3_expand]; ring
/-- Swapping the first two arguments of `det3` negates it. -/
theorem det3_swap (a b c : ℝ³) : det3 a b c = - det3 b a c := by simp only [det3_expand]; ring
/-- Swapping the last two arguments of `det3` negates it. -/
theorem det3_swap2 (a b c : ℝ³) : det3 a b c = - det3 a c b := by simp only [det3_expand]; ring

/-- Lookup of an orientation constant: the sign of `Ar g T p q r`, `0` if not tabulated. -/
def oriv (T p q r : Nat) : Int :=
  (((oriTab.flatMap perms6).find? (·.1 == (T, p, q, r))).map (·.2)).getD 0

/-- A nonzero tabulated orientation constant is the sign of `Ar`. -/
theorem oriv_sound {g : Geo} (hO : OriOK g) (T p q r : Nat) (h : oriv T p q r ≠ 0) :
    0 < (oriv T p q r : ℝ) * Ar g T p q r := by
  unfold oriv at h ⊢
  cases hf : (oriTab.flatMap perms6).find? (·.1 == (T, p, q, r)) with
  | none => simp [hf] at h
  | some k =>
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    obtain ⟨e, he, hk'⟩ := List.mem_flatMap.mp hm
    have := hO e he k hk'
    rw [hk] at this
    simpa [hf] using this

/-- Zero reals have the sign `zeroS`. -/
theorem Sg3_zero_of {ρ : V → Bool} (hP : Proper ρ) {r : ℝ} (h : r = 0) : Sg3 ρ zeroS r := by
  rw [h]; exact Sg3_zero hP

/-- A nonzero integer `n` with `0 < n * r` gives the constant `cS n` as the three valued sign of `r`. -/
theorem Sg3_of_mulpos {ρ : V → Bool} (hP : Proper ρ) {n : Int} {r : ℝ} (h : 0 < (n : ℝ) * r) :
    Sg3 ρ (cS n) r := by
  refine Sg3_cS hP n ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩
  · exact (pos_iff_pos_of_mul_pos h).mp (by exact_mod_cast hn)
  · exact (neg_iff_neg_of_mul_pos h).mp (by exact_mod_cast hn)
  · subst hn; simp at h

/-- The facing of the encoder, three valued: `<N t, x p - x q>`. -/
def fup3 (t p q : Nat) : S3 :=
  if inF t p = true then (if inF t q = true then zeroS else (ltrue, lfalse))
  else if inF t q = true then (lfalse, ltrue)
  else if p < q then atomS (V.fv t p q) else negS (atomS (V.fv t q p))

/-- **The facing tells the sign of `<N t, x p - x q>`** (zero when both points are in the facet), for points of the shape. -/
theorem fup3_sound {g : Geo} (hF : FacOK g) (t p q : Nat) (hp : p < 7) (hq : q < 7) :
    Sg3 (rho g) (fup3 t p q) ⟪g.N t, g.x p - g.x q⟫ := by
  have hP := rho_proper g
  have e1 : ∀ a b, ⟪g.N t, g.x a - g.x b⟫ = - ⟪g.N t, g.x b - g.x a⟫ := fun a b => by
    rw [← inner_neg_right, neg_sub]
  unfold fup3
  by_cases hip : inF t p = true
  · by_cases hiq : inF t q = true
    · simp only [hip, hiq, if_true]
      exact Sg3_zero_of hP (hF.zero t p q hip hiq)
    · have hiq' : inF t q = false := by simpa using hiq
      simp only [hip, hiq, if_true, if_false]
      have := hF.pos t p q hq hip hiq'
      have := Sg3_of_mulpos hP (n := 1) (r := ⟪g.N t, g.x p - g.x q⟫) (by simpa using this)
      simpa [cS, ltrue, lfalse, zeroS] using this
  · have hip' : inF t p = false := by simpa using hip
    by_cases hiq : inF t q = true
    · simp only [hip, hiq, if_true, if_false]
      have := hF.pos t q p hp hiq hip'
      have := Sg3_of_mulpos hP (n := -1) (r := ⟪g.N t, g.x p - g.x q⟫)
        (by rw [e1 p q]; push_cast; linarith)
      simpa [cS, ltrue, lfalse, zeroS] using this
    · simp only [hip, hiq, if_false]
      by_cases hpq : p < q
      · simp only [hpq, if_true]
        exact Sg3_atomG g (v := V.fv t p q) (by simp [rho])
      · simp only [hpq, if_false]
        have := (Sg3_atomG g (v := V.fv t q p) (by simp [rho])).neg
        rw [e1 p q]; exact this

/-- Both ends of edge `e` lie in facet `T`. -/
def inFe (T e : Nat) : Bool := inF T (EA e) && inF T (EB e)
/-- The diagonals of the quad (facet 5 = 1456, cyclic order 1 4 6 5). -/
def isDiag (T e : Nat) : Bool :=
  let a := EA e; let b := EB e
  T == 5 && ((a == 1 && b == 6) || (a == 4 && b == 5))
/-- Two edges of a quad on opposite sides. -/
def oppSides (T x y : Nat) : Bool :=
  T == 5 && !(EA x == EA y || EA x == EB y || EB x == EA y || EB x == EB y) && !(isDiag T x)

/-- The A term by two oriented triples (edges `x = c a`, `y = d b` of a quad, or not adjacent). -/
def AconstD (T x y : Nat) : Int :=
  let c := EA x; let a := EB x; let d := EA y; let b := EB y
  let o1 := oriv T a b d; let o2 := oriv T b c d
  if o1 == o2 then o1 else 0

/-- The constant sign of `A(dx, dy) = det3 dx dy (N T)`, `0` if unknown. -/
def Aconst (T x y : Nat) : Int :=
  let ex := [EA x, EB x]; let ey := [EA y, EB y]
  match ex.filter (ey.contains ·) with
  | [v] =>
    let sx := if EA x == v then (-1 : Int) else 1
    let sy := if EA y == v then (-1 : Int) else 1
    let ox := if EA x == v then EB x else EA x
    let oy := if EA y == v then EB y else EA y
    sx * sy * oriv T v ox oy
  | _ => AconstD T x y

/-- The entry of the facet route: two edges `x, y` of facet `T`, a third edge `o`. -/
def facS (T x y o : Nat) : S3 :=
  mul3 (if oppSides T x y then atomS (V.kv T x y) else cS (Aconst T x y)) (fup3 T (EA o) (EB o))

/-- The A term at a shared vertex. -/
theorem A_shared {g : Geo} (hO : OriOK g) (T x y v ox oy : Nat) (sx sy : Int)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (hx : g.dv x = (sx : ℝ) • (g.x ox - g.x v)) (hy : g.dv y = (sy : ℝ) • (g.x oy - g.x v))
    (h : oriv T v ox oy ≠ 0) :
    0 < ((sx * sy * oriv T v ox oy : Int) : ℝ) * det3 (g.dv x) (g.dv y) (g.N T) := by
  have o := oriv_sound hO T v ox oy h
  have e : det3 (g.dv x) (g.dv y) (g.N T) = (sx : ℝ) * sy * Ar g T v ox oy := by
    rw [hx, hy]; simp only [Ar, det3_expand, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]; ring
  have s1 : (sx : ℝ) * sx = 1 := by rcases hsx with rfl | rfl <;> norm_num
  have s2 : (sy : ℝ) * sy = 1 := by rcases hsy with rfl | rfl <;> norm_num
  rw [e]
  calc (0 : ℝ) < (oriv T v ox oy : ℝ) * Ar g T v ox oy := o
    _ = _ := by push_cast; linear_combination (-(oriv T v ox oy : ℝ) * Ar g T v ox oy * sy * sy) * s1 -
        ((oriv T v ox oy : ℝ) * Ar g T v ox oy) * s2

/-- The A term of two edges that are not simply adjacent: a sum of two oriented triples. -/
theorem A_diag {g : Geo} (hO : OriOK g) (T x y : Nat) (h : AconstD T x y ≠ 0) :
    0 < (AconstD T x y : ℝ) * det3 (g.dv x) (g.dv y) (g.N T) := by
  have e : det3 (g.dv x) (g.dv y) (g.N T) = Ar g T (EB x) (EB y) (EA y) + Ar g T (EB y) (EA x) (EA y) := by
    simp only [Geo.dv, Ar, det3_expand, PiLp.sub_apply]; ring
  unfold AconstD at h ⊢
  simp only at h ⊢
  by_cases hc : oriv T (EB x) (EB y) (EA y) == oriv T (EB y) (EA x) (EA y)
  · simp only [hc, if_true] at h ⊢
    have hc' := beq_iff_eq.mp hc
    have o1 := oriv_sound hO T (EB x) (EB y) (EA y) h
    have o2 := oriv_sound hO T (EB y) (EA x) (EA y) (by rwa [← hc'])
    rw [← hc'] at o2
    rw [e]; push_cast; nlinarith
  · simp [hc] at h

/-- The difference of an edge at a shared vertex `v`, as a signed difference from `v`. -/
theorem dv_shared (g : Geo) (x v : Nat) (hv : v = EA x ∨ v = EB x) :
    g.dv x = (((if EA x == v then (-1 : Int) else 1 : Int) : ℝ)) •
      (g.x (if EA x == v then EB x else EA x) - g.x v) := by
  by_cases hA : EA x = v
  · simp only [beq_self_eq_true, hA, if_true, Geo.dv]
    ext i; simp [hA]
  · have hB : v = EB x := by tauto
    have hn : ¬ (EA x == v) = true := by simpa using hA
    rw [if_neg hn, if_neg hn]
    unfold Geo.dv
    rw [hB]; simp

/-- **The A term is the sign of `det3 dx dy N`** when `Aconst` is nonzero. -/
theorem Aconst_sound {g : Geo} (hO : OriOK g) (T x y : Nat) (h : Aconst T x y ≠ 0) :
    0 < (Aconst T x y : ℝ) * det3 (g.dv x) (g.dv y) (g.N T) := by
  unfold Aconst at h ⊢
  rcases hv : List.filter (fun z => ([EA y, EB y]).contains z) [EA x, EB x] with _ | ⟨v, _ | ⟨w, L⟩⟩
  · simp only [hv] at h ⊢; exact A_diag hO T x y h
  · simp only [hv] at h ⊢
    have hm : v ∈ List.filter (fun z => ([EA y, EB y]).contains z) [EA x, EB x] := by rw [hv]; simp
    simp only [List.mem_filter, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hx : v = EA x ∨ v = EB x := by rcases hm.1 with h | h <;> simp [h]
    have hy : v = EA y ∨ v = EB y := by rcases hm.2 with h | h <;> simp [h]
    have h0 : oriv T v (if EA x == v then EB x else EA x) (if EA y == v then EB y else EA y) ≠ 0 := by
      intro h0; apply h; rw [h0]; simp
    exact A_shared hO T x y v _ _ _ _ (by split_ifs <;> simp) (by split_ifs <;> simp)
      (dv_shared g x v hx) (dv_shared g y v hy) h0
  · simp only [hv] at h ⊢; exact A_diag hO T x y h

/-- **Soundness of the facet route**: two edges `x, y` of facet `T` and a third edge `o`. -/
theorem facS_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) (T x y o : Nat) (hT : T < 9)
    (hx : inFe T x = true) (hy : inFe T y = true) (hp : EA o < 7) (hq : EB o < 7)
    (hA0 : oppSides T x y = false → Aconst T x y ≠ 0) :
    Sg3 (rho g) (facS T x y o) (det3 (g.dv x) (g.dv y) (g.dv o)) := by
  have hxi := Bool.and_eq_true_iff.mp hx
  have hyi := Bool.and_eq_true_iff.mp hy
  have hu : ⟪g.N T, g.dv x⟫ = 0 := hF.zero T _ _ hxi.1 hxi.2
  have hv : ⟪g.N T, g.dv y⟫ = 0 := hF.zero T _ _ hyi.1 hyi.2
  refine fac_core3 (rho_proper g) (rho_gateOK g) hu hv (hF.nn T hT) ?_ (fup3_sound hF T _ _ hp hq)
  by_cases ho : oppSides T x y = true
  · simp only [ho, if_true]
    exact Sg3_atomG g (v := V.kv T x y) (by simp [rho])
  · have ho' : oppSides T x y = false := by simpa using ho
    simp only [ho', Bool.false_eq_true, if_false]
    exact Sg3_of_mulpos (rho_proper g) (Aconst_sound hO T x y (hA0 ho'))

/-- The check of a facet-route key. -/
def facChk (e1 e2 e3 T x y o oi : Nat) (ent : S3) : Bool :=
  decide (T < 9) && inFe T x && inFe T y && !inFe T o && decide (EA o < 7) && decide (EB o < 7) &&
  (oppSides T x y || decide (Aconst T x y ≠ 0)) &&
  ((oi == 0 && e1 == o && e2 == x && e3 == y) || (oi == 1 && e1 == x && e2 == o && e3 == y) ||
   (oi == 2 && e1 == x && e2 == y && e3 == o)) &&
  decide (ent = if oi == 1 then negS (facS T x y o) else facS T x y o)

/-- **A key of the facet route is true.** -/
theorem fac_key3 {g : Geo} (hF : FacOK g) (hO : OriOK g) (e1 e2 e3 T x y o oi : Nat) (ent : S3)
    (h : facChk e1 e2 e3 T x y o oi ent = true) :
    Sg3 (rho g) ent (det3 (g.dv e1) (g.dv e2) (g.dv e3)) := by
  simp only [facChk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    beq_iff_eq, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hT, hx⟩, hy⟩, ho⟩, hp⟩, hq⟩, hA⟩, hperm⟩, hent⟩ := h
  have hA0 : oppSides T x y = false → Aconst T x y ≠ 0 := by
    intro hf; rcases hA with h | h
    · simp [hf] at h
    · exact h
  have S := facS_sound hF hO T x y o hT hx hy hp hq hA0
  rw [hent]
  rcases hperm with (⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩) | ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  · rw [h0]; simp only [show (0:Nat) ≠ 1 by decide, ite_false]
    rw [h1, h2, h3, det3_cyc]; exact S
  · rw [h0]; simp only [ite_true]
    rw [h1, h2, h3, det3_swap2]; exact S.neg
  · rw [h0]; simp only [show (2:Nat) ≠ 1 by decide, ite_false]
    rw [h1, h2, h3]; exact S

/-- Normalizer for the ring identities of the generated key proofs. -/
macro "ent_ring" : tactic =>
  `(tactic| (simp only [Geo.dv, EA, EB, edges, Bq, Geo.atom, det3_expand]; try simp; try ring))

/-- Three vectors in the plane of a facet have determinant 0. -/
theorem zq_key3 {g : Geo} (hF : FacOK g) (e1 e2 e3 T : Nat) (hT : T < 9)
    (h : (inFe T e1 && inFe T e2 && inFe T e3) = true) :
    Sg3 (rho g) zeroS (det3 (g.dv e1) (g.dv e2) (g.dv e3)) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have a1 := Bool.and_eq_true_iff.mp h1
  have a2 := Bool.and_eq_true_iff.mp h2
  have a3 := Bool.and_eq_true_iff.mp h3
  have hu : ⟪g.N T, g.dv e1⟫ = 0 := hF.zero T _ _ a1.1 a1.2
  have hv : ⟪g.N T, g.dv e2⟫ = 0 := hF.zero T _ _ a2.1 a2.2
  have hw : ⟪g.N T, g.dv e3⟫ = 0 := hF.zero T _ _ a3.1 a3.2
  have n := hF.nn T hT
  have id := det_perp (g.dv e1) (g.dv e2) (g.dv e3) (g.N T) hu hv
  rw [hw, mul_zero] at id
  refine entry_zero (rho_proper g) ?_
  rcases mul_eq_zero.mp id with h | h
  · exact h
  · exact absurd h n.ne'

/-- A key whose entry is an integer multiple of an atom (routes BR, L, M). -/
theorem at_key3 {g : Geo} (e1 e2 e3 : Nat) (v : V) (c : Int) (hv : rho g v = decide (0 < g.atom v))
    (hdet : det3 (g.dv e1) (g.dv e2) (g.dv e3) = (c : ℝ) * g.atom v) :
    Sg3 (rho g) (scaleS c (atomS v)) (det3 (g.dv e1) (g.dv e2) (g.dv e3)) :=
  entry_atom (rho_proper g) c (Sg3_atomG g hv) hdet

/-- A key with three vertices in a facet: the determinant is `c` times a bracket of known sign. -/
theorem b4_key3 {g : Geo} (hF : FacOK g) (hO : OriOK g) (e1 e2 e3 T p q r s : Nat) (c : Int)
    (hp : inF T p = true) (hq : inF T q = true) (hr : inF T r = true) (hs : inF T s = false)
    (hs7 : s < 7) (ho : oriv T p q r ≠ 0) (hc : c ≠ 0)
    (hdet : det3 (g.dv e1) (g.dv e2) (g.dv e3) = (c : ℝ) * Bq g p q r s) :
    Sg3 (rho g) (cS (c * -oriv T p q r)) (det3 (g.dv e1) (g.dv e2) (g.dv e3)) := by
  apply Sg3_of_mulpos (rho_proper g)
  have o := oriv_sound hO T p q r ho
  have b := brk_fwd hF T p q r s hp hq hr hs7 hs (oriv T p q r : ℝ) o
  have cc : 0 < (c : ℝ) * c := mul_self_pos.2 (by exact_mod_cast hc)
  rw [hdet]
  push_cast
  calc (0:ℝ) < ((c : ℝ) * c) * (-(oriv T p q r : ℝ) * Bq g p q r s) := mul_pos cc b
    _ = _ := by ring

end Minimality.H29.SAT
