module

public import Minimality.Type16SAT.TSem
public import Minimality.Type16SAT.Row

@[expose] public section

/-!
# L16T, T3: clause families 30 (link), 31 (Pluecker), 32 (Cramer), 33 (row3 on P)

For each family `F`: `FRows` is the list of the (up to) eight clauses of the zero sum, over `W`; `FChk` the decidable
check of the tag's parameters; `F_sound` says that every row of a checked tag holds under `rhoW g`;
`F_cover` that a clause covering one of the rows holds (the form the dispatcher calls).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical

namespace Minimality.H16T.SAT
open Minimality.H29.SAT Minimality.H16.SAT

/-- A list of rows covers: the clause covers one of them. -/
theorem holdsW_of_cover {g : Geo} {cl : List LitW} {rows : List (List LitW)}
    (hr : ∀ s ∈ rows, HoldsW (rhoW g) s) (hc : rows.any (fun s => coversW cl s) = true) :
    HoldsW (rhoW g) cl := by
  obtain ⟨s, hs, h⟩ := List.any_eq_true.mp hc
  exact HoldsW.of_covers (rhoW_proper g) h (hr s hs)

/-- The sign of `T(e, f)` over `W`. -/
def TW (e f : Nat) : S3W := liftS (Tt e f)

theorem TW_sound {g : Geo} (hG : GeoOK g) {e f : Nat} (he : e < 21) (hf : f < 21) :
    SgW (rhoW g) (TW e f) ⟪g.dv e, g.dv f⟫ := by
  have := Sg3_Tt g e f (fun h' _ => hG.hv e he)
  rw [vv_lt g he, vv_lt g hf] at this
  exact sgW_rho_lift this

/-- `P(f, q)` over `W`. -/
def PW (t f q : Nat) : S3W := liftS (PS t f q)

/-- Multiplication of three valued signs over `W`, real sign. -/
theorem mulW {g : Geo} {a b : S3W} {r s : ℝ} (ha : SgW (rhoW g) a r) (hb : SgW (rhoW g) b s) :
    SgW (rhoW g) (mul3W a b) (r * s) := SgW.mul3 (rhoW_proper g) (rhoW_gateOK g) ha hb

/-! ### Family 30: link -/

/-- `kS(kap, s)`: `s` for `kap > 0`, its negation otherwise. -/
def kapSW (kap : Int) (s : S3W) : S3W := if 0 < kap then s else negSW s

/-- The rows of the link: `kap P(f,h) - T(e1,f) T(e2,h) + T(e1,h) T(e2,f) = 0` (positively scaled). -/
def linkRows (t e1 e2 f h : Nat) (kap : Int) : List (List LitW) :=
  z4W (kapSW kap (PW t f h)) (negSW (mul3W (TW e1 f) (TW e2 h))) (mul3W (TW e1 h) (TW e2 f)) zeroSW

/-- The check of a link tag `30 t e1 e2 f h kap`: in-plane non-opposite edges, `kap` the forced sign constant
(`Aconst`, the sign of `det(D_e1, D_e2, N_t)`), `f < h`. -/
def linkChk (t e1 e2 f h : Nat) (kap : Int) : Bool :=
  decide (t < 8) && decide (e1 < e2) && decide (e2 < 21) && decide (f < h) && decide (h < 21) &&
  inFe t e1 && inFe t e2 && !oppSides t e1 e2 && decide (kap ≠ 0) && decide (Aconst t e1 e2 = kap)

theorem link_sound {g : Geo} (hG : GeoOK g) {t e1 e2 f h : Nat} {kap : Int}
    (hc : linkChk t e1 e2 f h kap = true) : ∀ cl ∈ linkRows t e1 e2 f h kap, HoldsW (rhoW g) cl := by
  simp only [linkChk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, h12⟩, h2⟩, hfh⟩, hh⟩, i1⟩, i2⟩, -⟩, hk0⟩, hk⟩ := hc
  have hi1 := Bool.and_eq_true_iff.mp i1
  have hi2 := Bool.and_eq_true_iff.mp i2
  have hu : ⟪g.N t, g.dv e1⟫ = 0 := hG.hF.zero t _ _ hi1.1 hi1.2
  have hv : ⟪g.N t, g.dv e2⟫ = 0 := hG.hF.zero t _ _ hi2.1 hi2.2
  have hA : 0 < (Aconst t e1 e2 : ℝ) * det3 (g.dv e1) (g.dv e2) (g.N t) :=
    Aconst_sound hG.hO t e1 e2 (by rw [hk]; exact hk0)
  rw [hk] at hA
  have NN := hG.hF.nn t ht
  have B := binet (g.dv e1) (g.dv e2) (g.N t) (g.dv f) (g.dv h)
    (by rw [real_inner_comm]; exact hu) (by rw [real_inner_comm]; exact hv)
  set A := det3 (g.dv e1) (g.dv e2) (g.N t) with hAdef
  have hP : Pp g t f h = det3 (g.dv f) (g.dv h) (g.N t) := rfl
  have SP := SgW_P g t f h
  have X := mulW (TW_sound hG (e := e1) (f := f) (by omega) (by omega))
    (TW_sound hG (e := e2) (f := h) h2 hh)
  have Y := mulW (TW_sound hG (e := e1) (f := h) (by omega) hh)
    (TW_sound hG (e := e2) (f := f) h2 (by omega))
  have SPk : SgW (rhoW g) (kapSW kap (PW t f h)) (A / ⟪g.N t, g.N t⟫ * Pp g t f h) := by
    unfold kapSW PW
    by_cases hk1 : 0 < kap
    · rw [if_pos hk1]
      have hApos : 0 < A := by
        have : (0 : ℝ) < kap := by exact_mod_cast hk1
        exact (pos_iff_pos_of_mul_pos hA).mp this
      exact SP.scale (div_pos hApos NN)
    · rw [if_neg hk1]
      have hkn : (kap : ℝ) < 0 := by
        have : kap < 0 := lt_of_le_of_ne (not_lt.mp hk1) hk0
        exact_mod_cast this
      have hAneg : A < 0 := by
        by_contra hh; push_neg at hh
        nlinarith
      have := (SP.neg).scale (c := -A / ⟪g.N t, g.N t⟫) (div_pos (by linarith) NN)
      have e : -A / ⟪g.N t, g.N t⟫ * -Pp g t f h = A / ⟪g.N t, g.N t⟫ * Pp g t f h := by ring
      rw [e] at this
      exact this
  refine z4W_sound SPk X.neg Y (SgW_zero (rhoW_proper g)) ?_
  have hNN : ⟪g.N t, g.N t⟫ ≠ 0 := NN.ne'
  field_simp
  rw [hP]
  linear_combination B

theorem link_cover {g : Geo} (hG : GeoOK g) {t e1 e2 f h : Nat} {kap : Int}
    (hc : linkChk t e1 e2 f h kap = true) {cl : List LitW}
    (hcov : (linkRows t e1 e2 f h kap).any (fun s => coversW cl s) = true) : HoldsW (rhoW g) cl :=
  holdsW_of_cover (link_sound hG hc) hcov

/-! ### Family 31: Pluecker -/

theorem plucker_id (n a b c d : ℝ³) :
    det3 n a b * det3 n c d - det3 n a c * det3 n b d + det3 n a d * det3 n b c = 0 := by
  simp only [det3_expand]; ring

def plkRows (t a b c d : Nat) : List (List LitW) :=
  z4W (mul3W (PW t a b) (PW t c d)) (negSW (mul3W (PW t a c) (PW t b d))) (mul3W (PW t a d) (PW t b c)) zeroSW

def plkChk (_t a b c d : Nat) : Bool := decide (a < b) && decide (b < c) && decide (c < d)

theorem plk_sound {g : Geo} {t a b c d : Nat} (hc : plkChk t a b c d = true) :
    ∀ cl ∈ plkRows t a b c d, HoldsW (rhoW g) cl := by
  have P := fun x y => SgW_P g t x y
  refine z4W_sound (mulW (P a b) (P c d)) (mulW (P a c) (P b d)).neg (mulW (P a d) (P b c))
    (SgW_zero (rhoW_proper g)) ?_
  have := plucker_id (g.N t) (g.dv a) (g.dv b) (g.dv c) (g.dv d)
  simp only [Pp, det3_expand] at this ⊢
  linear_combination this

theorem plk_cover {g : Geo} {t a b c d : Nat} (hc : plkChk t a b c d = true) {cl : List LitW}
    (hcov : (plkRows t a b c d).any (fun s => coversW cl s) = true) : HoldsW (rhoW g) cl :=
  holdsW_of_cover (plk_sound hc) hcov

/-! ### Family 32: Cramer -/

theorem cramer_id (N u v w l : ℝ³) (h : ⟪l, N⟫ = 0) :
    ⟪l, u⟫ * det3 v w N - ⟪l, v⟫ * det3 u w N + ⟪l, w⟫ * det3 u v N = 0 := by
  have fd := four_dep N u v w l
  rw [Minimality.H16.SAT.det3_cyc N v w, Minimality.H16.SAT.det3_cyc N u w, Minimality.H16.SAT.det3_cyc N u v] at fd
  linear_combination (-1 : ℝ) * fd + det3 u v w * h

theorem cross_inner_self_left (a b : ℝ³) : ⟪cross a b, a⟫ = 0 := by
  simp only [inn3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- The functional of the Cramer row: `kind = 0`: `T(x, .)`; `kind = 1`: `lineS(t, x, .)` given by the `LS` line `(view, k)`. -/
def lfunS (kind view : Nat) (k : Int) (x w : Nat) : S3W :=
  if kind = 0 then TW x w else liftS (lsS view k w)

def cramRows (t kind x view : Nat) (k : Int) (a b c : Nat) : List (List LitW) :=
  z4W (mul3W (lfunS kind view k x a) (PW t b c)) (negSW (mul3W (lfunS kind view k x b) (PW t a c)))
    (mul3W (lfunS kind view k x c) (PW t a b)) zeroSW

/-- The check of a Cramer tag `32 t kind x a b c`; for kind 1 the `LS` line `(view, k)` of the pair `(t, x)`. -/
def cramChk (t kind x view : Nat) (k : Int) (a b c : Nat) : Bool :=
  decide (t < 8) && decide (a < b) && decide (b < c) && decide (c < 21) &&
  (if kind = 0 then decide (x < 21) && inFe t x
   else decide (kind = 1) && decide (x < 8) && lsOK t x view k)

theorem lfun_sound {g : Geo} (hG : GeoOK g) {t kind x view : Nat} {k : Int}
    (hc : (if kind = 0 then decide (x < 21) && inFe t x
           else decide (kind = 1) && decide (x < 8) && lsOK t x view k) = true) :
    ∃ l : ℝ³, ⟪l, g.N t⟫ = 0 ∧ ∀ w, w < 21 → SgW (rhoW g) (lfunS kind view k x w) ⟪l, g.dv w⟫ := by
  unfold lfunS
  by_cases h0 : kind = 0
  · rw [if_pos h0] at hc
    simp only [if_pos h0, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
    obtain ⟨hx, hi⟩ := hc
    have hi' := Bool.and_eq_true_iff.mp hi
    refine ⟨g.dv x, ?_, fun w hw => TW_sound hG hx hw⟩
    rw [real_inner_comm]; exact hG.hF.zero _ _ _ hi'.1 hi'.2
  · rw [if_neg h0] at hc
    simp only [if_neg h0, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
    obtain ⟨⟨-, -⟩, hl⟩ := hc
    exact ⟨cross (g.N t) (g.N x), cross_inner_self_left _ _, fun w hw => ls_sound hG.hF hG.hO hl hw⟩

theorem cram_sound {g : Geo} (hG : GeoOK g) {t kind x view : Nat} {k : Int} {a b c : Nat}
    (hc : cramChk t kind x view k a b c = true) :
    ∀ cl ∈ cramRows t kind x view k a b c, HoldsW (rhoW g) cl := by
  simp only [cramChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ht, hab⟩, hbc⟩, hc21⟩, hx⟩ := hc
  obtain ⟨l, hl, S⟩ := lfun_sound hG hx
  have P := fun x y => SgW_P g t x y
  refine z4W_sound (mulW (S a (by omega)) (P b c)) (mulW (S b (by omega)) (P a c)).neg
    (mulW (S c hc21) (P a b)) (SgW_zero (rhoW_proper g)) ?_
  have := cramer_id (g.N t) (g.dv a) (g.dv b) (g.dv c) l hl
  simp only [Pp]
  linear_combination this

theorem cram_cover {g : Geo} (hG : GeoOK g) {t kind x view : Nat} {k : Int} {a b c : Nat}
    (hc : cramChk t kind x view k a b c = true) {cl : List LitW}
    (hcov : (cramRows t kind x view k a b c).any (fun s => coversW cl s) = true) : HoldsW (rhoW g) cl :=
  holdsW_of_cover (cram_sound hG hc) hcov

/-! ### Family 33: row3 on P -/

/-- `o(a, b) = P(f, EI a b)`, sign-flipped if `a > b`. -/
def oW (t f a b : Nat) : S3W := if a < b then PW t f (EI a b) else negSW (PW t f (EI b a))

def prowRows (t f a b c : Nat) : List (List LitW) :=
  z4W (oW t f a b) (oW t f b c) (oW t f c a) zeroSW

def prowChk (_t _f a b c : Nat) : Bool := decide (a < b) && decide (b < c) && decide (c < 7)

theorem oW_sound {g : Geo} (t f : Nat) {a b : Nat} (hab : a ≠ b) (ha : a < 7) (hb : b < 7) :
    SgW (rhoW g) (oW t f a b) (det3 (g.dv f) (g.x a - g.x b) (g.N t)) := by
  have key : ∀ a < 7, ∀ b < 7, a < b → EI a b < 21 ∧ EA (EI a b) = a ∧ EB (EI a b) = b := by
    decide +kernel
  unfold oW
  by_cases h : a < b
  · rw [if_pos h]
    obtain ⟨-, h2, h3⟩ := key a ha b hb h
    have := SgW_P g t f (EI a b)
    have hd : g.dv (EI a b) = g.x a - g.x b := by simp only [Geo.dv, h2, h3]
    simp only [Pp, hd] at this
    exact this
  · rw [if_neg h]
    have hlt : b < a := by omega
    obtain ⟨-, h2, h3⟩ := key b hb a ha hlt
    have := (SgW_P g t f (EI b a)).neg
    have hd : g.dv (EI b a) = g.x b - g.x a := by simp only [Geo.dv, h2, h3]
    simp only [Pp, hd] at this
    have e : -det3 (g.dv f) (g.x b - g.x a) (g.N t) = det3 (g.dv f) (g.x a - g.x b) (g.N t) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e] at this
    exact this

theorem prow_sound {g : Geo} {t f a b c : Nat} (hc : prowChk t f a b c = true) :
    ∀ cl ∈ prowRows t f a b c, HoldsW (rhoW g) cl := by
  simp only [prowChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hab, hbc⟩, hc7⟩ := hc
  refine z4W_sound (oW_sound t f (by omega) (by omega) (by omega)) (oW_sound t f (by omega) (by omega) (by omega))
    (oW_sound t f (by omega) (by omega) (by omega)) (SgW_zero (rhoW_proper g)) ?_
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem prow_cover {g : Geo} {t f a b c : Nat} (hc : prowChk t f a b c = true) {cl : List LitW}
    (hcov : (prowRows t f a b c).any (fun s => coversW cl s) = true) : HoldsW (rhoW g) cl :=
  holdsW_of_cover (prow_sound hc) hcov

end Minimality.H16T.SAT
