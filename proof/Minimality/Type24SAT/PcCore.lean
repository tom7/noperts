module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Positivstellensatz (Handelman / Krivine-Stengle) certificates, checked by evaluation in the kernel

A certificate for strict conditions `g_1 > 0, ..., g_k > 0` (integer polynomials in `n` variables) is a list of
terms `(c, a)` with `c > 0` a natural number and `a` an exponent vector over the `g_i`, such that
`Σ c · Π g_i ^ a_i = 0` as a polynomial.  At a common solution every term is positive, so the sum is positive:
contradiction (`check_sound`).

Representation (chosen for the kernel's speed: `Nat` operations on literals are GMP calls there).
- A monomial is one natural number, the exponents as base-`B` digits (variable `j` is digit `j`); the product of
  monomials is `Nat.add`, the comparison `Nat.blt` / `Nat.beq`.  `evk B v k` decodes the digits.  `Nat.add` is the
  product of monomials only without carries; `ds B n k` (the digit sum) bounds every digit, so the checker carries a
  degree bound for every polynomial it multiplies (`DL`) and requires every product's bound to stay below `B`.
- A polynomial is a list `(monomial, coefficient)`.  `padd` (merge), `pscale`, `pmul` are correct for every input,
  sorted or not; sortedness (ascending keys, which the generator provides and the operations keep) only makes the
  cancellation complete.
- The certificate is a binary tree of terms (`CT`), summed bottom-up (balanced merges).
- The kernel-evaluated functions are written with the recursors (`List.rec`, `Nat.rec`, `CT.rec`) directly: the
  kernel reduces them without the `brecOn` / matcher layers of compiled structural recursion (about 2x faster here).
The certificate data enter the proof only through `check ... = true`, proved by `decide +kernel`.
-/

set_option autoImplicit false

namespace Minimality.PC

/-- A sparse polynomial: (packed monomial, integer coefficient). -/
abbrev Poly := List (Nat × Int)

/-! ### Semantics -/

/-- Value of the packed monomial `k` (base `B` digits) at the point `v`. -/
noncomputable def evk (B : Nat) : List ℝ → Nat → ℝ
  | [], _ => 1
  | x :: xs, k => x ^ (k % B) * evk B xs (k / B)

/-- Value of a polynomial at the point `v`. -/
noncomputable def peval (B : Nat) (v : List ℝ) : Poly → ℝ
  | [] => 0
  | (m, c) :: p => (c : ℝ) * evk B v m + peval B v p

/-- Digit sum of the first `n` base `B` digits (the total degree of the monomial). -/
def ds (B : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => k % B + ds B n (k / B)

theorem add_mod_div_of_ds {B : Nat} (hB : 0 < B) {k1 k2 : Nat} (h : k1 % B + k2 % B < B) :
    (k1 + k2) % B = k1 % B + k2 % B ∧ (k1 + k2) / B = k1 / B + k2 / B := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mod, Nat.mod_eq_of_lt h]
  · rw [Nat.add_div hB, if_neg (by omega)]; rfl

/-- Without carries the packed sum is the product of monomials. -/
theorem evk_add (B : Nat) (hB : 0 < B) (v : List ℝ) (k1 k2 : Nat)
    (h : ds B v.length k1 + ds B v.length k2 < B) : evk B v (k1 + k2) = evk B v k1 * evk B v k2 := by
  induction v generalizing k1 k2 with
  | nil => simp [evk]
  | cons x xs ih =>
    simp only [List.length_cons, ds] at h
    obtain ⟨h1, h2⟩ := add_mod_div_of_ds hB (k1 := k1) (k2 := k2) (by omega)
    simp only [evk, h1, h2, pow_add]
    rw [ih (k1 / B) (k2 / B) (by omega)]; ring

theorem ds_add (B : Nat) (hB : 0 < B) (n k1 k2 : Nat) (h : ds B n k1 + ds B n k2 < B) :
    ds B n (k1 + k2) = ds B n k1 + ds B n k2 := by
  induction n generalizing k1 k2 with
  | zero => rfl
  | succ n ih =>
    simp only [ds] at h ⊢
    obtain ⟨h1, h2⟩ := add_mod_div_of_ds hB (k1 := k1) (k2 := k2) (by omega)
    rw [h1, h2, ih _ _ (by omega)]; ring

theorem evk_zero (B : Nat) (v : List ℝ) : evk B v 0 = 1 := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [evk, ih]

theorem ds_zero (B n : Nat) : ds B n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ds, ih]

theorem blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

/-- Every monomial of `p` has degree at most `D`. -/
def DL (B n D : Nat) (p : Poly) : Prop := ∀ t ∈ p, ds B n t.1 ≤ D

/-! ### The kernel-evaluated operations -/

/-- Merge of the term `(m, c)` followed by `p` into `q`; `rest = padd p`. -/
noncomputable def addGo (m : Nat) (c : Int) (rest : Poly → Poly) (p : Poly) (q : Poly) : Poly :=
  List.rec (motive := fun _ => Poly) ((m, c) :: p)
    (fun nd q ih => bif Nat.beq m nd.1 then
        (bif Nat.beq (Int.natAbs (Int.add c nd.2)) 0 then rest q else (m, Int.add c nd.2) :: rest q)
      else bif Nat.blt m nd.1 then (m, c) :: rest (nd :: q) else nd :: ih) q

/-- Sum of polynomials (a merge of sorted term lists). -/
noncomputable def padd (p : Poly) : Poly → Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun q => q) (fun mc p ih q => addGo mc.1 mc.2 ih p q) p

/-- A polynomial times the term `d * mono(n)`. -/
noncomputable def pscale (n : Nat) (d : Int) (p : Poly) : Poly :=
  List.rec (motive := fun _ => Poly) [] (fun mc _ ih => (Nat.add mc.1 n, Int.mul mc.2 d) :: ih) p

/-- Product of polynomials, one merge per term of `q`. -/
noncomputable def pmulS (p q : Poly) : Poly :=
  List.rec (motive := fun _ => Poly) [] (fun nd _ ih => padd (pscale nd.1 nd.2 p) ih) q

/-- Number of terms. -/
noncomputable def plen (p : Poly) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) p

/-- Product of polynomials, one merge per term of the shorter factor (the merges cost about `|short|^2 |long|`). -/
noncomputable def pmul (p q : Poly) : Poly := bif Nat.blt (plen p) (plen q) then pmulS q p else pmulS p q

/-- `p * g ^ k`. -/
noncomputable def ppow (g : Poly) (k : Nat) (p : Poly) : Poly :=
  Nat.rec (motive := fun _ => Poly → Poly) (fun p => p) (fun _ ih p => ih (pmul p g)) k p

/-- `p * Π g_i ^ a_i`. -/
noncomputable def tprod (gs : List Poly) : List Nat → Poly → Poly :=
  List.rec (motive := fun _ => List Nat → Poly → Poly) (fun _ p => p)
    (fun g _ ih as p => List.rec (motive := fun _ => Poly) p (fun a as' _ => ih as' (ppow g a p)) as) gs

/-- A certificate: a binary tree of terms `c · Π g_i ^ a_i`. -/
inductive CT where
  | leaf (c : Nat) (a : List Nat)
  | node (l r : CT)

/-- The certificate's sum. -/
noncomputable def ctSum (gs : List Poly) (t : CT) : Poly :=
  CT.rec (motive := fun _ => Poly) (fun c a => tprod gs a [(0, (c : Int))]) (fun _ _ il ir => padd il ir) t

/-- Degree bound of a term: `Σ a_i * dg_i`. -/
noncomputable def tdeg (dg : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun d _ ih as => List.rec (motive := fun _ => Nat) 0 (fun a as' _ => Nat.add (Nat.mul a d) (ih as')) as) dg

/-- Every leaf has a positive coefficient and degree bound below `B`. -/
noncomputable def ctOK (B : Nat) (dg : List Nat) (t : CT) : Bool :=
  CT.rec (motive := fun _ => Bool) (fun c a => Nat.blt 0 c && Nat.blt (tdeg dg a) B) (fun _ _ il ir => il && ir) t

/-- Every monomial of `g` has degree at most `d`. -/
noncomputable def degOK (B n : Nat) (g : Poly) (d : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun mc _ ih => Nat.ble (ds B n mc.1) d && ih) g

/-- The degree bounds `dg` hold for the polynomials `gs` (lists of equal length). -/
noncomputable def degsOK (B n : Nat) : List Poly → List Nat → Bool
  | [], [] => true
  | g :: gs, d :: dg => degOK B n g d && degsOK B n gs dg
  | _, _ => false

/-- **The checker.** -/
noncomputable def check (B n : Nat) (gs : List Poly) (dg : List Nat) (t : CT) : Bool :=
  Nat.blt 0 B && degsOK B n gs dg && ctOK B dg t && (ctSum gs t).isEmpty

/-! ### Soundness -/

section
variable {B : Nat} (v : List ℝ)

theorem padd_nil (q : Poly) : padd [] q = q := rfl
theorem padd_cons (m : Nat) (c : Int) (p q : Poly) : padd ((m, c) :: p) q = addGo m c (padd p) p q := rfl
theorem addGo_nil (m : Nat) (c : Int) (rest : Poly → Poly) (p : Poly) : addGo m c rest p [] = (m, c) :: p := rfl
theorem addGo_cons (m : Nat) (c : Int) (rest : Poly → Poly) (p : Poly) (n : Nat) (d : Int) (q : Poly) :
    addGo m c rest p ((n, d) :: q) =
      bif Nat.beq m n then
        (bif Nat.beq (Int.natAbs (Int.add c d)) 0 then rest q else (m, Int.add c d) :: rest q)
      else bif Nat.blt m n then (m, c) :: rest ((n, d) :: q) else (n, d) :: addGo m c rest p q := rfl

theorem peval_padd (p q : Poly) : peval B v (padd p q) = peval B v p + peval B v q := by
  induction p generalizing q with
  | nil => simp [padd_nil, peval]
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    rw [padd_cons]
    induction q with
    | nil => simp [addGo_nil, peval]
    | cons s q ihq =>
      obtain ⟨n, d⟩ := s
      rw [addGo_cons]
      cases h1 : Nat.beq m n
      · cases h3 : Nat.blt m n
        · simp only [Bool.cond_false, peval] at ihq ⊢; rw [ihq]; ring
        · simp only [Bool.cond_false, Bool.cond_true, peval, ih]; ring
      · have hmn : m = n := Nat.eq_of_beq_eq_true h1
        subst hmn
        cases h2 : Nat.beq (Int.natAbs (Int.add c d)) 0
        · simp only [Bool.cond_true, Bool.cond_false, peval, ih]
          have : ((Int.add c d : Int) : ℝ) = c + d := by
            show ((c + d : Int) : ℝ) = c + d
            push_cast; ring
          rw [this]; ring
        · have : c + d = 0 := Int.natAbs_eq_zero.mp (Nat.eq_of_beq_eq_true h2)
          have hr : ((c : ℝ) + d) = 0 := by exact_mod_cast this
          simp only [Bool.cond_true, peval, ih]
          linear_combination (-evk B v m) * hr

theorem DL_padd {n D : Nat} (p q : Poly) (hp : DL B n D p) (hq : DL B n D q) : DL B n D (padd p q) := by
  induction p generalizing q with
  | nil => simpa [padd_nil] using hq
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    have hm : ds B n m ≤ D := hp _ List.mem_cons_self
    have hp' : DL B n D p := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    rw [padd_cons]
    induction q with
    | nil =>
      rw [addGo_nil]; intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hm
      · exact hp' s hs
    | cons s q ihq =>
      obtain ⟨k, d⟩ := s
      have hk : ds B n k ≤ D := hq _ List.mem_cons_self
      have hq' : DL B n D q := fun s hs => hq s (List.mem_cons_of_mem _ hs)
      rw [addGo_cons]
      cases h1 : Nat.beq m k
      · cases h3 : Nat.blt m k
        · simp only [Bool.cond_false]; intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hk
          · exact ihq hq' s hs
        · simp only [Bool.cond_false, Bool.cond_true]; intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hm
          · exact ih _ hp' hq s hs
      · cases h2 : Nat.beq (Int.natAbs (Int.add c d)) 0
        · simp only [Bool.cond_true, Bool.cond_false]; intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hm
          · exact ih _ hp' hq' s hs
        · simp only [Bool.cond_true]; exact ih _ hp' hq'

theorem pscale_cons (n : Nat) (d : Int) (m : Nat) (c : Int) (p : Poly) :
    pscale n d ((m, c) :: p) = (m + n, c * d) :: pscale n d p := rfl

theorem pscale_sound (hB : 0 < B) {D E : Nat} (n : Nat) (d : Int) (p : Poly) (hp : DL B v.length D p)
    (hn : ds B v.length n ≤ E) (hDE : D + E < B) :
    DL B v.length (D + E) (pscale n d p) ∧ peval B v (pscale n d p) = d * evk B v n * peval B v p := by
  induction p with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, by simp [pscale, peval]⟩
  | cons t p ih =>
    obtain ⟨m, c⟩ := t
    have hm : ds B v.length m ≤ D := hp _ List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih (fun s hs => hp s (List.mem_cons_of_mem _ hs))
    have hlt : ds B v.length m + ds B v.length n < B := by omega
    rw [pscale_cons]
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · show ds B v.length (m + n) ≤ D + E
        rw [ds_add B hB _ _ _ hlt]; omega
      · exact ih1 s hs
    · simp only [peval, ih2, evk_add B hB v m n hlt]; push_cast; ring

theorem pmulS_cons (p : Poly) (n : Nat) (d : Int) (q : Poly) :
    pmulS p ((n, d) :: q) = padd (pscale n d p) (pmulS p q) := rfl

theorem pmulS_sound (hB : 0 < B) {D E : Nat} (p q : Poly) (hp : DL B v.length D p) (hq : DL B v.length E q)
    (hDE : D + E < B) :
    DL B v.length (D + E) (pmulS p q) ∧ peval B v (pmulS p q) = peval B v p * peval B v q := by
  induction q with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, by simp [pmulS, peval]⟩
  | cons t q ih =>
    obtain ⟨n, d⟩ := t
    obtain ⟨ih1, ih2⟩ := ih (fun s hs => hq s (List.mem_cons_of_mem _ hs))
    obtain ⟨s1, s2⟩ := pscale_sound v hB n d p hp (hq _ List.mem_cons_self) hDE
    rw [pmulS_cons]
    exact ⟨DL_padd _ _ s1 ih1, by rw [peval_padd, s2, ih2]; simp only [peval]; ring⟩

theorem pmul_sound (hB : 0 < B) {D E : Nat} (p q : Poly) (hp : DL B v.length D p) (hq : DL B v.length E q)
    (hDE : D + E < B) :
    DL B v.length (D + E) (pmul p q) ∧ peval B v (pmul p q) = peval B v p * peval B v q := by
  unfold pmul
  cases Nat.blt (plen p) (plen q)
  · exact pmulS_sound v hB p q hp hq hDE
  · simp only [Bool.cond_true]
    obtain ⟨h1, h2⟩ := pmulS_sound v hB q p hq hp (by omega)
    exact ⟨by rw [Nat.add_comm]; exact h1, by rw [h2, mul_comm]⟩

theorem ppow_succ (g : Poly) (k : Nat) (p : Poly) : ppow g (k + 1) p = ppow g k (pmul p g) := rfl

theorem ppow_sound (hB : 0 < B) {E : Nat} (g : Poly) (hg : DL B v.length E g) (hg0 : 0 < peval B v g) :
    ∀ (k : Nat) (p : Poly) (D : Nat), DL B v.length D p → D + k * E < B → 0 < peval B v p →
      DL B v.length (D + k * E) (ppow g k p) ∧ 0 < peval B v (ppow g k p)
  | 0, p, D, hp, _, h0 => by simp only [Nat.zero_mul, Nat.add_zero]; exact ⟨hp, h0⟩
  | k + 1, p, D, hp, hlt, h0 => by
    obtain ⟨m1, m2⟩ := pmul_sound v hB p g hp hg (by nlinarith)
    have := ppow_sound hB g hg hg0 k (pmul p g) (D + E) m1 (by nlinarith) (by rw [m2]; exact mul_pos h0 hg0)
    rw [ppow_succ]
    refine ⟨?_, this.2⟩
    have e : D + E + k * E = D + (k + 1) * E := by ring
    rw [← e]; exact this.1

theorem tprod_cons (g : Poly) (gs : List Poly) (a : Nat) (as : List Nat) (p : Poly) :
    tprod (g :: gs) (a :: as) p = tprod gs as (ppow g a p) := rfl

theorem tdeg_cons (d : Nat) (dg : List Nat) (a : Nat) (as : List Nat) :
    tdeg (d :: dg) (a :: as) = a * d + tdeg dg as := rfl

theorem degOK_DL (n d : Nat) : ∀ g : Poly, degOK B n g d = true → DL B n d g
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | t :: g, h => by
    have h' : Nat.ble (ds B n t.1) d = true ∧ degOK B n g d = true := by
      simpa [degOK] using h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Nat.le_of_ble_eq_true h'.1
    · exact degOK_DL n d g h'.2 s hs

theorem tprod_sound (hB : 0 < B) : ∀ (gs : List Poly) (dg : List Nat) (as : List Nat) (p : Poly) (D : Nat),
    degsOK B v.length gs dg = true → (∀ g ∈ gs, 0 < peval B v g) → DL B v.length D p →
    D + tdeg dg as < B → 0 < peval B v p → 0 < peval B v (tprod gs as p)
  | [], [], as, p, D, _, _, _, _, h0 => by cases as <;> exact h0
  | [], _ :: _, _, _, _, h, _, _, _, _ => by simp [degsOK] at h
  | _ :: _, [], _, _, _, h, _, _, _, _ => by simp [degsOK] at h
  | g :: gs, d :: dg, [], p, D, _, _, _, _, h0 => h0
  | g :: gs, d :: dg, a :: as, p, D, hdeg, hpos, hp, hlt, h0 => by
    simp only [degsOK, Bool.and_eq_true] at hdeg
    have hgd : DL B v.length d g := degOK_DL v.length d g hdeg.1
    rw [tdeg_cons] at hlt
    obtain ⟨q1, q2⟩ := ppow_sound v hB g hgd (hpos g List.mem_cons_self) a p D hp (by omega) h0
    rw [tprod_cons]
    exact tprod_sound hB gs dg as _ (D + a * d) hdeg.2 (fun h hh => hpos h (List.mem_cons_of_mem _ hh)) q1
      (by omega) q2

theorem ctSum_pos (hB : 0 < B) (gs : List Poly) (dg : List Nat) (hdeg : degsOK B v.length gs dg = true)
    (hpos : ∀ g ∈ gs, 0 < peval B v g) : ∀ t : CT, ctOK B dg t = true → 0 < peval B v (ctSum gs t)
  | .leaf c a, h => by
    have h' : Nat.blt 0 c = true ∧ Nat.blt (tdeg dg a) B = true := by simpa [ctOK] using h
    have hc : 0 < c := blt_lt h'.1
    have ha : tdeg dg a < B := blt_lt h'.2
    show 0 < peval B v (tprod gs a [(0, (c : Int))])
    refine tprod_sound v hB gs dg a _ 0 hdeg hpos ?_ (by omega) ?_
    · intro s hs
      rcases List.mem_singleton.mp hs with rfl
      exact (ds_zero B _).le
    · have : (0 : ℝ) < c := by exact_mod_cast hc
      simp [peval, evk_zero, this]
  | .node l r, h => by
    have h' : ctOK B dg l = true ∧ ctOK B dg r = true := by simpa [ctOK] using h
    show 0 < peval B v (padd (ctSum gs l) (ctSum gs r))
    rw [peval_padd]
    have := ctSum_pos hB gs dg hdeg hpos l h'.1
    have := ctSum_pos hB gs dg hdeg hpos r h'.2
    linarith

/-- **Soundness**: a certificate that passes the check shows that the conditions `g > 0` (`g ∈ gs`) have no common
solution `v` (a point with as many coordinates as the packed monomials have digits). -/
theorem check_sound (gs : List Poly) (dg : List Nat) (t : CT)
    (hpos : ∀ g ∈ gs, 0 < peval B v g) (h : check B v.length gs dg t = true) : False := by
  simp only [check, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hB, hdeg⟩, hok⟩, h0⟩ := h
  have := ctSum_pos v (blt_lt hB) gs dg hdeg hpos t hok
  rw [h0] at this
  simp [peval] at this

end

/-! ### Chunked certificates: the tree split into parts, each part's sum given as data (kernel memory per declaration) -/

/-- Sum of a list of polynomials. -/
noncomputable def psum (ps : List Poly) : Poly := List.rec (motive := fun _ => Poly) [] (fun p _ ih => padd p ih) ps

theorem peval_psum (v : List ℝ) {B : Nat} : ∀ ps : List Poly, peval B v (psum ps) = (ps.map (peval B v)).sum
  | [] => rfl
  | p :: ps => by
    show peval B v (padd p (psum ps)) = _
    rw [peval_padd, peval_psum v ps]; simp

/-- **Soundness, chunked**: parts `(t_j, P_j)` with `ctSum gs t_j = P_j` and `ctOK`, and `Σ P_j = 0`. -/
theorem chunks_sound {B : Nat} (v : List ℝ) (gs : List Poly) (dg : List Nat) (parts : List (CT × Poly))
    (hpos : ∀ g ∈ gs, 0 < peval B v g) (hB : 0 < B) (hdeg : degsOK B v.length gs dg = true) (hne : parts ≠ [])
    (hall : ∀ q ∈ parts, ctOK B dg q.1 = true ∧ ctSum gs q.1 = q.2) (h0 : psum (parts.map Prod.snd) = []) : False := by
  have hp : ∀ q ∈ parts, 0 < peval B v q.2 := fun q hq => by
    rw [← (hall q hq).2]; exact ctSum_pos v hB gs dg hdeg hpos q.1 (hall q hq).1
  have : 0 < peval B v (psum (parts.map Prod.snd)) := by
    rw [peval_psum, List.map_map]
    apply List.sum_pos
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hp q hq
    · simpa using hne
  rw [h0] at this
  simp [peval] at this

end Minimality.PC
