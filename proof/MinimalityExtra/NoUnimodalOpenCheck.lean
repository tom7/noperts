module

public import Mathlib
public import MinimalityExtra.NoUnimodalCheck

/-!
# Open neighbourhood of the no-unimodal-view point set: the checker

The checker of `NoUnimodalCheck`, but with the point configuration as a parameter `P`, so that it
can be run on the seven integer points (by the kernel) and on every nearby real configuration.
A certificate is a Cramer-type relation `∑ wᵢ fᵢ = 0` among forms `fᵢ` with weights that are
polynomials in `P`; it refutes a view `u` as soon as the weights have one strict sign.  The weight
signs are an open condition on `P`, so a certificate valid at the integer points is valid nearby.
Certificates: `c4` (four arbitrary forms, 4 Cramer weights), `c3` (three forms with a common
rim edge `a b`; weights from `det(e, wᵢ, wⱼ)`), `c2` (two rim forms of the planar quadrilateral;
needs that `P 0 .. P 3` are coplanar).
-/

@[expose] public section

namespace NoUniO

abbrev V (R : Type*) := R × R × R

section ops
variable {R : Type*} [CommRing R]

def vsub (a b : V R) : V R := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def vcross (a b : V R) : V R :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
def vdot (a b : V R) : R := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def vdet (a b c : V R) : R := vdot (vcross a b) c

abbrev Ref := ℕ × ℕ × ℕ × ℕ

def sideF (P : ℕ → V R) (a b m : ℕ) : V R := vcross (vsub (P b) (P a)) (vsub (P m) (P a))
def depF (P : ℕ → V R) (a b : ℕ) (s : Bool) : V R :=
  if s then vsub (P b) (P a) else vsub (P a) (P b)
/-- `(0, a, b, m)` is `sideF a b m`, `(1, a, b, _)` is `depF a b true`, `(2, a, b, _)` is
`depF a b false`. -/
def form (P : ℕ → V R) (r : Ref) : V R :=
  if r.1 = 0 then sideF P r.2.1 r.2.2.1 r.2.2.2 else depF P r.2.1 r.2.2.1 (decide (r.1 = 1))

inductive Cert
  | c4 (r1 r2 r3 r4 : Ref)
  | c3 (a b m1 m2 m3 : ℕ)
  | c2 (r1 r2 : Ref)

def weights (P : ℕ → V R) : Cert → List R
  | .c4 r1 r2 r3 r4 =>
    [vdet (form P r2) (form P r3) (form P r4), -vdet (form P r1) (form P r3) (form P r4),
     vdet (form P r1) (form P r2) (form P r4), -vdet (form P r1) (form P r2) (form P r3)]
  | .c3 a b m1 m2 m3 =>
    [vdet (vsub (P b) (P a)) (vsub (P m2) (P a)) (vsub (P m3) (P a)),
     -vdet (vsub (P b) (P a)) (vsub (P m1) (P a)) (vsub (P m3) (P a)),
     vdet (vsub (P b) (P a)) (vsub (P m1) (P a)) (vsub (P m2) (P a))]
  | .c2 r1 r2 => [-vdot (form P r1) (form P r2), vdot (form P r1) (form P r1)]

/-- the weights have one strict sign -/
def wsignB [LT R] [DecidableLT R] (l : List R) : Bool :=
  l.all (fun w => decide (0 < w)) || l.all (fun w => decide (w < 0))

def refs : Cert → List Ref
  | .c4 r1 r2 r3 r4 => [r1, r2, r3, r4]
  | .c3 a b m1 m2 m3 => [(0, a, b, m1), (0, a, b, m2), (0, a, b, m3)]
  | .c2 r1 r2 => [r1, r2]

end ops

def valid (ps : List (ℕ × ℕ)) (ds : List (ℕ × ℕ × Bool)) (r : Ref) : Bool :=
  decide ((r.1 = 0 ∧ (r.2.1, r.2.2.1) ∈ ps ∧ r.2.2.2 < 7 ∧ r.2.2.2 ≠ r.2.1 ∧ r.2.2.2 ≠ r.2.2.1) ∨
    (r.1 = 1 ∧ (r.2.1, r.2.2.1, true) ∈ ds) ∨ (r.1 = 2 ∧ (r.2.1, r.2.2.1, false) ∈ ds))

/-- the structural (point-independent) part of a certificate check -/
def structOk (ps : List (ℕ × ℕ)) (ds : List (ℕ × ℕ × Bool)) : Cert → Bool
  | .c2 r1 r2 => valid ps ds r1 && valid ps ds r2 && decide (r1.1 = 0 ∧ r2.1 = 0) &&
      decide (r1.2.1 < 4 ∧ r1.2.2.1 < 4 ∧ r1.2.2.2 < 4 ∧ r2.2.1 < 4 ∧ r2.2.2.1 < 4 ∧ r2.2.2.2 < 4)
  | c => (refs c).all (valid ps ds)

/-- the full check of a certificate on the point configuration `P` -/
def certB {R : Type*} [CommRing R] [LT R] [DecidableLT R] (P : ℕ → V R)
    (ps : List (ℕ × ℕ)) (ds : List (ℕ × ℕ × Bool)) (c : Cert) : Bool :=
  structOk ps ds c && wsignB (weights P c)

/-! ### Soundness of a certificate -/

def PosSide (P : ℕ → V ℝ) (u : V ℝ) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ a b, (a, b) ∈ ps → ∀ m, m < 7 → m ≠ a → m ≠ b → 0 < vdot (sideF P a b m) u

def PosDep (P : ℕ → V ℝ) (u : V ℝ) (ds : List (ℕ × ℕ × Bool)) : Prop :=
  ∀ a b s, (a, b, s) ∈ ds → 0 < vdot (depF P a b s) u

/-- the points `P 0, .., P 3` lie on a plane -/
def Planar (P : ℕ → V ℝ) : Prop :=
  ∃ (n : V ℝ) (h : ℝ), 0 < vdot n n ∧ ∀ i, i < 4 → vdot n (P i) = h

theorem valid_pos {P : ℕ → V ℝ} {u : V ℝ} {ps ds} (hS : PosSide P u ps) (hD : PosDep P u ds)
    (r : Ref) (h : valid ps ds r = true) : 0 < vdot (form P r) u := by
  obtain ⟨t, a, b, m⟩ := r
  simp only [valid, decide_eq_true_eq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · subst h0
    simpa [form] using hS a b h1 m h2 h3 h4
  · subst h0
    simpa [form] using hD a b true h1
  · subst h0
    simpa [form] using hD a b false h1

theorem cramer4_dot (f1 f2 f3 f4 u : V ℝ) :
    vdet f2 f3 f4 * vdot f1 u + (-vdet f1 f3 f4) * vdot f2 u + vdet f1 f2 f4 * vdot f3 u
      + (-vdet f1 f2 f3) * vdot f4 u = 0 := by
  simp only [vdet, vdot, vcross]; ring

theorem cramer3_dot (e w1 w2 w3 u : V ℝ) :
    vdet e w2 w3 * vdot (vcross e w1) u + (-vdet e w1 w3) * vdot (vcross e w2) u
      + vdet e w1 w2 * vdot (vcross e w3) u = 0 := by
  simp only [vdet, vdot, vcross]; ring

theorem par_cross (n p q : V ℝ) (hn : vdot n n ≠ 0) (hp : vdot n p = 0) (hq : vdot n q = 0) :
    ∃ t : ℝ, vcross p q = (t * n.1, t * n.2.1, t * n.2.2) := by
  obtain ⟨n1, n2, n3⟩ := n
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only [vdot, vcross] at *
  refine ⟨(n1 * (p2 * q3 - p3 * q2) + n2 * (p3 * q1 - p1 * q3) + n3 * (p1 * q2 - p2 * q1)) /
    (n1 * n1 + n2 * n2 + n3 * n3), ?_⟩
  simp only [div_mul_eq_mul_div, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hn]
    linear_combination (-(n2 * p3 - n3 * p2)) * hq + (n2 * q3 - n3 * q2) * hp
  · rw [eq_div_iff hn]
    linear_combination (-(n3 * p1 - n1 * p3)) * hq + (n3 * q1 - n1 * q3) * hp
  · rw [eq_div_iff hn]
    linear_combination (-(n1 * p2 - n2 * p1)) * hq + (n1 * q2 - n2 * q1) * hp

theorem quad_dot (n p q r s u : V ℝ) (hn : 0 < vdot n n) (hp : vdot n p = 0) (hq : vdot n q = 0)
    (hr : vdot n r = 0) (hs : vdot n s = 0) :
    vdot (vcross p q) (vcross p q) * vdot (vcross r s) u
      - vdot (vcross p q) (vcross r s) * vdot (vcross p q) u = 0 := by
  obtain ⟨t1, h1⟩ := par_cross n p q hn.ne' hp hq
  obtain ⟨t2, h2⟩ := par_cross n r s hn.ne' hr hs
  rw [h1, h2]
  simp only [vdot]
  ring

theorem form_side (P : ℕ → V ℝ) (a b m : ℕ) : form P (0, a, b, m) = sideF P a b m := by
  simp [form]

theorem sign_contra {w1 w2 w3 w4 y1 y2 y3 y4 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hw : (0 < w1 ∧ 0 < w2 ∧ 0 < w3 ∧ 0 < w4) ∨ (w1 < 0 ∧ w2 < 0 ∧ w3 < 0 ∧ w4 < 0))
    (h0 : w1 * y1 + w2 * y2 + w3 * y3 + w4 * y4 = 0) : False := by
  rcases hw with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · nlinarith [mul_pos a hy1, mul_pos b hy2, mul_pos c hy3, mul_pos d hy4]
  · nlinarith [mul_neg_of_neg_of_pos a hy1, mul_neg_of_neg_of_pos b hy2,
      mul_neg_of_neg_of_pos c hy3, mul_neg_of_neg_of_pos d hy4]

theorem sign_contra3 {w1 w2 w3 y1 y2 y3 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hw : (0 < w1 ∧ 0 < w2 ∧ 0 < w3) ∨ (w1 < 0 ∧ w2 < 0 ∧ w3 < 0))
    (h0 : w1 * y1 + w2 * y2 + w3 * y3 = 0) : False := by
  rcases hw with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · nlinarith [mul_pos a hy1, mul_pos b hy2, mul_pos c hy3]
  · nlinarith [mul_neg_of_neg_of_pos a hy1, mul_neg_of_neg_of_pos b hy2,
      mul_neg_of_neg_of_pos c hy3]

theorem sign_contra2 {w1 w2 y1 y2 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hw : (0 < w1 ∧ 0 < w2) ∨ (w1 < 0 ∧ w2 < 0)) (h0 : w1 * y1 + w2 * y2 = 0) : False := by
  rcases hw with ⟨a, b⟩ | ⟨a, b⟩
  · nlinarith [mul_pos a hy1, mul_pos b hy2]
  · nlinarith [mul_neg_of_neg_of_pos a hy1, mul_neg_of_neg_of_pos b hy2]

theorem certB_sound {P : ℕ → V ℝ} {u : V ℝ} {ps ds} (hpl : Planar P) (hS : PosSide P u ps)
    (hD : PosDep P u ds) {c : Cert} (h : certB P ps ds c = true) : False := by
  unfold certB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hst, hw⟩ := h
  simp only [wsignB, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  cases c with
  | c4 r1 r2 r3 r4 =>
    simp only [structOk, refs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hst
    have y1 := valid_pos hS hD r1 hst.1
    have y2 := valid_pos hS hD r2 hst.2.1
    have y3 := valid_pos hS hD r3 hst.2.2.1
    have y4 := valid_pos hS hD r4 hst.2.2.2
    simp only [weights, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hw
    exact sign_contra y1 y2 y3 y4 (by tauto) (cramer4_dot _ _ _ _ u)
  | c3 a b m1 m2 m3 =>
    simp only [structOk, refs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hst
    have y1 := valid_pos hS hD _ hst.1
    have y2 := valid_pos hS hD _ hst.2.1
    have y3 := valid_pos hS hD _ hst.2.2
    simp only [form_side, sideF] at y1 y2 y3
    simp only [weights, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hw
    have := cramer3_dot (vsub (P b) (P a)) (vsub (P m1) (P a)) (vsub (P m2) (P a))
      (vsub (P m3) (P a)) u
    exact sign_contra3 y1 y2 y3 (by tauto) this
  | c2 r1 r2 =>
    obtain ⟨t1, a1, b1, m1⟩ := r1
    obtain ⟨t2, a2, b2, m2⟩ := r2
    simp only [structOk, Bool.and_eq_true, decide_eq_true_eq] at hst
    obtain ⟨⟨⟨hv1, hv2⟩, ⟨ht1, ht2⟩⟩, hlt⟩ := hst
    subst ht1 ht2
    have y1 := valid_pos hS hD _ hv1
    have y2 := valid_pos hS hD _ hv2
    simp only [form_side, sideF] at y1 y2
    simp only [weights, form_side, sideF, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hw
    obtain ⟨n, hh, hn, hpn⟩ := hpl
    have hd : ∀ a b : ℕ, a < 4 → b < 4 → vdot n (vsub (P b) (P a)) = 0 := by
      intro a b ha hb
      have := hpn a ha
      have := hpn b hb
      simp only [vdot, vsub] at *
      linarith
    have key := quad_dot n (vsub (P b1) (P a1)) (vsub (P m1) (P a1)) (vsub (P b2) (P a2))
      (vsub (P m2) (P a2)) u hn (hd _ _ hlt.1 hlt.2.1) (hd _ _ hlt.1 hlt.2.2.1)
      (hd _ _ hlt.2.2.2.1 hlt.2.2.2.2.1) (hd _ _ hlt.2.2.2.1 hlt.2.2.2.2.2)
    exact sign_contra2 y1 y2 hw (by linear_combination key)


/-! ### Configurations and the certificate tree -/

def nxt (k i : ℕ) : ℕ := (i + 1) % k

def HR (P : ℕ → V ℝ) (u : V ℝ) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ i, i < k → ∀ m, m < 7 → m ≠ c i → m ≠ c (nxt k i) →
    0 < vdot (sideF P (c i) (c (nxt k i)) m) u

def HD (P : ℕ → V ℝ) (u : V ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool) : Prop :=
  ∀ i, i < k → 0 < vdot (depF P (c i) (c (nxt k i)) (s i)) u

/-- exactly one cyclic transition `true → false` -/
def OneT (k : ℕ) (s : ℕ → Bool) : Prop :=
  ((List.range k).filter fun i => s ((i + k - 1) % k) && !(s i)).length = 1

structure Conf (P : ℕ → V ℝ) (u : V ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool) : Prop where
  k3 : 3 ≤ k
  k7 : k ≤ 7
  lt7 : ∀ i, i < k → c i < 7
  inj : ∀ i, i < k → ∀ j, j < k → c i = c j → i = j
  min : ∀ i, i < k → c 0 ≤ c i
  hr : HR P u k c
  one : OneT k s
  hd : HD P u k c s

def Agree (c : ℕ → ℕ) (p : List ℕ) : Prop := ∀ i, i < p.length → c i = p.getD i 0

def pairs (p : List ℕ) : List (ℕ × ℕ) :=
  (List.range (p.length - 1)).map fun i => (p.getD i 0, p.getD (i + 1) 0)
def cpairs (p : List ℕ) : List (ℕ × ℕ) :=
  (List.range p.length).map fun i => (p.getD i 0, p.getD ((i + 1) % p.length) 0)
def dtr (p : List ℕ) (l : List Bool) : List (ℕ × ℕ × Bool) :=
  (List.range p.length).map fun i => (p.getD i 0, p.getD ((i + 1) % p.length) 0, l.getD i false)

theorem posSide_pairs {P u k c s} (H : Conf P u k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length ≤ k) : PosSide P u (pairs p) := by
  intro a b hab m hm h1 h2
  simp only [pairs, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
  obtain ⟨i, hi, rfl, rfl⟩ := hab
  have hi' : i < k := by omega
  have e1 := hA i (by omega)
  have e2 := hA (i + 1) (by omega)
  have hn : nxt k i = i + 1 := by
    unfold nxt; exact Nat.mod_eq_of_lt (by omega)
  have := H.hr i hi' m hm (by rw [e1]; exact h1) (by rw [hn, e2]; exact h2)
  rw [hn, e1, e2] at this
  exact this

theorem posSide_cpairs {P u k c s} (H : Conf P u k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) : PosSide P u (cpairs p) := by
  intro a b hab m hm h1 h2
  simp only [cpairs, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
  obtain ⟨i, hi, rfl, rfl⟩ := hab
  have e1 := hA i hi
  have hlt : (i + 1) % p.length < p.length := Nat.mod_lt _ (by omega)
  have e2 := hA ((i + 1) % p.length) hlt
  have hn : nxt k i = (i + 1) % p.length := by unfold nxt; rw [hp]
  have := H.hr i (by omega) m hm (by rw [e1]; exact h1) (by rw [hn, e2]; exact h2)
  rw [hn, e1, e2] at this
  exact this

theorem posDep_dtr {P u k c s} (H : Conf P u k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) {l : List Bool} (hl : ∀ i, i < k → l.getD i false = s i) :
    PosDep P u (dtr p l) := by
  intro a b t hab
  simp only [dtr, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
  obtain ⟨i, hi, rfl, rfl, rfl⟩ := hab
  have e1 := hA i hi
  have hlt : (i + 1) % p.length < p.length := Nat.mod_lt _ (by omega)
  have e2 := hA ((i + 1) % p.length) hlt
  have hn : nxt k i = (i + 1) % p.length := by unfold nxt; rw [hp]
  have := H.hd i (by omega)
  rw [hn, e1, e2, ← hl i (by omega)] at this
  exact this

/-! ### Patterns -/

def allBools : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap fun l => [l ++ [false], l ++ [true]]

def tc (k : ℕ) (l : List Bool) : ℕ :=
  ((List.range k).filter fun i => l.getD ((i + k - 1) % k) false && !(l.getD i false)).length

def patterns (k : ℕ) : List (List Bool) := (allBools k).filter fun l => decide (tc k l = 1)

theorem mem_allBools (s : ℕ → Bool) (n : ℕ) : (List.range n).map s ∈ allBools n := by
  induction n with
  | zero => simp [allBools]
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    simp only [allBools, List.mem_flatMap, List.map_cons, List.map_nil]
    refine ⟨_, ih, ?_⟩
    cases s n <;> simp

theorem getD_map_range (s : ℕ → Bool) {k i : ℕ} (h : i < k) :
    ((List.range k).map s).getD i false = s i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem mem_patterns {k : ℕ} {s : ℕ → Bool} (h : OneT k s) : (List.range k).map s ∈ patterns k := by
  unfold patterns
  rw [List.mem_filter]
  refine ⟨mem_allBools s k, ?_⟩
  simp only [decide_eq_true_eq]
  unfold tc
  refine Eq.trans ?_ h
  congr 1
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  have : (i + k - 1) % k < k := Nat.mod_lt _ (by omega)
  rw [getD_map_range s this, getD_map_range s hi']

/-! ### The tree -/

inductive Closure
  | none
  | rim (c : Cert)
  | pats (l : List Cert)

mutual
inductive Tree
  | kill (c : Cert)
  | br (cl : Closure) (f : Forest)
inductive Forest
  | nil
  | cons (m : ℕ) (t : Tree) (f : Forest)
end

abbrev OkFn := List (ℕ × ℕ) → List (ℕ × ℕ × Bool) → Cert → Bool

def OkSound (P : ℕ → V ℝ) (u : V ℝ) (ok : OkFn) : Prop :=
  ∀ ps ds c, ok ps ds c = true → PosSide P u ps → PosDep P u ds → False

def cands : List ℕ → List ℕ
  | [] => List.range 7
  | v :: p => (List.range 7).filter fun m => decide (v < m ∧ m ∉ v :: p)

def chkPats (ok : OkFn) (p : List ℕ) : List (List Bool) → List Cert → Bool
  | [], [] => true
  | l :: ls, c :: cs => ok (cpairs p) (dtr p l) c && chkPats ok p ls cs
  | _, _ => false

def chkC (ok : OkFn) (p : List ℕ) : Closure → Bool
  | .none => decide (p.length < 3)
  | .rim c => ok (cpairs p) [] c
  | .pats cs => chkPats ok p (patterns p.length) cs

mutual
def chkT (ok : OkFn) : List ℕ → Tree → Bool
  | p, .kill c => ok (pairs p) [] c
  | p, .br cl f => chkC ok p cl && chkF ok p (cands p) f
def chkF (ok : OkFn) : List ℕ → List ℕ → Forest → Bool
  | _, [], .nil => true
  | p, m :: ms, .cons m' t f => decide (m = m') && chkT ok (p ++ [m]) t && chkF ok p ms f
  | _, _, _ => false
end

/-! ### Soundness -/

theorem chkPats_sound {ok P u k c s} (H : Conf P u k c s) (hok : OkSound P u ok) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) :
    ∀ (pats : List (List Bool)) (cs : List Cert), chkPats ok p pats cs = true →
      (List.range k).map s ∈ pats → False := by
  intro pats
  induction pats with
  | nil => intro cs _ hm; simp at hm
  | cons l ls ih =>
    intro cs h hm
    cases cs with
    | nil => simp [chkPats] at h
    | cons c' cs' =>
      simp only [chkPats, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hm with rfl | hm'
      · refine hok _ _ _ h.1 (posSide_cpairs H hA hp)
          (posDep_dtr H hA hp (fun i hi => getD_map_range s hi))
      · exact ih cs' h.2 hm'

theorem chkC_sound {ok P u k c s} (H : Conf P u k c s) (hok : OkSound P u ok) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) (cl : Closure) (h : chkC ok p cl = true) : False := by
  cases cl with
  | none => have := H.k3; simp [chkC] at h; omega
  | rim c' => exact hok _ _ _ h (posSide_cpairs H hA hp) (fun _ _ _ h => by simp at h)
  | pats cs =>
    have hm := mem_patterns H.one
    simp only [chkC] at h
    rw [hp] at h
    exact chkPats_sound H hok hA hp _ cs h hm

theorem mem_cands {P u k c s} (H : Conf P u k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length < k) : c p.length ∈ cands p := by
  cases p with
  | nil => simp only [cands, List.mem_range]; exact H.lt7 0 hp
  | cons v p' =>
    simp only [cands, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨H.lt7 _ hp, ?_, ?_⟩
    · have h0 : c 0 = v := by simpa using hA 0 (by simp)
      have h1 := H.min _ hp
      have h2 : c 0 ≠ c (v :: p').length := fun h =>
        absurd (H.inj _ (by omega) _ hp h) (by simp)
      omega
    · intro hmem
      obtain ⟨i, hi, hi2⟩ := List.mem_iff_getElem.mp hmem
      have e := hA i hi
      have : c i = c (v :: p').length := by
        rw [e, List.getD_eq_getElem _ _ hi]; exact hi2
      have := H.inj _ (by omega) _ hp this
      omega

theorem agree_append {c : ℕ → ℕ} {p : List ℕ} (hA : Agree c p) : Agree c (p ++ [c p.length]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [List.getD_append _ _ _ _ h]; exact hA i h
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

mutual
theorem chkT_sound (ok : OkFn) : ∀ (t : Tree) (p : List ℕ), chkT ok p t = true →
    ∀ (P : ℕ → V ℝ) (u : V ℝ), OkSound P u ok → ∀ (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool), Conf P u k c s →
      p.length ≤ k → Agree c p → False
  | .kill c', p, h, P, u, hok, k, c, s, H, hp, hA =>
    hok _ _ _ h (posSide_pairs H hA hp) (fun _ _ _ h => by simp at h)
  | .br cl f, p, h, P, u, hok, k, c, s, H, hp, hA => by
    simp only [chkT, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le hp with hlt | heq
    · exact chkF_sound ok f p (cands p) h.2 P u hok k c s H hlt hA (mem_cands H hA hlt)
    · exact chkC_sound H hok hA heq cl h.1
theorem chkF_sound (ok : OkFn) : ∀ (f : Forest) (p ms : List ℕ), chkF ok p ms f = true →
    ∀ (P : ℕ → V ℝ) (u : V ℝ), OkSound P u ok → ∀ (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool), Conf P u k c s →
      p.length < k → Agree c p → c p.length ∈ ms → False
  | .nil, p, [], h, P, u, hok, k, c, s, H, hlt, hA, hm => by simp at hm
  | .nil, p, m :: ms, h, P, u, hok, k, c, s, H, hlt, hA, hm => by simp [chkF] at h
  | .cons m' t f, p, [], h, P, u, hok, k, c, s, H, hlt, hA, hm => by simp [chkF] at h
  | .cons m' t f, p, m :: ms, h, P, u, hok, k, c, s, H, hlt, hA, hm => by
    simp only [chkF, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, ht⟩, hf⟩ := h
    rcases List.mem_cons.mp hm with hm | hm
    · refine chkT_sound ok t (p ++ [m]) ht P u hok k c s H (by simp; omega) ?_
      have := agree_append hA
      rwa [hm] at this
    · exact chkF_sound ok f p ms hf P u hok k c s H hlt hA hm
end

/-- A tree that passes the check refutes every configuration. -/
theorem tree_sound (ok : OkFn) (t : Tree) (h : chkT ok [] t = true) (P : ℕ → V ℝ) (u : V ℝ)
    (hok : OkSound P u ok) (k : ℕ) (c : ℕ → ℕ)
    (s : ℕ → Bool) (H : Conf P u k c s) : False :=
  chkT_sound ok t [] h P u hok k c s H (Nat.zero_le _) (fun i hi => by simp at hi)

end NoUniO
