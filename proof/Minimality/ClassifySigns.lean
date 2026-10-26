module

public import Minimality.SevenTypes

@[expose] public section

/-!
# Classification of the 7-point types: sign vectors and a certificate checker

The combinatorial half of `exists_sevenType` (`Minimality/Classify.lean`). Seven labelled
points are described by the 35 signs `σ i` of the orientation determinants of the sorted
4-sets `quad i` (colex order). Abstractly, a sign vector is any `σ : Fin 35 → SignType`;
`fsg σ a b c d` is the sign it gives to an arbitrary 4-tuple (alternating: the sign of the
sorting permutation times `σ`, and `0` at a repeated point).

`Hyps σ` collects the sign conditions that the geometry supplies
(`Minimality/ClassifyGeom.lean`): the 3-term Grassmann–Plücker relations, convex position
(no point in a tetrahedron of four others), the quadrilateral facet `{0,1,2,3}`, the
normalization `σ(0,1,2,4) = +`, and lexicographic minimality among the relabellings that
fix `{0,1,2,3}` (`Canon`). `Good σ` says that for some type `k` and some relabelling `π`
every face of `typeL k` is cut out by a triple whose other signs are one-sided.

`check` verifies a decision tree (`Cert`, produced by `nopert229/cls_tree.cc`) whose
leaves are violated conditions, symmetry prunings or accepted types; `check_sound` shows
that a passing tree proves `Hyps σ → Good σ` for every sign vector extending the root.
-/

namespace Minimality.Classify

/-- The 35 sorted 4-subsets of `Fin 7`, in colex order (`quad i` has index
`a + C(b,2) + C(c,3) + C(d,4)`). -/
def quad : Fin 35 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4), (0, 1, 2, 5),
    (0, 1, 3, 5), (0, 2, 3, 5), (1, 2, 3, 5), (0, 1, 4, 5), (0, 2, 4, 5), (1, 2, 4, 5),
    (0, 3, 4, 5), (1, 3, 4, 5), (2, 3, 4, 5), (0, 1, 2, 6), (0, 1, 3, 6), (0, 2, 3, 6),
    (1, 2, 3, 6), (0, 1, 4, 6), (0, 2, 4, 6), (1, 2, 4, 6), (0, 3, 4, 6), (1, 3, 4, 6),
    (2, 3, 4, 6), (0, 1, 5, 6), (0, 2, 5, 6), (1, 2, 5, 6), (0, 3, 5, 6), (1, 3, 5, 6),
    (2, 3, 5, 6), (0, 4, 5, 6), (1, 4, 5, 6), (2, 4, 5, 6), (3, 4, 5, 6)]

/-- The colex index of a sorted 4-tuple. -/
def cidx (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Fin 35 :=
  ⟨(t.1.val + t.2.1.val * (t.2.1.val - 1) / 2 + t.2.2.1.val * (t.2.2.1.val - 1) *
    (t.2.2.1.val - 2) / 6 + t.2.2.2.val * (t.2.2.2.val - 1) * (t.2.2.2.val - 2) *
    (t.2.2.2.val - 3) / 24) % 35, Nat.mod_lt _ (by decide)⟩

/-- Compare-exchange, with the sign of the swap. -/
def cx (a b : Fin 7) : Fin 7 × Fin 7 × SignType :=
  if b < a then (b, a, .neg) else (a, b, .pos)

/-- Sort a 4-tuple (network (01)(23)(02)(13)(12)); the sign of the sorting permutation, or
`0` at a repeated entry. -/
def sort4 (a b c d : Fin 7) : (Fin 7 × Fin 7 × Fin 7 × Fin 7) × SignType :=
  let r1 := cx a b
  let r2 := cx c d
  let r3 := cx r1.1 r2.1
  let r4 := cx r1.2.1 r2.2.1
  let r5 := cx r4.1 r3.2.1
  ((r3.1, r5.1, r5.2.1, r4.2.1),
    if r3.1 < r5.1 ∧ r5.1 < r5.2.1 ∧ r5.2.1 < r4.2.1 then
      r1.2.2 * r2.2.2 * r3.2.2 * r4.2.2 * r5.2.2 else .zero)

/-- The sorted 4-set of a tuple and the sign relating them. -/
def lookup (a b c d : Fin 7) : Fin 35 × SignType :=
  let r := sort4 a b c d
  (cidx r.1, r.2)

/-- The sign of an arbitrary 4-tuple under the sign vector `σ`. -/
def fsg (σ : Fin 35 → SignType) (a b c d : Fin 7) : SignType :=
  (lookup a b c d).2 * σ (lookup a b c d).1

/-- The 24 permutations of four positions, with their signs. -/
def permTable : List ((Fin 4 × Fin 4 × Fin 4 × Fin 4) × SignType) :=
  [((0, 1, 2, 3), .pos), ((0, 1, 3, 2), .neg), ((0, 2, 1, 3), .neg), ((0, 2, 3, 1), .pos),
    ((0, 3, 1, 2), .pos), ((0, 3, 2, 1), .neg), ((1, 0, 2, 3), .neg), ((1, 0, 3, 2), .pos),
    ((1, 2, 0, 3), .pos), ((1, 2, 3, 0), .neg), ((1, 3, 0, 2), .neg), ((1, 3, 2, 0), .pos),
    ((2, 0, 1, 3), .pos), ((2, 0, 3, 1), .neg), ((2, 1, 0, 3), .neg), ((2, 1, 3, 0), .pos),
    ((2, 3, 0, 1), .pos), ((2, 3, 1, 0), .neg), ((3, 0, 1, 2), .neg), ((3, 0, 2, 1), .pos),
    ((3, 1, 0, 2), .pos), ((3, 1, 2, 0), .neg), ((3, 2, 0, 1), .neg), ((3, 2, 1, 0), .pos)]

/-- Entry `i` of a 4-tuple. -/
def tget (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Fin 4 → Fin 7 := ![t.1, t.2.1, t.2.2.1, t.2.2.2]

/-- `lookup` is correct: a tuple with a repeated entry gets sign `0`, any other is a
permutation of its sorted 4-set, with the permutation's sign (checked by evaluation). -/
def lookupOK (a b c d : Fin 7) : Bool :=
  let r := lookup a b c d
  (r.2 == .zero && (a == b || a == c || a == d || b == c || b == d || c == d)) ||
    permTable.any fun p => r.2 == p.2 && tget (quad r.1) p.1.1 == a &&
      tget (quad r.1) p.1.2.1 == b && tget (quad r.1) p.1.2.2.1 == c &&
      tget (quad r.1) p.1.2.2.2 == d

/-- `lookup` is correct on all 2401 tuples. -/
theorem lookupOK_all : ∀ a b c d : Fin 7, lookupOK a b c d = true := by decide

/-- The faces of the 29 types as lists (`sevenTypeFaces` as `Finset`s). -/
def typeL : Fin 29 → List (List (Fin 7)) :=
  ![
    [[0, 1, 2], [0, 1, 3, 4], [0, 2, 3, 5], [1, 2, 4, 5, 6], [3, 4, 6], [3, 5, 6]],
    [[0, 1, 2], [0, 1, 3, 4], [0, 2, 3, 5], [1, 2, 4, 6], [2, 5, 6], [3, 4, 5, 6]],
    [[0, 1, 2], [0, 1, 3], [0, 2, 3, 4, 5, 6], [1, 2, 5], [1, 3, 6], [1, 4, 5], [1, 4, 6]],
    [[0, 1, 2], [0, 1, 3, 4], [0, 2, 6], [0, 4, 5], [0, 5, 6], [1, 2, 3, 5, 6], [3, 4, 5]],
    [[0, 1, 2, 3], [0, 1, 4, 5], [0, 3, 4], [1, 2, 5, 6], [2, 3, 4], [2, 4, 6], [4, 5, 6]],
    [[0, 1, 2, 3], [0, 2, 4], [0, 3, 5], [0, 4, 5], [1, 2, 4, 5, 6], [1, 3, 6], [3, 5, 6]],
    [[0, 1, 2], [0, 1, 3], [0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 3, 4], [2, 4, 5], [4, 5, 6]],
    [[0, 1, 2, 3], [0, 1, 4], [0, 2, 4, 5], [1, 3, 6], [1, 4, 6], [2, 3, 5, 6], [4, 5, 6]],
    [[0, 1, 2], [0, 1, 3, 4], [0, 2, 5, 6], [0, 4, 6], [1, 2, 3], [2, 3, 5], [3, 4, 5, 6]],
    [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 4, 5], [1, 3, 4, 6], [2, 3, 5, 6], [4, 5, 6]],
    [[0, 1, 3], [0, 1, 5], [0, 2, 3, 4, 6], [0, 4, 5], [1, 2, 3], [1, 2, 6], [1, 4, 5], [1, 4, 6]],
    [[0, 1, 3, 5], [0, 2, 4], [0, 2, 5], [0, 3, 4, 6], [1, 2, 3], [1, 2, 5], [2, 3, 6], [2, 4, 6]],
    [[0, 1, 3], [0, 1, 4, 5], [0, 2, 3], [0, 2, 4], [1, 2, 3], [1, 2, 6], [1, 5, 6], [2, 4, 5, 6]],
    [[0, 1, 4], [0, 1, 6], [0, 2, 3, 5], [0, 3, 6], [0, 4, 5], [1, 4, 5, 6], [2, 3, 6], [2, 5, 6]],
    [[0, 1, 4, 5, 6], [0, 2, 4], [0, 2, 6], [1, 3, 4], [1, 3, 5], [2, 3, 4], [2, 3, 6], [3, 5, 6]],
    [[0, 2, 3, 5], [0, 2, 4], [0, 3, 6], [0, 4, 6], [1, 3, 5, 6], [1, 4, 5], [1, 4, 6], [2, 4, 5]],
    [[0, 2, 4, 6], [0, 3, 4], [0, 3, 6], [1, 2, 5], [1, 2, 6], [1, 3, 5], [1, 3, 6], [2, 3, 4, 5]],
    [[0, 1, 4], [0, 1, 5], [0, 3, 4], [0, 3, 5, 6], [1, 2, 4, 5], [2, 4, 6], [2, 5, 6], [3, 4, 6]],
    [[0, 2, 3, 5], [0, 2, 6], [0, 3, 4], [0, 4, 6], [1, 2, 5], [1, 2, 6], [1, 3, 5, 6], [3, 4, 6]],
    [[0, 1, 3, 5], [0, 1, 6], [0, 2, 5], [0, 2, 6], [1, 3, 4], [1, 4, 6], [2, 4, 5, 6], [3, 4, 5]],
    [[0, 1, 4], [0, 1, 5], [0, 2, 5, 6], [0, 4, 6], [1, 3, 4], [1, 3, 5], [2, 3, 4, 6], [2, 3, 5]],
    [[0, 1, 2], [0, 1, 3, 4], [0, 2, 3], [1, 2, 5], [1, 4, 6], [1, 5, 6], [2, 3, 4], [2, 4, 6], [2, 5, 6]],
    [[0, 1, 3], [0, 1, 4], [0, 3, 4, 5], [1, 2, 3], [1, 2, 5], [1, 4, 6], [1, 5, 6], [2, 3, 5], [4, 5, 6]],
    [[0, 1, 2], [0, 1, 6], [0, 2, 5], [0, 3, 4, 5], [0, 4, 6], [1, 2, 6], [2, 3, 5], [2, 3, 6], [3, 4, 6]],
    [[0, 1, 3], [0, 1, 4], [0, 2, 4, 6], [0, 3, 5], [0, 5, 6], [1, 2, 4], [1, 2, 6], [1, 3, 6], [3, 5, 6]],
    [[0, 1, 3], [0, 1, 6], [0, 2, 4, 6], [0, 3, 4], [1, 3, 6], [2, 3, 5], [2, 3, 6], [2, 4, 5], [3, 4, 5]],
    [[0, 1, 2], [0, 1, 6], [0, 2, 5], [0, 4, 5], [0, 4, 6], [1, 2, 3], [1, 3, 6], [2, 3, 5, 6], [4, 5, 6]],
    [[0, 1, 5], [0, 1, 6], [0, 2, 3], [0, 2, 4, 5], [0, 3, 6], [1, 4, 5], [1, 4, 6], [2, 3, 4], [3, 4, 6]],
    [[0, 1, 2], [0, 1, 5], [0, 2, 3], [0, 3, 5], [1, 2, 4], [1, 4, 5, 6], [2, 3, 4], [3, 4, 6], [3, 5, 6]]]

/-- `typeL` lists the faces of `sevenTypeFaces`. -/
theorem sevenTypeFaces_eq (k : Fin 29) :
    sevenTypeFaces k = (typeL k).map List.toFinset := by
  revert k; decide

/-! ### Partial sign vectors -/

/-- A partial sign vector (the signs decided so far along a branch). -/
abbrev PSig := Fin 35 → Option SignType

/-- `σ` extends the partial sign vector `P`. -/
def Ext (P : PSig) (σ : Fin 35 → SignType) : Prop := ∀ i s, P i = some s → σ i = s

/-- Extending by the value of `σ` at `v`. -/
theorem Ext.update {P : PSig} {σ : Fin 35 → SignType} (h : Ext P σ) (v : Fin 35) :
    Ext (Function.update P v (some (σ v))) σ := by
  intro i s hi
  by_cases hiv : i = v
  · subst hiv
    simp only [Function.update_self, Option.some.injEq] at hi
    exact hi
  · rw [Function.update_of_ne hiv] at hi
    exact h i s hi

/-- The sign of a 4-tuple under a partial sign vector, if decided. -/
def psg (P : PSig) (a b c d : Fin 7) : Option SignType :=
  if (lookup a b c d).2 = .zero then some .zero
  else (P (lookup a b c d).1).map ((lookup a b c d).2 * ·)

/-- The sign of a 4-tuple is decided by `P`. -/
def dfd (P : PSig) (a b c d : Fin 7) : Bool := (psg P a b c d).isSome

/-- The sign of a 4-tuple under `P` (`0` if undecided). -/
def pv (P : PSig) (a b c d : Fin 7) : SignType := (psg P a b c d).getD .zero

/-- A decided sign of a partial vector is the sign of every extension. -/
theorem fsg_of_dfd {P : PSig} {σ : Fin 35 → SignType} (h : Ext P σ) {a b c d : Fin 7}
    (hd : dfd P a b c d = true) : fsg σ a b c d = pv P a b c d := by
  unfold dfd at hd
  unfold pv fsg
  unfold psg at hd ⊢
  split_ifs at hd ⊢ with h0
  · rw [h0]; rfl
  · cases hPi : P (lookup a b c d).1 with
    | none => simp [hPi] at hd
    | some t => simp [h _ _ hPi]

/-! ### The sign conditions -/

/-- Three signs of reals with sum `0` are impossible: all `≥ 0` with one `> 0`, or the
mirror image. -/
def viol3 (p q r : SignType) : Bool :=
  (p != .neg && q != .neg && r != .neg && (p == .pos || q == .pos || r == .pos)) ||
    (p != .pos && q != .pos && r != .pos && (p == .neg || q == .neg || r == .neg))

/-- The 3-term Grassmann–Plücker relation
`[xyab][xycd] - [xyac][xybd] + [xyad][xybc] = 0`, violated in sign. -/
def gpV (σ : Fin 35 → SignType) (x y a b c d : Fin 7) : Bool :=
  viol3 (fsg σ x y a b * fsg σ x y c d) (-(fsg σ x y a c * fsg σ x y b d))
    (fsg σ x y a d * fsg σ x y b c)

/-- `v` lies in the tetrahedron `abcd` by signs: `[abcd] ≠ 0` and each of the four
determinants with `v` in place of a vertex vanishes or has the sign of `[abcd]`. -/
def tetV (s0 l1 l2 l3 l4 : SignType) : Bool :=
  s0 != .zero && (l1 == .zero || l1 == s0) && (l2 == .zero || l2 == s0) &&
    (l3 == .zero || l3 == s0) && (l4 == .zero || l4 == s0)

/-- The sign vector of the relabelling by `h`, renormalized so that its sign at
`(0,1,2,4)` is `+`. -/
def act (σ : Fin 35 → SignType) (h : Fin 7 → Fin 7) (i : Fin 35) : SignType :=
  fsg σ (h 0) (h 1) (h 2) (h 4) *
    fsg σ (h (quad i).1) (h (quad i).2.1) (h (quad i).2.2.1) (h (quad i).2.2.2)

/-- The order in which sign vectors are compared lexicographically (the 4-sets with at
least three points of `{0,1,2,3}` first). -/
def lexOrd : List (Fin 35) :=
  [0, 1, 5, 15, 2, 6, 16, 3, 7, 17, 4, 8, 18, 9, 19, 25, 10, 20, 26, 12, 22, 28, 31, 11, 21,
    27, 13, 23, 29, 32, 14, 24, 30, 33, 34]

/-- The sign conditions supplied by the geometry. -/
structure Hyps (σ : Fin 35 → SignType) : Prop where
  gp : ∀ x y a b c d, gpV σ x y a b c d = false
  tet : ∀ v a b c d : Fin 7, v ≠ a → v ≠ b → v ≠ c → v ≠ d →
    tetV (fsg σ a b c d) (fsg σ v b c d) (fsg σ a v c d) (fsg σ a b v d) (fsg σ a b c v) = false
  q0 : fsg σ 0 1 2 3 = .zero
  qn : fsg σ 0 1 2 4 = .pos
  q1 : ∀ a b c l m : Fin 7, a.val < 4 → b.val < 4 → c.val < 4 → a ≠ b → a ≠ c → b ≠ c →
    4 ≤ l.val → 4 ≤ m.val → fsg σ a b c l ≠ .zero ∧ fsg σ a b c l = fsg σ a b c m
  canon : ∀ h : Fin 7 → Fin 7, Function.Injective h → (∀ i, (h i).val < 4 ↔ i.val < 4) →
    ¬ List.Lex (· < ·) (lexOrd.map (act σ h)) (lexOrd.map σ)

/-- The face `g` is cut out by one of its triples: the other points all have one nonzero
sign `s`, the points of `g` sign `0`. -/
def FaceF (σ : Fin 35 → SignType) (g : List (Fin 7)) : Prop :=
  ∃ t0 t1 t2, t0 ∈ g ∧ t1 ∈ g ∧ t2 ∈ g ∧ ∃ s : SignType, s ≠ .zero ∧
    ∀ j, (j ∈ g → fsg σ t0 t1 t2 j = .zero) ∧ (j ∉ g → fsg σ t0 t1 t2 j = s)

/-- The conclusion: for some type `k` and relabelling `π` every face is cut out. -/
def Good (σ : Fin 35 → SignType) : Prop :=
  ∃ (k : Fin 29) (π : Fin 7 → Fin 7), Function.Injective π ∧ ∀ l ∈ typeL k, FaceF σ (l.map π)

/-! ### Leaf checks -/

/-- Leaf: a Grassmann–Plücker relation violated by the decided signs. -/
def gpLeaf (P : PSig) (x y a b c d : Fin 7) : Bool :=
  dfd P x y a b && dfd P x y c d && dfd P x y a c && dfd P x y b d && dfd P x y a d &&
    dfd P x y b c &&
    viol3 (pv P x y a b * pv P x y c d) (-(pv P x y a c * pv P x y b d))
      (pv P x y a d * pv P x y b c)

/-- Leaf: `v` in the tetrahedron `abcd` by the decided signs. -/
def tetLeaf (P : PSig) (v a b c d : Fin 7) : Bool :=
  v != a && v != b && v != c && v != d && dfd P a b c d && dfd P v b c d && dfd P a v c d &&
    dfd P a b v d && dfd P a b c v &&
    tetV (pv P a b c d) (pv P v b c d) (pv P a v c d) (pv P a b v d) (pv P a b c v)

/-- Leaf: `{0,1,2,3}` not coplanar. -/
def q0Leaf (P : PSig) : Bool := dfd P 0 1 2 3 && pv P 0 1 2 3 != .zero

/-- Leaf: the sign at `(0,1,2,4)` is not `+`. -/
def qnLeaf (P : PSig) : Bool := dfd P 0 1 2 4 && pv P 0 1 2 4 != .pos

/-- Leaf: for a triple `abc` of `{0,1,2,3}`, a point `l` off it on its plane, or two
points `l`, `m` off it on opposite sides. -/
def q1Leaf (P : PSig) (a b c l m : Fin 7) : Bool :=
  decide (a.val < 4) && decide (b.val < 4) && decide (c.val < 4) && a != b && a != c &&
    b != c && decide (4 ≤ l.val) && decide (4 ≤ m.val) && dfd P a b c l && dfd P a b c m &&
    (pv P a b c l == .zero || pv P a b c l != pv P a b c m)

/-- `h` is injective (checked). -/
def injB (h : Fin 7 → Fin 7) : Bool :=
  (List.finRange 7).all fun i => (List.finRange 7).all fun j => h i != h j || i == j

/-- `h` maps `{0,1,2,3}` onto itself (checked). -/
def qpresB (h : Fin 7 → Fin 7) : Bool :=
  (List.finRange 7).all fun i => decide ((h i).val < 4) == decide (i.val < 4)

/-- Strict order of signs, as a function. -/
def slt : SignType → SignType → Bool
  | .neg, .zero => true
  | .neg, .pos => true
  | .zero, .pos => true
  | _, _ => false

theorem slt_iff (a b : SignType) : slt a b = true ↔ a < b := by
  cases a <;> cases b <;> decide

/-- The sign of `act σ h i` is decided by `P`. -/
def pdfd (P : PSig) (h : Fin 7 → Fin 7) (i : Fin 35) : Bool :=
  dfd P (h 0) (h 1) (h 2) (h 4) &&
    dfd P (h (quad i).1) (h (quad i).2.1) (h (quad i).2.2.1) (h (quad i).2.2.2)

/-- The sign `act σ h i`, from `P`. -/
def pact (P : PSig) (h : Fin 7 → Fin 7) (i : Fin 35) : SignType :=
  pv P (h 0) (h 1) (h 2) (h 4) *
    pv P (h (quad i).1) (h (quad i).2.1) (h (quad i).2.2.1) (h (quad i).2.2.2)

/-- The relabelling by `h` is lexicographically smaller, as decided by `P`. -/
def symLess (P : PSig) (h : Fin 7 → Fin 7) : List (Fin 35) → Bool
  | [] => false
  | v :: vs => (P v).isSome && pdfd P h v &&
      (slt (pact P h v) ((P v).getD .zero) ||
        (pact P h v == (P v).getD .zero && symLess P h vs))

/-- Leaf: `h` is a relabelling fixing `{0,1,2,3}` whose image is lexicographically
smaller. -/
def symLeaf (P : PSig) (h : Fin 7 → Fin 7) : Bool := injB h && qpresB h && symLess P h lexOrd

/-- The face `g` is cut out by the triple `t0 t1 t2`, as decided by `P`. -/
def faceT (P : PSig) (g : List (Fin 7)) (t0 t1 t2 : Fin 7) : Bool :=
  [SignType.pos, SignType.neg].any fun s => (List.finRange 7).all fun j =>
    dfd P t0 t1 t2 j && (if g.elem j then pv P t0 t1 t2 j == .zero else pv P t0 t1 t2 j == s)

/-- The face `g` is cut out by one of its triples, as decided by `P`. -/
def faceB (P : PSig) (g : List (Fin 7)) : Bool :=
  (g.sublistsLen 3).any fun t => match t with
    | [t0, t1, t2] => faceT P g t0 t1 t2
    | _ => false

/-- Leaf: all faces of type `k`, relabelled by `π` (injective), are cut out. -/
def accLeaf (P : PSig) (k : Fin 29) (π : Fin 7 → Fin 7) : Bool :=
  injB π && (typeL k).all fun l => faceB P (l.map π)

/-! ### Certificates -/

/-- A decision tree over the signs. -/
inductive Cert where
  /-- branch on the sign `v` (children `-`, `0`, `+`) -/
  | br (v : Fin 35) (n z p : Cert)
  /-- a violated Grassmann–Plücker relation -/
  | gp (x y a b c d : Fin 7)
  /-- a point in a tetrahedron -/
  | tet (v a b c d : Fin 7)
  /-- `{0,1,2,3}` not coplanar -/
  | q0
  /-- the normalization violated -/
  | qn
  /-- a point off `{0,1,2,3}` on its plane, or two on opposite sides -/
  | q1 (a b c l m : Fin 7)
  /-- the relabelling by `h` is lexicographically smaller -/
  | sym (h : Fin 7 → Fin 7)
  /-- type `k`, relabelled by `π` -/
  | acc (k : Fin 29) (π : Fin 7 → Fin 7)

/-- The certificate checker. -/
def check : Cert → PSig → Bool
  | .br v n z p, P => check n (Function.update P v (some .neg)) &&
      check z (Function.update P v (some .zero)) && check p (Function.update P v (some .pos))
  | .gp x y a b c d, P => gpLeaf P x y a b c d
  | .tet v a b c d, P => tetLeaf P v a b c d
  | .q0, P => q0Leaf P
  | .qn, P => qnLeaf P
  | .q1 a b c l m, P => q1Leaf P a b c l m
  | .sym h, P => symLeaf P h
  | .acc k π, P => accLeaf P k π

/-! ### Soundness -/

theorem injB_spec {h : Fin 7 → Fin 7} (hb : injB h = true) : Function.Injective h := by
  intro i j hij
  simp only [injB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at hb
  rcases hb i j with h1 | h1
  · exact absurd hij h1
  · exact h1

theorem qpresB_spec {h : Fin 7 → Fin 7} (hb : qpresB h = true) (i : Fin 7) :
    (h i).val < 4 ↔ i.val < 4 := by
  simp only [qpresB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    decide_eq_decide] at hb
  exact hb i

/-- A decided lexicographic comparison holds for every extension. -/
theorem symLess_sound {P : PSig} {σ : Fin 35 → SignType} (hE : Ext P σ) (h : Fin 7 → Fin 7) :
    ∀ l, symLess P h l = true → List.Lex (· < ·) (l.map (act σ h)) (l.map σ)
  | [], hl => by simp [symLess] at hl
  | v :: vs, hl => by
    simp only [symLess, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨⟨hs, hd⟩, hl⟩ := hl
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    have hσ : σ v = t := hE v t ht
    have hact : act σ h v = pact P h v := by
      simp only [pdfd, Bool.and_eq_true] at hd
      rw [act, pact, fsg_of_dfd hE hd.1, fsg_of_dfd hE hd.2]
    rw [ht, Option.getD_some] at hl
    simp only [List.map_cons]
    rcases hl with hlt | ⟨heq, hrest⟩
    · rw [hact, hσ]
      exact List.Lex.rel ((slt_iff _ _).mp hlt)
    · rw [hact, hσ, heq]
      exact List.Lex.cons (symLess_sound hE h vs hrest)

theorem faceT_sound {P : PSig} {σ : Fin 35 → SignType} (hE : Ext P σ) {g : List (Fin 7)}
    {t0 t1 t2 : Fin 7} (hb : faceT P g t0 t1 t2 = true) :
    ∃ s : SignType, s ≠ .zero ∧
      ∀ j, (j ∈ g → fsg σ t0 t1 t2 j = .zero) ∧ (j ∉ g → fsg σ t0 t1 t2 j = s) := by
  simp only [faceT, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true] at hb
  have key : ∀ s : SignType, (∀ j, dfd P t0 t1 t2 j = true ∧
      (if g.elem j then pv P t0 t1 t2 j == .zero else pv P t0 t1 t2 j == s) = true) →
      ∀ j, (j ∈ g → fsg σ t0 t1 t2 j = .zero) ∧ (j ∉ g → fsg σ t0 t1 t2 j = s) := by
    intro s hs j
    obtain ⟨hd, hv⟩ := hs j
    rw [fsg_of_dfd hE hd]
    constructor
    · intro hj
      simp only [show g.elem j = true from List.elem_iff.mpr hj, ↓reduceIte] at hv
      exact beq_iff_eq.mp hv
    · intro hj
      have hf : g.elem j = false := Bool.eq_false_iff.mpr (fun h => hj (List.elem_iff.mp h))
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
      exact beq_iff_eq.mp hv
  rcases hb with hb | hb
  · exact ⟨.pos, by decide, key _ hb⟩
  · exact ⟨.neg, by decide, key _ hb⟩

theorem faceB_sound {P : PSig} {σ : Fin 35 → SignType} (hE : Ext P σ) {g : List (Fin 7)}
    (hb : faceB P g = true) : FaceF σ g := by
  simp only [faceB, List.any_eq_true] at hb
  obtain ⟨t, ht, hb⟩ := hb
  have hsub := (List.mem_sublistsLen.mp ht).1.subset
  match t, hb, hsub with
  | [t0, t1, t2], hb, hsub =>
    exact ⟨t0, t1, t2, hsub (by simp), hsub (by simp), hsub (by simp), faceT_sound hE hb⟩

/-- **Soundness of the checker.** -/
theorem check_sound : ∀ (c : Cert) (P : PSig), check c P = true →
    ∀ σ, Ext P σ → Hyps σ → Good σ
  | .br v n z p, P, hc, σ, hE, hH => by
    simp only [check, Bool.and_eq_true] at hc
    obtain ⟨⟨hn, hz⟩, hp⟩ := hc
    have hE' := hE.update v
    cases hv : σ v with
    | neg => rw [hv] at hE'; exact check_sound n _ hn σ hE' hH
    | zero => rw [hv] at hE'; exact check_sound z _ hz σ hE' hH
    | pos => rw [hv] at hE'; exact check_sound p _ hp σ hE' hH
  | .gp x y a b c d, P, hc, σ, hE, hH => by
    simp only [check, gpLeaf, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hv⟩ := hc
    have := hH.gp x y a b c d
    rw [gpV, fsg_of_dfd hE h1, fsg_of_dfd hE h2, fsg_of_dfd hE h3, fsg_of_dfd hE h4,
      fsg_of_dfd hE h5, fsg_of_dfd hE h6, hv] at this
    exact absurd this (by decide)
  | .tet v a b c d, P, hc, σ, hE, hH => by
    simp only [check, tetLeaf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc'⟩, hd⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hv⟩ := hc
    have := hH.tet v a b c d ha hb hc' hd
    rw [fsg_of_dfd hE h1, fsg_of_dfd hE h2, fsg_of_dfd hE h3, fsg_of_dfd hE h4,
      fsg_of_dfd hE h5, hv] at this
    exact absurd this (by decide)
  | .q0, P, hc, σ, hE, hH => by
    simp only [check, q0Leaf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    have := hH.q0
    rw [fsg_of_dfd hE hc.1] at this
    exact absurd this hc.2
  | .qn, P, hc, σ, hE, hH => by
    simp only [check, qnLeaf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    have := hH.qn
    rw [fsg_of_dfd hE hc.1] at this
    exact absurd this hc.2
  | .q1 a b c l m, P, hc, σ, hE, hH => by
    simp only [check, q1Leaf, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc'⟩, hab⟩, hac⟩, hbc⟩, hl⟩, hm⟩, h1⟩, h2⟩, hv⟩ := hc
    have := hH.q1 a b c l m ha hb hc' hab hac hbc hl hm
    rw [fsg_of_dfd hE h1, fsg_of_dfd hE h2] at this
    rcases hv with hv | hv
    · exact absurd hv this.1
    · exact absurd this.2 hv
  | .sym h, P, hc, σ, hE, hH => by
    simp only [check, symLeaf, Bool.and_eq_true] at hc
    obtain ⟨⟨hi, hq⟩, hs⟩ := hc
    exact absurd (symLess_sound hE h lexOrd hs) (hH.canon h (injB_spec hi) (qpresB_spec hq))
  | .acc k π, P, hc, σ, hE, _ => by
    simp only [check, accLeaf, Bool.and_eq_true, List.all_eq_true] at hc
    exact ⟨k, π, injB_spec hc.1, fun l hl => faceB_sound hE (hc.2 l hl)⟩

end Minimality.Classify

end
