module

public import Mathlib

/-!
# No unimodal view: the checker and its soundness

Everything is computable data on `ℕ` and `ℤ` (the 7 integer points, certificates of
non-existence of a direction `u`), plus the soundness proof that a successful check of a
prefix tree of directed cycles refutes every unimodal view.  See `NoUnimodalData.lean` for the
tree and `NoUnimodal.lean` for the final theorem.
-/

@[expose] public section

namespace NoUni


abbrev Ent := ℕ × ℤ × ℤ × ℤ

/-- real value of an integer form at u -/
def ev (e : ℤ × ℤ × ℤ) (u0 u1 u2 : ℝ) : ℝ := (e.1 : ℝ) * u0 + (e.2.1 : ℝ) * u1 + (e.2.2 : ℝ) * u2

theorem sum_pos_of_pos (c : List Ent) (u0 u1 u2 : ℝ)
    (hpos : ∀ e ∈ c, 0 < ev e.2 u0 u1 u2 ∨ e.1 = 0)
    (hn : ∃ e ∈ c, 0 < e.1 ∧ 0 < ev e.2 u0 u1 u2) :
    0 < (c.map fun e => (e.1 : ℝ) * ev e.2 u0 u1 u2).sum := by
  induction c with
  | nil => simp at hn
  | cons e t ih =>
    rw [List.map_cons, List.sum_cons]
    obtain ⟨f, hf, hf1, hf2⟩ := hn
    have hnn : ∀ g ∈ t, 0 ≤ (g.1 : ℝ) * ev g.2 u0 u1 u2 := by
      intro g hg
      rcases hpos g (List.mem_cons_of_mem _ hg) with h | h
      · exact mul_nonneg (Nat.cast_nonneg _) h.le
      · simp [h]
    have hrest : 0 ≤ (t.map fun e => (e.1 : ℝ) * ev e.2 u0 u1 u2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact hnn g hg
    rcases List.mem_cons.mp hf with rfl | hft
    · have : 0 < (f.1 : ℝ) * ev f.2 u0 u1 u2 := mul_pos (by exact_mod_cast hf1) hf2
      linarith
    · have ih' := ih (fun g hg => hpos g (List.mem_cons_of_mem _ hg)) ⟨f, hft, hf1, hf2⟩
      have he : 0 ≤ (e.1 : ℝ) * ev e.2 u0 u1 u2 := by
        rcases hpos e (List.mem_cons_self) with h | h
        · exact mul_nonneg (Nat.cast_nonneg _) h.le
        · simp [h]
      linarith

theorem lin_sum (c : List Ent) (u0 u1 u2 : ℝ) :
    (c.map fun e => (e.1 : ℝ) * ev e.2 u0 u1 u2).sum
      = u0 * ((c.map fun e => (e.1 * e.2.1 : ℤ)).sum : ℝ)
        + u1 * ((c.map fun e => (e.1 * e.2.2.1 : ℤ)).sum : ℝ)
        + u2 * ((c.map fun e => (e.1 * e.2.2.2 : ℤ)).sum : ℝ) := by
  induction c with
  | nil => simp
  | cons e t ih => simp only [List.map_cons, List.sum_cons, ev] at *; rw [ih]; push_cast; ring

/-- the Farkas refutation: integer cancellation of the combination forces False. -/
theorem farkas (c : List Ent) (u0 u1 u2 : ℝ)
    (hpos : ∀ e ∈ c, 0 < ev e.2 u0 u1 u2 ∨ e.1 = 0)
    (hn : ∃ e ∈ c, 0 < e.1 ∧ 0 < ev e.2 u0 u1 u2)
    (hz0 : (c.map fun e => (e.1 : ℤ) * e.2.1).sum = 0)
    (hz1 : (c.map fun e => (e.1 : ℤ) * e.2.2.1).sum = 0)
    (hz2 : (c.map fun e => (e.1 : ℤ) * e.2.2.2).sum = 0) : False := by
  have hp := sum_pos_of_pos c u0 u1 u2 hpos hn
  rw [lin_sum c u0 u1 u2, hz0, hz1, hz2] at hp
  simp at hp


/-! ### Points and forms -/

abbrev Pt := ℤ × ℤ × ℤ

/-- The seven points (integer coordinates, scaled by `10^9`). -/
def ptl : List Pt :=
  [(51897202, 413632303, 0), (-455240122, 71597558, 0), (-154550307, -361859367, 0),
   (521970500, -133513387, 0), (448927840, -154823279, -516291263),
   (38475512, 517400344, -509817599), (-239099660, -605980108, -417889553)]

def pt (n : ℕ) : Pt := ptl.getD n (0, 0, 0)
def psub (a b : Pt) : Pt := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def pcross (a b : Pt) : Pt :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
def pdet (a b c : Pt) : ℤ :=
  (pcross a b).1 * c.1 + (pcross a b).2.1 * c.2.1 + (pcross a b).2.2 * c.2.2

/-- the form `u ↦ det3 (x b - x a) (x m - x a) u` -/
def sideF (a b m : ℕ) : Pt := pcross (psub (pt b) (pt a)) (psub (pt m) (pt a))
/-- the form `u ↦ ±(⟪x b, u⟫ - ⟪x a, u⟫)` -/
def depF (a b : ℕ) (s : Bool) : Pt := if s then psub (pt b) (pt a) else psub (pt a) (pt b)

/-- A reference to a form: `(0, a, b, m)` is `sideF a b m`, `(1, a, b, _)` is `depF a b true`,
`(2, a, b, _)` is `depF a b false`. -/
abbrev Ref := ℕ × ℕ × ℕ × ℕ

def form (r : Ref) : Pt :=
  if r.1 = 0 then sideF r.2.1 r.2.2.1 r.2.2.2 else depF r.2.1 r.2.2.1 (decide (r.1 = 1))

def PosSide (u0 u1 u2 : ℝ) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ a b, (a, b) ∈ ps → ∀ m, m < 7 → m ≠ a → m ≠ b → 0 < ev (sideF a b m) u0 u1 u2

def PosDep (u0 u1 u2 : ℝ) (ds : List (ℕ × ℕ × Bool)) : Prop :=
  ∀ a b s, (a, b, s) ∈ ds → 0 < ev (depF a b s) u0 u1 u2

def valid (ps : List (ℕ × ℕ)) (ds : List (ℕ × ℕ × Bool)) (r : Ref) : Bool :=
  decide ((r.1 = 0 ∧ (r.2.1, r.2.2.1) ∈ ps ∧ r.2.2.2 < 7 ∧ r.2.2.2 ≠ r.2.1 ∧ r.2.2.2 ≠ r.2.2.1) ∨
    (r.1 = 1 ∧ (r.2.1, r.2.2.1, true) ∈ ds) ∨ (r.1 = 2 ∧ (r.2.1, r.2.2.1, false) ∈ ds))

theorem valid_pos {u0 u1 u2 : ℝ} {ps ds} (hS : PosSide u0 u1 u2 ps) (hD : PosDep u0 u1 u2 ds)
    (r : Ref) (h : valid ps ds r = true) : 0 < ev (form r) u0 u1 u2 := by
  obtain ⟨t, a, b, m⟩ := r
  simp only [valid, decide_eq_true_eq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · subst h0
    simpa [form] using hS a b h1 m h2 h3 h4
  · subst h0
    simpa [form] using hD a b true h1
  · subst h0
    simpa [form] using hD a b false h1

/-! ### Certificates -/

/-- `c4`: four forms whose weights are the Cramer determinants; `cw`: explicit weights. -/
inductive Cert
  | c4 (r1 r2 r3 r4 : Ref)
  | cw (l : List (ℕ × Ref))

def expand : Cert → List (ℕ × Ref)
  | .c4 r1 r2 r3 r4 =>
    [((pdet (form r2) (form r3) (form r4)).natAbs, r1),
     ((pdet (form r1) (form r3) (form r4)).natAbs, r2),
     ((pdet (form r1) (form r2) (form r4)).natAbs, r3),
     ((pdet (form r1) (form r2) (form r3)).natAbs, r4)]
  | .cw l => l

def ents (l : List (ℕ × Ref)) : List Ent := l.map fun p => (p.1, form p.2)

def certOk (ps : List (ℕ × ℕ)) (ds : List (ℕ × ℕ × Bool)) (c : Cert) : Bool :=
  (expand c).all (fun p => valid ps ds p.2) &&
  (expand c).any (fun p => decide (0 < p.1)) &&
  decide (((ents (expand c)).map fun e => (e.1 : ℤ) * e.2.1).sum = 0 ∧
    ((ents (expand c)).map fun e => (e.1 : ℤ) * e.2.2.1).sum = 0 ∧
    ((ents (expand c)).map fun e => (e.1 : ℤ) * e.2.2.2).sum = 0)

theorem certOk_sound {u0 u1 u2 : ℝ} {ps ds} (hS : PosSide u0 u1 u2 ps) (hD : PosDep u0 u1 u2 ds)
    {c : Cert} (h : certOk ps ds c = true) : False := by
  simp only [certOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, ⟨p0, hp0, hp0pos⟩⟩, hz0, hz1, hz2⟩ := h
  refine farkas (ents (expand c)) u0 u1 u2 ?_ ?_ hz0 hz1 hz2
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact Or.inl (valid_pos hS hD p.2 (hall p hp))
  · refine ⟨(p0.1, form p0.2), List.mem_map.mpr ⟨p0, hp0, rfl⟩, hp0pos, ?_⟩
    exact valid_pos hS hD p0.2 (hall p0 hp0)

/-! ### Configurations -/

def nxt (k i : ℕ) : ℕ := (i + 1) % k

def HR (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ i, i < k → ∀ m, m < 7 → m ≠ c i → m ≠ c (nxt k i) →
    0 < ev (sideF (c i) (c (nxt k i)) m) u0 u1 u2

def HD (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool) : Prop :=
  ∀ i, i < k → 0 < ev (depF (c i) (c (nxt k i)) (s i)) u0 u1 u2

/-- exactly one cyclic transition `true → false` -/
def OneT (k : ℕ) (s : ℕ → Bool) : Prop :=
  ((List.range k).filter fun i => s ((i + k - 1) % k) && !(s i)).length = 1

structure Conf (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool) : Prop where
  k3 : 3 ≤ k
  k7 : k ≤ 7
  lt7 : ∀ i, i < k → c i < 7
  inj : ∀ i, i < k → ∀ j, j < k → c i = c j → i = j
  min : ∀ i, i < k → c 0 ≤ c i
  hr : HR u0 u1 u2 k c
  one : OneT k s
  hd : HD u0 u1 u2 k c s

def Agree (c : ℕ → ℕ) (p : List ℕ) : Prop := ∀ i, i < p.length → c i = p.getD i 0

def pairs (p : List ℕ) : List (ℕ × ℕ) :=
  (List.range (p.length - 1)).map fun i => (p.getD i 0, p.getD (i + 1) 0)
def cpairs (p : List ℕ) : List (ℕ × ℕ) :=
  (List.range p.length).map fun i => (p.getD i 0, p.getD ((i + 1) % p.length) 0)
def dtr (p : List ℕ) (l : List Bool) : List (ℕ × ℕ × Bool) :=
  (List.range p.length).map fun i => (p.getD i 0, p.getD ((i + 1) % p.length) 0, l.getD i false)

theorem posSide_pairs {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length ≤ k) : PosSide u0 u1 u2 (pairs p) := by
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

theorem posSide_cpairs {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) : PosSide u0 u1 u2 (cpairs p) := by
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

theorem posDep_dtr {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) {l : List Bool} (hl : ∀ i, i < k → l.getD i false = s i) :
    PosDep u0 u1 u2 (dtr p l) := by
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

def cands : List ℕ → List ℕ
  | [] => List.range 7
  | v :: p => (List.range 7).filter fun m => decide (v < m ∧ m ∉ v :: p)

def chkPats (p : List ℕ) : List (List Bool) → List Cert → Bool
  | [], [] => true
  | l :: ls, c :: cs => certOk (cpairs p) (dtr p l) c && chkPats p ls cs
  | _, _ => false

def chkC (p : List ℕ) : Closure → Bool
  | .none => decide (p.length < 3)
  | .rim c => certOk (cpairs p) [] c
  | .pats cs => chkPats p (patterns p.length) cs

mutual
def chkT : List ℕ → Tree → Bool
  | p, .kill c => certOk (pairs p) [] c
  | p, .br cl f => chkC p cl && chkF p (cands p) f
def chkF : List ℕ → List ℕ → Forest → Bool
  | _, [], .nil => true
  | p, m :: ms, .cons m' t f => decide (m = m') && chkT (p ++ [m]) t && chkF p ms f
  | _, _, _ => false
end

/-! ### Soundness -/

theorem chkPats_sound {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) :
    ∀ (pats : List (List Bool)) (cs : List Cert), chkPats p pats cs = true →
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
      · refine certOk_sound (posSide_cpairs H hA hp)
          (posDep_dtr H hA hp (fun i hi => getD_map_range s hi)) h.1
      · exact ih cs' h.2 hm'

theorem chkC_sound {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
    (hp : p.length = k) (cl : Closure) (h : chkC p cl = true) : False := by
  cases cl with
  | none => have := H.k3; simp [chkC] at h; omega
  | rim c' => exact certOk_sound (posSide_cpairs H hA hp) (fun _ _ _ h => by simp at h) h
  | pats cs =>
    have hm := mem_patterns H.one
    simp only [chkC] at h
    rw [hp] at h
    exact chkPats_sound H hA hp _ cs h hm

theorem mem_cands {u0 u1 u2 k c s} (H : Conf u0 u1 u2 k c s) {p : List ℕ} (hA : Agree c p)
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
theorem chkT_sound : ∀ (t : Tree) (p : List ℕ), chkT p t = true →
    ∀ (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool), Conf u0 u1 u2 k c s →
      p.length ≤ k → Agree c p → False
  | .kill c', p, h, u0, u1, u2, k, c, s, H, hp, hA =>
    certOk_sound (posSide_pairs H hA hp) (fun _ _ _ h => by simp at h) h
  | .br cl f, p, h, u0, u1, u2, k, c, s, H, hp, hA => by
    simp only [chkT, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le hp with hlt | heq
    · exact chkF_sound f p (cands p) h.2 u0 u1 u2 k c s H hlt hA (mem_cands H hA hlt)
    · exact chkC_sound H hA heq cl h.1
theorem chkF_sound : ∀ (f : Forest) (p ms : List ℕ), chkF p ms f = true →
    ∀ (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ) (s : ℕ → Bool), Conf u0 u1 u2 k c s →
      p.length < k → Agree c p → c p.length ∈ ms → False
  | .nil, p, [], h, u0, u1, u2, k, c, s, H, hlt, hA, hm => by simp at hm
  | .nil, p, m :: ms, h, u0, u1, u2, k, c, s, H, hlt, hA, hm => by simp [chkF] at h
  | .cons m' t f, p, [], h, u0, u1, u2, k, c, s, H, hlt, hA, hm => by simp [chkF] at h
  | .cons m' t f, p, m :: ms, h, u0, u1, u2, k, c, s, H, hlt, hA, hm => by
    simp only [chkF, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, ht⟩, hf⟩ := h
    rcases List.mem_cons.mp hm with hm | hm
    · refine chkT_sound t (p ++ [m]) ht u0 u1 u2 k c s H (by simp; omega) ?_
      have := agree_append hA
      rwa [hm] at this
    · exact chkF_sound f p ms hf u0 u1 u2 k c s H hlt hA hm
end

/-- A tree that passes the check refutes every configuration. -/
theorem tree_sound (t : Tree) (h : chkT [] t = true) (u0 u1 u2 : ℝ) (k : ℕ) (c : ℕ → ℕ)
    (s : ℕ → Bool) (H : Conf u0 u1 u2 k c s) : False :=
  chkT_sound t [] h u0 u1 u2 k c s H (Nat.zero_le _) (fun i hi => by simp at hi)

end NoUni
