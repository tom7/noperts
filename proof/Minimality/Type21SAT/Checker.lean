module


@[expose] public section
/-!
# KERNEL3: a small verified RUP (LRAT-hint) checker, plain structural Lean, no imports

Literal code `c`: variable `c / 2`, positive iff `c % 2 = 0`.  A clause is a `List Nat`.
The clause database is a binary trie keyed by clause id (depth `D`).  The partial assignment during
unit propagation is a Nat bitmask over literal codes (bit `l` set = literal `l` is true).
-/
set_option autoImplicit false

namespace Minimality.H21.SAT.K3

abbrev Cl := List Nat

def Sat (ρ : Nat → Bool) (l : Nat) : Prop := ((l % 2 == 0) == ρ (l / 2)) = true
def SatCl (ρ : Nat → Bool) (c : Cl) : Prop := ∃ l ∈ c, Sat ρ l

def neg (l : Nat) : Nat := if l % 2 == 0 then l + 1 else l - 1

theorem sat_neg (ρ : Nat → Bool) (l : Nat) : Sat ρ (neg l) ↔ ¬ Sat ρ l := by
  unfold Sat neg
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) % 2 = 1 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    rw [ite_eq_left (by simp [h])]
    simp only [h, h1, h2]
    cases ρ (l / 2) <;> simp
  · have h0 : l % 2 = 1 := by omega
    have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    rw [ite_eq_right (by simp [h0])]
    simp only [h0, h1, h2]
    cases ρ (l / 2) <;> simp

/-! ## The trie -/

inductive Tr where
  | nil : Tr
  | cl : Cl → Tr
  | br : Tr → Tr → Tr

def ins : Nat → Tr → Nat → Cl → Tr
  | 0, _, _, c => Tr.cl c
  | f + 1, Tr.br a b, k, c =>
      if k % 2 == 0 then Tr.br (ins f a (k / 2) c) b else Tr.br a (ins f b (k / 2) c)
  | f + 1, _, k, c =>
      if k % 2 == 0 then Tr.br (ins f Tr.nil (k / 2) c) Tr.nil else Tr.br Tr.nil (ins f Tr.nil (k / 2) c)

def get : Nat → Tr → Nat → Option Cl
  | 0, Tr.cl c, _ => some c
  | 0, _, _ => none
  | f + 1, Tr.br a b, k => if k % 2 == 0 then get f a (k / 2) else get f b (k / 2)
  | f + 1, _, _ => none

/-- Every clause stored in the trie satisfies `P`. -/
def AllT (P : Cl → Prop) : Nat → Tr → Prop
  | 0, Tr.cl c => P c
  | f + 1, Tr.br a b => AllT P f a ∧ AllT P f b
  | _, _ => True

theorem get_sound (P : Cl → Prop) : ∀ (f : Nat) (t : Tr) (k : Nat) (c : Cl),
    AllT P f t → get f t k = some c → P c := by
  intro f
  induction f with
  | zero => intro t k c h e; cases t <;> simp_all [get, AllT]
  | succ f ih =>
    intro t k c h e
    cases t with
    | nil => simp [get] at e
    | cl c' => simp [get] at e
    | br a b =>
      simp only [AllT] at h
      simp only [get] at e
      by_cases hk : k % 2 == 0
      · simp only [hk, ite_true] at e; exact ih a _ c h.1 e
      · simp only [hk] at e; exact ih b _ c h.2 e

theorem ins_sound (P : Cl → Prop) : ∀ (f : Nat) (t : Tr) (k : Nat) (c : Cl),
    AllT P f t → P c → AllT P f (ins f t k c) := by
  intro f
  induction f with
  | zero => intro t k c h hc; simp [ins, AllT, hc]
  | succ f ih =>
    intro t k c h hc
    cases t with
    | nil =>
      by_cases hk : k % 2 == 0
      · simp only [ins, hk, ite_true, AllT]; exact ⟨ih _ _ _ (by cases f <;> simp [AllT]) hc, by cases f <;> simp⟩
      · simp only [ins, hk]; exact ⟨by cases f <;> simp [AllT], ih _ _ _ (by cases f <;> simp [AllT]) hc⟩
    | cl c' =>
      by_cases hk : k % 2 == 0
      · simp only [ins, hk, ite_true, AllT]; exact ⟨ih _ _ _ (by cases f <;> simp [AllT]) hc, by cases f <;> simp⟩
      · simp only [ins, hk]; exact ⟨by cases f <;> simp [AllT], ih _ _ _ (by cases f <;> simp [AllT]) hc⟩
    | br a b =>
      simp only [AllT] at h
      by_cases hk : k % 2 == 0
      · simp only [ins, hk, ite_true, AllT]; exact ⟨ih _ _ _ h.1 hc, h.2⟩
      · simp only [ins, hk]; exact ⟨h.1, ih _ _ _ h.2 hc⟩

theorem nil_allT (P : Cl → Prop) (f : Nat) : AllT P f Tr.nil := by cases f <;> simp [AllT]

/-! ## Unit propagation driven by hints -/

def bit (A l : Nat) : Bool := Nat.testBit A l

/-- Follow the hints; `true` iff a conflict is reached. -/
def go (D : Nat) (db : Tr) : Nat → List Nat → Bool
  | _, [] => false
  | A, h :: hs =>
    match get D db h with
    | none => false
    | some c =>
      match c.filter (fun l => !(bit A (neg l))) with
      | [] => true
      | [l] => go D db (A ||| 2 ^ l) hs
      | _ => false

def negMask (c : Cl) : Nat := c.foldl (fun A l => A ||| 2 ^ (neg l)) 0

def rup (D : Nat) (db : Tr) (c : Cl) (hs : List Nat) : Bool := go D db (negMask c) hs

def AsgOk (ρ : Nat → Bool) (A : Nat) : Prop := ∀ l, Nat.testBit A l = true → Sat ρ l

theorem go_sound (ρ : Nat → Bool) (D : Nat) (db : Tr) (hdb : AllT (SatCl ρ) D db) :
    ∀ (hs : List Nat) (A : Nat), AsgOk ρ A → go D db A hs = true → False := by
  intro hs
  induction hs with
  | nil => intro A _ h; simp [go] at h
  | cons h hs ih =>
    intro A hA hg
    simp only [go] at hg
    cases hget : get D db h with
    | none => rw [hget] at hg; simp at hg
    | some c =>
      rw [hget] at hg
      dsimp only at hg
      have hsat : SatCl ρ c := get_sound _ D db h c hdb hget
      obtain ⟨l0, hl0, hs0⟩ := hsat
      -- the literal l0 is not falsified by A
      have hnf : ∀ l ∈ c, bit A (neg l) = true → ¬ Sat ρ l := by
        intro l _ hb hsl
        exact (sat_neg ρ l).1 (hA _ hb) hsl
      have hmem : l0 ∈ c.filter (fun l => !(bit A (neg l))) := by
        rw [List.mem_filter]
        refine ⟨hl0, ?_⟩
        by_cases hb : bit A (neg l0) = true
        · exact absurd hs0 (hnf l0 hl0 hb)
        · simp [hb]
      generalize hf : c.filter (fun l => !(bit A (neg l))) = fl at hg hmem
      match fl, hg, hmem with
      | [], _, hmem => simp at hmem
      | [l], hg, hmem =>
        have hl : l = l0 := by simpa using (List.mem_singleton.1 hmem).symm
        subst hl
        refine ih (A ||| 2 ^ l) ?_ hg
        intro m hm
        rw [Nat.testBit_or, Nat.testBit_two_pow] at hm
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hm
        rcases hm with hm | hm
        · exact hA m hm
        · subst hm; exact hs0
      | _ :: _ :: _, hg, _ => simp at hg

theorem negMask_ok (ρ : Nat → Bool) (c : Cl) (hc : ¬ SatCl ρ c) : AsgOk ρ (negMask c) := by
  have key : ∀ (c : Cl) (A : Nat), (∀ l ∈ c, ¬ Sat ρ l) → AsgOk ρ A →
      AsgOk ρ (c.foldl (fun A l => A ||| 2 ^ (neg l)) A) := by
    intro c
    induction c with
    | nil => intro A _ h; exact h
    | cons l c ih =>
      intro A hall hA
      apply ih (A ||| 2 ^ neg l) (fun l' hl' => hall l' (List.mem_cons_of_mem _ hl'))
      intro m hm
      rw [Nat.testBit_or, Nat.testBit_two_pow] at hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hm
      rcases hm with hm | hm
      · exact hA m hm
      · subst hm; exact (sat_neg ρ l).2 (hall l (List.mem_cons_self))
  apply key c 0 (fun l hl hs => hc ⟨l, hl, hs⟩)
  intro l hl; simp at hl

theorem rup_sound (ρ : Nat → Bool) (D : Nat) (db : Tr) (hdb : AllT (SatCl ρ) D db) (c : Cl) (hs : List Nat)
    (h : rup D db c hs = true) : SatCl ρ c := by
  refine Classical.byContradiction fun hc => ?_
  exact go_sound ρ D db hdb hs _ (negMask_ok ρ c hc) h

/-! ## The proof steps and the whole check -/

abbrev Step := Nat × Cl × List Nat

/-- Run the steps; `true` iff all pass and the empty clause is derived. -/
def run (D : Nat) : Tr → List Step → Bool
  | _, [] => false
  | db, (id, c, hs) :: rest =>
    if rup D db c hs then
      (match c with
       | [] => true
       | _ :: _ => run D (ins D db id c) rest)
    else false

theorem run_sound (ρ : Nat → Bool) (D : Nat) : ∀ (steps : List Step) (db : Tr),
    AllT (SatCl ρ) D db → run D db steps = true → False := by
  intro steps
  induction steps with
  | nil => intro db _ h; simp [run] at h
  | cons s rest ih =>
    obtain ⟨id, c, hs⟩ := s
    intro db hdb h
    simp only [run] at h
    by_cases hr : rup D db c hs = true
    · have hsat := rup_sound ρ D db hdb c hs hr
      simp only [hr, ite_true] at h
      cases c with
      | nil => obtain ⟨l, hl, _⟩ := hsat; simp at hl
      | cons l c' => exact ih _ (ins_sound _ D db id _ hdb hsat) h
    · simp [hr] at h

/-- Load the original clauses with ids `k, k+1, ...`. -/
def load (D : Nat) : Tr → Nat → List Cl → Tr
  | db, _, [] => db
  | db, k, c :: cs => load D (ins D db k c) (k + 1) cs

theorem load_sound (ρ : Nat → Bool) (D : Nat) : ∀ (cs : List Cl) (db : Tr) (k : Nat),
    AllT (SatCl ρ) D db → (∀ c ∈ cs, SatCl ρ c) → AllT (SatCl ρ) D (load D db k cs) := by
  intro cs
  induction cs with
  | nil => intro db k h _; exact h
  | cons c cs ih =>
    intro db k h hc
    exact ih _ _ (ins_sound _ D db k c h (hc c List.mem_cons_self)) (fun d hd => hc d (List.mem_cons_of_mem _ hd))

def check (D : Nat) (cnf : List Cl) (steps : List Step) : Bool := run D (load D Tr.nil 1 cnf) steps

/-- **Soundness**: if the check passes, no assignment satisfies every clause of `cnf`. -/
theorem check_sound (D : Nat) (cnf : List Cl) (steps : List Step) (h : check D cnf steps = true) :
    ∀ ρ : Nat → Bool, ¬ ∀ c ∈ cnf, SatCl ρ c := by
  intro ρ hρ
  exact run_sound ρ D steps _ (load_sound ρ D cnf _ 1 (nil_allT _ D) hρ) h


/-! ## Chunked checking: each chunk is one kernel declaration, the derived clauses are passed forward as data -/

/-- Verify every step (RUP) and insert its clause. -/
def allRup (D : Nat) : Tr → List Step → Bool
  | _, [] => true
  | db, (id, c, hs) :: rest => rup D db c hs && allRup D (ins D db id c) rest

/-- Insert the clauses of the steps without checking. -/
def insAll (D : Nat) (db : Tr) (steps : List Step) : Tr :=
  steps.foldl (fun db s => ins D db s.1 s.2.1) db

theorem allRup_sound (ρ : Nat → Bool) (D : Nat) : ∀ (steps : List Step) (db : Tr),
    AllT (SatCl ρ) D db → allRup D db steps = true → (∀ s ∈ steps, SatCl ρ s.2.1) := by
  intro steps
  induction steps with
  | nil => intro db _ _ s hs; simp at hs
  | cons s rest ih =>
    obtain ⟨id, c, hs⟩ := s
    intro db hdb h
    simp only [allRup, Bool.and_eq_true] at h
    have hsat := rup_sound ρ D db hdb c hs h.1
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hsat
    · exact ih _ (ins_sound _ D db id c hdb hsat) h.2 t ht

theorem insAll_sound (ρ : Nat → Bool) (D : Nat) : ∀ (steps : List Step) (db : Tr),
    AllT (SatCl ρ) D db → (∀ s ∈ steps, SatCl ρ s.2.1) → AllT (SatCl ρ) D (insAll D db steps) := by
  intro steps
  induction steps with
  | nil => intro db h _; exact h
  | cons s rest ih =>
    intro db h hs
    exact ih _ (ins_sound _ D db s.1 s.2.1 h (hs s List.mem_cons_self)) (fun t ht => hs t (List.mem_cons_of_mem _ ht))

/-- One chunk: the steps of `pre` are taken as given (inserted, not checked), the chunk is verified. -/
def chkChunk (D : Nat) (cnf : List Cl) (pre chunk : List Step) : Bool :=
  allRup D (insAll D (load D Tr.nil 1 cnf) pre) chunk

/-- The chunks are checked one after the other, each one on top of all the earlier ones. -/
def OKs (D : Nat) (cnf : List Cl) : List Step → List (List Step) → Prop
  | _, [] => True
  | pre, c :: cs => chkChunk D cnf pre c = true ∧ OKs D cnf (pre ++ c) cs

theorem OKs_sound (ρ : Nat → Bool) (D : Nat) (cnf : List Cl) (hρ : ∀ c ∈ cnf, SatCl ρ c) :
    ∀ (cs : List (List Step)) (pre : List Step),
    AllT (SatCl ρ) D (insAll D (load D Tr.nil 1 cnf) pre) → (∀ s ∈ pre, SatCl ρ s.2.1) →
    OKs D cnf pre cs → (∀ s ∈ (pre ++ cs.flatten), SatCl ρ s.2.1) := by
  intro cs
  induction cs with
  | nil => intro pre _ hp _; simpa using hp
  | cons c cs ih =>
    intro pre hdb hp h
    simp only [OKs, chkChunk] at h
    have h1 := allRup_sound ρ D c _ hdb h.1
    have hdb' : AllT (SatCl ρ) D (insAll D (load D Tr.nil 1 cnf) (pre ++ c)) := by
      unfold insAll at hdb ⊢
      rw [List.foldl_append]
      exact insAll_sound ρ D c _ hdb h1
    have := ih (pre ++ c) hdb' (by
      intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hp s hs
      · exact h1 s hs) h.2
    simpa [List.append_assoc] using this

/-- **Chunked soundness**: all chunks check and the empty clause occurs among the steps. -/
theorem chunks_sound (D : Nat) (cnf : List Cl) (cs : List (List Step))
    (h : OKs D cnf [] cs) (hempty : cs.flatten.any (fun s => s.2.1.isEmpty) = true) :
    ∀ ρ : Nat → Bool, ¬ ∀ c ∈ cnf, SatCl ρ c := by
  intro ρ hρ
  have hdb : AllT (SatCl ρ) D (insAll D (load D Tr.nil 1 cnf) []) :=
    load_sound ρ D cnf Tr.nil 1 (nil_allT _ D) hρ
  have := OKs_sound ρ D cnf hρ cs [] hdb (by simp) h
  simp only [List.nil_append] at this
  obtain ⟨s, hs, he⟩ := List.any_eq_true.1 hempty
  obtain ⟨l, hl, _⟩ := this s hs
  cases hc : s.2.1 with
  | nil => rw [hc] at hl; simp at hl
  | cons a b => rw [hc] at he; simp at he

end Minimality.H21.SAT.K3

