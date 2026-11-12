module

public import Minimality.SilS0XD
public import Minimality.Type21SAT.Wit
public import Minimality.Type24SAT.Geo.RowSound
public import Minimality.Type24SAT.Geo.Pat
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# L3, part 16: the rule rows (family 17)

A rule row is `(e, pp, mask)` and the clause.  The clause is computed from these (and the `Tp` signature and the
encoder's cycle, which are read off the clause itself): for each facet `t` the negated state literal of the facing
`Fe e t`, then `not Tp` (mask of at least two facets) and `fail` (cycle of more than three).  The cycle of the pattern
is `patCyc pp`; its facts (injective, up/down silhouette, `AltCover` with the encoder's cycle) are checked on lists and
translated to `ZMod k`.  Soundness is `rule_leaf'` against `not IsRupert`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21
open Minimality.T24.SAT (s0x_S24)

open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- The facet vertex sets of the encoder are those of type 24 (`s0x_S24`). -/
theorem mem_S24 : ∀ (a : Fin 9) (q : Fin 7), q ∈ s0x_S24 a ↔ inF a.val q.val = true := by decide +kernel

/-! ### The real data of a shape -/

/-- Bit `t` of a number as a function on facets. -/
def bits (n : Nat) : Fin 9 → Bool := fun t => n.testBit t.val

/-- The real data (points, normals) of a shape with facets `F`; the tope variable is left false. -/
noncomputable def geo0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Geo :=
  ⟨fun i => x (Fin.ofNat 7 i), fun t => F.N (Fin.ofNat 9 t), fun _ _ _ => false⟩

/-- **The real data with the tope variable set to its meaning** `TpSem`. -/
noncomputable def geoF {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Geo :=
  { geo0 F with tpv := fun e m s => decide (TpSem F ((geo0 F).vv e) (bits m) (bits s)) }

/-- The views of `geoF` are those of `geo0`. -/
theorem geoF_vv {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (e : Nat) : (geoF F).vv e = (geo0 F).vv e := rfl

/-- The tope variable of `geoF` is `TpSem`. -/
theorem rho_tpv {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (e m s : Nat) :
    rho (geoF F) (V.tpv e m s) = decide (TpSem F ((geo0 F).vv e) (bits m) (bits s)) := rfl

theorem geoF_N {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : (geoF F).N t.val = F.N t := by
  simp only [geoF, geo0]; congr 1; ext; simp [Fin.ofNat]

theorem geoF_x {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (i : Fin 7) : (geoF F).x i.val = x i := by
  simp only [geoF, geo0]; congr 1; ext; simp [Fin.ofNat]

/-! ### Entries of normals with sign (`nEnt` of the encoder), three valued -/

/-- `nEnt a b c`: the entry of `det3 (N a) (N b) (N c)` from the sorted table, with the sign of the permutation. -/
def nEnt3 (a b c : Nat) : S3 :=
  if a = b ∨ b = c ∨ a = c then zeroS
  else if a < b then
    (if b < c then nlOf a b c else if a < c then negS (nlOf a c b) else nlOf c a b)
  else
    (if a < c then negS (nlOf b a c) else if b < c then nlOf b c a else negS (nlOf c b a))

/-- All 56 sorted triples of facets are in the normal table. -/
theorem nl_keys : ∀ a < 9, ∀ b < 9, ∀ c < 9, a < b → b < c → hasKey3 nlRoutes a b c = true := by
  decide +kernel

/-- `nEnt3` tells the truth about `det3` of three normals. -/
theorem nEnt3_sound {g : Geo} (hG : GeoOK g) {a b c : Nat} (ha : a < 9) (hb : b < 9) (hc : c < 9) :
    Sg3 (rho g) (nEnt3 a b c) (det3 (g.N a) (g.N b) (g.N c)) := by
  have sw23 : ∀ u v w : ℝ³, det3 u v w = -det3 u w v := fun u v w => by simp only [det3_expand]; ring
  have sw12 : ∀ u v w : ℝ³, det3 u v w = -det3 v u w := fun u v w => by simp only [det3_expand]; ring
  have cyc : ∀ u v w : ℝ³, det3 u v w = det3 w u v := fun u v w => by simp only [det3_expand]; ring
  have E := hG.eok
  unfold nEnt3
  by_cases hz : a = b ∨ b = c ∨ a = c
  · rw [ite_eq_left hz]
    have : det3 (g.N a) (g.N b) (g.N c) = 0 := by
      rcases hz with rfl | rfl | rfl <;> simp only [det3_expand] <;> ring
    rw [this]; exact Sg3_zeroG g
  · rw [ite_eq_right hz]
    have n1 : a ≠ b := fun h => hz (Or.inl h)
    have n2 : b ≠ c := fun h => hz (Or.inr (Or.inl h))
    have n3 : a ≠ c := fun h => hz (Or.inr (Or.inr h))
    by_cases p1 : a < b
    · rw [ite_eq_left p1]
      by_cases p2 : b < c
      · rw [ite_eq_left p2]; exact E.nl a b c (nl_keys a ha b hb c hc p1 p2)
      · rw [ite_eq_right p2]
        have p2' : c < b := by omega
        by_cases p3 : a < c
        · rw [ite_eq_left p3, sw23]; exact (E.nl a c b (nl_keys a ha c hc b hb p3 p2')).neg
        · rw [ite_eq_right p3, cyc]; exact E.nl c a b (nl_keys c hc a ha b hb (by omega) p1)
    · rw [ite_eq_right p1]
      have p1' : b < a := by omega
      by_cases p3 : a < c
      · rw [ite_eq_left p3, sw12]; exact (E.nl b a c (nl_keys b hb a ha c hc p1' p3)).neg
      · rw [ite_eq_right p3]
        by_cases p2 : b < c
        · rw [ite_eq_left p2, cyc, cyc]; exact E.nl b c a (nl_keys b hb c hc a ha p2 (by omega))
        · rw [ite_eq_right p2, show det3 (g.N a) (g.N b) (g.N c) = -det3 (g.N c) (g.N b) (g.N a) by
            simp only [det3_expand]; ring]
          exact (E.nl c b a (nl_keys c hc b hb a ha (by omega) p1')).neg

/-- The inner product with a cross product is a determinant. -/
theorem inner_cross_det3' (a b c : ℝ³) : ⟪c, cross a b⟫ = det3 a b c := by
  simp only [det3_expand, inn3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- The facing of facet `t` at view `e` (an edge difference, or a line view). -/
def Fe (e t : Nat) : S3 :=
  if e < 21 then fup3 t (EA e) (EB e) else nEnt3 (lineOf e).1 (lineOf e).2 t

/-- **The facing has the sign of `⟪N t, vv e⟫`.** -/
theorem Fe_sound {g : Geo} (hG : GeoOK g) {e t : Nat} (he : e < 43) (ht : t < 9) :
    Sg3 (rho g) (Fe e t) ⟪g.N t, g.vv e⟫ := by
  unfold Fe
  by_cases h21 : e < 21
  · rw [ite_eq_left h21, vv_lt g h21]
    exact fup3_sound hG.hF t _ _ (EAB_lt e h21).1 (EAB_lt e h21).2
  · rw [ite_eq_right h21]
    have hlm : lineOf e ∈ lines := by
      unfold lineOf
      have : e - 21 < lines.length := by simp [lines]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
      exact List.getElem_mem this
    have hb := lines_ok _ hlm
    have hv : g.vv e = cross (g.N (lineOf e).1) (g.N (lineOf e).2) := by
      simp only [Geo.vv, h21, ite_false]; rfl
    rw [hv, inner_cross_det3']
    exact nEnt3_sound hG hb.1 hb.2 ht

/-! ### The cycle of a pattern, on lists -/

/-- Entry `i` of a cycle list. -/
def cv (L : List Nat) (i : Nat) : Nat := L.getD i 0

/-- The cycle `L` as a map `ZMod k → Fin 7`. -/
def cOf {k : ℕ} (L : List Nat) : ZMod k → Fin 7 := fun i => Fin.ofNat 7 (cv L i.val)

/-- `t` is `(p1, p2, q1, q2)` up to swapping inside each pair (Boolean). -/
def mtB (t : Nat × Nat × Nat × Nat) (p1 p2 q1 q2 : Nat) : Bool :=
  ((t.1 == p1 && t.2.1 == p2) || (t.1 == p2 && t.2.1 == p1)) &&
  ((t.2.2.1 == q1 && t.2.2.2 == q2) || (t.2.2.1 == q2 && t.2.2.2 == q1))

/-- `t` is `(p1, p2, q1, q2)` up to swapping inside each pair. -/
def Mt (t : Nat × Nat × Nat × Nat) (p1 p2 q1 q2 : Nat) : Prop :=
  ((t.1 = p1 ∧ t.2.1 = p2) ∨ (t.1 = p2 ∧ t.2.1 = p1)) ∧
  ((t.2.2.1 = q1 ∧ t.2.2.2 = q2) ∨ (t.2.2.1 = q2 ∧ t.2.2.2 = q1))

theorem mtB_iff (t : Nat × Nat × Nat × Nat) (p1 p2 q1 q2 : Nat) : mtB t p1 p2 q1 q2 = true ↔ Mt t p1 p2 q1 q2 := by
  simp [mtB, Mt]

/-- Every weak alternation of the cycle (in the form `RobUni` needs) occurs in `alts cyc`. -/
def AltCover2 {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (cyc : List Nat) : Prop :=
  ∀ B : ZMod k, ∀ b < k, ∀ e < k, ∀ d < k, 0 < b → b < e → e < d →
    ∃ t ∈ alts cyc, Mt t (c B).val (c (B + e)).val (c (B + b)).val (c (B + d)).val

/-- Boolean check of `AltCover2` on lists. -/
def altChk (L cyc : List Nat) : Bool :=
  let k := L.length
  (List.range k).all fun B => (List.range k).all fun b => (List.range k).all fun e =>
    (List.range k).all fun d =>
      !(decide (0 < b ∧ b < e ∧ e < d)) ||
      (alts cyc).any (fun t => mtB t (cv L B) (cv L ((B + e) % k)) (cv L ((B + b) % k)) (cv L ((B + d) % k)))

/-- Boolean check of injectivity and the up/down silhouette property of the cycle `L` for the pattern `pp`. -/
def cycChk (pp : Nat) (L : List Nat) : Bool :=
  let k := L.length
  decide (3 ≤ k) && L.all (fun v => decide (v < 7)) && decide L.Nodup &&
  (List.range k).all fun i =>
    (List.range 9).any fun a => (List.range 9).any fun b =>
      pp.testBit a && !pp.testBit b && inF a (cv L i) && inF b (cv L i) &&
      inF a (cv L ((i + 1) % k)) && inF b (cv L ((i + 1) % k)) &&
      (List.range 7).all fun q => q == cv L i || q == cv L ((i + 1) % k) || !inF a q || !inF b q

/-- The value of the cycle map at `i + n`. -/
theorem val_add_nat {k : ℕ} [NeZero k] (B : ZMod k) (n : ℕ) : (B + (n : ZMod k)).val = (B.val + n) % k := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

/-- Values of the cycle map when all entries are below 7. -/
theorem cOf_val {k : ℕ} [NeZero k] {L : List Nat} (h7 : ∀ v ∈ L, v < 7) (i : ZMod k) :
    (cOf L i).val = cv L i.val := by
  have : cv L i.val < 7 := by
    unfold cv
    by_cases h : i.val < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact h7 _ (List.getElem_mem h)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
  simp [cOf, Fin.ofNat, Nat.mod_eq_of_lt this]

/-- **Cycle facts from the Boolean check**: injective, and an up/down silhouette. -/
theorem cycFacts {k : ℕ} [NeZero k] {pp : Nat} {L : List Nat} (hk : L.length = k) (h : cycChk pp L = true) :
    3 ≤ k ∧ Function.Injective (cOf (k := k) L) ∧ S0xCycOK s0x_S24 (cOf (k := k) L) (bits pp) := by
  unfold cycChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h3, h7⟩, hnd⟩, hall⟩ := h
  rw [hk] at h3 hall
  have h7' : ∀ v ∈ L, v < 7 := fun v hv => by simpa using h7 v hv
  have hk1 : 1 < k := by omega
  haveI : Fact (1 < k) := ⟨hk1⟩
  refine ⟨h3, ?_, ?_⟩
  · intro i j hij
    have e1 := cOf_val (k := k) h7' i
    have e2 := cOf_val (k := k) h7' j
    have : cv L i.val = cv L j.val := by rw [← e1, ← e2, hij]
    have hi : i.val < L.length := by rw [hk]; exact ZMod.val_lt i
    have hj : j.val < L.length := by rw [hk]; exact ZMod.val_lt j
    unfold cv at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj] at this
    simp only [Option.getD_some] at this
    have := (List.Nodup.getElem_inj_iff hnd).mp this
    exact ZMod.val_injective k this
  · intro i
    have hi : i.val < k := ZMod.val_lt i
    have hs := hall i.val (List.mem_range.mpr hi)
    obtain ⟨a, ha, hs⟩ := List.any_eq_true.mp hs
    obtain ⟨b, hb, hs⟩ := List.any_eq_true.mp hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨pa, pb⟩, a1⟩, b1⟩, a2⟩, b2⟩, hq⟩ := hs
    have ha8 : a < 9 := List.mem_range.mp ha
    have hb8 : b < 9 := List.mem_range.mp hb
    have hv1 : (i + 1).val = (i.val + 1) % k := by
      rw [ZMod.val_add, ZMod.val_one]
    have c0 : (cOf (k := k) L i).val = cv L i.val := cOf_val h7' i
    have c1 : (cOf (k := k) L (i + 1)).val = cv L ((i.val + 1) % k) := by
      rw [cOf_val h7' (i + 1), hv1]
    refine ⟨⟨a, ha8⟩, ⟨b, hb8⟩, pa, by simpa [bits] using pb, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_S24]; simpa [c0] using a1
    · rw [mem_S24]; simpa [c0] using b1
    · rw [mem_S24]; simpa [c1] using a2
    · rw [mem_S24]; simpa [c1] using b2
    · intro q hq0 hq1
      have := hq q.val (List.mem_range.mpr q.isLt)
      have hq0' : q.val ≠ cv L i.val := fun e => hq0 (Fin.ext (by rw [c0]; exact e))
      have hq1' : q.val ≠ cv L ((i.val + 1) % k) := fun e => hq1 (Fin.ext (by rw [c1]; exact e))
      rcases this with ((h | h) | h) | h
      · exact absurd h hq0'
      · exact absurd h hq1'
      · left; rw [mem_S24]; simpa using h
      · right; rw [mem_S24]; simpa using h

end Minimality.H24.SAT
