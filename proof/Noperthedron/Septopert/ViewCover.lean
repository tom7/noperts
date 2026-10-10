module

public import Noperthedron.Pipeline.WedgeCover
public import Noperthedron.Septopert.ViewReduce
public import Noperthedron.Septopert.Reduce

@[expose] public section

/-!
# Covering the C3v view domain by code triangles (two projective roots)

The view domain D′ = {u₀ ≥ u₁ ≥ 0, u₁ ≥ u₂} (`InC3vViewDomain`) lies in the
projective roots 0 (+++) and 1 (++−) (`AtlasProjectiveView.rootSign`):

- T1 = (1/3,1/3,1/3), (1/2,1/2,0), (1,0,0) on the plane u₀ + u₁ + u₂ = 1
  (the views with u₂ ≥ 0, root 0);
- T2 = (1,0,0), (1/2,1/2,0), (0,0,−1) on the plane u₀ + u₁ − u₂ = 1
  (the views with u₂ ≤ 0, root 1)

(codebdd.json's `view_domains`). `viewDomain_mem_base`: every atlas pose whose
view lies in D′ has its normalized view (in the matching root, at view scale
≥ 1) in T1 or T2.

The code triangles (`ViewCoverData.codeTriangles`, each with its root) cover
T1 and T2: per root, a decision tree over half-spaces `u ⬝ a ≥ 0` (as
`WedgeCover`, with the root's plane `u ⬝ s = 1`, s = `rootSign root`, in
place of `u ⬝ (1,1,1) = 1`); a leaf names a code triangle of the same root.
-/

namespace Noperthedron.Septopert.ViewCover

open Noperthedron.Atlas.ProjectiveView
open Noperthedron.Pipeline
open Noperthedron.Pipeline.WedgeCover
  (V Tri dotQ crossQ detQ vecEq orient edgeFn combo dotR vecEq_iff dotR_add dotR_smul dotR_neg
    dotR_zero dotR_combo_nonneg)

/-- The plane vector of a root: views of the root's triangle satisfy u ⬝ s = 1. -/
def planeVec (root : Fin 8) : V := AtlasProjectiveView.rootSign root

/-- A cover tree (as `WedgeCover.Node`; leaves index root-tagged triangles). -/
inductive Node where
  | split (n : V) (pos neg : Node)
  | empty (lam : List ℚ) (kappa : ℚ)
  | leaf (tri : ℕ) (certs : List (List ℚ × ℚ))

/-- Decidable check of a cover tree for root `root`, given the path
constraints `cs`. -/
def Node.check (tris : Array (Fin 8 × Tri)) (root : Fin 8) : List V → Node → Bool
  | cs, .split n pos neg => pos.check tris root (cs ++ [n]) && neg.check tris root (cs ++ [-n])
  | cs, .empty lam kappa =>
      lam.length == cs.length && lam.all (fun x => decide (0 ≤ x)) &&
        decide (0 < kappa) && vecEq (combo cs lam + kappa • planeVec root) 0
  | cs, .leaf t certs =>
      match tris[t]? with
      | none => false
      | some (r, tri) =>
          decide (r = root) &&
          decide (detQ (tri 0) (tri 1) (tri 2) ≠ 0) &&
          decide (dotQ (tri 0) (planeVec root) = 1) && decide (dotQ (tri 1) (planeVec root) = 1) &&
          decide (dotQ (tri 2) (planeVec root) = 1) &&
          (List.finRange 3).all fun i =>
            match certs[i.val]? with
            | none => false
            | some (mu, k) =>
                mu.length == cs.length && mu.all (fun x => decide (0 ≤ x)) &&
                  decide (0 ≤ k) && vecEq (edgeFn tri i) (combo cs mu + k • planeVec root)

/-! ## Soundness -/

theorem dotQ_cast (a s : V) (h : dotQ a s = 1) :
    (a 0 : ℝ) * (s 0 : ℝ) + (a 1 : ℝ) * (s 1 : ℝ) + (a 2 : ℝ) * (s 2 : ℝ) = 1 := by
  have := congrArg (fun q : ℚ => (q : ℝ)) h
  simpa [dotQ] using this

/-- Cramer's rule on the plane u ⬝ s = 1. -/
theorem inTriangle_of_edges (s : V) (tri : Tri) (u : Fin 3 → ℝ)
    (hdet : detQ (tri 0) (tri 1) (tri 2) ≠ 0)
    (hs0 : dotQ (tri 0) s = 1) (hs1 : dotQ (tri 1) s = 1) (hs2 : dotQ (tri 2) s = 1)
    (hsum : dotR u s = 1)
    (hedge : ∀ i, 0 ≤ dotR u (edgeFn tri i)) :
    InTriangle (toReal tri) u := by
  set D : ℚ := detQ (tri 0) (tri 1) (tri 2) with hD
  set o : ℚ := orient tri with ho
  have hoD : 0 < o * D := by
    simp only [ho, orient, hD]
    split_ifs with h
    · simpa using h
    · have : D < 0 := lt_of_le_of_ne (not_lt.mp h) hdet
      simp only [hD] at this
      nlinarith
  have hoDR : (0 : ℝ) < (o : ℝ) * (D : ℝ) := by exact_mod_cast hoD
  let r : Fin 3 → ℝ := fun i => dotR u (crossQ (tri (i + 1)) (tri (i + 2)))
  have hedge' : ∀ i, 0 ≤ (o : ℝ) * r i := by
    intro i
    have := hedge i
    simpa [edgeFn, dotR_smul, r] using this
  let weight : Fin 3 → ℝ := fun i => ((o : ℝ) * r i) / ((o : ℝ) * (D : ℝ))
  have hcramer : ∀ c, (D : ℝ) * u c = ∑ i, r i * (tri i c : ℝ) := by
    intro c
    simp only [r, dotR, crossQ, hD, detQ, dotQ, Fin.sum_univ_three]
    fin_cases c <;>
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.reduceFinMk] <;> push_cast <;> ring
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (hedge' i) hoDR.le
  · have hs0' := dotQ_cast _ _ hs0
    have hs1' := dotQ_cast _ _ hs1
    have hs2' := dotQ_cast _ _ hs2
    have hrsum : r 0 + r 1 + r 2 = (D : ℝ) := by
      have h0 := hcramer 0
      have h1 := hcramer 1
      have h2 := hcramer 2
      simp only [Fin.sum_univ_three] at h0 h1 h2
      have hsum' : u 0 * (s 0 : ℝ) + u 1 * (s 1 : ℝ) + u 2 * (s 2 : ℝ) = 1 := by
        simpa [dotR] using hsum
      have : (D : ℝ) * (u 0 * (s 0 : ℝ) + u 1 * (s 1 : ℝ) + u 2 * (s 2 : ℝ)) =
          r 0 * ((tri 0 0 : ℝ) * s 0 + tri 0 1 * s 1 + tri 0 2 * s 2) +
            r 1 * ((tri 1 0 : ℝ) * s 0 + tri 1 1 * s 1 + tri 1 2 * s 2) +
            r 2 * ((tri 2 0 : ℝ) * s 0 + tri 2 1 * s 1 + tri 2 2 * s 2) := by
        linear_combination (s 0 : ℝ) * h0 + (s 1 : ℝ) * h1 + (s 2 : ℝ) * h2
      rw [hsum', hs0', hs1', hs2'] at this
      linarith
    simp only [Fin.sum_univ_three, weight]
    rw [← add_div, ← add_div, ← mul_add, ← mul_add, hrsum]
    exact div_self hoDR.ne'
  · funext c
    simp only [affinePoint, toReal, weight]
    have := hcramer c
    rw [Fin.sum_univ_three] at this ⊢
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hdet
    have hoR : (o : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hoDR
      exact lt_irrefl _ hoDR
    field_simp
    nlinarith [this]

/-- Soundness of the cover tree check. -/
theorem Node.sound (tris : Array (Fin 8 × Tri)) (root : Fin 8) (u : Fin 3 → ℝ)
    (hsum : dotR u (planeVec root) = 1) :
    ∀ (node : Node) (cs : List V), node.check tris root cs = true →
      (∀ a ∈ cs, 0 ≤ dotR u a) →
      ∃ t : ℕ, ∃ tri, tris[t]? = some (root, tri) ∧ InTriangle (toReal tri) u
  | .split n pos neg, cs, hcheck, hcs => by
      simp only [Node.check, Bool.and_eq_true] at hcheck
      rcases le_total 0 (dotR u n) with h | h
      · exact Node.sound tris root u hsum pos (cs ++ [n]) hcheck.1 (by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hcs a ha
          · simp at ha; subst ha; exact h)
      · exact Node.sound tris root u hsum neg (cs ++ [-n]) hcheck.2 (by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hcs a ha
          · simp at ha; subst ha; rw [dotR_neg]; linarith)
  | .empty lam kappa, cs, hcheck, hcs => by
      simp only [Node.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        decide_eq_true_eq] at hcheck
      obtain ⟨⟨⟨_, hlam⟩, hk⟩, hzero⟩ := hcheck
      rw [vecEq_iff] at hzero
      have hnn := dotR_combo_nonneg u cs lam hcs hlam
      have hval : dotR u (combo cs lam + kappa • planeVec root) = 0 := by
        rw [hzero, dotR_zero]
      rw [dotR_add, dotR_smul, hsum] at hval
      have hkR : (0 : ℝ) < kappa := by exact_mod_cast hk
      linarith
  | .leaf t certs, cs, hcheck, hcs => by
      simp only [Node.check] at hcheck
      cases htri : tris[t]? with
      | none => simp [htri] at hcheck
      | some rt =>
        obtain ⟨r, tri⟩ := rt
        simp only [htri, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_finRange, true_implies] at hcheck
        obtain ⟨⟨⟨⟨⟨hr, hdet⟩, hs0⟩, hs1⟩, hs2⟩, hcerts⟩ := hcheck
        subst hr
        refine ⟨t, tri, htri, inTriangle_of_edges (planeVec r) tri u hdet hs0 hs1 hs2 hsum ?_⟩
        intro i
        have hi := hcerts i
        cases hc : certs[i.val]? with
        | none => simp [hc] at hi
        | some mk =>
          obtain ⟨mu, k⟩ := mk
          simp only [hc, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
            decide_eq_true_eq] at hi
          obtain ⟨⟨⟨_, hmu⟩, hk⟩, heq⟩ := hi
          rw [vecEq_iff] at heq
          rw [heq, dotR_add, dotR_smul, hsum]
          have := dotR_combo_nonneg u cs mu hcs hmu
          have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith

/-- Checking a split from its two children's checks. -/
theorem Node.check_split {tris : Array (Fin 8 × Tri)} {root : Fin 8} {cs : List V} {n : V}
    {pos neg : Node} (hp : pos.check tris root (cs ++ [n]) = true)
    (hn : neg.check tris root (cs ++ [-n]) = true) :
    (Node.split n pos neg).check tris root cs = true := by
  simp only [Node.check, hp, hn, Bool.and_self]

/-! ## Base triangles -/

/-- A base triangle: nondegenerate, corners on the root's plane. -/
def baseTriangleValid (root : Fin 8) (base : Tri) : Bool :=
  decide (detQ (base 0) (base 1) (base 2) ≠ 0) && decide (dotQ (base 0) (planeVec root) = 1) &&
    decide (dotQ (base 1) (planeVec root) = 1) && decide (dotQ (base 2) (planeVec root) = 1)

def baseConstraints (base : Tri) : List V := [edgeFn base 0, edgeFn base 1, edgeFn base 2]

theorem base_constraints_hold (root : Fin 8) (base : Tri)
    (hbase : baseTriangleValid root base = true)
    (u : Fin 3 → ℝ) (hu : InTriangle (toReal base) u) :
    dotR u (planeVec root) = 1 ∧ ∀ a ∈ baseConstraints base, 0 ≤ dotR u a := by
  simp only [baseTriangleValid, Bool.and_eq_true, decide_eq_true_eq] at hbase
  obtain ⟨⟨⟨hdet, hs0⟩, hs1⟩, hs2⟩ := hbase
  obtain ⟨w, hw, hws, rfl⟩ := hu
  rw [Fin.sum_univ_three] at hws
  have hs0R := dotQ_cast _ _ hs0
  have hs1R := dotQ_cast _ _ hs1
  have hs2R := dotQ_cast _ _ hs2
  constructor
  · simp only [dotR, affinePoint, toReal, Fin.sum_univ_three]
    linear_combination w 0 * hs0R + w 1 * hs1R + w 2 * hs2R + hws
  · have hpos : (0 : ℝ) < (orient base : ℝ) * (detQ (base 0) (base 1) (base 2) : ℝ) := by
      have : (0 : ℚ) < orient base * detQ (base 0) (base 1) (base 2) := by
        unfold orient
        split_ifs with h
        · simpa using h
        · have : detQ (base 0) (base 1) (base 2) < 0 :=
            lt_of_le_of_ne (not_lt.mp h) hdet
          linarith
      exact_mod_cast this
    have hkey : ∀ i : Fin 3, dotR (affinePoint (toReal base) w) (edgeFn base i) =
        (orient base : ℝ) * (detQ (base 0) (base 1) (base 2) : ℝ) * w i := by
      intro i
      fin_cases i <;>
        simp [dotR, edgeFn, crossQ, detQ, dotQ, affinePoint, toReal, Fin.sum_univ_three] <;>
        ring
    intro a ha
    simp only [baseConstraints, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · rw [hkey 0]; exact mul_nonneg hpos.le (hw 0)
    · rw [hkey 1]; exact mul_nonneg hpos.le (hw 1)
    · rw [hkey 2]; exact mul_nonneg hpos.le (hw 2)

/-- Main cover theorem for one root. -/
theorem base_covered (root : Fin 8) (base : Tri) (hbase : baseTriangleValid root base = true)
    (tris : Array (Fin 8 × Tri)) (tree : Node)
    (hcheck : tree.check tris root (baseConstraints base) = true)
    (u : Fin 3 → ℝ) (hu : InTriangle (toReal base) u) :
    ∃ t : ℕ, ∃ tri, tris[t]? = some (root, tri) ∧ InTriangle (toReal tri) u := by
  obtain ⟨hsum, hcs⟩ := base_constraints_hold root base hbase u hu
  exact Node.sound tris root u hsum tree (baseConstraints base) hcheck hcs

/-! ## The view domain lies over T1 ∪ T2 -/

/-- T1 (root 0, views with u₂ ≥ 0). -/
def baseT1 : Tri := ![![1 / 3, 1 / 3, 1 / 3], ![1 / 2, 1 / 2, 0], ![1, 0, 0]]

/-- T2 (root 1, views with u₂ ≤ 0). -/
def baseT2 : Tri := ![![1, 0, 0], ![1 / 2, 1 / 2, 0], ![0, 0, -1]]

theorem baseT1_valid : baseTriangleValid 0 baseT1 = true := by decide +kernel

theorem baseT2_valid : baseTriangleValid 1 baseT2 = true := by decide +kernel

theorem viewVector_eq (p : AtlasPose ℝ) (k : Fin 3) :
    AtlasEdgeCertificate.viewVector p k = rotRM_mat p.θ p.φ 0 2 k := by
  obtain ⟨e0, e1, e2⟩ := rotRM_mat_row2_zero p.θ p.φ
  fin_cases k <;> simp [AtlasEdgeCertificate.viewVector, e0, e1, e2]

/-- Every atlas pose with view in D′ has its normalized view in T1 (root 0) or
T2 (root 1), at view scale ≥ 1. -/
theorem viewDomain_mem_base (p : AtlasPose ℝ)
    (hdom : InC3vViewDomain (fun k => rotRM_mat p.θ p.φ 0 2 k)) :
    (1 ≤ AtlasProjectiveView.viewScale 0 p ∧
      InTriangle (toReal baseT1) (AtlasProjectiveView.normalizedView 0 p)) ∨
    (1 ≤ AtlasProjectiveView.viewScale 1 p ∧
      InTriangle (toReal baseT2) (AtlasProjectiveView.normalizedView 1 p)) := by
  set v := AtlasEdgeCertificate.viewVector p
  have hd : v 1 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 2 ≤ v 1 := by
    obtain ⟨h0, h1, h2⟩ := hdom
    simp only [v, viewVector_eq]
    exact ⟨h0, h1, h2⟩
  obtain ⟨h01, h1, h21⟩ := hd
  rcases le_total 0 (v 2) with h2 | h2
  · left
    have hsign : ∀ c, 0 ≤ (AtlasProjectiveView.rootSign 0 c : ℝ) * v c := by
      intro c
      fin_cases c <;> simp [AtlasProjectiveView.rootSign] <;> linarith
    have hscale := AtlasProjectiveView.one_le_viewScale_of_sign hsign
    have hs0 : 0 < AtlasProjectiveView.viewScale 0 p := by linarith
    have hscaleEq : AtlasProjectiveView.viewScale 0 p = v 0 + v 1 + v 2 := by
      simp [AtlasProjectiveView.viewScale, AtlasProjectiveView.rootSign, Fin.sum_univ_three, v]
    refine ⟨hscale, ?_⟩
    set u := AtlasProjectiveView.normalizedView 0 p
    have hu : ∀ c, u c = v c / AtlasProjectiveView.viewScale 0 p := fun c => rfl
    have hu01 : u 1 ≤ u 0 := by rw [hu, hu]; exact div_le_div_of_nonneg_right h01 hs0.le
    have hu12 : u 2 ≤ u 1 := by rw [hu, hu]; exact div_le_div_of_nonneg_right h21 hs0.le
    have hu2 : 0 ≤ u 2 := by rw [hu]; exact div_nonneg h2 hs0.le
    have husum : u 0 + u 1 + u 2 = 1 := by
      rw [hu, hu, hu, ← add_div, ← add_div, ← hscaleEq, div_self hs0.ne']
    refine ⟨![3 * u 2, 2 * (u 1 - u 2), u 0 - u 1], ?_, ?_, ?_⟩
    · intro c
      fin_cases c <;> simp <;> linarith
    · simp [Fin.sum_univ_three]
      linarith
    · funext c
      fin_cases c <;> simp [affinePoint, toReal, baseT1, Fin.sum_univ_three] <;> ring
  · right
    have hsign : ∀ c, 0 ≤ (AtlasProjectiveView.rootSign 1 c : ℝ) * v c := by
      intro c
      fin_cases c <;> simp [AtlasProjectiveView.rootSign] <;> linarith
    have hscale := AtlasProjectiveView.one_le_viewScale_of_sign hsign
    have hs0 : 0 < AtlasProjectiveView.viewScale 1 p := by linarith
    have hscaleEq : AtlasProjectiveView.viewScale 1 p = v 0 + v 1 - v 2 := by
      simp [AtlasProjectiveView.viewScale, AtlasProjectiveView.rootSign, Fin.sum_univ_three, v]
      ring
    refine ⟨hscale, ?_⟩
    set u := AtlasProjectiveView.normalizedView 1 p
    have hu : ∀ c, u c = v c / AtlasProjectiveView.viewScale 1 p := fun c => rfl
    have hu01 : u 1 ≤ u 0 := by rw [hu, hu]; exact div_le_div_of_nonneg_right h01 hs0.le
    have hu1 : 0 ≤ u 1 := by rw [hu]; exact div_nonneg h1 hs0.le
    have hu2 : u 2 ≤ 0 := by rw [hu]; exact div_nonpos_of_nonpos_of_nonneg h2 hs0.le
    have husum : u 0 + u 1 - u 2 = 1 := by
      rw [hu, hu, hu, ← add_div, ← sub_div, ← hscaleEq, div_self hs0.ne']
    refine ⟨![u 0 - u 1, 2 * u 1, -u 2], ?_, ?_, ?_⟩
    · intro c
      fin_cases c <;> simp <;> linarith
    · simp [Fin.sum_univ_three]
      linarith
    · funext c
      fin_cases c <;> simp [affinePoint, toReal, baseT2, Fin.sum_univ_three] <;> ring

/-- The cover of D′ by root-tagged triangles, given the two trees' checks. -/
theorem viewDomain_covered (tris : Array (Fin 8 × Tri)) (tree0 tree1 : Node)
    (h0 : tree0.check tris 0 (baseConstraints baseT1) = true)
    (h1 : tree1.check tris 1 (baseConstraints baseT2) = true)
    (p : AtlasPose ℝ) (hdom : InC3vViewDomain (fun k => rotRM_mat p.θ p.φ 0 2 k)) :
    ∃ t : ℕ, ∃ root : Fin 8, ∃ tri, tris[t]? = some (root, tri) ∧
      1 ≤ AtlasProjectiveView.viewScale root p ∧
      InTriangle (toReal tri) (AtlasProjectiveView.normalizedView root p) := by
  rcases viewDomain_mem_base p hdom with ⟨hs, hm⟩ | ⟨hs, hm⟩
  · obtain ⟨t, tri, ht, hin⟩ := base_covered 0 baseT1 baseT1_valid tris tree0 h0 _ hm
    exact ⟨t, 0, tri, ht, hs, hin⟩
  · obtain ⟨t, tri, ht, hin⟩ := base_covered 1 baseT2 baseT2_valid tris tree1 h1 _ hm
    exact ⟨t, 1, tri, ht, hs, hin⟩

end Noperthedron.Septopert.ViewCover
