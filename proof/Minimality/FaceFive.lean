module

public import Minimality.FaceChain
public import Minimality.L8T3
public import Minimality.SixClass
public import Nopert

@[expose] public section

/-!
# Theorem A: seven points with a face of five or six of them

Notes: `FEWER-FACES-PROOFS.md`, §2B (the constructive version of Theorem A).

* `isOpen_isCyclicUnimodal`: cyclic unimodality is an open condition.
* `det3_ey`, `det3_ez`: triple products with the coordinate views.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The unit vector along `y`. -/
noncomputable def ey : ℝ³ := EuclideanSpace.single 1 1

theorem ey_ne_zero : ey ≠ 0 := by
  intro h; have := congrArg (fun v : ℝ³ => v 1) h; simp [ey] at this

theorem inner_ey (x : ℝ³) : ⟪x, ey⟫ = x 1 := by
  simp [ey, PiLp.inner_apply]

theorem det3_ey (a b : ℝ³) : det3 a b ey = a 2 * b 0 - a 0 * b 2 := by
  simp [det3, inner_ey, cross]

theorem det3_ez (a b : ℝ³) : det3 a b ez = a 0 * b 1 - a 1 * b 0 := by
  simp [det3, inner_ez, cross]

/-- **Cyclic unimodality is open**: the strict comparisons that decide it
persist under small perturbations. -/
theorem isOpen_isCyclicUnimodal {k : ℕ} [NeZero k] :
    IsOpen {z : ZMod k → ℝ | IsCyclicUnimodal z} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro z0 hz0
  refine ⟨⋂ i, ⋂ j, {z : ZMod k → ℝ | z0 i < z0 j → z i < z j}, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hz
    have hord : ∀ i j, z0 i < z0 j ↔ z i < z j := by
      intro i j
      refine ⟨hz i j, fun h => ?_⟩
      rcases lt_trichotomy (z0 i) (z0 j) with h' | h' | h'
      · exact h'
      · exact absurd (hz0.1 h') (by rintro rfl; exact lt_irrefl _ h)
      · exact absurd (hz j i h') (not_lt.mpr h.le)
    refine ⟨fun i j hij => ?_, ?_⟩
    · by_contra hne
      rcases lt_or_gt_of_ne (hz0.1.ne hne) with h | h
      · exact lt_irrefl _ (hij ▸ (hord i j).mp h)
      · exact lt_irrefl _ (hij ▸ (hord j i).mp h)
    · rw [← hz0.2]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, hord]
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases h : z0 i < z0 j
    · simp only [h, true_implies]
      exact isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp [h]
  · simp only [Set.mem_iInter, Set.mem_ofPred_eq]; exact fun _ _ h => h

theorem isCyclicUnimodal_smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {c : ℝ} (hc : 0 < c)
    (hz : IsCyclicUnimodal z) : IsCyclicUnimodal fun i => c * z i := by
  refine ⟨fun i j h => hz.1 (by simpa [hc.ne'] using h), ?_⟩
  rw [← hz.2]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, mul_lt_mul_iff_right₀ hc]

theorem liftPt_proj {h : ℝ} {y : ℝ³} (hy : y 2 = h) : liftPt (proj_xy y) h = y := by
  ext i; fin_cases i <;> simp [liftPt, proj_xy, hy]

theorem fin_val_add_one_of_lt {n : ℕ} (j : Fin (n + 1)) (hj : j.val < n) :
    (j + 1).val = j.val + 1 := by
  rw [Fin.val_add_one]
  split_ifs with h
  · exact absurd (h ▸ hj) (by simp)
  · rfl

/-- **The edge-on lemma** (standard frame; FEWER-FACES-PROOFS.md §2B).  The face
`Q = V ∩ {z = h}` is in strictly convex position with distinct `x` and distinct
`y`, `A`, `B` are its `x`-extremes, `V` lies in `z ≤ h`, and every point below
the face other than `p` projects (along `y`) strictly inside the triangle
`A B p`.  If `p` is deeper than `A` or `B` (larger `y`), then `V` is Rupert: the
lower chain of `Q` followed by `p` is a unimodal silhouette at the views
`ey + ε ez` (Cor. 8.0′, eventual form). -/
theorem isRupert_edgeOn (V : Finset ℝ³) (h : ℝ) (A B p : ℝ³) (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hxinj : Set.InjOn (fun y : ℝ³ => y 0) (V.filter fun y => y 2 = h))
    (hyinj : Set.InjOn (fun y : ℝ³ => y 1) (V.filter fun y => y 2 = h))
    (hA : A ∈ V) (hAh : A 2 = h) (hB : B ∈ V) (hBh : B 2 = h)
    (hAmin : ∀ y ∈ V, y 2 = h → A 0 ≤ y 0) (hBmax : ∀ y ∈ V, y 2 = h → y 0 ≤ B 0)
    (hAB : A 0 < B 0) (hp : p ∈ V) (hph : p 2 < h)
    (hhid : ∀ y ∈ V, y 2 < h → y ≠ p →
      0 < det3 (p - B) (y - B) ey ∧ 0 < det3 (A - p) (y - p) ey)
    (hpAB : A 1 < p 1 ∨ B 1 < p 1) : IsRupert V := by
  classical
  set Q := V.filter fun y => y 2 = h with hQ
  set S := Q.image proj_xy with hS
  have hQV : ∀ y ∈ Q, y ∈ V ∧ y 2 = h := fun y hy => mem_filter.mp hy
  have hSinj : Set.InjOn (fun s : ℝ² => s 0) S := by
    intro s hs s' hs' he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hs'
    have : y = y' := hxinj hy hy' (by simpa [proj_xy] using he)
    rw [this]
  have hAQ : A ∈ Q := mem_filter.mpr ⟨hA, hAh⟩
  have hBQ : B ∈ Q := mem_filter.mpr ⟨hB, hBh⟩
  have hSmin : ∀ s ∈ S, (proj_xy A) 0 ≤ s 0 := by
    intro s hs; obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
    simpa [proj_xy] using hAmin y (hQV y hy).1 (hQV y hy).2
  have hSmax : ∀ s ∈ S, s 0 ≤ (proj_xy B) 0 := by
    intro s hs; obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
    simpa [proj_xy] using hBmax y (hQV y hy).1 (hQV y hy).2
  obtain ⟨n, c, h2, hc0, hcn, hcS, hcL, hcmono, hcons⟩ :=
    exists_lowerChain hSinj (mem_image_of_mem _ hAQ) (mem_image_of_mem _ hBQ) hSmin hSmax
      (by simpa [proj_xy] using hAB)
  -- the chain in space
  set c3 : Fin n → ℝ³ := fun i => liftPt (c i) h with hc3
  have hc3V : ∀ i, c3 i ∈ V ∧ c3 i 2 = h := by
    intro i
    obtain ⟨y, hy, hyc⟩ := mem_image.mp (hcS i)
    have : c3 i = y := by rw [hc3]; simp only; rw [← hyc]; exact liftPt_proj (hQV y hy).2
    rw [this]; exact hQV y hy
  have hc3x : ∀ i, c3 i 0 = c i 0 := fun i => by simp [hc3, liftPt]
  have hc3y : ∀ i, c3 i 1 = c i 1 := fun i => by simp [hc3, liftPt]
  have hc30 : c3 ⟨0, by omega⟩ = A := by
    simp only [hc3, hc0]; exact liftPt_proj hAh
  have hc3n : c3 ⟨n - 1, by omega⟩ = B := by
    simp only [hc3, hcn]; exact liftPt_proj hBh
  -- the cycle: the chain, then `p`
  set x : Fin (n + 1) → ℝ³ := fun j => if hj : j.val < n then c3 ⟨j.val, hj⟩ else p with hx
  have hxc : ∀ j : Fin (n + 1), ∀ hj : j.val < n, x j = c3 ⟨j.val, hj⟩ := fun j hj => by
    simp [hx, hj]
  have hxp : x (Fin.last n) = p := by simp [hx]
  have hxV : ∀ j, x j ∈ V := fun j => by
    by_cases hj : j.val < n
    · rw [hxc j hj]; exact (hc3V _).1
    · simp only [hx, hj, dite_false]; exact hp
  have hc3inj : ∀ a b : Fin n, c3 a = c3 b → a = b := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hcmono a b hlt; rw [← hc3x, ← hc3x, hab] at this; exact lt_irrefl _ this
    · have := hcmono b a hlt; rw [← hc3x, ← hc3x, hab] at this; exact lt_irrefl _ this
  have hinjx : Function.Injective x := by
    intro i j hij
    by_cases hi : i.val < n <;> by_cases hj : j.val < n
    · rw [hxc i hi, hxc j hj] at hij
      exact Fin.ext (by simpa using congrArg Fin.val (hc3inj _ _ hij))
    · have hjl : j = Fin.last n := Fin.ext (by have := j.isLt; simp; omega)
      rw [hxc i hi, hjl, hxp] at hij
      have := (hc3V ⟨i.val, hi⟩).2; rw [hij] at this; linarith
    · have hil : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
      rw [hxc j hj, hil, hxp] at hij
      have := (hc3V ⟨j.val, hj⟩).2; rw [← hij] at this; linarith
    · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  -- points of the face: distinct from a chain point means distinct projections
  have hprojne : ∀ y ∈ V, y 2 = h → ∀ a : Fin n, y ≠ c3 a → proj_xy y ≠ c a := by
    intro y _ hyh a hya he
    apply hya; rw [hc3]; simp only; rw [← he]; exact (liftPt_proj hyh).symm
  have hySx : ∀ y ∈ V, y 2 = h → proj_xy y ∈ S := fun y hy hyh =>
    mem_image_of_mem _ (mem_filter.mpr ⟨hy, hyh⟩)
  have hfaceA : ∀ y ∈ V, y 2 = h → y ≠ A → A 0 < y 0 := by
    intro y hy hyh hyA
    refine lt_of_le_of_ne (hAmin y hy hyh) fun he => hyA ?_
    exact (hxinj (mem_filter.mpr ⟨hy, hyh⟩) hAQ he.symm)
  have hfaceB : ∀ y ∈ V, y 2 = h → y ≠ B → y 0 < B 0 := by
    intro y hy hyh hyB
    refine lt_of_le_of_ne (hBmax y hy hyh) fun he => hyB ?_
    exact (hxinj (mem_filter.mpr ⟨hy, hyh⟩) hBQ he)
  have key : ∀ i : Fin (n + 1), ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ey ez := by
    intro i y hy hyi hyi1
    have hyh := hV y hy
    by_cases hi1 : i.val + 1 < n
    · -- a chain edge
      have hi : i.val < n := by omega
      have hval : (i + 1).val = i.val + 1 := fin_val_add_one_of_lt i hi
      have hi1' : (i + 1).val < n := by omega
      rw [hxc (i + 1) hi1'] at hyi1
      rw [hxc i hi] at hyi
      rw [hxc i hi, hxc (i + 1) hi1']
      set a : Fin n := ⟨i.val, hi⟩
      set a' : Fin n := ⟨(i + 1).val, hi1'⟩
      have ha'eq : a' = ⟨i.val + 1, hi1⟩ := Fin.ext hval
      have hlt : c a 0 < c a' 0 := hcmono a a' (Fin.lt_def.mpr (by simp [a, a', hval]))
      have hza := (hc3V a).2
      have hza' := (hc3V a').2
      rcases eq_or_lt_of_le hyh with hyh | hyh
      · right
        refine ⟨?_, ?_⟩
        · rw [det3_ey]; simp only [PiLp.sub_apply, hza, hza', hyh]; ring
        · rw [det3_ez]
          have hpos := cross2_pos_of_consecutive hconv hSinj (mem_image_of_mem _ hAQ)
            (mem_image_of_mem _ hBQ) hSmin hSmax (by simpa [proj_xy] using hAB) (hcS a) (hcS a')
            hlt (hcL a) (hcL a') (by rw [ha'eq]; exact hcons a hi1) (hySx y hy hyh)
            (hprojne y hy hyh a hyi) (hprojne y hy hyh a' hyi1)
          simp only [cross2, PiLp.sub_apply] at hpos
          simp only [PiLp.sub_apply, ← hc3x, ← hc3y] at hpos ⊢
          simpa [proj_xy] using hpos
      · left
        rw [det3_ey]
        simp only [PiLp.sub_apply, hza, hza']
        have : 0 < c3 a' 0 - c3 a 0 := by rw [hc3x, hc3x]; linarith
        nlinarith
    · by_cases hi : i.val < n
      · -- the edge `B → p`
        have hin : i.val = n - 1 := by omega
        have hla : i + 1 = Fin.last n := Fin.ext (by rw [fin_val_add_one_of_lt i hi]; simp; omega)
        have hxi : x i = B := by rw [hxc i hi, ← hc3n]; congr 1; exact Fin.ext hin
        rw [hla, hxp] at hyi1 ⊢
        rw [hxi] at hyi ⊢
        left
        rw [det3_ey]
        rcases eq_or_lt_of_le hyh with hyh | hyh
        · have := hfaceB y hy hyh hyi
          simp only [PiLp.sub_apply, hyh, hBh]
          nlinarith
        · have := (hhid y hy hyh hyi1).1
          rwa [det3_ey] at this
      · -- the edge `p → A`
        have hil : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
        subst hil
        have hx0 : x 0 = A := by
          rw [hxc 0 (by simp; omega), ← hc30]; congr 1
        rw [Fin.last_add_one, hx0] at hyi1 ⊢
        rw [hxp] at hyi ⊢
        left
        rw [det3_ey]
        rcases eq_or_lt_of_le hyh with hyh | hyh
        · have := hfaceA y hy hyh hyi1
          simp only [PiLp.sub_apply, hyh, hAh]
          nlinarith
        · have := (hhid y hy hyh hyi).2
          rwa [det3_ey] at this
  have hcinj : ∀ a b : Fin n, c a = c b → a = b := fun a b hab =>
    hc3inj a b (by simp only [hc3, hab])
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun j : ZMod (n + 1) => ⟪x j, ey + ε • ez⟫ := by
    have hcmp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a : Fin n, c a 1 < p 1 →
        0 < (p 1 - c a 1) + ε * (p 2 - h) := by
      refine eventually_all.2 fun a => ?_
      by_cases ha : c a 1 < p 1
      · exact (eventually_pos_affine (Or.inl (by linarith))).mono fun ε hε _ => hε
      · exact Eventually.of_forall fun ε h' => absurd h' ha
    filter_upwards [hcmp, self_mem_nhdsWithin] with ε hcmp hε
    have hε : 0 < ε := hε
    set d : Fin (n + 1) → ℝ := fun j => ⟪x j, ey + ε • ez⟫ with hd
    have hdc : ∀ j : Fin (n + 1), ∀ hj : j.val < n, d j = c ⟨j.val, hj⟩ 1 + ε * h := by
      intro j hj
      simp only [hd, inner_add_right, inner_ey, real_inner_smul_right, inner_ez, hxc j hj,
        (hc3V _).2, hc3y]
    have hdp : d (Fin.last n) = p 1 + ε * p 2 := by
      simp only [hd, inner_add_right, inner_ey, real_inner_smul_right, inner_ez, hxp]
    have hgt : ∀ a : Fin n, c a 1 < p 1 → c a 1 + ε * h < p 1 + ε * p 2 := fun a ha => by
      have := hcmp a ha; nlinarith
    have hle : ∀ a : Fin n, c a 1 + ε * h < p 1 + ε * p 2 → c a 1 < p 1 := fun a ha => by
      by_contra hc; push Not at hc; nlinarith
    have hA1 : c ⟨0, by omega⟩ 1 = A 1 := by rw [hc0]; simp [proj_xy]
    have hB1 : c ⟨n - 1, by omega⟩ 1 = B 1 := by rw [hcn]; simp [proj_xy]
    -- injectivity
    have hdinj : Function.Injective d := by
      intro i j hij
      by_cases hi : i.val < n <;> by_cases hj : j.val < n
      · rw [hdc i hi, hdc j hj] at hij
        have hy : c ⟨i.val, hi⟩ 1 = c ⟨j.val, hj⟩ 1 := by linarith
        have := hyinj (mem_filter.mpr (hc3V ⟨i.val, hi⟩)) (mem_filter.mpr (hc3V ⟨j.val, hj⟩))
          (by simp only; rw [hc3y, hc3y, hy])
        exact Fin.ext (by simpa using congrArg Fin.val (hc3inj _ _ this))
      · exfalso
        have hjl : j = Fin.last n := Fin.ext (by have := j.isLt; simp; omega)
        rw [hdc i hi, hjl, hdp] at hij
        by_cases hlt : c ⟨i.val, hi⟩ 1 < p 1
        · have := hgt _ hlt; linarith
        · have := mt (hle ⟨i.val, hi⟩) hlt; push Not at this; nlinarith
      · exfalso
        have hil : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
        rw [hdc j hj, hil, hdp] at hij
        by_cases hlt : c ⟨j.val, hj⟩ 1 < p 1
        · have := hgt _ hlt; linarith
        · have := mt (hle ⟨j.val, hj⟩) hlt; push Not at this; nlinarith
      · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
    -- index facts
    have hlast0 : Fin.last n ≠ 0 := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have hsub0 : (0 : Fin (n + 1)) - 1 = Fin.last n := by
      apply Fin.ext; rw [Fin.coe_sub_one]; simp
    have hsubl : (Fin.last n - 1).val = n - 1 := by
      rw [Fin.coe_sub_one]; simp [hlast0]
    -- a local maximum is at `A`, `B` or `p`
    have hclass : ∀ i : Fin (n + 1), d (i - 1) < d i → d (i + 1) < d i →
        i = 0 ∨ i.val = n - 1 ∨ i = Fin.last n := by
      intro i h1 h3
      by_contra hc
      push Not at hc
      obtain ⟨hi0, hin, hil⟩ := hc
      have hiv : 0 < i.val := Nat.pos_of_ne_zero (fun e => hi0 (Fin.ext e))
      have hilt : i.val < n := by
        have := i.isLt
        rcases Nat.lt_or_ge i.val n with h | h
        · exact h
        · exact absurd (Fin.ext (by simp; omega)) hil
      have hi1 : i.val + 1 < n := by omega
      have hsv : (i - 1).val = i.val - 1 := by
        rw [Fin.coe_sub_one]; simp [hi0]
      have hav : (i + 1).val = i.val + 1 := fin_val_add_one_of_lt i hilt
      rw [hdc (i - 1) (by omega), hdc i hilt, hdc (i + 1) (by omega)] at *
      set a : Fin n := ⟨i.val - 1, by omega⟩
      set b : Fin n := ⟨i.val, hilt⟩
      set b' : Fin n := ⟨i.val + 1, hi1⟩
      have ea : (⟨(i - 1).val, by omega⟩ : Fin n) = a := Fin.ext hsv
      have eb' : (⟨(i + 1).val, by omega⟩ : Fin n) = b' := Fin.ext hav
      rw [ea] at h1; rw [eb'] at h3
      have hab : a < b := Fin.lt_def.mpr (show i.val - 1 < i.val by omega)
      have hbb' : b < b' := Fin.lt_def.mpr (show i.val < i.val + 1 by omega)
      have hconsab : ∀ y ∈ S, c a 0 < y 0 → y 0 < c b 0 →
          0 < cross2 (proj_xy B - proj_xy A) (y - proj_xy A) := by
        have := hcons a (by simp [a]; omega)
        have eb : (⟨a.val + 1, by simp [a]; omega⟩ : Fin n) = b := Fin.ext (by simp [a, b]; omega)
        rwa [eb] at this
      have hpos := cross2_pos_of_consecutive hconv hSinj (mem_image_of_mem _ hAQ)
        (mem_image_of_mem _ hBQ) hSmin hSmax (by simpa [proj_xy] using hAB) (hcS a) (hcS b)
        (hcmono a b hab) (hcL a) (hcL b) hconsab (hcS b')
        (fun e => absurd (hcinj _ _ e) (ne_of_gt (hab.trans hbb')))
        (fun e => absurd (hcinj _ _ e) (ne_of_gt hbb'))
      have := y_lt_max_of_cross2 (hcmono a b hab) (hcmono b b' hbb') hpos
      rcases le_total (c a 1) (c b' 1) with hm | hm
      · rw [max_eq_right hm] at this; linarith
      · rw [max_eq_left hm] at this; linarith
    have hAmax : d (0 - 1) < d 0 → p 1 ≤ A 1 := by
      intro h1
      rw [hsub0, hdp, hdc 0 (by simp; omega)] at h1
      have h1' : p 1 + ε * p 2 < c ⟨0, by omega⟩ 1 + ε * h := by simpa using h1
      rw [← hA1]
      by_contra hc; push Not at hc
      have := hgt ⟨0, by omega⟩ hc; linarith
    have hBmax' : ∀ i : Fin (n + 1), i.val = n - 1 → d (i + 1) < d i → p 1 ≤ B 1 := by
      intro i hi h3
      have hil : i + 1 = Fin.last n := Fin.ext (by
        rw [fin_val_add_one_of_lt i (by omega)]; simp; omega)
      rw [hil, hdp, hdc i (by omega)] at h3
      have e : (⟨i.val, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hi
      rw [e] at h3
      rw [← hB1]
      by_contra hc; push Not at hc
      have := hgt _ hc; linarith
    have hpmax : d (Fin.last n - 1) < d (Fin.last n) → d (Fin.last n + 1) < d (Fin.last n) →
        A 1 < p 1 ∧ B 1 < p 1 := by
      intro h1 h3
      rw [Fin.last_add_one, hdp, hdc 0 (by simp; omega)] at h3
      rw [hdc _ (by omega), hdp] at h1
      have e : (⟨(Fin.last n - 1).val, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hsubl
      rw [e] at h1
      refine ⟨?_, ?_⟩
      · rw [← hA1]; exact hle _ (by simpa using h3)
      · rw [← hB1]; exact hle _ h1
    refine isCyclicUnimodal_of_atMostOne (k := n + 1) (by omega) hdinj ?_
    intro i j hi hj
    show (i : Fin (n + 1)) = j
    have ci := hclass i hi.1 hi.2
    have cj := hclass j hj.1 hj.2
    -- the three candidates exclude each other
    have h0 : ∀ k : Fin (n + 1), k = 0 → d (k - 1) < d k → p 1 ≤ A 1 := by
      rintro k rfl h; exact hAmax h
    rcases ci with rfl | hi' | rfl <;> rcases cj with hj' | hj' | hj'
    · exact hj'.symm
    · exfalso; have := hAmax hi.1; have := hBmax' j hj' hj.2
      rcases hpAB with h | h <;> linarith
    · exfalso; subst hj'; have := hAmax hi.1; have := hpmax hj.1 hj.2; linarith [this.1]
    · exfalso; subst hj'; have := hAmax hj.1; have := hBmax' i hi' hi.2
      rcases hpAB with h | h <;> linarith
    · exact Fin.ext (by rw [hi', hj'])
    · exfalso; subst hj'; have := hBmax' i hi' hi.2; have := hpmax hj.1 hj.2; linarith [this.2]
    · exfalso; subst hj'; have := hAmax hj.1; have := hpmax hi.1 hi.2; linarith [this.1]
    · exfalso; have := hBmax' j hj' hj.2; have := hpmax hi.1 hi.2; linarith [this.2]
    · exact hj'.symm
  have hk : 3 ≤ n + 1 := by omega
  refine isRupert_of_tilted_unimodal' (k := n + 1) V ey ez ey_ne_zero hk x hxV
    (fun i j hi hj => key i (x j) (hxV j) (hinjx.ne hi) (hinjx.ne hj))
    (fun y hy hyx i => key i y hy (hyx i) (hyx (i + 1)))
    (fun z => IsCyclicUnimodal z) isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz) hev (fun z _ hz => hz)

theorem rotZ_apply (c s : ℝ) (y : ℝ³) :
    (rotZ c s).toEuclideanLin y = !₂[c * y 0 - s * y 1, s * y 0 + c * y 1, y 2] := by
  ext i; fin_cases i <;> simp [rotZ, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]; ring

/-- Strict convex position is preserved by injective linear maps. -/
theorem ConvPos.image_linear {S : Finset ℝ²} (hS : ConvPos S) (f : ℝ² →ₗ[ℝ] ℝ²)
    (hf : Function.Injective f) : ConvPos (S.image f) := by
  classical
  intro t ht hmem
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  apply hS s hs
  have e : ((S.image f).erase (f s) : Set ℝ²) = f '' ((S.erase s : Finset ℝ²) : Set ℝ²) := by
    ext y; simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, mem_coe,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hne⟩; exact ⟨z, ⟨hz, fun e => hne (by rw [e])⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzs⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, fun e => hzs (hf e)⟩
  rw [e, ← LinearMap.image_convexHull] at hmem
  obtain ⟨z, hz, hzs⟩ := hmem
  rwa [hf hzs] at hz

/-- `tval u y`: the screen coordinate of `y` across the horizontal view `u` (the
coordinate along `u × ez`, scaled by `|u|`). -/
def tval (u y : ℝ³) : ℝ := u 1 * y 0 - u 0 * y 1

/-- **The edge-on lemma at any horizontal view `u`** (`isRupert_edgeOn` after a
rotation about the vertical axis taking `u` to `ey`). -/
theorem isRupert_edgeOn_dir (V : Finset ℝ³) (h : ℝ) (u A B p : ℝ³) (hu2 : u 2 = 0)
    (hu : u ≠ 0) (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hxinj : Set.InjOn (tval u) (V.filter fun y => y 2 = h))
    (hyinj : Set.InjOn (fun y : ℝ³ => ⟪y, u⟫) (V.filter fun y => y 2 = h))
    (hA : A ∈ V) (hAh : A 2 = h) (hB : B ∈ V) (hBh : B 2 = h)
    (hAmin : ∀ y ∈ V, y 2 = h → tval u A ≤ tval u y)
    (hBmax : ∀ y ∈ V, y 2 = h → tval u y ≤ tval u B)
    (hAB : tval u A < tval u B) (hp : p ∈ V) (hph : p 2 < h)
    (hhid : ∀ y ∈ V, y 2 < h → y ≠ p →
      0 < det3 (p - B) (y - B) u ∧ 0 < det3 (A - p) (y - p) u)
    (hpAB : ⟪A, u⟫ < ⟪p, u⟫ ∨ ⟪B, u⟫ < ⟪p, u⟫) : IsRupert V := by
  classical
  have hr2 : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    by_contra hc; push Not at hc
    apply hu; ext i; fin_cases i
    · show u 0 = 0; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    · show u 1 = 0; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    · exact hu2
  set r := Real.sqrt (u 0 ^ 2 + u 1 ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hr2
  have hrr : r * r = u 0 ^ 2 + u 1 ^ 2 := Real.mul_self_sqrt hr2.le
  set cc := u 1 / r
  set ss := u 0 / r
  have hr2' : r ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by rw [sq]; exact hrr
  have hcs : cc ^ 2 + ss ^ 2 = 1 := by
    simp only [cc, ss, div_pow]; rw [← add_div, hr2', add_comm]; exact div_self hr2.ne'
  set R := rotZ cc ss with hR
  have hRSO : R ∈ SO3 := rotZ_mem_SO3 hcs
  set f := R.toEuclideanLin with hf
  have hf0 : ∀ y, f y 0 = tval u y / r := fun y => by
    simp only [hf, hR, rotZ_apply, tval, cc, ss]; simp; ring
  have hf1 : ∀ y, f y 1 = ⟪y, u⟫ / r := fun y => by
    simp only [hf, hR, rotZ_apply, cc, ss]
    simp [PiLp.inner_apply, Fin.sum_univ_three, hu2]; ring
  have hf2 : ∀ y, f y 2 = y 2 := fun y => by simp [hf, hR, rotZ_apply]
  have hfinj : Function.Injective f := fun a b hab => by
    have h0 := congrArg (fun v : ℝ³ => v 0) hab
    have h1 := congrArg (fun v : ℝ³ => v 1) hab
    have h2 := congrArg (fun v : ℝ³ => v 2) hab
    simp only [hf, hR, rotZ_apply] at h0 h1 h2
    simp at h0 h1 h2
    ext i; fin_cases i
    · show a 0 = b 0
      have e : (cc ^ 2 + ss ^ 2) * a 0 = (cc ^ 2 + ss ^ 2) * b 0 := by
        linear_combination cc * h0 + ss * h1
      rwa [hcs, one_mul, one_mul] at e
    · show a 1 = b 1
      have e : (cc ^ 2 + ss ^ 2) * a 1 = (cc ^ 2 + ss ^ 2) * b 1 := by
        linear_combination -ss * h0 + cc * h1
      rwa [hcs, one_mul, one_mul] at e
    · exact h2
  have hdet : ∀ a b : ℝ³, det3 (f a) (f b) ey = det3 a b u / r := fun a b => by
    rw [det3_ey]
    simp only [hf, hR, rotZ_apply, det3, cross, cc, ss]
    simp [PiLp.inner_apply, Fin.sum_univ_three, hu2]; field_simp; ring
  have hfsub : ∀ a b : ℝ³, f a - f b = f (a - b) := fun a b => (map_sub f a b).symm
  apply isRupert_of_isRupert_image_rotation R hRSO V
  set V' := V.image f with hV'
  have hfilt : V'.filter (fun y => y 2 = h) = (V.filter fun y => y 2 = h).image f := by
    ext y; simp only [hV', mem_filter, mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzh⟩; exact ⟨z, ⟨hz, by rwa [hf2] at hzh⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzh⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, by rw [hf2]; exact hzh⟩
  -- the planar part of `f`
  set g : ℝ² →ₗ[ℝ] ℝ² :=
    { toFun := fun s => !₂[cc * s 0 - ss * s 1, ss * s 0 + cc * s 1]
      map_add' := fun a b => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun a b => by ext i; fin_cases i <;> simp <;> ring } with hg
  have hgf : ∀ y, proj_xy (f y) = g (proj_xy y) := fun y => by
    ext i; fin_cases i <;> simp [hg, hf, hR, rotZ_apply, proj_xy]
  have hginj : Function.Injective g := fun a b hab => by
    have h0 := congrArg (fun v : ℝ² => v 0) hab
    have h1 := congrArg (fun v : ℝ² => v 1) hab
    simp [hg] at h0 h1
    ext i; fin_cases i
    · show a 0 = b 0
      have e : (cc ^ 2 + ss ^ 2) * a 0 = (cc ^ 2 + ss ^ 2) * b 0 := by
        linear_combination cc * h0 + ss * h1
      rwa [hcs, one_mul, one_mul] at e
    · show a 1 = b 1
      have e : (cc ^ 2 + ss ^ 2) * a 1 = (cc ^ 2 + ss ^ 2) * b 1 := by
        linear_combination -ss * h0 + cc * h1
      rwa [hcs, one_mul, one_mul] at e
  have hmemV' : ∀ y ∈ V', ∃ z ∈ V, f z = y := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy; exact ⟨z, hz, rfl⟩
  have hdivlt : ∀ a b : ℝ, a < b → a / r < b / r := fun a b hab => div_lt_div_of_pos_right hab hr0
  have hdivle : ∀ a b : ℝ, a ≤ b → a / r ≤ b / r := fun a b hab => div_le_div_of_nonneg_right hab hr0.le
  have hdivinj : ∀ a b : ℝ, a / r = b / r → a = b := fun a b hab => by
    field_simp at hab; exact hab
  refine isRupert_edgeOn V' h (f A) (f B) (f p) ?_ ?_ ?_ ?_ (mem_image_of_mem _ hA) (by rw [hf2, hAh])
    (mem_image_of_mem _ hB) (by rw [hf2, hBh]) ?_ ?_ (by rw [hf0, hf0]; exact hdivlt _ _ hAB)
    (mem_image_of_mem _ hp) (by rw [hf2]; exact hph) ?_ ?_
  · intro y hy; obtain ⟨z, hz, rfl⟩ := hmemV' y hy; rw [hf2]; exact hV z hz
  · rw [hfilt, Finset.image_image]
    have e : (proj_xy ∘ f) = g ∘ proj_xy := funext hgf
    rw [e, ← Finset.image_image]
    exact hconv.image_linear g hginj
  · rw [hfilt]
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
    simp only [hf0] at hab
    rw [hxinj ha' hb' (hdivinj _ _ hab)]
  · rw [hfilt]
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
    simp only [hf1] at hab
    rw [hyinj ha' hb' (hdivinj _ _ hab)]
  · intro y hy hyh; obtain ⟨z, hz, rfl⟩ := hmemV' y hy
    rw [hf2] at hyh; rw [hf0, hf0]; exact hdivle _ _ (hAmin z hz hyh)
  · intro y hy hyh; obtain ⟨z, hz, rfl⟩ := hmemV' y hy
    rw [hf2] at hyh; rw [hf0, hf0]; exact hdivle _ _ (hBmax z hz hyh)
  · intro y hy hyh hyp; obtain ⟨z, hz, rfl⟩ := hmemV' y hy
    rw [hf2] at hyh
    have hzp : z ≠ p := fun e => hyp (by rw [e])
    obtain ⟨h1, h2⟩ := hhid z hz hyh hzp
    rw [hfsub, hfsub, hfsub, hfsub, hdet, hdet]
    exact ⟨div_pos h1 hr0, div_pos h2 hr0⟩
  · rw [hf1, hf1, hf1]
    rcases hpAB with h' | h'
    · exact Or.inl (hdivlt _ _ h')
    · exact Or.inr (hdivlt _ _ h')

theorem det3_add_mid (v w w' u : ℝ³) : det3 v (w + w') u = det3 v w u + det3 v w' u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_smul_mid (v w u : ℝ³) (c : ℝ) : det3 v (c • w) u = c * det3 v w u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_self_mid (v u : ℝ³) : det3 v v u = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_mid_right (v u : ℝ³) : det3 v u u = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_horiz (v w u : ℝ³) (hw : w 2 = 0) (hu : u 2 = 0) :
    det3 v w u = v 2 * tval u w := by
  simp [det3, cross, tval, PiLp.inner_apply, Fin.sum_univ_three, hw, hu]; ring

theorem tval_sub (u a b : ℝ³) : tval u (a - b) = tval u a - tval u b := by
  simp [tval]; ring

theorem tval_neg (u y : ℝ³) : tval (-u) y = -tval u y := by simp [tval]; ring

/-- **Case I at a given view.**  The face `Q = V ∩ {z = h}` (strictly convex
position, `tval u` and `⟪·, u⟫` injective on it), two points `p`, `q` below
it and no others; `q` lies on the line through `x = α a + β b + θ p` along `u`
(`a ≠ b` in `Q`, `α, β > 0`, `α + β + θ = 1`).  Then `V` is Rupert, by the edge-on
lemma at `u` or at `-u`. -/
theorem isRupert_caseI_at (V : Finset ℝ³) (h : ℝ) (u p q a b : ℝ³) (hu2 : u 2 = 0) (hu : u ≠ 0)
    (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hxinj : Set.InjOn (tval u) (V.filter fun y => y 2 = h))
    (hyinj : Set.InjOn (fun y : ℝ³ => ⟪y, u⟫) (V.filter fun y => y 2 = h))
    (hp : p ∈ V) (hph : p 2 < h) (hq : q ∈ V) (hqp : q ≠ p)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q)
    (ha : a ∈ V) (hah : a 2 = h) (hb : b ∈ V) (hbh : b 2 = h) (hab : a ≠ b)
    {α β θ κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hsum : α + β + θ = 1)
    (hqx : q = α • a + β • b + θ • p + κ • u) : IsRupert V := by
  classical
  set Q := V.filter fun y => y 2 = h with hQ
  have haQ : a ∈ Q := mem_filter.mpr ⟨ha, hah⟩
  obtain ⟨A, hAQ, hAmin⟩ := Q.exists_min_image (tval u) ⟨a, haQ⟩
  obtain ⟨B, hBQ, hBmax⟩ := Q.exists_max_image (tval u) ⟨a, haQ⟩
  have hA := (mem_filter.mp hAQ).1
  have hAh := (mem_filter.mp hAQ).2
  have hB := (mem_filter.mp hBQ).1
  have hBh := (mem_filter.mp hBQ).2
  have hbQ : b ∈ Q := mem_filter.mpr ⟨hb, hbh⟩
  have hAB : tval u A < tval u B := by
    rcases eq_or_ne A B with e | e
    · exfalso
      have h1 := hAmin a haQ; have h2 := hBmax a haQ
      have h3 := hAmin b hbQ; have h4 := hBmax b hbQ
      rw [e] at h1 h3
      exact hab (hxinj haQ hbQ (show tval u a = tval u b by linarith))
    · exact lt_of_le_of_ne (hAmin B hBQ) (fun h' => e (hxinj hAQ hBQ h'))
  -- the horizontal displacements to a face point
  have hhor : ∀ y z : ℝ³, y 2 = h → z 2 = h → (y - z) 2 = 0 := fun y z hy hz => by
    simp [hy, hz]
  -- the key determinant expansions
  have hxB : ∀ C : ℝ³, C 2 = h → det3 (p - C) (q - C) u =
      α * ((p 2 - h) * (tval u a - tval u C)) + β * ((p 2 - h) * (tval u b - tval u C)) := by
    intro C hC
    have e : q - C = α • (a - C) + β • (b - C) + θ • (p - C) + κ • u := by
      rw [hqx]; ext i; simp
      have := congrArg (fun t => t * C i) hsum; simp at this; linarith
    rw [e, det3_add_mid, det3_add_mid, det3_add_mid, det3_smul_mid, det3_smul_mid, det3_smul_mid,
      det3_smul_mid, det3_self_mid, det3_mid_right, det3_horiz _ _ _ (hhor a C hah hC) hu2,
      det3_horiz _ _ _ (hhor b C hbh hC) hu2, tval_sub, tval_sub]
    simp only [PiLp.sub_apply, hC]; ring
  have hxA : ∀ C : ℝ³, C 2 = h → det3 (C - p) (q - p) u =
      α * ((h - p 2) * (tval u a - tval u C)) + β * ((h - p 2) * (tval u b - tval u C)) := by
    intro C hC
    have e : q - p = α • (a - C) + β • (b - C) + (α + β) • (C - p) + κ • u := by
      rw [hqx]; ext i; simp
      have := congrArg (fun t => t * p i) hsum; simp at this; linarith
    rw [e, det3_add_mid, det3_add_mid, det3_add_mid, det3_smul_mid, det3_smul_mid, det3_smul_mid,
      det3_smul_mid, det3_self_mid, det3_mid_right, det3_horiz _ _ _ (hhor a C hah hC) hu2,
      det3_horiz _ _ _ (hhor b C hbh hC) hu2, tval_sub, tval_sub]
    simp only [PiLp.sub_apply, hC]; ring
  have hsB : α * (tval u a - tval u B) + β * (tval u b - tval u B) < 0 := by
    have h1 := hBmax a haQ; have h2 := hBmax b hbQ
    rcases eq_or_ne a B with e | e
    · have : tval u b < tval u B := lt_of_le_of_ne h2 (fun h' => hab (e.trans (hxinj hBQ hbQ h'.symm)))
      rw [e]; nlinarith
    · have : tval u a < tval u B := lt_of_le_of_ne h1 (fun h' => e (hxinj haQ hBQ h'))
      nlinarith
  have hsA : 0 < α * (tval u a - tval u A) + β * (tval u b - tval u A) := by
    have h1 := hAmin a haQ; have h2 := hAmin b hbQ
    rcases eq_or_ne a A with e | e
    · have : tval u A < tval u b := lt_of_le_of_ne h2 (fun h' => hab (e.trans (hxinj hAQ hbQ h')))
      rw [e]; nlinarith
    · have : tval u A < tval u a := lt_of_le_of_ne h1 (fun h' => e (hxinj haQ hAQ h'.symm))
      nlinarith
  have hhp : 0 < h - p 2 := by linarith
  have hfilt : ∀ y ∈ V, y 2 < h → y ≠ p → y = q := fun y hy hyh hyp =>
    (hrest y hy hyh).resolve_left hyp
  by_cases hdeep : ⟪A, u⟫ < ⟪p, u⟫ ∨ ⟪B, u⟫ < ⟪p, u⟫
  · refine isRupert_edgeOn_dir V h u A B p hu2 hu hV hconv hxinj hyinj hA hAh hB hBh
      (fun y hy hyh => hAmin y (mem_filter.mpr ⟨hy, hyh⟩))
      (fun y hy hyh => hBmax y (mem_filter.mpr ⟨hy, hyh⟩)) hAB hp hph ?_ hdeep
    intro y hy hyh hyp
    obtain rfl := hfilt y hy hyh hyp
    rw [hxB B hBh, hxA A hAh]
    constructor <;> nlinarith
  · push Not at hdeep
    have hne : ⟪A, u⟫ ≠ ⟪B, u⟫ := fun e => (ne_of_lt hAB) (by rw [hyinj hAQ hBQ e])
    have hneg : ∀ v w : ℝ³, det3 v w (-u) = -det3 v w u := fun v w => by
      simp [det3, inner_neg_right]
    refine isRupert_edgeOn_dir V h (-u) B A p (by simp [hu2]) (neg_ne_zero.mpr hu) hV hconv
      (fun y hy z hz e => hxinj hy hz (by simp only [tval_neg] at e; linarith))
      (fun y hy z hz e => hyinj hy hz (by simp only [inner_neg_right] at e; linarith))
      hB hBh hA hAh
      (fun y hy hyh => by rw [tval_neg, tval_neg]; linarith [hBmax y (mem_filter.mpr ⟨hy, hyh⟩)])
      (fun y hy hyh => by rw [tval_neg, tval_neg]; linarith [hAmin y (mem_filter.mpr ⟨hy, hyh⟩)])
      (by rw [tval_neg, tval_neg]; linarith) hp hph ?_ ?_
    · intro y hy hyh hyp
      obtain rfl := hfilt y hy hyh hyp
      rw [hneg, hneg, hxB A hAh, hxA B hBh]
      constructor <;> nlinarith
    · simp only [inner_neg_right, neg_lt_neg_iff]
      by_contra hc; push Not at hc
      exact hne (le_antisymm (by linarith [hc.1, hc.2, hdeep.1, hdeep.2])
        (by linarith [hc.1, hc.2, hdeep.1, hdeep.2]))

/-- Three distinct collinear points violate strict convex position. -/
theorem ConvPos.cross2_ne {S : Finset ℝ²} (hS : ConvPos S) {a b c : ℝ²} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cross2 (b - a) (c - a) ≠ 0 := by
  classical
  intro h0
  -- `c - a = t (b - a)`
  have hw : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, c - a = t • (b - a) := by
    simp only [cross2, PiLp.sub_apply] at h0
    by_cases h0' : b 0 - a 0 = 0
    · have h1 : b 1 - a 1 ≠ 0 := by
        intro h1; apply hw; ext i; fin_cases i
        · simpa using h0'
        · simpa using h1
      refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
      ext i; fin_cases i
      · simp only [Fin.zero_eta, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        have : (c 0 - a 0) * (b 1 - a 1) = 0 := by rw [h0'] at h0; linarith
        rw [h0']; simp; exact (mul_eq_zero.mp this).resolve_right h1
      · simp only [Fin.mk_one, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; field_simp
    · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
      ext i; fin_cases i
      · simp only [Fin.zero_eta, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; field_simp
      · simp only [Fin.mk_one, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp; linarith
  have ht0 : t ≠ 0 := by
    rintro rfl; apply hac; rw [zero_smul, sub_eq_zero] at ht; exact ht.symm
  have ht1 : t ≠ 1 := by
    rintro rfl; apply hbc; have := ht; simp only [one_smul, sub_left_inj] at this; exact this.symm
  have hcx : c = a + t • (b - a) := by rw [← ht]; abel
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · -- `a` between `c` and `b`
    apply hS a ha
    have h1t : (1 : ℝ) - t ≠ 0 := by linarith
    have : a = c + (-t / (1 - t)) • (b - c) := by
      rw [hcx]; ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp; ring
    rw [this]
    refine (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ?_)
      (subset_convexHull ℝ _ ?_) (segment_pt_mem ?_ ?_)
    · rw [← this]; simp [hc, Ne.symm hac]
    · rw [← this]; simp [hb, Ne.symm hab]
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith
  · rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · -- `c` between `a` and `b`
      apply hS c hc
      rw [hcx]
      refine (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ?_)
        (subset_convexHull ℝ _ ?_) (segment_pt_mem hpos.le hlt.le)
      · rw [← hcx]; simp [ha, hac]
      · rw [← hcx]; simp [hb, hbc]
    · -- `b` between `a` and `c`
      apply hS b hb
      have : b = a + (1 / t) • (c - a) := by
        rw [hcx]; ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp; ring
      rw [this]
      refine (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ?_)
        (subset_convexHull ℝ _ ?_) (segment_pt_mem (by positivity) ?_)
      · rw [← this]; simp [ha, hab]
      · rw [← this]; simp [hc, hbc.symm]
      · rw [div_le_one (by linarith)]; linarith

theorem det3_add_right (v w x y : ℝ³) : det3 v w (x + y) = det3 v w x + det3 v w y := by
  simp [det3, inner_add_right]

theorem det3_smul_right (v w x : ℝ³) (c : ℝ) : det3 v w (c • x) = c * det3 v w x := by
  simp [det3, real_inner_smul_right]

theorem det3_self_right (v w : ℝ³) : det3 v w v = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_self_right' (v w : ℝ³) : det3 v w w = 0 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- **Case I** (FEWER-FACES-PROOFS.md §2B): the face `Q = V ∩ {z = h}` has at
least three points, in strictly convex position; below it are exactly two
points `p`, `q`, with `q` higher.  Then `V` is Rupert. -/
theorem isRupert_caseI (V : Finset ℝ³) (h : ℝ) (p q : ℝ³) (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ3 : 2 < (V.filter fun y => y 2 = h).card)
    (hp : p ∈ V) (hq : q ∈ V) (hpq : p 2 < q 2) (hqh : q 2 < h)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q) : IsRupert V := by
  classical
  set Q := V.filter fun y => y 2 = h with hQ
  have hQV : ∀ y ∈ Q, y ∈ V ∧ y 2 = h := fun y hy => mem_filter.mp hy
  have hprojinj : ∀ y ∈ Q, ∀ y' ∈ Q, proj_xy y = proj_xy y' → y = y' := by
    intro y hy y' hy' he
    rw [← liftPt_proj (hQV y hy).2, ← liftPt_proj (hQV y' hy').2, he]
  -- the pair `a, b`: `q` is off the plane `abp`
  set D : ℝ³ → ℝ³ → ℝ := fun a b => det3 (b - a) (p - a) (q - a) with hD
  obtain ⟨a, b, haQ, hbQ, hab, hDab⟩ : ∃ a b, a ∈ Q ∧ b ∈ Q ∧ a ≠ b ∧ D a b ≠ 0 := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hQ3
    have hid : D a b - D a c + D b c =
        (q 2 - p 2) * cross2 (proj_xy b - proj_xy a) (proj_xy c - proj_xy a) := by
      simp only [hD, det3, cross, cross2, proj_xy, PiLp.inner_apply, Fin.sum_univ_three]
      simp [(hQV a ha).2, (hQV b hb).2, (hQV c hc).2]; ring
    have hcr : cross2 (proj_xy b - proj_xy a) (proj_xy c - proj_xy a) ≠ 0 :=
      hconv.cross2_ne (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) (mem_image_of_mem _ hc)
        (fun e => hab (hprojinj a ha b hb e)) (fun e => hac (hprojinj a ha c hc e))
        (fun e => hbc (hprojinj b hb c hc e))
    by_cases h1 : D a b = 0
    · by_cases h2 : D a c = 0
      · refine ⟨b, c, hb, hc, hbc, fun h3 => ?_⟩
        rw [h1, h2, h3] at hid
        have : q 2 - p 2 ≠ 0 := by linarith
        exact (mul_ne_zero this hcr) (by linarith)
      · exact ⟨a, c, ha, hc, hac, h2⟩
    · exact ⟨a, b, ha, hb, hab, h1⟩
  have haV := (hQV a haQ).1; have hah := (hQV a haQ).2
  have hbV := (hQV b hbQ).1; have hbh := (hQV b hbQ).2
  -- the height ratio
  have hhp : 0 < h - p 2 := by linarith
  set θ := (h - q 2) / (h - p 2) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) hhp
  have hθ1 : θ < 1 := (div_lt_one hhp).mpr (by linarith)
  have hθh : θ * (h - p 2) = h - q 2 := by rw [hθ]; field_simp
  set w := a - b with hw
  set u0 := (1 - θ) • b + θ • p - q with hu0
  have hw2 : w 2 = 0 := by simp [hw, hah, hbh]
  have hu02 : u0 2 = 0 := by
    simp only [hu0, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hbh]
    linarith
  -- `D a b = det3 w (p - a) u` for every `u = u0 + α w`
  have hDu : ∀ α : ℝ, D a b = det3 w (p - a) (u0 + α • w) := by
    intro α
    simp only [hD, hu0, hw, det3, cross]
    simp [PiLp.inner_apply, Fin.sum_univ_three]; ring
  -- a direction `e` in the plane is perpendicular to `u0 + α w` for at most one `α`
  have hbad : ∀ e : ℝ³, e 2 = 0 → e ≠ 0 →
      ({α : ℝ | ⟪e, u0 + α • w⟫ = 0}).Subsingleton := by
    intro e he2 hne α1 h1 α2 h2
    simp only [Set.mem_ofPred_eq, inner_add_right, real_inner_smul_right] at h1 h2
    by_contra hα
    have hew : ⟪e, w⟫ = 0 := by
      have : (α1 - α2) * ⟪e, w⟫ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hα)
    have heu : ⟪e, u0⟫ = 0 := by rw [hew, mul_zero, add_zero] at h1; exact h1
    -- then `u0 ∥ w`, so `D a b = 0`
    apply hDab
    rw [hDu 0, zero_smul, add_zero]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hew heu
    simp only [he2] at hew heu
    have hcr : u0 1 * w 0 - u0 0 * w 1 = 0 := by
      have hne' : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
        by_contra hc; push Not at hc
        apply hne; ext i; fin_cases i
        · exact hc.1
        · exact hc.2
        · exact he2
      rcases hne' with h0 | h1'
      · have : e 0 * (u0 1 * w 0 - u0 0 * w 1) = 0 := by
          linear_combination u0 1 * hew - w 1 * heu
        exact (mul_eq_zero.mp this).resolve_left h0
      · have : e 1 * (u0 1 * w 0 - u0 0 * w 1) = 0 := by
          linear_combination -(u0 0) * hew + w 0 * heu
        exact (mul_eq_zero.mp this).resolve_left h1'
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
    simp [hw2, hu02]
    linear_combination -(p 2 - a 2) * hcr
  -- the finitely many bad parameters
  set rot : ℝ³ → ℝ³ := fun d => !₂[-(d 1), d 0, 0] with hrot
  set pairs := (Q ×ˢ Q).filter (fun yy => yy.1 ≠ yy.2) with hpairs
  have hhor : ∀ yy ∈ pairs, (yy.1 - yy.2) 2 = 0 ∧ yy.1 - yy.2 ≠ 0 := by
    intro yy hyy
    obtain ⟨hmem, hne⟩ := mem_filter.mp hyy
    obtain ⟨h1, h2⟩ := mem_product.mp hmem
    exact ⟨by simp [(hQV _ h1).2, (hQV _ h2).2], sub_ne_zero.mpr hne⟩
  have hrot2 : ∀ d : ℝ³, rot d 2 = 0 := fun d => by simp [hrot]
  have hrotne : ∀ d : ℝ³, d 2 = 0 → d ≠ 0 → rot d ≠ 0 := by
    intro d hd2 hd he
    apply hd
    have h0 := congrArg (fun v : ℝ³ => v 0) he
    have h1 := congrArg (fun v : ℝ³ => v 1) he
    simp [hrot] at h0 h1
    ext i; fin_cases i
    · exact h1
    · exact h0
    · exact hd2
  have htrot : ∀ d u : ℝ³, ⟪rot d, u⟫ = tval u d := fun d u => by
    simp [hrot, tval, PiLp.inner_apply, Fin.sum_univ_three]; ring
  set bad := ⋃ yy ∈ pairs, ({α : ℝ | ⟪yy.1 - yy.2, u0 + α • w⟫ = 0} ∪
    {α : ℝ | ⟪rot (yy.1 - yy.2), u0 + α • w⟫ = 0}) with hbadset
  have hbadfin : bad.Finite := by
    refine Set.Finite.biUnion pairs.finite_toSet fun yy hyy => ?_
    obtain ⟨h2, hne⟩ := hhor yy hyy
    exact (hbad _ h2 hne).finite.union (hbad _ (hrot2 _) (hrotne _ h2 hne)).finite
  obtain ⟨α, ⟨hαI, hαB⟩⟩ := ((Set.Ioo_infinite (show (0 : ℝ) < 1 - θ by linarith)).sdiff
    hbadfin).nonempty
  have hα0 : 0 < α := hαI.1
  have hβ0 : 0 < 1 - θ - α := by linarith [hαI.2]
  set u := u0 + α • w with hu
  have hu2 : u 2 = 0 := by simp [hu, hu02, hw2]
  have hune : u ≠ 0 := by
    intro e; apply hDab; rw [hDu α, ← hu, e]; simp [det3]
  have hpair : ∀ y ∈ Q, ∀ y' ∈ Q, y ≠ y' → (y, y') ∈ pairs := fun y hy y' hy' hne =>
    mem_filter.mpr ⟨mem_product.mpr ⟨hy, hy'⟩, hne⟩
  have hxinj : Set.InjOn (tval u) Q := by
    intro y hy y' hy' he
    by_contra hne
    apply hαB
    simp only [hbadset, Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨(y, y'), hpair y hy y' hy' hne, Or.inr ?_⟩
    rw [← hu, htrot, tval_sub]; linarith
  have hyinj : Set.InjOn (fun y : ℝ³ => ⟪y, u⟫) Q := by
    intro y hy y' hy' he
    by_contra hne
    apply hαB
    simp only [hbadset, Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨(y, y'), hpair y hy y' hy' hne, Or.inl ?_⟩
    have he' : ⟪y, u⟫ = ⟪y', u⟫ := he
    rw [← hu, inner_sub_left, he', sub_self]
  have hqx : q = α • a + (1 - θ - α) • b + θ • p + (-1 : ℝ) • u := by
    rw [hu, hu0, hw]; ext i; simp; ring
  exact isRupert_caseI_at V h u p q a b hu2 hune hV hconv hxinj hyinj hp (by linarith) hq
    (by rintro rfl; linarith) hrest haV hah hbV hbh hab hα0 hβ0 (by ring) hqx

/-- **The cycle lemma for a face seen edge-on (general tilt).**  The predicted
silhouette at `ey + ε v` is a sequence `e` of face points (`z = h`) followed by
a point `p` below; the determinant tests of Lemma 8.0 are hypotheses.  If no
interior point of `e` is deeper than both its neighbours, `p` is deeper than
one end of `e`, and distinct cycle points differ in depth or in `⟪·, v⟫`, then
`V` is Rupert. -/
theorem isRupert_cycle_edgeOn (V : Finset ℝ³) (v p : ℝ³) {m : ℕ} (hm : 2 ≤ m)
    (e : Fin m → ℝ³) (heV : ∀ i, e i ∈ V) (hp : p ∈ V) (hinj : Function.Injective
      (fun j : Fin (m + 1) => if hj : j.val < m then e ⟨j.val, hj⟩ else p))
    (hE : ∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ y ∈ V, y ≠ e i → y ≠ e ⟨i.val + 1, hi⟩ →
      TiltSign (e ⟨i.val + 1, hi⟩ - e i) (y - e i) ey v)
    (hEp : ∀ y ∈ V, y ≠ e ⟨m - 1, by omega⟩ → y ≠ p →
      TiltSign (p - e ⟨m - 1, by omega⟩) (y - e ⟨m - 1, by omega⟩) ey v)
    (hpE : ∀ y ∈ V, y ≠ p → y ≠ e ⟨0, by omega⟩ → TiltSign (e ⟨0, by omega⟩ - p) (y - p) ey v)
    (hconvex : ∀ i : Fin m, ∀ (h0 : 0 < i.val) (h1 : i.val + 1 < m),
      e i 1 < max (e ⟨i.val - 1, by have := i.isLt; omega⟩ 1) (e ⟨i.val + 1, h1⟩ 1))
    (hdeep : e ⟨0, by omega⟩ 1 < p 1 ∨ e ⟨m - 1, by omega⟩ 1 < p 1)
    (hsep : ∀ j j' : Fin (m + 1), j ≠ j' →
      (if hj : j.val < m then e ⟨j.val, hj⟩ else p) 1 ≠
        (if hj : j'.val < m then e ⟨j'.val, hj⟩ else p) 1 ∨
      ⟪(if hj : j.val < m then e ⟨j.val, hj⟩ else p) -
        (if hj : j'.val < m then e ⟨j'.val, hj⟩ else p), v⟫ ≠ 0) : IsRupert V := by
  classical
  set x : Fin (m + 1) → ℝ³ := fun j => if hj : j.val < m then e ⟨j.val, hj⟩ else p with hx
  have hxc : ∀ j : Fin (m + 1), ∀ hj : j.val < m, x j = e ⟨j.val, hj⟩ := fun j hj => by
    simp [hx, hj]
  have hxp : x (Fin.last m) = p := by simp [hx]
  have hxV : ∀ j, x j ∈ V := fun j => by
    by_cases hj : j.val < m
    · rw [hxc j hj]; exact heV _
    · simp only [hx, hj, dite_false]; exact hp
  have key : ∀ i : Fin (m + 1), ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ey v := by
    intro i y hy hyi hyi1
    by_cases hi1 : i.val + 1 < m
    · have hi : i.val < m := by omega
      have hval : (i + 1).val = i.val + 1 := fin_val_add_one_of_lt i hi
      have e1 : x (i + 1) = e ⟨i.val + 1, hi1⟩ := by
        rw [hxc (i + 1) (by omega)]; congr 1; exact Fin.ext hval
      rw [e1] at hyi1 ⊢; rw [hxc i hi] at hyi ⊢
      exact hE ⟨i.val, hi⟩ hi1 y hy hyi hyi1
    · by_cases hi : i.val < m
      · have hla : i + 1 = Fin.last m := Fin.ext (by rw [fin_val_add_one_of_lt i hi]; simp; omega)
        have hxi : x i = e ⟨m - 1, by omega⟩ := by rw [hxc i hi]; congr 1; exact Fin.ext (by simp; omega)
        rw [hla, hxp] at hyi1 ⊢; rw [hxi] at hyi ⊢
        exact hEp y hy hyi hyi1
      · have hil : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
        subst hil
        have hx0 : x 0 = e ⟨0, by omega⟩ := by rw [hxc 0 (by simp; omega)]; congr 1
        rw [Fin.last_add_one, hx0] at hyi1 ⊢
        rw [hxp] at hyi ⊢
        exact hpE y hy hyi hyi1
  -- eventually the depths are injective and follow `y` where `y` differs
  have hev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j j' : Fin (m + 1), x j 1 < x j' 1 →
      x j 1 + ε * ⟪x j, v⟫ < x j' 1 + ε * ⟪x j', v⟫ := by
    refine eventually_all.2 fun j => eventually_all.2 fun j' => ?_
    by_cases hjj : x j 1 < x j' 1
    · refine (eventually_pos_affine (A := x j' 1 - x j 1) (B := ⟪x j', v⟫ - ⟪x j, v⟫)
        (Or.inl (by linarith))).mono fun ε hε _ => by nlinarith
    · exact Eventually.of_forall fun ε h' => absurd h' hjj
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun j : ZMod (m + 1) => ⟪x j, ey + ε • v⟫ := by
    filter_upwards [hev0, self_mem_nhdsWithin] with ε hev0 hε
    have hε : 0 < ε := hε
    set d : Fin (m + 1) → ℝ := fun j => ⟪x j, ey + ε • v⟫ with hd
    have hdx : ∀ j, d j = x j 1 + ε * ⟪x j, v⟫ := fun j => by
      simp [hd, inner_add_right, inner_ey, real_inner_smul_right]
    have hlt : ∀ j j', x j 1 < x j' 1 → d j < d j' := fun j j' h => by
      rw [hdx, hdx]; exact hev0 j j' h
    have hdinj : Function.Injective d := by
      intro j j' hjj
      by_contra hne
      rcases hsep j j' hne with h1 | h1
      · rcases lt_or_gt_of_ne h1 with h2 | h2
        · exact absurd hjj (ne_of_lt (hlt _ _ h2))
        · exact absurd hjj (ne_of_gt (hlt _ _ h2))
      · rw [hdx, hdx] at hjj
        have hy : x j 1 = x j' 1 := by
          by_contra hy
          rcases lt_or_gt_of_ne hy with h2 | h2
          · have := hlt _ _ h2; rw [hdx, hdx] at this; linarith
          · have := hlt _ _ h2; rw [hdx, hdx] at this; linarith
        apply h1
        rw [inner_sub_left]
        have : ε * (⟪x j, v⟫ - ⟪x j', v⟫) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hε.ne'
    have hlast0 : Fin.last m ≠ 0 := by
      intro e'; have := congrArg Fin.val e'; simp at this; omega
    have hsub0 : (0 : Fin (m + 1)) - 1 = Fin.last m := by
      apply Fin.ext; rw [Fin.coe_sub_one]; simp
    have hsubl : (Fin.last m - 1).val = m - 1 := by
      rw [Fin.coe_sub_one]; simp [hlast0]
    -- a local maximum is at an end of `e` or at `p`
    have hclass : ∀ i : Fin (m + 1), d (i - 1) < d i → d (i + 1) < d i →
        i = 0 ∨ i.val = m - 1 ∨ i = Fin.last m := by
      intro i h1 h3
      by_contra hc
      push Not at hc
      obtain ⟨hi0, hin, hil⟩ := hc
      have hiv : 0 < i.val := Nat.pos_of_ne_zero (fun e' => hi0 (Fin.ext e'))
      have hilt : i.val < m := by
        rcases Nat.lt_or_ge i.val m with h | h
        · exact h
        · exact absurd (Fin.ext (by have := i.isLt; simp; omega)) hil
      have hi1 : i.val + 1 < m := by omega
      have hsv : (i - 1).val = i.val - 1 := by rw [Fin.coe_sub_one]; simp [hi0]
      have hav : (i + 1).val = i.val + 1 := fin_val_add_one_of_lt i hilt
      have hcv := hconvex ⟨i.val, hilt⟩ hiv hi1
      have ea : x (i - 1) = e ⟨i.val - 1, by omega⟩ := by
        rw [hxc _ (by omega)]; congr 1; exact Fin.ext hsv
      have eb : x (i + 1) = e ⟨i.val + 1, hi1⟩ := by
        rw [hxc _ (by omega)]; congr 1; exact Fin.ext hav
      have ei : x i = e ⟨i.val, hilt⟩ := hxc i hilt
      rcases le_total (e ⟨i.val - 1, by omega⟩ 1) (e ⟨i.val + 1, hi1⟩ 1) with hm' | hm'
      · rw [max_eq_right hm'] at hcv
        have := hlt i (i + 1) (by rw [ei, eb]; exact hcv); linarith
      · rw [max_eq_left hm'] at hcv
        have := hlt i (i - 1) (by rw [ei, ea]; exact hcv); linarith
    have hx0 : x 0 = e ⟨0, by omega⟩ := by rw [hxc 0 (by simp; omega)]; congr 1
    have hxl1 : x (Fin.last m - 1) = e ⟨m - 1, by omega⟩ := by
      rw [hxc _ (by omega)]; congr 1; exact Fin.ext hsubl
    -- the end of `e` next to `p` is deeper than `p` if it is a local maximum
    have hA : d (0 - 1) < d 0 → ¬ e ⟨0, by omega⟩ 1 < p 1 := by
      intro h1 hc
      rw [hsub0] at h1
      have := hlt 0 (Fin.last m) (by rw [hx0, hxp]; exact hc); linarith
    have hB : ∀ i : Fin (m + 1), i.val = m - 1 → d (i + 1) < d i → ¬ e ⟨m - 1, by omega⟩ 1 < p 1 := by
      intro i hi h3 hc
      have hil : i + 1 = Fin.last m := Fin.ext (by
        rw [fin_val_add_one_of_lt i (by omega)]; simp; omega)
      have hxi : x i = e ⟨m - 1, by omega⟩ := by rw [hxc i (by omega)]; congr 1; exact Fin.ext hi
      rw [hil] at h3
      have := hlt i (Fin.last m) (by rw [hxi, hxp]; exact hc); linarith
    refine isCyclicUnimodal_of_atMostOne (k := m + 1) (by omega) hdinj ?_
    intro i j hi hj
    show (i : Fin (m + 1)) = j
    have ci := hclass i hi.1 hi.2
    have cj := hclass j hj.1 hj.2
    -- `p` and its neighbours exclude each other; the two ends exclude each other by `hdeep`
    have hp0 : d (0 - 1) < d 0 → d (Fin.last m) < d 0 := fun h => by rwa [hsub0] at h
    have hpl0 : d (Fin.last m + 1) < d (Fin.last m) → d 0 < d (Fin.last m) := fun h => by
      rwa [Fin.last_add_one] at h
    have hq1 : ∀ i : Fin (m + 1), i.val = m - 1 → d (i + 1) < d i → d (Fin.last m) < d i := by
      intro i hi h
      have hil : i + 1 = Fin.last m := Fin.ext (by
        rw [fin_val_add_one_of_lt i (by omega)]; simp; omega)
      rwa [hil] at h
    have hq2 : ∀ i : Fin (m + 1), i.val = m - 1 → d (Fin.last m - 1) < d (Fin.last m) →
        d i < d (Fin.last m) := by
      intro i hi h
      have : Fin.last m - 1 = i := Fin.ext (by rw [hsubl, hi])
      rwa [this] at h
    rcases ci with rfl | hi' | rfl <;> rcases cj with hj' | hj' | hj'
    · exact hj'.symm
    · exfalso
      have h1 := hA hi.1
      have h2 := hB j hj' hj.2
      rcases hdeep with h | h
      · exact h1 h
      · exact h2 h
    · exfalso; subst hj'
      have := hp0 hi.1; have := hpl0 hj.2; linarith
    · exfalso; subst hj'
      have h1 := hA hj.1
      have h2 := hB i hi' hi.2
      rcases hdeep with h | h
      · exact h1 h
      · exact h2 h
    · exact Fin.ext (by rw [hi', hj'])
    · exfalso; subst hj'
      have := hq1 i hi' hi.2; have := hq2 i hi' hj.1; linarith
    · exfalso; subst hj'
      have := hp0 hj.1; have := hpl0 hi.2; linarith
    · exfalso
      have := hq1 j hj' hj.2; have := hq2 j hj' hi.1; linarith
    · exact hj'.symm
  have hk : 3 ≤ m + 1 := by omega
  exact isRupert_of_tilted_unimodal' (k := m + 1) V ey v ey_ne_zero hk x hxV
    (fun i j hi hj => key i (x j) (hxV j) (hinj.ne hi) (hinj.ne hj))
    (fun y hy hyx i => key i y hy (hyx i) (hyx (i + 1)))
    (fun z => IsCyclicUnimodal z) isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz) hev (fun z _ hz => hz)

theorem det3_ey_mid (w v : ℝ³) : det3 w ey v = -w 2 * v 0 + w 0 * v 2 := by
  simp [det3, cross, ey, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- Points of the face with a common `x`: at most two (strict convex position). -/
theorem ConvPos.eq_of_same_x {S : Finset ℝ²} (hS : ConvPos S) {a b c : ℝ²} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a 0 = b 0) (hac : a 0 = c 0) :
    a = b ∨ a = c ∨ b = c := by
  by_contra hne
  push Not at hne
  apply hS.cross2_ne ha hb hc hne.1 hne.2.1 hne.2.2
  simp only [cross2, PiLp.sub_apply, ← hab, ← hac, sub_self, zero_mul, mul_zero]

/-- On or below the chord `AB` (with `A`, `B` the lowest points at the extreme
`x`), points have distinct `x`. -/
theorem ConvPos.injOn_below {S : Finset ℝ²} (hS : ConvPos S) {A B : ℝ²} (hA : A ∈ S)
    (hB : B ∈ S) (hAmin : ∀ y ∈ S, A 0 ≤ y 0) (hBmax : ∀ y ∈ S, y 0 ≤ B 0) (hAB : A 0 < B 0)
    (hAlow : ∀ y ∈ S, y 0 = A 0 → A 1 ≤ y 1) (hBlow : ∀ y ∈ S, y 0 = B 0 → B 1 ≤ y 1) :
    Set.InjOn (fun s : ℝ² => s 0) (S.filter fun s => cross2 (B - A) (s - A) ≤ 0) := by
  have key : ∀ a ∈ S, ∀ b ∈ S, cross2 (B - A) (b - A) ≤ 0 → a 0 = b 0 → a 1 < b 1 → False := by
    intro a ha b hb hbL hx hy
    have hbA : b ≠ A := by rintro rfl; have := hAlow a ha hx; linarith
    have hbB : b ≠ B := by rintro rfl; have := hBlow a ha hx; linarith
    have hba : b ≠ a := by rintro rfl; exact lt_irrefl _ hy
    apply hS.not_mem_hull4 hb ha ha hA hB hba hba hbA hbB
    -- the chord point over `a`
    have hd : 0 < B 0 - A 0 := by linarith
    set β := (a 0 - A 0) / (B 0 - A 0)
    have hβ0 : 0 ≤ β := div_nonneg (by linarith [hAmin a ha]) hd.le
    have hβ1 : β ≤ 1 := (div_le_one hd).mpr (by linarith [hBmax a ha])
    set P2 := A + β • (B - A)
    have hC : Convex ℝ (convexHull ℝ ({a, a, A, B} : Set ℝ²)) := convex_convexHull ℝ _
    have hP2 : P2 ∈ convexHull ℝ ({a, a, A, B} : Set ℝ²) :=
      hC.segment_subset (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
        (segment_pt_mem hβ0 hβ1)
    have hx2 : P2 0 = b 0 := by
      simp only [P2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, β]
      field_simp; rw [← hx]; ring
    have hy2 : b 1 ≤ P2 1 := by
      simp only [cross2, PiLp.sub_apply] at hbL
      simp only [P2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, β]
      rw [div_mul_eq_mul_div, add_div' _ _ _ hd.ne', le_div_iff₀ hd, hx]
      nlinarith
    have hPa : P2 1 - a 1 ≠ 0 := by linarith
    set γ := (b 1 - a 1) / (P2 1 - a 1)
    have hγ0 : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
    have hγ1 : γ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have : b = a + γ • (P2 - a) := by
      ext i; fin_cases i
      · show b 0 = a 0 + γ * (P2 0 - a 0); rw [hx2, hx]; ring
      · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, γ]
        field_simp; ring
    rw [this]
    exact hC.segment_subset (subset_convexHull ℝ _ (by simp)) hP2 (segment_pt_mem hγ0 hγ1)
  intro s hs s' hs' he
  simp only [coe_filter, Set.mem_ofPred_eq] at hs hs'
  simp only at he
  by_contra hne
  rcases lt_trichotomy (s 1) (s' 1) with h | h | h
  · exact key s hs.1 s' hs'.1 hs'.2 he h
  · exact hne (by ext i; fin_cases i <;> simp [he, h])
  · exact key s' hs'.1 s hs.1 hs.2 he.symm h

theorem det3_gen (a b v : ℝ³) : det3 a b v =
    (a 1 * b 2 - a 2 * b 1) * v 0 + (a 2 * b 0 - a 0 * b 2) * v 1 + (a 0 * b 1 - a 1 * b 0) * v 2 := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-! ### Determinant tests at the view `ey` with the tilt `v = (v₀, 0, 1)` -/

/-- A chain edge of the face (`x` increasing). -/
theorem tiltSign_chain {h : ℝ} {c c' y v : ℝ³} (hc : c 2 = h) (hc' : c' 2 = h)
    (hcc' : c 0 < c' 0) (hv2 : v 2 = 1) (hyh : y 2 ≤ h)
    (hcr : y 2 = h → 0 < (c' 0 - c 0) * (y 1 - c 1) - (c' 1 - c 1) * (y 0 - c 0)) :
    TiltSign (c' - c) (y - c) ey v := by
  rcases eq_or_lt_of_le hyh with hyh | hyh
  · right
    refine ⟨?_, ?_⟩
    · rw [det3_ey]; simp only [PiLp.sub_apply, hc, hc', hyh]; ring
    · rw [det3_gen]; simp only [PiLp.sub_apply, hc, hc', hyh, hv2]
      have := hcr hyh; nlinarith
  · left; rw [det3_ey]; simp only [PiLp.sub_apply, hc, hc']
    have : 0 < c' 0 - c 0 := by linarith
    nlinarith

/-- The vertical edge `atop → alo` over the `x`-minimal end. -/
theorem tiltSign_vertA {h : ℝ} {atop alo y v : ℝ³} (hx : alo 0 = atop 0) (hz : alo 2 = h)
    (hz' : atop 2 = h) (hlt : alo 1 < atop 1) (hv1 : v 1 = 0) (hv2 : v 2 = 1)
    (hy : 0 < (y 0 - atop 0) - (y 2 - h) * v 0) : TiltSign (alo - atop) (y - atop) ey v := by
  right
  refine ⟨?_, ?_⟩
  · rw [det3_ey]; simp only [PiLp.sub_apply, hx, hz, hz']; ring
  · rw [det3_gen]; simp only [PiLp.sub_apply, hx, hz, hz', hv1, hv2]
    have : 0 < atop 1 - alo 1 := by linarith
    nlinarith

/-- The vertical edge `blo → btop` over the `x`-maximal end. -/
theorem tiltSign_vertB {h : ℝ} {blo btop y v : ℝ³} (hx : btop 0 = blo 0) (hz : btop 2 = h)
    (hz' : blo 2 = h) (hlt : blo 1 < btop 1) (hv1 : v 1 = 0) (hv2 : v 2 = 1)
    (hy : 0 < (y 2 - h) * v 0 - (y 0 - blo 0)) : TiltSign (btop - blo) (y - blo) ey v := by
  right
  refine ⟨?_, ?_⟩
  · rw [det3_ey]; simp only [PiLp.sub_apply, hx, hz, hz']; ring
  · rw [det3_gen]; simp only [PiLp.sub_apply, hx, hz, hz', hv1, hv2]
    have : 0 < btop 1 - blo 1 := by linarith
    nlinarith

/-- The edge `btop → p`. -/
theorem tiltSign_Bp {h : ℝ} {btop p y v : ℝ³} (hz : btop 2 = h) (hph : p 2 < h)
    (hv1 : v 1 = 0) (hv2 : v 2 = 1) (hCB : 0 < (p 2 - h) * v 0 + (btop 0 - p 0))
    (hy : (y 2 = h ∧ y 0 < btop 0) ∨ (y 2 = h ∧ y 0 = btop 0 ∧ y 1 < btop 1) ∨
      (∃ lam : ℝ, 0 < lam ∧ y = p - lam • ey)) : TiltSign (p - btop) (y - btop) ey v := by
  rcases hy with ⟨hyh, hyx⟩ | ⟨hyh, hyx, hyy⟩ | ⟨lam, hlam, rfl⟩
  · left; rw [det3_ey]; simp only [PiLp.sub_apply, hz, hyh]
    nlinarith
  · right
    refine ⟨?_, ?_⟩
    · rw [det3_ey]; simp only [PiLp.sub_apply, hz, hyh, hyx]; ring
    · rw [det3_gen]; simp only [PiLp.sub_apply, hz, hyh, hyx, hv1, hv2]
      have : 0 < btop 1 - y 1 := by linarith
      nlinarith
  · right
    refine ⟨?_, ?_⟩
    · rw [det3_ey]; simp [ey]; try ring
    · rw [det3_gen]; simp [ey, hv1, hv2, hz]; nlinarith [mul_pos hlam hCB]

/-- The edge `p → atop`. -/
theorem tiltSign_pA {h : ℝ} {atop p y v : ℝ³} (hz : atop 2 = h) (hph : p 2 < h)
    (hv1 : v 1 = 0) (hv2 : v 2 = 1) (hCA : 0 < (h - p 2) * v 0 + (p 0 - atop 0))
    (hy : (y 2 = h ∧ atop 0 < y 0) ∨ (y 2 = h ∧ y 0 = atop 0 ∧ y 1 < atop 1) ∨
      (∃ lam : ℝ, 0 < lam ∧ y = p - lam • ey)) : TiltSign (atop - p) (y - p) ey v := by
  rcases hy with ⟨hyh, hyx⟩ | ⟨hyh, hyx, hyy⟩ | ⟨lam, hlam, rfl⟩
  · left; rw [det3_ey]; simp only [PiLp.sub_apply, hz, hyh]
    nlinarith
  · right
    refine ⟨?_, ?_⟩
    · rw [det3_ey]; simp only [PiLp.sub_apply, hz, hyh, hyx]; ring
    · rw [det3_gen]; simp only [PiLp.sub_apply, hz, hyh, hyx, hv1, hv2]
      have : 0 < atop 1 - y 1 := by linarith
      nlinarith
  · right
    refine ⟨?_, ?_⟩
    · rw [det3_ey]; simp [ey]; try ring
    · rw [det3_gen]; simp [ey, hv1, hv2, hz]; nlinarith [mul_pos hlam hCA]

set_option maxHeartbeats 1000000 in
/-- **Case II at the view along `pq`** (standard frame: the view is `ey`, `q`
is directly behind `p`).  If `p` is deeper than the top point at one `x`-end
of the face, the tilt `ey + ε v` with `v = (v₀, 0, 1)` for a suitable `v₀`
shows the face's lower chain (with the top points at the ends) and `p`, hiding
`q`; this is unimodal. -/
theorem isRupert_caseII_view (V : Finset ℝ³) (h : ℝ) (p q : ℝ³) {lam : ℝ} (hlam : 0 < lam)
    (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ3 : 2 < (V.filter fun y => y 2 = h).card)
    (hp : p ∈ V) (hph : p 2 < h) (hq : q ∈ V) (hqp : q = p - lam • ey)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q)
    (hdeep : (∀ y ∈ V, y 2 = h → (∀ z ∈ V, z 2 = h → y 0 ≤ z 0) → y 1 < p 1) ∨
      (∀ y ∈ V, y 2 = h → (∀ z ∈ V, z 2 = h → z 0 ≤ y 0) → y 1 < p 1)) : IsRupert V := by
  classical
  set Q := V.filter fun y => y 2 = h with hQ
  set S := Q.image proj_xy with hS
  have hQV : ∀ y ∈ Q, y ∈ V ∧ y 2 = h := fun y hy => mem_filter.mp hy
  have hQne : Q.Nonempty := card_pos.mp (by omega)
  -- the `x`-extremes and the lowest / top points over them
  obtain ⟨A', hA'Q, hA'min⟩ := Q.exists_min_image (fun y : ℝ³ => y 0) hQne
  obtain ⟨B', hB'Q, hB'max⟩ := Q.exists_max_image (fun y : ℝ³ => y 0) hQne
  set QA := Q.filter fun y => y 0 = A' 0 with hQA
  set QB := Q.filter fun y => y 0 = B' 0 with hQB
  have hQAne : QA.Nonempty := ⟨A', mem_filter.mpr ⟨hA'Q, rfl⟩⟩
  have hQBne : QB.Nonempty := ⟨B', mem_filter.mpr ⟨hB'Q, rfl⟩⟩
  obtain ⟨alo, haloA, halomin⟩ := QA.exists_min_image (fun y : ℝ³ => y 1) hQAne
  obtain ⟨atop, hatopA, hatopmax⟩ := QA.exists_max_image (fun y : ℝ³ => y 1) hQAne
  obtain ⟨blo, hbloB, hblomin⟩ := QB.exists_min_image (fun y : ℝ³ => y 1) hQBne
  obtain ⟨btop, hbtopB, hbtopmax⟩ := QB.exists_max_image (fun y : ℝ³ => y 1) hQBne
  have hprojinj : ∀ y ∈ Q, ∀ y' ∈ Q, proj_xy y = proj_xy y' → y = y' := by
    intro y hy y' hy' he
    rw [← liftPt_proj (hQV y hy).2, ← liftPt_proj (hQV y' hy').2, he]
  have hmemA : ∀ y ∈ QA, y ∈ Q ∧ y 0 = A' 0 := fun y hy => mem_filter.mp hy
  have hmemB : ∀ y ∈ QB, y ∈ Q ∧ y 0 = B' 0 := fun y hy => mem_filter.mp hy
  set A0 := A' 0
  set B0 := B' 0
  obtain ⟨haloQ, halox⟩ := hmemA alo haloA
  obtain ⟨hatopQ, hatopx⟩ := hmemA atop hatopA
  obtain ⟨hbloQ, hblox⟩ := hmemB blo hbloB
  obtain ⟨hbtopQ, hbtopx⟩ := hmemB btop hbtopB
  -- at most two points over each end, and they are `lo`, `top`
  have hendA : ∀ y ∈ Q, y 0 = A0 → y = alo ∨ y = atop := by
    intro y hy hyx
    rcases hconv.eq_of_same_x (mem_image_of_mem _ haloQ) (mem_image_of_mem _ hatopQ)
      (mem_image_of_mem _ hy) (by simp [proj_xy, halox, hatopx]) (by simp [proj_xy, halox, hyx])
      with e | e | e
    · have h1 := halomin y (mem_filter.mpr ⟨hy, hyx⟩)
      have h2 := hatopmax y (mem_filter.mpr ⟨hy, hyx⟩)
      have e' := hprojinj _ haloQ _ hatopQ e
      rw [← e'] at h2
      left; apply hprojinj _ hy _ haloQ
      ext i; fin_cases i
      · simp [proj_xy, hyx, halox]
      · simp [proj_xy]; linarith
    · left; exact (hprojinj _ haloQ _ hy e).symm
    · right; exact (hprojinj _ hatopQ _ hy e).symm
  have hendB : ∀ y ∈ Q, y 0 = B0 → y = blo ∨ y = btop := by
    intro y hy hyx
    rcases hconv.eq_of_same_x (mem_image_of_mem _ hbloQ) (mem_image_of_mem _ hbtopQ)
      (mem_image_of_mem _ hy) (by simp [proj_xy, hblox, hbtopx]) (by simp [proj_xy, hblox, hyx])
      with e | e | e
    · have h1 := hblomin y (mem_filter.mpr ⟨hy, hyx⟩)
      have h2 := hbtopmax y (mem_filter.mpr ⟨hy, hyx⟩)
      have e' := hprojinj _ hbloQ _ hbtopQ e
      rw [← e'] at h2
      left; apply hprojinj _ hy _ hbloQ
      ext i; fin_cases i
      · simp [proj_xy, hyx, hblox]
      · simp [proj_xy]; linarith
    · left; exact (hprojinj _ hbloQ _ hy e).symm
    · right; exact (hprojinj _ hbtopQ _ hy e).symm
  have hAB : A0 < B0 := by
    rcases lt_or_eq_of_le (hA'min B' hB'Q) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨y1, hy1, y2, hy2, y3, hy3, h12, h13, h23⟩ := two_lt_card.mp hQ3
      have hx : ∀ y ∈ Q, y 0 = A0 := fun y hy =>
        le_antisymm (by rw [h']; exact hB'max y hy) (hA'min y hy)
      rcases hendA y1 hy1 (hx y1 hy1) with e1 | e1 <;> rcases hendA y2 hy2 (hx y2 hy2) with e2 | e2 <;>
        rcases hendA y3 hy3 (hx y3 hy3) with e3 | e3 <;>
        first | exact h12 (e1.trans e2.symm) | exact h13 (e1.trans e3.symm) |
          exact h23 (e2.trans e3.symm)
  -- the plane picture
  have hSmin : ∀ y ∈ S, (proj_xy alo) 0 ≤ y 0 := by
    intro y hy; obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    simp only [proj_xy]; simp [halox]; exact hA'min z hz
  have hSmax : ∀ y ∈ S, y 0 ≤ (proj_xy blo) 0 := by
    intro y hy; obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    simp only [proj_xy]; simp [hblox]; exact hB'max z hz
  have hSAB : (proj_xy alo) 0 < (proj_xy blo) 0 := by simp [proj_xy, halox, hblox]; exact hAB
  have hSAlow : ∀ y ∈ S, y 0 = (proj_xy alo) 0 → (proj_xy alo) 1 ≤ y 1 := by
    intro y hy hyx; obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    simp [proj_xy, halox] at hyx ⊢; exact halomin z (mem_filter.mpr ⟨hz, hyx⟩)
  have hSBlow : ∀ y ∈ S, y 0 = (proj_xy blo) 0 → (proj_xy blo) 1 ≤ y 1 := by
    intro y hy hyx; obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    simp [proj_xy, hblox] at hyx ⊢; exact hblomin z (mem_filter.mpr ⟨hz, hyx⟩)
  have hLinj := hconv.injOn_below (mem_image_of_mem _ haloQ) (mem_image_of_mem _ hbloQ) hSmin hSmax
    hSAB hSAlow hSBlow
  obtain ⟨n, c, h2, hc0, hcn, hcS, hcL, hcmono, hcons⟩ :=
    exists_lowerChain' hLinj (mem_image_of_mem _ haloQ) (mem_image_of_mem _ hbloQ) hSmin hSmax hSAB
  -- a chain point is the lowest point of `S` over it
  have hclow : ∀ i : Fin n, ∀ y ∈ S, y ≠ c i → y 0 = c i 0 → c i 1 < y 1 := by
    intro i y hy hne hx
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with e | hlt
    · exact hne (by ext j; fin_cases j <;> simp [hx, e])
    · -- `y` is below `c i`, hence below the chord, contradicting distinct `x` below it
      have hyL : cross2 (proj_xy blo - proj_xy alo) (y - proj_xy alo) ≤ 0 := by
        have hd : 0 < (proj_xy blo) 0 - (proj_xy alo) 0 := by linarith
        have e : cross2 (proj_xy blo - proj_xy alo) (y - proj_xy alo) =
            cross2 (proj_xy blo - proj_xy alo) (c i - proj_xy alo) +
              ((proj_xy blo) 0 - (proj_xy alo) 0) * (y 1 - c i 1) := by
          simp only [cross2, PiLp.sub_apply]; rw [hx]; ring
        rw [e]; nlinarith [hcL i, mul_pos hd (sub_pos.mpr hlt)]
      exact hne (hLinj (mem_filter.mpr ⟨hy, hyL⟩) (mem_filter.mpr ⟨hcS i, hcL i⟩) hx)
  -- the tilt `v = (v₀, 0, 1)`
  have hhp : 0 < h - p 2 := by linarith
  set lo := -(p 0 - A0) / (h - p 2)
  set hi := (B0 - p 0) / (h - p 2)
  have hlohi : lo < hi := by
    simp only [lo, hi]; rw [div_lt_div_iff_of_pos_right hhp]; linarith
  set badv := ⋃ ab ∈ V ×ˢ V, {t : ℝ | ab.1 0 ≠ ab.2 0 ∧ t * (ab.1 0 - ab.2 0) + (ab.1 2 - ab.2 2) = 0}
    with hbadv
  have hbadvfin : badv.Finite := by
    refine Set.Finite.biUnion (V ×ˢ V).finite_toSet fun ab _ => ?_
    by_cases hne : ab.1 0 ≠ ab.2 0
    · refine (Set.finite_singleton (-(ab.1 2 - ab.2 2) / (ab.1 0 - ab.2 0))).subset ?_
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht
      simp only [Set.mem_singleton_iff]
      have := sub_ne_zero.mpr hne
      field_simp; linarith [ht.2]
    · exact (Set.finite_empty).subset fun t ht => absurd ht.1 hne
  obtain ⟨v0, ⟨hv0I, hv0B⟩⟩ := ((Set.Ioo_infinite hlohi).sdiff hbadvfin).nonempty
  have hCA : 0 < (h - p 2) * v0 + (p 0 - A0) := by
    have := hv0I.1; simp only [lo] at this; rw [div_lt_iff₀ hhp] at this; linarith
  have hCB : 0 < (p 2 - h) * v0 + (B0 - p 0) := by
    have := hv0I.2; simp only [hi] at this; rw [lt_div_iff₀ hhp] at this; linarith
  set v : ℝ³ := !₂[v0, 0, 1] with hv
  have hv0' : v 0 = v0 := by simp [hv]
  have hv1 : v 1 = 0 := by simp [hv]
  have hv2 : v 2 = 1 := by simp [hv]
  -- separation of distinct points by depth or by `v`
  have hsepV : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → a 1 ≠ b 1 ∨ ⟪a - b, v⟫ ≠ 0 := by
    intro a ha b hb hab
    by_cases h1 : a 1 = b 1
    · right
      have hin : ⟪a - b, v⟫ = (a 0 - b 0) * v0 + (a 2 - b 2) := by
        simp [hv, PiLp.inner_apply, Fin.sum_univ_three]; ring
      rw [hin]
      by_cases h0 : a 0 = b 0
      · have h2 : a 2 ≠ b 2 := by
          intro h2; apply hab; ext i; fin_cases i
          · exact h0
          · exact h1
          · exact h2
        rw [h0, sub_self, zero_mul, zero_add]; exact sub_ne_zero.mpr h2
      · intro h0'
        apply hv0B
        simp only [hbadv, Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨(a, b), mem_product.mpr ⟨ha, hb⟩, h0, by simp only; linarith⟩
    · left; exact h1
  -- the chain in space
  set c3 : Fin n → ℝ³ := fun i => liftPt (c i) h with hc3
  have hc3Q : ∀ i, c3 i ∈ Q := by
    intro i
    obtain ⟨y, hy, hyc⟩ := mem_image.mp (hcS i)
    have : c3 i = y := by rw [hc3]; simp only; rw [← hyc]; exact liftPt_proj (hQV y hy).2
    rw [this]; exact hy
  have hc3z : ∀ i, c3 i 2 = h := fun i => by simp [hc3, liftPt]
  have hc3x : ∀ i, c3 i 0 = c i 0 := fun i => by simp [hc3, liftPt]
  have hc3y : ∀ i, c3 i 1 = c i 1 := fun i => by simp [hc3, liftPt]
  have hc30 : c3 ⟨0, by omega⟩ = alo := by simp only [hc3, hc0]; exact liftPt_proj (hQV _ haloQ).2
  have hc3n : c3 ⟨n - 1, by omega⟩ = blo := by
    simp only [hc3, hcn]; exact liftPt_proj (hQV _ hbloQ).2
  have hcinj : ∀ i j : Fin n, c i = c j → i = j := by
    intro i j hij; by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := hcmono i j hl; rw [hij] at this; exact lt_irrefl _ this
    · have := hcmono j i hl; rw [hij] at this; exact lt_irrefl _ this
  -- coordinates of the ends
  have hQz : ∀ y ∈ Q, y 2 = h := fun y hy => (hQV y hy).2
  have hQx : ∀ y ∈ Q, A0 ≤ y 0 ∧ y 0 ≤ B0 := fun y hy => ⟨hA'min y hy, hB'max y hy⟩
  have hAlt : atop ≠ alo → alo 1 < atop 1 := by
    intro hne
    refine lt_of_le_of_ne (halomin atop hatopA) fun e' => hne ?_
    apply hprojinj _ hatopQ _ haloQ; ext i; fin_cases i
    · simp [proj_xy, halox, hatopx]
    · simp [proj_xy, e']
  have hBlt : btop ≠ blo → blo 1 < btop 1 := by
    intro hne
    refine lt_of_le_of_ne (hblomin btop hbtopB) fun e' => hne ?_
    apply hprojinj _ hbtopQ _ hbloQ; ext i; fin_cases i
    · simp [proj_xy, hblox, hbtopx]
    · simp [proj_xy, e']
  have hqx0 : q 0 = p 0 := by rw [hqp]; simp [ey]
  have hqx2 : q 2 = p 2 := by rw [hqp]; simp [ey]
  -- the points below the face are `p` and `q`, with the same `x` and `z`
  have hbelow : ∀ y ∈ V, y 2 < h → y 0 = p 0 ∧ y 2 = p 2 := by
    intro y hy hyh
    rcases hrest y hy hyh with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact ⟨hqx0, hqx2⟩
  have hfaceQ : ∀ y ∈ V, y 2 = h → y ∈ Q := fun y hy hyh => mem_filter.mpr ⟨hy, hyh⟩
  -- the extended chain: `atop`, the lower chain, `btop`
  set kA : ℕ := if atop = alo then 0 else 1 with hkA
  set kB : ℕ := if btop = blo then 0 else 1 with hkB
  have hkA1 : kA ≤ 1 := by simp only [hkA]; split_ifs <;> omega
  have hkB1 : kB ≤ 1 := by simp only [hkB]; split_ifs <;> omega
  have hkA0 : kA = 0 → atop = alo := by
    intro h0; by_contra hne; simp [hkA, hne] at h0
  have hkB0 : kB = 0 → btop = blo := by
    intro h0; by_contra hne; simp [hkB, hne] at h0
  have hkA1' : kA = 1 → atop ≠ alo := by
    intro h1 hh; simp [hkA, hh] at h1
  have hkB1' : kB = 1 → btop ≠ blo := by
    intro h1 hh; simp [hkB, hh] at h1
  set m := kA + n + kB with hm
  set e : Fin m → ℝ³ := fun i => if i.val < kA then atop else
    if hi : i.val - kA < n then c3 ⟨i.val - kA, hi⟩ else btop with he
  have heA : ∀ i : Fin m, i.val < kA → e i = atop := fun i hi => by simp [he, hi]
  have heC : ∀ i : Fin m, kA ≤ i.val → ∀ hi : i.val - kA < n, e i = c3 ⟨i.val - kA, hi⟩ :=
    fun i h1 hi => by simp [he, hi, not_lt.mpr h1]
  have heB : ∀ i : Fin m, kA + n ≤ i.val → e i = btop := fun i hi => by
    simp [he, show ¬ i.val < kA by omega, show ¬ i.val - kA < n by omega]
  have he0 : e ⟨0, by omega⟩ = atop := by
    rcases Nat.eq_zero_or_pos kA with h0 | h0
    · rw [heC _ (by simp [h0]) (by simp [h0]; omega)]
      have : c3 ⟨(⟨0, by omega⟩ : Fin m).val - kA, by simp [h0]; omega⟩ = c3 ⟨0, by omega⟩ := by
        congr 1; ext; simp [h0]
      exact (this.trans hc30).trans (hkA0 h0).symm
    · exact heA _ (by simpa using h0)
  have helast : e ⟨m - 1, by omega⟩ = btop := by
    rcases Nat.eq_zero_or_pos kB with h0 | h0
    · rw [heC _ (by simp; omega) (by simp; omega)]
      have : c3 ⟨(⟨m - 1, by omega⟩ : Fin m).val - kA, by simp; omega⟩ = c3 ⟨n - 1, by omega⟩ := by
        congr 1; ext; simp; omega
      exact (this.trans hc3n).trans (hkB0 h0).symm
    · exact heB _ (by simp; omega)
  have heV : ∀ i, e i ∈ V := fun i => by
    by_cases h1 : i.val < kA
    · rw [heA i h1]; exact (hQV _ hatopQ).1
    · by_cases h2 : i.val - kA < n
      · rw [heC i (by omega) h2]; exact (hQV _ (hc3Q _)).1
      · rw [heB i (by omega)]; exact (hQV _ hbtopQ).1
  have heQ : ∀ i, e i ∈ Q := fun i => hfaceQ _ (heV i) (by
    by_cases h1 : i.val < kA
    · rw [heA i h1]; exact hQz _ hatopQ
    · by_cases h2 : i.val - kA < n
      · rw [heC i (by omega) h2]; exact hc3z _
      · rw [heB i (by omega)]; exact hQz _ hbtopQ)
  have hc0x : c ⟨0, by omega⟩ 0 = A0 := by rw [hc0]; simp [proj_xy, halox]
  have hcnx : c ⟨n - 1, by omega⟩ 0 = B0 := by rw [hcn]; simp [proj_xy, hblox]
  -- face points other than the ends have `A0 < x < B0`
  have hmidA : ∀ y ∈ Q, y ≠ alo → y ≠ atop → A0 < y 0 := fun y hy h1 h2 =>
    lt_of_le_of_ne (hQx y hy).1 fun e' => (hendA y hy e'.symm).elim h1 h2
  have hmidB : ∀ y ∈ Q, y ≠ blo → y ≠ btop → y 0 < B0 := fun y hy h1 h2 =>
    lt_of_le_of_ne (hQx y hy).2 fun e' => (hendB y hy e').elim h1 h2
  -- the chain edges, through the plane picture
  have hchain : ∀ j : Fin n, ∀ hj : j.val + 1 < n, ∀ y ∈ V, y ≠ c3 j → y ≠ c3 ⟨j.val + 1, hj⟩ →
      TiltSign (c3 ⟨j.val + 1, hj⟩ - c3 j) (y - c3 j) ey v := by
    intro j hj y hy hy1 hy2
    have hjj : j < ⟨j.val + 1, hj⟩ := Fin.lt_def.mpr (by simp)
    refine tiltSign_chain (hc3z _) (hc3z _) (by rw [hc3x, hc3x]; exact hcmono _ _ hjj) hv2
      (hV y hy) fun hyh => ?_
    have hyS : proj_xy y ∈ S := mem_image_of_mem _ (hfaceQ y hy hyh)
    have hne1 : proj_xy y ≠ c j := fun e' => hy1 (by rw [← liftPt_proj hyh, e'])
    have hne2 : proj_xy y ≠ c ⟨j.val + 1, hj⟩ := fun e' => hy2 (by rw [← liftPt_proj hyh, e'])
    have := cross2_pos_of_consecutive' hconv (mem_image_of_mem _ haloQ) (mem_image_of_mem _ hbloQ)
      hSmin hSmax hSAB (hcS j) (hcS _) (hcmono _ _ hjj) (hcL j) (hcL _) (hcons j hj) (hclow j)
      (hclow _) hyS hne1 hne2
    simp only [cross2, PiLp.sub_apply] at this
    simpa [proj_xy, hc3x, hc3y] using this
  have hE : ∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ y ∈ V, y ≠ e i → y ≠ e ⟨i.val + 1, hi⟩ →
      TiltSign (e ⟨i.val + 1, hi⟩ - e i) (y - e i) ey v := by
    intro i hi y hy hy1 hy2
    by_cases h1 : i.val < kA
    · -- the vertical edge `atop → alo`
      have hk : kA = 1 := by omega
      have hi0 : i.val = 0 := by omega
      have e1 : e ⟨i.val + 1, hi⟩ = alo :=
        (heC ⟨i.val + 1, hi⟩ (by simp; omega) (by simp; omega)).trans
          ((congrArg c3 (Fin.ext (by simp; omega))).trans hc30)
      rw [heA i h1] at hy1; rw [e1] at hy2; rw [heA i h1, e1]
      refine tiltSign_vertA (by rw [halox, hatopx]) (hQz _ haloQ) (hQz _ hatopQ)
        (hAlt (hkA1' hk)) hv1 hv2 ?_
      rcases eq_or_lt_of_le (hV y hy) with hyh | hyh
      · rw [hyh, sub_self, zero_mul, sub_zero, hatopx]
        exact sub_pos.mpr (hmidA y (hfaceQ y hy hyh) hy2 hy1)
      · obtain ⟨hx0, hx2⟩ := hbelow y hy hyh
        rw [hx0, hx2, hatopx, hv0']; nlinarith [hCA]
    · by_cases h2 : i.val + 1 - kA < n
      · -- a chain edge
        have hj : i.val - kA + 1 < n := by omega
        have e0 : e i = c3 ⟨i.val - kA, by omega⟩ := heC i (by omega) (by omega)
        have e1 : e ⟨i.val + 1, hi⟩ = c3 ⟨i.val - kA + 1, hj⟩ :=
          (heC ⟨i.val + 1, hi⟩ (by simp; omega) (by simp; omega)).trans
            (congrArg c3 (Fin.ext (by simp; omega)))
        rw [e0] at hy1; rw [e1] at hy2; rw [e0, e1]
        exact hchain ⟨i.val - kA, by omega⟩ hj y hy hy1 hy2
      · -- the vertical edge `blo → btop`
        have hk : kB = 1 := by omega
        have e0 : e i = blo :=
          (heC i (by omega) (by omega)).trans ((congrArg c3 (Fin.ext (by simp; omega))).trans hc3n)
        have e1 : e ⟨i.val + 1, hi⟩ = btop := heB _ (by simp; omega)
        rw [e0] at hy1; rw [e1] at hy2; rw [e0, e1]
        refine tiltSign_vertB (by rw [hblox, hbtopx]) (hQz _ hbtopQ) (hQz _ hbloQ)
          (hBlt (hkB1' hk)) hv1 hv2 ?_
        rcases eq_or_lt_of_le (hV y hy) with hyh | hyh
        · rw [hyh, sub_self, zero_mul, zero_sub, hblox]
          have := hmidB y (hfaceQ y hy hyh) hy1 hy2; linarith
        · obtain ⟨hx0, hx2⟩ := hbelow y hy hyh
          rw [hx0, hx2, hblox, hv0']; nlinarith [hCB]
  have hEp : ∀ y ∈ V, y ≠ e ⟨m - 1, by omega⟩ → y ≠ p →
      TiltSign (p - e ⟨m - 1, by omega⟩) (y - e ⟨m - 1, by omega⟩) ey v := by
    intro y hy hy1 hy2
    rw [helast] at hy1 ⊢
    refine tiltSign_Bp (hQz _ hbtopQ) hph hv1 hv2 (by rw [hbtopx]; exact hCB) ?_
    rcases eq_or_lt_of_le (hV y hy) with hyh | hyh
    · rcases lt_or_eq_of_le (hQx y (hfaceQ y hy hyh)).2 with hx | hx
      · exact Or.inl ⟨hyh, by rw [hbtopx]; exact hx⟩
      · right; left
        have hyb : y = blo := (hendB y (hfaceQ y hy hyh) hx).resolve_right hy1
        refine ⟨hyh, by rw [hx, hbtopx], ?_⟩
        rw [hyb]; exact hBlt (by rintro rfl; exact hy1 hyb)
    · right; right
      rcases hrest y hy hyh with rfl | rfl
      · exact absurd rfl hy2
      · exact ⟨lam, hlam, hqp⟩
  have hpE : ∀ y ∈ V, y ≠ p → y ≠ e ⟨0, by omega⟩ →
      TiltSign (e ⟨0, by omega⟩ - p) (y - p) ey v := by
    intro y hy hy1 hy2
    rw [he0] at hy2 ⊢
    refine tiltSign_pA (hQz _ hatopQ) hph hv1 hv2 (by rw [hatopx]; exact hCA) ?_
    rcases eq_or_lt_of_le (hV y hy) with hyh | hyh
    · rcases lt_or_eq_of_le (hQx y (hfaceQ y hy hyh)).1 with hx | hx
      · exact Or.inl ⟨hyh, by rw [hatopx]; exact hx⟩
      · right; left
        have hya : y = alo := (hendA y (hfaceQ y hy hyh) hx.symm).resolve_right hy2
        refine ⟨hyh, by rw [← hx, hatopx], ?_⟩
        rw [hya]; exact hAlt (by rintro rfl; exact hy2 hya)
    · right; right
      rcases hrest y hy hyh with rfl | rfl
      · exact absurd rfl hy1
      · exact ⟨lam, hlam, hqp⟩
  -- convexity at the interior points
  have hconvex : ∀ i : Fin m, ∀ (h0 : 0 < i.val) (h1 : i.val + 1 < m),
      e i 1 < max (e ⟨i.val - 1, by have := i.isLt; omega⟩ 1) (e ⟨i.val + 1, h1⟩ 1) := by
    intro i h0 h1
    have hj : i.val - kA < n := by omega
    have ei : e i = c3 ⟨i.val - kA, hj⟩ := heC i (by omega) hj
    rw [ei]
    by_cases hj0 : i.val - kA = 0
    · -- next to `atop`
      have hk : kA = 1 := by omega
      have em : e ⟨i.val - 1, by have := i.isLt; omega⟩ = atop := heA _ (by simp; omega)
      have ec : c3 ⟨i.val - kA, hj⟩ = alo := (congrArg c3 (Fin.ext (by simp [hj0]))).trans hc30
      rw [em, ec]; exact lt_max_of_lt_left (hAlt (hkA1' hk))
    · by_cases hjn : i.val - kA = n - 1
      · -- next to `btop`
        have hk : kB = 1 := by omega
        have ep : e ⟨i.val + 1, h1⟩ = btop := heB _ (by simp; omega)
        have ec : c3 ⟨i.val - kA, hj⟩ = blo := (congrArg c3 (Fin.ext (by simp [hjn]))).trans hc3n
        rw [ep, ec]; exact lt_max_of_lt_right (hBlt (hkB1' hk))
      · -- inside the chain
        have em : e ⟨i.val - 1, by have := i.isLt; omega⟩ = c3 ⟨i.val - kA - 1, by omega⟩ :=
          (heC _ (by simp; omega) (by simp; omega)).trans (congrArg c3 (Fin.ext (by simp; omega)))
        have ep : e ⟨i.val + 1, h1⟩ = c3 ⟨i.val - kA + 1, by omega⟩ :=
          (heC _ (by simp; omega) (by simp; omega)).trans (congrArg c3 (Fin.ext (by simp; omega)))
        rw [em, ep, hc3y, hc3y, hc3y]
        set a : Fin n := ⟨i.val - kA - 1, by omega⟩
        set b : Fin n := ⟨i.val - kA, hj⟩
        set b' : Fin n := ⟨i.val - kA + 1, by omega⟩
        have hab : a < b := Fin.lt_def.mpr (show i.val - kA - 1 < i.val - kA by omega)
        have hbb' : b < b' := Fin.lt_def.mpr (show i.val - kA < i.val - kA + 1 by omega)
        have hconsab : ∀ y ∈ S, c a 0 < y 0 → y 0 < c b 0 →
            0 < cross2 (proj_xy blo - proj_xy alo) (y - proj_xy alo) := by
          have := hcons a (by simp [a]; omega)
          have eb : (⟨a.val + 1, by simp [a]; omega⟩ : Fin n) = b := Fin.ext (by simp [a, b]; omega)
          rwa [eb] at this
        have hpos := cross2_pos_of_consecutive' hconv (mem_image_of_mem _ haloQ)
          (mem_image_of_mem _ hbloQ) hSmin hSmax hSAB (hcS a) (hcS b) (hcmono a b hab) (hcL a)
          (hcL b) hconsab (hclow a) (hclow b) (hcS b')
          (fun e' => absurd (hcinj _ _ e') (ne_of_gt (hab.trans hbb')))
          (fun e' => absurd (hcinj _ _ e') (ne_of_gt hbb'))
        exact y_lt_max_of_cross2 (hcmono a b hab) (hcmono b b' hbb') hpos
  -- the cycle is injective
  have hc3A : ∀ j : Fin n, c3 j 0 = A0 → c3 j = alo := by
    intro j hj
    have : j = ⟨0, by omega⟩ := by
      by_contra hne
      have hlt : (⟨0, by omega⟩ : Fin n) < j := lt_of_le_of_ne (Fin.le_def.mpr (Nat.zero_le _))
        (Ne.symm hne)
      have := hcmono _ _ hlt; rw [hc0x, ← hc3x, hj] at this; exact lt_irrefl _ this
    rw [this, hc30]
  have hc3B : ∀ j : Fin n, c3 j 0 = B0 → c3 j = blo := by
    intro j hj
    have : j = ⟨n - 1, by omega⟩ := by
      by_contra hne
      have hlt : j < (⟨n - 1, by omega⟩ : Fin n) :=
        lt_of_le_of_ne (Fin.le_def.mpr (by have := j.isLt; simp; omega)) hne
      have := hcmono _ _ hlt; rw [hcnx, ← hc3x, hj] at this; exact lt_irrefl _ this
    rw [this, hc3n]
  have hc3inj : ∀ j j' : Fin n, c3 j = c3 j' → j = j' := fun j j' hjj =>
    hcinj j j' (by
      have h0 := congrArg (fun y : ℝ³ => y 0) hjj
      have h1 := congrArg (fun y : ℝ³ => y 1) hjj
      simp only [hc3x, hc3y] at h0 h1
      ext i; fin_cases i
      · exact h0
      · exact h1)
  have heinj : ∀ i i' : Fin m, e i = e i' → i = i' := by
    intro i i' hii
    have region : ∀ k : Fin m, (k.val < kA ∧ e k = atop) ∨
        (∃ hk : k.val - kA < n, kA ≤ k.val ∧ e k = c3 ⟨k.val - kA, hk⟩) ∨
        (kA + n ≤ k.val ∧ e k = btop) := by
      intro k
      by_cases h1 : k.val < kA
      · exact Or.inl ⟨h1, heA k h1⟩
      · by_cases h2 : k.val - kA < n
        · exact Or.inr (Or.inl ⟨h2, by omega, heC k (by omega) h2⟩)
        · exact Or.inr (Or.inr ⟨by omega, heB k (by omega)⟩)
    have hAx : atop 0 = A0 := hatopx
    have hBx : btop 0 = B0 := hbtopx
    rcases region i with ⟨h1, e1⟩ | ⟨hk1, h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases region i' with ⟨h2, e2⟩ | ⟨hk2, h2, e2⟩ | ⟨h2, e2⟩
    · exact Fin.ext (by omega)
    · exfalso; rw [e1, e2] at hii
      have := hc3A _ (by rw [← hii, hAx]); rw [← hii] at this; exact hkA1' (by omega) this
    · exfalso; rw [e1, e2] at hii; have := congrArg (fun y : ℝ³ => y 0) hii
      simp only [hAx, hBx] at this; linarith
    · exfalso; rw [e1, e2] at hii
      have := hc3A _ (by rw [hii, hAx]); rw [hii] at this; exact hkA1' (by omega) this
    · rw [e1, e2] at hii
      have := congrArg Fin.val (hc3inj _ _ hii); simp at this; exact Fin.ext (by omega)
    · exfalso; rw [e1, e2] at hii
      have := hc3B _ (by rw [hii, hBx]); rw [hii] at this; exact hkB1' (by omega) this
    · exfalso; rw [e1, e2] at hii; have := congrArg (fun y : ℝ³ => y 0) hii
      simp only [hAx, hBx] at this; linarith
    · exfalso; rw [e1, e2] at hii
      have := hc3B _ (by rw [← hii, hBx]); rw [← hii] at this; exact hkB1' (by omega) this
    · exact Fin.ext (by omega)
  have hpne : ∀ i : Fin m, e i ≠ p := fun i hi => by
    have := hQz _ (heQ i); rw [hi] at this; linarith
  have hinj : Function.Injective
      (fun j : Fin (m + 1) => if hj : j.val < m then e ⟨j.val, hj⟩ else p) := by
    intro j j' hjj
    simp only at hjj
    by_cases h1 : j.val < m <;> by_cases h2 : j'.val < m <;> simp only [h1, h2, dite_true, dite_false] at hjj
    · exact Fin.ext (by simpa using congrArg Fin.val (heinj _ _ hjj))
    · exact absurd hjj (hpne _)
    · exact absurd hjj.symm (hpne _)
    · exact Fin.ext (by have := j.isLt; have := j'.isLt; omega)
  have hdeep' : e ⟨0, by omega⟩ 1 < p 1 ∨ e ⟨m - 1, by omega⟩ 1 < p 1 := by
    rw [he0, helast]
    rcases hdeep with hd | hd
    · exact Or.inl (hd atop (hQV _ hatopQ).1 (hQz _ hatopQ) fun z hz hzh => by
        rw [hatopx]; exact hA'min z (hfaceQ z hz hzh))
    · exact Or.inr (hd btop (hQV _ hbtopQ).1 (hQz _ hbtopQ) fun z hz hzh => by
        rw [hbtopx]; exact hB'max z (hfaceQ z hz hzh))
  have hxV : ∀ j : Fin (m + 1), (if hj : j.val < m then e ⟨j.val, hj⟩ else p) ∈ V := by
    intro j; by_cases hj : j.val < m
    · simp only [hj, dite_true]; exact heV _
    · simp only [hj, dite_false]; exact hp
  exact isRupert_cycle_edgeOn V v p (by omega) e heV hp hinj hE hEp hpE hconvex hdeep'
    (fun j j' hne => hsepV _ (hxV j) _ (hxV j') (hinj.ne hne))

/-- **Two interior points `d` apart.**  If `d = Σ c y • y` with `Σ c = 0` and the
negative parts of `c` summing to less than one, then some `w` has `w` and
`w + d` in the interior of the hull. -/
theorem exists_interior_pair {S : Finset ℝ²} (hint : (interior (convexHull ℝ (S : Set ℝ²))).Nonempty)
    (c : ℝ² → ℝ) (d : ℝ²) (hc0 : ∑ y ∈ S, c y = 0) (hcd : ∑ y ∈ S, c y • y = d)
    (hneg : ∑ y ∈ S, max 0 (-c y) < 1) :
    ∃ w, w ∈ interior (convexHull ℝ (S : Set ℝ²)) ∧
      w + d ∈ interior (convexHull ℝ (S : Set ℝ²)) := by
  classical
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h] at hint; simp at hint
    · exact h
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hSne
  set δ := (1 - ∑ y ∈ S, max 0 (-c y)) / S.card with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) hcard
  set μ : ℝ² → ℝ := fun y => max 0 (-c y) + δ with hμ
  have hμ1 : ∑ y ∈ S, μ y = 1 := by
    simp only [hμ, sum_add_distrib, sum_const, nsmul_eq_mul, hδ]; field_simp; ring
  have hμpos : ∀ y ∈ S, 0 < μ y := fun y _ => by
    simp only [hμ]; have := le_max_left 0 (-c y); linarith
  have hμ'pos : ∀ y ∈ S, 0 < μ y + c y := fun y _ => by
    simp only [hμ]; have := le_max_right 0 (-c y); linarith
  have hμ'1 : ∑ y ∈ S, (μ y + c y) = 1 := by rw [sum_add_distrib, hμ1, hc0, add_zero]
  refine ⟨∑ y ∈ S, μ y • y, sum_smul_mem_interior_convexHull S μ hμpos hμ1 hint, ?_⟩
  have e : ∑ y ∈ S, μ y • y + d = ∑ y ∈ S, (μ y + c y) • y := by
    rw [← hcd, ← sum_add_distrib]; simp only [add_smul]
  rw [e]
  exact sum_smul_mem_interior_convexHull S (fun y => μ y + c y) hμ'pos hμ'1 hint

set_option maxHeartbeats 1000000 in
/-- **The witness of the fallback** (plane picture): the ends of the face are
vertical chords `aL aH`, `bL bH` of length at least `lam`, and the fifth point
`C` lies strictly between them, above the top side or below the bottom side.
Then two interior points are `(0, lam)` apart. -/
theorem fallback_witness (aL aH bL bH C : ℝ²) {lam : ℝ} (hlam : 0 < lam)
    (hxa : aL 0 = aH 0) (hxb : bL 0 = bH 0) (hab : aH 0 < bH 0) (hC1 : aH 0 < C 0)
    (hC2 : C 0 < bH 0) (hlA : lam ≤ aH 1 - aL 1) (hlB : lam ≤ bH 1 - bL 1)
    (hCaL : C ≠ aL) (hCaH : C ≠ aH) (hCbL : C ≠ bL) (hCbH : C ≠ bH)
    (hCpos : 0 < cross2 (bH - aH) (C - aH) ∨ cross2 (bL - aL) (C - aL) < 0) :
    ∃ w, w ∈ interior (convexHull ℝ (({aL, aH, bL, bH, C} : Finset ℝ²) : Set ℝ²)) ∧
      w + !₂[0, lam] ∈ interior (convexHull ℝ (({aL, aH, bL, bH, C} : Finset ℝ²) : Set ℝ²)) := by
  classical
  have hab' : aL 0 < bL 0 := by rw [hxa, hxb]; exact hab
  have hLA : 0 < aH 1 - aL 1 := by linarith
  have hLB : 0 < bH 1 - bL 1 := by linarith
  have haLH : aL ≠ aH := fun e => by rw [e] at hLA; linarith
  have hbLH : bL ≠ bH := fun e => by rw [e] at hLB; linarith
  have haLbL : aL ≠ bL := fun e => by rw [e] at hab'; linarith
  have haLbH : aL ≠ bH := fun e => by rw [e, ← hxb] at hab'; linarith
  have haHbL : aH ≠ bL := fun e => by rw [← e, hxa] at hab'; linarith
  have haHbH : aH ≠ bH := fun e => by rw [e] at hab; linarith
  set S : Finset ℝ² := {aL, aH, bL, bH, C} with hS
  -- the interior is nonempty: the centroid of `aL bL aH`
  have hint : (interior (convexHull ℝ (S : Set ℝ²))).Nonempty := by
    set g : ℝ² := (1 / 3 : ℝ) • (aL + bL + aH)
    have h0 : 0 < cross2 (bL - aL) (aH - aL) := by
      simp only [cross2, PiLp.sub_apply, hxa]; ring_nf; nlinarith
    refine ⟨g, interior_mono (convexHull_mono ?_) (mem_interior_tri h0 ?_ ?_ ?_)⟩
    · rintro y ⟨i, rfl⟩
      have hcase : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases hcase i with rfl | rfl | rfl <;> simp [tri, hS]
    · simp only [g, cross2, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at h0 ⊢
      nlinarith
    · simp only [g, cross2, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at h0 ⊢
      nlinarith
    · simp only [g, cross2, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at h0 ⊢
      nlinarith
  -- the parameters
  set xa := aH 0
  set xb := bH 0
  set sp := (C 0 - xa) / (xb - xa) with hsp
  have hsp0 : 0 < sp := div_pos (by linarith) (by linarith)
  have hsp1 : sp < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hne : xb - xa ≠ 0 := by simp only [xa, xb]; linarith
  have hspx : C 0 = (1 - sp) * xa + sp * xb := by rw [hsp]; field_simp; ring
  set αA := lam / (2 * (aH 1 - aL 1)) with hαA
  set αB := lam / (2 * (bH 1 - bL 1)) with hαB
  have hαA0 : 0 < αA := div_pos hlam (by linarith)
  have hαB0 : 0 < αB := div_pos hlam (by linarith)
  have hαA1 : αA ≤ 1 / 2 := by rw [hαA, div_le_iff₀ (by linarith)]; linarith
  have hαB1 : αB ≤ 1 / 2 := by rw [hαB, div_le_iff₀ (by linarith)]; linarith
  have hαAl : αA * (aH 1 - aL 1) = lam / 2 := by rw [hαA]; field_simp
  have hαBl : αB * (bH 1 - bL 1) = lam / 2 := by rw [hαB]; field_simp
  set α := min αA αB
  have hα0 : 0 < α := lt_min hαA0 hαB0
  have hαA' : α ≤ αA := min_le_left _ _
  have hαB' : α ≤ αB := min_le_right _ _
  have hd : ∀ y ∈ S, True := fun _ _ => trivial
  -- the sums over the five points
  have hsum : ∀ g : ℝ² → ℝ, ∑ y ∈ S, g y = g aL + g aH + g bL + g bH + g C := by
    intro g
    rw [hS, sum_insert (by simp [haLH, haLbL, haLbH, Ne.symm hCaL]),
      sum_insert (by simp [haHbL, haHbH, Ne.symm hCaH]),
      sum_insert (by simp [hbLH, Ne.symm hCbL]), sum_insert (by simp [Ne.symm hCbH]),
      sum_singleton]; ring
  have hsumv : ∀ g : ℝ² → ℝ, ∑ y ∈ S, g y • y = g aL • aL + g aH • aH + g bL • bL + g bH • bH +
      g C • C := by
    intro g
    rw [hS, sum_insert (by simp [haLH, haLbL, haLbH, Ne.symm hCaL]),
      sum_insert (by simp [haHbL, haHbH, Ne.symm hCaH]),
      sum_insert (by simp [hbLH, Ne.symm hCbL]), sum_insert (by simp [Ne.symm hCbH]),
      sum_singleton]; abel
  -- the coefficients, `C` above or below
  rcases hCpos with habove | hbelow
  · set T := aH 1 + sp * (bH 1 - aH 1)
    have hT : 0 < C 1 - T := by
      simp only [cross2, PiLp.sub_apply] at habove
      have : (bH 0 - aH 0) * (C 1 - T) = (bH 0 - aH 0) * (C 1 - aH 1) - (bH 1 - aH 1) * (C 0 - aH 0) := by
        simp only [T]; rw [hspx]; ring
      have hpos : 0 < (bH 0 - aH 0) * (C 1 - T) := by rw [this]; linarith
      exact pos_of_mul_pos_right hpos (by linarith)
    set r := (C 1 - T) / lam
    have hr : 0 < r := div_pos hT hlam
    set ε := α * r / (1 + α * r)
    have hε0 : 0 < ε := div_pos (mul_pos hα0 hr) (by positivity)
    have hε1 : ε < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    set κ := (1 - ε) * α
    have hκ : κ * (C 1 - T) = ε * lam := by
      simp only [κ, ε, r]; field_simp; ring
    have hκ0 : 0 < κ := mul_pos (by linarith) hα0
    set c : ℝ² → ℝ := fun y => if y = aL then -(1 - ε) * αA else if y = aH then
      (1 - ε) * αA - κ * (1 - sp) else if y = bL then -(1 - ε) * αB else if y = bH then
      (1 - ε) * αB - κ * sp else κ with hc
    have caL : c aL = -(1 - ε) * αA := by simp [hc]
    have caH : c aH = (1 - ε) * αA - κ * (1 - sp) := by simp [hc, Ne.symm haLH]
    have cbL : c bL = -(1 - ε) * αB := by simp [hc, Ne.symm haLbL, Ne.symm haHbL]
    have cbH : c bH = (1 - ε) * αB - κ * sp := by
      simp [hc, Ne.symm haLbH, Ne.symm haHbH, Ne.symm hbLH]
    have cC : c C = κ := by simp [hc, hCaL, hCaH, hCbL, hCbH]
    refine exists_interior_pair hint c _ ?_ ?_ ?_
    · rw [hsum, caL, caH, cbL, cbH, cC]; ring
    · rw [hsumv, caL, caH, cbL, cbH, cC]
      ext i; fin_cases i
      · simp; rw [hxa, hxb, hspx]; ring
      · simp
        have : (1 - ε) * (αA * (aH 1 - aL 1) + αB * (bH 1 - bL 1)) + κ * (C 1 - T) = lam := by
          rw [hαAl, hαBl, hκ]; ring
        simp only [T] at this; linarith
    · rw [hsum, caL, caH, cbL, cbH, cC]
      have h1 : κ * (1 - sp) ≤ (1 - ε) * αA := by
        simp only [κ]; nlinarith [mul_le_mul_of_nonneg_left hαA' (show (0:ℝ) ≤ 1 - ε by linarith)]
      have h2 : κ * sp ≤ (1 - ε) * αB := by
        simp only [κ]; nlinarith [mul_le_mul_of_nonneg_left hαB' (show (0:ℝ) ≤ 1 - ε by linarith)]
      have hA0 : 0 ≤ (1 - ε) * αA := mul_nonneg (by linarith) hαA0.le
      have hB0 : 0 ≤ (1 - ε) * αB := mul_nonneg (by linarith) hαB0.le
      have m1 : max 0 (-(-(1 - ε) * αA)) = (1 - ε) * αA := by rw [neg_mul, neg_neg]; exact max_eq_right hA0
      have m2 : max 0 (-((1 - ε) * αA - κ * (1 - sp))) = 0 := max_eq_left (by linarith)
      have m3 : max 0 (-(-(1 - ε) * αB)) = (1 - ε) * αB := by rw [neg_mul, neg_neg]; exact max_eq_right hB0
      have m4 : max 0 (-((1 - ε) * αB - κ * sp)) = 0 := max_eq_left (by linarith)
      have m5 : max 0 (-κ) = 0 := max_eq_left (by linarith)
      rw [m1, m2, m3, m4, m5]
      have : (1 - ε) * (αA + αB) ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
  · set Bt := aL 1 + sp * (bL 1 - aL 1)
    have hB : 0 < Bt - C 1 := by
      simp only [cross2, PiLp.sub_apply] at hbelow
      have : (bL 0 - aL 0) * (Bt - C 1) = -((bL 0 - aL 0) * (C 1 - aL 1) - (bL 1 - aL 1) * (C 0 - aL 0)) := by
        simp only [Bt]; rw [hspx, hxa, hxb]; ring
      have hpos : 0 < (bL 0 - aL 0) * (Bt - C 1) := by rw [this]; linarith
      exact pos_of_mul_pos_right hpos (by linarith)
    set r := (Bt - C 1) / lam
    have hr : 0 < r := div_pos hB hlam
    set ε := α * r / (1 + α * r)
    have hε0 : 0 < ε := div_pos (mul_pos hα0 hr) (by positivity)
    have hε1 : ε < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    set κ := (1 - ε) * α
    have hκ : κ * (Bt - C 1) = ε * lam := by
      simp only [κ, ε, r]; field_simp; ring
    have hκ0 : 0 < κ := mul_pos (by linarith) hα0
    set c : ℝ² → ℝ := fun y => if y = aL then -(1 - ε) * αA + κ * (1 - sp) else if y = aH then
      (1 - ε) * αA else if y = bL then -(1 - ε) * αB + κ * sp else if y = bH then
      (1 - ε) * αB else -κ with hc
    have caL : c aL = -(1 - ε) * αA + κ * (1 - sp) := by simp [hc]
    have caH : c aH = (1 - ε) * αA := by simp [hc, Ne.symm haLH]
    have cbL : c bL = -(1 - ε) * αB + κ * sp := by simp [hc, Ne.symm haLbL, Ne.symm haHbL]
    have cbH : c bH = (1 - ε) * αB := by
      simp [hc, Ne.symm haLbH, Ne.symm haHbH, Ne.symm hbLH]
    have cC : c C = -κ := by simp [hc, hCaL, hCaH, hCbL, hCbH]
    refine exists_interior_pair hint c _ ?_ ?_ ?_
    · rw [hsum, caL, caH, cbL, cbH, cC]; ring
    · rw [hsumv, caL, caH, cbL, cbH, cC]
      ext i; fin_cases i
      · simp; rw [hxa, hxb, hspx]; ring
      · simp
        have : (1 - ε) * (αA * (aH 1 - aL 1) + αB * (bH 1 - bL 1)) + κ * (Bt - C 1) = lam := by
          rw [hαAl, hαBl, hκ]; ring
        simp only [Bt] at this; linarith
    · rw [hsum, caL, caH, cbL, cbH, cC]
      have h1 : κ * (1 - sp) ≤ (1 - ε) * αA := by
        simp only [κ]; nlinarith [mul_le_mul_of_nonneg_left hαA' (show (0:ℝ) ≤ 1 - ε by linarith)]
      have h2 : κ * sp ≤ (1 - ε) * αB := by
        simp only [κ]; nlinarith [mul_le_mul_of_nonneg_left hαB' (show (0:ℝ) ≤ 1 - ε by linarith)]
      have hA0 : 0 ≤ (1 - ε) * αA := mul_nonneg (by linarith) hαA0.le
      have hB0 : 0 ≤ (1 - ε) * αB := mul_nonneg (by linarith) hαB0.le
      have m1 : max 0 (-(-(1 - ε) * αA + κ * (1 - sp))) = (1 - ε) * αA - κ * (1 - sp) := by
        rw [max_eq_right (by linarith)]; ring
      have m2 : max 0 (-((1 - ε) * αA)) = 0 := max_eq_left (by linarith)
      have m3 : max 0 (-(-(1 - ε) * αB + κ * sp)) = (1 - ε) * αB - κ * sp := by
        rw [max_eq_right (by linarith)]; ring
      have m4 : max 0 (-((1 - ε) * αB)) = 0 := max_eq_left (by linarith)
      have m5 : max 0 (-(-κ)) = κ := by rw [neg_neg]; exact max_eq_right hκ0.le
      rw [m1, m2, m3, m4, m5]
      have : (1 - ε) * (αA + αB) ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith

/-- **The fallback of case II** (FEWER-FACES-PROOFS.md §2B): both `x`-ends of
the face carry a point at least as deep as `p` and a point at most as deep as
`q`.  Then Theorem 5 (the waist lemma) applies with the face as the waist. -/
theorem isRupert_caseII_fallback (V : Finset ℝ³) (h : ℝ) (p q : ℝ³) {lam : ℝ} (hlam : 0 < lam)
    (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ5 : (V.filter fun y => y 2 = h).card = 5)
    (hp : p ∈ V) (hph : p 2 < h) (hq : q ∈ V) (hqp : q = p - lam • ey)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q)
    (hAhi : ∃ y ∈ V, y 2 = h ∧ (∀ z ∈ V, z 2 = h → y 0 ≤ z 0) ∧ p 1 ≤ y 1)
    (hAlo : ∃ y ∈ V, y 2 = h ∧ (∀ z ∈ V, z 2 = h → y 0 ≤ z 0) ∧ y 1 ≤ q 1)
    (hBhi : ∃ y ∈ V, y 2 = h ∧ (∀ z ∈ V, z 2 = h → z 0 ≤ y 0) ∧ p 1 ≤ y 1)
    (hBlo : ∃ y ∈ V, y 2 = h ∧ (∀ z ∈ V, z 2 = h → z 0 ≤ y 0) ∧ y 1 ≤ q 1) : IsRupert V := by
  classical
  set Q := V.filter fun y => y 2 = h with hQ
  have hQV : ∀ y ∈ Q, y ∈ V ∧ y 2 = h := fun y hy => mem_filter.mp hy
  have hfaceQ : ∀ y ∈ V, y 2 = h → y ∈ Q := fun y hy hyh => mem_filter.mpr ⟨hy, hyh⟩
  have hprojinj : ∀ y ∈ Q, ∀ y' ∈ Q, proj_xy y = proj_xy y' → y = y' := by
    intro y hy y' hy' he
    rw [← liftPt_proj (hQV y hy).2, ← liftPt_proj (hQV y' hy').2, he]
  obtain ⟨aH, haHV, haHh, haHmin, haH1⟩ := hAhi
  obtain ⟨aL, haLV, haLh, haLmin, haL1⟩ := hAlo
  obtain ⟨bH, hbHV, hbHh, hbHmax, hbH1⟩ := hBhi
  obtain ⟨bL, hbLV, hbLh, hbLmax, hbL1⟩ := hBlo
  have hq1 : q 1 = p 1 - lam := by rw [hqp]; simp [ey]
  have haQ := hfaceQ aH haHV haHh
  have haLQ := hfaceQ aL haLV haLh
  have hbQ := hfaceQ bH hbHV hbHh
  have hbLQ := hfaceQ bL hbLV hbLh
  have hxa : aL 0 = aH 0 := le_antisymm (haLmin aH haHV haHh) (haHmin aL haLV haLh)
  have hxb : bL 0 = bH 0 := le_antisymm (hbHmax bL hbLV hbLh) (hbLmax bH hbHV hbHh)
  have hlA : lam ≤ aH 1 - aL 1 := by linarith
  have hlB : lam ≤ bH 1 - bL 1 := by linarith
  have haLH : aL ≠ aH := by rintro e; rw [e] at hlA; linarith
  have hbLH : bL ≠ bH := by rintro e; rw [e] at hlB; linarith
  -- the two ends are apart
  have hconv' := hconv
  have hab : aH 0 < bH 0 := by
    rcases lt_or_eq_of_le (haHmin bH hbHV hbHh) with h' | h'
    · exact h'
    · exfalso
      -- then all five face points have the same `x`
      have hx : ∀ y ∈ Q, y 0 = aH 0 := fun y hy => le_antisymm
        (by rw [h']; exact hbHmax y (hQV y hy).1 (hQV y hy).2) (haHmin y (hQV y hy).1 (hQV y hy).2)
      obtain ⟨y, hy, hya, hyb⟩ : ∃ y ∈ Q, y ≠ aL ∧ y ≠ aH := by
        by_contra hc; push Not at hc
        have : Q ⊆ {aL, aH} := fun y hy => by
          by_cases e : y = aL
          · simp [e]
          · simp [hc y hy e]
        have := card_le_card this
        rw [hQ5] at this; have := card_le_two (a := aL) (b := aH); omega
      rcases hconv.eq_of_same_x (mem_image_of_mem _ haLQ) (mem_image_of_mem _ haQ)
        (mem_image_of_mem _ hy) (by simp [proj_xy, hxa]) (by simp [proj_xy, hxa, hx y hy])
        with e | e | e
      · exact haLH (hprojinj _ haLQ _ haQ e)
      · exact hya (hprojinj _ haLQ _ hy e).symm
      · exact hyb (hprojinj _ haQ _ hy e).symm
  have hab' : aL 0 < bL 0 := by rw [hxa, hxb]; exact hab
  have haLbL : aL ≠ bL := by rintro e; rw [e] at hab'; linarith
  have haLbH : aL ≠ bH := by rintro e; rw [e, ← hxb] at hab'; linarith
  have haHbL : aH ≠ bL := by rintro e; rw [← e, hxa] at hab'; linarith
  have haHbH : aH ≠ bH := by rintro e; rw [e] at hab; linarith
  -- the fifth point
  obtain ⟨C, hCQ, hCne⟩ : ∃ C ∈ Q, C ∉ ({aL, aH, bL, bH} : Finset ℝ³) := by
    by_contra hc; push Not at hc
    have := card_le_card (fun y hy => hc y hy)
    rw [hQ5] at this
    have h4 : ({aL, aH, bL, bH} : Finset ℝ³).card ≤ 4 := card_le_four
    omega
  simp only [mem_insert, mem_singleton, not_or] at hCne
  obtain ⟨hCaL, hCaH, hCbL, hCbH⟩ := hCne
  have hQeq : Q = {aL, aH, bL, bH, C} := by
    symm
    apply eq_of_subset_of_card_le
    · intro y hy; simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hQ5]
      rw [card_insert_of_notMem (by simp [haLH, haLbL, haLbH, Ne.symm hCaL]),
        card_insert_of_notMem (by simp [haHbL, haHbH, Ne.symm hCaH]),
        card_insert_of_notMem (by simp [hbLH, Ne.symm hCbL]),
        card_insert_of_notMem (by simp [Ne.symm hCbH]), card_singleton]
  have hCh := (hQV C hCQ).2
  have hCx1 : aH 0 < C 0 := by
    refine lt_of_le_of_ne (haHmin C (hQV C hCQ).1 hCh) fun e => ?_
    rcases hconv.eq_of_same_x (mem_image_of_mem _ haLQ) (mem_image_of_mem _ haQ)
      (mem_image_of_mem _ hCQ) (by simp [proj_xy, hxa]) (by simp [proj_xy, hxa, e]) with e' | e' | e'
    · exact haLH (hprojinj _ haLQ _ haQ e')
    · exact hCaL (hprojinj _ haLQ _ hCQ e').symm
    · exact hCaH (hprojinj _ haQ _ hCQ e').symm
  have hCx2 : C 0 < bH 0 := by
    refine lt_of_le_of_ne (hbHmax C (hQV C hCQ).1 hCh) fun e => ?_
    rcases hconv.eq_of_same_x (mem_image_of_mem _ hbLQ) (mem_image_of_mem _ hbQ)
      (mem_image_of_mem _ hCQ) (by simp [proj_xy, hxb]) (by simp [proj_xy, hxb, e]) with e' | e' | e'
    · exact hbLH (hprojinj _ hbLQ _ hbQ e')
    · exact hCbL (hprojinj _ hbLQ _ hCQ e').symm
    · exact hCbH (hprojinj _ hbQ _ hCQ e').symm
  -- `C` is above the top side or below the bottom side
  have hCpos : 0 < cross2 (proj_xy bH - proj_xy aH) (proj_xy C - proj_xy aH) ∨
      cross2 (proj_xy bL - proj_xy aL) (proj_xy C - proj_xy aL) < 0 := by
    by_contra hc; push Not at hc
    apply hconv.not_mem_hull4 (mem_image_of_mem _ hCQ) (mem_image_of_mem _ haLQ)
      (mem_image_of_mem _ hbLQ) (mem_image_of_mem _ haQ) (mem_image_of_mem _ hbQ)
      (fun e => hCaL (hprojinj _ hCQ _ haLQ e)) (fun e => hCbL (hprojinj _ hCQ _ hbLQ e))
      (fun e => hCaH (hprojinj _ hCQ _ haQ e)) (fun e => hCbH (hprojinj _ hCQ _ hbQ e))
    refine mem_convexHull_of_between (by simpa [proj_xy] using hab') (by simp [proj_xy, hxa]; linarith)
      (by simp [proj_xy, hxb]; linarith) (by simpa [proj_xy] using hab) (by simp [proj_xy]; linarith)
      (by simp [proj_xy]; linarith) hc.2 hc.1
  -- the witness in the plane
  have hpne : ∀ y z : ℝ³, y ≠ z → y ∈ Q → z ∈ Q → proj_xy y ≠ proj_xy z := fun y z hne hy hz e =>
    hne (hprojinj _ hy _ hz e)
  obtain ⟨w, hw1, hw2⟩ := fallback_witness (proj_xy aL) (proj_xy aH) (proj_xy bL) (proj_xy bH)
    (proj_xy C) hlam (by simp [proj_xy, hxa]) (by simp [proj_xy, hxb]) (by simpa [proj_xy] using hab)
    (by simpa [proj_xy] using hCx1) (by simpa [proj_xy] using hCx2) (by simpa [proj_xy] using hlA)
    (by simpa [proj_xy] using hlB) (hpne _ _ hCaL hCQ haLQ) (hpne _ _ hCaH hCQ haQ)
    (hpne _ _ hCbL hCQ hbLQ) (hpne _ _ hCbH hCQ hbQ) hCpos
  have hSeq : Q.image proj_xy = {proj_xy aL, proj_xy aH, proj_xy bL, proj_xy bH, proj_xy C} := by
    rw [hQeq]; simp [image_insert]
  rw [← hSeq] at hw1 hw2
  -- translate the face to `z = 0` and apply the waist lemma
  set t : ℝ³ := !₂[0, 0, -h] with ht
  have hVeq : V = Q ∪ {p, q} := by
    ext y; simp only [mem_union, mem_insert, mem_singleton]
    constructor
    · intro hy
      rcases eq_or_lt_of_le (hV y hy) with hyh | hyh
      · exact Or.inl (hfaceQ y hy hyh)
      · exact Or.inr (hrest y hy hyh)
    · rintro (hy | rfl | rfl)
      · exact (hQV y hy).1
      · exact hp
      · exact hq
  apply isRupert_of_isRupert_image_add t V
  have himg : V.image (fun x => t + x) =
      Q.image (fun x => t + x) ∪ ({t + p, t + q} : Finset ℝ³) := by
    rw [hVeq, image_union]; simp
  rw [himg]
  have hpq0 : p 0 = q 0 := by rw [hqp]; simp [ey]
  have hpq1 : p 1 = q 1 + lam := by rw [hqp]; simp [ey]
  have hpq2 : p 2 = q 2 := by rw [hqp]; simp [ey]
  have hqh : q 2 < h := by rw [← hpq2]; exact hph
  have hproj : (Q.image fun x => t + x).image proj_xy = Q.image proj_xy := by
    rw [image_image]; congr 1; funext x; ext i; fin_cases i <;> simp [proj_xy, ht]
  refine isRupert_of_waist _ _ ?_ (by rw [hproj]; exact ⟨w, hw1⟩) !₂[w 0 - q 0, w 1 - q 1, h - q 2]
    (by simp; linarith) ?_
  · intro y hy; obtain ⟨x, hx, rfl⟩ := mem_image.mp hy; simp [ht, (hQV x hx).2]
  · rw [hproj]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    have hfac : (q 2 - h) / (h - q 2) = -1 := by
      rw [div_eq_iff (by linarith)]; ring
    have hfac2 : (-h + q 2) / (h - q 2) = -1 := by
      rw [div_eq_iff (by linarith)]; ring
    rcases hx with rfl | rfl
    · convert hw2 using 1
      ext i; fin_cases i
      · simp [proj_xy, ht, hpq2, hfac2]; rw [hpq0]; ring
      · simp [proj_xy, ht, hpq2, hfac2]; rw [hpq1]; ring
    · convert hw1 using 1
      ext i; fin_cases i
      · simp [proj_xy, ht, hfac2]
      · simp [proj_xy, ht, hfac2]

theorem rotZ180_apply (y : ℝ³) : (rotZ (-1) 0).toEuclideanLin y = !₂[-y 0, -y 1, y 2] := by
  rw [rotZ_apply]; ext i; fin_cases i <;> simp

/-- **Case II in the standard frame**: the face `z = h` has five points, and `p`,
`q = p - λ ey` are the only points below it.  The view along `ey` (front `p`),
the view along `-ey` (front `q`), or the fallback applies. -/
theorem isRupert_caseII_std (V : Finset ℝ³) (h : ℝ) (p q : ℝ³) {lam : ℝ} (hlam : 0 < lam)
    (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ5 : (V.filter fun y => y 2 = h).card = 5)
    (hp : p ∈ V) (hph : p 2 < h) (hq : q ∈ V) (hqp : q = p - lam • ey)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q) : IsRupert V := by
  classical
  have hQ3 : 2 < (V.filter fun y => y 2 = h).card := by omega
  by_cases hd1 : (∀ y ∈ V, y 2 = h → (∀ z ∈ V, z 2 = h → y 0 ≤ z 0) → y 1 < p 1) ∨
      (∀ y ∈ V, y 2 = h → (∀ z ∈ V, z 2 = h → z 0 ≤ y 0) → y 1 < p 1)
  · exact isRupert_caseII_view V h p q hlam hV hconv hQ3 hp hph hq hqp hrest hd1
  -- the half turn about the vertical axis: `q` in front
  set R := rotZ (-1) 0 with hR
  have hRSO : R ∈ SO3 := rotZ_mem_SO3 (by norm_num)
  set f := R.toEuclideanLin with hf
  have hf0 : ∀ y, f y 0 = -y 0 := fun y => by simp [hf, hR, rotZ180_apply]
  have hf1 : ∀ y, f y 1 = -y 1 := fun y => by simp [hf, hR, rotZ180_apply]
  have hf2 : ∀ y, f y 2 = y 2 := fun y => by simp [hf, hR, rotZ180_apply]
  have hfinj : Function.Injective f := fun a b hab => by
    have h0 := congrArg (fun v : ℝ³ => v 0) hab
    have h1 := congrArg (fun v : ℝ³ => v 1) hab
    have h2 := congrArg (fun v : ℝ³ => v 2) hab
    simp only [hf0, hf1, hf2, neg_inj] at h0 h1 h2
    ext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  set V' := V.image f with hV'
  have hmemV' : ∀ y ∈ V', ∃ z ∈ V, f z = y := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy; exact ⟨z, hz, rfl⟩
  have hfilt : V'.filter (fun y => y 2 = h) = (V.filter fun y => y 2 = h).image f := by
    ext y; simp only [hV', mem_filter, mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzh⟩; exact ⟨z, ⟨hz, by rwa [hf2] at hzh⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzh⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, by rw [hf2]; exact hzh⟩
  have hfp : f p = f q - lam • ey := by
    rw [hqp]; ext i; fin_cases i <;> simp [hf0, hf1, hf2, ey]
  by_cases hd2 : (∀ y ∈ V', y 2 = h → (∀ z ∈ V', z 2 = h → y 0 ≤ z 0) → y 1 < f q 1) ∨
      (∀ y ∈ V', y 2 = h → (∀ z ∈ V', z 2 = h → z 0 ≤ y 0) → y 1 < f q 1)
  · apply isRupert_of_isRupert_image_rotation R hRSO V
    have hconv' : ConvPos ((V'.filter fun y => y 2 = h).image proj_xy) := by
      rw [hfilt, Finset.image_image]
      have e : (proj_xy ∘ f) = (-LinearMap.id : ℝ² →ₗ[ℝ] ℝ²) ∘ proj_xy := by
        funext y; ext i; fin_cases i <;> simp [proj_xy, hf0, hf1]
      rw [e, ← Finset.image_image]
      exact hconv.image_linear _ (fun a b hab => by simpa using hab)
    refine isRupert_caseII_view V' h (f q) (f p) hlam ?_ hconv' ?_ (mem_image_of_mem _ hq)
      (by rw [hf2, hqp]; simpa [ey] using hph) (mem_image_of_mem _ hp) hfp ?_ hd2
    · intro y hy; obtain ⟨z, hz, rfl⟩ := hmemV' y hy; rw [hf2]; exact hV z hz
    · rw [hfilt, card_image_of_injective _ hfinj]; exact hQ3
    · intro y hy hyh; obtain ⟨z, hz, rfl⟩ := hmemV' y hy
      rw [hf2] at hyh
      rcases hrest z hz hyh with rfl | rfl
      · right; rfl
      · left; rfl
  · -- the fallback
    push Not at hd1 hd2
    obtain ⟨⟨yA, hyA, hyAh, hyAmin, hyA1⟩, ⟨yB, hyB, hyBh, hyBmax, hyB1⟩⟩ := hd1
    obtain ⟨⟨yA', hyA', hyA'h, hyA'min, hyA'1⟩, ⟨yB', hyB', hyB'h, hyB'max, hyB'1⟩⟩ := hd2
    obtain ⟨zA, hzA, rfl⟩ := hmemV' yA' hyA'
    obtain ⟨zB, hzB, rfl⟩ := hmemV' yB' hyB'
    rw [hf2] at hyA'h hyB'h
    refine isRupert_caseII_fallback V h p q hlam hV hconv hQ5 hp hph hq hqp hrest
      ⟨yA, hyA, hyAh, hyAmin, hyA1⟩ ⟨zB, hzB, hyB'h, ?_, ?_⟩ ⟨yB, hyB, hyBh, hyBmax, hyB1⟩
      ⟨zA, hzA, hyA'h, ?_, ?_⟩
    · intro z hz hzh
      have := hyB'max (f z) (mem_image_of_mem _ hz) (by rw [hf2]; exact hzh)
      rw [hf0, hf0] at this; linarith
    · rw [hf1, hf1] at hyB'1; linarith
    · intro z hz hzh
      have := hyA'min (f z) (mem_image_of_mem _ hz) (by rw [hf2]; exact hzh)
      rw [hf0, hf0] at this; linarith
    · rw [hf1, hf1] at hyA'1; linarith

/-- **Case II**: the face `z = h` has five points, and `p ≠ q` at equal height
are the only points below it. -/
theorem isRupert_caseII (V : Finset ℝ³) (h : ℝ) (p q : ℝ³) (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ5 : (V.filter fun y => y 2 = h).card = 5)
    (hp : p ∈ V) (hph : p 2 < h) (hq : q ∈ V) (hpq : p ≠ q) (hz : p 2 = q 2)
    (hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q) : IsRupert V := by
  classical
  set u := p - q with hu
  have hu2 : u 2 = 0 := by simp [hu, hz]
  have hr2 : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    by_contra hc; push Not at hc
    apply hpq; rw [← sub_eq_zero]; ext i; fin_cases i
    · show u 0 = 0; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    · show u 1 = 0; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    · exact hu2
  set r := Real.sqrt (u 0 ^ 2 + u 1 ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hr2
  have hrr : r * r = u 0 ^ 2 + u 1 ^ 2 := Real.mul_self_sqrt hr2.le
  set cc := u 1 / r
  set ss := u 0 / r
  have hr2' : r ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by rw [sq]; exact hrr
  have hcs : cc ^ 2 + ss ^ 2 = 1 := by
    simp only [cc, ss, div_pow]; rw [← add_div, hr2', add_comm]; exact div_self hr2.ne'
  set R := rotZ cc ss with hR
  have hRSO : R ∈ SO3 := rotZ_mem_SO3 hcs
  set f := R.toEuclideanLin with hf
  have hf2 : ∀ y, f y 2 = y 2 := fun y => by simp [hf, hR, rotZ_apply]
  have hfinj : Function.Injective f := fun a b hab => by
    have h0 := congrArg (fun v : ℝ³ => v 0) hab
    have h1 := congrArg (fun v : ℝ³ => v 1) hab
    have h2 := congrArg (fun v : ℝ³ => v 2) hab
    simp only [hf, hR, rotZ_apply] at h0 h1 h2
    simp at h0 h1 h2
    ext i; fin_cases i
    · show a 0 = b 0
      have e : (cc ^ 2 + ss ^ 2) * a 0 = (cc ^ 2 + ss ^ 2) * b 0 := by
        linear_combination cc * h0 + ss * h1
      rwa [hcs, one_mul, one_mul] at e
    · show a 1 = b 1
      have e : (cc ^ 2 + ss ^ 2) * a 1 = (cc ^ 2 + ss ^ 2) * b 1 := by
        linear_combination -ss * h0 + cc * h1
      rwa [hcs, one_mul, one_mul] at e
    · exact h2
  have hfu : f q = f p - r • ey := by
    have hpq' : q = p - u := by rw [hu]; abel
    rw [hpq', map_sub]
    congr 1
    simp only [hf, hR, rotZ_apply, cc, ss]
    ext i; fin_cases i
    · simp [ey]; field_simp; ring
    · simp [ey]; field_simp; nlinarith [hrr]
    · simp [ey, hu2]
  set g : ℝ² →ₗ[ℝ] ℝ² :=
    { toFun := fun s => !₂[cc * s 0 - ss * s 1, ss * s 0 + cc * s 1]
      map_add' := fun a b => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun a b => by ext i; fin_cases i <;> simp <;> ring } with hg
  have hgf : ∀ y, proj_xy (f y) = g (proj_xy y) := fun y => by
    ext i; fin_cases i <;> simp [hg, hf, hR, rotZ_apply, proj_xy]
  have hginj : Function.Injective g := fun a b hab => by
    have h0 := congrArg (fun v : ℝ² => v 0) hab
    have h1 := congrArg (fun v : ℝ² => v 1) hab
    simp [hg] at h0 h1
    ext i; fin_cases i
    · show a 0 = b 0
      have e : (cc ^ 2 + ss ^ 2) * a 0 = (cc ^ 2 + ss ^ 2) * b 0 := by
        linear_combination cc * h0 + ss * h1
      rwa [hcs, one_mul, one_mul] at e
    · show a 1 = b 1
      have e : (cc ^ 2 + ss ^ 2) * a 1 = (cc ^ 2 + ss ^ 2) * b 1 := by
        linear_combination -ss * h0 + cc * h1
      rwa [hcs, one_mul, one_mul] at e
  apply isRupert_of_isRupert_image_rotation R hRSO V
  set V' := V.image f with hV'
  have hmemV' : ∀ y ∈ V', ∃ z ∈ V, f z = y := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy; exact ⟨z, hz, rfl⟩
  have hfilt : V'.filter (fun y => y 2 = h) = (V.filter fun y => y 2 = h).image f := by
    ext y; simp only [hV', mem_filter, mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzh⟩; exact ⟨z, ⟨hz, by rwa [hf2] at hzh⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzh⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, by rw [hf2]; exact hzh⟩
  refine isRupert_caseII_std V' h (f p) (f q) hr0 ?_ ?_ ?_ (mem_image_of_mem _ hp)
    (by rw [hf2]; exact hph) (mem_image_of_mem _ hq) hfu ?_
  · intro y hy; obtain ⟨z, hz, rfl⟩ := hmemV' y hy; rw [hf2]; exact hV z hz
  · rw [hfilt, Finset.image_image]
    have e : (proj_xy ∘ f) = g ∘ proj_xy := funext hgf
    rw [e, ← Finset.image_image]
    exact hconv.image_linear g hginj
  · rw [hfilt, card_image_of_injective _ hfinj]; exact hQ5
  · intro y hy hyh; obtain ⟨z, hz, rfl⟩ := hmemV' y hy
    rw [hf2] at hyh
    rcases hrest z hz hyh with rfl | rfl
    · left; rfl
    · right; rfl

/-- **Theorem A for five face points, standard frame**: seven points, five of
them on the face `z = h` in strictly convex position, the others below. -/
theorem isRupert_face5_std (V : Finset ℝ³) (h : ℝ) (hcard : V.card = 7)
    (hV : ∀ y ∈ V, y 2 ≤ h)
    (hconv : ConvPos ((V.filter fun y => y 2 = h).image proj_xy))
    (hQ5 : (V.filter fun y => y 2 = h).card = 5) : IsRupert V := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := V) (fun y : ℝ³ => y 2 = h)
  have hbelow2 : (V.filter fun y => ¬ y 2 = h).card = 2 := by omega
  obtain ⟨p, q, hpq, hpqe⟩ := card_eq_two.mp hbelow2
  have hpm : p ∈ V.filter fun y => ¬ y 2 = h := by rw [hpqe]; simp
  have hqm : q ∈ V.filter fun y => ¬ y 2 = h := by rw [hpqe]; simp
  obtain ⟨hp, hpn⟩ := mem_filter.mp hpm
  obtain ⟨hq, hqn⟩ := mem_filter.mp hqm
  have hph : p 2 < h := lt_of_le_of_ne (hV p hp) hpn
  have hqh : q 2 < h := lt_of_le_of_ne (hV q hq) hqn
  have hrest : ∀ y ∈ V, y 2 < h → y = p ∨ y = q := by
    intro y hy hyh
    have : y ∈ V.filter fun y => ¬ y 2 = h := mem_filter.mpr ⟨hy, ne_of_lt hyh⟩
    rw [hpqe] at this; simpa using this
  have hQ3 : 2 < (V.filter fun y => y 2 = h).card := by omega
  rcases lt_trichotomy (p 2) (q 2) with hlt | heq | hgt
  · exact isRupert_caseI V h p q hV hconv hQ3 hp hq hlt hqh hrest
  · exact isRupert_caseII V h p q hV hconv hQ5 hp hph hq hpq heq hrest
  · exact isRupert_caseI V h q p hV hconv hQ3 hq hp hgt hph
      (fun y hy hyh => (hrest y hy hyh).symm)

/-- Rupertness depends only on the convex hull. -/
theorem isRupert_of_convexHull_eq {V W : Finset ℝ³}
    (h : convexHull ℝ (V : Set ℝ³) = convexHull ℝ (W : Set ℝ³)) (hV : IsRupert V) :
    IsRupert W := by
  obtain ⟨R1, hR1, o, R2, hR2, hsub⟩ := hV
  exact ⟨R1, hR1, o, R2, hR2, by simpa only [h] using hsub⟩

/-- Points of a horizontal plane, none in the hull of the others, project to a
set in strictly convex position. -/
theorem convPos_of_extreme_plane {P : Finset ℝ³} {h : ℝ} (hP : ∀ w ∈ P, w 2 = h)
    (hext : ∀ w ∈ P, w ∉ convexHull ℝ ((P.erase w : Finset ℝ³) : Set ℝ³)) :
    ConvPos (P.image proj_xy) := by
  classical
  intro s hs hmem
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hs
  apply hext w hw
  -- the lift `s ↦ (s, h)` is affine and inverts `proj_xy` on `P`
  set L : ℝ² →ᵃ[ℝ] ℝ³ :=
    { toFun := fun t => liftPt t h
      linear :=
        { toFun := fun t => !₂[t 0, t 1, 0]
          map_add' := fun a b => by ext i; fin_cases i <;> simp
          map_smul' := fun a b => by ext i; fin_cases i <;> simp }
      map_vadd' := fun a b => by ext i; fin_cases i <;> simp [liftPt] } with hL
  have hLp : ∀ w ∈ P, L (proj_xy w) = w := fun w hw => by
    show liftPt (proj_xy w) h = w; exact liftPt_proj (hP w hw)
  have e : ((P.image proj_xy).erase (proj_xy w) : Set ℝ²) =
      proj_xy '' ((P.erase w : Finset ℝ³) : Set ℝ³) := by
    ext t; simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, mem_coe,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hne⟩; exact ⟨z, ⟨hz, fun e' => hne (by rw [e'])⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzw⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, fun e' => hzw ?_⟩
      rw [← hLp z hz, e', hLp w hw]
  rw [e] at hmem
  have := AffineMap.image_convexHull L (proj_xy '' ((P.erase w : Finset ℝ³) : Set ℝ³))
  have hmem' : L (proj_xy w) ∈ L '' convexHull ℝ (proj_xy '' ((P.erase w : Finset ℝ³) : Set ℝ³)) :=
    ⟨_, hmem, rfl⟩
  rw [this, Set.image_image, hLp w hw] at hmem'
  have hid : (fun x => L (proj_xy x)) '' ((P.erase w : Finset ℝ³) : Set ℝ³) =
      ((P.erase w : Finset ℝ³) : Set ℝ³) := by
    ext x; simp only [Set.mem_image, coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, ⟨hz, hzw⟩, rfl⟩; rw [hLp z hz]; exact ⟨hz, hzw⟩
    · rintro ⟨hx, hxw⟩; exact ⟨x, ⟨hx, hxw⟩, hLp x hx⟩
  rwa [hid] at hmem'

/-- **Theorem A** (FEWER-FACES-PROOFS.md §2): seven points with a solid hull,
of which at least five, but not all, lie on a facet, are Rupert. -/
theorem isRupert_of_card_seven_of_facet (V F : Finset ℝ³) (hcard : V.card = 7)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hFV : F ⊂ V) (hF : 5 ≤ F.card)
    (hfacet : IsFacet V F) : IsRupert V := by
  classical
  -- a point in the hull of the others: at most six vertices
  by_cases hext : ∃ x ∈ V, x ∈ convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³)
  · obtain ⟨x, hx, hxh⟩ := hext
    have hhull : convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³) = convexHull ℝ (V : Set ℝ³) := by
      apply le_antisymm (convexHull_mono (by simp))
      refine convexHull_min (fun y hy => ?_) (convex_convexHull ℝ _)
      by_cases hyx : y = x
      · rw [hyx]; exact hxh
      · exact subset_convexHull ℝ _ (by simpa [hyx] using hy)
    refine isRupert_of_convexHull_eq hhull (isRupert_of_card_le_six _ ?_ ?_)
    · rw [card_erase_of_mem hx]; omega
    · rw [hhull]; exact hint
  push Not at hext
  obtain ⟨f, hf0, hfneg⟩ := hfacet
  obtain ⟨x0, hx0V, hx0F⟩ := exists_of_ssubset hFV
  have hF7 : F.card < 7 := hcard ▸ card_lt_card hFV
  -- the facet's normal
  set N : ℝ³ := (InnerProductSpace.toDual ℝ ℝ³).symm (LinearMap.toContinuousLinearMap f.linear)
    with hN
  have hNf : ∀ x, f x = ⟪N, x⟫ + f 0 := fun x => by
    rw [hN, InnerProductSpace.toDual_symm_apply]
    have := f.map_vadd 0 x
    simpa using this
  have hFne : F.Nonempty := card_pos.mp (by omega)
  obtain ⟨y0, hy0⟩ := hFne
  have hN0 : N ≠ 0 := by
    intro h0
    have h1 := hf0 y0 hy0; have h2 := hfneg x0 hx0V hx0F
    rw [hNf, h0, inner_zero_left] at h1 h2; linarith
  have hNF : ∀ x ∈ F, ⟪N, x⟫ = -f 0 := fun x hx => by have := hf0 x hx; rw [hNf] at this; linarith
  -- six on the facet: a pyramid
  by_cases hF6 : F.card = 6
  · have hVF : V.erase x0 = F := by
      apply (eq_of_subset_of_card_le (fun y hy => ?_) (by rw [card_erase_of_mem hx0V]; omega)).symm
      exact mem_erase.mpr ⟨fun e => hx0F (e ▸ hy), hFV.1 hy⟩
    apply isRupert_of_pyramid V x0 hint
    rw [hVF]
    exact coplanar_of_plane hN0 hNF
  -- five on the facet: rotate its normal to `ez`
  have hF5 : F.card = 5 := by omega
  obtain ⟨R, hRSO, r, hr, hRN⟩ := exists_rotation_to_ez_pos N hN0
  set g := R.toEuclideanLin with hg
  have hginj : Function.Injective g := (so3Isometry hRSO).injective
  have hz : ∀ x, g x 2 = ⟪N, x⟫ / r := fun x => by
    have := inner_toEuclideanLin_SO3 hRSO N x
    rw [hRN, real_inner_smul_left, real_inner_comm, inner_ez] at this
    rw [← this, hg]; field_simp
  set h := -f 0 / r with hh
  apply isRupert_of_isRupert_image_rotation R hRSO V
  set V' := V.image g with hV'
  have hfilt : V'.filter (fun y => y 2 = h) = F.image g := by
    ext y; simp only [hV', mem_filter, mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxh⟩
      refine ⟨x, ?_, rfl⟩
      by_contra hxF
      have := hfneg x hx hxF
      rw [hz, hh, div_eq_div_iff hr.ne' hr.ne'] at hxh
      rw [hNf] at this
      have : ⟪N, x⟫ = -f 0 := by nlinarith
      linarith
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hFV.1 hx, rfl⟩, by rw [hz, hNF x hx]⟩
  refine isRupert_face5_std V' h ?_ ?_ ?_ ?_
  · rw [hV', card_image_of_injective _ hginj, hcard]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rw [hz, hh]
    by_cases hxF : x ∈ F
    · rw [hNF x hxF]
    · have := hfneg x hx hxF; rw [hNf] at this
      exact (div_le_div_iff_of_pos_right hr).mpr (by linarith)
  · rw [hfilt]
    refine convPos_of_extreme_plane (h := h) (fun w hw => ?_) (fun w hw hmem => ?_)
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hw; rw [hz, hNF x hx]
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
      apply hext x (hFV.1 hx)
      have e : (((F.image g).erase (g x) : Finset ℝ³) : Set ℝ³) =
          g '' ((F.erase x : Finset ℝ³) : Set ℝ³) := by
        ext y; simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, mem_coe,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨z, hz', rfl⟩, hne⟩; exact ⟨z, ⟨hz', fun e' => hne (by rw [e'])⟩, rfl⟩
        · rintro ⟨z, ⟨hz', hzx⟩, rfl⟩; exact ⟨⟨z, hz', rfl⟩, fun e' => hzx (hginj e')⟩
      rw [e, ← LinearMap.image_convexHull] at hmem
      obtain ⟨z, hzmem, hzx⟩ := hmem
      rw [hginj hzx] at hzmem
      exact convexHull_mono (by
        intro y hy; simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at hy ⊢
        exact ⟨hFV.1 hy.1, hy.2⟩) hzmem
  · rw [hfilt, card_image_of_injective _ hginj, hF5]

/-- **Non-vacuity of Theorem A**: a pentagon in `z = 0` and two points below
satisfy the hypotheses of `isRupert_of_card_seven_of_facet`. -/
example : IsRupert ({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0],
    !₂[0, 0, -1], !₂[1, 0, -2]} : Finset ℝ³) := by
  have hnd : [!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0],
      !₂[0, 0, -1], (!₂[1, 0, -2] : ℝ³)].Nodup := by
    apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  have hV : ({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0],
      !₂[0, 0, -1], !₂[1, 0, -2]} : Finset ℝ³) = [!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0],
      !₂[-2, 0, 0], !₂[0, -2, 0], !₂[0, 0, -1], (!₂[1, 0, -2] : ℝ³)].toFinset := by simp
  have hF : ({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0]} : Finset ℝ³) =
      [!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], (!₂[0, -2, 0] : ℝ³)].toFinset := by
    simp
  apply isRupert_of_card_seven_of_facet _
    {!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0]}
  · rw [hV, List.toFinset_card_of_nodup hnd]; rfl
  · -- a non-degenerate tetrahedron inside
    have hind := affineIndependent_of_det3 (a := !₂[2, 0, 0]) (b := !₂[1, 2, 0])
      (c := !₂[-2, 0, 0]) (d := !₂[0, 0, -1]) (by
        simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
          RCLike.inner_apply, conj_trivial]
        simp [Matrix.cons_val] <;> norm_num)
    have hsub : ({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-2, 0, 0], !₂[0, 0, -1]} : Set ℝ³) ⊆
        ((({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0],
          !₂[0, 0, -1], !₂[1, 0, -2]} : Finset ℝ³) : Set ℝ³)) := by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    have hint := (not_coplanar_iff_interior_convexHull_nonempty _).mp
      (fun hc => not_coplanar_of_affineIndependent hind (hc.subset hsub))
    exact hint
  · refine ⟨fun x hx => ?_, fun h => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
    · have hp := h (show (!₂[0, 0, -1] : ℝ³) ∈ ({!₂[2, 0, 0], !₂[1, 2, 0], !₂[-1, 2, 0],
        !₂[-2, 0, 0], !₂[0, -2, 0], !₂[0, 0, -1], !₂[1, 0, -2]} : Finset ℝ³) by simp)
      rw [hF, List.mem_toFinset] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h1 | h1 | h1 | h1 | h1 <;>
        · have := congrArg (fun v : ℝ³ => v 2) h1; simp at this
  · rw [hF, List.toFinset_card_of_nodup (by
      apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
      simp [List.nodup_cons, Matrix.cons_val] <;> norm_num)]; simp
  · refine ⟨affOf ez 0, fun x hx => ?_, fun x hx hxF => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [ez]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx hxF
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ez]

end Minimality

end
