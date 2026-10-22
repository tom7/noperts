module

public import Minimality.LimitRim

@[expose] public section

/-!
# Two realizing circles: no horizontal-double-normal exception (`FEWER-FACES-PROOFS.md` §22.2)

At a view `u₀` where a labelled rim `X` of `K` is only weakly convex (points of `K` over its
sides: middles of the two faces seen edge-on, the other axle end), Proposition 22.2 tilts the
view to `u₀ + εd` for `d` in an open cone in which every such point is hidden.  The silhouette
of `K` itself is then `X`, with depths `z + ε⟨d, ·⟩`, and Theorem 7.5 (one generic view with a
unimodal silhouette, `isRupert_of_open_unimodal` through `isRupert_of_tilted_unimodal'`) makes
`K` Rupert, whatever the horizontal double normals and the ties of `X` at `u₀`: robust
unimodality at `u₀` is an open condition on the order of the tilted depths.

* `IsRobustUnimodal.isCyclicUnimodal_of_order`: a sequence with distinct entries that keeps
  every strict comparison of a robustly unimodal sequence is unimodal (§18.0: "every small
  perturbation with distinct entries is unimodal"); `IsRobustUnimodal.not_weak_peaks` is the
  core (no weak two-peak pattern).
* `TiltHides`: every point of `V` over a side line of `X` at `u₀`, other than the side's ends,
  lies strictly inside along the tilt `d`.
* **`isRupert_of_tiltHides`** (Proposition 22.2, general form): `X` in `V`, injective, every
  point weakly left of every side at `u₀`, `TiltHides`, robustly unimodal depths at `u₀`; then
  `V` is Rupert.  No horizontal-double-normal hypothesis.
* **`isRupert_of_tendsto_rimCert_or`**: the limit lemma (`isRupert_of_tendsto_rimCert`) with
  "no horizontal double normal at `u`" weakened to "no horizontal double normal at `u`, or the
  limit rim hides its side points along some tilt".
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Robust unimodality is open in the order of the entries -/

theorem zmod_pos_add {k : ℕ} (B : ZMod k) (m j : ℕ) :
    B + (m : ZMod k) + (j : ZMod k) = B + ((m + j : ℕ) : ZMod k) := by
  push_cast; ring

theorem zmod_pos_wrap {k : ℕ} (B : ZMod k) (m : ℕ) :
    B + ((k + m : ℕ) : ZMod k) = B + (m : ZMod k) := by
  push_cast; rw [ZMod.natCast_self]; ring

/-- (R3) read at natural positions `p < q < r < s < p + k` from a base. -/
theorem IsRobustUnimodal.levelRun_nat {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    (B : ZMod k) {p q r s : ℕ} (hpq : p < q) (hqr : q < r) (hrs : r < s) (hs : s < p + k)
    (h : z (B + q) = z (B + r)) :
    ¬ (z (B + p) < z (B + q) ∧ z (B + r) < z (B + s)) ∧
      ¬ (z (B + q) < z (B + p) ∧ z (B + s) < z (B + r)) := by
  have e : ∀ m, p ≤ m → B + (p : ZMod k) + ((m - p : ℕ) : ZMod k) = B + (m : ZMod k) := by
    intro m hm; rw [zmod_pos_add, Nat.add_sub_cancel' hm]
  have := hz.noLevelRun (B + p) 0 (q - p) (r - p) (s - p) (by omega) (by omega) (by omega)
    (by omega) (by rw [e q hpq.le, e r (by omega)]; exact h)
  rwa [Nat.cast_zero, add_zero, e q hpq.le, e r (by omega), e s (by omega)] at this

/-- (R1) read at natural positions `p < q < r < s < p + k` from a base. -/
theorem IsRobustUnimodal.peaks_nat {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    (B : ZMod k) {p q r s : ℕ} (hpq : p < q) (hqr : q < r) (hrs : r < s) (hs : s < p + k) :
    ¬ (z (B + q) < z (B + p) ∧ z (B + q) < z (B + r) ∧ z (B + s) < z (B + p) ∧
      z (B + s) < z (B + r)) := by
  have e : ∀ m, p ≤ m → B + (p : ZMod k) + ((m - p : ℕ) : ZMod k) = B + (m : ZMod k) := by
    intro m hm; rw [zmod_pos_add, Nat.add_sub_cancel' hm]
  have := hz.noPeaks (B + p) 0 (q - p) (r - p) (s - p) (by omega) (by omega) (by omega)
    (by omega)
  rwa [Nat.cast_zero, add_zero, e q hpq.le, e r (by omega), e s (by omega)] at this

/-- **No weak two-peak pattern.**  At positions `0 < c < n < d < k` from a base, a robustly
unimodal sequence never has both `c` and `d` weakly below both `0` and `n`. -/
theorem IsRobustUnimodal.not_weak_peaks {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    (B : ZMod k) {c n d : ℕ} (h0c : 0 < c) (hcn : c < n) (hnd : n < d) (hdk : d < k)
    (h1 : z (B + c) ≤ z (B + (0 : ℕ))) (h2 : z (B + c) ≤ z (B + n))
    (h3 : z (B + d) ≤ z (B + (0 : ℕ))) (h4 : z (B + d) ≤ z (B + n)) : False := by
  have w0 : z (B + ((k + 0 : ℕ) : ZMod k)) = z (B + (0 : ℕ)) := by rw [zmod_pos_wrap]
  have wc : z (B + ((k + c : ℕ) : ZMod k)) = z (B + c) := by rw [zmod_pos_wrap]
  have wn : z (B + ((k + n : ℕ) : ZMod k)) = z (B + n) := by rw [zmod_pos_wrap]
  rw [Nat.add_zero] at w0
  have ne : ∀ a b : ℕ, a < k → b < k → a ≠ b → B + (a : ZMod k) ≠ B + (b : ZMod k) :=
    fun a b ha hb hab => zmod_add_ne ha hb hab B
  have triple : ∀ a b c' : ℕ, a < k → b < k → c' < k → a ≠ b → b ≠ c' → a ≠ c' →
      z (B + a) = z (B + b) → z (B + b) = z (B + c') → False :=
    fun a b c' ha hb hc hab hbc hac e1 e2 =>
      hz.noTriple _ _ _ (ne a b ha hb hab) (ne b c' hb hc hbc) (ne a c' ha hc hac) e1 e2
  rcases h1.lt_or_eq with h1 | h1 <;> rcases h2.lt_or_eq with h2 | h2 <;>
    rcases h3.lt_or_eq with h3 | h3 <;> rcases h4.lt_or_eq with h4 | h4
  · exact hz.peaks_nat B (p := 0) (q := c) (r := n) (s := d) h0c hcn hnd (by omega)
      ⟨h1, h2, h3, h4⟩
  · -- `d` level with `n`: `c < n = d < 0`
    exact (hz.levelRun_nat B (p := c) (q := n) (r := d) (s := k) hcn hnd hdk (by omega)
      h4.symm).1 ⟨h2, by rw [w0]; exact h3⟩
  · -- `d` level with `0`: `n > d = 0 > c`
    exact (hz.levelRun_nat B (p := n) (q := d) (r := k) (s := k + c) hnd hdk (by omega)
      (by omega) (by rw [w0]; exact h3)).2 ⟨h4, by rw [w0, wc]; exact h1⟩
  · exact triple 0 n d (by omega) (by omega) hdk (by omega) (by omega) (by omega)
      (by rw [← h3, h4]) h4.symm
  · -- `c` level with `n`: `0 > c = n > d`
    exact (hz.levelRun_nat B (p := 0) (q := c) (r := n) (s := d) h0c hcn hnd (by omega)
      h2).2 ⟨h1, h4⟩
  · exact triple c n d (by omega) (by omega) hdk (by omega) (by omega) (by omega) h2 h4.symm
  · linarith
  · exact triple c n d (by omega) (by omega) hdk (by omega) (by omega) (by omega) h2 h4.symm
  · -- `c` level with `0`: `d < 0 = c < n`
    exact (hz.levelRun_nat B (p := d) (q := k) (r := k + c) (s := k + n) hdk (by omega)
      (by omega) (by omega) (by rw [w0, wc]; exact h1.symm)).1
        ⟨by rw [w0]; exact h3, by rw [wc, wn]; exact h2⟩
  · linarith
  · exact triple 0 c d (by omega) (by omega) hdk (by omega) (by omega) (by omega) h1.symm
      (h1.trans h3.symm)
  · exact triple 0 c d (by omega) (by omega) hdk (by omega) (by omega) (by omega) h1.symm
      (h1.trans h3.symm)
  all_goals
    exact triple 0 c n (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      h1.symm h2

/-- **Robust unimodality is open** (§18.0): a sequence with distinct entries that keeps every
strict comparison of a robustly unimodal sequence is cyclically unimodal. -/
theorem IsRobustUnimodal.isCyclicUnimodal_of_order {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {z z' : ZMod k → ℝ} (hz : IsRobustUnimodal z) (hord : ∀ i j, z i < z j → z' i < z' j)
    (hinj : Function.Injective z') : IsCyclicUnimodal z' := by
  refine isCyclicUnimodal_of_localMax_unique (by omega) z' hinj ?_
  intro a b ha1 ha2 hb1 hb2
  by_contra hab
  have hle : ∀ i j, z' i < z' j → z i ≤ z j := fun i j h =>
    not_lt.mp fun h' => lt_asymm h (hord j i h')
  set n := (b - a).val with hn
  have hb : b = a + (n : ZMod k) := by rw [hn, ZMod.natCast_zmod_val]; ring
  have hnk : n < k := ZMod.val_lt _
  have hn0 : n ≠ 0 := by
    intro h0
    apply hab
    rw [hb, h0, Nat.cast_zero, add_zero]
  have hn1 : n ≠ 1 := by
    intro h1
    rw [hb, h1, Nat.cast_one, add_sub_cancel_right] at hb1
    exact lt_asymm ha2 hb1
  have hnk1 : n ≠ k - 1 := by
    intro h1
    have e : b + 1 = a := by
      rw [hb, h1, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    have e' : a - 1 = b := by rw [← e]; ring
    rw [e] at hb2
    rw [e'] at ha1
    exact lt_asymm ha1 hb2
  -- the least entry strictly between `a` and `b`, and strictly between `b` and `a`
  obtain ⟨c, hc, hcmin⟩ := (Finset.Ioo 0 n).exists_min_image (fun m => z' (a + (m : ZMod k)))
    ⟨1, by simp only [Finset.mem_Ioo]; omega⟩
  obtain ⟨d, hd, hdmin⟩ := (Finset.Ioo n k).exists_min_image (fun m => z' (a + (m : ZMod k)))
    ⟨n + 1, by simp only [Finset.mem_Ioo]; omega⟩
  simp only [Finset.mem_Ioo] at hc hd
  have e1 : a + ((1 : ℕ) : ZMod k) = a + 1 := by rw [Nat.cast_one]
  have en1 : a + ((n - 1 : ℕ) : ZMod k) = b - 1 := by
    rw [hb, Nat.cast_sub (by omega), Nat.cast_one]; ring
  have en2 : a + ((n + 1 : ℕ) : ZMod k) = b + 1 := by
    rw [hb, Nat.cast_add, Nat.cast_one]; ring
  have ek : a + ((k - 1 : ℕ) : ZMod k) = a - 1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
  have c1 : z' (a + (c : ZMod k)) < z' (a + ((0 : ℕ) : ZMod k)) := by
    have := hcmin 1 (by simp only [Finset.mem_Ioo]; omega)
    rw [e1] at this
    rw [Nat.cast_zero, add_zero]; exact lt_of_le_of_lt this ha2
  have c2 : z' (a + (c : ZMod k)) < z' (a + (n : ZMod k)) := by
    have := hcmin (n - 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [en1] at this
    rw [← hb]; exact lt_of_le_of_lt this hb1
  have c3 : z' (a + (d : ZMod k)) < z' (a + ((0 : ℕ) : ZMod k)) := by
    have := hdmin (k - 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [ek] at this
    rw [Nat.cast_zero, add_zero]; exact lt_of_le_of_lt this ha1
  have c4 : z' (a + (d : ZMod k)) < z' (a + (n : ZMod k)) := by
    have := hdmin (n + 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [en2] at this
    rw [← hb]; exact lt_of_le_of_lt this hb2
  exact hz.not_weak_peaks a hc.1 hc.2 hd.1 hd.2 (hle _ _ c1) (hle _ _ c2) (hle _ _ c3)
    (hle _ _ c4)

/-! ### Proposition 22.2: a tilt that hides the side points -/

/-- **The tilt `d` hides the side points of `X` at `u`**: every point of `V` over the line of a
side of `X` at `u`, other than the side's ends, lies strictly left of that side along `d`. -/
def TiltHides {k : ℕ} (V : Finset ℝ³) (u d : ℝ³) (X : ZMod k → ℝ³) : Prop :=
  ∀ z ∈ V, ∀ i, z ≠ X i → z ≠ X (i + 1) → det3 (X (i + 1) - X i) (z - X i) u = 0 →
    0 < det3 (X (i + 1) - X i) (z - X i) d

/-- **Proposition 22.2, general form.**  At the view `u`, the cycle `X` of points of `V` has
every point of `V` weakly left of every side, its depths are robustly unimodal, and some tilt
`d` hides every point over a side line (`TiltHides`).  Then for all small `ε > 0` the
silhouette at `u + εd` is `X` with every other point strictly inside, its depth order refines
that at `u`, and `V` is Rupert by Theorem 7.5 — with no condition on the horizontal double
normals or the ties of `X` at `u`. -/
theorem isRupert_of_tiltHides (V : Finset ℝ³) (u d : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (X : ZMod k → ℝ³) (hXV : ∀ i, X i ∈ V) (hinj : Function.Injective X)
    (hleft : ∀ z ∈ V, ∀ i, 0 ≤ det3 (X (i + 1) - X i) (z - X i) u)
    (hhide : TiltHides V u d X) (hz : IsRobustUnimodal (fun i => ⟪X i, u⟫)) : IsRupert V := by
  classical
  have tilt : ∀ z ∈ V, ∀ i, z ≠ X i → z ≠ X (i + 1) →
      TiltSign (X (i + 1) - X i) (z - X i) u d := by
    intro z hz i h1 h2
    rcases (hleft z hz i).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, hhide z hz i h1 h2 h.symm⟩
  set z0 : ZMod k → ℝ := fun i => ⟪X i, u⟫ with hz0
  refine isRupert_of_tilted_unimodal' V u d hu hk X hXV
    (fun i j h1 h2 => tilt _ (hXV j) i (hinj.ne h1) (hinj.ne h2))
    (fun y hy hyx i => tilt y hy i (hyx i) (hyx (i + 1)))
    (fun z => ∀ i j, z0 i < z0 j → z i < z j) ?_ ?_ ?_ ?_
  · have e : {z : ZMod k → ℝ | ∀ i j, z0 i < z0 j → z i < z j} =
        ⋂ i, ⋂ j, {z : ZMod k → ℝ | z0 i < z0 j → z i < z j} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases h : z0 i < z0 j
    · simp only [h, true_implies]
      exact isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp only [h, false_implies, Set.ofPred_true]
      exact isOpen_univ
  · intro z c hc hQ i j h
    exact mul_lt_mul_of_pos_left (hQ i j h) hc
  · refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases h : z0 i < z0 j
    · filter_upwards [eventually_pos_affine (A := z0 j - z0 i) (B := ⟪X j, d⟫ - ⟪X i, d⟫)
        (Or.inl (by linarith))] with ε hε _
      simp only [inner_add_right, real_inner_smul_right]
      simp only [hz0] at hε
      linarith
    · exact Eventually.of_forall fun _ h' => absurd h' h
  · intro z hzinj hQ
    exact hz.isCyclicUnimodal_of_order hk hQ hzinj

/-! ### The limit lemma with the tilt alternative -/

/-- The labels of a rim certificate are distinct. -/
theorem RimCertAt.lab_injective {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) : Function.Injective lab := by
  have hk := h.three
  intro i j hij
  by_contra hne
  by_cases h1 : j = i + 1
  · have h2 : i - 1 ≠ i := zmod_sub_one_ne hk i
    have h3 : i - 1 ≠ i + 1 := zmod_sub_one_ne_add_one hk i
    have := h.cyc i (i - 1) h2 h3
    rw [← h1, ← hij, sub_self] at this
    simp [det3_expand] at this
  · have := h.cyc i j (Ne.symm hne) h1
    rw [← hij, sub_self] at this
    simp [det3_expand] at this

/-- **Lemma 18.2 with Proposition 22.2.**  As `isRupert_of_tendsto_rimCert`, with the
horizontal-double-normal hypothesis at the limit view weakened: either there is no horizontal
double normal at `u`, or (given that every point of `x` lies weakly left of every side of the
labelled rim at `u`, which the limit provides) some tilt hides the points over its side lines.
In the second case the labelled rim itself, robustly unimodal at `u` by the limit, is the
silhouette along the tilt (`isRupert_of_tiltHides`). -/
theorem isRupert_of_tendsto_rimCert_or {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    {k : ℕ} [NeZero k] (lab : ZMod k → Fin n) {u : ℝ³} (hu : u ≠ 0)
    (hnd : NoHDNAt (univ.image x) u ∨
      ((∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u) →
        ∃ d, TiltHides (univ.image x) u d (fun i => x (lab i))))
    {ι : Type*} {l : Filter ι} (xs : ι → Fin n → ℝ³) (us : ι → ℝ³)
    (hxs : ∀ m, Tendsto (fun t => xs t m) l (𝓝 (x m))) (hus : Tendsto us l (𝓝 u))
    (hcert : ∃ᶠ t in l, RimCertAt (xs t) (us t) lab ∧
      ∀ i j, ⟪x (lab i), u⟫ = ⟪x (lab j), u⟫ → ⟪xs t (lab i), us t⟫ = ⟪xs t (lab j), us t⟫) :
    IsRupert (univ.image x) := by
  classical
  rcases hnd with hnd | hsec
  · exact isRupert_of_tendsto_rimCert x hseg hsp lab hu hnd xs us hxs hus hcert
  have hc := hcert.mono fun _ h => h.1
  obtain ⟨t₀, ht₀⟩ := hc.exists
  have hk := ht₀.three
  have hlab : Function.Injective lab := ht₀.lab_injective
  have hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u := by
    intro m i
    exact le_of_tendsto_frequently tendsto_const_nhds
      (Tendsto.det3' ((hxs _).sub (hxs _)) ((hxs _).sub (hxs _)) hus)
      (hc.mono fun t ht => ht.left m i)
  obtain ⟨d, hd⟩ := hsec hleft
  have hZ : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫) :=
    isRobustUnimodal_of_tendsto_ties (fun i => (hxs (lab i)).inner hus)
      (hcert.mono fun t ht => ⟨ht.1.robust, ht.2⟩)
  refine isRupert_of_tiltHides (univ.image x) u d hu hk (fun i => x (lab i))
    (fun i => mem_image_of_mem x (mem_univ _)) (hx.comp hlab) ?_ hd hZ
  intro z hz i
  obtain ⟨m, -, rfl⟩ := mem_image.mp hz
  exact hleft m i


/-! ### Two triangles seen edge-on: the tilt exists (Proposition 22.2 for triangles) -/

/-- `z` is a vertex of the triangle `p q r`. -/
def InTri (p q r z : ℝ³) : Prop := z = p ∨ z = q ∨ z = r

/-- **(G1) for two faces at a view** (§22.0, standing assumption): every point `y` of `V` on a
support line `ab` of the shadow at `u` (`a`, `b` with distinct projections, every point weakly
left), other than `a` and `b`, lies with `a` and `b` on one of the triangles `p₁ q₁ r₁`,
`p₂ q₂ r₂`.  A third point on a far side line, or a point over a far corner, breaks it: one
condition on the shape, so with a horizontal double normal at `u` codimension 2 (§22.4). -/
def G1Tri (V : Finset ℝ³) (u p₁ q₁ r₁ p₂ q₂ r₂ : ℝ³) : Prop :=
  ∀ a ∈ V, ∀ b ∈ V, ∀ y ∈ V, cross (b - a) u ≠ 0 → (∀ z ∈ V, 0 ≤ det3 (b - a) (z - a) u) →
    det3 (b - a) (y - a) u = 0 → y ≠ a → y ≠ b →
    (InTri p₁ q₁ r₁ a ∧ InTri p₁ q₁ r₁ b ∧ InTri p₁ q₁ r₁ y) ∨
      (InTri p₂ q₂ r₂ a ∧ InTri p₂ q₂ r₂ b ∧ InTri p₂ q₂ r₂ y)

theorem inTri_third_unique {p q r a b t t' : ℝ³} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (ha : InTri p q r a) (hb : InTri p q r b) (ht : InTri p q r t) (ht' : InTri p q r t')
    (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) (ht'a : t' ≠ a) (ht'b : t' ≠ b) : t = t' := by
  unfold InTri at *
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl <;> simp_all

theorem inTri_no_four {p q r a b c d : ℝ³} (ha : InTri p q r a) (hb : InTri p q r b)
    (hc : InTri p q r c) (hd : InTri p q r d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  unfold InTri at *
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> simp_all

theorem cross_tri_rot (a b y : ℝ³) : cross (b - a) (y - a) = cross (y - b) (a - b) := by
  ext j; fin_cases j <;> simp [cross] <;> ring

/-- The cross product of a triangle's two edges at a vertex is `± (q − p) × (r − p)`. -/
theorem cross_inTri {p q r a b y : ℝ³} (ha : InTri p q r a) (hb : InTri p q r b)
    (hy : InTri p q r y) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    cross (b - a) (y - a) = cross (q - p) (r - p) ∨
      cross (b - a) (y - a) = -cross (q - p) (r - p) := by
  unfold InTri at *
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl <;> first
    | exact absurd rfl hab | exact absurd rfl hya | exact absurd rfl hyb
    | (left; ext j; fin_cases j <;> simp [cross] <;> ring1)
    | (right; ext j; fin_cases j <;> simp [cross] <;> ring1)

/-- **One side constraint per triangle.**  Two sides of the injective cycle `X` that lie on the
triangle `p q r`, each with the triangle's third vertex, give the same cross product: the sides
are equal, or consecutive, and the triples are cyclic rotations of each other. -/
theorem cross_tri_sides {k : ℕ} [NeZero k] (hk : 3 ≤ k) {X : ZMod k → ℝ³}
    (hX : Function.Injective X) {p q r : ℝ³} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {i i' : ZMod k} {y y' : ℝ³}
    (h1 : InTri p q r (X i)) (h2 : InTri p q r (X (i + 1))) (h3 : InTri p q r y)
    (h4 : y ≠ X i) (h5 : y ≠ X (i + 1))
    (h1' : InTri p q r (X i')) (h2' : InTri p q r (X (i' + 1))) (h3' : InTri p q r y')
    (h4' : y' ≠ X i') (h5' : y' ≠ X (i' + 1)) :
    cross (X (i + 1) - X i) (y - X i) = cross (X (i' + 1) - X i') (y' - X i') := by
  have nx : ∀ j : ZMod k, X j ≠ X (j + 1) := fun j => hX.ne (zmod_ne_add_one (by omega) j)
  have n2 : ∀ j : ZMod k, X (j + 1 + 1) ≠ X j := by
    intro j h
    have := hX h
    have h2 : (2 : ZMod k) = 0 := by linear_combination this
    have : ((2 : ℕ) : ZMod k) = ((0 : ℕ) : ZMod k) := by exact_mod_cast h2
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 2 < k), Nat.zero_mod] at this
    omega
  by_cases e1 : i' = i
  · subst i'
    rw [inTri_third_unique hpq hqr hpr h1 h2 h3 h3' (nx i) h4 h5 h4' h5']
  by_cases e2 : i' = i + 1
  · subst i'
    -- `X (i + 2)` is the third vertex `y`, and `y'` is `X i`
    have hy : X (i + 1 + 1) = y := inTri_third_unique hpq hqr hpr h1 h2 h2' h3 (nx i)
      (n2 i) (nx (i + 1)).symm h4 h5
    have hy' : y' = X i := inTri_third_unique hpq hqr hpr h1' h2' h3' h1 (nx (i + 1)) h4'
      h5' (nx i) (n2 i).symm
    rw [hy, hy']
    ext j; fin_cases j <;> simp [cross] <;> ring
  by_cases e3 : i = i' + 1
  · subst i
    have hy : X (i' + 1 + 1) = y' := inTri_third_unique hpq hqr hpr h1' h2' h2 h3' (nx i')
      (n2 i') (nx (i' + 1)).symm h4' h5'
    have hy' : y = X i' := inTri_third_unique hpq hqr hpr h1 h2 h3 h1' (nx (i' + 1)) h4
      h5 (nx i') (n2 i').symm
    rw [hy, hy']
    ext j; fin_cases j <;> simp [cross] <;> ring
  exfalso
  have d1 : i ≠ i' := Ne.symm e1
  have d2 : i ≠ i' + 1 := e3
  have d3 : i + 1 ≠ i' := Ne.symm e2
  have d4 : i + 1 ≠ i' + 1 := fun h => d1 (add_right_cancel h)
  exact inTri_no_four h1 h2 h1' h2' (nx i) (hX.ne d1) (hX.ne d2) (hX.ne d3) (hX.ne d4) (nx i')

/-- The constraints of one triangle: all side constraints of `X` on the triangle share one
cross product `M = ± (q − p) × (r − p)`. -/
theorem exists_tri_normal {k : ℕ} [NeZero k] (hk : 3 ≤ k) {X : ZMod k → ℝ³}
    (hX : Function.Injective X) {p q r : ℝ³} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    ∃ M : ℝ³, (M = cross (q - p) (r - p) ∨ M = -cross (q - p) (r - p)) ∧
      ∀ i y, InTri p q r (X i) → InTri p q r (X (i + 1)) → InTri p q r y → y ≠ X i →
        y ≠ X (i + 1) → cross (X (i + 1) - X i) (y - X i) = M := by
  by_cases h : ∃ i y, InTri p q r (X i) ∧ InTri p q r (X (i + 1)) ∧ InTri p q r y ∧
      y ≠ X i ∧ y ≠ X (i + 1)
  · obtain ⟨i₀, y₀, a1, a2, a3, a4, a5⟩ := h
    refine ⟨cross (X (i₀ + 1) - X i₀) (y₀ - X i₀),
      cross_inTri a1 a2 a3 (hX.ne (zmod_ne_add_one (by omega) i₀)) a4 a5,
      fun i y b1 b2 b3 b4 b5 => cross_tri_sides hk hX hpq hqr hpr b1 b2 b3 b4 b5 a1 a2 a3 a4 a5⟩
  · push Not at h
    exact ⟨_, Or.inl rfl, fun i y b1 b2 b3 b4 b5 => absurd (h i y b1 b2 b3 b4) b5⟩

theorem inner_cross_cross_self (a b : ℝ³) : ⟪a, cross b (cross a b)⟫ = ⟪cross a b, cross a b⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp; ring

theorem inner_cross_cross_zero (a b : ℝ³) : ⟪b, cross b (cross a b)⟫ = 0 := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp; ring

/-- **Proposition 22.2, the cone of tilts.**  Every point over a side line of `X` at `u` lies,
with the side's ends, on one of two faces seen edge-on, and its constraint on the tilt,
`[X (i+1) − X i, z − X i, d] > 0`, is `⟪c M, d⟫ > 0` for `c > 0` and `M` the oriented normal
`M₁` or `M₂` of its face (the closing is realized on both face circles: the hidden points of each
face lie on one side of its chord).  If the two normals are not parallel, one tilt hides every
side point: `d` in the open cone `⟪M₁, d⟫ > 0`, `⟪M₂, d⟫ > 0`. -/
theorem exists_tiltHides_of_normals (V : Finset ℝ³) (u : ℝ³) {k : ℕ} (X : ZMod k → ℝ³)
    {M₁ M₂ : ℝ³} (hW : cross M₁ M₂ ≠ 0)
    (hcons : ∀ z ∈ V, ∀ i, z ≠ X i → z ≠ X (i + 1) → det3 (X (i + 1) - X i) (z - X i) u = 0 →
      ∃ c : ℝ, 0 < c ∧ (cross (X (i + 1) - X i) (z - X i) = c • M₁ ∨
        cross (X (i + 1) - X i) (z - X i) = c • M₂)) :
    ∃ d, TiltHides V u d X := by
  have hWW : 0 < ⟪cross M₁ M₂, cross M₁ M₂⟫ := real_inner_self_pos.mpr hW
  set d := cross M₂ (cross M₁ M₂) + cross M₁ (cross M₂ M₁) with hd
  have hd₁ : 0 < ⟪M₁, d⟫ := by
    have e2 : ⟪M₁, cross M₁ (cross M₂ M₁)⟫ = 0 := inner_cross_cross_zero M₂ M₁
    rw [hd, inner_add_right, inner_cross_cross_self, e2, add_zero]; exact hWW
  have hd₂ : 0 < ⟪M₂, d⟫ := by
    have e1 : ⟪M₂, cross M₂ (cross M₁ M₂)⟫ = 0 := inner_cross_cross_zero M₁ M₂
    have e3 : ⟪cross M₂ M₁, cross M₂ M₁⟫ = ⟪cross M₁ M₂, cross M₁ M₂⟫ := by
      simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
      simp; ring
    rw [hd, inner_add_right, e1, inner_cross_cross_self, e3, zero_add]; exact hWW
  refine ⟨d, fun z hz i h1 h2 h0 => ?_⟩
  obtain ⟨c, hc, h | h⟩ := hcons z hz i h1 h2 h0
  · rw [det3, h, real_inner_smul_left]; exact mul_pos hc hd₁
  · rw [det3, h, real_inner_smul_left]; exact mul_pos hc hd₂

/-- **Proposition 22.2 for two triangles.**  At a view `u` where every point over a support line
of the shadow lies on one of two triangles together with the line's ends (`G1Tri`), and the
triangles' planes are not parallel, every rim `X` of points of `V` with nondegenerate sides and
every point weakly left of every side has a tilt that hides its side points.  (A triangle has
one constraint, so every closing at two triangles is realized on both circles.) -/
theorem exists_tiltHides_tri (V : Finset ℝ³) (u : ℝ³) {p₁ q₁ r₁ p₂ q₂ r₂ : ℝ³}
    (h₁ : p₁ ≠ q₁ ∧ q₁ ≠ r₁ ∧ p₁ ≠ r₁) (h₂ : p₂ ≠ q₂ ∧ q₂ ≠ r₂ ∧ p₂ ≠ r₂)
    (hC : cross (cross (q₁ - p₁) (r₁ - p₁)) (cross (q₂ - p₂) (r₂ - p₂)) ≠ 0)
    (hG : G1Tri V u p₁ q₁ r₁ p₂ q₂ r₂)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (hXV : ∀ i, X i ∈ V)
    (hinj : Function.Injective X)
    (hleft : ∀ z ∈ V, ∀ i, 0 ≤ det3 (X (i + 1) - X i) (z - X i) u)
    (hside : ∀ i, cross (X (i + 1) - X i) u ≠ 0) :
    ∃ d, TiltHides V u d X := by
  obtain ⟨M₁, hM₁, hc₁⟩ := exists_tri_normal hk hinj h₁.1 h₁.2.1 h₁.2.2
  obtain ⟨M₂, hM₂, hc₂⟩ := exists_tri_normal hk hinj h₂.1 h₂.2.1 h₂.2.2
  have hW : cross M₁ M₂ ≠ 0 := by
    intro h0; apply hC
    have e : ∀ a b : ℝ³, cross (-a) b = -cross a b ∧ cross a (-b) = -cross a b := by
      intro a b; constructor <;> (ext j; fin_cases j <;> simp [cross] <;> ring)
    rcases hM₁ with rfl | rfl <;> rcases hM₂ with rfl | rfl
    · exact h0
    · rw [(e _ _).2, neg_eq_zero] at h0; exact h0
    · rw [(e _ _).1, neg_eq_zero] at h0; exact h0
    · rw [(e _ _).1, (e _ _).2, neg_neg] at h0; exact h0
  refine exists_tiltHides_of_normals V u X hW fun z hz i h1 h2 h0 => ?_
  rcases hG _ (hXV i) _ (hXV (i + 1)) z hz (hside i) (fun z' hz' => hleft z' hz' i) h0 h1 h2 with
    ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · exact ⟨1, one_pos, Or.inl (by rw [one_smul]; exact hc₁ i z a1 a2 a3 h1 h2)⟩
  · exact ⟨1, one_pos, Or.inr (by rw [one_smul]; exact hc₂ i z a1 a2 a3 h1 h2)⟩


/-! ### (G1) at a view: invariance and the sides of the rim -/

/-- **No two points over one point, except `e₁, e₂`** (the axle of an edge view; `e₁ = e₂`
for a vertex view, where it says that no segment is parallel to the view). -/
def ParOnly (V : Finset ℝ³) (u e₁ e₂ : ℝ³) : Prop :=
  ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → cross (y' - y) u = 0 → (y = e₁ ∧ y' = e₂) ∨ (y = e₂ ∧ y' = e₁)

theorem cross_neg_right' (a b : ℝ³) : cross a (-b) = -cross a b := by
  ext j; fin_cases j <;> simp [cross] <;> ring

theorem ParOnly.smul {V : Finset ℝ³} {u e₁ e₂ : ℝ³} (h : ParOnly V u e₁ e₂) {c : ℝ}
    (hc : c ≠ 0) : ParOnly V (c • u) e₁ e₂ := by
  intro y hy y' hy' hne h0
  rw [cross_smul_right' _ c u, smul_eq_zero] at h0
  exact h y hy y' hy' hne (h0.resolve_left hc)

theorem det3_swap_base (a b z u : ℝ³) :
    det3 (a - b) (z - b) u = -det3 (b - a) (z - a) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem G1Tri.neg {V : Finset ℝ³} {u p₁ q₁ r₁ p₂ q₂ r₂ : ℝ³}
    (h : G1Tri V u p₁ q₁ r₁ p₂ q₂ r₂) : G1Tri V (-u) p₁ q₁ r₁ p₂ q₂ r₂ := by
  intro a ha b hb y hy hc hl h0 hya hyb
  have hc' : cross (a - b) u ≠ 0 := by
    intro e; apply hc
    have : cross (a - b) u = cross (b - a) (-u) := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this] at e; exact e
  have hl' : ∀ z ∈ V, 0 ≤ det3 (a - b) (z - b) u := by
    intro z hz
    have := hl z hz
    rw [det3_neg_right] at this
    rw [det3_swap_base]; linarith
  have h0' : det3 (a - b) (y - b) u = 0 := by
    rw [det3_neg_right, neg_eq_zero] at h0
    rw [det3_swap_base, h0, neg_zero]
  rcases h b hb a ha y hy hc' hl' h0' hyb hya with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · exact Or.inl ⟨a2, a1, a3⟩
  · exact Or.inr ⟨a2, a1, a3⟩

theorem G1Tri.sigma {V : Finset ℝ³} {u p₁ q₁ r₁ p₂ q₂ r₂ : ℝ³}
    (h : G1Tri V u p₁ q₁ r₁ p₂ q₂ r₂) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    G1Tri V (σ • u) p₁ q₁ r₁ p₂ q₂ r₂ := by
  rcases hσ with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]; exact h.neg

/-- **The sides of the limit rim are not seen end-on**: with `ParOnly`, two consecutive labels
over one point are the exceptional pair, which the certificates never take as consecutive
labels. -/
theorem side_cross_ne_of_parOnly {n k : ℕ} {x : Fin n → ℝ³} (hx : Function.Injective x)
    {lab : ZMod k → Fin n} (hlab : Function.Injective lab) {u : ℝ³} {i₀ j₀ : Fin n}
    (hpar : ParOnly (univ.image x) u (x i₀) (x j₀))
    (hnot : ∀ m : ZMod k, ¬ ((lab m = i₀ ∧ lab (m + 1) = j₀) ∨ (lab m = j₀ ∧ lab (m + 1) = i₀)))
    (hk : 2 ≤ k) : ∀ m, cross (x (lab (m + 1)) - x (lab m)) u ≠ 0 := by
  intro m h0
  have hne : x (lab m) ≠ x (lab (m + 1)) := (hx.comp hlab).ne (zmod_ne_add_one hk m)
  rcases hpar _ (mem_image_of_mem x (mem_univ _)) _ (mem_image_of_mem x (mem_univ _)) hne h0 with
    ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hnot m (Or.inl ⟨hx e1, hx e2⟩)
  · exact hnot m (Or.inr ⟨hx e1, hx e2⟩)

/-- At an edge view (`u` a nonzero multiple of `y j₀ − y i₀`), a rim certificate never has
`i₀`, `j₀` as consecutive labels. -/
theorem RimCertAt.not_axle {n k : ℕ} {y : Fin n → ℝ³} {c : ℝ} {i₀ j₀ : Fin n}
    {lab : ZMod k → Fin n} (h : RimCertAt y (c • (y j₀ - y i₀)) lab) (m : ZMod k) :
    ¬ ((lab m = i₀ ∧ lab (m + 1) = j₀) ∨ (lab m = j₀ ∧ lab (m + 1) = i₀)) := by
  have hk := h.three
  have := h.cyc m (m - 1) (zmod_sub_one_ne hk m) (zmod_sub_one_ne_add_one hk m)
  rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> rw [e1, e2] at this <;>
    simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this <;>
    nlinarith

/-- **Proposition 22.2 at a two-triangle view, from the limit**: with `ParOnly` (exceptional
pair not consecutive on the rim), `G1Tri` and non-parallel face planes, the limit rim has a
hiding tilt. -/
theorem exists_tiltHides_limit {n k : ℕ} [NeZero k] {x : Fin n → ℝ³}
    (hx : Function.Injective x) {lab : ZMod k → Fin n} (hk : 3 ≤ k)
    (hlab : Function.Injective lab) {u : ℝ³} {i₀ j₀ : Fin n}
    (hpar : ParOnly (univ.image x) u (x i₀) (x j₀))
    (hnot : ∀ m : ZMod k, ¬ ((lab m = i₀ ∧ lab (m + 1) = j₀) ∨ (lab m = j₀ ∧ lab (m + 1) = i₀)))
    {p₁ q₁ r₁ p₂ q₂ r₂ : ℝ³}
    (h₁ : p₁ ≠ q₁ ∧ q₁ ≠ r₁ ∧ p₁ ≠ r₁) (h₂ : p₂ ≠ q₂ ∧ q₂ ≠ r₂ ∧ p₂ ≠ r₂)
    (hC : cross (cross (q₁ - p₁) (r₁ - p₁)) (cross (q₂ - p₂) (r₂ - p₂)) ≠ 0)
    (hG : G1Tri (univ.image x) u p₁ q₁ r₁ p₂ q₂ r₂)
    (hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u) :
    ∃ d, TiltHides (univ.image x) u d (fun i => x (lab i)) :=
  exists_tiltHides_tri (univ.image x) u h₁ h₂ hC hG hk _
    (fun i => mem_image_of_mem x (mem_univ _)) (hx.comp hlab)
    (fun z hz i => by obtain ⟨m, -, rfl⟩ := mem_image.mp hz; exact hleft m i)
    (side_cross_ne_of_parOnly hx hlab hpar hnot (by omega))

/-- `(A × B) × (A × C) = det (A, B, C) A`: two triangles on a common edge `A` have
non-parallel planes iff the fourth point is off the first plane. -/
theorem cross_cross_common (A B C : ℝ³) :
    cross (cross A B) (cross A C) = det3 A B C • A := by
  ext j; fin_cases j <;> simp [cross, det3_expand] <;> ring


/-- Three distinct points of a set in convex position (no point inside a segment of two others)
are not collinear. -/
theorem cross_ne_zero_of_noSeg {n : ℕ} {x : Fin n → ℝ³} (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {i j a : Fin n} (hij : i ≠ j) (hia : i ≠ a) (hja : j ≠ a) :
    cross (x j - x i) (x a - x i) ≠ 0 := by
  intro h0
  have he : x j - x i ≠ 0 := sub_ne_zero.mpr (hx.ne hij).symm
  set t := ⟪x a - x i, x j - x i⟫ / ⟪x j - x i, x j - x i⟫
  have ht : x a - x i = t • (x j - x i) := eq_smul_of_cross_eq_zero he h0
  have ha : x a = x i + t • (x j - x i) := by rw [← ht]; abel
  rcases lt_trichotomy t 0 with h | h | h
  · -- `i` lies between `a` and `j`
    refine hseg a j i (hx.ne hia) (hx.ne hij) (-t / (1 - t)) (div_pos (by linarith) (by linarith))
      ((div_lt_one (by linarith)).mpr (by linarith)) ?_
    rw [ha]
    have h1 : (1 - t) ≠ 0 := by linarith
    have : x i + t • (x j - x i) + (-t / (1 - t)) • (x j - (x i + t • (x j - x i))) =
        x i + (t + (-t / (1 - t)) * (1 - t)) • (x j - x i) := by module
    rw [this, div_mul_cancel₀ _ h1, add_neg_cancel, zero_smul, add_zero]
  · exact hx.ne hia (by rw [ha, h, zero_smul, add_zero])
  · rcases lt_trichotomy t 1 with h' | h' | h'
    · exact hseg i j a (hx.ne hia).symm (hx.ne hja).symm t h h' ha
    · exact hx.ne hja (by rw [ha, h', one_smul]; abel)
    · refine hseg i a j (hx.ne hij).symm (hx.ne hja) (1 / t) (by positivity)
        ((div_lt_one (by linarith)).mpr h') ?_
      rw [ha, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ h.ne', one_smul]
      abel


/-- **No two points over one point** at the view `u` (no segment parallel to `u`). -/
def NoParAt (V : Finset ℝ³) (u : ℝ³) : Prop :=
  ∀ y ∈ V, ∀ y' ∈ V, y ≠ y' → cross (y' - y) u ≠ 0

theorem NoParAt.parOnly {V : Finset ℝ³} {u : ℝ³} (h : NoParAt V u) (e : ℝ³) :
    ParOnly V u e e := fun y hy y' hy' hne h0 => absurd h0 (h y hy y' hy' hne)

/-- **(G1) at the view along the edge `vw` between the triangles `vwa`, `vwb`**: the axle is the
only pair of points over one point, and every point over a support line lies with the line's
ends on one of the two triangles. -/
def G1Edge (V : Finset ℝ³) (v w a b : ℝ³) : Prop :=
  ParOnly V (w - v) v w ∧ G1Tri V (w - v) v w a v w b

/-- **(G1) at a vertex view `u` between the triangles `p₀ p₁ p₂`, `q₀ q₁ q₂`**: no two points over
one point, and every point over a support line lies with the line's ends on one of the two
triangles. -/
def G1Vtx (V : Finset ℝ³) (u p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) : Prop :=
  NoParAt V u ∧ G1Tri V u p₀ p₁ p₂ q₀ q₁ q₂


end Minimality

end
