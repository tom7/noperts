module

public import Minimality.EdgeLimit
public import Minimality.VtxMain

@[expose] public section

/-!
# A four-corner edge closing at the limit without Lemma E (`FEWER-FACES-PROOFS.md` §22.12)

As `isRupert_ePair_limit`, from a frequent rim certificate of the closing `K_v` alone (no edge
pair, so no Lemma E): the closing passes to the limit (Lemma 18.2), and §22's conditions at the
view (`EdgeGen`) make `x` Rupert, unless the partner closing `K_w` has a weak saddle while
`K_v` has none; that residual is left to the caller (`hres`; for type 16's `T1` at `35`, Lemma
19.3's `T2` is unimodal there, §22.12).  Lemma E is used only in class `d` and only when `K_w`
has a weak saddle (`EdgeConf.isRupert_edgeClosing`), so it is not needed here.

* `isRupert_kv_limit`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

set_option maxHeartbeats 1000000 in
/-- **A closing `K_v` at the limit, with a residual** (Lemma 18.2 with §22).  The shapes
`K_k → x` carry one rim certificate `v a c b` at the edge view `ε (w − v)` (`ε = ±1`); the faces
of `x` at the axle are `S_a ∋ v, w, a` and `S_b ∋ v, w, b` (facets, at most one middle each); at
the view `u = ε (w − v)` the conditions of §22.4 hold (`EdgeGen`).  Then `x` is Rupert, or `K_v`
has no weak saddle and `K_w` has one at `u` (`hres`). -/
theorem isRupert_kv_limit {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v w a b c : Fin n} (hvw : v ≠ w) {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, (i ∈ Sa → ⟪Na, x i⟫ = κa) ∧ (i ∉ Sa → ⟪Na, x i⟫ < κa))
    (hfb : ∀ i, (i ∈ Sb → ⟪Nb, x i⟫ = κb) ∧ (i ∉ Sb → ⟪Nb, x i⟫ < κb))
    (hSa : v ∈ Sa ∧ w ∈ Sa ∧ a ∈ Sa ∧ b ∉ Sa ∧ c ∉ Sa ∧ ∀ i ∈ Sa, ∀ j ∈ Sa,
      i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j)
    (hSb : v ∈ Sb ∧ w ∈ Sb ∧ b ∈ Sb ∧ a ∉ Sb ∧ c ∉ Sb ∧ ∀ i ∈ Sb, ∀ j ∈ Sb,
      i ≠ v → i ≠ w → i ≠ b → j ≠ v → j ≠ w → j ≠ b → i = j)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun k => K k m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ k in atTop, RimCertPts (univ.image (K k)) (ε • (K k w - K k v))
      (quad (K k v) (K k a) (K k c) (K k b)))
    (hgen : EdgeGen (univ.image x) (ε • (x w - x v)) (x v) (x w) (Sa.image x) (Sb.image x) Na Nb)
    (hres : NWS4 (quad ⟪x v, ε • (x w - x v)⟫ ⟪x a, ε • (x w - x v)⟫ ⟪x c, ε • (x w - x v)⟫
        ⟪x b, ε • (x w - x v)⟫) →
      ¬ NWS4 (quad ⟪x w, ε • (x w - x v)⟫ ⟪x a, ε • (x w - x v)⟫ ⟪x c, ε • (x w - x v)⟫
        ⟪x b, ε • (x w - x v)⟫) → IsRupert (univ.image x)) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨hvA, hwA, haA, hbA, hcA, hA1⟩ := hSa
  obtain ⟨hvB, hwB, hbB, haB, hcB, hB1⟩ := hSb
  set V := univ.image x with hVdef
  have mem : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  have memK : ∀ k i, K k i ∈ univ.image (K k) := fun k i => mem_image_of_mem _ (mem_univ i)
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  set u := ε • (x w - x v) with hudef
  have hu : u ≠ 0 := smul_ne_zero hε0 (sub_ne_zero.mpr (hx.ne hvw.symm))
  have hus : Tendsto (fun k => ε • (K k w - K k v)) atTop (𝓝 u) :=
    ((hK w).sub (hK v)).const_smul ε
  have hXq : ∀ i, Tendsto (fun k => quad (K k v) (K k a) (K k c) (K k b) i) atTop
      (𝓝 (quad (x v) (x a) (x c) (x b) i)) := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hK v, hK a, hK c, hK b]
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ k in atTop, 0 ≤ f k) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  have hleft : ∀ z ∈ V, 0 ≤ det3 (x a - x v) (z - x v) u ∧ 0 ≤ det3 (x c - x a) (z - x a) u ∧
      0 ≤ det3 (x b - x c) (z - x c) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    refine ⟨lim0 (Tendsto.det3' ((hK a).sub (hK v)) ((hK i).sub (hK v)) hus)
      (hfreq.mono fun k hk => by simpa [a0, quad_0, quad_1] using hk.left _ (memK k i) 0),
      lim0 (Tendsto.det3' ((hK c).sub (hK a)) ((hK i).sub (hK a)) hus)
      (hfreq.mono fun k hk => by simpa [a1, quad_1, quad_2] using hk.left _ (memK k i) 1),
      lim0 (Tendsto.det3' ((hK b).sub (hK c)) ((hK i).sub (hK c)) hus)
      (hfreq.mono fun k hk => by simpa [a2, quad_2, quad_3] using hk.left _ (memK k i) 2),
      lim0 (Tendsto.det3' ((hK v).sub (hK b)) ((hK i).sub (hK b)) hus)
      (hfreq.mono fun k hk => by simpa [a3, quad_3, quad_0] using hk.left _ (memK k i) 3)⟩
  have hsupp : ∀ z ∈ V, SuppIn u (quad (x v) (x a) (x c) (x b)) z := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    refine suppIn_of_tendsto hu hus hXq (hK i) (hfreq.mono fun k hk => ?_)
    have hne : ε • (K k w - K k v) ≠ 0 := by
      intro h0
      have := hk.cyc 0 2 (by decide) (by decide)
      rw [h0] at this; simp [det3_expand] at this
    exact rimCertPts_suppIn hk hne _ (memK k i)
  -- the configuration at the limit
  set Ma := (Sa \ {v, w, a}).image x with hMadef
  set Mb := (Sb \ {v, w, b}).image x with hMbdef
  have memMa : ∀ z, z ∈ Ma ↔ ∃ i ∈ Sa, i ≠ v ∧ i ≠ w ∧ i ≠ a ∧ x i = z := by
    intro z
    simp only [hMadef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have memMb : ∀ z, z ∈ Mb ↔ ∃ i ∈ Sb, i ≠ v ∧ i ≠ w ∧ i ≠ b ∧ x i = z := by
    intro z
    simp only [hMbdef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have hSAeq : Sa.image x = insert (x v) (insert (x w) (insert (x a) Ma)) := by
    ext z
    simp only [mem_image, mem_insert, memMa]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = a; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvA, rfl⟩, ⟨w, hwA, rfl⟩, ⟨a, haA, rfl⟩, ⟨i, hi, rfl⟩]
  have hSBeq : Sb.image x = insert (x v) (insert (x w) (insert (x b) Mb)) := by
    ext z
    simp only [mem_image, mem_insert, memMb]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = b; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvB, rfl⟩, ⟨w, hwB, rfl⟩, ⟨b, hbB, rfl⟩, ⟨i, hi, rfl⟩]
  have notMa : ∀ j, j ∉ Sa → x j ∉ Ma := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMa _).mp hm
    exact hj (hx he ▸ hi)
  have notMb : ∀ j, j ∉ Sb → x j ∉ Mb := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMb _).mp hm
    exact hj (hx he ▸ hi)
  have ne : ∀ {i j : Fin n}, (i ∈ Sa ∧ j ∉ Sa) ∨ (i ∈ Sb ∧ j ∉ Sb) → x j ≠ x i := by
    rintro i j (⟨hi, hj⟩ | ⟨hi, hj⟩) e <;> exact hj (hx e ▸ hi)
  have E : EdgeConf V u (x v) (x w) (x a) (x b) (x c) ε Na Nb κa κb Ma Mb := {
    hu := hu
    hh := hε0
    hw := by
      rw [hudef, smul_smul, hεε, one_smul]; abel
    hv := mem v
    hwV := mem w
    ha := mem a
    hb := mem b
    hc := mem c
    hMa := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMa z).mp hz; exact mem i
    hMb := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMb z).mp hz; exact mem i
    faceA := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfa v).1 hvA
        · rw [hx e]; exact (hfa w).1 hwA
        · rw [hx e]; exact (hfa a).1 haA
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMa _).mp e
          rw [← he]; exact (hfa j).1 hj
      · intro he
        have hi : i ∈ Sa := by
          by_contra hi; exact absurd he ((hfa i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = a; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMa _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceA_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sa
      · exact ((hfa i).1 hi).le
      · exact ((hfa i).2 hi).le
    faceB := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfb v).1 hvB
        · rw [hx e]; exact (hfb w).1 hwB
        · rw [hx e]; exact (hfb b).1 hbB
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMb _).mp e
          rw [← he]; exact (hfb j).1 hj
      · intro he
        have hi : i ∈ Sb := by
          by_contra hi; exact absurd he ((hfb i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = b; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMb _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceB_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sb
      · exact ((hfb i).1 hi).le
      · exact ((hfb i).2 hi).le
    hbA := ⟨ne (Or.inl ⟨hvA, hbA⟩), ne (Or.inl ⟨hwA, hbA⟩), ne (Or.inl ⟨haA, hbA⟩),
      notMa b hbA⟩
    hcA := ⟨ne (Or.inl ⟨hvA, hcA⟩), ne (Or.inl ⟨hwA, hcA⟩), ne (Or.inl ⟨haA, hcA⟩),
      notMa c hcA⟩
    haB := ⟨ne (Or.inr ⟨hvB, haB⟩), ne (Or.inr ⟨hwB, haB⟩), notMb a haB⟩
    hcB := ⟨ne (Or.inr ⟨hbB, hcB⟩), notMb c hcB⟩
    hMa' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMa z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    hMb' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMb z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    left := hleft
    par := hgen.par
    g1 := by rw [← hSAeq, ← hSBeq]; exact hgen.g1
    noSeg := by
      intro p hp q hq y hy hyp hyq s hs0 hs1
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp
      obtain ⟨j, -, rfl⟩ := mem_image.mp hq
      obtain ⟨m, -, rfl⟩ := mem_image.mp hy
      exact hseg i j m hyp hyq s hs0 hs1
    supp := hsupp }
  have hMa1 : ∀ m ∈ Ma, ∀ m' ∈ Ma, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMa z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMa z').mp hz'
    rw [hA1 i hi j hj h1 h2 h3 k1 k2 k3]
  have hMb1 : ∀ m ∈ Mb, ∀ m' ∈ Mb, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMb z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMb z').mp hz'
    rw [hB1 i hi j hj h1 h2 h3 k1 k2 k3]
  have imgA : ∀ i ∈ Sa, x i ∈ Sa.image x := fun i hi => mem_image_of_mem x hi
  have imgB : ∀ i ∈ Sb, x i ∈ Sb.image x := fun i hi => mem_image_of_mem x hi
  have nimA : ∀ i ∉ Sa, x i ∉ Sa.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have nimB : ∀ i ∉ Sb, x i ∉ Sb.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have fA := fun p (hp : p ∈ Sa) => footA_of_gen hgen.footA (imgA p hp) (imgA a haA) (mem c)
    (mem b) (nimA c hcA) (nimA b hbA)
  have fB := fun p (hp : p ∈ Sb) => footA_of_gen hgen.footB (imgB p hp) (imgB b hbB) (mem c)
    (mem a) (nimB c hcB) (nimB a haB)
  -- the closing at the limit
  have hq : Function.Injective (quad (x v) (x a) (x c) (x b)) := E.quad_injective
  have hrob : IsRobustUnimodal (fun i => ⟪quad (x v) (x a) (x c) (x b) i, u⟫) := by
    refine isRobustUnimodal_of_tendsto_ties (fun i => (hXq i).inner hus)
      (hfreq.mono fun k hk => ⟨hk.robust, fun i i' e => ?_⟩)
    by_cases hii : i = i'
    · rw [hii]
    · exact absurd e (hgen.dist _ (E.quad_mem i) _ (E.quad_mem i') (hq.ne hii))
  have hinj : Function.Injective (fun i => ⟪quad (x v) (x a) (x c) (x b) i, u⟫) := by
    intro i j hij
    by_contra hne
    exact hgen.dist _ (E.quad_mem i) _ (E.quad_mem j) (hq.ne hne) hij
  have hz : NWS4 (quad ⟪x v, u⟫ ⟪x a, u⟫ ⟪x c, u⟫ ⟪x b, u⟫) := by
    rw [quad_inner'] at hinj hrob
    exact nws4_of_cyclic (hrob.isCyclicUnimodal_of_order (by norm_num) (fun i j h => h) hinj)
  by_cases hKw : NWS4 (quad ⟪x w, u⟫ ⟪x a, u⟫ ⟪x c, u⟫ ⟪x b, u⟫)
  · exact E.isRupert_edgeClosing hMa1 hMb1 hrob hgen.dist hgen.one (fA v hvA) (fB v hvB)
      (fun _ hk => absurd hKw hk) (fun _ hk => absurd hKw hk)
  · exact hres hz hKw

end Minimality

end
