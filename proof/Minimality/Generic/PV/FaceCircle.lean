module

public import Minimality.Generic.PV.PVChain
public import Minimality.FaceFive
public import Minimality.Oct9Weak

@[expose] public section


/-! Task 4: the one-face rim lemma (Corollary FC), frame-free, with an orientation sign `σ`
(`σ = 1`: counterclockwise as in `isRupert_of_tilted_unimodal'`; `σ = -1`: the pair view of
Lemma PV, see PVOrient.lean). -/

namespace Minimality
open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Determinant algebra -/

/-- Gram-type identity: `|n|² det(a,b,w) = ⟪n,a⟫ det(n,b,w) + ⟪n,b⟫ det(a,n,w) + ⟪n,w⟫ det(a,b,n)`. -/
theorem det3_gram (n a b w : ℝ³) :
    ⟪n, n⟫ * det3 a b w =
      ⟪n, a⟫ * det3 n b w + ⟪n, b⟫ * det3 a n w + ⟪n, w⟫ * det3 a b n := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

theorem det3_swap_ab (a b w : ℝ³) : det3 b a w = -det3 a b w := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

theorem inner_self_pos_of_ne {n : ℝ³} (hn : n ≠ 0) : 0 < ⟪n, n⟫ := real_inner_self_pos.mpr hn

/-- **The in-plane / off-plane test of one chain edge** (frame-free, sign-parametrized).
`c → c'` is an edge of a face in the plane `⟪n,·⟫ = h`, the view `u0` is parallel to the plane,
`y` lies on the closed negative side.  Off the plane the test is decided at the view `u0` by the
direction of the edge (`hdir`); in the plane it is decided by the tilt (`hcr`: `y` lies to the
`σ⟪n,v⟫`-positive side of the edge). -/
theorem tiltSignS_edge {σ : ℝ} {n u0 v c c' y : ℝ³} {h : ℝ} (hn : n ≠ 0) (hu : ⟪n, u0⟫ = 0)
    (hc : ⟪n, c⟫ = h) (hc' : ⟪n, c'⟫ = h) (hy : ⟪n, y⟫ ≤ h)
    (hdir : 0 < σ * det3 n (c' - c) u0)
    (hcr : ⟪n, y⟫ = h → 0 < σ * ⟪n, v⟫ * det3 (c' - c) (y - c) n) :
    TiltSignS σ (c' - c) (y - c) u0 v := by
  have hN := inner_self_pos_of_ne hn
  have ha : ⟪n, c' - c⟫ = 0 := by rw [inner_sub_right, hc, hc']; ring
  have hb : ⟪n, y - c⟫ = ⟪n, y⟫ - h := by rw [inner_sub_right, hc]
  have g0 := det3_gram n (c' - c) (y - c) u0
  rw [ha, hb, hu] at g0
  rcases hy.lt_or_eq with hlt | heq
  · left
    have h1 : det3 (c' - c) n u0 = -det3 n (c' - c) u0 := det3_swap_ab _ _ _
    have h2 : ⟪n, n⟫ * (σ * det3 (c' - c) (y - c) u0) = (h - ⟪n, y⟫) * (σ * det3 n (c' - c) u0) := by
      have : ⟪n, n⟫ * det3 (c' - c) (y - c) u0 = (⟪n, y⟫ - h) * det3 (c' - c) n u0 := by
        linarith
      rw [h1] at this
      linear_combination σ * this
    have h3 : 0 < (h - ⟪n, y⟫) * (σ * det3 n (c' - c) u0) := mul_pos (by linarith) hdir
    rw [← h2] at h3
    exact (mul_pos_iff_of_pos_left hN).mp h3
  · right
    have hb0 : ⟪n, y - c⟫ = 0 := by rw [hb, heq]; ring
    have g1 := det3_gram n (c' - c) (y - c) u0
    rw [ha, hb0, hu] at g1
    have h0 : det3 (c' - c) (y - c) u0 = 0 := by
      have : ⟪n, n⟫ * det3 (c' - c) (y - c) u0 = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hN.ne'
      · exact h'
    refine ⟨h0, ?_⟩
    have g2 := det3_gram n (c' - c) (y - c) v
    rw [ha, hb0] at g2
    have h4 := hcr heq
    have : ⟪n, n⟫ * (σ * det3 (c' - c) (y - c) v) = σ * ⟪n, v⟫ * det3 (c' - c) (y - c) n := by
      linear_combination σ * g2
    rw [← this] at h4
    exact (mul_pos_iff_of_pos_left hN).mp h4

/-- **Generic rim certificate.**  A cycle `x` of vertices of `V` whose depths at `u₀` are distinct and
cyclically unimodal, and whose edges pass the `TiltSignS σ` tests against every other vertex of `V`,
shows that `V` is Rupert (Lemma 8.0 + Cor. 8.0′ at the unmodified view `u₀`; ties absent). -/
theorem isRupert_of_rim_key (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (key : ∀ i, ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hCU : IsCyclicUnimodal fun i => ⟪x i, u₀⟫) : IsRupert V := by
  have hxinj : Function.Injective x := fun a b h => hinj (by simp only [h])
  refine isRupert_of_tilted_unimodal_σ V u₀ v hu₀ hk x hxV σ hσ ?_ ?_ IsCyclicUnimodal
    isOpen_isCyclicUnimodal (fun z c hc hz => isCyclicUnimodal_smul hc hz) ?_ (fun z _ hz => hz)
  · intro i j hj1 hj2
    exact key i (x j) (hxV j) (fun h => hj1 (hxinj h)) (fun h => hj2 (hxinj h))
  · intro y hy hyx i
    exact key i y hy (hyx i) (hyx (i + 1))
  · have hc : Continuous fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫ :=
      continuous_pi fun i => by fun_prop
    have h0 : (fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫) 0 ∈ {z | IsCyclicUnimodal z} := by
      simpa using hCU
    exact Eventually.filter_mono nhdsWithin_le_nhds
      (hc.continuousAt.preimage_mem_nhds (isOpen_isCyclicUnimodal.mem_nhds h0))

theorem zmod_val_add_one {N : ℕ} (hN : 1 ≤ N) (i : ZMod (N + 1)) (hi : i.val < N) :
    (i + 1).val = i.val + 1 := by
  haveI : Fact (1 < N + 1) := ⟨by omega⟩
  rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]

/-- **The one-face rim lemma (Corollary FC, exact form).**  `F` is a face in the plane
`⟪n,·⟫ = h` with `V` on its closed negative side; the view `u₀` is parallel to the plane (the face is
edge-on); `v` is the tilt (`⟪n,v⟫ ≠ 0`; its sign selects lower/upper chain).  The rim is a cycle
`x₀ … x_N`: the first `m` entries are the chain `A → B` of `F` (`hplane`), the remaining entries
`R = x_m … x_N` are arbitrary vertices of `V`; the rim is traversed with the orientation `σ`.

* chain edges: `hdir` (the chain advances in the positive direction along the screen line,
  `σ det(n, edge, u₀) > 0`) and `hchain` (the other vertices of `F` lie on the `σ⟪n,v⟫`-positive side
  of every chain edge, i.e. the chain is the lower (`σ⟪n,v⟫>0`, `σ>0`) resp. upper chain: this is
  `cross2_pos_of_consecutive` from `FaceChain.lean`);
* `R`-edges and the two bridges `x_{m-1} → x_m`, `x_N → x_0`: arbitrary `TiltSignS` rows (`hR`);
* depths: `hinj` and cyclic unimodality `hCU` of the depth cycle at `u₀`.  (By Lemma SK this is the
  unimodality of the skeleton `(A, lo/hi, B, R)`, see `isRupert_faceCircle_skeleton`.)

Specializing `R = {p}` recovers `isRupert_edgeOn_dir`; Lemma PV uses this with `R` = bridge,
second chain, bridge. -/
theorem isRupert_faceCircle (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hplane : ∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h)
    (hdir : ∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀)
    (hchain : ∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n)
    (hR : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (hCU : IsCyclicUnimodal fun i => ⟪x i, u₀⟫) : IsRupert V := by
  refine isRupert_of_rim_key V u₀ v hu₀ (by omega) x hxV σ hσ hinj ?_ hCU
  intro i y hy hyi hyi1
  by_cases hi : i.val + 1 < m
  · have hval : (i + 1).val = i.val + 1 := zmod_val_add_one (by omega) i (by omega)
    exact tiltSignS_edge hn hu (hplane i (by omega)) (hplane (i + 1) (by omega)) (hV y hy)
      (hdir i hi) (fun heq => hchain i hi y hy heq hyi hyi1)
  · exact hR i (by omega) y hy hyi hyi1

/-- **Corollary FC (skeleton form), lower (V-shaped) chain.**  Same as `isRupert_faceCircle`, but the depth
hypothesis is the unimodality of the *skeleton* `(A, lo, B) ++ R`: the depth list of the rim is
`A ++ B ++ R` where `A ++ B` (length `m`) are the chain depths (V-shaped: `A` strictly
decreasing, `B` strictly increasing; `e` the lowest chain depth, omitted from the skeleton when it is an end)
and `R` the depths of the rest; Lemma SK (`CU_chain_V`) transfers unimodality. -/
theorem isRupert_faceCircle_skelV (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hplane : ∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h)
    (hdir : ∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀)
    (hchain : ∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n)
    (hR : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (A B R : List ℝ) (a e c : ℝ)
    (hdepth : List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = A ++ B ++ R)
    (hAB : A.length + B.length = m) (hA : A.Pairwise (· > ·)) (hB : B.Pairwise (· < ·))
    (ha : (A ++ B).head? = some a) (hc : (A ++ B).getLast? = some c) (he : e ∈ A ++ B)
    (hext : ∀ x ∈ A ++ B, e ≤ x) (hsk : CU (skel1 a e c ++ R)) : IsRupert V := by
  have hnd : (A ++ B ++ R).Nodup := by
    rw [← hdepth, List.nodup_ofFn]
    intro i j hij
    have := hinj hij
    apply Fin.ext
    have h1 := congrArg ZMod.val this
    rwa [ZMod.val_cast_of_lt (by omega : (i : ℕ) < N + 1),
      ZMod.val_cast_of_lt (by omega : (j : ℕ) < N + 1)] at h1
  have hCU : IsCyclicUnimodal fun i => ⟪x i, u₀⟫ := by
    rw [← CU_ofFn, hdepth]
    exact (CU_chain_V m A B R a e c hAB hA hB hnd hm ha hc he hext).mpr hsk
  exact isRupert_faceCircle V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir hchain hR hinj hCU

/-- **Corollary FC (skeleton form), upper (Λ-shaped) chain.**  Same as `isRupert_faceCircle`, but the depth
hypothesis is the unimodality of the *skeleton* `(A, hi, B) ++ R`: the depth list of the rim is
`A ++ B ++ R` where `A ++ B` (length `m`) are the chain depths (Λ-shaped: `A` strictly
increasing, `B` strictly decreasing; `e` the highest chain depth, omitted from the skeleton when it is an end)
and `R` the depths of the rest; Lemma SK (`CU_chain_L`) transfers unimodality. -/
theorem isRupert_faceCircle_skelL (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hplane : ∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h)
    (hdir : ∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀)
    (hchain : ∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n)
    (hR : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (A B R : List ℝ) (a e c : ℝ)
    (hdepth : List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = A ++ B ++ R)
    (hAB : A.length + B.length = m) (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· > ·))
    (ha : (A ++ B).head? = some a) (hc : (A ++ B).getLast? = some c) (he : e ∈ A ++ B)
    (hext : ∀ x ∈ A ++ B, x ≤ e) (hsk : CU (skel1 a e c ++ R)) : IsRupert V := by
  have hnd : (A ++ B ++ R).Nodup := by
    rw [← hdepth, List.nodup_ofFn]
    intro i j hij
    have := hinj hij
    apply Fin.ext
    have h1 := congrArg ZMod.val this
    rwa [ZMod.val_cast_of_lt (by omega : (i : ℕ) < N + 1),
      ZMod.val_cast_of_lt (by omega : (j : ℕ) < N + 1)] at h1
  have hCU : IsCyclicUnimodal fun i => ⟪x i, u₀⟫ := by
    rw [← CU_ofFn, hdepth]
    exact (CU_chain_L m A B R a e c hAB hA hB hnd hm ha hc he hext).mpr hsk
  exact isRupert_faceCircle V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir hchain hR hinj hCU

end Minimality
