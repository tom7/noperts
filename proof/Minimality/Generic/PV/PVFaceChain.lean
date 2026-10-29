module

public import Minimality.Generic.PV.PVFace
public import Minimality.Generic.PV.PVSeq

@[expose] public section


/-! The lower/upper chain of a face (frame-free), with every output the rim needs. -/

namespace Minimality
open scoped RealInnerProductSpace
open Finset

/-- A chain `c` of the face `F` from `A` to `B` (lower chain in the chart with depth sign `s`). -/
structure IsFaceChain (s : ℝ) (n d : ℝ³) (F : Finset ℝ³) (A B : ℝ³) {m : ℕ} (c : Fin m → ℝ³) : Prop where
  two : 2 ≤ m
  first : ∀ h : 0 < m, c ⟨0, h⟩ = A
  last : ∀ h : m - 1 < m, c ⟨m - 1, h⟩ = B
  mem : ∀ i, c i ∈ F
  mono : ∀ i j, i < j → ⟪cross n d, c i⟫ < ⟪cross n d, c j⟫
  turn : ∀ i (h : i.val + 1 < m), ∀ y ∈ F, y ≠ c i → y ≠ c ⟨i.val + 1, h⟩ →
    det3 (c ⟨i.val + 1, h⟩ - c i) (y - c i) n * s < 0
  vshape : VShapedSeq fun i => s * ⟪d, c i⟫
  ext_mem : ∀ y ∈ F, (∀ z ∈ F, s * ⟪d, y⟫ ≤ s * ⟪d, z⟫) → ∃ i, c i = y

theorem faceChain {s : ℝ} (hs : s = 1 ∨ s = -1) {n d : ℝ³} (hn : n ≠ 0) (hd : d ≠ 0)
    (hnd : ⟪n, d⟫ = 0) {F : Finset ℝ³} {h : ℝ} (hF : ∀ p ∈ F, ⟪n, p⟫ = h)
    (hconv : ConvPos (F.image (chartS s n d)))
    (hdinj : ∀ p ∈ F, ∀ q ∈ F, ⟪d, p⟫ = ⟪d, q⟫ → p = q)
    {A B : ℝ³} (hA : A ∈ F) (hB : B ∈ F) (hAB : A ≠ B)
    (hAmin : ∀ y ∈ F, y ≠ A → ⟪cross n d, A⟫ < ⟪cross n d, y⟫)
    (hBmax : ∀ y ∈ F, y ≠ B → ⟪cross n d, y⟫ < ⟪cross n d, B⟫) :
    ∃ (m : ℕ) (c : Fin m → ℝ³), IsFaceChain s n d F A B c := by
  classical
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd
  set ch := chartS s n d with hch
  have hinjF : ∀ p ∈ F, ∀ q ∈ F, ch p = ch q → p = q := fun p hp q hq he =>
    chartS_injOn hs hn hd hnd (hF p hp) (hF q hq) he
  set S := F.image ch with hS
  have hAS : ch A ∈ S := mem_image_of_mem _ hA
  have hBS : ch B ∈ S := mem_image_of_mem _ hB
  have hAB' : ch A 0 < ch B 0 := by
    simp only [hch, chartS_zero]; exact hAmin B hB (Ne.symm hAB)
  have hSmin : ∀ y ∈ S, ch A 0 ≤ y 0 := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    by_cases hpA : p = A
    · rw [hpA]
    · simp only [hch, chartS_zero]; exact (hAmin p hp hpA).le
  have hSmax : ∀ y ∈ S, y 0 ≤ ch B 0 := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    by_cases hpB : p = B
    · rw [hpB]
    · simp only [hch, chartS_zero]; exact (hBmax p hp hpB).le
  have hAlow : ∀ y ∈ S, y 0 = ch A 0 → ch A 1 ≤ y 1 := by
    intro y hy he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    by_cases hpA : p = A
    · rw [hpA]
    · exfalso
      have := hAmin p hp hpA
      simp only [hch, chartS_zero] at he
      linarith
  have hBlow : ∀ y ∈ S, y 0 = ch B 0 → ch B 1 ≤ y 1 := by
    intro y hy he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    by_cases hpB : p = B
    · rw [hpB]
    · exfalso
      have := hBmax p hp hpB
      simp only [hch, chartS_zero] at he
      linarith
  have hinj := ConvPos.injOn_below hconv hAS hBS hSmin hSmax hAB' hAlow hBlow
  obtain ⟨m, c, h2, hc0, hcn, hcS, hcL, hcmono, hcons⟩ :=
    exists_lowerChain' hinj hAS hBS hSmin hSmax hAB'
  choose p hpF hpc using fun i => mem_image.mp (hcS i)
  have hBA : 0 < ch B 0 - ch A 0 := by linarith
  have hlow : ∀ j : Fin m, ∀ y ∈ S, y ≠ c j → y 0 = c j 0 → c j 1 < y 1 := by
    intro j y hy hne hx
    by_cases hL : cross2 (ch B - ch A) (y - ch A) ≤ 0
    · exact absurd (hinj (mem_filter.mpr ⟨hy, hL⟩) (mem_filter.mpr ⟨hcS j, hcL j⟩) hx) hne
    · push Not at hL
      have h1 := hcL j
      simp only [cross2, PiLp.sub_apply] at hL h1
      by_contra hh
      push Not at hh
      rw [hx] at hL
      nlinarith [mul_nonneg hBA.le (sub_nonneg.mpr hh)]
  have hpos' : ∀ (i : Fin m) (hi : i.val + 1 < m), ∀ y ∈ S, y ≠ c i → y ≠ c ⟨i.val + 1, hi⟩ →
      0 < cross2 (c ⟨i.val + 1, hi⟩ - c i) (y - c i) := by
    intro i hi y hy h1 h2
    have hlt : c i 0 < c ⟨i.val + 1, hi⟩ 0 := hcmono i ⟨i.val + 1, hi⟩ (Fin.lt_def.mpr (by simp))
    exact cross2_pos_of_consecutive' hconv hAS hBS hSmin hSmax hAB' (hcS i) (hcS _) hlt (hcL i)
      (hcL _) (hcons i hi) (hlow i) (hlow _) hy h1 h2
  have hpx : ∀ i, ⟪cross n d, p i⟫ = c i 0 := fun i => by
    rw [← hpc i]; simp [hch, chartS_zero]
  have hpy : ∀ i, s * ⟪d, p i⟫ = c i 1 := fun i => by
    rw [← hpc i]; simp [hch, chartS_one]
  have hmono : ∀ i j : Fin m, i < j → ⟪cross n d, p i⟫ < ⟪cross n d, p j⟫ := by
    intro i j hij; rw [hpx, hpx]; exact hcmono i j hij
  have hpinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hmono i j hlt; rw [hij] at this; exact lt_irrefl _ this
    · have := hmono j i hlt; rw [hij] at this; exact lt_irrefl _ this
  refine ⟨m, p, ⟨h2, ?_, ?_, hpF, hmono, ?_, ?_, ?_⟩⟩
  · intro hm
    apply hinjF _ (hpF _) _ hA
    rw [hpc]; exact hc0
  · intro hm
    apply hinjF _ (hpF _) _ hB
    rw [hpc]; exact hcn
  · intro i hi y hy hyi hyi1
    have hpos := hpos' i hi (ch y) (mem_image_of_mem _ hy)
      (fun he => hyi (hinjF _ hy _ (hpF _) (by rw [he, hpc])))
      (fun he => hyi1 (hinjF _ hy _ (hpF _) (by rw [he, hpc])))
    rw [← hpc i, ← hpc ⟨i.val + 1, hi⟩, hch, chartS_sub, chartS_sub,
      cross2_chartS s n d _ _ hnd] at hpos
    by_contra hge
    push Not at hge
    nlinarith [mul_nonneg hdd.le hge]
  · refine vshaped_of_consec _ (by omega) ?_ ?_
    · intro i j hij
      have : ⟪d, p i⟫ = ⟪d, p j⟫ := mul_left_cancel₀ hs0 hij
      exact hpinj (hdinj _ (hpF i) _ (hpF j) this)
    · intro k hk
      have := y_lt_max_of_cross2 (a := c ⟨k, by omega⟩) (b := c ⟨k + 1, by omega⟩)
        (c := c ⟨k + 2, hk⟩) (hcmono _ _ (Fin.lt_def.mpr (by simp)))
        (hcmono _ _ (Fin.lt_def.mpr (by simp)))
        (hpos' ⟨k, by omega⟩ (by simp; omega) (c ⟨k + 2, hk⟩) (hcS _)
          (fun he => by
            have := hcmono ⟨k, by omega⟩ ⟨k + 2, hk⟩ (Fin.lt_def.mpr (by simp))
            rw [he] at this; exact lt_irrefl _ this)
          (fun he => by
            have := hcmono ⟨k + 1, by omega⟩ ⟨k + 2, hk⟩ (Fin.lt_def.mpr (by simp))
            simp only at he
            rw [he] at this; exact lt_irrefl _ this))
      simp only [hpy]
      exact this
  · intro y hy hymin
    have hyS : ch y ∈ S := mem_image_of_mem _ hy
    have hy1 : ∀ z ∈ F, ch y 1 ≤ ch z 1 := by
      intro z hz; simpa [hch, chartS_one] using hymin z hz
    have hyA := hy1 A hA
    have hyB := hy1 B hB
    have hy0A := hSmin _ hyS
    have hy0B := hSmax _ hyS
    have hyL : cross2 (ch B - ch A) (ch y - ch A) ≤ 0 := by
      simp only [cross2, PiLp.sub_apply]
      nlinarith [mul_nonneg (sub_nonneg.mpr hy0B) (sub_nonneg.mpr hyA),
        mul_nonneg (sub_nonneg.mpr hy0A) (sub_nonneg.mpr hyB)]
    by_cases hex : ∃ i, c i 0 = ch y 0
    · obtain ⟨i, hi⟩ := hex
      refine ⟨i, ?_⟩
      have := hinj (mem_filter.mpr ⟨hyS, hyL⟩) (mem_filter.mpr ⟨hcS i, hcL i⟩) hi.symm
      exact hinjF _ (hpF i) _ hy (by rw [hpc, this])
    · exfalso
      push Not at hex
      have h0 : c ⟨0, by omega⟩ 0 < ch y 0 := by
        rw [hc0]; exact lt_of_le_of_ne hy0A (fun he => hex ⟨0, by omega⟩ (by rw [hc0, he]))
      set T := (univ : Finset (Fin m)).filter (fun i => c i 0 < ch y 0) with hT
      have hTne : T.Nonempty := ⟨⟨0, by omega⟩, by simp [hT, h0]⟩
      set i := T.max' hTne with hi
      have hiT : c i 0 < ch y 0 := (mem_filter.mp (T.max'_mem hTne)).2
      have hi1 : i.val + 1 < m := by
        by_contra hge
        have hil : i = ⟨m - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp; omega)
        rw [hil, hcn] at hiT
        linarith
      have hgt : ch y 0 < c ⟨i.val + 1, hi1⟩ 0 := by
        rcases lt_or_ge (ch y 0) (c ⟨i.val + 1, hi1⟩ 0) with hlt | hge
        · exact hlt
        · exfalso
          have hlt := lt_of_le_of_ne hge (hex ⟨i.val + 1, hi1⟩)
          have hmem : (⟨i.val + 1, hi1⟩ : Fin m) ∈ T := by simp [hT, hlt]
          have hle := T.le_max' _ hmem
          rw [← hi, Fin.le_def] at hle
          simp at hle
      have := hcons i hi1 (ch y) hyS hiT hgt
      linarith

end Minimality
