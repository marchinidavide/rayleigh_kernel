import RayleighKernel.Discrete.Sampling
import RayleighKernel.Probability.CovarianceForm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory
open scoped Interval

namespace RayleighKernel.Probability

def kernelZeroExtension (w : Discrete.Kernel) (j : ℤ) : ℝ :=
  if 0 ≤ j then w j.toNat else 0

def cutoffKernel (N : ℕ) (w : Discrete.Kernel) : Discrete.Kernel :=
  fun j => if j < N then w j else 0

def cutoffZeroExtension (N : ℕ) (w : Discrete.Kernel) (j : ℤ) : ℝ :=
  kernelZeroExtension (cutoffKernel N w) j

def lagInnerProductCutoff (N : ℕ) (w : Discrete.Kernel) (lag : ℤ) : ℝ :=
  ∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = lag), w p.1 * w p.2

def toeplitzCovariance (γ : ℤ → ℝ) : ℕ → ℕ → ℝ :=
  fun j k => γ ((j : ℤ) - (k : ℤ))

def finiteLagSet (N : ℕ) : Finset ℤ :=
  ((Finset.range N).product (Finset.range N)).image
    (fun p => (p.1 : ℤ) - (p.2 : ℤ))

theorem cutoffKernel_eq (N : ℕ) (w : Discrete.Kernel) (j : ℕ) :
    cutoffKernel N w j = if j < N then w j else 0 := rfl

def finiteLagCovarianceGrouped (γ : ℤ → ℝ) (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  ∑ lag ∈ finiteLagSet N, γ lag * lagInnerProductCutoff N w lag

theorem finiteLagCovarianceGrouped_eq_covarianceForm
    (γ : ℤ → ℝ) (N : ℕ) (w : Discrete.Kernel) :
    finiteLagCovarianceGrouped γ N w =
      finiteCovarianceForm (toeplitzCovariance γ) N w := by
  classical
  classical
  unfold finiteLagCovarianceGrouped finiteLagSet lagInnerProductCutoff
  let s := (Finset.range N).product (Finset.range N)
  have h := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := ((Finset.range N).product (Finset.range N)).image
      (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)))
    (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    (fun p : ℕ × ℕ => γ ((p.1 : ℤ) - (p.2 : ℤ)) * w p.1 * w p.2)
  dsimp [s] at h
  unfold finiteCovarianceForm toeplitzCovariance
  calc
    _ = ∑ lag ∈ ((Finset.range N).product (Finset.range N)).image
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)),
        ∑ p ∈ (Finset.range N).product (Finset.range N) with
          (p.1 : ℤ) - (p.2 : ℤ) = lag,
          γ ((p.1 : ℤ) - (p.2 : ℤ)) * w p.1 * w p.2 := by
            apply Finset.sum_congr rfl
            intro lag hlag
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            simp only [Finset.mem_filter] at hp
            rw [hp.2]
            ring
    _ = _ := by
      have h' :
          (∑ lag ∈ finiteLagSet N, ∑ p ∈ (Finset.range N).product (Finset.range N)
            with (p.1 : ℤ) - (p.2 : ℤ) = lag,
            γ ((p.1 : ℤ) - (p.2 : ℤ)) * w p.1 * w p.2) =
            ∑ p ∈ (Finset.range N).product (Finset.range N),
              γ ((p.1 : ℤ) - (p.2 : ℤ)) * w p.1 * w p.2 := by
        simp [finiteLagSet] at h ⊢
        exact h
      exact h'.trans (by
        simp [Finset.sum_product, mul_left_comm, mul_comm])

theorem finiteLagCovarianceGrouped_summable (γ : ℤ → ℝ) (N : ℕ)
    (w : Discrete.Kernel) :
    Summable (fun lag : ℤ => if lag ∈ finiteLagSet N
      then γ lag * lagInnerProductCutoff N w lag else 0) := by
  apply summable_of_ne_finset_zero (s := finiteLagSet N)
  intro lag hlag
  simp [hlag]

theorem lagInnerProductCutoff_eq_zero_of_not_mem_finiteLagSet
    (N : ℕ) (w : Discrete.Kernel) {lag : ℤ} (hlag : lag ∉ finiteLagSet N) :
    lagInnerProductCutoff N w lag = 0 := by
  classical
  unfold lagInnerProductCutoff
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact False.elim (hlag (Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩))

def sampledProfileKernel (L : ℕ) (f : ℝ → ℝ) : Discrete.Kernel :=
  Discrete.sampledKernel (1 / (L : ℝ)) f

def sampledProfileValue (L N : ℕ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j.toNat < N then f ((j : ℝ) / (L : ℝ)) else 0

def sampledLagRiemannSum (L N : ℕ) (f : ℝ → ℝ) (lag : ℤ) : ℝ :=
  ∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = lag),
    sampledProfileValue L N f (p.1 : ℤ) * sampledProfileValue L N f (p.2 : ℤ)

def sampledDifferenceValue (L N : ℕ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  sampledProfileValue L N f j - sampledProfileValue L N f (j - 1)

def sampledDifferenceLagRiemannSum (L N : ℕ) (f : ℝ → ℝ) (lag : ℤ) : ℝ :=
  ∑ p ∈ ((Finset.range N).product (Finset.range N)).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = lag),
    sampledDifferenceValue L N f (p.1 : ℤ) *
      sampledDifferenceValue L N f (p.2 : ℤ)

theorem sampledProfileValue_eq (L N : ℕ) (f : ℝ → ℝ) (j : ℤ) :
    sampledProfileValue L N f j =
      if 0 ≤ j ∧ j.toNat < N then f ((j : ℝ) / (L : ℝ)) else 0 := rfl

theorem sampledDifferenceValue_eq (L N : ℕ) (f : ℝ → ℝ) (j : ℤ) :
    sampledDifferenceValue L N f j =
      sampledProfileValue L N f j - sampledProfileValue L N f (j - 1) := rfl

theorem sampledProfileValue_sample (L N : ℕ) (f : ℝ → ℝ) (j : ℤ) (_hL : 0 < L) :
    sampledProfileValue L N f j =
      if 0 ≤ j ∧ j.toNat < N then
        f ((j : ℝ) / (L : ℝ)) else 0 := by
  exact sampledProfileValue_eq L N f j

theorem sampledDifferenceValue_sample (L N : ℕ) (f : ℝ → ℝ) (j : ℤ)
    (_hL : 0 < L) :
    sampledDifferenceValue L N f j =
      (if 0 ≤ j ∧ j.toNat < N then f ((j : ℝ) / (L : ℝ)) else 0) -
      (if 0 ≤ j - 1 ∧ (j - 1).toNat < N then
        f (((j - 1 : ℤ) : ℝ) / (L : ℝ)) else 0) := by
  rw [sampledDifferenceValue_eq]
  rfl

theorem sampledProfileKernel_value_bridge (L N : ℕ) (f : ℝ → ℝ) {j : ℕ}
    (hj : j < N) (hL : 0 < L) :
    (L : ℝ) * sampledProfileKernel L f j =
      sampledProfileValue L N f (j : ℤ) := by
  rw [sampledProfileValue_eq]
  simp [hj, sampledProfileKernel]
  field_simp

theorem sampledDifferenceKernel_value_bridge (L N : ℕ) (f : ℝ → ℝ) {j : ℕ}
    (hj : j < N) (hL : 0 < L) :
    (L : ℝ) * Discrete.difference (sampledProfileKernel L f) j =
      sampledDifferenceValue L N f (j : ℤ) := by
  rw [sampledDifferenceValue_eq, sampledProfileValue_eq]
  cases j with
  | zero =>
      rw [sampledProfileValue_eq]
      simp [hj, sampledProfileKernel, Discrete.difference]
      field_simp
  | succ j =>
      change (L : ℝ) * Discrete.difference (sampledProfileKernel L f) (j + 1) =
        sampledProfileValue L N f (j + 1 : ℤ) -
          sampledProfileValue L N f ((j + 1 : ℤ) - 1)
      rw [sampledProfileValue_eq, sampledProfileValue_eq]
      simp [hj, show 0 ≤ (j + 1 : ℤ) by omega, sampledProfileKernel,
        Discrete.difference]
      have hjlt : j < N := by omega
      simp [hjlt]
      field_simp

theorem sampledLagInnerProductCutoff_scaled (L N : ℕ) (f : ℝ → ℝ) (lag : ℤ)
    (hL : 0 < L) :
    (L : ℝ) * lagInnerProductCutoff N (sampledProfileKernel L f) lag =
      (1 / (L : ℝ)) * sampledLagRiemannSum L N f lag := by
  unfold lagInnerProductCutoff sampledLagRiemannSum
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter] at hj
  have hp := Finset.mem_product.mp hj.1
  have hj₁ : j.1 < N := Finset.mem_range.mp hp.1
  have hj₂ : j.2 < N := Finset.mem_range.mp hp.2
  rw [show (L : ℝ) ^ 2 * (sampledProfileKernel L f j.1 *
      sampledProfileKernel L f j.2) =
      ((L : ℝ) * sampledProfileKernel L f j.1) *
        ((L : ℝ) * sampledProfileKernel L f j.2) by ring]
  rw [sampledProfileKernel_value_bridge L N f hj₁ hL,
    sampledProfileKernel_value_bridge L N f hj₂ hL]

theorem sampledDifferenceLagInnerProductCutoff_scaled (L N : ℕ) (f : ℝ → ℝ)
    (lag : ℤ) (hL : 0 < L) :
    (L : ℝ) ^ 3 *
        lagInnerProductCutoff N (Discrete.difference (sampledProfileKernel L f)) lag =
      (L : ℝ) * sampledDifferenceLagRiemannSum L N f lag := by
  unfold lagInnerProductCutoff sampledDifferenceLagRiemannSum
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter] at hj
  have hp := Finset.mem_product.mp hj.1
  have hj₁ : j.1 < N := Finset.mem_range.mp hp.1
  have hj₂ : j.2 < N := Finset.mem_range.mp hp.2
  rw [show (L : ℝ) ^ 2 * (Discrete.difference (sampledProfileKernel L f) j.1 *
      Discrete.difference (sampledProfileKernel L f) j.2) =
      ((L : ℝ) * Discrete.difference (sampledProfileKernel L f) j.1) *
        ((L : ℝ) * Discrete.difference (sampledProfileKernel L f) j.2) by ring]
  rw [sampledDifferenceKernel_value_bridge L N f hj₁ hL,
    sampledDifferenceKernel_value_bridge L N f hj₂ hL]

def sampledProfileHorizon (K L : ℕ) : ℕ := K * L + 1

theorem lagInnerProductCutoff_natCast_eq_shifted
    (N : ℕ) (w : Discrete.Kernel) (d : ℕ) (_hd : d ≤ N) :
    lagInnerProductCutoff N w (d : ℤ) =
      ∑ k ∈ Finset.range (N - d), w (k + d) * w k := by
  classical
  unfold lagInnerProductCutoff
  apply Finset.sum_bij' (fun p _ => p.2) (fun k _ => (k + d, k))
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.1 = p.2 + d := by omega
    have hn := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hk := Finset.mem_range.mp hn
    apply Finset.mem_range.mpr
    rw [Nat.lt_sub_iff_add_lt]
    omega
  · intro k hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_range.mpr (by
        have hk' := Finset.mem_range.mp hk
        rw [Nat.lt_sub_iff_add_lt] at hk'
        omega), Finset.mem_range.mpr (lt_of_lt_of_le
        (Finset.mem_range.mp hk) (Nat.sub_le ..))⟩
    · norm_num [Nat.cast_add]
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.1 = p.2 + d := by omega
    apply Prod.ext <;> omega
  · intro k hk
    rfl
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.1 = p.2 + d := by omega
    rw [heq]

theorem lagInnerProductCutoff_neg_natCast_eq_shifted
    (N : ℕ) (w : Discrete.Kernel) (d : ℕ) (_hd : d ≤ N) :
    lagInnerProductCutoff N w (-(d : ℤ)) =
      ∑ k ∈ Finset.range (N - d), w k * w (k + d) := by
  classical
  unfold lagInnerProductCutoff
  apply Finset.sum_bij' (fun p _ => p.1) (fun k _ => (k, k + d))
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.2 = p.1 + d := by omega
    have hn := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    have hk := Finset.mem_range.mp hn
    apply Finset.mem_range.mpr
    rw [Nat.lt_sub_iff_add_lt]
    omega
  · intro k hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le
        (Finset.mem_range.mp hk) (Nat.sub_le ..)), Finset.mem_range.mpr (by
        have hk' := Finset.mem_range.mp hk
        rw [Nat.lt_sub_iff_add_lt] at hk'
        omega)⟩
    · norm_num [Nat.cast_add]
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.2 = p.1 + d := by omega
    apply Prod.ext <;> omega
  · intro k hk
    rfl
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have heq : p.2 = p.1 + d := by omega
    rw [heq]

theorem lagInnerProductCutoff_eq_shifted_natAbs
    (N : ℕ) (w : Discrete.Kernel) (lag : ℤ) (habs : lag.natAbs ≤ N) :
    lagInnerProductCutoff N w lag =
      if 0 ≤ lag then ∑ k ∈ Finset.range (N - lag.natAbs),
        w (k + lag.natAbs) * w k
      else ∑ k ∈ Finset.range (N - lag.natAbs),
        w k * w (k + lag.natAbs) := by
  by_cases h : 0 ≤ lag
  · rw [ite_eq_left h]
    have hlag : lag = (lag.natAbs : ℤ) := (Int.natAbs_of_nonneg h).symm
    rw [hlag]
    have hnat : ((lag.natAbs : ℤ).natAbs) = lag.natAbs := Int.natAbs_natCast _
    rw [hnat]
    exact lagInnerProductCutoff_natCast_eq_shifted N w lag.natAbs habs
  · rw [ite_eq_right h]
    have hn : lag = -(lag.natAbs : ℤ) := by
      have := Int.natAbs_of_nonneg (show 0 ≤ -lag by omega)
      omega
    rw [hn]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
      lagInnerProductCutoff_neg_natCast_eq_shifted N w lag.natAbs habs




private theorem direct_c1_cell_error
    (g : ℝ → ℝ) (a h M : ℝ) (hh : 0 ≤ h)
    (hg : ContDiff ℝ 1 g) (hM : ∀ x ∈ Set.Icc a (a + h), ‖deriv g x‖ ≤ M) :
    ‖h * g a - ∫ x in a..a + h, g x‖ ≤ M * h ^ 2 := by
  have hdiff : ∀ x ∈ Set.Icc a (a + h),
      ‖g x - g a‖ ≤ M * (x - a) := by
    intro x hx
    apply norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
      (f' := deriv g) (C := M) ?_ ?_ x hx
    · intro y hy
      exact (((hg.differentiable (by norm_num)) y).hasDerivAt).hasDerivWithinAt
    · intro y hy
      exact hM y ⟨hy.1, le_of_lt hy.2⟩
  have hnorm : ∀ x ∈ Set.Ioc a (a + h), ‖g a - g x‖ ≤ M * h := by
    intro x hx
    have hx' : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hx.1, hx.2⟩
    rw [norm_sub_rev]
    calc
      ‖g x - g a‖ ≤ M * (x - a) := hdiff x hx'
      _ ≤ M * h := by
        have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
          (hM a ⟨le_rfl, le_add_of_nonneg_right hh⟩)
        gcongr
        linarith [hx'.2]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => g a - g x) (a := a) (b := a + h) (C := M * h) (by
      simpa [Set.uIoc_of_le (le_add_of_nonneg_right hh)] using hnorm)
  have hconst : ∫ x in a..a + h, (g a : ℝ) = h * g a := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const)
      (hg.continuous.intervalIntegrable a (a + h)), hconst] at hi
  have habs : |a + h - a| = h := by
    rw [add_sub_cancel_left, abs_of_nonneg hh]
  rw [habs] at hi
  simpa [norm_sub_rev, sub_eq_add_neg, mul_assoc, pow_two] using hi

private theorem direct_c1_grid_error
    (g : ℝ → ℝ) (K L : ℕ) (M : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hg : ContDiff ℝ 1 g)
    (hM : ∀ x ∈ Set.Icc (0 : ℝ) K, ‖deriv g x‖ ≤ M) :
    ‖(1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) / (L : ℝ)) - ∫ x in (0 : ℝ)..(K : ℝ), g x‖ ≤
      (K : ℝ) * M / L := by
  let h : ℝ := 1 / (L : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hKL : (K * L : ℝ) * h = (K : ℝ) := by
    dsimp [h]
    field_simp
  have hsum : ∑ j ∈ Finset.range (K * L),
      ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x =
      ∫ x in (0 : ℝ)..(K : ℝ), g x := by
    let a : ℕ → ℝ := fun j => (j : ℝ) * h
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (f := g) (a := a) (n := K * L) (μ := volume) (fun _ _ => by
        exact hg.continuous.intervalIntegrable _ _)
    simpa [a, Nat.cast_add, add_mul, hKL] using hs
  have hcell : ∀ j ∈ Finset.range (K * L),
      ‖h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x‖ ≤ M * h ^ 2 := by
    intro j hj
    have hj' : j + 1 ≤ K * L := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hbound : ∀ x ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
        ‖deriv g x‖ ≤ M := by
      intro x hx
      apply hM x
      constructor
      · exact le_trans (by positivity) hx.1
      · calc
          x ≤ ((j : ℝ) + 1) * h := hx.2
          _ = ((j : ℝ) * h) + h := by ring
          _ ≤ (K : ℝ) := by
            rw [← hKL]
            calc
              ((j : ℝ) * h) + h = ((j + 1 : ℕ) : ℝ) * h := by norm_num; ring
              _ ≤ ((K * L : ℕ) : ℝ) * h :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hj') hh.le
              _ = (K : ℝ) * (L : ℝ) * h := by norm_num [Nat.cast_mul]
    convert direct_c1_cell_error g ((j : ℝ) * h) h M hh.le hg (by
      intro x hx
      apply hbound x
      simpa only [add_assoc, add_mul, Nat.cast_one, one_mul] using hx) using 1
    · congr 3
      ring
  have herr : ‖∑ j ∈ Finset.range (K * L),
      (h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x)‖ ≤
      (K * L : ℝ) * (M * h ^ 2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K * L),
          ‖h * g ((j : ℝ) * h) -
            ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (K * L), M * h ^ 2 :=
        Finset.sum_le_sum (fun j hj => hcell j hj)
      _ = (K * L : ℝ) * (M * h ^ 2) := by simp
  have hrewrite : (∑ j ∈ Finset.range (K * L),
      (h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x)) =
      h * ∑ j ∈ Finset.range (K * L), g ((j : ℝ) * h) -
        ∫ x in (0 : ℝ)..(K : ℝ), g x := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, hsum]
  rw [hrewrite] at herr
  have hleft : (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
      g ((j : ℝ) / (L : ℝ)) = h * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) * h) := by
    apply congrArg (fun s => (1 / (L : ℝ)) * s)
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [h]
    field_simp
  have hright : (K : ℝ) * M / L = (K * L : ℝ) * (M * h ^ 2) := by
    dsimp [h]
    field_simp
  rw [hleft, hright]
  exact herr

private theorem direct_c1_grid_tendsto
    (g : ℝ → ℝ) (K : ℕ) (hK : 0 < K)
    (hg : ContDiff ℝ 1 g)
    (hM : ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) K, ‖deriv g x‖ ≤ M) :
    Tendsto (fun L : ℕ =>
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) / (L : ℝ))) atTop
      (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), g x)) := by
  obtain ⟨M, hM⟩ := hM
  have herr : ∀ᶠ L : ℕ in atTop, ‖
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) / (L : ℝ)) - ∫ x in (0 : ℝ)..(K : ℝ), g x‖ ≤
      (K : ℝ) * M / L := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact direct_c1_grid_error g K L M hK hL hg hM
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : Tendsto (fun L : ℕ => (K : ℝ) * M / L) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)))
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) herr hbound

private theorem abs_shifted_product_sum_sub_square_sum_le
    (F : ℕ → ℝ) (m d : ℕ) (A B : ℝ)
    (hd : d ≤ m) (hA : 0 ≤ A) (_hB0 : 0 ≤ B)
    (hF : ∀ k < m, |F k| ≤ B)
    (hshift : ∀ k < m - d, |F (k+d) - F k| ≤ A) :
  |(∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
      ∑ k ∈ Finset.range m, (F k)^2| ≤
    (m-d : ℝ)*A*B + (d:ℝ)*B^2 := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => F k ^ 2) (Nat.sub_le m d)
  have hrew :
      (∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
          ∑ k ∈ Finset.range m, (F k)^2 =
        (∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k) -
          ∑ k ∈ Finset.Ico (m-d) m, (F k)^2 := by
    rw [← hsplit]
    have hterm :
        (∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
            ∑ k ∈ Finset.range (m-d), (F k)^2 =
          ∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [← hterm]
    ring
  rw [hrew]
  calc
    |(∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k) -
          ∑ k ∈ Finset.Ico (m-d) m, (F k)^2|
        ≤ |∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k| +
          |∑ k ∈ Finset.Ico (m-d) m, (F k)^2| := abs_sub _ _
    _ ≤ (∑ k ∈ Finset.range (m-d), |(F (k+d) - F k) * F k|) +
          ∑ k ∈ Finset.Ico (m-d) m, |(F k)^2| := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ k ∈ Finset.range (m-d), A * B) +
          ∑ k ∈ Finset.Ico (m-d) m, B^2 := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        have hk' : k + d < m := by
          have hk'' := Finset.mem_range.mp hk
          rw [Nat.lt_sub_iff_add_lt] at hk''
          exact hk''
        exact mul_le_mul (hshift k (Finset.mem_range.mp hk))
          (hF k (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.sub_le ..)))
          (abs_nonneg _) hA
      · apply Finset.sum_le_sum
        intro k hk
        have hk' : k < m := (Finset.mem_Ico.mp hk).2
        have habs : |F k| ≤ B := hF k hk'
        rw [← sq_abs]
        simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg (F k)) habs)
    _ = (m-d : ℝ)*A*B + (d:ℝ)*B^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      rw [Nat.card_Ico]
      have htail : m - (m - d) = d := by omega
      rw [htail]
      norm_cast
      ring

private theorem sampled_shifted_sum_endpoint_eq
    (f : ℝ → ℝ) (K L d : ℕ) (hL : 0 < L) (hd : d ≤ K * L) (hd0 : 0 < d)
    (hK : f (K : ℝ) = 0) :
    (∑ k ∈ Finset.range (K * L + 1 - d),
        f (((k + d : ℕ) : ℝ) / (L : ℝ)) * f ((k : ℝ) / (L : ℝ))) =
      ∑ k ∈ Finset.range (K * L - d),
        f (((k + d : ℕ) : ℝ) / (L : ℝ)) * f ((k : ℝ) / (L : ℝ)) := by
  have hsub : K * L + 1 - d = (K * L - d) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have _ := hd0
  have hlast : K * L - d + d = K * L := by omega
  rw [hlast]
  have harg : ((K * L : ℕ) : ℝ) / (L : ℝ) = (K : ℝ) := by
    norm_num [Nat.cast_mul]
    field_simp
  rw [harg, hK, zero_mul]
  simp

private theorem sampled_shifted_sum_endpoint_eq_zero
    (f : ℝ → ℝ) (K L : ℕ) (hL : 0 < L) (hK : f (K : ℝ) = 0) :
    (∑ k ∈ Finset.range (K * L + 1),
        f (((k : ℕ) : ℝ) / (L : ℝ)) * f ((k : ℝ) / (L : ℝ))) =
      ∑ k ∈ Finset.range (K * L),
        (f ((k : ℝ) / (L : ℝ)))^2 := by
  rw [show K * L + 1 = (K * L) + 1 by rfl, Finset.sum_range_succ]
  have harg : ((K * L : ℕ) : ℝ) / (L : ℝ) = (K : ℝ) := by
    norm_num [Nat.cast_mul]
    field_simp
  rw [harg, hK, zero_mul]
  simp [pow_two]

private theorem sampled_scaled_lag_eq_extended
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ)
    (hL : 0 < L) (hd : lag.natAbs ≤ K * L) (_hfK : f (K : ℝ) = 0) :
    (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
      (sampledProfileKernel L f) lag =
      (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L + 1 - lag.natAbs),
        f (((k + lag.natAbs : ℕ) : ℝ) / (L : ℝ)) * f ((k : ℝ) / (L : ℝ)) := by
  rw [show sampledProfileHorizon K L = K * L + 1 by rfl]
  have hdN : lag.natAbs ≤ K * L + 1 := by omega
  rw [lagInnerProductCutoff_eq_shifted_natAbs _ _ _ hdN]
  by_cases hpos : 0 ≤ lag
  · rw [ite_eq_left hpos, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k + lag.natAbs < K * L + 1 := by
      have hk'' := Finset.mem_range.mp hk
      rw [Nat.lt_sub_iff_add_lt] at hk''
      omega
    have hk0 : k < K * L + 1 := by omega
    rw [show (L : ℝ) * (sampledProfileKernel L f (k + lag.natAbs) *
      sampledProfileKernel L f k) = (1 / (L : ℝ)) *
      ((L : ℝ) * sampledProfileKernel L f (k + lag.natAbs)) *
      ((L : ℝ) * sampledProfileKernel L f k) by field_simp]
    simp [sampledProfileKernel, hL.ne', Nat.cast_add]
    field_simp
  · rw [ite_eq_right hpos, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k + lag.natAbs < K * L + 1 := by
      have hk'' := Finset.mem_range.mp hk
      rw [Nat.lt_sub_iff_add_lt] at hk''
      omega
    have hk0 : k < K * L + 1 := by omega
    rw [show (L : ℝ) * (sampledProfileKernel L f k *
      sampledProfileKernel L f (k + lag.natAbs)) = (1 / (L : ℝ)) *
      ((L : ℝ) * sampledProfileKernel L f (k + lag.natAbs)) *
      ((L : ℝ) * sampledProfileKernel L f k) by field_simp]
    simp [sampledProfileKernel, hL.ne', Nat.cast_add]
    field_simp

private theorem sampled_scaled_lag_eq_shifted_grid
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ)
    (hL : 0 < L) (hd : lag.natAbs ≤ K * L) (hfK : f (K : ℝ) = 0) :
    (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
      (sampledProfileKernel L f) lag =
      (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L - lag.natAbs),
        f (((k + lag.natAbs : ℕ) : ℝ) / (L : ℝ)) * f ((k : ℝ) / (L : ℝ)) := by
  rw [sampled_scaled_lag_eq_extended f K L lag hL hd hfK]
  by_cases hd0 : 0 < lag.natAbs
  · rw [sampled_shifted_sum_endpoint_eq f K L lag.natAbs hL hd hd0 hfK]
  · have hz : lag.natAbs = 0 := by omega
    rw [hz]
    simp only [Nat.sub_zero, Nat.add_zero]
    rw [sampled_shifted_sum_endpoint_eq_zero f K L hL hfK]
    simp [pow_two]

private theorem compact_value_bound
    (f : ℝ → ℝ) (K : ℕ) (hK : 0 < K) (hf : ContDiff ℝ 1 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) K, |f x| ≤ B := by
  let g : ℝ → ℝ := fun x => |f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) := hf.continuous.continuousOn.abs
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (g 0))
    (hB 0 ⟨le_rfl, by exact_mod_cast hK.le⟩)
  exact ⟨B, hB0, fun x hx => by simpa [g, Real.norm_eq_abs] using hB x hx⟩

private theorem compact_deriv_bound_nonneg
    (f : ℝ → ℝ) (K : ℕ) (hK : 0 < K) (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) K, ‖deriv f x‖ ≤ M := by
  let g : ℝ → ℝ := fun x => ‖deriv f x‖
  have hg : ContinuousOn g (Icc (0 : ℝ) K) := by
    simpa [g, iteratedDeriv_one] using
      (hf.continuous_iteratedDeriv 1 (by norm_num)).continuousOn.norm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0))
    (hM 0 ⟨le_rfl, by exact_mod_cast hK.le⟩)
  exact ⟨M, hM0, fun x hx => by simpa [g, Real.norm_eq_abs] using hM x hx⟩

private theorem sampled_shift_bound
    (g : ℝ → ℝ) (K L d : ℕ) (_hK : 0 < K) (hL : 0 < L) (hd : d ≤ K * L)
    (hg : ContDiff ℝ 1 g) (M : ℝ)
    (hM : ∀ x ∈ Icc (0 : ℝ) K, ‖deriv g x‖ ≤ M) :
    ∀ k < K * L - d, ‖g (((k + d : ℕ) : ℝ) / (L : ℝ)) -
      g ((k : ℝ) / (L : ℝ))‖ ≤ M *
        ((((k + d : ℕ) : ℝ) / L) - ((k : ℝ) / L)) := by
  intro k hk
  have hkd : k + d < K * L := by omega
  have hx0 : (k : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (le_trans (Nat.le_add_right k d) (Nat.le_of_lt hkd))
  have hx1 : (((k + d : ℕ) : ℝ) / L) ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.le_of_lt hkd)
  have hseg : ∀ y ∈ Ico ((k : ℝ) / L) (((k + d : ℕ) : ℝ) / L),
      ‖deriv g y‖ ≤ M := by
    intro y hy
    exact hM y ⟨le_trans hx0.1 hy.1, le_trans hy.2.le hx1.2⟩
  exact norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := deriv g)
    (C := M) (fun y hy => (((hg.differentiable (by norm_num)) y).hasDerivAt).hasDerivWithinAt)
    (fun y hy => hseg y hy) (((k + d : ℕ) : ℝ) / L) ⟨by
      apply (div_le_div_iff_of_pos_right (by exact_mod_cast hL)).2
      norm_num [Nat.cast_add], le_rfl⟩

private theorem sampled_shift_bound_mesh
    (f : ℝ → ℝ) (K L d : ℕ) (hK : 0 < K) (hL : 0 < L) (hd : d ≤ K * L)
    (hf : ContDiff ℝ 1 f) (M : ℝ)
    (hM : ∀ x ∈ Icc (0 : ℝ) K, ‖deriv f x‖ ≤ M) :
    ∀ k < K * L - d,
      |f (((k + d : ℕ) : ℝ) / (L : ℝ)) - f ((k : ℝ) / (L : ℝ))| ≤
        M * (d : ℝ) / (L : ℝ) := by
  intro k hk
  have h := sampled_shift_bound f K L d hK hL hd hf M hM k hk
  rw [Real.norm_eq_abs] at h
  have hcast : (((k + d : ℕ) : ℝ) / (L : ℝ) - (k : ℝ) / L) =
      (d : ℝ) / L := by
    rw [Nat.cast_add]
    ring
  rw [hcast] at h
  convert h using 1
  all_goals ring_nf

private theorem sampled_scaled_lag_sub_grid_norm_le
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ) (M B : ℝ)
    (hK : 0 < K) (hL : 0 < L) (hd : lag.natAbs ≤ K * L)
    (hf : ContDiff ℝ 1 f) (hfK : f K = 0) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ Icc (0 : ℝ) K, |f x| ≤ B)
    (hfM : ∀ x ∈ Icc (0 : ℝ) K, ‖deriv f x‖ ≤ M) :
    ‖(L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
        (sampledProfileKernel L f) lag -
      (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L),
        (f ((k : ℝ) / (L : ℝ))) ^ 2‖ ≤
      ((K : ℝ) * M * (lag.natAbs : ℝ) * B +
        (lag.natAbs : ℝ) * B ^ 2) / (L : ℝ) := by
  let d := lag.natAbs
  let F : ℕ → ℝ := fun k => f ((k : ℝ) / (L : ℝ))
  have hnorm := sampled_scaled_lag_eq_shifted_grid f K L lag hL hd hfK
  have hprod := abs_shifted_product_sum_sub_square_sum_le F (K * L) d
      (M * (d : ℝ) / L) B hd (by positivity) hB (by
        intro k hk
        apply hfB
        constructor
        · positivity
        · apply (div_le_iff₀ (by exact_mod_cast hL)).2
          exact_mod_cast (Nat.le_of_lt hk)) (by
        intro k hk
        exact sampled_shift_bound_mesh f K L d hK hL hd hf M hfM k hk)
  rw [hnorm]
  have hrewrite :
      (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L - d),
          f (((k + d : ℕ) : ℝ) / L) * f ((k : ℝ) / L) -
        (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L),
          (f ((k : ℝ) / L)) ^ 2 =
      (1 / (L : ℝ)) * ((∑ k ∈ Finset.range (K * L - d), F (k + d) * F k) -
        ∑ k ∈ Finset.range (K * L), (F k) ^ 2) := by
    dsimp [F]
    ring
  rw [hrewrite, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    (1 / (L : ℝ)) * |(∑ k ∈ Finset.range (K * L - d), F (k + d) * F k) -
        ∑ k ∈ Finset.range (K * L), (F k) ^ 2| ≤
      (1 / (L : ℝ)) * ((K * L - d : ℝ) * (M * (d : ℝ) / L) * B +
        (d : ℝ) * B ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hprod using 1
      all_goals norm_num [Nat.cast_mul]
    _ ≤ ((K : ℝ) * M * (d : ℝ) * B + (d : ℝ) * B ^ 2) / (L : ℝ) := by
      dsimp [d]
      have hKL : (K * L - lag.natAbs : ℝ) ≤ (K * L : ℝ) := by
        exact_mod_cast Nat.sub_le (K * L) lag.natAbs
      have hfirst : (K * L - lag.natAbs : ℝ) *
          (M * (lag.natAbs : ℝ) / L) * B ≤
          (K * L : ℝ) * (M * (lag.natAbs : ℝ) / L) * B := by
        gcongr
      rw [div_eq_mul_inv]
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL
      calc
        (1 / (L : ℝ)) * ((K * L - lag.natAbs : ℝ) *
            (M * (lag.natAbs : ℝ) / L) * B + (lag.natAbs : ℝ) * B ^ 2) ≤
            (1 / (L : ℝ)) * ((K * L : ℝ) *
              (M * (lag.natAbs : ℝ) / L) * B + (lag.natAbs : ℝ) * B ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst (le_refl _)) (by positivity)
        _ = ((K : ℝ) * M * (lag.natAbs : ℝ) * B +
            (lag.natAbs : ℝ) * B ^ 2) / (L : ℝ) := by
          field_simp

private theorem eventually_natAbs_le_mul (K : ℕ) (lag : ℤ) (hK : 0 < K) :
    ∀ᶠ L : ℕ in atTop, lag.natAbs ≤ K * L := by
  filter_upwards [eventually_ge_atTop lag.natAbs] with L hL
  exact le_trans hL (by
    have hK' : 1 ≤ K := hK
    simpa using Nat.mul_le_mul_right L hK')

private theorem sampled_lag_sub_grid_tendsto_zero
    (f : ℝ → ℝ) (K : ℕ) (lag : ℤ)
    (hK : 0 < K) (hf : ContDiff ℝ 1 f) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
          (sampledProfileKernel L f) lag -
        (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L),
          (f ((k : ℝ) / (L : ℝ))) ^ 2) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := compact_value_bound f K hK hf
  obtain ⟨M, hM0, hM⟩ := compact_deriv_bound_nonneg f K hK hf
  let C : ℝ := (K : ℝ) * M * (lag.natAbs : ℝ) * B +
    (lag.natAbs : ℝ) * B ^ 2
  have herr : ∀ᶠ L : ℕ in atTop, ‖
      (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
          (sampledProfileKernel L f) lag -
        (1 / (L : ℝ)) * ∑ k ∈ Finset.range (K * L),
          (f ((k : ℝ) / (L : ℝ))) ^ 2‖ ≤ C / (L : ℝ) := by
    filter_upwards [eventually_gt_atTop 0, eventually_natAbs_le_mul K lag hK]
      with L hL hlag
    simpa [C] using sampled_scaled_lag_sub_grid_norm_le f K L lag M B hK hL hlag
      hf hfK hM0 hB0 hB hM
  have hbound : Tendsto (fun L : ℕ => C / (L : ℝ)) atTop (𝓝 0) := by
    simpa [C, div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa using squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    herr hbound

theorem tendsto_sampledProfile_lagInnerProductCutoff_scaled
    (f : ℝ → ℝ) (K : ℕ) (lag : ℤ)
    (hK : 0 < K) (hf : ContDiff ℝ 1 f) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
        (sampledProfileKernel L f) lag) atTop
      (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2)) := by
  let g : ℝ → ℝ := fun x => f x ^ 2
  have hg : ContDiff ℝ 1 g := hf.pow 2
  obtain ⟨M, hM0, hM⟩ := compact_deriv_bound_nonneg g K hK hg
  have hgrid := direct_c1_grid_tendsto g K hK hg ⟨M, hM⟩
  have herr := sampled_lag_sub_grid_tendsto_zero f K lag hK hf hfK
  have hadd := herr.add hgrid
  convert hadd using 1 <;> simp [g, sub_add_cancel]

private theorem deriv_continuous_bound
    (f : ℝ → ℝ) (K : ℕ) (hf : ContDiff ℝ 1 f) :
    ContinuousOn (deriv f) (Icc (0 : ℝ) K) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M := by
  have hderiv : ContinuousOn (deriv f) (Icc (0 : ℝ) K) := by
    simpa [iteratedDeriv_one] using
      (hf.continuous_iteratedDeriv 1 (by norm_num)).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hderiv.abs)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (deriv f 0)) (by
    simpa [Real.norm_eq_abs] using hM 0
      ⟨le_rfl, by exact_mod_cast (Nat.zero_le K)⟩)
  exact ⟨hderiv, M, hM0, fun x hx => by
    simpa [Real.norm_eq_abs] using hM x hx⟩

private theorem exists_cell_deriv_eq_scaled_difference
    (f : ℝ → ℝ) (K L j : ℕ) (hL : 0 < L) (_hj : j < K * L)
    (hf : ContDiff ℝ 1 f) :
    ∃ c ∈ Ioo ((j : ℝ) / L) (((j + 1 : ℕ) : ℝ) / L),
      deriv f c = (L : ℝ) *
        (f (((j + 1 : ℕ) : ℝ) / L) - f ((j : ℝ) / L)) := by
  have hleft : (j : ℝ) / L < ((j + 1 : ℕ) : ℝ) / L := by
    apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hL)).2
    norm_num [Nat.cast_add]
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope f hleft
    hf.continuous.continuousOn (hf.differentiable (by norm_num)).differentiableOn
  refine ⟨c, hc, ?_⟩
  rw [hderiv]
  have hden : ((j + 1 : ℕ) : ℝ) / L - (j : ℝ) / L = 1 / L := by
    rw [Nat.cast_add]
    field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hL)]
    ring
  rw [hden]
  field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hL)]

private theorem scaled_increment_sub_deriv_le
    (f : ℝ → ℝ) (K L j : ℕ) (η δ : ℝ) (hL : 0 < L) (hj : j < K * L)
    (_hη : 0 ≤ η) (_hδ : 0 < δ) (hmesh : (1 : ℝ) / L < δ)
    (hf : ContDiff ℝ 1 f)
    (hmod : ∀ x ∈ Icc (0 : ℝ) K, ∀ y ∈ Icc (0 : ℝ) K,
      |x - y| < δ → |deriv f x - deriv f y| ≤ η) :
    |(L : ℝ) * (f (((j + 1 : ℕ) : ℝ) / L) - f ((j : ℝ) / L)) -
      deriv f ((j : ℝ) / L)| ≤ η := by
  obtain ⟨c, hc, hcv⟩ := exists_cell_deriv_eq_scaled_difference f K L j hL hj hf
  have hleft : (j : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.le_of_lt hj)
  have hright : ((j + 1 : ℕ) : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.succ_le_of_lt hj)
  have hcI : c ∈ Icc (0 : ℝ) K := ⟨le_trans hleft.1 hc.1.le, le_trans hc.2.le hright.2⟩
  have hdist : |c - (j : ℝ) / L| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le)]
    have hlen : ((j + 1 : ℕ) : ℝ) / L - (j : ℝ) / L = 1 / L := by
      rw [Nat.cast_add]
      field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hL)]
      ring
    have hle : c - (j : ℝ) / L ≤
        ((j + 1 : ℕ) : ℝ) / L - (j : ℝ) / L := by linarith [hc.2]
    have hmesh' := hmesh
    rw [← hlen] at hmesh'
    exact lt_of_le_of_lt hle hmesh'
  rw [← hcv]
  exact hmod _ hcI _ hleft hdist

private theorem sq_sub_sq_abs_le
    (a b M η : ℝ) (_hM : 0 ≤ M) (hη : 0 ≤ η) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hab : |a - b| ≤ η) : |a^2 - b^2| ≤ 2 * M * η := by
  rw [show a^2 - b^2 = (a - b) * (a + b) by ring, abs_mul]
  have hs : |a + b| ≤ 2 * M := by
    calc |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ M + M := add_le_add ha hb
      _ = 2 * M := by ring
  calc |a - b| * |a + b| ≤ η * (2 * M) := mul_le_mul hab hs (abs_nonneg _) hη
    _ = 2 * M * η := by ring

private theorem sampledDifferenceValue_interior
    (f : ℝ → ℝ) (K L j : ℕ) (_hL : 0 < L) (hj : 1 ≤ j) (hjK : j ≤ K * L) :
    sampledDifferenceValue L (K * L + 1) f (j : ℤ) =
      f ((j : ℝ) / L) - f (((j - 1 : ℕ) : ℝ) / L) := by
  rw [sampledDifferenceValue_eq]
  unfold sampledProfileValue
  have hjlt : j < K * L + 1 := by omega
  have hjpos : (0 : ℤ) ≤ j := by exact_mod_cast (Nat.zero_le j)
  have hjmpos : (0 : ℤ) ≤ (j : ℤ) - 1 := by omega
  have hjmnat : ((j : ℤ) - 1).toNat = j - 1 := by omega
  have hjm_lt : ((j : ℤ) - 1).toNat < K * L + 1 := by rw [hjmnat]; omega
  have harg : ((j : ℤ) : ℝ) - 1 = ((j - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ j)]
  have hargz : ((j : ℤ) - 1 : ℤ) = (j - 1 : ℕ) := by omega
  rw [ite_eq_left ⟨hjpos, hjlt⟩, ite_eq_left ⟨hjmpos, hjm_lt⟩]
  norm_num [hargz, harg]

private theorem sampledDifferenceValue_direct
    (f : ℝ → ℝ) (K L j : ℕ) (hL : 0 < L) (hj : j < K * L) :
    (L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ)) =
      (L : ℝ) * (f (((j + 1 : ℕ) : ℝ) / L) - f ((j : ℝ) / L)) := by
  rw [sampledDifferenceValue_interior f K L (j + 1) hL (by omega) (by omega)]
  congr 2

private theorem scaled_increment_abs_le
    (f : ℝ → ℝ) (K L j : ℕ) (M : ℝ) (hL : 0 < L) (hj : j < K * L)
    (hf : ContDiff ℝ 1 f)
    (hM : ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M) :
    |(L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ))| ≤ M := by
  rw [sampledDifferenceValue_direct f K L j hL hj]
  obtain ⟨c, hc, hcv⟩ := exists_cell_deriv_eq_scaled_difference f K L j hL hj hf
  have hleft : (j : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.le_of_lt hj)
  have hright : ((j + 1 : ℕ) : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.succ_le_of_lt hj)
  rw [← hcv]
  exact hM c ⟨le_trans hleft.1 hc.1.le, le_trans hc.2.le hright.2⟩

private theorem sampledProfile_difference_zero
    (f : ℝ → ℝ) (L : ℕ) (_hL : 0 < L) (hf0 : f 0 = 0) :
    Discrete.difference (sampledProfileKernel L f) 0 = 0 := by
  simp [Discrete.difference, sampledProfileKernel, hf0]

private theorem difference_zeroLag_sum_reindex
    (f : ℝ → ℝ) (K L : ℕ) (hL : 0 < L) (hf0 : f 0 = 0) :
    ∑ k ∈ Finset.range (K * L + 1),
      (Discrete.difference (sampledProfileKernel L f) k)^2 =
    ∑ j ∈ Finset.range (K * L),
      (Discrete.difference (sampledProfileKernel L f) (j + 1))^2 := by
  let q : ℕ → ℝ := fun k =>
    (Discrete.difference (sampledProfileKernel L f) k)^2
  have hshift : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), q k = q 0 +
        ∑ j ∈ Finset.range n, q (j + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  rw [show (∑ k ∈ Finset.range (K * L + 1), q k) =
      q 0 + ∑ j ∈ Finset.range (K * L), q (j + 1) by exact hshift (K * L)]
  have hq0 : q 0 = 0 := by
    simp [q, sampledProfile_difference_zero f L hL hf0]
  rw [hq0, zero_add]

private theorem lagInnerProductCutoff_zero_eq_difference_squares
    (f : ℝ → ℝ) (K L : ℕ) (hL : 0 < L) (hf0 : f 0 = 0) :
    lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) 0 =
    ∑ j ∈ Finset.range (K * L),
      (Discrete.difference (sampledProfileKernel L f) (j + 1))^2 := by
  have hshift := lagInnerProductCutoff_natCast_eq_shifted
    (sampledProfileHorizon K L) (Discrete.difference (sampledProfileKernel L f)) 0 (by omega)
  change lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) (0 : ℤ) = _
  rw [show lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) (0 : ℤ) =
      ∑ k ∈ Finset.range (sampledProfileHorizon K L - 0),
        Discrete.difference (sampledProfileKernel L f) (k + 0) *
          Discrete.difference (sampledProfileKernel L f) k by simpa using hshift]
  simp only [Nat.sub_zero, Nat.add_zero]
  rw [show sampledProfileHorizon K L = K * L + 1 by rfl, Finset.sum_range_succ]
  rw [show Discrete.difference (sampledProfileKernel L f) (K * L) *
      Discrete.difference (sampledProfileKernel L f) (K * L) =
      (Discrete.difference (sampledProfileKernel L f) (K * L))^2 by ring]
  have hsq : (∑ x ∈ Finset.range (K * L),
      Discrete.difference (sampledProfileKernel L f) x *
        Discrete.difference (sampledProfileKernel L f) x) =
      ∑ x ∈ Finset.range (K * L),
        (Discrete.difference (sampledProfileKernel L f) x)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsq, ← Finset.sum_range_succ]
  exact difference_zeroLag_sum_reindex f K L hL hf0

private theorem difference_zeroLag_normalization
    (f : ℝ → ℝ) (K L : ℕ) (hL : 0 < L) (hf0 : f 0 = 0) :
    (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) 0 =
    (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
      ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
        (((j + 1 : ℕ) : ℤ)))^2 := by
  rw [lagInnerProductCutoff_zero_eq_difference_squares f K L hL hf0]
  calc
    (L : ℝ)^3 * ∑ j ∈ Finset.range (K * L),
        (Discrete.difference (sampledProfileKernel L f) (j + 1))^2 =
      (L : ℝ) * ∑ j ∈ Finset.range (K * L),
        ((L : ℝ) * Discrete.difference (sampledProfileKernel L f) (j + 1))^2 := by
      rw [Finset.mul_sum]
      calc
        ∑ j ∈ Finset.range (K * L), (L : ℝ)^3 *
            (Discrete.difference (sampledProfileKernel L f) (j + 1))^2 =
          ∑ j ∈ Finset.range (K * L), (L : ℝ) *
            ((L : ℝ) * Discrete.difference (sampledProfileKernel L f) (j + 1))^2 := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (L : ℝ) * ∑ j ∈ Finset.range (K * L),
            ((L : ℝ) * Discrete.difference (sampledProfileKernel L f) (j + 1))^2 := by
              rw [Finset.mul_sum]
    _ = (L : ℝ) * ∑ j ∈ Finset.range (K * L),
        (sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ)))^2 := by
      apply congrArg (fun z : ℝ => (L : ℝ) * z)
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j + 1 < K * L + 1 :=
        Nat.succ_lt_succ (Finset.mem_range.mp hj)
      rw [← sampledDifferenceKernel_value_bridge L (K * L + 1) f hjlt hL]
    _ = (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
          (((j + 1 : ℕ) : ℤ)))^2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hL)]


private theorem continuous_grid_error
    (g : ℝ → ℝ) (K L : ℕ) (ε δ : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hε : 0 < ε) (_hδ : 0 < δ) (hmesh : (1 : ℝ) / L < δ)
    (hg : ContinuousOn g (Icc (0 : ℝ) K))
    (hmod : ∀ x ∈ Icc (0 : ℝ) K, ∀ y ∈ Icc (0 : ℝ) K,
      |x - y| < δ → ‖g x - g y‖ < ε / K) :
    ‖(1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) / (L : ℝ)) - ∫ x in (0 : ℝ)..(K : ℝ), g x‖ ≤ ε := by
  let h : ℝ := 1 / (L : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hKL : (K * L : ℝ) * h = (K : ℝ) := by
    dsimp [h]
    field_simp
  have hsum : ∑ j ∈ Finset.range (K * L),
      ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x =
      ∫ x in (0 : ℝ)..(K : ℝ), g x := by
    let a : ℕ → ℝ := fun j => (j : ℝ) * h
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (f := g) (a := a) (n := K * L) (μ := volume) (fun j hj => by
        have hab : a j ≤ a (j + 1) := by
          dsimp [a]
          exact mul_le_mul_of_nonneg_right (by norm_num) hh.le
        have hsub : [[a j, a (j + 1)]] ⊆ Icc (0 : ℝ) K := by
          intro x hx
          rw [uIcc_of_le hab] at hx
          exact ⟨le_trans (by positivity) hx.1, le_trans hx.2 (by
              dsimp [a]
              calc
                ((j + 1 : ℕ) : ℝ) * h ≤ (K * L : ℝ) * h := by
                  gcongr
                  exact_mod_cast (Nat.succ_le_of_lt hj)
                _ = (K : ℝ) := hKL)⟩
        simpa [uIcc_of_le hab] using (hg.mono hsub).intervalIntegrable)
    simpa [a, Nat.cast_add, add_mul, hKL]
      using hs
  have hcell : ∀ j ∈ Finset.range (K * L),
      ‖h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x‖ ≤
      h * (ε / (K : ℝ)) := by
    intro j hj
    have hj' : j + 1 ≤ K * L := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hleft : (j : ℝ) * h ∈ Icc (0 : ℝ) K := by
      constructor
      · positivity
      · rw [← hKL]
        gcongr
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hright : ((j : ℝ) + 1) * h ∈ Icc (0 : ℝ) K := by
      constructor
      · positivity
      · rw [← hKL]
        gcongr
        exact_mod_cast hj'
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => g ((j : ℝ) * h) - g x)
      (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h)
      (C := ε / (K : ℝ)) (by
        intro x hx
        have hab : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by linarith
        have hxI : x ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) := by
          rw [uIoc_of_le hab] at hx
          exact ⟨le_of_lt hx.1, hx.2⟩
        have hx' : x ∈ Icc (0 : ℝ) K :=
          ⟨le_trans hleft.1 hxI.1, le_trans hxI.2 hright.2⟩
        have hdist : |(j : ℝ) * h - x| < δ := by
          have hxle : x - (j : ℝ) * h ≤ h := by linarith [hxI.2]
          have hxnonneg : 0 ≤ x - (j : ℝ) * h := by linarith [hxI.1]
          rw [abs_sub_comm, abs_of_nonneg hxnonneg]
          exact lt_of_le_of_lt hxle (by simpa [h] using hmesh)
        simpa [norm_sub_rev] using (hmod x hx' ((j : ℝ) * h) hleft
          (by simpa [abs_sub_comm] using hdist)).le)
    have hsub : (∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h,
        (fun x => g ((j : ℝ) * h) - g x) x) =
        h * g ((j : ℝ) * h) - ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const]
      · rw [intervalIntegral.integral_const]
        congr 1
        dsimp
        ring
      · have hsub : [[(j : ℝ) * h, ((j : ℝ) + 1) * h]] ⊆ Icc (0 : ℝ) K := by
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact ⟨le_trans hleft.1 hx.1, le_trans hx.2 hright.2⟩
        exact (hg.mono hsub).intervalIntegrable
    rw [← hsub]
    convert hi using 1
    have hlen : |((j : ℝ) + 1) * h - (j : ℝ) * h| = h := by
      rw [show ((j : ℝ) + 1) * h - (j : ℝ) * h = h by ring, abs_of_pos hh]
    rw [hlen]
    ring
  have herr : ‖∑ j ∈ Finset.range (K * L),
      (h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x)‖ ≤
      (K * L : ℝ) * (h * (ε / (K : ℝ))) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K * L),
          ‖h * g ((j : ℝ) * h) -
            ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (K * L), h * (ε / (K : ℝ)) :=
        Finset.sum_le_sum (fun j hj => hcell j hj)
      _ = (K * L : ℝ) * (h * (ε / (K : ℝ))) := by simp
  have hrewrite : (∑ j ∈ Finset.range (K * L),
      (h * g ((j : ℝ) * h) -
        ∫ x in (j : ℝ) * h..((j : ℝ) + 1) * h, g x)) =
      h * ∑ j ∈ Finset.range (K * L), g ((j : ℝ) * h) -
        ∫ x in (0 : ℝ)..(K : ℝ), g x := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, hsum]
  rw [hrewrite] at herr
  have hleft' : (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
      g ((j : ℝ) / (L : ℝ)) = h * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) * h) := by
    apply congrArg (fun s => (1 / (L : ℝ)) * s)
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [h]
    field_simp
  rw [hleft']
  convert herr using 1
  dsimp [h]
  field_simp

private theorem continuous_grid_tendsto
    (g : ℝ → ℝ) (K : ℕ) (hK : 0 < K)
    (hg : ContinuousOn g (Icc (0 : ℝ) K)) :
    Tendsto (fun L : ℕ =>
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        g ((j : ℝ) / (L : ℝ))) atTop
      (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), g x)) := by
  have huc : UniformContinuousOn g (Icc (0 : ℝ) K) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by dsimp [ε']; linarith
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε' / K) (by positivity)
  have hmesh : Tendsto (fun L : ℕ => (1 : ℝ) / L) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)) using 1 ;
      simp [Function.comp_def, one_div]
  filter_upwards [eventually_gt_atTop 0, hmesh.eventually (Iio_mem_nhds hδ)] with L hLpos hL
  have herr := continuous_grid_error g K L ε' δ hK hLpos hε' hδ hL hg
    (fun x hx y hy hxy => hmod x hx y hy hxy)
  have hdist : dist ((1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
      g ((j : ℝ) / (L : ℝ))) (∫ x in (0 : ℝ)..(K : ℝ), g x) < ε := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt herr (by dsimp [ε']; linarith)
  exact hdist


private theorem inv_mul_sum_sub_inv_mul_sum_eq
    (L : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ) :
    (1 / (L : ℝ)) * (∑ j ∈ s, a j) -
      (1 / (L : ℝ)) * (∑ j ∈ s, b j) =
    (1 / (L : ℝ)) * ∑ j ∈ s, (a j - b j) := by
  calc
    (1 / (L : ℝ)) * (∑ j ∈ s, a j) -
        (1 / (L : ℝ)) * (∑ j ∈ s, b j) =
      (∑ j ∈ s, (1 / (L : ℝ)) * a j) -
        (∑ j ∈ s, (1 / (L : ℝ)) * b j) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ j ∈ s, ((1 / (L : ℝ)) * a j - (1 / (L : ℝ)) * b j) := by
          rw [Finset.sum_sub_distrib]
    _ = (1 / (L : ℝ)) * ∑ j ∈ s, (a j - b j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring


private theorem sampledDifference_cellAverage_square_sum_sub_grid_norm_le
    (f : ℝ → ℝ) (K L : ℕ) (M η δ : ℝ)
    (hK : 0<K) (hL : 0<L) (hM0 : 0≤M) (hη0 : 0≤η)
    (hδ : 0<δ) (hmesh : (1:ℝ)/L<δ) (hf : ContDiff ℝ 1 f)
    (hM : ∀x∈Icc (0:ℝ) K, |deriv f x|≤M)
    (hmod : ∀x∈Icc (0:ℝ) K, ∀y∈Icc (0:ℝ) K,
       |x-y|<δ → |deriv f x-deriv f y|≤η) :
     ‖(1/(L:ℝ)) * (∑ j ∈ Finset.range (K*L),
        ((L:ℝ)*sampledDifferenceValue L (K*L+1) f (((j+1:ℕ):ℤ)))^2
      ) - (1/(L:ℝ)) * (∑ j ∈ Finset.range (K*L),
        (deriv f ((j:ℝ)/(L:ℝ)))^2)‖
      ≤ (K:ℝ)*(2*M*η) := by
  let a : ℕ → ℝ := fun j =>
    ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ))) ^ 2
  let b : ℕ → ℝ := fun j => (deriv f ((j : ℝ) / (L : ℝ))) ^ 2
  have hrewrite :
      (1 / (L : ℝ)) * (∑ j ∈ Finset.range (K * L), a j) -
        (1 / (L : ℝ)) * (∑ j ∈ Finset.range (K * L), b j) =
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L), (a j - b j) :=
    inv_mul_sum_sub_inv_mul_sum_eq L (Finset.range (K * L)) a b
  have hterm : ∀ j ∈ Finset.range (K * L), |a j - b j| ≤ 2 * M * η := by
    intro j hj
    dsimp [a, b]
    apply sq_sub_sq_abs_le _ _ M η hM0 hη0
    · exact scaled_increment_abs_le f K L j M hL
        (Finset.mem_range.mp hj) hf hM
    · have hleft : (j : ℝ) / (L : ℝ) ∈ Icc (0 : ℝ) K := by
        constructor
        · positivity
        · apply (div_le_iff₀ (by exact_mod_cast hL)).2
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
      exact hM _ hleft
    · have hinc := scaled_increment_sub_deriv_le f K L j η δ hL
          (Finset.mem_range.mp hj) hη0 hδ hmesh hf hmod
      have hbridge := sampledDifferenceValue_direct f K L j hL
        (Finset.mem_range.mp hj)
      change |(L : ℝ) * sampledDifferenceValue L (K * L + 1) f
          (((j + 1 : ℕ) : ℤ)) - deriv f ((j : ℝ) / L)| ≤ η
      rw [hbridge]
      exact hinc
  rw [Real.norm_eq_abs, hrewrite, abs_mul]
  have hsum :
      |∑ j ∈ Finset.range (K * L), (a j - b j)| ≤
        ∑ j ∈ Finset.range (K * L), |a j - b j| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      ∑ j ∈ Finset.range (K * L), |a j - b j| ≤
        ∑ _j ∈ Finset.range (K * L), (2 * M * η) := by
    exact Finset.sum_le_sum (fun j hj => hterm j hj)
  have hconst :
      (1 / (L : ℝ)) * ∑ _j ∈ Finset.range (K * L), (2 * M * η) =
        (K : ℝ) * (2 * M * η) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num [Nat.cast_mul]
    field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hL)]
  calc
    |1 / (L : ℝ)| * |∑ j ∈ Finset.range (K * L), (a j - b j)| ≤
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L), |a j - b j| := by
      rw [abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1 / (L : ℝ)) * ∑ _j ∈ Finset.range (K * L), (2 * M * η) := by
      exact mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = (K : ℝ) * (2 * M * η) := hconst


private theorem cellAverage_square_sum_sub_grid_tendsto_zero
    (f : ℝ → ℝ) (K : ℕ) (hK : 0 < K) (hf : ContDiff ℝ 1 f) :
    Tendsto (fun L : ℕ =>
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
          (((j + 1 : ℕ) : ℤ))) ^ 2 -
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        (deriv f ((j : ℝ) / (L : ℝ))) ^ 2) atTop (𝓝 0) := by
  obtain ⟨hderiv, M, hM0, hM⟩ := deriv_continuous_bound f K hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / ((K : ℝ) * (2 * M + 1))
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hden : 0 < (K : ℝ) * (2 * M + 1) := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have huc : UniformContinuousOn (deriv f) (Icc (0 : ℝ) K) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hderiv
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  have hmesh : Tendsto (fun L : ℕ => (1 : ℝ) / L) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)) using 1 ;
      simp [Function.comp_def, one_div]
  filter_upwards [eventually_gt_atTop 0, hmesh.eventually (Iio_mem_nhds hδ)] with L hLpos hL
  have herr := sampledDifference_cellAverage_square_sum_sub_grid_norm_le f K L M η δ
    hK hLpos hM0 hη.le hδ hL hf hM
    (fun x hx y hy hxy => (hmod x hx y hy hxy).le)
  have hbound : (K : ℝ) * (2 * M * η) < ε := by
    dsimp [η]
    field_simp [hden.ne']
    nlinarith [hM0, hK0, hε]
  have hdist : dist ((1 / (L : ℝ)) * (∑ j ∈ Finset.range (K * L),
      ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ))) ^ 2) -
        (1 / (L : ℝ)) * (∑ j ∈ Finset.range (K * L),
          (deriv f ((j : ℝ) / (L : ℝ))) ^ 2)) 0 < ε := by
    simpa [Real.dist_eq] using (lt_of_le_of_lt herr hbound)
  exact hdist

private theorem tendsto_sampledDifference_zeroLagInnerProductCutoff_scaled
    (f : ℝ → ℝ) (K : ℕ) (hK : 0 < K)
    (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ) ^ 3 *
        lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0) atTop
      (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x) ^ 2)) := by
  obtain ⟨hderiv, M, hM0, hM⟩ := deriv_continuous_bound f K hf
  let g : ℝ → ℝ := fun x => (deriv f x) ^ 2
  have hg : ContinuousOn g (Icc (0 : ℝ) K) := hderiv.pow 2
  have hgrid := continuous_grid_tendsto g K hK hg
  have herr := cellAverage_square_sum_sub_grid_tendsto_zero (f := f) K hK hf
  have hcombined : Tendsto (fun L : ℕ =>
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ))) ^ 2)
      atTop (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), g x)) := by
    have hadd := herr.add hgrid
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  have heq : (fun L : ℕ => (L : ℝ) ^ 3 *
        lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0) =ᶠ[atTop]
      (fun L : ℕ => (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L),
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f (((j + 1 : ℕ) : ℤ))) ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact difference_zeroLag_normalization f K L hL hf0
  exact hcombined.congr' heq.symm

private theorem sum_range_succ_shift_of_right_zero
    (F G : ℕ → ℝ) (n : ℕ) (hG0 : G 0 = 0) :
    ∑ k ∈ Finset.range (n + 1), F k * G k =
      ∑ j ∈ Finset.range n, F (j + 1) * G (j + 1) := by
  induction n with
  | zero => simp [hG0]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]

private theorem difference_lag_sum_reindex
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ)
    (hL : 0 < L) (hf0 : f 0 = 0) (hd : lag.natAbs ≤ K * L) :
    lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) lag =
    ∑ j ∈ Finset.range (K * L - lag.natAbs),
      Discrete.difference (sampledProfileKernel L f) (j + 1 + lag.natAbs) *
      Discrete.difference (sampledProfileKernel L f) (j + 1) := by
  let m := K * L
  let d := lag.natAbs
  let D : ℕ → ℝ := Discrete.difference (sampledProfileKernel L f)
  have hd' : d ≤ m + 1 := by omega
  have hlag := lagInnerProductCutoff_eq_shifted_natAbs (m + 1) D lag hd'
  have hD0 : D 0 = 0 := by
    exact sampledProfile_difference_zero f L hL hf0
  have hsum : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), D (k + d) * D k =
        ∑ j ∈ Finset.range n, D (j + 1 + d) * D (j + 1) := by
    intro n
    simpa [D, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      sum_range_succ_shift_of_right_zero (fun k => D (k + d)) D n hD0
  change lagInnerProductCutoff (m + 1) D lag = _
  have hlen : m + 1 - d = (m - d) + 1 := by omega
  rw [hlag]
  by_cases hsign : 0 ≤ lag
  · simp [hsign]
    rw [hlen, hsum]
    simp [D, d, m]
  · simp [hsign]
    have hcomm :
        (∑ k ∈ Finset.range (m + 1 - d), D k * D (k + d)) =
          ∑ k ∈ Finset.range (m + 1 - d), D (k + d) * D k := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hcomm, hlen, hsum]
    simp [D, d, m]

private theorem difference_lag_normalization
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ)
    (hL : 0 < L) (hf0 : f 0 = 0) (hd : lag.natAbs ≤ K * L) :
    (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) lag =
    (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L - lag.natAbs),
      ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
        (((j + lag.natAbs + 1 : ℕ) : ℤ))) *
      ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
        (((j + 1 : ℕ) : ℤ))) := by
  rw [difference_lag_sum_reindex f K L lag hL hf0 hd]
  calc
    (L : ℝ)^3 * ∑ j ∈ Finset.range (K * L - lag.natAbs),
        Discrete.difference (sampledProfileKernel L f) (j + 1 + lag.natAbs) *
          Discrete.difference (sampledProfileKernel L f) (j + 1) =
      ∑ j ∈ Finset.range (K * L - lag.natAbs),
        (L : ℝ)^3 *
          (Discrete.difference (sampledProfileKernel L f) (j + 1 + lag.natAbs) *
            Discrete.difference (sampledProfileKernel L f) (j + 1)) := by
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (K * L - lag.natAbs),
        (1 / (L : ℝ)) *
          ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
            (((j + lag.natAbs + 1 : ℕ) : ℤ))) *
          ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
            (((j + 1 : ℕ) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < K * L - lag.natAbs := Finset.mem_range.mp hj
      have h1 : j + lag.natAbs + 1 < K * L + 1 := by omega
      have h0 : j + 1 < K * L + 1 := by omega
      have hidx : j + 1 + lag.natAbs = j + lag.natAbs + 1 := by omega
      rw [hidx]
      rw [← sampledDifferenceKernel_value_bridge L (K * L + 1) f h1 hL,
        ← sampledDifferenceKernel_value_bridge L (K * L + 1) f h0 hL]
      field_simp
    _ = (1 / (L : ℝ)) * ∑ j ∈ Finset.range (K * L - lag.natAbs),
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
          (((j + lag.natAbs + 1 : ℕ) : ℤ))) *
        ((L : ℝ) * sampledDifferenceValue L (K * L + 1) f
          (((j + 1 : ℕ) : ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring


private theorem scaled_differenceValue_shift_le
    (f : ℝ → ℝ) (K L j d : ℕ) (η δ : ℝ)
    (hL : 0 < L) (hd : d ≤ K * L) (hj : j < K * L - d)
    (_hδ : 0 < δ) (hmesh : ((d : ℝ) + 1) / (L : ℝ) < δ)
    (hf : ContDiff ℝ 1 f)
    (hmod : ∀ x ∈ Icc (0 : ℝ) K, ∀ y ∈ Icc (0 : ℝ) K,
      |x - y| < δ → |deriv f x - deriv f y| ≤ η) :
    |(L : ℝ) * sampledDifferenceValue L (K * L + 1) f
        (((j + d + 1 : ℕ) : ℤ)) -
      (L : ℝ) * sampledDifferenceValue L (K * L + 1) f
        (((j + 1 : ℕ) : ℤ))| ≤ η := by
  have hjd : j + d < K * L := by omega
  obtain ⟨c0, hc0, hc0v⟩ :=
    exists_cell_deriv_eq_scaled_difference f K L j hL (by omega) hf
  obtain ⟨c1, hc1, hc1v⟩ :=
    exists_cell_deriv_eq_scaled_difference f K L (j + d) hL hjd hf
  have hleft0 : (j : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.le_of_lt (by omega : j < K * L))
  have hright0 : ((j + 1 : ℕ) : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.succ_le_of_lt (by omega : j < K * L))
  have hleft1 : ((j + d : ℕ) : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.le_of_lt hjd)
  have hright1 : ((j + d + 1 : ℕ) : ℝ) / L ∈ Icc (0 : ℝ) K := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hL)).2
      exact_mod_cast (Nat.succ_le_of_lt hjd)
  have hc0I : c0 ∈ Icc (0 : ℝ) K :=
    ⟨le_trans hleft0.1 hc0.1.le, le_trans hc0.2.le hright0.2⟩
  have hc1I : c1 ∈ Icc (0 : ℝ) K :=
    ⟨le_trans hleft1.1 hc1.1.le, le_trans hc1.2.le hright1.2⟩
  have hright :
      ((j + d + 1 : ℕ) : ℝ) / L - (j : ℝ) / L =
        ((d : ℝ) + 1) / L := by
    rw [Nat.cast_add, Nat.cast_add]
    field_simp
    ring
  have hleft :
      ((j + 1 : ℕ) : ℝ) / L - ((j + d : ℕ) : ℝ) / L =
        (1 - (d : ℝ)) / L := by
    rw [Nat.cast_add, Nat.cast_add]
    field_simp
    ring
  have hnonnegd : (0 : ℝ) ≤ d := by positivity
  have hsmall : (1 - (d : ℝ)) / L ≤ ((d : ℝ) + 1) / L := by
    gcongr
    linarith
  have hdist : |c1 - c0| ≤ ((d : ℝ) + 1) / L := by
    rw [abs_le]
    constructor
    · linarith [hc0.2, hc1.1, hleft, hsmall]
    · linarith [hc1.2, hc0.1, hright]
  rw [sampledDifferenceValue_direct f K L (j + d) hL hjd,
    sampledDifferenceValue_direct f K L j hL (by omega : j < K * L)]
  rw [← hc1v, ← hc0v]
  exact hmod c1 hc1I c0 hc0I (lt_of_le_of_lt hdist hmesh)

private theorem abs_shifted_product_sum_sub_square_sum_le_difference
    (F : ℕ → ℝ) (m d : ℕ) (A B : ℝ)
    (hd : d ≤ m) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hF : ∀ k < m, |F k| ≤ B)
    (hshift : ∀ k < m - d, |F (k+d) - F k| ≤ A) :
    |(∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
        ∑ k ∈ Finset.range m, (F k)^2| ≤
      (m-d : ℝ)*A*B + (d:ℝ)*B^2 := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => F k ^ 2) (Nat.sub_le m d)
  have hrew :
      (∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
          ∑ k ∈ Finset.range m, (F k)^2 =
        (∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k) -
          ∑ k ∈ Finset.Ico (m-d) m, (F k)^2 := by
    rw [← hsplit]
    have hterm :
        (∑ k ∈ Finset.range (m-d), F (k+d)*F k) -
            ∑ k ∈ Finset.range (m-d), (F k)^2 =
          ∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [← hterm]
    ring
  rw [hrew]
  calc
    |(∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k) -
          ∑ k ∈ Finset.Ico (m-d) m, (F k)^2|
        ≤ |∑ k ∈ Finset.range (m-d), (F (k+d) - F k) * F k| +
          |∑ k ∈ Finset.Ico (m-d) m, (F k)^2| := abs_sub _ _
    _ ≤ (∑ k ∈ Finset.range (m-d), |(F (k+d) - F k) * F k|) +
          ∑ k ∈ Finset.Ico (m-d) m, |(F k)^2| := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ k ∈ Finset.range (m-d), A * B) +
          ∑ k ∈ Finset.Ico (m-d) m, B^2 := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        have hk' : k + d < m := by
          have hk' := Finset.mem_range.mp hk
          rw [Nat.lt_sub_iff_add_lt] at hk'
          exact hk'
        exact mul_le_mul (hshift k (Finset.mem_range.mp hk))
          (hF k (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.sub_le ..)))
          (abs_nonneg _) hA
      · apply Finset.sum_le_sum
        intro k hk
        have hk' : k < m := (Finset.mem_Ico.mp hk).2
        have habs : |F k| ≤ B := hF k hk'
        rw [← sq_abs]
        simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg (F k)) habs)
    _ = (m-d : ℝ)*A*B + (d:ℝ)*B^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      rw [Nat.card_Ico]
      have htail : m - (m - d) = d := by omega
      rw [htail]
      norm_cast
      ring

private theorem sampledDifference_lag_sub_zero_norm_le
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ) (M η δ : ℝ)
    (_hK : 0 < K) (hL : 0 < L) (hd : lag.natAbs ≤ K * L)
    (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (hM0 : 0 ≤ M) (hη0 : 0 ≤ η) (hδ : 0 < δ)
    (hmesh : ((lag.natAbs : ℝ) + 1) / (L : ℝ) < δ)
    (hM : ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M)
    (hmod : ∀ x ∈ Icc (0 : ℝ) K, ∀ y ∈ Icc (0 : ℝ) K,
      |x - y| < δ → |deriv f x - deriv f y| ≤ η) :
    ‖(L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) lag -
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0‖ ≤
      (K : ℝ) * η * M + ((lag.natAbs : ℝ) * M^2) / (L : ℝ) := by
  let d := lag.natAbs
  let m := K * L
  let A : ℕ → ℝ := fun j =>
    (L : ℝ) * sampledDifferenceValue L (m + 1) f (((j + 1 : ℕ) : ℤ))
  have hlag := difference_lag_normalization f K L lag hL hf0 hd
  have hzero := difference_zeroLag_normalization f K L hL hf0
  have hprod := abs_shifted_product_sum_sub_square_sum_le A m d η M hd hη0 hM0
    (by
      intro k hk
      dsimp [A]
      exact scaled_increment_abs_le f K L k M hL hk hf hM)
    (by
      intro k hk
      dsimp [A]
      simpa [m, Nat.cast_add, Nat.cast_one] using
        (scaled_differenceValue_shift_le f K L k d η δ hL hd hk hδ hmesh hf hmod)
    )
  have hlagA :
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) lag =
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range (m-d), A (j+d) * A j := by
    simpa only [A, m, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlag
  have hzeroA :
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0 =
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range m, A j ^ 2 := by
    simpa only [A, m, pow_two] using hzero
  rw [hlagA, hzeroA]
  have hrewrite :
      (1 / (L : ℝ)) * ∑ j ∈ Finset.range (m-d), A (j+d) * A j -
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range m, A j ^ 2 =
      (1 / (L : ℝ)) *
        ((∑ j ∈ Finset.range (m-d), A (j+d) * A j) -
          ∑ j ∈ Finset.range m, A j ^ 2) := by
    rw [← mul_sub]
  rw [hrewrite, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    (1 / (L : ℝ)) *
        |(∑ j ∈ Finset.range (m-d), A (j+d) * A j) -
          ∑ j ∈ Finset.range m, A j ^ 2| ≤
      (1 / (L : ℝ)) * ((m-d : ℝ) * η * M + (d : ℝ) * M^2) := by
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ (K : ℝ) * η * M + (d : ℝ) * M^2 / (L : ℝ) := by
      have hmd : (m - d : ℝ) ≤ (K * L : ℝ) := by
        exact_mod_cast Nat.sub_le m d
      have hfirst :
          (1 / (L : ℝ)) * ((m-d : ℝ) * η * M) ≤
            (1 / (L : ℝ)) * ((K * L : ℝ) * η * M) := by
        gcongr
      calc
        (1 / (L : ℝ)) * ((m-d : ℝ) * η * M + (d : ℝ) * M^2) ≤
            (1 / (L : ℝ)) * ((K * L : ℝ) * η * M + (d : ℝ) * M^2) := by
          gcongr
        _ = (K : ℝ) * η * M + (d : ℝ) * M^2 / (L : ℝ) := by
          field_simp

private theorem sampledDifference_lag_sub_zero_tendsto_zero
    (f : ℝ → ℝ) (K : ℕ) (lag : ℤ)
    (hK : 0 < K) (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) lag -
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0) atTop (𝓝 0) := by
  obtain ⟨hderiv, M, hM0, hM⟩ := deriv_continuous_bound f K hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (2 * ((K : ℝ) * M + 1))
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have huc : UniformContinuousOn (deriv f) (Icc (0 : ℝ) K) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hderiv
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  let d : ℝ := lag.natAbs
  have hmesh_tendsto : Tendsto (fun L : ℕ => (d + 1) / (L : ℝ)) atTop (𝓝 0) := by
    simpa [d, div_eq_mul_inv] using
      ((tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))))
  have hboundary_tendsto :
      Tendsto (fun L : ℕ => d * M^2 / (L : ℝ)) atTop (𝓝 0) := by
    simpa [d, div_eq_mul_inv] using
      ((tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))))
  filter_upwards [eventually_gt_atTop 0,
    eventually_natAbs_le_mul K lag hK,
    hmesh_tendsto.eventually (Iio_mem_nhds hδ),
    hboundary_tendsto.eventually (Iio_mem_nhds (show 0 < ε / 2 by linarith))] with
    L hL hdl hmesh hboundary
  have hbound := sampledDifference_lag_sub_zero_norm_le f K L lag M η δ
    hK hL hdl hf hf0 hM0 hη.le hδ hmesh
    hM (fun x hx y hy hxy => (hmod x hx y hy hxy).le)
  have hfirst : (K : ℝ) * η * M ≤ ε / 2 := by
    dsimp [η]
    have hden : 0 < 2 * ((K : ℝ) * M + 1) := by positivity
    have hnum : (K : ℝ) * M ≤ (K : ℝ) * M + 1 := by linarith
    calc
      (K : ℝ) * (ε / (2 * ((K : ℝ) * M + 1))) * M =
          (ε / (2 * ((K : ℝ) * M + 1))) * ((K : ℝ) * M) := by ring
      _ ≤ (ε / (2 * ((K : ℝ) * M + 1))) * ((K : ℝ) * M + 1) := by
        exact mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = ε / 2 := by field_simp
  have hdist : dist
      ((L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) lag -
        (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) 0) 0 < ε := by
    rw [Real.dist_eq]
    have hnorm : ‖
        (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
            (Discrete.difference (sampledProfileKernel L f)) lag -
          (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
            (Discrete.difference (sampledProfileKernel L f)) 0‖ < ε := by
      exact lt_of_le_of_lt hbound (by linarith)
    simpa [Real.norm_eq_abs] using hnorm
  exact hdist

theorem tendsto_sampledDifference_lagInnerProductCutoff_scaled
    (f : ℝ → ℝ) (K : ℕ) (lag : ℤ)
    (hK : 0 < K) (hf : ContDiff ℝ 1 f)
    (hf0 : f 0 = 0) (_hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
        (Discrete.difference (sampledProfileKernel L f)) lag) atTop
      (𝓝 (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2)) := by
  have herr := sampledDifference_lag_sub_zero_tendsto_zero f K lag hK hf hf0
  have hzero := tendsto_sampledDifference_zeroLagInnerProductCutoff_scaled
    f K hK hf hf0
  have hadd := herr.add hzero
  simpa [sub_add_cancel] using hadd

theorem lagInnerProductCutoff_zero_nonneg (N : ℕ) (w : Discrete.Kernel) :
    0 ≤ lagInnerProductCutoff N w (0 : ℤ) := by
  have h := lagInnerProductCutoff_natCast_eq_shifted N w 0 (Nat.zero_le N)
  have h' : lagInnerProductCutoff N w (0 : ℤ) =
      ∑ k ∈ Finset.range N, (w k)^2 := by
    simpa [pow_two] using h
  change 0 ≤ lagInnerProductCutoff N w (0 : ℤ)
  rw [h']
  positivity

private theorem shifted_lag_abs_le_square_sum
    (N d : ℕ) (w : Discrete.Kernel) (_hd : d ≤ N) :
    |∑ k ∈ Finset.range (N - d), w (k+d) * w k| ≤
      ∑ k ∈ Finset.range N, (w k)^2 := by
  let A : ℝ := ∑ k ∈ Finset.range N, (w k)^2
  have hA : 0 ≤ A := by positivity
  have h₁ : (∑ k ∈ Finset.range (N-d), (w (k+d))^2) ≤ A := by
    have heq : (∑ k ∈ Finset.range (N-d), (w (k+d))^2) =
        ∑ k ∈ Finset.Ico d N, (w k)^2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      rw [Nat.add_comm]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    · intro k hk _; positivity
  have h₂ : (∑ k ∈ Finset.range (N-d), (w k)^2) ≤ A := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.sub_le ..))
    · intro k hk _; positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N-d))
    (fun k => w (k+d)) (fun k => w k)
  have hs : (∑ k ∈ Finset.range (N-d), w (k+d) * w k)^2 ≤ A^2 := by
    calc
      _ ≤ (∑ k ∈ Finset.range (N-d), (w (k+d))^2) *
          (∑ k ∈ Finset.range (N-d), (w k)^2) := hcs
      _ ≤ A * A := by exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = A^2 := by ring
  exact abs_le_of_sq_le_sq hs hA

private theorem lagInnerProductCutoff_zero_eq_square_sum (N : ℕ) (w : Discrete.Kernel) :
    lagInnerProductCutoff N w (0 : ℤ) = ∑ k ∈ Finset.range N, (w k)^2 := by
  have h := lagInnerProductCutoff_natCast_eq_shifted N w 0 (Nat.zero_le N)
  simpa [pow_two] using h

theorem abs_lagInnerProductCutoff_le_zero
    (N : ℕ) (w : Discrete.Kernel) (lag : ℤ) :
    |lagInnerProductCutoff N w lag| ≤ lagInnerProductCutoff N w 0 := by
  by_cases h : lag.natAbs ≤ N
  · rw [lagInnerProductCutoff_eq_shifted_natAbs N w lag h]
    rw [lagInnerProductCutoff_zero_eq_square_sum]
    split_ifs with hp
    · exact shifted_lag_abs_le_square_sum N lag.natAbs w h
    · have hc : (∑ k ∈ Finset.range (N-lag.natAbs),
          w k * w (k+lag.natAbs)) =
        ∑ k ∈ Finset.range (N-lag.natAbs), w (k+lag.natAbs) * w k := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hc]
      exact shifted_lag_abs_le_square_sum N lag.natAbs w h
  · have hn : lag ∉ finiteLagSet N := by
      intro hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, heq⟩
      have h1 := Finset.mem_range.mp (Finset.mem_product.mp hp).1
      have h2 := Finset.mem_range.mp (Finset.mem_product.mp hp).2
      have hc : |lag| ≤ (N : ℤ) := by
        rw [← heq]
        omega
      have hc' : (lag.natAbs : ℤ) ≤ (N : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hc
      have h' : lag.natAbs ≤ N := by exact_mod_cast hc'
      exact h h'
    rw [lagInnerProductCutoff_eq_zero_of_not_mem_finiteLagSet N w hn]
    simp only [abs_zero]
    rw [lagInnerProductCutoff_zero_eq_square_sum]
    positivity

theorem tsum_mul_lagInnerProductCutoff_eq_finiteLagCovarianceGrouped
    (γ : ℤ → ℝ) (N : ℕ) (w : Discrete.Kernel) :
    (∑' lag : ℤ, γ lag * lagInnerProductCutoff N w lag) =
      finiteLagCovarianceGrouped γ N w := by
  unfold finiteLagCovarianceGrouped
  apply (tsum_eq_sum (s := finiteLagSet N) ?_).trans
  · rfl
  · intro lag hlag
    rw [lagInnerProductCutoff_eq_zero_of_not_mem_finiteLagSet N w hlag, mul_zero]

theorem abs_sampledProfile_lagInnerProductCutoff_scaled_le_zero
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ) :
    |(L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
      (sampledProfileKernel L f) lag| ≤
    (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
      (sampledProfileKernel L f) 0 := by
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (abs_lagInnerProductCutoff_le_zero _ _ _) (by positivity)

theorem abs_sampledDifference_lagInnerProductCutoff_scaled_le_zero
    (f : ℝ → ℝ) (K L : ℕ) (lag : ℤ) :
    |(L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) lag| ≤
    (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) 0 := by
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (abs_lagInnerProductCutoff_le_zero _ _ _) (by positivity)

private theorem weighted_tsum_tendsto {a : ℤ → ℝ} {u : ℕ → ℤ → ℝ} {v : ℤ → ℝ}
    (ha : Summable (fun lag => |a lag|))
    (hu : ∀ lag, Tendsto (fun n => u n lag) atTop (𝓝 (v lag)))
    (C : ℝ) (_hC : 0 ≤ C)
    (hdom : ∀ᶠ n in atTop, ∀ lag, |u n lag| ≤ C) :
    Tendsto (fun n => ∑' lag, a lag * u n lag) atTop
      (𝓝 (∑' lag, a lag * v lag)) := by
  let bound : ℤ → ℝ := fun lag => |a lag| * C
  have hbound : Summable bound := ha.mul_right C
  apply tendsto_tsum_of_dominated_convergence hbound
  · intro lag
    simpa [Real.norm_eq_abs, abs_mul] using (tendsto_const_nhds.mul (hu lag))
  · filter_upwards [hdom] with n hn lag
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hn lag) (abs_nonneg _)

private theorem eventually_abs_bound {x : ℕ → ℝ} {c : ℝ} (hx : Tendsto x atTop (𝓝 c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, |x n| ≤ C := by
  refine ⟨|c| + 1, by positivity, ?_⟩
  have h := (tendsto_norm.comp hx).eventually
    (eventually_lt_nhds (show ‖c‖ < ‖c‖ + 1 by linarith))
  filter_upwards [h] with n hn
  exact le_of_lt (by simpa [Real.norm_eq_abs] using hn)

theorem tendsto_tsum_sampledProfile_lagInnerProductCutoff_scaled
    (γ : ℤ → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (hγ : Summable (fun lag : ℤ => |γ lag|))
    (hK : 0 < K) (hf : ContDiff ℝ 1 f) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ => ∑' lag : ℤ,
      γ lag * ((L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
        (sampledProfileKernel L f) lag)) atTop
      (𝓝 ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2))) := by
  let I : ℝ := ∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2
  let u : ℕ → ℤ → ℝ := fun L lag =>
    (L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
      (sampledProfileKernel L f) lag
  have hu : ∀ lag, Tendsto (fun L => u L lag) atTop (𝓝 I) := by
    intro lag
    exact tendsto_sampledProfile_lagInnerProductCutoff_scaled f K lag hK hf hfK
  obtain ⟨C, hC, hCevent⟩ := eventually_abs_bound (hu 0)
  have hdom : ∀ᶠ L : ℕ in atTop, ∀ lag, |u L lag| ≤ C := by
    filter_upwards [hCevent, eventually_gt_atTop 0] with L hL0 hL
    intro lag
    have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    calc
      |u L lag| = (L : ℝ) * |lagInnerProductCutoff
          (sampledProfileHorizon K L) (sampledProfileKernel L f) lag| := by
        simp [u, abs_mul, abs_of_pos hLr]
      _ ≤ (L : ℝ) * lagInnerProductCutoff
          (sampledProfileHorizon K L) (sampledProfileKernel L f) 0 :=
        mul_le_mul_of_nonneg_left
          (abs_lagInnerProductCutoff_le_zero _ _ _) (by positivity)
      _ = |u L 0| := by
        simp [u, abs_mul, abs_of_pos hLr,
          abs_of_nonneg (lagInnerProductCutoff_zero_nonneg _ _)]
      _ ≤ C := hL0
  have h := weighted_tsum_tendsto hγ hu C hC hdom
  simpa [u, I, tsum_mul_right] using h

theorem tendsto_tsum_sampledDifference_lagInnerProductCutoff_scaled
    (γ : ℤ → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (hγ : Summable (fun lag : ℤ => |γ lag|))
    (hK : 0 < K) (hf : ContDiff ℝ 1 f)
    (hf0 : f 0 = 0) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ => ∑' lag : ℤ,
      γ lag * ((L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
        (Discrete.difference (sampledProfileKernel L f)) lag)) atTop
      (𝓝 ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x) ^ 2))) := by
  let I : ℝ := ∫ x in (0 : ℝ)..(K : ℝ), (deriv f x) ^ 2
  let u : ℕ → ℤ → ℝ := fun L lag =>
    (L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f)) lag
  have hu : ∀ lag, Tendsto (fun L => u L lag) atTop (𝓝 I) := by
    intro lag
    exact tendsto_sampledDifference_lagInnerProductCutoff_scaled
      f K lag hK hf hf0 hfK
  obtain ⟨C, hC, hCevent⟩ := eventually_abs_bound (hu 0)
  have hdom : ∀ᶠ L : ℕ in atTop, ∀ lag, |u L lag| ≤ C := by
    filter_upwards [hCevent, eventually_gt_atTop 0] with L hL0 hL
    intro lag
    have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    calc
      |u L lag| = (L : ℝ)^3 * |lagInnerProductCutoff
          (sampledProfileHorizon K L)
            (Discrete.difference (sampledProfileKernel L f)) lag| := by
        simp [u, abs_mul, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ (L : ℝ)^3)]
      _ ≤ (L : ℝ)^3 * lagInnerProductCutoff
          (sampledProfileHorizon K L)
            (Discrete.difference (sampledProfileKernel L f)) 0 :=
        mul_le_mul_of_nonneg_left
          (abs_lagInnerProductCutoff_le_zero _ _ _) (by positivity)
      _ = |u L 0| := by
        simp [u, abs_mul, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ (L : ℝ)^3),
          abs_of_nonneg (lagInnerProductCutoff_zero_nonneg _ _)]
      _ ≤ C := hL0
  have h := weighted_tsum_tendsto hγ hu C hC hdom
  simpa [u, I, tsum_mul_right] using h

theorem tendsto_sampledProfile_toeplitz_finiteCovarianceForm_scaled
    (γ : ℤ → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (hγ : Summable (fun lag : ℤ => |γ lag|))
    (hK : 0 < K) (hf : ContDiff ℝ 1 f) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ) * finiteCovarianceForm (toeplitzCovariance γ)
        (sampledProfileHorizon K L) (sampledProfileKernel L f)) atTop
      (𝓝 ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2))) := by
  have hts := tendsto_tsum_sampledProfile_lagInnerProductCutoff_scaled
    γ f K hγ hK hf hfK
  have heq : ∀ L : ℕ,
      (L : ℝ) * finiteCovarianceForm (toeplitzCovariance γ)
          (sampledProfileHorizon K L) (sampledProfileKernel L f) =
        ∑' lag : ℤ, γ lag *
          ((L : ℝ) * lagInnerProductCutoff (sampledProfileHorizon K L)
            (sampledProfileKernel L f) lag) := by
    intro L
    rw [← finiteLagCovarianceGrouped_eq_covarianceForm]
    rw [← tsum_mul_lagInnerProductCutoff_eq_finiteLagCovarianceGrouped]
    rw [← tsum_mul_left]
    congr 1
    funext lag
    ring
  exact hts.congr' (Filter.Eventually.of_forall (fun L => (heq L).symm))

theorem tendsto_sampledDifference_toeplitz_finiteCovarianceForm_scaled
    (γ : ℤ → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (hγ : Summable (fun lag : ℤ => |γ lag|))
    (hK : 0 < K) (hf : ContDiff ℝ 1 f)
    (hf0 : f 0 = 0) (hfK : f (K : ℝ) = 0) :
    Tendsto (fun L : ℕ =>
      (L : ℝ)^3 * finiteCovarianceForm (toeplitzCovariance γ)
        (sampledProfileHorizon K L)
        (Discrete.difference (sampledProfileKernel L f))) atTop
      (𝓝 ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2))) := by
  have hts := tendsto_tsum_sampledDifference_lagInnerProductCutoff_scaled
    γ f K hγ hK hf hf0 hfK
  have heq : ∀ L : ℕ,
      (L : ℝ)^3 * finiteCovarianceForm (toeplitzCovariance γ)
          (sampledProfileHorizon K L)
          (Discrete.difference (sampledProfileKernel L f)) =
        ∑' lag : ℤ, γ lag *
          ((L : ℝ)^3 * lagInnerProductCutoff (sampledProfileHorizon K L)
            (Discrete.difference (sampledProfileKernel L f)) lag) := by
    intro L
    rw [← finiteLagCovarianceGrouped_eq_covarianceForm]
    rw [← tsum_mul_lagInnerProductCutoff_eq_finiteLagCovarianceGrouped]
    rw [← tsum_mul_left]
    congr 1
    funext lag
    ring
  exact hts.congr' (Filter.Eventually.of_forall (fun L => (heq L).symm))

private theorem sampledProfileKernel_endpoint_zero
    (f : ℝ → ℝ) (K L : ℕ) (hL : 0 < L) (hfK : f (K : ℝ) = 0) :
    sampledProfileKernel L f (K * L) = 0 := by
  simp [sampledProfileKernel, Nat.cast_mul, hL.ne', hfK]

private theorem finiteCovarianceForm_succ_of_eq_zero
    (Γ : ℕ → ℕ → ℝ) (N : ℕ) (w : Discrete.Kernel) (hw : w N = 0) :
    finiteCovarianceForm Γ (N + 1) w = finiteCovarianceForm Γ N w := by
  unfold finiteCovarianceForm
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [Finset.sum_range_succ, hw]

theorem tendsto_sampledProfile_finiteGeneralizedRayleighQuotient_scaled
    (γ : ℤ → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (hγ : Summable (fun lag : ℤ => |γ lag|))
    (hΓ : 0 < ∑' lag : ℤ, γ lag)
    (hK : 0 < K) (hf : ContDiff ℝ 1 f)
    (hf0 : f 0 = 0) (hfK : f (K : ℝ) = 0)
    (hden : 0 < ∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2) :
    Tendsto (fun L : ℕ =>
      (L : ℝ)^2 * finiteGeneralizedRayleighQuotient
        (toeplitzCovariance γ) (K * L) (sampledProfileKernel L f)) atTop
      (𝓝 ((∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2) /
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2))) := by
  let A : ℕ → ℝ := fun L =>
    (L : ℝ)^3 * finiteCovarianceForm (toeplitzCovariance γ)
      (sampledProfileHorizon K L)
      (Discrete.difference (sampledProfileKernel L f))
  let B : ℕ → ℝ := fun L =>
    (L : ℝ) * finiteCovarianceForm (toeplitzCovariance γ)
      (K * L) (sampledProfileKernel L f)
  have hA : Tendsto A atTop (𝓝 ((∑' lag : ℤ, γ lag) *
      (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2))) := by
    simpa [A] using tendsto_sampledDifference_toeplitz_finiteCovarianceForm_scaled
      γ f K hγ hK hf hf0 hfK
  have hB : Tendsto B atTop (𝓝 ((∑' lag : ℤ, γ lag) *
      (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2))) := by
    have h := tendsto_sampledProfile_toeplitz_finiteCovarianceForm_scaled
      γ f K hγ hK hf hfK
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    dsimp [B]
    rw [show sampledProfileHorizon K L = K * L + 1 by rfl]
    rw [finiteCovarianceForm_succ_of_eq_zero]
    exact sampledProfileKernel_endpoint_zero f K L hL hfK
  have hBpos : 0 < (∑' lag : ℤ, γ lag) *
      (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2) := mul_pos hΓ hden
  have hquot : Tendsto (fun L => A L / B L) atTop
      (𝓝 (((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2)) /
        ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2)))) :=
    hA.div hB (ne_of_gt hBpos)
  have hcancel :
      ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2)) /
        ((∑' lag : ℤ, γ lag) *
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2)) =
      (∫ x in (0 : ℝ)..(K : ℝ), (deriv f x)^2) /
        (∫ x in (0 : ℝ)..(K : ℝ), f x ^ 2) := by
    field_simp [ne_of_gt hΓ, ne_of_gt hden]
  rw [hcancel] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  dsimp [A, B, finiteGeneralizedRayleighQuotient]
  change (L : ℝ)^3 *
      (finiteCovarianceForm (toeplitzCovariance γ) (K * L + 1)
        (Discrete.difference (sampledProfileKernel L f))) /
      ((L : ℝ) * finiteCovarianceForm (toeplitzCovariance γ) (K * L)
        (sampledProfileKernel L f)) = _
  field_simp

end RayleighKernel.Probability
