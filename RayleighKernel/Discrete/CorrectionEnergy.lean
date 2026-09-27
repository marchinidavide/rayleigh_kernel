import RayleighKernel.Discrete.CorrectionBumps
import RayleighKernel.Discrete.OptimizerEnergy

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open scoped BigOperators
open RayleighKernel.Analysis.HalfLineH1


def optimizerSampledCorrection (L : ℝ) (hL : 0 < L) (h : ℝ) : Kernel :=
  fun j => optimizerCorrectionLeft L hL h * sampledKernel h (optimizerBumpLeft L hL) j +
    optimizerCorrectionRight L hL h * sampledKernel h (optimizerBumpRight L hL) j

theorem correctedSampledOptimizer_eq (L : ℝ) (hL : 0 < L) (h : ℝ) :
    correctedSampledOptimizer L hL h = sampledKernel h (optimizerProfile L) +
      optimizerSampledCorrection L hL h := by
  funext j
  simp [correctedSampledOptimizer, optimizerSampledCorrection, sampledKernel_apply]
  ring

theorem optimizerSampledCorrection_tail (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    {j : ℕ} (hj : meshCount (optimizerSupport L) h < j) :
    optimizerSampledCorrection L hL h j = 0 := by
  simp only [optimizerSampledCorrection]
  have hl := sampledKernel_tail hh (optimizerSupport_pos hL).le
    (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL
      ((optimizerBumpHorizon_lt_support L hL).le.trans hx)) hj
  have hr := sampledKernel_tail hh (optimizerSupport_pos hL).le
    (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL
      ((optimizerBumpHorizon_lt_support L hL).le.trans hx)) hj
  rw [hl, hr, mul_zero, mul_zero, add_zero]

theorem correctedSampledOptimizer_tail (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    {j : ℕ} (hj : meshCount (optimizerSupport L) h < j) :
    correctedSampledOptimizer L hL h j = 0 := by
  rw [correctedSampledOptimizer_eq]
  simp only [Pi.add_apply]
  rw [sampledKernel_tail hh (optimizerSupport_pos hL).le
      (fun x hx => optimizerProfile_eq_zero_of_support_le hL hx) hj,
    optimizerSampledCorrection_tail L hL hh hj]
  simp

theorem summable_optimizerSampledCorrection (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h) :
    Summable (optimizerSampledCorrection L hL h) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  exact optimizerSampledCorrection_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj))

theorem summable_abs_optimizerSampledCorrection (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h) :
    Summable (fun j => |optimizerSampledCorrection L hL h j|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [optimizerSampledCorrection_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), abs_zero]

theorem summable_sq_optimizerSampledCorrection (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h) :
    Summable (fun j => (optimizerSampledCorrection L hL h j)^2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [optimizerSampledCorrection_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), zero_pow]
  norm_num

theorem summable_firstMoment_optimizerSampledCorrection (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => (j : ℝ) * optimizerSampledCorrection L hL h j) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [optimizerSampledCorrection_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), mul_zero]

theorem summable_difference_sq_optimizerSampledCorrection (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j => (difference (optimizerSampledCorrection L hL h) j)^2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 2))
  intro j hj
  cases j with
  | zero => exact False.elim (hj (by simp))
  | succ k =>
    have hk : meshCount (optimizerSupport L) h < k := by
      have hk' : meshCount (optimizerSupport L) h + 2 ≤ k + 1 :=
        Nat.succ_le_iff.mpr (by simpa using hj)
      omega
    rw [difference_succ,
      optimizerSampledCorrection_tail L hL hh (by omega),
      optimizerSampledCorrection_tail L hL hh hk]
    simp

theorem summable_abs_correctedSampledOptimizer (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j => |correctedSampledOptimizer L hL h j|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [correctedSampledOptimizer_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), abs_zero]

theorem summable_sq_correctedSampledOptimizer (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j => (correctedSampledOptimizer L hL h j)^2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [correctedSampledOptimizer_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), zero_pow]
  norm_num

theorem summable_firstMoment_correctedSampledOptimizer (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => (j : ℝ) * correctedSampledOptimizer L hL h j) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 1))
  intro j hj
  rw [correctedSampledOptimizer_tail L hL hh (Nat.lt_of_not_ge (by simpa using hj)), mul_zero]

theorem summable_difference_sq_correctedSampledOptimizer (L : ℝ) (hL : 0 < L)
    {h : ℝ} (hh : 0 < h) :
    Summable (fun j => (difference (correctedSampledOptimizer L hL h) j)^2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount (optimizerSupport L) h + 2))
  intro j hj
  cases j with
  | zero => exact False.elim (hj (by simp))
  | succ k =>
    have hk : meshCount (optimizerSupport L) h < k := by
      have hk' : meshCount (optimizerSupport L) h + 2 ≤ k + 1 :=
        Nat.succ_le_iff.mpr (by simpa using hj)
      omega
    rw [difference_succ,
      correctedSampledOptimizer_tail L hL hh (by omega),
      correctedSampledOptimizer_tail L hL hh hk]
    simp

theorem exists_pos_correctedSampledOptimizer_isAdmissible (L : ℝ) (hL : 0 < L) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      IsAdmissible h L (correctedSampledOptimizer L hL h) := by
  obtain ⟨h₀, hh₀, hc⟩ := exists_pos_correctedSampledOptimizer_constraints_nonnegative L hL
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hh₀
  have he := hc hh hh₀
  refine ⟨hh, he.2.2, ?_, ?_, ?_, ?_, he.1, he.2.1⟩
  · exact summable_abs_correctedSampledOptimizer L hL hh
  · exact summable_sq_correctedSampledOptimizer L hL hh
  · exact summable_difference_sq_correctedSampledOptimizer L hL hh
  · exact summable_firstMoment_correctedSampledOptimizer L hL hh

private theorem exists_correction_value_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : Continuous f) (hK : 0 < K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) K, |f x| ≤ B := by
  let g : ℝ → ℝ := fun x => |f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) := hf.continuousOn.abs
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (g 0)) (hB 0 ⟨le_rfl, hK.le⟩)
  refine ⟨B, hB0, ?_⟩
  intro x hx
  simpa [g, Real.norm_eq_abs] using hB x hx

private theorem sampled_correction_square_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : Continuous f) (hK : 0 < K) (hzero : ∀ x, K ≤ x → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      squareEnergy (sampledKernel h f) ≤ h * C := by
  obtain ⟨B, hB, hBb⟩ := exists_correction_value_bound hf hK
  refine ⟨(K + 1) * B ^ 2, by positivity, ?_⟩
  intro h hh hh1
  rw [squareEnergy_sampledKernel hh hK.le hzero]
  have hn := meshCount_mul_le hh hK.le
  have hc : h * ((meshCount K h : ℝ) + 1) ≤ K + 1 := by nlinarith
  have hs : (∑ j ∈ Finset.range (meshCount K h + 1),
      f ((j : ℝ) * h) ^ 2) ≤ (meshCount K h + 1 : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (meshCount K h + 1), B ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ meshCount K h := Nat.le_of_lt_succ (by simpa using hj)
        have hx : (j : ℝ) * h ∈ Icc (0 : ℝ) K :=
          ⟨by positivity, (mul_le_mul_of_nonneg_right (by exact_mod_cast hj') hh.le).trans hn⟩
        have hbb := hBb _ hx
        have hbb' : |f ((j : ℝ) * h)| ≤ |B| := by simpa [abs_of_nonneg hB] using hbb
        simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hbb'
      _ = _ := by simp
  have hpow := mul_le_mul_of_nonneg_left hs (sq_nonneg h)
  have hscale := mul_le_mul_of_nonneg_right hc (sq_nonneg B)
  nlinarith [hpow, hscale]

theorem exists_sampledOptimizerBumpLeft_squareEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      Discrete.squareEnergy (sampledKernel h (optimizerBumpLeft L hL)) ≤ h * C :=
  sampled_correction_square_bound (contDiff_optimizerBumpLeft L hL).continuous
    (optimizerBumpHorizon_pos L hL) (fun _ hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)

theorem exists_sampledOptimizerBumpRight_squareEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      Discrete.squareEnergy (sampledKernel h (optimizerBumpRight L hL)) ≤ h * C :=
  sampled_correction_square_bound (contDiff_optimizerBumpRight L hL).continuous
    (optimizerBumpHorizon_pos L hL) (fun _ hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)

private theorem correction_deriv_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M := by
  let g : ℝ → ℝ := fun x => |deriv f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) := by
    simpa [g, iteratedDeriv_one] using
      (hf.continuous_iteratedDeriv 1 (by norm_num)).continuousOn.abs
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_rfl, hK.le⟩)
  refine ⟨M, hM0, ?_⟩
  intro x hx
  simpa [g, iteratedDeriv_one, Real.norm_eq_abs] using hM x hx

private theorem sampled_correction_difference_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K)
    (hleft : ∀ x, x ≤ 0 → f x = 0)
    (hright : ∀ x, K ≤ x → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      differenceEnergy (sampledKernel h f) ≤ h ^ 3 * C := by
  obtain ⟨M, hM, hMb⟩ := correction_deriv_bound hf hK
  refine ⟨(K + 1) * M ^ 2, by positivity, ?_⟩
  intro h hh hh1
  rw [differenceEnergy_sampledKernel hh hK.le hright]
  have hN := meshCount_mul_le hh hK.le
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hsum : ∀ j ∈ Finset.range (meshCount K h),
      |f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)| ≤ M * h := by
    intro j hj
    have hjN : j + 1 ≤ meshCount K h := Nat.succ_le_iff.mpr (by simpa using hj)
    have ha : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h := by
      rw [Nat.cast_add, Nat.cast_one, add_mul]
      nlinarith [hh.le]
    have hb : ((j + 1 : ℕ) : ℝ) * h ≤ K := by
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) hh.le).trans hN
    have H := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
      (fun x _ => (hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt)
      (fun x hx => by
        have hx0 : (0 : ℝ) ≤ x := by nlinarith [ha, hx.1]
        simpa [Real.norm_eq_abs] using hMb x ⟨hx0, hx.2.le.trans hb⟩)
      (((j + 1 : ℕ) : ℝ) * h) ⟨ha, le_rfl⟩
    simpa [Nat.cast_add, add_mul] using H
  have hterm : |f ((meshCount K h : ℝ) * h)| ≤ M * h := by
    have H := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
      (fun x _ => (hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt)
      (fun x hx => by
        have hx0 : (0 : ℝ) ≤ x := by nlinarith [hN0, hx.1]
        simpa [Real.norm_eq_abs] using hMb x ⟨hx0, hx.2.le⟩)
      K ⟨hN, le_rfl⟩
    rw [hright K le_rfl] at H
    have hrem := meshCount_mul_add_remainder hh hK.le
    have hr := meshRemainder_le hh hK.le
    simpa [Real.norm_eq_abs, abs_neg] using H.trans (by nlinarith)
  have hbound : (∑ j ∈ Finset.range (meshCount K h),
      (f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) ^ 2) +
      f ((meshCount K h : ℝ) * h) ^ 2 ≤
      (meshCount K h + 1 : ℝ) * (M * h) ^ 2 := by
    have hi : (∑ j ∈ Finset.range (meshCount K h),
        (f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) ^ 2) ≤
        ∑ j ∈ Finset.range (meshCount K h), (M * h) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have habs : |f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)| ≤ |M*h| := by
        rw [abs_of_nonneg (mul_nonneg hM hh.le)]
        exact hsum j hj
      simpa [sq_abs] using sq_le_sq.mpr habs
    have ht : f ((meshCount K h : ℝ) * h)^2 ≤ (M*h)^2 := by
      have habs : |f ((meshCount K h : ℝ) * h)| ≤ |M*h| := by
        rw [abs_of_nonneg (mul_nonneg hM hh.le)]
        exact hterm
      simpa [sq_abs] using sq_le_sq.mpr habs
    have hconst : (∑ j ∈ Finset.range (meshCount K h), (M * h) ^ 2) =
        (meshCount K h : ℝ) * (M * h) ^ 2 := by simp
    calc
      _ ≤ (meshCount K h : ℝ) * (M*h)^2 + (M*h)^2 := by nlinarith [hi, ht, hconst]
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hbound (sq_nonneg h)
  have hcount : h * ((meshCount K h : ℝ) + 1) ≤ K + 1 := by nlinarith
  have hcoef := mul_le_mul_of_nonneg_right hcount (sq_nonneg M)
  have hmain : h ^ 2 * ((meshCount K h + 1 : ℝ) * (M*h)^2) ≤
      h ^ 3 * ((K+1)*M^2) := by
    calc
      h ^ 2 * ((meshCount K h + 1 : ℝ) * (M*h)^2) =
          (h * ((meshCount K h : ℝ) + 1) * M^2) * h^3 := by ring
      _ ≤ ((K+1)*M^2) * h^3 := by
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = h ^ 3 * ((K+1)*M^2) := by ring
  simp only [hleft 0 le_rfl]
  nlinarith [hscaled, hmain]

theorem exists_sampledOptimizerBumpLeft_differenceEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      Discrete.differenceEnergy (sampledKernel h (optimizerBumpLeft L hL)) ≤ h ^ 3 * C :=
  sampled_correction_difference_bound (contDiff_optimizerBumpLeft L hL)
    (optimizerBumpHorizon_pos L hL)
    (fun _ hx => by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact (not_lt_of_ge hx) (tsupport_optimizerBumpLeft L hL hs).1)
    (fun _ hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)

theorem exists_sampledOptimizerBumpRight_differenceEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      Discrete.differenceEnergy (sampledKernel h (optimizerBumpRight L hL)) ≤ h ^ 3 * C :=
  sampled_correction_difference_bound (contDiff_optimizerBumpRight L hL)
    (optimizerBumpHorizon_pos L hL)
    (fun _ hx => by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact (not_lt_of_ge hx) (tsupport_optimizerBumpRight L hL hs).1)
     (fun _ hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)

private theorem difference_linear (a b : ℝ) (u v : Kernel) :
    difference (fun j => a * u j + b * v j) =
      fun j => a * difference u j + b * difference v j := by
  funext j
  cases j with
  | zero => simp [difference]
  | succ j => simp [difference]; ring

private theorem energy_linear {a b : ℝ} {u v : Kernel}
    (hu : Summable (fun j => (u j)^2)) (hv : Summable (fun j => (v j)^2)) :
    squareEnergy (fun j => a*u j + b*v j) ≤
      2*a^2*squareEnergy u + 2*b^2*squareEnergy v := by
  have hp : Summable (fun j : ℕ => 2*a^2*(u j)^2 + 2*b^2*(v j)^2) :=
    (hu.mul_left (2*a^2)).add (hv.mul_left (2*b^2))
  have hs : Summable (fun j : ℕ => (a*u j + b*v j)^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun j => by nlinarith [sq_nonneg (a*u j-b*v j)]) hp
  rw [squareEnergy]
  let p : ℕ → ℝ := fun j => 2*a^2*(u j)^2 + 2*b^2*(v j)^2
  calc
    _ ≤ ∑' j : ℕ, p j := by
      have hp' : Summable p := by simpa [p] using hp
      apply hs.tsum_le_tsum
      intro j
      dsimp [p]
      nlinarith [sq_nonneg (a*u j-b*v j)]
      exact hp'
    _ = _ := by
      dsimp [p]
      rw [Summable.tsum_add (hu.mul_left (2*a^2)) (hv.mul_left (2*b^2))]
      simp only [tsum_mul_left, squareEnergy]

private theorem difference_energy_linear {a b : ℝ} {u v : Kernel}
    (hu : Summable (fun j => (difference u j)^2))
    (hv : Summable (fun j => (difference v j)^2)) :
    differenceEnergy (fun j => a*u j + b*v j) ≤
      2*a^2*differenceEnergy u + 2*b^2*differenceEnergy v := by
  change squareEnergy (difference (fun j => a*u j + b*v j)) ≤ _
  rw [difference_linear]
  exact energy_linear hu hv

private theorem coeff_sq {a b h C : ℝ} (hC : 0 ≤ C)
    (hb : |a| + |b| ≤ h^2*C) : a^2 ≤ h^4*C^2 ∧ b^2 ≤ h^4*C^2 := by
  have ha : |a| ≤ h^2*C := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb
  have hbb : |b| ≤ h^2*C := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hb
  constructor
  · have hsq := (sq_le_sq₀ (abs_nonneg a) (by positivity)).2 ha
    calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      _ ≤ (h ^ 2 * C) ^ 2 := hsq
      _ = h ^ 4 * C ^ 2 := by ring_nf
  · have hsq := (sq_le_sq₀ (abs_nonneg b) (by positivity)).2 hbb
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ (h ^ 2 * C) ^ 2 := hsq
      _ = h ^ 4 * C ^ 2 := by ring_nf

theorem exists_optimizerSampledCorrection_squareEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      squareEnergy (optimizerSampledCorrection L hL h) ≤ h ^ 5 * C := by
  obtain ⟨hc,Cc,hcp,hCc,hcb⟩ := exists_optimizerCorrection_abs_sum_bound L hL
  obtain ⟨Cl,hCl,hLb⟩ := exists_sampledOptimizerBumpLeft_squareEnergy_bound L hL
  obtain ⟨Cr,hCr,hRb⟩ := exists_sampledOptimizerBumpRight_squareEnergy_bound L hL
  let C := 2*Cc^2*(Cl+Cr)
  refine ⟨min hc 1,C,lt_min hcp (by norm_num),by positivity,?_⟩
  intro h hh hh0
  have hh1 : h ≤ 1 := le_trans hh0 (min_le_right _ _)
  obtain ⟨ha,hb⟩ := coeff_sq hCc (hcb hh (le_trans hh0 (min_le_left _ _)))
  have hs := energy_linear
    (a := optimizerCorrectionLeft L hL h) (b := optimizerCorrectionRight L hL h)
    (u := sampledKernel h (optimizerBumpLeft L hL)) (v := sampledKernel h (optimizerBumpRight L hL))
    (sampledKernel_square_summable hh (optimizerBumpHorizon_pos L hL).le
      (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx))
    (sampledKernel_square_summable hh (optimizerBumpHorizon_pos L hL).le
      (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx))
  change squareEnergy (fun j => optimizerCorrectionLeft L hL h *
    sampledKernel h (optimizerBumpLeft L hL) j + optimizerCorrectionRight L hL h *
    sampledKernel h (optimizerBumpRight L hL) j) ≤ _
  calc
    _ ≤ 2*optimizerCorrectionLeft L hL h^2*(h*Cl) +
        2*optimizerCorrectionRight L hL h^2*(h*Cr) := by
      calc _ ≤ 2*optimizerCorrectionLeft L hL h^2*squareEnergy
            (sampledKernel h (optimizerBumpLeft L hL)) +
            2*optimizerCorrectionRight L hL h^2*squareEnergy
            (sampledKernel h (optimizerBumpRight L hL)) := hs
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (hLb hh hh1) (by positivity))
          (mul_le_mul_of_nonneg_left (hRb hh hh1) (by positivity))
    _ ≤ 2*(h^4*Cc^2)*(h*Cl) + 2*(h^4*Cc^2)*(h*Cr) := by
      exact add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_right ha (by positivity : (0:ℝ) ≤ 2 * (h * Cl))])
        (by nlinarith [mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2 * (h * Cr))])
    _ = h^5*C := by dsimp [C]; ring

theorem exists_optimizerSampledCorrection_differenceEnergy_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      differenceEnergy (optimizerSampledCorrection L hL h) ≤ h ^ 7 * C := by
  obtain ⟨hc,Cc,hcp,hCc,hcb⟩ := exists_optimizerCorrection_abs_sum_bound L hL
  obtain ⟨Cl,hCl,hLb⟩ := exists_sampledOptimizerBumpLeft_differenceEnergy_bound L hL
  obtain ⟨Cr,hCr,hRb⟩ := exists_sampledOptimizerBumpRight_differenceEnergy_bound L hL
  let C := 2*Cc^2*(Cl+Cr)
  refine ⟨min hc 1,C,lt_min hcp (by norm_num),by positivity,?_⟩
  intro h hh hh0
  obtain ⟨ha,hb⟩ := coeff_sq hCc (hcb hh (le_trans hh0 (min_le_left _ _)))
  have hs := difference_energy_linear
    (a := optimizerCorrectionLeft L hL h) (b := optimizerCorrectionRight L hL h)
    (u := sampledKernel h (optimizerBumpLeft L hL)) (v := sampledKernel h (optimizerBumpRight L hL))
    (sampledKernel_difference_square_summable hh (optimizerBumpHorizon_pos L hL).le
      (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx))
    (sampledKernel_difference_square_summable hh (optimizerBumpHorizon_pos L hL).le
      (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx))
  change differenceEnergy (fun j => optimizerCorrectionLeft L hL h *
    sampledKernel h (optimizerBumpLeft L hL) j + optimizerCorrectionRight L hL h *
    sampledKernel h (optimizerBumpRight L hL) j) ≤ _
  calc
    _ ≤ 2*optimizerCorrectionLeft L hL h^2*(h^3*Cl) +
        2*optimizerCorrectionRight L hL h^2*(h^3*Cr) := by
      calc _ ≤ 2*optimizerCorrectionLeft L hL h^2*differenceEnergy
            (sampledKernel h (optimizerBumpLeft L hL)) +
            2*optimizerCorrectionRight L hL h^2*differenceEnergy
            (sampledKernel h (optimizerBumpRight L hL)) := hs
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (hLb hh (le_trans hh0 (min_le_right _ _))) (by positivity))
          (mul_le_mul_of_nonneg_left (hRb hh (le_trans hh0 (min_le_right _ _))) (by positivity))
    _ ≤ 2*(h^4*Cc^2)*(h^3*Cl) + 2*(h^4*Cc^2)*(h^3*Cr) := by
      exact add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_right ha (by positivity : (0:ℝ) ≤ 2 * (h^3 * Cl))])
        (by nlinarith [mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2 * (h^3 * Cr))])
    _ = h^7*C := by dsimp [C]; ring
end RayleighKernel.Discrete
