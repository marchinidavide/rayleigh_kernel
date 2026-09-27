import RayleighKernel.Discrete.Sampling
import RayleighKernel.Optimizer.Explicit
import RayleighKernel.Profile.Moments
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace RayleighKernel.Discrete
open RayleighKernel.Analysis.HalfLineH1

private def optimizerCore (L x : ℝ) : ℝ :=
  (1 / (optimizerSupport L * Profile.I0Star)) * Profile.FStar (x / optimizerSupport L)
private def optimizerMomentCore (L x : ℝ) : ℝ := x * optimizerCore L x

private theorem core_eq_profile_on_Icc {L : ℝ} (_hL : 0 < L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)) :
    optimizerCore L x = optimizerProfile L x := by
  rw [optimizerCore, optimizerProfile_of_mem hx]

private theorem core_endpoint_zero {L : ℝ} (hL : 0 < L) :
    optimizerCore L (optimizerSupport L) = 0 := by
  rw [optimizerCore, div_self (optimizerSupport_pos hL).ne', Profile.FStar_apply,
    Profile.value_one]
  · simp
  · exact (lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar).ne'
  · exact Profile.cos_ne_one_of_mem_Ioo_two_pi ⟨
      lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar,
      Profile.tStar_lt_two_pi⟩

private theorem core_zero {L : ℝ} (_hL : 0 < L) : optimizerCore L 0 = 0 := by
  simp [optimizerCore, Profile.FStar_apply, div_eq_mul_inv]

private theorem endpoint_control_of_deriv_bound {f : ℝ → ℝ} {N K M : ℝ}
    (hNK : N ≤ K) (_hM : 0 ≤ M) (hf : ∀ x ∈ Icc N K, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ico N K, |deriv f x| ≤ M) (hfK : f K = 0) :
    |f N| ≤ M * (K - N) := by
  rcases eq_or_lt_of_le hNK with rfl | hNK
  · simp [hfK]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hderiv x hx)
  have h' : |f N - f K| ≤ M * (K - N) := by
    simpa [abs_sub_comm] using h K ⟨hNK.le, le_rfl⟩
  rw [hfK, sub_zero] at h'
  exact h'

private theorem profile_eq_core_on_Icc {L : ℝ} (hL : 0 < L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)) :
    optimizerProfile L x = optimizerCore L x :=
  (core_eq_profile_on_Icc hL hx).symm

private theorem optimizerProfile_tail_zero {L x : ℝ} (hL : 0 < L)
    (hx : optimizerSupport L ≤ x) : optimizerProfile L x = 0 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · exact core_endpoint_zero hL ▸ (core_eq_profile_on_Icc hL
      ⟨(optimizerSupport_pos hL).le, le_rfl⟩).symm
  · apply optimizerProfile_of_not_mem
    intro hm
    exact (not_lt_of_ge hm.2) hx

private theorem core_contDiff {L : ℝ} (_hL : 0 < L) :
    ContDiff ℝ 2 (optimizerCore L) := by
  unfold optimizerCore
  rw [show Profile.FStar = Profile.value Profile.tStar from funext Profile.FStar_apply]
  unfold Profile.value
  fun_prop

private theorem momentCore_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (optimizerMomentCore L) := by
  unfold optimizerMomentCore
  exact (contDiff_id.mul (core_contDiff hL))

private theorem intervalIntegral_optimizerProfile_core {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, optimizerProfile L x) = 1 := by
  let B : (optimizer L hL).CorrectionBumps :=
    Classical.choice (exists_correctionBumps (optimizer_isMinimizer hL).1)
  have hmass := integral_continuousRep_zero_minimizerSupport hL
    (optimizer_isMinimizer hL) B
  have hsupport := minimizerSupport_eq_optimizerSupport hL (optimizer_isMinimizer hL) B
  rw [hsupport] at hmass
  simpa [continuousRep_optimizer hL] using hmass

private theorem intervalIntegral_mul_optimizerProfile_core {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, x * optimizerProfile L x) = L := by
  let B : (optimizer L hL).CorrectionBumps :=
    Classical.choice (exists_correctionBumps (optimizer_isMinimizer hL).1)
  have hmoment := integral_mul_continuousRep_zero_minimizerSupport hL
    (optimizer_isMinimizer hL) B
  have hsupport := minimizerSupport_eq_optimizerSupport hL (optimizer_isMinimizer hL) B
  rw [hsupport] at hmoment
  simpa [continuousRep_optimizer hL] using hmoment

private theorem intervalIntegral_optimizerCore {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, optimizerCore L x) = 1 := by
  rw [intervalIntegral.integral_congr]
  · exact intervalIntegral_optimizerProfile_core hL
  · intro x hx
    exact core_eq_profile_on_Icc hL (by
      simpa [uIcc_of_le (optimizerSupport_pos hL).le] using hx)

private theorem intervalIntegral_mul_optimizerCore {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, optimizerMomentCore L x) = L := by
  rw [intervalIntegral.integral_congr]
  · simpa [optimizerMomentCore] using intervalIntegral_mul_optimizerProfile_core hL
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) (optimizerSupport L) := by
      simpa [uIcc_of_le (optimizerSupport_pos hL).le] using hx
    simp [optimizerMomentCore, profile_eq_core_on_Icc hL hx']

private theorem iteratedDerivWithin_two_le_of_global_bound
    {f : ℝ → ℝ} {a b C : ℝ} (hf : ContDiff ℝ 2 f) (hab : a ≤ b)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ C) :
    ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ C := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · intro x
    by_cases hx : x = a
    · subst x
      rw [iteratedDerivWithin_succ, derivWithin_zero_of_not_accPt]
      · simp [hC]
      · intro ha
        rw [accPt_iff_frequently] at ha
        exact ha (Filter.Eventually.of_forall (by simp))
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure]
      · simpa using hC
      · simp [hx]
  rw [uIcc_of_lt hab]
  intro x
  by_cases hx : x ∈ Icc a b
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      hf.contDiffAt hx]
    exact hbound x hx
  · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
      (by rwa [closure_Icc]), abs_zero]
    exact hC

private theorem iteratedDerivWithin_two_le_of_fixed_bound
    {f : ℝ → ℝ} {K C t : ℝ} (hf : ContDiff ℝ 2 f) (_hK : 0 < K)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ C)
    (ht : 0 ≤ t) (htK : t ≤ K) :
    (∀ x, |iteratedDerivWithin 2 f [[0, t]] x| ≤ C) ∧
      (∀ x, |iteratedDerivWithin 2 f [[t, K]] x| ≤ C) := by
  constructor
  · apply iteratedDerivWithin_two_le_of_global_bound hf ht hC
    intro x hx; exact hbound x ⟨hx.1, le_trans hx.2 htK⟩
  · apply iteratedDerivWithin_two_le_of_global_bound hf htK hC
    intro x hx; exact hbound x ⟨le_trans ht hx.1, hx.2⟩

private theorem continuous_iteratedDeriv_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ ζ : ℝ, 0 ≤ ζ ∧ ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ ζ := by
  let g : ℝ → ℝ := fun x => |iteratedDeriv 2 f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) :=
    (hf.continuous_iteratedDeriv 2 (by norm_num)).continuousOn.abs
  obtain ⟨ζ, hζ⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hζ0 : 0 ≤ ζ := le_trans (norm_nonneg (g 0)) (hζ 0 ⟨le_rfl, hK.le⟩)
  refine ⟨ζ, hζ0, fun x hx => ?_⟩
  simpa [g, Real.norm_eq_abs] using hζ x hx

private theorem deriv_bound_exists {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M := by
  let g : ℝ → ℝ := fun x => |deriv f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) :=
    by simpa [g, iteratedDeriv_one] using
      (hf.continuous_iteratedDeriv 1 (by norm_num)).continuousOn.abs
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_rfl, hK.le⟩)
  refine ⟨M, hM0, fun x hx => ?_⟩
  simpa [g, iteratedDeriv_one, Real.norm_eq_abs] using hM x hx

private theorem profile_sum_eq_core_sum
    {L h K : ℝ} (hL : 0 < L) (hh : 0 < h) (hK : 0 ≤ K)
    (hSK : K ≤ optimizerSupport L) :
    (∑ j ∈ Finset.range (meshCount K h + 1), optimizerProfile L ((j : ℝ) * h)) =
      ∑ j ∈ Finset.range (meshCount K h + 1), optimizerCore L ((j : ℝ) * h) := by
  apply Finset.sum_congr rfl; intro j hj
  have hjN : j ≤ meshCount K h := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hj)
  have hjK : (j : ℝ) * h ≤ K := by
    calc (j : ℝ) * h ≤ (meshCount K h : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) (le_of_lt hh)
    _ ≤ K := meshCount_mul_le hh hK
  exact profile_eq_core_on_Icc hL ⟨by positivity, hjK.trans hSK⟩

private theorem profile_weighted_sum_eq_core_weighted_sum
    {L h K : ℝ} (hL : 0 < L) (hh : 0 < h) (hK : 0 ≤ K)
    (hSK : K ≤ optimizerSupport L) :
    (∑ j ∈ Finset.range (meshCount K h + 1), ((j : ℝ) * h) *
        optimizerProfile L ((j : ℝ) * h)) =
      ∑ j ∈ Finset.range (meshCount K h + 1), ((j : ℝ) * h) *
        optimizerCore L ((j : ℝ) * h) := by
  apply Finset.sum_congr rfl; intro j hj
  have hjN : j ≤ meshCount K h := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hj)
  have hjK : (j : ℝ) * h ≤ K := by
    calc (j : ℝ) * h ≤ (meshCount K h : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) (le_of_lt hh)
    _ ≤ K := meshCount_mul_le hh hK
  rw [profile_eq_core_on_Icc hL ⟨by positivity, hjK.trans hSK⟩]

theorem optimizerProfile_eq_zero_of_support_le
    {L x : ℝ} (hL : 0 < L) (hx : optimizerSupport L ≤ x) :
    optimizerProfile L x = 0 := optimizerProfile_tail_zero hL hx

theorem intervalIntegral_optimizerProfile {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, optimizerProfile L x) = 1 :=
  intervalIntegral_optimizerProfile_core hL

theorem intervalIntegral_mul_optimizerProfile {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, x * optimizerProfile L x) = L :=
  intervalIntegral_mul_optimizerProfile_core hL

theorem exists_optimizerProfile_mass_defect_bound
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ optimizerSupport L →
      |mass (sampledKernel h (optimizerProfile L)) - 1| ≤ h ^ 2 * C := by
  let K := optimizerSupport L
  obtain ⟨ζ, hζ, hζbound⟩ := continuous_iteratedDeriv_bound (core_contDiff hL)
    (optimizerSupport_pos hL)
  obtain ⟨M, hM, hMbound⟩ := deriv_bound_exists (core_contDiff hL)
    (optimizerSupport_pos hL)
  let C := K * ζ / 12 + ζ / 12 + M / 2
  have hKpos : 0 < K := optimizerSupport_pos hL
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhl
  have hK : 0 ≤ K := (optimizerSupport_pos hL).le
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hζs := iteratedDerivWithin_two_le_of_fixed_bound (core_contDiff hL)
    (optimizerSupport_pos hL) hζ hζbound hN0 hN
  have h₁c : ContDiffOn ℝ 2 (optimizerCore L) [[0, (meshCount K h : ℝ) * h]] :=
    (core_contDiff hL).contDiffOn
  have h₂c : ContDiffOn ℝ 2 (optimizerCore L)
      [[(meshCount K h : ℝ) * h, K]] := (core_contDiff hL).contDiffOn
  have h₁ : IntervalIntegrable (optimizerCore L) volume 0
      ((meshCount K h : ℝ) * h) :=
    (core_contDiff hL).continuous.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (optimizerCore L) volume
      ((meshCount K h : ℝ) * h) K := (core_contDiff hL).continuous.intervalIntegrable _ _
  have hderiv : ∀ x ∈ Ico ((meshCount K h : ℝ) * h) K,
      |deriv (optimizerCore L) x| ≤ M := by
    intro x hx
    exact hMbound x ⟨hN0.trans hx.1, hx.2.le⟩
  have hfend : |optimizerCore L ((meshCount K h : ℝ) * h)| ≤
      M * meshRemainder K h := by
    apply endpoint_control_of_deriv_bound hN hM
    · intro x hx
      exact (core_contDiff hL).contDiffAt.differentiableAt (by norm_num)
    · exact hderiv
    · exact core_endpoint_zero hL
  have hdef := sampledGridSum_sub_integral_le_mul_h_sq (optimizerCore L)
    hh hh1 hhl hζ hζ hM hfend h₁c h₂c hζs.1 hζs.2 h₁ h₂
    (core_zero hL) (core_endpoint_zero hL)
  rw [intervalIntegral_optimizerCore hL] at hdef
  rw [mass_sampledKernel hh hK (fun x hx => optimizerProfile_tail_zero hL hx)]
  simp only [K] at hdef ⊢
  rw [profile_sum_eq_core_sum hL hh (optimizerSupport_pos hL).le le_rfl]
  simpa [C, K, optimizerMomentCore] using hdef

theorem exists_optimizerProfile_firstMoment_defect_bound
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ optimizerSupport L →
      |h * firstMoment (sampledKernel h (optimizerProfile L)) - L| ≤ h ^ 2 * C := by
  let K := optimizerSupport L
  obtain ⟨ζ, hζ, hζbound⟩ := continuous_iteratedDeriv_bound (momentCore_contDiff hL)
    (optimizerSupport_pos hL)
  obtain ⟨M, hM, hMbound⟩ := deriv_bound_exists (momentCore_contDiff hL)
    (optimizerSupport_pos hL)
  let C := K * ζ / 12 + ζ / 12 + M / 2
  have hKpos : 0 < K := optimizerSupport_pos hL
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhl
  have hK : 0 ≤ K := (optimizerSupport_pos hL).le
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hζs := iteratedDerivWithin_two_le_of_fixed_bound (momentCore_contDiff hL)
    (optimizerSupport_pos hL) hζ hζbound hN0 hN
  have h₁c : ContDiffOn ℝ 2 (optimizerMomentCore L)
      [[0, (meshCount K h : ℝ) * h]] := (momentCore_contDiff hL).contDiffOn
  have h₂c : ContDiffOn ℝ 2 (optimizerMomentCore L)
      [[(meshCount K h : ℝ) * h, K]] := (momentCore_contDiff hL).contDiffOn
  have h₁ : IntervalIntegrable (optimizerMomentCore L) volume 0
      ((meshCount K h : ℝ) * h) :=
    (momentCore_contDiff hL).continuous.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (optimizerMomentCore L) volume
      ((meshCount K h : ℝ) * h) K :=
    (momentCore_contDiff hL).continuous.intervalIntegrable _ _
  have hderiv : ∀ x ∈ Ico ((meshCount K h : ℝ) * h) K,
      |deriv (optimizerMomentCore L) x| ≤ M := by
    intro x hx
    exact hMbound x ⟨hN0.trans hx.1, hx.2.le⟩
  have hfend : |optimizerMomentCore L ((meshCount K h : ℝ) * h)| ≤
      M * meshRemainder K h := by
    apply endpoint_control_of_deriv_bound hN hM
    · intro x hx
      exact (momentCore_contDiff hL).contDiffAt.differentiableAt (by norm_num)
    · exact hderiv
    · rw [show optimizerMomentCore L K = K * optimizerCore L K by rfl,
        core_endpoint_zero hL, mul_zero]
  have hdef := sampledGridSum_sub_integral_le_mul_h_sq (optimizerMomentCore L)
    hh hh1 hhl hζ hζ hM hfend h₁c h₂c hζs.1 hζs.2 h₁ h₂
    (by simp [optimizerMomentCore, core_zero hL])
    (by simp [optimizerMomentCore, core_endpoint_zero hL])
  rw [intervalIntegral_mul_optimizerCore hL] at hdef
  simp only [optimizerMomentCore] at hdef
  rw [firstMoment_sampledKernel hh hK (fun x hx => optimizerProfile_tail_zero hL hx)]
  simp only [K] at hdef ⊢
  rw [profile_weighted_sum_eq_core_weighted_sum hL hh (optimizerSupport_pos hL).le le_rfl]
  simpa [C, K] using hdef

end RayleighKernel.Discrete
