import RayleighKernel.Optimizer.Explicit
import RayleighKernel.Obstacle.Variations
import RayleighKernel.Discrete.Sampling
import RayleighKernel.Discrete.OptimizerSampling
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace RayleighKernel.Analysis.HalfLineH1

open MeasureTheory Set
open Filter
open scoped SchwartzMap Topology Interval BigOperators

open RayleighKernel.Discrete

/-- A fixed pair of interior test functions for the canonical optimizer. -/
def optimizerCorrectionBumps (L : ℝ) (hL : 0 < L) :
    (optimizer L hL).CorrectionBumps :=
  Classical.choice (exists_correctionBumps (optimizer_isMinimizer hL).1)

/-- The left member of the fixed optimizer correction pair. -/
def optimizerBumpLeft (L : ℝ) (hL : 0 < L) : ℝ → ℝ :=
  (optimizerCorrectionBumps L hL).bumpLeft.1

/-- The right member of the fixed optimizer correction pair. -/
def optimizerBumpRight (L : ℝ) (hL : 0 < L) : ℝ → ℝ :=
  (optimizerCorrectionBumps L hL).bumpRight.1

private theorem optimizerBumpLeft_data (L : ℝ) (hL : 0 < L) :
    HasCompactSupport (optimizerBumpLeft L hL) ∧
      (∀ x, 0 ≤ optimizerBumpLeft L hL x) ∧
      tsupport (optimizerBumpLeft L hL) ⊆ Ioo 0 (optimizerSupport L) := by
  let B := optimizerCorrectionBumps L hL
  refine ⟨B.left_hasCompactSupport, B.left_nonnegative, ?_⟩
  intro x hx
  have hxpos : x ∈ (optimizer L hL).positivitySet := B.left_support hx
  have hpos : 0 < (optimizer L hL).continuousRep x := hxpos
  rw [continuousRep_optimizer hL] at hpos
  exact (optimizerProfile_pos_iff hL).mp hpos

private theorem optimizerBumpRight_data (L : ℝ) (hL : 0 < L) :
    HasCompactSupport (optimizerBumpRight L hL) ∧
      (∀ x, 0 ≤ optimizerBumpRight L hL x) ∧
      tsupport (optimizerBumpRight L hL) ⊆ Ioo 0 (optimizerSupport L) := by
  let B := optimizerCorrectionBumps L hL
  refine ⟨B.right_hasCompactSupport, B.right_nonnegative, ?_⟩
  intro x hx
  have hxpos : x ∈ (optimizer L hL).positivitySet := B.right_support hx
  have hpos : 0 < (optimizer L hL).continuousRep x := hxpos
  rw [continuousRep_optimizer hL] at hpos
  exact (optimizerProfile_pos_iff hL).mp hpos

theorem contDiff_optimizerBumpLeft (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ 2 (optimizerBumpLeft L hL) :=
  (optimizerCorrectionBumps L hL).bumpLeft.1.smooth 2

theorem contDiff_optimizerBumpRight (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ 2 (optimizerBumpRight L hL) :=
  (optimizerCorrectionBumps L hL).bumpRight.1.smooth 2

theorem hasCompactSupport_optimizerBumpLeft (L : ℝ) (hL : 0 < L) :
    HasCompactSupport (optimizerBumpLeft L hL) :=
  (optimizerBumpLeft_data L hL).1

theorem hasCompactSupport_optimizerBumpRight (L : ℝ) (hL : 0 < L) :
    HasCompactSupport (optimizerBumpRight L hL) :=
  (optimizerBumpRight_data L hL).1

theorem nonnegative_optimizerBumpLeft (L : ℝ) (hL : 0 < L) (x : ℝ) :
    0 ≤ optimizerBumpLeft L hL x :=
  (optimizerBumpLeft_data L hL).2.1 x

theorem nonnegative_optimizerBumpRight (L : ℝ) (hL : 0 < L) (x : ℝ) :
    0 ≤ optimizerBumpRight L hL x :=
  (optimizerBumpRight_data L hL).2.1 x

theorem tsupport_optimizerBumpLeft (L : ℝ) (hL : 0 < L) :
    tsupport (optimizerBumpLeft L hL) ⊆ Ioo 0 (optimizerSupport L) :=
  (optimizerBumpLeft_data L hL).2.2

theorem tsupport_optimizerBumpRight (L : ℝ) (hL : 0 < L) :
    tsupport (optimizerBumpRight L hL) ⊆ Ioo 0 (optimizerSupport L) :=
  (optimizerBumpRight_data L hL).2.2

def optimizerBumpSupport (L : ℝ) (hL : 0 < L) : Set ℝ :=
  tsupport (optimizerBumpLeft L hL) ∪ tsupport (optimizerBumpRight L hL)

theorem isCompact_optimizerBumpSupport (L : ℝ) (hL : 0 < L) :
    IsCompact (optimizerBumpSupport L hL) := by
  unfold optimizerBumpSupport
  exact (hasCompactSupport_optimizerBumpLeft L hL).isCompact.union
    (hasCompactSupport_optimizerBumpRight L hL).isCompact

theorem optimizerBumpSupport_subset (L : ℝ) (hL : 0 < L) :
    optimizerBumpSupport L hL ⊆ Ioo 0 (optimizerSupport L) := by
  intro x hx
  rcases hx with hx | hx
  · exact tsupport_optimizerBumpLeft L hL hx
  · exact tsupport_optimizerBumpRight L hL hx

theorem exists_optimizerBump_profile_margin (L : ℝ) (hL : 0 < L) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ optimizerBumpSupport L hL,
      m ≤ optimizerProfile L x := by
  have hcont : Continuous (optimizerProfile L) := by
    have heq : optimizerProfile L = (optimizer L hL).continuousRep := by
      funext x
      exact (continuousRep_optimizer hL x).symm
    rw [heq]
    exact (optimizer L hL).continuous_continuousRep
  apply (isCompact_optimizerBumpSupport L hL).exists_forall_le' hcont.continuousOn
  intro x hx
  exact (optimizerProfile_pos_iff hL).2 (optimizerBumpSupport_subset L hL hx)

theorem exists_optimizerBump_horizon (L : ℝ) (hL : 0 < L) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ K₀ < optimizerSupport L ∧
      (∀ x, K₀ ≤ x → optimizerBumpLeft L hL x = 0) ∧
      (∀ x, K₀ ≤ x → optimizerBumpRight L hL x = 0) := by
  let S := optimizerBumpSupport L hL
  have hScompact : IsCompact S := isCompact_optimizerBumpSupport L hL
  have hSK : S ⊆ Ioo 0 (optimizerSupport L) := optimizerBumpSupport_subset L hL
  by_cases hSne : S.Nonempty
  · obtain ⟨x₀, hx₀, hmax⟩ := hScompact.exists_isMaxOn hSne continuous_id.continuousOn
    let K₀ := (x₀ + optimizerSupport L) / 2
    have hx₀pos : 0 < x₀ := (hSK hx₀).1
    have hx₀K : x₀ < optimizerSupport L := (hSK hx₀).2
    have hK₀pos : 0 < K₀ := by
      dsimp [K₀]
      linarith
    have hK₀K : K₀ < optimizerSupport L := by
      dsimp [K₀]
      linarith
    refine ⟨K₀, hK₀pos, hK₀K, ?_, ?_⟩
    · intro x hxK
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hxs : x ∈ S := Or.inl hx
      have hle : x ≤ x₀ := by
        change x ∈ {y | y ≤ x₀}
        exact hmax hxs
      have hlt : x₀ < K₀ := by
        dsimp [K₀]
        linarith
      linarith
    · intro x hxK
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hxs : x ∈ S := Or.inr hx
      have hle : x ≤ x₀ := by
        change x ∈ {y | y ≤ x₀}
        exact hmax hxs
      have hlt : x₀ < K₀ := by
        dsimp [K₀]
        linarith
      linarith
  · have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hSne
    let K₀ := optimizerSupport L / 2
    have hKpos : 0 < K₀ := by
      dsimp [K₀]
      exact half_pos (optimizerSupport_pos hL)
    have hKK : K₀ < optimizerSupport L := by
      dsimp [K₀]
      linarith [optimizerSupport_pos hL]
    refine ⟨K₀, hKpos, hKK, ?_, ?_⟩
    · intro x hxK
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hxm : x ∈ S := Or.inl hx
      rw [hSempty] at hxm
      exact hxm
    · intro x hxK
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hxm : x ∈ S := Or.inr hx
      rw [hSempty] at hxm
      exact hxm

def optimizerBumpHorizon (L : ℝ) (hL : 0 < L) : ℝ :=
  Classical.choose (exists_optimizerBump_horizon L hL)

theorem optimizerBumpHorizon_pos (L : ℝ) (hL : 0 < L) :
    0 < optimizerBumpHorizon L hL :=
  (Classical.choose_spec (exists_optimizerBump_horizon L hL)).1

theorem optimizerBumpHorizon_lt_support (L : ℝ) (hL : 0 < L) :
    optimizerBumpHorizon L hL < optimizerSupport L :=
  (Classical.choose_spec (exists_optimizerBump_horizon L hL)).2.1

theorem optimizerBumpLeft_eq_zero_of_horizon_le (L : ℝ) (hL : 0 < L)
    {x : ℝ} (hx : optimizerBumpHorizon L hL ≤ x) :
    optimizerBumpLeft L hL x = 0 :=
  (Classical.choose_spec (exists_optimizerBump_horizon L hL)).2.2.1 x hx

theorem optimizerBumpRight_eq_zero_of_horizon_le (L : ℝ) (hL : 0 < L)
    {x : ℝ} (hx : optimizerBumpHorizon L hL ≤ x) :
    optimizerBumpRight L hL x = 0 :=
  (Classical.choose_spec (exists_optimizerBump_horizon L hL)).2.2.2 x hx

private theorem correction_endpoint_control_of_deriv_bound {f : ℝ → ℝ} {N K M : ℝ}
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

private theorem correction_iteratedDerivWithin_two_le_of_global_bound
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

private theorem correction_iteratedDerivWithin_two_le_of_fixed_bound
     {f : ℝ → ℝ} {K C t : ℝ} (hf : ContDiff ℝ 2 f) (_hK : 0 < K)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ C)
    (ht : 0 ≤ t) (htK : t ≤ K) :
    (∀ x, |iteratedDerivWithin 2 f [[0, t]] x| ≤ C) ∧
      (∀ x, |iteratedDerivWithin 2 f [[t, K]] x| ≤ C) := by
  constructor
  · apply correction_iteratedDerivWithin_two_le_of_global_bound hf ht hC
    intro x hx; exact hbound x ⟨hx.1, le_trans hx.2 htK⟩
  · apply correction_iteratedDerivWithin_two_le_of_global_bound hf htK hC
    intro x hx; exact hbound x ⟨le_trans ht hx.1, hx.2⟩

private theorem correction_continuous_iteratedDeriv_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ ζ : ℝ, 0 ≤ ζ ∧ ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ ζ := by
  let g : ℝ → ℝ := fun x => |iteratedDeriv 2 f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) :=
    (hf.continuous_iteratedDeriv 2 (by norm_num)).continuousOn.abs
  obtain ⟨ζ, hζ⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hζ0 : 0 ≤ ζ := le_trans (norm_nonneg (g 0)) (hζ 0 ⟨le_rfl, hK.le⟩)
  refine ⟨ζ, hζ0, fun x hx => ?_⟩
  simpa [g, Real.norm_eq_abs] using hζ x hx

private theorem correction_deriv_bound_exists {f : ℝ → ℝ} {K : ℝ}
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

private theorem correction_contDiff_mul_id {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun x => x * f x) :=
  contDiff_id.mul hf

private theorem correction_intervalIntegral_eq_integral_of_zero_outside_Icc
    {f : ℝ → ℝ} {K : ℝ} (hK : 0 < K) (hf : ∀ x, x ≤ 0 ∨ K ≤ x → f x = 0) :
    (∫ x in 0..K, f x) = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le hK.le, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rcases le_total x 0 with hx0 | hx0
    · exact hf x (Or.inl hx0)
    · exact hf x (Or.inr (le_of_not_ge fun hKx => hx ⟨hx0, hKx⟩)))

def optimizerBumpMassLeft (L : ℝ) (hL : 0 < L) : ℝ :=
  ∫ x, optimizerBumpLeft L hL x

def optimizerBumpMassRight (L : ℝ) (hL : 0 < L) : ℝ :=
  ∫ x, optimizerBumpRight L hL x

def optimizerBumpMomentLeft (L : ℝ) (hL : 0 < L) : ℝ :=
  ∫ x, x * optimizerBumpLeft L hL x

def optimizerBumpMomentRight (L : ℝ) (hL : 0 < L) : ℝ :=
  ∫ x, x * optimizerBumpRight L hL x

private theorem exists_correction_sampled_mass_defect_bound
    {f : ℝ → ℝ} {K : ℝ} (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ K →
      (∀ x, x ≤ 0 → f x = 0) → (∀ x, K ≤ x → f x = 0) → f K = 0 →
      |Discrete.mass (sampledKernel h f) - ∫ x, f x| ≤ h ^ 2 * C := by
  obtain ⟨ζ, hζ, hζbound⟩ := correction_continuous_iteratedDeriv_bound hf hK
  obtain ⟨M, hM, hMbound⟩ := correction_deriv_bound_exists hf hK
  let C := K * ζ / 12 + ζ / 12 + M / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhk hfleft htail hfK
  have hK0 : 0 ≤ K := hK.le
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK0
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hζs := correction_iteratedDerivWithin_two_le_of_fixed_bound hf hK hζ
    hζbound hN0 hN
  have h₁c : ContDiffOn ℝ 2 f [[0, (meshCount K h : ℝ) * h]] := hf.contDiffOn
  have h₂c : ContDiffOn ℝ 2 f [[(meshCount K h : ℝ) * h, K]] := hf.contDiffOn
  have h₁ : IntervalIntegrable f volume 0 ((meshCount K h : ℝ) * h) :=
    hf.continuous.intervalIntegrable _ _
  have h₂ : IntervalIntegrable f volume ((meshCount K h : ℝ) * h) K :=
    hf.continuous.intervalIntegrable _ _
  have hderiv : ∀ x ∈ Ico ((meshCount K h : ℝ) * h) K,
      |deriv f x| ≤ M := by
    intro x hx
    exact hMbound x ⟨hN0.trans hx.1, hx.2.le⟩
  have hfend : |f ((meshCount K h : ℝ) * h)| ≤
      M * meshRemainder K h := by
    apply correction_endpoint_control_of_deriv_bound hN hM
    · intro x hx
      exact (hf.contDiffAt.differentiableAt (by norm_num))
    · exact hderiv
    · exact hfK
  have hf0 : f 0 = 0 := hfleft 0 le_rfl
  have hdef := mass_sampledKernel_sub_integral_le_mul_h_sq hh hh1 hhk hfK htail
    hζ hζ hM hfend h₁c h₂c hζs.1 hζs.2 h₁ h₂ hf0
  rw [correction_intervalIntegral_eq_integral_of_zero_outside_Icc hK
    (fun x hx => by
      rcases hx with hx0 | hxK
      · exact hfleft x hx0
      · exact htail x hxK)] at hdef
  simpa [C] using hdef

private theorem exists_correction_sampled_moment_defect_bound
    {f : ℝ → ℝ} {K : ℝ} (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ K →
      (∀ x, x ≤ 0 → f x = 0) → (∀ x, K ≤ x → f x = 0) →
      |h * Discrete.firstMoment (sampledKernel h f) - ∫ x, x * f x| ≤ h ^ 2 * C := by
  let g : ℝ → ℝ := fun x => x * f x
  have hg : ContDiff ℝ 2 g := correction_contDiff_mul_id hf
  obtain ⟨ζ, hζ, hζbound⟩ := correction_continuous_iteratedDeriv_bound hg hK
  obtain ⟨M, hM, hMbound⟩ := correction_deriv_bound_exists hg hK
  let C := K * ζ / 12 + ζ / 12 + M / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhk hfleft htail
  have hK0 : 0 ≤ K := hK.le
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK0
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hζs := correction_iteratedDerivWithin_two_le_of_fixed_bound hg hK hζ
    hζbound hN0 hN
  have h₁c : ContDiffOn ℝ 2 g [[0, (meshCount K h : ℝ) * h]] := hg.contDiffOn
  have h₂c : ContDiffOn ℝ 2 g [[(meshCount K h : ℝ) * h, K]] := hg.contDiffOn
  have h₁ : IntervalIntegrable g volume 0 ((meshCount K h : ℝ) * h) :=
    hg.continuous.intervalIntegrable _ _
  have h₂ : IntervalIntegrable g volume ((meshCount K h : ℝ) * h) K :=
    hg.continuous.intervalIntegrable _ _
  have hgderiv : ∀ x ∈ Ico ((meshCount K h : ℝ) * h) K,
      |deriv g x| ≤ M := by
    intro x hx
    exact hMbound x ⟨hN0.trans hx.1, hx.2.le⟩
  have hgend : |g ((meshCount K h : ℝ) * h)| ≤
      M * meshRemainder K h := by
    apply correction_endpoint_control_of_deriv_bound hN hM
    · intro x hx
      exact (hg.contDiffAt.differentiableAt (by norm_num))
    · exact hgderiv
    · simp [g, htail _ (le_rfl : K ≤ K)]
  have hdef := firstMoment_sampledKernel_sub_integral_le_mul_h_sq (f := f) (g := g)
    hh hh1 hhk htail (by simp [g, htail _ (le_rfl : K ≤ K)]) (by intro x; rfl)
    hζ hζ hM hgend h₁c h₂c hζs.1 hζs.2 h₁ h₂ (by simp [g])
  rw [correction_intervalIntegral_eq_integral_of_zero_outside_Icc hK
    (fun x hx => by
       rcases hx with hx0 | hxK
       · simp [g, hfleft x hx0]
       · simp [g, htail x hxK])] at hdef
  simpa [C, g] using hdef

def sampledBumpMassLeft (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  Discrete.mass (sampledKernel h (optimizerBumpLeft L hL))

def sampledBumpMassRight (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  Discrete.mass (sampledKernel h (optimizerBumpRight L hL))

def sampledBumpMomentLeft (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  h * Discrete.firstMoment (sampledKernel h (optimizerBumpLeft L hL))

def sampledBumpMomentRight (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  h * Discrete.firstMoment (sampledKernel h (optimizerBumpRight L hL))

private theorem optimizerBumpLeft_eq_zero_of_nonpositive (L : ℝ) (hL : 0 < L)
    {x : ℝ} (hx : x ≤ 0) : optimizerBumpLeft L hL x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxs
  exact (not_lt_of_ge hx) (tsupport_optimizerBumpLeft L hL hxs).1

private theorem optimizerBumpRight_eq_zero_of_nonpositive (L : ℝ) (hL : 0 < L)
    {x : ℝ} (hx : x ≤ 0) : optimizerBumpRight L hL x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hxs
  exact (not_lt_of_ge hx) (tsupport_optimizerBumpRight L hL hxs).1

theorem exists_sampledBumpMassLeft_defect_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerBumpHorizon L hL →
      |sampledBumpMassLeft L hL h - optimizerBumpMassLeft L hL| ≤ h ^ 2 * C := by
  obtain ⟨C, hC, hbound⟩ := exists_correction_sampled_mass_defect_bound
    (contDiff_optimizerBumpLeft L hL) (optimizerBumpHorizon_pos L hL)
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 hhk
  have h := hbound hh hh1 hhk
    (fun x hx => optimizerBumpLeft_eq_zero_of_nonpositive L hL hx)
    (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)
    (optimizerBumpLeft_eq_zero_of_horizon_le L hL le_rfl)
  simpa [sampledBumpMassLeft, optimizerBumpMassLeft] using h

theorem exists_sampledBumpMassRight_defect_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerBumpHorizon L hL →
      |sampledBumpMassRight L hL h - optimizerBumpMassRight L hL| ≤ h ^ 2 * C := by
  obtain ⟨C, hC, hbound⟩ := exists_correction_sampled_mass_defect_bound
    (contDiff_optimizerBumpRight L hL) (optimizerBumpHorizon_pos L hL)
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 hhk
  have h := hbound hh hh1 hhk
    (fun x hx => optimizerBumpRight_eq_zero_of_nonpositive L hL hx)
    (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)
    (optimizerBumpRight_eq_zero_of_horizon_le L hL le_rfl)
  simpa [sampledBumpMassRight, optimizerBumpMassRight] using h

theorem exists_sampledBumpMomentLeft_defect_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerBumpHorizon L hL →
      |sampledBumpMomentLeft L hL h - optimizerBumpMomentLeft L hL| ≤ h ^ 2 * C := by
  obtain ⟨C, hC, hbound⟩ := exists_correction_sampled_moment_defect_bound
    (contDiff_optimizerBumpLeft L hL) (optimizerBumpHorizon_pos L hL)
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 hhk
  have h := hbound hh hh1 hhk
    (fun x hx => optimizerBumpLeft_eq_zero_of_nonpositive L hL hx)
    (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)
  simpa [sampledBumpMomentLeft, optimizerBumpMomentLeft] using h

theorem exists_sampledBumpMomentRight_defect_bound (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerBumpHorizon L hL →
      |sampledBumpMomentRight L hL h - optimizerBumpMomentRight L hL| ≤ h ^ 2 * C := by
  obtain ⟨C, hC, hbound⟩ := exists_correction_sampled_moment_defect_bound
    (contDiff_optimizerBumpRight L hL) (optimizerBumpHorizon_pos L hL)
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 hhk
  have h := hbound hh hh1 hhk
    (fun x hx => optimizerBumpRight_eq_zero_of_nonpositive L hL hx)
    (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)
  simpa [sampledBumpMomentRight, optimizerBumpMomentRight] using h

theorem optimizerBumpDet_pos (L : ℝ) (hL : 0 < L) :
    0 < optimizerBumpMassLeft L hL * optimizerBumpMomentRight L hL -
      optimizerBumpMassRight L hL * optimizerBumpMomentLeft L hL := by
  unfold optimizerBumpMassLeft optimizerBumpMassRight optimizerBumpMomentLeft
    optimizerBumpMomentRight optimizerBumpLeft optimizerBumpRight
  have hmL := PositiveTestFunction.testMass_eq_mass
    (optimizerCorrectionBumps L hL).bumpLeft
  have hmR := PositiveTestFunction.testMass_eq_mass
    (optimizerCorrectionBumps L hL).bumpRight
  have hqL := testFirstMoment_bridge (optimizerCorrectionBumps L hL).bumpLeft
  have hqR := testFirstMoment_bridge (optimizerCorrectionBumps L hL).bumpRight
  have hdet := optimizerCorrectionBumps L hL |>.determinant_pos
  rw [← hmL, ← hmR, ← hqL, ← hqR] at hdet
  simpa [PositiveTestFunction.testMass, PositiveTestFunction.testFirstMoment] using hdet

def sampledBumpMatrix (L : ℝ) (hL : 0 < L) (h : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![sampledBumpMassLeft L hL h, sampledBumpMassRight L hL h;
      sampledBumpMomentLeft L hL h, sampledBumpMomentRight L hL h]

def optimizerBumpMatrix (L : ℝ) (hL : 0 < L) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![optimizerBumpMassLeft L hL, optimizerBumpMassRight L hL;
      optimizerBumpMomentLeft L hL, optimizerBumpMomentRight L hL]

private theorem tendsto_of_abs_sub_le_sq_mul_right
    {F : ℝ → ℝ} {a C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ δ →
      |F h - a| ≤ h ^ 2 * C) :
    Tendsto F (𝓝[>] 0) (𝓝 a) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    Ioo_mem_nhdsGT hεC] with h hδ' h1 hε'
  rw [Real.dist_eq]
  have hsq : h ^ 2 ≤ h := by
    nlinarith [mul_nonneg h1.1.le (sub_nonneg.mpr h1.2.le)]
  calc
    |F h - a| ≤ h ^ 2 * C := hbound hδ'.1 h1.2.le hδ'.2.le
    _ ≤ h * C := mul_le_mul_of_nonneg_right hsq hC
    _ < h * (C + 1) := by
      nlinarith [mul_pos hδ'.1 (by norm_num : (0 : ℝ) < 1)]
    _ < ε := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hε'.2

private theorem tendsto_sampledBumpMassLeft (L : ℝ) (hL : 0 < L) :
    Tendsto (sampledBumpMassLeft L hL) (𝓝[>] 0) (𝓝 (optimizerBumpMassLeft L hL)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sampledBumpMassLeft_defect_bound L hL
  exact tendsto_of_abs_sub_le_sq_mul_right hC (optimizerBumpHorizon_pos L hL) hbound

private theorem tendsto_sampledBumpMassRight (L : ℝ) (hL : 0 < L) :
    Tendsto (sampledBumpMassRight L hL) (𝓝[>] 0) (𝓝 (optimizerBumpMassRight L hL)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sampledBumpMassRight_defect_bound L hL
  exact tendsto_of_abs_sub_le_sq_mul_right hC (optimizerBumpHorizon_pos L hL) hbound

private theorem tendsto_sampledBumpMomentLeft (L : ℝ) (hL : 0 < L) :
    Tendsto (sampledBumpMomentLeft L hL) (𝓝[>] 0) (𝓝 (optimizerBumpMomentLeft L hL)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sampledBumpMomentLeft_defect_bound L hL
  exact tendsto_of_abs_sub_le_sq_mul_right hC (optimizerBumpHorizon_pos L hL) hbound

private theorem tendsto_sampledBumpMomentRight (L : ℝ) (hL : 0 < L) :
    Tendsto (sampledBumpMomentRight L hL) (𝓝[>] 0) (𝓝 (optimizerBumpMomentRight L hL)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sampledBumpMomentRight_defect_bound L hL
  exact tendsto_of_abs_sub_le_sq_mul_right hC (optimizerBumpHorizon_pos L hL) hbound

theorem det_optimizerBumpMatrix_pos (L : ℝ) (hL : 0 < L) :
    0 < (optimizerBumpMatrix L hL).det := by
  rw [Matrix.det_fin_two]
  simpa [optimizerBumpMatrix] using optimizerBumpDet_pos L hL

theorem tendsto_sampledBumpMatrix (L : ℝ) (hL : 0 < L) :
    Tendsto (sampledBumpMatrix L hL) (𝓝[>] 0) (𝓝 (optimizerBumpMatrix L hL)) := by
  change Tendsto (fun h => fun i j => sampledBumpMatrix L hL h i j) (𝓝[>] 0)
    (𝓝 (fun i j => optimizerBumpMatrix L hL i j))
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j <;> simp [sampledBumpMatrix, optimizerBumpMatrix]
  · exact tendsto_sampledBumpMassLeft L hL
  · exact tendsto_sampledBumpMassRight L hL
  · exact tendsto_sampledBumpMomentLeft L hL
  · exact tendsto_sampledBumpMomentRight L hL

theorem tendsto_det_sampledBumpMatrix (L : ℝ) (hL : 0 < L) :
    Tendsto (fun h => (sampledBumpMatrix L hL h).det) (𝓝[>] 0)
      (𝓝 (optimizerBumpMatrix L hL).det) := by
  have hdet : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) :=
    Continuous.matrix_det continuous_id
  exact hdet.continuousAt.tendsto.comp (tendsto_sampledBumpMatrix L hL)

theorem eventually_det_sampledBumpMatrix_pos (L : ℝ) (hL : 0 < L) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < (sampledBumpMatrix L hL h).det := by
  apply (tendsto_det_sampledBumpMatrix L hL).eventually
  exact isOpen_Ioi.mem_nhds (det_optimizerBumpMatrix_pos L hL)

theorem eventually_sampledBumpMatrix_isUnit (L : ℝ) (hL : 0 < L) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), IsUnit (sampledBumpMatrix L hL h) := by
  filter_upwards [eventually_det_sampledBumpMatrix_pos L hL] with h hh
  rw [Matrix.isUnit_iff_isUnit_det]
  exact (isUnit_iff_ne_zero.mpr (ne_of_gt hh))

def sampledBumpDet (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  sampledBumpMassLeft L hL h * sampledBumpMomentRight L hL h -
    sampledBumpMassRight L hL h * sampledBumpMomentLeft L hL h

theorem sampledBumpDet_eq_matrix_det (L : ℝ) (hL : 0 < L) (h : ℝ) :
    sampledBumpDet L hL h = (sampledBumpMatrix L hL h).det := by
  rw [Matrix.det_fin_two]
  rfl

private theorem exists_pos_threshold_of_eventually_nhdsWithin {P : ℝ → Prop}
    (hP : ∀ᶠ h in 𝓝[>] (0 : ℝ), P h) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ → P h := by
  obtain ⟨u, hu, huP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hP
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε / 2, by positivity, ?_⟩
  intro h hh hh₀
  apply huP
  exact ⟨hεu (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh]; linarith), hh⟩

theorem exists_sampledBumpDet_lower_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      (optimizerBumpMassLeft L hL * optimizerBumpMomentRight L hL -
        optimizerBumpMassRight L hL * optimizerBumpMomentLeft L hL) / 2 ≤
        sampledBumpDet L hL h := by
  have hp : 0 < (optimizerBumpMatrix L hL).det := det_optimizerBumpMatrix_pos L hL
  have he : ∀ᶠ h in 𝓝[>] (0 : ℝ), (optimizerBumpMatrix L hL).det / 2 <
      (sampledBumpMatrix L hL h).det := by
    apply (tendsto_det_sampledBumpMatrix L hL).eventually
    exact isOpen_Ioi.mem_nhds (show
      (optimizerBumpMatrix L hL).det / 2 < (optimizerBumpMatrix L hL).det by
        linarith [hp])
  obtain ⟨h₀, hh₀, hb⟩ := exists_pos_threshold_of_eventually_nhdsWithin he
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hh₀
  rw [sampledBumpDet_eq_matrix_det]
  have hh' := hb hh hh₀
  simpa [sampledBumpMatrix, optimizerBumpMatrix, Matrix.det_fin_two] using hh'.le

def sampledBumpSolveLeft (L : ℝ) (hL : 0 < L) (h : ℝ) (rMass rMoment : ℝ) : ℝ :=
  (rMass * sampledBumpMomentRight L hL h - sampledBumpMassRight L hL h * rMoment) /
    sampledBumpDet L hL h

def sampledBumpSolveRight (L : ℝ) (hL : 0 < L) (h : ℝ) (rMass rMoment : ℝ) : ℝ :=
  (sampledBumpMassLeft L hL h * rMoment - rMass * sampledBumpMomentLeft L hL h) /
    sampledBumpDet L hL h

theorem sampledBumpSolveLeft_eq (L : ℝ) (hL : 0 < L) (h : ℝ) (rMass rMoment : ℝ)
    (hdet : sampledBumpDet L hL h ≠ 0) :
    sampledBumpMassLeft L hL h * sampledBumpSolveLeft L hL h rMass rMoment +
      sampledBumpMassRight L hL h * sampledBumpSolveRight L hL h rMass rMoment = rMass := by
  dsimp [sampledBumpSolveLeft, sampledBumpSolveRight]
  field_simp [hdet]
  dsimp [sampledBumpDet]
  ring

theorem sampledBumpSolveRight_eq (L : ℝ) (hL : 0 < L) (h : ℝ) (rMass rMoment : ℝ)
    (hdet : sampledBumpDet L hL h ≠ 0) :
    sampledBumpMomentLeft L hL h * sampledBumpSolveLeft L hL h rMass rMoment +
      sampledBumpMomentRight L hL h * sampledBumpSolveRight L hL h rMass rMoment = rMoment := by
  dsimp [sampledBumpSolveLeft, sampledBumpSolveRight]
  field_simp [hdet]
  dsimp [sampledBumpDet]
  ring

private theorem eventually_abs_le_abs_add_one_of_tendsto
    {F : ℝ → ℝ} {a : ℝ} (hF : Tendsto F (𝓝[>] 0) (𝓝 a)) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), |F h| ≤ |a| + 1 := by
  apply (hF.eventually (Metric.isOpen_ball.mem_nhds (show a ∈ Metric.ball a 1 by simp))).mono
  intro h hh
  rw [Real.dist_eq] at hh
  calc
    |F h| ≤ |F h - a| + |a| := by
      calc
        |F h| = |(F h - a) + a| := by rw [sub_add_cancel]
        _ ≤ |F h - a| + |a| := abs_add_le _ _
    _ ≤ |a| + 1 := by linarith

theorem exists_sampledBumpSolve_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      ∀ rMass rMoment : ℝ,
        |sampledBumpSolveLeft L hL h rMass rMoment| ≤
            C * (|rMass| + |rMoment|) ∧
        |sampledBumpSolveRight L hL h rMass rMoment| ≤
            C * (|rMass| + |rMoment|) := by
  let d : ℝ := optimizerBumpMassLeft L hL * optimizerBumpMomentRight L hL -
    optimizerBumpMassRight L hL * optimizerBumpMomentLeft L hL
  have hd : 0 < d := by
    dsimp [d]
    exact optimizerBumpDet_pos L hL
  obtain ⟨hdet₀, hhdet₀, hdetbound⟩ := exists_sampledBumpDet_lower_bound L hL
  have he : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |sampledBumpMomentRight L hL h| ≤ |optimizerBumpMomentRight L hL| + 1 ∧
      |sampledBumpMassRight L hL h| ≤ |optimizerBumpMassRight L hL| + 1 ∧
      |sampledBumpMassLeft L hL h| ≤ |optimizerBumpMassLeft L hL| + 1 ∧
      |sampledBumpMomentLeft L hL h| ≤ |optimizerBumpMomentLeft L hL| + 1 := by
    filter_upwards [
      eventually_abs_le_abs_add_one_of_tendsto (tendsto_sampledBumpMomentRight L hL),
      eventually_abs_le_abs_add_one_of_tendsto (tendsto_sampledBumpMassRight L hL),
      eventually_abs_le_abs_add_one_of_tendsto (tendsto_sampledBumpMassLeft L hL),
      eventually_abs_le_abs_add_one_of_tendsto (tendsto_sampledBumpMomentLeft L hL)] with h h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  obtain ⟨hentry₀, hhentry₀, hentrybound⟩ := exists_pos_threshold_of_eventually_nhdsWithin he
  let B : ℝ := max (|optimizerBumpMomentRight L hL| + 1)
    (max (|optimizerBumpMassRight L hL| + 1)
      (max (|optimizerBumpMassLeft L hL| + 1)
        (|optimizerBumpMomentLeft L hL| + 1)))
  let C : ℝ := 2 * B / d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨min hdet₀ hentry₀, C, by positivity, by positivity, ?_⟩
  intro h hh hh₀ rMass rMoment
  have hd' := hdetbound hh (le_trans hh₀ (min_le_left _ _))
  have he' := hentrybound hh (le_trans hh₀ (min_le_right _ _))
  have hden : 0 < |sampledBumpDet L hL h| :=
    lt_of_lt_of_le (by positivity) (le_trans hd' (le_abs_self _))
  have hmr : |sampledBumpMomentRight L hL h| ≤ B := le_trans he'.1 (le_max_left _ _)
  have hrr : |sampledBumpMassRight L hL h| ≤ B :=
    le_trans he'.2.1 (le_max_of_le_right (le_max_left _ _))
  have hlr : |sampledBumpMassLeft L hL h| ≤ B :=
    le_trans he'.2.2.1 (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hml : |sampledBumpMomentLeft L hL h| ≤ B :=
    le_trans he'.2.2.2 (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_refl _))))
  have hn1 : |rMass * sampledBumpMomentRight L hL h - sampledBumpMassRight L hL h * rMoment| ≤
      B * (|rMass| + |rMoment|) := by
    calc
      _ ≤ |rMass| * |sampledBumpMomentRight L hL h| +
          |sampledBumpMassRight L hL h| * |rMoment| := by
        simpa [sub_eq_add_neg, abs_mul] using abs_add_le
          (rMass * sampledBumpMomentRight L hL h)
          (-(sampledBumpMassRight L hL h * rMoment))
      _ ≤ |rMass| * B + B * |rMoment| := add_le_add
        (mul_le_mul_of_nonneg_left hmr (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hrr (abs_nonneg _))
      _ = B * (|rMass| + |rMoment|) := by ring
  have hn2 : |sampledBumpMassLeft L hL h * rMoment - rMass * sampledBumpMomentLeft L hL h| ≤
      B * (|rMass| + |rMoment|) := by
    calc
      _ ≤ |sampledBumpMassLeft L hL h| * |rMoment| +
          |rMass| * |sampledBumpMomentLeft L hL h| := by
        simpa [sub_eq_add_neg, abs_mul] using abs_add_le
          (sampledBumpMassLeft L hL h * rMoment)
          (-(rMass * sampledBumpMomentLeft L hL h))
      _ ≤ B * |rMoment| + |rMass| * B := add_le_add
        (mul_le_mul_of_nonneg_right hlr (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hml (abs_nonneg _))
      _ = B * (|rMass| + |rMoment|) := by ring
  have hc : B ≤ C * |sampledBumpDet L hL h| := by
    calc
      B = C * (d / 2) := by dsimp [C]; field_simp [ne_of_gt hd]
      _ ≤ C * |sampledBumpDet L hL h| :=
        mul_le_mul_of_nonneg_left (le_trans hd' (le_abs_self _)) (by positivity)
  constructor
  · change |(rMass * sampledBumpMomentRight L hL h - sampledBumpMassRight L hL h * rMoment) /
      sampledBumpDet L hL h| ≤ _
    rw [abs_div]
    apply (div_le_iff₀ hden).2
    exact le_trans hn1 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hc (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  · change |(sampledBumpMassLeft L hL h * rMoment - rMass * sampledBumpMomentLeft L hL h) /
      sampledBumpDet L hL h| ≤ _
    rw [abs_div]
    apply (div_le_iff₀ hden).2
    exact le_trans hn2 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
         mul_le_mul_of_nonneg_right hc (add_nonneg (abs_nonneg _) (abs_nonneg _)))

def optimizerSampledMassResidual (L : ℝ) (_hL : 0 < L) (h : ℝ) : ℝ :=
  1 - Discrete.mass (sampledKernel h (optimizerProfile L))

def optimizerSampledMomentResidual (L : ℝ) (_hL : 0 < L) (h : ℝ) : ℝ :=
  L - h * Discrete.firstMoment (sampledKernel h (optimizerProfile L))

def optimizerCorrectionLeft (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  sampledBumpSolveLeft L hL h (optimizerSampledMassResidual L hL h)
    (optimizerSampledMomentResidual L hL h)

def optimizerCorrectionRight (L : ℝ) (hL : 0 < L) (h : ℝ) : ℝ :=
  sampledBumpSolveRight L hL h (optimizerSampledMassResidual L hL h)
    (optimizerSampledMomentResidual L hL h)

def correctedSampledOptimizer (L : ℝ) (hL : 0 < L) (h : ℝ) : Discrete.Kernel :=
  fun j => sampledKernel h (optimizerProfile L) j +
    optimizerCorrectionLeft L hL h * sampledKernel h (optimizerBumpLeft L hL) j +
    optimizerCorrectionRight L hL h * sampledKernel h (optimizerBumpRight L hL) j

theorem exists_optimizerCorrection_abs_sum_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      |optimizerCorrectionLeft L hL h| + |optimizerCorrectionRight L hL h| ≤ h ^ 2 * C := by
  obtain ⟨hs, Cs, hhs, hCs, hsolve⟩ := exists_sampledBumpSolve_bound L hL
  obtain ⟨Cm, hCm, hm⟩ := Discrete.exists_optimizerProfile_mass_defect_bound hL
  obtain ⟨Cq, hCq, hq⟩ := Discrete.exists_optimizerProfile_firstMoment_defect_bound hL
  let C := 2 * Cs * (Cm + Cq)
  refine ⟨min (min hs 1) (optimizerSupport L), C, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hhs (by norm_num)) (optimizerSupport_pos hL)
  · dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) hCs) (add_nonneg hCm hCq)
  intro h hh hh0
  have hh1 : h ≤ 1 := le_trans hh0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhK : h ≤ optimizerSupport L := le_trans hh0 (min_le_right _ _)
  have hm' := hm hh hh1 hhK
  have hq' := hq hh hh1 hhK
  have hm'' : |optimizerSampledMassResidual L hL h| ≤ h ^ 2 * Cm := by
    simpa [optimizerSampledMassResidual, abs_sub_comm] using hm'
  have hq'' : |optimizerSampledMomentResidual L hL h| ≤ h ^ 2 * Cq := by
    simpa [optimizerSampledMomentResidual, abs_sub_comm] using hq'
  have hs' := hsolve hh (le_trans hh0 (le_trans (min_le_left _ _) (min_le_left _ _)))
    (optimizerSampledMassResidual L hL h) (optimizerSampledMomentResidual L hL h)
  have hsum : |optimizerSampledMassResidual L hL h| +
      |optimizerSampledMomentResidual L hL h| ≤ h ^ 2 * (Cm + Cq) := by
    nlinarith [hm'', hq'']
  dsimp [optimizerCorrectionLeft, optimizerCorrectionRight]
  have hsum' :
      |sampledBumpSolveLeft L hL h (optimizerSampledMassResidual L hL h)
          (optimizerSampledMomentResidual L hL h)| +
        |sampledBumpSolveRight L hL h (optimizerSampledMassResidual L hL h)
          (optimizerSampledMomentResidual L hL h)| ≤
      2 * Cs * (|optimizerSampledMassResidual L hL h| +
        |optimizerSampledMomentResidual L hL h|) := by
    calc
      _ ≤ Cs * (|optimizerSampledMassResidual L hL h| +
          |optimizerSampledMomentResidual L hL h|) +
          Cs * (|optimizerSampledMassResidual L hL h| +
            |optimizerSampledMomentResidual L hL h|) := add_le_add hs'.1 hs'.2
      _ = _ := by ring_nf
  dsimp [C]
  calc
    _ ≤ 2 * Cs * (|optimizerSampledMassResidual L hL h| +
        |optimizerSampledMomentResidual L hL h|) := hsum'
    _ ≤ 2 * Cs * (h ^ 2 * (Cm + Cq)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hCs)
    _ = h ^ 2 * (2 * Cs * (Cm + Cq)) := by ring

theorem exists_optimizerCorrection_coeff_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      |optimizerCorrectionLeft L hL h| ≤ h ^ 2 * C ∧
      |optimizerCorrectionRight L hL h| ≤ h ^ 2 * C := by
  obtain ⟨h₀, C, h₀pos, hC, hb⟩ := exists_optimizerCorrection_abs_sum_bound L hL
  refine ⟨h₀, C, h₀pos, hC, ?_⟩
  intro h hh hh₀
  have hsumb := hb hh hh₀
  exact ⟨le_trans (le_add_of_nonneg_right (abs_nonneg _)) hsumb,
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) hsumb⟩

private theorem mass_add_smul_add_smul {u v w : Discrete.Kernel} {a b : ℝ}
    (hu : Summable u) (hv : Summable v) (hw : Summable w) :
    Discrete.mass (fun j => u j + a * v j + b * w j) =
      Discrete.mass u + a * Discrete.mass v + b * Discrete.mass w := by
  have hsum : Summable (fun j => u j + (a * v j + b * w j)) :=
    hu.add ((hv.mul_left a).add (hw.mul_left b))
  change (∑' j : ℕ, (u j + a * v j + b * w j)) = _
  calc
    _ = (∑' j : ℕ, (u j + (a * v j + b * w j))) := by
      apply congrArg tsum
      funext j
      ring
    _ = (∑' j : ℕ, u j) + ∑' j : ℕ, (a * v j + b * w j) :=
      hu.tsum_add ((hv.mul_left a).add (hw.mul_left b))
    _ = (∑' j : ℕ, u j) + (∑' j : ℕ, a * v j) + ∑' j : ℕ, b * w j := by
      rw [Summable.tsum_add (hv.mul_left a) (hw.mul_left b)]
      ring
    _ = _ := by
      rw [Summable.tsum_mul_left a hv, Summable.tsum_mul_left b hw]
      dsimp [Discrete.mass]

private theorem firstMoment_add_smul_add_smul {u v w : Discrete.Kernel} {a b : ℝ}
    (hu : Summable (fun j : ℕ => (j : ℝ) * u j))
    (hv : Summable (fun j : ℕ => (j : ℝ) * v j))
    (hw : Summable (fun j : ℕ => (j : ℝ) * w j)) :
    Discrete.firstMoment (fun j => u j + a * v j + b * w j) =
      Discrete.firstMoment u + a * Discrete.firstMoment v + b * Discrete.firstMoment w := by
  have hvaS : Summable (fun j : ℕ => (j : ℝ) * (a * v j)) := by
    apply (hv.mul_left a).congr
    intro j
    ring
  have hwaS : Summable (fun j : ℕ => (j : ℝ) * (b * w j)) := by
    apply (hw.mul_left b).congr
    intro j
    ring
  have hsum : Summable (fun j : ℕ => (j : ℝ) * u j +
      ((j : ℝ) * (a * v j) + (j : ℝ) * (b * w j))) :=
    hu.add (hvaS.add hwaS)
  calc
    _ = (∑' j : ℕ, ((j : ℝ) * u j +
        ((j : ℝ) * (a * v j) + (j : ℝ) * (b * w j)))) := by
      apply congrArg tsum; funext j; dsimp [Discrete.firstMoment]; ring
    _ = (∑' j : ℕ, (j : ℝ) * u j) +
        ∑' j : ℕ, ((j : ℝ) * (a * v j) + (j : ℝ) * (b * w j)) :=
      hu.tsum_add (hvaS.add hwaS)
    _ = _ := by
      rw [Summable.tsum_add hvaS hwaS]
      have hva : (∑' j : ℕ, (j : ℝ) * (a * v j)) = a * Discrete.firstMoment v := by
        calc
          _ = ∑' j : ℕ, a * ((j : ℝ) * v j) := by congr 1; funext j; ring
          _ = _ := Summable.tsum_mul_left a hv
      have hwa : (∑' j : ℕ, (j : ℝ) * (b * w j)) = b * Discrete.firstMoment w := by
        calc
          _ = ∑' j : ℕ, b * ((j : ℝ) * w j) := by congr 1; funext j; ring
          _ = _ := Summable.tsum_mul_left b hw
      rw [hva, hwa]
      change Discrete.firstMoment u + _ = _
      ring

theorem mass_correctedSampledOptimizer (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    (hdet : sampledBumpDet L hL h ≠ 0) :
    Discrete.mass (correctedSampledOptimizer L hL h) = 1 := by
  let f := sampledKernel h (optimizerProfile L)
  let l := sampledKernel h (optimizerBumpLeft L hL)
  let r := sampledKernel h (optimizerBumpRight L hL)
  have hf := sampledKernel_summable hh (optimizerSupport_pos hL).le
    (fun x hx => optimizerProfile_eq_zero_of_support_le hL hx)
  have hl := sampledKernel_summable hh (optimizerBumpHorizon_pos L hL).le
    (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)
  have hr := sampledKernel_summable hh (optimizerBumpHorizon_pos L hL).le
    (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)
  rw [show correctedSampledOptimizer L hL h = fun (j : ℕ) => f j +
     optimizerCorrectionLeft L hL h * l j + optimizerCorrectionRight L hL h * r j by
       funext j; rfl]
  rw [mass_add_smul_add_smul hf hl hr]
  change Discrete.mass f + optimizerCorrectionLeft L hL h * Discrete.mass l +
    optimizerCorrectionRight L hL h * Discrete.mass r = 1
  rw [show Discrete.mass l = sampledBumpMassLeft L hL h by rfl,
    show Discrete.mass r = sampledBumpMassRight L hL h by rfl]
  calc
    _ = Discrete.mass f + (optimizerCorrectionLeft L hL h * sampledBumpMassLeft L hL h +
        optimizerCorrectionRight L hL h * sampledBumpMassRight L hL h) := by ring
    _ = 1 := by
      have he := sampledBumpSolveLeft_eq L hL h
        (optimizerSampledMassResidual L hL h) (optimizerSampledMomentResidual L hL h) hdet
      simp only [optimizerCorrectionLeft, optimizerCorrectionRight]
      simp only [optimizerSampledMassResidual]
      rw [show optimizerSampledMassResidual L hL h =
        1 - Discrete.mass (sampledKernel h (optimizerProfile L)) by rfl] at he
      dsimp [f]
      ring_nf at he ⊢
      linarith [he]

theorem firstMoment_correctedSampledOptimizer (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    (hdet : sampledBumpDet L hL h ≠ 0) :
    h * Discrete.firstMoment (correctedSampledOptimizer L hL h) = L := by
  let f := sampledKernel h (optimizerProfile L)
  let l := sampledKernel h (optimizerBumpLeft L hL)
  let r := sampledKernel h (optimizerBumpRight L hL)
  have hf := sampledKernel_firstMoment_summable hh (optimizerSupport_pos hL).le
    (fun x hx => optimizerProfile_eq_zero_of_support_le hL hx)
  have hl := sampledKernel_firstMoment_summable hh (optimizerBumpHorizon_pos L hL).le
    (fun x hx => optimizerBumpLeft_eq_zero_of_horizon_le L hL hx)
  have hr := sampledKernel_firstMoment_summable hh (optimizerBumpHorizon_pos L hL).le
    (fun x hx => optimizerBumpRight_eq_zero_of_horizon_le L hL hx)
  rw [show correctedSampledOptimizer L hL h = fun j => f j +
    optimizerCorrectionLeft L hL h * l j + optimizerCorrectionRight L hL h * r j by
      funext j; rfl]
  rw [firstMoment_add_smul_add_smul hf hl hr]
  change h * (Discrete.firstMoment f + optimizerCorrectionLeft L hL h *
    Discrete.firstMoment l + optimizerCorrectionRight L hL h * Discrete.firstMoment r) = L
  calc
    _ = h * Discrete.firstMoment f +
        (optimizerCorrectionLeft L hL h * (h * Discrete.firstMoment l) +
          optimizerCorrectionRight L hL h * (h * Discrete.firstMoment r)) := by ring
    _ = L := by
      rw [show h * Discrete.firstMoment l = sampledBumpMomentLeft L hL h by rfl,
        show h * Discrete.firstMoment r = sampledBumpMomentRight L hL h by rfl]
      have he := sampledBumpSolveRight_eq L hL h
        (optimizerSampledMassResidual L hL h) (optimizerSampledMomentResidual L hL h) hdet
      simp only [optimizerCorrectionLeft, optimizerCorrectionRight]
      simp only [optimizerSampledMomentResidual]
      rw [show optimizerSampledMomentResidual L hL h =
        L - h * Discrete.firstMoment (sampledKernel h (optimizerProfile L)) by rfl] at he
      dsimp [f]
      ring_nf at he ⊢
      linarith [he]

theorem exists_pos_correctedSampledOptimizer_constraints (L : ℝ) (hL : 0 < L) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      Discrete.mass (correctedSampledOptimizer L hL h) = 1 ∧
      h * Discrete.firstMoment (correctedSampledOptimizer L hL h) = L := by
  obtain ⟨h₀, hh₀, hb⟩ := exists_sampledBumpDet_lower_bound L hL
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hh₀
  have hdet : sampledBumpDet L hL h ≠ 0 := by
    apply ne_of_gt
    have hpos : 0 < (optimizerBumpMassLeft L hL * optimizerBumpMomentRight L hL -
        optimizerBumpMassRight L hL * optimizerBumpMomentLeft L hL) / 2 := by
      exact div_pos (optimizerBumpDet_pos L hL) (by norm_num)
    exact lt_of_lt_of_le hpos (hb hh hh₀)
  exact ⟨mass_correctedSampledOptimizer L hL hh hdet,
    firstMoment_correctedSampledOptimizer L hL hh hdet⟩

theorem integrable_optimizerBumpLeft (L : ℝ) (hL : 0 < L) :
    Integrable (optimizerBumpLeft L hL) :=
  ((contDiff_optimizerBumpLeft L hL).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpLeft L hL))

theorem integrable_optimizerBumpRight (L : ℝ) (hL : 0 < L) :
    Integrable (optimizerBumpRight L hL) :=
  ((contDiff_optimizerBumpRight L hL).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpRight L hL))

theorem integrable_optimizerBumpLeft_moment (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => x * optimizerBumpLeft L hL x) :=
  ((continuous_id.mul (contDiff_optimizerBumpLeft L hL).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpLeft L hL).mul_left)

theorem integrable_optimizerBumpRight_moment (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => x * optimizerBumpRight L hL x) :=
  ((continuous_id.mul (contDiff_optimizerBumpRight L hL).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpRight L hL).mul_left)

theorem integrable_optimizerBumpLeft_sq (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => optimizerBumpLeft L hL x ^ 2) := by
  exact ((contDiff_optimizerBumpLeft L hL).continuous.mul
    (contDiff_optimizerBumpLeft L hL).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpLeft L hL).mul_left |>.congr
      (Filter.Eventually.of_forall fun x => by simp [pow_two])

theorem integrable_optimizerBumpRight_sq (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => optimizerBumpRight L hL x ^ 2) := by
  exact ((contDiff_optimizerBumpRight L hL).continuous.mul
    (contDiff_optimizerBumpRight L hL).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_optimizerBumpRight L hL).mul_left |>.congr
      (Filter.Eventually.of_forall fun x => by simp [pow_two])

theorem integrable_optimizerBumpLeft_deriv_sq (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => (deriv (optimizerBumpLeft L hL) x) ^ 2) := by
  exact (((contDiff_optimizerBumpLeft L hL).continuous_deriv (by norm_num)).mul
    ((contDiff_optimizerBumpLeft L hL).continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
    ((hasCompactSupport_optimizerBumpLeft L hL).deriv.mul_left) |>.congr
      (Filter.Eventually.of_forall fun x => by simp [pow_two])

theorem integrable_optimizerBumpRight_deriv_sq (L : ℝ) (hL : 0 < L) :
    Integrable (fun x => (deriv (optimizerBumpRight L hL) x) ^ 2) := by
  exact (((contDiff_optimizerBumpRight L hL).continuous_deriv (by norm_num)).mul
    ((contDiff_optimizerBumpRight L hL).continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
    ((hasCompactSupport_optimizerBumpRight L hL).deriv.mul_left) |>.congr
      (Filter.Eventually.of_forall fun x => by simp [pow_two])

private theorem exists_optimizerBumpSupport_amplitude (L : ℝ) (hL : 0 < L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ optimizerBumpSupport L hL,
      |optimizerBumpLeft L hL x| + |optimizerBumpRight L hL x| ≤ B := by
  let g : ℝ → ℝ := fun x => |optimizerBumpLeft L hL x| + |optimizerBumpRight L hL x|
  have hg : ContinuousOn g (optimizerBumpSupport L hL) := by
    dsimp [g]
    exact ((contDiff_optimizerBumpLeft L hL).continuous.continuousOn.abs.add
      (contDiff_optimizerBumpRight L hL).continuous.continuousOn.abs)
  obtain ⟨B, hB⟩ := isCompact_optimizerBumpSupport L hL |>.exists_bound_of_continuousOn hg
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx
  have h := hB x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at h
  exact le_trans h (le_max_left _ _)

theorem exists_pos_correctedSampledOptimizer_nonnegative (L : ℝ) (hL : 0 < L) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      ∀ j : ℕ, 0 ≤ correctedSampledOptimizer L hL h j := by
  obtain ⟨m, hm, hmargin⟩ := exists_optimizerBump_profile_margin L hL
  obtain ⟨B, hB, hBbound⟩ := exists_optimizerBumpSupport_amplitude L hL
  obtain ⟨hc, C, hhc, hC, hcoeff⟩ := exists_optimizerCorrection_abs_sum_bound L hL
  let d : ℝ := m / (B * C + 1)
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos hm (by nlinarith [mul_nonneg hB hC])
  refine ⟨min (min hc 1) (min d (optimizerSupport L)), ?_, ?_⟩
  · exact lt_min (lt_min hhc (by norm_num)) (lt_min hd (optimizerSupport_pos hL))
  intro h hh hh₀ j
  let x : ℝ := (j : ℝ) * h
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h1 : h ≤ 1 := le_trans hh₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcoeff' := hcoeff hh (le_trans hh₀ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hsmall : h ^ 2 * C * B ≤ m := by
    have hs : h ^ 2 ≤ h := by nlinarith
    have hd' : h ≤ m / (B * C + 1) := le_trans hh₀
      (le_trans (min_le_right _ _) (min_le_left _ _))
    have hm' : h * (B * C + 1) ≤ m :=
      (le_div_iff₀ (by nlinarith [mul_nonneg hB hC])).mp hd'
    calc
      h ^ 2 * C * B ≤ h * C * B := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hC) hB
      _ ≤ h * (B * C + 1) := by nlinarith
      _ ≤ m := hm'
  by_cases hxs : x ∈ optimizerBumpSupport L hL
  · have hcorr : |optimizerCorrectionLeft L hL h * optimizerBumpLeft L hL x +
        optimizerCorrectionRight L hL h * optimizerBumpRight L hL x| ≤ m := by
      calc
        _ ≤ (|optimizerCorrectionLeft L hL h| + |optimizerCorrectionRight L hL h|) *
            (|optimizerBumpLeft L hL x| + |optimizerBumpRight L hL x|) := by
          calc
            _ ≤ |optimizerCorrectionLeft L hL h * optimizerBumpLeft L hL x| +
                |optimizerCorrectionRight L hL h * optimizerBumpRight L hL x| := by
              exact abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
            _ ≤ _ := by
              nlinarith [mul_nonneg (abs_nonneg (optimizerCorrectionLeft L hL h))
                (abs_nonneg (optimizerBumpRight L hL x)),
                mul_nonneg (abs_nonneg (optimizerCorrectionRight L hL h))
                (abs_nonneg (optimizerBumpLeft L hL x))]
        _ ≤ h ^ 2 * C * B := by
          exact mul_le_mul hcoeff' (hBbound x hxs) (by positivity) (by positivity)
        _ ≤ m := hsmall
    simp only [correctedSampledOptimizer, sampledKernel_apply]
    have hb : 0 ≤ optimizerProfile L x +
        (optimizerCorrectionLeft L hL h * optimizerBumpLeft L hL x +
          optimizerCorrectionRight L hL h * optimizerBumpRight L hL x) := by
      nlinarith [hmargin x hxs, neg_le_of_abs_le hcorr]
    dsimp [x] at hb ⊢
    nlinarith [mul_nonneg (le_of_lt hh) hb]
  · have hl := image_eq_zero_of_notMem_tsupport (fun hx' => hxs (Or.inl hx'))
    have hr := image_eq_zero_of_notMem_tsupport (fun hx' => hxs (Or.inr hx'))
    simp only [correctedSampledOptimizer, sampledKernel_apply]
    rw [hl, hr, mul_zero, mul_zero, add_zero, mul_zero, add_zero]
    have hn := (optimizer_isAdmissible hL).nonnegative x (by simp [halfLine, hx])
    rw [continuousRep_optimizer hL] at hn
    exact mul_nonneg (le_of_lt hh) hn

theorem exists_pos_correctedSampledOptimizer_constraints_nonnegative
    (L : ℝ) (hL : 0 < L) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      Discrete.mass (correctedSampledOptimizer L hL h) = 1 ∧
      h * Discrete.firstMoment (correctedSampledOptimizer L hL h) = L ∧
      (∀ j, 0 ≤ correctedSampledOptimizer L hL h j) := by
  obtain ⟨hc, hhc, hconstraints⟩ := exists_pos_correctedSampledOptimizer_constraints L hL
  obtain ⟨hn, hhn, hnonneg⟩ := exists_pos_correctedSampledOptimizer_nonnegative L hL
  refine ⟨min hc hn, by positivity, ?_⟩
  intro h hh hh₀
  have hhc' := hconstraints hh (le_trans hh₀ (min_le_left _ _))
  have hhn' := hnonneg hh (le_trans hh₀ (min_le_right _ _))
  exact ⟨hhc'.1, hhc'.2, hhn'⟩


end RayleighKernel.Analysis.HalfLineH1
