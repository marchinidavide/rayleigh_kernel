import RayleighKernel.Probability.SquareSummableFilter
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal NNReal
namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

structure IsGaussianWhiteInput (r : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop extends
    IsWhiteInput r μ where
  gaussian : IsGaussianProcess r μ

theorem finiteSignal_hasGaussianLaw {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} (hr : IsGaussianWhiteInput r μ) (t : ℤ) :
    HasGaussianLaw (finiteSignal N w r t) μ := by
  have hg : IsGaussianProcess
      (fun j : ℕ => w j • r (t - (j : ℤ))) μ :=
    IsGaussianProcess.smul (fun j : ℕ => w j)
      (hr.gaussian.comp_right (fun j : ℕ => t - (j : ℤ)))
  have hs := hg.hasGaussianLaw_fun_sum (I := Finset.range N)
  convert hs using 1
  ext ω
  simp [finiteSignal, smul_eq_mul]

theorem finiteSignal_map_eq_gaussianReal {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hr : IsGaussianWhiteInput r μ) (t : ℤ) :
    μ.map (finiteSignal N w r t) =
      gaussianReal 0 (Real.toNNReal (∑ j ∈ Finset.range N, (w j) ^ 2)) := by
  rw [(finiteSignal_hasGaussianLaw hr t).map_eq_gaussianReal]
  rw [finiteSignal_expectation_zero hr.toIsWhiteInput t,
    finiteSignal_variance hr.toIsWhiteInput t]

theorem finiteSignal_difference_hasGaussianLaw {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} (hr : IsGaussianWhiteInput r μ)
    (t : ℤ) (hwN : w N = 0) :
    HasGaussianLaw
      (fun ω => finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω) μ := by
  rw [finiteSignal_sub_previous N w r t hwN]
  exact finiteSignal_hasGaussianLaw hr t

theorem finiteSignal_difference_map_eq_gaussianReal {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hr : IsGaussianWhiteInput r μ) (t : ℤ) (hwN : w N = 0) :
    μ.map (fun ω => finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω) =
      gaussianReal 0
        (Real.toNNReal (∑ j ∈ Finset.range (N + 1), (Discrete.difference w j) ^ 2)) := by
  rw [(finiteSignal_difference_hasGaussianLaw hr t hwN).map_eq_gaussianReal]
  rw [finiteSignal_sub_previous N w r t hwN]
  rw [finiteSignal_expectation_zero hr.toIsWhiteInput t,
    finiteSignal_variance hr.toIsWhiteInput t]

theorem infiniteSignalLp_hasGaussianLaw [IsProbabilityMeasure μ] {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    HasGaussianLaw (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) μ := by
  let XN : ℕ → Ω → ℝ := fun N => finiteSignal N w r t
  let X : Ω → ℝ := infiniteSignalLp hr.toIsWhiteInput w t
  have hLp : Tendsto (fun N => partialSum hr.toIsWhiteInput w t N) atTop
      (𝓝 (infiniteSignalLp hr.toIsWhiteInput w t)) :=
    partialSum_tendsto hr.toIsWhiteInput w t hw
  have htm : TendstoInMeasure μ (fun N => (partialSum hr.toIsWhiteInput w t N : Ω → ℝ))
      atTop (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hLp
  have heq : ∀ N, XN N =ᵐ[μ] (partialSum hr.toIsWhiteInput w t N : Ω → ℝ) := by
    intro N
    have h := finiteSignal_toLp_eq_sum hr.toIsWhiteInput N w t
    have hf := (finiteSignal_memLp (N := N) (w := w) (r := r) (μ := μ)
      hr.toIsWhiteInput t).coeFn_toLp
    filter_upwards [hf] with ω h₁
    change finiteSignal N w r t ω = _
    rw [← h₁]
    exact congrFun (congrArg (fun f : Lp ℝ 2 μ => (f : Ω → ℝ)) h) ω
  have htm' : TendstoInMeasure μ XN atTop X :=
    htm.congr_left (fun N => (heq N).symm)
  have hd1 : TendstoInDistribution XN atTop X (fun _ => μ) μ :=
    htm'.tendstoInDistribution (fun N =>
      (finiteSignal_memLp (N := N) (w := w) (r := r) (μ := μ)
        hr.toIsWhiteInput t).aemeasurable)
  let ν : Measure ℝ := gaussianReal 0 (Real.toNNReal (Discrete.squareEnergy w))
  have hchar : ∀ u : ℝ, Tendsto
      (fun N => charFun ((fun _ : ℕ => μ) N |>.map (XN N)) u) atTop
      (𝓝 (charFun (ν.map id) u)) := by
    intro u
    simp only [Measure.map_id]
    rw [charFun_gaussianReal]
    simp_rw [show XN = (fun N => finiteSignal N w r t) from rfl]
    simp_rw [finiteSignal_map_eq_gaussianReal hr t, charFun_gaussianReal]
    have hs : Tendsto (fun N => ∑ j ∈ Finset.range N, (w j) ^ 2) atTop
        (𝓝 (Discrete.squareEnergy w)) := by
      simpa [Discrete.squareEnergy] using hw.hasSum.tendsto_sum_nat
    have hsc : Tendsto (fun N =>
        (Real.toNNReal (∑ j ∈ Finset.range N, (w j) ^ 2) : ℝ)) atTop
        (𝓝 (Real.toNNReal (Discrete.squareEnergy w) : ℝ)) := by
      exact NNReal.tendsto_coe.2 (tendsto_real_toNNReal hs)
    have hc : Continuous (fun x : ℝ => Complex.exp (-(x * u ^ 2) / 2)) := by fun_prop
    have hh := hc.continuousAt.tendsto.comp hsc
    convert hh using 1
    · funext N
      have hN : 0 ≤ ∑ j ∈ Finset.range N, w j ^ 2 :=
        Finset.sum_nonneg (fun j hj => sq_nonneg _)
      simp [max_eq_left hN, mul_comm]
      ring_nf
    · have hS : 0 ≤ Discrete.squareEnergy w :=
        tsum_nonneg (fun j => sq_nonneg (w j))
      simp [max_eq_left hS, mul_comm]
      ring_nf
  have hd2 : TendstoInDistribution XN atTop id (fun _ => μ) ν :=
    TendstoInDistribution.of_tendsto_charFun
      (fun N => (finiteSignal_memLp (N := N) (w := w) (r := r) (μ := μ)
        hr.toIsWhiteInput t).aemeasurable)
      measurable_id.aemeasurable hchar
  have hmap : μ.map X = ν := by
    rw [tendstoInDistribution_unique XN hd1 hd2, Measure.map_id]
  let _ : IsGaussian (μ.map X) := by rw [hmap]; infer_instance
  exact IsGaussian.hasGaussianLaw
    (Lp.aestronglyMeasurable (infiniteSignalLp hr.toIsWhiteInput w t)).aemeasurable

theorem infiniteSignalLp_map_eq_gaussianReal [IsProbabilityMeasure μ]
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ} (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    μ.map (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) =
      gaussianReal 0 (Real.toNNReal (Discrete.squareEnergy w)) := by
  exact (infiniteSignalLp_hasGaussianLaw hr t hw).map_eq_gaussianReal.trans
    (by rw [infiniteSignalLp_integral_eq_zero hr.toIsWhiteInput w t hw,
      infiniteSignalLp_variance hr.toIsWhiteInput w t hw])

theorem infiniteSignalLp_difference_hasGaussianLaw [IsProbabilityMeasure μ]
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ} (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2)) :
    HasGaussianLaw (fun ω =>
      (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
      (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω) μ := by
  apply (infiniteSignalLp_hasGaussianLaw (w := Discrete.difference w) hr t hdw).congr
  exact (infiniteSignalLp_difference_ae hr.toIsWhiteInput w t hw hdw).symm

theorem infiniteSignalLp_difference_map_eq_gaussianReal [IsProbabilityMeasure μ]
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ} (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2)) :
    μ.map (fun ω =>
      (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
      (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω) =
      gaussianReal 0 (Real.toNNReal (Discrete.differenceEnergy w)) := by
  rw [(infiniteSignalLp_difference_hasGaussianLaw hr t hw hdw).map_eq_gaussianReal]
  rw [integral_sub
    ((Lp.memLp (infiniteSignalLp hr.toIsWhiteInput w t)).integrable one_le_two)
    ((Lp.memLp (infiniteSignalLp hr.toIsWhiteInput w (t - 1))).integrable one_le_two),
    infiniteSignalLp_integral_eq_zero hr.toIsWhiteInput w t hw,
    infiniteSignalLp_integral_eq_zero hr.toIsWhiteInput w (t - 1) hw,
    infiniteSignalLp_difference_variance hr.toIsWhiteInput w t hw hdw]
  simp

lemma integral_mul_exp_neg_mul_sq_Ioi {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Set.Ioi 0, x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hderiv : ∀ x : ℝ, x ∈ Set.Ici 0 →
      HasDerivAt (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
        (x * Real.exp (-b * x ^ 2)) x := by
    intro x hx
    convert ((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹) using 1
    field_simp
    ring
  have hlim : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ ?_
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (integrable_mul_exp_neg_mul_sq hb).integrableOn hlim using 1
  simp

theorem integral_abs_standardGaussian :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal_def]
  let f : ℝ → ℝ := fun x => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
  have hf : Integrable f := integrable_mul_exp_neg_mul_sq (by norm_num)
  have habs' : ∫ x : ℝ, f |x| = 2 := by
    calc
      ∫ x : ℝ, f |x| = (2 : ℝ) * ∫ x : ℝ in Set.Ioi 0, f x := integral_comp_abs
      _ = 2 := by
        rw [show f = (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by rfl,
          integral_mul_exp_neg_mul_sq_Ioi (b := (1 / 2 : ℝ)) (by norm_num)]
        norm_num
  have habs : ∫ x : ℝ, |x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = 2 := by
    convert habs' using 1
    apply congrArg (fun y : ℝ => y)
    simp [f, sq_abs]
  have hfun : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / 2) * |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * f |x|) := by
    funext x
    simp [f, sq_abs]
    ring_nf
  norm_num only [NNReal.coe_one, mul_one]
  rw [hfun, integral_const_mul, habs']
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  rw [Real.sqrt_div (by positivity : 0 ≤ (2 : ℝ))]
  rw [← Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
  field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  ring_nf
  norm_num

theorem integral_abs_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, |x| ∂gaussianReal 0 v =
      Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var]
  let c : ℝ := Real.sqrt (v : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Real.sqrt_ne_zero'.2 (by positivity)
  have hmap := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) c
  have hvar : (.mk (c ^ 2) (sq_nonneg c) * (1 : ℝ≥0)) = v := by
    apply Subtype.ext
    simp [c, Real.sq_sqrt (show 0 ≤ (v : ℝ) by positivity)]
  rw [hvar] at hmap
  simp only [mul_zero] at hmap
  rw [← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  · have heq : (fun x : ℝ => |c * x|) = (fun x => c * |x|) := by
      funext x
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [heq, integral_const_mul, integral_abs_standardGaussian]
    dsimp [c]
    ring

theorem integral_abs_gaussianReal_sq (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ x : ℝ, |x| ∂gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) =
      Real.sqrt (2 / Real.pi) * τ := by
  have hs : Real.sqrt (((⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) : ℝ)) = τ := by
    change Real.sqrt (τ ^ 2) = τ
    exact Real.sqrt_sq hτ
  have h := integral_abs_gaussianReal (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0)
  convert h using 1
  exact congrArg (fun z : ℝ => Real.sqrt (2 / Real.pi) * z) hs.symm

theorem integral_abs_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) :
    ∫ ω, |X ω| ∂μ = Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  calc
    ∫ ω, |X ω| ∂μ = ∫ x : ℝ, |x| ∂gaussianReal 0 v :=
      hX.integral_comp (f := fun x : ℝ => |x|) (by fun_prop)
    _ = _ := integral_abs_gaussianReal v

theorem infiniteSignalLp_integral_abs [IsProbabilityMeasure μ]
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ}
    (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j)^2)) :
    ∫ ω, |(infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω| ∂μ =
      Real.sqrt (2 / Real.pi) * Real.sqrt (Discrete.squareEnergy w) := by
  have hS : 0 ≤ Discrete.squareEnergy w := tsum_nonneg (fun j => sq_nonneg (w j))
  let hlaw : HasLaw (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ)
      (gaussianReal 0 (Real.toNNReal (Discrete.squareEnergy w))) μ := {
    aemeasurable := (Lp.aestronglyMeasurable
      (infiniteSignalLp hr.toIsWhiteInput w t)).aemeasurable
    map_eq := infiniteSignalLp_map_eq_gaussianReal hr t hw }
  simpa [Real.toNNReal_of_nonneg hS] using
    (integral_abs_of_hasLaw_gaussianReal
      (X := (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ))
      (v := Real.toNNReal (Discrete.squareEnergy w))
      hlaw)

theorem infiniteSignalLp_difference_integral_abs [IsProbabilityMeasure μ]
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ}
    (hr : IsGaussianWhiteInput r μ) (t : ℤ)
    (hw : Summable (fun j => (w j)^2))
    (hdw : Summable (fun j => (Discrete.difference w j)^2)) :
    ∫ ω, |(infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
      (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω| ∂μ =
      Real.sqrt (2 / Real.pi) * Real.sqrt (Discrete.differenceEnergy w) := by
  have hS : 0 ≤ Discrete.differenceEnergy w :=
    tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j))
  let hlaw : HasLaw (fun ω : Ω =>
      (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
        (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω)
      (gaussianReal 0 (Real.toNNReal (Discrete.differenceEnergy w))) μ := {
    aemeasurable := (infiniteSignalLp_difference_hasGaussianLaw hr t hw hdw).aemeasurable
    map_eq := infiniteSignalLp_difference_map_eq_gaussianReal hr t hw hdw }
  simpa [Real.toNNReal_of_nonneg hS] using
    (integral_abs_of_hasLaw_gaussianReal
      (X := fun ω : Ω =>
        (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
          (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω)
      (v := Real.toNNReal (Discrete.differenceEnergy w))
      hlaw)

end RayleighKernel.Probability
