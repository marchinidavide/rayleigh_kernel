import RayleighKernel.Probability.NormalAbsoluteMoment
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal NNReal
namespace RayleighKernel.Probability

private theorem sqrt_sq_of_nonneg {Ω : Type*} (V : Ω → ℝ)
    (hVnonneg : ∀ x, 0 ≤ V x) :
    ∀ x, (Real.sqrt (V x)) ^ 2 = V x := by
  intro x
  exact Real.sq_sqrt (hVnonneg x)

private theorem sqrt_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (V : Ω → ℝ) (hVmeas : Measurable V)
    (hVnonneg : ∀ x, 0 ≤ V x) (hVint : Integrable V μ) :
    MemLp (fun x => Real.sqrt (V x)) 2 μ := by
  have hsquare : Integrable (fun x => (Real.sqrt (V x)) ^ 2) μ := by
    simpa [sqrt_sq_of_nonneg V hVnonneg] using hVint
  exact (memLp_two_iff_integrable_sq hVmeas.sqrt.aestronglyMeasurable).2 hsquare

def commonScaleGaussianInput {ΩV ΩG : Type*}
    (V : ΩV → ℝ) (G : ℤ → ΩG → ℝ) : ℤ → ΩV × ΩG → ℝ :=
  fun k p => Real.sqrt (V p.1) * G k p.2

def commonScaleGaussianReference {ΩV ΩG : Type*}
    (V : ΩV → ℝ) (G : ℤ → ΩG → ℝ) : ΩV × ΩG → ℝ :=
  fun p => Real.sqrt (V p.1) * G 0 p.2

theorem finiteSignal_identDistrib_const_mul
    {ΩG : Type*} [MeasurableSpace ΩG] {νG : Measure ΩG}
    [IsProbabilityMeasure νG] (G : ℤ → ΩG → ℝ)
    (hG : IsGaussianWhiteInput G νG)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    IdentDistrib (finiteSignal N w G t)
      (fun z => Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) * G 0 z) νG νG := by
  let S : ℝ := ∑ j ∈ Finset.range N, (w j)^2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hleft : HasLaw (finiteSignal N w G t)
      (gaussianReal 0 (Real.toNNReal S)) νG := by
    refine ⟨(finiteSignal_memLp hG.toIsWhiteInput t).aemeasurable, ?_⟩
    simpa [S] using finiteSignal_map_eq_gaussianReal hG t
  have h0 : HasLaw (G 0) (gaussianReal 0 1) νG :=
    ⟨(hG.memLp 0).aemeasurable, by
      rw [(hG.gaussian.hasGaussianLaw_eval 0).map_eq_gaussianReal,
        hG.centered 0,
        ProbabilityTheory.variance_of_integral_eq_zero
          (hG.memLp 0).aemeasurable (hG.centered 0)]
      have hm : (∫ ω, (G 0 ω)^2 ∂νG) = 1 := by
        simpa [pow_two] using hG.secondMoment 0 0
      rw [hm]
      simp⟩
  have hright0 := gaussianReal_const_mul h0 (Real.sqrt S)
  have hvar : (.mk ((Real.sqrt S)^2) (sq_nonneg (Real.sqrt S)) * (1 : ℝ≥0)) =
      Real.toNNReal S := by
    apply Subtype.ext
    simp [Real.sq_sqrt hS, Real.toNNReal_of_nonneg hS]
  have hright : HasLaw (fun z => Real.sqrt S * G 0 z)
      (gaussianReal 0 (Real.toNNReal S)) νG := by
    rw [hvar] at hright0
    simpa using hright0
  simpa [S] using hleft.identDistrib hright

private theorem pair_identDistrib_of_snd
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V)
    {X Y : ΩG → ℝ} (hXY : IdentDistrib X Y νG νG) :
    IdentDistrib (fun p : ΩV × ΩG => (V p.1, X p.2))
      (fun p : ΩV × ΩG => (V p.1, Y p.2))
      (νV.prod νG) (νV.prod νG) := by
  have hX : AEMeasurable X νG := hXY.aemeasurable_fst
  have hY : AEMeasurable Y νG := hXY.aemeasurable_snd
  have hfst : AEMeasurable (fun p : ΩV × ΩG => V p.1) (νV.prod νG) :=
    (hVmeas.comp measurable_fst).aemeasurable
  have hX' : AEMeasurable X
      ((νV.prod νG).map (fun p : ΩV × ΩG => p.2)) := by
    rw [measurePreserving_snd.map_eq]
    exact hX
  have hY' : AEMeasurable Y
      ((νV.prod νG).map (fun p : ΩV × ΩG => p.2)) := by
    rw [measurePreserving_snd.map_eq]
    exact hY
  have hsndX : AEMeasurable (fun p : ΩV × ΩG => X p.2) (νV.prod νG) :=
    hX'.comp_aemeasurable measurable_snd.aemeasurable
  have hsndY : AEMeasurable (fun p : ΩV × ΩG => Y p.2) (νV.prod νG) :=
    hY'.comp_aemeasurable measurable_snd.aemeasurable
  refine
    { aemeasurable_fst := hfst.prodMk hsndX
      aemeasurable_snd := hfst.prodMk hsndY
      map_eq := ?_ }
  have hmap : ∀ (Z : ΩG → ℝ) (hZ : AEMeasurable Z νG),
      Measure.map (fun p : ΩV × ΩG => (V p.1, Z p.2)) (νV.prod νG) =
        (νV.map V).prod (νG.map Z) := by
    intro Z hZ
    have heq : (fun p : ΩV × ΩG => (V p.1, Z p.2)) =ᵐ[νV.prod νG]
        (fun p => (V p.1, hZ.mk Z p.2)) := by
      have hz : Z =ᵐ[(νV.prod νG).map (fun p : ΩV × ΩG => p.2)] hZ.mk := by
        rw [measurePreserving_snd.map_eq]
        exact hZ.ae_eq_mk
      filter_upwards [ae_eq_comp measurable_snd.aemeasurable hz] with p hp
      exact congrArg (fun x => (V p.1, x)) hp
    rw [Measure.map_congr heq, show (fun p : ΩV × ΩG =>
        (V p.1, hZ.mk Z p.2)) = Prod.map V (hZ.mk Z) by rfl,
      ← Measure.map_prod_map νV νG hVmeas hZ.measurable_mk]
    exact congrArg (fun m => (νV.map V).prod m)
      (Measure.map_congr hZ.ae_eq_mk.symm)
  rw [hmap X hX, hmap Y hY, hXY.map_eq]

private theorem pair_identDistrib_comp_mul_sqrt
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V)
    {X Y : ΩG → ℝ} (hXY : IdentDistrib X Y νG νG) :
    IdentDistrib
      (fun p : ΩV × ΩG => Real.sqrt (V p.1) * X p.2)
      (fun p : ΩV × ΩG => Real.sqrt (V p.1) * Y p.2)
      (νV.prod νG) (νV.prod νG) := by
  have hp := pair_identDistrib_of_snd (νV := νV) (νG := νG)
    (X := X) (Y := Y) V hVmeas hXY
  have hm : Measurable (fun p : ℝ × ℝ => Real.sqrt p.1 * p.2) := by
    fun_prop
  simpa [Function.comp_def] using hp.comp hm

theorem finiteSignal_commonScale_factorization
    {ΩV ΩG : Type*} (V : ΩV → ℝ) (G : ℤ → ΩG → ℝ)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    finiteSignal N w (commonScaleGaussianInput V G) t =
      fun p => Real.sqrt (V p.1) * finiteSignal N w G t p.2 := by
  funext p
  simp [finiteSignal, commonScaleGaussianInput]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteSignal_commonScale_projection_identDistrib
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V)
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    IdentDistrib
      (finiteSignal N w (commonScaleGaussianInput V G) t)
      (fun p => Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) *
        commonScaleGaussianReference V G p)
      (νV.prod νG) (νV.prod νG) := by
  have hpair := pair_identDistrib_comp_mul_sqrt (νV := νV) (νG := νG)
    V hVmeas (finiteSignal_identDistrib_const_mul G hG N w t)
  have hleft : finiteSignal N w (commonScaleGaussianInput V G) t =
      fun p => Real.sqrt (V p.1) * finiteSignal N w G t p.2 :=
    finiteSignal_commonScale_factorization V G N w t
  have hscale : ∀ p : ΩV × ΩG,
      Real.sqrt (V p.1) *
          (Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) * G 0 p.2) =
        Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) *
          commonScaleGaussianReference V G p := by
    intro p
    simp [commonScaleGaussianReference]
    ring
  rw [hleft]
  exact hpair.trans
    (IdentDistrib.of_ae_eq hpair.aemeasurable_snd
      (Filter.Eventually.of_forall hscale))

theorem commonScaleGaussianReference_memLp
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (G : ℤ → ΩG → ℝ)
    (hG : IsGaussianWhiteInput G νG) :
    MemLp (commonScaleGaussianReference V G) 2 (νV.prod νG) := by
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · change AEStronglyMeasurable
      (fun p => Real.sqrt (V p.1) * G 0 p.2) (νV.prod νG)
    exact (((sqrt_memLp_two V hVmeas hVnonneg hVint).comp_fst νG).aemeasurable.mul
      ((hG.memLp 0).comp_snd νV).aemeasurable).aestronglyMeasurable
  · have hV2 : Integrable V νV := hVint
    have hG2 : Integrable (fun z => (G 0 z)^2) νG := by
      simpa [Real.norm_eq_abs, sq_abs] using
        (hG.memLp 0).integrable_norm_pow' (p := 2)
    convert Integrable.mul_prod hV2 hG2 using 1
    funext p
    simp [commonScaleGaussianReference, mul_pow, sqrt_sq_of_nonneg V hVnonneg]

theorem commonScaleGaussianReference_centered
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (G : ℤ → ΩG → ℝ)
    (hG : IsGaussianWhiteInput G νG) :
    ∫ p, commonScaleGaussianReference V G p ∂(νV.prod νG) = 0 := by
  have _ := hVmeas
  have _ := hVnonneg
  have _ := hVint
  calc
    _ = (∫ v, Real.sqrt (V v) ∂νV) * ∫ z, G 0 z ∂νG := by
      simpa [commonScaleGaussianReference] using
        (integral_prod_mul (μ := νV) (ν := νG)
          (fun v => Real.sqrt (V v)) (G 0))
    _ = 0 := by simp [hG.centered 0]

theorem commonScaleGaussianReference_secondMoment
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1)
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG) :
    ∫ p, (commonScaleGaussianReference V G p)^2 ∂(νV.prod νG) = 1 := by
  have _ := hVmeas
  have _ := hVint
  calc
    _ = ∫ p, V p.1 * (G 0 p.2)^2 ∂(νV.prod νG) := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [commonScaleGaussianReference, mul_pow,
        sqrt_sq_of_nonneg V hVnonneg]
    _ = (∫ v, V v ∂νV) * ∫ z, (G 0 z)^2 ∂νG := by
      exact integral_prod_mul V (fun z => (G 0 z)^2)
    _ = 1 := by
      rw [hVmean]
      have hm : (∫ z, (G 0 z)^2 ∂νG) = 1 := by
        simpa [pow_two] using hG.secondMoment 0 0
      rw [hm]
      simp

theorem commonScaleGaussian_projectionScaleWhite
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1)
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG) :
    ProjectionScaleWhite (commonScaleGaussianInput V G) (νV.prod νG)
      (commonScaleGaussianReference V G) (νV.prod νG) 1 := by
  refine
    { scale_pos := by norm_num
      reference_memLp := commonScaleGaussianReference_memLp V hVmeas hVnonneg hVint G hG
      reference_centered := commonScaleGaussianReference_centered V hVmeas hVnonneg hVint G hG
      reference_secondMoment := commonScaleGaussianReference_secondMoment V hVmeas hVnonneg hVint hVmean G hG
      projection := ?_ }
  intro N w t
  simpa using finiteSignal_commonScale_projection_identDistrib V hVmeas G hG N w t

theorem commonScaleGaussianInput_coordinate_crossSecondMoment
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1)
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG) (s t : ℤ) :
    ∫ p, commonScaleGaussianInput V G s p *
      commonScaleGaussianInput V G t p ∂(νV.prod νG) = if s = t then 1 else 0 := by
  simpa using ProjectionScaleWhite.coordinate_crossSecondMoment
    (commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG) s t

theorem commonScaleGaussianReference_integral_abs
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (G : ℤ → ΩG → ℝ)
    (hG : IsGaussianWhiteInput G νG) :
    ∫ p, |commonScaleGaussianReference V G p| ∂(νV.prod νG) =
      Real.sqrt (2 / Real.pi) * ∫ v, Real.sqrt (V v) ∂νV := by
  have hs := sqrt_memLp_two V hVmeas hVnonneg hVint
  have hsint : Integrable (fun v => Real.sqrt (V v)) νV := hs.integrable one_le_two
  have hgi : Integrable (fun z => |G 0 z|) νG :=
    by simpa [Real.norm_eq_abs] using (hG.memLp 0).integrable one_le_two |>.norm
  calc
    _ = (∫ v, Real.sqrt (V v) ∂νV) * ∫ z, |G 0 z| ∂νG := by
      simpa [commonScaleGaussianReference, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
        (integral_prod_mul (μ := νV) (ν := νG)
          (fun v => Real.sqrt (V v)) (fun z => |G 0 z|))
    _ = (∫ v, Real.sqrt (V v) ∂νV) * Real.sqrt (2 / Real.pi) := by
      have h0 : HasLaw (G 0) (gaussianReal 0 1) νG :=
        ⟨(hG.memLp 0).aemeasurable, by
          rw [(hG.gaussian.hasGaussianLaw_eval 0).map_eq_gaussianReal,
            hG.centered 0,
            ProbabilityTheory.variance_of_integral_eq_zero
              (hG.memLp 0).aemeasurable (hG.centered 0)]
          have hm : (∫ z, (G 0 z)^2 ∂νG) = 1 := by
            simpa [pow_two] using hG.secondMoment 0 0
          rw [hm]
          simp⟩
      rw [integral_abs_of_hasLaw_gaussianReal h0]
      simp
    _ = Real.sqrt (2 / Real.pi) * ∫ v, Real.sqrt (V v) ∂νV := by ring

theorem commonScaleGaussianReference_sqrt_integral_pos
    {ΩV : Type*} [MeasurableSpace ΩV] {νV : Measure ΩV}
    [IsProbabilityMeasure νV]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1) :
    0 < ∫ v, Real.sqrt (V v) ∂νV := by
  have hs := sqrt_memLp_two V hVmeas hVnonneg hVint
  have hsint : Integrable (fun v => Real.sqrt (V v)) νV := hs.integrable one_le_two
  have hnonneg : ∀ v, 0 ≤ Real.sqrt (V v) := fun v => Real.sqrt_nonneg _
  by_contra h
  have hz : ∫ v, Real.sqrt (V v) ∂νV = 0 := le_antisymm (not_lt.mp h) (integral_nonneg hnonneg)
  have hae : (fun v => Real.sqrt (V v)) =ᵐ[νV] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun v => Real.sqrt_nonneg (V v)) hsint).1 hz
  have hvzero : V =ᵐ[νV] 0 := by
    filter_upwards [hae] with v hv
    rw [← sqrt_sq_of_nonneg V hVnonneg v, hv]
    simp
  have hi : (∫ v, V v ∂νV) = 0 := by
    simpa using (integral_congr_ae hvzero)
  linarith

theorem commonScaleGaussianInput_turnoverIsotropicWhite
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1)
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG) :
    TurnoverIsotropicWhite (commonScaleGaussianInput V G) (νV.prod νG) 1
      (Real.sqrt (2 / Real.pi) * ∫ v, Real.sqrt (V v) ∂νV) := by
  refine TurnoverIsotropicWhite.mk (by norm_num) ?_ ?_ ?_ ?_ ?_
  · have hc : 0 < Real.sqrt (2 / Real.pi) := by positivity
    exact mul_pos hc (commonScaleGaussianReference_sqrt_integral_pos V hVmeas hVnonneg hVint hVmean)
  · intro t
    exact (commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG).coordinate_memLp t
  · intro t
    exact (commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG).coordinate_integral t
  · intro N w t
    simpa [one_pow, finiteSquareEnergy] using
      (commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG).projection_secondMoment N w t
  · intro N w t
    have hi := finiteSignal_commonScale_projection_identDistrib
      (νV := νV) (νG := νG) V hVmeas G hG N w t
    have hiabs := hi.comp (by fun_prop : Measurable (fun x : ℝ => |x|))
    have habs : (∫ p, |finiteSignal N w (commonScaleGaussianInput V G) t p| ∂(νV.prod νG)) =
        ∫ p, |Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) *
          commonScaleGaussianReference V G p| ∂(νV.prod νG) := by
      simpa [Function.comp_def] using hiabs.integral_eq
    rw [habs]
    rw [show (fun p => |Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) *
        commonScaleGaussianReference V G p|) =
        (fun p => Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) *
          |commonScaleGaussianReference V G p|) by
      funext p
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] ]
    rw [integral_const_mul,
      commonScaleGaussianReference_integral_abs V hVmeas hVnonneg hVint G hG]
    rw [show finiteSquareEnergy N w = ∑ j ∈ Finset.range N, (w j)^2 by rfl]
    ring

theorem commonScaleGaussianInput_coordinates_not_indep
    {ΩV ΩG : Type*} [MeasurableSpace ΩV] [MeasurableSpace ΩG]
    {νV : Measure ΩV} {νG : Measure ΩG}
    [IsProbabilityMeasure νV] [IsProbabilityMeasure νG]
    (V : ΩV → ℝ) (hVmeas : Measurable V) (hVnonneg : ∀ v, 0 ≤ V v)
    (hVint : Integrable V νV) (hVmean : ∫ v, V v ∂νV = 1)
    (hV2 : MemLp V 2 νV) (hVnonconstant : ¬ V =ᵐ[νV] (fun _ => 1))
    (G : ℤ → ΩG → ℝ) (hG : IsGaussianWhiteInput G νG) :
    ¬ IndepFun (commonScaleGaussianInput V G 0)
      (commonScaleGaussianInput V G 1) (νV.prod νG) := by
  have hGind : IndepFun (G 0) (G 1) νG := by
    apply HasGaussianLaw.indepFun_of_covariance_eq_zero
      (hG.gaussian.hasGaussianLaw_prodMk (s := 0) (t := 1))
    rw [covariance_eq_sub (hG.memLp 0) (hG.memLp 1)]
    rw [hG.secondMoment]
    simp [hG.centered]
  have hGsq : ∫ z, (G 0 z)^2 * (G 1 z)^2 ∂νG = 1 := by
    have hi := hGind.comp (by fun_prop : Measurable (fun x : ℝ => x^2))
      (by fun_prop : Measurable (fun x : ℝ => x^2))
    have hfact := hi.integral_mul_eq_mul_integral
      ((hG.memLp 0).aestronglyMeasurable.pow 2)
      ((hG.memLp 1).aestronglyMeasurable.pow 2)
    have hfact' : (∫ z, (G 0 z)^2 * (G 1 z)^2 ∂νG) =
        (∫ z, (G 0 z)^2 ∂νG) * ∫ z, (G 1 z)^2 ∂νG := by
      simpa [Function.comp_def] using hfact
    rw [show (∫ z, (G 0 z)^2 ∂νG) = 1 by
        simpa [pow_two] using hG.secondMoment 0 0,
      show (∫ z, (G 1 z)^2 ∂νG) = 1 by
        simpa [pow_two] using hG.secondMoment 1 1] at hfact'
    simpa using hfact'
  have hmix : ∫ p, (commonScaleGaussianInput V G 0 p)^2 *
      (commonScaleGaussianInput V G 1 p)^2 ∂(νV.prod νG) =
      ∫ v, V v ^ 2 ∂νV := by
    calc
      _ = ∫ p, V p.1 ^ 2 * ((G 0 p.2)^2 * (G 1 p.2)^2) ∂(νV.prod νG) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp [commonScaleGaussianInput, mul_pow, sqrt_sq_of_nonneg V hVnonneg]
        ring
      _ = (∫ v, V v ^ 2 ∂νV) * ∫ z, (G 0 z)^2 * (G 1 z)^2 ∂νG := by
        exact integral_prod_mul (fun v => V v ^ 2)
          (fun z => (G 0 z)^2 * (G 1 z)^2)
      _ = ∫ v, V v ^ 2 ∂νV := by rw [hGsq, mul_one]
  intro hind
  have hmix_ind := hind.comp (by fun_prop : Measurable (fun x : ℝ => x^2))
    (by fun_prop : Measurable (fun x : ℝ => x^2))
  have h0 := commonScaleGaussianInput_coordinate_crossSecondMoment
    V hVmeas hVnonneg hVint hVmean G hG 0 0
  have h1 := commonScaleGaussianInput_coordinate_crossSecondMoment
    V hVmeas hVnonneg hVint hVmean G hG 1 1
  have hsqind := hmix_ind.integral_mul_eq_mul_integral
    (((commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG).coordinate_memLp 0).aestronglyMeasurable.pow 2)
    (((commonScaleGaussian_projectionScaleWhite V hVmeas hVnonneg hVint hVmean G hG).coordinate_memLp 1).aestronglyMeasurable.pow 2)
  have hsqind' : (∫ p, (commonScaleGaussianInput V G 0 p)^2 *
      (commonScaleGaussianInput V G 1 p)^2 ∂(νV.prod νG)) =
      (∫ p, (commonScaleGaussianInput V G 0 p)^2 ∂(νV.prod νG)) *
        ∫ p, (commonScaleGaussianInput V G 1 p)^2 ∂(νV.prod νG) := by
    convert hsqind using 1
    all_goals rfl
  have h0' : ∫ p, (commonScaleGaussianInput V G 0 p)^2 ∂(νV.prod νG) = 1 := by
    simpa [pow_two] using h0
  have h1' : ∫ p, (commonScaleGaussianInput V G 1 p)^2 ∂(νV.prod νG) = 1 := by
    simpa [pow_two] using h1
  rw [hsqind', h0', h1'] at hmix
  have hV2mean : ∫ v, V v ^ 2 ∂νV = 1 := by linarith
  have hVvar : Var[V; νV] = 0 := by
    rw [variance_eq_sub hV2]
    simp [hV2mean, hVmean]
  have hae := ae_eq_integral_of_variance_eq_zero hV2 hVvar
  apply hVnonconstant
  filter_upwards [hae] with v hv
  simpa [hVmean] using hv

end RayleighKernel.Probability
