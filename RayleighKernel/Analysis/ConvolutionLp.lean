import RayleighKernel.Analysis.HalfLineSobolev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.Variance

noncomputable section
open ContinuousLinearMap MeasureTheory Set Filter Metric
open scoped ENNReal Topology Convolution

namespace RayleighKernel.Analysis

noncomputable def translateL2 (a : ℝ) : RealL2 →ₗᵢ[ℝ] RealL2 := by
  simpa using
    (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2 : ENNReal))
      (μ := (volume : Measure ℝ)) (μb := volume) (f := fun x : ℝ => x + a)
      (measurePreserving_add_right (volume : Measure ℝ) a))

theorem translateL2_ae_eq (a : ℝ) (g : RealL2) :
    (translateL2 a g : ℝ → ℝ) =ᵐ[volume] fun x => (g : ℝ → ℝ) (x + a) := by
  simpa [translateL2, Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving (g := (g : Lp ℝ (2 : ENNReal) volume))
      (hf := measurePreserving_add_right (volume : Measure ℝ) a))

theorem translateL2_norm (a : ℝ) (g : RealL2) : ‖translateL2 a g‖ = ‖g‖ := by
  exact (translateL2 a).norm_map g

theorem continuous_translateL2 (f : RealL2) :
    Continuous (fun a : ℝ => translateL2 a f) := by
  let g : ℝ → C(ℝ, ℝ) := fun a =>
    ⟨fun x => x + a, continuous_id.add continuous_const⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    dsimp [g]
    fun_prop
  have hgm : ∀ a, MeasurePreserving (g a) volume volume := by
    intro a
    simpa [g] using measurePreserving_add_right (volume : Measure ℝ) a
  have hcomp := (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    hg hgm (by norm_num : (2 : ENNReal) ≠ ∞)
  change Continuous (fun a : ℝ => Lp.compMeasurePreserving
    (fun x : ℝ => x + a) (measurePreserving_add_right volume a) f)
  simpa [g] using hcomp

noncomputable def kernelMeasure (ψ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (ψ x)

theorem kernelMeasure_univ (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) : kernelMeasure ψ Set.univ = 1 := by
  have hψi : Integrable ψ volume :=
    hψc.integrable_of_hasCompactSupport (μ := volume) hψcs
  have hψae : (ae volume).EventuallyLE 0 ψ := Eventually.of_forall hψ0
  have hlin : (∫⁻ x, ENNReal.ofReal (ψ x) ∂volume) = ENNReal.ofReal (∫ x, ψ x ∂volume) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal hψi hψae
  have hwd : kernelMeasure ψ Set.univ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂volume := by
    simp [kernelMeasure, withDensity_apply, MeasurableSet.univ]
  simpa [hψint] using hwd.trans hlin

theorem integral_kernelMeasure_eq_integral_mul (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (g : ℝ → ℝ) :
    (∫ x, g x ∂kernelMeasure ψ) = ∫ x, ψ x * g x ∂volume := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop : (ae volume).Eventually (fun x => ENNReal.ofReal (ψ x) < ∞) :=
    Eventually.of_forall (fun _ => by simp)
  have hwd := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g
  have hwd' : (∫ x, g x ∂kernelMeasure ψ) =
      ∫ x, (ENNReal.ofReal (ψ x)).toReal • g x ∂volume := by
    simpa [kernelMeasure] using hwd
  refine hwd'.trans ?_
  refine integral_congr_ae (ae_of_all _ (fun x => ?_))
  simp [ENNReal.toReal_ofReal (hψ0 x), smul_eq_mul]

theorem sq_integral_le_integral_sq_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : MemLp f 2 μ) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' : 0 ≤ (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

theorem kernel_jensen_sub (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : ℝ → ℝ) (x : ℝ)
    (hfshift : MemLp (fun t => f (x - t)) 2 (kernelMeasure ψ)) :
    (∫ t, f (x - t) ∂kernelMeasure ψ - f x) ^ 2 ≤
      ∫ t, (f (x - t) - f x) ^ 2 ∂kernelMeasure ψ := by
  let μ : Measure ℝ := kernelMeasure ψ
  let g : ℝ → ℝ := fun t => f (x - t) - f x
  let _ : IsProbabilityMeasure μ := ⟨by
    simpa [μ] using kernelMeasure_univ ψ hψc hψcs hψ0 hψint⟩
  have hshift : MemLp (fun t => f (x - t)) 2 μ := by simpa [μ] using hfshift
  have hg : MemLp g 2 μ := hshift.sub (memLp_const (μ := μ) (c := f x))
  have hJ := sq_integral_le_integral_sq_probability μ g hg
  have hsub : (∫ t, g t ∂μ) = ∫ t, f (x - t) ∂μ - f x := by
    have hshift_int : Integrable (fun t => f (x - t)) μ := hshift.integrable (by norm_num)
    have hconst : (∫ _t : ℝ, f x ∂μ) = f x := by simp
    rw [show g = (fun t => f (x - t) - f x) from rfl]
    rw [integral_sub hshift_int (integrable_const (f x)), hconst]
  simpa [g, μ, hsub] using hJ

def smoothFun (ψ : ℝ → ℝ) (f : RealL2) (x : ℝ) : ℝ :=
  ∫ t, (f : ℝ → ℝ) (x - t) ∂kernelMeasure ψ

theorem smoothFun_sub_sq_le_integral_sq_translate
    (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂volume = 1)
    (f : RealL2) (x : ℝ)
    (hfshift : MemLp (fun t => (f : ℝ → ℝ) (x - t)) 2 (kernelMeasure ψ)) :
    (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2 ≤
      ∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂kernelMeasure ψ := by
  exact kernel_jensen_sub ψ hψc hψcs hψ0 hψint (f : ℝ → ℝ) x hfshift

theorem translation_error_integrable_prod (ψ : ℝ → ℝ)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : RealL2) :
    Integrable (fun z : ℝ × ℝ =>
      ((f : ℝ → ℝ) (z.1 - z.2) - (f : ℝ → ℝ) z.1) ^ 2)
      (volume.prod (kernelMeasure ψ)) := by
  let μ : Measure ℝ := kernelMeasure ψ
  let _ : IsProbabilityMeasure μ := ⟨by
    simpa [μ] using kernelMeasure_univ ψ hψc hψcs hψ0 hψint⟩
  have hμ_univ : μ Set.univ = 1 := by simp
  have hf_mem : MemLp (f : ℝ → ℝ) 2 volume := Lp.memLp f
  have hf_sq_int : Integrable (fun x : ℝ => (f : ℝ → ℝ) x ^ 2) volume := by
    simpa [Real.norm_eq_abs, sq_abs] using hf_mem.integrable_sq
  have hfst_map : Integrable (fun x : ℝ => (f : ℝ → ℝ) x ^ 2)
      (Measure.map Prod.fst (volume.prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod : Integrable
      (fun z : ℝ × ℝ => ((f : ℝ → ℝ) z.1) ^ 2) (volume.prod μ) :=
    hfst_map.comp_measurable measurable_fst
  have hsub : MeasurePreserving (fun z : ℝ × ℝ => (z.1 - z.2, z.2))
      (volume.prod μ) (volume.prod μ) :=
    measurePreserving_sub_prod (μ := (volume : Measure ℝ)) (ν := μ)
  have hf_shift_sq_prod : Integrable
      (fun z : ℝ × ℝ => ((f : ℝ → ℝ) (z.1 - z.2)) ^ 2) (volume.prod μ) := by
    have h := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hdom : Integrable (fun z : ℝ × ℝ =>
      (2 : ℝ) * (((f : ℝ → ℝ) (z.1 - z.2)) ^ 2 + ((f : ℝ → ℝ) z.1) ^ 2))
      (volume.prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => (f : ℝ → ℝ) z.1)
      (volume.prod μ) := by
    have hf_map : AEStronglyMeasurable (f : ℝ → ℝ)
        (Measure.map Prod.fst (volume.prod μ)) := by
      simp only [Measure.map_fst_prod, hμ_univ]
      simpa using hf_mem.aestronglyMeasurable
    exact hf_map.comp_measurable measurable_fst
  have hf_shift_aesm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => (f : ℝ → ℝ) (z.1 - z.2)) (volume.prod μ) := by
    have h := hf_fst_aesm.comp_measurePreserving hsub
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have h_aesm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => ((f : ℝ → ℝ) (z.1 - z.2) - (f : ℝ → ℝ) z.1) ^ 2)
      (volume.prod μ) := by
    exact (hf_shift_aesm.sub hf_fst_aesm).pow 2
  refine Integrable.mono hdom h_aesm ?_
  refine Eventually.of_forall ?_
  rintro ⟨x, t⟩
  have hineq : ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ≤
      (2 : ℝ) * (((f : ℝ → ℝ) (x - t)) ^ 2 + ((f : ℝ → ℝ) x) ^ 2) := by
    simpa [sub_eq_add_neg] using
      (add_sq_le (a := (f : ℝ → ℝ) (x - t)) (b := -(f : ℝ → ℝ) x))
  have hnonneg : 0 ≤ ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 := sq_nonneg _
  have hsum_nonneg : 0 ≤ ((f : ℝ → ℝ) (x - t)) ^ 2 + ((f : ℝ → ℝ) x) ^ 2 := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hsum_nonneg] using hineq

theorem translation_error_integrable_average (ψ : ℝ → ℝ)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : RealL2) :
    Integrable (fun x : ℝ =>
      ∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂kernelMeasure ψ) volume := by
  let _ : IsProbabilityMeasure (kernelMeasure ψ) :=
    ⟨kernelMeasure_univ ψ hψc hψcs hψ0 hψint⟩
  let _ : IsFiniteMeasure (kernelMeasure ψ) := by infer_instance
  let _ : SFinite (kernelMeasure ψ) := by infer_instance
  simpa using
    (translation_error_integrable_prod ψ hψc hψcs hψ0 hψint f).integral_prod_left

theorem kernelMeasure_le_smul_volume (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ kernelMeasure ψ ≤ c • volume := by
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  refine (MeasureTheory.lintegral_mono (fun x => hψle x)).trans ?_
  simp

theorem translate_memLp_kernel (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (f : RealL2) (x : ℝ) :
    MemLp (fun t => (f : ℝ → ℝ) (x - t)) 2 (kernelMeasure ψ) := by
  obtain ⟨c, hc, hle⟩ := kernelMeasure_le_smul_volume ψ hψc hψcs hψ0
  apply MemLp.of_measure_le_smul (μ := volume) (μ' := kernelMeasure ψ) hc hle
  have hmp : MeasurePreserving (fun t : ℝ => x - t) volume volume := by
    convert (measurePreserving_add_right (volume : Measure ℝ) x).comp
      (volume.measurePreserving_neg) using 1
    ext t
    simp [sub_eq_add_neg, add_comm]
  exact (Lp.memLp f).comp_measurePreserving hmp

theorem smoothFun_eq_convolution (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (f : RealL2) (x : ℝ) :
    smoothFun ψ f x = ((f : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] ψ) x := by
  rw [smoothFun, integral_kernelMeasure_eq_integral_mul ψ hψc hψ0]
  rw [convolution_lsmul_swap]
  simp [smul_eq_mul, mul_comm]

theorem continuous_smoothFun (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (f : RealL2) :
    Continuous (smoothFun ψ f) := by
  rw [show smoothFun ψ f = (fun x => ((f : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] ψ) x) by
    funext x; exact smoothFun_eq_convolution ψ hψc hψ0 f x]
  apply hψcs.continuous_convolution_right
  · exact (Lp.memLp f).locallyIntegrable (by norm_num)
  · exact hψc

theorem smoothFun_memLp (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : RealL2) :
    MemLp (smoothFun ψ f) 2 volume := by
  have hf_mem : MemLp (f : ℝ → ℝ) 2 volume := Lp.memLp f
  have hcont := continuous_smoothFun ψ hψc hψcs hψ0 f
  have hfae : AEStronglyMeasurable (f : ℝ → ℝ) volume := hf_mem.aestronglyMeasurable
  have hdiff_aesm : AEStronglyMeasurable (fun x : ℝ =>
      smoothFun ψ f x - (f : ℝ → ℝ) x) volume := hcont.aestronglyMeasurable.sub hfae
  have hsq_aesm : AEStronglyMeasurable (fun x : ℝ =>
      (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2) volume := hdiff_aesm.pow 2
  have havg := translation_error_integrable_average ψ hψc hψcs hψ0 hψint f
  have hsq : Integrable (fun x : ℝ =>
      (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2) volume := by
    refine Integrable.mono havg hsq_aesm ?_
    filter_upwards with x
    have hx := smoothFun_sub_sq_le_integral_sq_translate ψ hψc hψcs hψ0 hψint f x
      (translate_memLp_kernel ψ hψc hψcs hψ0 f x)
    have hnonneg : 0 ≤ ∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2
        ∂kernelMeasure ψ := MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hx
  have hdiff : MemLp (fun x : ℝ =>
      smoothFun ψ f x - (f : ℝ → ℝ) x) 2 volume :=
    (memLp_two_iff_integrable_sq hdiff_aesm).2 hsq
  have hsum := hdiff.add hf_mem
  have heq : (fun x : ℝ => smoothFun ψ f x) =
      (fun x => (fun x : ℝ => smoothFun ψ f x - (f : ℝ → ℝ) x) x + (f : ℝ → ℝ) x) := by
    funext x
    ring
  have : MemLp (fun x : ℝ =>
      (fun x : ℝ => smoothFun ψ f x - (f : ℝ → ℝ) x) x + (f : ℝ → ℝ) x) 2 volume := by
    exact hsum
  rw [show smoothFun ψ f =
      (fun x : ℝ => (fun x : ℝ => smoothFun ψ f x - (f : ℝ → ℝ) x) x + (f : ℝ → ℝ) x) by
        funext x; ring]
  exact this

def smoothLp (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂volume = 1)
    (f : RealL2) : RealL2 :=
  (smoothFun_memLp ψ hψc hψcs hψ0 hψint f).toLp (smoothFun ψ f)

theorem smoothLp_ae_eq (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : RealL2) :
    (smoothLp ψ hψc hψcs hψ0 hψint f : ℝ → ℝ) =ᵐ[volume] smoothFun ψ f := by
  exact MemLp.coeFn_toLp _

theorem norm_sq_translateL2_sub_eq_integral_sq (t : ℝ) (f : RealL2) :
    ‖translateL2 (-t) f - f‖ ^ 2 =
      ∫ x, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂volume := by
  have htrans : (translateL2 (-t) f : ℝ → ℝ) =ᵐ[volume]
      fun x => (f : ℝ → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using translateL2_ae_eq (-t) f
  have hdiff : ((translateL2 (-t) f - f : RealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => (f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x := by
    filter_upwards [Lp.coeFn_sub (translateL2 (-t) f) f, htrans] with x hx htx
    rw [show (translateL2 (-t) f - f : RealL2) x =
      (translateL2 (-t) f : ℝ → ℝ) x - (f : ℝ → ℝ) x by simpa using hx, htx]
  have hnorm := norm_sq_eq_re_inner (𝕜 := ℝ) (translateL2 (-t) f - f)
  rw [hnorm, MeasureTheory.L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  simp only [RCLike.re_to_real]
  have hi : (∫ x, ‖((translateL2 (-t) f - f : RealL2) : ℝ → ℝ) x‖ ^ 2 ∂volume) =
      ∫ x, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hdiff] with x hx
    rw [hx]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hi]

theorem norm_sq_smoothLp_sub_le_integral_norm_sq_translate (ψ : ℝ → ℝ)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) (f : RealL2) :
    ‖smoothLp ψ hψc hψcs hψ0 hψint f - f‖ ^ 2 ≤
      ∫ t, ‖translateL2 (-t) f - f‖ ^ 2 ∂kernelMeasure ψ := by
  let μ : Measure ℝ := kernelMeasure ψ
  let _ : IsProbabilityMeasure μ := ⟨by
    simpa [μ] using kernelMeasure_univ ψ hψc hψcs hψ0 hψint⟩
  let _ : IsFiniteMeasure μ := by infer_instance
  let _ : SFinite μ := by infer_instance
  have hprod := translation_error_integrable_prod ψ hψc hψcs hψ0 hψint f
  have hpoint : ∀ x, (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2 ≤
      ∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂μ := by
    intro x
    exact smoothFun_sub_sq_le_integral_sq_translate ψ hψc hψcs hψ0 hψint f x
      (translate_memLp_kernel ψ hψc hψcs hψ0 f x)
  have hleft : Integrable (fun x : ℝ =>
      (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2) volume := by
    exact (smoothFun_memLp ψ hψc hψcs hψ0 hψint f).sub (Lp.memLp f) |>.integrable_sq
  have havg := translation_error_integrable_average ψ hψc hψcs hψ0 hψint f
  have hinterm : ∫ x, (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2 ∂volume ≤
      ∫ x, (∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂μ) ∂volume :=
    integral_mono_ae hleft havg (Filter.Eventually.of_forall hpoint)
  have hswap :
      (∫ x, (∫ t, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂μ) ∂volume) =
        ∫ t, (∫ x, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂volume) ∂μ := by
    simpa using integral_integral_swap (μ := volume) (ν := μ) hprod
  have hinner : (fun t : ℝ =>
      ∫ x, ((f : ℝ → ℝ) (x - t) - (f : ℝ → ℝ) x) ^ 2 ∂volume) =
      (fun t => ‖translateL2 (-t) f - f‖ ^ 2) := by
    funext t
    exact (norm_sq_translateL2_sub_eq_integral_sq t f).symm
  have hleftnorm : ‖smoothLp ψ hψc hψcs hψ0 hψint f - f‖ ^ 2 =
      ∫ x, (smoothFun ψ f x - (f : ℝ → ℝ) x) ^ 2 ∂volume := by
    have hnorm := norm_sq_eq_re_inner (𝕜 := ℝ)
      (smoothLp ψ hψc hψcs hψ0 hψint f - f)
    rw [hnorm, MeasureTheory.L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    simp only [RCLike.re_to_real]
    have hae : ((smoothLp ψ hψc hψcs hψ0 hψint f - f : RealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => smoothFun ψ f x - (f : ℝ → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (smoothLp ψ hψc hψcs hψ0 hψint f) f,
        smoothLp_ae_eq ψ hψc hψcs hψ0 hψint f] with x hx hs
      rw [show (smoothLp ψ hψc hψcs hψ0 hψint f - f : RealL2) x =
        (smoothLp ψ hψc hψcs hψ0 hψint f : ℝ → ℝ) x - (f : ℝ → ℝ) x by simpa using hx,
        hs]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hleftnorm]
  exact hinterm.trans_eq (hswap.trans (by simp [μ, hinner]))

def mollifierBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(2 * (n + 1 : ℕ) : ℝ)⁻¹, ((n + 1 : ℕ) : ℝ)⁻¹, by positivity, by
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    rw [inv_lt_inv₀ (by positivity) hn]
    nlinarith⟩

theorem mollifierBump_rOut_tendsto :
    Tendsto (fun n => (mollifierBump n).rOut) atTop (𝓝 (0 : ℝ)) := by
  simpa [Function.comp_def, mollifierBump, Nat.cast_add, Nat.cast_one] using
    ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1).comp
      (tendsto_add_atTop_nat 1))

def mollifierKernel (n : ℕ) : ℝ → ℝ := (mollifierBump n).normed volume

theorem mollifierKernel_continuous (n : ℕ) : Continuous (mollifierKernel n) := by
  exact (mollifierBump n).continuous_normed

theorem mollifierKernel_compactSupport (n : ℕ) : HasCompactSupport (mollifierKernel n) := by
  exact (mollifierBump n).hasCompactSupport_normed

theorem mollifierKernel_nonneg (n : ℕ) : ∀ x, 0 ≤ mollifierKernel n x := by
  exact (mollifierBump n).nonneg_normed

theorem mollifierKernel_integral (n : ℕ) : ∫ x, mollifierKernel n x ∂volume = 1 := by
  exact (mollifierBump n).integral_normed

theorem kernel_average_sq_le_of_support_ball (ψ : ℝ → ℝ)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂volume = 1) {δ η : ℝ} (hη : 0 ≤ η)
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : ℝ) δ) (f : RealL2)
    (hmod : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) δ →
      ‖translateL2 (-t) f - f‖ ≤ η) :
    ∫ t, ‖translateL2 (-t) f - f‖ ^ 2 ∂kernelMeasure ψ ≤ η ^ 2 := by
  let μ : Measure ℝ := kernelMeasure ψ
  let _ : IsProbabilityMeasure μ := ⟨by
    simpa [μ] using kernelMeasure_univ ψ hψc hψcs hψ0 hψint⟩
  have hzero : μ (Metric.ball (0 : ℝ) δ)ᶜ = 0 := by
    have hψzero : ∀ x : ℝ, x ∈ (Metric.ball (0 : ℝ) δ)ᶜ → ψ x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hx (hψsupp hxt)
    have hs : MeasurableSet (Metric.ball (0 : ℝ) δ)ᶜ := measurableSet_ball.compl
    rw [show μ = kernelMeasure ψ by rfl]
    simp [kernelMeasure, MeasureTheory.withDensity_apply, hs]
    apply MeasureTheory.setLIntegral_eq_zero (μ := volume)
      (s := (Metric.ball (0 : ℝ) δ)ᶜ) hs
    intro x hx
    simp [hψzero x hx]
  have hball : Metric.ball (0 : ℝ) δ ∈ ae μ := MeasureTheory.mem_ae_iff.2 hzero
  have hbound : ∀ᵐ t ∂μ, ‖‖translateL2 (-t) f - f‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hball] with t ht
    have hle := hmod t ht
    have hsq := (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have ha : 0 ≤ ‖translateL2 (-t) f - f‖ ^ 2 := sq_nonneg _
    have hb : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using hsq
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun t : ℝ => ‖translateL2 (-t) f - f‖ ^ 2)
    (C := η ^ 2) hbound
  have hμ : μ.real Set.univ = 1 := by simp [MeasureTheory.measureReal_def]
  have hnonneg : 0 ≤ ∫ t, ‖translateL2 (-t) f - f‖ ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, hμ, μ] using hnorm

theorem mollifier_smoothLp_tendsto (f : RealL2) :
    Tendsto (fun n => ‖(smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
      (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n) (mollifierKernel_integral n) f - f)‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.continuous_iff.1 (continuous_translateL2 f)) 0 (ε / 2) (by positivity)
  have hδ' : 0 < δ := hδ
  filter_upwards [mollifierBump_rOut_tendsto.eventually (eventually_lt_nhds hδ')] with n hn
  have hsupp : tsupport (mollifierKernel n) ⊆ Metric.ball (0 : ℝ) δ := by
    rw [show mollifierKernel n = (mollifierBump n).normed volume by rfl]
    rw [(mollifierBump n).tsupport_normed_eq]
    intro x hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) hn)
  have hmod' : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) δ →
      ‖translateL2 (-t) f - f‖ ≤ ε / 2 := by
    intro t ht
    have ht' : dist (-t) 0 < δ := by simpa [Real.dist_eq] using ht
    have hh := hmod (-t) ht'
    have hle := le_of_lt hh
    have hz : translateL2 (0 : ℝ) f = f := by
      apply Lp.ext
      simpa using translateL2_ae_eq 0 f
    rw [hz] at hle
    simpa [dist_eq_norm] using hle
  have hsq : ‖smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
      (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n) (mollifierKernel_integral n) f - f‖ ^ 2 ≤
      (ε / 2) ^ 2 :=
    (norm_sq_smoothLp_sub_le_integral_norm_sq_translate (mollifierKernel n)
      (mollifierKernel_continuous n) (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
      (mollifierKernel_integral n) f).trans (kernel_average_sq_le_of_support_ball (mollifierKernel n)
        (mollifierKernel_continuous n) (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
        (mollifierKernel_integral n) (by positivity) hsupp f hmod')
  have hnorm : ‖smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
      (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n) (mollifierKernel_integral n) f - f‖ ≤ ε / 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    (lt_of_le_of_lt hnorm (by linarith : ε / 2 < ε))




end RayleighKernel.Analysis
