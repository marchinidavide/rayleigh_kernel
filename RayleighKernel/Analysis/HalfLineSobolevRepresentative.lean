import RayleighKernel.Analysis.HalfLineSobolev
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuous representatives for the half-line Sobolev space

This file constructs the canonical representative of `HalfLineH1` by integrating its stored weak
derivative from the origin.  The only analytic input beyond the graph-space construction is the
one-dimensional fundamental theorem for interval integrals already available in mathlib.
-/

noncomputable section

namespace RayleighKernel
namespace Analysis

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The canonical primitive of the stored weak derivative, normalized to vanish at the origin. -/
def HalfLineH1.continuousRep (u : HalfLineH1) (x : ℝ) : ℝ :=
  ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t

@[simp]
theorem HalfLineH1.continuousRep_zero_element : (0 : HalfLineH1).continuousRep = 0 := by
  funext x
  simp [HalfLineH1.continuousRep]

private theorem HalfLineH1.weakDeriv_locallyIntegrable (u : HalfLineH1) :
    LocallyIntegrable (u.weakDeriv : ℝ → ℝ) volume :=
  (Lp.memLp u.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim

/-- The stored weak derivative is integrable on every bounded interval. -/
theorem HalfLineH1.weakDeriv_intervalIntegrable (u : HalfLineH1) (a b : ℝ) :
    IntervalIntegrable (u.weakDeriv : ℝ → ℝ) volume a b :=
  intervalIntegrable_iff.mpr <|
    (u.weakDeriv_locallyIntegrable.integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc

@[simp]
theorem HalfLineH1.continuousRep_add (u v : HalfLineH1) :
    (u + v).continuousRep = u.continuousRep + v.continuousRep := by
  funext x
  change (∫ t in 0..x, (((u + v).weakDeriv : RealL2) : ℝ → ℝ) t) =
    (∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t) + ∫ t in 0..x, (v.weakDeriv : ℝ → ℝ) t
  rw [map_add]
  calc
    (∫ t in 0..x, (((u.weakDeriv + v.weakDeriv : RealL2) : ℝ → ℝ)) t) =
        ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t + (v.weakDeriv : ℝ → ℝ) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_add u.weakDeriv v.weakDeriv] with y hy _
      exact hy
    _ = (∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t) +
        ∫ t in 0..x, (v.weakDeriv : ℝ → ℝ) t :=
      intervalIntegral.integral_add (u.weakDeriv_intervalIntegrable 0 x)
        (v.weakDeriv_intervalIntegrable 0 x)

@[simp]
theorem HalfLineH1.continuousRep_smul (c : ℝ) (u : HalfLineH1) :
    (c • u).continuousRep = c • u.continuousRep := by
  funext x
  change (∫ t in 0..x, (((c • u).weakDeriv : RealL2) : ℝ → ℝ) t) =
    c • ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t
  rw [map_smul]
  calc
    (∫ t in 0..x, ((c • u.weakDeriv : RealL2) : ℝ → ℝ) t) =
        ∫ t in 0..x, c * (u.weakDeriv : ℝ → ℝ) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u.weakDeriv] with y hy _
      simpa [smul_eq_mul] using hy
    _ = c * ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t :=
      intervalIntegral.integral_const_mul c _

/-- The canonical representative satisfies the fundamental theorem of calculus between arbitrary
endpoints. -/
theorem HalfLineH1.continuousRep_sub (u : HalfLineH1) (a b : ℝ) :
    u.continuousRep b - u.continuousRep a =
      ∫ t in a..b, (u.weakDeriv : ℝ → ℝ) t := by
  exact intervalIntegral.integral_interval_sub_left
    (u.weakDeriv_intervalIntegrable 0 b) (u.weakDeriv_intervalIntegrable 0 a)

/-- The canonical representative has the standard global Hölder-`1/2` bound controlled by the
`L²` norm of its weak derivative. -/
theorem HalfLineH1.abs_continuousRep_sub_le (u : HalfLineH1) (a b : ℝ) :
    |u.continuousRep b - u.continuousRep a| ≤ Real.sqrt |b - a| * ‖u.weakDeriv‖ := by
  have hs : volume (uIoc a b) ≠ ∞ := by
    simp [Real.volume_uIoc]
  let χ : RealL2 := indicatorConstLp 2 measurableSet_uIoc hs 1
  have hinner : inner ℝ χ u.weakDeriv =
      ∫ t in uIoc a b, (u.weakDeriv : ℝ → ℝ) t := by
    simpa [χ] using L2.inner_indicatorConstLp_one measurableSet_uIoc hs u.weakDeriv
  rw [u.continuousRep_sub, intervalIntegral.intervalIntegral_eq_integral_uIoc, ← hinner]
  have hnorm : ‖χ‖ = Real.sqrt |b - a| := by
    simp only [χ]
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    simp [Real.volume_uIoc, Measure.real, Real.sqrt_eq_rpow]
  simp only [abs_smul, abs_ite, abs_one, abs_neg, ite_self, one_smul]
  rw [← hnorm]
  exact abs_real_inner_le_norm χ u.weakDeriv

/-- The canonical representative is uniformly continuous on the whole line. -/
theorem HalfLineH1.uniformContinuous_continuousRep (u : HalfLineH1) :
    UniformContinuous u.continuousRep := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  by_cases hD : ‖u.weakDeriv‖ = 0
  · refine ⟨1, zero_lt_one, fun {a b} _ ↦ ?_⟩
    have h := u.abs_continuousRep_sub_le b a
    rw [hD, mul_zero] at h
    have hz : |u.continuousRep a - u.continuousRep b| = 0 :=
      le_antisymm h (abs_nonneg _)
    simpa [Real.dist_eq, abs_eq_zero.mp hz] using hε
  · have hDpos : 0 < ‖u.weakDeriv‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
    refine ⟨(ε / ‖u.weakDeriv‖) ^ 2, sq_pos_of_pos (div_pos hε hDpos), ?_⟩
    intro a b hab
    have h := u.abs_continuousRep_sub_le b a
    have hsqrt : Real.sqrt |a - b| < ε / ‖u.weakDeriv‖ := by
      apply (Real.sqrt_lt' (div_pos hε hDpos)).mpr
      simpa only [Real.dist_eq] using hab
    calc
      dist (u.continuousRep a) (u.continuousRep b) =
          |u.continuousRep a - u.continuousRep b| := Real.dist_eq _ _
      _ ≤ Real.sqrt |a - b| * ‖u.weakDeriv‖ := h
      _ < (ε / ‖u.weakDeriv‖) * ‖u.weakDeriv‖ :=
        mul_lt_mul_of_pos_right hsqrt hDpos
      _ = ε := div_mul_cancel₀ ε hD

/-- The canonical representative is locally absolutely continuous. -/
theorem HalfLineH1.continuousRep_absolutelyContinuousOnInterval (u : HalfLineH1) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u.continuousRep a b := by
  let c : ℝ := min (min a b) 0
  let d : ℝ := max (max a b) 0
  have hInt : IntervalIntegrable (u.weakDeriv : ℝ → ℝ) volume c d :=
    u.weakDeriv_intervalIntegrable _ _
  have hAC := hInt.absolutelyContinuousOnInterval_intervalIntegral
    (show 0 ∈ uIcc c d by simp [c, d, uIcc_of_le])
  apply hAC.mono
  simp only [uIcc]
  intro x hx
  simp only [mem_Icc] at hx ⊢
  dsimp [c, d]
  constructor <;> simp_all

/-- The canonical representative is continuous on every bounded interval. -/
theorem HalfLineH1.continuousOn_continuousRep (u : HalfLineH1) (a b : ℝ) :
    ContinuousOn u.continuousRep (uIcc a b) :=
  (u.continuousRep_absolutelyContinuousOnInterval a b).continuousOn

/-- The canonical representative is continuous on the whole line. -/
theorem HalfLineH1.continuous_continuousRep (u : HalfLineH1) : Continuous u.continuousRep := by
  rw [continuous_iff_continuousAt]
  intro x
  have hle : x - 1 ≤ x + 1 := by linarith
  have hx : x ∈ Icc (x - 1) (x + 1) := by constructor <;> linarith
  exact (u.continuousOn_continuousRep (x - 1) (x + 1)) x (by
      simpa only [uIcc_of_le hle] using hx) |>.continuousAt
    (by rw [uIcc_of_le hle]; exact Icc_mem_nhds (by linarith) (by linarith))

/-- The canonical representative has trace zero at the origin. -/
@[simp]
theorem HalfLineH1.continuousRep_zero (u : HalfLineH1) : u.continuousRep 0 = 0 := by
  simp [HalfLineH1.continuousRep]

/-- Almost everywhere, the classical derivative of the canonical representative is the stored
weak derivative. -/
theorem HalfLineH1.hasDerivAt_continuousRep_ae (u : HalfLineH1) :
    ∀ᵐ x ∂volume, HasDerivAt u.continuousRep (u.weakDeriv x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral u.weakDeriv_locallyIntegrable] with x hx
  exact hx 0

/-- Almost everywhere, `deriv` of the canonical representative is the stored weak derivative. -/
theorem HalfLineH1.deriv_continuousRep_ae (u : HalfLineH1) :
    deriv u.continuousRep =ᵐ[volume] (u.weakDeriv : ℝ → ℝ) :=
  u.hasDerivAt_continuousRep_ae.mono fun _ hx ↦ hx.deriv

/-- The classical derivative of the canonical representative realizes the stored weak derivative
as an element of whole-line `L²`. -/
theorem HalfLineH1.deriv_continuousRep_memLp (u : HalfLineH1) :
    MemLp (deriv u.continuousRep) 2 volume :=
  (Lp.memLp u.weakDeriv).ae_eq u.deriv_continuousRep_ae.symm

/-- Sending the classical derivative of the canonical representative back to `L²` recovers the
stored weak derivative. -/
theorem HalfLineH1.toLp_deriv_continuousRep (u : HalfLineH1) :
    u.deriv_continuousRep_memLp.toLp (deriv u.continuousRep) = u.weakDeriv := by
  apply Lp.ext
  exact u.deriv_continuousRep_memLp.coeFn_toLp.trans u.deriv_continuousRep_ae

/-- The classical derivative of the canonical representative vanishes almost everywhere on the
nonpositive half-line. -/
theorem HalfLineH1.deriv_continuousRep_ae_eq_zero_on_nonpositive (u : HalfLineH1) :
    deriv u.continuousRep =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 :=
  EventuallyEq.trans (ae_restrict_of_ae u.deriv_continuousRep_ae)
    u.weakDeriv_ae_eq_zero_on_nonpositive

/-- A smooth generator agrees pointwise with its canonical representative. -/
theorem PositiveTestFunction.continuousRep_toHalfLineH1 (φ : PositiveTestFunction) (x : ℝ) :
    (PositiveTestFunction.toHalfLineH1 φ).continuousRep x = φ.1 x := by
  have hftc := intervalIntegral.integral_deriv_of_contDiffOn_uIcc
    (f := fun y : ℝ ↦ φ.1 y) (a := 0) (b := x) (φ.1.smooth 1).contDiffOn
  rw [HalfLineH1.continuousRep]
  calc
    (∫ t in 0..x, ((PositiveTestFunction.toHalfLineH1 φ).weakDeriv : ℝ → ℝ) t) =
        ∫ t in 0..x, deriv φ.1 t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [((SchwartzMap.derivCLM ℝ ℝ φ.1).coeFn_toLp 2 volume)] with y hy _
      exact hy
    _ = φ.1 x - φ.1 0 := hftc
    _ = φ.1 x := by rw [show φ.1 0 = 0 by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h ↦ (not_lt_of_ge (show (0 : ℝ) ≤ 0 by rfl)) (φ.2 h)]; simp

private theorem positiveTestFunction_tendsto_ae
    {φ : ℕ → PositiveTestFunction} {u : HalfLineH1}
    (hφ : Tendsto (fun n ↦ PositiveTestFunction.toHalfLineH1 (φ n)) atTop (𝓝 u)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume, Tendsto (fun n ↦ (φ (ns n) : ℝ → ℝ) x) atTop (𝓝 (u.value x)) := by
  have hvalue : Tendsto
      (fun n ↦ (PositiveTestFunction.toHalfLineH1 (φ n)).value) atTop (𝓝 u.value) :=
    HalfLineH1.tendsto_value hφ
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hvalue).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hcoe : ∀ᵐ x ∂volume, ∀ n,
      ((PositiveTestFunction.toHalfLineH1 (φ n)).value : ℝ → ℝ) x = (φ n).1 x := by
    exact ae_all_iff.mpr fun n ↦ (φ n).1.coeFn_toLp 2 volume
  filter_upwards [hlim, hcoe] with x hx hφx
  simpa only [hφx] using hx

/-- The canonical primitive is an almost-everywhere representative of the stored `L²` value. -/
theorem HalfLineH1.continuousRep_ae_eq_value (u : HalfLineH1) :
    u.continuousRep =ᵐ[volume] (u.value : ℝ → ℝ) := by
  obtain ⟨φ, hφ⟩ := u.exists_positiveTestFunction_sequence
  obtain ⟨ns, hns, hpointwise⟩ := positiveTestFunction_tendsto_ae hφ
  have hφsub : Tendsto (fun n ↦ PositiveTestFunction.toHalfLineH1 (φ (ns n))) atTop (𝓝 u) :=
    hφ.comp hns.tendsto_atTop
  have hderiv : Tendsto
      (fun n ↦ (PositiveTestFunction.toHalfLineH1 (φ (ns n))).weakDeriv) atTop
      (𝓝 u.weakDeriv) :=
    HalfLineH1.tendsto_weakDeriv hφsub
  have hInt (x : ℝ) : Tendsto
      (fun n ↦ ∫ t in 0..x, ((PositiveTestFunction.toHalfLineH1 (φ (ns n))).weakDeriv : ℝ → ℝ) t)
      atTop (𝓝 (∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t)) := by
    have hs : volume (uIoc (0 : ℝ) x) ≠ ∞ := by
      simp [Real.volume_uIoc]
    let χ : RealL2 := indicatorConstLp 2 measurableSet_uIoc hs 1
    have hinner : ∀ v : RealL2,
        inner ℝ χ v = ∫ t in uIoc (0 : ℝ) x, (v : ℝ → ℝ) t := by
      intro v
      simpa [χ] using L2.inner_indicatorConstLp_one measurableSet_uIoc hs v
    have htendsto : Tendsto
        (fun n ↦ inner ℝ χ (PositiveTestFunction.toHalfLineH1 (φ (ns n))).weakDeriv)
        atTop (𝓝 (inner ℝ χ u.weakDeriv)) := by
      exact (innerSL ℝ χ).continuous.tendsto u.weakDeriv |>.comp hderiv
    simp_rw [hinner] at htendsto
    rw [show (fun n ↦ ∫ t in 0..x,
        ((PositiveTestFunction.toHalfLineH1 (φ (ns n))).weakDeriv : ℝ → ℝ) t) =
        fun n ↦ (if 0 ≤ x then 1 else -1 : ℝ) •
          ∫ t in uIoc (0 : ℝ) x,
            ((PositiveTestFunction.toHalfLineH1 (φ (ns n))).weakDeriv : ℝ → ℝ) t by
      funext n
      exact intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _]
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact htendsto.const_smul (if 0 ≤ x then 1 else -1 : ℝ)
  filter_upwards [hpointwise] with x hx
  have hx' : Tendsto (fun n ↦ (φ (ns n)).1 x) atTop (𝓝 (u.continuousRep x)) := by
    rw [show (fun n ↦ (φ (ns n)).1 x) =
        fun n ↦ (PositiveTestFunction.toHalfLineH1 (φ (ns n))).continuousRep x by
      funext n
      exact PositiveTestFunction.continuousRep_toHalfLineH1 (φ (ns n)) x |>.symm]
    exact hInt x
  symm
  exact tendsto_nhds_unique hx hx'

/-- The canonical representative realizes the stored value as an element of whole-line `L²`. -/
theorem HalfLineH1.continuousRep_memLp (u : HalfLineH1) : MemLp u.continuousRep 2 volume :=
  (Lp.memLp u.value).ae_eq u.continuousRep_ae_eq_value.symm

/-- The square of the canonical representative is integrable on the whole line. -/
theorem HalfLineH1.continuousRep_sq_integrable (u : HalfLineH1) :
    Integrable (fun x ↦ u.continuousRep x ^ 2) volume :=
  u.continuousRep_memLp.integrable_sq

/-- The canonical representative tends to zero at `+∞`.  This follows from its global uniform
continuity and square-integrability. -/
theorem HalfLineH1.tendsto_continuousRep_atTop (u : HalfLineH1) :
    Tendsto u.continuousRep atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ :=
    Metric.uniformContinuous_iff.mp u.uniformContinuous_continuousRep (ε / 2) (by positivity)
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hshift : Tendsto (fun x : ℝ ↦ x - r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + r)] with a ha
    linarith
  have htail : Tendsto
      (fun x : ℝ ↦ ∫ y in Ici (x - r), u.continuousRep y ^ 2) atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ici_zero hshift
  have hthreshold : 0 < 2 * r * (ε / 2) ^ 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail _ hthreshold
  refine ⟨N, fun x hx ↦ ?_⟩
  have htail_nonneg : 0 ≤ ∫ y in Ici (x - r), u.continuousRep y ^ 2 :=
    setIntegral_nonneg measurableSet_Ici fun _ _ ↦ sq_nonneg _
  have htail_lt : (∫ y in Ici (x - r), u.continuousRep y ^ 2) <
      2 * r * (ε / 2) ^ 2 := by
    have := hN x hx
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg htail_nonneg] using this
  rw [Real.dist_eq, sub_zero]
  by_contra hnot
  have hxlarge : ε ≤ |u.continuousRep x| := le_of_not_gt hnot
  have hpoint : ∀ y ∈ Icc (x - r) (x + r), (ε / 2) ^ 2 ≤ u.continuousRep y ^ 2 := by
    intro y hy
    have hydist : dist y x < δ := by
      rw [Real.dist_eq]
      have : |y - x| ≤ r := by
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      exact this.trans_lt (by dsimp [r]; linarith)
    have hclose := huc hydist
    rw [Real.dist_eq] at hclose
    have hylower : ε / 2 < |u.continuousRep y| := by
      have habs := abs_sub_abs_le_abs_sub (u.continuousRep x) (u.continuousRep y)
      rw [abs_sub_comm] at hclose
      linarith
    have hehalf : 0 ≤ ε / 2 := by positivity
    have huabs : 0 ≤ |u.continuousRep y| := abs_nonneg _
    have hsquares : (ε / 2) ^ 2 ≤ |u.continuousRep y| ^ 2 := by nlinarith
    simpa only [sq_abs] using hsquares
  have hconst_integrable :
      IntegrableOn (fun _ : ℝ ↦ (ε / 2) ^ 2) (Icc (x - r) (x + r)) :=
    integrableOn_const (by simp [Real.volume_Icc]) (by simp)
  have hsquare_integrable :
      IntegrableOn (fun y ↦ u.continuousRep y ^ 2) (Icc (x - r) (x + r)) :=
    u.continuousRep_sq_integrable.integrableOn
  have hinterval_tail :
      (∫ y in Icc (x - r) (x + r), u.continuousRep y ^ 2) ≤
        ∫ y in Ici (x - r), u.continuousRep y ^ 2 := by
    apply setIntegral_mono_set u.continuousRep_sq_integrable.integrableOn
    · filter_upwards with y
      exact sq_nonneg _
    · filter_upwards with y hy
      exact hy.1
  have hlower : 2 * r * (ε / 2) ^ 2 ≤
      ∫ y in Ici (x - r), u.continuousRep y ^ 2 := by
    calc
      2 * r * (ε / 2) ^ 2 = ∫ _ in Icc (x - r) (x + r), (ε / 2) ^ 2 := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ x + r - (x - r)), smul_eq_mul]
        ring
      _ ≤ ∫ y in Icc (x - r) (x + r), u.continuousRep y ^ 2 :=
        setIntegral_mono_on hconst_integrable hsquare_integrable measurableSet_Icc hpoint
      _ ≤ ∫ y in Ici (x - r), u.continuousRep y ^ 2 := hinterval_tail
  exact (not_lt_of_ge hlower) htail_lt

/-- The square of the classical derivative of the canonical representative is integrable on the
whole line. -/
theorem HalfLineH1.deriv_continuousRep_sq_integrable (u : HalfLineH1) :
    Integrable (fun x ↦ deriv u.continuousRep x ^ 2) volume := by
  exact u.deriv_continuousRep_memLp.integrable_sq

/-- Sending the canonical representative back to `L²` recovers the stored value. -/
theorem HalfLineH1.toLp_continuousRep (u : HalfLineH1) :
    u.continuousRep_memLp.toLp u.continuousRep = u.value := by
  apply Lp.ext
  exact u.continuousRep_memLp.coeFn_toLp.trans u.continuousRep_ae_eq_value

/-- The canonical representative vanishes pointwise on the nonpositive half-line. -/
theorem HalfLineH1.continuousRep_eq_zero_of_nonpositive (u : HalfLineH1) {x : ℝ} (hx : x ≤ 0) :
    u.continuousRep x = 0 := by
  have hzero : u.continuousRep =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] (0 : ℝ → ℝ) :=
    EventuallyEq.trans (ae_restrict_of_ae u.continuousRep_ae_eq_value)
      u.value_ae_eq_zero_on_nonpositive
  exact MeasureTheory.Measure.eqOn_of_ae_eq hzero
    (u.continuous_continuousRep.continuousOn)
    continuous_zero.continuousOn
    (by
      rw [interior_Iic, closure_Iio]) hx

/-- The ordinary support of the canonical representative lies in the positive half-line. -/
theorem HalfLineH1.support_continuousRep_subset (u : HalfLineH1) :
    Function.support u.continuousRep ⊆ Ioi 0 := by
  intro x hx
  exact lt_of_not_ge fun hx0 ↦ hx (u.continuousRep_eq_zero_of_nonpositive hx0)

/-- The whole-line square integral of the canonical representative is its stored `L²` norm
squared. -/
theorem HalfLineH1.integral_continuousRep_sq_eq_norm_value_sq (u : HalfLineH1) :
    (∫ x : ℝ, u.continuousRep x ^ 2) = ‖u.value‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u.value, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.continuousRep_ae_eq_value] with x hx
  simp only [Real.inner_apply]
  rw [hx, pow_two]

/-- Restricting the square integral of the canonical representative to `[0, ∞)` does not change
its value. -/
theorem HalfLineH1.integral_continuousRep_sq_Ici_eq_norm_value_sq (u : HalfLineH1) :
    (∫ x : ℝ in Ici 0, u.continuousRep x ^ 2) = ‖u.value‖ ^ 2 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    rw [u.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx), zero_pow two_ne_zero])]
  exact u.integral_continuousRep_sq_eq_norm_value_sq

/-- The whole-line Dirichlet integral of the canonical representative is the stored weak-derivative
`L²` norm squared. -/
theorem HalfLineH1.integral_deriv_continuousRep_sq_eq_norm_weakDeriv_sq (u : HalfLineH1) :
    (∫ x : ℝ, deriv u.continuousRep x ^ 2) = ‖u.weakDeriv‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u.weakDeriv, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.deriv_continuousRep_ae] with x hx
  simp only [Real.inner_apply]
  rw [hx, pow_two]

/-- Restricting the Dirichlet integral of the canonical representative to `[0, ∞)` does not change
its value. -/
theorem HalfLineH1.integral_deriv_continuousRep_sq_Ici_eq_norm_weakDeriv_sq (u : HalfLineH1) :
    (∫ x : ℝ in Ici 0, deriv u.continuousRep x ^ 2) = ‖u.weakDeriv‖ ^ 2 := by
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
  · exact u.integral_deriv_continuousRep_sq_eq_norm_weakDeriv_sq
  · filter_upwards [ae_imp_of_ae_restrict
      u.deriv_continuousRep_ae_eq_zero_on_nonpositive] with x hx hx_not_mem
    rw [hx (show x ≤ 0 from le_of_not_ge hx_not_mem)]
    simp

/-- Whole-line Cauchy--Schwarz for the canonical representative and its classical derivative. -/
theorem HalfLineH1.integral_abs_continuousRep_mul_abs_deriv_le (u : HalfLineH1) :
    (∫ x : ℝ, |u.continuousRep x| * |deriv u.continuousRep x|) ≤
      ‖u.value‖ * ‖u.weakDeriv‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (f := u.continuousRep) (g := deriv u.continuousRep)
    Real.HolderConjugate.two_two (by simpa using u.continuousRep_memLp)
      (by simpa using u.deriv_continuousRep_memLp)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
  rw [u.integral_continuousRep_sq_eq_norm_value_sq,
    u.integral_deriv_continuousRep_sq_eq_norm_weakDeriv_sq] at h
  have hvalue : (‖u.value‖ ^ 2) ^ (1 / (2 : ℝ)) = ‖u.value‖ := by
    rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (norm_nonneg _) two_ne_zero]
  have hderiv : (‖u.weakDeriv‖ ^ 2) ^ (1 / (2 : ℝ)) = ‖u.weakDeriv‖ := by
    rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (norm_nonneg _) two_ne_zero]
  calc
    (∫ x : ℝ, |u.continuousRep x| * |deriv u.continuousRep x|) ≤
        (‖u.value‖ ^ 2) ^ (1 / (2 : ℝ)) * (‖u.weakDeriv‖ ^ 2) ^ (1 / (2 : ℝ)) := h
    _ = ‖u.value‖ * ‖u.weakDeriv‖ := by rw [hvalue, hderiv]

/-- The one-dimensional Sobolev estimate, pointwise for the canonical representative:
`|u(x)|² ≤ 2 ‖u‖₂ ‖u'‖₂`. -/
theorem HalfLineH1.continuousRep_sq_le (u : HalfLineH1) (x : ℝ) :
    u.continuousRep x ^ 2 ≤ 2 * ‖u.value‖ * ‖u.weakDeriv‖ := by
  have hproduct : Integrable (u.continuousRep * deriv u.continuousRep) volume :=
    u.continuousRep_memLp.integrable_mul u.deriv_continuousRep_memLp
  have hcauchy := u.integral_abs_continuousRep_mul_abs_deriv_le
  have hbound (b : ℝ) (hxb : x ≤ b) :
      u.continuousRep x ^ 2 - u.continuousRep b ^ 2 ≤
        2 * ‖u.value‖ * ‖u.weakDeriv‖ := by
    have hACu := u.continuousRep_absolutelyContinuousOnInterval x b
    have hid := hACu.integral_deriv_mul_eq_sub hACu
    have habs : |u.continuousRep b ^ 2 - u.continuousRep x ^ 2| ≤
        ∫ y in x..b, |deriv u.continuousRep y * u.continuousRep y +
          u.continuousRep y * deriv u.continuousRep y| := by
      calc
        |u.continuousRep b ^ 2 - u.continuousRep x ^ 2| =
            |u.continuousRep b * u.continuousRep b -
              u.continuousRep x * u.continuousRep x| := by rw [pow_two, pow_two]
        _ = |∫ y in x..b, deriv u.continuousRep y * u.continuousRep y +
            u.continuousRep y * deriv u.continuousRep y| := congrArg abs hid.symm
        _ ≤ ∫ y in x..b, |deriv u.continuousRep y * u.continuousRep y +
            u.continuousRep y * deriv u.continuousRep y| :=
          intervalIntegral.abs_integral_le_integral_abs hxb
    have hinterval : (∫ y in x..b,
        |deriv u.continuousRep y * u.continuousRep y +
          u.continuousRep y * deriv u.continuousRep y|) ≤
        2 * ∫ y : ℝ, |u.continuousRep y| * |deriv u.continuousRep y| := by
      rw [intervalIntegral.integral_of_le hxb]
      calc
        (∫ y in Ioc x b, |deriv u.continuousRep y * u.continuousRep y +
            u.continuousRep y * deriv u.continuousRep y|) =
            ∫ y in Ioc x b, 2 * (|u.continuousRep y| * |deriv u.continuousRep y|) := by
              apply integral_congr_ae
              filter_upwards with y
              rw [mul_comm (deriv u.continuousRep y), ← two_mul,
                abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul]
        _ ≤ ∫ y : ℝ, 2 * (|u.continuousRep y| * |deriv u.continuousRep y|) := by
          apply setIntegral_le_integral
          · convert hproduct.abs.const_mul 2 using 1
            ext y
            simp [abs_mul]
          · filter_upwards with y
            positivity
        _ = 2 * ∫ y : ℝ, |u.continuousRep y| * |deriv u.continuousRep y| := by
          rw [integral_const_mul]
    calc
      u.continuousRep x ^ 2 - u.continuousRep b ^ 2 ≤
          |u.continuousRep b ^ 2 - u.continuousRep x ^ 2| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ ∫ y in x..b, |deriv u.continuousRep y * u.continuousRep y +
          u.continuousRep y * deriv u.continuousRep y| := habs
      _ ≤ 2 * ∫ y : ℝ, |u.continuousRep y| * |deriv u.continuousRep y| := hinterval
      _ ≤ 2 * (‖u.value‖ * ‖u.weakDeriv‖) := mul_le_mul_of_nonneg_left hcauchy zero_le_two
      _ = 2 * ‖u.value‖ * ‖u.weakDeriv‖ := by ring
  have hlim : Tendsto (fun b ↦ u.continuousRep x ^ 2 - u.continuousRep b ^ 2)
      atTop (𝓝 (u.continuousRep x ^ 2)) := by
    simpa using tendsto_const_nhds.sub (u.tendsto_continuousRep_atTop.pow 2)
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨x, fun b hb ↦ hbound b hb⟩)

/-- Absolute-value form of the pointwise Sobolev estimate.  Taking the supremum over `x` gives the
manuscript inequality `‖u‖∞² ≤ 2 ‖u‖₂ ‖u'‖₂`. -/
theorem HalfLineH1.abs_continuousRep_sq_le (u : HalfLineH1) (x : ℝ) :
    |u.continuousRep x| ^ 2 ≤ 2 * ‖u.value‖ * ‖u.weakDeriv‖ := by
  simpa only [sq_abs] using u.continuousRep_sq_le x

/-- Integrability on the nonnegative half-line implies whole-line integrability because the
canonical representative vanishes on the nonpositive half-line. -/
theorem HalfLineH1.continuousRep_integrable_of_integrableOn_halfLine (u : HalfLineH1)
    (hInt : IntegrableOn u.continuousRep (Ici 0)) : Integrable u.continuousRep := by
  rw [← integrableOn_univ]
  rw [← show Iic (0 : ℝ) ∪ Ici 0 = univ from Iic_union_Ici]
  apply IntegrableOn.union
  · exact (integrableOn_congr_fun
      (f := u.continuousRep) (g := fun _ : ℝ ↦ 0) (s := Iic 0)
      (fun x hx ↦ u.continuousRep_eq_zero_of_nonpositive hx) measurableSet_Iic).mpr
        integrableOn_zero
  · exact hInt

/-- The elementary `L¹`--`L∞` interpolation step used in the Gagliardo--Nirenberg estimate. -/
theorem HalfLineH1.norm_value_sq_le_integral_abs_mul_sqrt (u : HalfLineH1)
    (hInt : Integrable u.continuousRep) :
    ‖u.value‖ ^ 2 ≤ (∫ x : ℝ, |u.continuousRep x|) *
      Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := by
  have hpoint (x : ℝ) : |u.continuousRep x| ≤
      Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    simpa only [sq_abs] using u.abs_continuousRep_sq_le x
  rw [← u.integral_continuousRep_sq_eq_norm_value_sq]
  calc
    (∫ x : ℝ, u.continuousRep x ^ 2) =
        ∫ x : ℝ, |u.continuousRep x| * |u.continuousRep x| := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← sq_abs, pow_two]
    _ ≤ ∫ x : ℝ, |u.continuousRep x| *
        Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := by
      apply integral_mono
      · have hsquare := u.continuousRep_sq_integrable
        convert hsquare using 1
        ext x
        rw [← sq_abs, pow_two]
      · exact hInt.abs.mul_const _
      · intro x
        exact mul_le_mul_of_nonneg_left (hpoint x) (abs_nonneg _)
    _ = (∫ x : ℝ, |u.continuousRep x|) *
        Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := integral_mul_const _ _

/-- Polynomial form of the one-dimensional Gagliardo--Nirenberg estimate. -/
theorem HalfLineH1.norm_value_cubed_le (u : HalfLineH1)
    (hInt : Integrable u.continuousRep) :
    ‖u.value‖ ^ 3 ≤ 2 * (∫ x : ℝ, |u.continuousRep x|) ^ 2 * ‖u.weakDeriv‖ := by
  let A := ‖u.value‖
  let B := ∫ x : ℝ, |u.continuousRep x|
  let C := ‖u.weakDeriv‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ abs_nonneg _
  have hC : 0 ≤ C := norm_nonneg _
  have hbase : A ^ 2 ≤ B * Real.sqrt (2 * A * C) := by
    simpa only [A, B, C] using u.norm_value_sq_le_integral_abs_mul_sqrt hInt
  have hsqrt : Real.sqrt (2 * A * C) ^ 2 = 2 * A * C := Real.sq_sqrt (by positivity)
  have hsquare : (A ^ 2) ^ 2 ≤ (B * Real.sqrt (2 * A * C)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg A) hbase 2
  rw [mul_pow, hsqrt] at hsquare
  rcases hA.eq_or_lt with hAzero | hApos
  · change A ^ 3 ≤ 2 * B ^ 2 * C
    rw [← hAzero]
    simpa using mul_nonneg (mul_nonneg zero_le_two (sq_nonneg B)) hC
  · change A ^ 3 ≤ 2 * B ^ 2 * C
    nlinarith [sq_nonneg B]

/-- The one-dimensional Gagliardo--Nirenberg inequality used in the manuscript:
`‖u‖₂² ≤ 2^(2/3) ‖u‖₁^(4/3) ‖u'‖₂^(2/3)`. -/
theorem HalfLineH1.norm_value_sq_le_rpow (u : HalfLineH1)
    (hInt : Integrable u.continuousRep) :
    ‖u.value‖ ^ 2 ≤
      (2 : ℝ) ^ (2 / 3 : ℝ) * (∫ x : ℝ, |u.continuousRep x|) ^ (4 / 3 : ℝ) *
        ‖u.weakDeriv‖ ^ (2 / 3 : ℝ) := by
  let A := ‖u.value‖
  let B := ∫ x : ℝ, |u.continuousRep x|
  let C := ‖u.weakDeriv‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ abs_nonneg _
  have hC : 0 ≤ C := norm_nonneg _
  have hcubic : A ^ 3 ≤ 2 * B ^ 2 * C := by
    simpa only [A, B, C] using u.norm_value_cubed_le hInt
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ A ^ 3) hcubic
    (by norm_num : 0 ≤ (2 / 3 : ℝ))
  change A ^ 2 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * B ^ (4 / 3 : ℝ) * C ^ (2 / 3 : ℝ)
  calc
    A ^ 2 = (A ^ 3) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast_mul hA]
      norm_num
    _ ≤ (2 * B ^ 2 * C) ^ (2 / 3 : ℝ) := hrpow
    _ = (2 : ℝ) ^ (2 / 3 : ℝ) * B ^ (4 / 3 : ℝ) * C ^ (2 / 3 : ℝ) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * B ^ 2) hC,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (sq_nonneg B)]
      rw [← Real.rpow_natCast_mul hB]
      norm_num

/-- Half-line form of the one-dimensional Gagliardo--Nirenberg inequality.  The half-line `L¹`
norm is written as a set integral, matching the variational API. -/
theorem HalfLineH1.norm_value_sq_le_rpow_of_integrableOn_halfLine (u : HalfLineH1)
    (hInt : IntegrableOn u.continuousRep (Ici 0)) :
    ‖u.value‖ ^ 2 ≤
      (2 : ℝ) ^ (2 / 3 : ℝ) * (∫ x in Ici 0, |u.continuousRep x|) ^ (4 / 3 : ℝ) *
        ‖u.weakDeriv‖ ^ (2 / 3 : ℝ) := by
  have hWhole := u.continuousRep_integrable_of_integrableOn_halfLine hInt
  have hIntegral : (∫ x in Ici 0, |u.continuousRep x|) =
      ∫ x : ℝ, |u.continuousRep x| :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      rw [u.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx), abs_zero])
  rw [hIntegral]
  exact u.norm_value_sq_le_rpow hWhole

/-- A continuous whole-line function representing the stored `L²` value is the canonical
representative. -/
theorem HalfLineH1.eq_continuousRep_of_continuous_ae_eq_value (u : HalfLineH1) {f : ℝ → ℝ}
    (hf : Continuous f) (hfu : f =ᵐ[volume] (u.value : ℝ → ℝ)) : f = u.continuousRep :=
  MeasureTheory.Measure.eq_of_ae_eq
    (hfu.trans u.continuousRep_ae_eq_value.symm) hf u.continuous_continuousRep

/-- A locally absolutely continuous half-line representative with trace zero and the stored weak
derivative agrees with the canonical representative on `[0, ∞)`. -/
theorem HalfLineH1.eqOn_continuousRep_of_trace_deriv (u : HalfLineH1) {f : ℝ → ℝ}
    (hf0 : f 0 = 0)
    (hf_ac : ∀ R, 0 < R → AbsolutelyContinuousOnInterval f 0 R)
    (hf_deriv : deriv f =ᵐ[(volume : Measure ℝ).restrict (Ici 0)]
      (u.weakDeriv : ℝ → ℝ)) :
    Set.EqOn f u.continuousRep (Ici 0) := by
  intro x hx
  have hx_nonneg : 0 ≤ x := hx
  rcases hx_nonneg.eq_or_lt with hx0 | hxpos
  · subst x
    rw [hf0, u.continuousRep_zero]
  · have hIntegral : (∫ t in 0..x, deriv f t) =
        ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hf_deriv] with y hy hyI
      apply hy
      rw [uIoc_of_le hxpos.le] at hyI
      exact hyI.1.le
    calc
      f x = f x - f 0 := by rw [hf0, sub_zero]
      _ = ∫ t in 0..x, deriv f t := (hf_ac x hxpos).integral_deriv_eq_sub.symm
      _ = ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) t := hIntegral
      _ = u.continuousRep x := rfl

end Analysis
end RayleighKernel
