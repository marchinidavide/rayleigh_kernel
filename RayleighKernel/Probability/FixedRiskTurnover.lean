import RayleighKernel.Probability.GaussianTurnover

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology
namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {r : ℤ → Ω → ℝ}

def fixedRiskScale (σ : ℝ) (w : Discrete.Kernel) : ℝ :=
  σ / Real.sqrt (Discrete.squareEnergy w)

def fixedRiskPosition (hr : IsWhiteInput r μ) (σ : ℝ)
    (w : Discrete.Kernel) (t : ℤ) : Ω → ℝ :=
  fun ω => fixedRiskScale σ w * (infiniteSignalLp hr w t : Ω → ℝ) ω

def gaussianFixedRiskTurnover (σ : ℝ) (w : Discrete.Kernel) : ℝ :=
  σ * Real.sqrt (2 / Real.pi) * Real.sqrt (Discrete.rayleighQuotient w)

theorem fixedRiskPosition_sub_previous (hr : IsWhiteInput r μ) (σ : ℝ)
    (w : Discrete.Kernel) (t : ℤ) (ω : Ω) :
    fixedRiskPosition hr σ w t ω - fixedRiskPosition hr σ w (t - 1) ω =
      fixedRiskScale σ w *
         ((infiniteSignalLp hr w t : Ω → ℝ) ω -
          (infiniteSignalLp hr w (t - 1) : Ω → ℝ) ω) := by
  simp [fixedRiskPosition]
  ring

theorem fixedRiskPosition_variance [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (σ : ℝ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) (hS : 0 < Discrete.squareEnergy w) :
    Var[(fixedRiskPosition hr σ w t); μ] = σ ^ 2 := by
  rw [show fixedRiskPosition hr σ w t =
      (fun ω => fixedRiskScale σ w *
        (infiniteSignalLp hr w t : Ω → ℝ) ω) by rfl]
  rw [variance_const_mul, infiniteSignalLp_variance hr w t hw]
  dsimp [fixedRiskScale]
  rw [div_pow, Real.sq_sqrt hS.le]
  field_simp [ne_of_gt hS]

theorem fixedRiskPosition_difference_variance [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (σ : ℝ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2))
    (hS : 0 < Discrete.squareEnergy w) :
    Var[(fun ω => fixedRiskPosition hr σ w t ω -
      fixedRiskPosition hr σ w (t - 1) ω); μ] =
      σ ^ 2 * Discrete.rayleighQuotient w := by
  simp only [fixedRiskPosition]
  have hfun : (fun ω => fixedRiskScale σ w *
      (infiniteSignalLp hr w t : Ω → ℝ) ω -
        fixedRiskScale σ w * (infiniteSignalLp hr w (t - 1) : Ω → ℝ) ω) =
      (fun ω => fixedRiskScale σ w *
        ((infiniteSignalLp hr w t : Ω → ℝ) ω -
          (infiniteSignalLp hr w (t - 1) : Ω → ℝ) ω)) := by
    funext ω
    ring
  rw [hfun]
  rw [variance_const_mul,
    infiniteSignalLp_difference_variance hr w t hw hdw]
  dsimp [fixedRiskScale, Discrete.rayleighQuotient]
  rw [div_pow, Real.sq_sqrt hS.le]
  field_simp

theorem gaussianFixedRiskTurnover_integral [IsProbabilityMeasure μ]
    {r : ℤ → Ω → ℝ} (hr : IsGaussianWhiteInput r μ) (σ : ℝ)
    (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2))
    (hS : 0 < Discrete.squareEnergy w) :
    ∫ ω, |fixedRiskPosition hr.toIsWhiteInput σ w t ω -
      fixedRiskPosition hr.toIsWhiteInput σ w (t - 1) ω| ∂μ =
      gaussianFixedRiskTurnover σ w := by
  simp only [fixedRiskPosition]
  rw [show (fun ω => |fixedRiskScale σ w *
      (infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
      fixedRiskScale σ w *
        (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω|) =
      (fun ω => |fixedRiskScale σ w| *
        |(infiniteSignalLp hr.toIsWhiteInput w t : Ω → ℝ) ω -
          (infiniteSignalLp hr.toIsWhiteInput w (t - 1) : Ω → ℝ) ω|) by
    funext ω
    rw [← mul_sub, abs_mul]]
  rw [integral_const_mul,
    infiniteSignalLp_difference_integral_abs hr t hw hdw]
  have hscale : |fixedRiskScale σ w| = σ / Real.sqrt (Discrete.squareEnergy w) := by
    rw [fixedRiskScale, abs_of_nonneg]
    exact div_nonneg hσ (Real.sqrt_nonneg _)
  rw [hscale]
  have hd : 0 ≤ Discrete.differenceEnergy w :=
    tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j))
  dsimp [gaussianFixedRiskTurnover, Discrete.rayleighQuotient]
  rw [Real.sqrt_div hd]
  field_simp

theorem gaussianFixedRiskTurnover_le_iff {σ : ℝ} {w v : Discrete.Kernel}
    (hσ : 0 < σ) (hSw : 0 < Discrete.squareEnergy w)
    (hSv : 0 < Discrete.squareEnergy v) :
    gaussianFixedRiskTurnover σ w ≤ gaussianFixedRiskTurnover σ v ↔
      Discrete.rayleighQuotient w ≤ Discrete.rayleighQuotient v := by
  have hwq : 0 ≤ Discrete.rayleighQuotient w := by
    exact div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j))) hSw.le
  have hvq : 0 ≤ Discrete.rayleighQuotient v := by
    exact div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j))) hSv.le
  have hc : 0 < σ * Real.sqrt (2 / Real.pi) := by positivity
  dsimp [gaussianFixedRiskTurnover]
  constructor
  · intro h
    have h' : Real.sqrt (Discrete.rayleighQuotient w) ≤
        Real.sqrt (Discrete.rayleighQuotient v) := by
      nlinarith
    exact (Real.sqrt_le_sqrt_iff hvq).mp h'
  · intro h
    have h' : Real.sqrt (Discrete.rayleighQuotient w) ≤
        Real.sqrt (Discrete.rayleighQuotient v) :=
      (Real.sqrt_le_sqrt_iff hvq).mpr h
    nlinarith

theorem gaussianFixedRiskTurnover_isMinOn_iff {σ : ℝ} {A : Set Discrete.Kernel}
    {w : Discrete.Kernel} (hwA : w ∈ A)
    (hA : ∀ u ∈ A, 0 < Discrete.squareEnergy u)
    (hσ : 0 < σ) :
    IsMinOn (gaussianFixedRiskTurnover σ) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro h v hv
    exact (gaussianFixedRiskTurnover_le_iff hσ (hA w hwA) (hA v hv)).mp (h hv)
  · intro h v hv
    exact (gaussianFixedRiskTurnover_le_iff hσ (hA w hwA) (hA v hv)).mpr (h hv)

theorem gaussianFixedRiskTurnover_integral_admissible [IsProbabilityMeasure μ]
    {r : ℤ → Ω → ℝ} {h L : ℝ} {w : Discrete.Kernel}
    (hr : IsGaussianWhiteInput r μ) (σ : ℝ) (t : ℤ)
    (hw : Discrete.IsAdmissible h L w) (hσ : 0 ≤ σ) :
    ∫ ω, |fixedRiskPosition hr.toIsWhiteInput σ w t ω -
      fixedRiskPosition hr.toIsWhiteInput σ w (t - 1) ω| ∂μ =
      gaussianFixedRiskTurnover σ w :=
  gaussianFixedRiskTurnover_integral hr σ w t hσ hw.summable_sq
    hw.summable_difference_sq hw.squareEnergy_pos

end RayleighKernel.Probability
