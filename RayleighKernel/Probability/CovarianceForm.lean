import RayleighKernel.Probability.Rademacher

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology
namespace RayleighKernel.Probability

def finiteCovarianceForm (Γ : ℕ → ℕ → ℝ) (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, w j * Γ j k * w k

def finiteGeneralizedRayleighQuotient (Γ : ℕ → ℕ → ℝ) (N : ℕ)
    (w : Discrete.Kernel) : ℝ :=
  finiteCovarianceForm Γ (N + 1) (Discrete.difference w) /
    finiteCovarianceForm Γ N w

def scalarIdentityCovariance (q : ℝ) : ℕ → ℕ → ℝ :=
  fun j k => if j = k then q else 0

theorem finiteCovarianceForm_scalarIdentity (q : ℝ) (N : ℕ) (w : Discrete.Kernel) :
    finiteCovarianceForm (scalarIdentityCovariance q) N w =
      q * finiteSquareEnergy N w := by
  classical
  unfold finiteCovarianceForm finiteSquareEnergy
  simp only [scalarIdentityCovariance, mul_ite, ite_mul, mul_zero, zero_mul]
  simp_rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  simp only [Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]
  ring

theorem finiteGeneralizedRayleighQuotient_scalarIdentity (q : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (hq : 0 < q) (hS : 0 < finiteSquareEnergy N w) :
    finiteGeneralizedRayleighQuotient (scalarIdentityCovariance q) N w =
      finiteRayleighQuotient N w := by
  rw [finiteGeneralizedRayleighQuotient,
    finiteCovarianceForm_scalarIdentity,
    finiteCovarianceForm_scalarIdentity,
    show finiteSquareEnergy (N + 1) (Discrete.difference w) =
      finiteDifferenceEnergy N w by rfl,
    finiteRayleighQuotient]
  field_simp [ne_of_gt hq, ne_of_gt hS]

structure FiniteCovarianceModel {Ω : Type*} [MeasurableSpace Ω]
    (r : ℤ → Ω → ℝ) (μ : Measure Ω) (Γ : ℕ → ℕ → ℝ) (cEll : ℝ) : Prop where
  projection_memLp : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    MemLp (finiteSignal N w r t) 2 μ
  projection_centered : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    ∫ ω, finiteSignal N w r t ω ∂μ = 0
  projection_secondMoment : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    ∫ ω, (finiteSignal N w r t ω)^2 ∂μ = finiteCovarianceForm Γ N w
  projection_integral_abs : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    ∫ ω, |finiteSignal N w r t ω| ∂μ = cEll * Real.sqrt (finiteCovarianceForm Γ N w)

theorem finiteCovarianceForm_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ} {μ : Measure Ω}
    {Γ : ℕ → ℕ → ℝ} {cEll : ℝ} (h : FiniteCovarianceModel r μ Γ cEll)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    0 ≤ finiteCovarianceForm Γ N w := by
  rw [← h.projection_secondMoment N w t]
  exact integral_nonneg (fun ω => sq_nonneg (finiteSignal N w r t ω))

def finiteCorrelatedFixedRiskScale (σ : ℝ) (Γ : ℕ → ℕ → ℝ)
    (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  σ / Real.sqrt (finiteCovarianceForm Γ N w)

def finiteCorrelatedFixedRiskPosition {Ω : Type*}
    (σ : ℝ) (Γ : ℕ → ℕ → ℝ) (N : ℕ) (w : Discrete.Kernel)
    (r : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => finiteCorrelatedFixedRiskScale σ Γ N w * finiteSignal N w r t ω

theorem finiteCorrelatedFixedRiskPosition_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {Γ : ℕ → ℕ → ℝ} {cEll σ : ℝ}
    (h : FiniteCovarianceModel r μ Γ cEll) (N : ℕ) (w : Discrete.Kernel) (t : ℤ)
    (hQ : 0 < finiteCovarianceForm Γ N w) :
    Var[finiteCorrelatedFixedRiskPosition σ Γ N w r t; μ] = σ ^ 2 := by
  rw [show finiteCorrelatedFixedRiskPosition σ Γ N w r t =
      (fun ω => finiteCorrelatedFixedRiskScale σ Γ N w * finiteSignal N w r t ω) by rfl]
  rw [variance_const_mul]
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (h.projection_memLp N w t).aemeasurable (h.projection_centered N w t)]
  rw [h.projection_secondMoment N w t]
  dsimp [finiteCorrelatedFixedRiskScale]
  rw [div_pow, Real.sq_sqrt hQ.le]
  field_simp

theorem finiteCorrelatedFixedRiskPosition_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {Γ : ℕ → ℕ → ℝ} {cEll σ : ℝ}
    (h : FiniteCovarianceModel r μ Γ cEll) (N : ℕ) (w : Discrete.Kernel) (t : ℤ)
    (hσ : 0 ≤ σ) (hQ : 0 < finiteCovarianceForm Γ N w) (hwN : w N = 0) :
    ∫ ω, |finiteCorrelatedFixedRiskPosition σ Γ N w r t ω -
      finiteCorrelatedFixedRiskPosition σ Γ N w r (t - 1) ω| ∂μ =
      cEll * σ * Real.sqrt
        (finiteGeneralizedRayleighQuotient Γ N w) := by
  simp only [finiteCorrelatedFixedRiskPosition]
  rw [show (fun ω => |finiteCorrelatedFixedRiskScale σ Γ N w * finiteSignal N w r t ω -
      finiteCorrelatedFixedRiskScale σ Γ N w * finiteSignal N w r (t - 1) ω|) =
      (fun ω => |finiteCorrelatedFixedRiskScale σ Γ N w| *
        |finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω|) by
          funext ω; rw [← mul_sub, abs_mul]]
  rw [integral_const_mul]
  rw [show (fun ω => |finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω|) =
      (fun ω => |finiteSignal (N + 1) (Discrete.difference w) r t ω|) by
        funext ω
        rw [congrFun (finiteSignal_sub_previous N w r t hwN) ω]]
  rw [h.projection_integral_abs]
  have hscale : |finiteCorrelatedFixedRiskScale σ Γ N w| =
      σ / Real.sqrt (finiteCovarianceForm Γ N w) := by
    rw [finiteCorrelatedFixedRiskScale, abs_of_nonneg]
    exact div_nonneg hσ (Real.sqrt_nonneg _)
  rw [hscale]
  have hD : 0 ≤ finiteCovarianceForm Γ (N + 1) (Discrete.difference w) :=
    finiteCovarianceForm_nonneg h (N + 1) (Discrete.difference w) t
  dsimp [finiteGeneralizedRayleighQuotient]
  rw [Real.sqrt_div hD]
  field_simp [ne_of_gt hQ]

end RayleighKernel.Probability
