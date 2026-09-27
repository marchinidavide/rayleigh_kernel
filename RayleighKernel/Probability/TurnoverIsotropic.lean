import RayleighKernel.Probability.AggregateCost

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology NNReal
namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {r : ℤ → Ω → ℝ}
variable {σr mr σ : ℝ} {N : ℕ} {t : ℤ}

structure TurnoverIsotropicWhite (r : ℤ → Ω → ℝ) (μ : Measure Ω)
    (σr mr : ℝ) : Prop where
  scale_pos : 0 < σr
  absScale_pos : 0 < mr
  coordinate_memLp : ∀ t, MemLp (r t) 2 μ
  coordinate_integral : ∀ t, ∫ ω, r t ω ∂μ = 0
  projection_secondMoment : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    ∫ ω, (finiteSignal N w r t ω)^2 ∂μ =
      σr^2 * finiteSquareEnergy N w
  projection_integral_abs : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    ∫ ω, |finiteSignal N w r t ω| ∂μ =
      mr * Real.sqrt (finiteSquareEnergy N w)

theorem TurnoverIsotropicWhite.projection_memLp
    (h : TurnoverIsotropicWhite r μ σr mr) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    MemLp (finiteSignal N w r t) 2 μ := by
  unfold finiteSignal
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' (Finset.range N)
      (f := fun j ω => w j * r (t - (j : ℤ)) ω)
      (fun j hj => (h.coordinate_memLp (t - (j : ℤ))).const_mul (w j)))

theorem TurnoverIsotropicWhite.projection_integral [IsProbabilityMeasure μ]
    (h : TurnoverIsotropicWhite r μ σr mr) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    ∫ ω, finiteSignal N w r t ω ∂μ = 0 := by
  unfold finiteSignal
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, h.coordinate_integral]
    simp
  · intro j hj
    exact ((h.coordinate_memLp (t - (j : ℤ))).const_mul (w j)).integrable one_le_two

theorem TurnoverIsotropicWhite.projection_variance [IsProbabilityMeasure μ]
    (h : TurnoverIsotropicWhite r μ σr mr) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    Var[finiteSignal N w r t; μ] = σr^2 * finiteSquareEnergy N w := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (h.projection_memLp N w t).aemeasurable (h.projection_integral N w t)]
  exact h.projection_secondMoment N w t

def turnoverIsotropicFixedRiskTurnover (mr σr σ : ℝ)
    (w : Discrete.Kernel) : ℝ :=
  (mr / σr) * σ * Real.sqrt (Discrete.rayleighQuotient w)

theorem turnoverIsotropicFixedRiskPosition_variance [IsProbabilityMeasure μ]
    (h : TurnoverIsotropicWhite r μ σr mr) (σ : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hS : 0 < finiteSquareEnergy N w) :
    Var[projectionFixedRiskPosition σ σr N w r t; μ] = σ^2 := by
  rw [show projectionFixedRiskPosition σ σr N w r t =
      (fun ω => projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω) by rfl]
  rw [variance_const_mul, h.projection_variance N w t]
  dsimp [projectionFixedRiskScale]
  rw [div_pow]
  field_simp [ne_of_gt h.scale_pos, ne_of_gt hS]
  rw [Real.sq_sqrt hS.le]

theorem turnoverIsotropicFixedRiskPosition_integral_abs
    (h : TurnoverIsotropicWhite r μ σr mr) (σ : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    ∫ ω, |projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω| ∂μ =
      (mr / σr) * σ * Real.sqrt (finiteRayleighQuotient N w) := by
  simp only [projectionFixedRiskPosition]
  rw [show (fun ω => |projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω -
      projectionFixedRiskScale σ σr N w * finiteSignal N w r (t - 1) ω|) =
      (fun ω => |projectionFixedRiskScale σ σr N w| *
        |finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω|) by
          funext ω
          rw [← mul_sub, abs_mul]]
  rw [integral_const_mul]
  rw [show (fun ω => |finiteSignal N w r t ω -
      finiteSignal N w r (t - 1) ω|) =
      (fun ω => |finiteSignal (N + 1) (Discrete.difference w) r t ω|) by
        funext ω
        rw [congrFun (finiteSignal_sub_previous N w r t hwN) ω]]
  rw [h.projection_integral_abs]
  rw [show finiteSquareEnergy (N + 1) (Discrete.difference w) =
      finiteDifferenceEnergy N w by rfl]
  have hscale : |projectionFixedRiskScale σ σr N w| =
      σ / (σr * Real.sqrt (finiteSquareEnergy N w)) := by
    rw [projectionFixedRiskScale, abs_of_nonneg]
    exact div_nonneg hσ (mul_nonneg h.scale_pos.le (Real.sqrt_nonneg _))
  rw [hscale]
  have hD : 0 ≤ finiteDifferenceEnergy N w :=
    Finset.sum_nonneg (fun j hj => sq_nonneg (Discrete.difference w j))
  dsimp [finiteRayleighQuotient]
  rw [Real.sqrt_div hD]
  field_simp [ne_of_gt h.scale_pos, ne_of_gt hS]

theorem turnoverIsotropicFixedRiskPosition_integral_abs_of_cutoff
    (h : TurnoverIsotropicWhite r μ σr mr) (σ : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < Discrete.squareEnergy w)
    (htail : ∀ j, N ≤ j → w j = 0) :
    ∫ ω, |projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω| ∂μ =
      turnoverIsotropicFixedRiskTurnover mr σr σ w := by
  have hSf : 0 < finiteSquareEnergy N w := by
    rw [← squareEnergy_eq_finiteSquareEnergy N w htail]
    exact hS
  have hwN : w N = 0 := htail N le_rfl
  rw [turnoverIsotropicFixedRiskPosition_integral_abs h σ N w t hσ hSf hwN]
  simp [turnoverIsotropicFixedRiskTurnover,
    rayleighQuotient_eq_finiteRayleighQuotient N w htail]

theorem turnoverIsotropicFixedRiskTurnover_le_iff
    (h : TurnoverIsotropicWhite r μ σr mr) {σ : ℝ}
    {w v : Discrete.Kernel} (hσ : 0 < σ)
    (hSw : 0 < Discrete.squareEnergy w) (hSv : 0 < Discrete.squareEnergy v) :
    turnoverIsotropicFixedRiskTurnover mr σr σ w ≤
        turnoverIsotropicFixedRiskTurnover mr σr σ v ↔
      Discrete.rayleighQuotient w ≤ Discrete.rayleighQuotient v := by
  have hwq : 0 ≤ Discrete.rayleighQuotient w := by
    exact div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j))) hSw.le
  have hvq : 0 ≤ Discrete.rayleighQuotient v := by
    exact div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j))) hSv.le
  have hc : 0 < (mr / σr) * σ :=
    mul_pos (div_pos h.absScale_pos h.scale_pos) hσ
  dsimp [turnoverIsotropicFixedRiskTurnover]
  constructor
  · intro hle
    have hsqrt : Real.sqrt (Discrete.rayleighQuotient w) ≤
        Real.sqrt (Discrete.rayleighQuotient v) := by nlinarith
    exact (Real.sqrt_le_sqrt_iff hvq).mp hsqrt
  · intro hle
    have hsqrt : Real.sqrt (Discrete.rayleighQuotient w) ≤
        Real.sqrt (Discrete.rayleighQuotient v) :=
      (Real.sqrt_le_sqrt_iff hvq).mpr hle
    nlinarith

theorem turnoverIsotropicFixedRiskTurnover_isMinOn_iff
    (ht : TurnoverIsotropicWhite r μ σr mr)
    {A : Set Discrete.Kernel} {w : Discrete.Kernel} (hwA : w ∈ A)
    (hA : ∀ u ∈ A, 0 < Discrete.squareEnergy u) (hσ : 0 < σ) :
    IsMinOn (turnoverIsotropicFixedRiskTurnover mr σr σ) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro hmin v hv
    exact (turnoverIsotropicFixedRiskTurnover_le_iff ht
      hσ (hA w hwA) (hA v hv)).mp (hmin hv)
  · intro hmin v hv
    exact (turnoverIsotropicFixedRiskTurnover_le_iff ht
      hσ (hA w hwA) (hA v hv)).mpr (hmin hv)

theorem turnoverIsotropicFixedRiskPosition_integral_isMinOn_iff
    (h : TurnoverIsotropicWhite r μ σr mr) [IsProbabilityMeasure μ]
    {σ : ℝ} {N : ℕ} {t : ℤ} {A : Set Discrete.Kernel} {w : Discrete.Kernel}
    (hwA : w ∈ A) (hA : ∀ u ∈ A, 0 < Discrete.squareEnergy u)
    (htail : ∀ u ∈ A, ∀ j, N ≤ j → u j = 0) (hσ : 0 < σ) :
    IsMinOn (fun u => ∫ ω, |projectionFixedRiskPosition σ σr N u r t ω -
      projectionFixedRiskPosition σ σr N u r (t - 1) ω| ∂μ) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro hmin v hv
    have hminv := hmin hv
    change (∫ ω, |projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω| ∂μ) ≤
      ∫ ω, |projectionFixedRiskPosition σ σr N v r t ω -
        projectionFixedRiskPosition σ σr N v r (t - 1) ω| ∂μ at hminv
    rw [turnoverIsotropicFixedRiskPosition_integral_abs_of_cutoff h σ N v t hσ.le
      (hA v hv) (htail v hv)] at hminv
    rw [turnoverIsotropicFixedRiskPosition_integral_abs_of_cutoff h σ N w t hσ.le
      (hA w hwA) (htail w hwA)] at hminv
    exact (turnoverIsotropicFixedRiskTurnover_le_iff h hσ (hA w hwA) (hA v hv)).mp hminv
  · intro hmin v hv
    have hq := hmin hv
    change (∫ ω, |projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω| ∂μ) ≤
      ∫ ω, |projectionFixedRiskPosition σ σr N v r t ω -
        projectionFixedRiskPosition σ σr N v r (t - 1) ω| ∂μ
    rw [turnoverIsotropicFixedRiskPosition_integral_abs_of_cutoff h σ N v t hσ.le
      (hA v hv) (htail v hv)]
    rw [turnoverIsotropicFixedRiskPosition_integral_abs_of_cutoff h σ N w t hσ.le
      (hA w hwA) (htail w hwA)]
    exact (turnoverIsotropicFixedRiskTurnover_le_iff h hσ (hA w hwA) (hA v hv)).mpr hq

end RayleighKernel.Probability
