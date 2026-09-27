import RayleighKernel.Probability.ProjectionScale

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology NNReal
namespace RayleighKernel.Probability

variable {Ω ΩZ : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩZ]
variable {r : ℤ → Ω → ℝ} {μ : Measure Ω} {Z : ΩZ → ℝ} {ν : Measure ΩZ}
variable {c : ℝ≥0 → ℝ}
variable {σr : ℝ}

def aggregateCostProfile (c : ℝ≥0 → ℝ) (σ : ℝ)
    (Z : ΩZ → ℝ) (ν : Measure ΩZ) (q : ℝ) : ℝ :=
  ∫ z, c ‖σ * Real.sqrt q * Z z‖₊ ∂ν

def finiteSquareEnergy (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  ∑ j ∈ Finset.range N, (w j)^2

def finiteDifferenceEnergy (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  ∑ j ∈ Finset.range (N+1), (Discrete.difference w j)^2

def finiteRayleighQuotient (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  finiteDifferenceEnergy N w / finiteSquareEnergy N w

def projectionFixedRiskScale (σ σr : ℝ) (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  σ / (σr * Real.sqrt (finiteSquareEnergy N w))

def projectionFixedRiskPosition (σ σr : ℝ) (N : ℕ) (w : Discrete.Kernel)
    (r : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω

omit [MeasurableSpace Ω] in
theorem projectionFixedRiskPosition_sub_previous (σ σr : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (r : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) (hwN : w N = 0) :
    projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω =
    projectionFixedRiskScale σ σr N w *
        finiteSignal (N + 1) (Discrete.difference w) r t ω := by
  change projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω -
      projectionFixedRiskScale σ σr N w * finiteSignal N w r (t - 1) ω = _
  rw [← mul_sub, congrFun (finiteSignal_sub_previous N w r t hwN) ω]

theorem projectionFixedRiskPosition_difference_identDistrib
    (h : ProjectionScaleWhite r μ Z ν σr) (σ : ℝ) (N : ℕ) (w : Discrete.Kernel)
    (t : ℤ) (_hσ : 0 ≤ σ) (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    IdentDistrib
      (fun ω => projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω)
      (fun z => σ * Real.sqrt (finiteRayleighQuotient N w) * Z z) μ ν := by
  have hlaw := h.projection (N + 1) (Discrete.difference w) t
  rw [← finiteSignal_sub_previous N w r t hwN] at hlaw
  have hscaled := hlaw.const_mul (projectionFixedRiskScale σ σr N w)
  have hD : 0 ≤ finiteDifferenceEnergy N w := by
    exact Finset.sum_nonneg (fun j hj => sq_nonneg (Discrete.difference w j))
  have hsqrt : Real.sqrt (finiteSquareEnergy N w) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hS)
  have hscale : (fun z => projectionFixedRiskScale σ σr N w *
      (σr * Real.sqrt (finiteDifferenceEnergy N w) * Z z)) =
      (fun z => σ * Real.sqrt (finiteRayleighQuotient N w) * Z z) := by
    funext z
    dsimp [projectionFixedRiskScale, finiteRayleighQuotient,
      finiteDifferenceEnergy, finiteSquareEnergy]
    have hsqrtdiv : Real.sqrt (finiteDifferenceEnergy N w /
        finiteSquareEnergy N w) = Real.sqrt (finiteDifferenceEnergy N w) /
          Real.sqrt (finiteSquareEnergy N w) := Real.sqrt_div hD _
    have hroot : Real.sqrt (finiteRayleighQuotient N w) =
        Real.sqrt (finiteDifferenceEnergy N w) /
          Real.sqrt (finiteSquareEnergy N w) := by
      simpa [finiteRayleighQuotient] using hsqrtdiv
    have hroot' : Real.sqrt ((∑ j ∈ Finset.range (N + 1),
        (Discrete.difference w j)^2) / (∑ j ∈ Finset.range N, (w j)^2)) =
        Real.sqrt (∑ j ∈ Finset.range (N + 1), (Discrete.difference w j)^2) /
          Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) := Real.sqrt_div hD _
    rw [hroot']
    field_simp [ne_of_gt h.scale_pos, hsqrt]
  have hleft : (fun ω => projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω) =
      (fun ω => projectionFixedRiskScale σ σr N w *
        (finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω)) := by
    funext ω
    simp only [projectionFixedRiskPosition]
    ring
  simp only [projectionFixedRiskPosition]
  rw [show (fun ω => projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω -
      projectionFixedRiskScale σ σr N w * finiteSignal N w r (t - 1) ω) =
      (fun ω => projectionFixedRiskScale σ σr N w *
        (finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω)) by
          funext ω; ring]
  convert hscaled using 1
  · funext z
    simpa [finiteDifferenceEnergy] using (congrFun hscale z).symm

theorem aggregateCostProfile_eq_of_identDistrib
    (hc : Measurable c) {f : Ω → ℝ} {g : ΩZ → ℝ}
    (hfg : IdentDistrib f g μ ν) :
    (∫ ω, c ‖f ω‖₊ ∂μ) = ∫ z, c ‖g z‖₊ ∂ν := by
  simpa only [Function.comp_apply] using
    (hfg.comp (hc.comp measurable_nnnorm)).integral_eq

theorem projectionFixedRiskPosition_aggregateCost
    (h : ProjectionScaleWhite r μ Z ν σr) (c : ℝ≥0 → ℝ) (hc : Measurable c)
    (σ : ℝ) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    (∫ ω, c ‖projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω‖₊ ∂μ) =
      aggregateCostProfile c σ Z ν (finiteRayleighQuotient N w) := by
  rw [aggregateCostProfile]
  exact aggregateCostProfile_eq_of_identDistrib hc
    (projectionFixedRiskPosition_difference_identDistrib h σ N w t hσ hS hwN)

theorem squareEnergy_eq_finiteSquareEnergy (N : ℕ) (w : Discrete.Kernel)
    (htail : ∀ j, N ≤ j → w j = 0) :
    Discrete.squareEnergy w = finiteSquareEnergy N w := by
  rw [Discrete.squareEnergy, tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro j hj
    have hjN : N ≤ j := by simpa [Finset.mem_range] using hj
    simp [htail j hjN]

theorem differenceEnergy_eq_finiteDifferenceEnergy (N : ℕ) (w : Discrete.Kernel)
    (htail : ∀ j, N ≤ j → w j = 0) :
    Discrete.differenceEnergy w = finiteDifferenceEnergy N w := by
  rw [Discrete.differenceEnergy,
    tsum_eq_sum (s := Finset.range (N + 1))]
  · rfl
  · intro j hj
    have hjN : N + 1 ≤ j := by simpa [Finset.mem_range] using hj
    cases j with
    | zero => omega
    | succ k =>
      have hk : N ≤ k := by omega
      simp [Discrete.difference, htail k hk, htail (k + 1) (by omega)]

theorem rayleighQuotient_eq_finiteRayleighQuotient (N : ℕ) (w : Discrete.Kernel)
    (htail : ∀ j, N ≤ j → w j = 0) :
    Discrete.rayleighQuotient w = finiteRayleighQuotient N w := by
  simp only [Discrete.rayleighQuotient, finiteRayleighQuotient,
    squareEnergy_eq_finiteSquareEnergy N w htail,
    differenceEnergy_eq_finiteDifferenceEnergy N w htail]

theorem reference_not_ae_zero
    (h : ProjectionScaleWhite r μ Z ν σr) : ¬ Z =ᵐ[ν] 0 := by
  intro hZ
  have hZsq : (fun z => Z z ^ 2) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    filter_upwards [hZ] with z hz
    simp [hz]
  have hzero : ∫ z, (Z z)^2 ∂ν = 0 := by
    simpa using integral_congr_ae hZsq
  linarith [h.reference_secondMoment, hzero]

theorem projectionFixedRiskPosition_aggregateCost_of_cutoff
    (h : ProjectionScaleWhite r μ Z ν σr) (c : ℝ≥0 → ℝ) (hc : Measurable c)
    (σ : ℝ) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < Discrete.squareEnergy w)
    (htail : ∀ j, N ≤ j → w j = 0) :
    (∫ ω, c ‖projectionFixedRiskPosition σ σr N w r t ω -
      projectionFixedRiskPosition σ σr N w r (t - 1) ω‖₊ ∂μ) =
      aggregateCostProfile c σ Z ν (Discrete.rayleighQuotient w) := by
  have hSf : 0 < finiteSquareEnergy N w := by
    rw [← squareEnergy_eq_finiteSquareEnergy N w htail]
    exact hS
  have hwN : w N = 0 := htail N le_rfl
  rw [projectionFixedRiskPosition_aggregateCost h c hc σ N w t hσ hSf hwN]
  rw [rayleighQuotient_eq_finiteRayleighQuotient N w htail]

theorem aggregateCostProfile_strictMonoOn (c : ℝ≥0 → ℝ) (σ : ℝ)
    (Z : ΩZ → ℝ) (ν : Measure ΩZ) (hc : StrictMono c) (hσ : 0 < σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν)
    (hZ : ¬ Z =ᵐ[ν] 0) :
    StrictMonoOn (aggregateCostProfile c σ Z ν) (Set.Ici 0) := by
  intro q hq q' hq' hqq'
  have hle : (fun z => c ‖σ * Real.sqrt q * Z z‖₊) ≤ᵐ[ν]
      (fun z => c ‖σ * Real.sqrt q' * Z z‖₊) := by
    filter_upwards [] with z
    apply hc.monotone
    simp only [nnnorm_mul, Real.nnnorm_of_nonneg hσ.le,
      Real.nnnorm_of_nonneg (Real.sqrt_nonneg q),
      Real.nnnorm_of_nonneg (Real.sqrt_nonneg q')]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqq'.le) (by positivity)) (by positivity)
  have hIntLe := integral_mono_ae (hint q hq) (hint q' hq') hle
  apply lt_of_le_of_ne hIntLe
  intro heq
  have hae := (integral_eq_iff_of_ae_le (hint q hq) (hint q' hq') hle).mp heq
  apply hZ
  filter_upwards [hae] with z hz
  by_contra hz0
  have hsqrt : Real.sqrt q < Real.sqrt q' := Real.sqrt_lt_sqrt hq hqq'
  have hsqrtnorm : ‖Real.sqrt q‖ < ‖Real.sqrt q'‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg q),
      abs_of_nonneg (Real.sqrt_nonneg q')] using hsqrt
  have hZpos : 0 < ‖Z z‖ := norm_pos_iff.mpr hz0
  have harg : ‖σ * Real.sqrt q * Z z‖₊ < ‖σ * Real.sqrt q' * Z z‖₊ := by
    apply_mod_cast (show ‖σ * Real.sqrt q * Z z‖ <
        ‖σ * Real.sqrt q' * Z z‖ by
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hsqrtnorm (by simpa [abs_of_pos hσ])) hZpos)
  exact (ne_of_lt (hc harg)) hz

theorem ProjectionScaleWhite.aggregateCostProfile_strictMonoOn
    (h : ProjectionScaleWhite r μ Z ν σr) (c : ℝ≥0 → ℝ) (σ : ℝ)
    (hc : StrictMono c) (hσ : 0 < σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν) :
    StrictMonoOn (aggregateCostProfile c σ Z ν) (Set.Ici 0) :=
  _root_.RayleighKernel.Probability.aggregateCostProfile_strictMonoOn
    c σ Z ν hc hσ hint (reference_not_ae_zero h)

theorem aggregateCostProfile_monoOn (c : ℝ≥0 → ℝ) (σ : ℝ) (Z : ΩZ → ℝ)
    (ν : Measure ΩZ) (hc : Monotone c) (hσ : 0 ≤ σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν) :
    MonotoneOn (aggregateCostProfile c σ Z ν) (Set.Ici 0) := by
  intro q hq q' hq' hqq'
  apply integral_mono (hint q hq) (hint q' hq')
  intro z
  apply hc
  simp only [nnnorm_mul, Real.nnnorm_of_nonneg hσ,
    Real.nnnorm_of_nonneg (Real.sqrt_nonneg q),
    Real.nnnorm_of_nonneg (Real.sqrt_nonneg q')]
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact_mod_cast Real.sqrt_le_sqrt hqq'
    · positivity
  · positivity

theorem aggregateCostProfile_isMinOn_of_isMinOn
    {A : Set Discrete.Kernel} {Ψ : ℝ → ℝ} {w : Discrete.Kernel}
    (hΨ : MonotoneOn Ψ (Set.Ici 0))
    (hw : w ∈ A) (hnonneg : ∀ v ∈ A, 0 ≤ Discrete.rayleighQuotient v)
    (hmin : IsMinOn Discrete.rayleighQuotient A w) :
    IsMinOn (fun v => Ψ (Discrete.rayleighQuotient v)) A w := by
  intro v hv
  exact hΨ (hnonneg w hw) (hnonneg v hv) (hmin hv)

theorem isMinOn_iff_of_strictMonoOn
    {A : Set Discrete.Kernel} {Ψ : ℝ → ℝ} {w : Discrete.Kernel}
    (hΨ : StrictMonoOn Ψ (Set.Ici 0)) (hw : w ∈ A)
    (hnonneg : ∀ v ∈ A, 0 ≤ Discrete.rayleighQuotient v) :
    IsMinOn (fun v => Ψ (Discrete.rayleighQuotient v)) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro h v hv
    by_contra hnot
    have hlt : Discrete.rayleighQuotient v < Discrete.rayleighQuotient w :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge (h hv) (hΨ (hnonneg v hv) (hnonneg w hw) hlt))
  · intro h v hv
    exact hΨ.monotoneOn (hnonneg w hw) (hnonneg v hv) (h hv)

theorem aggregateCostProfile_isMinOn_of_rayleigh_isMinOn
    {A : Set Discrete.Kernel} {w : Discrete.Kernel}
    (c : ℝ≥0 → ℝ) (σ : ℝ) (Z : ΩZ → ℝ) (ν : Measure ΩZ)
    (hc : Monotone c) (hσ : 0 ≤ σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν)
    (hw : w ∈ A) (hnonneg : ∀ v ∈ A, 0 ≤ Discrete.rayleighQuotient v)
    (hmin : IsMinOn Discrete.rayleighQuotient A w) :
    IsMinOn (fun v => aggregateCostProfile c σ Z ν
      (Discrete.rayleighQuotient v)) A w :=
  aggregateCostProfile_isMinOn_of_isMinOn
    (aggregateCostProfile_monoOn c σ Z ν hc hσ hint) hw hnonneg hmin

theorem aggregateCostProfile_isMinOn_iff_rayleigh_isMinOn
    {A : Set Discrete.Kernel} {w : Discrete.Kernel}
    (c : ℝ≥0 → ℝ) (σ : ℝ) (Z : ΩZ → ℝ) (ν : Measure ΩZ)
    (hc : StrictMono c) (hσ : 0 < σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν)
    (hZ : ¬ Z =ᵐ[ν] 0) (hw : w ∈ A)
    (hnonneg : ∀ v ∈ A, 0 ≤ Discrete.rayleighQuotient v) :
    IsMinOn (fun v => aggregateCostProfile c σ Z ν
      (Discrete.rayleighQuotient v)) A w ↔
      IsMinOn Discrete.rayleighQuotient A w :=
  isMinOn_iff_of_strictMonoOn
    (aggregateCostProfile_strictMonoOn c σ Z ν hc hσ hint hZ) hw hnonneg

theorem ProjectionScaleWhite.aggregateCostProfile_isMinOn_iff_rayleigh_isMinOn
    (h : ProjectionScaleWhite r μ Z ν σr) {A : Set Discrete.Kernel}
    {w : Discrete.Kernel} (c : ℝ≥0 → ℝ) (σ : ℝ) (hc : StrictMono c)
    (hσ : 0 < σ)
    (hint : ∀ q ∈ Set.Ici (0 : ℝ), Integrable (fun z =>
      c ‖σ * Real.sqrt q * Z z‖₊) ν) (hw : w ∈ A)
    (hnonneg : ∀ v ∈ A, 0 ≤ Discrete.rayleighQuotient v) :
    IsMinOn (fun v => aggregateCostProfile c σ Z ν
      (Discrete.rayleighQuotient v)) A w ↔
      IsMinOn Discrete.rayleighQuotient A w :=
  _root_.RayleighKernel.Probability.aggregateCostProfile_isMinOn_iff_rayleigh_isMinOn
    c σ Z ν hc hσ hint
    (reference_not_ae_zero h) hw hnonneg

end RayleighKernel.Probability
