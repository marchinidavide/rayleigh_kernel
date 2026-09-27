import RayleighKernel.Probability.FiniteDifferences

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology
namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {r : ℤ → Ω → ℝ} {σr g mrg η σ : ℝ}

structure PowerProjectionIsotropic (r : ℤ → Ω → ℝ) (μ : Measure Ω)
    (σr mrg g : ℝ) : Prop where
  scale_pos : 0 < σr
  momentScale_pos : 0 < mrg
  exponent_one_le : 1 ≤ g
  coordinate_memLp : ∀ t, MemLp (r t) 2 μ
  coordinate_centered : ∀ t, ∫ ω, r t ω ∂μ = 0
  projection_secondMoment : ∀ N (w : Discrete.Kernel) t,
    ∫ ω, (finiteSignal N w r t ω)^2 ∂μ = σr^2 * finiteSquareEnergy N w
  projection_abs_gMoment : ∀ N (w : Discrete.Kernel) t,
    ∫ ω, |finiteSignal N w r t ω| ^ g ∂μ =
      mrg * Real.rpow (finiteSquareEnergy N w) (g / 2)

theorem PowerProjectionIsotropic.projection_memLp
    (h : PowerProjectionIsotropic r μ σr mrg g) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) : MemLp (finiteSignal N w r t) 2 μ := by
  unfold finiteSignal
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' (Finset.range N)
      (f := fun j ω => w j * r (t - (j : ℤ)) ω)
      (fun j hj => (h.coordinate_memLp (t - (j : ℤ))).const_mul (w j)))

theorem PowerProjectionIsotropic.projection_integral_zero [IsProbabilityMeasure μ]
    (h : PowerProjectionIsotropic r μ σr mrg g) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) :
    ∫ ω, finiteSignal N w r t ω ∂μ = 0 := by
  unfold finiteSignal
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, h.coordinate_centered]
    simp
  · intro j hj
    exact ((h.coordinate_memLp (t - (j : ℤ))).const_mul (w j)).integrable one_le_two

theorem PowerProjectionIsotropic.projection_variance [IsProbabilityMeasure μ]
    (h : PowerProjectionIsotropic r μ σr mrg g) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) :
    Var[finiteSignal N w r t; μ] = σr^2 * finiteSquareEnergy N w := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (h.projection_memLp N w t).aemeasurable (h.projection_integral_zero N w t)]
  exact h.projection_secondMoment N w t

def powerFixedRiskCost (η mrg σr σ g q : ℝ) : ℝ :=
  η * (mrg / Real.rpow σr g) * Real.rpow σ g * Real.rpow q (g / 2)

theorem sqrt_rpow {S g : ℝ} (hS : 0 ≤ S) :
    Real.rpow (Real.sqrt S) g = Real.rpow S (g / 2) := by
  calc
    Real.rpow (Real.sqrt S) g = Real.rpow (Real.rpow S (1 / 2)) g := by
      congr 1; exact Real.sqrt_eq_rpow S
    _ = Real.rpow S ((1 / 2) * g) := (Real.rpow_mul hS (1 / 2) g).symm
    _ = Real.rpow S (g / 2) := by congr 1; ring

theorem product_scale_rpow {σr S g : ℝ} (hS : 0 ≤ S) (hsr : 0 ≤ σr) :
    Real.rpow (σr * Real.sqrt S) g =
      Real.rpow σr g * Real.rpow S (g / 2) := by
  calc
    Real.rpow (σr * Real.sqrt S) g =
        Real.rpow σr g * Real.rpow (Real.sqrt S) g :=
      Real.mul_rpow hsr (Real.sqrt_nonneg S)
    _ = _ := by rw [sqrt_rpow hS]

theorem quotient_scale_rpow {σ σr S g : ℝ} (hσ : 0 ≤ σ) (hS : 0 ≤ S)
    (hsr : 0 < σr) :
    Real.rpow (σ / (σr * Real.sqrt S)) g =
      Real.rpow σ g / (Real.rpow σr g * Real.rpow S (g / 2)) := by
  calc
    Real.rpow (σ / (σr * Real.sqrt S)) g =
        Real.rpow σ g / Real.rpow (σr * Real.sqrt S) g :=
      Real.div_rpow hσ (mul_nonneg hsr.le (Real.sqrt_nonneg S)) g
    _ = _ := by rw [product_scale_rpow hS hsr.le]

theorem quotient_power {D S g : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) :
    Real.rpow (D / S) (g / 2) =
      Real.rpow D (g / 2) / Real.rpow S (g / 2) :=
  Real.div_rpow hD hS (g / 2)

theorem combined_scalar_identity {σ σr S D g η mrg : ℝ}
    (hσ : 0 ≤ σ) (hsr : 0 < σr) (hS : 0 < S) (hD : 0 ≤ D) :
    η * Real.rpow (σ / (σr * Real.sqrt S)) g *
        (mrg * Real.rpow D (g / 2)) =
      η * (mrg / Real.rpow σr g) * Real.rpow σ g *
        Real.rpow (D / S) (g / 2) := by
  rw [quotient_scale_rpow hσ hS.le hsr, quotient_power hD hS.le]
  have hσrpow : Real.rpow σr g ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hsr g)
  have hSpow : Real.rpow S (g / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hS (g / 2))
  field_simp [hσrpow, hSpow]

theorem powerFixedRiskCost_eq_integral [IsProbabilityMeasure μ]
    (h : PowerProjectionIsotropic r μ σr mrg g) (σ η : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    (∫ ω, η * Real.rpow
      |projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω| g ∂μ) =
      powerFixedRiskCost η mrg σr σ g (finiteRayleighQuotient N w) := by
  have hfac := h.projection_abs_gMoment (N + 1) (Discrete.difference w) t
  have hS0 : 0 ≤ finiteSquareEnergy N w := hS.le
  have hD : 0 ≤ finiteDifferenceEnergy N w :=
    Finset.sum_nonneg (fun j hj => sq_nonneg (Discrete.difference w j))
  rw [show (fun ω => η * Real.rpow
      |projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω| g) =
      (fun ω => η * Real.rpow
        |projectionFixedRiskScale σ σr N w| g *
          Real.rpow |finiteSignal (N + 1) (Discrete.difference w) r t ω| g) by
        funext ω
        simp only [projectionFixedRiskPosition]
        rw [← mul_sub, congrFun (finiteSignal_sub_previous N w r t hwN) ω]
        rw [abs_mul]
        change η * ((|projectionFixedRiskScale σ σr N w| *
          |finiteSignal (N + 1) (Discrete.difference w) r t ω|) ^ g) =
          η * |projectionFixedRiskScale σ σr N w| ^ g *
            |finiteSignal (N + 1) (Discrete.difference w) r t ω| ^ g
        have hp := Real.mul_rpow
          (abs_nonneg (projectionFixedRiskScale σ σr N w))
          (abs_nonneg (finiteSignal (N + 1) (Discrete.difference w) r t ω))
          (z := g)
        simpa [mul_assoc] using congrArg (fun x => η * x) hp]
  rw [integral_const_mul]
  rw [show |projectionFixedRiskScale σ σr N w| =
      σ / (σr * Real.sqrt (finiteSquareEnergy N w)) by
        rw [projectionFixedRiskScale, abs_of_nonneg]
        exact div_nonneg hσ (mul_nonneg h.scale_pos.le (Real.sqrt_nonneg _))]
  change (∫ ω, Real.rpow
      |finiteSignal (N + 1) (Discrete.difference w) r t ω| g ∂μ) = _ at hfac
  rw [hfac]
  simpa [powerFixedRiskCost, finiteRayleighQuotient, finiteDifferenceEnergy,
    finiteSquareEnergy] using
    combined_scalar_identity hσ h.scale_pos hS hD

theorem powerFixedRiskPosition_variance [IsProbabilityMeasure μ]
    (h : PowerProjectionIsotropic r μ σr mrg g) (σ : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hS : 0 < finiteSquareEnergy N w) :
    Var[projectionFixedRiskPosition σ σr N w r t; μ] = σ^2 := by
  rw [show projectionFixedRiskPosition σ σr N w r t =
      (fun ω => projectionFixedRiskScale σ σr N w * finiteSignal N w r t ω) by rfl]
  rw [variance_const_mul, h.projection_variance N w t]
  dsimp [projectionFixedRiskScale]
  rw [div_pow]
  field_simp [ne_of_gt h.scale_pos, ne_of_gt hS]
  rw [Real.sq_sqrt hS.le]

theorem powerFixedRiskPosition_integral_rpow_of_cutoff [IsProbabilityMeasure μ]
    (h : PowerProjectionIsotropic r μ σr mrg g) (σ η : ℝ) (N : ℕ)
    (w : Discrete.Kernel) (t : ℤ) (hσ : 0 ≤ σ)
    (hS : 0 < Discrete.squareEnergy w)
    (htail : ∀ j, N ≤ j → w j = 0) :
    (∫ ω, η * Real.rpow
      |projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω| g ∂μ) =
      powerFixedRiskCost η mrg σr σ g (Discrete.rayleighQuotient w) := by
  have hSf : 0 < finiteSquareEnergy N w := by
    rw [← squareEnergy_eq_finiteSquareEnergy N w htail]
    exact hS
  rw [powerFixedRiskCost_eq_integral h σ η N w t hσ hSf (htail N le_rfl)]
  rw [rayleighQuotient_eq_finiteRayleighQuotient N w htail]

theorem powerFixedRiskCost_le_iff {η mrg σr σ g q v : ℝ}
    (hη : 0 < η) (hmrg : 0 < mrg) (hsr : 0 < σr) (hσ : 0 < σ)
    (hg : 0 < g) (hq : 0 ≤ q) (hv : 0 ≤ v) :
    powerFixedRiskCost η mrg σr σ g q ≤ powerFixedRiskCost η mrg σr σ g v ↔ q ≤ v := by
  unfold powerFixedRiskCost
  have hK : 0 < η * (mrg / Real.rpow σr g) * Real.rpow σ g :=
    mul_pos (mul_pos hη (div_pos hmrg (Real.rpow_pos_of_pos hsr g)))
      (Real.rpow_pos_of_pos hσ g)
  constructor
  · intro h
    apply (Real.rpow_le_rpow_iff hq hv (by linarith : 0 < g / 2)).mp
    exact le_of_mul_le_mul_left (by simpa using h) hK
  · intro h
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_iff hq hv (by linarith : 0 < g / 2)).mpr h) hK.le

theorem powerFixedRiskCost_isMinOn_iff
    {A : Set Discrete.Kernel} {w : Discrete.Kernel}
    (hwA : w ∈ A) (hA : ∀ v ∈ A, 0 < Discrete.squareEnergy v)
    (hη : 0 < η) (hmrg : 0 < mrg) (hsr : 0 < σr) (hσ : 0 < σ)
    (hg : 0 < g) :
    IsMinOn (fun v => powerFixedRiskCost η mrg σr σ g
      (Discrete.rayleighQuotient v)) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro h v hv
    have hwq : 0 ≤ Discrete.rayleighQuotient w :=
      div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j)))
        (hA w hwA).le
    have hvq : 0 ≤ Discrete.rayleighQuotient v :=
      div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j)))
        (hA v hv).le
    exact (powerFixedRiskCost_le_iff hη hmrg hsr hσ hg
      hwq hvq).mp (h hv)
  · intro h v hv
    have hwq : 0 ≤ Discrete.rayleighQuotient w :=
      div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j)))
        (hA w hwA).le
    have hvq : 0 ≤ Discrete.rayleighQuotient v :=
      div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j)))
        (hA v hv).le
    exact (powerFixedRiskCost_le_iff hη hmrg hsr hσ hg
      hwq hvq).mpr (h hv)

theorem powerFixedRiskCost_formula_objective_minimizer_iff
    {A : Set Discrete.Kernel} {w : Discrete.Kernel}
    (hwA : w ∈ A) (hA : ∀ v ∈ A, 0 < Discrete.squareEnergy v)
    {η₁ m₁ σr₁ σ₁ g₁ η₂ m₂ σr₂ σ₂ g₂ : ℝ}
    (h₁ : 0 < η₁ ∧ 0 < m₁ ∧ 0 < σr₁ ∧ 0 < σ₁ ∧ 0 < g₁)
    (h₂ : 0 < η₂ ∧ 0 < m₂ ∧ 0 < σr₂ ∧ 0 < σ₂ ∧ 0 < g₂) :
    IsMinOn (fun v => powerFixedRiskCost η₁ m₁ σr₁ σ₁ g₁
      (Discrete.rayleighQuotient v)) A w ↔
      IsMinOn (fun v => powerFixedRiskCost η₂ m₂ σr₂ σ₂ g₂
        (Discrete.rayleighQuotient v)) A w := by
  rw [powerFixedRiskCost_isMinOn_iff hwA hA h₁.1 h₁.2.1 h₁.2.2.1
      h₁.2.2.2.1 h₁.2.2.2.2,
    powerFixedRiskCost_isMinOn_iff hwA hA h₂.1 h₂.2.1 h₂.2.2.1
      h₂.2.2.2.1 h₂.2.2.2.2]

theorem powerFixedRiskPosition_integral_rpow_isMinOn_iff
    [IsProbabilityMeasure μ] (h : PowerProjectionIsotropic r μ σr mrg g)
    {A : Set Discrete.Kernel} {w : Discrete.Kernel} (hwA : w ∈ A)
    (hA : ∀ v ∈ A, 0 < Discrete.squareEnergy v)
    {N : ℕ} {t : ℤ}
    (htail : ∀ v ∈ A, ∀ j, N ≤ j → v j = 0) (hη : 0 < η) (hσ : 0 < σ)
    (hg : 0 < g) :
    IsMinOn (fun v => ∫ ω, η * Real.rpow
      |projectionFixedRiskPosition σ σr N v r t ω -
        projectionFixedRiskPosition σ σr N v r (t - 1) ω| g ∂μ) A w ↔
      IsMinOn Discrete.rayleighQuotient A w := by
  constructor
  · intro hmin v hv
    have hq : Discrete.rayleighQuotient w ≤ Discrete.rayleighQuotient v := by
      apply (powerFixedRiskCost_le_iff hη h.momentScale_pos h.scale_pos hσ hg)
        (div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j)))
          (hA w hwA).le)
        (div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j)))
          (hA v hv).le) |>.mp
      have hc : (∫ ω, η * Real.rpow
          |projectionFixedRiskPosition σ σr N w r t ω -
            projectionFixedRiskPosition σ σr N w r (t - 1) ω| g ∂μ) ≤
          ∫ ω, η * Real.rpow
            |projectionFixedRiskPosition σ σr N v r t ω -
              projectionFixedRiskPosition σ σr N v r (t - 1) ω| g ∂μ := hmin hv
      rw [powerFixedRiskPosition_integral_rpow_of_cutoff h σ η N v t hσ.le
        (hA v hv) (htail v hv),
        powerFixedRiskPosition_integral_rpow_of_cutoff h σ η N w t hσ.le
          (hA w hwA) (htail w hwA)] at hc
      exact hc
    exact hq
  · intro hmin v hv
    change (∫ ω, η * Real.rpow
      |projectionFixedRiskPosition σ σr N w r t ω -
        projectionFixedRiskPosition σ σr N w r (t - 1) ω| g ∂μ) ≤
      ∫ ω, η * Real.rpow
        |projectionFixedRiskPosition σ σr N v r t ω -
          projectionFixedRiskPosition σ σr N v r (t - 1) ω| g ∂μ
    rw [powerFixedRiskPosition_integral_rpow_of_cutoff h σ η N v t hσ.le
      (hA v hv) (htail v hv),
      powerFixedRiskPosition_integral_rpow_of_cutoff h σ η N w t hσ.le
        (hA w hwA) (htail w hwA)]
    apply (powerFixedRiskCost_le_iff hη h.momentScale_pos h.scale_pos hσ hg)
      (div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference w j)))
        (hA w hwA).le)
      (div_nonneg (tsum_nonneg (fun j => sq_nonneg (Discrete.difference v j)))
        (hA v hv).le) |>.mpr
    exact hmin hv

end RayleighKernel.Probability
