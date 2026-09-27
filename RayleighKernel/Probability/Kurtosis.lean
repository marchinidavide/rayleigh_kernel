import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import RayleighKernel.Probability.AggregateCost

noncomputable section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace RayleighKernel.Probability

structure IsKurtosisWhiteInput {Ω : Type*} [MeasurableSpace Ω]
    (r : ℤ → Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop
    extends IsWhiteInput r μ where
  projection_memLp_four : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    MemLp (finiteSignal N w r t) 4 μ
  projection_fourth_le : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    (∫ ω, (finiteSignal N w r t ω) ^ 4 ∂μ) ≤
      K * (finiteSquareEnergy N w) ^ 2
  kurtosis_one_le : 1 ≤ K

private lemma pointwise_young (x t : ℝ) (ht : 0 ≤ t) :
    3 * t ^ 2 * x ^ 2 ≤ x ^ 4 + 2 * t ^ 3 * |x| := by
  have h : 0 ≤ |x| * (|x| - t) ^ 2 * (|x| + 2 * t) := by positivity
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [h, hx, abs_nonneg x]

private lemma integrable_sq_of_integrable_abs_fourth {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h1 : Integrable (fun ω => |X ω|) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ) :
    Integrable (fun ω => X ω ^ 2) μ := by
  have hsum : Integrable (fun ω => |X ω| + X ω ^ 4) μ := h1.add h4
  have hsabs : Integrable (fun ω => |X ω| ^ 2) μ := by
    have hbound : ∀ᵐ ω ∂μ, ‖X ω ^ (2 : ℕ)‖ ≤ |X ω| + X ω ^ 4 := by
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hx2 : X ω ^ 2 = |X ω| ^ 2 := (sq_abs (X ω)).symm
      have hx4 : X ω ^ 4 = |X ω| ^ 4 := by
        rw [show X ω ^ 4 = (X ω ^ 2) ^ 2 by ring, hx2]
        ring
      have hsmall : |X ω| ≤ 1 ∨ 1 ≤ |X ω| := le_total _ _
      rcases hsmall with hsmall | hlarge
      · rw [hx2, hx4]
        have hy := mul_nonneg (abs_nonneg (X ω)) (sub_nonneg.mpr hsmall)
        nlinarith
      · rw [hx2, hx4]
        have hy : 0 ≤ |X ω| ^ 2 * (|X ω| ^ 2 - 1) := by
          apply mul_nonneg (sq_nonneg _)
          nlinarith [sq_nonneg (|X ω| - 1)]
        nlinarith
    have hbound' : ∀ᵐ ω ∂μ, ‖|X ω| ^ (2 : ℕ)‖ ≤ |X ω| + X ω ^ 4 := by
      filter_upwards [hbound] with ω hω
      simpa [Real.norm_eq_abs, sq_abs] using hω
    exact hsum.mono' (h1.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable hbound'
  apply hsabs.congr
  filter_upwards [] with ω
  exact sq_abs (X ω)

theorem integral_sq_cube_le_integral_abs_sq_mul_integral_fourth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h1 : Integrable (fun ω => |X ω|) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, X ω ^ 2 ∂μ) ^ 3 ≤
      (∫ ω, |X ω| ∂μ) ^ 2 * (∫ ω, X ω ^ 4 ∂μ) := by
  have h2 := integrable_sq_of_integrable_abs_fourth h1 h4
  let A : ℝ := ∫ ω, |X ω| ∂μ
  let B : ℝ := ∫ ω, X ω ^ 2 ∂μ
  let C : ℝ := ∫ ω, X ω ^ 4 ∂μ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg (fun ω => by positivity)
  by_cases hAz : A = 0
  · have hBz : B = 0 := by
      dsimp [A] at hAz
      have hzero : (fun ω => |X ω|) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall
          (fun ω => abs_nonneg (X ω))) h1).mp hAz
      dsimp [B]
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with ω hω
      rw [← sq_abs]
      simp [hω]
    change B ^ 3 ≤ A ^ 2 * C
    rw [hBz, hAz]
    norm_num
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    let t : ℝ := B / A
    have ht : 0 ≤ t := div_nonneg hB hAp.le
    have hpoint : ∀ᵐ ω ∂μ, 3 * t ^ 2 * X ω ^ 2 ≤
        X ω ^ 4 + 2 * t ^ 3 * |X ω| := Filter.Eventually.of_forall
      (fun ω => pointwise_young (X ω) t ht)
    have hiL : Integrable (fun ω => 3 * t ^ 2 * X ω ^ 2) μ :=
      h2.const_mul (3 * t ^ 2)
    have hiR : Integrable (fun ω => X ω ^ 4 + 2 * t ^ 3 * |X ω|) μ :=
      h4.add (h1.const_mul (2 * t ^ 3))
    have hint := integral_mono_ae hiL hiR hpoint
    have hcalc : 3 * t ^ 2 * B ≤ C + 2 * t ^ 3 * A := by
      calc
        3 * t ^ 2 * B = ∫ ω, 3 * t ^ 2 * X ω ^ 2 ∂μ := by
          rw [← integral_const_mul]
        _ ≤ ∫ ω, X ω ^ 4 + 2 * t ^ 3 * |X ω| ∂μ := hint
        _ = C + 2 * t ^ 3 * A := by
          rw [integral_add h4 (h1.const_mul (2 * t ^ 3))]
          rw [← integral_const_mul]
    dsimp [t] at hcalc
    field_simp [ne_of_gt hAp] at hcalc
    nlinarith

theorem integral_sq_mul_sqrt_sq_div_sqrt_fourth_le_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h1 : Integrable (fun ω => |X ω|) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ)
    (hCpos : 0 < ∫ ω, X ω ^ 4 ∂μ) :
    (∫ ω, X ω ^ 2 ∂μ) * Real.sqrt (∫ ω, X ω ^ 2 ∂μ) /
        Real.sqrt (∫ ω, X ω ^ 4 ∂μ) ≤ ∫ ω, |X ω| ∂μ := by
  have hcube := integral_sq_cube_le_integral_abs_sq_mul_integral_fourth h1 h4
  let A : ℝ := ∫ ω, |X ω| ∂μ
  let B : ℝ := ∫ ω, X ω ^ 2 ∂μ
  let C : ℝ := ∫ ω, X ω ^ 4 ∂μ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hC : 0 ≤ C := le_of_lt hCpos
  have hsqrtC : 0 < Real.sqrt C := Real.sqrt_pos.2 hCpos
  have hsqrtB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hsquares : (B * Real.sqrt B) ^ 2 ≤ (A * Real.sqrt C) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hC]
    nlinarith [hcube]
  have hroot : B * Real.sqrt B ≤ A * Real.sqrt C :=
    (sq_le_sq₀ (mul_nonneg hB hsqrtB) (mul_nonneg hA hsqrtC.le)).mp hsquares
  apply (div_le_iff₀ hsqrtC).2
  simpa [A, B, C, mul_comm] using hroot

private theorem integral_abs_le_sqrt_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) : ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (show MemLp |f| (ENNReal.ofReal (2 : ℝ)) μ by simpa using hf.abs)
    (show MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ by
      simpa using (memLp_const (μ := μ) (p := (2 : ENNReal)) (1 : ℝ)))
  rw [Real.sqrt_eq_rpow]
  convert h using 1 <;> simp [sq]

theorem IsKurtosisWhiteInput.projection_integral_abs_bounds
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℝ}
    (h : IsKurtosisWhiteInput r μ K) (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    Real.sqrt (finiteSquareEnergy N w) / Real.sqrt K ≤
        ∫ ω, |finiteSignal N w r t ω| ∂μ ∧
      (∫ ω, |finiteSignal N w r t ω| ∂μ) ≤
        Real.sqrt (finiteSquareEnergy N w) := by
  let X : Ω → ℝ := finiteSignal N w r t
  let B : ℝ := finiteSquareEnergy N w
  have hmem4 : MemLp X 4 μ := h.projection_memLp_four N w t
  have hmem2 : MemLp X 2 μ := hmem4.mono_exponent (by norm_num)
  have h1 : Integrable (fun ω => |X ω|) μ :=
    (hmem2.integrable one_le_two).norm
  have h4 : Integrable (fun ω => X ω ^ 4) μ := by
    have hi := hmem4.integrable_norm_pow (p := 4) (by norm_num)
    apply hi.congr
    filter_upwards [] with ω
    change |X ω| ^ 4 = X ω ^ 4
    rw [show |X ω| ^ 4 = (|X ω| ^ 2) ^ 2 by ring, sq_abs]
    ring
  have hvar := finiteSignal_variance h.toIsWhiteInput t (N := N) (w := w)
  rw [ProbabilityTheory.variance_of_integral_eq_zero hmem2.aemeasurable
    (finiteSignal_expectation_zero h.toIsWhiteInput t)] at hvar
  have hB0 : 0 ≤ B := by dsimp [B]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB_eq : (∫ ω, X ω ^ 2 ∂μ) = B := by simpa [X, B, finiteSquareEnergy] using hvar
  have hupper : ∫ ω, |X ω| ∂μ ≤ Real.sqrt B := by
    rw [← hB_eq]
    exact integral_abs_le_sqrt_sq hmem2
  have hcube := integral_sq_cube_le_integral_abs_sq_mul_integral_fourth h1 h4
  rw [hB_eq] at hcube
  have hfourth : (∫ ω, X ω ^ 4 ∂μ) ≤ K * B ^ 2 := by
    simpa [X, B] using h.projection_fourth_le N w t
  have hA : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have hC : 0 ≤ ∫ ω, X ω ^ 4 ∂μ := integral_nonneg (fun _ => by positivity)
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) h.kurtosis_one_le
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hlower : Real.sqrt B / Real.sqrt K ≤ ∫ ω, |X ω| ∂μ := by
    by_cases hBz : B = 0
    · simp [hBz, hA]
    · have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
      have hpoly : B ^ 3 ≤ (∫ ω, |X ω| ∂μ) ^ 2 * (K * B ^ 2) :=
        le_trans hcube (mul_le_mul_of_nonneg_left hfourth (sq_nonneg _))
      have hB2 : 0 < B ^ 2 := sq_pos_of_pos hBp
      have hBA : B ≤ K * (∫ ω, |X ω| ∂μ) ^ 2 := by
        calc
          B = B ^ 3 / B ^ 2 := by field_simp
          _ ≤ ((∫ ω, |X ω| ∂μ) ^ 2 * (K * B ^ 2)) / B ^ 2 :=
            div_le_div_of_nonneg_right hpoly (le_of_lt hB2)
          _ = K * (∫ ω, |X ω| ∂μ) ^ 2 := by
            field_simp
      apply (div_le_iff₀ hsK).2
      have hsquare : Real.sqrt B ≤ (∫ ω, |X ω| ∂μ) * Real.sqrt K := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [hBA, Real.sq_sqrt (le_of_lt hK)]
      nlinarith
  exact ⟨hlower, hupper⟩

theorem IsKurtosisWhiteInput.fixedRisk_turnover_energy_bounds
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℝ}
    (h : IsKurtosisWhiteInput r μ K) (σ : ℝ) (N : ℕ) (w : Discrete.Kernel)
    (t : ℤ) (hσ : 0 ≤ σ) (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    σ / Real.sqrt (finiteSquareEnergy N w) *
        (Real.sqrt (finiteDifferenceEnergy N w) / Real.sqrt K) ≤
      ∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
        projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ ∧
      (∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
        projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ) ≤
        σ / Real.sqrt (finiteSquareEnergy N w) *
          Real.sqrt (finiteDifferenceEnergy N w) := by
  have hp := h.projection_integral_abs_bounds (N + 1) (Discrete.difference w) t
  have hs : 0 < Real.sqrt (finiteSquareEnergy N w) := Real.sqrt_pos.2 hS
  have hc : 0 ≤ σ / Real.sqrt (finiteSquareEnergy N w) := div_nonneg hσ hs.le
  have hI : (∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
      projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ) =
      (σ / Real.sqrt (finiteSquareEnergy N w)) *
        (∫ ω, |finiteSignal (N + 1) (Discrete.difference w) r t ω| ∂μ) := by
    simp only [projectionFixedRiskPosition]
    rw [show (fun ω => |projectionFixedRiskScale σ 1 N w * finiteSignal N w r t ω -
        projectionFixedRiskScale σ 1 N w * finiteSignal N w r (t - 1) ω|) =
        (fun ω => |projectionFixedRiskScale σ 1 N w *
          finiteSignal (N + 1) (Discrete.difference w) r t ω|) by
      funext ω
      rw [← mul_sub]
      congr 1
      exact congrArg (fun z => projectionFixedRiskScale σ 1 N w * z)
        (congrFun (finiteSignal_sub_previous N w r t hwN) ω)]
    rw [show (fun ω => |projectionFixedRiskScale σ 1 N w *
        finiteSignal (N + 1) (Discrete.difference w) r t ω|) =
        (fun ω => |projectionFixedRiskScale σ 1 N w| *
          |finiteSignal (N + 1) (Discrete.difference w) r t ω|) by
      funext ω; rw [abs_mul]]
    rw [show |projectionFixedRiskScale σ 1 N w| =
        σ / Real.sqrt (finiteSquareEnergy N w) by
      dsimp [projectionFixedRiskScale]
      simp only [one_mul]
      rw [abs_of_nonneg hc]]
    rw [← integral_const_mul]
  constructor
  · rw [hI]
    simpa only [finiteSquareEnergy, finiteDifferenceEnergy] using
      (mul_le_mul_of_nonneg_left hp.1 hc)
  · rw [hI]
    simpa only [finiteSquareEnergy, finiteDifferenceEnergy] using
      (mul_le_mul_of_nonneg_left hp.2 hc)

theorem IsKurtosisWhiteInput.fixedRisk_turnover_quotient_bounds
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℝ}
    (h : IsKurtosisWhiteInput r μ K) (σ : ℝ) (N : ℕ) (w : Discrete.Kernel)
    (t : ℤ) (hσ : 0 ≤ σ) (hS : 0 < finiteSquareEnergy N w) (hwN : w N = 0) :
    σ / Real.sqrt K * Real.sqrt (finiteRayleighQuotient N w) ≤
      ∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
        projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ ∧
      (∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
        projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ) ≤
        σ * Real.sqrt (finiteRayleighQuotient N w) := by
  have he := h.fixedRisk_turnover_energy_bounds σ N w t hσ hS hwN
  have hD : 0 ≤ finiteDifferenceEnergy N w :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : 0 < Real.sqrt (finiteSquareEnergy N w) := Real.sqrt_pos.2 hS
  have hroot : Real.sqrt (finiteRayleighQuotient N w) =
      Real.sqrt (finiteDifferenceEnergy N w) /
        Real.sqrt (finiteSquareEnergy N w) := by
    simpa [finiteRayleighQuotient] using (Real.sqrt_div hD (finiteSquareEnergy N w))
  rw [hroot]
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he.1
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he.2

theorem IsKurtosisWhiteInput.fixedRisk_turnover_sqrtK_approx
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℝ} (h : IsKurtosisWhiteInput r μ K)
    {σ : ℝ} {N : ℕ} {t : ℤ} {A : Set Discrete.Kernel}
    {wR wT : Discrete.Kernel}
    (hA : ∀ w ∈ A, 0 < finiteSquareEnergy N w)
    (hcut : ∀ w ∈ A, w N = 0) (hwR : wR ∈ A) (hwT : wT ∈ A)
    (hσ : 0 ≤ σ)
    (hR : IsMinOn (finiteRayleighQuotient N) A wR)
    (hT : IsMinOn (fun w => ∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
      projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ) A wT) :
    (∫ ω, |projectionFixedRiskPosition σ 1 N wT r t ω -
      projectionFixedRiskPosition σ 1 N wT r (t - 1) ω| ∂μ) ≤
        (∫ ω, |projectionFixedRiskPosition σ 1 N wR r t ω -
          projectionFixedRiskPosition σ 1 N wR r (t - 1) ω| ∂μ) ∧
      (∫ ω, |projectionFixedRiskPosition σ 1 N wR r t ω -
          projectionFixedRiskPosition σ 1 N wR r (t - 1) ω| ∂μ) ≤
        Real.sqrt K *
          (∫ ω, |projectionFixedRiskPosition σ 1 N wT r t ω -
            projectionFixedRiskPosition σ 1 N wT r (t - 1) ω| ∂μ) := by
  let T : Discrete.Kernel → ℝ := fun w =>
    ∫ ω, |projectionFixedRiskPosition σ 1 N w r t ω -
      projectionFixedRiskPosition σ 1 N w r (t - 1) ω| ∂μ
  have hq : finiteRayleighQuotient N wR ≤ finiteRayleighQuotient N wT := hR hwT
  have hsqrt : Real.sqrt (finiteRayleighQuotient N wR) ≤
      Real.sqrt (finiteRayleighQuotient N wT) := by
    exact Real.sqrt_le_sqrt hq
  have bR := h.fixedRisk_turnover_quotient_bounds σ N wR t hσ (hA wR hwR) (hcut wR hwR)
  have bT := h.fixedRisk_turnover_quotient_bounds σ N wT t hσ (hA wT hwT) (hcut wT hwT)
  constructor
  · exact hT hwR
  · have hscale : 0 ≤ σ * Real.sqrt (finiteRayleighQuotient N wR) := by positivity
    have hu : T wR ≤ σ * Real.sqrt (finiteRayleighQuotient N wR) := bR.2
    have hl : σ / Real.sqrt K * Real.sqrt (finiteRayleighQuotient N wT) ≤ T wT := bT.1
    dsimp [T] at hu hl ⊢
    have hK : 0 < Real.sqrt K := Real.sqrt_pos.2
      (lt_of_lt_of_le (by norm_num) h.kurtosis_one_le)
    calc
      T wR ≤ σ * Real.sqrt (finiteRayleighQuotient N wR) := hu
      _ ≤ σ * Real.sqrt (finiteRayleighQuotient N wT) :=
        mul_le_mul_of_nonneg_left hsqrt hσ
      _ ≤ Real.sqrt K * T wT := by
        have hmul := mul_le_mul_of_nonneg_left hl hK.le
        calc
          σ * Real.sqrt (finiteRayleighQuotient N wT) =
              Real.sqrt K * (σ / Real.sqrt K *
                Real.sqrt (finiteRayleighQuotient N wT)) := by
            field_simp
          _ ≤ Real.sqrt K * T wT := hmul

end RayleighKernel.Probability
