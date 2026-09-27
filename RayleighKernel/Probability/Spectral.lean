import RayleighKernel.Probability.CovarianceForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RayleighKernel.Probability

/-- The finite Fourier polynomial, using the positive-exponent convention `exp(iω)^j`. -/
def finiteTransfer (N : ℕ) (w : Discrete.Kernel) (ω : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, (w j : ℂ) * (Complex.exp (Complex.I * (ω : ℂ))) ^ j

/-- The normalized finite spectral energy; the normalization is `1/(2π)`. -/
def finiteSpectralEnergy (s : ℝ → ℝ) (N : ℕ) (w : Discrete.Kernel) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ ω in Set.Icc (-Real.pi) Real.pi,
    ‖finiteTransfer N w ω‖ ^ 2 * s ω

structure FiniteSpectralRepresentation (Γ : ℕ → ℕ → ℝ) (s : ℝ → ℝ) : Prop where
  covarianceForm_eq : ∀ N (w : Discrete.Kernel),
    finiteCovarianceForm Γ N w = finiteSpectralEnergy s N w

private theorem finite_difference_sum (N : ℕ) (w : Discrete.Kernel) (z : ℂ) :
    (∑ j ∈ Finset.range (N + 1), (Discrete.difference w j : ℂ) * z ^ j) =
      (1 - z) * (∑ j ∈ Finset.range N, (w j : ℂ) * z ^ j) +
        (w N : ℂ) * z ^ N := by
  induction N with
  | zero => simp [Discrete.difference]
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [Discrete.difference_succ]
      rw [← Finset.sum_range_succ, ih]
      rw [pow_succ]
      push_cast
      ring

theorem finiteTransfer_difference (N : ℕ) (w : Discrete.Kernel) (ω : ℝ)
    (hwN : w N = 0) :
    finiteTransfer (N + 1) (Discrete.difference w) ω =
      (1 - Complex.exp (Complex.I * (ω : ℂ))) * finiteTransfer N w ω := by
  unfold finiteTransfer
  rw [finite_difference_sum]
  simp [hwN]

theorem complex_normSq_one_sub_exp_pos_I (ω : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * (ω : ℂ))‖ ^ 2 =
      4 * Real.sin (ω / 2) ^ 2 := by
  have h := congrArg (fun x : ℝ => x ^ 2)
    (Complex.norm_exp_I_mul_ofReal_sub_one ω)
  rw [show (1 : ℂ) - Complex.exp (Complex.I * (ω : ℂ)) =
      -(Complex.exp (Complex.I * (ω : ℂ)) - 1) by ring]
  rw [norm_neg]
  rw [h]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  simp only [mul_pow, Real.norm_eq_abs]
  rw [sq_abs]
  ring

theorem finiteCovarianceForm_spectral
    {Γ : ℕ → ℕ → ℝ} {s : ℝ → ℝ}
    (hs : FiniteSpectralRepresentation Γ s) (N : ℕ) (w : Discrete.Kernel) :
    finiteCovarianceForm Γ N w = finiteSpectralEnergy s N w :=
  hs.covarianceForm_eq N w

theorem finiteCovarianceForm_difference_spectral
    {Γ : ℕ → ℕ → ℝ} {s : ℝ → ℝ}
    (hs : FiniteSpectralRepresentation Γ s) (N : ℕ) (w : Discrete.Kernel)
    (hwN : w N = 0) :
    finiteCovarianceForm Γ (N + 1) (Discrete.difference w) =
      (1 / (2 * Real.pi)) * ∫ ω in Set.Icc (-Real.pi) Real.pi,
        (4 * Real.sin (ω / 2) ^ 2) * ‖finiteTransfer N w ω‖ ^ 2 * s ω := by
  rw [hs.covarianceForm_eq]
  unfold finiteSpectralEnergy
  congr 1
  congr 1
  funext ω
  rw [finiteTransfer_difference N w ω hwN, norm_mul,
    mul_pow, complex_normSq_one_sub_exp_pos_I]

theorem finiteGeneralizedRayleighQuotient_spectral
    {Γ : ℕ → ℕ → ℝ} {s : ℝ → ℝ}
    (hs : FiniteSpectralRepresentation Γ s) (N : ℕ) (w : Discrete.Kernel)
    (hwN : w N = 0) (hQ : 0 < finiteCovarianceForm Γ N w) :
    finiteGeneralizedRayleighQuotient Γ N w =
      (∫ ω in Set.Icc (-Real.pi) Real.pi,
        (4 * Real.sin (ω / 2) ^ 2) * ‖finiteTransfer N w ω‖ ^ 2 * s ω) /
      (∫ ω in Set.Icc (-Real.pi) Real.pi,
        ‖finiteTransfer N w ω‖ ^ 2 * s ω) := by
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hden : 0 < ∫ ω in Set.Icc (-Real.pi) Real.pi,
      ‖finiteTransfer N w ω‖ ^ 2 * s ω := by
    have hQ' : 0 < finiteSpectralEnergy s N w := by
      rw [← finiteCovarianceForm_spectral hs N w]
      exact hQ
    unfold finiteSpectralEnergy at hQ'
    rw [mul_comm] at hQ'
    exact pos_of_mul_pos_left hQ' (by positivity)
  unfold finiteGeneralizedRayleighQuotient
  rw [finiteCovarianceForm_difference_spectral hs N w hwN,
    finiteCovarianceForm_spectral hs N w]
  unfold finiteSpectralEnergy
  field_simp [ne_of_gt hQ, ne_of_gt hden, ne_of_gt hpi]

end RayleighKernel.Probability
