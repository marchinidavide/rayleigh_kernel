import RayleighKernel.Variational
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Scaling identities

This file formalizes the change of variables in Section 3 of the manuscript. The normalization
`g(y) = L f(Ly)` preserves mass, sends first moment `L` to first moment one, and multiplies the
Rayleigh quotient by `L²`.
-/

noncomputable section

namespace RayleighKernel

open MeasureTheory Set

/-- Rescale a profile of lookback `L` to unit lookback. -/
def rescale (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun y ↦ L * f (L * y)

@[simp]
theorem rescale_apply (L : ℝ) (f : ℝ → ℝ) (y : ℝ) : rescale L f y = L * f (L * y) := rfl

@[simp]
theorem rescale_zero (L : ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) : rescale L f 0 = 0 := by
  simp [rescale, hf]

theorem rescale_nonnegative {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : ∀ x ∈ halfLine, 0 ≤ f x) {y : ℝ} (hy : y ∈ halfLine) : 0 ≤ rescale L f y := by
  exact mul_nonneg hL (hf (L * y) (mul_nonneg hL hy))

theorem deriv_rescale (L : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    deriv (rescale L f) y = L ^ 2 * deriv f (L * y) := by
  change deriv (fun x ↦ L * f (L * x)) y = L ^ 2 * deriv f (L * y)
  rw [deriv_const_mul_field, deriv_comp_mul_left]
  ring

theorem mass_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) : mass (rescale L f) = mass f := by
  rw [mass, mass, halfLine, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  change (∫ y in Ioi 0, L * f (L * y)) = ∫ x in Ioi 0, f x
  rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hL]
  simp [smul_eq_mul, hL.ne']

theorem firstMoment_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    firstMoment (rescale L f) = L⁻¹ * firstMoment f := by
  rw [firstMoment, firstMoment, halfLine, integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi]
  simpa only [rescale, mul_zero, smul_eq_mul, mul_assoc, mul_left_comm] using
    integral_comp_mul_left_Ioi (fun x ↦ x * f x) 0 hL

theorem squareEnergy_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    squareEnergy (rescale L f) = L * squareEnergy f := by
  rw [squareEnergy, squareEnergy, halfLine, integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi]
  have hchange := integral_comp_mul_left_Ioi (fun x ↦ f x ^ 2) 0 hL
  simp only [mul_zero, smul_eq_mul] at hchange
  calc
    (∫ y in Ioi 0, rescale L f y ^ 2) = L ^ 2 * ∫ y in Ioi 0, f (L * y) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      simp only [rescale]
      ring
    _ = L ^ 2 * (L⁻¹ * ∫ x in Ioi 0, f x ^ 2) := by rw [hchange]
    _ = L * ∫ x in Ioi 0, f x ^ 2 := by field_simp

theorem dirichletEnergy_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    dirichletEnergy (rescale L f) = L ^ 3 * dirichletEnergy f := by
  rw [dirichletEnergy, dirichletEnergy, halfLine, integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi]
  have hchange := integral_comp_mul_left_Ioi (fun x ↦ deriv f x ^ 2) 0 hL
  simp only [mul_zero, smul_eq_mul] at hchange
  calc
    (∫ y in Ioi 0, deriv (rescale L f) y ^ 2) =
        L ^ 4 * ∫ y in Ioi 0, deriv f (L * y) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [deriv_rescale]
      ring
    _ = L ^ 4 * (L⁻¹ * ∫ x in Ioi 0, deriv f x ^ 2) := by rw [hchange]
    _ = L ^ 3 * ∫ x in Ioi 0, deriv f x ^ 2 := by field_simp

theorem rayleighQuotient_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    rayleighQuotient (rescale L f) = L ^ 2 * rayleighQuotient f := by
  rw [rayleighQuotient, dirichletEnergy_rescale hL, squareEnergy_rescale hL,
    rayleighQuotient]
  field_simp

end RayleighKernel
