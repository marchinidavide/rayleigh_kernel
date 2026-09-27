import RayleighKernel.Profile.Moments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rayleigh self-consistency for the explicit profile

This file formalizes the integration-by-parts identity that converts the Rayleigh energy gap into
a relation between the zeroth and first moments of the dimensionless profile.
-/

noncomputable section

namespace RayleighKernel.Profile

open MeasureTheory

/-- Difference between the two sides of the dimensionless Rayleigh eigenvalue identity. -/
def energyGap (t : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..1, slope t y ^ 2) - t ^ 2 * ∫ y in (0 : ℝ)..1, value t y ^ 2

theorem continuous_value (t : ℝ) : Continuous (value t) := by
  unfold value
  fun_prop

theorem continuous_slope (t : ℝ) : Continuous (slope t) := by
  unfold slope
  fun_prop

theorem continuous_curvature (t : ℝ) : Continuous (curvature t) := by
  unfold curvature
  fun_prop

theorem integral_slope_sq_eq_neg_integral_value_mul_curvature {t : ℝ}
    (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    (∫ y in (0 : ℝ)..1, slope t y ^ 2) =
      -(∫ y in (0 : ℝ)..1, value t y * curvature t y) := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := value t) (v := slope t) (u' := slope t) (v' := curvature t)
    (fun y _ ↦ value_hasDerivAt t y) (fun y _ ↦ slope_hasDerivAt t y)
    ((continuous_slope t).intervalIntegrable 0 1)
    ((continuous_curvature t).intervalIntegrable 0 1)
  rw [value_one ht hcos, slope_one ht hcos, value_zero] at hparts
  simp only [zero_mul, sub_zero] at hparts
  have hsquare : (∫ y in (0 : ℝ)..1, slope t y ^ 2) =
      ∫ y in (0 : ℝ)..1, slope t y * slope t y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact pow_two (slope t y)
  rw [hsquare]
  linarith

theorem energyGap_eq_moments {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    energyGap t = t ^ 2 * (coefficientC t * momentZero t - momentOne t) := by
  rw [energyGap, integral_slope_sq_eq_neg_integral_value_mul_curvature ht hcos]
  have hvalue_sq : IntervalIntegrable (fun y ↦ value t y ^ 2) volume 0 1 :=
    ((continuous_value t).pow 2).intervalIntegrable 0 1
  have hvalue_curvature : IntervalIntegrable (fun y ↦ value t y * curvature t y) volume 0 1 :=
    ((continuous_value t).mul (continuous_curvature t)).intervalIntegrable 0 1
  have hmomentZero : IntervalIntegrable (value t) volume 0 1 :=
    (continuous_value t).intervalIntegrable 0 1
  have hmomentOne : IntervalIntegrable (fun y ↦ y * value t y) volume 0 1 :=
    (continuous_id.mul (continuous_value t)).intervalIntegrable 0 1
  have hscaledValueSq : IntervalIntegrable (fun y ↦ t ^ 2 * value t y ^ 2) volume 0 1 :=
    hvalue_sq.const_mul (t ^ 2)
  calc
    -(∫ y in (0 : ℝ)..1, value t y * curvature t y) -
        t ^ 2 * ∫ y in (0 : ℝ)..1, value t y ^ 2 =
        (∫ y in (0 : ℝ)..1, -(value t y * curvature t y)) -
          ∫ y in (0 : ℝ)..1, t ^ 2 * value t y ^ 2 := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    _ =
        ∫ y in (0 : ℝ)..1,
          (-(value t y * curvature t y) - t ^ 2 * value t y ^ 2) := by
      symm
      exact intervalIntegral.integral_sub hvalue_curvature.neg hscaledValueSq
    _ = ∫ y in (0 : ℝ)..1, t ^ 2 * (coefficientC t * value t y - y * value t y) := by
      apply intervalIntegral.integral_congr
      intro y _
      have hode := ode_identity t y
      linear_combination -(value t y) * hode
    _ = t ^ 2 * (coefficientC t * momentZero t - momentOne t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (hmomentZero.const_mul (coefficientC t)) hmomentOne,
        intervalIntegral.integral_const_mul]
      rfl

theorem energyGap_eq_consistencyPolynomial {t : ℝ} (ht : t ≠ 0)
    (hcos : Real.cos t ≠ 1) :
    energyGap t = -consistencyPolynomial t / (12 * t ^ 2) := by
  rw [energyGap_eq_moments ht hcos, momentZero_eq_formula ht hcos,
    momentOne_eq_formula ht hcos, coefficientC, momentZeroFormula, momentOneFormula,
    consistencyPolynomial, ← slope_zero_eq_initialSlope ht (sin_half_ne_zero_of_cos_ne_one hcos)]
  simp only [slope, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero,
    coefficientA]
  field_simp
  ring_nf
  have htrig : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsin3 : Real.sin t ^ 3 = Real.sin t * Real.sin t ^ 2 := by ring
  have hsin4 : Real.sin t ^ 4 = (Real.sin t ^ 2) ^ 2 := by ring
  simp_rw [hsin3, hsin4, htrig]
  ring

theorem energyGap_eq_zero_iff {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    energyGap t = 0 ↔ consistencyPolynomial t = 0 := by
  rw [energyGap_eq_consistencyPolynomial ht hcos]
  simp [ht]

end RayleighKernel.Profile
