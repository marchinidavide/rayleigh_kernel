import RayleighKernel.Profile.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Free-boundary algebra for the explicit profile

The coefficients were obtained by imposing value matching and smooth fit at `y = 1`. This file
checks those identities directly and relates the auxiliary scalar `p(t)` to the initial slope.
-/

noncomputable section

namespace RayleighKernel.Profile

@[simp]
theorem value_zero (t : ℝ) : value t 0 = 0 := by
  simp [value]

theorem value_one {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) : value t 1 = 0 := by
  rw [value, coefficientA, coefficientC]
  field_simp
  ring_nf
  calc
    Real.sin t ^ 2 * t - t + t * Real.cos t ^ 2 =
        t * (Real.sin t ^ 2 + Real.cos t ^ 2 - 1) := by ring
    _ = 0 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem slope_one {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) : slope t 1 = 0 := by
  rw [slope, coefficientA, coefficientC]
  field_simp
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem slope_zero_eq_initialSlope {t : ℝ} (ht : t ≠ 0) (hsin : Real.sin (t / 2) ≠ 0) :
    slope t 0 = initialSlope t := by
  rw [slope, initialSlope, coefficientA, Real.cot_eq_cos_div_sin]
  simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
  have hsin_two : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    rw [← Real.sin_two_mul (t / 2)]
    congr 1
    ring
  have hcos_two : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub (t / 2)]
    congr 1
    ring
  rw [hsin_two, hcos_two]
  field_simp [ht, hsin]
  ring

theorem sin_half_ne_zero_of_cos_ne_one {t : ℝ} (hcos : Real.cos t ≠ 1) :
    Real.sin (t / 2) ≠ 0 := by
  intro hsin
  apply hcos
  have hcos_two : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub (t / 2)]
    congr 1
    ring
  rw [hcos_two, hsin]
  ring

end RayleighKernel.Profile
