import RayleighKernel.Profile.Derivatives
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments of the explicit profile

This file starts the exact self-consistency calculation by evaluating the two moments needed to
recover the mass normalization and support length.
-/

noncomputable section

namespace RayleighKernel.Profile

/-- Closed form for the zeroth moment from the manuscript. -/
def momentZeroFormula (t : ℝ) : ℝ :=
  (t ^ 2 * (1 + Real.cos t) - 4 * t * Real.sin t + 4 * (1 - Real.cos t)) /
    (2 * t ^ 2 * (1 - Real.cos t))

/-- Closed form for the first moment from the manuscript. -/
def momentOneFormula (t : ℝ) : ℝ :=
  (t * (Real.cos t + 2) - 3 * Real.sin t) / (6 * t * (1 - Real.cos t))

/-- An antiderivative of the explicit profile when `t ≠ 0`. -/
def momentZeroPrimitive (t y : ℝ) : ℝ :=
  -(coefficientA t / t) * Real.cos (t * y) +
    coefficientC t / t * Real.sin (t * y) - coefficientC t * y + y ^ 2 / 2

theorem momentZeroPrimitive_hasDerivAt {t : ℝ} (ht : t ≠ 0) (y : ℝ) :
    HasDerivAt (momentZeroPrimitive t) (value t y) y := by
  have harg : HasDerivAt (fun z : ℝ ↦ t * z) t y := hasDerivAt_const_mul t
  have hsin : HasDerivAt (fun z : ℝ ↦ Real.sin (t * z)) (Real.cos (t * y) * t) y :=
    (Real.hasDerivAt_sin (t * y)).comp y harg
  have hcos : HasDerivAt (fun z : ℝ ↦ Real.cos (t * z)) (-Real.sin (t * y) * t) y :=
    (Real.hasDerivAt_cos (t * y)).comp y harg
  unfold momentZeroPrimitive value
  have h := (((hcos.const_mul (-(coefficientA t / t))).add
    (hsin.const_mul (coefficientC t / t))).sub
      ((hasDerivAt_id y).const_mul (coefficientC t))).add
        (((hasDerivAt_id y).pow 2).div_const 2)
  convert h using 1
  · ext z
    simp only [Pi.add_apply, Pi.sub_apply, id_eq, Pi.pow_apply]
  · simp only [id_eq]
    field_simp
    ring

theorem momentZero_eq_primitive_sub {t : ℝ} (ht : t ≠ 0) :
    momentZero t = momentZeroPrimitive t 1 - momentZeroPrimitive t 0 := by
  rw [momentZero]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ ↦ momentZeroPrimitive_hasDerivAt ht y)
    (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)) |>.add
      (continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const)) |>.add
          continuous_id |>.intervalIntegrable 0 1)

theorem momentZero_eq_formula {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    momentZero t = momentZeroFormula t := by
  rw [momentZero_eq_primitive_sub ht]
  simp only [momentZeroPrimitive, momentZeroFormula, mul_one, Real.sin_zero, Real.cos_zero,
    mul_zero, sub_zero, one_pow]
  rw [coefficientA, coefficientC]
  field_simp
  ring_nf
  have htrig : (Real.cos t - 1) *
      (Real.sin t ^ 2 + Real.cos t ^ 2 - 1) = 0 := by
    rw [Real.sin_sq_add_cos_sq]
    ring
  ring_nf at htrig
  linarith

/-- An antiderivative of `y * Fₜ(y)` when `t ≠ 0`. -/
def momentOnePrimitive (t y : ℝ) : ℝ :=
  -(coefficientA t / t) * y * Real.cos (t * y) +
    coefficientA t / t ^ 2 * Real.sin (t * y) +
    coefficientC t / t * y * Real.sin (t * y) +
    coefficientC t / t ^ 2 * Real.cos (t * y) -
    coefficientC t * y ^ 2 / 2 + y ^ 3 / 3

theorem momentOnePrimitive_hasDerivAt {t : ℝ} (ht : t ≠ 0) (y : ℝ) :
    HasDerivAt (momentOnePrimitive t) (y * value t y) y := by
  have harg : HasDerivAt (fun z : ℝ ↦ t * z) t y := hasDerivAt_const_mul t
  have hsin : HasDerivAt (fun z : ℝ ↦ Real.sin (t * z)) (Real.cos (t * y) * t) y :=
    (Real.hasDerivAt_sin (t * y)).comp y harg
  have hcos : HasDerivAt (fun z : ℝ ↦ Real.cos (t * z)) (-Real.sin (t * y) * t) y :=
    (Real.hasDerivAt_cos (t * y)).comp y harg
  unfold momentOnePrimitive value
  have h := ((((((hasDerivAt_id y).mul hcos).const_mul (-(coefficientA t / t))).add
    (hsin.const_mul (coefficientA t / t ^ 2))).add
      (((hasDerivAt_id y).mul hsin).const_mul (coefficientC t / t))).add
        (hcos.const_mul (coefficientC t / t ^ 2))).sub
          (((hasDerivAt_id y).pow 2).const_mul (coefficientC t) |>.div_const 2) |>.add
            (((hasDerivAt_id y).pow 3).div_const 3)
  convert h using 1
  · ext z
    simp only [Pi.add_apply, Pi.sub_apply, id_eq, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [id_eq]
    field_simp
    ring

theorem momentOne_eq_primitive_sub {t : ℝ} (ht : t ≠ 0) :
    momentOne t = momentOnePrimitive t 1 - momentOnePrimitive t 0 := by
  rw [momentOne]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ ↦ momentOnePrimitive_hasDerivAt ht y)
    (continuous_id.mul
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)) |>.add
        (continuous_const.mul
          ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const)) |>.add
            continuous_id) |>.intervalIntegrable 0 1)

theorem momentOne_eq_formula {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    momentOne t = momentOneFormula t := by
  rw [momentOne_eq_primitive_sub ht]
  simp only [momentOnePrimitive, momentOneFormula, mul_one, Real.sin_zero, Real.cos_zero,
    mul_zero, one_pow]
  rw [coefficientA, coefficientC]
  field_simp
  ring_nf

theorem supportRatio_eq_formula {t : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    momentZero t / momentOne t = momentZeroFormula t / momentOneFormula t := by
  rw [momentZero_eq_formula ht hcos, momentOne_eq_formula ht hcos]

end RayleighKernel.Profile
