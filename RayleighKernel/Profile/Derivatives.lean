import RayleighKernel.Profile.Boundary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

/-!
# Differential identities for the explicit profile

The formulas in this file are ordinary real derivative statements. The final identity is the
inhomogeneous Euler--Lagrange equation on the positive phase.
-/

noncomputable section

namespace RayleighKernel.Profile

theorem value_hasDerivAt (t y : ℝ) : HasDerivAt (value t) (slope t y) y := by
  have harg : HasDerivAt (fun z : ℝ ↦ t * z) t y := hasDerivAt_const_mul t
  have hsin : HasDerivAt (fun z : ℝ ↦ Real.sin (t * z)) (Real.cos (t * y) * t) y :=
    (Real.hasDerivAt_sin (t * y)).comp y harg
  have hcos : HasDerivAt (fun z : ℝ ↦ Real.cos (t * z)) (-Real.sin (t * y) * t) y :=
    (Real.hasDerivAt_cos (t * y)).comp y harg
  unfold value slope
  have h := ((hsin.const_mul (coefficientA t)).add
    ((hcos.sub_const 1).const_mul (coefficientC t))).add (hasDerivAt_id y)
  convert h using 1
  · ext z
    simp only [Pi.add_apply, id_eq]
  · ring

theorem slope_hasDerivAt (t y : ℝ) : HasDerivAt (slope t) (curvature t y) y := by
  have harg : HasDerivAt (fun z : ℝ ↦ t * z) t y := hasDerivAt_const_mul t
  have hsin : HasDerivAt (fun z : ℝ ↦ Real.sin (t * z)) (Real.cos (t * y) * t) y :=
    (Real.hasDerivAt_sin (t * y)).comp y harg
  have hcos : HasDerivAt (fun z : ℝ ↦ Real.cos (t * z)) (-Real.sin (t * y) * t) y :=
    (Real.hasDerivAt_cos (t * y)).comp y harg
  unfold slope curvature
  convert (((hcos.const_mul (t * coefficientA t)).sub
    (hsin.const_mul (t * coefficientC t))).add_const 1) using 1
  · ring

theorem deriv_value (t y : ℝ) : deriv (value t) y = slope t y :=
  (value_hasDerivAt t y).deriv

theorem deriv_slope (t y : ℝ) : deriv (slope t) y = curvature t y :=
  (slope_hasDerivAt t y).deriv

theorem second_deriv_value (t y : ℝ) : deriv (deriv (value t)) y = curvature t y := by
  rw [show deriv (value t) = slope t from funext (deriv_value t), deriv_slope]

theorem ode_identity (t y : ℝ) :
    curvature t y + t ^ 2 * value t y = t ^ 2 * (y - coefficientC t) := by
  simp only [curvature, value]
  ring

theorem differential_equation (t y : ℝ) :
    deriv (deriv (value t)) y + t ^ 2 * value t y = t ^ 2 * (y - coefficientC t) := by
  rw [second_deriv_value, ode_identity]

end RayleighKernel.Profile
