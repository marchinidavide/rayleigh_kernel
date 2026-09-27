import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Explicit profile definitions

This file defines the dimensionless linear-plus-trigonometric profile and the scalar quantities
from Sections 6--8 of the manuscript. Algebraic, differential, and integral identities are kept
in separate downstream modules.
-/

noncomputable section

namespace RayleighKernel.Profile

/-- Sine coefficient selected by the two free-boundary conditions. -/
def coefficientA (t : ℝ) : ℝ :=
  (t * Real.sin t + Real.cos t - 1) / (t * (Real.cos t - 1))

/-- Cosine coefficient selected by the two free-boundary conditions. -/
def coefficientC (t : ℝ) : ℝ :=
  (t * Real.cos t - Real.sin t) / (t * (Real.cos t - 1))

/-- Dimensionless linear-plus-trigonometric profile. -/
def value (t y : ℝ) : ℝ :=
  coefficientA t * Real.sin (t * y) + coefficientC t * (Real.cos (t * y) - 1) + y

/-- First derivative predicted by direct differentiation of `value`. -/
def slope (t y : ℝ) : ℝ :=
  t * coefficientA t * Real.cos (t * y) - t * coefficientC t * Real.sin (t * y) + 1

/-- Second derivative predicted by direct differentiation of `value`. -/
def curvature (t y : ℝ) : ℝ :=
  -(t ^ 2) * (coefficientA t * Real.sin (t * y) + coefficientC t * Real.cos (t * y))

/-- The auxiliary initial slope `p(t) = Fₜ'(0)`. -/
def initialSlope (t : ℝ) : ℝ := 2 - t * Real.cot (t / 2)

/-- Polynomial-trigonometric consistency function from the manuscript. -/
def consistencyPolynomial (t : ℝ) : ℝ :=
  t ^ 4 - 6 * t ^ 2 * initialSlope t +
    3 * initialSlope t ^ 3 * (initialSlope t - 2)

/-- Zeroth moment of the dimensionless profile. -/
def momentZero (t : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, value t y

/-- First moment of the dimensionless profile. -/
def momentOne (t : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, y * value t y

end RayleighKernel.Profile
