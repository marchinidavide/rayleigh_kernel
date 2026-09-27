import RayleighKernel.Discrete.Interpolation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set Filter Topology MeasureTheory

namespace RayleighKernel.Discrete

/-- Integral of an affine function over an interval. -/
theorem integral_affine (a b A B : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, (A + (x - a) * B) =
      (b - a) * A + (b - a)^2 * B / 2 := by
  let F : ℝ → ℝ := fun x => (A - a * B) * x + B * x^2 / 2
  have hF : ∀ x, HasDerivAt F (A + (x - a) * B) x := by
    intro x
    dsimp [F]
    convert (hasDerivAt_id x).const_mul (A - a * B) |>.add
      (((hasDerivAt_id x).pow 2).const_mul (B / 2)) using 1
    · funext y; simp; ring
    · simp; ring
  have hcont : ContinuousOn F (Icc a b) := by dsimp [F]; fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => A + (x - a) * B) volume a b := by
    apply (show Continuous (fun x : ℝ => A + (x - a) * B) by fun_prop).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont]
  · dsimp [F]; ring
  · intro x hx; exact hF x
  · exact hint

/-- Integral of `x` times an affine function over an interval. -/
theorem integral_id_mul_affine (a b A B : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, x * (A + (x - a) * B) =
      a * ((b - a) * A + (b - a)^2 * B / 2) +
        A * (b - a)^2 / 2 + B * (b - a)^3 / 3 := by
  let F : ℝ → ℝ := fun x => (A - a * B) * x^2 / 2 + B * x^3 / 3
  have hF : ∀ x, HasDerivAt F (x * (A + (x - a) * B)) x := by
    intro x
    dsimp [F]
    convert (((hasDerivAt_id x).pow 2).const_mul ((A - a * B) / 2)).add
      (((hasDerivAt_id x).pow 3).const_mul (B / 3)) using 1
    · funext y; simp; ring
    · simp; ring
  have hcont : ContinuousOn F (Icc a b) := by dsimp [F]; fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => x * (A + (x - a) * B)) volume a b := by
    apply (show Continuous (fun x : ℝ => x * (A + (x - a) * B)) by fun_prop).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont]
  · dsimp [F]; ring
  · intro x hx; exact hF x
  · exact hint

private theorem neg_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) :
    EqOn (interpolant h w) (fun x => (x + h) * (w 0 / h^2)) (uIcc (-h) 0) := by
  intro x hx
  have hneg : -h ≤ (0 : ℝ) := by linarith
  rw [uIcc_of_le hneg] at hx
  rcases hx with ⟨hx₁, hx₂⟩
  rcases lt_or_eq_of_le hx₁ with hlt | rfl
  · exact interpolant_neg_interval hh ⟨hlt, hx₂⟩
  · simp [interpolant]

private theorem neg_integral_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) :
    (∫ x in -h..0, interpolant h w x) =
      ∫ x in -h..0, (x + h) * (w 0 / h^2) := by
  exact intervalIntegral.integral_congr (neg_bridge h w hh)

private theorem neg_weighted_integral_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) :
    (∫ x in -h..0, x * interpolant h w x) =
      ∫ x in -h..0, x * ((x + h) * (w 0 / h^2)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  rw [neg_bridge h w hh hx]

private theorem cell_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    EqOn (interpolant h w)
      (fun x => w j / h + (x - (j : ℝ) * h) *
        (w (j + 1) - w j) / h^2)
      (uIcc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)) := by
  intro x hx
  have hcell_le : (j : ℝ) * h ≤ (((j + 1 : ℕ) : ℝ) * h) := by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith
  rw [uIcc_of_le hcell_le] at hx
  rcases hx with ⟨hx₁, hx₂⟩
  by_cases he : x = ((j + 1 : ℕ) : ℝ) * h
  · subst x
    rw [interpolant_node hh (j + 1)]
    field_simp [ne_of_gt hh]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
  · exact interpolant_cell hh j ⟨hx₁, lt_of_le_of_ne hx₂ he⟩

private theorem cell_integral_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    (∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h, interpolant h w x) =
      ∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h,
        w j / h + (x - (j : ℝ) * h) * (w (j + 1) - w j) / h^2 := by
  exact intervalIntegral.integral_congr (cell_bridge h w hh j)

private theorem cell_weighted_integral_bridge (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    (∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h, x * interpolant h w x) =
      ∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h,
        x * (w j / h + (x - (j : ℝ) * h) * (w (j + 1) - w j) / h^2) := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  rw [cell_bridge h w hh j hx]

/-- Mass of the interpolant on the initial strip. -/
theorem neg_mass (h : ℝ) (w : Kernel) (hh : 0 < h) :
    (∫ x in -h..0, interpolant h w x) = w 0 / 2 := by
  rw [neg_integral_bridge h w hh]
  have H := integral_affine (-h) 0 0 (w 0 / h^2) (by linarith)
  convert H using 1
  · congr 1; funext x; ring
  · field_simp [ne_of_gt hh]
    ring

/-- First moment of the interpolant on the initial strip. -/
theorem neg_first_moment (h : ℝ) (w : Kernel) (hh : 0 < h) :
    (∫ x in -h..0, x * interpolant h w x) = -(h * w 0) / 6 := by
  rw [neg_weighted_integral_bridge h w hh]
  have H := integral_id_mul_affine (-h) 0 0 (w 0 / h^2) (by linarith)
  convert H using 1
  · congr 1; funext x; ring
  · field_simp [ne_of_gt hh]
    ring

/-- Mass of the interpolant on a positive mesh cell. -/
theorem cell_mass (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    (∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h, interpolant h w x) =
      (w j + w (j + 1)) / 2 := by
  have hcell_le : (j : ℝ) * h ≤ (((j + 1 : ℕ) : ℝ) * h) := by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith
  rw [cell_integral_bridge h w hh j]
  have H := integral_affine ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)
      (w j / h) ((w (j + 1) - w j) / h^2) hcell_le
  convert H using 1
  · congr 1; funext x; ring
  · field_simp [ne_of_gt hh]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
    ring

/-- First moment of the interpolant on a positive mesh cell. -/
theorem cell_first_moment (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    (∫ x in (j : ℝ) * h..((j + 1 : ℕ) : ℝ) * h, x * interpolant h w x) =
      h / 6 * ((3 * (j : ℝ) + 1) * w j + (3 * (j : ℝ) + 2) * w (j + 1)) := by
  have hcell_le : (j : ℝ) * h ≤ (((j + 1 : ℕ) : ℝ) * h) := by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith
  rw [cell_weighted_integral_bridge h w hh j]
  have H := integral_id_mul_affine ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)
      (w j / h) ((w (j + 1) - w j) / h^2) hcell_le
  convert H using 1
  · congr 1; funext x; ring
  · field_simp [ne_of_gt hh]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
    ring

/-! The remaining four declarations provide interval-integrability for the same strips. -/

/-- The interpolant is interval-integrable on the initial strip. -/
theorem neg_integrable (h : ℝ) (w : Kernel) (hh : 0 < h) :
    IntervalIntegrable (interpolant h w) volume (-h) 0 :=
  (continuous_interpolant hh).intervalIntegrable _ _

/-- The interpolant is interval-integrable on every positive mesh cell. -/
theorem cell_integrable (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    IntervalIntegrable (interpolant h w) volume
      ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) :=
  (continuous_interpolant hh).intervalIntegrable _ _

/-- `x` times the interpolant is interval-integrable on the initial strip. -/
theorem neg_weighted_integrable (h : ℝ) (w : Kernel) (hh : 0 < h) :
    IntervalIntegrable (fun x => x * interpolant h w x) volume (-h) 0 :=
  (continuous_id.mul (continuous_interpolant hh)).intervalIntegrable _ _

/-- `x` times the interpolant is interval-integrable on every positive mesh cell. -/
theorem cell_weighted_integrable (h : ℝ) (w : Kernel) (hh : 0 < h) (j : ℕ) :
    IntervalIntegrable (fun x => x * interpolant h w x) volume
      ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) :=
  (continuous_id.mul (continuous_interpolant hh)).intervalIntegrable _ _

end RayleighKernel.Discrete
