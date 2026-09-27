import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite discrete kernels

The discrete model uses genuine sequences on `ℕ`.  The summability fields in
`IsAdmissible` make every displayed series below a genuine finite real series,
rather than relying on the default value of `tsum` outside its domain.
-/

noncomputable section

namespace RayleighKernel.Discrete

open scoped BigOperators
open Filter
open scoped Topology

/-- A discrete kernel, indexed by the nonnegative integers. -/
abbrev Kernel := ℕ → ℝ

/-- The zero-extended first difference, with the convention `w (-1) = 0`. -/
def difference (w : Kernel) : Kernel
  | 0 => w 0
  | j + 1 => w (j + 1) - w j

@[simp] theorem difference_zero (w : Kernel) : difference w 0 = w 0 := rfl

@[simp] theorem difference_succ (w : Kernel) (j : ℕ) :
    difference w (j + 1) = w (j + 1) - w j := rfl

/-- Discrete total mass. -/
def mass (w : Kernel) : ℝ := ∑' j : ℕ, w j

/-- The unscaled first moment of a discrete kernel. -/
def firstMoment (w : Kernel) : ℝ := ∑' j : ℕ, (j : ℝ) * w j

/-- The square energy of a discrete kernel. -/
def squareEnergy (w : Kernel) : ℝ := ∑' j : ℕ, (w j) ^ 2

/-- The energy of the zero-extended first difference. -/
def differenceEnergy (w : Kernel) : ℝ := ∑' j : ℕ, (difference w j) ^ 2

/-- The discrete Rayleigh quotient. -/
def rayleighQuotient (w : Kernel) : ℝ := differenceEnergy w / squareEnergy w

/-- The finite-series hypotheses and normalization defining an admissible kernel. -/
structure IsAdmissible (h L : ℝ) (w : Kernel) : Prop where
  h_pos : 0 < h
  nonnegative : ∀ j, 0 ≤ w j
  summable_abs : Summable (fun j => |w j|)
  summable_sq : Summable (fun j => (w j) ^ 2)
  summable_difference_sq : Summable (fun j => (difference w j) ^ 2)
  summable_firstMoment : Summable (fun j : ℕ => (j : ℝ) * w j)
  mass_eq : mass w = 1
  scaled_firstMoment_eq : h * firstMoment w = L

namespace IsAdmissible

theorem summable {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : Summable w := by
  exact (summable_abs_iff.mp hw.summable_abs)

theorem tendsto_atTop_zero {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Tendsto w atTop (𝓝 0) :=
  hw.summable.tendsto_atTop_zero

theorem summable_mass {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : Summable (fun j => w j) :=
  hw.summable

theorem summable_firstMoment' {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Summable (fun j : ℕ => (j : ℝ) * w j) := hw.summable_firstMoment

theorem summable_squareEnergy {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Summable (fun j => (w j) ^ 2) := hw.summable_sq

theorem summable_differenceEnergy {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Summable (fun j => (difference w j) ^ 2) := hw.summable_difference_sq

theorem mass_eq' {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : mass w = 1 := hw.mass_eq

theorem firstMoment_eq {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : h * firstMoment w = L :=
  hw.scaled_firstMoment_eq

theorem nonzero {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : ∃ j, w j ≠ 0 := by
  by_contra hn
  have hz : ∀ j, w j = 0 := by
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  have hm : mass w = 0 := by
    rw [mass]
    simp [hz]
  linarith [hw.mass_eq, hm]

theorem squareEnergy_pos {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : 0 < squareEnergy w := by
  obtain ⟨j, hj⟩ := hw.nonzero
  have hsq : 0 < (w j) ^ 2 := sq_pos_of_ne_zero hj
  exact hw.summable_sq.tsum_pos (fun i => sq_nonneg (w i)) j hsq

theorem squareEnergy_ne_zero {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : squareEnergy w ≠ 0 :=
  ne_of_gt hw.squareEnergy_pos

theorem mass_nonneg {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : 0 ≤ mass w := by
  rw [mass]
  exact tsum_nonneg fun j => hw.nonnegative j

theorem squareEnergy_nonneg {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) : 0 ≤ squareEnergy w :=
  le_of_lt hw.squareEnergy_pos

theorem differenceEnergy_nonneg {h L : ℝ} {w : Kernel} (_hw : IsAdmissible h L w) :
    0 ≤ differenceEnergy w := by
  rw [differenceEnergy]
  exact tsum_nonneg fun j => sq_nonneg (difference w j)

theorem rayleighQuotient_nonneg {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    0 ≤ rayleighQuotient w := by
  unfold rayleighQuotient
  exact div_nonneg (hw.differenceEnergy_nonneg) (hw.squareEnergy_nonneg)

theorem rayleighQuotient_denominator_ne_zero {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    squareEnergy w ≠ 0 := hw.squareEnergy_ne_zero

end IsAdmissible

end RayleighKernel.Discrete
