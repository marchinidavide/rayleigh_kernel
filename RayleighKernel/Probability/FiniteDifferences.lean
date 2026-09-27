import RayleighKernel.Probability.TurnoverIsotropic

noncomputable section
open scoped BigOperators
namespace RayleighKernel.Probability

def differencePrimitive (a : Discrete.Kernel) : Discrete.Kernel :=
  fun j => ∑ k ∈ Finset.range (j + 1), a k

@[simp] theorem difference_differencePrimitive (a : Discrete.Kernel) :
    Discrete.difference (differencePrimitive a) = a := by
  funext j
  cases j with
  | zero => simp [differencePrimitive]
  | succ j =>
    simp only [Discrete.difference_succ, differencePrimitive]
    rw [Finset.sum_range_succ]
    ring

theorem sum_difference_eq_endpoint (w : Discrete.Kernel) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), Discrete.difference w j = w N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Discrete.difference_succ]
    ring

theorem sum_difference_eq_zero_of_cutoff (w : Discrete.Kernel) (N : ℕ)
    (htail : ∀ j, N ≤ j → w j = 0) :
    ∑ j ∈ Finset.range (N + 1), Discrete.difference w j = 0 := by
  rw [sum_difference_eq_endpoint]
  exact htail N le_rfl

private theorem differencePrimitive_eq_sum_range_of_ge
    (a : Discrete.Kernel) (N j : ℕ) (hNj : N ≤ j)
    (htail : ∀ k, N + 1 ≤ k → a k = 0) :
    differencePrimitive a j = ∑ k ∈ Finset.range (N + 1), a k := by
  induction j, hNj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hprefix : (∑ k ∈ Finset.range (j + 1), a k) =
        ∑ k ∈ Finset.range (N + 1), a k := by
      simpa [differencePrimitive] using ih
    rw [differencePrimitive, Finset.sum_range_succ, hprefix,
      htail (j + 1) (by omega)]
    simp

theorem differencePrimitive_cutoff (a : Discrete.Kernel) (N : ℕ)
    (htail : ∀ j, N + 1 ≤ j → a j = 0)
    (hsum : ∑ j ∈ Finset.range (N + 1), a j = 0) :
    ∀ j, N ≤ j → differencePrimitive a j = 0 := by
  intro j hj
  rw [differencePrimitive_eq_sum_range_of_ge a N j hj htail, hsum]

theorem differencePrimitive_eq_a (a : Discrete.Kernel) :
    Discrete.difference (differencePrimitive a) = a :=
  difference_differencePrimitive a

theorem exists_cutoff_difference_iff_zero_sum
    (a : Discrete.Kernel) (N : ℕ)
    (ha : ∀ j, N + 1 ≤ j → a j = 0) :
    (∃ w, (∀ j, N ≤ j → w j = 0) ∧ Discrete.difference w = a) ↔
      ∑ j ∈ Finset.range (N + 1), a j = 0 := by
  constructor
  · rintro ⟨w, hw, hwa⟩
    rw [← show (∑ j ∈ Finset.range (N + 1),
        Discrete.difference w j) = ∑ j ∈ Finset.range (N + 1), a j by
          rw [hwa]]
    exact sum_difference_eq_zero_of_cutoff w N hw
  · intro hsum
    refine ⟨differencePrimitive a, differencePrimitive_cutoff a N ha hsum,
      differencePrimitive_eq_a a⟩

end RayleighKernel.Probability
