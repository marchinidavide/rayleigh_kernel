import RayleighKernel.Discrete.Defs
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open scoped BigOperators ProbabilityTheory
namespace RayleighKernel.Probability

structure IsWhiteInput {Ω : Type*} [MeasurableSpace Ω] (r : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  memLp : ∀ t, MemLp (r t) 2 μ
  centered : ∀ t, μ[r t] = 0
  secondMoment : ∀ t s, μ[(r t) * (r s)] = if t = s then 1 else 0

def finiteSignal {Ω : Type*} (N : ℕ) (w : Discrete.Kernel) (r : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  ∑ j ∈ Finset.range N, (fun ω => w j * r (t - (j : ℤ)) ω)

theorem finiteSignal_memLp {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} (hr : IsWhiteInput r μ) (t : ℤ) :
    MemLp (finiteSignal N w r t) 2 μ := by
  unfold finiteSignal
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum' (Finset.range N)
      (f := fun j ω => w j * r (t - (j : ℤ)) ω)
      (fun j hj => (hr.memLp (t - (j : ℤ))).const_mul (w j)))

theorem finiteSignal_expectation_zero {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hr : IsWhiteInput r μ) (t : ℤ) : μ[finiteSignal N w r t] = 0 := by
  unfold finiteSignal
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hr.centered]
    simp
  · intro j hj
    exact ((hr.memLp (t - (j : ℤ))).const_mul (w j)).integrable one_le_two

theorem finiteSignal_covariance {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hr : IsWhiteInput r μ) (j k : ℕ) (t : ℤ) :
    cov[r (t - (j : ℤ)), r (t - (k : ℤ)); μ] = if j = k then 1 else 0 := by
  rw [ProbabilityTheory.covariance_eq_sub (hr.memLp _) (hr.memLp _)]
  simp only [hr.centered, mul_zero, sub_zero]
  by_cases h : j = k
  · subst k
    simpa using hr.secondMoment (t - (j : ℤ)) (t - (j : ℤ))
  · have h' : t - (j : ℤ) ≠ t - (k : ℤ) := by omega
    simpa [h, h'] using hr.secondMoment (t - (j : ℤ)) (t - (k : ℤ))

theorem finiteSignal_variance {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {w : Discrete.Kernel}
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] (hr : IsWhiteInput r μ) (t : ℤ) :
    Var[finiteSignal N w r t; μ] = ∑ j ∈ Finset.range N, (w j) ^ 2 := by
  unfold finiteSignal
  have hsum := ProbabilityTheory.variance_fun_sum'
    (μ := μ) (s := Finset.range N)
    (X := fun j ω => w j * r (t - (j : ℤ)) ω)
    (fun j hj => (hr.memLp (t - (j : ℤ))).const_mul (w j))
  rw [show (∑ j ∈ Finset.range N, (fun ω => w j * r (t - (j : ℤ)) ω)) =
      (fun ω => ∑ j ∈ Finset.range N, w j * r (t - (j : ℤ)) ω) by
        ext ω; simp]
  rw [hsum]
  simp_rw [ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right, finiteSignal_covariance hr]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Finset.mem_range.mp hx, sq]

theorem finiteSignal_difference_correction {Ω : Type*} (N : ℕ) (w : Discrete.Kernel)
    (r : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω =
      finiteSignal (N + 1) (Discrete.difference w) r t ω -
        w N * r (t - (N : ℤ)) ω := by
  induction N with
  | zero => simp [finiteSignal]
  | succ N ih =>
      rw [finiteSignal, finiteSignal, finiteSignal, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Pi.add_apply, Finset.sum_apply]
      change (∑ x ∈ Finset.range N, w x * r (t - (x : ℤ)) ω) +
          w N * r (t - (N : ℤ)) ω -
          ((∑ x ∈ Finset.range N, w x * r (t - 1 - (x : ℤ)) ω) +
            w N * r (t - 1 - (N : ℤ)) ω) = _
      have hi := ih
      simp only [finiteSignal, Finset.sum_apply] at hi
      calc
        _ = ((∑ x ∈ Finset.range N, w x * r (t - (x : ℤ)) ω) -
          ∑ x ∈ Finset.range N, w x * r (t - 1 - (x : ℤ)) ω) +
          w N * r (t - (N : ℤ)) ω - w N * r (t - 1 - (N : ℤ)) ω := by ring
        _ = (∑ c ∈ Finset.range (N + 1), Discrete.difference w c *
          r (t - (c : ℤ)) ω - w N * r (t - (N : ℤ)) ω) +
          w N * r (t - (N : ℤ)) ω - w N * r (t - 1 - (N : ℤ)) ω := by rw [hi]
        _ = _ := by
          rw [Finset.sum_range_succ]
          ring_nf
          rw [show -1 + t - (N : ℤ) = t - ((N + 1 : ℕ) : ℤ) by omega]
          have hd : Discrete.difference w (1 + N) = w (1 + N) - w N := by
            simp [Nat.add_comm, Discrete.difference_succ]
          rw [hd]
          ring_nf

theorem finiteSignal_sub_previous {Ω : Type*} (N : ℕ) (w : Discrete.Kernel)
    (r : ℤ → Ω → ℝ) (t : ℤ) (hwN : w N = 0) :
    (fun ω => finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω) =
      finiteSignal (N + 1) (Discrete.difference w) r t := by
  funext ω
  rw [finiteSignal_difference_correction N w r t ω, hwN]
  simp

theorem finiteSignal_difference_variance {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {w : Discrete.Kernel} {r : ℤ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (t : ℤ) (hwN : w N = 0) :
    Var[fun ω => finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω; μ] =
      ∑ j ∈ Finset.range (N + 1), (Discrete.difference w j) ^ 2 := by
  rw [show (fun ω => finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω) =
      finiteSignal (N + 1) (Discrete.difference w) r t by
        exact finiteSignal_sub_previous N w r t hwN]
  exact finiteSignal_variance hr t

end RayleighKernel.Probability
