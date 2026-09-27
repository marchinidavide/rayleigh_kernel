import RayleighKernel.Probability.FixedRiskTurnover

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology
namespace RayleighKernel.Probability

structure ProjectionScaleWhite
    {Ω ΩZ : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩZ]
    (r : ℤ → Ω → ℝ) (μ : Measure Ω)
    (Z : ΩZ → ℝ) (ν : Measure ΩZ) (σr : ℝ) : Prop where
  scale_pos : 0 < σr
  reference_memLp : MemLp Z 2 ν
  reference_centered : ∫ z, Z z ∂ν = 0
  reference_secondMoment : ∫ z, (Z z)^2 ∂ν = 1
  projection : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    IdentDistrib (finiteSignal N w r t)
      (fun z => σr * Real.sqrt (∑ j ∈ Finset.range N, (w j)^2) * Z z) μ ν

namespace ProjectionScaleWhite

variable {Ω ΩZ : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩZ]
variable {r : ℤ → Ω → ℝ} {μ : Measure Ω} {Z : ΩZ → ℝ} {ν : Measure ΩZ}
variable {σr : ℝ}
variable (h : ProjectionScaleWhite r μ Z ν σr)

theorem projection_memLp (h : ProjectionScaleWhite r μ Z ν σr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    MemLp (finiteSignal N w r t) 2 μ := by
  rw [(ProjectionScaleWhite.projection h N w t).memLp_iff]
  exact (h.reference_memLp.const_mul
    (σr * Real.sqrt (∑ j ∈ Finset.range N, (w j)^2)))

theorem projection_integral (h : ProjectionScaleWhite r μ Z ν σr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    ∫ ω, finiteSignal N w r t ω ∂μ = 0 := by
  rw [(ProjectionScaleWhite.projection h N w t).integral_eq]
  rw [integral_const_mul, h.reference_centered]
  simp

theorem projection_secondMoment (h : ProjectionScaleWhite r μ Z ν σr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    ∫ ω, (finiteSignal N w r t ω)^2 ∂μ =
      σr^2 * ∑ j ∈ Finset.range N, (w j)^2 := by
  have hs : 0 ≤ ∑ j ∈ Finset.range N, (w j)^2 :=
    Finset.sum_nonneg (fun j hj => sq_nonneg _)
  rw [(ProjectionScaleWhite.projection h N w t).sq.integral_eq]
  simp only [mul_pow]
  rw [integral_const_mul, h.reference_secondMoment]
  rw [Real.sq_sqrt hs]
  ring

theorem projection_variance (h : ProjectionScaleWhite r μ Z ν σr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    Var[finiteSignal N w r t; μ] =
      σr^2 * ∑ j ∈ Finset.range N, (w j)^2 := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (projection_memLp h N w t).aemeasurable (projection_integral h N w t)]
  exact projection_secondMoment h N w t

private def oneKernel : Discrete.Kernel := fun j => if j = 0 then 1 else 0

private theorem finiteSignal_oneKernel {Ω : Type*} (r : ℤ → Ω → ℝ) (s : ℤ) :
    finiteSignal 1 oneKernel r s = r s := by
  funext ω
  simp [finiteSignal, oneKernel]

theorem coordinate_memLp (h : ProjectionScaleWhite r μ Z ν σr) (s : ℤ) : MemLp (r s) 2 μ := by
  rw [← finiteSignal_oneKernel r s]
  exact projection_memLp h 1 oneKernel s

theorem coordinate_integral (h : ProjectionScaleWhite r μ Z ν σr) (s : ℤ) :
    ∫ ω, r s ω ∂μ = 0 := by
  rw [← finiteSignal_oneKernel r s]
  exact projection_integral h 1 oneKernel s

theorem coordinate_secondMoment (h : ProjectionScaleWhite r μ Z ν σr) (s : ℤ) :
    ∫ ω, (r s ω)^2 ∂μ = σr^2 := by
  rw [← finiteSignal_oneKernel r s]
  simpa [oneKernel] using projection_secondMoment h 1 oneKernel s

private def lagKernel (d : ℕ) : Discrete.Kernel := fun j => if j = d then 1 else 0

private theorem finiteSignal_lagKernel {Ω : Type*} (r : ℤ → Ω → ℝ) (t : ℤ)
    {d N : ℕ} (hdN : d < N) :
    finiteSignal N (lagKernel d) r t = r (t - (d : ℤ)) := by
  funext ω
  simp [finiteSignal, lagKernel, Finset.mem_range, hdN]

private theorem lagKernel_sum_sq (d N : ℕ) (hdN : d < N) :
    ∑ j ∈ Finset.range N, (lagKernel d j)^2 = 1 := by
  simp [lagKernel, Finset.mem_range, hdN]

private theorem finiteSignal_add_kernel {Ω : Type*} (N : ℕ)
    (w v : Discrete.Kernel) (r : ℤ → Ω → ℝ) (t : ℤ) :
    finiteSignal N (w + v) r t =
      fun ω => finiteSignal N w r t ω + finiteSignal N v r t ω := by
  funext ω
  simp only [finiteSignal, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_apply]

private theorem addKernel_sum_sq (d N : ℕ) (hd : 0 < d) (hdN : d < N) :
    ∑ j ∈ Finset.range N, (oneKernel j + lagKernel d j)^2 = 2 := by
  rw [show (fun j => (oneKernel j + lagKernel d j)^2) =
      (fun j => (oneKernel j)^2 + (lagKernel d j)^2 +
        2 * oneKernel j * lagKernel d j) by
        funext j; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ j ∈ Finset.range N,
      2 * oneKernel j * lagKernel d j) = 0 := by
    simp [oneKernel, lagKernel, Finset.mem_range, hdN, Nat.ne_of_gt hd]
  rw [hcross]
  have hN : 0 < N := lt_of_lt_of_le hd hdN.le
  simp [oneKernel, lagKernel, Finset.mem_range, hdN, hN]
  norm_num

private theorem finiteSignal_oneKernel_of_pos {Ω : Type*} (r : ℤ → Ω → ℝ)
    (t : ℤ) {N : ℕ} (hN : 0 < N) : finiteSignal N oneKernel r t = r t := by
  funext ω
  simp [finiteSignal, oneKernel, Finset.mem_range, hN]

private theorem cross_of_lt [IsProbabilityMeasure μ]
    (h : ProjectionScaleWhite r μ Z ν σr) (s t : ℤ) (hst : s < t) :
    ∫ ω, r s ω * r t ω ∂μ = 0 := by
  let d : ℕ := (t - s).toNat
  have hdint : (d : ℤ) = t - s := by
    dsimp [d]
    exact Int.toNat_of_nonneg (by omega)
  have hd : 0 < d := by
    dsimp [d]
    omega
  let N := d + 1
  have hdN : d < N := by simp [N]
  have hsig := projection_secondMoment h N (oneKernel + lagKernel d) t
  rw [finiteSignal_add_kernel N oneKernel (lagKernel d) r t] at hsig
  rw [finiteSignal_oneKernel_of_pos r t (by simp [N])] at hsig
  rw [finiteSignal_lagKernel r t hdN] at hsig
  rw [show t - (d : ℤ) = s by omega] at hsig
  have hsum := addKernel_sum_sq d N hd hdN
  rw [show (∑ j ∈ Finset.range N, (oneKernel + lagKernel d) j ^ 2) =
      ∑ j ∈ Finset.range N, (oneKernel j + lagKernel d j) ^ 2 by
        simp only [Pi.add_apply]] at hsig
  rw [hsum] at hsig
  have hsLp := coordinate_memLp h s
  have htLp := coordinate_memLp h t
  have hstInt : Integrable (fun ω => r s ω * r t ω) μ :=
    hsLp.integrable_mul htLp
  have hsq : (fun ω => (r t ω + r s ω)^2) =
      fun ω => (r t ω)^2 + 2 * (r s ω * r t ω) + (r s ω)^2 := by
    funext ω
    ring
  have hsig'' : ∫ ω, (r t ω + r s ω)^2 ∂μ = σr^2 * 2 := by
    simpa using hsig
  rw [hsq] at hsig''
  have hsumInt : Integrable (fun ω =>
      (r t ω)^2 + 2 * (r s ω * r t ω) + (r s ω)^2) μ :=
    (htLp.integrable_sq.add (hstInt.const_mul 2)).add (hsLp.integrable_sq)
  rw [show (fun ω => (r t ω)^2 + 2 * (r s ω * r t ω) + (r s ω)^2) =
      (fun ω => (r t ω)^2 + 2 * (r s ω * r t ω)) +
        (fun ω => (r s ω)^2) by rfl] at hsig''
  have hEq :
      (∫ ω, (r t ω)^2 + 2 * (r s ω * r t ω) + (r s ω)^2 ∂μ) =
        σr^2 * 2 := hsig''
  have hEq2 :
      (∫ ω, (r t ω)^2 + 2 * (r s ω * r t ω) + (r s ω)^2 ∂μ) =
      (∫ ω, (r t ω)^2 ∂μ) +
        (∫ ω, 2 * (r s ω * r t ω) ∂μ) +
        (∫ ω, (r s ω)^2 ∂μ) := by
    have hA := integral_add (htLp.integrable_sq.add (hstInt.const_mul 2))
      hsLp.integrable_sq
    have hB := integral_add htLp.integrable_sq (hstInt.const_mul 2)
    convert congrArg₂ (· + ·) hB rfl using 1
  rw [hEq2] at hEq
  rw [integral_const_mul, coordinate_secondMoment h t,
    coordinate_secondMoment h s] at hEq
  nlinarith [hEq]

theorem coordinate_crossSecondMoment [IsProbabilityMeasure μ]
    (h : ProjectionScaleWhite r μ Z ν σr) (s t : ℤ) :
    ∫ ω, r s ω * r t ω ∂μ = if s = t then σr^2 else 0 := by
  by_cases hst : s = t
  · subst t
    simpa [sq] using coordinate_secondMoment h s
  · by_cases hlt : s < t
    · simpa [hst] using cross_of_lt h s t hlt
    · have hlt' : t < s := by omega
      rw [show (∫ ω, r s ω * r t ω ∂μ) =
          ∫ ω, r t ω * r s ω ∂μ by
            congr 1; funext ω; ring]
      simpa [hst] using cross_of_lt h t s hlt'

theorem toIsWhiteInput [IsProbabilityMeasure μ]
    (h : ProjectionScaleWhite r μ Z ν 1) : IsWhiteInput r μ where
  memLp := coordinate_memLp h
  centered := coordinate_integral h
  secondMoment s t := by
    simpa using coordinate_crossSecondMoment h s t

end ProjectionScaleWhite
end RayleighKernel.Probability
