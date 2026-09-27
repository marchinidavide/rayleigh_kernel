import RayleighKernel.Probability.UniformIntegrability

/-!
# Finite diffuse coefficient rows

This module contains only the finite-row norm, maximum, and diffuseness
packaging used by the weighted triangular-array results.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open Filter
open scoped BigOperators Topology

namespace RayleighKernel.Probability

/-- The Euclidean norm of a coefficient row on a finite index set. -/
def rowL2Norm {ι : Type*} (s : Finset ι) (a : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ s, (a i) ^ 2)

/-- A total finite maximum of the absolute row coefficients. -/
def rowMax {ι : Type*} (s : Finset ι) (a : ι → ℝ) : ℝ :=
  s.fold max 0 (fun i => |a i|)

theorem rowL2Norm_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    0 ≤ rowL2Norm s a := by
  exact Real.sqrt_nonneg _

theorem rowL2Norm_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (rowL2Norm s a) ^ 2 = ∑ i ∈ s, (a i) ^ 2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (a i))

theorem rowL2Norm_pos_of_mem_ne_zero {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : ∃ i ∈ s, a i ≠ 0) : 0 < rowL2Norm s a := by
  unfold rowL2Norm
  rw [Real.sqrt_pos]
  rw [Finset.sum_pos_iff_of_nonneg (fun i hi => sq_nonneg (a i))]
  obtain ⟨i, hi, hai⟩ := ha
  exact ⟨i, hi, sq_pos_of_ne_zero hai⟩

theorem rowL2Norm_pos_iff {ι : Type*} {s : Finset ι} {a : ι → ℝ} :
    0 < rowL2Norm s a ↔ ∃ i ∈ s, a i ≠ 0 := by
  constructor
  · intro hpos
    by_contra h
    have hz : ∀ i ∈ s, a i = 0 := by
      intro i hi
      by_contra hai
      exact h ⟨i, hi, hai⟩
    have hsum : (∑ i ∈ s, (a i) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hz i hi]
    rw [rowL2Norm, hsum] at hpos
    simp at hpos
  · exact rowL2Norm_pos_of_mem_ne_zero

theorem rowL2Norm_ne_zero_of_mem_ne_zero {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : ∃ i ∈ s, a i ≠ 0) : rowL2Norm s a ≠ 0 :=
  ne_of_gt (rowL2Norm_pos_of_mem_ne_zero ha)

theorem rowL2Norm_normalized_sq_sum {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : 0 < rowL2Norm s a) :
    ∑ i ∈ s, (a i / rowL2Norm s a) ^ 2 = 1 := by
  have hsum : 0 < ∑ i ∈ s, (a i) ^ 2 := by
    exact Real.sqrt_pos.mp (by simpa [rowL2Norm] using ha)
  have hnorm : (rowL2Norm s a) ^ 2 = ∑ i ∈ s, (a i) ^ 2 :=
    rowL2Norm_sq s a
  calc
    ∑ i ∈ s, (a i / rowL2Norm s a) ^ 2 =
        (∑ i ∈ s, (a i) ^ 2) / (rowL2Norm s a) ^ 2 := by
      rw [Finset.sum_div]
      congr 1
      funext i
      ring
    _ = 1 := by rw [hnorm]; field_simp

theorem rowMax_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    0 ≤ rowMax s a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rowMax]
  | @insert i t hit ih =>
      rw [rowMax, Finset.fold_insert hit]
      exact le_max_of_le_left (abs_nonneg _)

theorem abs_le_rowMax {ι : Type*} {s : Finset ι} {a : ι → ℝ} {i : ι}
    (hi : i ∈ s) : |a i| ≤ rowMax s a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hi
  | @insert j t hj ih =>
      rw [rowMax, Finset.fold_insert hj]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih hi)

theorem normalized_abs_le_max_ratio {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    {i : ι} (hi : i ∈ s) (hnorm : 0 < rowL2Norm s a) :
    |a i / rowL2Norm s a| ≤ rowMax s a / rowL2Norm s a := by
  rw [abs_div, abs_of_pos hnorm]
  exact (div_le_div_of_nonneg_right (abs_le_rowMax hi) hnorm.le)

theorem rowMax_ratio_eventually_diffuse
    {ι : Type*} [DecidableEq ι] (s : ℕ → Finset ι) (a : ℕ → ι → ℝ)
    (hnorm : ∀ n, 0 < rowL2Norm (s n) (a n))
    (hratio : Tendsto (fun n => rowMax (s n) (a n) /
      rowL2Norm (s n) (a n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i ∈ s n, |a n i / rowL2Norm (s n) (a n)| ≤ ε := by
  intro ε hε
  have hev : ∀ᶠ n in atTop,
      rowMax (s n) (a n) / rowL2Norm (s n) (a n) < ε :=
    (tendsto_order.mp hratio).2 ε hε
  filter_upwards [hev] with n hn i hi
  exact (normalized_abs_le_max_ratio hi (hnorm n)).trans hn.le

private theorem weightedFinsetSum_div_rowL2Norm
    {Ω ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → ℝ}
    {X : ι → Ω → ℝ} (_hnorm : 0 < rowL2Norm s a) :
    weightedFinsetSum s (fun i => a i / rowL2Norm s a) X =
      fun ω => weightedFinsetSum s a X ω / rowL2Norm s a := by
  funext ω
  unfold weightedFinsetSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem tendstoInDistribution_weightedFinsetSum_of_rowMax_ratio
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (s : ℕ → Finset ι) (a : ℕ → ι → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P') (hZ : AEMeasurable Z P)
    (hZ1 : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P) (hindep : iIndepFun X P)
    (hnorm : ∀ n, 0 < rowL2Norm (s n) (a n))
    (hratio : Tendsto (fun n => rowMax (s n) (a n) /
      rowL2Norm (s n) (a n)) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => weightedFinsetSum (s n) (a n) X ω /
        rowL2Norm (s n) (a n)) atTop Y (fun _ => P) P' := by
  let b : ℕ → ι → ℝ := fun n i => a n i / rowL2Norm (s n) (a n)
  have hsum : ∀ n, ∑ i ∈ s n, (b n i) ^ 2 = 1 := by
    intro n
    exact rowL2Norm_normalized_sq_sum (hnorm n)
  have hdiffuse := rowMax_ratio_eventually_diffuse s a hnorm hratio
  have hconv := tendstoInDistribution_weightedFinsetSum_of_diffuse s b hY hZ hZ1
    hZ2i hZ3 hZ0 hZ2 hident hindep hsum hdiffuse
  convert hconv using 1
  funext n ω
  exact (weightedFinsetSum_div_rowL2Norm (hnorm n)) ▸ rfl

theorem tendsto_integral_abs_weightedFinsetSum_of_rowMax_ratio
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (s : ℕ → Finset ι) (a : ℕ → ι → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P') (hZ : AEMeasurable Z P)
    (hZ1 : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P) (hindep : iIndepFun X P)
    (hnorm : ∀ n, 0 < rowL2Norm (s n) (a n))
    (hratio : Tendsto (fun n => rowMax (s n) (a n) /
      rowL2Norm (s n) (a n)) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, |weightedFinsetSum (s n) (a n) X ω| ∂P) /
      rowL2Norm (s n) (a n)) atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  let b : ℕ → ι → ℝ := fun n i => a n i / rowL2Norm (s n) (a n)
  have hsum : ∀ n, ∑ i ∈ s n, (b n i) ^ 2 = 1 := by
    intro n
    exact rowL2Norm_normalized_sq_sum (hnorm n)
  have hdiffuse := rowMax_ratio_eventually_diffuse s a hnorm hratio
  have hlim := tendsto_integral_abs_weightedFinsetSum_of_diffuse s b hY hZ hZ1
    hZ2i hZ3 hZ0 hZ2 hident hindep hsum hdiffuse
  have hscalar : ∀ n,
      (∫ ω, |weightedFinsetSum (s n) (b n) X ω| ∂P) =
        (∫ ω, |weightedFinsetSum (s n) (a n) X ω| ∂P) /
          rowL2Norm (s n) (a n) := by
    intro n
    rw [show weightedFinsetSum (s n) (b n) X =
        fun ω => weightedFinsetSum (s n) (a n) X ω /
          rowL2Norm (s n) (a n) by
      exact weightedFinsetSum_div_rowL2Norm (hnorm n)]
    rw [show (fun ω => |weightedFinsetSum (s n) (a n) X ω /
        rowL2Norm (s n) (a n)|) =
        fun ω => |weightedFinsetSum (s n) (a n) X ω| /
          rowL2Norm (s n) (a n) by
      funext ω
      rw [abs_div, abs_of_pos (hnorm n)]]
    rw [show (fun ω => |weightedFinsetSum (s n) (a n) X ω| /
        rowL2Norm (s n) (a n)) =
        fun ω => (rowL2Norm (s n) (a n))⁻¹ *
          |weightedFinsetSum (s n) (a n) X ω| by
      funext ω
      ring]
    rw [integral_const_mul]
    ring
  simpa only [hscalar] using hlim

theorem weightedFinsetSum_range_eq_finiteSignal
    {Ω : Type*} (N : ℕ) (w : Discrete.Kernel)
    (r : ℤ → Ω → ℝ) (t : ℤ) :
    weightedFinsetSum (Finset.range N) w
        (fun j ω => r (t - (j : ℤ)) ω) = finiteSignal N w r t := by
  funext ω
  simp [weightedFinsetSum, finiteSignal]

private theorem lag_map_injective (t : ℤ) :
    Function.Injective (fun j : ℕ => t - (j : ℤ)) := by
  intro j k h
  apply Int.ofNat_inj.mp
  exact sub_right_injective h

private theorem iIndepFun_lag_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {r : ℤ → Ω → ℝ} (t : ℤ) (hindep : iIndepFun r P) :
    iIndepFun (fun j : ℕ => r (t - (j : ℤ))) P := by
  exact hindep.precomp (lag_map_injective t)

theorem tendstoInDistribution_finiteSignal_difference_of_rowMax_ratio
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {r : ℤ → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (N : ℕ → ℕ) (w : ℕ → Discrete.Kernel) (t : ℤ)
    (hY : HasLaw Y (gaussianReal 0 1) P') (hZ : AEMeasurable Z P)
    (hZ1 : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P) (hZ0 : P[Z] = 0)
    (hZ2 : P[Z ^ 2] = 1) (hident : ∀ k : ℤ, IdentDistrib (r k) Z P P)
    (hindep : iIndepFun r P) (hcut : ∀ n, w n (N n) = 0)
    (hnorm : ∀ n, 0 < rowL2Norm (Finset.range (N n + 1))
      (Discrete.difference (w n)))
    (hratio : Tendsto (fun n => rowMax (Finset.range (N n + 1))
      (Discrete.difference (w n)) /
      rowL2Norm (Finset.range (N n + 1)) (Discrete.difference (w n)))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω =>
        (finiteSignal (N n) (w n) r t ω -
          finiteSignal (N n) (w n) r (t - 1) ω) /
          rowL2Norm (Finset.range (N n + 1))
            (Discrete.difference (w n)))
      atTop Y (fun _ => P) P' := by
  let X : ℕ → Ω → ℝ := fun j ω => r (t - (j : ℤ)) ω
  have hident' : ∀ j, IdentDistrib (X j) Z P P := by
    intro j
    exact hident (t - (j : ℤ))
  have hindep' : iIndepFun X P := by
    exact iIndepFun_lag_family t hindep
  have hconv := tendstoInDistribution_weightedFinsetSum_of_rowMax_ratio
    (fun n => Finset.range (N n + 1)) (fun n => Discrete.difference (w n))
    hY hZ hZ1 hZ2i hZ3 hZ0 hZ2 hident' hindep' hnorm hratio
  convert hconv using 1
  funext n ω
  have hd := finiteSignal_sub_previous (N n) (w n) r t (hcut n)
  rw [congrFun hd ω]
  exact (weightedFinsetSum_range_eq_finiteSignal _ _ _ _).symm ▸ rfl

theorem tendsto_integral_abs_finiteSignal_difference_of_rowMax_ratio
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {r : ℤ → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (N : ℕ → ℕ) (w : ℕ → Discrete.Kernel) (t : ℤ)
    (hY : HasLaw Y (gaussianReal 0 1) P') (hZ : AEMeasurable Z P)
    (hZ1 : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P) (hZ0 : P[Z] = 0)
    (hZ2 : P[Z ^ 2] = 1) (hident : ∀ k : ℤ, IdentDistrib (r k) Z P P)
    (hindep : iIndepFun r P) (hcut : ∀ n, w n (N n) = 0)
    (hnorm : ∀ n, 0 < rowL2Norm (Finset.range (N n + 1))
      (Discrete.difference (w n)))
    (hratio : Tendsto (fun n => rowMax (Finset.range (N n + 1))
      (Discrete.difference (w n)) /
      rowL2Norm (Finset.range (N n + 1))
        (Discrete.difference (w n))) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, |finiteSignal (N n) (w n) r t ω -
        finiteSignal (N n) (w n) r (t - 1) ω| ∂P) /
        rowL2Norm (Finset.range (N n + 1))
          (Discrete.difference (w n))) atTop
      (𝓝 (Real.sqrt (2 / Real.pi))) := by
  let X : ℕ → Ω → ℝ := fun j ω => r (t - (j : ℤ)) ω
  have hident' : ∀ j, IdentDistrib (X j) Z P P := fun j =>
    hident (t - (j : ℤ))
  have hindep' : iIndepFun X P := iIndepFun_lag_family t hindep
  have hlim := tendsto_integral_abs_weightedFinsetSum_of_rowMax_ratio
    (fun n => Finset.range (N n + 1)) (fun n => Discrete.difference (w n))
    hY hZ hZ1 hZ2i hZ3 hZ0 hZ2 hident' hindep' hnorm hratio
  convert hlim using 1
  funext n
  have hd := finiteSignal_sub_previous (N n) (w n) r t (hcut n)
  rw [show (fun ω => |finiteSignal (N n) (w n) r t ω -
      finiteSignal (N n) (w n) r (t - 1) ω|) =
      fun ω => |finiteSignal (N n + 1) (Discrete.difference (w n)) r t ω| by
    exact funext fun ω => congrArg abs (congrFun hd ω)]
  rw [show (fun ω => |finiteSignal (N n + 1) (Discrete.difference (w n)) r t ω|) =
      fun ω => |weightedFinsetSum (Finset.range (N n + 1))
        (Discrete.difference (w n)) X ω| by
    rw [weightedFinsetSum_range_eq_finiteSignal]]

end RayleighKernel.Probability
