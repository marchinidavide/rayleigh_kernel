import RayleighKernel.Probability.FiniteDifferences
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology lp

namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

private def dptruncate (x : ℓ²(ℕ, ℝ)) (N : ℕ) : ℓ²(ℕ, ℝ) :=
  ∑ j ∈ Finset.range N, lp.single 2 j (x j)

private def dpcorrection (x : ℓ²(ℕ, ℝ)) (N M : ℕ) : ℓ²(ℕ, ℝ) :=
  ∑ j ∈ Finset.Ico N (N + M), lp.single 2 j
    (-(∑ k ∈ Finset.range N, x k) / (M : ℝ))

def IsFiniteZeroSum (x : ℓ²(ℕ, ℝ)) : Prop :=
  ∃ K, (∀ j, K ≤ j → x j = 0) ∧ ∑ j ∈ Finset.range K, x j = 0

private theorem dpeval_sum_single (f : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) :
    (∑ k ∈ s, lp.single 2 k (f k)) j = if j ∈ s then f j else 0 := by
  classical
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

private theorem dptruncate_apply (x : ℓ²(ℕ, ℝ)) (N j : ℕ) :
    dptruncate x N j = if j < N then x j else 0 := by
  change (∑ i ∈ Finset.range N, lp.single 2 i (x i)) j = _
  rw [dpeval_sum_single]
  simp [Finset.mem_range]

private theorem dpcorrection_apply (x : ℓ²(ℕ, ℝ)) (N M j : ℕ) :
    dpcorrection x N M j =
      if N ≤ j ∧ j < N + M then
        -(∑ k ∈ Finset.range N, x k) / (M : ℝ) else 0 := by
  change (∑ i ∈ Finset.Ico N (N + M), lp.single 2 i
    (-(∑ k ∈ Finset.range N, x k) / (M : ℝ))) j = _
  rw [dpeval_sum_single]
  simp [Finset.mem_Ico]

private theorem dpcorrected_apply_of_ge (x : ℓ²(ℕ, ℝ)) (N M j : ℕ)
    (hj : N + M ≤ j) :
    (dptruncate x N + dpcorrection x N M) j = 0 := by
  change dptruncate x N j + dpcorrection x N M j = 0
  rw [dptruncate_apply, dpcorrection_apply]
  have hN : ¬ j < N := by omega
  have hI : ¬ (N ≤ j ∧ j < N + M) := by omega
  simp [hN, hI]

private theorem dptruncate_sum_range (x : ℓ²(ℕ, ℝ)) (N M : ℕ) :
    ∑ j ∈ Finset.range (N + M), dptruncate x N j =
      ∑ j ∈ Finset.range N, x j := by
  calc
    _ = ∑ j ∈ Finset.range N, dptruncate x N j := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj hnot
        rw [dptruncate_apply]
        have hjN : N ≤ j := Nat.le_of_not_gt (by simpa using hnot)
        simp [Nat.not_lt.mpr hjN]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [dptruncate_apply]
      simp only [Finset.mem_range] at hj
      simp [hj]

private theorem dpcorrection_sum_range_eq (x : ℓ²(ℕ, ℝ)) (N M : ℕ) (hM : 0 < M) :
    ∑ j ∈ Finset.range (N + M), dpcorrection x N M j =
      -(∑ k ∈ Finset.range N, x k) := by
  calc
    _ = ∑ j ∈ Finset.Ico N (N + M),
        (-(∑ k ∈ Finset.range N, x k) / (M : ℝ)) := by
      rw [show (∑ j ∈ Finset.range (N + M), dpcorrection x N M j) =
        ∑ j ∈ Finset.Ico N (N + M), dpcorrection x N M j by
          symm
          apply Finset.sum_subset
          · intro j hj
            simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
            omega
          · intro j hj hnot
            rw [dpcorrection_apply]
            simp only [Finset.mem_range] at hj
            simp only [Finset.mem_Ico] at hnot
            have hnot' : ¬ (N ≤ j ∧ j < N + M) := by
              intro h; exact hnot h
            simp [hnot']]
      apply Finset.sum_congr rfl
      intro j hj
      rw [dpcorrection_apply]
      simp [Finset.mem_Ico.mp hj]
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Ico]
      have hMN : N + M - N = M := by omega
      rw [hMN]
      simp only [nsmul_eq_mul]
      field_simp [hM.ne']

private theorem dpfinite_zero_sum_corrected (x : ℓ²(ℕ, ℝ)) (N M : ℕ) (hM : 0 < M) :
    IsFiniteZeroSum (dptruncate x N + dpcorrection x N M) := by
  refine ⟨N + M, dpcorrected_apply_of_ge x N M, ?_⟩
  change (∑ j ∈ Finset.range (N + M),
      (dptruncate x N j + dpcorrection x N M j)) = 0
  rw [Finset.sum_add_distrib, dptruncate_sum_range, dpcorrection_sum_range_eq x N M hM]
  ring

private theorem dptruncate_tendsto (x : ℓ²(ℕ, ℝ)) :
    Tendsto (fun N => dptruncate x N) atTop (𝓝 x) := by
  simpa [dptruncate] using (lp.hasSum_single (p := (2 : ENNReal))
    (by norm_num) x).tendsto_sum_nat

private theorem dpexists_large_nat_reciprocal_sq (s δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ s^2 / M < δ^2 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (s^2 / δ^2) 0)
  have hM0 : 0 < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
  refine ⟨M, by exact_mod_cast hM0, ?_⟩
  apply (div_lt_iff₀ hM0).mpr
  have hratio : s^2 / δ^2 < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
  have := (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hratio
  nlinarith

private theorem dpcorrection_norm_sq (x : ℓ²(ℕ, ℝ)) (N M : ℕ) (hM : 0 < M) :
    ‖dpcorrection x N M‖ ^ (2 : ℝ) =
      (∑ k ∈ Finset.range N, x k)^2 / M := by
  change ‖∑ j ∈ Finset.Ico N (N + M), lp.single 2 j
      (-(∑ k ∈ Finset.range N, x k) / (M : ℝ))‖ ^ (2 : ℝ) = _
  have hn := lp.norm_sum_single (p := (2 : ENNReal)) (by norm_num)
      (fun _ : ℕ => (-(∑ k ∈ Finset.range N, x k) / (M : ℝ)))
      (Finset.Ico N (N + M))
  have hn' : ‖(∑ j ∈ Finset.Ico N (N + M), lp.single 2 j
      (-(∑ k ∈ Finset.range N, x k) / (M : ℝ)))‖ ^ (2 : ℝ) =
      ∑ j ∈ Finset.Ico N (N + M),
        ‖-(∑ k ∈ Finset.range N, x k) / (M : ℝ)‖ ^ (2 : ℝ) := by
    simpa [ENNReal.toReal_ofNat] using hn
  rw [hn']
  simp only [norm_neg, norm_div, norm_natCast, Real.norm_eq_abs]
  rw [show (∑ j ∈ Finset.Ico N (N + M),
      (|(∑ k ∈ Finset.range N, x k)| / (M : ℝ)) ^ (2 : ℝ)) =
      M * (|(∑ k ∈ Finset.range N, x k)| / M)^2 by
        rw [Finset.sum_const, Nat.card_Ico]
        simp]
  field_simp [hM.ne']
  simp [sq_abs]

private theorem dp_exists_finiteZeroSum_dist_lt
    (x : ℓ²(ℕ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℓ²(ℕ, ℝ), IsFiniteZeroSum y ∧ dist y x < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((dptruncate_tendsto x).eventually (Metric.ball_mem_nhds x (by linarith : 0 < ε / 2)))
  have htr : dist (dptruncate x N) x < ε / 2 := hN N le_rfl
  obtain ⟨M, hM, hMs⟩ := dpexists_large_nat_reciprocal_sq
    (∑ k ∈ Finset.range N, x k) (ε / 2) (by linarith)
  have hs : ‖dpcorrection x N M‖ ^ (2 : ℝ) < (ε / 2)^2 := by
    rw [dpcorrection_norm_sq x N M hM]
    exact hMs
  have hc : ‖dpcorrection x N M‖ < ε / 2 := by
    apply (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp
    simpa only [Real.rpow_two] using hs
  refine ⟨dptruncate x N + dpcorrection x N M,
    dpfinite_zero_sum_corrected x N M hM, ?_⟩
  calc
    dist (dptruncate x N + dpcorrection x N M) x ≤
        dist (dptruncate x N + dpcorrection x N M) (dptruncate x N) +
          dist (dptruncate x N) x := dist_triangle _ _ _
    _ = ‖dpcorrection x N M‖ + dist (dptruncate x N) x := by
      rw [dist_eq_norm, add_sub_cancel_left]
    _ < ε := by linarith

theorem dense_finiteZeroSum :
    Dense {x : ℓ²(ℕ, ℝ) | IsFiniteZeroSum x} := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨y, hy, hyd⟩ := dp_exists_finiteZeroSum_dist_lt x hr
  exact ⟨y, hyd, hy⟩

private def privateKernelOfLp (x : ℓ²(ℕ, ℝ)) : Discrete.Kernel := fun j => x j

structure DifferenceProjectionIsotropicWhite
    {Ω : Type*} [MeasurableSpace Ω]
    (r : ℤ → Ω → ℝ) (μ : Measure Ω) (σr mr : ℝ) : Prop where
  scale_pos : 0 < σr
  absScale_pos : 0 < mr
  coordinate_memLp : ∀ t, MemLp (r t) 2 μ
  coordinate_integral : ∀ t, ∫ ω, r t ω ∂μ = 0
  projection_secondMoment : ∀ N w t,
    ∫ ω, (finiteSignal N w r t ω)^2 ∂μ = σr^2 * finiteSquareEnergy N w
  difference_projection_integral_abs : ∀ (N : ℕ) (w : Discrete.Kernel) (t : ℤ),
    (∀ j, N ≤ j → w j = 0) →
    ∫ ω, |finiteSignal (N+1) (Discrete.difference w) r t ω| ∂μ =
      mr * Real.sqrt (finiteDifferenceEnergy N w)

private theorem finiteEnergy_sub_eq_norm_sq {P : ℕ} (x y : ℓ²(ℕ, ℝ))
    (hx : ∀ j, P ≤ j → x j = 0) (hy : ∀ j, P ≤ j → y j = 0) :
    finiteSquareEnergy P (privateKernelOfLp x - privateKernelOfLp y) = ‖x - y‖ ^ 2 := by
  have hxy : ∀ j, P ≤ j → (x - y) j = 0 := by
    intro j hj
    simp [hx j hj, hy j hj]
  change (∑ j ∈ Finset.range P, ((x - y) j) ^ 2) = ‖x - y‖ ^ 2
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  rw [tsum_eq_sum (s := Finset.range P)]
  · simp only [Real.norm_eq_abs]
    norm_num [ENNReal.toReal_ofNat]
    have hs : 0 ≤ ∑ x_1 ∈ Finset.range P, (x x_1 - y x_1) ^ 2 :=
      Finset.sum_nonneg (fun j hj => sq_nonneg _)
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hs]
  · intro j hj
    have hj' : P ≤ j := by simpa [Finset.mem_range] using hj
    simp [hxy j hj']

private theorem dp_abs_integral_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun ω => |f ω|) μ)
    (hg : Integrable (fun ω => |g ω|) μ)
    (hfg : Integrable (fun ω => |f ω - g ω|) μ) :
    |∫ ω, |f ω| ∂μ - ∫ ω, |g ω| ∂μ| ≤ ∫ ω, |f ω - g ω| ∂μ := by
  have hdiff : Integrable (fun ω => |f ω| - |g ω|) μ := hf.sub hg
  have hnorm := norm_integral_le_integral_norm (μ := μ)
    (fun ω => |f ω| - |g ω|)
  have hi : (∫ ω, |f ω| - |g ω| ∂μ) =
      ∫ ω, |f ω| ∂μ - ∫ ω, |g ω| ∂μ := integral_sub hf hg
  rw [hi] at hnorm
  have hnorm' : Integrable (fun ω => ‖|f ω| - |g ω|‖) μ := hdiff.norm
  calc
    _ = ‖∫ ω, |f ω| ∂μ - ∫ ω, |g ω| ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖|f ω| - |g ω|‖ ∂μ := hnorm
    _ ≤ _ := by
      have hm := integral_mono hnorm' hfg.norm (fun ω => by
        simpa only [Real.norm_eq_abs, abs_abs] using
          (abs_abs_sub_abs_le_abs_sub (f ω) (g ω)))
      simpa only [Real.norm_eq_abs, abs_abs] using hm

private theorem dp_integral_abs_le_sqrt_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (show MemLp |f| (ENNReal.ofReal (2 : ℝ)) μ by simpa using hf.abs)
    (show MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ by
      simpa using (memLp_const (μ := μ) (p := (2 : ENNReal)) (1 : ℝ)))
  rw [Real.sqrt_eq_rpow]
  convert h using 1 <;> simp [sq]

private theorem DifferenceProjectionIsotropicWhite.finiteSignal_abs_lipschitz_lp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {σr mr : ℝ}
    [IsProbabilityMeasure μ]
    (h : DifferenceProjectionIsotropicWhite r μ σr mr)
    (P : ℕ) (x y : ℓ²(ℕ,ℝ))
    (hx : ∀ j, P ≤ j → x j = 0)
    (hy : ∀ j, P ≤ j → y j = 0)
    (t : ℤ) :
    |∫ ω, |finiteSignal P (privateKernelOfLp x) r t ω| ∂μ -
      ∫ ω, |finiteSignal P (privateKernelOfLp y) r t ω| ∂μ| ≤
      σr * dist x y := by
  have hmem (w : Discrete.Kernel) : MemLp (finiteSignal P w r t) 2 μ := by
    unfold finiteSignal
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum' (Finset.range P)
        (f := fun j ω => w j * r (t - (j : ℤ)) ω)
        (fun j hj => (h.coordinate_memLp (t - (j : ℤ))).const_mul (w j)))
  have hia : Integrable (fun ω => |finiteSignal P (privateKernelOfLp x) r t ω|) μ :=
    ((hmem _).integrable one_le_two).norm
  have hib : Integrable (fun ω => |finiteSignal P (privateKernelOfLp y) r t ω|) μ :=
    ((hmem _).integrable one_le_two).norm
  have hfg : Integrable (fun ω =>
      |finiteSignal P (privateKernelOfLp x) r t ω -
        finiteSignal P (privateKernelOfLp y) r t ω|) μ :=
    (((hmem _).sub (hmem _)).integrable one_le_two).norm
  have hh := dp_abs_integral_sub_le hia hib hfg
  have heq : (fun ω => finiteSignal P (privateKernelOfLp x) r t ω -
      finiteSignal P (privateKernelOfLp y) r t ω) =
      finiteSignal P (privateKernelOfLp x - privateKernelOfLp y) r t := by
    funext ω
    simp only [finiteSignal, sub_eq_add_neg, Finset.sum_apply]
    change (∑ j ∈ Finset.range P, x j * r (t - (j : ℤ)) ω) -
      (∑ j ∈ Finset.range P, y j * r (t - (j : ℤ)) ω) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    change x j * r (t - (j : ℤ)) ω - y j * r (t - (j : ℤ)) ω =
      (x j - y j) * r (t - (j : ℤ)) ω
    ring
  calc
    _ ≤ ∫ ω, |finiteSignal P (privateKernelOfLp x) r t ω -
        finiteSignal P (privateKernelOfLp y) r t ω| ∂μ := hh
    _ = ∫ ω, |finiteSignal P (privateKernelOfLp x - privateKernelOfLp y) r t ω| ∂μ := by
      congr 1
      funext ω
      exact congrArg abs (congrFun heq ω)
    _ ≤ σr * Real.sqrt (finiteSquareEnergy P
        (privateKernelOfLp x - privateKernelOfLp y)) := by
      have hs := dp_integral_abs_le_sqrt_sq
        (f := finiteSignal P (privateKernelOfLp x - privateKernelOfLp y) r t)
        (hmem (privateKernelOfLp x - privateKernelOfLp y))
      rw [h.projection_secondMoment P (privateKernelOfLp x - privateKernelOfLp y) t] at hs
      rw [Real.sqrt_mul (sq_nonneg σr)] at hs
      rw [show Real.sqrt (σr ^ 2) = σr by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos h.scale_pos]] at hs
      exact hs
    _ = σr * dist x y := by
      rw [finiteEnergy_sub_eq_norm_sq x y hx hy]
      rw [Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

private def privateFinitePrefixLp (N : ℕ) (w : Discrete.Kernel) : ℓ²(ℕ, ℝ) :=
  ∑ j ∈ Finset.range N, lp.single 2 j (w j)

private theorem privateFinitePrefixLp_apply (N : ℕ) (w : Discrete.Kernel) (j : ℕ) :
    privateFinitePrefixLp N w j = if j < N then w j else 0 := by
  classical
  simp only [privateFinitePrefixLp, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]
  simp [Finset.mem_range]

private theorem privateFinitePrefixLp_apply_of_lt (N : ℕ) (w : Discrete.Kernel) {j : ℕ}
    (hj : j < N) : privateFinitePrefixLp N w j = w j := by
  rw [privateFinitePrefixLp_apply]
  simp [hj]

private theorem privateFinitePrefixLp_apply_of_le (N : ℕ) (w : Discrete.Kernel) {j : ℕ}
    (hj : N ≤ j) : privateFinitePrefixLp N w j = 0 := by
  rw [privateFinitePrefixLp_apply]
  simp [Nat.not_lt.mpr hj]

omit [MeasurableSpace Ω] in
private theorem finiteSignal_eq_of_eq_on_range {N P : ℕ} (_hNP : N ≤ P)
     {a b : Discrete.Kernel} {r : ℤ → Ω → ℝ} (t : ℤ)
    (h : ∀ j, j < N → a j = b j) :
    finiteSignal N a r t = finiteSignal N b r t := by
  funext ω
  simp only [finiteSignal, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

omit [MeasurableSpace Ω] in
private theorem finiteSignal_padding {N P : ℕ} (hNP : N ≤ P) {a : Discrete.Kernel}
    (htail : ∀ j, N ≤ j → a j = 0) {r : ℤ → Ω → ℝ} (t : ℤ) :
    finiteSignal P a r t = finiteSignal N a r t := by
  funext ω
  simp only [finiteSignal, Finset.sum_apply]
  rw [← Finset.sum_subset (Finset.range_mono hNP)]
  intro j hjP hjN
  have hj : N ≤ j := by simpa [Finset.mem_range] using hjN
  simp [htail j hj]

private theorem finiteSquareEnergy_padding {N P : ℕ} (hNP : N ≤ P) {a : Discrete.Kernel}
    (htail : ∀ j, N ≤ j → a j = 0) :
    finiteSquareEnergy P a = finiteSquareEnergy N a := by
  unfold finiteSquareEnergy
  rw [← Finset.sum_subset (Finset.range_mono hNP)]
  intro j hjP hjN
  have hj : N ≤ j := by simpa [Finset.mem_range] using hjN
  simp [htail j hj]

omit [MeasurableSpace Ω] in
private theorem finitePrefix_padding_signal {N P : ℕ} (hNP : N ≤ P)
    (w : Discrete.Kernel) {r : ℤ → Ω → ℝ} (t : ℤ) :
    finiteSignal P (privateKernelOfLp (privateFinitePrefixLp N w)) r t =
      finiteSignal N w r t := by
  change finiteSignal P (fun j => privateFinitePrefixLp N w j) r t = _
  rw [finiteSignal_padding hNP
    (fun j hj => privateFinitePrefixLp_apply_of_le N w hj)]
  apply finiteSignal_eq_of_eq_on_range hNP t
  intro j hj
  rw [privateFinitePrefixLp_apply_of_lt N w hj]

private theorem finitePrefix_padding_energy {N P : ℕ} (hNP : N ≤ P)
    (w : Discrete.Kernel) :
    finiteSquareEnergy P (privateKernelOfLp (privateFinitePrefixLp N w)) =
      finiteSquareEnergy N w := by
  change finiteSquareEnergy P (fun j => privateFinitePrefixLp N w j) = _
  rw [finiteSquareEnergy_padding hNP
    (fun j hj => privateFinitePrefixLp_apply_of_le N w hj)]
  apply Finset.sum_congr rfl
  intro j hj
  change privateFinitePrefixLp N w j ^ 2 = w j ^ 2
  rw [privateFinitePrefixLp_apply_of_lt N w (Finset.mem_range.mp hj)]

private theorem dp_prefix_eq_of_support {K : ℕ} (y : ℓ²(ℕ, ℝ))
    (hy : ∀ j, K ≤ j → y j = 0) :
    privateFinitePrefixLp K (privateKernelOfLp y) = y := by
  ext j
  rw [privateFinitePrefixLp_apply]
  by_cases hj : j < K
  · simp [hj, privateKernelOfLp]
  · have hKj : K ≤ j := Nat.le_of_not_gt hj
    simp [hj, hy j hKj]

private theorem dp_prefix_sqrt_energy_eq_norm {K : ℕ} (y : ℓ²(ℕ, ℝ))
    (hy : ∀ j, K ≤ j → y j = 0) :
    Real.sqrt (finiteSquareEnergy K (privateKernelOfLp y)) = ‖y‖ := by
  have hnorm : ‖privateFinitePrefixLp K (privateKernelOfLp y)‖ ^ (2 : ℝ) =
      finiteSquareEnergy K (privateKernelOfLp y) := by
    simpa [privateFinitePrefixLp, finiteSquareEnergy, privateKernelOfLp,
      Real.norm_eq_abs, sq_abs] using
      (lp.norm_sum_single (p := (2 : ENNReal)) (by norm_num)
        (fun j => y j) (Finset.range K))
  rw [← hnorm]
  rw [dp_prefix_eq_of_support y hy]
  simpa only [Real.rpow_two] using Real.sqrt_sq (norm_nonneg y)

private theorem dp_zeroSum_projection_integral_abs_of_support
    {Ω : Type*} [MeasurableSpace Ω] {r : ℤ → Ω → ℝ}
    {μ : Measure Ω} {σr mr : ℝ}
    (h : DifferenceProjectionIsotropicWhite r μ σr mr)
    (y : ℓ²(ℕ, ℝ)) (K P : ℕ)
    (hytail : ∀ j, K ≤ j → y j = 0)
    (hysum : ∑ j ∈ Finset.range K, y j = 0)
    (hKP : K ≤ P) (t : ℤ) :
    ∫ ω, |finiteSignal P (privateKernelOfLp y) r t ω| ∂μ = mr * ‖y‖ := by
  by_cases hK : K = 0
  · subst K
    have hyzero : y = 0 := by
      ext j
      simp [hytail j (Nat.zero_le j)]
    subst y
    simp [privateKernelOfLp, finiteSignal]
  · obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := by
      exact ⟨K - 1, by omega⟩
    obtain ⟨v, hvtail, hvdiff⟩ :=
      (exists_cutoff_difference_iff_zero_sum (privateKernelOfLp y) N
        (by intro j hj; exact hytail j (by omega))).2 (by
          simpa [privateKernelOfLp] using hysum)
    have hmain := h.difference_projection_integral_abs N v t hvtail
    have hsignal : finiteSignal (N + 1) (Discrete.difference v) r t =
        finiteSignal (N + 1) (privateKernelOfLp y) r t := by
      rw [hvdiff]
    have hpad : finiteSignal P (privateKernelOfLp y) r t =
        finiteSignal (N + 1) (privateKernelOfLp y) r t :=
      finiteSignal_padding hKP hytail t
    change (∫ ω, (|finiteSignal P (privateKernelOfLp y) r t|) ω ∂μ) = _
    rw [hpad]
    have hsignal' : (fun ω => |finiteSignal (N + 1) (privateKernelOfLp y) r t ω|) =
      (fun ω => |finiteSignal (N + 1) (Discrete.difference v) r t ω|) := by
        funext ω
        rw [congrFun hsignal ω]
    change (∫ ω, |finiteSignal (N + 1) (privateKernelOfLp y) r t ω| ∂μ) = _
    rw [hsignal']
    rw [hmain]
    have henergy : finiteDifferenceEnergy N v =
        finiteSquareEnergy (N + 1) (privateKernelOfLp y) := by
      simp only [finiteDifferenceEnergy]
      rw [hvdiff]
      rfl
    rw [henergy, dp_prefix_sqrt_energy_eq_norm y hytail]

private theorem dp_common_horizon_estimates
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {σr mr : ℝ} [IsProbabilityMeasure μ]
    (h : DifferenceProjectionIsotropicWhite r μ σr mr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℓ²(ℕ, ℝ), ∃ K P : ℕ, ∃ x : ℓ²(ℕ, ℝ),
      x = privateFinitePrefixLp N w ∧
      (∀ j, K ≤ j → (privateKernelOfLp y) j = 0) ∧
      (∑ j ∈ Finset.range K, y j = 0) ∧ N ≤ P ∧ K ≤ P ∧
      dist y x < ε / (σr + mr + 1) ∧
      finiteSignal N w r t =
        finiteSignal P (privateKernelOfLp x) r t ∧
      (∫ ω, |finiteSignal P (privateKernelOfLp y) r t ω| ∂μ = mr * ‖y‖) ∧
      |∫ ω, |finiteSignal P (privateKernelOfLp x) r t ω| ∂μ -
          ∫ ω, |finiteSignal P (privateKernelOfLp y) r t ω| ∂μ| ≤
        σr * dist x y ∧
      |mr * ‖x‖ - mr * ‖y‖| ≤ mr * dist x y := by
  have hden : 0 < σr + mr + 1 := by linarith [h.scale_pos, h.absScale_pos]
  obtain ⟨y, hy, hyd⟩ := dp_exists_finiteZeroSum_dist_lt
    (privateFinitePrefixLp N w) (div_pos hε hden)
  obtain ⟨K, hytail, hysum⟩ := hy
  let P := max N K
  have hNP : N ≤ P := Nat.le_max_left _ _
  have hKP : K ≤ P := Nat.le_max_right _ _
  have htail : ∀ j, K ≤ j → (privateKernelOfLp y) j = 0 := by
    intro j hj
    exact hytail j hj
  refine ⟨y, K, P, privateFinitePrefixLp N w, rfl, htail, hysum, hNP, hKP, hyd, ?_, ?_, ?_, ?_⟩
  · exact (finitePrefix_padding_signal hNP w t).symm
  · exact dp_zeroSum_projection_integral_abs_of_support h y K P hytail hysum hKP t
  · exact h.finiteSignal_abs_lipschitz_lp P
      (privateFinitePrefixLp N w) y
      (fun j hj => privateFinitePrefixLp_apply_of_le N w (le_trans hNP hj))
      (fun j hj => htail j (le_trans hKP hj)) t
  · calc
      |mr * ‖privateFinitePrefixLp N w‖ - mr * ‖y‖| =
          |mr * (‖privateFinitePrefixLp N w‖ - ‖y‖)| := by rw [mul_sub]
      _ = mr * |‖privateFinitePrefixLp N w‖ - ‖y‖| := by
        rw [abs_mul, abs_of_pos h.absScale_pos]
      _ ≤ mr * dist (privateFinitePrefixLp N w) y :=
        mul_le_mul_of_nonneg_left
          (show |‖privateFinitePrefixLp N w‖ - ‖y‖| ≤
            dist (privateFinitePrefixLp N w) y by
              simpa only [dist_eq_norm] using (abs_norm_sub_norm_le _ _))
          h.absScale_pos.le

theorem DifferenceProjectionIsotropicWhite.projection_integral_abs_of_difference
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {σr mr : ℝ}
    [IsProbabilityMeasure μ]
    (h : DifferenceProjectionIsotropicWhite r μ σr mr)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    ∫ ω, |finiteSignal N w r t ω| ∂μ =
      mr * Real.sqrt (finiteSquareEnergy N w) := by
  by_contra hne
  let x : ℓ²(ℕ, ℝ) := privateFinitePrefixLp N w
  let A : ℝ := ∫ ω, |finiteSignal N w r t ω| ∂μ
  let B : ℝ := mr * ‖x‖
  have hAB : A ≠ B := by
    intro hab
    apply hne
    dsimp [A, B, x] at hab ⊢
    have hxnorm : ‖privateFinitePrefixLp N w‖ ^ (2 : ℝ) = finiteSquareEnergy N w := by
      simpa [privateFinitePrefixLp, finiteSquareEnergy, Real.norm_eq_abs, sq_abs] using
        (lp.norm_sum_single (p := (2 : ENNReal)) (by norm_num)
          (fun j => w j) (Finset.range N))
    rw [← hxnorm]
    simpa using hab
  have hε : 0 < |A - B| := (abs_pos).2 (sub_ne_zero.mpr hAB)
  obtain ⟨y, K, P, x', hx', hytail, hysum, hNP, hKP, hdist,
      hsignal, hyint, hlip, hnorm⟩ :=
    dp_common_horizon_estimates h N w t hε
  have hxdist : dist x' y = dist y x' := dist_comm _ _
  have hAC : |A - mr * ‖y‖| ≤ σr * dist x' y := by
    dsimp [A]
    rw [hsignal]
    rw [hyint] at hlip
    exact hlip
  have hCB : |mr * ‖y‖ - B| ≤ mr * dist x' y := by
    dsimp [B]
    have hnorm' : |mr * ‖x‖ - mr * ‖y‖| ≤ mr * dist x' y := by
      simpa [hx'] using hnorm
    simpa [abs_sub_comm] using hnorm'
  have htri : |A - B| ≤ |A - mr * ‖y‖| + |mr * ‖y‖ - B| := by
    calc
       |A - B| = |(A - mr * ‖y‖) + (mr * ‖y‖ - B)| := by congr 1; ring
      _ ≤ |A - mr * ‖y‖| + |mr * ‖y‖ - B| := by
        simpa only [Real.norm_eq_abs] using
          (norm_add_le (A - mr * ‖y‖) (mr * ‖y‖ - B))
  have hupper : |A - B| ≤ (σr + mr) * dist x' y := by
    calc
      |A - B| ≤ |A - mr * ‖y‖| + |mr * ‖y‖ - B| := htri
      _ ≤ σr * dist x' y + mr * dist x' y := add_le_add hAC hCB
      _ = (σr + mr) * dist x' y := by ring
  have hscale : 0 < σr + mr := by linarith [h.scale_pos, h.absScale_pos]
  have hstrict : (σr + mr) * dist x' y < |A - B| := by
    have hden : 0 < σr + mr + 1 := by linarith
    have hfrac : (σr + mr) * (|A - B| / (σr + mr + 1)) < |A - B| := by
      field_simp
      nlinarith [hε]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_of_lt (by simpa [dist_comm] using hdist))
        (le_of_lt hscale)) hfrac
  exact (not_lt_of_ge hupper) hstrict

theorem turnoverIsotropicWhite_of_difference_projection
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : ℤ → Ω → ℝ} {σr mr : ℝ}
    [IsProbabilityMeasure μ]
    (h : DifferenceProjectionIsotropicWhite r μ σr mr) :
    TurnoverIsotropicWhite r μ σr mr := by
  refine
    { scale_pos := h.scale_pos
      absScale_pos := h.absScale_pos
      coordinate_memLp := h.coordinate_memLp
      coordinate_integral := h.coordinate_integral
      projection_secondMoment := h.projection_secondMoment
      projection_integral_abs := ?_ }
  intro N w t
  exact h.projection_integral_abs_of_difference N w t

end RayleighKernel.Probability
