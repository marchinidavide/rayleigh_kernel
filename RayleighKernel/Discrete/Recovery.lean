import RayleighKernel.Discrete.CorrectionEnergy

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open scoped BigOperators
open RayleighKernel.Analysis.HalfLineH1

private lemma finiteWeightedYoung {x y h : ℝ} (hh : 0 < h) :
    h^2 * |(x+y)^2-x^2| ≤ h^4*x^2 + (h^2+1)*y^2 := by
  have hexpand : |(x + y)^2 - x^2| ≤ 2 * |x * y| + y^2 := by
    rw [show (x + y)^2 - x^2 = 2 * (x * y) + y^2 by ring]
    calc
      |2 * (x * y) + y^2| ≤ |2 * (x * y)| + |y^2| := abs_add_le _ _
      _ = 2 * |x * y| + y^2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
        ring
  have hyoung : 2 * h^2 * |x * y| ≤ h^4 * x^2 + y^2 := by
    have hs := sq_nonneg (h^2 * |x| - |y|)
    have hid : (h^2 * abs x - abs y)^2 = h^4*x^2 - 2*h^2*|x*y| + y^2 := by
      calc
        (h^2 * abs x - abs y)^2 = h^4 * (abs x)^2 - 2*h^2*abs x*abs y + (abs y)^2 := by ring
        _ = h^4*x^2 - 2*h^2*|x*y| + y^2 := by
          rw [sq_abs x, sq_abs y, abs_mul x y]
          ring
    rw [hid] at hs
    nlinarith
  calc
    h^2 * |(x+y)^2-x^2| ≤ h^2 * (2 * |x*y| + y^2) :=
      mul_le_mul_of_nonneg_left hexpand (by positivity)
    _ = 2 * h^2 * |x*y| + h^2*y^2 := by ring
    _ ≤ (h^4*x^2 + y^2) + h^2*y^2 := by nlinarith [hyoung]
    _ = h^4*x^2 + (h^2+1)*y^2 := by ring

private theorem squareEnergyEqSumRangeOfTail {w : Kernel} {N : ℕ}
    (htail : ∀ j, N < j → w j=0) :
    squareEnergy w = ∑ j ∈ Finset.range (N+1), (w j)^2 := by
  rw [squareEnergy]
  apply tsum_eq_sum (s := Finset.range (N+1))
  intro j hj
  rw [htail j (Nat.lt_of_not_ge (by simpa using hj))]
  simp

private theorem differenceEnergyEqSumRangeOfTail {w : Kernel} {N : ℕ}
    (htail : ∀ j, N < j → w j=0) :
    differenceEnergy w = ∑ j ∈ Finset.range (N+2), (difference w j)^2 := by
  rw [differenceEnergy]
  apply tsum_eq_sum (s := Finset.range (N+2))
  intro j hj
  cases j with
  | zero => exact False.elim (hj (by simp))
  | succ k =>
    have hk : N < k := by
      have hk' : N + 2 ≤ k + 1 := Nat.succ_le_iff.mpr (by simpa using hj)
      omega
    rw [difference_succ, htail (k+1) (by omega), htail k hk]
    simp

private theorem finiteWeightedSquarePerturbation
    {u c : Kernel} {N : ℕ} {h : ℝ} (hh : 0 < h)
    (hu : ∀ j, N < j → u j = 0) (hc : ∀ j, N < j → c j = 0) :
    h^2 * |squareEnergy (fun j => u j + c j) - squareEnergy u| ≤
      h^4 * squareEnergy u + (h^2+1) * squareEnergy c := by
  let s : Finset ℕ := Finset.range (N+1)
  have hsum : squareEnergy (fun j => u j + c j) - squareEnergy u =
      ∑ j ∈ s, ((u j + c j)^2 - (u j)^2) := by
    rw [squareEnergyEqSumRangeOfTail (fun j hj => by simp [hu j hj, hc j hj]),
      squareEnergyEqSumRangeOfTail hu]
    simp only [s]
    rw [Finset.sum_sub_distrib]
  have hbound : ∀ j ∈ s,
      h^2 * |(u j + c j)^2 - (u j)^2| ≤ h^4*(u j)^2 + (h^2+1)*(c j)^2 := by
    intro j hj
    exact finiteWeightedYoung hh
  have habs : h^2 * |∑ j ∈ s, ((u j + c j)^2 - (u j)^2)| ≤
      ∑ j ∈ s, h^2 * |(u j + c j)^2 - (u j)^2| := by
    calc
      h^2 * |∑ j ∈ s, ((u j + c j)^2 - (u j)^2)| ≤
          h^2 * ∑ j ∈ s, |(u j + c j)^2 - (u j)^2| :=
        mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ = ∑ j ∈ s, h^2 * |(u j + c j)^2 - (u j)^2| := by
        rw [Finset.mul_sum]
  have hterm : (∑ j ∈ s, h^2 * |(u j + c j)^2 - (u j)^2|) ≤
      ∑ j ∈ s, (h^4*(u j)^2 + (h^2+1)*(c j)^2) :=
    Finset.sum_le_sum (fun j hj => hbound j hj)
  rw [hsum]
  calc
    h^2 * |∑ j ∈ s, ((u j + c j)^2 - (u j)^2)| ≤
        ∑ j ∈ s, h^2 * |(u j + c j)^2 - (u j)^2| := habs
    _ ≤ ∑ j ∈ s, (h^4*(u j)^2 + (h^2+1)*(c j)^2) := hterm
    _ = h^4 * squareEnergy u + (h^2+1) * squareEnergy c := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.mul_sum, squareEnergyEqSumRangeOfTail hu]
      · rw [← Finset.mul_sum, squareEnergyEqSumRangeOfTail hc]

private theorem differenceAddLinearFinite (u c : Kernel) :
    difference (fun j => u j + c j) = fun j => difference u j + difference c j := by
  funext j
  cases j with
  | zero => simp [difference]
  | succ j => simp [difference]; ring

private theorem finiteWeightedDifferencePerturbation
    {u c : Kernel} {N : ℕ} {h : ℝ} (hh : 0 < h)
    (hu : ∀ j, N < j → u j = 0) (hc : ∀ j, N < j → c j = 0) :
    h^2 * |differenceEnergy (fun j => u j + c j) - differenceEnergy u| ≤
      h^4 * differenceEnergy u + (h^2+1) * differenceEnergy c := by
  change h^2 * |squareEnergy (difference (fun j => u j + c j)) -
    squareEnergy (difference u)| ≤ _
  rw [differenceAddLinearFinite]
  apply finiteWeightedSquarePerturbation (N := N + 1) hh
  · intro j hj
    cases j with
    | zero => omega
    | succ k =>
      rw [difference_succ, hu (k+1) (by omega), hu k (by omega)]
      simp
  · intro j hj
    cases j with
    | zero => omega
    | succ k =>
      rw [difference_succ, hc (k+1) (by omega), hc k (by omega)]
      simp

private theorem sampledOptimizerTail (L : ℝ) (hL : 0 < L) {h : ℝ} (hh : 0 < h)
    {j : ℕ} (hj : meshCount (optimizerSupport L) h < j) :
    sampledKernel h (optimizerProfile L) j = 0 :=
  sampledKernel_tail hh (optimizerSupport_pos hL).le
    (fun _ hx => optimizerProfile_eq_zero_of_support_le hL hx) hj

private theorem sampledOptimizerSquareUpper (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      squareEnergy (sampledKernel h (optimizerProfile L)) ≤ h * C := by
  obtain ⟨C, hC, hb⟩ := exists_optimizerProfile_squareEnergy_defect_bound hL
  let E := |(optimizer L hL).squareEnergy|
  refine ⟨min 1 (optimizerSupport L), E + C, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (optimizerSupport_pos hL)
  · dsimp [E]
    positivity
  · intro h hh hh₀
    have h1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
    have hK : h ≤ optimizerSupport L := hh₀.trans (min_le_right _ _)
    have hq := (abs_le.mp (hb hh h1 hK)).2
    have hquot : squareEnergy (sampledKernel h (optimizerProfile L)) / h ≤
        (optimizer L hL).squareEnergy + h^2 * C := by nlinarith
    have hmul := (div_le_iff₀ hh).mp hquot
    have hmul' : squareEnergy (sampledKernel h (optimizerProfile L)) ≤
        h * ((optimizer L hL).squareEnergy + h^2 * C) := by simpa [mul_comm] using hmul
    have hh2 : h^2 ≤ 1 := by nlinarith [hh.le, h1]
    have hdef : h^2 * C ≤ C := by simpa using (mul_le_mul_of_nonneg_right hh2 hC)
    have hcoef : (optimizer L hL).squareEnergy + h^2 * C ≤ E + C :=
      add_le_add (le_abs_self _) hdef
    have hfinal := mul_le_mul_of_nonneg_left hcoef hh.le
    dsimp [E] at hfinal ⊢
    exact hmul'.trans hfinal

private theorem sampledOptimizerDifferenceUpper (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      differenceEnergy (sampledKernel h (optimizerProfile L)) ≤ h^3 * C := by
  obtain ⟨C, hC, hb⟩ := exists_optimizerProfile_differenceEnergy_defect_bound hL
  let E := |(optimizer L hL).dirichletEnergy|
  refine ⟨min 1 (optimizerSupport L), E + C, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (optimizerSupport_pos hL)
  · dsimp [E]
    positivity
  · intro h hh hh₀
    have h1 : h ≤ 1 := hh₀.trans (min_le_left _ _)
    have hK : h ≤ optimizerSupport L := hh₀.trans (min_le_right _ _)
    have hq := (abs_le.mp (hb hh h1 hK)).2
    have hquot : differenceEnergy (sampledKernel h (optimizerProfile L)) / h^3 ≤
        (optimizer L hL).dirichletEnergy + h * C := by nlinarith
    have hmul := (div_le_iff₀ (by positivity : 0 < h^3)).mp hquot
    have hmul' : differenceEnergy (sampledKernel h (optimizerProfile L)) ≤
        h^3 * ((optimizer L hL).dirichletEnergy + h * C) := by simpa [mul_comm] using hmul
    have hdef : h * C ≤ C := by simpa using (mul_le_mul_of_nonneg_right h1 hC)
    have hcoef : (optimizer L hL).dirichletEnergy + h * C ≤ E + C :=
      add_le_add (le_abs_self _) hdef
    have hfinal := mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ h^3)
    dsimp [E] at hfinal ⊢
    exact hmul'.trans hfinal

private theorem finiteWeightedSquareTarget (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      h^2 * |squareEnergy (correctedSampledOptimizer L hL h) -
        squareEnergy (sampledKernel h (optimizerProfile L))| ≤ h^5 * C := by
  obtain ⟨hs, Cs, hs0, hCs, hCb⟩ := exists_optimizerSampledCorrection_squareEnergy_bound L hL
  obtain ⟨hu, Cu, hu0, huC, huB⟩ := sampledOptimizerSquareUpper L hL
  refine ⟨min (min hs hu) 1, Cu + 2 * Cs, ?_, by positivity, ?_⟩
  · exact lt_min (lt_min hs0 hu0) (by norm_num)
  intro h hh hh₀
  rw [correctedSampledOptimizer_eq]
  have hhs : h ≤ hs := le_trans hh₀ (min_le_left _ _ |>.trans (min_le_left _ _))
  have hhu : h ≤ hu := le_trans hh₀ (min_le_left _ _ |>.trans (min_le_right _ _))
  have h1 : h ≤ 1 := le_trans hh₀ (min_le_right _ _)
  have huTail : ∀ j, meshCount (optimizerSupport L) h < j →
      sampledKernel h (optimizerProfile L) j = 0 := fun j hj => sampledOptimizerTail L hL hh hj
  have hcTail : ∀ j, meshCount (optimizerSupport L) h < j →
      optimizerSampledCorrection L hL h j = 0 := fun j hj => optimizerSampledCorrection_tail L hL hh hj
  have hmain := finiteWeightedSquarePerturbation hh huTail hcTail
  have hu' := huB hh hhu
  have hc' := hCb hh hhs
  have hplus : h^2 + 1 ≤ 2 := by nlinarith [sq_nonneg h, h1]
  have hbase : h^4 * squareEnergy (sampledKernel h (optimizerProfile L)) ≤ h^4 * (h * Cu) :=
    mul_le_mul_of_nonneg_left hu' (by positivity)
  have hcorr : (h^2 + 1) * squareEnergy (optimizerSampledCorrection L hL h) ≤ 2 * (h^5 * Cs) := by
    have hstep := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ h^2 + 1)
    have hstep' := mul_le_mul_of_nonneg_right hplus (by positivity : 0 ≤ h^5 * Cs)
    exact hstep.trans (hstep'.trans_eq (by ring))
  have hweighted := hmain.trans (add_le_add hbase hcorr)
  convert hweighted using 1 ; ring

private theorem finiteWeightedDifferenceTarget (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      h^2 * |differenceEnergy (correctedSampledOptimizer L hL h) -
        differenceEnergy (sampledKernel h (optimizerProfile L))| ≤ h^7 * C := by
  obtain ⟨hs, Cs, hs0, hCs, hCb⟩ := exists_optimizerSampledCorrection_differenceEnergy_bound L hL
  obtain ⟨hu, Cu, hu0, huC, huB⟩ := sampledOptimizerDifferenceUpper L hL
  refine ⟨min (min hs hu) 1, Cu + 2 * Cs, ?_, by positivity, ?_⟩
  · exact lt_min (lt_min hs0 hu0) (by norm_num)
  intro h hh hh₀
  rw [correctedSampledOptimizer_eq]
  have hhs : h ≤ hs := le_trans hh₀ (min_le_left _ _ |>.trans (min_le_left _ _))
  have hhu : h ≤ hu := le_trans hh₀ (min_le_left _ _ |>.trans (min_le_right _ _))
  have h1 : h ≤ 1 := le_trans hh₀ (min_le_right _ _)
  have huTail : ∀ j : ℕ, meshCount (optimizerSupport L) h < j →
      sampledKernel h (optimizerProfile L) j = 0 := fun j hj => sampledOptimizerTail L hL hh hj
  have hcTail : ∀ j : ℕ, meshCount (optimizerSupport L) h < j →
      optimizerSampledCorrection L hL h j = 0 := fun j hj => optimizerSampledCorrection_tail L hL hh hj
  have hmain := finiteWeightedDifferencePerturbation hh huTail hcTail
  have hu' := huB hh hhu
  have hc' := hCb hh hhs
  have hplus : h^2 + 1 ≤ 2 := by nlinarith [sq_nonneg h, h1]
  have hbase := mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ h^4)
  have hcorr : (h^2 + 1) * differenceEnergy (optimizerSampledCorrection L hL h) ≤ 2 * (h^7 * Cs) := by
    have hstep := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ h^2 + 1)
    have hstep' := mul_le_mul_of_nonneg_right hplus (by positivity : 0 ≤ h^7 * Cs)
    exact hstep.trans (hstep'.trans_eq (by ring))
  have hweighted := hmain.trans (add_le_add hbase hcorr)
  convert hweighted using 1 ; ring

theorem exists_correctedSampledOptimizer_squareEnergy_sub_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      |squareEnergy (correctedSampledOptimizer L hL h) -
        squareEnergy (sampledKernel h (optimizerProfile L))| ≤ h ^ 3 * C := by
  obtain ⟨h₀, C, h₀pos, hC, hb⟩ := finiteWeightedSquareTarget L hL
  refine ⟨h₀, C, h₀pos, hC, ?_⟩
  intro h hh hh₀
  have hsq : 0 < h^2 := sq_pos_of_pos hh
  have hmul : h^2 * |squareEnergy (correctedSampledOptimizer L hL h) -
      squareEnergy (sampledKernel h (optimizerProfile L))| ≤ h^2 * (h^3 * C) := by
    convert hb hh hh₀ using 1 ; ring
  exact le_of_mul_le_mul_left hmul hsq

theorem exists_correctedSampledOptimizer_differenceEnergy_sub_bound (L : ℝ) (hL : 0 < L) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ h₀ →
      |differenceEnergy (correctedSampledOptimizer L hL h) -
        differenceEnergy (sampledKernel h (optimizerProfile L))| ≤ h ^ 5 * C := by
  obtain ⟨h₀, C, h₀pos, hC, hb⟩ := finiteWeightedDifferenceTarget L hL
  refine ⟨h₀, C, h₀pos, hC, ?_⟩
  intro h hh hh₀
  have hsq : 0 < h^2 := sq_pos_of_pos hh
  have hmul : h^2 * |differenceEnergy (correctedSampledOptimizer L hL h) -
      differenceEnergy (sampledKernel h (optimizerProfile L))| ≤ h^2 * (h^5 * C) := by
    convert hb hh hh₀ using 1 ; ring
  exact le_of_mul_le_mul_left hmul hsq

private theorem tendsto_of_abs_le_sq_mul_right
    {F : ℝ → ℝ} {C δ a : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ {h : ℝ}, 0 < h → h ≤ δ →
      |F h - a| ≤ h ^ 2 * C) :
    Tendsto F (𝓝[>] 0) (𝓝 a) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    Ioo_mem_nhdsGT hεC] with h hδ' h1 hε'
  rw [Real.dist_eq]
  have hsq : h ^ 2 ≤ h := by
    nlinarith [mul_nonneg h1.1.le (sub_nonneg.mpr h1.2.le)]
  calc
    |F h - a| ≤ h ^ 2 * C := hbound hδ'.1 hδ'.2.le
    _ ≤ h * C := mul_le_mul_of_nonneg_right hsq hC
    _ < h * (C + 1) := by
      nlinarith [mul_pos hδ'.1 (by norm_num : (0 : ℝ) < 1)]
    _ < ε := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hε'.2

private theorem tendsto_of_abs_le_sq_mul_right_zero
    {F : ℝ → ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ {h : ℝ}, 0 < h → h ≤ δ → |F h| ≤ h ^ 2 * C) :
    Tendsto F (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_abs_le_sq_mul_right (a := 0) hC hδ
  intro h hh hhδ
  simpa using hbound hh hhδ

private theorem tendsto_corrected_squareEnergy_sub_div (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun h : ℝ => (squareEnergy (correctedSampledOptimizer L hL h) -
        squareEnergy (sampledKernel h (optimizerProfile L))) / h)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨h₀, C, h₀pos, hC, hbound⟩ :=
    exists_correctedSampledOptimizer_squareEnergy_sub_bound L hL
  apply tendsto_of_abs_le_sq_mul_right_zero hC h₀pos
  intro h hh hh₀
  rw [abs_div, abs_of_pos hh]
  have hmul := hbound hh hh₀
  apply (div_le_iff₀ hh).2
  nlinarith [hmul]

private theorem tendsto_corrected_differenceEnergy_sub_div (L : ℝ) (hL : 0 < L) :
    Tendsto
      (fun h : ℝ => (differenceEnergy (correctedSampledOptimizer L hL h) -
        differenceEnergy (sampledKernel h (optimizerProfile L))) / h ^ 3)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨h₀, C, h₀pos, hC, hbound⟩ :=
    exists_correctedSampledOptimizer_differenceEnergy_sub_bound L hL
  apply tendsto_of_abs_le_sq_mul_right_zero hC h₀pos
  intro h hh hh₀
  rw [abs_div, abs_of_pos (by positivity : 0 < h ^ 3)]
  have hmul := hbound hh hh₀
  apply (div_le_iff₀ (by positivity : 0 < h ^ 3)).2
  nlinarith [hmul]

theorem tendsto_squareEnergy_correctedSampledOptimizer_div (L : ℝ) (hL : 0 < L) :
    Tendsto (fun h : ℝ => squareEnergy (correctedSampledOptimizer L hL h) / h)
      (𝓝[>] 0) (𝓝 (optimizer L hL).squareEnergy) := by
  have hs := tendsto_squareEnergy_sampledKernel_div hL
  have hd := tendsto_corrected_squareEnergy_sub_div L hL
  have hadd := hs.add hd
  have hadd' : Tendsto
      (fun h : ℝ => squareEnergy (sampledKernel h (optimizerProfile L)) / h +
        (squareEnergy (correctedSampledOptimizer L hL h) -
          squareEnergy (sampledKernel h (optimizerProfile L))) / h)
      (𝓝[>] 0) (𝓝 (optimizer L hL).squareEnergy) := by simpa using hadd
  apply hadd'.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  field_simp [ne_of_gt hh.1]
  ring

theorem tendsto_differenceEnergy_correctedSampledOptimizer_div (L : ℝ) (hL : 0 < L) :
    Tendsto (fun h : ℝ => differenceEnergy (correctedSampledOptimizer L hL h) / h ^ 3)
      (𝓝[>] 0) (𝓝 (optimizer L hL).dirichletEnergy) := by
  have hs := tendsto_differenceEnergy_sampledKernel_div hL
  have hd := tendsto_corrected_differenceEnergy_sub_div L hL
  have hadd := hs.add hd
  have hadd' : Tendsto
      (fun h : ℝ => differenceEnergy (sampledKernel h (optimizerProfile L)) / h ^ 3 +
        (differenceEnergy (correctedSampledOptimizer L hL h) -
          differenceEnergy (sampledKernel h (optimizerProfile L))) / h ^ 3)
      (𝓝[>] 0) (𝓝 (optimizer L hL).dirichletEnergy) := by simpa using hadd
  apply hadd'.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  field_simp [ne_of_gt hh.1]
  ring

theorem tendsto_scaled_rayleighQuotient_correctedSampledOptimizer (L : ℝ) (hL : 0 < L) :
    Tendsto (fun h : ℝ => (h⁻¹)^2 * rayleighQuotient
      (correctedSampledOptimizer L hL h))
      (𝓝[>] 0) (𝓝 (optimizer L hL).rayleighQuotient) := by
  have hnum := tendsto_differenceEnergy_correctedSampledOptimizer_div L hL
  have hden := tendsto_squareEnergy_correctedSampledOptimizer_div L hL
  have hden_pos : 0 < (optimizer L hL).squareEnergy :=
    Analysis.HalfLineH1.squareEnergy_pos_of_mass_eq_one
      (optimizer_isAdmissible hL).mass_eq
  have hquot : Tendsto
      (fun h : ℝ =>
        (differenceEnergy (correctedSampledOptimizer L hL h) / h ^ 3) /
          (squareEnergy (correctedSampledOptimizer L hL h) / h))
      (𝓝[>] 0) (𝓝 ((optimizer L hL).dirichletEnergy /
        (optimizer L hL).squareEnergy)) :=
    hnum.div hden hden_pos.ne'
  have hpos : ∀ᶠ h in 𝓝[>] 0,
      0 < squareEnergy (correctedSampledOptimizer L hL h) / h :=
    hden (Ioi_mem_nhds hden_pos)
  apply hquot.congr'
  filter_upwards [hpos, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh hh1
  have hh0 : h ≠ 0 := ne_of_gt hh1.1
  have hS : squareEnergy (correctedSampledOptimizer L hL h) ≠ 0 := by
    intro hS
    rw [hS, zero_div] at hh
    linarith
  dsimp [rayleighQuotient]
  field_simp [hh0, hS]

theorem exists_discreteRecovery (L : ℝ) (hL : 0 < L) :
    ∃ w : ℝ → Kernel,
      (∀ᶠ h in 𝓝[>] 0, IsAdmissible h L (w h)) ∧
      Tendsto (fun h : ℝ => (h⁻¹)^2 * rayleighQuotient (w h))
        (𝓝[>] 0) (𝓝 (Analysis.Lambda L)) := by
  let w : ℝ → Kernel := fun h => correctedSampledOptimizer L hL h
  refine ⟨w, ?_, ?_⟩
  · obtain ⟨h₀, hh₀, hw⟩ :=
      exists_pos_correctedSampledOptimizer_isAdmissible L hL
    filter_upwards [Ioo_mem_nhdsGT hh₀] with h hh
    exact hw hh.1 hh.2.le
  · have hq := tendsto_scaled_rayleighQuotient_correctedSampledOptimizer L hL
    have heq : (optimizer L hL).rayleighQuotient = Analysis.Lambda L :=
      Analysis.HalfLineH1.rayleighQuotient_eq_Lambda_of_isMinimizer hL
        (Analysis.HalfLineH1.optimizer_isMinimizer hL)
    rw [← heq]
    simpa [w] using hq

def scaledDiscreteMinimum (h L : ℝ) : ℝ :=
  sInf {q : ℝ | ∃ w : Kernel, IsAdmissible h L w ∧
    q = (h⁻¹)^2 * rayleighQuotient w}

theorem scaledDiscreteMinimum_bddBelow (h L : ℝ) :
    BddBelow {q : ℝ | ∃ w : Kernel, IsAdmissible h L w ∧
      q = (h⁻¹)^2 * rayleighQuotient w} := by
  refine ⟨0, ?_⟩
  rintro q ⟨w, hw, rfl⟩
  exact mul_nonneg (sq_nonneg _) hw.rayleighQuotient_nonneg

theorem scaledDiscreteMinimum_le_of_isAdmissible
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    scaledDiscreteMinimum h L ≤ (h⁻¹)^2 * rayleighQuotient w := by
  unfold scaledDiscreteMinimum
  exact csInf_le (scaledDiscreteMinimum_bddBelow h L) ⟨w, hw, rfl⟩

theorem eventually_scaledDiscreteMinimum_le_corrected (L : ℝ) (hL : 0 < L) :
    ∀ᶠ h in 𝓝[>] 0,
      scaledDiscreteMinimum h L ≤
        (h⁻¹)^2 * rayleighQuotient (correctedSampledOptimizer L hL h) := by
  obtain ⟨h₀, hh₀, hvalid⟩ := exists_pos_correctedSampledOptimizer_isAdmissible L hL
  filter_upwards [Ioo_mem_nhdsGT hh₀] with h hh
  exact scaledDiscreteMinimum_le_of_isAdmissible (hvalid hh.1 hh.2.le)

theorem eventually_scaledDiscreteMinimum_le_add (L : ℝ) (hL : 0 < L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] 0,
      scaledDiscreteMinimum h L ≤ (optimizer L hL).rayleighQuotient + ε := by
  have hconv := tendsto_scaled_rayleighQuotient_correctedSampledOptimizer L hL
  have hev : ∀ᶠ h in 𝓝[>] 0,
      (h⁻¹)^2 * rayleighQuotient (correctedSampledOptimizer L hL h) <
        (optimizer L hL).rayleighQuotient + ε :=
    hconv (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  exact (eventually_scaledDiscreteMinimum_le_corrected L hL).and hev |>.mono
    (fun h hh => hh.1.trans (le_of_lt hh.2))

theorem limsup_scaledDiscreteMinimum_le_optimizer (L : ℝ) (hL : 0 < L) :
    limsup (fun h : ℝ => scaledDiscreteMinimum h L) (𝓝[>] 0) ≤
      (optimizer L hL).rayleighQuotient := by
  obtain ⟨h₀, hh₀, hvalid⟩ := exists_pos_correctedSampledOptimizer_isAdmissible L hL
  have hnonneg : ∀ᶠ h in 𝓝[>] 0, 0 ≤ scaledDiscreteMinimum h L := by
    filter_upwards [Ioo_mem_nhdsGT hh₀] with h hh
    apply le_csInf
    · exact ⟨_, correctedSampledOptimizer L hL h, hvalid hh.1 hh.2.le, rfl⟩
    · rintro q ⟨w, hw, rfl⟩
      exact mul_nonneg (sq_nonneg _) hw.rayleighQuotient_nonneg
  apply (Filter.limsup_le_iff (u := fun h : ℝ => scaledDiscreteMinimum h L)
    (x := (optimizer L hL).rayleighQuotient)
    (isCoboundedUnder_le_of_eventually_le _ hnonneg)
    (isBoundedUnder_of_eventually_le
      (eventually_scaledDiscreteMinimum_le_add L hL (by norm_num : (0 : ℝ) < 1)))).2
  intro y hy
  have hε : 0 < y - (optimizer L hL).rayleighQuotient := sub_pos.mpr hy
  have hε' : 0 < (y - (optimizer L hL).rayleighQuotient) / 2 := by positivity
  exact (eventually_scaledDiscreteMinimum_le_add L hL hε').mono
    (fun h hh => by
      have hlt : (optimizer L hL).rayleighQuotient +
          (y - (optimizer L hL).rayleighQuotient) / 2 < y := by linarith
      exact lt_of_le_of_lt hh hlt)

theorem limsup_scaledDiscreteMinimum_le (L : ℝ) (hL : 0 < L) :
    limsup (fun h : ℝ => scaledDiscreteMinimum h L) (𝓝[>] 0) ≤ Analysis.Lambda L := by
  have heq : (optimizer L hL).rayleighQuotient = Analysis.Lambda L :=
    Analysis.HalfLineH1.rayleighQuotient_eq_Lambda_of_isMinimizer hL
      (Analysis.HalfLineH1.optimizer_isMinimizer hL)
  simpa only [heq] using limsup_scaledDiscreteMinimum_le_optimizer L hL
end RayleighKernel.Discrete
