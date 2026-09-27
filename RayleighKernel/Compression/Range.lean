import RayleighKernel.Compression.ImageIntervals

noncomputable section

namespace RayleighKernel

open Set MeasureTheory

namespace Analysis.HalfLineH1

theorem compressionMap_eq_measureReal_inter_Ioc (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    f.compressionMap x = volume.real (f.positivitySet ∩ Ioc 0 x) := by
  rw [f.compressionMap_eq_intervalIntegral, intervalIntegral.integral_of_le hx]
  change (∫ t in Ioc 0 x, f.positivitySet.indicator (fun _ ↦ (1 : ℝ)) t) = _
  rw [setIntegral_indicator f.isOpen_positivitySet.measurableSet]
  simp only [setIntegral_one_eq_measureReal]
  congr 1
  ext t
  simp [and_comm]

lemma compressionMap_abs_sub_le_of_le
    (f : HalfLineH1) {x y : ℝ} (hxy : x ≤ y) :
    |f.compressionMap y - f.compressionMap x| ≤ |y - x| := by
  have hsub := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_openSetIndicator f.isOpen_positivitySet 0 y)
    (intervalIntegrable_openSetIndicator f.isOpen_positivitySet 0 x)
  have hupper :
      (∫ t in x..y, openSetIndicator f.positivitySet t) ≤
        ∫ _t in x..y, (1 : ℝ) := intervalIntegral.integral_mono_on hxy
    (intervalIntegrable_openSetIndicator f.isOpen_positivitySet x y)
    intervalIntegrable_const (fun t _ ↦ by
      by_cases h : t ∈ f.positivitySet <;> simp [openSetIndicator, h])
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) hxy (fun t ↦ by
    simpa [openSetIndicator] using
      (Set.indicator_nonneg (s := f.positivitySet)
        (f := fun _ : ℝ ↦ (1 : ℝ)) (fun _ _ ↦ by norm_num) t))
  rw [f.compressionMap_eq_intervalIntegral, f.compressionMap_eq_intervalIntegral]
  have hdiff : (∫ t in (0 : ℝ)..y, openSetIndicator f.positivitySet t) -
      ∫ t in (0 : ℝ)..x, openSetIndicator f.positivitySet t =
      ∫ t in x..y, openSetIndicator f.positivitySet t := hsub
  rw [hdiff, abs_of_nonneg (by
    exact intervalIntegral.integral_nonneg_of_forall hxy (fun t ↦ by
      simpa [openSetIndicator] using
        (Set.indicator_nonneg (s := f.positivitySet)
          (f := fun _ : ℝ ↦ (1 : ℝ)) (fun _ _ ↦ by norm_num) t)))]
  have habs : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
  simpa [intervalIntegral.integral_const, smul_eq_mul, habs] using hupper

lemma compressionMap_abs_sub_le (f : HalfLineH1) (x y : ℝ) :
    |f.compressionMap y - f.compressionMap x| ≤ |y - x| := by
  rcases le_total x y with hxy | hyx
  · exact compressionMap_abs_sub_le_of_le f hxy
  · have h := compressionMap_abs_sub_le_of_le f hyx
    simpa [abs_sub_comm] using h

theorem compressionMap_lipschitzWith (f : HalfLineH1) :
    LipschitzWith 1 f.compressionMap := by
  apply LipschitzWith.of_edist_le
  intro x y
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  simpa [edist_dist, Real.dist_eq, abs_sub_comm] using
    ENNReal.ofReal_le_ofReal (compressionMap_abs_sub_le f x y)

end Analysis.HalfLineH1

def compressionTarget (f : Analysis.HalfLineH1) : Set ℝ :=
  {y | 0 < y ∧ ENNReal.ofReal y < volume f.positivitySet}

namespace Analysis.HalfLineH1

private lemma positivitySet_subset_Ioi (f : HalfLineH1) :
    f.positivitySet ⊆ Ioi 0 := by
  intro z hz
  exact lt_of_not_ge fun hz0 ↦ hz.ne'
    (f.continuousRep_eq_zero_of_nonpositive hz0)

theorem exists_compressionMap_gt_of_mem_compressionTarget
    (f : HalfLineH1) {y : ℝ} (hy : y ∈ compressionTarget f) :
    ∃ x > 0, y < f.compressionMap x := by
  by_contra h
  push Not at h
  let s : ℕ → Set ℝ := fun n ↦ f.positivitySet ∩ Ioc 0 (n + 1 : ℝ)
  have hsmono : Monotone s := by
    intro m n hmn z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    exact hz.2.2.trans (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hsunion : (⋃ n : ℕ, s n) = f.positivitySet := by
    ext z
    constructor
    · rintro hz
      rcases mem_iUnion.mp hz with ⟨n, hn⟩
      exact hn.1
    · intro hzP
      have hz0 : 0 < z := positivitySet_subset_Ioi f hzP
      obtain ⟨N : ℕ, hN⟩ := exists_nat_ge z
      refine mem_iUnion.mpr ⟨N, hzP, hz0, ?_⟩
      exact hN.trans (by exact_mod_cast Nat.le_add_right N 1)
  have hmeasure : volume f.positivitySet ≤ ENNReal.ofReal y := by
    rw [← hsunion, hsmono.measure_iUnion]
    refine iSup_le fun n ↦ ?_
    have hfin : volume (s n) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (measure_Ioc_lt_top.ne) (measure_mono inter_subset_right)
    have hreal := h ((n + 1 : ℕ) : ℝ) (by positivity : 0 < ((n + 1 : ℕ) : ℝ))
    rw [f.compressionMap_eq_measureReal_inter_Ioc (by positivity)] at hreal
    have hreal' : volume.real (s n) ≤ y := by
      simpa [s] using hreal
    rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal hreal'
  exact (not_lt_of_ge hmeasure) hy.2

/-- Every point of the target interval is attained by the cumulative compression map
at a strictly positive point. -/
theorem compressionTarget_subset_range_Ioi (f : HalfLineH1) :
    compressionTarget f ⊆ f.compressionMap '' Ioi 0 := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := f.exists_compressionMap_gt_of_mem_compressionTarget hy
  have hcont : ContinuousOn f.compressionMap (Icc 0 x) := by
    simpa [uIcc_of_le hx.le] using f.compressionMap_continuousOn 0 x
  obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hx.le hcont
    ⟨by rw [f.compressionMap_eq_zero_of_nonpositive le_rfl]; exact hy.1.le,
      hxy.le⟩
  rcases hzy with ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  by_contra hz0
  have hzle : z ≤ 0 := le_of_not_gt hz0
  have hzero := f.compressionMap_eq_zero_of_nonpositive hzle
  linarith [hy.1]

end Analysis.HalfLineH1

end RayleighKernel
