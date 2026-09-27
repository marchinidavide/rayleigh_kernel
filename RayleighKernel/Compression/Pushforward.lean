import RayleighKernel.Compression.Energy

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem translatedComponent_subset_compressionTarget
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    translatedComponent f D n ⊆ compressionTarget f := by
  rintro y ⟨x, hx, hxy⟩
  subst y
  have hypos : 0 < f.compressionMap x :=
    translatedComponent_subset_Ioi_zero f D n ⟨x, hx, rfl⟩
  obtain ⟨u, huSub, huOpen, hxu⟩ := mem_nhds_iff.1 ((D.isOpen_component n).mem_nhds hx)
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 huOpen x hxu
  let z : ℝ := x + δ / 2
  have hz : z ∈ D.component n := huSub (hδC (by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [z]
    rw [abs_of_nonneg (by linarith)]
    linarith))
  have hstrict : f.compressionMap x < f.compressionMap z :=
    compressionMap_strictMono_on_component f D n hx (by dsimp [z]; linarith)
  have hxpos : 0 < x := by
    exact lt_of_not_ge fun hx0 => (D.subset n hx).ne'
      (f.continuousRep_eq_zero_of_nonpositive hx0)
  have hznonneg : 0 ≤ z := by dsimp [z]; linarith
  have hmeasure : volume (f.positivitySet ∩ Ioc 0 z) ≤ volume f.positivitySet :=
    measure_mono inter_subset_left
  have hto : ENNReal.ofReal (f.compressionMap z) = volume (f.positivitySet ∩ Ioc 0 z) := by
    rw [f.compressionMap_eq_measureReal_inter_Ioc hznonneg, measureReal_def]
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono inter_subset_right))
  have hzpos : 0 < f.compressionMap z := lt_trans hypos hstrict
  refine ⟨hypos, ?_⟩
  calc
    ENNReal.ofReal (f.compressionMap x) < ENNReal.ofReal (f.compressionMap z) :=
      (ENNReal.ofReal_lt_ofReal_iff hzpos).2 hstrict
    _ = volume (f.positivitySet ∩ Ioc 0 z) := hto
    _ ≤ volume f.positivitySet := hmeasure

theorem iUnion_translatedComponent_ae_eq_compressionTarget
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) :
    (⋃ n, translatedComponent f D n) =ᵐ[volume] compressionTarget f := by
  apply ae_eq_set.2
  constructor
  · have hsub : (⋃ n, translatedComponent f D n) ⊆ compressionTarget f :=
      iUnion_subset fun n => translatedComponent_subset_compressionTarget f D n
    rw [sdiff_eq_empty.mpr hsub, measure_empty]
  · exact f.compressionTarget_diff_iUnion_translatedComponent_measure_zero D

theorem lintegral_translatedComponent
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (φ : ℝ → ℝ≥0∞) :
    (∫⁻ y in translatedComponent f D n, φ y) =
      ∫⁻ x in D.component n, φ (f.compressionMap x) := by
  let s : ℝ := componentGap f D n
  let H : ℝ → ℝ≥0∞ := (D.component n).indicator (fun x => φ (f.compressionMap x))
  have hpoint : (translatedComponent f D n).indicator φ = fun y => H (y + s) := by
    funext y
    by_cases hyt : y ∈ translatedComponent f D n
    · have hys : y + s ∈ D.component n := by simpa [s] using
        (translatedComponent_eq_preimage_add_componentGap f D n).mp hyt
      simp [Set.indicator, hyt, H, hys, s,
        f.compressionMap_eq_sub_componentGap_of_mem D n hys]
    · have hys : y + s ∉ D.component n := by
        intro h
        exact hyt ((translatedComponent_eq_preimage_add_componentGap f D n).mpr (by simpa [s] using h))
      simp [Set.indicator, hyt, H, hys]
  rw [← lintegral_indicator (compressionMap_image_component_isOpen f D n).measurableSet]
  rw [hpoint]
  rw [(measurePreserving_add_right (volume : Measure ℝ) s).lintegral_comp_emb
    (MeasurableEquiv.addRight s).measurableEmbedding H]
  rw [lintegral_indicator (D.isOpen_component n).measurableSet]

theorem lintegral_compressionTarget_eq_lintegral_comp_compressionMap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (φ : ℝ → ℝ≥0∞) :
    (∫⁻ y in compressionTarget f, φ y) =
      ∫⁻ x in f.positivitySet, φ (f.compressionMap x) := by
  rw [← setLIntegral_congr (iUnion_translatedComponent_ae_eq_compressionTarget f D)]
  rw [lintegral_iUnion (fun n => (compressionMap_image_component_isOpen f D n).measurableSet)
    (translatedComponent_pairwiseDisjoint f D)]
  rw [← D.union_eq]
  rw [lintegral_iUnion (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)]
  apply tsum_congr
  intro n
  exact lintegral_translatedComponent f D n φ

theorem integrableOn_compressionMap_mul_continuousRep
    (f : HalfLineH1)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    IntegrableOn (fun x => f.compressionMap x * f.continuousRep x) halfLine := by
  have hmeas : AEStronglyMeasurable
      (fun x => f.compressionMap x * f.continuousRep x) (volume.restrict halfLine) := by
    exact (f.compressionMap_lipschitzWith.continuous.mul
      f.continuous_continuousRep).aestronglyMeasurable
  apply Integrable.mono' hmoment.integrable hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hT0 := f.compressionMap_nonneg_of_nonneg hx
  have hTx := f.compressionMap_le_self_of_nonneg hx
  have hf := hnonneg x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hT0 hf)]
  exact mul_le_mul_of_nonneg_right hTx hf

theorem integral_mul_continuousRep_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (∫ y in translatedComponent f D n,
      y * (translatedComponentProfile f D n hnonneg).continuousRep y) =
    ∫ x in D.component n,
      f.compressionMap x * f.continuousRep x := by
  have hleft : (∫ y in translatedComponent f D n,
      y * (translatedComponentProfile f D n hnonneg).continuousRep y) =
      ∫ y in translatedComponent f D n,
        y * f.continuousRep (y + componentGap f D n) := by
    apply setIntegral_congr_fun (compressionMap_image_component_isOpen f D n).measurableSet
    intro y hy
    have hy0 : 0 ≤ y := (translatedComponent_subset_Ioi_zero f D n hy).le
    change y * (translatedComponentProfile f D n hnonneg).continuousRep y = _
    rw [continuousRep_translatedComponentProfile f D n hnonneg hy0]
    obtain ⟨x, hx, hxy⟩ := hy
    have hxs : x = y + componentGap f D n := by
      have hm := f.compressionMap_eq_sub_componentGap_of_mem D n hx
      linarith [hxy]
    rw [Set.indicator_of_mem (by rw [← hxs]; exact hx)]
  rw [hleft, ← integral_indicator (compressionMap_image_component_isOpen f D n).measurableSet]
  let s : ℝ := componentGap f D n
  let H : ℝ → ℝ := (D.component n).indicator
    (fun x => f.compressionMap x * f.continuousRep x)
  have hpoint : (translatedComponent f D n).indicator
      (fun y => y * f.continuousRep (y + s)) = fun y => H (y + s) := by
    funext y
    by_cases hyt : y ∈ translatedComponent f D n
    · have hys : y + s ∈ D.component n := by
        simpa [s] using (translatedComponent_eq_preimage_add_componentGap f D n).mp hyt
      rw [Set.indicator_of_mem hyt]
      rw [show H (y + s) = f.compressionMap (y + s) * f.continuousRep (y + s) by
        simp [H, hys]]
      rw [f.compressionMap_eq_sub_componentGap_of_mem D n hys]
      dsimp [s]
      ring
    · have hys : y + s ∉ D.component n := by
        intro h
        exact hyt ((translatedComponent_eq_preimage_add_componentGap f D n).mpr
          (by simpa [s] using h))
      simp [Set.indicator, hyt, H, hys]
  rw [hpoint]
  rw [(measurePreserving_add_right (volume : Measure ℝ) s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding H]
  rw [integral_indicator (D.isOpen_component n).measurableSet]

theorem weighted_translatedComponentProfile_eq_shiftedIndicator
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (fun y => y * (translatedComponentProfile f D n hnonneg).continuousRep y) =
      fun y => ((D.component n).indicator
        (fun x => f.compressionMap x * f.continuousRep x))
        (y + componentGap f D n) := by
  funext y
  by_cases hy0 : 0 ≤ y
  · rw [continuousRep_translatedComponentProfile f D n hnonneg hy0]
    by_cases hyt : y ∈ translatedComponent f D n
    · have hys : y + componentGap f D n ∈ D.component n := by
        simpa using (translatedComponent_eq_preimage_add_componentGap f D n).mp hyt
      rw [Set.indicator_of_mem hys]
      rw [show ((D.component n).indicator
          (fun x => f.compressionMap x * f.continuousRep x))
          (y + componentGap f D n) =
          f.compressionMap (y + componentGap f D n) *
            f.continuousRep (y + componentGap f D n) by
        simp [hys]]
      change y * f.continuousRep (y + componentGap f D n) =
        f.compressionMap (y + componentGap f D n) * f.continuousRep (y + componentGap f D n)
      rw [f.compressionMap_eq_sub_componentGap_of_mem D n hys]
      ring
    · have hys : y + componentGap f D n ∉ D.component n := by
        intro h
        exact hyt ((translatedComponent_eq_preimage_add_componentGap f D n).mpr h)
      simp [Set.indicator, hys]
  · have hyle : y ≤ 0 := le_of_not_ge hy0
    rw [(translatedComponentProfile f D n hnonneg).continuousRep_eq_zero_of_nonpositive hyle]
    have hys : y + componentGap f D n ∉ D.component n := by
      intro h
      have hyt : y ∈ translatedComponent f D n :=
        (translatedComponent_eq_preimage_add_componentGap f D n).mpr h
      exact (not_lt_of_ge hyle) (translatedComponent_subset_Ioi_zero f D n hyt)
    simp [Set.indicator, hys]

theorem integrable_mul_continuousRep_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    Integrable (fun y => y * (translatedComponentProfile f D n hnonneg).continuousRep y) := by
  let W : ℝ → ℝ := fun x => f.compressionMap x * f.continuousRep x
  have hWD : IntegrableOn W (D.component n) :=
    (integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment).mono_set
      ((D.subset n).trans (positivitySet_subset_halfLine f))
  have hind : Integrable ((D.component n).indicator W) :=
    hWD.integrable_indicator (D.isOpen_component n).measurableSet
  have hshift := (measurePreserving_add_right (volume : Measure ℝ)
    (componentGap f D n)).integrable_comp_of_integrable hind
  have heq := weighted_translatedComponentProfile_eq_shiftedIndicator f D n hnonneg
  have hmeas : AEStronglyMeasurable
      (fun y => y * (translatedComponentProfile f D n hnonneg).continuousRep y) volume := by
    rw [heq]
    exact hshift.aestronglyMeasurable
  exact hshift.congr' hmeas (Eventually.of_forall (fun y => by
    exact congrArg norm (congrFun heq y).symm))


theorem integrableOn_mul_continuousRep_compressedProfile_component
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    IntegrableOn (fun y => y * (compressedProfile f D hnonneg).continuousRep y)
      (translatedComponent f D n) := by
  have hi := (integrable_mul_continuousRep_translatedComponentProfile f D n
    hnonneg hmoment).integrableOn (s := translatedComponent f D n)
  apply hi.congr
  filter_upwards [ae_restrict_mem
    (compressionMap_image_component_isOpen f D n).measurableSet] with y hy
  rw [continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
    f D n hnonneg hy]

theorem summable_integral_norm_mul_continuousRep_compressedProfile_components
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    Summable (fun n => ∫ y in translatedComponent f D n,
      ‖y * (compressedProfile f D hnonneg).continuousRep y‖) := by
  have hW := integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment
  have hs := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (hW.mono_set (by rw [D.union_eq]; exact positivitySet_subset_halfLine f))
  apply hs.summable.congr
  intro n
  rw [← integral_mul_continuousRep_translatedComponentProfile f D n hnonneg]
  apply setIntegral_congr_fun (compressionMap_image_component_isOpen f D n).measurableSet
  intro y hy
  have hy0 : 0 ≤ y := (translatedComponent_subset_Ioi_zero f D n hy).le
  have hnon : 0 ≤ (compressedProfile f D hnonneg).continuousRep y := by
    exact compressedProfile_nonnegative f D hnonneg y hy0
  change y * (translatedComponentProfile f D n hnonneg).continuousRep y = _
  change y * (translatedComponentProfile f D n hnonneg).continuousRep y =
    ‖y * (compressedProfile f D hnonneg).continuousRep y‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy0 hnon)]
  rw [continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem f D n hnonneg hy]

theorem firstMoment_integrableOn_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (_hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    IntegrableOn (fun y => y * (compressedProfile f D hnonneg).continuousRep y) halfLine := by
  let U : Set ℝ := ⋃ n, translatedComponent f D n
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n =>
    (compressionMap_image_component_isOpen f D n).measurableSet
  have hu : IntegrableOn (fun y => y * (compressedProfile f D hnonneg).continuousRep y) U :=
    MeasureTheory.integrableOn_iUnion_of_summable_integral_norm
      (fun n => integrableOn_mul_continuousRep_compressedProfile_component f D n
        hnonneg hmoment)
      (summable_integral_norm_mul_continuousRep_compressedProfile_components f D hnonneg hmoment)
  have hi : Integrable (U.indicator
      (fun y => y * (compressedProfile f D hnonneg).continuousRep y)) :=
    hu.integrable_indicator hU
  have hzero : ∀ x ∉ U, x * (compressedProfile f D hnonneg).continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · rw [(compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive hx0, mul_zero]
    · rw [continuousRep_compressedProfile_eq_zero_of_not_mem_iUnion f D hnonneg
        (le_of_not_ge hx0) hx, mul_zero]
  have heq : (fun x => x * (compressedProfile f D hnonneg).continuousRep x) =ᵐ[volume.restrict halfLine]
      U.indicator (fun x => x * (compressedProfile f D hnonneg).continuousRep x) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [] with x hx
    by_cases hxu : x ∈ U
    · simp [Set.indicator, hxu]
    · simp [Set.indicator, hxu, hzero x hxu]
  exact hi.integrableOn.congr heq.symm


theorem firstMoment_compressedProfile_eq_integral_compressionMap_mul
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (_hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    (compressedProfile f D hnonneg).firstMoment =
      ∫ x in halfLine, f.compressionMap x * f.continuousRep x := by
  let U : Set ℝ := ⋃ n, translatedComponent f D n
  have ht := MeasureTheory.hasSum_integral_iUnion
    (fun n => (compressionMap_image_component_isOpen f D n).measurableSet)
    (translatedComponent_pairwiseDisjoint f D)
    (MeasureTheory.integrableOn_iUnion_of_summable_integral_norm
      (fun n => integrableOn_mul_continuousRep_compressedProfile_component f D n
        hnonneg hmoment)
      (summable_integral_norm_mul_continuousRep_compressedProfile_components f D hnonneg hmoment))
  have hs := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    ((integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment).mono_set
      (by rw [D.union_eq]; exact positivitySet_subset_halfLine f))
  have hterms : (fun n => ∫ y in translatedComponent f D n,
      y * (compressedProfile f D hnonneg).continuousRep y) =
      (fun n => ∫ x in D.component n,
        f.compressionMap x * f.continuousRep x) := by
    funext n
    calc
      ∫ y in translatedComponent f D n,
          y * (compressedProfile f D hnonneg).continuousRep y =
          ∫ y in translatedComponent f D n,
            y * (translatedComponentProfile f D n hnonneg).continuousRep y := by
              apply setIntegral_congr_fun (compressionMap_image_component_isOpen f D n).measurableSet
              intro y hy
              change y * (compressedProfile f D hnonneg).continuousRep y = _
              rw [continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
                f D n hnonneg hy]
      _ = ∫ x in D.component n, f.compressionMap x * f.continuousRep x :=
        integral_mul_continuousRep_translatedComponentProfile f D n hnonneg
  have hu : (∫ y in U, y * (compressedProfile f D hnonneg).continuousRep y) =
      ∫ x in f.positivitySet, f.compressionMap x * f.continuousRep x := by
    have huniq := HasSum.unique (hterms ▸ ht) hs
    simpa [U, D.union_eq] using huniq
  have hcomp_zero : ∀ x ∉ U,
      x * (compressedProfile f D hnonneg).continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · rw [(compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive hx0, mul_zero]
    · rw [continuousRep_compressedProfile_eq_zero_of_not_mem_iUnion f D hnonneg
        (le_of_not_ge hx0) hx, mul_zero]
  have hsource_zero : ∀ x ∉ f.positivitySet,
      f.compressionMap x * f.continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · rw [f.compressionMap_eq_zero_of_nonpositive hx0, zero_mul]
    · have hf : f.continuousRep x = 0 := le_antisymm (le_of_not_gt hx) (hnonneg x (le_of_not_ge hx0))
      rw [hf, mul_zero]
  have hU : (∫ x in U, x * (compressedProfile f D hnonneg).continuousRep x) =
      ∫ x, x * (compressedProfile f D hnonneg).continuousRep x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero hcomp_zero
  have hP : (∫ x in f.positivitySet, f.compressionMap x * f.continuousRep x) =
      ∫ x, f.compressionMap x * f.continuousRep x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsource_zero
  have hcompHalf : (∫ x in halfLine, x * (compressedProfile f D hnonneg).continuousRep x) =
      ∫ x, x * (compressedProfile f D hnonneg).continuousRep x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [(compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx), mul_zero]
  have hsourceHalf : (∫ x in halfLine, f.compressionMap x * f.continuousRep x) =
      ∫ x, f.compressionMap x * f.continuousRep x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx0 : x ≤ 0 := le_of_not_ge hx
    rw [f.compressionMap_eq_zero_of_nonpositive hx0, zero_mul]
  unfold HalfLineH1.firstMoment RayleighKernel.firstMoment
  rw [hcompHalf, ← hU, hu, hP, ← hsourceHalf]

lemma firstMoment_compressedProfile_le
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    (compressedProfile f D hnonneg).firstMoment ≤ f.firstMoment := by
  rw [firstMoment_compressedProfile_eq_integral_compressionMap_mul f D hnonneg
    hint hmoment]
  unfold HalfLineH1.firstMoment RayleighKernel.firstMoment
  apply setIntegral_mono_ae_restrict
  · exact (integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment)
  · exact hmoment
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  exact mul_le_mul_of_nonneg_right (f.compressionMap_le_self_of_nonneg hx) (hnonneg x hx)


end RayleighKernel.Analysis.HalfLineH1
