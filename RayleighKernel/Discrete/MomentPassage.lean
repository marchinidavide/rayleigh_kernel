import RayleighKernel.Discrete.ShiftedCompactness
import RayleighKernel.Variational.Existence

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open RayleighKernel.Analysis

theorem shiftedInterpolant_firstMoment_integrableOn_and_le_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) :
    IntegrableOn (fun x ↦ x * v.continuousRep x) halfLine ∧ v.firstMoment ≤ L := by
  have hv := shiftedInterpolant_nonnegative_of_tendstoUniformlyOn hw hunif
  have hcompact : ∀ R : ℝ, 0 < R →
      (∫ x in Icc 0 R, x * v.continuousRep x) ≤ L := by
    intro R hR
    have hlocal := Analysis.HalfLineH1.tendsto_setIntegral_mul_continuousRep_of_tendstoUniformlyOn
      (g := fun x ↦ x) continuous_id (u := fun n ↦ shiftedInterpolantH1 (w n) (hw n))
      (v := v) isCompact_Icc (by
        simpa only [continuousRep_shiftedInterpolantH1_eq] using
          hunif (Icc 0 R) isCompact_Icc)
    have hseq : ∀ n, (∫ x in Icc 0 R,
        x * (shiftedInterpolantH1 (w n) (hw n)).continuousRep x) ≤ L + mesh n := by
      intro n
      rw [continuousRep_shiftedInterpolantH1_eq (hw n)]
      have hh := setIntegral_mono_set (integrable_mul_shiftedInterpolant (hw n)).integrableOn
        (show 0 ≤ᵐ[volume.restrict halfLine]
            (fun x ↦ x * shiftedInterpolant (mesh n) (w n) x) by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
          exact mul_nonneg hx (shiftedInterpolant_nonnegative (hw n) x))
        (Filter.Eventually.of_forall (fun x (hx : x ∈ Icc 0 R) ↦ hx.1))
      rw [shiftedInterpolant_firstMoment (hw n)] at hh
      exact hh
    have hlim : Tendsto (fun n ↦ L + mesh n) atTop (𝓝 L) := by
      simpa using (tendsto_const_nhds (x := L)).add hmesh
    exact le_of_tendsto_of_tendsto hlocal hlim (Filter.Eventually.of_forall hseq)
  have hlocal_int : ∀ R : ℝ, IntegrableOn (fun x ↦ x * v.continuousRep x) (Icc 0 R) := by
    intro R
    exact (continuousOn_id.mul v.continuous_continuousRep.continuousOn).integrableOn_compact
      isCompact_Icc
  have hbound : ∀ᶠ R in atTop,
      ∫ x in Icc 0 R, ‖x * v.continuousRep x‖ ≤ L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hEq : (∫ x in Icc 0 R, ‖x * v.continuousRep x‖) =
        ∫ x in Icc 0 R, x * v.continuousRep x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg hx.1 (hv x hx.1)
    rw [hEq]
    exact hcompact R hR
  have hcover : AECover (volume.restrict halfLine) atTop (fun R : ℝ ↦ Icc 0 R) := by
    refine ⟨?_, fun R ↦ measurableSet_Icc⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    filter_upwards [eventually_ge_atTop x] with R hR
    exact ⟨hx, hR⟩
  have hinter : Integrable (fun x ↦ x * v.continuousRep x)
      (volume.restrict halfLine) := hcover.integrable_of_integral_norm_bounded L
    (fun R ↦ (hlocal_int R).mono_measure Measure.restrict_le_self)
    (by filter_upwards [hbound] with R hR
        rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
          apply Measure.restrict_restrict_of_subset
          exact Icc_subset_Ici_self]
        exact hR)
  have hmoment_tendsto : Tendsto (fun R : ℝ ↦
      ∫ x in Icc 0 R, x * v.continuousRep x ∂(volume.restrict halfLine)) atTop
        (𝓝 (∫ x, x * v.continuousRep x ∂(volume.restrict halfLine))) :=
    hcover.integral_tendsto_of_countably_generated hinter
  have hle : (∫ x, x * v.continuousRep x ∂(volume.restrict halfLine)) ≤ L := by
    refine le_of_tendsto' hmoment_tendsto ?_
    intro R
    by_cases hR : 0 < R
    · rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
      exact hcompact R hR
    · rcases eq_or_lt_of_le (le_of_not_gt hR) with rfl | hneg
      · have hL : 0 ≤ L := by
          rw [← (hw 0).firstMoment_eq]
          exact mul_nonneg (hw 0).h_pos.le
            (tsum_nonneg (fun j ↦
              mul_nonneg (Nat.cast_nonneg j) ((hw 0).nonnegative j)))
        simpa [v.continuousRep_zero] using hL
      · have hL : 0 ≤ L := by
          rw [← (hw 0).firstMoment_eq]
          exact mul_nonneg (hw 0).h_pos.le
            (tsum_nonneg (fun j ↦
              mul_nonneg (Nat.cast_nonneg j) ((hw 0).nonnegative j)))
        simpa [Icc_eq_empty_of_lt hneg] using hL
  exact ⟨hinter, by
    simpa [Analysis.HalfLineH1.firstMoment, RayleighKernel.firstMoment, halfLine] using hle⟩

structure ShiftedLimitData (L : ℝ) (v : Analysis.HalfLineH1) : Prop where
  nonnegative : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x
  integrable : IntegrableOn v.continuousRep halfLine
  firstMoment_integrable : IntegrableOn (fun x ↦ x * v.continuousRep x) halfLine
  mass_eq : v.mass = 1
  firstMoment_pos : 0 < v.firstMoment
  firstMoment_le : v.firstMoment ≤ L

theorem shiftedLimitData_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n ↦ shiftedInterpolant (mesh n) (w n)) v.continuousRep atTop K) :
    ShiftedLimitData L v := by
  have hn := shiftedInterpolant_nonnegative_of_tendstoUniformlyOn hw hunif
  have hi := shiftedInterpolant_integrableOn_continuousRep_of_tendstoUniformlyOn hw hunif
  have hm := mass_shiftedInterpolant_limit_of_tendstoUniformlyOn hmesh hw hunif
  have hfi := shiftedInterpolant_firstMoment_integrableOn_and_le_of_tendstoUniformlyOn
    hmesh hw hunif
  exact ⟨hn, hi, hfi.1, hm,
    Analysis.HalfLineH1.firstMoment_pos_of_mass_eq_one_of_nonnegative hn hm hfi.1, hfi.2⟩

theorem ShiftedLimitData.isAdmissible_firstMoment {L : ℝ} {v : Analysis.HalfLineH1}
    (d : ShiftedLimitData L v) : v.IsAdmissible v.firstMoment := by
  exact ⟨d.nonnegative, d.integrable, d.firstMoment_integrable, d.mass_eq, rfl⟩

theorem ShiftedLimitData.firstMoment_eq_of_rayleighQuotient_le_Lambda
    {L : ℝ} {v : Analysis.HalfLineH1} (d : ShiftedLimitData L v) (hL : 0 < L)
    (hq : v.rayleighQuotient ≤ Analysis.Lambda L) : v.firstMoment = L := by
  by_contra hne
  have hmlt : v.firstMoment < L := lt_of_le_of_ne d.firstMoment_le hne
  let a : ℝ := v.firstMoment / L
  have ha : 0 < a := div_pos d.firstMoment_pos hL
  have ha1 : a < 1 := (div_lt_one hL).2 hmlt
  have hscaled : (v.rescale a ha).IsAdmissible L := by
    have h := v.rescale_isAdmissible ha d.isAdmissible_firstMoment
    convert h using 1
    dsimp [a]
    field_simp [ne_of_gt hL, ne_of_gt d.firstMoment_pos]
  have hlower := Analysis.Lambda_le_of_isAdmissible hscaled
  have hqscale := v.rayleighQuotient_rescale ha
  have hpos := Analysis.HalfLineH1.rayleighQuotient_pos_of_mass_eq_one d.mass_eq
  rw [hqscale] at hlower
  have hs : a ^ 2 < 1 := by nlinarith
  nlinarith

theorem ShiftedLimitData.isAdmissible_of_rayleighQuotient_le_Lambda
    {L : ℝ} {v : Analysis.HalfLineH1} (d : ShiftedLimitData L v) (hL : 0 < L)
    (hq : v.rayleighQuotient ≤ Analysis.Lambda L) : v.IsAdmissible L := by
  exact { d.isAdmissible_firstMoment with
    firstMoment_eq := d.firstMoment_eq_of_rayleighQuotient_le_Lambda hL hq }

end RayleighKernel.Discrete
