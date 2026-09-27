import RayleighKernel.Compression.Convergence
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem deriv_ae_eq_zero_on_levelSet
    {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFdiff : ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ F x) (c : ℝ) :
    deriv F =ᵐ[(volume : Measure ℝ).restrict {x | F x = c}] 0 := by
  let s : Set ℝ := {x | F x = c} ∩ {x | DifferentiableAt ℝ F x}
  have hs : MeasurableSet s := by
    exact measurableSet_preimage (hFcont.measurable) (measurableSet_singleton c) |>.inter
      (measurableSet_of_differentiableAt ℝ F)
  have happrox : ApproximatesLinearOn F (0 : ℝ →L[ℝ] ℝ) s 0 := by
    intro x hx y hy
    simp only [s, mem_inter_iff, mem_ofPred_eq] at hx hy
    rw [hx.1, hy.1]
    simp
  have hfd : ∀ᵐ x ∂(volume : Measure ℝ).restrict s, fderiv ℝ F x = 0 := by
    have h := happrox.norm_fderiv_sub_le volume hs
      (fun x ↦ fderiv ℝ F x)
      (fun x hx ↦ (DifferentiableAt.hasFDerivAt hx.2).hasFDerivWithinAt)
    filter_upwards [h] with x hx
    have hn : ‖fderiv ℝ F x‖₊ = 0 := le_antisymm (by simpa using hx) bot_le
    exact nnnorm_eq_zero.mp hn
  have hderiv_s : deriv F =ᵐ[(volume : Measure ℝ).restrict s] 0 := by
    filter_upwards [hfd, ae_restrict_mem hs] with x hx hxs
    rw [← fderiv_apply_one_eq_deriv, hx]
    simp
  have hsets : s =ᵐ[(volume : Measure ℝ)] {x | F x = c} := by
    filter_upwards [hFdiff] with x hx
    simp only [s, mem_inter_iff, mem_ofPred_eq]
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx⟩⟩
  rw [← Measure.restrict_congr_set hsets]
  exact hderiv_s

theorem deriv_continuousRep_ae_eq_zero_on_zeroSet (f : HalfLineH1) :
    deriv f.continuousRep =ᵐ[(volume : Measure ℝ).restrict
      {x | f.continuousRep x = 0}] 0 := by
  exact deriv_ae_eq_zero_on_levelSet f.continuous_continuousRep
    (f.hasDerivAt_continuousRep_ae.mono fun _ h ↦ h.differentiableAt) 0

theorem weakDeriv_ae_eq_zero_on_compl_positivitySet
    (f : HalfLineH1)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (f.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict f.positivitySetᶜ] 0 := by
  have hset : f.positivitySetᶜ = {x | f.continuousRep x = 0} := by
    ext x
    constructor
    · intro hx
      by_cases hx0 : x ≤ 0
      · exact f.continuousRep_eq_zero_of_nonpositive hx0
      · have hn : 0 ≤ f.continuousRep x := hnonneg x (le_of_not_ge hx0)
        exact le_antisymm (le_of_not_gt hx) hn
    · intro hx
      simp only [HalfLineH1.positivitySet, mem_compl_iff, mem_ofPred_eq]
      exact not_lt_of_ge (le_of_eq hx)
  rw [hset]
  have hweak : (f.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict
      {x | f.continuousRep x = 0}] deriv f.continuousRep :=
    ae_restrict_of_ae f.deriv_continuousRep_ae.symm
  exact hweak.trans (deriv_continuousRep_ae_eq_zero_on_zeroSet f)

theorem norm_sq_sum_value_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (s : Finset ℕ) :
    ‖Finset.sum s (fun n => (translatedComponentProfile f D n hnonneg).value)‖ ^ 2 =
      Finset.sum s (fun n => ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, norm_add_sq_real, ih]
    have hcross : inner ℝ (Finset.sum s
        (fun n => (translatedComponentProfile f D n hnonneg).value))
        (translatedComponentProfile f D a hnonneg).value = 0 := by
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact inner_value_translatedComponentProfile_eq_zero f D hnonneg (by
        intro hia
        subst a
        exact ha hi)
    rw [real_inner_comm, hcross, mul_zero, Finset.sum_insert ha]
    ring

theorem norm_sq_sum_weakDeriv_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (s : Finset ℕ) :
    ‖Finset.sum s (fun n => (translatedComponentProfile f D n hnonneg).weakDeriv)‖ ^ 2 =
      Finset.sum s (fun n => ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, norm_add_sq_real, ih]
    have hcross : inner ℝ (Finset.sum s
        (fun n => (translatedComponentProfile f D n hnonneg).weakDeriv))
        (translatedComponentProfile f D a hnonneg).weakDeriv = 0 := by
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact inner_weakDeriv_translatedComponentProfile_eq_zero f D hnonneg (by
        intro hia
        subst a
        exact ha hi)
    rw [real_inner_comm, hcross, mul_zero, Finset.sum_insert ha]
    ring

theorem summable_norm_sq_value_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    Summable (fun n => ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2) := by
  have hv := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (f.continuousRep_sq_integrable.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hv' : Summable (fun n => ∫ x in D.component n, f.continuousRep x ^ 2) := hv.summable
  exact hv'.congr (fun n => by
    calc
      ∫ x in D.component n, f.continuousRep x ^ 2 =
          ‖(componentRestrictionProfile f D n hnonneg).value‖ ^ 2 :=
        (norm_value_componentRestrictionProfile_sq_eq_integral f D n hnonneg).symm
      _ = ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2 := by
        rw [norm_value_translatedComponentProfile])

theorem summable_norm_sq_weakDeriv_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    Summable (fun n => ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2) := by
  have hd := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    ((Lp.memLp f.weakDeriv).integrable_sq.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hd' : Summable (fun n => ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2) := hd.summable
  exact hd'.congr (fun n => by
    calc
      ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 =
          ‖(componentRestrictionProfile f D n hnonneg).weakDeriv‖ ^ 2 :=
        (norm_weakDeriv_componentRestrictionProfile_sq_eq_integral f D n hnonneg).symm
      _ = ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2 := by
        rw [norm_weakDeriv_translatedComponentProfile])

theorem norm_value_compressedProfile_sq_eq_tsum
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(compressedProfile f D hnonneg).value‖ ^ 2 =
      ∑' n, ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2 := by
  have hl := (HalfLineH1.tendsto_value (tendsto_finiteCompressedProfile f D hnonneg)).norm.pow 2
  have hr := (summable_norm_sq_value_translatedComponentProfile f D hnonneg).hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hl
  simpa only [finiteCompressedProfile, map_sum, norm_sq_sum_value_translatedComponentProfile] using hr

theorem norm_weakDeriv_compressedProfile_sq_eq_tsum
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(compressedProfile f D hnonneg).weakDeriv‖ ^ 2 =
      ∑' n, ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2 := by
  have hl := (HalfLineH1.tendsto_weakDeriv (tendsto_finiteCompressedProfile f D hnonneg)).norm.pow 2
  have hr := (summable_norm_sq_weakDeriv_translatedComponentProfile f D hnonneg).hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hl
  simpa only [finiteCompressedProfile, map_sum, norm_sq_sum_weakDeriv_translatedComponentProfile] using hr

theorem tsum_norm_sq_value_translatedComponentProfile_eq
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (∑' n, ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2) = ‖f.value‖ ^ 2 := by
  have hv := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (f.continuousRep_sq_integrable.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hsum := hv.tsum_eq
  rw [D.union_eq] at hsum
  calc
    (∑' n, ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2) =
        ∑' n, ∫ x in D.component n, f.continuousRep x ^ 2 := by
      apply tsum_congr
      intro n
      calc
        ‖(translatedComponentProfile f D n hnonneg).value‖ ^ 2 =
            ‖(componentRestrictionProfile f D n hnonneg).value‖ ^ 2 := by
          rw [norm_value_translatedComponentProfile]
        _ = ∫ x in D.component n, f.continuousRep x ^ 2 :=
          norm_value_componentRestrictionProfile_sq_eq_integral f D n hnonneg
    _ = ∫ x in f.positivitySet, f.continuousRep x ^ 2 := hsum
    _ = ‖f.value‖ ^ 2 := by
      have hset : (∫ x in f.positivitySet, f.continuousRep x ^ 2) =
          ∫ x in Ici 0, f.continuousRep x ^ 2 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · exact f.integral_continuousRep_sq_eq_norm_value_sq.trans
            f.integral_continuousRep_sq_Ici_eq_norm_value_sq.symm
        · intro x hx
          by_cases hx0 : x ≤ 0
          · rw [f.continuousRep_eq_zero_of_nonpositive hx0, zero_pow two_ne_zero]
          · have hz : f.continuousRep x = 0 :=
              le_antisymm (le_of_not_gt (fun h => hx (by exact h)))
                (hnonneg x (le_of_not_ge hx0))
            rw [hz, zero_pow two_ne_zero]
      exact hset.trans f.integral_continuousRep_sq_Ici_eq_norm_value_sq

theorem tsum_norm_sq_weakDeriv_translatedComponentProfile_eq
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (∑' n, ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2) =
      ‖f.weakDeriv‖ ^ 2 := by
  have hd := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    ((Lp.memLp f.weakDeriv).integrable_sq.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hsum := hd.tsum_eq
  rw [D.union_eq] at hsum
  have hzero := weakDeriv_ae_eq_zero_on_compl_positivitySet f hnonneg
  calc
    (∑' n, ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2) =
        ∑' n, ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 := by
      apply tsum_congr
      intro n
      calc
        ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ ^ 2 =
            ‖(componentRestrictionProfile f D n hnonneg).weakDeriv‖ ^ 2 := by
          rw [norm_weakDeriv_translatedComponentProfile]
        _ = ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 :=
          norm_weakDeriv_componentRestrictionProfile_sq_eq_integral f D n hnonneg
    _ = ∫ x in f.positivitySet, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 := hsum
    _ = ‖f.weakDeriv‖ ^ 2 := by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
      · have hderiv : (fun x => (f.weakDeriv : ℝ → ℝ) x ^ 2) =ᵐ[volume]
            (fun x => deriv f.continuousRep x ^ 2) := by
          filter_upwards [f.deriv_continuousRep_ae] with x hx
          simp [hx]
        rw [integral_congr_ae hderiv]
        exact f.integral_deriv_continuousRep_sq_eq_norm_weakDeriv_sq
      · filter_upwards [ae_imp_of_ae_restrict hzero] with x hx hxnot
        have hz := hx hxnot
        simpa using hz

theorem squareEnergy_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (compressedProfile f D hnonneg).squareEnergy = f.squareEnergy := by
  rw [HalfLineH1.squareEnergy, HalfLineH1.squareEnergy]
  rw [norm_value_compressedProfile_sq_eq_tsum,
    tsum_norm_sq_value_translatedComponentProfile_eq]

theorem dirichletEnergy_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (compressedProfile f D hnonneg).dirichletEnergy = f.dirichletEnergy := by
  rw [HalfLineH1.dirichletEnergy, HalfLineH1.dirichletEnergy]
  rw [norm_weakDeriv_compressedProfile_sq_eq_tsum,
    tsum_norm_sq_weakDeriv_translatedComponentProfile_eq]

theorem positivitySet_subset_halfLine (f : HalfLineH1) :
    f.positivitySet ⊆ halfLine := by
  intro x hx
  exact (show 0 < x from lt_of_not_ge fun h => hx.ne'
    (f.continuousRep_eq_zero_of_nonpositive h)).le

theorem integrable_continuousRep_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine) :
    Integrable (translatedComponentProfile f D n hnonneg).continuousRep := by
  have hwhole := f.continuousRep_integrable_of_integrableOn_halfLine hint
  have hshift := (measurePreserving_add_right (volume : Measure ℝ)
    (componentGap f D n)).integrable_comp hwhole.aestronglyMeasurable
  have hind := (hshift.mpr hwhole).indicator
    (compressionMap_image_component_isOpen f D n).measurableSet
  have hrep := (translatedComponentProfile f D n hnonneg).continuousRep_ae_eq_value.trans
    (value_translatedComponentProfile_ae_indicator f D n hnonneg)
  exact hind.congr hrep.symm

theorem integral_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (∫ y in translatedComponent f D n,
      (translatedComponentProfile f D n hnonneg).continuousRep y) =
      ∫ x in D.component n, f.continuousRep x := by
  have hleft : (∫ y in translatedComponent f D n,
      (translatedComponentProfile f D n hnonneg).continuousRep y) =
      ∫ y in translatedComponent f D n, f.continuousRep
        (y + componentGap f D n) := by
    apply setIntegral_congr_fun (μ := (volume : Measure ℝ))
      (compressionMap_image_component_isOpen f D n).measurableSet
    intro y hy
    rw [continuousRep_translatedComponentProfile f D n hnonneg
      (show (0 : ℝ) ≤ y from (translatedComponent_subset_Ioi_zero f D n hy).le)]
    have hz := (translatedComponent_eq_preimage_add_componentGap f D n).mp hy
    simp [Set.indicator, hz]
  rw [hleft, ← integral_indicator (compressionMap_image_component_isOpen f D n).measurableSet]
  let s : ℝ := componentGap f D n
  let H : ℝ → ℝ := (D.component n).indicator f.continuousRep
  have hpoint : (translatedComponent f D n).indicator
      (fun y => f.continuousRep (y + s)) = fun y => H (y + s) := by
    funext y
    by_cases hy : y ∈ translatedComponent f D n
    · have hz : y + s ∈ D.component n := by
        simpa [s] using (translatedComponent_eq_preimage_add_componentGap f D n).mp hy
      simp [Set.indicator, hy, H, hz]
    · have hz : y + s ∉ D.component n := by
        intro hz
        exact hy ((translatedComponent_eq_preimage_add_componentGap f D n).mpr hz)
      simp [Set.indicator, hy, H, hz]
  rw [show (fun y => f.continuousRep (y + componentGap f D n)) =
      (fun y => f.continuousRep (y + s)) by rfl, hpoint]
  rw [(measurePreserving_add_right (volume : Measure ℝ) s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding H]
  rw [integral_indicator (D.isOpen_component n).measurableSet]

theorem continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {y : ℝ}
    (hy : y ∈ translatedComponent f D n) :
    (compressedProfile f D hnonneg).continuousRep y =
      (translatedComponentProfile f D n hnonneg).continuousRep y := by
  obtain ⟨z, hz, hzy⟩ := hy
  rw [← hzy]
  exact (continuousRep_compressedProfile_compressionMap f D hnonneg hz).trans
    (continuousRep_translatedComponentProfile_compressionMap f D n hnonneg hz).symm

theorem integrableOn_continuousRep_compressedProfile_component
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine) :
    IntegrableOn (compressedProfile f D hnonneg).continuousRep
      (translatedComponent f D n) := by
  have hi := (integrable_continuousRep_translatedComponentProfile f D n hnonneg hint).integrableOn
    (s := translatedComponent f D n)
  apply hi.congr
  filter_upwards [ae_restrict_mem (compressionMap_image_component_isOpen f D n).measurableSet]
    with y hy
  exact (continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
    f D n hnonneg hy).symm

theorem summable_integral_norm_continuousRep_compressedProfile_components
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine) :
    Summable (fun n => ∫ y in translatedComponent f D n,
      ‖(compressedProfile f D hnonneg).continuousRep y‖) := by
  have hi := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (hint.mono_set (by rw [D.union_eq]; exact positivitySet_subset_halfLine f))
  apply hi.summable.congr
  intro n
  have heq : (∫ y in translatedComponent f D n,
      ‖(compressedProfile f D hnonneg).continuousRep y‖) =
      ∫ y in translatedComponent f D n,
        (translatedComponentProfile f D n hnonneg).continuousRep y := by
    apply setIntegral_congr_fun (compressionMap_image_component_isOpen f D n).measurableSet
    intro y hy
    change ‖(compressedProfile f D hnonneg).continuousRep y‖ = _
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
        f D n hnonneg hy
    · rw [continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
        f D n hnonneg hy]
      rw [continuousRep_translatedComponentProfile f D n hnonneg
        (show (0 : ℝ) ≤ y from (translatedComponent_subset_Ioi_zero f D n hy).le)]
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy, f.compressionMap_eq_sub_componentGap_of_mem D n hz]
      rw [show z - componentGap f D n + componentGap f D n = z by ring]
      simpa [Set.indicator, hz] using hnonneg z (positivitySet_subset_halfLine f (D.subset n hz))
  rw [heq, integral_translatedComponentProfile f D n hnonneg]

theorem integrableOn_continuousRep_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine) :
    IntegrableOn (compressedProfile f D hnonneg).continuousRep halfLine := by
  let U : Set ℝ := ⋃ n, translatedComponent f D n
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n =>
    (compressionMap_image_component_isOpen f D n).measurableSet
  have hunion : IntegrableOn (compressedProfile f D hnonneg).continuousRep U :=
    MeasureTheory.integrableOn_iUnion_of_summable_integral_norm
      (fun n => integrableOn_continuousRep_compressedProfile_component f D n hnonneg hint)
      (summable_integral_norm_continuousRep_compressedProfile_components f D hnonneg hint)
  have hind : Integrable (U.indicator (compressedProfile f D hnonneg).continuousRep) :=
    hunion.integrable_indicator hU
  have hzero : ∀ x ∉ U, (compressedProfile f D hnonneg).continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · exact (compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive hx0
    · exact continuousRep_compressedProfile_eq_zero_of_not_mem_iUnion f D hnonneg
        (le_of_not_ge hx0) hx
  have heq : (compressedProfile f D hnonneg).continuousRep =ᵐ[volume.restrict halfLine]
      U.indicator (compressedProfile f D hnonneg).continuousRep := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [] with x hx
    by_cases hxu : x ∈ U
    · simp [Set.indicator, hxu]
    · simp [Set.indicator, hxu, hzero x hxu]
  exact hind.integrableOn.congr heq.symm

theorem mass_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine) :
    (compressedProfile f D hnonneg).mass = f.mass := by
  let U : Set ℝ := ⋃ n, translatedComponent f D n
  have hunion := MeasureTheory.hasSum_integral_iUnion
    (fun n => (compressionMap_image_component_isOpen f D n).measurableSet)
    (translatedComponent_pairwiseDisjoint f D)
    (MeasureTheory.integrableOn_iUnion_of_summable_integral_norm
      (fun n => integrableOn_continuousRep_compressedProfile_component f D n hnonneg hint)
      (summable_integral_norm_continuousRep_compressedProfile_components f D hnonneg hint))
  have hsource := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (hint.mono_set (by rw [D.union_eq]; exact positivitySet_subset_halfLine f))
  have hterms : (fun n => ∫ x in translatedComponent f D n,
      (compressedProfile f D hnonneg).continuousRep x) =
    (fun n => ∫ x in D.component n, f.continuousRep x) := by
    funext n
    calc
      ∫ x in translatedComponent f D n, (compressedProfile f D hnonneg).continuousRep x =
          ∫ x in translatedComponent f D n,
            (translatedComponentProfile f D n hnonneg).continuousRep x := by
        apply setIntegral_congr_fun (compressionMap_image_component_isOpen f D n).measurableSet
        intro x hx
        exact continuousRep_compressedProfile_eq_translatedComponentProfile_of_mem
          f D n hnonneg hx
      _ = ∫ x in D.component n, f.continuousRep x :=
        integral_translatedComponentProfile f D n hnonneg
  have hunion' : HasSum (fun n => ∫ x in D.component n, f.continuousRep x)
      (∫ x in U, (compressedProfile f D hnonneg).continuousRep x) := by
    rw [← hterms]
    exact hunion
  have hsum : (∫ x in U, (compressedProfile f D hnonneg).continuousRep x) =
      ∫ x in f.positivitySet, f.continuousRep x := by
    have heq := HasSum.unique hunion' hsource
    simpa [U, D.union_eq] using heq
  have hcomp_zero : ∀ x ∉ U,
      (compressedProfile f D hnonneg).continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · exact (compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive hx0
    · exact continuousRep_compressedProfile_eq_zero_of_not_mem_iUnion f D hnonneg
        (le_of_not_ge hx0) hx
  have hsource_zero : ∀ x ∉ f.positivitySet, f.continuousRep x = 0 := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · exact f.continuousRep_eq_zero_of_nonpositive hx0
    · exact le_antisymm (le_of_not_gt hx) (hnonneg x (le_of_not_ge hx0))
  unfold HalfLineH1.mass RayleighKernel.mass
  have hcomp_nonpos : ∀ x ∉ halfLine,
      (compressedProfile f D hnonneg).continuousRep x = 0 := fun x hx =>
    (compressedProfile f D hnonneg).continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx)
  have hsource_nonpos : ∀ x ∉ halfLine, f.continuousRep x = 0 := fun x hx =>
    f.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx)
  have hcompU : (∫ x in U, (compressedProfile f D hnonneg).continuousRep x) =
      ∫ x, (compressedProfile f D hnonneg).continuousRep x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hcomp_zero
  have hsourceP : (∫ x in f.positivitySet, f.continuousRep x) =
      ∫ x, f.continuousRep x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsource_zero
  rw [hcompU, hsourceP] at hsum
  have hcompHalf : (∫ x in halfLine, (compressedProfile f D hnonneg).continuousRep x) =
      ∫ x, (compressedProfile f D hnonneg).continuousRep x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hcomp_nonpos
  have hsourceHalf : (∫ x in halfLine, f.continuousRep x) =
      ∫ x, f.continuousRep x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsource_nonpos
  exact hcompHalf.trans (hsum.trans hsourceHalf.symm)

end RayleighKernel.Analysis.HalfLineH1
