import RayleighKernel.Compression.FiniteProfiles
import RayleighKernel.Analysis.HalfLineSobolevCompactness
import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem inner_eq_zero_of_ae_eq_indicator_of_disjoint
    {g h : RealL2} {s t : Set ℝ} (hst : Disjoint s t)
    {G H : ℝ → ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume] s.indicator G)
    (hh : (h : ℝ → ℝ) =ᵐ[volume] t.indicator H) :
    inner ℝ g h = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hg, hh] with x hxg hxh
  rw [hxg, hxh, Real.inner_apply]
  by_cases hsx : x ∈ s
  · have htx : x ∉ t := fun htx => (Set.disjoint_left.mp hst) hsx htx
    simp [Set.indicator, hsx, htx]
  · simp [Set.indicator, hsx]

theorem inner_value_translatedComponentProfile_eq_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (translatedComponentProfile f D m hnonneg).value
      (translatedComponentProfile f D n hnonneg).value = 0 := by
  exact inner_eq_zero_of_ae_eq_indicator_of_disjoint
    (translatedComponent_pairwiseDisjoint f D hmn)
    (value_translatedComponentProfile_ae_indicator f D m hnonneg)
    (value_translatedComponentProfile_ae_indicator f D n hnonneg)

theorem inner_weakDeriv_translatedComponentProfile_eq_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (translatedComponentProfile f D m hnonneg).weakDeriv
      (translatedComponentProfile f D n hnonneg).weakDeriv = 0 := by
  exact inner_eq_zero_of_ae_eq_indicator_of_disjoint
    (translatedComponent_pairwiseDisjoint f D hmn)
    (weakDeriv_translatedComponentProfile_ae_indicator f D m hnonneg)
    (weakDeriv_translatedComponentProfile_ae_indicator f D n hnonneg)

theorem inner_translatedComponentProfile_eq_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (translatedComponentProfile f D m hnonneg)
      (translatedComponentProfile f D n hnonneg) = 0 := by
  change inner ℝ (translatedComponentProfile f D m hnonneg).value
      (translatedComponentProfile f D n hnonneg).value +
      inner ℝ (translatedComponentProfile f D m hnonneg).weakDeriv
        (translatedComponentProfile f D n hnonneg).weakDeriv = 0
  rw [inner_value_translatedComponentProfile_eq_zero f D hnonneg hmn,
    inner_weakDeriv_translatedComponentProfile_eq_zero f D hnonneg hmn,
    add_zero]

theorem norm_value_componentRestrictionProfile_sq_eq_integral
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(componentRestrictionProfile f D n hnonneg).value‖ ^ 2 =
      ∫ x in D.component n, f.continuousRep x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_indicator (D.isOpen_component n).measurableSet]
  apply integral_congr_ae
  filter_upwards [value_componentRestrictionProfile_ae_indicator f D n hnonneg] with x hx
  rw [hx, Real.inner_apply]
  by_cases h : x ∈ D.component n <;> simp [Set.indicator, h, pow_two]

theorem norm_weakDeriv_componentRestrictionProfile_sq_eq_integral
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(componentRestrictionProfile f D n hnonneg).weakDeriv‖ ^ 2 =
      ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_indicator (D.isOpen_component n).measurableSet]
  apply integral_congr_ae
  filter_upwards [weakDeriv_componentRestrictionProfile_ae_indicator f D n hnonneg] with x hx
  rw [hx, Real.inner_apply]
  by_cases h : x ∈ D.component n <;> simp [Set.indicator, h, pow_two]

theorem norm_translatedComponentProfile_sq_eq_component_integrals
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖translatedComponentProfile f D n hnonneg‖ ^ 2 =
      (∫ x in D.component n, f.continuousRep x ^ 2) +
        ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2 := by
  rw [norm_sq_translatedComponentProfile]
  rw [(componentRestrictionProfile f D n hnonneg).norm_sq_eq,
    (componentRestrictionProfile f D n hnonneg).norm_valueOnHalfLine,
    (componentRestrictionProfile f D n hnonneg).norm_weakDerivOnHalfLine,
    norm_value_componentRestrictionProfile_sq_eq_integral,
    norm_weakDeriv_componentRestrictionProfile_sq_eq_integral]

theorem norm_sq_finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) :
    ‖finiteCompressedProfile f D hnonneg N‖ ^ 2 =
      Finset.sum (Finset.range N) (fun n =>
        ‖translatedComponentProfile f D n hnonneg‖ ^ 2) := by
  induction N with
  | zero => simp [finiteCompressedProfile]
  | succ N ih =>
    rw [finiteCompressedProfile_succ, norm_add_sq_real, ih]
    have hcross : inner ℝ (finiteCompressedProfile f D hnonneg N)
        (translatedComponentProfile f D N hnonneg) = 0 := by
      rw [finiteCompressedProfile]
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [real_inner_comm]
      exact inner_translatedComponentProfile_eq_zero f D hnonneg
        (Nat.ne_of_lt (Finset.mem_range.1 hi))
    rw [hcross, mul_zero]
    rw [Finset.sum_range_succ]
    ring

theorem norm_sq_sum_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (s : Finset ℕ) :
    ‖Finset.sum s (fun n => translatedComponentProfile f D n hnonneg)‖ ^ 2 =
      Finset.sum s (fun n => ‖translatedComponentProfile f D n hnonneg‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, norm_add_sq_real, ih]
    have hcross : inner ℝ (Finset.sum s (fun n => translatedComponentProfile f D n hnonneg))
        (translatedComponentProfile f D a hnonneg) = 0 := by
      rw [real_inner_comm, inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact inner_translatedComponentProfile_eq_zero f D hnonneg (by
        intro hia
        subst a
        exact ha hi)
    rw [real_inner_comm, hcross, mul_zero, Finset.sum_insert ha]
    ring

theorem finiteCompressedProfile_sub_eq_tail_sum
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N M : ℕ} (hNM : N ≤ M) :
    finiteCompressedProfile f D hnonneg M - finiteCompressedProfile f D hnonneg N =
      Finset.sum ((Finset.range M).filter (N ≤ ·))
        (fun n => translatedComponentProfile f D n hnonneg) := by
  rw [finiteCompressedProfile, finiteCompressedProfile]
  exact Finset.sum_range_sub_sum_range hNM

theorem norm_sq_finiteCompressedProfile_sub
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N M : ℕ} (hNM : N ≤ M) :
    ‖finiteCompressedProfile f D hnonneg M - finiteCompressedProfile f D hnonneg N‖ ^ 2 =
      Finset.sum ((Finset.range M).filter (N ≤ ·))
        (fun n => ‖translatedComponentProfile f D n hnonneg‖ ^ 2) := by
  rw [finiteCompressedProfile_sub_eq_tail_sum f D hnonneg hNM]
  exact norm_sq_sum_translatedComponentProfile f D hnonneg _

theorem summable_norm_sq_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    Summable (fun n => ‖translatedComponentProfile f D n hnonneg‖ ^ 2) := by
  have hv := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    (f.continuousRep_sq_integrable.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hd := MeasureTheory.hasSum_integral_iUnion
    (fun n => (D.isOpen_component n).measurableSet)
    (fun m n hmn => D.pairwiseDisjoint hmn)
    ((Lp.memLp f.weakDeriv).integrable_sq.integrableOn.mono_set
      (iUnion_subset fun n => D.subset n))
  have hv' : Summable (fun n => ∫ x in D.component n, f.continuousRep x ^ 2) := hv.summable
  have hd' : Summable (fun n => ∫ x in D.component n, ((f.weakDeriv : ℝ → ℝ) x) ^ 2) := hd.summable
  exact (hv'.add hd').congr (fun n =>
    (norm_translatedComponentProfile_sq_eq_component_integrals f D n hnonneg).symm)

theorem summable_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    Summable (fun n => translatedComponentProfile f D n hnonneg) := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hsq := (summable_norm_sq_translatedComponentProfile f D hnonneg)
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hsq) (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨s, fun t ht => ?_⟩
  have hsum := hs t ht
  have hsum' : ‖Finset.sum t (fun n => translatedComponentProfile f D n hnonneg)‖ ^ 2 < ε ^ 2 := by
    calc
      _ = Finset.sum t (fun n => ‖translatedComponentProfile f D n hnonneg‖ ^ 2) :=
        norm_sq_sum_translatedComponentProfile f D hnonneg t
      _ < ε ^ 2 := by
        have hnonneg_sum : 0 ≤ Finset.sum t (fun i => ‖translatedComponentProfile f D i hnonneg‖ ^ 2) :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg_sum] using hsum
  have hnonneg' : 0 ≤ ‖Finset.sum t (fun n => translatedComponentProfile f D n hnonneg)‖ :=
    norm_nonneg _
  nlinarith [sq_nonneg ‖Finset.sum t (fun n => translatedComponentProfile f D n hnonneg)‖]

def compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) : HalfLineH1 :=
  ∑' n, translatedComponentProfile f D n hnonneg

theorem hasSum_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    HasSum (fun n => translatedComponentProfile f D n hnonneg)
      (compressedProfile f D hnonneg) := by
  exact (summable_translatedComponentProfile f D hnonneg).hasSum

theorem tendsto_finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    Tendsto (finiteCompressedProfile f D hnonneg) atTop
      (𝓝 (compressedProfile f D hnonneg)) := by
  change Tendsto (fun N => Finset.sum (Finset.range N)
    (fun n => translatedComponentProfile f D n hnonneg)) atTop
      (𝓝 (compressedProfile f D hnonneg))
  simpa only [compressedProfile] using
    (hasSum_translatedComponentProfile f D hnonneg).tendsto_sum_nat

theorem cauchySeq_finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    CauchySeq (finiteCompressedProfile f D hnonneg) := by
  exact (tendsto_finiteCompressedProfile f D hnonneg).cauchySeq

theorem tendsto_continuousRep_finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (y : ℝ) :
    Tendsto (fun N => (finiteCompressedProfile f D hnonneg N).continuousRep y) atTop
      (𝓝 ((compressedProfile f D hnonneg).continuousRep y)) := by
  apply HalfLineH1.tendsto_continuousRep_of_tendsto_inner
  intro w
  have hc : Continuous (fun u : HalfLineH1 => inner ℝ u w) :=
    continuous_id.inner continuous_const
  exact (hc.continuousAt.tendsto.comp (tendsto_finiteCompressedProfile f D hnonneg))

@[simp] theorem continuousRep_compressedProfile_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (compressedProfile f D hnonneg).continuousRep 0 = 0 := by
  exact (compressedProfile f D hnonneg).continuousRep_zero

theorem compressedProfile_nonnegative
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ∀ y ∈ Ici 0, 0 ≤ (compressedProfile f D hnonneg).continuousRep y := by
  intro y hy
  exact ge_of_tendsto' (tendsto_continuousRep_finiteCompressedProfile f D hnonneg y)
    (fun N => finiteCompressedProfile_nonnegative f D hnonneg N y hy)

theorem continuousRep_compressedProfile_compressionMap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {n z} (hz : z ∈ D.component n) :
    (compressedProfile f D hnonneg).continuousRep (f.compressionMap z) = f.continuousRep z := by
  have hlim := tendsto_continuousRep_finiteCompressedProfile f D hnonneg
    (f.compressionMap z)
  have hfinite : Tendsto (fun N =>
      (finiteCompressedProfile f D hnonneg N).continuousRep (f.compressionMap z)) atTop
      (𝓝 (f.continuousRep z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1 : ℕ)] with N hN
    exact (continuousRep_finiteCompressedProfile_compressionMap f D hnonneg hN hz).symm
  exact tendsto_nhds_unique hlim hfinite

theorem continuousRep_compressedProfile_eq_zero_of_not_mem_iUnion
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {y : ℝ} (hy0 : y ∈ Ici 0)
    (hy : y ∉ ⋃ n, translatedComponent f D n) :
    (compressedProfile f D hnonneg).continuousRep y = 0 := by
  have hfinite : Tendsto (fun N =>
      (finiteCompressedProfile f D hnonneg N).continuousRep y) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℕ)] with N hN
    exact (continuousRep_finiteCompressedProfile_eq_zero_of_not_mem f D hnonneg hy0
      (by
        intro n hn hyn
        exact hy (mem_iUnion.2 ⟨n, hyn⟩))).symm
  exact tendsto_nhds_unique
    (tendsto_continuousRep_finiteCompressedProfile f D hnonneg y) hfinite

theorem norm_sq_compressedProfile_eq_tsum
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖compressedProfile f D hnonneg‖ ^ 2 =
      ∑' n, ‖translatedComponentProfile f D n hnonneg‖ ^ 2 := by
  have hl : Tendsto (fun N => ‖finiteCompressedProfile f D hnonneg N‖ ^ 2) atTop
      (𝓝 (‖compressedProfile f D hnonneg‖ ^ 2)) :=
    (tendsto_finiteCompressedProfile f D hnonneg).norm.pow 2
  have hr := (summable_norm_sq_translatedComponentProfile f D hnonneg).hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hl
  simpa only [norm_sq_finiteCompressedProfile f D hnonneg] using hr

end RayleighKernel.Analysis.HalfLineH1
