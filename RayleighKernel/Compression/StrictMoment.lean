import RayleighKernel.Compression.Pushforward

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

def compressionMomentDefect (f : HalfLineH1) (x : ℝ) : ℝ :=
  volume.real (f.positivitySetᶜ ∩ Ioc 0 x)

theorem compressionMomentDefect_nonneg (f : HalfLineH1) (x : ℝ) :
    0 ≤ f.compressionMomentDefect x := by
  exact measureReal_nonneg

theorem compressionMap_add_compressionMomentDefect (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    f.compressionMap x + f.compressionMomentDefect x = x := by
  rw [compressionMomentDefect, f.compressionMap_eq_measureReal_inter_Ioc hx]
  have h := measureReal_inter_add_sdiff (μ := (volume : Measure ℝ))
    (s := Ioc 0 x) f.isOpen_positivitySet.measurableSet (h := measure_Ioc_lt_top.ne)
  have hset : volume.real (f.positivitySet ∩ Ioc 0 x) +
      volume.real (f.positivitySetᶜ ∩ Ioc 0 x) = volume.real (Ioc 0 x) := by
    simpa [inter_comm, sdiff_eq, inter_assoc, and_assoc, and_left_comm, and_comm] using h
  rw [hset, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · simp
  · linarith

theorem sub_compressionMap_eq_compressionMomentDefect (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    x - f.compressionMap x = f.compressionMomentDefect x := by
  linarith [compressionMap_add_compressionMomentDefect f hx]

theorem integrableOn_compressionMomentDefect_mul_continuousRep
    (f : HalfLineH1)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    IntegrableOn (fun x => f.compressionMomentDefect x * f.continuousRep x) halfLine := by
  have hT := integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment
  have hdiff : IntegrableOn
      (fun x => x * f.continuousRep x - f.compressionMap x * f.continuousRep x) halfLine :=
    hmoment.sub hT
  apply hdiff.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [← sub_mul, sub_compressionMap_eq_compressionMomentDefect f hx]

theorem firstMoment_sub_compressedProfile_eq_integral_compressionMomentDefect
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    f.firstMoment - (compressedProfile f D hnonneg).firstMoment =
      ∫ x in f.positivitySet,
        f.compressionMomentDefect x * f.continuousRep x := by
  let hT := integrableOn_compressionMap_mul_continuousRep f hnonneg hmoment
  have hdef := integrableOn_compressionMomentDefect_mul_continuousRep f hnonneg hmoment
  have hdiff : (∫ x in halfLine, x * f.continuousRep x -
      f.compressionMap x * f.continuousRep x) =
      ∫ x in halfLine, f.compressionMomentDefect x * f.continuousRep x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    calc
      x * f.continuousRep x - f.compressionMap x * f.continuousRep x =
          (x - f.compressionMap x) * f.continuousRep x := by ring
      _ = f.compressionMomentDefect x * f.continuousRep x := by
        rw [sub_compressionMap_eq_compressionMomentDefect f hx]
  have hhalf : (∫ x in halfLine, f.compressionMomentDefect x * f.continuousRep x) =
      ∫ x in f.positivitySet, f.compressionMomentDefect x * f.continuousRep x := by
    calc
      (∫ x in halfLine, f.compressionMomentDefect x * f.continuousRep x) =
          ∫ x, f.compressionMomentDefect x * f.continuousRep x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro x hx
          rw [f.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx), mul_zero])
      _ = ∫ x in f.positivitySet, f.compressionMomentDefect x * f.continuousRep x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro x hx
          by_cases hx0 : x ≤ 0
          · rw [f.continuousRep_eq_zero_of_nonpositive hx0, mul_zero]
          · have hf : f.continuousRep x = 0 :=
              le_antisymm (le_of_not_gt hx) (hnonneg x (le_of_not_ge hx0))
            rw [hf, mul_zero])).symm
  change RayleighKernel.firstMoment f.continuousRep -
      RayleighKernel.firstMoment (compressedProfile f D hnonneg).continuousRep = _
  change f.firstMoment - (compressedProfile f D hnonneg).firstMoment = _
  rw [firstMoment_compressedProfile_eq_integral_compressionMap_mul f D hnonneg hint hmoment]
  change (∫ x in halfLine, x * f.continuousRep x) -
      (∫ x in halfLine, f.compressionMap x * f.continuousRep x) = _
  rw [← integral_sub hmoment hT, hdiff, hhalf]

theorem compressionMomentDefect_mono (f : HalfLineH1) {x y : ℝ} (hxy : x ≤ y) :
    f.compressionMomentDefect x ≤ f.compressionMomentDefect y := by
  have hfinite : volume (f.positivitySetᶜ ∩ Ioc 0 y) ≠ ∞ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  exact measureReal_mono (inter_subset_inter_right f.positivitySetᶜ
    (Ioc_subset_Ioc_right hxy)) hfinite

theorem firstMoment_compressedProfile_lt_iff_integral_compressionMomentDefect_pos
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    (compressedProfile f D hnonneg).firstMoment < f.firstMoment ↔
      0 < ∫ x in f.positivitySet,
        f.compressionMomentDefect x * f.continuousRep x := by
  rw [← sub_pos, firstMoment_sub_compressedProfile_eq_integral_compressionMomentDefect
    f D hnonneg hint hmoment]

theorem firstMoment_compressedProfile_lt_of_gap_below_positive_mass
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    (hint : IntegrableOn f.continuousRep halfLine)
    (hmoment : IntegrableOn (fun x => x * f.continuousRep x) halfLine)
    {R : ℝ} (hR : 0 ≤ R)
    (hgap : 0 < volume.real (f.positivitySetᶜ ∩ Ioc 0 R))
    (hmassAbove : 0 < ∫ x in f.positivitySet ∩ Ioi R, f.continuousRep x) :
    (compressedProfile f D hnonneg).firstMoment < f.firstMoment := by
  apply (firstMoment_compressedProfile_lt_iff_integral_compressionMomentDefect_pos
    f D hnonneg hint hmoment).2
  let S : Set ℝ := f.positivitySet ∩ Ioi R
  let gap : ℝ := volume.real (f.positivitySetᶜ ∩ Ioc 0 R)
  have hSsub : S ⊆ f.positivitySet := inter_subset_left
  have hShalf : S ⊆ halfLine := hSsub.trans (positivitySet_subset_halfLine f)
  have hsourceS : IntegrableOn f.continuousRep S := hint.mono_set hShalf
  have hdef : IntegrableOn
      (fun x => f.compressionMomentDefect x * f.continuousRep x) halfLine :=
    integrableOn_compressionMomentDefect_mul_continuousRep f hnonneg hmoment
  have hdefS : IntegrableOn
      (fun x => f.compressionMomentDefect x * f.continuousRep x) S :=
    hdef.mono_set hShalf
  have hleft : IntegrableOn (fun x => gap * f.continuousRep x) S :=
    hsourceS.const_mul gap
  have hpoint : ∀ᵐ x ∂(volume.restrict S),
      gap * f.continuousRep x ≤
      f.compressionMomentDefect x * f.continuousRep x := by
    filter_upwards [ae_restrict_mem
      (f.isOpen_positivitySet.measurableSet.inter measurableSet_Ioi)]
      with x hx
    have hxR : R ≤ x := le_of_lt hx.2
    have hx0 : 0 ≤ x := le_trans hR hxR
    have hdefR : gap ≤ f.compressionMomentDefect x := by
      exact le_trans (by rfl) (compressionMomentDefect_mono f hxR)
    exact mul_le_mul_of_nonneg_right hdefR (hnonneg x hx0)
  have htail : 0 < ∫ x in S,
      f.compressionMomentDefect x * f.continuousRep x := by
    have hmono := setIntegral_mono_ae_restrict hleft hdefS hpoint
    have hconst : (∫ x in S, gap * f.continuousRep x) = gap *
        (∫ x in S, f.continuousRep x) := by
      rw [integral_const_mul]
    rw [hconst] at hmono
    exact lt_of_lt_of_le (by simpa [gap, S] using mul_pos hgap hmassAbove) hmono
  exact lt_of_lt_of_le htail (setIntegral_mono_set
    (hdef.mono_set (positivitySet_subset_halfLine f))
    (Filter.Eventually.of_forall (fun x => by
      by_cases hx0 : x ≤ 0
      · change 0 ≤ f.compressionMomentDefect x * f.continuousRep x
        rw [f.continuousRep_eq_zero_of_nonpositive hx0, mul_zero]
      · exact mul_nonneg (compressionMomentDefect_nonneg f x)
          (hnonneg x (le_of_not_ge hx0))))
    (Filter.Eventually.of_forall hSsub))

end RayleighKernel.Analysis.HalfLineH1
