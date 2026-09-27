import RayleighKernel.Compression.Range
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

namespace RayleighKernel

open Set MeasureTheory

theorem volume_image_eq_zero_of_lipschitzWith
    {K : NNReal} {F : ℝ → ℝ} (hF : LipschitzWith K F) {s : Set ℝ}
    (hs : volume s = 0) : volume (F '' s) = 0 := by
  have h := hF.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num) s
  rw [hausdorffMeasure_real] at h
  rw [hs] at h
  simpa using h

theorem volume_image_eq_zero_of_hasDerivWithinAt_zero
    {F : ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ x ∈ s, HasDerivWithinAt F 0 s x) :
    volume (F '' s) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (fun x hx ↦ (hF x hx).hasFDerivWithinAt)
  intro x hx
  simp

namespace Analysis.HalfLineH1

theorem measure_compressionMap_image_Ioi_diff_positivitySet_eq_zero
    (f : HalfLineH1) :
    volume (f.compressionMap '' (Ioi 0 \ f.positivitySet)) = 0 := by
  let good : Set ℝ := {x | HasDerivAt f.compressionMap
    (openSetIndicator f.positivitySet x) x}
  have hgood : volume goodᶜ = 0 := by
    exact (ae_iff.mp f.compressionMap_ae_hasDerivAt)
  have hcomp : Ioi 0 \ f.positivitySet =
      ((Ioi 0 \ f.positivitySet) ∩ good) ∪
        ((Ioi 0 \ f.positivitySet) ∩ goodᶜ) := by
    ext x
    by_cases hx : x ∈ good <;> simp
  rw [hcomp, image_union]
  apply measure_union_null
  · apply volume_image_eq_zero_of_hasDerivWithinAt_zero
    intro x hx
    have hzero : openSetIndicator f.positivitySet x = 0 := by
      simp [openSetIndicator, hx.1.2]
    have hF : HasFDerivWithinAt f.compressionMap
        (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ))
        (Ioi 0 \ f.positivitySet ∩ good) x := by
      convert (hx.2.hasFDerivAt.hasFDerivWithinAt
        (s := Ioi 0 \ f.positivitySet ∩ good) :
        HasFDerivWithinAt f.compressionMap
          (ContinuousLinearMap.toSpanSingleton ℝ (openSetIndicator f.positivitySet x))
          (Ioi 0 \ f.positivitySet ∩ good) x) using 1
      simp [hzero]
    exact hF
  · apply volume_image_eq_zero_of_lipschitzWith f.compressionMap_lipschitzWith
    exact measure_mono_null inter_subset_right hgood

theorem compressionTarget_diff_iUnion_translatedComponent_measure_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) :
    volume (compressionTarget f \ ⋃ n, translatedComponent f D n) = 0 := by
  apply measure_mono_null ?_ (f.measure_compressionMap_image_Ioi_diff_positivitySet_eq_zero)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := f.compressionTarget_subset_range_Ioi hy.1
  have hxpos : x ∈ Ioi 0 := hx
  by_cases hxP : x ∈ f.positivitySet
  · have hymem : y ∈ ⋃ n, translatedComponent f D n := by
      rw [translatedComponent_iUnion f D]
      exact ⟨x, hxP, hxy⟩
    exact (hy.2 hymem).elim
  · exact ⟨x, ⟨hxpos, hxP⟩, hxy⟩

end Analysis.HalfLineH1

end RayleighKernel
