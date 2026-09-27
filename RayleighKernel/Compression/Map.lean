import RayleighKernel.Compression.PositivityComponents
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section

namespace RayleighKernel

open Set MeasureTheory

/-- The indicator of an open set, viewed as a real-valued integrand. -/
def openSetIndicator (s : Set ℝ) (x : ℝ) : ℝ := s.indicator (fun _ ↦ 1) x

theorem measurable_openSetIndicator {s : Set ℝ} (hs : IsOpen s) :
    Measurable (openSetIndicator s) := by
  exact measurable_const.indicator hs.measurableSet

theorem integrableOn_openSetIndicator {s : Set ℝ} (hs : IsOpen s) {a b : ℝ} :
    IntegrableOn (openSetIndicator s) (uIoc a b) := by
  apply IntegrableOn.of_bound (μ := volume) (s := uIoc a b)
    (by
       rcases le_total a b with hab | hba
       · rw [uIoc_of_le hab]
         exact measure_Ioc_lt_top
       · rw [uIoc_of_ge hba]
         exact measure_Ioc_lt_top)
    (measurable_openSetIndicator hs).aestronglyMeasurable 1
  filter_upwards with x
  by_cases hx : x ∈ s <;> simp [openSetIndicator, hx]

theorem intervalIntegrable_openSetIndicator {s : Set ℝ} (hs : IsOpen s) (a b : ℝ) :
    IntervalIntegrable (openSetIndicator s) volume a b := by
  rw [intervalIntegrable_iff]
  exact integrableOn_openSetIndicator hs

/-- Cumulative length of an open subset of the real line, measured from the origin. -/
def cumulativeLength (s : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, openSetIndicator s t

namespace cumulativeLength

variable {s : Set ℝ} (hs : IsOpen s)

theorem eq_intervalIntegral (x : ℝ) :
    cumulativeLength s x = ∫ t in (0 : ℝ)..x, openSetIndicator s t := rfl

theorem monotone (hs : IsOpen s) : Monotone (cumulativeLength s) := by
  intro x y hxy
  rw [cumulativeLength, cumulativeLength]
  have hsub := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_openSetIndicator hs 0 y)
    (intervalIntegrable_openSetIndicator hs 0 x)
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) hxy (fun t ↦ by
    simpa [openSetIndicator] using
      (Set.indicator_nonneg (s := s) (f := fun _ : ℝ ↦ (1 : ℝ))
        (fun _ _ ↦ by norm_num) t))
  have hnon' : 0 ≤ (∫ t in (0 : ℝ)..y, openSetIndicator s t) -
      ∫ t in (0 : ℝ)..x, openSetIndicator s t := hsub.symm ▸ hnon
  exact sub_nonneg.mp hnon'

theorem absolutelyContinuousOnInterval (hs : IsOpen s) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (cumulativeLength s) a b := by
  let F : ℝ → ℝ := fun x => ∫ v in a..x, openSetIndicator s v
  have hF := (intervalIntegrable_openSetIndicator hs a b).absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ =>
      ∫ v in 0..a, openSetIndicator s v) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hadd := hF.add hconst
  apply hadd.congr
  intro x hx
  change (∫ v in a..x, openSetIndicator s v) + ∫ v in 0..a, openSetIndicator s v = _
  rw [cumulativeLength]
  have h := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_openSetIndicator hs 0 x)
    (intervalIntegrable_openSetIndicator hs 0 a)
  linarith

theorem continuousOn (hs : IsOpen s) (a b : ℝ) : ContinuousOn (cumulativeLength s) (uIcc a b) := by
  exact (absolutelyContinuousOnInterval hs a b).continuousOn

theorem ae_hasDerivAt (hs : IsOpen s) :
    ∀ᵐ x, HasDerivAt (cumulativeLength s) (openSetIndicator s x) x := by
  have hi : LocallyIntegrable (openSetIndicator s) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    apply IntegrableOn.of_bound (μ := volume) (s := K) hK.measure_lt_top
      (measurable_openSetIndicator hs).aestronglyMeasurable 1
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [openSetIndicator, hx]
  have hderiv := (LocallyIntegrable.ae_hasDerivAt_integral hi).mono fun x hx ↦ hx 0
  convert hderiv using 1
  funext x
  rfl

end cumulativeLength

namespace Analysis

def HalfLineH1.compressionMap (f : HalfLineH1) : ℝ → ℝ :=
  cumulativeLength f.positivitySet

namespace HalfLineH1

theorem compressionMap_eq_intervalIntegral (f : HalfLineH1) (x : ℝ) :
    f.compressionMap x = ∫ t in (0 : ℝ)..x,
      openSetIndicator f.positivitySet t := rfl

theorem compressionMap_monotone (f : HalfLineH1) :
    Monotone f.compressionMap := by
  exact cumulativeLength.monotone f.isOpen_positivitySet

theorem compressionMap_absolutelyContinuousOnInterval (f : HalfLineH1) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f.compressionMap a b := by
  exact cumulativeLength.absolutelyContinuousOnInterval f.isOpen_positivitySet a b

theorem compressionMap_continuousOn (f : HalfLineH1) (a b : ℝ) :
    ContinuousOn f.compressionMap (uIcc a b) := by
  exact cumulativeLength.continuousOn f.isOpen_positivitySet a b

theorem compressionMap_ae_hasDerivAt (f : HalfLineH1) :
    ∀ᵐ x, HasDerivAt f.compressionMap (openSetIndicator f.positivitySet x) x := by
  exact cumulativeLength.ae_hasDerivAt f.isOpen_positivitySet

theorem compressionMap_eq_zero_of_nonpositive (f : HalfLineH1) {x : ℝ} (hx : x ≤ 0) :
    f.compressionMap x = 0 := by
  rw [compressionMap_eq_intervalIntegral]
  rw [intervalIntegral.integral_of_ge hx]
  have hpos : f.positivitySet ⊆ Ioi 0 := by
    intro z hz
    exact lt_of_not_ge fun hz0 ↦ hz.ne'
      (f.continuousRep_eq_zero_of_nonpositive hz0)
  have hz : (∫ t in x..0, openSetIndicator f.positivitySet t) = 0 := by
    rw [intervalIntegral.integral_of_le hx]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases ht' : t ∈ f.positivitySet
    · exact False.elim (not_lt_of_ge ht.2 (hpos ht'))
    · change f.positivitySet.indicator (fun _ ↦ (1 : ℝ)) t = (0 : ℝ)
      simp [ht']
  rw [intervalIntegral.integral_of_le hx] at hz
  rw [hz]
  simp

theorem compressionMap_nonneg_of_nonneg (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f.compressionMap x := by
  rw [compressionMap_eq_intervalIntegral]
  exact intervalIntegral.integral_nonneg_of_forall hx (fun t ↦ by
    by_cases ht : t ∈ f.positivitySet <;> simp [openSetIndicator, ht])

theorem compressionMap_le_self_of_nonneg (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    f.compressionMap x ≤ x := by
  rw [compressionMap_eq_intervalIntegral]
  calc
    (∫ t in (0 : ℝ)..x, openSetIndicator f.positivitySet t) ≤
        ∫ _t in (0 : ℝ)..x, (1 : ℝ) := by
          exact intervalIntegral.integral_mono_on hx
            (intervalIntegrable_openSetIndicator f.isOpen_positivitySet 0 x)
            intervalIntegrable_const (fun t _ht ↦ by
              by_cases ht' : t ∈ f.positivitySet <;> simp [openSetIndicator, ht'])
    _ = x := by simp [intervalIntegral.integral_const, smul_eq_mul]

theorem compressionMap_bounds_of_nonneg (f : HalfLineH1) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f.compressionMap x ∧ f.compressionMap x ≤ x :=
  ⟨f.compressionMap_nonneg_of_nonneg hx, f.compressionMap_le_self_of_nonneg hx⟩

theorem compressionMap_sub_eq_sub_of_component
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    {x y : ℝ} (hx : x ∈ D.component n) (hy : y ∈ D.component n) :
    f.compressionMap y - f.compressionMap x = y - x := by
  rw [compressionMap_eq_intervalIntegral, compressionMap_eq_intervalIntegral,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_openSetIndicator f.isOpen_positivitySet 0 y)
      (intervalIntegrable_openSetIndicator f.isOpen_positivitySet 0 x)]
  have hxy : uIcc x y ⊆ D.component n :=
    (D.ordConnected_component n).uIcc_subset hx hy
  have hone : ∀ t ∈ uIoc x y, openSetIndicator f.positivitySet t = 1 := by
    intro t ht
    simp [openSetIndicator, D.subset n (hxy (Ioc_subset_Icc_self ht))]
  have hEq : (∫ t in x..y, openSetIndicator f.positivitySet t) =
      ∫ _t in x..y, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    exact hone t ht
  rw [hEq]
  simp [intervalIntegral.integral_const]

end HalfLineH1

end Analysis

end RayleighKernel
