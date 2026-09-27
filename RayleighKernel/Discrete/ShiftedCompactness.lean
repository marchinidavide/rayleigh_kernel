import RayleighKernel.Discrete.Compactness
import RayleighKernel.Analysis.HalfLineSobolevConverse
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open RayleighKernel.Analysis

def shiftedInterpolant (h : ℝ) (w : Kernel) (x : ℝ) : ℝ := interpolant h w (x - h)

theorem shiftedInterpolant_zero {h : ℝ} {w : Kernel} (_hh : 0 < h) :
    shiftedInterpolant h w 0 = 0 := by
  simp [shiftedInterpolant]

theorem shiftedInterpolant_eq_zero_of_nonpos {h : ℝ} {w : Kernel} (_hh : 0 < h)
    {x : ℝ} (hx : x ≤ 0) : shiftedInterpolant h w x = 0 := by
  rw [shiftedInterpolant, interpolant_of_le_neg h w]
  linarith

theorem continuous_shiftedInterpolant {h : ℝ} {w : Kernel} (hh : 0 < h) :
    Continuous (shiftedInterpolant h w) := by
  exact (continuous_interpolant (w := w) hh).comp
    (continuous_id.sub continuous_const)

private def rawRightSlope (h : ℝ) (w : Kernel) (x : ℝ) : ℝ :=
  if x < -h then 0 else if x < 0 then w 0 / h^2
  else let j := ⌊x / h⌋₊; (w (j+1)-w j)/h^2

private theorem hasDerivWithinAt_interpolant_Ici
    {h : ℝ} {w : Kernel} (hh : 0 < h) (x : ℝ) :
    HasDerivWithinAt (interpolant h w) (rawRightSlope h w x) (Ici x) x := by
  by_cases hx : x < -h
  · have hd : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ici x) x :=
      (hasDerivAt_const x 0).hasDerivWithinAt
    have hslope : rawRightSlope h w x = 0 := by simp [rawRightSlope, hx]
    rw [hslope]
    refine hd.congr_of_eventuallyEq (f₁ := interpolant h w) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with y hy hyupper
      exact interpolant_of_le_neg h w (le_of_lt hyupper)
    · have hxeq : interpolant h w x = (fun _ : ℝ => (0 : ℝ)) x := by
        simp [interpolant_of_le_neg h w (le_of_lt hx)]
      exact hxeq
  · by_cases hxeq : x = -h
    · let g : ℝ → ℝ := fun y => (y + h) * (w 0 / h^2)
      have hg : HasDerivAt g (w 0 / h^2) x := by
        convert ((hasDerivAt_id x).add_const h).mul_const (w 0 / h^2) using 1 <;>
          simp [g]
      have hd : HasDerivWithinAt g (w 0 / h^2) (Ici x) x := hg.hasDerivWithinAt
      have hslope : rawRightSlope h w x = w 0 / h^2 := by
        simp [rawRightSlope, hxeq, hh]
      rw [hslope]
      refine hd.congr_of_eventuallyEq (f₁ := interpolant h w) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show x < 0 by rw [hxeq]; linarith))]
          with y hy hyo
        change x ≤ y at hy
        rcases lt_or_eq_of_le hy with hlt | rfl
        · rw [hxeq] at hlt
          exact interpolant_neg_interval hh ⟨hlt, le_of_lt hyo⟩
        · rw [hxeq, interpolant_neg_node]
          simp [g]
      · have hbase : interpolant h w x = g x := by
          rw [hxeq, interpolant_neg_node]
          simp [g]
        exact hbase
    · by_cases hxneg : x < 0
      · have hxstrip : x ∈ Ioo (-h) 0 :=
          ⟨lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hxeq), hxneg⟩
        have hd : HasDerivWithinAt (interpolant h w) (w 0 / h^2) (Ici x) x :=
          (hasDerivAt_interpolant_neg (w := w) hh hxstrip).hasDerivWithinAt
        simpa [rawRightSlope, hx, hxneg] using hd
      · let j : ℕ := ⌊x / h⌋₊
        have hx0 : 0 ≤ x := le_of_not_gt hxneg
        have hfloor : x ∈ Ico ((j : ℝ) * h) ((j + 1 : ℕ) * h) := by
          constructor
          · exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hx0 hh.le))
          · have hf := Nat.lt_floor_add_one (x / h)
            norm_num [Nat.cast_add, add_mul] at hf ⊢
            simpa [j, Nat.cast_add, add_mul] using (div_lt_iff₀ hh).mp hf
        let g : ℝ → ℝ := fun y =>
          w j / h + (y - (j : ℝ) * h) * (w (j + 1) - w j) / h^2
        have hg : HasDerivAt g ((w (j + 1) - w j) / h^2) x := by
          convert (((hasDerivAt_id x).sub_const ((j : ℝ) * h)).mul_const
            ((w (j + 1) - w j) / h^2)).add_const (w j / h) using 1 <;>
            simp [g]
          ext y
          ring
        have hd : HasDerivWithinAt g ((w (j + 1) - w j) / h^2) (Ici x) x :=
          hg.hasDerivWithinAt
        have hslope : rawRightSlope h w x = (w (j + 1) - w j) / h^2 := by
          simp [rawRightSlope, hx, hxneg, j]
        rw [hslope]
        refine hd.congr_of_eventuallyEq (f₁ := interpolant h w) ?_ ?_
        · filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hfloor.2)] with y hy hyupper
          exact interpolant_cell hh j ⟨le_trans hfloor.1 hy, hyupper⟩
        · have hbase : interpolant h w x = g x := by
            rw [interpolant_cell hh j hfloor]
          exact hbase

private theorem rawRightSlope_norm_le
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (x : ℝ) :
    ‖rawRightSlope h w x‖ ≤ (differenceEnergy w + 1) / h^2 := by
  have hh := hw.h_pos
  have hdiff : ∀ j, |difference w j| ≤ differenceEnergy w + 1 := by
    intro j
    have hj : (difference w j)^2 ≤ differenceEnergy w := by
      rw [differenceEnergy]
      simpa using hw.summable_difference_sq.sum_le_tsum ({j})
        (fun k hk => sq_nonneg (difference w k))
    have hnon : 0 ≤ differenceEnergy w := hw.differenceEnergy_nonneg
    have habs : |difference w j| ^ 2 = (difference w j)^2 := sq_abs _
    nlinarith [sq_nonneg (|difference w j| - 1)]
  by_cases hx : x < -h
  · simp [rawRightSlope, hx]
    have hnon : 0 ≤ differenceEnergy w := hw.differenceEnergy_nonneg
    positivity
  by_cases hx0 : x < 0
  · have hslope : rawRightSlope h w x = w 0 / h ^ 2 := by
      simp [rawRightSlope, hx, hx0]
    rw [hslope, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hh)]
    exact div_le_div_of_nonneg_right
      (by simpa [difference_zero] using hdiff 0) (sq_nonneg h)
  · let j : ℕ := ⌊x / h⌋₊
    have hslope : rawRightSlope h w x = (w (j + 1) - w j) / h ^ 2 := by
      simp [rawRightSlope, hx, hx0, j]
    rw [hslope, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hh)]
    gcongr
    simpa [difference] using hdiff (j + 1)

private theorem hasDerivWithinAt_shiftedInterpolant_Ici
    {h : ℝ} {w : Kernel} (hh : 0 < h) (x : ℝ) :
    HasDerivWithinAt (shiftedInterpolant h w)
      (rawRightSlope h w (x - h)) (Ici x) x := by
  have hg : HasDerivAt (fun y : ℝ => y - h) 1 x :=
    (hasDerivAt_id x).sub_const h
  have hmap : MapsTo (fun y : ℝ => y - h) (Ici x) (Ici (x - h)) := by
    intro y hy
    exact sub_le_sub_right hy h
  have hc := (hasDerivWithinAt_interpolant_Ici (h := h) (w := w) hh (x - h))
  have hcomp := hc.comp x hg.hasDerivWithinAt hmap
  change HasDerivWithinAt (fun y : ℝ => interpolant h w (y - h))
    (rawRightSlope h w (x - h)) (Ici x) x
  simpa [Function.comp_def] using hcomp

theorem shiftedInterpolant_absolutelyContinuousOnInterval
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (R : ℝ) (hR : 0 < R) :
    AbsolutelyContinuousOnInterval (shiftedInterpolant h w) 0 R := by
  let C : NNReal := ⟨(differenceEnergy w + 1) / h^2,
    div_nonneg (by linarith [hw.differenceEnergy_nonneg]) (sq_nonneg h)⟩
  have hderiv : ∀ x ∈ Ico (0 : ℝ) R,
      HasDerivWithinAt (shiftedInterpolant h w)
        (rawRightSlope h w (x - h)) (Ici x) x := by
    intro x hx
    exact hasDerivWithinAt_shiftedInterpolant_Ici hw.h_pos x
  have hbound : ∀ x ∈ Ico (0 : ℝ) R,
      ‖rawRightSlope h w (x - h)‖ ≤ (C : ℝ) := by
    intro x hx
    exact rawRightSlope_norm_le hw (x - h)
  have hLip : LipschitzOnWith C (shiftedInterpolant h w) (Icc (0 : ℝ) R) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro a ha b hb
    rcases le_total a b with hab | hba
    · have hab' : ‖shiftedInterpolant h w b - shiftedInterpolant h w a‖ ≤
          (C : ℝ) * (b - a) := by
        have hderiv' : ∀ z ∈ Ico a b,
            HasDerivWithinAt (shiftedInterpolant h w)
              (rawRightSlope h w (z - h)) (Ici z) z := by
          intro z hz
          exact hderiv z ⟨le_trans ha.1 hz.1, lt_of_lt_of_le hz.2 hb.2⟩
        have hbound' : ∀ z ∈ Ico a b,
            ‖rawRightSlope h w (z - h)‖ ≤ (C : ℝ) := by
          intro z hz
          exact hbound z ⟨le_trans ha.1 hz.1, lt_of_lt_of_le hz.2 hb.2⟩
        exact norm_image_sub_le_of_norm_deriv_right_le_segment
          (a := a) (b := b)
          (continuous_shiftedInterpolant hw.h_pos).continuousOn hderiv' hbound' b
          ⟨hab, le_rfl⟩
      have hn : ‖a - b‖ = b - a := by
        rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hab)]
        linarith
      rw [hn]
      simpa [norm_sub_rev] using hab'
    · have hba' : ‖shiftedInterpolant h w a - shiftedInterpolant h w b‖ ≤
          (C : ℝ) * (a - b) := by
        have hderiv' : ∀ z ∈ Ico b a,
            HasDerivWithinAt (shiftedInterpolant h w)
              (rawRightSlope h w (z - h)) (Ici z) z := by
          intro z hz
          exact hderiv z ⟨le_trans hb.1 hz.1, lt_of_lt_of_le hz.2 ha.2⟩
        have hbound' : ∀ z ∈ Ico b a,
            ‖rawRightSlope h w (z - h)‖ ≤ (C : ℝ) := by
          intro z hz
          exact hbound z ⟨le_trans hb.1 hz.1, lt_of_lt_of_le hz.2 ha.2⟩
        exact norm_image_sub_le_of_norm_deriv_right_le_segment
          (a := b) (b := a)
          (continuous_shiftedInterpolant hw.h_pos).continuousOn hderiv' hbound' a
          ⟨hba, le_rfl⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hba)] using hba'
  apply (show LipschitzOnWith C (shiftedInterpolant h w) (uIcc (0 : ℝ) R) from ?_)
    |>.absolutelyContinuousOnInterval
  simpa [uIcc_of_le hR.le] using hLip

theorem shiftedInterpolant_deriv_eq (h : ℝ) (w : Kernel) (x : ℝ) :
    deriv (shiftedInterpolant h w) x = deriv (interpolant h w) (x - h) := by
  exact deriv_comp_sub_const (interpolant h w) h x

private theorem shiftedInterpolant_memLp_of_memLp
    {h : ℝ} {w : Kernel} (hv : MemLp (interpolant h w) 2 volume)
    (hd : MemLp (deriv (interpolant h w)) 2 volume) :
    MemLp (shiftedInterpolant h w) 2 volume ∧
      MemLp (deriv (shiftedInterpolant h w)) 2 volume := by
  have hm : MeasurePreserving (fun x : ℝ => x - h) volume volume :=
    measurePreserving_sub_right volume h
  have hv' : MemLp ((interpolant h w) ∘ (fun x : ℝ => x - h)) 2 volume :=
    hv.comp_measurePreserving hm
  have hd' : MemLp ((deriv (interpolant h w)) ∘ (fun x : ℝ => x - h)) 2 volume :=
    hd.comp_measurePreserving hm
  refine ⟨?_, ?_⟩
  · change MemLp ((interpolant h w) ∘ (fun x : ℝ => x - h)) 2 volume
    exact hv'
  · rw [show deriv (shiftedInterpolant h w) =
        (deriv (interpolant h w)) ∘ (fun x : ℝ => x - h) by
          funext x; exact shiftedInterpolant_deriv_eq h w x]
    exact hd'

theorem shiftedInterpolant_value_memLp_of_admissible
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    MemLp (shiftedInterpolant h w) 2 volume := by
  exact (shiftedInterpolant_memLp_of_memLp
    ((memLp_two_iff_integrable_sq
      ((continuous_interpolant hw.h_pos).aestronglyMeasurable)).2
      (integrable_sq_interpolant hw))
    ((memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_sq_deriv_interpolant hw))).1

theorem shiftedInterpolant_deriv_memLp_of_admissible
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    MemLp (deriv (shiftedInterpolant h w)) 2 volume := by
  exact (shiftedInterpolant_memLp_of_memLp
    ((memLp_two_iff_integrable_sq
      ((continuous_interpolant hw.h_pos).aestronglyMeasurable)).2
      (integrable_sq_interpolant hw))
    ((memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_sq_deriv_interpolant hw))).2

theorem shiftedInterpolant_ae_eq_zero_on_nonpositive
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    shiftedInterpolant h w =ᵐ[volume.restrict (Iic 0)] 0 := by
  apply (ae_restrict_iff' measurableSet_Iic).2
  filter_upwards with x hx
  exact shiftedInterpolant_eq_zero_of_nonpos hw.h_pos hx

private theorem shiftedInterpolant_deriv_eq_zero_of_neg
    {h : ℝ} {w : Kernel} (hh : 0 < h) {x : ℝ} (hx : x < 0) :
    deriv (shiftedInterpolant h w) x = 0 := by
  have heq : shiftedInterpolant h w =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact shiftedInterpolant_eq_zero_of_nonpos hh hy.le
  have hz : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  exact (hz.congr_of_eventuallyEq heq).deriv

theorem deriv_shiftedInterpolant_ae_eq_zero_on_nonpositive
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    deriv (shiftedInterpolant h w) =ᵐ[volume.restrict (Iic 0)] 0 := by
  apply (ae_restrict_iff' measurableSet_Iic).2
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
  intro hxi
  exact shiftedInterpolant_deriv_eq_zero_of_neg hw.h_pos (lt_of_le_of_ne hxi hx)

private theorem admissible_apply_le_one
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (j : ℕ) : w j ≤ 1 := by
  have hs := hw.summable.sum_le_tsum ({j}) (fun k hk => hw.nonnegative k)
  rw [show (∑ k ∈ ({j} : Finset ℕ), w k) = w j by simp] at hs
  calc w j ≤ mass w := by simpa [mass] using hs
       _ = 1 := hw.mass_eq

private theorem interpolant_le_inv
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (x : ℝ) :
    interpolant h w x ≤ h⁻¹ := by
  by_cases hx : x ≤ -h
  · rw [interpolant_of_le_neg h w hx]; exact inv_nonneg.mpr hw.h_pos.le
  by_cases hx0 : x ≤ 0
  · rw [interpolant_neg_interval hw.h_pos ⟨lt_of_not_ge hx, hx0⟩]
    have hbound : (x + h) * (w 0 / h ^ 2) ≤ (x + h) * (1 / h ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (admissible_apply_le_one hw 0) (by positivity))
        (by linarith)
    calc
      _ ≤ (x + h) * (1 / h ^ 2) := hbound
      _ ≤ h * (1 / h ^ 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = h⁻¹ := by field_simp [ne_of_gt hw.h_pos]
  let j : ℕ := ⌊x / h⌋₊
  have hmem : x ∈ Ico ((j : ℝ) * h) ((j + 1 : ℕ) * h) := by
    constructor
    · have hxpos : 0 ≤ x := le_of_not_ge hx0
      exact (le_div_iff₀ hw.h_pos).mp (Nat.floor_le (div_nonneg hxpos hw.h_pos.le))
    · have hf := Nat.lt_floor_add_one (x / h)
      norm_num [Nat.cast_add, add_mul] at hf ⊢
      simpa [j, Nat.cast_add, add_mul] using (div_lt_iff₀ hw.h_pos).mp hf
  rw [interpolant_cell hw.h_pos j hmem]
  have ha : 0 ≤ x - (j : ℝ) * h := by linarith [hmem.1]
  have hb : 0 ≤ ((j + 1 : ℕ) : ℝ) * h - x := by linarith [hmem.2]
  have heq : w j / h + (x - (j : ℝ) * h) * (w (j + 1) - w j) / h ^ 2 =
      (((j + 1 : ℕ) * h - x) * w j + (x - (j : ℝ) * h) * w (j + 1)) / h ^ 2 := by
    field_simp; norm_num [Nat.cast_add, add_mul]; ring
  rw [heq, div_le_iff₀ (sq_pos_of_pos hw.h_pos)]
  have hnum : (((j + 1 : ℕ) : ℝ) * h - x) * w j +
      (x - (j : ℝ) * h) * w (j + 1) ≤ h := by
    calc
      _ ≤ (((j + 1 : ℕ) : ℝ) * h - x) * 1 + (x - (j : ℝ) * h) * 1 := by
        gcongr <;> exact admissible_apply_le_one hw _
      _ = h := by norm_num [Nat.cast_add, add_mul]
  field_simp [ne_of_gt hw.h_pos]
  simpa [mul_comm] using hnum

private theorem abs_shiftedInterpolant_le_inv
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (x : ℝ) :
    |shiftedInterpolant h w x| ≤ h⁻¹ := by
  rw [shiftedInterpolant, abs_of_nonneg (interpolant_nonneg hw.h_pos hw.nonnegative _)]
  exact interpolant_le_inv hw _

private theorem tendsto_shiftedInterpolant_mul_schwartz_atTop
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (φ : SchwartzMap ℝ ℝ) :
    Tendsto (fun x => shiftedInterpolant h w x * φ x) atTop (𝓝 0) := by
  have hφ : Tendsto (fun x => ‖φ x‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_norm.comp ((φ.tendsto_cocompact).mono_left atTop_le_cocompact))
  have hbound : ∀ x, ‖shiftedInterpolant h w x * φ x‖ ≤ h⁻¹ * ‖φ x‖ := by
    intro x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_shiftedInterpolant_le_inv hw x) (norm_nonneg _)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _))
    (Eventually.of_forall hbound)
  simpa using (tendsto_const_nhds (x := h⁻¹)).mul hφ

private theorem setIntegral_Ioi_shiftedInterpolant_mul_schwartzDeriv_eq_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (φ : SchwartzMap ℝ ℝ) :
    (∫ x in Ioi (0 : ℝ),
      shiftedInterpolant h w x * deriv (φ : ℝ → ℝ) x) =
      - ∫ x in Ioi (0 : ℝ),
        deriv (shiftedInterpolant h w) x * φ x := by
  let F := shiftedInterpolant h w
  let q := deriv (shiftedInterpolant h w)
  have hF : MemLp F 2 volume := shiftedInterpolant_value_memLp_of_admissible hw
  have hq : MemLp q 2 volume := shiftedInterpolant_deriv_memLp_of_admissible hw
  have hφ : MemLp (φ : ℝ → ℝ) 2 volume := φ.memLp 2 volume
  have hφd : MemLp (deriv (φ : ℝ → ℝ)) 2 volume :=
    (SchwartzMap.derivCLM ℝ ℝ φ).memLp 2 volume
  have hleft : Integrable (F * deriv (φ : ℝ → ℝ)) volume := hF.integrable_mul hφd
  have hright : Integrable (q * (φ : ℝ → ℝ)) volume := hq.integrable_mul hφ
  have hparts : ∀ R : ℝ, 0 < R →
      ∫ x in (0 : ℝ)..R, F x * deriv (φ : ℝ → ℝ) x =
        F R * φ R - F 0 * φ 0 - ∫ x in (0 : ℝ)..R, q x * φ x := by
    intro R hR
    have hp := (shiftedInterpolant_absolutelyContinuousOnInterval hw R hR).integral_mul_deriv_eq_deriv_mul
      (ContDiffOn.absolutelyContinuousOnInterval (fun x _ =>
        (φ.contDiffAt 1).contDiffWithinAt))
    simpa [F, q] using hp
  have hlimL := intervalIntegral_tendsto_integral_Ioi 0 hleft.integrableOn tendsto_id
  have hlimR := intervalIntegral_tendsto_integral_Ioi 0 hright.integrableOn tendsto_id
  have hboundary : Tendsto (fun R : ℝ => F R * φ R) atTop (𝓝 0) :=
    tendsto_shiftedInterpolant_mul_schwartz_atTop hw φ
  have hzero : F 0 = 0 := shiftedInterpolant_zero hw.h_pos
  have ht : Tendsto (fun R : ℝ =>
      F R * φ R - F 0 * φ 0 - ∫ x in (0 : ℝ)..R, q x * φ x) atTop
      (𝓝 (-∫ x in Ioi (0 : ℝ), q x * φ x)) := by
    simpa [hzero] using hboundary.sub hlimR
  have hevent : (fun R : ℝ => ∫ x in (0 : ℝ)..R,
      F x * deriv (φ : ℝ → ℝ) x) =ᶠ[atTop]
      (fun R => F R * φ R - F 0 * φ 0 - ∫ x in (0 : ℝ)..R, q x * φ x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hparts R hR
  have hlimLneg := ht.congr' hevent.symm
  have hEq : (∫ x in Ioi (0 : ℝ), F x * deriv (φ : ℝ → ℝ) x) =
      - ∫ x in Ioi (0 : ℝ), q x * φ x :=
    tendsto_nhds_unique hlimL hlimLneg
  simpa [F, q] using hEq

private theorem integral_shiftedInterpolant_mul_schwartzDeriv_eq_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (φ : SchwartzMap ℝ ℝ) :
    (∫ x : ℝ, shiftedInterpolant h w x * deriv (φ : ℝ → ℝ) x) =
      - ∫ x : ℝ, deriv (shiftedInterpolant h w) x * φ x := by
  have hleft0 : shiftedInterpolant h w =ᵐ[volume.restrict (Iic 0)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change shiftedInterpolant h w x = 0
    exact shiftedInterpolant_eq_zero_of_nonpos hw.h_pos hx
  have hright0 : deriv (shiftedInterpolant h w) =ᵐ[volume.restrict (Iic 0)] 0 :=
     deriv_shiftedInterpolant_ae_eq_zero_on_nonpositive hw
  have hleftset := setIntegral_eq_integral_of_ae_compl_eq_zero
    (μ := volume) (s := Ioi 0) (f := shiftedInterpolant h w * deriv (φ : ℝ → ℝ)) (by
      filter_upwards [ae_imp_of_ae_restrict hleft0] with x hx hxs
      have hxle : x ≤ 0 := le_of_not_gt hxs
      simp [hx hxle])
  have hrightset := setIntegral_eq_integral_of_ae_compl_eq_zero
    (μ := volume) (s := Ioi 0) (f := deriv (shiftedInterpolant h w) * (φ : ℝ → ℝ)) (by
      filter_upwards [ae_imp_of_ae_restrict hright0] with x hx hxs
      have hxle : x ≤ 0 := le_of_not_gt hxs
      simp [hx hxle])
  have hleftset' : (∫ x in Ioi (0 : ℝ),
      shiftedInterpolant h w x * deriv (φ : ℝ → ℝ) x) =
      ∫ x : ℝ, shiftedInterpolant h w x * deriv (φ : ℝ → ℝ) x := by
    simpa [Pi.mul_apply] using hleftset
  have hrightset' : (∫ x in Ioi (0 : ℝ),
      deriv (shiftedInterpolant h w) x * φ x) =
      ∫ x : ℝ, deriv (shiftedInterpolant h w) x * φ x := by
    simpa [Pi.mul_apply] using hrightset
  rw [← hleftset', ← hrightset']
  exact setIntegral_Ioi_shiftedInterpolant_mul_schwartzDeriv_eq_neg hw φ

theorem shiftedInterpolant_weakDerivative_identity
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∀ φ : SchwartzMap ℝ ℝ,
      l2Pairing ((shiftedInterpolant_value_memLp_of_admissible hw).toLp
        (shiftedInterpolant h w)) (schwartzDeriv φ) =
      -l2Pairing ((shiftedInterpolant_deriv_memLp_of_admissible hw).toLp
        (deriv (shiftedInterpolant h w))) (schwartzValue φ) := by
  intro φ
  let hF := shiftedInterpolant_value_memLp_of_admissible hw
  let hq := shiftedInterpolant_deriv_memLp_of_admissible hw
  have hleft : l2Pairing (hF.toLp (shiftedInterpolant h w)) (schwartzDeriv φ) =
      ∫ x : ℝ, shiftedInterpolant h w x * deriv (φ : ℝ → ℝ) x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp,
      (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume] with x hx hφx
    simp [schwartzDeriv, schwartzValue, hx, hφx]
  have hright : l2Pairing (hq.toLp (deriv (shiftedInterpolant h w)))
      (schwartzValue φ) =
      ∫ x : ℝ, deriv (shiftedInterpolant h w) x * φ x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hq.coeFn_toLp, φ.coeFn_toLp 2 volume] with x hx hφx
    simp [schwartzValue, hx, hφx]
  rw [hleft, hright]
  exact integral_shiftedInterpolant_mul_schwartzDeriv_eq_neg hw φ

theorem shiftedInterpolant_representativeData
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Analysis.HalfLineRepresentativeData (shiftedInterpolant h w) := by
  refine ⟨shiftedInterpolant_zero hw.h_pos,
    shiftedInterpolant_absolutelyContinuousOnInterval hw,
    shiftedInterpolant_value_memLp_of_admissible hw,
    shiftedInterpolant_deriv_memLp_of_admissible hw,
    shiftedInterpolant_ae_eq_zero_on_nonpositive hw,
    deriv_shiftedInterpolant_ae_eq_zero_on_nonpositive hw,
    ?_⟩
  exact shiftedInterpolant_weakDerivative_identity hw

def shiftedInterpolantH1 {h L : ℝ} (w : Kernel) (hw : IsAdmissible h L w) :
    Analysis.HalfLineH1 :=
  Analysis.HalfLineH1.ofRepresentative (shiftedInterpolant h w)
    (shiftedInterpolant_representativeData hw)

theorem continuousRep_shiftedInterpolantH1
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    {x : ℝ} (hx : 0 ≤ x) :
    (shiftedInterpolantH1 w hw).continuousRep x = shiftedInterpolant h w x := by
  apply Analysis.HalfLineH1.continuousRep_ofRepresentative
  exact hx

theorem value_shiftedInterpolantH1
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).value =
      (shiftedInterpolant_value_memLp_of_admissible hw).toLp (shiftedInterpolant h w) := by
  exact Analysis.HalfLineH1.value_ofRepresentative _ _

theorem weakDeriv_shiftedInterpolantH1
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).weakDeriv =
      (shiftedInterpolant_deriv_memLp_of_admissible hw).toLp
        (deriv (shiftedInterpolant h w)) := by
  exact Analysis.HalfLineH1.weakDeriv_ofRepresentative _ _

theorem continuousRep_shiftedInterpolantH1_eq
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).continuousRep = shiftedInterpolant h w := by
  funext x
  by_cases hx : 0 ≤ x
  · exact continuousRep_shiftedInterpolantH1 hw hx
  · rw [(shiftedInterpolantH1 w hw).continuousRep_eq_zero_of_nonpositive
      (le_of_not_ge hx)]
    exact (shiftedInterpolant_eq_zero_of_nonpos hw.h_pos (le_of_not_ge hx)).symm

private theorem norm_shiftedInterpolantH1_value_sq {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ‖(shiftedInterpolantH1 w hw).value‖ ^ 2 = ∫ x, (shiftedInterpolant h w x)^2 := by
  rw [← Analysis.HalfLineH1.integral_continuousRep_sq_eq_norm_value_sq]
  apply integral_congr_ae
  rw [continuousRep_shiftedInterpolantH1_eq hw]

private theorem norm_shiftedInterpolantH1_weakDeriv_sq {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ‖(shiftedInterpolantH1 w hw).weakDeriv‖ ^ 2 = ∫ x, (deriv (shiftedInterpolant h w) x)^2 := by
  rw [← Analysis.HalfLineH1.integral_deriv_continuousRep_sq_eq_norm_weakDeriv_sq]
  have ha := Analysis.HalfLineH1.deriv_continuousRep_ae (shiftedInterpolantH1 w hw)
  have hb := Analysis.HalfLineH1.weakDeriv_ofRepresentative_ae_eq (shiftedInterpolant h w) (shiftedInterpolant_representativeData hw)
  apply integral_congr_ae
  filter_upwards [ha, hb] with x hax hbx
  rw [hax]
  have hx : (shiftedInterpolantH1 w hw).weakDeriv x = deriv (shiftedInterpolant h w) x := by simpa [shiftedInterpolantH1] using hbx
  rw [hx]

theorem integral_sq_shiftedInterpolant
    {h L : ℝ} {w : Kernel} (_hw : IsAdmissible h L w) :
    (∫ x, (shiftedInterpolant h w x)^2) = ∫ x, (interpolant h w x)^2 := by
  have hm : MeasurePreserving (fun x : ℝ => x - h) volume volume :=
    measurePreserving_sub_right volume h
  rw [show (fun x => (shiftedInterpolant h w x)^2) =
      (fun x => (interpolant h w (x - h))^2) by funext x; rfl]
  exact hm.integral_comp (MeasurableEquiv.subRight h).measurableEmbedding
    (fun x => (interpolant h w x)^2)

theorem integral_sq_deriv_shiftedInterpolant
    {h L : ℝ} {w : Kernel} (_hw : IsAdmissible h L w) :
    (∫ x, (deriv (shiftedInterpolant h w) x)^2) =
      ∫ x, (deriv (interpolant h w) x)^2 := by
  rw [show (fun x => (deriv (shiftedInterpolant h w) x)^2) =
      (fun x => (deriv (interpolant h w) (x - h))^2) by
        funext x; rw [shiftedInterpolant_deriv_eq]]
  have hm : MeasurePreserving (fun x : ℝ => x - h) volume volume :=
    measurePreserving_sub_right volume h
  exact hm.integral_comp (MeasurableEquiv.subRight h).measurableEmbedding
    (fun x => (deriv (interpolant h w) x)^2)

theorem norm_shiftedInterpolantH1_sq
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ‖shiftedInterpolantH1 w hw‖ ^ 2 = interpolantH1Energy h w := by
  rw [Analysis.HalfLineH1.norm_sq_eq,
    (shiftedInterpolantH1 w hw).norm_valueOnHalfLine,
    (shiftedInterpolantH1 w hw).norm_weakDerivOnHalfLine,
    norm_shiftedInterpolantH1_value_sq hw,
    norm_shiftedInterpolantH1_weakDeriv_sq hw,
    integral_sq_shiftedInterpolant hw,
    integral_sq_deriv_shiftedInterpolant hw]
  rfl

theorem norm_shiftedInterpolantH1_sq_le_of_scaled_rayleighQuotient_le
    {h L Q : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    ‖shiftedInterpolantH1 w hw‖ ^ 2 ≤ (1 + 4 * Q) + Q * (1 + 4 * Q) := by
  rw [norm_shiftedInterpolantH1_sq]
  exact interpolantH1Energy_le_of_scaled_rayleighQuotient_le hw hQ

theorem norm_shiftedInterpolantH1_le_add_one_of_interpolantH1Energy_le
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) {C : ℝ}
    (hC : 0 ≤ C) (henergy : interpolantH1Energy h w ≤ C) :
    ‖shiftedInterpolantH1 w hw‖ ≤ C + 1 := by
  have hnorm : ‖shiftedInterpolantH1 w hw‖ ^ 2 ≤ C := by
    rw [norm_shiftedInterpolantH1_sq hw]
    exact henergy
  have hnon : 0 ≤ ‖shiftedInterpolantH1 w hw‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖shiftedInterpolantH1 w hw‖ - 1)]

theorem exists_shiftedInterpolant_compact_subsequence_of_energy_le
    {h : ℕ → ℝ} {L C : ℝ} {w : ℕ → Kernel}
    (hC : 0 ≤ C) (hw : ∀ n, IsAdmissible (h n) L (w n))
    (henergy : ∀ n, interpolantH1Energy (h n) (w n) ≤ C) :
    ∃ (ns : ℕ → ℕ) (v : Analysis.HalfLineH1), StrictMono ns ∧
      ‖v‖ ≤ C + 1 ∧
      (∀ z : Analysis.HalfLineH1,
        Tendsto (fun n ↦ inner ℝ (shiftedInterpolantH1 (w (ns n)) (hw (ns n))) z)
          atTop (𝓝 (inner ℝ v z))) ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn
            (fun n ↦ shiftedInterpolant (h (ns n)) (w (ns n)))
            v.continuousRep atTop K ∧
        Tendsto
          (fun n ↦ ∫ x in K,
            (shiftedInterpolant (h (ns n)) (w (ns n)) x - v.continuousRep x) ^ 2)
          atTop (𝓝 0) := by
  let u : ℕ → Analysis.HalfLineH1 :=
    fun n ↦ shiftedInterpolantH1 (w n) (hw n)
  have hu : ∀ n, ‖u n‖ ≤ C + 1 := by
    intro n
    exact norm_shiftedInterpolantH1_le_add_one_of_interpolantH1Energy_le
      (hw n) hC (henergy n)
  obtain ⟨ns, v, hns, hv, hweak, hlocal⟩ :=
    Analysis.HalfLineH1.exists_weakly_and_locally_uniformly_convergent_subsequence
      (by linarith) hu
  refine ⟨ns, v, hns, hv, hweak, ?_⟩
  intro K hK
  obtain ⟨hunif, hsq⟩ := hlocal K hK
  have heq : (fun n ↦ (u (ns n)).continuousRep) =
      (fun n ↦ shiftedInterpolant (h (ns n)) (w (ns n))) := by
    funext n
    exact continuousRep_shiftedInterpolantH1_eq (hw (ns n))
  refine ⟨?_, ?_⟩
  · convert hunif using 1
    exact heq.symm
  · convert hsq using 1
    funext n
    congr 1
    funext x
    rw [congrFun heq.symm n]

theorem exists_shiftedInterpolant_compact_subsequence_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n,
      ((mesh n)⁻¹)^2 * rayleighQuotient (w n) ≤
        scaledDiscreteMinimum (mesh n) L + eps n) :
    ∃ (ns : ℕ → ℕ) (v : Analysis.HalfLineH1) (C : ℝ), StrictMono ns ∧
      0 ≤ C ∧ ‖v‖ ≤ C + 1 ∧
      (∀ z : Analysis.HalfLineH1,
        Tendsto (fun n ↦ inner ℝ (shiftedInterpolantH1 (w (ns n)) (hw (ns n))) z)
          atTop (𝓝 (inner ℝ v z))) ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn
            (fun n ↦ shiftedInterpolant (mesh (ns n)) (w (ns n)))
            v.continuousRep atTop K ∧
        Tendsto
          (fun n ↦ ∫ x in K,
            (shiftedInterpolant (mesh (ns n)) (w (ns n)) x - v.continuousRep x) ^ 2)
          atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := eventually_interpolantH1Energy_le_of_nearMinimizer
    L hL hmesh heps hw hnear
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hbound)
  let h' : ℕ → ℝ := fun n ↦ mesh (N + n)
  let w' : ℕ → Kernel := fun n ↦ w (N + n)
  have hw' : ∀ n, IsAdmissible (h' n) L (w' n) := by
    intro n
    exact hw (N + n)
  have henergy' : ∀ n, interpolantH1Energy (h' n) (w' n) ≤ C := by
    intro n
    exact hN (N + n) (by omega)
  obtain ⟨ns, v, hns, hv, hweak, hlocal⟩ :=
    exists_shiftedInterpolant_compact_subsequence_of_energy_le hC hw' henergy'
  let ns' : ℕ → ℕ := fun n ↦ N + ns n
  refine ⟨ns', v, C, ?_, hC, hv, ?_, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_left (hns hab) N
  · intro z
    simpa [ns', w', hw', h'] using hweak z
  · intro K hK
    obtain ⟨hunif, hsq⟩ := hlocal K hK
    have heq : (fun n ↦ (shiftedInterpolantH1 (w' (ns n)) (hw' (ns n))).continuousRep) =
        (fun n ↦ shiftedInterpolant (h' (ns n)) (w' (ns n))) := by
      funext n
      exact continuousRep_shiftedInterpolantH1_eq (hw' (ns n))
    refine ⟨?_, ?_⟩
    · convert hunif using 1
    · convert hsq using 1

private theorem shifted_integrable {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Integrable (shiftedInterpolant h w) := by
  have hi := integrable_interpolant_of_summable hw.h_pos hw.nonnegative hw.summable
  rw [show shiftedInterpolant h w = (interpolant h w) ∘ (fun x : ℝ => x - h) by
    funext x; rfl]
  exact (measurePreserving_sub_right volume h).integrable_comp_of_integrable hi

private theorem shifted_weighted_integrable {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Integrable (fun x => x * shiftedInterpolant h w x) := by
  have hg : Integrable (fun y => y * interpolant h w y) := integrable_mul_interpolant hw
  have hi := shifted_integrable hw
  have hcompg : Integrable ((fun y : ℝ => y * interpolant h w y) ∘ (fun x : ℝ => x - h)) :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hg
  have hcompi : Integrable ((interpolant h w) ∘ (fun x : ℝ => x - h)) := by
    exact (measurePreserving_sub_right volume h).integrable_comp_of_integrable
      (integrable_interpolant_of_summable hw.h_pos hw.nonnegative hw.summable)
  rw [show (fun x : ℝ => x * shiftedInterpolant h w x) =
      (fun x => x * interpolant h w (x - h)) by funext x; rfl]
  have hadd : Integrable
      (fun x : ℝ => ((x - h) * interpolant h w (x - h)) + h * interpolant h w (x - h)) :=
    hcompg.add (hcompi.const_mul h)
  apply hadd.congr
  filter_upwards [] with x
  ring

private theorem shifted_integral_eq_whole {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    (∫ x in halfLine, shiftedInterpolant h w x) = ∫ x, shiftedInterpolant h w x := by
  have hzero : shiftedInterpolant h w =ᵐ[volume.restrict (Iic 0)] 0 :=
    shiftedInterpolant_ae_eq_zero_on_nonpositive hw
  have hs := setIntegral_eq_integral_of_ae_compl_eq_zero
    (μ := volume) (s := halfLine) (f := shiftedInterpolant h w) (by
      filter_upwards [ae_imp_of_ae_restrict hzero] with x hx hxs
      change ¬ 0 ≤ x at hxs
      exact shiftedInterpolant_eq_zero_of_nonpos (w := w) hw.h_pos (le_of_not_ge hxs))
  exact hs

private theorem shifted_weighted_integral_eq_whole {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    (∫ x in halfLine, x * shiftedInterpolant h w x) =
      ∫ x, x * shiftedInterpolant h w x := by
  have hzero : shiftedInterpolant h w =ᵐ[volume.restrict (Iic 0)] 0 :=
    shiftedInterpolant_ae_eq_zero_on_nonpositive hw
  have hs := setIntegral_eq_integral_of_ae_compl_eq_zero
    (μ := volume) (s := halfLine) (f := fun x => x * shiftedInterpolant h w x) (by
      filter_upwards [ae_imp_of_ae_restrict hzero] with x hx hxs
      change ¬ 0 ≤ x at hxs
      rw [shiftedInterpolant_eq_zero_of_nonpos (w := w) hw.h_pos (le_of_not_ge hxs)]
      simp)
  exact hs

theorem shiftedInterpolant_nonnegative {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∀ x, 0 ≤ shiftedInterpolant h w x := by
  intro x
  exact interpolant_nonneg hw.h_pos hw.nonnegative (x - h)

theorem integrable_shiftedInterpolant {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Integrable (shiftedInterpolant h w) := shifted_integrable hw

theorem shiftedInterpolant_mass {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (∫ x in halfLine, shiftedInterpolant h w x) = 1 := by
  rw [shifted_integral_eq_whole hw]
  change (∫ x, (interpolant h w) (x - h)) = 1
  rw [(measurePreserving_sub_right volume h).integral_comp
    (MeasurableEquiv.subRight h).measurableEmbedding]
  exact hw.integral_interpolant

theorem integrable_mul_shiftedInterpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) : Integrable (fun x => x * shiftedInterpolant h w x) :=
  shifted_weighted_integrable hw

theorem shiftedInterpolant_firstMoment {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (∫ x in halfLine, x * shiftedInterpolant h w x) = L + h := by
  rw [shifted_weighted_integral_eq_whole hw]
  change (∫ x, x * interpolant h w (x - h)) = L + h
  have hi := integrable_mul_interpolant hw
  have hj := integrable_interpolant_of_summable hw.h_pos hw.nonnegative hw.summable
  have hcompg := (measurePreserving_sub_right volume h).integrable_comp_of_integrable hi
  have hcompi := (measurePreserving_sub_right volume h).integrable_comp_of_integrable hj
  have hrewrite : (fun x : ℝ => x * interpolant h w (x - h)) =
      (fun x => ((x - h) * interpolant h w (x - h)) + h * interpolant h w (x - h)) := by
    funext x; ring
  rw [hrewrite, integral_add]
  · rw [MeasureTheory.integral_const_mul]
    change (∫ x, ((fun y : ℝ => y * interpolant h w y) ∘ (fun x : ℝ => x - h)) x) +
      h * ∫ x, ((interpolant h w) ∘ (fun x : ℝ => x - h)) x = L + h
    simp only [Function.comp_apply]
    have hg' := (measurePreserving_sub_right volume h).integral_comp
      (MeasurableEquiv.subRight h).measurableEmbedding
      (fun x : ℝ => x * interpolant h w x)
    have hi' := (measurePreserving_sub_right volume h).integral_comp
      (MeasurableEquiv.subRight h).measurableEmbedding
      (interpolant h w)
    rw [hg', hi']
    rw [hw.integral_mul_interpolant, hw.integral_interpolant]
    ring
  · exact hcompg
  · exact hcompi.const_mul h

theorem mass_shiftedInterpolantH1 {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) : (shiftedInterpolantH1 w hw).mass = 1 := by
  rw [Analysis.HalfLineH1.mass, RayleighKernel.mass]
  rw [continuousRep_shiftedInterpolantH1_eq hw]
  exact shiftedInterpolant_mass hw

theorem firstMoment_shiftedInterpolantH1 {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) : (shiftedInterpolantH1 w hw).firstMoment = L + h := by
  rw [Analysis.HalfLineH1.firstMoment, RayleighKernel.firstMoment]
  rw [continuousRep_shiftedInterpolantH1_eq hw]
  exact shiftedInterpolant_firstMoment hw

theorem shiftedInterpolant_tailMass_le_firstMoment_div {h L R : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) (hR : 0 < R) :
    (∫ x in Ici R, shiftedInterpolant h w x) ≤ (L + h) / R := by
  have hsubset : Ici R ⊆ halfLine := fun x hx => le_trans hR.le hx
  have htail : IntegrableOn (shiftedInterpolant h w) (Ici R) :=
    (shifted_integrable hw).integrableOn.mono_set hsubset
  have hweighted : IntegrableOn (fun x => x * shiftedInterpolant h w x) (Ici R) :=
    (shifted_weighted_integrable hw).integrableOn.mono_set hsubset
  calc
    (∫ x in Ici R, shiftedInterpolant h w x) ≤
        ∫ x in Ici R, R⁻¹ * (x * shiftedInterpolant h w x) := by
      apply setIntegral_mono_ae_restrict htail (hweighted.const_mul R⁻¹)
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hn := shiftedInterpolant_nonnegative hw x
      calc
        shiftedInterpolant h w x = R⁻¹ * (R * shiftedInterpolant h w x) := by field_simp
        _ ≤ R⁻¹ * (x * shiftedInterpolant h w x) := by
          gcongr
          exact hx
    _ = R⁻¹ * ∫ x in Ici R, x * shiftedInterpolant h w x := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ R⁻¹ * ∫ x in halfLine, x * shiftedInterpolant h w x := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      apply setIntegral_mono_set (shifted_weighted_integrable hw).integrableOn
      · filter_upwards [ae_restrict_mem (μ := volume) (s := halfLine) measurableSet_Ici] with x hx
        exact mul_nonneg hx (shiftedInterpolant_nonnegative hw x)
      · exact Filter.Eventually.of_forall hsubset
    _ = R⁻¹ * (L + h) := by
      exact congrArg (fun z : ℝ => R⁻¹ * z) (shiftedInterpolant_firstMoment hw)
    _ = (L + h) / R := by rw [div_eq_mul_inv, mul_comm]

theorem shiftedInterpolant_nonnegative_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) :
    ∀ x ∈ halfLine, 0 ≤ v.continuousRep x := by
  intro x hx
  have hpoint : Tendsto (fun n ↦ shiftedInterpolant (mesh n) (w n) x) atTop
      (𝓝 (v.continuousRep x)) := by
    have h := (hunif {x} isCompact_singleton).tendsto_at (mem_singleton x)
    simpa only [continuousRep_shiftedInterpolantH1_eq] using h
  exact ge_of_tendsto' hpoint (fun n ↦ shiftedInterpolant_nonnegative (hw n) x)

theorem shiftedInterpolant_compact_mass_upper_bound_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) {R : ℝ} :
    (∫ x in Icc 0 R, v.continuousRep x) ≤ 1 := by
  let u : ℕ → Analysis.HalfLineH1 := fun n ↦ shiftedInterpolantH1 (w n) (hw n)
  have heq : ∀ n, (u n).continuousRep = shiftedInterpolant (mesh n) (w n) := by
    intro n; exact continuousRep_shiftedInterpolantH1_eq (hw n)
  have hlocal := Analysis.HalfLineH1.tendsto_setIntegral_continuousRep_of_tendstoUniformlyOn
    (u := u) (v := v) isCompact_Icc
      (by simpa only [heq] using hunif (Icc 0 R) isCompact_Icc)
  have hseq : ∀ n, (∫ x in Icc 0 R, (u n).continuousRep x) ≤ 1 := by
    intro n
    have hi : Integrable (u n).continuousRep := by
      rw [heq n]; exact integrable_shiftedInterpolant (hw n)
    have hm : (∫ x in halfLine, (u n).continuousRep x) = 1 := by
      rw [heq n]; exact shiftedInterpolant_mass (hw n)
    rw [← hm]
    apply setIntegral_mono_set hi.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [heq n]
      exact shiftedInterpolant_nonnegative (hw n) x
    · exact Filter.Eventually.of_forall (fun x hx ↦ hx.1)
  exact le_of_tendsto' hlocal hseq

theorem shiftedInterpolant_compact_mass_lower_bound_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) {R : ℝ} (hR : 0 < R) :
    1 - L / R ≤ ∫ x in Icc 0 R, v.continuousRep x := by
  let u : ℕ → Analysis.HalfLineH1 := fun n ↦ shiftedInterpolantH1 (w n) (hw n)
  have heq : ∀ n, (u n).continuousRep = shiftedInterpolant (mesh n) (w n) := by
    intro n; exact continuousRep_shiftedInterpolantH1_eq (hw n)
  have hlocal := Analysis.HalfLineH1.tendsto_setIntegral_continuousRep_of_tendstoUniformlyOn
    (u := u) (v := v) isCompact_Icc
      (by simpa only [heq] using hunif (Icc 0 R) isCompact_Icc)
  have hseq : ∀ n, 1 - (L + mesh n) / R ≤ ∫ x in Icc 0 R, (u n).continuousRep x := by
    intro n
    have hi : Integrable (u n).continuousRep := by
      rw [heq n]; exact integrable_shiftedInterpolant (hw n)
    have hmass : (∫ x in halfLine, (u n).continuousRep x) = 1 := by
      rw [heq n]; exact shiftedInterpolant_mass (hw n)
    have htail := shiftedInterpolant_tailMass_le_firstMoment_div (hw n) hR
    rw [← heq n] at htail
    have hsplit : (∫ x in Ico 0 R, (u n).continuousRep x) +
        ∫ x in Ici R, (u n).continuousRep x = 1 := by
      rw [← hmass]
      rw [← setIntegral_union (by
        apply Set.disjoint_left.mpr
        intro x hxs hxt
        exact (not_lt_of_ge hxt) hxs.2) measurableSet_Ici
        (hi.integrableOn.mono_set (by intro x hx; exact hx.1))
        (hi.integrableOn.mono_set (by intro x hx; exact le_trans hR.le hx))]
      rw [Ico_union_Ici_eq_Ici hR.le]
      simp [halfLine] at hmass ⊢
    have hIco : 1 - (L + mesh n) / R ≤ ∫ x in Ico 0 R, (u n).continuousRep x := by
      linarith
    simpa only [integral_Icc_eq_integral_Ico] using hIco
  have hleft : Tendsto (fun n => 1 - (L + mesh n) / R) atTop
      (𝓝 (1 - L / R)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (((tendsto_const_nhds (x := L)).add hmesh).mul
        (tendsto_const_nhds (x := R⁻¹)))
    convert h using 1 <;> simp [div_eq_mul_inv]
  exact le_of_tendsto_of_tendsto hleft hlocal (Filter.Eventually.of_forall hseq)

theorem shiftedInterpolant_integrableOn_continuousRep_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) : IntegrableOn v.continuousRep halfLine := by
  have hv := shiftedInterpolant_nonnegative_of_tendstoUniformlyOn hw hunif
  apply Analysis.HalfLineH1.integrableOn_continuousRep_of_nonnegative_of_compact_mass_le_one hv
  intro R hR
  exact shiftedInterpolant_compact_mass_upper_bound_of_tendstoUniformlyOn hw hunif

theorem mass_shiftedInterpolant_limit_of_tendstoUniformlyOn
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
        v.continuousRep atTop K) : v.mass = 1 := by
  have hv := shiftedInterpolant_nonnegative_of_tendstoUniformlyOn hw hunif
  have hint := shiftedInterpolant_integrableOn_continuousRep_of_tendstoUniformlyOn hw hunif
  have hmass_tendsto : Tendsto (fun R : ℝ ↦
      (∫ x in Icc 0 R, v.continuousRep x)) atTop (𝓝 v.mass) := by
    have hcover : AECover (volume.restrict halfLine) atTop
        (fun R : ℝ ↦ Icc 0 R) := by
      refine ⟨?_, fun R ↦ measurableSet_Icc⟩
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      filter_upwards [eventually_ge_atTop x] with R hR
      exact ⟨hx, hR⟩
    have h := hcover.integral_tendsto_of_countably_generated hint
    convert h using 1
    · ext R
      rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
    · rfl
  have hupper : v.mass ≤ 1 := by
    apply le_of_tendsto hmass_tendsto
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact shiftedInterpolant_compact_mass_upper_bound_of_tendstoUniformlyOn hw hunif
  have hleft : Tendsto (fun R : ℝ ↦ 1 - L / R) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := L)).mul tendsto_inv_atTop_zero)
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using h
  have hlower_mass : 1 ≤ v.mass := by
    apply le_of_tendsto_of_tendsto hleft hmass_tendsto
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact shiftedInterpolant_compact_mass_lower_bound_of_tendstoUniformlyOn hmesh hw hunif hR
  exact le_antisymm hupper hlower_mass

theorem shiftedInterpolantH1_isAdmissible {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).IsAdmissible (L + h) := by
  refine ⟨?_, ?_, ?_, mass_shiftedInterpolantH1 hw, firstMoment_shiftedInterpolantH1 hw⟩
  · intro x hx
    rw [continuousRep_shiftedInterpolantH1_eq hw]
    exact shiftedInterpolant_nonnegative hw x
  · rw [continuousRep_shiftedInterpolantH1_eq hw]
    exact integrable_shiftedInterpolant hw |>.integrableOn
  · rw [continuousRep_shiftedInterpolantH1_eq hw]
    exact integrable_mul_shiftedInterpolant hw |>.integrableOn

theorem shiftedInterpolant_tailSquareEnergy_le_of_norm_le
    {h L R B : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (hR : 0 < R)
    (hB : ‖shiftedInterpolantH1 w hw‖ ≤ B) :
    (∫ x in Ici R, shiftedInterpolant h w x ^ 2) ≤
      Real.sqrt (2 * B * B) * ((L + h) / R) := by
  let u := shiftedInterpolantH1 w hw
  have hu : u.IsAdmissible (L + h) := shiftedInterpolantH1_isAdmissible hw
  have ht := HalfLineH1.tailSquareEnergy_le_of_isAdmissible hu hR
  rw [continuousRep_shiftedInterpolantH1_eq hw] at ht
  have hprod : 2 * ‖u.value‖ * ‖u.weakDeriv‖ ≤ 2 * B * B := by
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
    have hv : ‖u.value‖ ≤ B := (HalfLineH1.norm_value_le u).trans hB
    have hd : ‖u.weakDeriv‖ ≤ B := (HalfLineH1.norm_weakDeriv_le u).trans hB
    nlinarith [mul_le_mul hv hd (norm_nonneg u.weakDeriv) hB0]
  have hsqrt := Real.sqrt_le_sqrt hprod
  have htail := shiftedInterpolant_tailMass_le_firstMoment_div hw hR
  have hroot : 0 ≤ Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := Real.sqrt_nonneg _
  have hfirst : 0 ≤ L + h := by
    rw [← hu.firstMoment_eq, HalfLineH1.firstMoment]
    exact setIntegral_nonneg measurableSet_Ici (fun x hx =>
      mul_nonneg hx (hu.nonnegative x hx))
  have htailnonneg : 0 ≤ (L + h) / R := div_nonneg hfirst hR.le
  exact ht.trans ((mul_le_mul_of_nonneg_left htail hroot).trans
    (mul_le_mul_of_nonneg_right hsqrt htailnonneg))

theorem shiftedInterpolant_tailSquareEnergy_le_of_norm_le_of_mesh_le_one
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L B R : ℝ}
    (hw : ∀ n, IsAdmissible (mesh n) L (w n)) (hB : ∀ n,
      ‖shiftedInterpolantH1 (w n) (hw n)‖ ≤ B) (hR : 0 < R)
    (hmesh : ∀ n, mesh n ≤ 1) (n : ℕ) :
    (∫ x in Ici R, shiftedInterpolant (mesh n) (w n) x ^ 2) ≤
      Real.sqrt (2 * B * B) * ((L + 1) / R) := by
  have ht := shiftedInterpolant_tailSquareEnergy_le_of_norm_le (hw n) hR (hB n)
  have hnon : 0 ≤ Real.sqrt (2 * B * B) := Real.sqrt_nonneg _
  have hRnon : 0 ≤ (L + mesh n) / R := by
    have hL : 0 ≤ L + mesh n := by
      have hu := shiftedInterpolantH1_isAdmissible (hw n)
      rw [← hu.firstMoment_eq, HalfLineH1.firstMoment]
      exact setIntegral_nonneg measurableSet_Ici (fun x hx =>
        mul_nonneg hx (hu.nonnegative x hx))
    exact div_nonneg hL (le_of_lt hR)
  apply ht.trans
  have hnum : L + mesh n ≤ L + 1 := by linarith [hmesh n]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hR.le) hnon

theorem shiftedInterpolant_squareEnergy_tendsto_of_global_continuousRep_sq_sub
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L : ℝ} {v : Analysis.HalfLineH1}
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hglobal : Tendsto (fun n ↦ ∫ x in halfLine,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, (interpolant (mesh n) (w n) x) ^ 2) atTop
      (𝓝 v.squareEnergy) := by
  have hsq := HalfLineH1.tendsto_squareEnergy_of_tendsto_global_continuousRep_sq_sub
    (u := fun n ↦ shiftedInterpolantH1 (w n) (hw n)) (v := v) (by
      simpa only [continuousRep_shiftedInterpolantH1_eq] using hglobal)
  have heq : ∀ n, (shiftedInterpolantH1 (w n) (hw n)).squareEnergy =
      (∫ x, (interpolant (mesh n) (w n) x) ^ 2) := by
    intro n
    rw [HalfLineH1.squareEnergy, norm_shiftedInterpolantH1_value_sq (hw n)]
    change (∫ x, (interpolant (mesh n) (w n) (x - mesh n)) ^ 2) = _
    exact (measurePreserving_sub_right volume (mesh n)).integral_comp
      (MeasurableEquiv.subRight (mesh n)).measurableEmbedding
      (fun x => (interpolant (mesh n) (w n) x) ^ 2)
  simpa only [heq] using hsq

theorem tendsto_global_shiftedInterpolant_sq_sub_of_local
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L B : ℝ} {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hB : ∀ n, ‖shiftedInterpolantH1 (w n) (hw n)‖ ≤ B)
    (hlocal : ∀ R : ℝ, 0 < R → Tendsto (fun n ↦ ∫ x in Icc 0 R,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x)^2)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in halfLine,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x)^2)
      atTop (𝓝 0) := by
  have hev : ∀ᶠ n in atTop, mesh n ≤ 1 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hmesh 1 (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at hd
    exact hd.2.le
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hmesh 1 (by positivity)
  have hL1 : 0 ≤ L + 1 := by
    have hu := shiftedInterpolantH1_isAdmissible (hw N)
    have hfirst : 0 ≤ L + mesh N := by
      rw [← hu.firstMoment_eq, HalfLineH1.firstMoment]
      exact setIntegral_nonneg measurableSet_Ici (fun x hx =>
        mul_nonneg hx (hu.nonnegative x hx))
    have hd := hN N (le_rfl)
    rw [Real.dist_eq, sub_zero, abs_lt] at hd
    linarith
  have htail : Tendsto (fun R : ℝ ↦ 2 *
      (Real.sqrt (2 * B * B) * ((L + 1) / R) +
        ∫ x in Ici R, v.continuousRep x ^ 2)) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun R : ℝ ↦
        Real.sqrt (2 * B * B) * ((L + 1) / R)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul (tendsto_const_nhds.mul
          (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))))
    simpa only [zero_add, add_zero, mul_zero] using
      (hfirst.add (HalfLineH1.tendsto_continuousRep_sq_integral_Ici_zero v)).const_mul 2
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 htail (ε / 2) (by linarith)
  let R : ℝ := max K 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  have hRK : K ≤ R := le_max_left K 1
  have htail_small : 2 * (Real.sqrt (2 * B * B) * ((L + 1) / R) +
      ∫ x in Ici R, v.continuousRep x ^ 2) < ε / 2 := by
    have hn : 0 ≤ 2 * (Real.sqrt (2 * B * B) * ((L + 1) / R) +
        ∫ x in Ici R, v.continuousRep x ^ 2) := by positivity
    have h := hK R hRK
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hn] at h
    exact h
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (hlocal R hR) (ε / 2) (by linarith)
  refine ⟨max M N, fun n hn ↦ ?_⟩
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hloc := hM n hnM
  have htailn := shiftedInterpolant_tailSquareEnergy_le_of_norm_le (hw n) hR (hB n)
  have htailn' : (∫ x in Ici R, shiftedInterpolant (mesh n) (w n) x ^ 2) ≤
      Real.sqrt (2 * B * B) * ((L + 1) / R) := by
    have hd := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_lt] at hd
    have hnum : L + mesh n ≤ L + 1 := by linarith [hd.2]
    have hnon : 0 ≤ Real.sqrt (2 * B * B) := Real.sqrt_nonneg _
    exact htailn.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hnum hR.le) hnon)
  have hdiff : (∫ x in Ici R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2) ≤ 2 * (Real.sqrt (2 * B * B) * ((L + 1) / R) +
      ∫ x in Ici R, v.continuousRep x ^ 2) := by
    have hq := HalfLineH1.tail_continuousRep_sub_sq_le
      (u := shiftedInterpolantH1 (w n) (hw n)) (v := v) (R := R)
    rw [continuousRep_shiftedInterpolantH1_eq (hw n)] at hq
    nlinarith [hq, htailn']
  have hsplit : (∫ x in halfLine, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2) = (∫ x in Ico 0 R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2) + ∫ x in Ici R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2 := by
    rw [show halfLine = Ico 0 R ∪ Ici R by rw [Ico_union_Ici_eq_Ici hR.le, halfLine]]
    apply setIntegral_union
    · exact Set.disjoint_left.mpr (by intro x hx hy; exact (not_lt_of_ge hy) hx.2)
    · exact measurableSet_Ici
    · exact ((shiftedInterpolant_value_memLp_of_admissible (hw n)).sub
        v.continuousRep_memLp).integrable_sq.integrableOn
    · exact ((shiftedInterpolant_value_memLp_of_admissible (hw n)).sub
        v.continuousRep_memLp).integrable_sq.integrableOn
  rw [hsplit]
  have hloc' : (∫ x in Ico 0 R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2) < ε / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hloc
    simpa only [integral_Icc_eq_integral_Ico] using hloc
  have hn1 : 0 ≤ ∫ x in Ico 0 R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2 := setIntegral_nonneg measurableSet_Ico (by intro x _; positivity)
  have hn2 : 0 ≤ ∫ x in Ici R, (shiftedInterpolant (mesh n) (w n) x -
      v.continuousRep x)^2 := setIntegral_nonneg measurableSet_Ici (by intro x _; positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg hn1 hn2)]
  nlinarith [hdiff, htail_small]

theorem shiftedInterpolantH1_rayleighQuotient_eq_interpolationRayleighQuotient
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).rayleighQuotient =
      interpolationRayleighQuotient h (interpolant h w) := by
  unfold HalfLineH1.rayleighQuotient HalfLineH1.dirichletEnergy
  rw [norm_shiftedInterpolantH1_weakDeriv_sq hw,
    HalfLineH1.squareEnergy,
    norm_shiftedInterpolantH1_value_sq hw,
    integral_sq_deriv_shiftedInterpolant hw,
    integral_sq_shiftedInterpolant hw]
  rw [integral_sq_deriv_interpolant hw, integral_sq_interpolant hw]
  unfold interpolationRayleighQuotient
  rw [integral_sq_deriv_interpolant_Ici_neg hw,
    integral_sq_interpolant_Ici_neg hw]
theorem shiftedInterpolantH1_rayleighQuotient_eq_scaled_div_correction
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (shiftedInterpolantH1 w hw).rayleighQuotient =
      (h⁻¹) ^ 2 * rayleighQuotient w /
        (1 - rayleighQuotient w / 6) := by
  rw [shiftedInterpolantH1_rayleighQuotient_eq_interpolationRayleighQuotient hw,
    interpolationRayleighQuotient_interpolant hw]

theorem tendsto_shiftedInterpolantH1_rayleighQuotient_of_tendsto_scaled
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L ell : ℝ}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hscaled : Tendsto (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n))
      atTop (𝓝 ell)) :
    Tendsto
      (fun n ↦ (shiftedInterpolantH1 (w n) (hw n)).rayleighQuotient)
      atTop (𝓝 ell) := by
  have hmesh0 : Tendsto mesh atTop (𝓝 0) :=
    tendsto_nhdsWithin_iff.1 hmesh |>.1
  have hmesh_ne : ∀ᶠ n in atTop, mesh n ≠ 0 := by
    filter_upwards [(tendsto_nhdsWithin_iff.1 hmesh).2] with n hn
    exact ne_of_gt hn
  have hqzero : Tendsto (fun n ↦ rayleighQuotient (w n)) atTop (𝓝 0) := by
    have hsquare : Tendsto (fun n ↦ mesh n ^ 2) atTop (𝓝 0) :=
      by simpa using hmesh0.pow 2
    have hprod : Tendsto
        (fun n ↦ mesh n ^ 2 * ((mesh n)⁻¹ ^ 2 * rayleighQuotient (w n)))
        atTop (𝓝 0) := by simpa using hsquare.mul hscaled
    apply (tendsto_congr' ?_).2 hprod
    filter_upwards [hmesh_ne] with n hn
    field_simp
  have hcorr : Tendsto (fun n ↦ 1 - rayleighQuotient (w n) / 6)
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (hqzero.mul (tendsto_const_nhds (x := (6 : ℝ)⁻¹)))
    simpa only [div_eq_mul_inv, div_zero, sub_zero, zero_mul] using h
  have hquot := hscaled.div hcorr (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) /
        (1 - rayleighQuotient (w n) / 6)) atTop (𝓝 ell) := by
    rw [show (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n)) /
        (fun n ↦ 1 - rayleighQuotient (w n) / 6) =
        (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) /
          (1 - rayleighQuotient (w n) / 6)) by rfl] at hquot
    simpa only [div_one] using hquot
  apply (tendsto_congr' ?_).2 hquot'
  filter_upwards [hmesh_ne] with n hn
  rw [shiftedInterpolantH1_rayleighQuotient_eq_scaled_div_correction (hw n)]

theorem shiftedInterpolantH1_rayleighQuotient_le_of_tendsto_scaled
    {mesh : ℕ → ℝ} {w : ℕ → Kernel} {L ell B : ℝ}
    {v : Analysis.HalfLineH1}
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (_hbound : ∀ n, ‖shiftedInterpolantH1 (w n) (hw n)‖ ≤ B)
    (hweak : ∀ z : Analysis.HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (shiftedInterpolantH1 (w n) (hw n)) z)
        atTop (𝓝 (inner ℝ v z)))
    (hglobal : Tendsto (fun n ↦ ∫ x in halfLine,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x) ^ 2)
      atTop (𝓝 0))
    (hmass : v.mass = 1)
    (hscaled : Tendsto (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n))
      atTop (𝓝 ell)) :
    v.rayleighQuotient ≤ ell := by
  have hsquare := shiftedInterpolant_squareEnergy_tendsto_of_global_continuousRep_sq_sub
    hw hglobal
  have hpos : ∀ n, 0 < (shiftedInterpolantH1 (w n) (hw n)).squareEnergy := by
    intro n
    exact HalfLineH1.squareEnergy_pos_of_mass_eq_one (mass_shiftedInterpolantH1 (hw n))
  have hvpos := HalfLineH1.squareEnergy_pos_of_mass_eq_one hmass
  have hmesh' : Tendsto mesh atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨hmesh, Filter.Eventually.of_forall (fun n ↦ (hw n).h_pos)⟩
  have hq := tendsto_shiftedInterpolantH1_rayleighQuotient_of_tendsto_scaled
    hmesh' hw hscaled
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hq ε hε
  let u : ℕ → Analysis.HalfLineH1 := fun n ↦
    shiftedInterpolantH1 (w (n + N)) (hw (n + N))
  have hweak' : ∀ z : Analysis.HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z)) := by
    intro z
    convert (hweak z).comp (tendsto_add_atTop_nat N) using 1
    rfl
  have hsquare' : Tendsto (fun n ↦ (u n).squareEnergy) atTop (𝓝 v.squareEnergy) := by
    convert hsquare.comp (tendsto_add_atTop_nat N) using 1
    funext n
    rw [HalfLineH1.squareEnergy, norm_shiftedInterpolantH1_value_sq (hw (n + N))]
    exact (measurePreserving_sub_right volume (mesh (n + N))).integral_comp
      (MeasurableEquiv.subRight (mesh (n + N))).measurableEmbedding
      (fun x => (interpolant (mesh (n + N)) (w (n + N)) x) ^ 2)
  have hpos' : ∀ n, 0 < (u n).squareEnergy := fun n => hpos (n + N)
  have hle' : ∀ n, (u n).rayleighQuotient ≤ ell + ε := by
    intro n
    have hh := hN (n + N) (by omega)
    rw [Real.dist_eq, abs_lt] at hh
    linarith
  exact HalfLineH1.rayleighQuotient_le_of_tendsto_squareEnergy_of_le hweak' hsquare'
    hpos' hvpos hle'

end RayleighKernel.Discrete
