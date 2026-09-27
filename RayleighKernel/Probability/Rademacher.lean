import RayleighKernel.Probability.GaussianScaleMixture
import Mathlib.Probability.UniformOn

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal
namespace RayleighKernel.Probability

def rademacherMeasure : Measure Bool := uniformOn Set.univ

def rademacherSign : Bool → ℝ := fun b => if b then 1 else -1

def rademacherFirst : Bool × Bool → ℝ := fun p => rademacherSign p.1

def rademacherSecond : Bool × Bool → ℝ := fun p => rademacherSign p.2

def rademacherProductMeasure : Measure (Bool × Bool) :=
  rademacherMeasure.prod rademacherMeasure

private instance rademacherMeasure_isProbabilityMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  dsimp [rademacherMeasure]
  infer_instance

private instance rademacherProductMeasure_isProbabilityMeasure :
    IsProbabilityMeasure rademacherProductMeasure := by
  dsimp [rademacherProductMeasure]
  infer_instance

private theorem rademacherMeasure_eq :
    rademacherMeasure = (2 : ℝ≥0∞)⁻¹ • Measure.count := by
  rw [rademacherMeasure]
  apply Measure.ext_of_singleton
  intro b
  fin_cases b <;> simp [uniformOn, cond_apply, Measure.count_apply_finite]

private theorem rademacher_integral_bool (f : Bool → ℝ) :
    (∫ b, f b ∂rademacherMeasure) = (f false + f true) / 2 := by
  rw [rademacherMeasure_eq]
  rw [integral_smul_measure, integral_count]
  norm_num
  ring

private theorem rademacher_integral_prod (f : Bool × Bool → ℝ) :
    (∫ p, f p ∂rademacherProductMeasure) =
      (f (false, false) + f (false, true) + f (true, false) + f (true, true)) / 4 := by
  rw [rademacherProductMeasure]
  rw [integral_prod]
  · simp_rw [rademacher_integral_bool]
    ring
  · exact Integrable.of_finite

theorem rademacherSign_memLp : MemLp rademacherSign 2 rademacherMeasure := by
  exact MemLp.of_bound (by fun_prop) 1 (Eventually.of_forall (by
    intro b
    simp [rademacherSign, Real.norm_eq_abs]
    split <;> norm_num))

theorem rademacherFirst_memLp : MemLp rademacherFirst 2 rademacherProductMeasure := by
  exact MemLp.of_bound (by fun_prop) 1 (Eventually.of_forall (by
    intro p
    simp [rademacherFirst, rademacherSign, Real.norm_eq_abs]
    split <;> norm_num))

theorem rademacherSecond_memLp : MemLp rademacherSecond 2 rademacherProductMeasure := by
  exact MemLp.of_bound (by fun_prop) 1 (Eventually.of_forall (by
    intro p
    simp [rademacherSecond, rademacherSign, Real.norm_eq_abs]
    split <;> norm_num))

theorem rademacher_independent :
    rademacherFirst ⟂ᵢ[rademacherProductMeasure] rademacherSecond := by
  rw [rademacherProductMeasure]
  change (fun p => rademacherSign p.1) ⟂ᵢ[rademacherMeasure.prod rademacherMeasure]
    (fun p => rademacherSign p.2)
  exact indepFun_prod (μ := rademacherMeasure) (ν := rademacherMeasure)
    (X := rademacherSign) (Y := rademacherSign)
    (measurable_of_finite rademacherSign) (measurable_of_finite rademacherSign)

theorem rademacherFirst_centered :
    ∫ p, rademacherFirst p ∂rademacherProductMeasure = 0 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherFirst, rademacherSign]

theorem rademacherSecond_centered :
    ∫ p, rademacherSecond p ∂rademacherProductMeasure = 0 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherSecond, rademacherSign]

theorem rademacherFirst_secondMoment :
    ∫ p, (rademacherFirst p)^2 ∂rademacherProductMeasure = 1 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherFirst, rademacherSign]

theorem rademacherSecond_secondMoment :
    ∫ p, (rademacherSecond p)^2 ∂rademacherProductMeasure = 1 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherSecond, rademacherSign]

theorem rademacher_crossSecondMoment :
    ∫ p, rademacherFirst p * rademacherSecond p ∂rademacherProductMeasure = 0 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherFirst, rademacherSecond, rademacherSign]

theorem rademacher_abs_projection (a b : ℝ) :
    (∫ p, |a * rademacherFirst p + b * rademacherSecond p|
      ∂rademacherProductMeasure) = (|a + b| + |a - b|) / 2 := by
  rw [rademacher_integral_prod]
  norm_num [rademacherFirst, rademacherSecond, rademacherSign]
  rw [show -a + b = -(a - b) by ring, show -a + -b = -(a + b) by ring]
  simp only [abs_neg]
  ring_nf

theorem rademacher_abs_projection_eq_max (a b : ℝ) :
    (|a + b| + |a - b|) / 2 = max |a| |b| := by
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · rcases le_total a b with hab | hba
      · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (by linarith),
          abs_of_nonpos (sub_nonpos.mpr hab), max_eq_right (by linarith)]
        ring
      · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (by linarith),
          abs_of_nonneg (sub_nonneg.mpr hba), max_eq_left (by linarith)]
        ring
    · have hb' : b ≤ 0 := hb
      rcases le_total a (-b) with hab | hba
      · rw [abs_of_nonneg ha, abs_of_nonpos hb', abs_of_nonpos (by linarith),
          abs_of_nonneg (by linarith), max_eq_right (by linarith)]
        ring
      · rw [abs_of_nonneg ha, abs_of_nonpos hb', abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith), max_eq_left (by linarith)]
        ring
  · have ha' : a ≤ 0 := ha
    rcases le_total 0 b with hb | hb
    · rcases le_total (-a) b with hab | hba
      · rw [abs_of_nonpos ha', abs_of_nonneg hb, abs_of_nonneg (by linarith),
          abs_of_nonpos (by linarith), max_eq_right (by linarith)]
        ring
      · rw [abs_of_nonpos ha', abs_of_nonneg hb, abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
    · rcases le_total a b with hab | hba
      · rw [abs_of_nonpos ha', abs_of_nonpos hb, abs_of_nonpos (by linarith),
          abs_of_nonpos (sub_nonpos.mpr hab), max_eq_left (by linarith)]
        ring
      · rw [abs_of_nonpos ha', abs_of_nonpos hb, abs_of_nonpos (by linarith),
          abs_of_nonneg (sub_nonneg.mpr hba), max_eq_right (by linarith)]
        ring

theorem rademacher_abs_projection_eq_max' (a b : ℝ) :
    (∫ p, |a * rademacherFirst p + b * rademacherSecond p|
      ∂rademacherProductMeasure) = max |a| |b| := by
  rw [rademacher_abs_projection, rademacher_abs_projection_eq_max]

theorem rademacher_not_euclidean_isotropic :
    ¬ ∃ c : ℝ, ∀ a b : ℝ,
      (∫ p, |a * rademacherFirst p + b * rademacherSecond p|
        ∂rademacherProductMeasure) = c * Real.sqrt (a ^ 2 + b ^ 2) := by
  rintro ⟨c, h⟩
  have hc : c = 1 := by
    have hh := h 1 0
    rw [rademacher_abs_projection_eq_max' 1 0] at hh
    norm_num at hh ⊢
    exact hh.symm
  have hbad := h 1 1
  rw [rademacher_abs_projection 1 1, hc] at hbad
  norm_num at hbad
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

end RayleighKernel.Probability
