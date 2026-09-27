import RayleighKernel.Profile.SelfConsistency
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positivity of the free-boundary profile

This file proves the factorization and monotonicity argument that selects `0 < t < 2π` as the only
branch on which the explicit free-boundary profile can be nonnegative.
-/

noncomputable section

namespace RayleighKernel.Profile

open Set

/-- Auxiliary quotient used to factor the free-boundary profile. -/
def alpha (t : ℝ) : ℝ := (t - Real.sin t) / (1 - Real.cos t)

/-- Numerator controlling the sign of `alpha'`. -/
def alphaDerivativeNumerator (t : ℝ) : ℝ :=
  (1 - Real.cos t) ^ 2 - (t - Real.sin t) * Real.sin t

/-- The derivative of `alphaDerivativeNumerator`. -/
def alphaDerivativeNumeratorSlope (t : ℝ) : ℝ := Real.sin t - t * Real.cos t

@[simp]
theorem alphaDerivativeNumerator_zero : alphaDerivativeNumerator 0 = 0 := by
  simp [alphaDerivativeNumerator]

@[simp]
theorem alphaDerivativeNumeratorSlope_zero : alphaDerivativeNumeratorSlope 0 = 0 := by
  simp [alphaDerivativeNumeratorSlope]

theorem alphaDerivativeNumeratorSlope_hasDerivAt (t : ℝ) :
    HasDerivAt alphaDerivativeNumeratorSlope (t * Real.sin t) t := by
  convert Real.hasDerivAt_sin t |>.sub
    ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem alphaDerivativeNumerator_hasDerivAt (t : ℝ) :
    HasDerivAt alphaDerivativeNumerator (alphaDerivativeNumeratorSlope t) t := by
  have h := ((hasDerivAt_const t 1).sub (Real.hasDerivAt_cos t) |>.pow 2).sub
    (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).mul (Real.hasDerivAt_sin t))
  convert h using 1
  · ext x
    simp only [alphaDerivativeNumerator, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id_eq]
  · simp only [alphaDerivativeNumeratorSlope]
    have htrig := Real.sin_sq_add_cos_sq t
    simp only [Pi.sub_apply, id_eq] at htrig ⊢
    ring_nf at htrig ⊢

theorem alpha_hasDerivAt {t : ℝ} (hcos : Real.cos t ≠ 1) :
    HasDerivAt alpha (alphaDerivativeNumerator t / (1 - Real.cos t) ^ 2) t := by
  have h := ((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).div
    ((hasDerivAt_const t 1).sub (Real.hasDerivAt_cos t)) (sub_ne_zero.mpr hcos.symm)
  convert h using 1
  · ext x
    simp only [alpha, Pi.sub_apply, Pi.div_apply, id_eq]
  · simp only [alphaDerivativeNumerator, Pi.sub_apply, id_eq]
    field_simp [sub_ne_zero.mpr hcos.symm]
    ring

theorem cos_ne_one_of_mem_Ioo_two_pi {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi)) :
    Real.cos t ≠ 1 := by
  intro h
  have htneg : -(2 * Real.pi) < t := lt_trans (neg_lt_zero.mpr Real.two_pi_pos) ht.1
  have htzero := (Real.cos_eq_one_iff_of_lt_of_lt htneg ht.2).mp h
  exact ht.1.ne' htzero

theorem alphaDerivativeNumeratorSlope_pos {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    0 < alphaDerivativeNumeratorSlope t := by
  have hmono : StrictMonoOn alphaDerivativeNumeratorSlope (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
    · exact (Real.continuous_sin.sub
        (continuous_id.mul Real.continuous_cos)).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [(alphaDerivativeNumeratorSlope_hasDerivAt x).deriv]
      exact mul_pos hx.1 (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  simpa using hmono ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1

theorem alphaDerivativeNumerator_pos_of_lt_pi {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    0 < alphaDerivativeNumerator t := by
  have hmono : StrictMonoOn alphaDerivativeNumerator (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
    · unfold alphaDerivativeNumerator
      fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      rw [(alphaDerivativeNumerator_hasDerivAt x).deriv]
      exact alphaDerivativeNumeratorSlope_pos hx
  simpa using hmono ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1

theorem sin_nonpos_of_pi_le_of_le_two_pi {t : ℝ} (hpi : Real.pi ≤ t)
    (htwo : t ≤ 2 * Real.pi) : Real.sin t ≤ 0 := by
  have hs : 0 ≤ Real.sin (2 * Real.pi - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_two_pi_sub] at hs
  linarith

theorem alphaDerivativeNumerator_pos_of_pi_le {t : ℝ} (hpi : Real.pi ≤ t)
    (htwo : t < 2 * Real.pi) : 0 < alphaDerivativeNumerator t := by
  have hsin : Real.sin t ≤ 0 := sin_nonpos_of_pi_le_of_le_two_pi hpi htwo.le
  have ht : 0 < t := lt_of_lt_of_le Real.pi_pos hpi
  have hcos : Real.cos t ≠ 1 := cos_ne_one_of_mem_Ioo_two_pi ⟨ht, htwo⟩
  have hsquare : 0 < (1 - Real.cos t) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hcos.symm)
  unfold alphaDerivativeNumerator
  nlinarith [Real.neg_one_le_sin t]

theorem alphaDerivativeNumerator_pos {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi)) :
    0 < alphaDerivativeNumerator t := by
  by_cases hpi : t < Real.pi
  · exact alphaDerivativeNumerator_pos_of_lt_pi ⟨ht.1, hpi⟩
  · exact alphaDerivativeNumerator_pos_of_pi_le (le_of_not_gt hpi) ht.2

theorem strictMonoOn_alpha : StrictMonoOn alpha (Ioo 0 (2 * Real.pi)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (2 * Real.pi))
  · intro t ht
    exact (alpha_hasDerivAt (cos_ne_one_of_mem_Ioo_two_pi ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(alpha_hasDerivAt (cos_ne_one_of_mem_Ioo_two_pi ht)).deriv]
    exact div_pos (alphaDerivativeNumerator_pos ht)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr (cos_ne_one_of_mem_Ioo_two_pi ht).symm))

theorem value_unfactored {t y : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1) :
    t * value t y =
      alpha t * (1 - Real.cos (t * (1 - y))) - t * (1 - y) + Real.sin (t * (1 - y)) := by
  rw [value, coefficientA, coefficientC, alpha]
  have harg : t * y = t - t * (1 - y) := by ring
  rw [harg, Real.sin_sub, Real.cos_sub]
  field_simp
  ring_nf
  have htrig : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [htrig]
  ring

theorem alpha_mul_one_sub_cos {s : ℝ} (hcos : Real.cos s ≠ 1) :
    alpha s * (1 - Real.cos s) = s - Real.sin s := by
  rw [alpha]
  field_simp

theorem value_factorization {t y : ℝ} (ht : t ≠ 0) (hcos_t : Real.cos t ≠ 1)
    (hcos_s : Real.cos (t * (1 - y)) ≠ 1) :
    t * value t y =
      (alpha t - alpha (t * (1 - y))) * (1 - Real.cos (t * (1 - y))) := by
  rw [value_unfactored ht hcos_t, sub_mul, alpha_mul_one_sub_cos hcos_s]
  ring

theorem value_pos {t y : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi)) (hy : y ∈ Ioo 0 1) :
    0 < value t y := by
  let s := t * (1 - y)
  have hs : s ∈ Ioo 0 (2 * Real.pi) := by
    constructor
    · exact mul_pos ht.1 (sub_pos.mpr hy.2)
    · calc
        s < t := mul_lt_of_lt_one_right ht.1 (sub_lt_self 1 hy.1)
        _ < 2 * Real.pi := ht.2
  have hst : s < t := mul_lt_of_lt_one_right ht.1 (sub_lt_self 1 hy.1)
  have halpha : alpha s < alpha t := strictMonoOn_alpha hs ht hst
  have hcos_s : Real.cos s ≠ 1 := cos_ne_one_of_mem_Ioo_two_pi hs
  have hfactor := value_factorization ht.1.ne' (cos_ne_one_of_mem_Ioo_two_pi ht) hcos_s
  have honecos : 0 < 1 - Real.cos s := by
    have hle := Real.cos_le_one s
    exact sub_pos.mpr (lt_of_le_of_ne hle hcos_s)
  have hproduct : 0 < (alpha t - alpha s) * (1 - Real.cos s) :=
    mul_pos (sub_pos.mpr halpha) honecos
  rw [show t * (1 - y) = s by rfl] at hfactor
  have htvalue : 0 < t * value t y := hfactor.symm ▸ hproduct
  exact ((mul_pos_iff.mp htvalue).resolve_right (by
    rintro ⟨htneg, _⟩
    exact (not_lt_of_ge ht.1.le) htneg)).2

theorem exists_value_neg_of_two_pi_lt {t : ℝ} (ht : 2 * Real.pi < t)
    (hcos : Real.cos t ≠ 1) : ∃ y ∈ Ioo (0 : ℝ) 1, value t y < 0 := by
  let y := 1 - 2 * Real.pi / t
  have ht0 : 0 < t := lt_trans Real.two_pi_pos ht
  have hy : y ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [y]
      rw [sub_pos, div_lt_one ht0]
      exact ht
    · dsimp [y]
      have hdiv : 0 < 2 * Real.pi / t := div_pos Real.two_pi_pos ht0
      linarith
  refine ⟨y, hy, ?_⟩
  have hs : t * (1 - y) = 2 * Real.pi := by
    dsimp [y]
    field_simp
    ring
  have hvalue := value_unfactored ht0.ne' hcos (y := y)
  rw [hs, Real.cos_two_pi, Real.sin_two_pi] at hvalue
  simp only [sub_self, mul_zero, zero_sub, add_zero] at hvalue
  have htvalue : t * value t y < 0 := by rw [hvalue]; exact neg_neg_of_pos Real.two_pi_pos
  exact ((mul_neg_iff.mp htvalue).resolve_right (by
    rintro ⟨htneg, _⟩
    exact (not_lt_of_ge ht0.le) htneg)).2

end RayleighKernel.Profile
