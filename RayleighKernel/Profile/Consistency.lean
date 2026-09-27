import RayleighKernel.Profile.Positivity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Differential identities for the consistency polynomial

This file develops the exact derivative formulas used to prove existence and uniqueness of the
admissible consistency root.
-/

noncomputable section

namespace RayleighKernel.Profile

open Set
open Filter

theorem cot_hasDerivAt {x : ℝ} (hsin : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 / Real.sin x ^ 2)) x := by
  have h := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin
  convert h using 1
  · ext y
    simpa only [Pi.div_apply] using Real.cot_eq_cos_div_sin y
  · field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]

theorem initialSlope_hasDerivAt {t : ℝ} (hsin : Real.sin (t / 2) ≠ 0) :
    HasDerivAt initialSlope
      (-Real.cot (t / 2) + t / (2 * Real.sin (t / 2) ^ 2)) t := by
  have harg : HasDerivAt (fun z : ℝ ↦ z / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have hcot : HasDerivAt (fun z : ℝ ↦ Real.cot (z / 2))
      (-(1 / Real.sin (t / 2) ^ 2) * (1 / 2)) t :=
    (cot_hasDerivAt hsin).comp t harg |>.congr_of_eventuallyEq (by rfl)
  unfold initialSlope
  convert (hasDerivAt_const t 2).sub ((hasDerivAt_id t).mul hcot) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem initialSlope_derivative_identity {t : ℝ} (ht : t ≠ 0)
    (hsin : Real.sin (t / 2) ≠ 0) :
    deriv initialSlope t =
      (t ^ 2 + initialSlope t ^ 2 - 2 * initialSlope t) / (2 * t) := by
  rw [(initialSlope_hasDerivAt hsin).deriv]
  rw [initialSlope, Real.cot_eq_cos_div_sin]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem consistencyPolynomial_hasDerivAt {t : ℝ} (ht : t ≠ 0)
    (hsin : Real.sin (t / 2) ≠ 0) :
    HasDerivAt consistencyPolynomial
      (4 * t ^ 3 - 12 * t * initialSlope t -
        6 * t ^ 2 * ((t ^ 2 + initialSlope t ^ 2 - 2 * initialSlope t) / (2 * t)) +
        3 * (3 * initialSlope t ^ 2 *
          ((t ^ 2 + initialSlope t ^ 2 - 2 * initialSlope t) / (2 * t)) *
            (initialSlope t - 2) +
          initialSlope t ^ 3 *
            ((t ^ 2 + initialSlope t ^ 2 - 2 * initialSlope t) / (2 * t)))) t := by
  let p' := (t ^ 2 + initialSlope t ^ 2 - 2 * initialSlope t) / (2 * t)
  have hp : HasDerivAt initialSlope p' t := by
    have h := initialSlope_hasDerivAt hsin
    convert h using 1
    exact ((initialSlope_hasDerivAt hsin).deriv.symm.trans
      (initialSlope_derivative_identity ht hsin)).symm
  unfold consistencyPolynomial
  convert (((hasDerivAt_id t).pow 4).sub
    ((((hasDerivAt_id t).pow 2).mul hp).const_mul 6)).add
    (((hp.pow 3).mul (hp.sub_const 2)).const_mul 3) using 1
  · ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    simp only [id_eq]
    ring
  · simp only [id_eq, Nat.cast_ofNat]
    dsimp [p']
    ring

/-- The polynomial displayed in the manuscript for `t * Q'(t)` after writing `p=2+u`. -/
def consistencyDerivativeNumerator (t u : ℝ) : ℝ :=
  t ^ 2 * (t ^ 2 - 12) + 6 * t ^ 2 * u ^ 3 + 24 * t ^ 2 * u ^ 2 +
    18 * t ^ 2 * u + 6 * u ^ 5 + 39 * u ^ 4 + 90 * u ^ 3 + 84 * u ^ 2 + 24 * u

theorem consistencyPolynomial_deriv_eq {t : ℝ} (ht : t ≠ 0)
    (hsin : Real.sin (t / 2) ≠ 0) :
    deriv consistencyPolynomial t =
      consistencyDerivativeNumerator t (initialSlope t - 2) / t := by
  rw [(consistencyPolynomial_hasDerivAt ht hsin).deriv]
  unfold consistencyDerivativeNumerator
  field_simp
  ring

theorem initialSlope_sub_two_eq_tan (t : ℝ) :
    initialSlope t - 2 = t * Real.tan ((t - Real.pi) / 2) := by
  rw [initialSlope, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
  have harg : t / 2 = Real.pi / 2 + (t - Real.pi) / 2 := by ring
  rw [harg, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp only [zero_mul, one_mul, zero_sub]
  field_simp
  ring

theorem initialSlope_sub_two_pos {t : ℝ} (hpi : Real.pi < t)
    (htwo : t < 2 * Real.pi) : 0 < initialSlope t - 2 := by
  rw [initialSlope_sub_two_eq_tan]
  exact mul_pos (lt_trans Real.pi_pos hpi)
    (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith))

theorem consistencyDerivativeNumerator_pos {t u : ℝ} (ht : Real.sqrt 12 ≤ t)
    (hu : 0 < u) : 0 < consistencyDerivativeNumerator t u := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) ht
  have ht_sq : 12 ≤ t ^ 2 := by
    calc
      (12 : ℝ) = (Real.sqrt 12) ^ 2 := by norm_num
      _ ≤ t ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg 12) ht0.le).mpr ht
  unfold consistencyDerivativeNumerator
  positivity

theorem consistencyPolynomial_deriv_pos {t : ℝ} (hroot : Real.sqrt 12 ≤ t)
    (htwo : t < 2 * Real.pi) : 0 < deriv consistencyPolynomial t := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) hroot
  have hpi : Real.pi < t := by
    have hpi_sq : Real.pi ^ 2 < 12 := by
      nlinarith [Real.pi_lt_d2]
    have ht_sq : 12 ≤ t ^ 2 := by
      calc
        (12 : ℝ) = (Real.sqrt 12) ^ 2 := by norm_num
        _ ≤ t ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg 12) ht0.le).mpr hroot
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (t / 2) ≠ 0 := by
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith) |>.ne'
  rw [consistencyPolynomial_deriv_eq ht0.ne' hsin]
  exact div_pos
    (consistencyDerivativeNumerator_pos hroot (initialSlope_sub_two_pos hpi htwo)) ht0

theorem strictMonoOn_consistencyPolynomial :
    StrictMonoOn consistencyPolynomial (Ico (Real.sqrt 12) (2 * Real.pi)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico (Real.sqrt 12) (2 * Real.pi))
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) ht.1
    have hsin : Real.sin (t / 2) ≠ 0 := by
      exact Real.sin_pos_of_pos_of_lt_pi (half_pos ht0)
        (by linarith [ht.2]) |>.ne'
    exact (consistencyPolynomial_hasDerivAt ht0.ne' hsin).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    exact consistencyPolynomial_deriv_pos ht.1.le ht.2

/-- Auxiliary function used to prove the elementary cotangent bound in the manuscript. -/
def cotBoundAux (x : ℝ) : ℝ := (1 - x ^ 2 / 3) * Real.sin x - x * Real.cos x

@[simp]
theorem cotBoundAux_zero : cotBoundAux 0 = 0 := by simp [cotBoundAux]

theorem cotBoundAux_hasDerivAt (x : ℝ) :
    HasDerivAt cotBoundAux (x / 3 * alphaDerivativeNumeratorSlope x) x := by
  unfold cotBoundAux alphaDerivativeNumeratorSlope
  convert ((((hasDerivAt_const x 1).sub (((hasDerivAt_id x).pow 2).div_const 3)).mul
    (Real.hasDerivAt_sin x)).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))) using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply, Pi.sub_apply]
    ring

theorem cotBoundAux_pos {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2)) : 0 < cotBoundAux x := by
  have hmono : StrictMonoOn cotBoundAux (Icc 0 (Real.pi / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (Real.pi / 2))
    · unfold cotBoundAux
      fun_prop
    · intro z hz
      rw [interior_Icc] at hz
      rw [(cotBoundAux_hasDerivAt z).deriv]
      have hzpi : z < Real.pi := lt_trans hz.2 (by linarith [Real.pi_pos])
      exact mul_pos (div_pos hz.1 (by norm_num))
        (alphaDerivativeNumeratorSlope_pos ⟨hz.1, hzpi⟩)
  simpa using hmono ⟨le_rfl, Real.pi_div_two_pos.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1

theorem mul_cot_lt_one_sub_sq_div_three {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    x * Real.cot x < 1 - x ^ 2 / 3 := by
  have hxpi : x < Real.pi := lt_trans hx.2 (by linarith [Real.pi_pos])
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hxpi
  have haux := cotBoundAux_pos hx
  unfold cotBoundAux at haux
  rw [Real.cot_eq_cos_div_sin]
  rw [← mul_div_assoc]
  rw [div_lt_iff₀ hsin]
  nlinarith

theorem initialSlope_gt_sq_div_six {t : ℝ} (ht : t ∈ Ioc 0 Real.pi) :
    t ^ 2 / 6 < initialSlope t := by
  rcases ht.2.eq_or_lt with rfl | htpi
  · rw [initialSlope, Real.cot_eq_cos_div_sin, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    have hsqrt_lower : (17 : ℝ) / 5 < Real.sqrt 12 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12), Real.sqrt_nonneg 12]
    have hpi_root : Real.pi < Real.sqrt 12 :=
      lt_trans Real.pi_lt_d2 (lt_trans (by norm_num) hsqrt_lower)
    have hpi_sq : Real.pi ^ 2 < 12 := by
      calc
        Real.pi ^ 2 < (Real.sqrt 12) ^ 2 :=
          pow_lt_pow_left₀ hpi_root Real.pi_pos.le (by norm_num)
        _ = 12 := by norm_num
    norm_num
    linarith
  · have hhalf : t / 2 ∈ Ioo 0 (Real.pi / 2) := by
      constructor
      · exact half_pos ht.1
      · linarith
    have hcot := mul_cot_lt_one_sub_sq_div_three hhalf
    rw [initialSlope]
    nlinarith

theorem initialSlope_le_two {t : ℝ} (ht : t ∈ Ioc 0 Real.pi) :
    initialSlope t ≤ 2 := by
  have hsin : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos ht.1) (by linarith [ht.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos (t / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos, ht.1]) (by linarith [ht.2])
  rw [initialSlope, Real.cot_eq_cos_div_sin]
  rw [← mul_div_assoc]
  exact sub_le_self 2 (div_nonneg (mul_nonneg ht.1.le hcos) hsin.le)

theorem consistencyPolynomial_neg_of_le_pi {t : ℝ} (ht : t ∈ Ioc 0 Real.pi) :
    consistencyPolynomial t < 0 := by
  have hp_lower := initialSlope_gt_sq_div_six ht
  have hp_upper := initialSlope_le_two ht
  have hp_pos : 0 < initialSlope t :=
    lt_trans (div_pos (sq_pos_of_pos ht.1) (by norm_num)) hp_lower
  unfold consistencyPolynomial
  have hfirst : t ^ 4 - 6 * t ^ 2 * initialSlope t < 0 := by
    nlinarith [sq_pos_of_pos ht.1]
  have hlast : 3 * initialSlope t ^ 3 * (initialSlope t - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) (pow_nonneg hp_pos.le 3)) (sub_nonpos.mpr hp_upper)
  linarith

theorem sqrt_twelve_lt_three_point_four_seven : Real.sqrt 12 < (347 : ℝ) / 100 := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)
  have hsqrt_nonneg := Real.sqrt_nonneg 12
  nlinarith

theorem pi_lt_sqrt_twelve : Real.pi < Real.sqrt 12 := by
  have hsqrt_lower : (17 : ℝ) / 5 < Real.sqrt 12 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12), Real.sqrt_nonneg 12]
  exact lt_trans Real.pi_lt_d2 (lt_trans (by norm_num) hsqrt_lower)

theorem initialSlope_sub_two_lt_three_fifths {t : ℝ} (hpi : Real.pi < t)
    (hroot : t ≤ Real.sqrt 12) : initialSlope t - 2 < (3 : ℝ) / 5 := by
  let x := (t - Real.pi) / 2
  have hxpos : 0 < x := by dsimp [x]; linarith
  have htbound : t < (347 : ℝ) / 100 :=
    lt_of_le_of_lt hroot sqrt_twelve_lt_three_point_four_seven
  have hxbound : x < (1 : ℝ) / 6 := by
    dsimp [x]
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have hsin : Real.sin x ≤ x := Real.sin_le hxpos.le
  have hcos : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hden : (71 : ℝ) / 72 < Real.cos x := by nlinarith [sq_nonneg (x - 1 / 6)]
  have htan : Real.tan x < (12 : ℝ) / 71 := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ (lt_trans (by norm_num) hden)]
    nlinarith
  rw [initialSlope_sub_two_eq_tan]
  have htan_pos := Real.tan_pos_of_pos_of_lt_pi_div_two hxpos
    (lt_trans hxbound (by nlinarith [Real.pi_gt_three]))
  change t * Real.tan x < _
  nlinarith

theorem consistencyPolynomial_eq_u {t u : ℝ} (hu : initialSlope t = 2 + u) :
    consistencyPolynomial t = t ^ 2 * (t ^ 2 - 12) +
      u * (3 * u ^ 3 + 18 * u ^ 2 + 36 * u + 24 - 6 * t ^ 2) := by
  rw [consistencyPolynomial, hu]
  ring

theorem consistencyPolynomial_neg_of_pi_lt_of_le_sqrt_twelve {t : ℝ}
    (hpi : Real.pi < t) (hroot : t ≤ Real.sqrt 12) : consistencyPolynomial t < 0 := by
  let u := initialSlope t - 2
  have htwo : t < 2 * Real.pi := by
    have hsqrt := sqrt_twelve_lt_three_point_four_seven
    nlinarith [Real.pi_gt_three]
  have hu_pos : 0 < u := initialSlope_sub_two_pos hpi htwo
  have hu_upper : u < (3 : ℝ) / 5 := initialSlope_sub_two_lt_three_fifths hpi hroot
  have ht_sq : t ^ 2 ≤ 12 := by
    have ht0 : 0 < t := lt_trans Real.pi_pos hpi
    calc
      t ^ 2 ≤ (Real.sqrt 12) ^ 2 := (sq_le_sq₀ ht0.le (Real.sqrt_nonneg 12)).mpr hroot
      _ = 12 := by norm_num
  have hu_eq : initialSlope t = 2 + u := by dsimp only [u]; ring
  rw [consistencyPolynomial_eq_u hu_eq]
  have hu2 : u ^ 2 < ((3 : ℝ) / 5) ^ 2 := pow_lt_pow_left₀ hu_upper hu_pos.le (by norm_num)
  have hu3 : u ^ 3 < ((3 : ℝ) / 5) ^ 3 := pow_lt_pow_left₀ hu_upper hu_pos.le (by norm_num)
  have hbracket : 3 * u ^ 3 + 18 * u ^ 2 + 36 * u + 24 - 6 * t ^ 2 < 0 := by
    have ht_sq_lower : 9 < t ^ 2 := by nlinarith [Real.pi_gt_three]
    norm_num at hu2 hu3 ⊢
    linarith
  have hfirst : t ^ 2 * (t ^ 2 - 12) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (sub_nonpos.mpr ht_sq)
  have hsecond : u * (3 * u ^ 3 + 18 * u ^ 2 + 36 * u + 24 - 6 * t ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hu_pos hbracket
  linarith

theorem consistencyPolynomial_neg_of_le_sqrt_twelve {t : ℝ} (ht : 0 < t)
    (hroot : t ≤ Real.sqrt 12) : consistencyPolynomial t < 0 := by
  by_cases hpi : t ≤ Real.pi
  · exact consistencyPolynomial_neg_of_le_pi ⟨ht, hpi⟩
  · exact consistencyPolynomial_neg_of_pi_lt_of_le_sqrt_twelve (lt_of_not_ge hpi) hroot

theorem tendsto_half_shift_two_pi :
    Filter.Tendsto (fun t : ℝ ↦ (t - Real.pi) / 2) (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)))
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Filter.Tendsto (fun t : ℝ ↦ (t - Real.pi) / 2)
        (nhds (2 * Real.pi)) (nhds ((2 * Real.pi - Real.pi) / 2)) :=
      ((continuous_id.sub continuous_const).div_const 2).continuousAt
    have h' : Filter.Tendsto (fun t : ℝ ↦ (t - Real.pi) / 2)
        (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)))
        (nhds ((2 * Real.pi - Real.pi) / 2)) := h.mono_left nhdsWithin_le_nhds
    simpa only [show (2 * Real.pi - Real.pi) / 2 = Real.pi / 2 by ring] using h'
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos])] with t ht
    show (t - Real.pi) / 2 < Real.pi / 2
    linarith [ht.2]

theorem tendsto_initialSlope_sub_two_at_two_pi :
    Filter.Tendsto (fun t : ℝ ↦ initialSlope t - 2)
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) atTop := by
  rw [show (fun t : ℝ ↦ initialSlope t - 2) =
      fun t : ℝ ↦ t * Real.tan ((t - Real.pi) / 2) by
    funext t
    exact initialSlope_sub_two_eq_tan t]
  apply Filter.Tendsto.pos_mul_atTop (show 0 < 2 * Real.pi by positivity)
  · exact (tendsto_nhdsWithin_iff.1 tendsto_id).1
  · exact Real.tendsto_tan_pi_div_two.comp tendsto_half_shift_two_pi

theorem tendsto_initialSlope_at_two_pi :
    Filter.Tendsto initialSlope (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) atTop := by
  rw [show initialSlope = fun t : ℝ ↦ (initialSlope t - 2) + 2 by funext t; ring]
  exact tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_initialSlope_sub_two_at_two_pi

theorem consistencyPolynomial_lower_bound {t : ℝ} (hp : 4 ≤ initialSlope t) :
    initialSlope t ^ 4 / 2 ≤ consistencyPolynomial t := by
  unfold consistencyPolynomial
  have hp_nonneg : 0 ≤ initialSlope t := le_trans (by norm_num) hp
  have hbracket : 0 ≤ 5 * initialSlope t ^ 2 - 12 * initialSlope t - 18 := by
    nlinarith [mul_nonneg hp_nonneg (sub_nonneg.mpr hp)]
  have hfactor : 0 ≤ initialSlope t ^ 2 *
      (5 * initialSlope t ^ 2 - 12 * initialSlope t - 18) :=
    mul_nonneg (sq_nonneg _) hbracket
  have hquartic : initialSlope t ^ 4 / 2 ≤
      -9 * initialSlope t ^ 2 +
        3 * initialSlope t ^ 3 * (initialSlope t - 2) := by
    nlinarith
  have htpart : -9 * initialSlope t ^ 2 ≤
      t ^ 4 - 6 * t ^ 2 * initialSlope t := by
    nlinarith [sq_nonneg (t ^ 2 - 3 * initialSlope t)]
  linarith

theorem tendsto_consistencyPolynomial_at_two_pi :
    Filter.Tendsto consistencyPolynomial
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) atTop := by
  apply tendsto_atTop_mono' _ _
    (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      ((tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp
        tendsto_initialSlope_at_two_pi))
  filter_upwards [tendsto_initialSlope_at_two_pi.eventually_ge_atTop 4] with t ht
  exact consistencyPolynomial_lower_bound ht

theorem initialSlope_two_pi_sub_pi_div_two :
    initialSlope (2 * Real.pi - Real.pi / 2) = 2 + (2 * Real.pi - Real.pi / 2) := by
  have hu : initialSlope (2 * Real.pi - Real.pi / 2) - 2 =
      2 * Real.pi - Real.pi / 2 := by
    rw [initialSlope_sub_two_eq_tan]
    have harg : ((2 * Real.pi - Real.pi / 2) - Real.pi) / 2 = Real.pi / 4 := by ring
    rw [harg, Real.tan_pi_div_four, mul_one]
  linarith

theorem consistencyPolynomial_at_two_pi_sub_pi_div_two_pos :
    0 < consistencyPolynomial (2 * Real.pi - Real.pi / 2) := by
  rw [consistencyPolynomial_eq_u initialSlope_two_pi_sub_pi_div_two]
  ring_nf
  positivity

theorem sqrt_twelve_lt_two_pi_sub_pi_div_two :
    Real.sqrt 12 < 2 * Real.pi - Real.pi / 2 := by
  have hsqrt := sqrt_twelve_lt_three_point_four_seven
  nlinarith [Real.pi_gt_three]

theorem two_pi_sub_pi_div_two_lt_two_pi :
    2 * Real.pi - Real.pi / 2 < 2 * Real.pi := by linarith [Real.pi_pos]

theorem continuousOn_consistencyPolynomial_root_interval :
    ContinuousOn consistencyPolynomial
      (Icc (Real.sqrt 12) (2 * Real.pi - Real.pi / 2)) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) ht.1
  have htpi : t / 2 < Real.pi := by linarith [ht.2, Real.pi_pos]
  have hsin : Real.sin (t / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (half_pos ht0) htpi).ne'
  exact (consistencyPolynomial_hasDerivAt ht0.ne' hsin).continuousAt

theorem exists_consistency_root :
    ∃ t ∈ Icc (Real.sqrt 12) (2 * Real.pi - Real.pi / 2),
      consistencyPolynomial t = 0 := by
  have hzero_mem : (0 : ℝ) ∈ Icc
      (consistencyPolynomial (Real.sqrt 12))
      (consistencyPolynomial (2 * Real.pi - Real.pi / 2)) :=
    ⟨(consistencyPolynomial_neg_of_le_sqrt_twelve
      (Real.sqrt_pos.2 (by norm_num)) le_rfl).le,
      consistencyPolynomial_at_two_pi_sub_pi_div_two_pos.le⟩
  exact intermediate_value_Icc
    (le_of_lt sqrt_twelve_lt_two_pi_sub_pi_div_two)
    continuousOn_consistencyPolynomial_root_interval hzero_mem

/-- The exact consistency root on the unique profile branch, obtained by the IVT. -/
noncomputable def tStar : ℝ := Classical.choose exists_consistency_root

theorem tStar_mem :
    tStar ∈ Icc (Real.sqrt 12) (2 * Real.pi - Real.pi / 2) :=
  (Classical.choose_spec exists_consistency_root).1

theorem consistencyPolynomial_tStar : consistencyPolynomial tStar = 0 :=
  (Classical.choose_spec exists_consistency_root).2

theorem sqrt_twelve_lt_tStar : Real.sqrt 12 < tStar := by
  exact lt_of_not_ge fun h ↦
    (consistencyPolynomial_neg_of_le_sqrt_twelve
      (lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) tStar_mem.1) h).ne
      consistencyPolynomial_tStar

theorem tStar_lt_two_pi : tStar < 2 * Real.pi :=
  lt_of_le_of_lt tStar_mem.2 two_pi_sub_pi_div_two_lt_two_pi

theorem consistencyPolynomial_eq_zero_iff {t : ℝ} (ht : 0 < t)
    (htwo : t < 2 * Real.pi) : consistencyPolynomial t = 0 ↔ t = tStar := by
  constructor
  · intro hzero
    by_cases hroot : t ≤ Real.sqrt 12
    · exact False.elim ((consistencyPolynomial_neg_of_le_sqrt_twelve ht hroot).ne hzero)
    · apply strictMonoOn_consistencyPolynomial.injOn
        ⟨le_of_lt (lt_of_not_ge hroot), htwo⟩
        ⟨sqrt_twelve_lt_tStar.le, tStar_lt_two_pi⟩
      exact hzero.trans consistencyPolynomial_tStar.symm
  · rintro rfl
    exact consistencyPolynomial_tStar

theorem energyGap_eq_zero_iff_tStar {t : ℝ} (ht : 0 < t)
    (htwo : t < 2 * Real.pi) : energyGap t = 0 ↔ t = tStar := by
  have hcos : Real.cos t ≠ 1 := by
    intro hcos
    have htzero := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [htwo]) htwo).mp hcos
    exact ht.ne' htzero
  exact (energyGap_eq_zero_iff ht.ne' hcos).trans
    (consistencyPolynomial_eq_zero_iff ht htwo)

theorem coefficientC_mul_momentZero_eq_momentOne_iff_tStar {t : ℝ}
    (ht : 0 < t) (htwo : t < 2 * Real.pi) :
    coefficientC t * momentZero t = momentOne t ↔ t = tStar := by
  have hcos : Real.cos t ≠ 1 := cos_ne_one_of_mem_Ioo_two_pi ⟨ht, htwo⟩
  rw [← sub_eq_zero, ← mul_eq_zero_iff_left (show t ^ 2 ≠ 0 by positivity), ← energyGap_eq_moments
    ht.ne' hcos, energyGap_eq_zero_iff_tStar ht htwo]

end RayleighKernel.Profile
