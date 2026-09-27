import RayleighKernel.Optimizer.Explicit
import RayleighKernel.Profile.Derivatives
import RayleighKernel.Profile.Consistency
import Mathlib.Analysis.Calculus.LHopital

noncomputable section

namespace RayleighKernel.Profile

open Set Filter
open scoped Topology

private theorem second_order_left_asymptotic
    (f f' f'' : ℝ → ℝ) (hf : f 1 = 0) (hf' : f' 1 = 0)
    (hfd : ∀ y, HasDerivAt f (f' y) y)
    (hf'd : ∀ y, HasDerivAt f' (f'' y) y)
    (hcont : ContinuousAt f'' 1) :
    Tendsto (fun y : ℝ => f y / (1 - y) ^ 2) (𝓝[<] 1) (𝓝 (f'' 1 / 2)) := by
  let g : ℝ → ℝ := fun y => y - 1
  let q : ℝ → ℝ := fun y => (y - 1) ^ 2
  have hg (y : ℝ) : HasDerivAt g 1 y := by
    change HasDerivAt (fun z : ℝ => z - 1) 1 y
    simpa using (hasDerivAt_id y).sub_const 1
  have hq (y : ℝ) : HasDerivAt q (2 * (y - 1)) y := by
    change HasDerivAt (fun z : ℝ => (z - 1) ^ 2) (2 * (y - 1)) y
    convert ((hasDerivAt_id y).sub_const 1).pow 2 using 1
    · rfl
    · simp only [id_eq]
      ring
  have hg' : ∀ᶠ y in 𝓝[<] (1 : ℝ), (1 : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall (fun _ => one_ne_zero)
  have hq' : ∀ᶠ y in 𝓝[<] (1 : ℝ), (2 * (y - 1) : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt hy))
  have hg0 : Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun y : ℝ => y - 1) (𝓝 (1 : ℝ)) (𝓝 0) := by
      convert (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 1) (𝓝 1)).sub_const 1 using 1 <;>
        simp
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hq0 : Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa [q] using hg0.pow 2
  have hf0 : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    rw [← hf]
    exact (hfd 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hf'0 : Tendsto f' (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    rw [← hf']
    exact (hf'd 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun y : ℝ => f' y / g y) (𝓝[<] 1) (𝓝 (f'' 1)) := by
    apply HasDerivAt.lhopital_zero_nhdsLT (Filter.Eventually.of_forall hf'd)
      (Filter.Eventually.of_forall hg) hg' hf'0 hg0
    simpa [g] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h := HasDerivAt.lhopital_zero_nhdsLT (Filter.Eventually.of_forall hfd)
    (Filter.Eventually.of_forall hq) hq' hf0 hq0
      (by
        convert hquot.div_const 2 using 1
        funext y
        field_simp
        ring)
  convert h using 1
  funext y
  ring

private theorem tStar_mem_Ioo : tStar ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
  exact ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar, tStar_lt_two_pi⟩

@[simp] theorem FStar_zero : FStar 0 = 0 := by
  simp [FStar, value_zero]

theorem slope_tStar_zero_eq : slope tStar 0 = 1 + tStar * AStar := by
  simp [slope, AStar]
  ring

theorem FStar_hasDerivAt_zero : HasDerivAt FStar (1 + tStar * AStar) 0 := by
  rw [show FStar = value tStar from funext FStar_apply]
  convert value_hasDerivAt tStar 0 using 1
  exact slope_tStar_zero_eq.symm

theorem deriv_FStar_zero : deriv FStar 0 = 1 + tStar * AStar :=
  FStar_hasDerivAt_zero.deriv

theorem one_add_tStar_mul_AStar_pos : 0 < 1 + tStar * AStar := by
  rw [← slope_tStar_zero_eq, slope_zero_eq_initialSlope tStar_mem_Ioo.1.ne'
    (sin_half_ne_zero_of_cos_ne_one (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo))]
  have h := initialSlope_sub_two_pos (lt_trans pi_lt_sqrt_twelve sqrt_twelve_lt_tStar)
    tStar_lt_two_pi
  have hinit : 2 < initialSlope tStar := by linarith
  rw [← slope_zero_eq_initialSlope tStar_mem_Ioo.1.ne'
    (sin_half_ne_zero_of_cos_ne_one (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo))] at hinit
  linarith

theorem deriv_FStar_zero_pos : 0 < deriv FStar 0 := by
  rw [deriv_FStar_zero]
  exact one_add_tStar_mul_AStar_pos

theorem FStar_zero_right_asymptotic :
    Tendsto (fun y : ℝ => FStar y / y) (𝓝[>] 0)
      (𝓝 (1 + tStar * AStar)) := by
  simpa [FStar_zero, div_eq_mul_inv, mul_comm] using
    (FStar_hasDerivAt_zero.tendsto_slope_zero_right)

theorem FStar_one : FStar 1 = 0 := by
  rw [FStar_apply, value_one tStar_mem_Ioo.1.ne'
    (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo)]

theorem FStar_hasDerivAt (y : ℝ) : HasDerivAt FStar (slope tStar y) y := by
  rw [show FStar = value tStar from funext FStar_apply]
  exact value_hasDerivAt tStar y

theorem deriv_FStar (y : ℝ) : deriv FStar y = slope tStar y :=
  (FStar_hasDerivAt y).deriv

theorem deriv_FStar_one : deriv FStar 1 = 0 := by
  rw [deriv_FStar, slope_one tStar_mem_Ioo.1.ne'
    (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo)]

theorem CStar_lt_one : CStar < 1 := by
  have hlt : I1Star < I0Star := by
    unfold I1Star I0Star
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun y => y * value tStar y) (g := value tStar) zero_lt_one
      (continuous_id.mul (continuous_value tStar)).continuousOn
      (continuous_value tStar).continuousOn
      (by intro y hy
          by_cases hy1 : y = 1
          · subst y
            simp [value_one tStar_mem_Ioo.1.ne'
              (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo)]
          · have hp := value_pos tStar_mem_Ioo ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩
            nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) hp.le])
      (by exact ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, by
        have hp := value_pos tStar_mem_Ioo
          (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1)
        nlinarith [hp]⟩)
  have hprod : CStar * I0Star < I0Star := by
    rw [CStar_mul_I0Star_eq_I1Star]
    exact hlt
  nlinarith [I0Star_pos]

theorem second_deriv_FStar_one : deriv (deriv FStar) 1 = tStar ^ 2 * (1 - CStar) := by
  rw [show deriv FStar = slope tStar from funext deriv_FStar, deriv_slope]
  simpa [CStar, value_one tStar_mem_Ioo.1.ne'
    (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo)] using (ode_identity tStar 1)

theorem second_deriv_FStar_one_pos : 0 < deriv (deriv FStar) 1 := by
  rw [second_deriv_FStar_one]
  exact mul_pos (sq_pos_of_pos tStar_mem_Ioo.1) (sub_pos.mpr CStar_lt_one)

theorem FStar_one_left_asymptotic :
    Tendsto (fun y : ℝ => FStar y / (1 - y) ^ 2) (𝓝[<] 1)
      (𝓝 (deriv (deriv FStar) 1 / 2)) := by
  have h := second_order_left_asymptotic FStar (slope tStar) (curvature tStar)
    FStar_one (slope_one tStar_mem_Ioo.1.ne'
      (cos_ne_one_of_mem_Ioo_two_pi tStar_mem_Ioo)) FStar_hasDerivAt
    (fun y => slope_hasDerivAt tStar y) (continuous_curvature tStar).continuousAt
  convert h using 1
  rw [show deriv FStar = slope tStar from funext deriv_FStar, deriv_slope]

theorem FStar_one_left_asymptotic_explicit :
    Tendsto (fun y : ℝ => FStar y / (1 - y) ^ 2) (𝓝[<] 1)
      (𝓝 (tStar ^ 2 * (1 - CStar) / 2)) := by
  rw [← second_deriv_FStar_one]
  exact FStar_one_left_asymptotic

end RayleighKernel.Profile
