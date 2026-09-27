import RayleighKernel.Probability.PowerCost
import RayleighKernel.Probability.GaussianTurnover

noncomputable section
open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal NNReal
namespace RayleighKernel.Probability

private theorem half_standardGaussian_rpow_integral {g : ℝ} (hg : 1 ≤ g) :
    ∫ x : ℝ in Set.Ioi 0, Real.rpow x g * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      Real.rpow 2 ((g - 1) / 2) * Real.Gamma ((g + 1) / 2) := by
  let a : ℝ := (g - 1) / 2
  have ha : -1 < a := by dsimp [a]; linarith
  have hcomp := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => Real.rpow u a * Real.exp (-(1 / 2 : ℝ) * u))
    (p := (2 : ℝ)) (by norm_num)
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (g + 1) / 2) (r := (1 / 2 : ℝ)) (by linarith) (by norm_num)
  have hcomp' :
      ∫ x : ℝ in Set.Ioi 0, 2 * x *
          (Real.rpow (x ^ 2) a * Real.exp (-(1 / 2 : ℝ) * (x ^ 2))) =
        Real.rpow 2 ((g + 1) / 2) * Real.Gamma ((g + 1) / 2) := by
    calc
      _ = ∫ x : ℝ in Set.Ioi 0, (2 * x ^ (2 - 1)) •
          (Real.rpow (x ^ 2) a * Real.exp (-(1 / 2 : ℝ) * (x ^ 2))) := by
        congr 1
        funext x
        simp only [smul_eq_mul]
        norm_num
      _ = ∫ y : ℝ in Set.Ioi 0, Real.rpow y a * Real.exp (-(1 / 2 : ℝ) * y) := hcomp
      _ = _ := by
        convert hgamma using 1
        · congr 1
          funext y
          dsimp [a]
          rw [show (-(1 / 2 : ℝ) * y) = -(1 / 2 * y) by ring]
          congr 1
          ring_nf
        · norm_num
  have heq : (fun x : ℝ => Real.rpow x g * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun x : ℝ => (2 : ℝ)⁻¹ *
        (2 * x * (Real.rpow (x ^ 2) a * Real.exp (-(1 / 2 : ℝ) * (x ^ 2))))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    dsimp [a]
    have hpow : Real.rpow (Real.rpow x 2) ((g - 1) / 2) =
        Real.rpow x (g - 1) := by
      calc
        _ = Real.rpow x (2 * ((g - 1) / 2)) :=
          (Real.rpow_mul (le_of_lt hx') 2 ((g - 1) / 2)).symm
        _ = _ := by congr 1; ring
    have hpow' : (x ^ (2 : ℕ)) ^ ((g - 1) / 2) = Real.rpow x (g - 1) := by
      simpa [Real.rpow_two] using hpow
    rw [hpow']
    have hmul : Real.rpow x g = x * Real.rpow x (g - 1) := by
      calc
        Real.rpow x g = Real.rpow x (1 + (g - 1)) := by congr 1; ring
        _ = Real.rpow x 1 * Real.rpow x (g - 1) := Real.rpow_add hx' _ _
        _ = _ := by simp
    change Real.rpow x g * _ = _
    rw [hmul]
    field_simp
  rw [integral_congr_ae heq, integral_const_mul, hcomp']
  dsimp [a]
  have hpow : Real.rpow 2 ((g + 1) / 2) =
      2 * Real.rpow 2 ((g - 1) / 2) := by
    calc
      Real.rpow 2 ((g + 1) / 2) = Real.rpow 2 (1 + (g - 1) / 2) := by
        congr 1; ring
      _ = Real.rpow 2 1 * Real.rpow 2 ((g - 1) / 2) :=
        Real.rpow_add (by norm_num) _ _
      _ = 2 * Real.rpow 2 ((g - 1) / 2) := by norm_num
  change (2 : ℝ)⁻¹ * (Real.rpow 2 ((g + 1) / 2) * _) = _
  rw [hpow]
  ring_nf
  simp [mul_comm]

theorem integral_rpow_abs_standardGaussian {g : ℝ} (hg : 1 ≤ g) :
    ∫ x : ℝ, Real.rpow |x| g ∂gaussianReal 0 1 =
      Real.rpow 2 (g / 2) * Real.Gamma ((g + 1) / 2) / Real.sqrt Real.pi := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal_def]
  have hfun : (fun x : ℝ => (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) * Real.rpow |x| g) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
        (Real.rpow |x| g * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    funext x
    simp
    ring_nf
  change (∫ x : ℝ, (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
    Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) * Real.rpow |x| g) = _
  rw [hfun, integral_const_mul]
  rw [show (fun x : ℝ => Real.rpow |x| g *
      Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      (fun x : ℝ => (Real.rpow |x| g * Real.exp (-(1 / 2 : ℝ) * |x| ^ 2))) by
    funext x
    simp [sq_abs]]
  rw [show (fun x : ℝ => Real.rpow |x| g *
      Real.exp (-(1 / 2 : ℝ) * |x| ^ 2)) =
      (fun x : ℝ => (fun y : ℝ => Real.rpow y g *
        Real.exp (-(1 / 2 : ℝ) * y ^ 2)) |x|) by
    funext x
    simp [sq_abs]]
  rw [show (∫ x : ℝ, (fun y : ℝ => Real.rpow y g *
      Real.exp (-(1 / 2 : ℝ) * y ^ 2)) |x|) =
      2 * ∫ x : ℝ in Set.Ioi 0, Real.rpow x g *
        Real.exp (-(1 / 2 : ℝ) * x ^ 2) by
    have hh := (integral_comp_abs (f := fun x : ℝ =>
      Real.rpow x g * Real.exp (-(1 / 2 : ℝ) * x ^ 2)))
    simpa only [Function.comp_apply] using hh]
  rw [half_standardGaussian_rpow_integral hg]
  simp only [mul_one]
  have hsqrt : Real.sqrt (2 * Real.pi) =
      Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow2 : Real.rpow 2 (g / 2) =
      Real.sqrt 2 * Real.rpow 2 ((g - 1) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow 2 (g / 2) = Real.rpow 2 (1 / 2 + (g - 1) / 2) := by
        congr 1; ring
      _ = Real.rpow 2 (1 / 2) * Real.rpow 2 ((g - 1) / 2) :=
        Real.rpow_add (by norm_num) _ _
  rw [hsqrt, hpow2]
  field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos),
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem PowerProjectionIsotropic.moment_quotient_eq_standardGaussianGamma
    {Ω : Type*} [MeasurableSpace Ω]
    {r : ℤ → Ω → ℝ} {μ : Measure Ω} {σr mrg g : ℝ}
    (h : PowerProjectionIsotropic r μ σr mrg g)
    (hmrg : mrg = Real.rpow σr g *
      (∫ x : ℝ, Real.rpow |x| g ∂gaussianReal 0 1)) :
    mrg / Real.rpow σr g =
      Real.rpow 2 (g / 2) * Real.Gamma ((g + 1) / 2) / Real.sqrt Real.pi := by
  rw [hmrg, integral_rpow_abs_standardGaussian h.exponent_one_le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos h.scale_pos g)]

end RayleighKernel.Probability
