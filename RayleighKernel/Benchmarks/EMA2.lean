import RayleighKernel.Variational
import RayleighKernel.Variational.Triangular
import RayleighKernel.Optimizer.Explicit
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
namespace RayleighKernel
open MeasureTheory Set

def ema2Profile (L x : ℝ) : ℝ := 4 * x / L ^ 2 * Real.exp (-2 * x / L)

private lemma scalar_q1 {L : ℝ} (hL : 0 < L) :
    (2 / L) ^ (-(1 + 1 : ℝ) / 1) * (1 / 1) * Real.Gamma ((1 + 1) / 1) = L^2/4 := by
  have hb : 0 ≤ 2 / L := by positivity
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg hb, Real.rpow_natCast]
  field_simp
  ring

private lemma scalar_q2 {L : ℝ} (hL : 0 < L) :
    (2 / L) ^ (-(2 + 1 : ℝ) / 1) * (1 / 1) * Real.Gamma ((2 + 1) / 1) = L^3/4 := by
  have hb : 0 ≤ 2 / L := by positivity
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg hb, Real.rpow_natCast]
  field_simp
  ring

private lemma integral_q1 {L : ℝ} (hL : 0 < L) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(2/L)*x) = L^2/4 := by
  have hb : 0 < 2 / L := by positivity
  convert integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ))
      (b := 2 / L) (by norm_num) (by norm_num) hb using 1
  · simp [div_eq_mul_inv]
  · exact (scalar_q1 hL).symm

private lemma integral_q2 {L : ℝ} (hL : 0 < L) :
    ∫ x in Ioi (0 : ℝ), x^2 * Real.exp (-(2/L)*x) = L^3/4 := by
  have hb : 0 < 2 / L := by positivity
  convert integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (2 : ℝ))
      (b := 2 / L) (by norm_num) (by norm_num) hb using 1
  · simp [div_eq_mul_inv]
  · exact (scalar_q2 hL).symm

private lemma integrable1_Ici {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-b * x)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b)
      (by norm_num) one_pos hb using 1
  simp

private lemma integrable2_Ici {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-b * x)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := b)
      (by norm_num) one_pos hb using 1
  simp

private lemma integrable0_Ici {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.exp (-b * x)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := b)
      (by norm_num) one_pos hb using 1
  simp

private lemma integral0_Ici {b : ℝ} (hb : 0 < b) :
    ∫ x in Ici (0 : ℝ), Real.exp (-b * x) = 1 / b := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (0 : ℝ))
    (b := b) (by norm_num) (by norm_num) hb
  rw [integral_Ici_eq_integral_Ioi]
  convert h using 1
  · simp
  · simp [Real.rpow_neg_one]

private lemma integral1_Ici {b : ℝ} (hb : 0 < b) :
    ∫ x in Ici (0 : ℝ), x * Real.exp (-b * x) = 1 / b ^ 2 := by
  rw [integral_Ici_eq_integral_Ioi]
  convert integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ))
      (b := b) (by norm_num) (by norm_num) hb using 1
  · simp
  · norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg (le_of_lt hb)]

private lemma integral2_Ici {b : ℝ} (hb : 0 < b) :
    ∫ x in Ici (0 : ℝ), x ^ 2 * Real.exp (-b * x) = 2 / b ^ 3 := by
  rw [integral_Ici_eq_integral_Ioi]
  convert integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (2 : ℝ))
      (b := b) (by norm_num) (by norm_num) hb using 1
  · simp
  · norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg (le_of_lt hb)]
    exact mul_comm _ _

theorem ema2Profile_nonneg {L x : ℝ} (hx : x ∈ halfLine) (hL : 0 < L) :
    0 ≤ ema2Profile L x := by
  unfold ema2Profile
  have hx' : 0 ≤ x := hx
  positivity

@[simp] theorem ema2Profile_zero (L : ℝ) : ema2Profile L 0 = 0 := by simp [ema2Profile]

theorem hasDerivAt_ema2Profile {L x : ℝ} (hL : 0 < L) :
    HasDerivAt (ema2Profile L)
      (4 / L ^ 2 * Real.exp (-2 * x / L) * (1 - 2 * x / L)) x := by
  have harg : HasDerivAt (fun y : ℝ => -2 * y / L) (-2 / L) x := by
    simpa [Function.id_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).const_mul (-2)).div_const L
  have hpref : HasDerivAt (fun y : ℝ => 4 * y / L^2) (4 / L^2) x := by
    simpa [Function.id_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).const_mul 4).div_const (L^2)
  have hexp := (Real.hasDerivAt_exp _).comp x harg
  have hm := hpref.mul hexp
  convert hm using 1
  · funext y
    simp [ema2Profile, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp only [Function.comp_apply]
    field_simp
    ring

theorem deriv_ema2Profile {L x : ℝ} (hL : 0 < L) :
    deriv (ema2Profile L) x =
      4 / L ^ 2 * Real.exp (-2 * x / L) * (1 - 2 * x / L) :=
  (hasDerivAt_ema2Profile hL).deriv

private lemma ema2Profile_sq_eq {L x : ℝ} :
    ema2Profile L x ^ 2 = (16 / L ^ 4) * (x ^ 2 * Real.exp (-(4 / L) * x)) := by
  unfold ema2Profile
  rw [pow_two]
  have he : Real.exp ((-2 / L) * x) * Real.exp ((-2 / L) * x) =
      Real.exp (-(4 / L) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (4 * x / L ^ 2 * Real.exp (-2 * x / L)) *
        (4 * x / L ^ 2 * Real.exp (-2 * x / L)) =
        (16 / L ^ 4) * (x ^ 2 *
          (Real.exp ((-2 / L) * x) * Real.exp ((-2 / L) * x))) := by ring_nf
    _ = (16 / L ^ 4) * (x ^ 2 * Real.exp (-(4 / L) * x)) := by rw [he]

private lemma deriv_ema2Profile_sq_eq {L x : ℝ} (hL : 0 < L) :
    deriv (ema2Profile L) x ^ 2 =
      16 / L ^ 4 * Real.exp (-(4 / L) * x) -
        64 / L ^ 5 * (x * Real.exp (-(4 / L) * x)) +
        64 / L ^ 6 * (x ^ 2 * Real.exp (-(4 / L) * x)) := by
  rw [deriv_ema2Profile hL, pow_two]
  have he : Real.exp (-2 * x / L) * Real.exp (-2 * x / L) =
      Real.exp (-(4 / L) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    4 / L ^ 2 * Real.exp (-2 * x / L) * (1 - 2 * x / L) *
        (4 / L ^ 2 * Real.exp (-2 * x / L) * (1 - 2 * x / L)) =
        (16 / L ^ 4) * ((1 - 2 * x / L) ^ 2 *
          (Real.exp (-2 * x / L) * Real.exp (-2 * x / L))) := by ring
    _ = (16 / L ^ 4) * ((1 - 2 * x / L) ^ 2 *
          Real.exp (-(4 / L) * x)) := by rw [he]
    _ = 16 / L ^ 4 * Real.exp (-(4 / L) * x) -
        64 / L ^ 5 * (x * Real.exp (-(4 / L) * x)) +
        64 / L ^ 6 * (x ^ 2 * Real.exp (-(4 / L) * x)) := by
      field_simp [hL.ne']
      ring_nf

theorem ema2Profile_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (ema2Profile L) halfLine := by
  rw [show halfLine = Ici 0 by rfl]
  have h := integrable1_Ici (b := 2 / L) (by positivity : 0 < 2 / L)
  rw [show ema2Profile L =
      (fun x => (4 / L ^ 2) * (x * Real.exp (-(2 / L) * x))) by
        funext x; simp [ema2Profile, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]]
  exact h.const_mul (4 / L ^ 2)

theorem ema2Profile_firstMoment_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => x * ema2Profile L x) halfLine := by
  rw [show halfLine = Ici 0 by rfl]
  have h := integrable2_Ici (b := 2 / L) (by positivity : 0 < 2 / L)
  rw [show (fun x => x * ema2Profile L x) =
      (fun x => (4 / L ^ 2) * (x ^ 2 * Real.exp (-(2 / L) * x))) by
        funext x; simp [ema2Profile, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]; ring_nf]
  exact h.const_mul (4 / L ^ 2)

theorem ema2Profile_mass {L : ℝ} (hL : 0 < L) : mass (ema2Profile L) = 1 := by
  rw [mass, halfLine, integral_Ici_eq_integral_Ioi]
  rw [show (fun x => ema2Profile L x) =
      (fun x => (4 / L ^ 2) * (x * Real.exp (-(2 / L) * x))) by
    funext x; simp [ema2Profile, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]]
  rw [integral_const_mul, integral_q1 hL]
  field_simp [hL.ne']

theorem ema2Profile_firstMoment {L : ℝ} (hL : 0 < L) :
    firstMoment (ema2Profile L) = L := by
  rw [firstMoment, halfLine, integral_Ici_eq_integral_Ioi]
  rw [show (fun x => x * ema2Profile L x) =
      (fun x => (4 / L ^ 2) * (x ^ 2 * Real.exp (-(2 / L) * x))) by
    funext x; simp [ema2Profile, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]; ring_nf]
  rw [integral_const_mul, integral_q2 hL]
  field_simp [hL.ne']

theorem ema2Profile_square_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => ema2Profile L x ^ 2) halfLine := by
  have h := integrable2_Ici (b := 4 / L) (by positivity : 0 < 4 / L)
  rw [show (fun x => ema2Profile L x ^ 2) =
      (fun x => (16 / L ^ 4) * (x ^ 2 * Real.exp (-(4 / L) * x))) by
        funext x; exact ema2Profile_sq_eq]
  exact h.const_mul (16 / L ^ 4)

theorem ema2Profile_derivative_square_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => deriv (ema2Profile L) x ^ 2) halfLine := by
  let b : ℝ := 4 / L
  let u0 : ℝ → ℝ := fun x => (16 / L ^ 4) * Real.exp (-b * x)
  let u1 : ℝ → ℝ := fun x => (64 / L ^ 5) * (x * Real.exp (-b * x))
  let u2 : ℝ → ℝ := fun x => (64 / L ^ 6) * (x ^ 2 * Real.exp (-b * x))
  have hb : 0 < b := by dsimp [b]; positivity
  have hu0 : IntegrableOn u0 (Ici 0) := (integrable0_Ici hb).const_mul (16 / L ^ 4)
  have hu1 : IntegrableOn u1 (Ici 0) := (integrable1_Ici hb).const_mul (64 / L ^ 5)
  have hu2 : IntegrableOn u2 (Ici 0) := (integrable2_Ici hb).const_mul (64 / L ^ 6)
  have heq : (fun x => deriv (ema2Profile L) x ^ 2) = (u0 - u1) + u2 := by
    funext x
    exact deriv_ema2Profile_sq_eq hL
  rw [heq]
  exact (hu0.sub hu1).add hu2

theorem ema2Profile_squareEnergy {L : ℝ} (hL : 0 < L) :
    squareEnergy (ema2Profile L) = 1 / (2 * L) := by
  unfold squareEnergy halfLine
  rw [show (fun x => ema2Profile L x ^ 2) =
      (fun x => (16 / L ^ 4) * (x ^ 2 * Real.exp (-(4 / L) * x))) by
        funext x; exact ema2Profile_sq_eq]
  rw [integral_const_mul, integral2_Ici (by positivity : 0 < 4 / L)]
  field_simp
  ring

theorem ema2Profile_dirichletEnergy {L : ℝ} (hL : 0 < L) :
    dirichletEnergy (ema2Profile L) = 2 / L ^ 3 := by
  let b : ℝ := 4 / L
  let u0 : ℝ → ℝ := fun x => (16 / L ^ 4) * Real.exp (-b * x)
  let u1 : ℝ → ℝ := fun x => (64 / L ^ 5) * (x * Real.exp (-b * x))
  let u2 : ℝ → ℝ := fun x => (64 / L ^ 6) * (x ^ 2 * Real.exp (-b * x))
  have hb : 0 < b := by dsimp [b]; positivity
  have hu0 : IntegrableOn u0 (Ici 0) := (integrable0_Ici hb).const_mul (16 / L ^ 4)
  have hu1 : IntegrableOn u1 (Ici 0) := (integrable1_Ici hb).const_mul (64 / L ^ 5)
  have hu2 : IntegrableOn u2 (Ici 0) := (integrable2_Ici hb).const_mul (64 / L ^ 6)
  have heq : (fun x => deriv (ema2Profile L) x ^ 2) = (u0 - u1) + u2 := by
    funext x
    exact deriv_ema2Profile_sq_eq hL
  unfold dirichletEnergy halfLine
  rw [heq]
  change integral (volume.restrict (Ici 0)) ((u0 - u1) + u2) = _
  calc
    integral (volume.restrict (Ici 0)) ((u0 - u1) + u2) =
        integral (volume.restrict (Ici 0)) (u0 - u1) +
          integral (volume.restrict (Ici 0)) u2 :=
      MeasureTheory.integral_add (μ := volume.restrict (Ici 0)) (hu0.sub hu1) hu2
    _ = (integral (volume.restrict (Ici 0)) u0 -
          integral (volume.restrict (Ici 0)) u1) +
          integral (volume.restrict (Ici 0)) u2 := by
      exact congrArg (fun z => z + integral (volume.restrict (Ici 0)) u2)
        (MeasureTheory.integral_sub (μ := volume.restrict (Ici 0)) hu0 hu1)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      rw [integral0_Ici hb, integral1_Ici hb, integral2_Ici hb]
      dsimp [b]
      field_simp [hL.ne']
      ring

theorem ema2Profile_rayleighQuotient {L : ℝ} (hL : 0 < L) :
    rayleighQuotient (ema2Profile L) = 4 / L ^ 2 := by
  rw [rayleighQuotient, ema2Profile_dirichletEnergy hL, ema2Profile_squareEnergy hL]
  field_simp [hL.ne']
  ring

theorem Profile.lambdaStar_le_five_halves : Profile.lambdaStar ≤ 5 / 2 := by
  have hbound : Profile.lambdaStar / (1 : ℝ) ^ 2 ≤ 5 / (2 * (1 : ℝ) ^ 2) := by
    rw [← Analysis.HalfLineH1.Lambda_eq_lambdaStar_div_sq (by norm_num : (0 : ℝ) < 1)]
    calc
      Analysis.Lambda 1 ≤
          (Analysis.HalfLineH1.triangular 1 (by norm_num : (0 : ℝ) < 1)).rayleighQuotient :=
        Analysis.Lambda_le_of_isAdmissible
          (Analysis.HalfLineH1.triangular_isAdmissible (by norm_num : (0 : ℝ) < 1))
      _ = 5 / (2 * (1 : ℝ) ^ 2) :=
        Analysis.HalfLineH1.rayleighQuotient_triangular (by norm_num)
  have hLsq : 0 < (1 : ℝ) ^ 2 := by norm_num
  nlinarith [hbound]

theorem Profile.lambdaStar_lt_four : Profile.lambdaStar < 4 := by
  linarith [Profile.lambdaStar_le_five_halves]

theorem Analysis.HalfLineH1.optimizer_rayleighQuotient_lt_ema2 {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.optimizer L hL).rayleighQuotient <
      RayleighKernel.rayleighQuotient (ema2Profile L) := by
  rw [Analysis.HalfLineH1.rayleighQuotient_optimizer hL,
    ema2Profile_rayleighQuotient hL]
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  apply (div_lt_div_iff_of_pos_right hLsq).2
  exact Profile.lambdaStar_lt_four

theorem optimizer_ema2_objective_ratio {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.optimizer L hL).rayleighQuotient /
        RayleighKernel.rayleighQuotient (ema2Profile L) = Profile.lambdaStar / 4 := by
  rw [Analysis.HalfLineH1.rayleighQuotient_optimizer hL,
    ema2Profile_rayleighQuotient hL]
  field_simp [hL.ne']

theorem Analysis.HalfLineH1.optimizer_sqrt_rayleighQuotient_lt_ema2 {L : ℝ} (hL : 0 < L) :
    Real.sqrt ((Analysis.HalfLineH1.optimizer L hL).rayleighQuotient) <
      Real.sqrt (RayleighKernel.rayleighQuotient (ema2Profile L)) := by
  apply Real.sqrt_lt_sqrt
  · rw [Analysis.HalfLineH1.rayleighQuotient_optimizer hL]
    exact div_nonneg Profile.lambdaStar_pos.le (sq_nonneg L)
  · simpa [ema2Profile_rayleighQuotient hL] using
      Analysis.HalfLineH1.optimizer_rayleighQuotient_lt_ema2 hL

end RayleighKernel
