import RayleighKernel.Optimizer.Explicit
noncomputable section
namespace RayleighKernel.Analysis.HalfLineH1
open MeasureTheory Set
structure MainOptimizerData (L : ℝ) (hL : 0 < L) where
  optimizer_isAdmissible : (optimizer L hL).IsAdmissible L
  optimizer_isMinimizer : (optimizer L hL).IsMinimizer L
  minimizer_iff_optimizer : ∀ {f : HalfLineH1}, f.IsMinimizer L ↔ f = optimizer L hL
  continuousRep_optimizer : ∀ x, (optimizer L hL).continuousRep x = optimizerProfile L x
  optimizer_continuousRep_of_mem : ∀ {x}, x ∈ Icc (0 : ℝ) (optimizerSupport L) →
    (optimizer L hL).continuousRep x =
      1 / (optimizerSupport L * Profile.I0Star) * Profile.FStar (x / optimizerSupport L)
  optimizer_continuousRep_of_not_mem : ∀ {x}, x ∉ Icc (0 : ℝ) (optimizerSupport L) →
    (optimizer L hL).continuousRep x = 0
  optimizer_pos_iff : ∀ {x}, 0 < optimizerProfile L x ↔ x ∈ Ioo 0 (optimizerSupport L)
  optimizer_continuousRep_pos_iff : ∀ {x},
    0 < (optimizer L hL).continuousRep x ↔ x ∈ Ioo 0 (optimizerSupport L)
  minimizer_ae_unique : ∀ {f : HalfLineH1}, f.IsMinimizer L →
    f.continuousRep =ᵐ[volume] (optimizer L hL).continuousRep
  minimizer_continuousRep_unique : ∀ {f : HalfLineH1}, f.IsMinimizer L →
    f.continuousRep = (optimizer L hL).continuousRep
  support_identity : optimizerSupport L = L / Profile.CStar
  support_ratio : optimizerSupport L / L = Profile.kappaStar
  kappa_ratio : Profile.kappaStar = Profile.I0Star / Profile.I1Star
  kappa_CStar : Profile.kappaStar = 1 / Profile.CStar
  kappa_trigonometric : Profile.kappaStar = (Profile.tStar * (Real.cos Profile.tStar - 1)) /
    (Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar)
  optimizer_quotient : (optimizer L hL).rayleighQuotient = Profile.lambdaStar / L ^ 2
  minimum : Lambda L = Profile.lambdaStar / L ^ 2
  dimensionless_minimum : L ^ 2 * Lambda L = Profile.lambdaStar
  sharp_inequality : ∀ {f : HalfLineH1}, f.IsAdmissible L → Profile.lambdaStar / L ^ 2 * f.squareEnergy ≤ f.dirichletEnergy
  sharp_equality : ∀ {f : HalfLineH1}, f.IsAdmissible L → (Profile.lambdaStar / L ^ 2 * f.squareEnergy = f.dirichletEnergy ↔ f = optimizer L hL)
  sharp_equality_ae : ∀ {f : HalfLineH1}, f.IsAdmissible L →
    (Profile.lambdaStar / L ^ 2 * f.squareEnergy = f.dirichletEnergy ↔
      f.continuousRep =ᵐ[volume] (optimizer L hL).continuousRep)
  scale_free : ∀ z, scaleFreeOptimizerProfile z = L * optimizerProfile L (L * z)
  scale_free_representative : ∀ z,
    L * (optimizer L hL).continuousRep (L * z) = scaleFreeOptimizerProfile z
  scale_free_mass : RayleighKernel.mass scaleFreeOptimizerProfile = 1
  scale_free_firstMoment : RayleighKernel.firstMoment scaleFreeOptimizerProfile = 1
theorem mainOptimizerTheorem (L : ℝ) (hL : 0 < L) : MainOptimizerData L hL where
  optimizer_isAdmissible := optimizer_isAdmissible hL
  optimizer_isMinimizer := optimizer_isMinimizer hL
  minimizer_iff_optimizer := isMinimizer_iff_eq_optimizer hL
  continuousRep_optimizer := continuousRep_optimizer hL
  optimizer_continuousRep_of_mem := fun hx => by
    rw [continuousRep_optimizer hL, optimizerProfile_of_mem hx]
  optimizer_continuousRep_of_not_mem := fun hx => by
    rw [continuousRep_optimizer hL, optimizerProfile_of_not_mem hx]
  optimizer_pos_iff := optimizerProfile_pos_iff hL
  optimizer_continuousRep_pos_iff := by
    intro x
    rw [continuousRep_optimizer hL]
    exact optimizerProfile_pos_iff hL
  minimizer_ae_unique := continuousRep_ae_eq_optimizer_of_isMinimizer hL
  minimizer_continuousRep_unique := fun hf => by
    funext x
    exact continuousRep_eq_continuousRep_optimizer_of_isMinimizer hL hf x
  support_identity := optimizerSupport_eq_div hL
  support_ratio := optimizerSupport_div hL
  kappa_ratio := Profile.I0Star_div_I1Star_eq_kappaStar.symm
  kappa_CStar := Profile.kappaStar_eq_one_div_CStar
  kappa_trigonometric := Profile.kappaStar_eq_trigonometric
  optimizer_quotient := rayleighQuotient_optimizer hL
  minimum := Lambda_eq_lambdaStar_div_sq hL
  dimensionless_minimum := by
    rw [Lambda_eq_lambdaStar_div_sq hL]
    field_simp
  sharp_inequality := sharp_dirichletEnergy hL
  sharp_equality := sharp_dirichletEnergy_eq_iff_eq_optimizer hL
  sharp_equality_ae := sharp_dirichletEnergy_eq_iff_continuousRep_ae_eq_optimizer hL
  scale_free := scaleFreeOptimizerProfile_eq_mul_optimizerProfile hL
  scale_free_representative := fun z =>
    mul_continuousRep_optimizer_eq_scaleFreeOptimizerProfile hL z
  scale_free_mass := mass_scaleFreeOptimizerProfile
  scale_free_firstMoment := firstMoment_scaleFreeOptimizerProfile
end RayleighKernel.Analysis.HalfLineH1
