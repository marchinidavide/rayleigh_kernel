import RayleighKernel.Numerics.Constants
import RayleighKernel.Benchmarks.EMA2

noncomputable section
namespace RayleighKernel.Numerics

open Set
open RayleighKernel.Profile

private theorem lambdaStar_div_four_mem_roundingBin : Profile.lambdaStar / 4 ∈ Set.Ioo
    (54976798355 / 10^11 : ℝ) (54976798365 / 10^11 : ℝ) := by
  rcases lambdaStar_mem_roundingBin with ⟨hl, hu⟩
  constructor <;> nlinarith

private theorem objective_reduction_mem_roundingBin :
    100 * (1 - Profile.lambdaStar / 4) ∈ Set.Ioo
      (45015 / 1000 : ℝ) (45025 / 1000 : ℝ) := by
  rcases lambdaStar_mem_roundingBin with ⟨hl, hu⟩
  constructor <;> nlinarith

private theorem turnover_reduction_mem_roundingBin :
    100 * (1 - Real.sqrt (Profile.lambdaStar / 4)) ∈ Set.Ioo
      (25845 / 1000 : ℝ) (25855 / 1000 : ℝ) := by
  have hnonneg : 0 ≤ Profile.lambdaStar / 4 :=
    div_nonneg Profile.lambdaStar_pos.le (by norm_num)
  have hs : 0 ≤ Real.sqrt (Profile.lambdaStar / 4) := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt (Profile.lambdaStar / 4)) ^ 2 = Profile.lambdaStar / 4 :=
    Real.sq_sqrt hnonneg
  rcases lambdaStar_mem_roundingBin with ⟨hl, hu⟩
  constructor <;> nlinarith

theorem optimizer_ema2_objective_ratio_mem_roundingBin {L : ℝ} (hL : 0 < L) :
    ((Analysis.HalfLineH1.optimizer L hL).rayleighQuotient /
      RayleighKernel.rayleighQuotient (RayleighKernel.ema2Profile L)) ∈ Set.Ioo
      (54976798355 / 10^11 : ℝ) (54976798365 / 10^11 : ℝ) := by
  rw [RayleighKernel.optimizer_ema2_objective_ratio hL]
  exact lambdaStar_div_four_mem_roundingBin

theorem optimizer_ema2_objective_reduction_percent_mem_roundingBin
    {L : ℝ} (hL : 0 < L) :
    100 * (1 - ((Analysis.HalfLineH1.optimizer L hL).rayleighQuotient /
      RayleighKernel.rayleighQuotient (RayleighKernel.ema2Profile L))) ∈ Set.Ioo
      (45015 / 1000 : ℝ) (45025 / 1000 : ℝ) := by
  rw [RayleighKernel.optimizer_ema2_objective_ratio hL]
  exact objective_reduction_mem_roundingBin

theorem optimizer_ema2_turnover_reduction_percent_mem_roundingBin
    {L : ℝ} (hL : 0 < L) :
    100 * (1 - Real.sqrt
      ((Analysis.HalfLineH1.optimizer L hL).rayleighQuotient /
        RayleighKernel.rayleighQuotient (RayleighKernel.ema2Profile L))) ∈ Set.Ioo
      (25845 / 1000 : ℝ) (25855 / 1000 : ℝ) := by
  rw [RayleighKernel.optimizer_ema2_objective_ratio hL]
  exact turnover_reduction_mem_roundingBin

end RayleighKernel.Numerics
