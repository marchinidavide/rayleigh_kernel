import RayleighKernel.Numerics.RootBracket
import RayleighKernel.Optimizer.Explicit
import RayleighKernel.Optimizer.Endpoints
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace RayleighKernel.Numerics
open Set
open RayleighKernel.Profile

private def cL : ℝ := -909574918715993819541224261933921244531 / 10^39
private def cU : ℝ := -909574918715993819541224261933921244530 / 10^39
private def sL : ℝ := -415539970692102297178434542990880983410 / 10^39
private def sU : ℝ := -415539970692102297178434542990880983409 / 10^39

private theorem err80 : ‖(tMinus : ℂ) * Complex.I‖ / 81 ≤ 1 / 2 := by
  rw [norm_real_mul_I]
  norm_num [tMinus, abs_of_nonneg]

private theorem cos_box : cL < Real.cos tMinus ∧ Real.cos tMinus < cU := by
  let e : ℝ := 1 / 10^65
  have h := cos_expTaylor_error 80 tMinus err80
  rw [norm_real_mul_I] at h
  have he : |Real.cos tMinus - (expTaylor 80 ((tMinus : ℂ) * Complex.I)).re| < e := by
    dsimp [e]
    exact lt_of_le_of_lt h (by norm_num [tMinus, abs_of_nonneg])
  rw [abs_lt] at he
  have hl : cL + e < (expTaylor 80 ((tMinus : ℂ) * Complex.I)).re := by
    norm_num [cL, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hu : (expTaylor 80 ((tMinus : ℂ) * Complex.I)).re < cU - e := by
    norm_num [cU, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  constructor
  · linarith
  · linarith

private theorem sin_box : sL < Real.sin tMinus ∧ Real.sin tMinus < sU := by
  let e : ℝ := 1 / 10^65
  have h := sin_expTaylor_error 80 tMinus err80
  rw [norm_real_mul_I] at h
  have he : |Real.sin tMinus - (expTaylor 80 ((tMinus : ℂ) * Complex.I)).im| < e := by
    dsimp [e]
    exact lt_of_le_of_lt h (by norm_num [tMinus, abs_of_nonneg])
  rw [abs_lt] at he
  have hl : sL + e < (expTaylor 80 ((tMinus : ℂ) * Complex.I)).im := by
    norm_num [sL, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hu : (expTaylor 80 ((tMinus : ℂ) * Complex.I)).im < sU - e := by
    norm_num [sU, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  constructor <;> linarith

private theorem trig_box_star :
    cL - 2/10^49 < Real.cos Profile.tStar ∧
      Real.cos Profile.tStar < cU + 2/10^49 ∧
    sL - 2/10^49 < Real.sin Profile.tStar ∧
      Real.sin Profile.tStar < sU + 2/10^49 := by
  have ht := tStar_mem_rootBracket
  have hd1 : |Profile.tStar - tMinus| < 2/10^49 := by
    rw [abs_lt]
    constructor
    · have : 0 < tStar - tMinus := sub_pos.mpr ht.1
      linarith
    · have : tStar - tMinus < tPlus - tMinus := sub_lt_sub_right ht.2 tMinus
      norm_num [tMinus, tPlus] at this ⊢
      linarith
  have hc := Real.abs_cos_sub_cos_le Profile.tStar tMinus
  have hs := Real.abs_sin_sub_sin_le Profile.tStar tMinus
  have hc' : |Real.cos Profile.tStar - Real.cos tMinus| < 2/10^49 := lt_of_le_of_lt hc hd1
  have hs' : |Real.sin Profile.tStar - Real.sin tMinus| < 2/10^49 := lt_of_le_of_lt hs hd1
  rw [abs_lt] at hc' hs'
  rcases cos_box with ⟨cl,cu⟩
  rcases sin_box with ⟨sl,su⟩
  have hcLo : cL - 2/10^49 < Real.cos Profile.tStar := by linarith
  have hcHi : Real.cos Profile.tStar < cU + 2/10^49 := by linarith
  have hsLo : sL - 2/10^49 < Real.sin Profile.tStar := by linarith
  have hsHi : Real.sin Profile.tStar < sU + 2/10^49 := by linarith
  exact ⟨hcLo, hcHi, hsLo, hsHi⟩

private theorem coeff_bounds :
    (4977105454133845 / 10^16 : ℝ) < coefficientA Profile.tStar ∧
      coefficientA Profile.tStar < 4977105454133855 / 10^16 ∧
    (4153706496517605 / 10^16 : ℝ) < coefficientC Profile.tStar ∧
      coefficientC Profile.tStar < 4153706496517615 / 10^16 := by
  rcases trig_box_star with ⟨cl,cu,sl,su⟩
  have ht := tStar_mem_rootBracket
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have htsL : tPlus * (sL - 2/10^49) < Profile.tStar * Real.sin Profile.tStar := by
    have h1 : tPlus * (sL - 2/10^49) < Profile.tStar * (sL - 2/10^49) :=
      (mul_lt_mul_of_neg_right ht.2 (by norm_num [sL]))
    have h2 : Profile.tStar * (sL - 2/10^49) < Profile.tStar * Real.sin Profile.tStar :=
      mul_lt_mul_of_pos_left (by linarith [cl]) (by linarith [ht.1, ht0])
    exact h1.trans h2
  have htsU : Profile.tStar * Real.sin Profile.tStar < tMinus * (sU + 2/10^49) := by
    have h1 : Profile.tStar * Real.sin Profile.tStar < Profile.tStar * (sU + 2/10^49) :=
      mul_lt_mul_of_pos_left (by linarith [su]) (by linarith [ht.1, ht0])
    have h2 : Profile.tStar * (sU + 2/10^49) < tMinus * (sU + 2/10^49) :=
      mul_lt_mul_of_neg_right ht.1 (by norm_num [sU])
    exact h1.trans h2
  have htcL : tPlus * (cL - 2/10^49) < Profile.tStar * Real.cos Profile.tStar := by
    have h1 : tPlus * (cL - 2/10^49) < Profile.tStar * (cL - 2/10^49) :=
      mul_lt_mul_of_neg_right ht.2 (by norm_num [cL])
    have h2 : Profile.tStar * (cL - 2/10^49) < Profile.tStar * Real.cos Profile.tStar :=
      mul_lt_mul_of_pos_left (by linarith [cl]) (by linarith [ht.1, ht0])
    exact h1.trans h2
  have htcU : Profile.tStar * Real.cos Profile.tStar < tMinus * (cU + 2/10^49) := by
    have h1 : Profile.tStar * Real.cos Profile.tStar < Profile.tStar * (cU + 2/10^49) :=
      mul_lt_mul_of_pos_left (by linarith [cu]) (by linarith [ht.1, ht0])
    have h2 : Profile.tStar * (cU + 2/10^49) < tMinus * (cU + 2/10^49) :=
      mul_lt_mul_of_neg_right ht.1 (by norm_num [cU])
    exact h1.trans h2
  have hDlo : tPlus * (cL - 2/10^49 - 1) < Profile.tStar * (Real.cos Profile.tStar - 1) := by
    exact (mul_lt_mul_of_neg_right ht.2 (by norm_num [cL])).trans
      (mul_lt_mul_of_pos_left (by linarith [cl]) (by linarith [ht.1, ht0]))
  have hDhi : Profile.tStar * (Real.cos Profile.tStar - 1) < tMinus * (cU + 2/10^49 - 1) := by
    exact (mul_lt_mul_of_pos_left (by linarith [cu]) (by linarith [ht.1, ht0])).trans
      (mul_lt_mul_of_neg_right ht.1 (by norm_num [cU]))
  have hD : Profile.tStar * (Real.cos Profile.tStar - 1) < 0 := by
    have : cU + 2/10^49 - 1 < 0 := by norm_num [cU]
    exact lt_of_lt_of_le hDhi (mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) (le_of_lt this))
  have hNAL : tPlus * (sL - 2/10^49) + (cL - 2/10^49) - 1 <
      Profile.tStar * Real.sin Profile.tStar + Real.cos Profile.tStar - 1 := by linarith [htsL, cl]
  have hNAU : Profile.tStar * Real.sin Profile.tStar + Real.cos Profile.tStar - 1 <
      tMinus * (sU + 2/10^49) + (cU + 2/10^49) - 1 := by linarith [htsU, cu]
  have hNCL : tPlus * (cL - 2/10^49) - (sU + 2/10^49) <
      Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar := by linarith [htcL, su]
  have hNCU : Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar <
      tMinus * (cU + 2/10^49) - (sL - 2/10^49) := by linarith [htcU, sl]
  have hcornerAL : tMinus * (sU + 2/10^49) + (cU + 2/10^49) - 1 <
      (4977105454133845 / 10^16 : ℝ) * (tPlus * (cL - 2/10^49 - 1)) := by
    norm_num [tMinus, tPlus, cL, cU, sU]
  have hcornerAU : (4977105454133855 / 10^16 : ℝ) *
      (tMinus * (cU + 2/10^49 - 1)) <
      tPlus * (sL - 2/10^49) + (cL - 2/10^49) - 1 := by
    norm_num [tMinus, tPlus, cL, cU, sL]
  have hcornerCL : tMinus * (cU + 2/10^49) - (sL - 2/10^49) <
      (4153706496517605 / 10^16 : ℝ) * (tPlus * (cL - 2/10^49 - 1)) := by
    norm_num [tMinus, tPlus, cL, cU, sL]
  have hcornerCU : (4153706496517615 / 10^16 : ℝ) *
      (tMinus * (cU + 2/10^49 - 1)) <
      tPlus * (cL - 2/10^49) - (sU + 2/10^49) := by
    norm_num [tMinus, tPlus, cL, cU, sU]
  have hnumA_l :
      Profile.tStar * Real.sin Profile.tStar + Real.cos Profile.tStar - 1 <
        4977105454133845 / 10^16 * (Profile.tStar * (Real.cos Profile.tStar - 1)) := by
    calc
      _ < tMinus * (sU + 2/10^49) + (cU + 2/10^49) - 1 := hNAU
      _ < (4977105454133845 / 10^16 : ℝ) *
          (tPlus * (cL - 2/10^49 - 1)) := hcornerAL
      _ < (4977105454133845 / 10^16 : ℝ) *
          (Profile.tStar * (Real.cos Profile.tStar - 1)) := by
        exact mul_lt_mul_of_pos_left hDlo (by norm_num)
  have hnumA_u :
      4977105454133855 / 10^16 * (Profile.tStar * (Real.cos Profile.tStar - 1)) <
        Profile.tStar * Real.sin Profile.tStar + Real.cos Profile.tStar - 1 := by
    calc
      _ < (4977105454133855 / 10^16 : ℝ) *
          (tMinus * (cU + 2/10^49 - 1)) := by
        exact mul_lt_mul_of_pos_left hDhi (by norm_num)
      _ < tPlus * (sL - 2/10^49) + (cL - 2/10^49) - 1 := hcornerAU
      _ < _ := hNAL
  have hnumC_l :
      Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar <
        4153706496517605 / 10^16 * (Profile.tStar * (Real.cos Profile.tStar - 1)) := by
    calc
      _ < tMinus * (cU + 2/10^49) - (sL - 2/10^49) := hNCU
      _ < (4153706496517605 / 10^16 : ℝ) *
          (tPlus * (cL - 2/10^49 - 1)) := hcornerCL
      _ < _ := mul_lt_mul_of_pos_left hDlo (by norm_num)
  have hnumC_u :
      4153706496517615 / 10^16 * (Profile.tStar * (Real.cos Profile.tStar - 1)) <
        Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar := by
    calc
      _ < (4153706496517615 / 10^16 : ℝ) *
          (tMinus * (cU + 2/10^49 - 1)) := mul_lt_mul_of_pos_left hDhi (by norm_num)
      _ < tPlus * (cL - 2/10^49) - (sU + 2/10^49) := hcornerCU
      _ < _ := hNCL
  constructor
  · exact (lt_div_iff_of_neg hD).2 hnumA_l
  constructor
  · exact (div_lt_iff_of_neg hD).2 hnumA_u
  constructor
  · exact (lt_div_iff_of_neg hD).2 hnumC_l
  · exact (div_lt_iff_of_neg hD).2 hnumC_u

theorem AStar_mem_roundingBin : Profile.AStar ∈ Set.Ioo
      (4977105454133845 / 10^16 : ℝ) (4977105454133855 / 10^16 : ℝ) := by
  simpa [Profile.AStar, Profile.coefficientA] using ⟨coeff_bounds.1, coeff_bounds.2.1⟩

theorem CStar_mem_roundingBin : Profile.CStar ∈ Set.Ioo
       (4153706496517605 / 10^16 : ℝ) (4153706496517615 / 10^16 : ℝ) := by
    simpa [Profile.CStar, Profile.coefficientC] using ⟨coeff_bounds.2.2.1, coeff_bounds.2.2.2⟩

private theorem CStar_mem_tightBin : Profile.CStar ∈ Set.Ioo
    (415370649651761323 / 10^18 : ℝ)
    (415370649651761324 / 10^18 : ℝ) := by
  rcases trig_box_star with ⟨cl,cu,sl,su⟩
  have ht := tStar_mem_rootBracket
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have htsU : Profile.tStar * Real.sin Profile.tStar <
      tMinus * (sU + 2/10^49) := by
    have h1 : Profile.tStar * Real.sin Profile.tStar <
        Profile.tStar * (sU + 2/10^49) :=
      mul_lt_mul_of_pos_left (by linarith [su]) (by linarith [ht.1, ht0])
    have h2 : Profile.tStar * (sU + 2/10^49) <
        tMinus * (sU + 2/10^49) :=
      mul_lt_mul_of_neg_right ht.1 (by norm_num [sU])
    exact h1.trans h2
  have htcL : tPlus * (cL - 2/10^49) <
      Profile.tStar * Real.cos Profile.tStar := by
    have h1 : tPlus * (cL - 2/10^49) <
        Profile.tStar * (cL - 2/10^49) :=
      mul_lt_mul_of_neg_right ht.2 (by norm_num [cL])
    have h2 : Profile.tStar * (cL - 2/10^49) <
        Profile.tStar * Real.cos Profile.tStar :=
      mul_lt_mul_of_pos_left (by linarith [cl]) (by linarith [ht.1, ht0])
    exact h1.trans h2
  have htcU : Profile.tStar * Real.cos Profile.tStar <
      tMinus * (cU + 2/10^49) := by
    have h1 : Profile.tStar * Real.cos Profile.tStar <
        Profile.tStar * (cU + 2/10^49) :=
      mul_lt_mul_of_pos_left (by linarith [cu]) (by linarith [ht.1, ht0])
    have h2 : Profile.tStar * (cU + 2/10^49) <
        tMinus * (cU + 2/10^49) :=
      mul_lt_mul_of_neg_right ht.1 (by norm_num [cU])
    exact h1.trans h2
  have hDlo : tPlus * (cL - 2/10^49 - 1) <
      Profile.tStar * (Real.cos Profile.tStar - 1) := by
    exact (mul_lt_mul_of_neg_right ht.2 (by norm_num [cL])).trans
      (mul_lt_mul_of_pos_left (by linarith [cl]) (by linarith [ht.1, ht0]))
  have hDup : Profile.tStar * (Real.cos Profile.tStar - 1) <
      tMinus * (cU + 2/10^49 - 1) := by
    exact (mul_lt_mul_of_pos_left (by linarith [cu]) (by linarith [ht.1, ht0])).trans
      (mul_lt_mul_of_neg_right ht.1 (by norm_num [cU]))
  have hD : Profile.tStar * (Real.cos Profile.tStar - 1) < 0 := by
    have h : cU + 2/10^49 - 1 < 0 := by norm_num [cU]
    exact lt_of_lt_of_le hDup
      (mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) (le_of_lt h))
  have hNlo : tPlus * (cL - 2/10^49) - (sU + 2/10^49) <
      Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar := by
    linarith [htcL, su]
  have hNup : Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar <
      tMinus * (cU + 2/10^49) - (sL - 2/10^49) := by
    linarith [htcU, sl]
  have hcornerL : tMinus * (cU + 2/10^49) - (sL - 2/10^49) <
      (415370649651761323 / 10^18 : ℝ) *
        (tPlus * (cL - 2/10^49 - 1)) := by
    norm_num [tMinus, tPlus, cL, cU, sL]
  have hcornerU : (415370649651761324 / 10^18 : ℝ) *
      (tMinus * (cU + 2/10^49 - 1)) <
      tPlus * (cL - 2/10^49) - (sU + 2/10^49) := by
    norm_num [tMinus, tPlus, cL, cU, sU]
  have hlow : (415370649651761323 / 10^18 : ℝ) <
      Profile.coefficientC Profile.tStar := by
    rw [Profile.coefficientC]
    apply (lt_div_iff_of_neg hD).2
    calc
      Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar <
          tMinus * (cU + 2/10^49) - (sL - 2/10^49) := hNup
      _ < (415370649651761323 / 10^18 : ℝ) *
          (tPlus * (cL - 2/10^49 - 1)) := hcornerL
      _ < (415370649651761323 / 10^18 : ℝ) *
          (Profile.tStar * (Real.cos Profile.tStar - 1)) :=
        mul_lt_mul_of_pos_left hDlo (by norm_num)
  have hupp : Profile.coefficientC Profile.tStar <
      (415370649651761324 / 10^18 : ℝ) := by
    rw [Profile.coefficientC]
    apply (div_lt_iff_of_neg hD).2
    calc
      (415370649651761324 / 10^18 : ℝ) *
          (Profile.tStar * (Real.cos Profile.tStar - 1)) <
          (415370649651761324 / 10^18 : ℝ) *
            (tMinus * (cU + 2/10^49 - 1)) :=
        mul_lt_mul_of_pos_left hDup (by norm_num)
      _ < tPlus * (cL - 2/10^49) - (sU + 2/10^49) := hcornerU
      _ < Profile.tStar * Real.cos Profile.tStar - Real.sin Profile.tStar := hNlo
  exact ⟨by simpa [Profile.CStar] using hlow, by simpa [Profile.CStar] using hupp⟩

theorem kappaStar_mem_roundingBin : Profile.kappaStar ∈ Set.Ioo
    (24074883500757225 / 10^16 : ℝ)
    (24074883500757235 / 10^16 : ℝ) := by
  rcases CStar_mem_tightBin with ⟨hcL, hcU⟩
  rw [Profile.kappaStar_eq_one_div_CStar]
  have hC : 0 < Profile.CStar := Profile.CStar_pos
  have hqL : (0 : ℝ) < 24074883500757225 / 10^16 := by norm_num
  have hqU : (0 : ℝ) < 24074883500757235 / 10^16 := by norm_num
  have hlow : (24074883500757225 / 10^16 : ℝ) * Profile.CStar < 1 := by
    calc
      (24074883500757225 / 10^16 : ℝ) * Profile.CStar <
          (24074883500757225 / 10^16 : ℝ) *
            (415370649651761324 / 10^18 : ℝ) :=
        mul_lt_mul_of_pos_left hcU hqL
      _ < 1 := by norm_num
  have hupp : (1 : ℝ) <
      (24074883500757235 / 10^16 : ℝ) * Profile.CStar := by
    calc
      (1 : ℝ) < (24074883500757235 / 10^16 : ℝ) *
          (415370649651761323 / 10^18 : ℝ) := by norm_num
      _ < (24074883500757235 / 10^16 : ℝ) * Profile.CStar :=
        mul_lt_mul_of_pos_left hcL hqU
  constructor
  · exact (lt_div_iff₀ hC).2 hlow
  · exact (div_lt_iff₀ hC).2 hupp

theorem lambdaStar_mem_roundingBin : Profile.lambdaStar ∈ Set.Ioo
    (21990719345624955 / 10^16 : ℝ)
    (21990719345624965 / 10^16 : ℝ) := by
  rcases CStar_mem_tightBin with ⟨hcL, hcU⟩
  have ht := tStar_mem_rootBracket
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have htstar : 0 < Profile.tStar := lt_trans ht0 ht.1
  have hcl : 0 < (415370649651761323 / 10^18 : ℝ) := by norm_num
  have hcu : 0 < (415370649651761324 / 10^18 : ℝ) := by norm_num
  have ht2L : tMinus^2 < Profile.tStar^2 := by
    nlinarith [ht.1, ht0]
  have ht2U : Profile.tStar^2 < tPlus^2 := by
    nlinarith [ht.2, htstar]
  have hc2L : (415370649651761323 / 10^18 : ℝ)^2 < Profile.CStar^2 := by
    nlinarith [hcL, hcl]
  have hc2U : Profile.CStar^2 < (415370649651761324 / 10^18 : ℝ)^2 := by
    nlinarith [hcU, hcu]
  have hprodL : tMinus^2 *
      (415370649651761323 / 10^18 : ℝ)^2 <
      Profile.tStar^2 * Profile.CStar^2 := by
    calc
      tMinus^2 * (415370649651761323 / 10^18 : ℝ)^2 <
          Profile.tStar^2 * (415370649651761323 / 10^18 : ℝ)^2 :=
        mul_lt_mul_of_pos_right ht2L (sq_pos_of_pos hcl)
      _ < Profile.tStar^2 * Profile.CStar^2 :=
        mul_lt_mul_of_pos_left hc2L (sq_pos_of_pos htstar)
  have hprodU : Profile.tStar^2 * Profile.CStar^2 <
      tPlus^2 * (415370649651761324 / 10^18 : ℝ)^2 := by
    calc
      Profile.tStar^2 * Profile.CStar^2 <
          tPlus^2 * Profile.CStar^2 :=
        mul_lt_mul_of_pos_right ht2U (sq_pos_of_pos Profile.CStar_pos)
      _ < tPlus^2 * (415370649651761324 / 10^18 : ℝ)^2 :=
        mul_lt_mul_of_pos_left hc2U (sq_pos_of_pos (by norm_num [tPlus]))
  rw [Profile.lambdaStar_eq]
  constructor
  · exact (by norm_num [tMinus] :
      (21990719345624955 / 10^16 : ℝ) <
        tMinus^2 * (415370649651761323 / 10^18 : ℝ)^2).trans hprodL
  · exact hprodU.trans (by norm_num [tPlus] :
      tPlus^2 * (415370649651761324 / 10^18 : ℝ)^2 <
        (21990719345624965 / 10^16 : ℝ))

theorem I0Star_mem_roundingBin : Profile.I0Star ∈ Set.Ioo
    (3024961166919075 / 10^16 : ℝ)
    (3024961166919085 / 10^16 : ℝ) := by
  let d : ℝ := 2 / 10^49
  let cl : ℝ := cL - d
  let cu : ℝ := cU + d
  let sl : ℝ := sL - d
  let su : ℝ := sU + d
  let NLower : ℝ := tMinus^2 * (1 + cl) - 4 * (tMinus * su) + 4 * (1 - cu)
  let NUpper : ℝ := tPlus^2 * (1 + cu) - 4 * (tPlus * sl) + 4 * (1 - cl)
  let DLower : ℝ := 2 * tMinus^2 * (1 - cu)
  let DUpper : ℝ := 2 * tPlus^2 * (1 - cl)
  let N : ℝ := tStar^2 * (1 + Real.cos tStar) - 4 * (tStar * Real.sin tStar) +
    4 * (1 - Real.cos tStar)
  let D : ℝ := 2 * (tStar^2 * (1 - Real.cos tStar))
  have ht := tStar_mem_rootBracket
  have htr := trig_box_star
  have hcl : cl < Real.cos tStar := by dsimp [cl, d]; linarith [htr.1]
  have hcu : Real.cos tStar < cu := by dsimp [cu, d]; linarith [htr.2.1]
  have hsl : sl < Real.sin tStar := by dsimp [sl, d]; linarith [htr.2.2.1]
  have hsu : Real.sin tStar < su := by dsimp [su, d]; linarith [htr.2.2.2]
  have hcl1pos : 0 < 1 + cl := by
    norm_num [cl, cL, d]
  have hcu1pos : 0 < 1 + cu := by
    norm_num [cu, cU, d]
  have hslneg : sl < 0 := by
    norm_num [sl, sL, d]
  have hsuneg : su < 0 := by
    norm_num [su, sU, d]
  have honecu : 0 < 1 - cu := by
    norm_num [cu, cU, d]
  have honecl : 0 < 1 - cl := by
    norm_num [cl, cL, d]
  have h1cl : 1 + cl < 1 + Real.cos tStar := by linarith [hcl]
  have h1cu : 1 + Real.cos tStar < 1 + cu := by linarith [hcu]
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have htp0 : 0 < tPlus := by norm_num [tPlus]
  have htp : 0 < tStar := lt_trans ht0 ht.1
  have hcos : Real.cos tStar < 1 := by
    linarith [show cu < 1 by norm_num [cu, cU, d]]
  have hden : 0 < D := by dsimp [D]; positivity
  have hN : NLower < N ∧ N < NUpper := by
    dsimp [NLower, NUpper]
    have htm2 : tMinus^2 < tStar^2 := by nlinarith [ht.1]
    have htp2 : tStar^2 < tPlus^2 := by nlinarith [ht.2]
    have h1l : tMinus^2 * (1 + cl) < tStar^2 * (1 + Real.cos tStar) := by
      calc
        tMinus^2 * (1 + cl) < tStar^2 * (1 + cl) :=
          mul_lt_mul_of_pos_right htm2 hcl1pos
        _ < tStar^2 * (1 + Real.cos tStar) :=
          mul_lt_mul_of_pos_left h1cl (sq_pos_of_pos htp)
    have h1u : tStar^2 * (1 + Real.cos tStar) < tPlus^2 * (1 + cu) := by
      calc
        tStar^2 * (1 + Real.cos tStar) < tStar^2 * (1 + cu) :=
          mul_lt_mul_of_pos_left h1cu (sq_pos_of_pos htp)
        _ < tPlus^2 * (1 + cu) :=
          mul_lt_mul_of_pos_right htp2 hcu1pos
    have hsUpper1 : tStar * Real.sin tStar < tStar * su :=
      mul_lt_mul_of_pos_left hsu htp
    have hsUpper2 : tStar * su < tMinus * su :=
      mul_lt_mul_of_neg_right ht.1 hsuneg
    have hsUpper : tStar * Real.sin tStar < tMinus * su := hsUpper1.trans hsUpper2
    have hsLower1 : tPlus * sl < tStar * sl :=
      mul_lt_mul_of_neg_right ht.2 hslneg
    have hsLower2 : tStar * sl < tStar * Real.sin tStar :=
      mul_lt_mul_of_pos_left hsl htp
    have hsLower : tPlus * sl < tStar * Real.sin tStar := hsLower1.trans hsLower2
    have h3l : 1 - cu < 1 - Real.cos tStar := by linarith
    have h3u : 1 - Real.cos tStar < 1 - cl := by linarith
    have hn2l : -4 * (tMinus * su) < -4 * (tStar * Real.sin tStar) := by linarith [hsUpper]
    have hn2u : -4 * (tStar * Real.sin tStar) < -4 * (tPlus * sl) := by linarith [hsLower]
    have hn3l : 4 * (1 - cu) < 4 * (1 - Real.cos tStar) := by linarith [h3l]
    have hn3u : 4 * (1 - Real.cos tStar) < 4 * (1 - cl) := by linarith [h3u]
    constructor
    · dsimp [N]
      linarith [h1l, hn2l, hn3l]
    · dsimp [N]
      linarith [h1u, hn2u, hn3u]
  have hD : DLower < D ∧ D < DUpper := by
    dsimp [DLower, DUpper]
    have htm2 : tMinus^2 < tStar^2 := by nlinarith [ht.1]
    have htp2 : tStar^2 < tPlus^2 := by nlinarith [ht.2]
    have hdLower1 : tMinus^2 * (1-cu) < tStar^2 * (1-cu) :=
      mul_lt_mul_of_pos_right htm2 honecu
    have hdLower2 : tStar^2 * (1-cu) < tStar^2 * (1-Real.cos tStar) :=
      mul_lt_mul_of_pos_left (by linarith [hcu]) (sq_pos_of_pos htp)
    have hdLower0 := hdLower1.trans hdLower2
    have hdLower : 2 * (tMinus^2 * (1-cu)) < 2 * (tStar^2 * (1-Real.cos tStar)) :=
      mul_lt_mul_of_pos_left hdLower0 (by norm_num)
    have hdUpper1 : tStar^2 * (1-Real.cos tStar) < tStar^2 * (1-cl) :=
      mul_lt_mul_of_pos_left (by linarith [hcl]) (sq_pos_of_pos htp)
    have hdUpper2 : tStar^2 * (1-cl) < tPlus^2 * (1-cl) :=
      mul_lt_mul_of_pos_right htp2 honecl
    have hdUpper0 := hdUpper1.trans hdUpper2
    have hdUpper : 2 * (tStar^2 * (1-Real.cos tStar)) < 2 * (tPlus^2 * (1-cl)) :=
      mul_lt_mul_of_pos_left hdUpper0 (by norm_num)
    constructor <;> simpa [DLower, DUpper, D, mul_assoc] using ‹_›
  have hformula : Profile.I0Star = N / D := by
    rw [Profile.I0Star_eq]
    have hf := Profile.momentZero_eq_formula htp.ne'
      (Profile.cos_ne_one_of_mem_Ioo_two_pi
        ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar, tStar_lt_two_pi⟩)
    rw [hf]
    simp only [Profile.momentZeroFormula, N, D]
    ring
  rw [hformula]
  have hqL : (0 : ℝ) < 3024961166919075 / 10^16 := by norm_num
  have hqU : (0 : ℝ) < 3024961166919085 / 10^16 := by norm_num
  have hQL : (3024961166919075 / 10^16 : ℝ) * D <
      (3024961166919075 / 10^16 : ℝ) * DUpper :=
    mul_lt_mul_of_pos_left hD.2 hqL
  have hQLc : (3024961166919075 / 10^16 : ℝ) * DUpper < NLower := by
    norm_num [DUpper, NLower, tMinus, tPlus, cL, cU, sL, sU, d, cl, cu, sl, su]
  have hQUc : NUpper < (3024961166919085 / 10^16 : ℝ) * DLower := by
    norm_num [DLower, NUpper, tMinus, tPlus, cL, cU, sL, sU, d, cl, cu, sl, su]
  have hQU : (3024961166919085 / 10^16 : ℝ) * DLower <
      (3024961166919085 / 10^16 : ℝ) * D :=
    mul_lt_mul_of_pos_left hD.1 hqU
  have hNL : NLower < N := hN.1
  have hNU : N < NUpper := hN.2
  have hden' : 0 < D := hden
  constructor
  · exact (lt_div_iff₀ hden').2 (hQL.trans (hQLc.trans hNL))
  · exact (div_lt_iff₀ hden').2 (hNU.trans (hQUc.trans hQU))

theorem I1Star_mem_roundingBin : Profile.I1Star ∈ Set.Ioo
    (1256480085074525 / 10^16 : ℝ)
    (1256480085074535 / 10^16 : ℝ) := by
  let d : ℝ := 2 / 10^49
  let cl : ℝ := cL - d
  let cu : ℝ := cU + d
  let sl : ℝ := sL - d
  let su : ℝ := sU + d
  let N : ℝ := Profile.tStar * (Real.cos Profile.tStar + 2) -
    3 * Real.sin Profile.tStar
  let D : ℝ := 6 * (Profile.tStar * (1 - Real.cos Profile.tStar))
  let NLower : ℝ := tMinus * (cl + 2) - 3 * su
  let NUpper : ℝ := tPlus * (cu + 2) - 3 * sl
  let DLower : ℝ := 6 * (tMinus * (1 - cu))
  let DUpper : ℝ := 6 * (tPlus * (1 - cl))
  have ht := tStar_mem_rootBracket
  have htr := trig_box_star
  have hcl : cl < Real.cos Profile.tStar := by
    dsimp [cl, d]
    linarith [htr.1]
  have hcu : Real.cos Profile.tStar < cu := by
    dsimp [cu, d]
    linarith [htr.2.1]
  have hsl : sl < Real.sin Profile.tStar := by
    dsimp [sl, d]
    linarith [htr.2.2.1]
  have hsu : Real.sin Profile.tStar < su := by
    dsimp [su, d]
    linarith [htr.2.2.2]
  have hcl2pos : 0 < 2 + cl := by norm_num [cl, cL, d]
  have hcu2pos : 0 < 2 + cu := by norm_num [cu, cU, d]
  have honecu : 0 < 1 - cu := by norm_num [cu, cU, d]
  have honecl : 0 < 1 - cl := by norm_num [cl, cL, d]
  have htMinus_pos : 0 < tMinus := by norm_num [tMinus]
  have htPlus_pos : 0 < tPlus := by norm_num [tPlus]
  have htStar_pos : 0 < Profile.tStar := lt_trans htMinus_pos ht.1
  have hcos_lt_one : Real.cos Profile.tStar < 1 := by
    linarith [show cu < 1 by norm_num [cu, cU, d]]
  have hnum : NLower < N ∧ N < NUpper := by
    have htl : tMinus * (cl + 2) <
        Profile.tStar * (Real.cos Profile.tStar + 2) := by
      calc
        tMinus * (cl + 2) < Profile.tStar * (cl + 2) :=
          mul_lt_mul_of_pos_right ht.1 (by linarith [hcl2pos])
        _ < Profile.tStar * (Real.cos Profile.tStar + 2) :=
          mul_lt_mul_of_pos_left (by linarith [hcl]) htStar_pos
    have htu : Profile.tStar * (Real.cos Profile.tStar + 2) <
        tPlus * (cu + 2) := by
      calc
        Profile.tStar * (Real.cos Profile.tStar + 2) <
            Profile.tStar * (cu + 2) :=
          mul_lt_mul_of_pos_left (by linarith [hcu]) htStar_pos
        _ < tPlus * (cu + 2) :=
          mul_lt_mul_of_pos_right ht.2 (by linarith [hcu2pos])
    have hsinL : -3 * su < -3 * Real.sin Profile.tStar := by
      linarith [hsu]
    have hsinU : -3 * Real.sin Profile.tStar < -3 * sl := by
      linarith [hsl]
    constructor <;> dsimp [NLower, NUpper, N] <;> linarith
  have hden : DLower < D ∧ D < DUpper := by
    have hdl : tMinus * (1 - cu) <
        Profile.tStar * (1 - Real.cos Profile.tStar) := by
      calc
        tMinus * (1 - cu) < Profile.tStar * (1 - cu) :=
          mul_lt_mul_of_pos_right ht.1 honecu
        _ < Profile.tStar * (1 - Real.cos Profile.tStar) :=
          mul_lt_mul_of_pos_left (by linarith [hcu]) htStar_pos
    have hdu : Profile.tStar * (1 - Real.cos Profile.tStar) <
        tPlus * (1 - cl) := by
      calc
        Profile.tStar * (1 - Real.cos Profile.tStar) <
            Profile.tStar * (1 - cl) :=
          mul_lt_mul_of_pos_left (by linarith [hcl]) htStar_pos
        _ < tPlus * (1 - cl) :=
          mul_lt_mul_of_pos_right ht.2 honecl
    constructor
    · dsimp [DLower, D]
      exact mul_lt_mul_of_pos_left hdl (by norm_num)
    · dsimp [D, DUpper]
      exact mul_lt_mul_of_pos_left hdu (by norm_num)
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (by norm_num)
      (mul_pos htStar_pos (by linarith [hcos_lt_one]))
  have hformula : Profile.I1Star = N / D := by
    rw [Profile.I1Star_eq]
    have hcos : Real.cos Profile.tStar ≠ 1 :=
      Profile.cos_ne_one_of_mem_Ioo_two_pi
        ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar,
          tStar_lt_two_pi⟩
    rw [Profile.momentOne_eq_formula htStar_pos.ne' hcos]
    simp only [Profile.momentOneFormula, N, D]
    ring
  have hqL : (0 : ℝ) < 1256480085074525 / 10^16 := by norm_num
  have hqU : (0 : ℝ) < 1256480085074535 / 10^16 := by norm_num
  have hcornerL : (1256480085074525 / 10^16 : ℝ) * DUpper < NLower := by
    norm_num [tMinus, tPlus, cL, cU, sL, sU, d, cl, cu, sl, su,
      NLower, NUpper, DLower, DUpper]
  have hcornerU : NUpper <
      (1256480085074535 / 10^16 : ℝ) * DLower := by
    norm_num [tMinus, tPlus, cL, cU, sL, sU, d, cl, cu, sl, su,
      NLower, NUpper, DLower, DUpper]
  rw [hformula]
  constructor
  · apply (lt_div_iff₀ hDpos).2
    exact (mul_lt_mul_of_pos_left hden.2 hqL).trans
      (hcornerL.trans hnum.1)
  · apply (div_lt_iff₀ hDpos).2
    exact hnum.2.trans (hcornerU.trans (mul_lt_mul_of_pos_left hden.1 hqU))

theorem deriv_FStar_zero_mem_roundingBin : deriv Profile.FStar 0 ∈ Set.Ioo
    (277689086555 / 10^11 : ℝ)
    (277689086565 / 10^11 : ℝ) := by
  rw [Profile.deriv_FStar_zero]
  rcases AStar_mem_roundingBin with ⟨haL, haU⟩
  have ht := tStar_mem_rootBracket
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have ha0 : 0 < (4977105454133845 / 10^16 : ℝ) := by norm_num
  have hprodL : tMinus * (4977105454133845 / 10^16 : ℝ) <
      Profile.tStar * Profile.AStar := by
    calc
      tMinus * (4977105454133845 / 10^16 : ℝ) <
          Profile.tStar * (4977105454133845 / 10^16 : ℝ) :=
        mul_lt_mul_of_pos_right ht.1 ha0
      _ < Profile.tStar * Profile.AStar :=
        mul_lt_mul_of_pos_left haL (lt_trans ht0 ht.1)
  have hprodU : Profile.tStar * Profile.AStar <
      tPlus * (4977105454133855 / 10^16 : ℝ) := by
    calc
      Profile.tStar * Profile.AStar <
          Profile.tStar * (4977105454133855 / 10^16 : ℝ) :=
        mul_lt_mul_of_pos_left haU (lt_trans ht0 ht.1)
      _ < tPlus * (4977105454133855 / 10^16 : ℝ) := by
        exact mul_lt_mul_of_pos_right ht.2 (by norm_num)
  constructor
  · norm_num [tMinus] at hprodL ⊢
    linarith
  · norm_num [tPlus] at hprodU ⊢
    linarith

theorem second_deriv_FStar_one_mem_roundingBin :
    deriv (deriv Profile.FStar) 1 ∈ Set.Ioo
    (745158121175 / 10^11 : ℝ)
    (745158121185 / 10^11 : ℝ) := by
  rw [Profile.second_deriv_FStar_one]
  rcases CStar_mem_tightBin with ⟨hcL, hcU⟩
  have ht := tStar_mem_rootBracket
  have ht0 : 0 < tMinus := by norm_num [tMinus]
  have htstar : 0 < Profile.tStar := lt_trans ht0 ht.1
  have htl : tMinus ^ 2 < Profile.tStar ^ 2 := by
    nlinarith [ht.1, ht0]
  have htu : Profile.tStar ^ 2 < tPlus ^ 2 := by
    nlinarith [ht.2, htstar]
  have hbl : 0 < (1 - (415370649651761324 / 10^18 : ℝ)) := by
    norm_num
  have hbu : 0 < (1 - (415370649651761323 / 10^18 : ℝ)) := by
    norm_num
  have hB : 0 < 1 - Profile.CStar := by linarith [hcU]
  have hprodL : tMinus ^ 2 * (1 - (415370649651761324 / 10^18 : ℝ)) <
      Profile.tStar ^ 2 * (1 - Profile.CStar) := by
    calc
      tMinus ^ 2 * (1 - (415370649651761324 / 10^18 : ℝ)) <
          Profile.tStar ^ 2 * (1 - (415370649651761324 / 10^18 : ℝ)) :=
        mul_lt_mul_of_pos_right htl hbl
      _ < Profile.tStar ^ 2 * (1 - Profile.CStar) :=
        mul_lt_mul_of_pos_left (by linarith [hcU]) (sq_pos_of_pos htstar)
  have hprodU : Profile.tStar ^ 2 * (1 - Profile.CStar) <
      tPlus ^ 2 * (1 - (415370649651761323 / 10^18 : ℝ)) := by
    calc
      Profile.tStar ^ 2 * (1 - Profile.CStar) <
          Profile.tStar ^ 2 * (1 - (415370649651761323 / 10^18 : ℝ)) :=
        mul_lt_mul_of_pos_left (by linarith [hcL]) (sq_pos_of_pos htstar)
      _ < tPlus ^ 2 * (1 - (415370649651761323 / 10^18 : ℝ)) :=
        mul_lt_mul_of_pos_right htu hbu
  constructor
  · norm_num [tMinus] at hprodL ⊢
    linarith
  · norm_num [tPlus] at hprodU ⊢
    linarith

end RayleighKernel.Numerics
