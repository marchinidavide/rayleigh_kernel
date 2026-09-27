import RayleighKernel.Optimizer.Normalize
import RayleighKernel.Scaling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace RayleighKernel.Profile

open Set MeasureTheory

def AStar : ℝ := coefficientA tStar
def CStar : ℝ := coefficientC tStar
def FStar (y : ℝ) : ℝ := value tStar y
def I0Star : ℝ := momentZero tStar
def I1Star : ℝ := momentOne tStar
def kappaStar : ℝ := 1 / CStar
def lambdaStar : ℝ := tStar ^ 2 * CStar ^ 2

@[simp] theorem FStar_apply (y : ℝ) : FStar y = value tStar y := rfl
@[simp] theorem AStar_eq : AStar = coefficientA tStar := rfl
@[simp] theorem CStar_eq : CStar = coefficientC tStar := rfl
@[simp] theorem I0Star_eq : I0Star = momentZero tStar := rfl
@[simp] theorem I1Star_eq : I1Star = momentOne tStar := rfl
@[simp] theorem kappaStar_eq : kappaStar = 1 / CStar := rfl
@[simp] theorem lambdaStar_eq : lambdaStar = tStar ^ 2 * CStar ^ 2 := rfl

theorem FStar_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < FStar y := by
  exact value_pos ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar,
    tStar_lt_two_pi⟩ hy

theorem I0Star_pos : 0 < I0Star := by
  unfold I0Star
  exact intervalIntegral.integral_pos zero_lt_one (continuous_value tStar).continuousOn
    (fun y hy => by
      by_cases h : y = 1
      · subst y
        rw [value_one (lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar).ne'
          (cos_ne_one_of_mem_Ioo_two_pi ⟨lt_trans (Real.sqrt_pos.2 (by norm_num))
            sqrt_twelve_lt_tStar, tStar_lt_two_pi⟩)]
      · exact (value_pos ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar,
          tStar_lt_two_pi⟩ ⟨hy.1, lt_of_le_of_ne hy.2 h⟩).le)
    ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, FStar_pos (by norm_num)⟩

theorem I1Star_pos : 0 < I1Star := by
  unfold I1Star
  apply intervalIntegral.integral_pos zero_lt_one
    (continuous_id.mul (continuous_value tStar)).continuousOn
  · intro y hy
    exact mul_nonneg hy.1.le (by
      by_cases h : y = 1
      · subst y
        rw [value_one (lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar).ne'
          (cos_ne_one_of_mem_Ioo_two_pi ⟨lt_trans (Real.sqrt_pos.2 (by norm_num))
            sqrt_twelve_lt_tStar, tStar_lt_two_pi⟩)]
      · exact (value_pos ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar,
          tStar_lt_two_pi⟩ ⟨hy.1, lt_of_le_of_ne hy.2 h⟩).le)
  · exact ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩,
      mul_pos (by norm_num) (FStar_pos (by norm_num))⟩

theorem CStar_mul_I0Star_eq_I1Star : CStar * I0Star = I1Star := by
  change coefficientC tStar * momentZero tStar = momentOne tStar
  exact (coefficientC_mul_momentZero_eq_momentOne_iff_tStar
    (lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar) tStar_lt_two_pi).mpr rfl

theorem CStar_pos : 0 < CStar := by
  by_contra h
  have hnonpos : CStar ≤ 0 := le_of_not_gt h
  have hprod : CStar * I0Star ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnonpos I0Star_pos.le
  have hprod' : 0 < CStar * I0Star := by rw [CStar_mul_I0Star_eq_I1Star]; exact I1Star_pos
  exact (not_lt_of_ge hprod) hprod'

theorem I1Star_div_I0Star_eq_CStar : I1Star / I0Star = CStar := by
  rw [div_eq_iff (ne_of_gt I0Star_pos)]
  exact CStar_mul_I0Star_eq_I1Star.symm

theorem I0Star_div_I1Star_eq_kappaStar : I0Star / I1Star = kappaStar := by
  rw [kappaStar]
  calc
    I0Star / I1Star = I0Star / (CStar * I0Star) := by rw [CStar_mul_I0Star_eq_I1Star]
    _ = 1 / CStar := by
      calc
        I0Star / (CStar * I0Star) = (I0Star / I0Star) / CStar := by
          rw [show CStar * I0Star = I0Star * CStar by ring]
          field_simp [ne_of_gt I0Star_pos, ne_of_gt CStar_pos]
        _ = 1 / CStar := by rw [div_self (ne_of_gt I0Star_pos)]

theorem kappaStar_eq_one_div_CStar : kappaStar = 1 / CStar := rfl
theorem kappaStar_pos : 0 < kappaStar := by rw [kappaStar]; exact one_div_pos.mpr CStar_pos

theorem kappaStar_eq_trigonometric :
    kappaStar = (tStar * (Real.cos tStar - 1)) /
      (tStar * Real.cos tStar - Real.sin tStar) := by
  rw [kappaStar, CStar, coefficientC]
  have ht : tStar ≠ 0 := (lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar).ne'
  have hcos : Real.cos tStar ≠ 1 := cos_ne_one_of_mem_Ioo_two_pi
    ⟨lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar, tStar_lt_two_pi⟩
  have hnum : tStar * Real.cos tStar - Real.sin tStar ≠ 0 := by
    intro h
    have : coefficientC tStar = 0 := by unfold coefficientC; rw [h, zero_div]
    exact (ne_of_gt CStar_pos) (by simpa [CStar] using this)
  field_simp [ht, sub_ne_zero.mpr hcos, hnum]

theorem lambdaStar_pos : 0 < lambdaStar := by
  rw [lambdaStar]
  exact mul_pos (sq_pos_of_pos (lt_trans (Real.sqrt_pos.2 (by norm_num)) sqrt_twelve_lt_tStar))
    (sq_pos_of_pos CStar_pos)

end RayleighKernel.Profile

namespace RayleighKernel.Analysis.HalfLineH1

open Set

def optimizerSupport (L : ℝ) : ℝ := Profile.kappaStar * L
def optimizerProfile (L x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) (optimizerSupport L) then
    (1 / (optimizerSupport L * Profile.I0Star)) * Profile.FStar (x / optimizerSupport L)
  else 0

theorem optimizerSupport_eq (L : ℝ) : optimizerSupport L = Profile.kappaStar * L := rfl
theorem optimizerSupport_pos {L : ℝ} (hL : 0 < L) : 0 < optimizerSupport L := by
  rw [optimizerSupport]
  exact mul_pos Profile.kappaStar_pos hL
theorem optimizerSupport_div {L : ℝ} (hL : 0 < L) :
    optimizerSupport L / L = Profile.kappaStar := by
  rw [optimizerSupport]
  field_simp [hL.ne']
theorem optimizerSupport_eq_div {L : ℝ} (hL : 0 < L) :
    optimizerSupport L = L / Profile.CStar := by
  rw [optimizerSupport, Profile.kappaStar_eq_one_div_CStar]
  field_simp [Profile.CStar_pos.ne']
theorem optimizerProfile_of_mem {L x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)) :
    optimizerProfile L x = 1 / (optimizerSupport L * Profile.I0Star) *
      Profile.FStar (x / optimizerSupport L) := by
  simp [optimizerProfile, hx]
theorem optimizerProfile_of_not_mem {L x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) (optimizerSupport L)) : optimizerProfile L x = 0 := by
  simp [optimizerProfile, hx]
theorem optimizerProfile_zero {L : ℝ} (hL : 0 < L) : optimizerProfile L 0 = 0 := by
  rw [optimizerProfile_of_mem ⟨le_rfl, (optimizerSupport_pos hL).le⟩]
  simp [Profile.FStar_apply, Profile.value_zero]
theorem optimizerProfile_pos {L x : ℝ} (hL : 0 < L)
    (hx : x ∈ Ioo 0 (optimizerSupport L)) : 0 < optimizerProfile L x := by
  rw [optimizerProfile_of_mem ⟨hx.1.le, hx.2.le⟩]
  have hy : x / optimizerSupport L ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hx.1 (optimizerSupport_pos hL)
    · apply (div_lt_iff₀ (optimizerSupport_pos hL)).2
      simpa using hx.2
  exact mul_pos (one_div_pos.mpr (mul_pos (optimizerSupport_pos hL) Profile.I0Star_pos))
     (Profile.FStar_pos hy)

theorem optimizerProfile_pos_iff {L : ℝ} (hL : 0 < L) {x : ℝ} :
    0 < optimizerProfile L x ↔ x ∈ Ioo 0 (optimizerSupport L) := by
  constructor
  · intro hx
    have hmem : x ∈ Icc (0 : ℝ) (optimizerSupport L) := by
      by_contra hm
      rw [optimizerProfile_of_not_mem hm] at hx
      linarith
    constructor
    · by_contra hzero
      have : x = 0 := le_antisymm (le_of_not_gt hzero) hmem.1
      subst x
      rw [optimizerProfile_zero hL] at hx
      linarith
    · by_contra hupper
      have : x = optimizerSupport L := le_antisymm hmem.2 (le_of_not_gt hupper)
      subst x
      rw [optimizerProfile_of_mem ⟨(optimizerSupport_pos hL).le, le_rfl⟩] at hx
      rw [div_self (optimizerSupport_pos hL).ne'] at hx
      have hzero : Profile.FStar 1 = 0 := Profile.value_one
        (lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar).ne'
        (Profile.cos_ne_one_of_mem_Ioo_two_pi ⟨lt_trans (Real.sqrt_pos.2 (by norm_num))
          Profile.sqrt_twelve_lt_tStar, Profile.tStar_lt_two_pi⟩)
      rw [hzero] at hx
      linarith
  · exact optimizerProfile_pos hL

def scaleFreeOptimizerProfile (z : ℝ) : ℝ :=
  if z ∈ Icc (0 : ℝ) Profile.kappaStar then
    (1 / (Profile.kappaStar * Profile.I0Star)) * Profile.FStar (z / Profile.kappaStar)
  else 0

theorem scaleFreeOptimizerProfile_of_mem {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) Profile.kappaStar) :
    scaleFreeOptimizerProfile z =
      1 / (Profile.kappaStar * Profile.I0Star) * Profile.FStar (z / Profile.kappaStar) := by
  simp only [scaleFreeOptimizerProfile, hz, ite_true]

theorem scaleFreeOptimizerProfile_of_not_mem {z : ℝ}
    (hz : z ∉ Icc (0 : ℝ) Profile.kappaStar) :
    scaleFreeOptimizerProfile z = 0 := by
  simp only [scaleFreeOptimizerProfile, hz, ite_false]

theorem scaleFreeOptimizerProfile_zero : scaleFreeOptimizerProfile 0 = 0 := by
  rw [scaleFreeOptimizerProfile_of_mem ⟨le_rfl, Profile.kappaStar_pos.le⟩]
  simp [Profile.FStar_apply, Profile.value_zero]

theorem scaleFreeOptimizerProfile_kappaStar :
    scaleFreeOptimizerProfile Profile.kappaStar = 0 := by
  rw [scaleFreeOptimizerProfile_of_mem ⟨Profile.kappaStar_pos.le, le_rfl⟩]
  rw [div_self Profile.kappaStar_pos.ne']
  simp [Profile.FStar_apply, Profile.value_one
    (lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar).ne'
    (Profile.cos_ne_one_of_mem_Ioo_two_pi ⟨lt_trans (Real.sqrt_pos.2 (by norm_num))
      Profile.sqrt_twelve_lt_tStar, Profile.tStar_lt_two_pi⟩)]

theorem scaleFreeOptimizerProfile_pos {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) Profile.kappaStar) :
    0 < scaleFreeOptimizerProfile z := by
  rw [scaleFreeOptimizerProfile_of_mem ⟨hz.1.le, hz.2.le⟩]
  have hy : z / Profile.kappaStar ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hz.1 Profile.kappaStar_pos
    · apply (div_lt_iff₀ Profile.kappaStar_pos).2
      simpa using hz.2
  exact mul_pos (one_div_pos.mpr (mul_pos Profile.kappaStar_pos Profile.I0Star_pos)
    ) (Profile.FStar_pos hy)

theorem scaleFreeOptimizerProfile_pos_iff {z : ℝ} :
    0 < scaleFreeOptimizerProfile z ↔ z ∈ Ioo (0 : ℝ) Profile.kappaStar := by
  constructor
  · intro hz
    have hmem : z ∈ Icc (0 : ℝ) Profile.kappaStar := by
      by_contra h
      rw [scaleFreeOptimizerProfile_of_not_mem h] at hz
      linarith
    constructor
    · by_contra h
      have : z = 0 := le_antisymm (le_of_not_gt h) hmem.1
      subst z
      rw [scaleFreeOptimizerProfile_zero] at hz
      linarith
    · by_contra h
      have : z = Profile.kappaStar := le_antisymm hmem.2 (le_of_not_gt h)
      subst z
      rw [scaleFreeOptimizerProfile_kappaStar] at hz
      linarith
  · exact scaleFreeOptimizerProfile_pos

end RayleighKernel.Analysis.HalfLineH1

namespace RayleighKernel.Analysis.HalfLineH1

open Set MeasureTheory

theorem minimizerSupport_eq_optimizerSupport
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1}
    (hfmin : f.IsMinimizer L) (B : f.CorrectionBumps) :
    f.minimizerSupport = optimizerSupport L := by
  have hC := coefficientC_minimizerParameter_eq_firstMoment_div_support hL hfmin B
  rw [minimizerParameter_eq_tStar hL hfmin B] at hC
  change Profile.CStar = L / f.minimizerSupport at hC
  have hK : 0 < f.minimizerSupport := minimizerSupport_pos hL hfmin B
  have hCstar : 0 < Profile.CStar := Profile.CStar_pos
  have hdiv := optimizerSupport_eq_div hL
  calc
    f.minimizerSupport = L / Profile.CStar := by
      field_simp [hK.ne', hCstar.ne'] at hC ⊢
      nlinarith
    _ = optimizerSupport L := hdiv.symm

theorem minimizerAmplitude_eq_optimizerAmplitude
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1}
    (hfmin : f.IsMinimizer L) (B : f.CorrectionBumps) :
    f.minimizerSlope B * f.minimizerSupport =
      1 / (optimizerSupport L * Profile.I0Star) := by
  have hA : f.minimizerSupport = optimizerSupport L := by
    exact minimizerSupport_eq_optimizerSupport hL hfmin B
  have hzero := momentZero_minimizerParameter hL hfmin B
  rw [minimizerParameter_eq_tStar hL hfmin B] at hzero
  change Profile.I0Star = 1 / (f.minimizerSlope B * f.minimizerSupport ^ 2) at hzero
  have hD : 0 < f.minimizerSlope B := minimizerSlope_pos hL hfmin B
  have hK : 0 < f.minimizerSupport := minimizerSupport_pos hL hfmin B
  have hI : 0 < Profile.I0Star := Profile.I0Star_pos
  have hS : 0 < optimizerSupport L := optimizerSupport_pos hL
  rw [hA] at hzero
  rw [hA]
  field_simp [hD.ne', hK.ne', hI.ne', hS.ne'] at hzero ⊢
  exact hzero

theorem continuousRep_eq_optimizerProfile_of_isMinimizer_of_mem
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1}
    (hfmin : f.IsMinimizer L) (B : f.CorrectionBumps)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)) :
    f.continuousRep x = optimizerProfile L x := by
  have hA : f.minimizerSupport = optimizerSupport L := by
    exact minimizerSupport_eq_optimizerSupport hL hfmin B
  have hB : f.minimizerSlope B * f.minimizerSupport =
      1 / (optimizerSupport L * Profile.I0Star) := by
    exact minimizerAmplitude_eq_optimizerAmplitude hL hfmin B
  have hK : 0 < f.minimizerSupport := minimizerSupport_pos hL hfmin B
  have hy : x / f.minimizerSupport ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hx.1 hK.le
    · apply (div_le_iff₀ hK).2
      rw [hA]
      simpa using hx.2
  rw [optimizerProfile_of_mem hx]
  have hnorm := normalizedMinimizerValue_eq_profile_value hL hfmin B hy
  rw [minimizerParameter_eq_tStar hL hfmin B] at hnorm
  unfold normalizedMinimizerValue at hnorm
  rw [hA] at hnorm
  have hB' : f.minimizerSlope B * optimizerSupport L =
      1 / (optimizerSupport L * Profile.I0Star) := by
    simpa [hA] using hB
  rw [hB'] at hnorm
  have hxarg : optimizerSupport L * (x / optimizerSupport L) = x := by
    rw [div_eq_mul_inv]
    calc
      optimizerSupport L * (x * (optimizerSupport L)⁻¹) =
          x * (optimizerSupport L * (optimizerSupport L)⁻¹) := by ring
      _ = x := by rw [mul_inv_cancel₀ (optimizerSupport_pos hL).ne', mul_one]
  rw [hxarg] at hnorm
  change f.continuousRep x = _
  have hden : (1 / (optimizerSupport L * Profile.I0Star) : ℝ) ≠ 0 := by
    exact one_div_ne_zero (mul_ne_zero (optimizerSupport_pos hL).ne' Profile.I0Star_pos.ne')
  calc
    f.continuousRep x = Profile.value Profile.tStar (x / optimizerSupport L) *
        (1 / (optimizerSupport L * Profile.I0Star)) :=
      (div_eq_iff hden).mp hnorm
    _ = 1 / (optimizerSupport L * Profile.I0Star) *
        Profile.FStar (x / optimizerSupport L) := by
      simp [Profile.FStar_apply, mul_comm]

theorem continuousRep_eq_optimizerProfile_of_isMinimizer_withB
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1}
    (hfmin : f.IsMinimizer L) (B : f.CorrectionBumps) (x : ℝ) :
    f.continuousRep x = optimizerProfile L x := by
  by_cases hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)
  · exact continuousRep_eq_optimizerProfile_of_isMinimizer_of_mem hL hfmin B hx
  · by_cases hx0 : x ≤ 0
    · rw [f.continuousRep_eq_zero_of_nonpositive hx0]
      exact (optimizerProfile_of_not_mem hx).symm
    · have hxpos : 0 < x := lt_of_not_ge hx0
      have hKx : optimizerSupport L < x := by
        exact lt_of_not_ge (fun h => hx ⟨hxpos.le, h⟩)
      have hsupport := minimizerSupport_eq_optimizerSupport hL hfmin B
      have hfzero := continuousRep_eq_zero_of_positivityHullEndpoint_le hL hfmin B
        (show f.minimizerSupport ≤ x by linarith [hsupport, hKx])
      rw [hfzero]
      exact (optimizerProfile_of_not_mem hx).symm

theorem continuousRep_eq_optimizerProfile_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1}
    (hfmin : f.IsMinimizer L) (x : ℝ) :
    f.continuousRep x = optimizerProfile L x := by
  let B : f.CorrectionBumps := Classical.choice (exists_correctionBumps hfmin.1)
  exact continuousRep_eq_optimizerProfile_of_isMinimizer_withB hL hfmin B x

theorem rayleighQuotient_eq_lambdaStar_div_sq_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    f.rayleighQuotient = Profile.lambdaStar / L ^ 2 := by
  let B : f.CorrectionBumps := Classical.choice (exists_correctionBumps hfmin.1)
  have hq : 0 < f.rayleighQuotient := minimizerRayleighQuotient_pos hL hfmin
  have hC : 0 < Profile.CStar := Profile.CStar_pos
  have hparam := minimizerParameter_eq_tStar hL hfmin B
  have hsupport := minimizerSupport_eq_optimizerSupport hL hfmin B
  rw [optimizerSupport_eq_div hL] at hsupport
  have hsq : f.rayleighQuotient * f.minimizerSupport ^ 2 =
      Profile.tStar ^ 2 := by
    unfold minimizerParameter at hparam
    have hsqrt : (Real.sqrt f.rayleighQuotient) ^ 2 = f.rayleighQuotient :=
      Real.sq_sqrt hq.le
    calc
      f.rayleighQuotient * f.minimizerSupport ^ 2 =
          (Real.sqrt f.rayleighQuotient) ^ 2 * f.minimizerSupport ^ 2 := by
            rw [hsqrt]
      _ = (Real.sqrt f.rayleighQuotient * f.minimizerSupport) ^ 2 := by ring
      _ = Profile.tStar ^ 2 := by rw [hparam]
  rw [Profile.lambdaStar]
  field_simp [hC.ne', hL.ne'] at hsupport ⊢
  rw [← hsupport]
  nlinarith [hsq]

theorem rayleighQuotient_eq_tStar_sq_mul_CStar_sq_div_sq_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    f.rayleighQuotient = Profile.tStar ^ 2 * Profile.CStar ^ 2 / L ^ 2 := by
  exact rayleighQuotient_eq_lambdaStar_div_sq_of_isMinimizer hL hfmin

noncomputable def optimizer (L : ℝ) (hL : 0 < L) : HalfLineH1 :=
  Classical.choose (exists_isMinimizer hL)

theorem optimizer_isMinimizer {L : ℝ} (hL : 0 < L) :
    (optimizer L hL).IsMinimizer L := Classical.choose_spec (exists_isMinimizer hL)

theorem rayleighQuotient_eq_Lambda_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    f.rayleighQuotient = Lambda L := by
  obtain ⟨u, hu, huq⟩ := exists_isAdmissible_rayleighQuotient_eq_Lambda hL
  apply le_antisymm
  · rw [← huq]
    exact hfmin.2 u hu
  · exact Lambda_le_of_isAdmissible hfmin.1

theorem rayleighQuotient_optimizer
    {L : ℝ} (hL : 0 < L) :
    (optimizer L hL).rayleighQuotient = Profile.lambdaStar / L ^ 2 := by
  exact rayleighQuotient_eq_lambdaStar_div_sq_of_isMinimizer hL
    (optimizer_isMinimizer hL)

theorem Lambda_eq_lambdaStar_div_sq {L : ℝ} (hL : 0 < L) :
    Lambda L = Profile.lambdaStar / L ^ 2 := by
  exact (rayleighQuotient_eq_Lambda_of_isMinimizer hL (optimizer_isMinimizer hL)).symm.trans
    (rayleighQuotient_optimizer hL)

theorem Lambda_eq_tStar_sq_mul_CStar_sq_div_sq {L : ℝ} (hL : 0 < L) :
    Lambda L = Profile.tStar ^ 2 * Profile.CStar ^ 2 / L ^ 2 := by
  rw [Lambda_eq_lambdaStar_div_sq hL, Profile.lambdaStar_eq]

theorem optimizer_isAdmissible {L : ℝ} (hL : 0 < L) :
    (optimizer L hL).IsAdmissible L := (optimizer_isMinimizer hL).1

theorem continuousRep_optimizer {L : ℝ} (hL : 0 < L) (x : ℝ) :
    (optimizer L hL).continuousRep x = optimizerProfile L x :=
  continuousRep_eq_optimizerProfile_of_isMinimizer hL (optimizer_isMinimizer hL) x

theorem continuousRep_eq_continuousRep_optimizer_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) (x : ℝ) :
    f.continuousRep x = (optimizer L hL).continuousRep x := by
  rw [continuousRep_eq_optimizerProfile_of_isMinimizer hL hfmin,
    continuousRep_optimizer hL]

theorem continuousRep_ae_eq_optimizer_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    f.continuousRep =ᵐ[volume] (optimizer L hL).continuousRep := by
  exact Filter.Eventually.of_forall
    (continuousRep_eq_continuousRep_optimizer_of_isMinimizer hL hfmin)

theorem eq_optimizer_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    f = optimizer L hL := by
  apply HalfLineH1.ext_value
  apply MeasureTheory.Lp.ext
  exact (f.continuousRep_ae_eq_value.symm.trans
    ((continuousRep_ae_eq_optimizer_of_isMinimizer hL hfmin).trans
      (optimizer L hL).continuousRep_ae_eq_value))

theorem isMinimizer_iff_eq_optimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} :
    f.IsMinimizer L ↔ f = optimizer L hL := by
  constructor
  · exact eq_optimizer_of_isMinimizer hL
  · intro hf
    rw [hf]
    exact optimizer_isMinimizer hL

theorem eq_of_isMinimizer_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f g : HalfLineH1}
    (hfmin : f.IsMinimizer L) (hgmin : g.IsMinimizer L) : f = g := by
  exact (eq_optimizer_of_isMinimizer hL hfmin).trans
    (eq_optimizer_of_isMinimizer hL hgmin).symm

theorem lambdaStar_div_sq_le_rayleighQuotient
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 ≤ u.rayleighQuotient := by
  rw [← Lambda_eq_lambdaStar_div_sq hL]
  exact Lambda_le_of_isAdmissible hu

theorem sharp_dirichletEnergy
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 * u.squareEnergy ≤ u.dirichletEnergy := by
  have henergy : 0 < u.squareEnergy := u.squareEnergy_pos_of_mass_eq_one hu.mass_eq
  have hquot := lambdaStar_div_sq_le_rayleighQuotient hL hu
  rw [HalfLineH1.rayleighQuotient] at hquot
  rw [le_div_iff₀ henergy] at hquot
  exact hquot

theorem sharp_dirichletEnergy_inequality
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 * f.squareEnergy ≤ f.dirichletEnergy :=
  sharp_dirichletEnergy hL hf

theorem sharp_dirichletEnergy_inequality_tStar_CStar
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    Profile.tStar ^ 2 * Profile.CStar ^ 2 / L ^ 2 * f.squareEnergy ≤
      f.dirichletEnergy := by
  simpa [Profile.lambdaStar_eq] using sharp_dirichletEnergy hL hf

theorem rayleighQuotient_eq_lambdaStar_div_sq_iff
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    u.rayleighQuotient = Profile.lambdaStar / L ^ 2 ↔ u = optimizer L hL := by
  constructor
  · intro hq
    have hmin : u.IsMinimizer L := by
      refine ⟨hu, fun v hv ↦ ?_⟩
      calc
        u.rayleighQuotient = Lambda L := by
          rw [hq, Lambda_eq_lambdaStar_div_sq hL]
        _ ≤ v.rayleighQuotient := Lambda_le_of_isAdmissible hv
    exact eq_optimizer_of_isMinimizer hL hmin
  · intro huo
    rw [huo]
    exact rayleighQuotient_optimizer hL

theorem isMinimizer_iff_rayleighQuotient_eq_lambdaStar_div_sq
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    f.IsMinimizer L ↔ f.rayleighQuotient = Profile.lambdaStar / L ^ 2 := by
  constructor
  · exact rayleighQuotient_eq_lambdaStar_div_sq_of_isMinimizer hL
  · intro hq
    refine ⟨hf, fun g hg => ?_⟩
    calc
      f.rayleighQuotient = Lambda L := by
        rw [hq, Lambda_eq_lambdaStar_div_sq hL]
      _ ≤ g.rayleighQuotient := Lambda_le_of_isAdmissible hg

theorem rayleighQuotient_eq_lambdaStar_div_sq_iff_eq_optimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    f.rayleighQuotient = Profile.lambdaStar / L ^ 2 ↔ f = optimizer L hL :=
  rayleighQuotient_eq_lambdaStar_div_sq_iff hL hf

theorem dirichletEnergy_eq_lambdaStar_div_sq_mul_squareEnergy_iff
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    u.dirichletEnergy = Profile.lambdaStar / L ^ 2 * u.squareEnergy ↔
      u = optimizer L hL := by
  have henergy : 0 < u.squareEnergy := u.squareEnergy_pos_of_mass_eq_one hu.mass_eq
  constructor
  · intro he
    apply (rayleighQuotient_eq_lambdaStar_div_sq_iff hL hu).1
    exact (div_eq_iff henergy.ne').2 he
  · intro he
    have hq := (rayleighQuotient_eq_lambdaStar_div_sq_iff hL hu).2 he
    exact (div_eq_iff henergy.ne').1 hq

theorem sharp_dirichletEnergy_eq_iff_eq_optimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 * f.squareEnergy = f.dirichletEnergy ↔
      f = optimizer L hL := by
  constructor
  · intro he
    apply (rayleighQuotient_eq_lambdaStar_div_sq_iff_eq_optimizer hL hf).1
    exact (div_eq_iff (f.squareEnergy_pos_of_mass_eq_one hf.mass_eq).ne').2 he.symm
  · intro he
    have hq := (rayleighQuotient_eq_lambdaStar_div_sq_iff_eq_optimizer hL hf).2 he
    exact (div_eq_iff (f.squareEnergy_pos_of_mass_eq_one hf.mass_eq).ne').1 hq |>.symm

theorem sharp_dirichletEnergy_eq_iff_tStar_CStar_eq_optimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    Profile.tStar ^ 2 * Profile.CStar ^ 2 / L ^ 2 * f.squareEnergy =
        f.dirichletEnergy ↔ f = optimizer L hL := by
  simpa [Profile.lambdaStar_eq] using sharp_dirichletEnergy_eq_iff_eq_optimizer hL hf

theorem rayleighQuotient_eq_lambdaStar_div_sq_iff_ae_eq_optimizer
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    u.rayleighQuotient = Profile.lambdaStar / L ^ 2 ↔
      u.continuousRep =ᵐ[volume] (optimizer L hL).continuousRep := by
  constructor
  · intro hq
    exact continuousRep_ae_eq_optimizer_of_isMinimizer hL
      ⟨hu, fun v hv ↦ by
        calc
          u.rayleighQuotient = Lambda L := by
            rw [hq, Lambda_eq_lambdaStar_div_sq hL]
          _ ≤ v.rayleighQuotient := Lambda_le_of_isAdmissible hv⟩
  · intro hae
    apply (rayleighQuotient_eq_lambdaStar_div_sq_iff hL hu).2
    apply HalfLineH1.ext_value
    apply MeasureTheory.Lp.ext
    exact u.continuousRep_ae_eq_value.symm.trans
      (hae.trans (optimizer L hL).continuousRep_ae_eq_value)

theorem sharp_dirichletEnergy_eq_iff_continuousRep_ae_eq_optimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hf : f.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 * f.squareEnergy = f.dirichletEnergy ↔
      f.continuousRep =ᵐ[volume] (optimizer L hL).continuousRep := by
  constructor
  · intro he
    have hfeq := (sharp_dirichletEnergy_eq_iff_eq_optimizer hL hf).1 he
    subst f
    exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro hae
    apply (sharp_dirichletEnergy_eq_iff_eq_optimizer hL hf).2
    apply HalfLineH1.ext_value
    apply MeasureTheory.Lp.ext
    exact f.continuousRep_ae_eq_value.symm.trans
      (hae.trans (optimizer L hL).continuousRep_ae_eq_value)

theorem sharp_dirichletEnergy_continuousRep
    {L : ℝ} (hL : 0 < L) {u : HalfLineH1} (hu : u.IsAdmissible L) :
    Profile.lambdaStar / L ^ 2 *
        (∫ x in halfLine, u.continuousRep x ^ 2) ≤
      ∫ x in halfLine, deriv u.continuousRep x ^ 2 := by
  change Profile.lambdaStar / L ^ 2 * RayleighKernel.squareEnergy u.continuousRep ≤
    RayleighKernel.dirichletEnergy u.continuousRep
  rw [u.squareEnergy_continuousRep, u.dirichletEnergy_continuousRep]
  exact sharp_dirichletEnergy hL hu

theorem mem_optimizerSupport_mul_iff {L z : ℝ} (hL : 0 < L) :
    L * z ∈ Icc (0 : ℝ) (optimizerSupport L) ↔
      z ∈ Icc (0 : ℝ) Profile.kappaStar := by
  rw [optimizerSupport_eq]
  constructor
  · intro hz
    constructor
    · exact (nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hz.1) hL)
    · apply (le_of_mul_le_mul_left (by simpa [mul_comm] using hz.2) hL)
  · intro hz
    constructor
    · exact mul_nonneg hL.le hz.1
    · apply (mul_le_mul_of_nonneg_left hz.2 hL.le) |>.trans_eq
      ring

theorem rescale_optimizerProfile {L : ℝ} (hL : 0 < L) (z : ℝ) :
    RayleighKernel.rescale L (optimizerProfile L) z =
      scaleFreeOptimizerProfile z := by
  rw [RayleighKernel.rescale]
  by_cases hz : z ∈ Icc (0 : ℝ) Profile.kappaStar
  · have hLz : L * z ∈ Icc (0 : ℝ) (optimizerSupport L) :=
      (mem_optimizerSupport_mul_iff hL).2 hz
    rw [optimizerProfile_of_mem hLz]
    simp only [scaleFreeOptimizerProfile, hz, ite_true]
    rw [optimizerSupport_eq]
    have hK : Profile.kappaStar ≠ 0 := Profile.kappaStar_pos.ne'
    field_simp [hK, hL.ne']
  · have hLz : L * z ∉ Icc (0 : ℝ) (optimizerSupport L) := by
      intro h
      exact hz ((mem_optimizerSupport_mul_iff hL).1 h)
    rw [optimizerProfile_of_not_mem hLz]
    unfold scaleFreeOptimizerProfile
    simp only [hz, ite_false]
    simp

def scaleFreeOptimizer : HalfLineH1 := optimizer 1 zero_lt_one

theorem continuousRep_scaleFreeOptimizer (z : ℝ) :
    scaleFreeOptimizer.continuousRep z = scaleFreeOptimizerProfile z := by
  change (optimizer 1 zero_lt_one).continuousRep z = scaleFreeOptimizerProfile z
  rw [continuousRep_optimizer zero_lt_one]
  by_cases hz : z ∈ Icc (0 : ℝ) Profile.kappaStar
  · rw [optimizerProfile_of_mem]
    · unfold scaleFreeOptimizerProfile
      simp only [hz, ite_true]
      rw [optimizerSupport_eq]
      field_simp [Profile.kappaStar_pos.ne']
    · simpa [optimizerSupport_eq] using hz
  · rw [optimizerProfile_of_not_mem]
    · unfold scaleFreeOptimizerProfile
      simp only [hz, ite_false]
    · simpa [optimizerSupport_eq] using hz

theorem mass_scaleFreeOptimizerProfile :
    RayleighKernel.mass scaleFreeOptimizerProfile = 1 := by
  have hfun : scaleFreeOptimizerProfile = (optimizer 1 zero_lt_one).continuousRep := by
    funext z
    exact (continuousRep_scaleFreeOptimizer z).symm
  rw [hfun]
  exact (optimizer_isAdmissible zero_lt_one).mass_eq

theorem firstMoment_scaleFreeOptimizerProfile :
    RayleighKernel.firstMoment scaleFreeOptimizerProfile = 1 := by
  have hfun : scaleFreeOptimizerProfile = (optimizer 1 zero_lt_one).continuousRep := by
    funext z
    exact (continuousRep_scaleFreeOptimizer z).symm
  rw [hfun]
  exact (optimizer_isAdmissible zero_lt_one).firstMoment_eq

theorem mul_continuousRep_optimizer_eq_scaleFreeOptimizerProfile
    {L : ℝ} (hL : 0 < L) (z : ℝ) :
    L * (optimizer L hL).continuousRep (L * z) = scaleFreeOptimizerProfile z := by
  rw [continuousRep_optimizer hL, ← rescale_optimizerProfile hL]
  rfl

theorem scaleFreeOptimizerProfile_eq_mul_optimizerProfile
    {L : ℝ} (hL : 0 < L) (z : ℝ) :
    scaleFreeOptimizerProfile z = L * optimizerProfile L (L * z) := by
  exact (rescale_optimizerProfile hL z).symm

end RayleighKernel.Analysis.HalfLineH1
