import RayleighKernel.Obstacle.KKT
import RayleighKernel.Variational.Scaling

/-!
This module is an additive homogeneous centered-cone and one-bump first-variation/KKT
frontend.  Its homogeneous cone is quotient-equivalent to normalized admissibility, and
its one-bump conclusions provide a first-variation forcing description.  It does not
replace the existing two-bump Riesz/reaction-measure/regularity chain, which remains the
authoritative downstream implementation.
-/

noncomputable section
namespace RayleighKernel.Analysis

open MeasureTheory Set
open scoped SchwartzMap Topology ENNReal

structure HomogeneousCentered (L : ℝ) (u : HalfLineH1) : Prop where
  nonnegative : ∀ x ∈ halfLine, 0 ≤ u.continuousRep x
  integrable : IntegrableOn u.continuousRep halfLine
  firstMoment_integrable : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine
  nonzero : u ≠ 0
  centered : ∫ x in halfLine, (x - L) * u.continuousRep x = 0

theorem centeredIntegral_eq_sub_mass_mul {L : ℝ} {u : HalfLineH1}
    (hu : IntegrableOn u.continuousRep halfLine)
    (hu1 : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine) :
    (∫ x in halfLine, (x - L) * u.continuousRep x) = u.firstMoment - L * u.mass := by
  rw [HalfLineH1.firstMoment, HalfLineH1.mass]
  rw [show (fun x : ℝ => (x - L) * u.continuousRep x) =
      (fun x => x * u.continuousRep x - L * u.continuousRep x) by
        funext x; ring]
  rw [integral_sub hu1 (hu.const_mul L), integral_const_mul]
  rfl

theorem centeredIntegral_eq_zero_iff {L : ℝ} {u : HalfLineH1}
    (hu : IntegrableOn u.continuousRep halfLine)
    (hu1 : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine) :
    ((∫ x in halfLine, (x - L) * u.continuousRep x) = 0 ↔
      u.firstMoment = L * u.mass) := by
  rw [centeredIntegral_eq_sub_mass_mul hu hu1]
  constructor <;> intro h <;> linarith

theorem mass_pos_of_homogeneousCentered {L : ℝ} {u : HalfLineH1}
    (hu : HomogeneousCentered L u) : 0 < u.mass := by
  have hnonneg : 0 ≤ u.mass := by
    rw [HalfLineH1.mass]
    exact setIntegral_nonneg measurableSet_Ici (fun x hx ↦ hu.nonnegative x hx)
  by_contra hnot
  have hzero : u.mass = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hae : u.continuousRep =ᵐ[volume.restrict halfLine] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae (μ := volume.restrict halfLine)
      (Filter.Eventually.of_forall (fun x ↦ by
        by_cases hx : x ∈ halfLine
        · exact hu.nonnegative x hx
        · exact le_of_eq (u.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx)).symm))
      hu.integrable).mp
    exact hzero
  have hae' : ∀ᵐ x ∂volume, x ∈ halfLine → u.continuousRep x = 0 :=
    (ae_restrict_iff' measurableSet_Ici).mp hae
  have hrep : u.continuousRep =ᵐ[volume] 0 := by
    filter_upwards [hae'] with x hx
    by_cases hxi : x ∈ halfLine
    · exact hx hxi
    · exact u.continuousRep_eq_zero_of_nonpositive (le_of_not_ge hxi)
  have hz : u.value = 0 := by
    apply Lp.ext
    filter_upwards [u.continuousRep_ae_eq_value, hrep] with x hx hzx
    rw [← hx, hzx]
    simp
  exact hu.nonzero (HalfLineH1.ext_value hz)

def normalizeMass (u : HalfLineH1) : HalfLineH1 := u.mass⁻¹ • u

theorem normalizeMass_isAdmissible {L : ℝ} {u : HalfLineH1}
    (hu : HomogeneousCentered L u) : (normalizeMass u).IsAdmissible L := by
  let c : ℝ := u.mass⁻¹
  have hc : 0 < c := inv_pos.mpr (mass_pos_of_homogeneousCentered hu)
  have hmass : (normalizeMass u).mass = 1 := by
    rw [normalizeMass, HalfLineH1.mass_smul_continuousRep]
    field_simp [ne_of_gt (mass_pos_of_homogeneousCentered hu)]
  have hmoment : (normalizeMass u).firstMoment = L := by
    rw [normalizeMass, HalfLineH1.firstMoment_smul_continuousRep]
    rw [show u.firstMoment = L * u.mass by
      exact (centeredIntegral_eq_zero_iff hu.integrable hu.firstMoment_integrable).mp hu.centered]
    field_simp [ne_of_gt (mass_pos_of_homogeneousCentered hu)]
  refine ⟨?_, ?_, ?_, hmass, hmoment⟩
  · intro x hx
    rw [normalizeMass, HalfLineH1.continuousRep_smul]
    exact mul_nonneg hc.le (hu.nonnegative x hx)
  · rw [normalizeMass, HalfLineH1.continuousRep_smul]
    exact hu.integrable.const_mul _
  · rw [normalizeMass, HalfLineH1.continuousRep_smul]
    change Integrable (fun x => x * (u.mass⁻¹ * u.continuousRep x))
      (volume.restrict halfLine)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hu.firstMoment_integrable.const_mul u.mass⁻¹)

theorem rayleighQuotient_normalizeMass {L : ℝ} {u : HalfLineH1}
    (hu : HomogeneousCentered L u) :
    (normalizeMass u).rayleighQuotient = u.rayleighQuotient := by
  exact HalfLineH1.rayleighQuotient_smul
    (inv_ne_zero (ne_of_gt (mass_pos_of_homogeneousCentered hu))) u

theorem homogeneousCentered_of_isAdmissible {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) : HomogeneousCentered L u := by
  refine ⟨hu.nonnegative, hu.integrable, hu.firstMoment_integrable, ?_, ?_⟩
  · intro hz
    have hmass : u.mass = 0 := by
      rw [hz, HalfLineH1.mass, HalfLineH1.continuousRep_zero_element]
      change ∫ x in halfLine, (0 : ℝ) = 0
      simp
    linarith [hu.mass_eq]
  · exact (centeredIntegral_eq_zero_iff hu.integrable hu.firstMoment_integrable).mpr
      (by rw [hu.mass_eq, mul_one, hu.firstMoment_eq])

theorem normalizeMass_eq_of_isAdmissible {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) : normalizeMass u = u := by
  rw [normalizeMass, hu.mass_eq, inv_one, one_smul]

theorem rayleighQuotient_normalizeMass_of_isAdmissible {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) : (normalizeMass u).rayleighQuotient = u.rayleighQuotient := by
  rw [normalizeMass_eq_of_isAdmissible hu]

def IsHomogeneousMinimizer (L : ℝ) (f : HalfLineH1) : Prop :=
  HomogeneousCentered L f ∧
    ∀ u : HalfLineH1, HomogeneousCentered L u →
      f.rayleighQuotient ≤ u.rayleighQuotient

theorem isHomogeneousMinimizer_of_isMinimizer
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    IsHomogeneousMinimizer L f := by
  refine ⟨homogeneousCentered_of_isAdmissible hfmin.1, ?_⟩
  intro u hu
  calc
    f.rayleighQuotient ≤ (normalizeMass u).rayleighQuotient :=
      hfmin.2 _ (normalizeMass_isAdmissible hu)
    _ = u.rayleighQuotient := rayleighQuotient_normalizeMass hu

theorem isMinimizer_normalizeMass_of_isHomogeneousMinimizer
    {L : ℝ} {u : HalfLineH1} (hu : IsHomogeneousMinimizer L u) :
    (normalizeMass u).IsMinimizer L := by
  refine ⟨normalizeMass_isAdmissible hu.1, ?_⟩
  intro v hv
  calc
    (normalizeMass u).rayleighQuotient = u.rayleighQuotient :=
      rayleighQuotient_normalizeMass hu.1
    _ ≤ v.rayleighQuotient := hu.2 v (homogeneousCentered_of_isAdmissible hv)

theorem isHomogeneousMinimizer_iff_normalizeMass_isMinimizer
    {L : ℝ} {u : HalfLineH1} :
    IsHomogeneousMinimizer L u ↔
      HomogeneousCentered L u ∧ (normalizeMass u).IsMinimizer L := by
  constructor
  · intro hu
    exact ⟨hu.1, isMinimizer_normalizeMass_of_isHomogeneousMinimizer hu⟩
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, ?_⟩
    intro v hv
    calc
      u.rayleighQuotient = (normalizeMass u).rayleighQuotient :=
        (rayleighQuotient_normalizeMass hu).symm
      _ ≤ (normalizeMass v).rayleighQuotient :=
        hmin.2 _ (normalizeMass_isAdmissible hv)
      _ = v.rayleighQuotient := rayleighQuotient_normalizeMass hv

def centeredFunctional (L : ℝ) (u : HalfLineH1) : ℝ :=
  u.firstMoment - L * u.mass

def centeredTest (L : ℝ) (ψ : PositiveTestFunction) : ℝ :=
  PositiveTestFunction.testFirstMoment ψ - L * PositiveTestFunction.testMass ψ

lemma centeredFunctional_eq_integral {L : ℝ} {u : HalfLineH1}
    (hu : IntegrableOn u.continuousRep halfLine)
    (hu1 : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine) :
    centeredFunctional L u = ∫ x in halfLine, (x - L) * u.continuousRep x := by
  rw [centeredFunctional, centeredIntegral_eq_sub_mass_mul hu hu1]

lemma centeredTest_eq_integral (L : ℝ) (ψ : PositiveTestFunction) :
    centeredTest L ψ = ∫ x : ℝ, (x - L) * ψ.1 x := by
  rw [centeredTest, PositiveTestFunction.testFirstMoment, PositiveTestFunction.testMass]
  rw [show (fun x : ℝ => (x - L) * ψ.1 x) =
      (fun x => x * ψ.1 x - L * ψ.1 x) by funext x; ring]
  rw [integral_sub]
  · rw [integral_const_mul]
  · exact (ψ.1.integrable_pow_mul volume 1).mono
      (continuous_id.mul ψ.1.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs])
  · exact ψ.1.integrable.const_mul _

lemma centeredTest_add (L : ℝ) (φ ψ : PositiveTestFunction) :
    centeredTest L (φ + ψ) = centeredTest L φ + centeredTest L ψ := by
  simp only [centeredTest, PositiveTestFunction.testMass_add,
    PositiveTestFunction.testFirstMoment_add]
  ring

lemma centeredTest_smul (L c : ℝ) (φ : PositiveTestFunction) :
    centeredTest L (c • φ) = c * centeredTest L φ := by
  simp only [centeredTest, PositiveTestFunction.testMass_smul,
    PositiveTestFunction.testFirstMoment_smul]
  ring

/-- The centered mass--moment functional packaged as a linear map on test functions. -/
def centeredTestLinear (L : ℝ) : PositiveTestFunction →ₗ[ℝ] ℝ where
  toFun ψ := centeredTest L ψ
  map_add' φ ψ := centeredTest_add L φ ψ
  map_smul' c ψ := centeredTest_smul L c ψ

@[simp] theorem centeredTestLinear_apply (L : ℝ) (ψ : PositiveTestFunction) :
    centeredTestLinear L ψ = centeredTest L ψ := rfl

lemma centeredTest_neg (L : ℝ) (φ : PositiveTestFunction) :
    centeredTest L (-φ) = -centeredTest L φ := by
  rw [show (-φ : PositiveTestFunction) = (-1 : ℝ) • φ by simp,
    centeredTest_smul]
  ring

structure CenteredCorrectionBump (L : ℝ) (f : HalfLineH1) where
  test : PositiveTestFunction
  hasCompactSupport : HasCompactSupport test.1
  nonnegative : ∀ x, 0 ≤ test.1 x
  support : tsupport test.1 ⊆ f.positivitySet
  centered_ne_zero : centeredTest L test ≠ 0

def CenteredCorrectionBump.coefficient {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) : ℝ :=
  centeredTest L ψ / centeredTest L B.test

def CenteredCorrectionBump.correctedTest {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) : PositiveTestFunction :=
  ψ - B.coefficient ψ • B.test

def CenteredCorrectionBump.correctedVariation {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) : HalfLineH1 :=
  PositiveTestFunction.toHalfLineH1 (B.correctedTest ψ)

def CenteredCorrectionBump.multiplier {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) : ℝ :=
  -f.firstVariation (PositiveTestFunction.toHalfLineH1 B.test) /
    centeredTest L B.test

lemma CenteredCorrectionBump.centered_correctedTest {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    centeredTest L (B.correctedTest ψ) = 0 := by
  rw [CenteredCorrectionBump.correctedTest, sub_eq_add_neg,
    centeredTest_add, centeredTest_neg, centeredTest_smul]
  dsimp [CenteredCorrectionBump.coefficient]
  field_simp [B.centered_ne_zero]
  ring

lemma CenteredCorrectionBump.correctedVariation_continuousRep {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    (B.correctedVariation ψ).continuousRep = (B.correctedTest ψ).1 := by
  funext x
  exact PositiveTestFunction.continuousRep_toHalfLineH1 (B.correctedTest ψ) x

lemma CenteredCorrectionBump.correctedVariation_integrable {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    IntegrableOn (B.correctedVariation ψ).continuousRep halfLine := by
  rw [B.correctedVariation_continuousRep]
  exact (B.correctedTest ψ).1.integrable.mono_measure Measure.restrict_le_self

lemma CenteredCorrectionBump.correctedVariation_firstMoment_integrable
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) :
    IntegrableOn (fun x => x * (B.correctedVariation ψ).continuousRep x) halfLine := by
  rw [B.correctedVariation_continuousRep]
  exact ((B.correctedTest ψ).1.integrable_pow_mul volume 1).mono
    ((continuous_id.mul (B.correctedTest ψ).1.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs]) |>.mono_measure
      Measure.restrict_le_self

lemma CenteredCorrectionBump.correctedVariation_mass {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    (B.correctedVariation ψ).mass = PositiveTestFunction.testMass (B.correctedTest ψ) := by
  exact (PositiveTestFunction.testMass_eq_mass (B.correctedTest ψ)).symm

lemma CenteredCorrectionBump.correctedVariation_firstMoment {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    (B.correctedVariation ψ).firstMoment =
      PositiveTestFunction.testFirstMoment (B.correctedTest ψ) := by
  exact (testFirstMoment_bridge (B.correctedTest ψ)).symm

lemma CenteredCorrectionBump.correctedVariation_centeredFunctional {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    centeredFunctional L (B.correctedVariation ψ) = 0 := by
  rw [centeredFunctional, B.correctedVariation_mass, B.correctedVariation_firstMoment]
  simpa [centeredTest] using B.centered_correctedTest ψ

lemma CenteredCorrectionBump.exists_pos_lower_bound {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) :
    ∃ δ > 0, ∀ x ∈ tsupport B.test.1, δ ≤ f.continuousRep x := by
  let K : Set ℝ := tsupport B.test.1
  have hK : IsCompact K := B.hasCompactSupport.isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne
      f.continuous_continuousRep.continuousOn
    exact ⟨f.continuousRep x, B.support hxK, fun y hy => hx hy⟩
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

lemma CenteredCorrectionBump.exists_correction_bound {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    ∃ C ≥ 0, ∀ x, |B.coefficient ψ * B.test.1 x| ≤ C := by
  refine ⟨|B.coefficient ψ| * SchwartzMap.seminorm ℝ 0 0 B.test.1, by positivity, ?_⟩
  intro x
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_le_seminorm ℝ B.test.1 x) (abs_nonneg _)

theorem CenteredCorrectionBump.correctedTest_add {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (φ ψ : PositiveTestFunction) :
    B.correctedTest (φ + ψ) = B.correctedTest φ + B.correctedTest ψ := by
  have hc : B.coefficient (φ + ψ) = B.coefficient φ + B.coefficient ψ := by
    dsimp [CenteredCorrectionBump.coefficient]
    rw [centeredTest_add]
    field_simp [B.centered_ne_zero]
  apply Subtype.ext
  simp only [CenteredCorrectionBump.correctedTest, hc, sub_eq_add_neg, add_smul, add_assoc]
  abel

theorem CenteredCorrectionBump.correctedTest_smul {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (c : ℝ) (ψ : PositiveTestFunction) :
    B.correctedTest (c • ψ) = c • B.correctedTest ψ := by
  have hc : B.coefficient (c • ψ) = c * B.coefficient ψ := by
    dsimp [CenteredCorrectionBump.coefficient]
    rw [centeredTest_smul]
    field_simp [B.centered_ne_zero]
  rw [CenteredCorrectionBump.correctedTest, hc]
  apply Subtype.ext
  change (c • ψ.1 - (c * B.coefficient ψ) • B.test.1) =
    c • (ψ.1 - B.coefficient ψ • B.test.1)
  ext x
  simp [smul_eq_mul]
  ring

theorem CenteredCorrectionBump.correctedVariation_add {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (φ ψ : PositiveTestFunction) :
    B.correctedVariation (φ + ψ) = B.correctedVariation φ + B.correctedVariation ψ := by
  change PositiveTestFunction.toHalfLineH1 (B.correctedTest (φ + ψ)) = _
  rw [B.correctedTest_add]
  exact @RayleighKernel.Analysis.HalfLineH1.PositiveTestFunction.toHalfLineH1_add
    (B.correctedTest φ) (B.correctedTest ψ)

theorem CenteredCorrectionBump.correctedVariation_smul {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (c : ℝ) (ψ : PositiveTestFunction) :
    B.correctedVariation (c • ψ) = c • B.correctedVariation ψ := by
  change PositiveTestFunction.toHalfLineH1 (B.correctedTest (c • ψ)) = _
  rw [B.correctedTest_smul]
  exact @RayleighKernel.Analysis.HalfLineH1.PositiveTestFunction.toHalfLineH1_smul
    c (B.correctedTest ψ)

lemma centeredTest_pos_of_support_above {L : ℝ} {s : Set ℝ} {B : PositiveTestBumpIn s}
    (hs : s ⊆ Ioi L) : 0 < centeredTest L B.test := by
  rw [centeredTest_eq_integral]
  refine ((continuous_id.sub continuous_const).mul B.test.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := B.center) B.hasCompactSupport.mul_left ?_ ?_
  · intro z
    by_cases hz : z ∈ tsupport B.test.1
    · exact mul_nonneg (sub_nonneg.mpr (le_of_lt (hs (B.tsupport_subset hz)))) (B.nonnegative z)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · rw [B.value_center]
    have := hs B.center_mem
    norm_num [B.value_center]
    exact (ne_of_gt (show 0 < B.center - L by simpa [mem_Ioi] using this))

lemma centeredTest_neg_of_support_below {L : ℝ} {s : Set ℝ} {B : PositiveTestBumpIn s}
    (hs : s ⊆ Iio L) : centeredTest L B.test < 0 := by
  rw [centeredTest_eq_integral]
  have hp : 0 < ∫ z, (L - z) * B.test.1 z := by
    refine ((continuous_const.sub continuous_id).mul B.test.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := B.center) B.hasCompactSupport.mul_left ?_ ?_
    · intro z
      by_cases hz : z ∈ tsupport B.test.1
      · exact mul_nonneg (sub_nonneg.mpr (le_of_lt (hs (B.tsupport_subset hz)))) (B.nonnegative z)
      · simp [image_eq_zero_of_notMem_tsupport hz]
    · rw [B.value_center]
      have := hs B.center_mem
      norm_num [B.value_center]
      exact (ne_of_gt (show 0 < L - B.center by simpa [mem_Iio] using this))
  rw [show (fun z => (L - z) * B.test.1 z) =
      (fun z => -((z - L) * B.test.1 z)) by funext z; ring] at hp
  rw [integral_neg] at hp
  linarith

theorem exists_centeredCorrectionBump {L : ℝ} {f : HalfLineH1}
    (hf : f.IsAdmissible L) : Nonempty (CenteredCorrectionBump L f) := by
  obtain ⟨x, hx⟩ := f.positivitySet_nonempty hf
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (f.isOpen_positivitySet.mem_nhds hx)
  let y := if x + r / 2 = L then x - r / 2 else x + r / 2
  have hyball : y ∈ Metric.ball x r := by
    dsimp [y]; split_ifs <;> rw [Metric.mem_ball, Real.dist_eq, abs_lt] <;> constructor <;> linarith
  have hy : y ∈ f.positivitySet := hball hyball
  have hne : y ≠ L := by
    dsimp [y]; split_ifs with h <;> intro heq
    · linarith
    · exact h heq
  have hpos : f.positivitySet ⊆ Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_not_ge fun hz0 ↦ hz.ne' (f.continuousRep_eq_zero_of_nonpositive hz0)
  by_cases hLy : L < y
  · let s := f.positivitySet ∩ Ioi L
    obtain ⟨B, hB⟩ := exists_positiveTestBumpIn (f.isOpen_positivitySet.inter isOpen_Ioi) ⟨hy, hLy⟩
      (inter_subset_left.trans hpos)
    exact ⟨⟨B.test, B.hasCompactSupport, B.nonnegative,
      B.tsupport_subset.trans inter_subset_left,
      ne_of_gt (centeredTest_pos_of_support_above inter_subset_right)⟩⟩
  · let s := f.positivitySet ∩ Iio L
    obtain ⟨B, hB⟩ := exists_positiveTestBumpIn (f.isOpen_positivitySet.inter isOpen_Iio) ⟨hy, lt_of_le_of_ne (le_of_not_gt hLy) hne⟩
      (inter_subset_left.trans hpos)
    exact ⟨⟨B.test, B.hasCompactSupport, B.nonnegative,
      B.tsupport_subset.trans inter_subset_left,
      ne_of_lt (centeredTest_neg_of_support_below inter_subset_right)⟩⟩

structure PerturbationL1Package (f h : HalfLineH1) (ε : ℝ) : Prop where
  representative : ∀ x, (f + ε • h).continuousRep x = f.continuousRep x + ε * h.continuousRep x
  integrable : IntegrableOn (f + ε • h).continuousRep halfLine
  firstMoment_integrable : IntegrableOn (fun x => x * (f + ε • h).continuousRep x) halfLine
  mass_formula : (f + ε • h).mass = f.mass + ε * h.mass
  firstMoment_formula : (f + ε • h).firstMoment = f.firstMoment + ε * h.firstMoment

theorem perturbationL1Package_of {f h : HalfLineH1} {ε : ℝ}
    (hf : IntegrableOn f.continuousRep halfLine)
    (hf1 : IntegrableOn (fun x => x * f.continuousRep x) halfLine)
    (hh : IntegrableOn h.continuousRep halfLine)
    (hh1 : IntegrableOn (fun x => x * h.continuousRep x) halfLine) :
    PerturbationL1Package f h ε := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]; simp [smul_eq_mul]
  · rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]; exact hf.add (hh.const_mul ε)
  · rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
    change IntegrableOn (fun x => x * (f.continuousRep x + ε * h.continuousRep x)) halfLine
    rw [show (fun x => x * (f.continuousRep x + ε * h.continuousRep x)) =
      (fun x => x * f.continuousRep x + ε * (x * h.continuousRep x)) by funext x; ring]
    exact hf1.add (hh1.const_mul ε)
  · have hε : IntegrableOn (ε • h).continuousRep halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      exact hh.const_mul ε
    exact (HalfLineH1.mass_add_continuousRep hf hε).trans (by rw [HalfLineH1.mass_smul_continuousRep])
  · have hε : IntegrableOn (fun x => x * (ε • h).continuousRep x) halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      change IntegrableOn (fun x => x * (ε * h.continuousRep x)) halfLine
      rw [show (fun x => x * (ε * h.continuousRep x)) =
        (fun x => ε * (x * h.continuousRep x)) by funext x; ring]
      change Integrable (fun x => ε * (x * h.continuousRep x))
        (Measure.restrict volume halfLine)
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hh1.const_mul ε
    exact (HalfLineH1.firstMoment_add_continuousRep hf1 hε).trans
      (by rw [HalfLineH1.firstMoment_smul_continuousRep])

theorem correctedVariation_perturbationL1Package {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) {ε : ℝ}
    (hf : IntegrableOn f.continuousRep halfLine)
    (hf1 : IntegrableOn (fun x => x * f.continuousRep x) halfLine) :
    PerturbationL1Package f (B.correctedVariation ψ) ε :=
  perturbationL1Package_of hf hf1 (B.correctedVariation_integrable ψ)
    (B.correctedVariation_firstMoment_integrable ψ)

theorem perturbation_ne_zero_of_mass_bound {f h : HalfLineH1} {ε : ℝ}
    (hf : f.mass = 1) (hp : PerturbationL1Package f h ε)
    (he : |ε * h.mass| < 1) : f + ε • h ≠ 0 := by
  intro hz
  have hm : (f + ε • h).mass = 0 := by
    rw [hz, HalfLineH1.mass, HalfLineH1.continuousRep_zero_element]
    change ∫ x in halfLine, (0 : ℝ) = 0
    simp
  rw [hp.mass_formula, hf] at hm
  have hprod : ε * h.mass = -1 := by linarith
  have habs : |ε * h.mass| = 1 := by rw [hprod]; norm_num
  linarith

theorem perturbation_centered_of_centeredFunctional_zero {L : ℝ} {f h : HalfLineH1} {ε : ℝ}
    (hf : f.IsAdmissible L) (hp : PerturbationL1Package f h ε)
    (hc : centeredFunctional L h = 0) :
    (∫ x in halfLine, (x - L) * (f + ε • h).continuousRep x) = 0 := by
  rw [centeredIntegral_eq_sub_mass_mul hp.integrable hp.firstMoment_integrable,
    hp.mass_formula, hp.firstMoment_formula, hf.mass_eq, hf.firstMoment_eq]
  rw [centeredFunctional] at hc
  calc
    L + ε * h.firstMoment - L * (1 + ε * h.mass) =
        ε * (h.firstMoment - L * h.mass) := by ring
    _ = 0 := by rw [hc]; simp

theorem CenteredCorrectionBump.perturbation_nonnegative_of_small
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) (hψ : ∀ x, 0 ≤ ψ.1 x) (hf : f.IsAdmissible L) :
    ∃ εpos > 0, ∀ ε : ℝ, 0 < ε → ε ≤ εpos →
      ∀ x ∈ halfLine, 0 ≤ (f + ε • B.correctedVariation ψ).continuousRep x := by
  obtain ⟨δ, hδ, hδf⟩ := B.exists_pos_lower_bound
  obtain ⟨C, hC, hCbound⟩ := B.exists_correction_bound ψ
  let εpos := δ / (C + 1)
  have hεpos : 0 < εpos := div_pos hδ (by linarith)
  refine ⟨εpos, hεpos, ?_⟩
  intro ε hε hεle x hx
  rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul,
    B.correctedVariation_continuousRep]
  change 0 ≤ f.continuousRep x + ε * (ψ.1 x - B.coefficient ψ * B.test.1 x)
  by_cases hxs : x ∈ tsupport B.test.1
  · have hfx := hδf x hxs
    have habs := hCbound x
    have hupper : B.coefficient ψ * B.test.1 x ≤ C := (le_abs_self _).trans habs
    have hεC : ε * C ≤ δ := by
      have := (le_div_iff₀ (by linarith : 0 < C + 1)).mp hεle
      nlinarith
    nlinarith [hψ x]
  · have hB : B.test.1 x = 0 := image_eq_zero_of_notMem_tsupport hxs
    rw [hB]
    simpa [hB] using add_nonneg (hf.nonnegative x hx) (mul_nonneg (le_of_lt hε) (hψ x))

theorem CenteredCorrectionBump.exists_pos_homogeneousCentered_correctedVariation
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) (hψ : ∀ x, 0 ≤ ψ.1 x) (hf : f.IsAdmissible L) :
    ∃ ε0 > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      HomogeneousCentered L (f + ε • B.correctedVariation ψ) := by
  obtain ⟨εpos, hεpos, hnonneg⟩ := B.perturbation_nonnegative_of_small ψ hψ hf
  let εmass := 1 / (2 * (|(B.correctedVariation ψ).mass| + 1))
  let ε0 := min εpos εmass
  have hεmass : 0 < εmass := by dsimp [εmass]; positivity
  refine ⟨min εpos εmass, lt_min hεpos hεmass, ?_⟩
  intro ε hε hεle
  have hp : PerturbationL1Package f (B.correctedVariation ψ) ε :=
    correctedVariation_perturbationL1Package B ψ hf.integrable hf.firstMoment_integrable
  have hprod : |ε * (B.correctedVariation ψ).mass| < 1 := by
    rw [abs_mul, abs_of_pos hε]
    have he := le_trans hεle (min_le_right _ _)
    have hm : 0 ≤ |(B.correctedVariation ψ).mass| := abs_nonneg _
    calc ε * |(B.correctedVariation ψ).mass| ≤
        (1 / (2 * (|(B.correctedVariation ψ).mass| + 1))) * |(B.correctedVariation ψ).mass| :=
          mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ < 1 := by
        have hd : 0 < 2 * (|(B.correctedVariation ψ).mass| + 1) := by positivity
        rw [show 1 / (2 * (|(B.correctedVariation ψ).mass| + 1)) *
            |(B.correctedVariation ψ).mass| =
            |(B.correctedVariation ψ).mass| /
              (2 * (|(B.correctedVariation ψ).mass| + 1)) by ring]
        apply (div_lt_iff₀ hd).mpr
        nlinarith
  have hne := perturbation_ne_zero_of_mass_bound hf.mass_eq hp hprod
  have hcenter := perturbation_centered_of_centeredFunctional_zero hf hp
    (B.correctedVariation_centeredFunctional ψ)
  refine ⟨hnonneg ε hε (le_trans hεle (min_le_left _ _)), hp.integrable, hp.firstMoment_integrable, hne, hcenter⟩

private lemma exists_pos_lower_bound_of_compact_test {f : HalfLineH1}
    {ψ : PositiveTestFunction} (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    ∃ δ > 0, ∀ x ∈ tsupport ψ.1, δ ≤ f.continuousRep x := by
  let K : Set ℝ := tsupport ψ.1
  have hK : IsCompact K := hψcompact.isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne
      f.continuous_continuousRep.continuousOn
    exact ⟨f.continuousRep x, hψsupport hxK, fun y hy => hx hy⟩
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

private lemma exists_compact_test_bound (ψ : PositiveTestFunction) :
    ∃ C ≥ 0, ∀ x, |ψ.1 x| ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 ψ.1, by positivity, ?_⟩
  intro x
  exact SchwartzMap.norm_le_seminorm ℝ ψ.1 x

/-- Compact interior corrected variations remain homogeneous-feasible for both signs. -/
theorem CenteredCorrectionBump.exists_twoSided_homogeneousCentered_correctedVariation
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) (hf : f.IsAdmissible L) :
    ∃ ε0 > 0, ∀ s : ℝ, |s| ≤ ε0 →
      HomogeneousCentered L (f + s • B.correctedVariation ψ) := by
  obtain ⟨δψ, hδψ, hδψf⟩ := exists_pos_lower_bound_of_compact_test hψcompact hψsupport
  obtain ⟨δB, hδB, hδBf⟩ := B.exists_pos_lower_bound
  obtain ⟨Cψ, hCψ, hψbound⟩ := exists_compact_test_bound ψ
  obtain ⟨CB, hCB, hBbound⟩ := B.exists_correction_bound ψ
  let δ := min δψ δB
  let C := Cψ + CB
  let εpos := δ / (C + 1)
  let εmass := 1 / (2 * (|(B.correctedVariation ψ).mass| + 1))
  let ε0 := min εpos εmass
  have hδ : 0 < δ := lt_min hδψ hδB
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hεpos : 0 < εpos := div_pos hδ (by linarith)
  have hεmass : 0 < εmass := by dsimp [εmass]; positivity
  refine ⟨ε0, lt_min hεpos hεmass, ?_⟩
  intro s hs
  let h := B.correctedVariation ψ
  have hnonneg : ∀ x ∈ halfLine, 0 ≤ (f + s • h).continuousRep x := by
    intro x hx
    rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul,
      B.correctedVariation_continuousRep]
    change 0 ≤ f.continuousRep x + s * (ψ.1 x - B.coefficient ψ * B.test.1 x)
    by_cases hxs : x ∈ tsupport ψ.1 ∪ tsupport B.test.1
    · have hfx : δ ≤ f.continuousRep x := by
        by_cases hxp : x ∈ tsupport ψ.1
        · exact (min_le_left δψ δB).trans (hδψf x hxp)
        · exact (min_le_right δψ δB).trans (hδBf x (by
            exact hxs.resolve_left hxp))
      have hterm : |ψ.1 x - B.coefficient ψ * B.test.1 x| ≤ C := by
        calc
          |ψ.1 x - B.coefficient ψ * B.test.1 x| ≤
              |ψ.1 x| + |B.coefficient ψ * B.test.1 x| := abs_sub _ _
          _ ≤ Cψ + CB := add_le_add (hψbound x) (hBbound x)
      have hsc : |s| * C ≤ δ := by
        have hden : 0 < C + 1 := by linarith
        have := (le_div_iff₀ hden).mp (le_trans hs (min_le_left _ _))
        nlinarith
      have habs : |s * (ψ.1 x - B.coefficient ψ * B.test.1 x)| ≤ δ := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hterm (abs_nonneg s)).trans hsc
      linarith [neg_le_of_abs_le habs]
    · have hψx : ψ.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hxs (Or.inl hx))
      have hBx : B.test.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hxs (Or.inr hx))
      simp [hψx, hBx, hf.nonnegative x hx]
  have hp : PerturbationL1Package f h s :=
    correctedVariation_perturbationL1Package B ψ hf.integrable hf.firstMoment_integrable
  have hprod : |s * h.mass| < 1 := by
    rw [abs_mul]
    have hs' : |s| ≤ εmass := le_trans hs (min_le_right _ _)
    have hm : 0 ≤ |h.mass| := abs_nonneg _
    calc
      |s| * |h.mass| ≤ (1 / (2 * (|h.mass| + 1))) * |h.mass| :=
        mul_le_mul_of_nonneg_right hs' hm
      _ < 1 := by
        have hd : 0 < 2 * (|h.mass| + 1) := by positivity
        rw [show 1 / (2 * (|h.mass| + 1)) * |h.mass| =
          |h.mass| / (2 * (|h.mass| + 1)) by ring]
        apply (div_lt_iff₀ hd).mpr
        nlinarith
  have hne := perturbation_ne_zero_of_mass_bound hf.mass_eq hp hprod
  have hcenter := perturbation_centered_of_centeredFunctional_zero hf hp
    (B.correctedVariation_centeredFunctional ψ)
  exact ⟨hnonneg, hp.integrable, hp.firstMoment_integrable, hne, hcenter⟩

def CenteredCorrectionBump.correctedFirstVariation {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) : PositiveTestFunction →ₗ[ℝ] ℝ where
  toFun ψ := f.firstVariation (B.correctedVariation ψ)
  map_add' φ ψ := by rw [B.correctedVariation_add, f.firstVariation_add]
  map_smul' c ψ := by rw [B.correctedVariation_smul, f.firstVariation_smul]; simp [smul_eq_mul]

theorem CenteredCorrectionBump.firstVariation_correctedVariation_nonneg
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction)
    (hψ : ∀ x, 0 ≤ ψ.1 x) : 0 ≤ f.firstVariation (B.correctedVariation ψ) := by
  obtain ⟨ε0, hε0, hfeas⟩ := B.exists_pos_homogeneousCentered_correctedVariation ψ hψ hfmin.1
  let h := B.correctedVariation ψ
  have hden : 0 < f.squareEnergy := f.squareEnergy_pos_of_mass_eq_one hfmin.1.mass_eq
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ => (f + s • h).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hq : f.rayleighQuotient ≤ (f + t • h).rayleighQuotient :=
      (isHomogeneousMinimizer_of_isMinimizer hfmin).2
        (f + t • h) (hfeas t ht.1 ht.2.le)
    simpa using (div_nonneg (sub_nonneg.mpr hq) (le_of_lt ht.1))
  exact HalfLineH1.firstVariation_nonneg_of_eventually_slope_nonneg f h hden hev

/-- Interior corrected variations have vanishing first variation at a minimizer. -/
theorem CenteredCorrectionBump.firstVariation_correctedVariation_eq_zero_of_tsupport_subset_positivity
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction)
    (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    f.firstVariation (B.correctedVariation ψ) = 0 := by
  obtain ⟨ε0, hε0, hfeas⟩ :=
    B.exists_twoSided_homogeneousCentered_correctedVariation ψ hψcompact hψsupport hfmin.1
  let h := B.correctedVariation ψ
  have hden : 0 < f.squareEnergy := f.squareEnergy_pos_of_mass_eq_one hfmin.1.mass_eq
  have hplus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ ↦ (f + s • h).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hq : f.rayleighQuotient ≤ (f + t • h).rayleighQuotient :=
      (isHomogeneousMinimizer_of_isMinimizer hfmin).2 _ (hfeas t (by
        simpa [abs_of_pos ht.1] using ht.2.le))
    have hq' : (f + 0 • h).rayleighQuotient ≤ (f + t • h).rayleighQuotient := by
      simpa using hq
    simpa using (div_nonneg (sub_nonneg.mpr hq') (by simpa using ht.1.le))
  have hminus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ ↦ (f + s • (-h)).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hq : f.rayleighQuotient ≤ (f + (-t) • h).rayleighQuotient :=
      (isHomogeneousMinimizer_of_isMinimizer hfmin).2 _ (hfeas (-t) (by
        rw [abs_neg, abs_of_pos ht.1]
        exact ht.2.le))
    have heq : f + t • (-h) = f + (-t) • h := by
      rw [show -h = (-1 : ℝ) • h by simp]
      simp
    rw [heq]
    have hq' : (f + 0 • (-h)).rayleighQuotient ≤ (f + t • (-h)).rayleighQuotient := by
      rw [heq]
      simpa using hq
    simpa using (div_nonneg (sub_nonneg.mpr hq') (by simpa using ht.1.le))
  exact HalfLineH1.firstVariation_eq_zero_of_eventually_slope_nonneg f h hden hplus hminus

/-- The centered corrected functional vanishes on compactly supported interior tests. -/
theorem CenteredCorrectionBump.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction)
    (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    B.correctedFirstVariation ψ = 0 := by
  rw [show B.correctedFirstVariation ψ = f.firstVariation (B.correctedVariation ψ) by rfl]
  exact B.firstVariation_correctedVariation_eq_zero_of_tsupport_subset_positivity
    hfmin ψ hψcompact hψsupport

@[simp] theorem CenteredCorrectionBump.correctedFirstVariation_apply
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ = f.firstVariation (B.correctedVariation ψ) := rfl

theorem CenteredCorrectionBump.correctedFirstVariation_nonneg
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : CenteredCorrectionBump L f) {ψ : PositiveTestFunction}
    (hψ : ∀ x, 0 ≤ ψ.1 x) : 0 ≤ B.correctedFirstVariation ψ := by
  exact B.firstVariation_correctedVariation_nonneg hfmin ψ hψ

theorem CenteredCorrectionBump.firstVariation_decomposition {L : ℝ} {f : HalfLineH1}
    (B : CenteredCorrectionBump L f) (ψ : PositiveTestFunction) :
    f.firstVariation (B.correctedVariation ψ) =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
         B.multiplier * centeredTest L ψ := by
  rw [CenteredCorrectionBump.correctedVariation, CenteredCorrectionBump.correctedTest]
  rw [show PositiveTestFunction.toHalfLineH1 (ψ - B.coefficient ψ • B.test) =
      PositiveTestFunction.toHalfLineH1 ψ - B.coefficient ψ • PositiveTestFunction.toHalfLineH1 B.test by
        rw [sub_eq_add_neg, HalfLineH1.PositiveTestFunction.toHalfLineH1_add,
          show -(B.coefficient ψ • B.test) = (-B.coefficient ψ) • B.test by rw [neg_smul],
          HalfLineH1.PositiveTestFunction.toHalfLineH1_smul, sub_eq_add_neg, neg_smul]]
  rw [sub_eq_add_neg, f.firstVariation_add, show
      -(B.coefficient ψ • PositiveTestFunction.toHalfLineH1 B.test) =
        (-B.coefficient ψ) • PositiveTestFunction.toHalfLineH1 B.test by rw [neg_smul],
      f.firstVariation_smul]
  dsimp [CenteredCorrectionBump.multiplier, CenteredCorrectionBump.coefficient]
  field_simp [B.centered_ne_zero]

theorem CenteredCorrectionBump.correctedFirstVariation_decomposition
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
        B.multiplier * centeredTest L ψ := by
  rw [B.correctedFirstVariation_apply]
  exact B.firstVariation_decomposition ψ

/-- Centered-bump multipliers are independent of the centered bump witness. -/
theorem CenteredCorrectionBump.multiplier_eq_of_isMinimizer
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ B₂ : CenteredCorrectionBump L f) : B₁.multiplier = B₂.multiplier := by
  have h := B₁.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity
    hfmin B₂.test B₂.hasCompactSupport B₂.support
  rw [B₁.correctedFirstVariation_decomposition] at h
  have hc₁ : centeredTest L B₁.test ≠ 0 := B₁.centered_ne_zero
  have hc₂ : centeredTest L B₂.test ≠ 0 := B₂.centered_ne_zero
  have h' := B₂.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity
    hfmin B₁.test B₁.hasCompactSupport B₁.support
  rw [B₂.correctedFirstVariation_decomposition] at h'
  rw [CenteredCorrectionBump.multiplier] at h h' ⊢
  apply (div_eq_div_iff hc₁ hc₂).mpr
  field_simp [hc₁, hc₂] at h h'
  nlinarith [h]

private lemma solve_centered_two_bump_system
    {m₁ j₁ m₂ j₂ x y : ℝ}
    (hdet : 0 < m₁ * j₂ - m₂ * j₁)
    (heq₁ : x * j₁ + y * m₁ = 0)
    (heq₂ : x * j₂ + y * m₂ = 0) : x = 0 ∧ y = 0 := by
  have hx : x = 0 := by
    have hmul : x * (m₂ * j₁ - m₁ * j₂) = 0 := by
      linear_combination m₂ * heq₁ - m₁ * heq₂
    have hne : m₂ * j₁ - m₁ * j₂ ≠ 0 := by nlinarith
    exact (mul_eq_zero.mp hmul).resolve_right hne
  have hy : y = 0 := by
    have hmul : y * (m₁ * j₂ - m₂ * j₁) = 0 := by
      linear_combination j₂ * heq₁ - j₁ * heq₂
    have hne : m₁ * j₂ - m₂ * j₁ ≠ 0 := ne_of_gt hdet
    exact (mul_eq_zero.mp hmul).resolve_right hne
  exact ⟨hx, hy⟩

private theorem CenteredCorrectionBump.coefficients_eq_correctionBumps
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps) :
    B₁.multiplier = B₂.momentMultiplier ∧
      B₂.massMultiplier + B₁.multiplier * L = 0 := by
  have hl₁ := B₁.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity hfmin
    B₂.bumpLeft B₂.left_hasCompactSupport B₂.left_support
  have hr₁ := B₁.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity hfmin
    B₂.bumpRight B₂.right_hasCompactSupport B₂.right_support
  have hl₂ := B₂.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity hfmin
    B₂.bumpLeft B₂.left_hasCompactSupport B₂.left_support
  have hr₂ := B₂.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity hfmin
    B₂.bumpRight B₂.right_hasCompactSupport B₂.right_support
  rw [B₁.correctedFirstVariation_decomposition] at hl₁ hr₁
  rw [B₂.correctedFirstVariation_multiplier_decomposition] at hl₂ hr₂
  simp [centeredTest, PositiveTestFunction.testMass,
    PositiveTestFunction.testFirstMoment] at hl₁ hr₁ hl₂ hr₂
  let m₁ := ∫ x, B₂.bumpLeft.1 x
  let j₁ := ∫ x, x * B₂.bumpLeft.1 x
  let m₂ := ∫ x, B₂.bumpRight.1 x
  let j₂ := ∫ x, x * B₂.bumpRight.1 x
  let x := B₁.multiplier - B₂.momentMultiplier
  let y := -L * B₁.multiplier - B₂.massMultiplier
  have heq₁ : x * j₁ + y * m₁ = 0 := by
    dsimp [x, y, m₁, j₁]
    linear_combination hl₁ - hl₂
  have heq₂ : x * j₂ + y * m₂ = 0 := by
    dsimp [x, y, m₂, j₂]
    linear_combination hr₁ - hr₂
  have hdet : 0 < m₁ * j₂ - m₂ * j₁ := by
    dsimp [m₁, j₁, m₂, j₂]
    have h := B₂.testDeterminant_pos
    dsimp [HalfLineH1.CorrectionBumps.testDeterminant] at h
    simpa [m₁, j₁, m₂, j₂, PositiveTestFunction.testMass,
      PositiveTestFunction.testFirstMoment, HalfLineH1.mass,
      HalfLineH1.firstMoment, RayleighKernel.mass, halfLine, mul_comm] using h
  have ⟨hx, hy⟩ := solve_centered_two_bump_system hdet heq₁ heq₂
  constructor
  · dsimp [x] at hx
    exact sub_eq_zero.mp hx
  · linarith [hy]

/-- A centered-bump multiplier agrees with the moment multiplier of any two-bump witness.

The proof uses the positive mass--moment determinant of the two-bump witness and does
not depend on the later ODE multiplier-balance theorem. -/
theorem CenteredCorrectionBump.multiplier_eq_correctionBumps_momentMultiplier
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps) :
    B₁.multiplier = B₂.momentMultiplier := by
  exact (B₁.coefficients_eq_correctionBumps hfmin B₂).1

/-- The mass coefficient and centered-bump multiplier satisfy the old witness balance. -/
theorem CenteredCorrectionBump.correctionBumps_massMultiplier_add_mul_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps) :
    B₂.massMultiplier + B₁.multiplier * L = 0 := by
  exact (B₁.coefficients_eq_correctionBumps hfmin B₂).2

/-- The old two-bump multiplier balance follows directly from a centered witness. -/
theorem HalfLineH1.balance_from_centered_bridge
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps) :
    B₂.massMultiplier + B₂.momentMultiplier * L = 0 := by
  have h := B₁.correctionBumps_massMultiplier_add_mul_eq_zero hfmin B₂
  have hm := B₁.multiplier_eq_correctionBumps_momentMultiplier hfmin B₂
  rw [← hm]
  exact h

/-- The centered-bump and two-bump corrected first-variation maps agree. -/
theorem CenteredCorrectionBump.correctedFirstVariation_eq_correctionBumps
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps) :
    B₁.correctedFirstVariation = B₂.correctedFirstVariation := by
  have hm := B₁.multiplier_eq_correctionBumps_momentMultiplier hfmin B₂
  have hbal := B₁.correctionBumps_massMultiplier_add_mul_eq_zero hfmin B₂
  apply LinearMap.ext
  intro ψ
  rw [B₁.correctedFirstVariation_decomposition,
    B₂.correctedFirstVariation_multiplier_decomposition, hm]
  simp only [centeredTest]
  have hbal' : B₂.massMultiplier + B₁.multiplier * L = 0 := hbal
  change f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
      B₂.momentMultiplier * ((∫ x, x * ψ.1 x) - L * ∫ x, ψ.1 x) =
    f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
      B₂.massMultiplier * (∫ x, ψ.1 x) +
        B₂.momentMultiplier * (∫ x, x * ψ.1 x)
  have hbal₂ : B₂.massMultiplier + B₂.momentMultiplier * L = 0 := by
    rw [← hm]
    exact hbal'
  have hmB : B₂.massMultiplier = -B₂.momentMultiplier * L := by linarith [hbal₂]
  rw [hmB]
  ring

/-- The established two-bump reaction measure represents the centered corrected
first variation on compactly supported smooth positive tests. -/
theorem CenteredCorrectionBump.integral_correctionBumps_reactionMeasure_smooth
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps)
    (ψ : PositiveTestFunction) (hcompact : HasCompactSupport ψ.1) :
    ∫ x, ψ.1 x ∂B₂.reactionMeasure hfmin = B₁.correctedFirstVariation ψ := by
  rw [B₂.integral_reactionMeasure_smooth hfmin ψ hcompact]
  exact (B₁.correctedFirstVariation_eq_correctionBumps hfmin B₂).symm ▸ rfl

/-- The preceding reaction-measure bridge in centered forcing form. -/
theorem CenteredCorrectionBump.integral_correctionBumps_reactionMeasure_forcing
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ : CenteredCorrectionBump L f) (B₂ : f.CorrectionBumps)
    (ψ : PositiveTestFunction) (hcompact : HasCompactSupport ψ.1) :
    ∫ x, ψ.1 x ∂B₂.reactionMeasure hfmin =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
        B₁.multiplier * (∫ x : ℝ, (x - L) * ψ.1 x) := by
  rw [B₁.integral_correctionBumps_reactionMeasure_smooth hfmin B₂ ψ hcompact]
  rw [B₁.correctedFirstVariation_decomposition, centeredTest_eq_integral]

/-- The centered corrected first-variation map is independent of its witness. -/
theorem CenteredCorrectionBump.correctedFirstVariation_eq_of_isMinimizer
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B₁ B₂ : CenteredCorrectionBump L f) :
    B₁.correctedFirstVariation = B₂.correctedFirstVariation := by
  apply LinearMap.ext
  intro ψ
  rw [B₁.correctedFirstVariation_decomposition, B₂.correctedFirstVariation_decomposition,
    B₁.multiplier_eq_of_isMinimizer hfmin B₂]

theorem CenteredCorrectionBump.correctedFirstVariation_forcing
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
        B.multiplier * (∫ x : ℝ, (x - L) * ψ.1 x) := by
  rw [B.correctedFirstVariation_decomposition, centeredTest_eq_integral]

theorem CenteredCorrectionBump.firstVariation_correctedVariation_nonneg_for_nonnegative
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : CenteredCorrectionBump L f) {ψ : PositiveTestFunction}
    (hψ : ∀ x, 0 ≤ ψ.1 x) : 0 ≤ B.correctedFirstVariation ψ := by
  exact B.correctedFirstVariation_nonneg hfmin hψ

theorem CenteredCorrectionBump.firstVariation_correctedVariation_forcing
    {L : ℝ} {f : HalfLineH1} (B : CenteredCorrectionBump L f)
    (ψ : PositiveTestFunction) :
    f.firstVariation (B.correctedVariation ψ) =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
        (-f.firstVariation (PositiveTestFunction.toHalfLineH1 B.test) /
          centeredTest L B.test) * (∫ x : ℝ, (x - L) * ψ.1 x) := by
  rw [← B.correctedFirstVariation_apply, B.correctedFirstVariation_forcing]
  rfl

end RayleighKernel.Analysis
