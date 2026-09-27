import RayleighKernel.Obstacle.Variations
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

noncomputable section
namespace RayleighKernel
namespace Analysis
open MeasureTheory Set
open scoped SchwartzMap Topology CompactlySupported

lemma PositiveTestFunction.testMass_add (φ ψ : PositiveTestFunction) :
    PositiveTestFunction.testMass (φ + ψ) = PositiveTestFunction.testMass φ +
      PositiveTestFunction.testMass ψ := by
  change ∫ x : ℝ, (φ.1 x + ψ.1 x) = (∫ x : ℝ, φ.1 x) + ∫ x : ℝ, ψ.1 x
  rw [integral_add φ.1.integrable ψ.1.integrable]

lemma PositiveTestFunction.testMass_smul (c : ℝ) (φ : PositiveTestFunction) :
    PositiveTestFunction.testMass (c • φ) = c * PositiveTestFunction.testMass φ := by
  change ∫ x : ℝ, c * φ.1 x = c * ∫ x : ℝ, φ.1 x
  exact integral_smul c φ.1

lemma PositiveTestFunction.testFirstMoment_add (φ ψ : PositiveTestFunction) :
    PositiveTestFunction.testFirstMoment (φ + ψ) = PositiveTestFunction.testFirstMoment φ +
      PositiveTestFunction.testFirstMoment ψ := by
  change ∫ x : ℝ, x * (φ.1 x + ψ.1 x) =
    (∫ x : ℝ, x * φ.1 x) + ∫ x : ℝ, x * ψ.1 x
  rw [show (fun x : ℝ => x * (φ.1 x + ψ.1 x)) =
      (fun x => x * φ.1 x + x * ψ.1 x) by funext x; ring, integral_add]
  · exact (φ.1.integrable_pow_mul volume 1).mono
      (continuous_id.mul φ.1.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs])
  · exact (ψ.1.integrable_pow_mul volume 1).mono
      (continuous_id.mul ψ.1.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs])

lemma PositiveTestFunction.testFirstMoment_smul (c : ℝ) (φ : PositiveTestFunction) :
    PositiveTestFunction.testFirstMoment (c • φ) = c * PositiveTestFunction.testFirstMoment φ := by
  change ∫ x : ℝ, x * (c * φ.1 x) = c * ∫ x : ℝ, x * φ.1 x
  rw [show (fun x : ℝ => x * (c * φ.1 x)) =
      c • (fun x : ℝ => x * φ.1 x) by funext x; simp [smul_eq_mul, mul_left_comm]]
  exact integral_smul c (fun x : ℝ => x * φ.1 x)

def PositiveTestFunction.massMoment : PositiveTestFunction →ₗ[ℝ] ℝ × ℝ where
  toFun φ := (PositiveTestFunction.testMass φ, PositiveTestFunction.testFirstMoment φ)
  map_add' φ ψ := by
    rw [PositiveTestFunction.testMass_add, PositiveTestFunction.testFirstMoment_add]
    rfl
  map_smul' c φ := by
    rw [PositiveTestFunction.testMass_smul, PositiveTestFunction.testFirstMoment_smul]
    rfl

@[simp] lemma PositiveTestFunction.massMoment_apply (φ : PositiveTestFunction) :
    PositiveTestFunction.massMoment φ =
      (PositiveTestFunction.testMass φ, PositiveTestFunction.testFirstMoment φ) := rfl

namespace HalfLineH1

def CorrectionBumps.testDeterminant {f : HalfLineH1} (B : f.CorrectionBumps) : ℝ :=
  PositiveTestFunction.testMass B.bumpLeft * PositiveTestFunction.testFirstMoment B.bumpRight -
    PositiveTestFunction.testMass B.bumpRight * PositiveTestFunction.testFirstMoment B.bumpLeft

lemma CorrectionBumps.testDeterminant_pos {f : HalfLineH1} (B : f.CorrectionBumps) :
    0 < B.testDeterminant := by
  rw [CorrectionBumps.testDeterminant]
  rw [PositiveTestFunction.testMass_eq_mass B.bumpLeft,
    PositiveTestFunction.testMass_eq_mass B.bumpRight,
    testFirstMoment_bridge B.bumpLeft, testFirstMoment_bridge B.bumpRight]
  exact B.determinant_pos

def CorrectionBumps.leftCoefficient {f : HalfLineH1} (B : f.CorrectionBumps) :
    (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  let m1 := PositiveTestFunction.testMass B.bumpLeft
  let j1 := PositiveTestFunction.testFirstMoment B.bumpLeft
  let m2 := PositiveTestFunction.testMass B.bumpRight
  let j2 := PositiveTestFunction.testFirstMoment B.bumpRight
  let det := B.testDeterminant
  { toFun := fun z => (j2 * z.1 - m2 * z.2) / det
    map_add' := by
      intro x y
      dsimp
      ring
    map_smul' := by
      intro c z
      dsimp
      ring }

def CorrectionBumps.rightCoefficient {f : HalfLineH1} (B : f.CorrectionBumps) :
    (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  let m1 := PositiveTestFunction.testMass B.bumpLeft
  let j1 := PositiveTestFunction.testFirstMoment B.bumpLeft
  let m2 := PositiveTestFunction.testMass B.bumpRight
  let j2 := PositiveTestFunction.testFirstMoment B.bumpRight
  let det := B.testDeterminant
  { toFun := fun z => (-j1 * z.1 + m1 * z.2) / det
    map_add' := by
      intro x y
      dsimp
      ring
    map_smul' := by
      intro c z
      dsimp
      ring }

def CorrectionBumps.rightInverse {f : HalfLineH1} (B : f.CorrectionBumps) :
    (ℝ × ℝ) →ₗ[ℝ] PositiveTestFunction :=
  { toFun := fun z => B.leftCoefficient z • B.bumpLeft + B.rightCoefficient z • B.bumpRight
    map_add' := by
      intro x y
      rw [B.leftCoefficient.map_add, B.rightCoefficient.map_add]
      rw [add_smul, add_smul]
      exact add_add_add_comm _ _ _ _
    map_smul' := by
      intro c z
      rw [B.leftCoefficient.map_smul, B.rightCoefficient.map_smul]
      simp only [RingHom.id_apply]
      module }

theorem CorrectionBumps.massMoment_rightInverse {f : HalfLineH1} (B : f.CorrectionBumps)
    (z : ℝ × ℝ) :
    PositiveTestFunction.massMoment (B.rightInverse z) = z := by
  let m1 := PositiveTestFunction.testMass B.bumpLeft
  let j1 := PositiveTestFunction.testFirstMoment B.bumpLeft
  let m2 := PositiveTestFunction.testMass B.bumpRight
  let j2 := PositiveTestFunction.testFirstMoment B.bumpRight
  let det := B.testDeterminant
  have hdet : det ≠ 0 := ne_of_gt (CorrectionBumps.testDeterminant_pos B)
  apply Prod.ext
  · change PositiveTestFunction.testMass (B.rightInverse z) = z.1
    rw [show B.rightInverse z = B.leftCoefficient z • B.bumpLeft +
      B.rightCoefficient z • B.bumpRight by rfl]
    rw [PositiveTestFunction.testMass_add, PositiveTestFunction.testMass_smul,
      PositiveTestFunction.testMass_smul]
    change (j2 * z.1 - m2 * z.2) / det * m1 +
      (-j1 * z.1 + m1 * z.2) / det * m2 = z.1
    field_simp [hdet]
    dsimp [det, CorrectionBumps.testDeterminant]
    ring
  · change PositiveTestFunction.testFirstMoment (B.rightInverse z) = z.2
    rw [show B.rightInverse z = B.leftCoefficient z • B.bumpLeft +
      B.rightCoefficient z • B.bumpRight by rfl]
    rw [PositiveTestFunction.testFirstMoment_add,
      PositiveTestFunction.testFirstMoment_smul,
      PositiveTestFunction.testFirstMoment_smul]
    change (j2 * z.1 - m2 * z.2) / det * j1 +
      (-j1 * z.1 + m1 * z.2) / det * j2 = z.2
    field_simp [hdet]
    dsimp [det, CorrectionBumps.testDeterminant]
    ring

def CorrectionBumps.correctedTest {f : HalfLineH1} (B : f.CorrectionBumps)
    (ψ : PositiveTestFunction) : PositiveTestFunction :=
  ψ - B.rightInverse (PositiveTestFunction.massMoment ψ)

def CorrectionBumps.correctedVariation {f : HalfLineH1} (B : f.CorrectionBumps)
    (ψ : PositiveTestFunction) : HalfLineH1 :=
  PositiveTestFunction.toHalfLineH1 (B.correctedTest ψ)

theorem CorrectionBumps.massMoment_correctedTest {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    PositiveTestFunction.massMoment (B.correctedTest ψ) = 0 := by
  rw [CorrectionBumps.correctedTest, map_sub,
    B.massMoment_rightInverse]
  exact sub_self _

theorem CorrectionBumps.correctedVariation_mass {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    (B.correctedVariation ψ).mass = 0 := by
  rw [CorrectionBumps.correctedVariation]
  rw [← PositiveTestFunction.testMass_eq_mass]
  have h := congrArg Prod.fst (B.massMoment_correctedTest ψ)
  simpa [PositiveTestFunction.massMoment_apply] using h

theorem CorrectionBumps.correctedVariation_firstMoment {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    (B.correctedVariation ψ).firstMoment = 0 := by
  rw [CorrectionBumps.correctedVariation]
  rw [← testFirstMoment_bridge]
  have h := congrArg Prod.snd (B.massMoment_correctedTest ψ)
  simpa [PositiveTestFunction.massMoment_apply] using h

end HalfLineH1

namespace HalfLineH1

lemma CorrectionBumps.compact_support_union {f : HalfLineH1} (B : f.CorrectionBumps) :
    IsCompact (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1) := by
  have hl : IsCompact (closure (Function.support B.bumpLeft.1)) :=
    hasCompactSupport_def.mp B.left_hasCompactSupport
  have hr : IsCompact (closure (Function.support B.bumpRight.1)) :=
    hasCompactSupport_def.mp B.right_hasCompactSupport
  simpa [tsupport] using hl.union hr

lemma CorrectionBumps.support_union_subset_positivity {f : HalfLineH1} (B : f.CorrectionBumps) :
    (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1) ⊆ f.positivitySet := by
  exact union_subset B.left_support B.right_support

lemma CorrectionBumps.exists_pos_lower_bound {f : HalfLineH1} (B : f.CorrectionBumps) :
    ∃ δ > 0, ∀ x ∈ tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1,
      δ ≤ f.continuousRep x := by
  let K := tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1
  have hK : IsCompact K := by
    dsimp [K]
    exact B.compact_support_union
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne
      f.continuous_continuousRep.continuousOn
    have hpos : 0 < f.continuousRep x := B.support_union_subset_positivity hxK
    refine ⟨f.continuousRep x, hpos, ?_⟩
    intro y hy
    exact hx hy
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

lemma CorrectionBumps.exists_correction_bound {f : HalfLineH1} (B : f.CorrectionBumps)
    (ψ : PositiveTestFunction) :
    ∃ C ≥ 0, ∀ x, |(B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x| ≤ C := by
  let z := PositiveTestFunction.massMoment ψ
  let a := B.leftCoefficient z
  let b := B.rightCoefficient z
  refine ⟨|a| * (SchwartzMap.seminorm ℝ 0 0 B.bumpLeft.1) +
      |b| * (SchwartzMap.seminorm ℝ 0 0 B.bumpRight.1), ?_, ?_⟩
  · positivity
  · intro x
    change |a * B.bumpLeft.1 x + b * B.bumpRight.1 x| ≤ _
    calc
      |a * B.bumpLeft.1 x + b * B.bumpRight.1 x| ≤
          |a| * |B.bumpLeft.1 x| + |b| * |B.bumpRight.1 x| := by
            simpa [abs_mul] using (abs_add_le (a * B.bumpLeft.1 x) (b * B.bumpRight.1 x))
      _ ≤ |a| * (SchwartzMap.seminorm ℝ 0 0 B.bumpLeft.1) +
          |b| * (SchwartzMap.seminorm ℝ 0 0 B.bumpRight.1) := by
        gcongr
        · exact SchwartzMap.norm_le_seminorm ℝ B.bumpLeft.1 x
        · exact SchwartzMap.norm_le_seminorm ℝ B.bumpRight.1 x

lemma CorrectionBumps.correctedVariation_continuousRep {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) (x : ℝ) :
    (B.correctedVariation ψ).continuousRep x =
      ψ.1 x - (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x := by
  rw [CorrectionBumps.correctedVariation,
    PositiveTestFunction.continuousRep_toHalfLineH1,
    CorrectionBumps.correctedTest]
  rfl

lemma CorrectionBumps.correctedVariation_integrable {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    IntegrableOn (B.correctedVariation ψ).continuousRep halfLine := by
  have hψ : Integrable ψ.1 := ψ.1.integrable
  have hr : Integrable (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 :=
    (B.rightInverse (PositiveTestFunction.massMoment ψ)).1.integrable
  have hd : Integrable (fun x => ψ.1 x -
      (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x) := hψ.sub hr
  rw [show (B.correctedVariation ψ).continuousRep =
      fun x => ψ.1 x - (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x by
    funext x; exact B.correctedVariation_continuousRep ψ x]
  exact hd.mono_measure (Measure.restrict_le_self)

lemma CorrectionBumps.correctedVariation_firstMoment_integrable {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    IntegrableOn (fun x => x * (B.correctedVariation ψ).continuousRep x) halfLine := by
  let φ := B.correctedTest ψ
  have hi : Integrable (fun x => x * φ.1 x) := by
    exact (φ.1.integrable_pow_mul volume 1).mono
      ((continuous_id.mul φ.1.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs])
  rw [show (B.correctedVariation ψ).continuousRep = φ.1 by
    funext x
    exact PositiveTestFunction.continuousRep_toHalfLineH1 φ x]
  exact hi.mono_measure (Measure.restrict_le_self)

lemma mass_add_continuousRep {u v : HalfLineH1}
    (hu : IntegrableOn u.continuousRep halfLine)
    (hv : IntegrableOn v.continuousRep halfLine) :
    (u + v).mass = u.mass + v.mass := by
  rw [HalfLineH1.mass, HalfLineH1.mass, HalfLineH1.mass,
    HalfLineH1.continuousRep_add]
  exact integral_add hu hv

lemma mass_smul_continuousRep {c : ℝ} {u : HalfLineH1}
    :
    (c • u).mass = c * u.mass := by
  rw [HalfLineH1.mass, HalfLineH1.mass, HalfLineH1.continuousRep_smul]
  exact integral_smul c (u.continuousRep) |>.trans (by rfl)

lemma firstMoment_add_continuousRep {u v : HalfLineH1}
    (hu1 : IntegrableOn (fun x => x * u.continuousRep x) halfLine)
    (hv1 : IntegrableOn (fun x => x * v.continuousRep x) halfLine) :
    (u + v).firstMoment = u.firstMoment + v.firstMoment := by
  rw [HalfLineH1.firstMoment, HalfLineH1.firstMoment, HalfLineH1.firstMoment,
    HalfLineH1.continuousRep_add, RayleighKernel.firstMoment]
  simp only [Pi.add_apply]
  rw [show (fun x => x * (u.continuousRep x + v.continuousRep x)) =
      (fun x => x * u.continuousRep x + x * v.continuousRep x) by
        funext x; ring]
  exact integral_add hu1 hv1

lemma firstMoment_smul_continuousRep {c : ℝ} {u : HalfLineH1}
    :
    (c • u).firstMoment = c * u.firstMoment := by
  rw [HalfLineH1.firstMoment, HalfLineH1.firstMoment, HalfLineH1.continuousRep_smul]
  rw [RayleighKernel.firstMoment]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (fun x => x * (c * u.continuousRep x)) =
      (fun x => c * (x * u.continuousRep x)) by
        funext x; ring]
  exact integral_smul c _

theorem CorrectionBumps.exists_pos_of_nonnegative_correctedVariation
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψ : ∀ x, 0 ≤ ψ.1 x) :
    ∃ (ε0 : ℝ), ε0 > 0 ∧ ∀ ε, 0 < ε → ε ≤ ε0 →
      ∀ x ∈ halfLine, 0 ≤ (f + ε • B.correctedVariation ψ).continuousRep x := by
  obtain ⟨δ, hδ, hδK⟩ := B.exists_pos_lower_bound
  obtain ⟨C, hC, hCr⟩ := B.exists_correction_bound ψ
  refine ⟨δ / (C + 1), div_pos hδ (by linarith), ?_⟩
  intro ε hε hε0 x hx
  rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [B.correctedVariation_continuousRep]
  by_cases hK : x ∈ tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1
  · have hfx : δ ≤ f.continuousRep x := hδK x hK
    have hr : |(B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x| ≤ C := hCr x
    have hlow : -C ≤ ψ.1 x - (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x := by
      have habs : -(C : ℝ) ≤ (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x :=
        by linarith [neg_le_of_abs_le hr]
      have hup : (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x ≤ C :=
        le_trans (le_abs_self _) hr
      linarith [hψ x, hup]
    have heC : ε * C ≤ δ := by
      have hden : 0 < C + 1 := by linarith
      have hmul : ε * (C + 1) ≤ δ := (le_div_iff₀ hden).mp hε0
      nlinarith [hC, hε, hmul]
    nlinarith
  · have hleft : B.bumpLeft.1 x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hK (Or.inl h)
    have hright : B.bumpRight.1 x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hK (Or.inr h)
    have hrzero : (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x = 0 := by
      change B.leftCoefficient (PositiveTestFunction.massMoment ψ) * B.bumpLeft.1 x +
        B.rightCoefficient (PositiveTestFunction.massMoment ψ) * B.bumpRight.1 x = 0
      simp [hleft, hright]
    rw [hrzero, sub_zero]
    exact add_nonneg (hf.nonnegative x hx) (mul_nonneg (le_of_lt hε) (hψ x))

theorem CorrectionBumps.exists_pos_isAdmissible_correctedVariation
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψ : ∀ x, 0 ≤ ψ.1 x) :
    ∃ (ε0 : ℝ), ε0 > 0 ∧ ∀ ε, 0 < ε → ε ≤ ε0 →
      (f + ε • B.correctedVariation ψ).IsAdmissible L := by
  obtain ⟨ε0, hε0, hfeas⟩ :=
    CorrectionBumps.exists_pos_of_nonnegative_correctedVariation hf B ψ hψ
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hεle
  let h := B.correctedVariation ψ
  have hi : IntegrableOn (f + ε • h).continuousRep halfLine := by
    rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
    exact hf.integrable.add ((B.correctedVariation_integrable ψ).smul ε)
  have hi1 : IntegrableOn (fun x => x * (f + ε • h).continuousRep x) halfLine := by
    rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
    have hs : IntegrableOn (fun x => x * (ε * h.continuousRep x)) halfLine := by
      change Integrable (fun x => x * (ε * h.continuousRep x))
        (Measure.restrict volume halfLine)
      simpa [h, mul_comm, mul_left_comm, mul_assoc] using
        (B.correctedVariation_firstMoment_integrable ψ).const_mul ε
    rw [show (fun x => x * (f.continuousRep + ε • h.continuousRep) x) =
        (fun x => x * f.continuousRep x + x * (ε * h.continuousRep x)) by
          funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring]
    exact hf.firstMoment_integrable.add hs
  refine ⟨hfeas ε hε hεle, hi, hi1, ?_, ?_⟩
  ·
    have hεi : IntegrableOn (ε • B.correctedVariation ψ).continuousRep halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      exact (B.correctedVariation_integrable ψ).const_mul ε
    calc
      (f + ε • B.correctedVariation ψ).mass =
          f.mass + (ε • B.correctedVariation ψ).mass :=
        mass_add_continuousRep hf.integrable hεi
      _ = f.mass + ε * (B.correctedVariation ψ).mass := by
        rw [mass_smul_continuousRep]
      _ = 1 := by rw [hf.mass_eq, B.correctedVariation_mass]; simp
  ·
    have hεi : IntegrableOn (ε • B.correctedVariation ψ).continuousRep halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      exact (B.correctedVariation_integrable ψ).const_mul ε
    have hεi1 : IntegrableOn (fun x => x * (ε • B.correctedVariation ψ).continuousRep x)
        halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      change Integrable (fun x => x * (ε * (B.correctedVariation ψ).continuousRep x))
        (Measure.restrict volume halfLine)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (B.correctedVariation_firstMoment_integrable ψ).const_mul ε
    calc
      (f + ε • B.correctedVariation ψ).firstMoment =
          f.firstMoment + (ε • B.correctedVariation ψ).firstMoment :=
        firstMoment_add_continuousRep hf.firstMoment_integrable hεi1
      _ = f.firstMoment + ε * (B.correctedVariation ψ).firstMoment := by
        rw [firstMoment_smul_continuousRep]
      _ = L := by rw [hf.firstMoment_eq, B.correctedVariation_firstMoment]; simp

theorem CorrectionBumps.firstVariation_correctedVariation_nonneg
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψ : ∀ x, 0 ≤ ψ.1 x) :
    0 ≤ f.firstVariation (B.correctedVariation ψ) := by
  obtain ⟨ε0, hε0, hfeas⟩ :=
    CorrectionBumps.exists_pos_isAdmissible_correctedVariation hfmin.1 B ψ hψ
  let h := B.correctedVariation ψ
  have hden : 0 < f.squareEnergy := f.squareEnergy_pos_of_mass_eq_one hfmin.1.mass_eq
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ => (f + s • h).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hq := hfmin.2 (f + t • h) (hfeas t ht.1 ht.2.le)
    have hsub : 0 ≤ (f + t • h).rayleighQuotient - f.rayleighQuotient := sub_nonneg.mpr hq
    have htpos : 0 < t := ht.1
    simpa using (div_nonneg hsub (le_of_lt htpos))
  exact HalfLineH1.firstVariation_nonneg_of_eventually_slope_nonneg f h hden hev

@[simp] lemma PositiveTestFunction.toHalfLineH1_add (φ ψ : PositiveTestFunction) :
    PositiveTestFunction.toHalfLineH1 (φ + ψ) =
      PositiveTestFunction.toHalfLineH1 φ + PositiveTestFunction.toHalfLineH1 ψ := by
  apply Subtype.ext
  exact positiveTestGraph.map_add φ ψ

@[simp] lemma PositiveTestFunction.toHalfLineH1_smul (c : ℝ) (φ : PositiveTestFunction) :
    PositiveTestFunction.toHalfLineH1 (c • φ) =
      c • PositiveTestFunction.toHalfLineH1 φ := by
  apply Subtype.ext
  exact positiveTestGraph.map_smul c φ

@[simp] theorem CorrectionBumps.correctedVariation_add {f : HalfLineH1}
    (B : f.CorrectionBumps) (φ ψ : PositiveTestFunction) :
    B.correctedVariation (φ + ψ) = B.correctedVariation φ + B.correctedVariation ψ := by
  rw [CorrectionBumps.correctedVariation, CorrectionBumps.correctedVariation,
    CorrectionBumps.correctedVariation]
  rw [show B.correctedTest (φ + ψ) = B.correctedTest φ + B.correctedTest ψ by
    dsimp [CorrectionBumps.correctedTest]
    rw [PositiveTestFunction.testMass_add, PositiveTestFunction.testFirstMoment_add]
    have hm := PositiveTestFunction.massMoment.map_add φ ψ
    have hm' :
        (PositiveTestFunction.testMass φ + PositiveTestFunction.testMass ψ,
          PositiveTestFunction.testFirstMoment φ + PositiveTestFunction.testFirstMoment ψ) =
          PositiveTestFunction.massMoment φ + PositiveTestFunction.massMoment ψ := by
      convert hm.symm using 1 <;>
        simp [PositiveTestFunction.massMoment_apply,
          PositiveTestFunction.testMass_add, PositiveTestFunction.testFirstMoment_add,
          Prod.mk_add_mk]
    rw [hm', map_add]
    simp only [sub_eq_add_neg]
    abel]
  rw [PositiveTestFunction.toHalfLineH1_add]

@[simp] theorem CorrectionBumps.correctedVariation_smul {f : HalfLineH1}
    (B : f.CorrectionBumps) (c : ℝ) (φ : PositiveTestFunction) :
    B.correctedVariation (c • φ) = c • B.correctedVariation φ := by
  rw [CorrectionBumps.correctedVariation, CorrectionBumps.correctedVariation,
    show B.correctedTest (c • φ) = c • B.correctedTest φ by
      dsimp [CorrectionBumps.correctedTest]
      rw [PositiveTestFunction.testMass_smul, PositiveTestFunction.testFirstMoment_smul]
      have hm := PositiveTestFunction.massMoment.map_smul c φ
      have hm' : (c * PositiveTestFunction.testMass φ,
          c * PositiveTestFunction.testFirstMoment φ) =
          c • PositiveTestFunction.massMoment φ := by
        rw [PositiveTestFunction.massMoment_apply] at hm
        rw [PositiveTestFunction.testMass_smul, PositiveTestFunction.testFirstMoment_smul] at hm
        exact hm
      rw [hm', map_smul]
      simp only [sub_eq_add_neg, smul_add, smul_neg]
      abel,
    PositiveTestFunction.toHalfLineH1_smul]

def CorrectionBumps.correctedFirstVariation {f : HalfLineH1}
    (B : f.CorrectionBumps) : PositiveTestFunction →ₗ[ℝ] ℝ where
  toFun ψ := f.firstVariation (B.correctedVariation ψ)
  map_add' φ ψ := by rw [B.correctedVariation_add, f.firstVariation_add]
  map_smul' c φ := by
    rw [B.correctedVariation_smul, f.firstVariation_smul]
    simp [smul_eq_mul]

@[simp] theorem CorrectionBumps.correctedFirstVariation_apply {f : HalfLineH1}
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ = f.firstVariation (B.correctedVariation ψ) := rfl

theorem CorrectionBumps.correctedFirstVariation_nonneg
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L) (B : f.CorrectionBumps)
    {ψ : PositiveTestFunction} (hψ : ∀ x, 0 ≤ ψ.1 x) :
    0 ≤ B.correctedFirstVariation ψ := by
  exact CorrectionBumps.firstVariation_correctedVariation_nonneg hfmin B ψ hψ

theorem CorrectionBumps.correctedFirstVariation_decomposition
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ =
      f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) -
        f.firstVariation
          (PositiveTestFunction.toHalfLineH1
            (B.rightInverse (PositiveTestFunction.massMoment ψ))) := by
  rw [CorrectionBumps.correctedFirstVariation_apply, CorrectionBumps.correctedVariation,
    CorrectionBumps.correctedTest]
  have hsub :
      PositiveTestFunction.toHalfLineH1
          (ψ - B.rightInverse (PositiveTestFunction.massMoment ψ)) =
        PositiveTestFunction.toHalfLineH1 ψ -
          PositiveTestFunction.toHalfLineH1
            (B.rightInverse (PositiveTestFunction.massMoment ψ)) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, PositiveTestFunction.toHalfLineH1_add]
    congr 1
    rw [show -B.rightInverse (PositiveTestFunction.massMoment ψ) =
      (-1 : ℝ) • B.rightInverse (PositiveTestFunction.massMoment ψ) by simp]
    rw [PositiveTestFunction.toHalfLineH1_smul]
    simp
  rw [hsub, sub_eq_add_neg, f.firstVariation_add]
  have hn := f.firstVariation_smul (-1)
    (PositiveTestFunction.toHalfLineH1
      (B.rightInverse (PositiveTestFunction.massMoment ψ)))
  rw [show -PositiveTestFunction.toHalfLineH1
      (B.rightInverse (PositiveTestFunction.massMoment ψ)) =
      (-1 : ℝ) • PositiveTestFunction.toHalfLineH1
        (B.rightInverse (PositiveTestFunction.massMoment ψ)) by simp, hn]
  have hmass : PositiveTestFunction.massMoment ψ =
      (PositiveTestFunction.testMass ψ, PositiveTestFunction.testFirstMoment ψ) := rfl
  rw [hmass]
  simp [sub_eq_add_neg]

theorem exists_nonnegative_compact_cutoff
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) :
    ∃ χ : PositiveTestFunction, HasCompactSupport χ.1 ∧
      (∀ x, 0 ≤ χ.1 x) ∧ (∀ x, χ.1 x ≤ 1) ∧
      (∀ x ∈ K, χ.1 x = 1) := by
  obtain ⟨V, hVopen, hKV, hVcl, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_Ioi hKpos
  obtain ⟨g, hgdiff, hgrange, hgsupp, hgone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVopen hK.isClosed hKV
  let χs : 𝓢(ℝ, ℝ) := (show HasCompactSupport g from by
    rw [hasCompactSupport_def, hgsupp]
    exact hVcompact).toSchwartzMap hgdiff
  have hχsupp : tsupport χs ⊆ Ioi 0 := by
    rw [show tsupport χs = closure (Function.support g) by rfl, hgsupp]
    exact hVcl
  let χ : PositiveTestFunction := ⟨χs, hχsupp⟩
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · change IsCompact (closure (Function.support g))
    rw [hgsupp]
    exact hVcompact
  · intro x
    exact (hgrange ⟨x, rfl⟩).1
  · intro x
    exact (hgrange ⟨x, rfl⟩).2
  · intro x hx
    exact (hgone x).mp hx

theorem CorrectionBumps.correctedFirstVariation_bound_on_compact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {K : Set ℝ} (hK : IsCompact K)
    (hKpos : K ⊆ Ioi 0) :
    ∃ C ≥ 0, ∀ ψ : PositiveTestFunction, tsupport ψ.1 ⊆ K →
      |B.correctedFirstVariation ψ| ≤ C * SchwartzMap.seminorm ℝ 0 0 ψ.1 := by
  obtain ⟨χ, hχcompact, hχnonneg, hχle, hχone⟩ :=
    exists_nonnegative_compact_cutoff hK hKpos
  let C : ℝ := B.correctedFirstVariation χ
  refine ⟨C, CorrectionBumps.correctedFirstVariation_nonneg hfmin B hχnonneg, ?_⟩
  intro ψ hψsupport
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ.1
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hψbound : ∀ x, |ψ.1 x| ≤ M := by
    intro x
    exact SchwartzMap.norm_le_seminorm ℝ ψ.1 x
  have hψzero : ∀ x, x ∉ K → ψ.1 x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hxs => hx (hψsupport hxs))
  have hplus : ∀ x, 0 ≤ (M • χ + ψ).1 x := by
    intro x
    by_cases hx : x ∈ K
    · change 0 ≤ M * χ.1 x + ψ.1 x
      rw [hχone x hx]
      linarith [neg_le_of_abs_le (hψbound x)]
    · change 0 ≤ M * χ.1 x + ψ.1 x
      rw [hψzero x hx]
      simpa using mul_nonneg hM (hχnonneg x)
  have hminus : ∀ x, 0 ≤ (M • χ - ψ).1 x := by
    intro x
    by_cases hx : x ∈ K
    · change 0 ≤ M * χ.1 x - ψ.1 x
      rw [hχone x hx]
      linarith [le_abs_self (ψ.1 x), hψbound x]
    · change 0 ≤ M * χ.1 x - ψ.1 x
      rw [hψzero x hx]
      simpa using mul_nonneg hM (hχnonneg x)
  have hp := CorrectionBumps.correctedFirstVariation_nonneg hfmin B hplus
  have hm := CorrectionBumps.correctedFirstVariation_nonneg hfmin B hminus
  rw [CorrectionBumps.correctedFirstVariation_apply] at hp hm ⊢
  have hp' : 0 ≤ M * B.correctedFirstVariation χ +
      B.correctedFirstVariation ψ := by
    change 0 ≤ B.correctedFirstVariation (M • χ + ψ) at hp
    simpa [map_add, map_smul, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hp
  have hm' : 0 ≤ M * B.correctedFirstVariation χ -
      B.correctedFirstVariation ψ := by
    change 0 ≤ B.correctedFirstVariation (M • χ - ψ) at hm
    rw [B.correctedFirstVariation.map_sub, B.correctedFirstVariation.map_smul] at hm
    simpa [smul_eq_mul, sub_eq_add_neg] using hm
  have hupper : B.correctedFirstVariation ψ ≤ C * M := by
    dsimp [C, M] at *
    linarith [hp']
  have hlower : -(C * M) ≤ B.correctedFirstVariation ψ := by
    dsimp [C, M] at *
    linarith [hm']
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-! The bridge from half-line compactly supported continuous tests to the existing whole-line
Schwartz test functions. -/

def compactTestZeroExtend (φ : C_c(Ioi (0 : ℝ), ℝ)) : ℝ → ℝ :=
  Subtype.val.extend φ 0

lemma compactTestZeroExtend_continuous (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    Continuous (compactTestZeroExtend φ) := by
  exact φ.hasCompactSupport.continuous_extend_zero isOpen_Ioi φ.continuous

lemma compactTestZeroExtend_hasCompactSupport (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    HasCompactSupport (compactTestZeroExtend φ) := by
  exact φ.hasCompactSupport.extend_zero continuous_subtype_val

lemma compactTestZeroExtend_apply (φ : C_c(Ioi (0 : ℝ), ℝ)) (x : Ioi (0 : ℝ)) :
    compactTestZeroExtend φ x = φ x := by
  exact Subtype.val_injective.extend_apply φ 0 x

lemma compactTestZeroExtend_eq_zero_of_nonpos (φ : C_c(Ioi (0 : ℝ), ℝ)) {x : ℝ}
    (hx : x ∉ Ioi (0 : ℝ)) : compactTestZeroExtend φ x = 0 := by
  change Function.extend Subtype.val φ 0 x = 0
  rw [Function.extend_apply' _ _ _]
  · rfl
  · rintro ⟨y, hy⟩
    exact hx (hy ▸ y.2)

lemma compactTestZeroExtend_tsupport_subset (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    tsupport (compactTestZeroExtend φ) ⊆
      (Subtype.val : Ioi (0 : ℝ) → ℝ) '' tsupport (φ : Ioi (0 : ℝ) → ℝ) := by
  exact φ.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val

lemma compactTestZeroExtend_add (φ θ : C_c(Ioi (0 : ℝ), ℝ)) :
    compactTestZeroExtend (φ + θ) = compactTestZeroExtend φ + compactTestZeroExtend θ := by
  funext x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · change compactTestZeroExtend (φ + θ) x =
      compactTestZeroExtend φ x + compactTestZeroExtend θ x
    rw [compactTestZeroExtend_apply (φ + θ) ⟨x, hx⟩,
      compactTestZeroExtend_apply φ ⟨x, hx⟩,
      compactTestZeroExtend_apply θ ⟨x, hx⟩]
    rfl
  · simp [compactTestZeroExtend_eq_zero_of_nonpos φ hx,
      compactTestZeroExtend_eq_zero_of_nonpos θ hx,
      compactTestZeroExtend_eq_zero_of_nonpos (φ + θ) hx]

lemma compactTestZeroExtend_smul (c : ℝ) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    compactTestZeroExtend (c • φ) = c • compactTestZeroExtend φ := by
  funext x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · change compactTestZeroExtend (c • φ) x = c * compactTestZeroExtend φ x
    rw [compactTestZeroExtend_apply (c • φ) ⟨x, hx⟩,
      compactTestZeroExtend_apply φ ⟨x, hx⟩]
    rfl
  · simp [compactTestZeroExtend_eq_zero_of_nonpos φ hx,
      compactTestZeroExtend_eq_zero_of_nonpos (c • φ) hx]

theorem exists_positiveTestFunction_approx_compactTest
    (φ : C_c(Ioi (0 : ℝ), ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : PositiveTestFunction, HasCompactSupport ψ.1 ∧
      tsupport ψ.1 ⊆ tsupport (compactTestZeroExtend φ) ∧
      (∀ x : ℝ, dist (ψ.1 x) (compactTestZeroExtend φ x) < ε) := by
  obtain ⟨g, hgdiff, hgapprox, hgsupp⟩ :=
    (compactTestZeroExtend_continuous φ).exists_contDiff_approx (n := ⊤)
      continuous_const (fun _ => hε)
  have hgc : HasCompactSupport g :=
    (compactTestZeroExtend_hasCompactSupport φ).mono hgsupp
  let gs : 𝓢(ℝ, ℝ) := hgc.toSchwartzMap hgdiff
  have hgt : tsupport gs ⊆ tsupport (compactTestZeroExtend φ) := by
    exact closure_mono hgsupp
  have hpos : tsupport gs ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      (compactTestZeroExtend_tsupport_subset φ) (hgt hx)
    exact y.2
  refine ⟨⟨gs, hpos⟩, hgc, hgt, ?_⟩
  exact hgapprox

lemma CorrectionBumps.correctedFirstVariation_compare_on_compact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {K : Set ℝ} (hK : IsCompact K)
    (hKpos : K ⊆ Ioi 0) {ψ θ : PositiveTestFunction} {ε : ℝ}
    (hε : 0 ≤ ε) (hψ : tsupport ψ.1 ⊆ K) (hθ : tsupport θ.1 ⊆ K)
    (hclose : ∀ x, |ψ.1 x - θ.1 x| ≤ ε) :
    ∃ C ≥ 0, |B.correctedFirstVariation ψ - B.correctedFirstVariation θ| ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ := B.correctedFirstVariation_bound_on_compact hfmin hK hKpos
  refine ⟨C, hC, ?_⟩
  have hs : SchwartzMap.seminorm ℝ 0 0 (ψ.1 - θ.1) ≤ ε := by
    apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ hε
    intro x
    rw [norm_iteratedFDeriv_zero]
    simpa [pow_zero, one_mul, Real.norm_eq_abs, Pi.sub_apply] using hclose x
  have hsupport : tsupport (ψ.1 - θ.1) ⊆ K :=
    (tsupport_sub ψ.1 θ.1).trans (union_subset hψ hθ)
  rw [← B.correctedFirstVariation.map_sub]
  exact (hbound (ψ - θ) hsupport).trans (mul_le_mul_of_nonneg_left hs hC)

def compactTestApprox (φ : C_c(Ioi (0 : ℝ), ℝ)) (n : ℕ) : PositiveTestFunction :=
  Classical.choose (exists_positiveTestFunction_approx_compactTest φ
    (by positivity : 0 < 1 / ((n : ℝ) + 1)))

lemma compactTestApprox_spec (φ : C_c(Ioi (0 : ℝ), ℝ)) (n : ℕ) :
    HasCompactSupport (compactTestApprox φ n).1 ∧
      tsupport (compactTestApprox φ n).1 ⊆ tsupport (compactTestZeroExtend φ) ∧
      ∀ x, dist ((compactTestApprox φ n).1 x) (compactTestZeroExtend φ x) <
        1 / ((n : ℝ) + 1) := by
  exact Classical.choose_spec (exists_positiveTestFunction_approx_compactTest φ
    (by positivity : 0 < 1 / ((n : ℝ) + 1)))

lemma compactTestApprox_support (φ : C_c(Ioi (0 : ℝ), ℝ)) (n : ℕ) :
    tsupport (compactTestApprox φ n).1 ⊆ tsupport (compactTestZeroExtend φ) :=
  (compactTestApprox_spec φ n).2.1

lemma compactTestApprox_uniform_error (φ : C_c(Ioi (0 : ℝ), ℝ)) (n : ℕ) :
    ∀ x, dist ((compactTestApprox φ n).1 x) (compactTestZeroExtend φ x) <
      1 / ((n : ℝ) + 1) :=
  (compactTestApprox_spec φ n).2.2

theorem CorrectionBumps.correctedFirstVariation_compactTestApprox_cauchy
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    CauchySeq (fun n => B.correctedFirstVariation (compactTestApprox φ n)) := by
  let K := tsupport (compactTestZeroExtend φ)
  have hK : IsCompact K := (compactTestZeroExtend_hasCompactSupport φ).isCompact
  have hKpos : K ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset φ hx
    exact y.2
  obtain ⟨C, hC, hboundK⟩ := B.correctedFirstVariation_bound_on_compact hfmin hK hKpos
  apply Metric.cauchySeq_iff'.2
  intro δ hδ
  let η := δ / (2 * (C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < η :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (eventually_lt_nhds hη))
  have hev' := (Filter.eventually_atTop.1 hev)
  obtain ⟨N, hN⟩ := hev'
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : ∀ x, |(compactTestApprox φ n).1 x - (compactTestApprox φ N).1 x| ≤
      1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by
    intro x
    have h1 := compactTestApprox_uniform_error φ n x
    have h2 := compactTestApprox_uniform_error φ N x
    have ht := dist_triangle ((compactTestApprox φ n).1 x)
      (compactTestZeroExtend φ x) ((compactTestApprox φ N).1 x)
    rw [Real.dist_eq] at h1 h2
    have h2' : |compactTestZeroExtend φ x - (compactTestApprox φ N).1 x| <
        1 / ((N : ℝ) + 1) := by simpa [abs_sub_comm] using h2
    have ht' : |(compactTestApprox φ n).1 x - (compactTestApprox φ N).1 x| ≤
        |(compactTestApprox φ n).1 x - compactTestZeroExtend φ x| +
          |compactTestZeroExtend φ x - (compactTestApprox φ N).1 x| := by
      simpa only [Real.dist_eq, abs_sub_comm] using ht
    linarith
  have hseminorm : SchwartzMap.seminorm ℝ 0 0
      ((compactTestApprox φ n).1 - (compactTestApprox φ N).1) ≤
      1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by
    apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (by positivity)
    intro x
    rw [norm_iteratedFDeriv_zero]
    simpa [pow_zero, one_mul, Real.norm_eq_abs, Pi.sub_apply] using hdist x
  have hsupport : tsupport ((compactTestApprox φ n).1 -
      (compactTestApprox φ N).1) ⊆ K := by
    exact (tsupport_sub _ _).trans (union_subset
      (by simpa [K] using compactTestApprox_support φ n)
      (by simpa [K] using compactTestApprox_support φ N))
  have hbound : |B.correctedFirstVariation (compactTestApprox φ n) -
      B.correctedFirstVariation (compactTestApprox φ N)| ≤
      C * (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := by
    rw [← B.correctedFirstVariation.map_sub]
    exact (hboundK _ hsupport).trans (mul_le_mul_of_nonneg_left hseminorm hC)
  have hsum : 1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) < 2 * η := by
    have hn' := hN n hn
    have hN' := hN N le_rfl
    linarith
  calc
    dist (B.correctedFirstVariation (compactTestApprox φ n))
        (B.correctedFirstVariation (compactTestApprox φ N)) =
        |B.correctedFirstVariation (compactTestApprox φ n) -
          B.correctedFirstVariation (compactTestApprox φ N)| := by rw [Real.dist_eq]
    _ ≤ C * (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := hbound
    _ < δ := by
      have hCmul : C * (2 * η) < δ := by
        dsimp [η]
        have hden : 0 < C + 1 := by linarith
        field_simp
        nlinarith [hδ, hC]
      by_cases hC0 : C = 0
      · simp [hC0, hδ]
      · exact (mul_lt_mul_of_pos_left hsum (lt_of_le_of_ne hC (Ne.symm hC0))).trans hCmul

def CorrectionBumps.correctedFirstVariationExtensionValue
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) : ℝ :=
  let _ := hfmin
  Filter.limUnder Filter.atTop
    (fun n => B.correctedFirstVariation (compactTestApprox φ n))

theorem CorrectionBumps.tendsto_correctedFirstVariation_compactTestApprox
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    Filter.Tendsto (fun n => B.correctedFirstVariation (compactTestApprox φ n)) Filter.atTop
      (𝓝 (CorrectionBumps.correctedFirstVariationExtensionValue hfmin B φ)) := by
  exact (B.correctedFirstVariation_compactTestApprox_cauchy hfmin φ).tendsto_limUnder

lemma CorrectionBumps.correctedFirstVariation_compactTestApprox_difference_tendsto_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ))
    (ψ : ℕ → PositiveTestFunction) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hsupport : ∀ n, tsupport (ψ n).1 ⊆ tsupport (compactTestZeroExtend φ))
    (happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend φ x| ≤ ε n)
    (hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => B.correctedFirstVariation (ψ n) -
      B.correctedFirstVariation (compactTestApprox φ n)) Filter.atTop (𝓝 0) := by
  let K := tsupport (compactTestZeroExtend φ)
  have hK : IsCompact K := (compactTestZeroExtend_hasCompactSupport φ).isCompact
  have hKpos : K ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset φ hx
    exact y.2
  obtain ⟨C, hC, hbound⟩ := B.correctedFirstVariation_bound_on_compact hfmin hK hKpos
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum : Filter.Tendsto (fun n => ε n + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    by simpa using hεlim.add hinv
  have hscaled : Filter.Tendsto (fun n => C * (ε n + 1 / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
    simpa [zero_mul] using hsum.const_mul C
  apply (tendsto_zero_iff_norm_tendsto_zero (f := fun n =>
    B.correctedFirstVariation (ψ n) -
      B.correctedFirstVariation (compactTestApprox φ n))).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hscaled
  · filter_upwards [] with n
    exact norm_nonneg _
  · filter_upwards [] with n
    have hdist : ∀ x, |(ψ n).1 x - (compactTestApprox φ n).1 x| ≤
        ε n + 1 / ((n : ℝ) + 1) := by
      intro x
      have h1 := happrox n x
      have h2 := compactTestApprox_uniform_error φ n x
      have ht := dist_triangle ((ψ n).1 x) (compactTestZeroExtend φ x)
        ((compactTestApprox φ n).1 x)
      rw [Real.dist_eq] at h2
      have h2' : |compactTestZeroExtend φ x - (compactTestApprox φ n).1 x| <
          1 / ((n : ℝ) + 1) := by simpa [abs_sub_comm] using h2
      have ht' : |(ψ n).1 x - (compactTestApprox φ n).1 x| ≤
          |(ψ n).1 x - compactTestZeroExtend φ x| +
            |compactTestZeroExtend φ x - (compactTestApprox φ n).1 x| := by
        simpa only [Real.dist_eq, abs_sub_comm] using ht
      linarith [h1, h2']
    have hs : SchwartzMap.seminorm ℝ 0 0 ((ψ n).1 -
        (compactTestApprox φ n).1) ≤ ε n + 1 / ((n : ℝ) + 1) := by
      apply SchwartzMap.seminorm_le_bound ℝ 0 0 _
        (add_nonneg (hε n) (by positivity))
      intro x
      rw [norm_iteratedFDeriv_zero]
      simpa [pow_zero, one_mul, Real.norm_eq_abs, Pi.sub_apply] using hdist x
    have hsup : tsupport ((ψ n).1 - (compactTestApprox φ n).1) ⊆ K :=
      (tsupport_sub _ _).trans (union_subset (hsupport n)
        (by simpa [K] using compactTestApprox_support φ n))
    rw [← B.correctedFirstVariation.map_sub]
    have hb := hbound (ψ n - compactTestApprox φ n) hsup
    rw [show (ψ n - compactTestApprox φ n).1 = (ψ n).1 -
        (compactTestApprox φ n).1 by rfl] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hs hC)

theorem CorrectionBumps.correctedFirstVariation_compactTestApprox_unique_limit
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ))
    (ψ : ℕ → PositiveTestFunction) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hsupport : ∀ n, tsupport (ψ n).1 ⊆ tsupport (compactTestZeroExtend φ))
    (happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend φ x| ≤ ε n)
    (hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => B.correctedFirstVariation (ψ n)) Filter.atTop
      (𝓝 (CorrectionBumps.correctedFirstVariationExtensionValue hfmin B φ)) := by
  have hd := B.correctedFirstVariation_compactTestApprox_difference_tendsto_zero
    hfmin φ ψ ε hε hsupport happrox hεlim
  have hc := B.tendsto_correctedFirstVariation_compactTestApprox hfmin φ
  convert hd.add hc using 1 <;> simp [sub_add_cancel]

theorem CorrectionBumps.correctedFirstVariation_compactTestApprox_unique_limit_on_compact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi 0, ℝ)) {K : Set ℝ}
    (hK : IsCompact K) (hKpos : K ⊆ Ioi 0)
    (htarget : tsupport (compactTestZeroExtend φ) ⊆ K)
    (ψ : ℕ → PositiveTestFunction) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hsupport : ∀ n, tsupport (ψ n).1 ⊆ K)
    (happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend φ x| ≤ ε n)
    (hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => B.correctedFirstVariation (ψ n)) Filter.atTop
      (𝓝 (CorrectionBumps.correctedFirstVariationExtensionValue hfmin B φ)) := by
  obtain ⟨C, hC, hbound⟩ := B.correctedFirstVariation_bound_on_compact hfmin hK hKpos
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum : Filter.Tendsto (fun n => ε n + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    by simpa using hεlim.add hinv
  have hscaled : Filter.Tendsto (fun n => C * (ε n + 1 / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by simpa [zero_mul] using hsum.const_mul C
  have hd : Filter.Tendsto (fun n => B.correctedFirstVariation (ψ n) -
      B.correctedFirstVariation (compactTestApprox φ n)) Filter.atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) hscaled
    · filter_upwards [] with n; exact norm_nonneg _
    · filter_upwards [] with n
      have hdist : ∀ x, |(ψ n).1 x - (compactTestApprox φ n).1 x| ≤
          ε n + 1 / ((n : ℝ) + 1) := by
        intro x
        have h1 := happrox n x
        have h2 := compactTestApprox_uniform_error φ n x
        rw [Real.dist_eq] at h2
        have h2' : |compactTestZeroExtend φ x - (compactTestApprox φ n).1 x| <
            1 / ((n : ℝ) + 1) := by simpa [abs_sub_comm] using h2
        have ht := dist_triangle ((ψ n).1 x) (compactTestZeroExtend φ x)
          ((compactTestApprox φ n).1 x)
        have ht' : |(ψ n).1 x - (compactTestApprox φ n).1 x| ≤
            |(ψ n).1 x - compactTestZeroExtend φ x| +
              |compactTestZeroExtend φ x - (compactTestApprox φ n).1 x| := by
          simpa only [Real.dist_eq, abs_sub_comm] using ht
        linarith
      have hs : SchwartzMap.seminorm ℝ 0 0 ((ψ n).1 -
          (compactTestApprox φ n).1) ≤ ε n + 1 / ((n : ℝ) + 1) := by
        apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (add_nonneg (hε n) (by positivity))
        intro x
        rw [norm_iteratedFDeriv_zero]
        simpa [pow_zero, one_mul, Real.norm_eq_abs, Pi.sub_apply] using hdist x
      have hsup : tsupport ((ψ n).1 - (compactTestApprox φ n).1) ⊆ K :=
        (tsupport_sub _ _).trans (union_subset (hsupport n)
          (compactTestApprox_support φ n |>.trans htarget))
      rw [← B.correctedFirstVariation.map_sub]
      have hb := hbound (ψ n - compactTestApprox φ n) hsup
      rw [show (ψ n - compactTestApprox φ n).1 = (ψ n).1 -
        (compactTestApprox φ n).1 by rfl] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hs hC)
  convert hd.add (B.tendsto_correctedFirstVariation_compactTestApprox hfmin φ) using 1 <;>
    simp [sub_add_cancel]

theorem CorrectionBumps.correctedFirstVariationExtensionValue_nonneg
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {φ : C_c(Ioi (0 : ℝ), ℝ)} (hφ : 0 ≤ φ) :
    0 ≤ B.correctedFirstVariationExtensionValue hfmin φ := by
  let K₀ := tsupport (compactTestZeroExtend φ)
  have hK₀ : IsCompact K₀ := (compactTestZeroExtend_hasCompactSupport φ).isCompact
  have hK₀pos : K₀ ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset φ hx
    exact y.2
  obtain ⟨χ, hχcompact, hχnonneg, hχle, hχone⟩ :=
    exists_nonnegative_compact_cutoff hK₀ hK₀pos
  let K := K₀ ∪ tsupport χ.1
  have hK : IsCompact K := hK₀.union hχcompact.isCompact
  have hKpos : K ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · exact hK₀pos hx
    · exact χ.2 hx
  let ψ : ℕ → PositiveTestFunction := fun n =>
    compactTestApprox φ n + (1 / ((n : ℝ) + 1)) • χ
  have htarget : ∀ x, 0 ≤ compactTestZeroExtend φ x := by
    intro x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [compactTestZeroExtend_apply φ ⟨x, hx⟩]
      exact hφ ⟨x, hx⟩
    · rw [compactTestZeroExtend_eq_zero_of_nonpos φ hx]
  have hsupp : ∀ n, tsupport (ψ n).1 ⊆ K := by
    intro n
    exact (tsupport_add _ _).trans (union_subset
      ((compactTestApprox_support φ n).trans subset_union_left)
      (tsupport_smul_subset_right (fun _ : ℝ => (1 / ((n : ℝ) + 1))) χ.1 |>.trans
        subset_union_right))
  have htargetK : tsupport (compactTestZeroExtend φ) ⊆ K := subset_union_left
  have hnonneg : ∀ n x, 0 ≤ (ψ n).1 x := by
    intro n x
    by_cases hx : x ∈ K₀
    · have he := compactTestApprox_uniform_error φ n x
      rw [Real.dist_eq] at he
      change 0 ≤ (compactTestApprox φ n).1 x +
        (1 / ((n : ℝ) + 1)) * χ.1 x
      rw [hχone x hx]
      have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith [neg_le_of_abs_le (le_of_lt he), htarget x]
    · have ha : (compactTestApprox φ n).1 x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (show x ∈ K₀ from
          compactTestApprox_support φ n h))
      have ht : compactTestZeroExtend φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx h)
      simp [ha, ψ]
      exact mul_nonneg (by positivity) (hχnonneg x)
  have happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend φ x| ≤
      2 / ((n : ℝ) + 1) := by
    intro n x
    have he := compactTestApprox_uniform_error φ n x
    rw [Real.dist_eq] at he
    by_cases hx : x ∈ K
    · have hχ' : χ.1 x ≤ 1 := hχle x
      rw [show (ψ n).1 x = (compactTestApprox φ n).1 x +
        (1 / ((n : ℝ) + 1)) * χ.1 x by rfl]
      have hrewrite :
          (compactTestApprox φ n).1 x + 1 / ((n : ℝ) + 1) * χ.1 x -
            compactTestZeroExtend φ x =
          ((compactTestApprox φ n).1 x - compactTestZeroExtend φ x) +
            1 / ((n : ℝ) + 1) * χ.1 x := by ring
      have habs := abs_add_le
        ((compactTestApprox φ n).1 x - compactTestZeroExtend φ x)
        (1 / ((n : ℝ) + 1) * χ.1 x)
      have hnon : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      calc
        |(ψ n).1 x - compactTestZeroExtend φ x| ≤
            |(compactTestApprox φ n).1 x - compactTestZeroExtend φ x| +
              |1 / ((n : ℝ) + 1) * χ.1 x| := by
                change |(compactTestApprox φ n).1 x +
                  1 / ((n : ℝ) + 1) * χ.1 x - compactTestZeroExtend φ x| ≤ _
                rw [hrewrite]
                exact habs
        _ ≤
            1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
              rw [abs_mul, abs_of_nonneg hnon]
              exact add_le_add (le_of_lt he)
                (by rw [abs_of_nonneg (hχnonneg x)]
                    exact mul_le_of_le_one_right hnon (hχle x))
        _ = 2 / ((n : ℝ) + 1) := by ring
    · have hn := hnonneg n x
      have hz : (ψ n).1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp n h))
      rw [hz]
      have ht : compactTestZeroExtend φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (htargetK h))
      simpa [ht] using (show 0 ≤ 2 / ((n : ℝ) + 1) by positivity)
  have hlim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hseq := B.correctedFirstVariation_compactTestApprox_unique_limit_on_compact
    hfmin φ hK hKpos htargetK ψ (fun n : ℕ => 2 / ((n : ℝ) + 1))
      (by intro n; positivity) hsupp happrox hlim
  apply ge_of_tendsto hseq
  filter_upwards [] with n
  exact B.correctedFirstVariation_nonneg hfmin (hnonneg n)

theorem CorrectionBumps.correctedFirstVariationExtensionValue_add
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ θ : C_c(Ioi (0 : ℝ), ℝ)) :
    B.correctedFirstVariationExtensionValue hfmin (φ + θ) =
      B.correctedFirstVariationExtensionValue hfmin φ +
        B.correctedFirstVariationExtensionValue hfmin θ := by
  let K := tsupport (compactTestZeroExtend φ) ∪ tsupport (compactTestZeroExtend θ)
  have hK : IsCompact K := (compactTestZeroExtend_hasCompactSupport φ).isCompact.union
    (compactTestZeroExtend_hasCompactSupport θ).isCompact
  have hKpos : K ⊆ Ioi 0 := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset φ hx
      exact y.2
    · obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset θ hx
      exact y.2
  let ψ : ℕ → PositiveTestFunction := fun n => compactTestApprox φ n + compactTestApprox θ n
  have hsupp : ∀ n, tsupport (ψ n).1 ⊆ K := by
    intro n
    exact (tsupport_add _ _).trans (union_subset
      (compactTestApprox_support φ n |>.trans subset_union_left)
      (compactTestApprox_support θ n |>.trans subset_union_right))
  have htarget : tsupport (compactTestZeroExtend (φ + θ)) ⊆ K := by
    rw [compactTestZeroExtend_add]
    exact (tsupport_add _ _).trans (union_subset subset_union_left subset_union_right)
  have happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend (φ + θ) x| ≤
      2 / ((n : ℝ) + 1) := by
    intro n x
    rw [show (ψ n).1 x = (compactTestApprox φ n).1 x +
      (compactTestApprox θ n).1 x by rfl, compactTestZeroExtend_add, Pi.add_apply]
    have hφ := compactTestApprox_uniform_error φ n x
    have hθ := compactTestApprox_uniform_error θ n x
    rw [Real.dist_eq] at hφ hθ
    have heq :
        (compactTestApprox φ n).1 x + (compactTestApprox θ n).1 x -
          (compactTestZeroExtend φ x + compactTestZeroExtend θ x) =
        ((compactTestApprox φ n).1 x - compactTestZeroExtend φ x) +
          ((compactTestApprox θ n).1 x - compactTestZeroExtend θ x) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      have := add_lt_add hφ hθ
      convert le_of_lt this using 1
      all_goals field_simp
      all_goals ring)
  have hlim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hseq := B.correctedFirstVariation_compactTestApprox_unique_limit_on_compact
    hfmin (φ + θ) hK hKpos htarget ψ (fun n => (2 : ℝ) / ((n : ℝ) + 1))
      (by intro n; positivity) hsupp happrox hlim
  apply tendsto_nhds_unique hseq
  have hadd : (fun n => B.correctedFirstVariation (ψ n)) =
      (fun n => B.correctedFirstVariation (compactTestApprox φ n) +
        B.correctedFirstVariation (compactTestApprox θ n)) := by
    funext n
    simp [ψ, map_add]
  rw [hadd]
  exact (B.tendsto_correctedFirstVariation_compactTestApprox hfmin φ).add
     (B.tendsto_correctedFirstVariation_compactTestApprox hfmin θ)

theorem CorrectionBumps.correctedFirstVariationExtensionValue_smul
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (c : ℝ) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    CorrectionBumps.correctedFirstVariationExtensionValue hfmin B (c • φ) =
      c * CorrectionBumps.correctedFirstVariationExtensionValue hfmin B φ := by
  let K := tsupport (compactTestZeroExtend φ)
  have hK : IsCompact K := (compactTestZeroExtend_hasCompactSupport φ).isCompact
  have hKpos : K ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := compactTestZeroExtend_tsupport_subset φ hx
    exact y.2
  have htarget : tsupport (compactTestZeroExtend (c • φ)) ⊆ K := by
    rw [compactTestZeroExtend_smul]
    exact tsupport_smul_subset_right (fun _ : ℝ => c) (compactTestZeroExtend φ) |>.trans (by
      exact subset_rfl)
  let ψ : ℕ → PositiveTestFunction := fun n => c • compactTestApprox φ n
  have hsupp : ∀ n, tsupport (ψ n).1 ⊆ K := by
    intro n
    exact tsupport_smul_subset_right (fun _ : ℝ => c) _ |>.trans (compactTestApprox_support φ n)
  have happrox : ∀ n x, |(ψ n).1 x - compactTestZeroExtend (c • φ) x| ≤
      |c| / ((n : ℝ) + 1) := by
    intro n x
    rw [show (ψ n).1 x = c * (compactTestApprox φ n).1 x by rfl,
      compactTestZeroExtend_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show c * (compactTestApprox φ n).1 x - c * compactTestZeroExtend φ x =
      c * ((compactTestApprox φ n).1 x - compactTestZeroExtend φ x) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (le_of_lt (by simpa [Real.dist_eq] using compactTestApprox_uniform_error φ n x))
      (abs_nonneg c)
  have hlim : Filter.Tendsto (fun n : ℕ => |c| / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |c|
  have hseq := B.correctedFirstVariation_compactTestApprox_unique_limit_on_compact
    hfmin (c • φ) hK hKpos htarget ψ (fun n : ℕ => |c| / ((n : ℝ) + 1))
      (by intro n; positivity) hsupp happrox hlim
  apply tendsto_nhds_unique hseq
  have hadd : (fun n => B.correctedFirstVariation (ψ n)) =
      (fun n => c * B.correctedFirstVariation (compactTestApprox φ n)) := by
    funext n
    simp [ψ, map_smul, smul_eq_mul]
  rw [hadd]
  exact (B.tendsto_correctedFirstVariation_compactTestApprox hfmin φ).const_mul c

def CorrectionBumps.correctedFirstVariationExtensionLinear
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : C_c(Ioi (0 : ℝ), ℝ) →ₗ[ℝ] ℝ where
  toFun := CorrectionBumps.correctedFirstVariationExtensionValue hfmin B
  map_add' φ θ := B.correctedFirstVariationExtensionValue_add hfmin φ θ
  map_smul' c φ := B.correctedFirstVariationExtensionValue_smul hfmin c φ

@[simp] theorem CorrectionBumps.correctedFirstVariationExtensionLinear_apply
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    B.correctedFirstVariationExtensionLinear hfmin φ =
       B.correctedFirstVariationExtensionValue hfmin φ := rfl

def CorrectionBumps.correctedFirstVariationExtension
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : C_c(Ioi (0 : ℝ), ℝ) →ₚ[ℝ] ℝ :=
  { toLinearMap := B.correctedFirstVariationExtensionLinear hfmin
    monotone' := fun φ θ hφθ => by
      have h := B.correctedFirstVariationExtensionValue_nonneg hfmin (sub_nonneg.mpr hφθ)
      change 0 ≤ B.correctedFirstVariationExtensionLinear hfmin (θ - φ) at h
      rw [(B.correctedFirstVariationExtensionLinear hfmin).map_sub] at h
      exact sub_nonneg.mp h }

@[simp] theorem CorrectionBumps.correctedFirstVariationExtension_apply
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    B.correctedFirstVariationExtension hfmin φ =
      B.correctedFirstVariationExtensionValue hfmin φ := rfl

def PositiveTestFunction.toCompactTest (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) : C_c(Ioi (0 : ℝ), ℝ) :=
  let K : Set ℝ := tsupport ψ.1
  let K' : Set (Ioi (0 : ℝ)) :=
    (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' K
  have hK : IsCompact K := hcompact.isCompact
  have hKrange : K ⊆ Set.range (Subtype.val : Ioi (0 : ℝ) → ℝ) := by
    intro x hx
    exact ⟨⟨x, ψ.2 hx⟩, rfl⟩
  have hK' : IsCompact K' := by
    exact Topology.IsEmbedding.subtypeVal.isCompact_preimage' hK hKrange
  ⟨ψ.1.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩, by
    apply HasCompactSupport.of_support_subset_isCompact hK'
    intro x hx
    change ψ.1 x ≠ 0 at hx
    exact subset_tsupport ψ.1 hx⟩

lemma PositiveTestFunction.toCompactTest_apply (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) (x : Ioi (0 : ℝ)) :
    PositiveTestFunction.toCompactTest ψ hcompact x = ψ.1 x := by
  rfl

lemma compactTestZeroExtend_toCompactTest (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) :
    compactTestZeroExtend (PositiveTestFunction.toCompactTest ψ hcompact) = ψ.1 := by
  funext x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [compactTestZeroExtend_apply _ ⟨x, hx⟩]
    exact PositiveTestFunction.toCompactTest_apply ψ hcompact ⟨x, hx⟩
  · rw [compactTestZeroExtend_eq_zero_of_nonpos _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.2 h))).symm

theorem CorrectionBumps.correctedFirstVariationExtensionValue_toCompactTest
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) :
    B.correctedFirstVariationExtensionValue hfmin
        (PositiveTestFunction.toCompactTest ψ hcompact) =
      B.correctedFirstVariation ψ := by
  let K : Set ℝ := tsupport ψ.1
  have hK : IsCompact K := hcompact.isCompact
  have hKpos : K ⊆ Ioi (0 : ℝ) := ψ.2
  have htarget : tsupport (compactTestZeroExtend
      (PositiveTestFunction.toCompactTest ψ hcompact)) ⊆ K := by
    rw [compactTestZeroExtend_toCompactTest ψ hcompact]
  let ψseq : ℕ → PositiveTestFunction := fun _ => ψ
  have hsupp : ∀ n, tsupport (ψseq n).1 ⊆ K := by
    intro n
    exact subset_rfl
  have happrox : ∀ n x, |(ψseq n).1 x - compactTestZeroExtend
      (PositiveTestFunction.toCompactTest ψ hcompact) x| ≤ (0 : ℝ) := by
    intro n x
    rw [compactTestZeroExtend_toCompactTest ψ hcompact]
    simp [ψseq]
  have hεlim : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds
  have hseq := B.correctedFirstVariation_compactTestApprox_unique_limit_on_compact
    hfmin (PositiveTestFunction.toCompactTest ψ hcompact) hK hKpos htarget ψseq
      (fun _ => (0 : ℝ))
      (fun _ => le_rfl) hsupp happrox hεlim
  apply tendsto_nhds_unique hseq
  have hconst : Filter.Tendsto (fun _ : ℕ => B.correctedFirstVariation ψ)
      Filter.atTop (𝓝 (B.correctedFirstVariation ψ)) := tendsto_const_nhds
  simpa only [ψseq] using hconst

theorem CorrectionBumps.correctedFirstVariationExtension_toCompactTest
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) :
    B.correctedFirstVariationExtension hfmin
        (PositiveTestFunction.toCompactTest ψ hcompact) =
      B.correctedFirstVariation ψ := by
  rw [CorrectionBumps.correctedFirstVariationExtension_apply]
  exact B.correctedFirstVariationExtensionValue_toCompactTest hfmin ψ hcompact

def CorrectionBumps.reactionMeasure
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : Measure (Ioi (0 : ℝ)) :=
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) :=
    IsOpen.locallyCompactSpace isOpen_Ioi
  RealRMK.rieszMeasure (B.correctedFirstVariationExtension hfmin)

theorem CorrectionBumps.integral_reactionMeasure
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : C_c(Ioi (0 : ℝ), ℝ)) :
    ∫ x, φ x ∂B.reactionMeasure hfmin =
      B.correctedFirstVariationExtension hfmin φ := by
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) :=
    IsOpen.locallyCompactSpace isOpen_Ioi
  exact RealRMK.integral_rieszMeasure
    (B.correctedFirstVariationExtension hfmin) φ

theorem CorrectionBumps.integral_reactionMeasure_smooth
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) :
    ∫ x, ψ.1 x ∂B.reactionMeasure hfmin = B.correctedFirstVariation ψ := by
  simpa only [PositiveTestFunction.toCompactTest_apply] using
    B.integral_reactionMeasure hfmin (PositiveTestFunction.toCompactTest ψ hcompact)
      |>.trans (B.correctedFirstVariationExtension_toCompactTest hfmin ψ hcompact)

theorem CorrectionBumps.reactionMeasure_regular
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    (B.reactionMeasure hfmin).Regular := by
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) :=
    IsOpen.locallyCompactSpace isOpen_Ioi
  change (RealRMK.rieszMeasure (B.correctedFirstVariationExtension hfmin)).Regular
  exact RealRMK.regular_rieszMeasure (B.correctedFirstVariationExtension hfmin)

theorem CorrectionBumps.reactionMeasure_isFiniteMeasureOnCompacts
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    IsFiniteMeasureOnCompacts (B.reactionMeasure hfmin) := by
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) :=
    IsOpen.locallyCompactSpace isOpen_Ioi
  change IsFiniteMeasureOnCompacts
    (RealRMK.rieszMeasure (B.correctedFirstVariationExtension hfmin))
  exact (RealRMK.regular_rieszMeasure
    (B.correctedFirstVariationExtension hfmin)).toIsFiniteMeasureOnCompacts
