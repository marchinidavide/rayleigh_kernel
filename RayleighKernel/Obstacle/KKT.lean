import RayleighKernel.Obstacle.PositiveDistribution
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
namespace RayleighKernel
namespace Analysis

open MeasureTheory Set
open scoped SchwartzMap Topology CompactlySupported

namespace HalfLineH1

def CorrectionBumps.massMultiplier {f : HalfLineH1} (B : f.CorrectionBumps) : ℝ :=
  -f.firstVariation (PositiveTestFunction.toHalfLineH1 (B.rightInverse (1, 0)))

def CorrectionBumps.momentMultiplier {f : HalfLineH1} (B : f.CorrectionBumps) : ℝ :=
  -f.firstVariation (PositiveTestFunction.toHalfLineH1 (B.rightInverse (0, 1)))

lemma CorrectionBumps.firstVariation_rightInverse_decomposition
    {f : HalfLineH1} (B : f.CorrectionBumps) (z : ℝ × ℝ) :
    f.firstVariation (PositiveTestFunction.toHalfLineH1 (B.rightInverse z)) =
      z.1 * f.firstVariation
          (PositiveTestFunction.toHalfLineH1 (B.rightInverse (1, 0))) +
      z.2 * f.firstVariation
          (PositiveTestFunction.toHalfLineH1 (B.rightInverse (0, 1))) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by
    ext <;> simp
  rw [hz, B.rightInverse.map_add, B.rightInverse.map_smul, B.rightInverse.map_smul,
    PositiveTestFunction.toHalfLineH1_add, PositiveTestFunction.toHalfLineH1_smul,
    PositiveTestFunction.toHalfLineH1_smul, f.firstVariation_add,
    f.firstVariation_smul, f.firstVariation_smul]
  simp only [Prod.smul_mk, smul_eq_mul]
  norm_num

theorem CorrectionBumps.correctedFirstVariation_multiplier_decomposition
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    B.correctedFirstVariation ψ = f.firstVariation (PositiveTestFunction.toHalfLineH1 ψ) +
      B.massMultiplier * PositiveTestFunction.testMass ψ +
      B.momentMultiplier * PositiveTestFunction.testFirstMoment ψ := by
  rw [B.correctedFirstVariation_decomposition]
  rw [PositiveTestFunction.massMoment_apply]
  have h := B.firstVariation_rightInverse_decomposition
    (PositiveTestFunction.massMoment ψ)
  have h' : f.firstVariation
      (PositiveTestFunction.toHalfLineH1
        (B.rightInverse (PositiveTestFunction.testMass ψ,
          PositiveTestFunction.testFirstMoment ψ))) =
      PositiveTestFunction.testMass ψ * f.firstVariation
          (PositiveTestFunction.toHalfLineH1 (B.rightInverse (1, 0))) +
      PositiveTestFunction.testFirstMoment ψ * f.firstVariation
          (PositiveTestFunction.toHalfLineH1 (B.rightInverse (0, 1))) := by
    simpa [PositiveTestFunction.massMoment_apply] using h
  rw [h']
  dsimp [CorrectionBumps.massMultiplier, CorrectionBumps.momentMultiplier]
  ring

theorem CorrectionBumps.weak_KKT_equation
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hcompact : HasCompactSupport ψ.1) :
    ∫ x : Ioi (0 : ℝ), ψ.1 x ∂B.reactionMeasure hfmin =
      inner ℝ f.weakDeriv (PositiveTestFunction.toHalfLineH1 ψ).weakDeriv -
        f.rayleighQuotient * inner ℝ f.value (PositiveTestFunction.toHalfLineH1 ψ).value +
      B.massMultiplier * PositiveTestFunction.testMass ψ +
      B.momentMultiplier * PositiveTestFunction.testFirstMoment ψ := by
  rw [B.integral_reactionMeasure_smooth hfmin ψ hcompact,
    B.correctedFirstVariation_multiplier_decomposition]
  rfl

lemma CorrectionBumps.interiorVariationSupport
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (_hψcompact : HasCompactSupport ψ.1)
    (_hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    IsCompact (tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1)) := by
  exact _hψcompact.isCompact.union B.compact_support_union

lemma CorrectionBumps.interiorVariationSupport_subset_positivity
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (_hψcompact : HasCompactSupport ψ.1)
    (_hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    (tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1)) ⊆
      f.positivitySet := by
  intro x hx
  rcases hx with hx | hx
  · exact _hψsupport hx
  · exact B.support_union_subset_positivity hx

lemma CorrectionBumps.exists_interiorVariation_pos_lower_bound
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (_hψcompact : HasCompactSupport ψ.1)
    (_hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    ∃ δ > 0, ∀ x ∈ tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1),
      δ ≤ f.continuousRep x := by
  let K : Set ℝ := tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1)
  have hK : IsCompact K := B.interiorVariationSupport ψ _hψcompact _hψsupport
  have hKpos : K ⊆ f.positivitySet :=
    B.interiorVariationSupport_subset_positivity ψ _hψcompact _hψsupport
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne
      f.continuous_continuousRep.continuousOn
    have hpos : 0 < f.continuousRep x := hKpos hxK
    refine ⟨f.continuousRep x, hpos, ?_⟩
    intro y hy
    exact hx hy
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

lemma CorrectionBumps.exists_interiorVariation_bound
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction) :
    ∃ C ≥ 0, ∀ x, |(B.correctedVariation ψ).continuousRep x| ≤ C := by
  obtain ⟨C, hC, hCr⟩ := B.exists_correction_bound ψ
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 ψ.1
  refine ⟨M + C, by dsimp [M]; positivity, ?_⟩
  intro x
  rw [B.correctedVariation_continuousRep]
  have hψ : |ψ.1 x| ≤ M := by
    exact SchwartzMap.norm_le_seminorm ℝ ψ.1 x
  have hc := hCr x
  have hsum : |ψ.1 x - (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x| ≤
      |ψ.1 x| + |(B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x| := by
    simpa [sub_eq_add_neg] using
      (abs_add_le (ψ.1 x) (-(B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x))
  linarith

lemma CorrectionBumps.interiorVariation_eq_zero_off_support
    {f : HalfLineH1} (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (_hψcompact : HasCompactSupport ψ.1)
    (_hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    ∀ x, x ∉ tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1) →
      (B.correctedVariation ψ).continuousRep x = 0 := by
  intro x hx
  rw [B.correctedVariation_continuousRep]
  have hψ : ψ.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
  have hl : B.bumpLeft.1 x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr (Or.inl h)))
  have hr : B.bumpRight.1 x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr (Or.inr h)))
  have hc : (B.rightInverse (PositiveTestFunction.massMoment ψ)).1 x = 0 := by
    change B.leftCoefficient _ * B.bumpLeft.1 x + B.rightCoefficient _ * B.bumpRight.1 x = 0
    simp [hl, hr]
  have hmass : PositiveTestFunction.massMoment ψ =
      (PositiveTestFunction.testMass ψ, PositiveTestFunction.testFirstMoment ψ) := rfl
  rw [hmass] at hc
  simp [hψ, hc]

lemma CorrectionBumps.interiorVariation_nonnegative_of_small
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    ∃ ε0 > 0, ∀ s : ℝ, |s| ≤ ε0 →
      ∀ x ∈ halfLine, 0 ≤ (f + s • B.correctedVariation ψ).continuousRep x := by
  obtain ⟨δ, hδ, hδK⟩ :=
    B.exists_interiorVariation_pos_lower_bound ψ hψcompact hψsupport
  obtain ⟨C, hC, hbound⟩ := B.exists_interiorVariation_bound ψ
  let ε0 : ℝ := δ / (C + 1)
  have hε0 : 0 < ε0 := div_pos hδ (by linarith)
  refine ⟨ε0, hε0, ?_⟩
  intro s hs x hx
  rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  let K : Set ℝ := tsupport ψ.1 ∪ (tsupport B.bumpLeft.1 ∪ tsupport B.bumpRight.1)
  by_cases hxK : x ∈ K
  · have hfx : δ ≤ f.continuousRep x := hδK x hxK
    have hh := hbound x
    have hmul : |s| * C ≤ δ := by
      have hden : 0 < C + 1 := by linarith
      have hcross : |s| * (C + 1) ≤ δ :=
        (le_div_iff₀ hden).mp (by simpa [ε0] using hs)
      nlinarith
    have habs : |s * (B.correctedVariation ψ).continuousRep x| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hh (abs_nonneg s)).trans hmul
    linarith [neg_le_of_abs_le habs]
  · have hz := B.interiorVariation_eq_zero_off_support ψ hψcompact hψsupport x hxK
    rw [hz, mul_zero, add_zero]
    exact hf.nonnegative x hx

theorem CorrectionBumps.exists_isAdmissible_correctedVariation_of_small
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    ∃ ε0 > 0, ∀ s : ℝ, |s| ≤ ε0 →
      (f + s • B.correctedVariation ψ).IsAdmissible L := by
  obtain ⟨ε0, hε0, hnonneg⟩ :=
    B.interiorVariation_nonnegative_of_small hf ψ hψcompact hψsupport
  refine ⟨ε0, hε0, ?_⟩
  intro s hs
  let h := B.correctedVariation ψ
  have hi : IntegrableOn (f + s • h).continuousRep halfLine := by
    rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
    exact hf.integrable.add ((B.correctedVariation_integrable ψ).smul s)
  have hi1 : IntegrableOn (fun x => x * (f + s • h).continuousRep x) halfLine := by
    rw [HalfLineH1.continuousRep_add, HalfLineH1.continuousRep_smul]
    have hs1 : IntegrableOn (fun x => x * (s * h.continuousRep x)) halfLine := by
      change Integrable (fun x => x * (s * h.continuousRep x))
        (Measure.restrict volume halfLine)
      simpa [h, mul_comm, mul_left_comm, mul_assoc] using
        (B.correctedVariation_firstMoment_integrable ψ).const_mul s
    rw [show (fun x => x * (f.continuousRep + s • h.continuousRep) x) =
      (fun x => x * f.continuousRep x + x * (s * h.continuousRep x)) by
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring]
    exact hf.firstMoment_integrable.add hs1
  refine ⟨hnonneg s hs, hi, hi1, ?_, ?_⟩
  · have hsi : IntegrableOn (s • h).continuousRep halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      exact (B.correctedVariation_integrable ψ).const_mul s
    calc
      (f + s • h).mass = f.mass + (s • h).mass :=
        mass_add_continuousRep hf.integrable hsi
      _ = f.mass + s * h.mass := by rw [mass_smul_continuousRep]
      _ = 1 := by rw [hf.mass_eq, B.correctedVariation_mass]; simp
  · have hsi1 : IntegrableOn (fun x => x * (s • h).continuousRep x) halfLine := by
      rw [HalfLineH1.continuousRep_smul]
      change Integrable (fun x => x * (s * h.continuousRep x))
        (Measure.restrict volume halfLine)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (B.correctedVariation_firstMoment_integrable ψ).const_mul s
    calc
      (f + s • h).firstMoment = f.firstMoment + (s • h).firstMoment :=
        firstMoment_add_continuousRep hf.firstMoment_integrable hsi1
      _ = f.firstMoment + s * h.firstMoment := by rw [firstMoment_smul_continuousRep]
      _ = L := by rw [hf.firstMoment_eq, B.correctedVariation_firstMoment]; simp

theorem CorrectionBumps.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (ψ : PositiveTestFunction)
    (hψcompact : HasCompactSupport ψ.1)
    (hψsupport : tsupport ψ.1 ⊆ f.positivitySet) :
    B.correctedFirstVariation ψ = 0 := by
  obtain ⟨ε0, hε0, hfeas⟩ :=
    B.exists_isAdmissible_correctedVariation_of_small hfmin.1 ψ hψcompact hψsupport
  let h := B.correctedVariation ψ
  have hden : 0 < f.squareEnergy := f.squareEnergy_pos_of_mass_eq_one hfmin.1.mass_eq
  have hplus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ => (f + s • h).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hq := hfmin.2 (f + t • h)
      (hfeas t (by simpa [abs_of_pos ht.1] using ht.2.le))
    have hsub : 0 ≤ (f + t • h).rayleighQuotient - f.rayleighQuotient :=
      sub_nonneg.mpr hq
    simpa using (div_nonneg hsub (le_of_lt ht.1))
  have hminus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ => (f + s • (-h)).rayleighQuotient) 0 t := by
    filter_upwards [Ioo_mem_nhdsGT hε0] with t ht
    rw [slope_def_field]
    have hst : |(-t : ℝ)| ≤ ε0 := by
      rw [abs_neg, abs_of_pos ht.1]
      exact ht.2.le
    have hq := hfmin.2 (f + (-t) • h) (hfeas (-t) hst)
    have hq' : (f + t • (-h)).rayleighQuotient = (f + (-t) • h).rayleighQuotient := by
      rw [show -h = (-1 : ℝ) • h by simp]
      simp
    rw [hq']
    have hsub : 0 ≤ (f + (-t) • h).rayleighQuotient - f.rayleighQuotient :=
      sub_nonneg.mpr hq
    simpa using (div_nonneg hsub (le_of_lt ht.1))
  rw [CorrectionBumps.correctedFirstVariation_apply]
  exact HalfLineH1.firstVariation_eq_zero_of_eventually_slope_nonneg f h hden hplus hminus

theorem exists_nonnegative_compact_cutoff_in_positivitySet
    {f : HalfLineH1} {K : Set ℝ} (hK : IsCompact K)
    (hKpos : K ⊆ f.positivitySet) :
    ∃ χ : PositiveTestFunction, HasCompactSupport χ.1 ∧
      (∀ x, 0 ≤ χ.1 x) ∧ (∀ x, χ.1 x ≤ 1) ∧
      tsupport χ.1 ⊆ f.positivitySet ∧ (∀ x ∈ K, χ.1 x = 1) := by
  have hpos : f.positivitySet ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_not_ge fun hx0 ↦ hx.ne'
      (f.continuousRep_eq_zero_of_nonpositive hx0)
  obtain ⟨V, hVopen, hKV, hVcl, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK f.isOpen_positivitySet hKpos
  obtain ⟨g, hgdiff, hgrange, hgsupp, hgone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVopen hK.isClosed hKV
  let χs : 𝓢(ℝ, ℝ) := (show HasCompactSupport g from by
    rw [hasCompactSupport_def, hgsupp]
    exact hVcompact).toSchwartzMap hgdiff
  have hχsupp : tsupport χs ⊆ f.positivitySet := by
    rw [show tsupport χs = closure (Function.support g) by rfl, hgsupp]
    exact hVcl
  have hχpos : tsupport χs ⊆ Ioi (0 : ℝ) := hχsupp.trans hpos
  let χ : PositiveTestFunction := ⟨χs, hχpos⟩
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · change IsCompact (closure (Function.support g))
    rw [hgsupp]
    exact hVcompact
  · intro x
    exact (hgrange ⟨x, rfl⟩).1
  · intro x
    exact (hgrange ⟨x, rfl⟩).2
  · exact hχsupp
  · intro x hx
    exact (hgone x).mp hx

lemma CorrectionBumps.reactionMeasure_compact_positivitySet_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {K : Set (Ioi (0 : ℝ))}
    (hK : IsCompact K)
    (hKpos : K ⊆ {x : Ioi (0 : ℝ) | x.1 ∈ f.positivitySet}) :
    B.reactionMeasure hfmin K = 0 := by
  let Kreal : Set ℝ := (Subtype.val : Ioi (0 : ℝ) → ℝ) '' K
  have hKreal : IsCompact Kreal := by
    exact hK.image continuous_subtype_val
  have hKrealpos : Kreal ⊆ f.positivitySet := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hKpos hy
  obtain ⟨χ, hχcompact, hχnonneg, hχle, hχsupport, hχone⟩ :=
    exists_nonnegative_compact_cutoff_in_positivitySet hKreal hKrealpos
  let φ : C_c(Ioi (0 : ℝ), ℝ) := PositiveTestFunction.toCompactTest χ hχcompact
  have hφone : ∀ x ∈ K, φ x = 1 := by
    intro x hx
    exact hχone (x : ℝ) ⟨x, hx, rfl⟩
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) :=
    IsOpen.locallyCompactSpace isOpen_Ioi
  have hle := RealRMK.rieszMeasure_le_of_eq_one
    (B.correctedFirstVariationExtension hfmin) (f := φ) (by
      intro x
      exact hχnonneg (x : ℝ)) hK (by
      intro x hx
      exact hφone x hx)
  have hzero : B.correctedFirstVariationExtension hfmin φ = 0 := by
    rw [show φ = PositiveTestFunction.toCompactTest χ hχcompact by rfl]
    rw [B.correctedFirstVariationExtension_toCompactTest hfmin χ hχcompact]
    exact B.correctedFirstVariation_eq_zero_of_tsupport_subset_positivity hfmin χ
      hχcompact hχsupport
  have hle' : B.reactionMeasure hfmin K ≤ 0 := by
    change RealRMK.rieszMeasure (B.correctedFirstVariationExtension hfmin) K ≤ 0
    simpa [hzero] using hle
  exact nonpos_iff_eq_zero.mp hle'

theorem CorrectionBumps.reactionMeasure_positivitySet_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    B.reactionMeasure hfmin {x : Ioi (0 : ℝ) | x.1 ∈ f.positivitySet} = 0 := by
  let U : Set (Ioi (0 : ℝ)) := {x | x.1 ∈ f.positivitySet}
  have hU : IsOpen U := by
    change IsOpen ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' f.positivitySet)
    exact f.isOpen_positivitySet.preimage continuous_subtype_val
  let _ : (B.reactionMeasure hfmin).Regular := B.reactionMeasure_regular hfmin
  rw [show {x : Ioi (0 : ℝ) | x.1 ∈ f.positivitySet} = U by rfl,
    hU.measure_eq_iSup_isCompact]
  apply le_antisymm
  · refine iSup_le fun (K : Set (Ioi (0 : ℝ))) =>
      iSup_le fun (hKU : K ⊆ U) => iSup_le fun (hKcompact : IsCompact K) => ?_
    rw [B.reactionMeasure_compact_positivitySet_eq_zero hfmin hKcompact hKU]
  · exact bot_le

lemma CorrectionBumps.reactionMeasure_ae_eq_zero_on_contact_compl
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∀ᵐ x : Ioi (0 : ℝ) ∂B.reactionMeasure hfmin, f.continuousRep (x : ℝ) = 0 := by
  let U : Set (Ioi (0 : ℝ)) := {x | x.1 ∈ f.positivitySet}
  have hUzero : B.reactionMeasure hfmin U = 0 := by
    exact B.reactionMeasure_positivitySet_eq_zero hfmin
  have hcontact : ({x : Ioi (0 : ℝ) | f.continuousRep x = 0} : Set (Ioi (0 : ℝ)))ᶜ ⊆ U := by
    intro x hx
    have hnonneg : 0 ≤ f.continuousRep (x : ℝ) := by
      exact hfmin.1.nonnegative (x : ℝ) (by simpa [halfLine] using x.property.le)
    have hpos : 0 < f.continuousRep (x : ℝ) := lt_of_le_of_ne hnonneg (by
      intro hz
      exact hx (by simp [hz]))
    exact hpos
  exact mem_ae_iff.mpr (measure_mono_null hcontact hUzero)

theorem CorrectionBumps.reactionMeasure_support_subset_contactSet
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    (B.reactionMeasure hfmin).support ⊆
      {x : Ioi (0 : ℝ) | f.continuousRep (x : ℝ) = 0} := by
  let C : Set (Ioi (0 : ℝ)) := {x | f.continuousRep (x : ℝ) = 0}
  have hCclosed : IsClosed C := by
    change IsClosed ((fun x : Ioi (0 : ℝ) => f.continuousRep (x : ℝ)) ⁻¹' ({0} : Set ℝ))
    exact IsClosed.preimage
      (f.continuous_continuousRep.comp continuous_subtype_val) isClosed_singleton
  apply Measure.support_subset_of_isClosed hCclosed
  exact B.reactionMeasure_ae_eq_zero_on_contact_compl hfmin

theorem CorrectionBumps.integral_continuousRep_reactionMeasure_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∫ x : Ioi (0 : ℝ), f.continuousRep x ∂B.reactionMeasure hfmin = 0 := by
  calc
    (∫ x : Ioi (0 : ℝ), f.continuousRep x ∂B.reactionMeasure hfmin) =
        ∫ _ : Ioi (0 : ℝ), (0 : ℝ) ∂B.reactionMeasure hfmin := by
      apply integral_congr_ae
      filter_upwards [B.reactionMeasure_ae_eq_zero_on_contact_compl hfmin] with x hx
      simpa using hx
    _ = 0 := by simp

end HalfLineH1

end Analysis
end RayleighKernel
