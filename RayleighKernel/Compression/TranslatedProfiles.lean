import RayleighKernel.Compression.ComponentProfiles
import RayleighKernel.Analysis.ConvolutionLp
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Set MeasureTheory
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem deriv_compSubConst (φ : SchwartzMap ℝ ℝ) (s x : ℝ) :
    (SchwartzMap.derivCLM ℝ ℝ (φ.compSubConstCLM ℝ s) : ℝ → ℝ) x =
      deriv (φ : ℝ → ℝ) (x - s) := by
  change deriv (fun y : ℝ => φ (y - s)) x = _
  rw [deriv_comp_sub_const]

theorem coe_schwartzValue_ae (φ : SchwartzMap ℝ ℝ) :
    ((schwartzValue φ : RealL2) : ℝ → ℝ) =ᵐ[volume] (φ : ℝ → ℝ) := φ.coeFn_toLp 2 volume

theorem coe_schwartzDeriv_ae (φ : SchwartzMap ℝ ℝ) :
    ((schwartzDeriv φ : RealL2) : ℝ → ℝ) =ᵐ[volume] deriv (φ : ℝ → ℝ) :=
  (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume

theorem integral_mul_comp_sub_eq_integral_comp_add_mul
    {g h : ℝ → ℝ} (s : ℝ) :
    (∫ x, g (x + s) * h x) = ∫ z, g z * h (z - s) := by
  let H : ℝ → ℝ := fun z => g z * h (z - s)
  have hc := (measurePreserving_add_right (volume : Measure ℝ) s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding H
  simpa [H, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hc

theorem l2Pairing_translateL2_schwartzValue (s : ℝ) (g : RealL2) (φ : SchwartzMap ℝ ℝ) :
    l2Pairing (translateL2 s g) (schwartzValue φ) =
      l2Pairing g (schwartzValue (φ.compSubConstCLM ℝ s)) := by
  unfold l2Pairing
  rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
  have hl : (∫ x, (translateL2 s g : ℝ → ℝ) x *
      (schwartzValue φ : RealL2) x) = ∫ x, (g : ℝ → ℝ) (x + s) * φ x := by
    apply integral_congr_ae
    filter_upwards [translateL2_ae_eq s g, coe_schwartzValue_ae φ] with x hx hφ
    rw [hx, hφ]
  have hr : (∫ x, (g : ℝ → ℝ) x *
      (schwartzValue (φ.compSubConstCLM ℝ s) : RealL2) x) =
      ∫ x, (g : ℝ → ℝ) x * φ (x - s) := by
    apply integral_congr_ae
    filter_upwards [coe_schwartzValue_ae (φ.compSubConstCLM ℝ s)] with x hφ
    rw [hφ]
    simp [SchwartzMap.compSubConstCLM_apply]
  change (∫ x, (translateL2 s g : ℝ → ℝ) x * (schwartzValue φ : RealL2) x) =
    ∫ x, (g : ℝ → ℝ) x * (schwartzValue (φ.compSubConstCLM ℝ s) : RealL2) x
  rw [hl, hr]
  exact integral_mul_comp_sub_eq_integral_comp_add_mul s

theorem l2Pairing_translateL2_schwartzDeriv (s : ℝ) (g : RealL2) (φ : SchwartzMap ℝ ℝ) :
    l2Pairing (translateL2 s g) (schwartzDeriv φ) =
      l2Pairing g (schwartzDeriv (φ.compSubConstCLM ℝ s)) := by
  unfold l2Pairing
  rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
  have hl : (∫ x, (translateL2 s g : ℝ → ℝ) x * (schwartzDeriv φ : RealL2) x) =
      ∫ x, (g : ℝ → ℝ) (x + s) * deriv (φ : ℝ → ℝ) x := by
    apply integral_congr_ae
    filter_upwards [translateL2_ae_eq s g, coe_schwartzDeriv_ae φ] with x hx hφ
    rw [hx, hφ]
  have hr : (∫ x, (g : ℝ → ℝ) x *
      (schwartzDeriv (φ.compSubConstCLM ℝ s) : RealL2) x) =
      ∫ x, (g : ℝ → ℝ) x * deriv (φ : ℝ → ℝ) (x - s) := by
    apply integral_congr_ae
    filter_upwards [coe_schwartzDeriv_ae (φ.compSubConstCLM ℝ s)] with x hφ
    rw [hφ]
    change _ * deriv (fun y : ℝ => φ (y - s)) x = _
    rw [deriv_comp_sub_const]
  change (∫ x, (translateL2 s g : ℝ → ℝ) x * (schwartzDeriv φ : RealL2) x) =
    ∫ x, (g : ℝ → ℝ) x * (schwartzDeriv (φ.compSubConstCLM ℝ s) : RealL2) x
  rw [hl, hr]
  exact integral_mul_comp_sub_eq_integral_comp_add_mul s

theorem translateL2_ae_eq_zero_on_nonpositive (s : ℝ) (g : RealL2)
    (hg : (g : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    (translateL2 s g : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  have hg' : ∀ᵐ z : ℝ ∂volume, z ≤ s → (g : ℝ → ℝ) z = 0 :=
    (ae_restrict_iff' measurableSet_Iic).mp hg
  have hpull : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → (g : ℝ → ℝ) (x + s) = 0 := by
    have hc := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae hg'
    filter_upwards [hc] with x hx hx0
    exact hx (by linarith)
  refine (ae_restrict_iff' measurableSet_Iic).2 ?_
  filter_upwards [translateL2_ae_eq s g, hpull] with x hx hp hx0
  rw [hx, hp hx0]
  rfl

def translateLeft (u : HalfLineH1) (s : ℝ)
    (hvalue : (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0)
    (hderiv : (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) : HalfLineH1 := by
  let hv := translateL2 s u.value
  let hd := translateL2 s u.weakDeriv
  have hv0 := translateL2_ae_eq_zero_on_nonpositive s u.value hvalue
  have hd0 := translateL2_ae_eq_zero_on_nonpositive s u.weakDeriv hderiv
  have hweak : ∀ φ : SchwartzMap ℝ ℝ,
      l2Pairing hv (schwartzDeriv φ) = -l2Pairing hd (schwartzValue φ) := by
    intro φ
    let ψ := φ.compSubConstCLM ℝ s
    rw [show hv = translateL2 s u.value by rfl, show hd = translateL2 s u.weakDeriv by rfl,
      l2Pairing_translateL2_schwartzDeriv, l2Pairing_translateL2_schwartzValue]
    exact u.weakDerivative_identity ψ
  exact ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm (hv, hd),
    graph_mem_halfLineH1Submodule_of_weakDerivative hv hd hv0 hd0 hweak⟩

@[simp] theorem value_translateLeft (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    (translateLeft u s hvalue hderiv).value = translateL2 s u.value := rfl

@[simp] theorem weakDeriv_translateLeft (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    (translateLeft u s hvalue hderiv).weakDeriv = translateL2 s u.weakDeriv := rfl

theorem value_translateLeft_ae (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    ((translateLeft u s hvalue hderiv).value : ℝ → ℝ) =ᵐ[volume] fun y => (u.value : ℝ → ℝ) (y + s) :=
  translateL2_ae_eq s u.value

theorem weakDeriv_translateLeft_ae (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    ((translateLeft u s hvalue hderiv).weakDeriv : ℝ → ℝ) =ᵐ[volume] fun y => (u.weakDeriv : ℝ → ℝ) (y + s) :=
  translateL2_ae_eq s u.weakDeriv

theorem continuousRep_translateLeft (u : HalfLineH1) (s : ℝ) (_hs : 0 ≤ s) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0)
    (_hu0 : u.continuousRep s = 0) {y : ℝ} (_hy : y ∈ Ici 0) :
    (translateLeft u s hvalue hderiv).continuousRep y = u.continuousRep (y + s) := by
  let f : ℝ → ℝ := fun y => u.continuousRep (y + s)
  have hf : Continuous f := u.continuous_continuousRep.comp (continuous_id.add continuous_const)
  have hfu : f =ᵐ[volume] ((translateLeft u s hvalue hderiv).value : ℝ → ℝ) := by
    have hu := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae
      u.continuousRep_ae_eq_value
    filter_upwards [hu, value_translateLeft_ae u s hvalue hderiv] with x hx htrans
    exact hx.trans htrans.symm
  have heq := HalfLineH1.eq_continuousRep_of_continuous_ae_eq_value
    (translateLeft u s hvalue hderiv) hf hfu
  exact (congrFun heq y).symm

def translatedComponentProfile (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (n : ℕ) (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) : HalfLineH1 :=
  let u := componentRestrictionProfile f D n hnonneg
  translateLeft u (componentGap f D n)
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg)

theorem continuousRep_translatedComponentProfile (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {y : ℝ} (hy : y ∈ Ici 0) :
    (translatedComponentProfile f D n hnonneg).continuousRep y =
      (D.component n).indicator f.continuousRep (y + componentGap f D n) := by
  let u := componentRestrictionProfile f D n hnonneg
  have hgap := componentGap_nonneg f D n
  have hzero := componentRestrictionProfile_continuousRep_componentGap_eq_zero f D n hnonneg
  have hrep := continuousRep_translateLeft u (componentGap f D n) hgap
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg) hzero hy
  rw [translatedComponentProfile]
  exact hrep.trans (continuousRep_componentRestrictionProfile f D n hnonneg (by
    show 0 ≤ y + componentGap f D n
    exact add_nonneg hy hgap))

theorem continuousRep_translatedComponentProfile_compressionMap (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {z : ℝ} (hz : z ∈ D.component n) :
    (translatedComponentProfile f D n hnonneg).continuousRep (f.compressionMap z) = f.continuousRep z := by
  have hz0 : z ∈ Ici 0 := by
    have hzpos : 0 < z := (show f.positivitySet ⊆ Ioi 0 from fun x hx =>
      lt_of_not_ge fun h => hx.ne' (f.continuousRep_eq_zero_of_nonpositive h)) (D.subset n hz)
    show 0 ≤ z
    exact hzpos.le
  rw [continuousRep_translatedComponentProfile f D n hnonneg
    (show f.compressionMap z ∈ Ici 0 from f.compressionMap_nonneg_of_nonneg hz0)]
  rw [f.compressionMap_eq_sub_componentGap_of_mem D n hz]
  simp [Set.indicator, hz]

theorem continuousRep_translatedComponentProfile_eq_zero_of_not_mem (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {y : ℝ} (hy0 : y ∈ Ici 0)
    (hy : y ∉ translatedComponent f D n) :
    (translatedComponentProfile f D n hnonneg).continuousRep y = 0 := by
  rw [continuousRep_translatedComponentProfile f D n hnonneg hy0]
  have hnot : y + componentGap f D n ∉ D.component n := by
    intro hmem
    exact hy ((translatedComponent_eq_preimage_add_componentGap f D n).mpr hmem)
  simp [Set.indicator, hnot]

@[simp] theorem continuousRep_translatedComponentProfile_zero (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (translatedComponentProfile f D n hnonneg).continuousRep 0 = 0 := by
  apply continuousRep_translatedComponentProfile_eq_zero_of_not_mem f D n hnonneg
      (show (0 : ℝ) ∈ Ici 0 from by norm_num)
  intro h
  have : (0 : ℝ) < 0 := translatedComponent_subset_Ioi_zero f D n h
  exact (lt_irrefl 0) this

theorem translatedComponentProfile_nonnegative (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ∀ y ∈ Ici 0, 0 ≤ (translatedComponentProfile f D n hnonneg).continuousRep y := by
  intro y hy
  change 0 ≤ y at hy
  rw [continuousRep_translatedComponentProfile f D n hnonneg hy]
  by_cases h : y + componentGap f D n ∈ D.component n
  · simpa [Set.indicator, h] using hnonneg (y + componentGap f D n)
      (by
        show 0 ≤ y + componentGap f D n
        exact add_nonneg hy (componentGap_nonneg f D n))
  · simp only [Set.indicator, h, ↓reduceIte, le_refl]

theorem value_translatedComponentProfile_ae_indicator
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
  ((translatedComponentProfile f D n hnonneg).value : ℝ → ℝ) =ᵐ[volume]
    (translatedComponent f D n).indicator
      (fun y => f.continuousRep (y + componentGap f D n)) := by
  have htrans := value_translateLeft_ae (componentRestrictionProfile f D n hnonneg)
    (componentGap f D n)
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
  have hpull := (measurePreserving_add_right (volume : Measure ℝ) (componentGap f D n)).quasiMeasurePreserving.ae
    (value_componentRestrictionProfile_ae_indicator f D n hnonneg)
  rw [translatedComponentProfile]
  filter_upwards [htrans, hpull] with y hy hprofile
  rw [hy, hprofile]
  by_cases hmem : y + componentGap f D n ∈ D.component n
  · have htranslated : y ∈ translatedComponent f D n :=
      (translatedComponent_eq_preimage_add_componentGap f D n).mpr hmem
    simp [Set.indicator, hmem, htranslated]
  · have htranslated : y ∉ translatedComponent f D n := by
      intro hy'
      exact hmem ((translatedComponent_eq_preimage_add_componentGap f D n).mp hy')
    simp [Set.indicator, hmem, htranslated]

theorem weakDeriv_translatedComponentProfile_ae_indicator
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
  ((translatedComponentProfile f D n hnonneg).weakDeriv : ℝ → ℝ) =ᵐ[volume]
    (translatedComponent f D n).indicator
      (fun y => (f.weakDeriv : ℝ → ℝ) (y + componentGap f D n)) := by
  have htrans := weakDeriv_translateLeft_ae (componentRestrictionProfile f D n hnonneg)
    (componentGap f D n)
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
  have hpull := (measurePreserving_add_right (volume : Measure ℝ) (componentGap f D n)).quasiMeasurePreserving.ae
    (weakDeriv_componentRestrictionProfile_ae_indicator f D n hnonneg)
  rw [translatedComponentProfile]
  filter_upwards [htrans, hpull] with y hy hprofile
  rw [hy, hprofile]
  by_cases hmem : y + componentGap f D n ∈ D.component n
  · have htranslated : y ∈ translatedComponent f D n :=
      (translatedComponent_eq_preimage_add_componentGap f D n).mpr hmem
    simp [Set.indicator, hmem, htranslated]
  · have htranslated : y ∉ translatedComponent f D n := by
      intro hy'
      exact hmem ((translatedComponent_eq_preimage_add_componentGap f D n).mp hy')
    simp [Set.indicator, hmem, htranslated]

@[simp] theorem norm_value_translateLeft (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    ‖(translateLeft u s hvalue hderiv).value‖ = ‖u.value‖ := by
  rw [value_translateLeft, translateL2_norm]

@[simp] theorem norm_weakDeriv_translateLeft (u : HalfLineH1) (s : ℝ) (hvalue :
    (u.value : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) (hderiv :
    (u.weakDeriv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic s)] 0) :
    ‖(translateLeft u s hvalue hderiv).weakDeriv‖ = ‖u.weakDeriv‖ := by
  rw [weakDeriv_translateLeft, translateL2_norm]

@[simp] theorem norm_value_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(translatedComponentProfile f D n hnonneg).value‖ =
      ‖(componentRestrictionProfile f D n hnonneg).value‖ := by
  exact norm_value_translateLeft (componentRestrictionProfile f D n hnonneg)
    (componentGap f D n)
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg)

@[simp] theorem norm_weakDeriv_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖(translatedComponentProfile f D n hnonneg).weakDeriv‖ =
      ‖(componentRestrictionProfile f D n hnonneg).weakDeriv‖ := by
  exact norm_weakDeriv_translateLeft (componentRestrictionProfile f D n hnonneg)
    (componentGap f D n)
    (componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap f D n hnonneg)
    (componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap f D n hnonneg)

theorem norm_sq_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖translatedComponentProfile f D n hnonneg‖ ^ 2 =
      ‖componentRestrictionProfile f D n hnonneg‖ ^ 2 := by
  rw [(translatedComponentProfile f D n hnonneg).norm_sq_eq,
    (componentRestrictionProfile f D n hnonneg).norm_sq_eq,
    (translatedComponentProfile f D n hnonneg).norm_valueOnHalfLine,
    (translatedComponentProfile f D n hnonneg).norm_weakDerivOnHalfLine,
    (componentRestrictionProfile f D n hnonneg).norm_valueOnHalfLine,
    (componentRestrictionProfile f D n hnonneg).norm_weakDerivOnHalfLine,
    norm_value_translatedComponentProfile, norm_weakDeriv_translatedComponentProfile]

@[simp] theorem norm_translatedComponentProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ‖translatedComponentProfile f D n hnonneg‖ =
      ‖componentRestrictionProfile f D n hnonneg‖ := by
  nlinarith [norm_sq_translatedComponentProfile f D n hnonneg,
    norm_nonneg (translatedComponentProfile f D n hnonneg),
    norm_nonneg (componentRestrictionProfile f D n hnonneg)]

end RayleighKernel.Analysis.HalfLineH1
