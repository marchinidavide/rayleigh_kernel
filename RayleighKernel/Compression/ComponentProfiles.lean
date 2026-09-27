import RayleighKernel.Compression.ComponentRestriction

noncomputable section

namespace RayleighKernel
open Set MeasureTheory
open Analysis
namespace Analysis
namespace HalfLineH1

theorem weakDerivative_identity_of_compact_interval
    {F q : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hAC : AbsolutelyContinuousOnInterval F 0 B)
    (hF : MemLp F 2 volume) (hq : MemLp q 2 volume)
    (hFzero_left : ∀ x ≤ 0, F x = 0)
    (hFzero_right : ∀ x, B ≤ x → F x = 0)
    (hqzero_left : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → q x = 0)
    (hqzero_right : ∀ᵐ x : ℝ ∂volume, B ≤ x → q x = 0)
    (hderiv : deriv F =ᵐ[volume] q) :
    ∀ φ : SchwartzMap ℝ ℝ,
      l2Pairing (hF.toLp F) (schwartzDeriv φ) =
        -l2Pairing (hq.toLp q) (schwartzValue φ) := by
  intro φ
  have hφ : MemLp (φ : ℝ → ℝ) 2 volume := φ.memLp 2 volume
  have hφd : MemLp (deriv (φ : ℝ → ℝ)) 2 volume :=
    (SchwartzMap.derivCLM ℝ ℝ φ).memLp 2 volume
  have hleftInt : Integrable (fun x ↦ F x * deriv (φ : ℝ → ℝ) x) volume :=
    hF.integrable_mul hφd
  have hrightInt : Integrable (fun x ↦ q x * φ x) volume := hq.integrable_mul hφ
  have hparts := hAC.integral_mul_deriv_eq_deriv_mul
    (ContDiffOn.absolutelyContinuousOnInterval (fun x _ ↦
      (φ.contDiffAt 1).contDiffWithinAt))
  have hleft : l2Pairing (hF.toLp F) (schwartzDeriv φ) =
      ∫ x in (0 : ℝ)..B, F x * deriv (φ : ℝ → ℝ) x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    have heq : (∫ x : ℝ, F x * deriv (φ : ℝ → ℝ) x) =
        ∫ x in Ioc 0 B, F x * deriv (φ : ℝ → ℝ) x := by
      have hc : (∫ x in (Ioc (0 : ℝ) B)ᶜ, F x * deriv (φ : ℝ → ℝ) x) = 0 := by
        apply integral_eq_zero_of_ae
        refine (ae_restrict_iff' measurableSet_Ioc.compl).2 ?_
        filter_upwards with x hx
        rcases le_or_gt x 0 with hx0 | hx0
        · simp [hFzero_left x hx0]
        · have hBx : B ≤ x := by
            by_contra hBx
            exact hx ⟨hx0, le_of_not_ge hBx⟩
          simp [hFzero_right x hBx]
      have hd := integral_add_compl (s := Ioc (0 : ℝ) B) measurableSet_Ioc hleftInt
      rw [hc] at hd
      linarith
    rw [intervalIntegral.integral_of_le hB]
    have hnorm : (∫ x : ℝ, ((ContinuousLinearMap.mul ℝ ℝ)
        (((hF.toLp F : RealL2) : ℝ → ℝ) x)
        (((schwartzDeriv φ : RealL2) : ℝ → ℝ) x))) =
        ∫ x : ℝ, F x * deriv (φ : ℝ → ℝ) x := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp,
        (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume] with x hx hφx
      simp [schwartzDeriv, schwartzValue, hx, hφx]
    rw [hnorm, heq]
  have hright : l2Pairing (hq.toLp q) (schwartzValue φ) =
      ∫ x in (0 : ℝ)..B, q x * φ x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    have heq : (∫ x : ℝ, q x * (φ : ℝ → ℝ) x) =
        ∫ x in Ioc 0 B, q x * (φ : ℝ → ℝ) x := by
      have hc : (∫ x in (Ioc (0 : ℝ) B)ᶜ, q x * (φ : ℝ → ℝ) x) = 0 := by
        apply integral_eq_zero_of_ae
        refine (ae_restrict_iff' measurableSet_Ioc.compl).2 ?_
        filter_upwards [hqzero_left, hqzero_right] with x hx0 hxB hx
        rcases le_or_gt x 0 with hx0' | hx0'
        · simp [hx0 hx0']
        · have hBx : B ≤ x := by
            by_contra hBx
            exact hx ⟨hx0', le_of_not_ge hBx⟩
          simp [hxB hBx]
      have hd := integral_add_compl (s := Ioc (0 : ℝ) B) measurableSet_Ioc hrightInt
      rw [hc] at hd
      linarith
    rw [intervalIntegral.integral_of_le hB]
    have hnorm : (∫ x : ℝ, ((ContinuousLinearMap.mul ℝ ℝ)
        (((hq.toLp q : RealL2) : ℝ → ℝ) x)
        (((schwartzValue φ : RealL2) : ℝ → ℝ) x))) =
        ∫ x : ℝ, q x * (φ : ℝ → ℝ) x := by
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp, φ.coeFn_toLp 2 volume] with x hx hφx
      simp [schwartzValue, hx, hφx]
    rw [hnorm, heq]
  rw [hleft, hright]
  have hq' : (∫ x in (0 : ℝ)..B, deriv F x * φ x) =
      ∫ x in (0 : ℝ)..B, q x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx hmem
    rw [hx]
  rw [hq'] at hparts
  simp [hFzero_left 0 le_rfl, hFzero_right B le_rfl] at hparts
  linarith

theorem restrictedIooValue_eq_indicator_global
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    restrictedIooValue f a b = (Ioo a b).indicator f.continuousRep := by
  funext x
  by_cases hx : x ≤ 0
  · rw [restrictedIooValue]
    rw [intervalIntegral.integral_of_ge hx]
    have hz : (∫ t in Ioc x 0, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      have htn : t ∉ Ioo a b := fun h => (not_lt_of_ge (le_trans ht.2 ha0)) h.1
      simp [Set.indicator, htn]
    rw [hz, neg_zero]
    simp [Set.indicator, not_lt_of_ge (le_trans hx ha0)]
  · exact restrictedIooValue_eq_indicator f (le_of_not_ge hx) ha0 ha hb

theorem restrictedIoiValue_eq_indicator_global
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) :
    restrictedIoiValue f a = (Ioi a).indicator f.continuousRep := by
  funext x
  by_cases hx : x ≤ 0
  · rw [restrictedIoiValue]
    rw [intervalIntegral.integral_of_ge hx]
    have hz : (∫ t in Ioc x 0, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      have htn : t ∉ Ioi a := fun h => (not_lt_of_ge (le_trans ht.2 ha0)) h
      simp [Set.indicator, htn]
    rw [hz, neg_zero]
    simp [Set.indicator, not_lt_of_ge (le_trans hx ha0)]
  · exact restrictedIoiValue_eq_indicator f (le_of_not_ge hx) ha0 ha

theorem restrictedIooValue_memLp
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    MemLp (restrictedIooValue f a b) 2 volume := by
  rw [restrictedIooValue_eq_indicator_global f ha0 ha hb]
  exact MemLp.indicator measurableSet_Ioo f.continuousRep_memLp

theorem restrictedIoiValue_memLp
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) :
    MemLp (restrictedIoiValue f a) 2 volume := by
  rw [restrictedIoiValue_eq_indicator_global f ha0 ha]
  exact MemLp.indicator measurableSet_Ioi f.continuousRep_memLp

theorem restrictedIooValue_ae_eq_zero_on_nonpositive
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    restrictedIooValue f a b =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  rw [restrictedIooValue_eq_indicator_global f ha0 ha hb]
  refine (ae_restrict_iff' measurableSet_Iic).2 ?_
  filter_upwards with x hx
  simp [Set.indicator, not_lt_of_ge (le_trans hx ha0)]

theorem restrictedIoiValue_ae_eq_zero_on_nonpositive
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) :
    restrictedIoiValue f a =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  rw [restrictedIoiValue_eq_indicator_global f ha0 ha]
  refine (ae_restrict_iff' measurableSet_Iic).2 ?_
  filter_upwards with x hx
  simp [Set.indicator, not_lt_of_ge (le_trans hx ha0)]

theorem restrictedIooValue_deriv_ae_eq_zero_on_nonpositive
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) :
    deriv (restrictedIooValue f a b) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  refine (ae_restrict_iff' measurableSet_Iic).2 ?_
  filter_upwards [restrictedIooValue_deriv_ae f a b] with x hx hnonpos
  rw [hx]
  simp [Set.indicator, not_lt_of_ge (le_trans hnonpos ha0)]

theorem restrictedIoiValue_deriv_ae_eq_zero_on_nonpositive
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a) :
    deriv (restrictedIoiValue f a) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  refine (ae_restrict_iff' measurableSet_Iic).2 ?_
  filter_upwards [restrictedIoiValue_deriv_ae f a] with x hx hnonpos
  rw [hx]
  simp [Set.indicator, not_lt_of_ge (le_trans hnonpos ha0)]

theorem restrictedIooValue_weakDerivative_identity
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    ∀ φ : SchwartzMap ℝ ℝ,
      l2Pairing ((restrictedIooValue_memLp f ha0 ha hb).toLp (restrictedIooValue f a b))
          (schwartzDeriv φ) =
        -l2Pairing ((restrictedIooValue_deriv_memLp f a b).toLp
          (deriv (restrictedIooValue f a b))) (schwartzValue φ) := by
  let hval := restrictedIooValue_memLp f ha0 ha hb
  let hder := restrictedIooValue_deriv_memLp f a b
  have hB : 0 ≤ b := le_trans ha0 hab.le
  have hAC : AbsolutelyContinuousOnInterval (restrictedIooValue f a b) 0 b :=
    continuousRep_indicator_weakDeriv_Ioo_primitive_absolutelyContinuousOnInterval f
      (lt_of_le_of_lt ha0 hab)
  have hFzero_left : ∀ x ≤ 0, restrictedIooValue f a b x = 0 := by
    intro x hx
    rw [restrictedIooValue_eq_indicator_global f ha0 ha hb]
    simp [Set.indicator, not_lt_of_ge (le_trans hx ha0)]
  have hFzero_right : ∀ x, b ≤ x → restrictedIooValue f a b x = 0 := by
    intro x hbx
    rw [restrictedIooValue_eq_indicator_global f ha0 ha hb]
    simp only [Set.indicator]
    split_ifs with hx
    · exact False.elim ((not_lt_of_ge hbx) hx.2)
    · rfl
  have hqzero_left : ∀ᵐ x : ℝ ∂volume, x ≤ 0 →
      deriv (restrictedIooValue f a b) x = 0 :=
    (ae_restrict_iff' measurableSet_Iic).mp
      (restrictedIooValue_deriv_ae_eq_zero_on_nonpositive f ha0)
  have hqzero_right : ∀ᵐ x : ℝ ∂volume, b ≤ x →
      deriv (restrictedIooValue f a b) x = 0 := by
    filter_upwards [restrictedIooValue_deriv_ae f a b] with x hx hbx
    rw [hx]
    simp only [Set.indicator]
    split_ifs with hx'
    · exact False.elim ((not_lt_of_ge hbx) hx'.2)
    · rfl
  intro φ
  have hq : MemLp (deriv (restrictedIooValue f a b)) 2 volume :=
    restrictedIooValue_deriv_memLp f a b
  have hi := weakDerivative_identity_of_compact_interval hB hAC hval
    hq hFzero_left hFzero_right hqzero_left hqzero_right
    (Filter.EventuallyEq.rfl)
  exact hi φ

def restrictedIooProfile
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) : HalfLineH1 :=
  let hv := (restrictedIooValue_memLp f ha0 ha hb).toLp (restrictedIooValue f a b)
  let hd := (restrictedIooValue_deriv_memLp f a b).toLp
    (deriv (restrictedIooValue f a b))
  let hzv : (hv : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
    filter_upwards [(restrictedIooValue_memLp f ha0 ha hb).coeFn_toLp.filter_mono ae_restrict_le,
      restrictedIooValue_ae_eq_zero_on_nonpositive f ha0 ha hb] with x hx hzero
    rw [hx, hzero]
  let hzd : (hd : ℝ → ℝ) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
    filter_upwards [(restrictedIooValue_deriv_memLp f a b).coeFn_toLp.filter_mono ae_restrict_le,
      restrictedIooValue_deriv_ae_eq_zero_on_nonpositive f ha0] with x hx hzero
    rw [hx, hzero]
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm (hv, hd),
    graph_mem_halfLineH1Submodule_of_weakDerivative hv hd hzv hzd
      (restrictedIooValue_weakDerivative_identity f ha0 hab ha hb)⟩

@[simp] theorem value_restrictedIooProfile
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    (restrictedIooProfile f ha0 hab ha hb).value =
      (restrictedIooValue_memLp f ha0 ha hb).toLp (restrictedIooValue f a b) := rfl

@[simp] theorem weakDeriv_restrictedIooProfile
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    (restrictedIooProfile f ha0 hab ha hb).weakDeriv =
      (restrictedIooValue_deriv_memLp f a b).toLp
        (deriv (restrictedIooValue f a b)) := rfl

theorem value_restrictedIooProfile_ae
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    ((restrictedIooProfile f ha0 hab ha hb).value : ℝ → ℝ) =ᵐ[volume]
      restrictedIooValue f a b := by
  exact (restrictedIooValue_memLp f ha0 ha hb).coeFn_toLp

theorem weakDeriv_restrictedIooProfile_ae
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    ((restrictedIooProfile f ha0 hab ha hb).weakDeriv : ℝ → ℝ) =ᵐ[volume]
      deriv (restrictedIooValue f a b) := by
  exact (restrictedIooValue_deriv_memLp f a b).coeFn_toLp

theorem continuousRep_restrictedIooProfile
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) {x : ℝ}
    (hx : x ∈ Ici 0) :
    (restrictedIooProfile f ha0 hab ha hb).continuousRep x =
      (Ioo a b).indicator f.continuousRep x := by
  have hEq := HalfLineH1.eqOn_continuousRep_of_trace_deriv
    (restrictedIooProfile f ha0 hab ha hb)
    (by simp)
    (fun R hR =>
      continuousRep_indicator_weakDeriv_Ioo_primitive_absolutelyContinuousOnInterval
        f (a := a) (b := b) hR)
    (by
      refine (ae_restrict_iff' measurableSet_Ici).2 ?_
      filter_upwards [restrictedIooValue_deriv_ae f a b,
        (restrictedIooValue_deriv_memLp f a b).coeFn_toLp] with y hy hLp hyI
      change deriv (restrictedIooValue f a b) y =
        (restrictedIooProfile f ha0 hab ha hb).weakDeriv y
      rw [weakDeriv_restrictedIooProfile]
      exact hLp.symm)
  exact (hEq hx).symm.trans
    (congrFun (restrictedIooValue_eq_indicator_global f ha0 ha hb) x)

theorem continuousRep_restrictedIooProfile_of_mem
    (f : HalfLineH1) {a b x : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0)
    (hx : x ∈ Ioo a b) :
    (restrictedIooProfile f ha0 hab ha hb).continuousRep x = f.continuousRep x := by
  have h := continuousRep_restrictedIooProfile f ha0 hab ha hb
    (le_trans ha0 hx.1.le)
  rw [h]
  simp [Set.indicator, hx]

theorem continuousRep_restrictedIooProfile_nonnegative
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ∀ x ∈ Ici 0, 0 ≤ (restrictedIooProfile f ha0 hab ha hb).continuousRep x := by
  intro x hx
  rw [continuousRep_restrictedIooProfile f ha0 hab ha hb hx]
  by_cases h : x ∈ Ioo a b
  · simpa [Set.indicator, h] using hnonneg x hx
  · simp [Set.indicator, h]

@[simp] theorem continuousRep_neg (u : HalfLineH1) :
    (-u).continuousRep = -u.continuousRep := by
  simpa using HalfLineH1.continuousRep_smul (-1 : ℝ) u

@[simp] theorem continuousRep_sub_eq (u v : HalfLineH1) :
    (u - v).continuousRep = u.continuousRep - v.continuousRep := by
  rw [sub_eq_add_neg, HalfLineH1.continuousRep_add, continuousRep_neg]
  rfl

def restrictedIoiProfile (f : HalfLineH1) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0) : HalfLineH1 :=
  if h : a = 0 then f
  else f - restrictedIooProfile f (a := 0) (b := a)
    le_rfl (lt_of_le_of_ne ha0 (Ne.symm h)) f.continuousRep_zero ha

theorem continuousRep_restrictedIoiProfile
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0) {x : ℝ}
    (hx : x ∈ Ici 0) :
    (restrictedIoiProfile f a ha0 ha).continuousRep x =
      (Ioi a).indicator f.continuousRep x := by
  by_cases h : a = 0
  · subst a
    simp only [restrictedIoiProfile, dite_true]
    by_cases hzero : x = 0
    · subst x
      simp [Set.indicator, f.continuousRep_zero]
    · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
      simp [Set.indicator, hpos]
  · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm h)
    rw [restrictedIoiProfile]
    simp only [h, dite_false]
    rw [continuousRep_sub_eq]
    change f.continuousRep x -
      (restrictedIooProfile f le_rfl hapos f.continuousRep_zero ha).continuousRep x = _
    rw [continuousRep_restrictedIooProfile f le_rfl hapos
      f.continuousRep_zero ha hx]
    by_cases hxa : x ≤ a
    · by_cases hzero : x = 0
      · subst x
        simp [Set.indicator, f.continuousRep_zero]
      · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
        by_cases hxeq : x = a
        · subst x
          simp [Set.indicator, ha]
        · have hlt : x < a := lt_of_le_of_ne hxa hxeq
          simp [Set.indicator, hpos, hlt, hxa]
    · have hax : a < x := lt_of_not_ge hxa
      simp [Set.indicator, hax, le_of_lt hax]

theorem continuousRep_restrictedIoiProfile_nonnegative
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ∀ x ∈ Ici 0, 0 ≤ (restrictedIoiProfile f a ha0 ha).continuousRep x := by
  intro x hx
  rw [continuousRep_restrictedIoiProfile f ha0 ha hx]
  by_cases hxa : x ∈ Ioi a
  · simpa [Set.indicator, hxa] using hnonneg x hx
  · simp [Set.indicator, hxa]

def componentRestrictionProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) : HalfLineH1 := by
  classical
  exact
  dite (D.component n).Nonempty
    (fun hne => dite (BddAbove (D.component n))
      (fun habove =>
        let hs := component_eq_Ioo_of_bddAbove f D n hne habove
        let ha0 := component_sInf_nonneg f D n hne
        let ha := component_sInf_eq_zero_of_nonnegative f D n hne hnonneg
        let hb := component_sSup_eq_zero_of_nonnegative f D n hne habove hnonneg
        let hlt : sInf (D.component n) < sSup (D.component n) := by
          obtain ⟨x, hx⟩ := hne
          have hx' : x ∈ Ioo (sInf (D.component n)) (sSup (D.component n)) := hs ▸ hx
          exact lt_trans hx'.1 hx'.2
        restrictedIooProfile f ha0 hlt ha hb)
      (fun _ => restrictedIoiProfile f (sInf (D.component n))
        (component_sInf_nonneg f D n hne)
        (component_sInf_eq_zero_of_nonnegative f D n hne hnonneg)))
    (fun _ => 0)

theorem continuousRep_componentRestrictionProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {x : ℝ} (hx : x ∈ Ici 0) :
    (componentRestrictionProfile f D n hnonneg).continuousRep x =
      (D.component n).indicator f.continuousRep x := by
  by_cases hne : (D.component n).Nonempty
  · by_cases habove : BddAbove (D.component n)
    · simp only [componentRestrictionProfile, dite_true, hne, habove]
      let hs := component_eq_Ioo_of_bddAbove f D n hne habove
      let ha0 := component_sInf_nonneg f D n hne
      let ha := component_sInf_eq_zero_of_nonnegative f D n hne hnonneg
      let hb := component_sSup_eq_zero_of_nonnegative f D n hne habove hnonneg
      let hlt : sInf (D.component n) < sSup (D.component n) := by
        obtain ⟨y, hy⟩ := hne
        have hy' : y ∈ Ioo (sInf (D.component n)) (sSup (D.component n)) := hs ▸ hy
        exact lt_trans hy'.1 hy'.2
      rw [continuousRep_restrictedIooProfile f ha0 hlt ha hb hx]
      rw [hs, csInf_Ioo hlt, csSup_Ioo hlt]
    · simp only [componentRestrictionProfile, dite_true, hne, dite_false, habove]
      rw [continuousRep_restrictedIoiProfile f (component_sInf_nonneg f D n hne)
        (component_sInf_eq_zero_of_nonnegative f D n hne hnonneg) hx]
      rw [component_eq_Ioi_of_not_bddAbove f D n hne habove]
      rw [csInf_Ioi]
  · simp only [componentRestrictionProfile, dite_false, hne]
    have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

theorem componentRestrictionProfile_nonnegative
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ∀ x ∈ Ici 0, 0 ≤ (componentRestrictionProfile f D n hnonneg).continuousRep x := by
  intro x hx
  rw [continuousRep_componentRestrictionProfile f D n hnonneg hx]
  by_cases h : x ∈ D.component n
  · simp only [Set.indicator_of_mem h]
    exact hnonneg x hx
  · simp [Set.indicator, h]

@[simp] theorem weakDeriv_sub_profile (u v : HalfLineH1) :
  (u-v).weakDeriv = u.weakDeriv - v.weakDeriv := by
  exact map_sub HalfLineH1.weakDeriv u v

theorem coe_weakDeriv_sub_ae (u v : HalfLineH1) :
    (((u-v).weakDeriv : RealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => (u.weakDeriv : ℝ → ℝ) x - (v.weakDeriv : ℝ → ℝ) x := by
  rw [weakDeriv_sub_profile]
  exact Lp.coeFn_sub u.weakDeriv v.weakDeriv

theorem sub_indicator_Ioo_eq_indicator_Ioi_ae
    (q : ℝ → ℝ) {a : ℝ} (ha0 : 0 ≤ a)
    (hq0 : q =ᵐ[(volume).restrict (Iic 0)] 0) :
    (fun x => q x - (Ioo 0 a).indicator q x) =ᵐ[volume]
    (Ioi a).indicator q := by
  have hq0' : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → q x = 0 :=
    (ae_restrict_iff' measurableSet_Iic).mp hq0
  filter_upwards [hq0', MeasureTheory.Measure.ae_ne volume (0 : ℝ),
    MeasureTheory.Measure.ae_ne volume a] with x hx hzero ha
  by_cases hx0 : x ≤ 0
  · rw [hx hx0]
    have h1 : x ∉ Ioo 0 a := fun h => (not_lt_of_ge hx0) h.1
    have h2 : x ∉ Ioi a := fun h => (not_lt_of_ge ha0) (lt_of_lt_of_le h hx0)
    simp [Set.indicator, h1, h2]
  · have hxpos : 0 < x := lt_of_not_ge hx0
    by_cases hxa : x < a
    · have h1 : x ∈ Ioo 0 a := ⟨hxpos, hxa⟩
      have h2 : x ∉ Ioi a := fun h => (not_lt_of_ge (le_of_lt hxa)) h
      simp [Set.indicator, h1, h2]
    · by_cases hxeq : x = a
      · subst x
        exact False.elim (ha rfl)
      · have hax : a < x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hxeq)
        simp [Set.indicator, hax, hxa]

theorem value_restrictedIooProfile_ae_indicator
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    ((restrictedIooProfile f ha0 hab ha hb).value : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator f.continuousRep := by
  exact (value_restrictedIooProfile_ae f ha0 hab ha hb).trans
    (Filter.Eventually.of_forall (congrFun
      (restrictedIooValue_eq_indicator_global f ha0 ha hb)))

theorem weakDeriv_restrictedIooProfile_ae_indicator
    (f : HalfLineH1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    ((restrictedIooProfile f ha0 hab ha hb).weakDeriv : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) := by
  exact (weakDeriv_restrictedIooProfile_ae f ha0 hab ha hb).trans
    (restrictedIooValue_deriv_ae f a b)

theorem restrictedIoiProfile_eq_sub_of_ne
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) (h : a ≠ 0) :
    restrictedIoiProfile f a ha0 ha = f - restrictedIooProfile f (a := 0) (b := a)
      le_rfl (lt_of_le_of_ne ha0 (Ne.symm h)) f.continuousRep_zero ha := by
  simp only [restrictedIoiProfile, dite_eq_right h]

theorem weakDeriv_restrictedIoiProfile_ae_indicator
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) :
    ((restrictedIoiProfile f a ha0 ha).weakDeriv : ℝ → ℝ) =ᵐ[volume]
      (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) := by
  by_cases h : a = 0
  · subst a
    simp only [restrictedIoiProfile, dite_true]
    have hpure := sub_indicator_Ioo_eq_indicator_Ioi_ae
      (f.weakDeriv : ℝ → ℝ) (by positivity)
      f.weakDeriv_ae_eq_zero_on_nonpositive
    filter_upwards [hpure] with x hx
    simpa [Set.indicator] using hx
  · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm h)
    rw [restrictedIoiProfile_eq_sub_of_ne f ha0 ha h]
    filter_upwards [coe_weakDeriv_sub_ae f
        (restrictedIooProfile f (a := 0) (b := a) le_rfl hapos
          f.continuousRep_zero ha),
      weakDeriv_restrictedIooProfile_ae_indicator f le_rfl hapos
        f.continuousRep_zero ha,
      sub_indicator_Ioo_eq_indicator_Ioi_ae (f.weakDeriv : ℝ → ℝ) hapos.le
        (f.weakDeriv_ae_eq_zero_on_nonpositive)] with x hx hq hsub
    rw [hq] at hx
    exact hx.trans hsub

theorem value_restrictedIoiProfile_ae_indicator
    (f : HalfLineH1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : f.continuousRep a = 0) :
    ((restrictedIoiProfile f a ha0 ha).value : ℝ → ℝ) =ᵐ[volume]
      (Ioi a).indicator f.continuousRep := by
  have hcv := (restrictedIoiProfile f a ha0 ha).continuousRep_ae_eq_value.symm
  have hz := (restrictedIoiProfile f a ha0 ha).value_ae_eq_zero_on_nonpositive
  have hz' : ∀ᵐ x : ℝ ∂volume, x ≤ 0 →
      ((restrictedIoiProfile f a ha0 ha).value : ℝ → ℝ) x = 0 :=
    (ae_restrict_iff' measurableSet_Iic).mp hz
  filter_upwards [hcv, hz'] with x hx hz
  by_cases hx0 : 0 ≤ x
  · rw [hx, continuousRep_restrictedIoiProfile f ha0 ha hx0]
  · have hxle : x ≤ 0 := le_of_not_ge hx0
    rw [hz hxle]
    have hxi : x ∉ Ioi a := fun hax => (not_lt_of_ge ha0) (hax.trans_le hxle)
    simp [Set.indicator, hxi]

theorem weakDeriv_componentRestrictionProfile_ae_indicator
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ((componentRestrictionProfile f D n hnonneg).weakDeriv : ℝ → ℝ) =ᵐ[volume]
      (D.component n).indicator (f.weakDeriv : ℝ → ℝ) := by
  by_cases hne : (D.component n).Nonempty
  · by_cases habove : BddAbove (D.component n)
    · simp only [componentRestrictionProfile, dite_true, hne, habove]
      let hs := component_eq_Ioo_of_bddAbove f D n hne habove
      let ha0 := component_sInf_nonneg f D n hne
      let ha := component_sInf_eq_zero_of_nonnegative f D n hne hnonneg
      let hb := component_sSup_eq_zero_of_nonnegative f D n hne habove hnonneg
      let hlt : sInf (D.component n) < sSup (D.component n) := by
        obtain ⟨y, hy⟩ := hne
        have hy' : y ∈ Ioo (sInf (D.component n)) (sSup (D.component n)) := hs ▸ hy
        exact lt_trans hy'.1 hy'.2
      simpa only [← hs] using
        (weakDeriv_restrictedIooProfile_ae_indicator f ha0 hlt ha hb)
    · simp only [componentRestrictionProfile, dite_true, hne, dite_false, habove]
      have hshape := component_eq_Ioi_of_not_bddAbove f D n hne habove
      simpa only [← hshape] using
        (weakDeriv_restrictedIoiProfile_ae_indicator f
          (component_sInf_nonneg f D n hne)
          (component_sInf_eq_zero_of_nonnegative f D n hne hnonneg))
  · simp only [componentRestrictionProfile, dite_false, hne]
    have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    filter_upwards with x
    simp

theorem value_componentRestrictionProfile_ae_indicator
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ((componentRestrictionProfile f D n hnonneg).value : ℝ → ℝ) =ᵐ[volume]
      (D.component n).indicator f.continuousRep := by
  have hcv := (componentRestrictionProfile f D n hnonneg).continuousRep_ae_eq_value.symm
  have hz := (componentRestrictionProfile f D n hnonneg).value_ae_eq_zero_on_nonpositive
  have hz' : ∀ᵐ x : ℝ ∂volume, x ≤ 0 →
      ((componentRestrictionProfile f D n hnonneg).value : ℝ → ℝ) x = 0 :=
    (ae_restrict_iff' measurableSet_Iic).mp hz
  filter_upwards [hcv, hz'] with x hx hz
  by_cases hx0 : 0 ≤ x
  · rw [hx, continuousRep_componentRestrictionProfile f D n hnonneg hx0]
  · have hxle : x ≤ 0 := le_of_not_ge hx0
    rw [hz hxle]
    have hxi : x ∉ D.component n := by
      intro hmem
      exact (not_lt_of_ge hxle) ((show f.positivitySet ⊆ Ioi 0 from fun y hy ↦
        lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0))
        (D.subset n hmem))
    simp [Set.indicator, hxi]

def componentGap (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) : ℝ :=
  by
    classical
    exact if h : (D.component n).Nonempty then
      let x := Classical.choose h
      x - f.compressionMap x
    else 0

theorem componentGap_nonneg (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    0 ≤ componentGap f D n := by
  by_cases h : (D.component n).Nonempty
  · rw [componentGap, dite_eq_left h]
    have hx0 : 0 ≤ Classical.choose h := by
      exact le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun y hy ↦
        lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0))
        (D.subset n (Classical.choose_spec h)))
    exact sub_nonneg.mpr (f.compressionMap_le_self_of_nonneg hx0)
  · rw [componentGap, dite_eq_right h]

theorem compressionMap_eq_sub_componentGap_of_mem
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    {x : ℝ} (hx : x ∈ D.component n) :
    f.compressionMap x = x - componentGap f D n := by
  have hne : (D.component n).Nonempty := ⟨x, hx⟩
  rw [componentGap, dite_eq_left hne]
  let z := Classical.choose hne
  have hz := Classical.choose_spec hne
  have htrans := f.compressionMap_sub_eq_sub_of_component D n hz hx
  dsimp [z]
  linarith

theorem translatedComponent_eq_preimage_add_componentGap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    {y : ℝ} :
    y ∈ translatedComponent f D n ↔
      y + componentGap f D n ∈ D.component n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [compressionMap_eq_sub_componentGap_of_mem f D n hx]
    ring_nf
    exact hx
  · intro hy
    refine ⟨y + componentGap f D n, hy, ?_⟩
    rw [compressionMap_eq_sub_componentGap_of_mem f D n hy]
    ring

theorem translatedComponent_subset_Ioi_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    translatedComponent f D n ⊆ Ioi 0 := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_component n) x hx
  let z := x - δ / 2
  have hz : z ∈ D.component n := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> dsimp [z] <;> linarith)
  have hzx : z < x := by dsimp [z]; linarith
  have hzpos : 0 < z := lt_of_not_ge fun hz0 ↦
    (D.subset n hz).ne' (f.continuousRep_eq_zero_of_nonpositive hz0)
  have hmap := compressionMap_strictMono_on_component f D n hz hzx
  exact lt_of_le_of_lt (f.compressionMap_nonneg_of_nonneg hzpos.le) hmap

theorem componentGap_le_sInf
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) :
    componentGap f D n ≤ sInf (D.component n) := by
  apply le_csInf hne
  intro x hx
  rw [componentGap, dite_eq_left hne]
  let z := Classical.choose hne
  have hz := Classical.choose_spec hne
  have htrans := f.compressionMap_sub_eq_sub_of_component D n hz hx
  have hnonneg := f.compressionMap_nonneg_of_nonneg (le_of_lt ((show
    f.positivitySet ⊆ Ioi 0 from fun y hy ↦
      lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0))
    (D.subset n hx)))
  dsimp [z]
  linarith

theorem componentRestrictionProfile_value_ae_eq_zero_on_Iic_componentGap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ((componentRestrictionProfile f D n hnonneg).value : ℝ → ℝ) =ᵐ[
      (volume : Measure ℝ).restrict (Iic (componentGap f D n))] 0 := by
  by_cases hne : (D.component n).Nonempty
  · have hnot : ∀ {x : ℝ}, x ≤ componentGap f D n → x ∉ D.component n := by
      intro x hxgap hxmem
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_component n) x hxmem
      let z := x - δ / 2
      have hz : z ∈ D.component n := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> dsimp [z] <;> linarith)
      have hbelow : BddBelow (D.component n) := ⟨0, fun y hy =>
        le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun t ht ↦
          lt_of_not_ge fun ht0 ↦ ht.ne' (f.continuousRep_eq_zero_of_nonpositive ht0))
          (D.subset n hy))⟩
      have hsz : sInf (D.component n) ≤ z := csInf_le hbelow hz
      have hgap := componentGap_le_sInf f D n hne
      have hzx : z < x := by dsimp [z]; linarith
      linarith
    refine (ae_restrict_iff' measurableSet_Iic).2 ?_
    filter_upwards [value_componentRestrictionProfile_ae_indicator f D n hnonneg] with x hx hgap
    rw [hx]
    simp [Set.indicator, hnot hgap]
  · have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [componentRestrictionProfile, dite_false, hne]
    filter_upwards with x
    simp

theorem componentRestrictionProfile_weakDeriv_ae_eq_zero_on_Iic_componentGap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    ((componentRestrictionProfile f D n hnonneg).weakDeriv : ℝ → ℝ) =ᵐ[
      (volume : Measure ℝ).restrict (Iic (componentGap f D n))] 0 := by
  by_cases hne : (D.component n).Nonempty
  · have hnot : ∀ {x : ℝ}, x ≤ componentGap f D n → x ∉ D.component n := by
      intro x hxgap hxmem
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_component n) x hxmem
      let z := x - δ / 2
      have hz : z ∈ D.component n := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> dsimp [z] <;> linarith)
      have hbelow : BddBelow (D.component n) := ⟨0, fun y hy =>
        le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun t ht ↦
          lt_of_not_ge fun ht0 ↦ ht.ne' (f.continuousRep_eq_zero_of_nonpositive ht0))
          (D.subset n hy))⟩
      have hsz : sInf (D.component n) ≤ z := csInf_le hbelow hz
      have hgap := componentGap_le_sInf f D n hne
      have hzx : z < x := by dsimp [z]; linarith
      linarith
    refine (ae_restrict_iff' measurableSet_Iic).2 ?_
    filter_upwards [weakDeriv_componentRestrictionProfile_ae_indicator f D n hnonneg] with x hx hgap
    rw [hx]
    simp [Set.indicator, hnot hgap]
  · have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [componentRestrictionProfile, dite_false, hne]
    filter_upwards with x
    simp

theorem componentRestrictionProfile_continuousRep_componentGap_eq_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (componentRestrictionProfile f D n hnonneg).continuousRep (componentGap f D n) = 0 := by
  have hgap0 := componentGap_nonneg f D n
  rw [continuousRep_componentRestrictionProfile f D n hnonneg hgap0]
  by_cases hne : (D.component n).Nonempty
  · have hnot : componentGap f D n ∉ D.component n := by
      intro hxmem
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (D.isOpen_component n)
        (componentGap f D n) hxmem
      let z := componentGap f D n - δ / 2
      have hz : z ∈ D.component n := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> dsimp [z] <;> linarith)
      have hbelow : BddBelow (D.component n) := ⟨0, fun y hy =>
        le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun t ht ↦
          lt_of_not_ge fun ht0 ↦ ht.ne' (f.continuousRep_eq_zero_of_nonpositive ht0))
          (D.subset n hy))⟩
      have hsz : sInf (D.component n) ≤ z := csInf_le hbelow hz
      have hgap := componentGap_le_sInf f D n hne
      have hzgap : z < componentGap f D n := by dsimp [z]; linarith
      linarith [hgap, hsz, hzgap]
    simp [Set.indicator, hnot]
  · have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

end HalfLineH1
end Analysis
end RayleighKernel
