import RayleighKernel.Compression.Coverage
import Mathlib.Order.Interval.Set.OrdConnectedLinear

noncomputable section

namespace RayleighKernel

open Set MeasureTheory

theorem openOrdConnected_eq_Ioo_of_bdd
    {C : Set ℝ} (hopen : IsOpen C) (hord : OrdConnected C)
    (hne : C.Nonempty) (hbelow : BddBelow C) (habove : BddAbove C) :
    C = Ioo (sInf C) (sSup C) := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [← interior_Icc]
    exact interior_maximal (subset_Icc_csInf_csSup hbelow habove) hopen hz
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := exists_lt_of_csInf_lt hne hz.1
    obtain ⟨y, hy, hzy⟩ := exists_lt_of_lt_csSup hne hz.2
    exact hord.out hx hy ⟨hxz.le, hzy.le⟩

theorem openOrdConnected_eq_Ioi_of_not_bddAbove
    {C : Set ℝ} (hopen : IsOpen C) (hord : OrdConnected C)
    (hne : C.Nonempty) (hbelow : BddBelow C) (habove : ¬ BddAbove C) :
    C = Ioi (sInf C) := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [← interior_Ici]
    exact interior_maximal (fun _ hz' ↦ csInf_le hbelow hz') hopen hz
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := exists_lt_of_csInf_lt hne hz
    obtain ⟨y, hy, hzy⟩ := (not_bddAbove_iff.mp habove) z
    exact hord.out hx hy ⟨hxz.le, hzy.le⟩

namespace Analysis
namespace HalfLineH1

theorem continuousRep_indicator_weakDeriv_Ioo_primitive_absolutelyContinuousOnInterval
    (f : HalfLineH1) {a b R : ℝ} (hR : 0 < R) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in 0..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) 0 R := by
  have hloc : LocallyIntegrable
      ((Ioo a b).indicator (f.weakDeriv : ℝ → ℝ)) volume := by
    exact (Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim |>.indicator
      measurableSet_Ioo
  have hInt : IntervalIntegrable
      ((Ioo a b).indicator (f.weakDeriv : ℝ → ℝ)) volume 0 R := by
    rw [intervalIntegrable_iff]
    exact (hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  exact hInt.absolutelyContinuousOnInterval_intervalIntegral (by simp [hR.le])

theorem continuousRep_indicator_weakDeriv_Ioi_primitive_absolutelyContinuousOnInterval
    (f : HalfLineH1) {a R : ℝ} (hR : 0 < R) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in 0..x, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) 0 R := by
  have hloc : LocallyIntegrable
      ((Ioi a).indicator (f.weakDeriv : ℝ → ℝ)) volume := by
    exact (Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim |>.indicator
      measurableSet_Ioi
  have hInt : IntervalIntegrable
      ((Ioi a).indicator (f.weakDeriv : ℝ → ℝ)) volume 0 R := by
    rw [intervalIntegrable_iff]
    exact (hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  exact hInt.absolutelyContinuousOnInterval_intervalIntegral (by simp [hR.le])

def restrictedIooValue (f : HalfLineH1) (a b : ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t

def restrictedIoiValue (f : HalfLineH1) (a : ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t

lemma restricted_intervalIntegrable (f : HalfLineH1) (s : Set ℝ)
    (hs : MeasurableSet s) (p q : ℝ) :
    IntervalIntegrable (s.indicator (f.weakDeriv : ℝ → ℝ)) volume p q := by
  have hloc : LocallyIntegrable (f.weakDeriv : ℝ → ℝ) volume :=
    (Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim
  rw [intervalIntegrable_iff]
  exact (hloc.integrableOn_isCompact isCompact_uIcc).indicator hs |>.mono_set
    uIoc_subset_uIcc

theorem integral_indicator_Ioo_weakDeriv_eq_zero_of_le
    (f : HalfLineH1) {a b x : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫ t in 0..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
  rw [intervalIntegral.integral_of_le hx0]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have htn : t ∉ Ioo a b := fun h => (not_lt_of_ge (le_trans ht.2 hxa)) h.1
  simp [Set.indicator, htn]

theorem integral_indicator_Ioi_weakDeriv_eq_zero_of_le
    (f : HalfLineH1) {a x : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫ t in 0..x, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
  rw [intervalIntegral.integral_of_le hx0]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have htn : t ∉ Ioi a := fun h => (not_lt_of_ge (le_trans ht.2 hxa)) h
  simp [Set.indicator, htn]

theorem integral_indicator_Ioo_weakDeriv_eq_continuousRep
    (f : HalfLineH1) {a b x : ℝ} (ha0 : 0 ≤ a) (hax : a < x) (hxb : x ≤ b)
    (ha : f.continuousRep a = 0) :
    (∫ t in 0..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) =
      f.continuousRep x := by
  have h0a : (∫ t in 0..a, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 :=
    integral_indicator_Ioo_weakDeriv_eq_zero_of_le f ha0 le_rfl
  have hax' : (∫ t in a..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) =
      ∫ t in a..x, (f.weakDeriv : ℝ → ℝ) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    simp only [uIoo_of_le hax.le] at ht
    have htb : t < b := lt_of_lt_of_le ht.2 hxb
    simp [Set.indicator, show t ∈ Ioo a b from ⟨ht.1, htb⟩]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (f := fun t ↦ (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t)]
  · rw [h0a, zero_add, hax', ← f.continuousRep_sub a x, ha, sub_zero]
  · exact restricted_intervalIntegrable f (Ioo a b) measurableSet_Ioo 0 a
  · exact restricted_intervalIntegrable f (Ioo a b) measurableSet_Ioo a x

theorem integral_indicator_Ioi_weakDeriv_eq_continuousRep
    (f : HalfLineH1) {a x : ℝ} (ha0 : 0 ≤ a) (hax : a < x)
    (ha : f.continuousRep a = 0) :
    (∫ t in 0..x, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) =
      f.continuousRep x := by
  have h0a : (∫ t in 0..a, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 :=
    integral_indicator_Ioi_weakDeriv_eq_zero_of_le f ha0 le_rfl
  have hax' : (∫ t in a..x, (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t) =
      ∫ t in a..x, (f.weakDeriv : ℝ → ℝ) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    simp only [uIoo_of_le hax.le] at ht
    simp [Set.indicator, ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (f := fun t ↦ (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) t)]
  · rw [h0a, zero_add, hax', ← f.continuousRep_sub a x, ha, sub_zero]
  · exact restricted_intervalIntegrable f (Ioi a) measurableSet_Ioi 0 a
  · exact restricted_intervalIntegrable f (Ioi a) measurableSet_Ioi a x

theorem integral_indicator_Ioo_weakDeriv_eq_zero_of_right_le
    (f : HalfLineH1) {a b x : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hbx : b ≤ x)
    (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    (∫ t in 0..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
  have h0b : (∫ t in 0..b, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
    by_cases hab' : a = b
    · subst b
      exact integral_indicator_Ioo_weakDeriv_eq_zero_of_le f ha0 le_rfl
    · exact (integral_indicator_Ioo_weakDeriv_eq_continuousRep f ha0
        (lt_of_le_of_ne hab hab') le_rfl ha).trans hb
  have hbx' : (∫ t in b..x, (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t) = 0 := by
    rw [intervalIntegral.integral_of_le hbx]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have htn : t ∉ Ioo a b := fun h => (not_lt_of_ge ht.1.le) h.2
    simp [Set.indicator, htn]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (f := fun t ↦ (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) t)]
  · rw [h0b, hbx', add_zero]
  · exact restricted_intervalIntegrable f (Ioo a b) measurableSet_Ioo 0 b
  · exact restricted_intervalIntegrable f (Ioo a b) measurableSet_Ioo b x

theorem restrictedIooValue_eq_indicator
    (f : HalfLineH1) {a b x : ℝ} (hx : x ∈ Ici 0)
    (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0) (hb : f.continuousRep b = 0) :
    restrictedIooValue f a b x = (Ioo a b).indicator f.continuousRep x := by
  by_cases hxa : x ≤ a
  · rw [restrictedIooValue, integral_indicator_Ioo_weakDeriv_eq_zero_of_le f hx hxa]
    simp [Set.indicator, not_lt_of_ge hxa]
  · have hax : a < x := lt_of_not_ge hxa
    by_cases hxb : x ≤ b
    · rw [restrictedIooValue,
        integral_indicator_Ioo_weakDeriv_eq_continuousRep f (a := a) (b := b) (x := x)
          (ha0 := ha0) (hax := hax) (hxb := hxb) ha]
      by_cases hxb' : x < b
      · simp [Set.indicator, hax, hxb']
      · have hxeq : x = b := le_antisymm hxb (le_of_not_gt hxb')
        subst x
        simp [Set.indicator, hax, hb]
    · have hbx : b ≤ x := le_of_not_ge hxb
      by_cases hab : a ≤ b
      · rw [restrictedIooValue,
          integral_indicator_Ioo_weakDeriv_eq_zero_of_right_le f
            (ha0 := ha0) (hab := hab) (hbx := hbx) ha hb]
        simp [Set.indicator, not_lt_of_ge hbx]
      · have hba : b ≤ a := le_of_not_ge hab
        rw [restrictedIooValue]
        simp [Set.indicator, not_lt_of_ge hba]

theorem restrictedIoiValue_eq_indicator
    (f : HalfLineH1) {a x : ℝ} (hx : x ∈ Ici 0)
    (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0) :
    restrictedIoiValue f a x = (Ioi a).indicator f.continuousRep x := by
  by_cases hxa : x ≤ a
  · rw [restrictedIoiValue, integral_indicator_Ioi_weakDeriv_eq_zero_of_le f hx hxa]
    simp [Set.indicator, not_lt_of_ge hxa]
  · rw [restrictedIoiValue,
      integral_indicator_Ioi_weakDeriv_eq_continuousRep f (a := a) (x := x)
        (ha0 := ha0) (hax := lt_of_not_ge hxa) ha]
    simp [Set.indicator, hxa]

theorem continuousRep_indicator_Ioo_absolutelyContinuousOnInterval
    (f : HalfLineH1) {a b R : ℝ} (hR : 0 < R)
    (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0)
    (hb : f.continuousRep b = 0) :
    AbsolutelyContinuousOnInterval
      ((Ioo a b).indicator f.continuousRep) 0 R := by
  apply (continuousRep_indicator_weakDeriv_Ioo_primitive_absolutelyContinuousOnInterval
    f hR).congr
  rw [uIcc_of_le hR.le]
  intro x hx
  exact restrictedIooValue_eq_indicator f hx.1 ha0 ha hb

theorem continuousRep_indicator_Ioi_absolutelyContinuousOnInterval
    (f : HalfLineH1) {a R : ℝ} (hR : 0 < R)
    (ha0 : 0 ≤ a) (ha : f.continuousRep a = 0) :
    AbsolutelyContinuousOnInterval
      ((Ioi a).indicator f.continuousRep) 0 R := by
  apply (continuousRep_indicator_weakDeriv_Ioi_primitive_absolutelyContinuousOnInterval
    f hR).congr
  rw [uIcc_of_le hR.le]
  intro x hx
  exact restrictedIoiValue_eq_indicator f hx.1 ha0 ha

theorem restrictedIooValue_deriv_ae
    (f : HalfLineH1) (a b : ℝ) :
    deriv (restrictedIooValue f a b) =ᵐ[volume]
      (Ioo a b).indicator (f.weakDeriv : ℝ → ℝ) := by
  exact (LocallyIntegrable.ae_hasDerivAt_integral
    ((Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim |>.indicator
      measurableSet_Ioo)).mono fun x hx => hx 0 |>.deriv

theorem restrictedIoiValue_deriv_ae
    (f : HalfLineH1) (a : ℝ) :
    deriv (restrictedIoiValue f a) =ᵐ[volume]
      (Ioi a).indicator (f.weakDeriv : ℝ → ℝ) := by
  exact (LocallyIntegrable.ae_hasDerivAt_integral
    ((Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.elim |>.indicator
      measurableSet_Ioi)).mono fun x hx => hx 0 |>.deriv

theorem restrictedIooValue_deriv_memLp
    (f : HalfLineH1) (a b : ℝ) :
    MemLp (deriv (restrictedIooValue f a b)) 2 volume := by
  exact memLp_congr_ae (restrictedIooValue_deriv_ae f a b) |>.mpr
    (MemLp.indicator measurableSet_Ioo (Lp.memLp f.weakDeriv))

theorem restrictedIoiValue_deriv_memLp
    (f : HalfLineH1) (a : ℝ) :
    MemLp (deriv (restrictedIoiValue f a)) 2 volume := by
  exact memLp_congr_ae (restrictedIoiValue_deriv_ae f a) |>.mpr
    (MemLp.indicator measurableSet_Ioi (Lp.memLp f.weakDeriv))

theorem component_bddBelow (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    BddBelow (D.component n) := by
  refine ⟨0, ?_⟩
  intro x hx
  exact le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun y hy ↦
    lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0))
      (D.subset n hx))

theorem component_eq_Ioo_of_bddAbove (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) (habove : BddAbove (D.component n)) :
    D.component n = Ioo (sInf (D.component n)) (sSup (D.component n)) :=
  openOrdConnected_eq_Ioo_of_bdd (D.isOpen_component n) (D.ordConnected_component n)
    hne (component_bddBelow f D n) habove

theorem component_eq_Ioi_of_not_bddAbove (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) (habove : ¬ BddAbove (D.component n)) :
    D.component n = Ioi (sInf (D.component n)) :=
  openOrdConnected_eq_Ioi_of_not_bddAbove (D.isOpen_component n)
    (D.ordConnected_component n) hne (component_bddBelow f D n) habove

theorem component_sInf_nonneg (f : HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) : 0 ≤ sInf (D.component n) := by
  apply le_csInf hne
  intro x hx
  exact le_of_lt ((show f.positivitySet ⊆ Ioi 0 from fun y hy ↦
    lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0))
      (D.subset n hx))

theorem component_sInf_not_mem_positivitySet
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) :
    sInf (D.component n) ∉ f.positivitySet := by
  have hne0 := hne
  obtain ⟨x, hx⟩ := hne0
  intro he
  by_cases habove : BddAbove (D.component n)
  · have hshape := component_eq_Ioo_of_bddAbove f D n hne habove
    have hsub : uIcc (sInf (D.component n)) x ⊆ f.positivitySet := by
      intro z hz
      rw [uIcc_of_le (mem_Ioo.mp (hshape ▸ hx)).1.le] at hz
      rcases hz with ⟨hz0, hzx⟩
      by_cases hzl : z = sInf (D.component n)
      · simpa [hzl] using he
      · exact D.subset n (hshape ▸ ⟨lt_of_le_of_ne hz0 (Ne.symm hzl),
          lt_of_le_of_lt hzx (mem_Ioo.mp (hshape ▸ hx)).2⟩)
    have hm := mem_ordConnectedComponent.mpr (by simpa [uIcc_comm] using hsub)
    have hEq := D.maximal n hx
    have hmemC : sInf (D.component n) ∈ D.component n := hEq.symm ▸ hm
    have hmemI : sInf (D.component n) ∈ Ioo (sInf (D.component n)) (sSup (D.component n)) :=
      hshape ▸ hmemC
    exact (not_lt_of_ge (le_refl _)) hmemI.1
  · have hshape := component_eq_Ioi_of_not_bddAbove f D n hne habove
    have hsub : uIcc (sInf (D.component n)) x ⊆ f.positivitySet := by
      intro z hz
      rw [uIcc_of_le (mem_Ioi.mp (hshape ▸ hx)).le] at hz
      rcases hz with ⟨hz0, hzx⟩
      by_cases hzl : z = sInf (D.component n)
      · simpa [hzl] using he
      · exact D.subset n (hshape ▸ lt_of_le_of_ne hz0 (Ne.symm hzl))
    have hm := mem_ordConnectedComponent.mpr (by simpa [uIcc_comm] using hsub)
    have hEq := D.maximal n hx
    have hmemC : sInf (D.component n) ∈ D.component n := hEq.symm ▸ hm
    have hi : sInf (D.component n) ∈ Ioi (sInf (D.component n)) := hshape ▸ hmemC
    exact (lt_irrefl _ (mem_Ioi.mp hi))

theorem component_sSup_not_mem_positivitySet
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) (habove : BddAbove (D.component n)) :
    sSup (D.component n) ∉ f.positivitySet := by
  have hne0 := hne
  obtain ⟨z, hz⟩ := hne0
  intro hp
  have hs := component_eq_Ioo_of_bddAbove f D n hne habove
  have hsub : uIcc z (sSup (D.component n)) ⊆ f.positivitySet := by
    intro y hy
    rw [uIcc_of_le ((mem_Ioo.mp (hs ▸ hz)).2.le)] at hy
    rcases hy with ⟨hyz, hyr⟩
    by_cases he : y = sSup (D.component n)
    · simpa [he] using hp
    · exact D.subset n (hs ▸ ⟨lt_of_lt_of_le (mem_Ioo.mp (hs ▸ hz)).1 hyz,
        lt_of_le_of_ne hyr he⟩)
  have hm := mem_ordConnectedComponent.mpr (by simpa [uIcc_comm] using hsub)
  have hc := D.maximal n hz
  have hmem : sSup (D.component n) ∈ D.component n := hc ▸ hm
  have hi : sSup (D.component n) ∈ Ioo (sInf (D.component n)) (sSup (D.component n)) :=
    hs ▸ hmem
  exact (not_lt_of_ge (le_refl _)) hi.2

theorem component_sInf_eq_zero_of_nonnegative
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    f.continuousRep (sInf (D.component n)) = 0 := by
  have h0 : sInf (D.component n) ∈ Ici 0 := component_sInf_nonneg f D n hne
  have hn := component_sInf_not_mem_positivitySet f D n hne
  have hle : 0 ≤ f.continuousRep (sInf (D.component n)) := hnonneg _ h0
  exact le_antisymm (le_of_not_gt hn) hle

theorem component_sSup_eq_zero_of_nonnegative
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hne : (D.component n).Nonempty) (habove : BddAbove (D.component n))
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    f.continuousRep (sSup (D.component n)) = 0 := by
  have h0 : sSup (D.component n) ∈ Ici 0 := by
    exact le_trans (component_sInf_nonneg f D n hne)
      (csInf_le_csSup hne (component_bddBelow f D n) habove)
  have hn := component_sSup_not_mem_positivitySet f D n hne habove
  exact le_antisymm (le_of_not_gt hn) (hnonneg _ h0)

theorem componentRestriction_absolutelyContinuousOnInterval
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x)
    {R : ℝ} (hR : 0 < R) :
    AbsolutelyContinuousOnInterval
      ((D.component n).indicator f.continuousRep) 0 R := by
  by_cases hne : (D.component n).Nonempty
  · by_cases habove : BddAbove (D.component n)
    · rw [component_eq_Ioo_of_bddAbove f D n hne habove]
      exact continuousRep_indicator_Ioo_absolutelyContinuousOnInterval f hR
        (component_sInf_nonneg f D n hne)
        (component_sInf_eq_zero_of_nonnegative f D n hne hnonneg)
        (component_sSup_eq_zero_of_nonnegative f D n hne habove hnonneg)
    · rw [component_eq_Ioi_of_not_bddAbove f D n hne habove]
      exact continuousRep_indicator_Ioi_absolutelyContinuousOnInterval f hR
        (component_sInf_nonneg f D n hne)
        (component_sInf_eq_zero_of_nonnegative f D n hne hnonneg)
  · have hempty : D.component n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simpa using continuousRep_indicator_Ioo_absolutelyContinuousOnInterval f hR
      le_rfl f.continuousRep_zero f.continuousRep_zero

end HalfLineH1
end Analysis
end RayleighKernel
