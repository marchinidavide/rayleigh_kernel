import RayleighKernel.Compression.TranslatedProfiles

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

def finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) : HalfLineH1 :=
  Finset.sum (Finset.range N) (fun n => translatedComponentProfile f D n hnonneg)

@[simp] theorem finiteCompressedProfile_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    finiteCompressedProfile f D hnonneg 0 = 0 := by
  simp [finiteCompressedProfile]

theorem finiteCompressedProfile_succ
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) :
    finiteCompressedProfile f D hnonneg (N + 1) =
      finiteCompressedProfile f D hnonneg N +
        translatedComponentProfile f D N hnonneg := by
  simp [finiteCompressedProfile, Finset.sum_range_succ]

theorem continuousRep_finiteCompressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) (y : ℝ) :
    (finiteCompressedProfile f D hnonneg N).continuousRep y =
      Finset.sum (Finset.range N)
        (fun n => (translatedComponentProfile f D n hnonneg).continuousRep y) := by
  induction N with
  | zero => simp [finiteCompressedProfile]
  | succ N ih =>
      rw [finiteCompressedProfile_succ, continuousRep_add]
      change (finiteCompressedProfile f D hnonneg N).continuousRep y +
        (translatedComponentProfile f D N hnonneg).continuousRep y = _
      rw [ih, Finset.sum_range_succ]

theorem continuousRep_finiteCompressedProfile_eq_shifted_sum
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) {y : ℝ}
    (hy : y ∈ Ici 0) :
    (finiteCompressedProfile f D hnonneg N).continuousRep y =
      Finset.sum (Finset.range N)
        (fun n => (D.component n).indicator f.continuousRep
          (y + componentGap f D n)) := by
  rw [continuousRep_finiteCompressedProfile]
  apply Finset.sum_congr rfl
  intro n hn
  exact continuousRep_translatedComponentProfile f D n hnonneg hy

theorem finiteCompressedProfile_nonnegative
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) :
    ∀ y ∈ Ici 0,
      0 ≤ (finiteCompressedProfile f D hnonneg N).continuousRep y := by
  intro y hy
  rw [continuousRep_finiteCompressedProfile]
  exact Finset.sum_nonneg fun n hn =>
    translatedComponentProfile_nonnegative f D n hnonneg y hy

@[simp] theorem continuousRep_finiteCompressedProfile_zero
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) (N : ℕ) :
    (finiteCompressedProfile f D hnonneg N).continuousRep 0 = 0 := by
  rw [continuousRep_finiteCompressedProfile]
  simp only [continuousRep_translatedComponentProfile_zero, Finset.sum_const_zero]

theorem continuousRep_finiteCompressedProfile_eq_zero_of_not_mem
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N : ℕ} {y : ℝ}
    (hy0 : y ∈ Ici 0)
    (hy : ∀ n < N, y ∉ translatedComponent f D n) :
    (finiteCompressedProfile f D hnonneg N).continuousRep y = 0 := by
  rw [continuousRep_finiteCompressedProfile]
  apply Finset.sum_eq_zero
  intro n hn
  exact continuousRep_translatedComponentProfile_eq_zero_of_not_mem f D n hnonneg
    hy0 (hy n (Finset.mem_range.1 hn))

theorem continuousRep_finiteCompressedProfile_of_mem
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N n : ℕ} (hn : n < N)
    {y : ℝ} (hy : y ∈ translatedComponent f D n) :
    (finiteCompressedProfile f D hnonneg N).continuousRep y =
      f.continuousRep (y + componentGap f D n) := by
  have hy0 : y ∈ Ici 0 := by
    change 0 ≤ y
    exact le_of_lt (show 0 < y from translatedComponent_subset_Ioi_zero f D n hy)
  rw [continuousRep_finiteCompressedProfile]
  rw [Finset.sum_eq_single n (fun m hm hmn =>
    continuousRep_translatedComponentProfile_eq_zero_of_not_mem f D m hnonneg hy0
      (fun hym =>
        (Set.disjoint_left.mp (translatedComponent_pairwiseDisjoint f D hmn) hym hy).elim))
    (fun hnot => False.elim (hnot (Finset.mem_range.mpr hn)))]
  rw [continuousRep_translatedComponentProfile f D n hnonneg hy0]
  simp [Set.indicator, (translatedComponent_eq_preimage_add_componentGap f D n).mp hy]

theorem continuousRep_finiteCompressedProfile_compressionMap
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N n : ℕ} (hn : n < N)
    {z : ℝ} (hz : z ∈ D.component n) :
    (finiteCompressedProfile f D hnonneg N).continuousRep (f.compressionMap z) =
      f.continuousRep z := by
  rw [continuousRep_finiteCompressedProfile]
  rw [Finset.sum_eq_single n (fun m hm hmn =>
    continuousRep_translatedComponentProfile_eq_zero_of_not_mem f D m hnonneg
      (f.compressionMap_nonneg_of_nonneg (by
        have hz0 : z ∈ Ici 0 := by
          change 0 ≤ z
          exact le_of_lt (lt_of_not_ge fun hz0 =>
            (D.subset n hz).ne' (f.continuousRep_eq_zero_of_nonpositive hz0))
        exact hz0))
      (fun hym =>
        (Set.disjoint_left.mp (translatedComponent_pairwiseDisjoint f D hmn)
          hym ⟨z, hz, rfl⟩).elim))
    (fun hnot => False.elim (hnot (Finset.mem_range.mpr hn)))]
  exact continuousRep_translatedComponentProfile_compressionMap f D n hnonneg hz

theorem continuousRep_finiteCompressedProfile_mono_nat
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) {N M : ℕ} (hNM : N ≤ M)
    {y : ℝ} (hy : y ∈ Ici 0) :
    (finiteCompressedProfile f D hnonneg N).continuousRep y ≤
      (finiteCompressedProfile f D hnonneg M).continuousRep y := by
  rw [continuousRep_finiteCompressedProfile, continuousRep_finiteCompressedProfile]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM)
    (fun n hnN _ => translatedComponentProfile_nonnegative f D n hnonneg y hy)

end RayleighKernel.Analysis.HalfLineH1
