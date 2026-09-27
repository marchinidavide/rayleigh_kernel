import RayleighKernel.Discrete.CellIntegrals
import Mathlib.Order.SuccPred.IntervalSucc

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace RayleighKernel.Discrete

private def positiveCell (h : ℝ) (j : ℕ) : Set ℝ :=
  Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)

private theorem positiveCell_iUnion {h : ℝ} (hh : 0 < h) :
    (⋃ j : ℕ, positiveCell h j) = Ici 0 := by
  let f : ℕ → ℝ := fun j => (j : ℝ) * h
  have hf : StrictMono f := by
    intro a b hab
    dsimp [f]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) hh
  have hmono : ∀ j, f 0 ≤ f j := by
    intro j
    dsimp [f]
    exact mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hh)
  have hn_unbounded : ¬ BddAbove (Set.range (fun n : ℕ => (n : ℝ))) := by
    have hn : ¬ BddAbove (Set.range (fun n : ℕ => n)) :=
      (StrictMono.not_bddAbove_range_of_isSuccArchimedean
        (f := fun n : ℕ => n) (by intro a b hab; exact hab))
    rintro ⟨B, hB⟩
    apply hn
    refine ⟨Nat.ceil B + 1, ?_⟩
    intro n hnmem
    obtain ⟨k, rfl⟩ := hnmem
    have hk : (k : ℝ) ≤ B := hB ⟨k, rfl⟩
    have hk' : k ≤ Nat.ceil B := by exact_mod_cast hk.trans (Nat.le_ceil B)
    have hk'' : k ≤ Nat.ceil B + 1 := by omega
    norm_num at hk ⊢
    exact_mod_cast hk''
  have hbdd : ¬ BddAbove (Set.range f) := by
    rintro ⟨B, hB⟩
    apply hn_unbounded
    refine ⟨B / h, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply (le_div_iff₀ hh).2
    simpa [f, mul_comm] using hB ⟨n, rfl⟩
  simpa [f, positiveCell, Nat.cast_add, add_mul] using
    (iUnion_Ico_map_succ_eq_Ici (α := ℕ) (f := f) hmono hbdd)

private theorem positiveCell_pairwise {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (fun j : ℕ => positiveCell h j)) := by
  let f : ℕ → ℝ := fun j => (j : ℝ) * h
  have hmono : Monotone f := by
    intro a b hab
    dsimp [f]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (le_of_lt hh)
  simpa [f, positiveCell, Nat.cast_add, add_mul] using
    hmono.pairwise_disjoint_on_Ico_succ

private theorem cell_integral_set {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    ∫ x in positiveCell h j, interpolant h w x = (w j + w (j + 1)) / 2 := by
  rw [show positiveCell h j = Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) by rfl]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith [hh])]
  rw [cell_mass h w hh j]

private theorem neg_integral_set {h : ℝ} {w : Kernel} (hh : 0 < h) :
    ∫ x in Ico (-h) 0, interpolant h w x = w 0 / 2 := by
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [neg_mass h w hh]

private theorem neg_weighted_integral_set {h : ℝ} {w : Kernel} (hh : 0 < h) :
    (∫ x in Ico (-h) 0, x * interpolant h w x) = -(h * w 0) / 6 := by
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [neg_first_moment h w hh]

private theorem cell_weighted_integral_set {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    (∫ x in positiveCell h j, x * interpolant h w x) =
      h / 6 * ((3 * (j : ℝ) + 1) * w j + (3 * (j : ℝ) + 2) * w (j + 1)) := by
  rw [show positiveCell h j = Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) by rfl]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith [hh])]
  rw [cell_first_moment h w hh j]

/-- The positive-cell mass series is summable for an absolutely summable kernel. -/
theorem summable_interpolant_cell_masses {w : Kernel} (hw : Summable w) :
    Summable (fun j : ℕ => (w j + w (j + 1)) / 2) := by
  have hshift : Summable (fun j : ℕ => w (j + 1)) := by
    simpa [Function.comp_def] using hw.comp_injective Nat.succ_injective
  have hadd : Summable (fun j : ℕ => w j + w (j + 1)) := hw.add hshift
  simpa [div_eq_mul_inv] using hadd.mul_right (2 : ℝ)⁻¹

/-- The positive-cell first-moment series is summable for an admissible kernel. -/
theorem summable_interpolant_cell_first_moments {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Summable (fun j : ℕ => h / 6 * ((3 * (j : ℝ) + 1) * w j +
      (3 * (j : ℝ) + 2) * w (j + 1))) := by
  have hshift : Summable (fun j : ℕ => (j : ℝ) * w (j + 1)) := by
    have hs := hw.summable_firstMoment.comp_injective Nat.succ_injective
    have hs0 := hw.summable.comp_injective Nat.succ_injective
    apply hs.sub hs0 |>.congr
    intro j
    simp only [Function.comp_apply]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
  have hshift0 : Summable (fun j : ℕ => w (j + 1)) := by
    simpa [Function.comp_def] using hw.summable.comp_injective Nat.succ_injective
  have ha : Summable (fun j : ℕ => (3 * (j : ℝ) + 1) * w j) := by
    apply (hw.summable_firstMoment.mul_left 3).add hw.summable |>.congr
    intro j
    ring
  have hb : Summable (fun j : ℕ => (3 * (j : ℝ) + 2) * w (j + 1)) := by
    apply (hshift.mul_left 3).add (hshift0.mul_left 2) |>.congr
    intro j
    ring
  apply (ha.add hb).mul_right (h / 6) |>.congr
  intro j
  ring

theorem integrable_interpolant_of_summable {h : ℝ} {w : Kernel} (hh : 0 < h)
    (hw_nonneg : ∀ j, 0 ≤ w j) (hw_sum : Summable w) :
    Integrable (interpolant h w) := by
  have hpos : IntegrableOn (interpolant h w) (Ici 0) := by
    have hu : IntegrableOn (interpolant h w) (⋃ j, positiveCell h j) :=
      integrableOn_iUnion_of_summable_integral_norm
        (fun j => by
          dsimp [positiveCell]
          exact IntegrableOn.mono_set
            ((continuous_interpolant hh).continuousOn.integrableOn_Icc
              (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h)) Ico_subset_Icc_self)
        (by
          convert summable_interpolant_cell_masses hw_sum using 1
          funext j
          rw [← integral_congr_ae (Filter.Eventually.of_forall (fun x =>
            by rw [Real.norm_of_nonneg (interpolant_nonneg hh hw_nonneg x)]))]
          exact cell_integral_set hh j)
    rw [← positiveCell_iUnion hh]
    exact hu
  have hneg : IntegrableOn (interpolant h w) (Ico (-h) 0) := by
    apply IntegrableOn.mono_set
      ((continuous_interpolant hh).continuousOn.integrableOn_Icc (a := -h) (b := 0))
    exact Ico_subset_Icc_self
  have hleft : IntegrableOn (interpolant h w) (Ico (-h) 0 ∪ Ici 0) := hneg.union hpos
  have hleft' : IntegrableOn (interpolant h w) (Ici (-h)) := by
    convert hleft using 1
    ext x
    simp only [mem_union, mem_Ici, mem_Ico]
    constructor
    · intro hx
      by_cases hx0 : x < 0
      · exact Or.inl ⟨hx, hx0⟩
      · exact Or.inr (le_of_not_gt hx0)
    · rintro (hx | hx)
      · exact hx.1
      · linarith
  have hzero : IntegrableOn (interpolant h w) (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx
      exact (interpolant_of_le_neg h w (le_of_lt hx)).symm
    · exact measurableSet_Iio
  have hall : IntegrableOn (interpolant h w) (Iio (-h) ∪ Ici (-h)) := hzero.union hleft'
  rw [show Iio (-h) ∪ Ici (-h) = (Set.univ : Set ℝ) by
    ext x
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ]
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x < -h
      · exact Or.inl hx
      · exact Or.inr (le_of_not_gt hx)] at hall
  exact (integrableOn_univ).mp hall

private theorem positive_integral_hasSum {h : ℝ} {w : Kernel} (hh : 0 < h)
    (hw_nonneg : ∀ j, 0 ≤ w j) (hw_sum : Summable w) :
    HasSum (fun j => ∫ x in positiveCell h j, interpolant h w x)
      (∫ x in Ici 0, interpolant h w x) := by
  rw [← positiveCell_iUnion hh]
  apply MeasureTheory.hasSum_integral_iUnion
    (fun j => by dsimp [positiveCell]; measurability)
    (positiveCell_pairwise hh)
  exact integrableOn_iUnion_of_summable_integral_norm
    (fun j => by
      dsimp [positiveCell]
      exact IntegrableOn.mono_set
        ((continuous_interpolant hh).continuousOn.integrableOn_Icc
          (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h)) Ico_subset_Icc_self)
    (by
      convert summable_interpolant_cell_masses hw_sum using 1
      funext (j : ℕ)
      rw [show positiveCell h j = Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) by rfl]
      rw [← integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        by rw [Real.norm_of_nonneg (interpolant_nonneg hh hw_nonneg x)]))]
      exact cell_integral_set hh j)

private theorem cell_tsum_integral {w : Kernel} (hw_sum : Summable w) :
    ∑' j, (w j + w (j + 1)) / 2 = mass w - w 0 / 2 := by
  have hshift : Summable (fun j => w (j + 1)) := by
    simpa [Function.comp_def] using hw_sum.comp_injective Nat.succ_injective
  have htail := hw_sum.sum_add_tsum_nat_add 1
  have hsum : (∑' j, w j) = w 0 + ∑' j, w (j + 1) := by
    simpa using htail.symm
  calc
    ∑' j, (w j + w (j + 1)) / 2 =
        ((∑' j, w j) + (∑' j, w (j + 1))) / 2 := by
      rw [show (fun j => (w j + w (j + 1)) / 2) =
          (fun j => (w j + w (j + 1)) * (2 : ℝ)⁻¹) by
            funext j; ring]
      rw [Summable.tsum_mul_right, Summable.tsum_add hw_sum hshift]
      · ring
      · exact hw_sum.add hshift
    _ = mass w - w 0 / 2 := by
      unfold mass
      rw [hsum]
      ring

theorem integral_interpolant_eq_mass {h : ℝ} {w : Kernel} (hh : 0 < h)
    (hw_nonneg : ∀ j, 0 ≤ w j) (hw_sum : Summable w) :
    ∫ x, interpolant h w x = mass w := by
  have hi : Integrable (interpolant h w) :=
    integrable_interpolant_of_summable hh hw_nonneg hw_sum
  have hpos := positive_integral_hasSum hh hw_nonneg hw_sum
  have hpos' : (∫ x in Ici 0, interpolant h w x) = mass w - w 0 / 2 := by
    rw [← hpos.tsum_eq]
    calc
      ∑' j, ∫ x in positiveCell h j, interpolant h w x =
          ∑' j, (w j + w (j + 1)) / 2 := by
            congr 1
            funext j
            exact cell_integral_set hh j
      _ = mass w - w 0 / 2 := cell_tsum_integral hw_sum
  have hsplit : (∫ x, interpolant h w x) =
      (∫ x in Iio (-h), interpolant h w x) +
        (∫ x in Ici (-h), interpolant h w x) := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hi.integrableOn hi.integrableOn
  have hsplit' : (∫ x in Ici (-h), interpolant h w x) =
      (∫ x in Ico (-h) 0, interpolant h w x) +
        (∫ x in Ici 0, interpolant h w x) := by
    have hd : Disjoint (Ico (-h) 0) (Ici 0) := by
      rw [disjoint_left]
      intro x hx hy
      exact (not_lt_of_ge hy) hx.2
    have hu : Ico (-h) 0 ∪ Ici 0 = Ici (-h) := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx.1
        · exact le_trans (le_of_lt (by linarith : -h < 0)) hx
      · intro hx
        by_cases hx0 : x < 0
        · exact Or.inl ⟨hx, hx0⟩
        · exact Or.inr (le_of_not_gt hx0)
    rw [← hu]
    exact setIntegral_union hd measurableSet_Ici hi.integrableOn hi.integrableOn

  rw [hsplit, hsplit']
  have hz : (∫ x in Iio (-h), interpolant h w x) = 0 := by
    calc
      (∫ x in Iio (-h), interpolant h w x) = ∫ x in Iio (-h), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
        exact interpolant_of_le_neg h w (le_of_lt hx)
      _ = 0 := by simp
  rw [hz, neg_integral_set hh, hpos']
  ring

theorem interpolant_integrableOn_Ici_neg {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    IntegrableOn (interpolant h w) (Ici (-h)) := by
  exact (integrable_interpolant_of_summable hw.h_pos hw.nonnegative hw.summable).integrableOn

theorem interpolant_integral_Ici_neg {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), interpolant h w x = mass w := by
  have hi := integrable_interpolant_of_summable hw.h_pos hw.nonnegative hw.summable
  have hz : (∫ x in Iio (-h), interpolant h w x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact interpolant_of_le_neg h w (le_of_lt hx)
  have hs : (∫ x, interpolant h w x) =
      (∫ x in Iio (-h), interpolant h w x) +
        (∫ x in Ici (-h), interpolant h w x) := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hi.integrableOn hi.integrableOn
  rw [hz, zero_add] at hs
  rw [← hs, integral_interpolant_eq_mass hw.h_pos hw.nonnegative hw.summable]

theorem interpolant_integral_Ici_neg_eq_one {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), interpolant h w x = 1 := by
  rw [interpolant_integral_Ici_neg hw, hw.mass_eq]

private theorem cell_weighted_norm_integral {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) (j : ℕ) :
    ∫ x in positiveCell h j, ‖x * interpolant h w x‖ =
      h / 6 * ((3 * (j : ℝ) + 1) * w j + (3 * (j : ℝ) + 2) * w (j + 1)) := by
  rw [show positiveCell h j = Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) by rfl]
  calc
    _ = ∫ x in Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h),
        x * interpolant h w x := by
      apply setIntegral_congr_fun
        (show MeasurableSet (Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)) by measurability)
      intro x hx
      change ‖x * interpolant h w x‖ = x * interpolant h w x
      rw [Real.norm_of_nonneg]
      exact mul_nonneg (le_trans (mul_nonneg (Nat.cast_nonneg j) (le_of_lt hw.h_pos)) hx.1)
        (interpolant_nonneg hw.h_pos hw.nonnegative x)
    _ = _ := by
      rw [integral_Ico_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (by
        rw [Nat.cast_add, Nat.cast_one, add_mul]
        linarith [hw.h_pos])]
      exact cell_first_moment h w hw.h_pos j

theorem integrable_mul_interpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Integrable (fun x => x * interpolant h w x) := by
  have hpos : IntegrableOn (fun x => x * interpolant h w x) (Ici 0) := by
    rw [← positiveCell_iUnion hw.h_pos]
    exact integrableOn_iUnion_of_summable_integral_norm
      (fun j => by
        dsimp [positiveCell]
        exact IntegrableOn.mono_set
          ((continuous_id.mul (continuous_interpolant hw.h_pos)).continuousOn.integrableOn_Icc
            (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h)) Ico_subset_Icc_self)
      (by
        convert summable_interpolant_cell_first_moments hw using 1
        funext j
        exact cell_weighted_norm_integral hw j)
  have hneg : IntegrableOn (fun x => x * interpolant h w x) (Ico (-h) 0) := by
    exact IntegrableOn.mono_set
      ((continuous_id.mul (continuous_interpolant hw.h_pos)).continuousOn.integrableOn_Icc
        (a := -h) (b := 0)) Ico_subset_Icc_self
  have hleft : IntegrableOn (fun x => x * interpolant h w x) (Ici (-h)) := by
    apply (hneg.union hpos).mono_set
    intro x hx
    by_cases hx0 : x < 0
    · exact Or.inl ⟨hx, hx0⟩
    · exact Or.inr (le_of_not_gt hx0)
  have hzero : IntegrableOn (fun x => x * interpolant h w x) (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx
      simp [interpolant_of_le_neg h w (le_of_lt hx)]
    · exact measurableSet_Iio
  have hall := hzero.union hleft
  rw [show Iio (-h) ∪ Ici (-h) = (Set.univ : Set ℝ) by
    ext x
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ]
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x < -h
      · exact Or.inl hx
      · exact Or.inr (le_of_not_gt hx)] at hall
  exact (integrableOn_univ).mp hall

private def mseq (w : Kernel) (j : ℕ) : ℝ := (j : ℝ) * w j
private def succSeq (w : Kernel) (j : ℕ) : ℝ := w (j + 1)
private def shiftedMseq (w : Kernel) (j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) * w (j + 1)
private def succMomentSeq (w : Kernel) (j : ℕ) : ℝ := (j : ℝ) * w (j + 1)
private def A (w : Kernel) (j : ℕ) : ℝ := (3 * (j : ℝ) + 1) * w j
private def B (w : Kernel) (j : ℕ) : ℝ := (3 * (j : ℝ) + 2) * w (j + 1)
private def C (h : ℝ) (w : Kernel) (j : ℕ) : ℝ := h / 6 * (A w j + B w j)

private theorem tail_mass_tsum {w : Kernel} (hw : Summable w) :
    (∑' j, succSeq w j) = mass w - w 0 := by
  have hs : Summable (succSeq w) := by
    apply (hw.comp_injective Nat.succ_injective).congr
    intro j
    rfl
  have ht := hw.sum_add_tsum_nat_add 1
  have heq : mass w = w 0 + ∑' j, succSeq w j := by
    simpa [mass, succSeq] using ht.symm
  rw [heq]
  ring

private theorem shifted_moment_tsum {w : Kernel} (hw : Summable (mseq w)) :
    (∑' j, shiftedMseq w j) = ∑' j, mseq w j := by
  have ht := hw.sum_add_tsum_nat_add 1
  simpa [mseq, shiftedMseq] using ht

private theorem succ_moment_tsum {w : Kernel} (hw : Summable w)
    (hm : Summable (mseq w)) :
    (∑' j, succMomentSeq w j) =
      (∑' j, mseq w j) - (mass w - w 0) := by
  have hshift : Summable (shiftedMseq w) := by
    apply (hm.comp_injective Nat.succ_injective).congr
    intro j
    dsimp [shiftedMseq]
    rfl
  have hsucc : Summable (succSeq w) := by
    apply (hw.comp_injective Nat.succ_injective).congr
    intro j
    rfl
  have hsub := hshift.sub hsucc
  have hfun : succMomentSeq w = fun j => shiftedMseq w j - succSeq w j := by
    funext j
    dsimp [succMomentSeq, shiftedMseq, succSeq]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
  rw [hfun, hshift.tsum_sub hsucc]
  rw [shifted_moment_tsum hm, tail_mass_tsum hw]

private theorem tsum_A {w : Kernel} (hm : Summable (mseq w)) (hw : Summable w) :
    (∑' j, A w j) = 3 * (∑' j, mseq w j) + mass w := by
  have ha : Summable (A w) := by
    apply (hm.mul_left 3).add hw |>.congr
    intro j
    dsimp [A, mseq]
    ring
  calc
    (∑' j, A w j) = ∑' j, (3 * mseq w j + w j) := by
      congr 1
      funext j; dsimp [A, mseq]; ring
    _ = (∑' j, 3 * mseq w j) + ∑' j, w j :=
      by exact Summable.tsum_add (hm.mul_left 3) hw
    _ = 3 * (∑' j, mseq w j) + mass w := by
      rw [Summable.tsum_mul_left 3 hm]
      rfl

private theorem tsum_B {w : Kernel} (hm : Summable (mseq w)) (hw : Summable w) :
    (∑' j, B w j) = 3 * (∑' j, mseq w j) - mass w + w 0 := by
  have hsm : Summable (succMomentSeq w) := by
    exact (hm.comp_injective Nat.succ_injective).sub
      (hw.comp_injective Nat.succ_injective) |>.congr (by
        intro j; dsimp [succMomentSeq, mseq]
        norm_num [Nat.cast_add, Nat.cast_one, add_mul])
  have hs : Summable (succSeq w) := by
    apply (hw.comp_injective Nat.succ_injective).congr
    intro j
    rfl
  have hb : Summable (B w) := by
    apply ((hsm.mul_left 3).add (hs.mul_left 2)).congr
    intro j; dsimp [B, succMomentSeq, succSeq]; ring
  calc
    (∑' j, B w j) = ∑' j, (3 * succMomentSeq w j + 2 * succSeq w j) := by
      congr 1
      funext j; dsimp [B, succMomentSeq, succSeq]; ring
    _ = (∑' j, 3 * succMomentSeq w j) + ∑' j, 2 * succSeq w j :=
      by exact Summable.tsum_add (hsm.mul_left 3) (hs.mul_left 2)
    _ = 3 * (∑' j, succMomentSeq w j) + 2 * (∑' j, succSeq w j) := by
      rw [Summable.tsum_mul_left 3 hsm, Summable.tsum_mul_left 2 hs]
    _ = 3 * (∑' j, mseq w j) - mass w + w 0 := by
      rw [succ_moment_tsum hw hm, tail_mass_tsum hw]
      ring

private theorem tsum_C {h : ℝ} {w : Kernel} (hm : Summable (mseq w)) (hw : Summable w) :
    (∑' j, C h w j) = h * (∑' j, mseq w j) + h * w 0 / 6 := by
  have hA := tsum_A hm hw
  have hB := tsum_B hm hw
  have hA_sum : Summable (A w) := by
    apply (hm.mul_left 3).add hw |>.congr
    intro j; dsimp [A, mseq]; ring
  have hB_sum : Summable (B w) := by
    have hs : Summable (succSeq w) := by
      apply (hw.comp_injective Nat.succ_injective).congr
      intro j; rfl
    have hsm : Summable (succMomentSeq w) := by
      exact (hm.comp_injective Nat.succ_injective).sub
        (hw.comp_injective Nat.succ_injective) |>.congr (by
          intro j; dsimp [succMomentSeq, mseq]
          norm_num [Nat.cast_add, Nat.cast_one, add_mul])
    apply ((hsm.mul_left 3).add (hs.mul_left 2)).congr
    intro j; dsimp [B, succMomentSeq, succSeq]; ring
  calc
    (∑' j, C h w j) = ∑' j, h / 6 * (A w j + B w j) := by rfl
    _ = h / 6 * (∑' j, (A w j + B w j)) := by
      exact Summable.tsum_mul_left (h / 6) (hA_sum.add hB_sum)
    _ = h / 6 * ((∑' j, A w j) + ∑' j, B w j) := by
      rw [(hA_sum.tsum_add hB_sum)]
    _ = h * (∑' j, mseq w j) + h * w 0 / 6 := by rw [hA, hB]; ring

private theorem summable_C {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Summable (C h w) := by
  convert summable_interpolant_cell_first_moments hw using 1
  funext j
  rfl

private theorem weighted_integrable_positive {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => x * interpolant h w x) (Ici 0) := by
  rw [← positiveCell_iUnion hw.h_pos]
  apply integrableOn_iUnion_of_summable_integral_norm
    (fun j => by
      dsimp [positiveCell]
      exact IntegrableOn.mono_set
        ((continuous_id.mul (continuous_interpolant hw.h_pos)).continuousOn.integrableOn_Icc
          (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h)) Ico_subset_Icc_self)
  have hnorm : Summable (fun j => ∫ x in positiveCell h j,
      ‖x * interpolant h w x‖) :=
    (summable_C hw).congr (fun j => (cell_weighted_norm_integral hw j).symm)
  exact hnorm

private theorem weighted_hasSum_positive {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    HasSum (fun j => ∫ x in positiveCell h j, x * interpolant h w x)
      (∫ x in Ici 0, x * interpolant h w x) := by
  rw [← positiveCell_iUnion hw.h_pos]
  apply MeasureTheory.hasSum_integral_iUnion
    (fun j => by dsimp [positiveCell]; measurability)
    (positiveCell_pairwise hw.h_pos)
  have hpos := weighted_integrable_positive hw
  rw [← positiveCell_iUnion hw.h_pos] at hpos
  exact hpos

private theorem initial_union {h : ℝ} (hh : 0 < h) :
    Ico (-h) 0 ∪ Ici 0 = Ici (-h) := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact hx.1
    · exact le_trans (le_of_lt (by linarith [hh] : -h < 0)) hx
  · intro hx
    by_cases hx0 : x < 0
    · exact Or.inl ⟨hx, hx0⟩
    · exact Or.inr (le_of_not_gt hx0)

theorem interpolant_firstMoment_integrableOn_Ici_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => x * interpolant h w x) (Ici (-h)) := by
  have hneg : IntegrableOn (fun x => x * interpolant h w x) (Ico (-h) 0) :=
    IntegrableOn.mono_set
      ((continuous_id.mul (continuous_interpolant hw.h_pos)).continuousOn.integrableOn_Icc
        (a := -h) (b := 0)) Ico_subset_Icc_self
  have hpos := weighted_integrable_positive hw
  rw [← initial_union hw.h_pos]
  exact hneg.union hpos

theorem interpolant_firstMoment_Ici_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), x * interpolant h w x = h * firstMoment w := by
  rw [← initial_union hw.h_pos]
  have hd : Disjoint (Ico (-h) 0) (Ici 0) := by
    rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy) hx.2
  have hneg : IntegrableOn (fun x : ℝ => x * interpolant h w x) (Ico (-h) 0) volume :=
    IntegrableOn.mono_set
      ((continuous_id.mul (continuous_interpolant hw.h_pos)).continuousOn.integrableOn_Icc
        (a := -h) (b := 0)) Ico_subset_Icc_self
  have hpos : IntegrableOn (fun x : ℝ => x * interpolant h w x) (Ici 0) volume :=
    weighted_integrable_positive hw
  rw [setIntegral_union (μ := volume) hd measurableSet_Ici hneg hpos]
  rw [neg_weighted_integral_set hw.h_pos]
  rw [← (weighted_hasSum_positive hw).tsum_eq]
  calc
    _ = -(h * w 0) / 6 + ∑' j, C h w j := by
      congr 1
      apply congrArg tsum
      funext j
      exact cell_weighted_integral_set hw.h_pos j
    _ = h * firstMoment w := by
      rw [tsum_C hw.summable_firstMoment' hw.summable]
      simp only [firstMoment, mseq]
      ring

theorem interpolant_firstMoment_Ici_neg_eq
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), x * interpolant h w x = L := by
  rw [interpolant_firstMoment_Ici_neg hw]
  exact hw.scaled_firstMoment_eq

theorem integral_mul_interpolant_eq_scaled_firstMoment
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x, x * interpolant h w x = h * firstMoment w := by
  have hi := integrable_mul_interpolant hw
  have hz : (∫ x in Iio (-h), x * interpolant h w x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    simp [interpolant_of_le_neg h w (le_of_lt hx)]
  have hs : (∫ x, x * interpolant h w x) =
      (∫ x in Iio (-h), x * interpolant h w x) +
        (∫ x in Ici (-h), x * interpolant h w x) := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hi.integrableOn hi.integrableOn
  rw [hs, hz, zero_add, interpolant_firstMoment_Ici_neg hw]

namespace IsAdmissible

theorem integral_interpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    ∫ x, interpolant h w x = 1 := by
  rw [integral_interpolant_eq_mass hw.h_pos hw.nonnegative hw.summable, hw.mass_eq]

theorem integral_mul_interpolant
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x, x * interpolant h w x = L := by
  rw [integral_mul_interpolant_eq_scaled_firstMoment hw]
  exact hw.scaled_firstMoment_eq

end IsAdmissible

end RayleighKernel.Discrete
