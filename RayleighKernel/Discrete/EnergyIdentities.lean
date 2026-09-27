import RayleighKernel.Discrete.GlobalIntegrals
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.SuccPred.IntervalSucc

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace RayleighKernel.Discrete

private def energyCell (h : ℝ) (j : ℕ) : Set ℝ :=
  Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)

private theorem energyCell_iUnion {h : ℝ} (hh : 0 < h) :
    (⋃ j : ℕ, energyCell h j) = Ici 0 := by
  let f : ℕ → ℝ := fun j => (j : ℝ) * h
  have hmono : ∀ j, f 0 ≤ f j := by
    intro j; dsimp [f]; norm_num; positivity
  have hunbdd : ¬ BddAbove (Set.range f) := by
    intro hb
    obtain ⟨B, hB⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt (B / h)
    have hBn : B < (n : ℝ) * h := by
      calc
        B = (B / h) * h := by field_simp
        _ < (n : ℝ) * h := mul_lt_mul_of_pos_right hn hh
    exact (not_lt_of_ge (hB ⟨n, rfl⟩)) hBn
  simpa [f, energyCell, Nat.cast_add, add_mul] using
    (iUnion_Ico_map_succ_eq_Ici (α := ℕ) (f := f) hmono hunbdd)

private theorem energyCell_pairwise {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (fun j : ℕ => energyCell h j)) := by
  let f : ℕ → ℝ := fun j => (j : ℝ) * h
  have hm : Monotone f := by
    intro a b hab; dsimp [f]; gcongr
  simpa [f, energyCell, Nat.cast_add, add_mul] using hm.pairwise_disjoint_on_Ico_succ

private theorem ae_ne (a : ℝ) : ∀ᵐ x : ℝ, x ≠ a := by
  rw [ae_iff]
  simp

private theorem deriv_sq_neg_ae {h : ℝ} {w : Kernel} (hh : 0 < h) :
    (∀ᵐ x : ℝ ∂volume.restrict (Ico (-h) 0),
      (deriv (interpolant h w) x) ^ 2 = (difference w 0) ^ 2 / h ^ 4) := by
  apply (ae_restrict_iff' measurableSet_Ico).2
  filter_upwards [ae_ne 0, ae_ne (-h)] with x hx0 hxh
  intro hx
  have hd := hasDerivAt_interpolant_neg hh (w := w)
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxh), hx.2⟩
  rw [hd.deriv]
  simp only [difference_zero]
  field_simp

private theorem deriv_sq_cell_ae {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    (∀ᵐ x : ℝ ∂volume.restrict (energyCell h j),
      (deriv (interpolant h w) x) ^ 2 = (difference w (j + 1)) ^ 2 / h ^ 4) := by
  apply (ae_restrict_iff' measurableSet_Ico).2
  filter_upwards [ae_ne (((j : ℝ) * h)),
    ae_ne (((j + 1 : ℕ) : ℝ) * h)] with x hxstart hxend
  intro hx
  have hd := hasDerivAt_interpolant_cell hh j (w := w)
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxstart),
      hx.2⟩
  rw [hd.deriv]
  simp only [difference_succ]
  field_simp

private theorem neg_energyCell {h : ℝ} {w : Kernel} (hh : 0 < h) :
    ∫ x in Ico (-h) 0, (deriv (interpolant h w) x) ^ 2 =
      (difference w 0) ^ 2 / h ^ 3 := by
  rw [integral_congr_ae (deriv_sq_neg_ae (h := h) (w := w) hh)]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt hh]
  ring

private theorem cell_energyCell {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    ∫ x in energyCell h j, (deriv (interpolant h w) x) ^ 2 =
      (difference w (j + 1)) ^ 2 / h ^ 3 := by
  rw [integral_congr_ae (deriv_sq_cell_ae (h := h) (w := w) hh j)]
  unfold energyCell
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by
    rw [Nat.cast_add, Nat.cast_one, add_mul]
    linarith)]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt hh]
  norm_num [Nat.cast_add, Nat.cast_one, add_mul]

private theorem summable_cell_energy {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Summable (fun j => (difference w (j + 1)) ^ 2 / h ^ 3) := by
  have hs : Summable (fun j => (difference w (j + 1)) ^ 2) :=
    hw.summable_difference_sq.comp_injective Nat.succ_injective
  simpa [div_eq_mul_inv] using hs.mul_right (h ^ 3)⁻¹

private theorem integrableOn_deriv_sq_positive {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2) (Ici 0) := by
  rw [← energyCell_iUnion hw.h_pos]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro j
    have hd : ∀ᵐ x : ℝ ∂volume.restrict (energyCell h j),
        (deriv (interpolant h w) x) ^ 2 =
          (difference w (j + 1)) ^ 2 / h ^ 4 := deriv_sq_cell_ae hw.h_pos j
    have hc : IntegrableOn (fun _ : ℝ =>
        (difference w (j + 1)) ^ 2 / h ^ 4) (energyCell h j) volume :=
      IntegrableOn.mono_set
        ((continuous_const : Continuous (fun _ : ℝ =>
          (difference w (j + 1)) ^ 2 / h ^ 4)).continuousOn.integrableOn_Icc
          (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h))
        (by exact Ico_subset_Icc_self)
    have hd' : (fun _ : ℝ => (difference w (j + 1)) ^ 2 / h ^ 4) =ᵐ[
        volume.restrict (energyCell h j)] (fun x => (deriv (interpolant h w) x) ^ 2) := by
      filter_upwards [hd] with x hx
      exact hx.symm
    exact hc.integrable.congr hd'
  · apply (summable_cell_energy hw).congr
    intro j
    rw [← cell_energyCell hw.h_pos j]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      (Real.norm_of_nonneg (sq_nonneg _)).symm)

private theorem initial_union {h : ℝ} (hh : 0 < h) : Ico (-h) 0 ∪ Ici 0 = Ici (-h) := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact hx.1
    · exact le_trans (by linarith [hh] : -h ≤ 0) hx
  · intro hx
    by_cases hx0 : x < 0
    · exact Or.inl ⟨hx, hx0⟩
    · exact Or.inr (le_of_not_gt hx0)

/-- The squared derivative of the interpolant is integrable on its interpolation domain. -/
theorem integrableOn_sq_deriv_interpolant_Ici_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2) (Ici (-h)) := by
  rw [← initial_union hw.h_pos]
  have hn : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Ico (-h) 0) volume := by
    have hc : IntegrableOn (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4)
        (Ico (-h) 0) volume := IntegrableOn.mono_set
      ((continuous_const : Continuous (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4)).continuousOn
        |>.integrableOn_Icc (a := -h) (b := 0)) Ico_subset_Icc_self
    have hd' : (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4) =ᵐ[
        volume.restrict (Ico (-h) 0)] (fun x => (deriv (interpolant h w) x) ^ 2) := by
      filter_upwards [deriv_sq_neg_ae (h := h) (w := w) hw.h_pos] with x hx
      exact hx.symm
    exact hc.integrable.congr hd'
  exact hn.union (integrableOn_deriv_sq_positive hw)

/-- The exact derivative-energy identity on the interpolation domain. -/
theorem integral_sq_deriv_interpolant_Ici_neg
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), (deriv (interpolant h w) x) ^ 2 =
      differenceEnergy w / h ^ 3 := by
  rw [← initial_union hw.h_pos]
  have hd : Disjoint (Ico (-h) 0) (Ici 0) := by
    rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy) hx.2
  have hn : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Ico (-h) 0) volume := by
    have hc : IntegrableOn (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4)
        (Ico (-h) 0) volume := IntegrableOn.mono_set
      ((continuous_const : Continuous (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4)).continuousOn
        |>.integrableOn_Icc (a := -h) (b := 0)) Ico_subset_Icc_self
    have hd' : (fun _ : ℝ => (difference w 0) ^ 2 / h ^ 4) =ᵐ[
        volume.restrict (Ico (-h) 0)] (fun x => (deriv (interpolant h w) x) ^ 2) :=
      by
        filter_upwards [deriv_sq_neg_ae (h := h) (w := w) hw.h_pos] with x hx
        exact hx.symm
    exact hc.integrable.congr hd'
  have hp := integrableOn_deriv_sq_positive hw
  rw [setIntegral_union (μ := volume) hd measurableSet_Ici hn hp]
  rw [neg_energyCell hw.h_pos]
  have hp' := integrableOn_deriv_sq_positive hw
  rw [← energyCell_iUnion hw.h_pos] at hp'
  have hs := MeasureTheory.hasSum_integral_iUnion
    (fun j => by dsimp [energyCell]; measurability)
    (energyCell_pairwise hw.h_pos)
    hp'
  have hsum : (∫ x in Ici 0, (deriv (interpolant h w) x) ^ 2) =
      ∑' j, ∫ x in energyCell h j, (deriv (interpolant h w) x) ^ 2 := by
    rw [energyCell_iUnion hw.h_pos] at hs
    exact hs.tsum_eq.symm
  calc
    _ = (difference w 0) ^ 2 / h ^ 3 +
        ∑' j, (difference w (j + 1)) ^ 2 / h ^ 3 := by
      rw [hsum]
      congr 1
      apply congrArg tsum
      funext j
      exact cell_energyCell hw.h_pos j
    _ = differenceEnergy w / h ^ 3 := by
      have ht := hw.summable_difference_sq.sum_add_tsum_nat_add 1
      rw [differenceEnergy]
      simp only [difference_zero] at ht ⊢
      have hs : Summable (fun j => (difference w (j + 1)) ^ 2) := by
        simpa [Function.comp_def] using
          hw.summable_difference_sq.comp_injective Nat.succ_injective
      rw [show (∑' j, (difference w (j + 1)) ^ 2 / h ^ 3) =
           (∑' j, (difference w (j + 1)) ^ 2) * (h ^ 3)⁻¹ by
             rw [show (fun j => (difference w (j + 1)) ^ 2 / h ^ 3) =
                 (fun j => (difference w (j + 1)) ^ 2 * (h ^ 3)⁻¹) by
                   funext j; rfl]
             exact Summable.tsum_mul_right (h ^ 3)⁻¹ hs]
      simp only [div_eq_mul_inv]
      rw [← ht]
      norm_num
      ring

private theorem deriv_sq_eq_zero_of_lt_neg {h : ℝ} {w : Kernel} {x : ℝ}
    (hx : x < -h) : (deriv (interpolant h w) x) ^ 2 = 0 := by
  have hd : HasDerivAt (interpolant h w) 0 x := by
    apply (hasDerivAt_const x 0).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact interpolant_of_le_neg h w (le_of_lt hy)
  rw [hd.deriv]
  simp

private theorem integral_sq_affine (a b A B : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, (A + (x - a) * B) ^ 2 =
      (b - a) * A ^ 2 + (b - a) ^ 2 * A * B + (b - a) ^ 3 * B ^ 2 / 3 := by
  let F : ℝ → ℝ := fun x =>
    (A - a * B) ^ 2 * x + (A - a * B) * B * x ^ 2 + B ^ 2 * x ^ 3 / 3
  have hF : ∀ x, HasDerivAt F ((A + (x - a) * B) ^ 2) x := by
    intro x
    dsimp [F]
    convert (((hasDerivAt_id x).const_mul ((A - a * B) ^ 2)).add
      (((hasDerivAt_id x).pow 2).const_mul ((A - a * B) * B))).add
      (((hasDerivAt_id x).pow 3).const_mul (B ^ 2 / 3)) using 1
    · funext y; simp [Function.id_def]; ring
    · simp; ring
  have hcont : ContinuousOn F (Icc a b) := by dsimp [F]; fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => (A + (x - a) * B) ^ 2)
      volume a b := by
    apply (show Continuous (fun x : ℝ => (A + (x - a) * B) ^ 2) by fun_prop).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont]
  · dsimp [F]; ring
  · intro x hx; exact hF x
  · exact hint

private theorem neg_sq_set {h : ℝ} {w : Kernel} (hh : 0 < h) :
    ∫ x in Ico (-h) 0, (interpolant h w x) ^ 2 = (w 0) ^ 2 / (3 * h) := by
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have H := integral_sq_affine (-h) 0 0 (w 0 / h ^ 2) (by linarith)
  convert H using 1
  · apply intervalIntegral.integral_congr
    intro x hx
    change (interpolant h w x) ^ 2 = _
    have hle : -h ≤ (0 : ℝ) := by linarith
    rw [uIcc_of_le hle] at hx
    by_cases he : x = -h
    · subst x; simp [interpolant]
    · rw [interpolant_neg_interval hh ⟨lt_of_le_of_ne hx.1 (Ne.symm he), hx.2⟩]
      ring
  · field_simp [ne_of_gt hh]; ring

private theorem cell_sq_set {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    ∫ x in energyCell h j, (interpolant h w x) ^ 2 =
      ((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) / (3 * h) := by
  unfold energyCell
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by
    rw [Nat.cast_add, Nat.cast_one, add_mul]; linarith)]
  have H := integral_sq_affine ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)
      (w j / h) ((w (j + 1) - w j) / h ^ 2) (by
        rw [Nat.cast_add, Nat.cast_one, add_mul]; linarith)
  convert H using 1
  · apply intervalIntegral.integral_congr
    intro x hx
    change (interpolant h w x) ^ 2 = _
    have hle : (j : ℝ) * h ≤ (((j + 1 : ℕ) : ℝ) * h) := by
      rw [Nat.cast_add, Nat.cast_one, add_mul]; linarith
    rw [uIcc_of_le hle] at hx
    by_cases he : x = (((j + 1 : ℕ) : ℝ) * h)
    · subst x
      rw [interpolant_node hh (j + 1)]
      field_simp [ne_of_gt hh]
      norm_num [Nat.cast_add, Nat.cast_one, add_mul]
    · rw [interpolant_cell hh j ⟨hx.1, lt_of_le_of_ne hx.2 he⟩]
      dsimp; ring
  · field_simp [ne_of_gt hh]
    norm_num [Nat.cast_add, Nat.cast_one, add_mul]
    ring

private theorem summable_adjacent_product {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) : Summable (fun j : ℕ => w j * w (j + 1)) := by
  have hshift : Summable (fun j : ℕ => (w (j + 1)) ^ 2) := by
    apply hw.summable_sq.comp_injective Nat.succ_injective |>.congr
    intro j; rfl
  apply (hw.summable_sq.add hshift).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  have hs := sq_nonneg (|w j| - |w (j + 1)|)
  have hsq₁ : |w j| ^ 2 = (w j) ^ 2 := sq_abs (w j)
  have hsq₂ : |w (j + 1)| ^ 2 = (w (j + 1)) ^ 2 := sq_abs (w (j + 1))
  nlinarith

private theorem summable_cell_sq {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Summable (fun j : ℕ =>
      ((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) / (3 * h)) := by
  have hp := summable_adjacent_product hw
  have hs : Summable (fun j : ℕ => (w (j + 1)) ^ 2) :=
    hw.summable_sq.comp_injective Nat.succ_injective |>.congr (by intro j; rfl)
  have ha : Summable (fun j : ℕ =>
      (w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) := by
    simpa [Function.comp_def] using (hw.summable_sq.add hp).add hs
  simpa [div_eq_mul_inv] using ha.mul_right (3 * h)⁻¹

private theorem integrable_sq_positive {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => (interpolant h w x) ^ 2) (Ici 0) := by
  rw [← energyCell_iUnion hw.h_pos]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro j
    exact IntegrableOn.mono_set
      ((continuous_interpolant hw.h_pos).pow 2 |>.continuousOn.integrableOn_Icc
        (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h)) Ico_subset_Icc_self
  · apply (summable_cell_sq hw).congr
    intro j
    rw [← cell_sq_set hw.h_pos j]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      (Real.norm_of_nonneg (sq_nonneg _)).symm)

private theorem differenceEnergy_eq {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    differenceEnergy w = 2 * squareEnergy w - 2 * ∑' j, w j * w (j + 1) := by
  have hp := summable_adjacent_product hw
  have hd := hw.summable_difference_sq.sum_add_tsum_nat_add 1
  have hs : Summable (fun j : ℕ => (w j) ^ 2) := hw.summable_sq
  have ht : (∑' j, (difference w (j + 1)) ^ 2) =
      ∑' j, ((w (j + 1)) ^ 2 - 2 * w j * w (j + 1) + (w j) ^ 2) := by
    apply tsum_congr
    intro j
    rw [difference_succ]
    ring
  have hd' : (difference w 0) ^ 2 + ∑' j, (difference w (j + 1)) ^ 2 =
      ∑' j, (difference w j) ^ 2 := by
    simpa [difference_zero] using hd
  rw [differenceEnergy, squareEnergy]
  rw [← hd', ht]
  have hshift : Summable (fun j : ℕ => (w (j + 1)) ^ 2) :=
    hs.comp_injective Nat.succ_injective |>.congr (by intro j; rfl)
  have hm : Summable (fun j => 2 * w j * w (j + 1)) := by
    exact (hp.mul_left 2).congr (by intro j; ring)
  have hsum : (∑' j, ((w (j + 1)) ^ 2 - 2 * w j * w (j + 1) + (w j) ^ 2)) =
      (∑' j, (w (j + 1)) ^ 2) - 2 * (∑' j, w j * w (j + 1)) +
        ∑' j, (w j) ^ 2 := by
    calc
      _ = ∑' j, (((w (j + 1)) ^ 2 - 2 * w j * w (j + 1)) + (w j) ^ 2) := by
        apply congrArg tsum
        funext j
        ring
      _ = (∑' j, ((w (j + 1)) ^ 2 - 2 * w j * w (j + 1))) + ∑' j, (w j) ^ 2 :=
        Summable.tsum_add (hshift.sub hm) hs
      _ = _ := by
        rw [Summable.tsum_sub hshift hm]
        have hmul : (∑' j, 2 * w j * w (j + 1)) =
            2 * (∑' j, w j * w (j + 1)) := by
          calc
            _ = ∑' j, (2 : ℝ) * (w j * w (j + 1)) := by
              apply congrArg tsum
              funext j
              ring
            _ = _ := Summable.tsum_mul_left 2 hp
        rw [hmul]
  rw [hsum]
  simp only [difference_zero]
  have htail : (w 0) ^ 2 + ∑' j, (w (j + 1)) ^ 2 = ∑' j, (w j) ^ 2 := by
    simpa using hw.summable_sq.sum_add_tsum_nat_add 1
  rw [← htail]
  ring

theorem differenceEnergy_le_four_mul_squareEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    differenceEnergy w ≤ 4 * squareEnergy w := by
  have hp := summable_adjacent_product hw
  have hs := hw.summable_sq
  have hshift : Summable (fun j : ℕ => (w (j + 1)) ^ 2) :=
    hs.comp_injective Nat.succ_injective |>.congr (by intro j; rfl)
  have hsum : Summable (fun j : ℕ => ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2) := by
    apply (hs.add hshift).mul_right (2 : ℝ)⁻¹ |>.congr
    intro j
    field_simp
  have hterm : ∀ j : ℕ,
      -(w j * w (j + 1)) ≤ ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2 := by
    intro j
    nlinarith [sq_nonneg (w j + w (j + 1))]
  have hi : -(∑' j, w j * w (j + 1)) ≤
      ∑' j, ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2 := by
    rw [← tsum_neg]
    exact hp.neg.tsum_le_tsum hterm hsum
  have htail := hs.sum_add_tsum_nat_add 1
  have hright : (∑' j, ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2) ≤ squareEnergy w := by
    rw [show (∑' j, ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2) =
        (squareEnergy w + (∑' j, (w (j + 1)) ^ 2)) / 2 by
      rw [show (fun j : ℕ => ((w j) ^ 2 + (w (j + 1)) ^ 2) / 2) =
          (fun j : ℕ => ((w j) ^ 2 + (w (j + 1)) ^ 2) * (2 : ℝ)⁻¹) by
            funext j; rfl]
      rw [Summable.tsum_mul_right (2 : ℝ)⁻¹ (hs.add hshift)]
      rw [Summable.tsum_add hs hshift]
      simp only [div_eq_mul_inv]
      rw [show squareEnergy w = ∑' b, w b ^ 2 by rfl]
    ]
    rw [show squareEnergy w = (w 0) ^ 2 + ∑' j, (w (j + 1)) ^ 2 by
      simpa [squareEnergy] using htail.symm]
    nlinarith [sq_nonneg (w 0)]
  have hprod : -(∑' j, w j * w (j + 1)) ≤ squareEnergy w := hi.trans hright
  rw [differenceEnergy_eq hw]
  nlinarith

theorem integrable_sq_interpolant_Ici_neg {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    IntegrableOn (fun x => (interpolant h w x) ^ 2) (Ici (-h)) := by
  have hn : IntegrableOn (fun x => (interpolant h w x) ^ 2) (Ico (-h) 0) :=
    IntegrableOn.mono_set
      ((continuous_interpolant hw.h_pos).pow 2 |>.continuousOn.integrableOn_Icc
        (a := -h) (b := 0)) Ico_subset_Icc_self
  have hp := integrable_sq_positive hw
  rw [← initial_union hw.h_pos]
  exact hn.union hp

theorem integral_sq_interpolant_Ici_neg {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), (interpolant h w x) ^ 2 =
      squareEnergy w / h - differenceEnergy w / (6 * h) := by
  rw [← initial_union hw.h_pos]
  have hn : IntegrableOn (fun x : ℝ => (interpolant h w x) ^ 2) (Ico (-h) 0) :=
    IntegrableOn.mono_set
      ((continuous_interpolant hw.h_pos).pow 2 |>.continuousOn.integrableOn_Icc
        (a := -h) (b := 0)) Ico_subset_Icc_self
  have hp := integrable_sq_positive hw
  have hd : Disjoint (Ico (-h) 0) (Ici 0) := by
    rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy) hx.2
  rw [setIntegral_union (μ := volume) hd measurableSet_Ici hn hp]
  rw [neg_sq_set hw.h_pos]
  have hp' := hp
  rw [← energyCell_iUnion hw.h_pos] at hp'
  have hs := MeasureTheory.hasSum_integral_iUnion
    (fun j => by dsimp [energyCell]; measurability)
    (energyCell_pairwise hw.h_pos) hp'
  have hsum : (∫ x in Ici 0, (interpolant h w x) ^ 2) =
      ∑' j, ∫ x in energyCell h j, (interpolant h w x) ^ 2 := by
    rw [energyCell_iUnion hw.h_pos] at hs
    exact hs.tsum_eq.symm
  rw [hsum]
  rw [show ∑' j, ∫ x in energyCell h j, (interpolant h w x) ^ 2 =
      ∑' j, (((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) / (3 * h)) by
    apply congrArg tsum
    funext j
    exact cell_sq_set hw.h_pos j]
  have hp := summable_adjacent_product hw
  have hs := hw.summable_sq
  have hshift : Summable (fun j : ℕ => (w (j + 1)) ^ 2) :=
    hs.comp_injective Nat.succ_injective |>.congr (by intro j; rfl)
  have hcell := summable_cell_sq hw
  have htail := hs.sum_add_tsum_nat_add 1
  have htail' : (∑' j, (w (j + 1)) ^ 2) = squareEnergy w - (w 0)^2 := by
    unfold squareEnergy
    have := htail
    norm_num at this
    linarith
  have hcell' : (∑' j, (((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) / (3 * h))) =
      (squareEnergy w + (∑' j, w j * w (j + 1)) +
        (∑' j, (w (j + 1)) ^ 2)) / (3 * h) := by
    have hnum : Summable (fun j => (w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) :=
      (hs.add hp).add hshift
    rw [show (fun j => ((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) / (3 * h)) =
        (fun j => ((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2) * (3 * h)⁻¹) by
          funext j; rfl]
    rw [Summable.tsum_mul_right (3 * h)⁻¹ hnum]
    rw [show (∑' j, ((w j) ^ 2 + w j * w (j + 1) + (w (j + 1)) ^ 2)) =
        squareEnergy w + (∑' j, w j * w (j + 1)) + ∑' j, (w (j + 1)) ^ 2 by
      rw [Summable.tsum_add (hs.add hp) hshift, Summable.tsum_add hs hp]
      rfl]
    simp [div_eq_mul_inv]
  rw [hcell']
  rw [htail']
  rw [differenceEnergy_eq hw]
  field_simp [ne_of_gt hw.h_pos]
  ring

theorem integrable_sq_interpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Integrable (fun x => (interpolant h w x) ^ 2) := by
  have hl : IntegrableOn (fun x => (interpolant h w x) ^ 2) (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx; simp [interpolant_of_le_neg h w (le_of_lt hx)]
    · exact measurableSet_Iio
  have hr := integrable_sq_interpolant_Ici_neg hw
  have hall := hl.union hr
  rw [show Iio (-h) ∪ Ici (-h) = (Set.univ : Set ℝ) by
    ext x; simp only [mem_union, mem_Iio, mem_Ici, mem_univ]
    constructor
    · intro _; trivial
    · intro _; by_cases hx : x < -h
      · exact Or.inl hx
      · exact Or.inr (le_of_not_gt hx)] at hall
  exact (integrableOn_univ).mp hall

theorem integral_sq_interpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    ∫ x, (interpolant h w x) ^ 2 =
      squareEnergy w / h - differenceEnergy w / (6 * h) := by
  have hr := integral_sq_interpolant_Ici_neg hw
  have hl : IntegrableOn (fun x => (interpolant h w x) ^ 2) (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx; simp [interpolant_of_le_neg h w (le_of_lt hx)]
    · exact measurableSet_Iio
  have hsplit : (∫ x, (interpolant h w x) ^ 2) =
      (∫ x in Iio (-h), (interpolant h w x) ^ 2) +
        (∫ x in Ici (-h), (interpolant h w x) ^ 2) := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici hl
      (integrable_sq_interpolant_Ici_neg hw)
  rw [hsplit]
  have hz : (∫ x in Iio (-h), (interpolant h w x) ^ 2) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    simp [interpolant_of_le_neg h w (le_of_lt hx)]
  rw [hz, zero_add, hr]

theorem integrable_sq_deriv_interpolant
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    Integrable (fun x => (deriv (interpolant h w) x) ^ 2) := by
  have hleft : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx
      exact (deriv_sq_eq_zero_of_lt_neg hx).symm
    · exact measurableSet_Iio
  have hright : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Ici (-h)) := integrableOn_sq_deriv_interpolant_Ici_neg hw
  have hall := hleft.union hright
  have hunion : Iio (-h) ∪ Ici (-h) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : x < -h
      · exact Or.inl hx
      · exact Or.inr (le_of_not_gt hx)
  have huniv : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Set.univ : Set ℝ) := by
    rw [← hunion]
    exact hall
  exact (integrableOn_univ).mp huniv

theorem integral_sq_deriv_interpolant
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x, (deriv (interpolant h w) x) ^ 2 = differenceEnergy w / h ^ 3 := by
  have hi := integrable_sq_deriv_interpolant hw
  have hleft : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Iio (-h)) := by
    apply IntegrableOn.congr_fun (integrableOn_zero (μ := volume))
    · intro x hx
      exact (deriv_sq_eq_zero_of_lt_neg hx).symm
    · exact measurableSet_Iio
  have hright : IntegrableOn (fun x => (deriv (interpolant h w) x) ^ 2)
      (Ici (-h)) := integrableOn_sq_deriv_interpolant_Ici_neg hw
  have hsplit : (∫ x, (deriv (interpolant h w) x) ^ 2) =
      (∫ x in Iio (-h), (deriv (interpolant h w) x) ^ 2) +
        (∫ x in Ici (-h), (deriv (interpolant h w) x) ^ 2) := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hleft hright
  have hzero : (∫ x in Iio (-h), (deriv (interpolant h w) x) ^ 2) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact deriv_sq_eq_zero_of_lt_neg hx
  rw [hsplit, hzero, zero_add, integral_sq_deriv_interpolant_Ici_neg hw]

/-- Auxiliary quotient over the full interpolation domain `[-h, ∞)`. -/
def interpolationRayleighQuotient (h : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in Ici (-h), (deriv f x) ^ 2) /
    (∫ x in Ici (-h), f x ^ 2)

theorem integral_sq_interpolant_Ici_neg_eq_factor
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    ∫ x in Ici (-h), (interpolant h w x) ^ 2 =
      squareEnergy w / h * (1 - rayleighQuotient w / 6) := by
  rw [integral_sq_interpolant_Ici_neg hw]
  unfold rayleighQuotient
  field_simp [ne_of_gt hw.h_pos, hw.squareEnergy_ne_zero]

theorem interpolationRayleighQuotient_factor_pos
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    0 < 1 - rayleighQuotient w / 6 := by
  have hq : rayleighQuotient w ≤ 4 := by
    unfold rayleighQuotient
    exact (div_le_iff₀ hw.squareEnergy_pos).2
      (differenceEnergy_le_four_mul_squareEnergy hw)
  nlinarith

theorem interpolationRayleighQuotient_interpolant
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    interpolationRayleighQuotient h (interpolant h w) =
      (h⁻¹) ^ 2 * rayleighQuotient w /
        (1 - rayleighQuotient w / 6) := by
  unfold interpolationRayleighQuotient
  rw [integral_sq_deriv_interpolant_Ici_neg hw,
    integral_sq_interpolant_Ici_neg_eq_factor hw]
  have hfactor : 1 - rayleighQuotient w / 6 ≠ 0 :=
    ne_of_gt (interpolationRayleighQuotient_factor_pos hw)
  field_simp [ne_of_gt hw.h_pos, hw.squareEnergy_ne_zero, hfactor]
  unfold rayleighQuotient
  congr 1
  field_simp [hw.squareEnergy_ne_zero]

end RayleighKernel.Discrete
