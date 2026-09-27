import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace RayleighKernel.Discrete

/-- Trapezoidal integration on a full mesh followed by one shortened interval. -/
def shortenedTrapezoidalIntegral
    (f : ℝ → ℝ) (N : ℕ) (a h r : ℝ) : ℝ :=
  trapezoidal_integral f N a (a + (N : ℝ) * h) +
    trapezoidal_integral f 1
      (a + (N : ℝ) * h)
      (a + (N : ℝ) * h + r)

theorem shortenedTrapezoidalIntegral_sub_integral
    (f : ℝ → ℝ) {N : ℕ}
    (a h r : ℝ)
    (h₁ : IntervalIntegrable f volume a (a + (N : ℝ) * h))
    (h₂ : IntervalIntegrable f volume
      (a + (N : ℝ) * h) (a + (N : ℝ) * h + r)) :
    shortenedTrapezoidalIntegral f N a h r -
        (∫ x in a..a + (N : ℝ) * h + r, f x) =
      trapezoidal_error f N a (a + (N : ℝ) * h) +
        trapezoidal_error f 1
          (a + (N : ℝ) * h)
          (a + (N : ℝ) * h + r) := by
  unfold shortenedTrapezoidalIntegral trapezoidal_error
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
  ring

theorem abs_shortenedTrapezoidalIntegral_sub_integral_le
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (a h r ζ₁ ζ₂ : ℝ)
    (h₁c : ContDiffOn ℝ 2 f [[a, a + (N : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 f
      [[a + (N : ℝ) * h, a + (N : ℝ) * h + r]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 f
      [[a, a + (N : ℝ) * h]] x| ≤ ζ₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 f
      [[a + (N : ℝ) * h, a + (N : ℝ) * h + r]] x| ≤ ζ₂)
    (h₁ : IntervalIntegrable f volume a (a + (N : ℝ) * h))
    (h₂ : IntervalIntegrable f volume
      (a + (N : ℝ) * h) (a + (N : ℝ) * h + r)) :
    |shortenedTrapezoidalIntegral f N a h r -
        (∫ x in a..a + (N : ℝ) * h + r, f x)| ≤
      |(N : ℝ) * h| ^ 3 * ζ₁ / (12 * (N : ℝ) ^ 2) +
        |r| ^ 3 * ζ₂ / 12 := by
  rw [shortenedTrapezoidalIntegral_sub_integral f a h r h₁ h₂]
  grw [abs_add_le]
  gcongr
  · simpa only [add_sub_cancel_left] using trapezoidal_error_le_of_c2 h₁c h₁ζ hN
  · simpa using trapezoidal_error_le_of_c2 h₂c h₂ζ (by norm_num : 0 < (1 : ℕ))

theorem sum_trapezoidalIntegral_grid
    {f : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (a h : ℝ) :
    ∑ i ∈ Finset.range N,
      trapezoidal_integral f 1
        (a + (i : ℝ) * h)
        (a + ((i + 1 : ℕ) : ℝ) * h) =
      trapezoidal_integral f N a (a + (N : ℝ) * h) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (sum_trapezoidal_integral_adjacent_intervals (f := f) (N := N)
      (a := a) (h := h) hN)

theorem sum_trapezoidalError_grid
    {f : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (a h : ℝ)
    (hf : IntervalIntegrable f volume a (a + (N : ℝ) * h)) :
    ∑ i ∈ Finset.range N,
      trapezoidal_error f 1
        (a + (i : ℝ) * h)
        (a + ((i + 1 : ℕ) : ℝ) * h) =
      trapezoidal_error f N a (a + (N : ℝ) * h) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (sum_trapezoidal_error_adjacent_intervals (f := f) (N := N)
      (a := a) (h := h) hN hf)

private theorem sum_half_endpoint_weights (f : ℝ → ℝ) (N : ℕ) (h : ℝ) :
    (∑ i ∈ Finset.range N,
      (h / 2) * (f ((i : ℝ) * h) +
        f (((i + 1 : ℕ) : ℝ) * h))) =
      h * (∑ i ∈ Finset.range (N + 1), f ((i : ℝ) * h)) -
        h / 2 * f 0 - h / 2 * f ((N : ℝ) * h) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, add_mul]
      ring

theorem shortenedTrapezoidalIntegral_grid_expansion
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (h r : ℝ) :
    shortenedTrapezoidalIntegral f N 0 h r =
      h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) - h / 2 * f 0 +
        (r - h) / 2 * f ((N : ℝ) * h) + r / 2 * f ((N : ℝ) * h + r) := by
  unfold shortenedTrapezoidalIntegral
  rw [← sum_trapezoidalIntegral_grid hN 0 h]
  simp only [trapezoidal_integral_one, zero_add, Nat.cast_add, Nat.cast_one,
    add_mul, add_sub_cancel_left, one_mul]
  have hs := sum_half_endpoint_weights f N h
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hs
  rw [hs]
  ring

theorem shortenedTrapezoidalIntegral_grid_expansion_of_endpoints
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {h r : ℝ}
    (hf0 : f 0 = 0) (hfend : f ((N : ℝ) * h + r) = 0) :
  shortenedTrapezoidalIntegral f N 0 h r =
      h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) +
        (r - h) / 2 * f ((N : ℝ) * h) := by
  rw [shortenedTrapezoidalIntegral_grid_expansion f hN h r, hf0, hfend]
  ring

theorem gridSampleSum_eq_shortenedTrapezoidalIntegral_add_endpoint
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {h r : ℝ}
    (hf0 : f 0 = 0) (hfend : f ((N : ℝ) * h + r) = 0) :
    h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) =
      shortenedTrapezoidalIntegral f N 0 h r + (h - r) / 2 * f ((N : ℝ) * h) := by
  rw [shortenedTrapezoidalIntegral_grid_expansion_of_endpoints f hN hf0 hfend]
  ring

theorem gridSampleSum_sub_integral
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {h r : ℝ}
    (hf0 : f 0 = 0) (hfend : f ((N : ℝ) * h + r) = 0)
    (h₁ : IntervalIntegrable f volume 0 ((N : ℝ) * h))
    (h₂ : IntervalIntegrable f volume ((N : ℝ) * h) ((N : ℝ) * h + r)) :
    h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) -
        (∫ x in 0..(N : ℝ) * h + r, f x) =
      trapezoidal_error f N 0 ((N : ℝ) * h) +
        trapezoidal_error f 1 ((N : ℝ) * h) ((N : ℝ) * h + r) +
        (h - r) / 2 * f ((N : ℝ) * h) := by
  calc
    _ = (shortenedTrapezoidalIntegral f N 0 h r -
          (∫ x in 0..(N : ℝ) * h + r, f x)) +
          (h - r) / 2 * f ((N : ℝ) * h) := by
      rw [gridSampleSum_eq_shortenedTrapezoidalIntegral_add_endpoint f hN hf0 hfend]
      ring
    _ = _ := by
      have hs := shortenedTrapezoidalIntegral_sub_integral f (N := N) 0 h r
        (by simpa using h₁) (by simpa using h₂)
      simpa using congrArg (fun x => x + (h - r) / 2 * f ((N : ℝ) * h)) hs

theorem abs_gridSampleSum_sub_integral_le
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {h r ζ₁ ζ₂ : ℝ}
    (h₁c : ContDiffOn ℝ 2 f [[0, (N : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 f [[(N : ℝ) * h, (N : ℝ) * h + r]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 f [[0, (N : ℝ) * h]] x| ≤ ζ₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 f [[(N : ℝ) * h, (N : ℝ) * h + r]] x| ≤ ζ₂)
    (h₁ : IntervalIntegrable f volume 0 ((N : ℝ) * h))
    (h₂ : IntervalIntegrable f volume ((N : ℝ) * h) ((N : ℝ) * h + r))
    (hf0 : f 0 = 0) (hfend : f ((N : ℝ) * h + r) = 0) :
    |h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) -
        (∫ x in 0..(N : ℝ) * h + r, f x)| ≤
      |(N : ℝ) * h| ^ 3 * ζ₁ / (12 * (N : ℝ) ^ 2) +
        |r| ^ 3 * ζ₂ / 12 + |h - r| / 2 * |f ((N : ℝ) * h)| := by
  rw [gridSampleSum_sub_integral f hN hf0 hfend h₁ h₂]
  grw [abs_add_le]
  grw [abs_add_le]
  gcongr
  · simpa [sub_zero] using trapezoidal_error_le_of_c2 h₁c h₁ζ hN
  · simpa using trapezoidal_error_le_of_c2 h₂c h₂ζ (by norm_num : (0 : ℕ) < 1)
  · rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem gridSampleSum_sub_integral_le_mul_h_sq
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {h r ζ₁ ζ₂ K M : ℝ}
    (hpos : 0 < h) (hr0 : 0 ≤ r) (hrh : r ≤ h) (hh1 : h ≤ 1)
    (hNK : (N : ℝ) * h ≤ K) (hz₁ : 0 ≤ ζ₁) (hz₂ : 0 ≤ ζ₂) (hM : 0 ≤ M)
    (hf : |f ((N : ℝ) * h)| ≤ M * r)
    (h₁c : ContDiffOn ℝ 2 f [[0, (N : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 f [[(N : ℝ) * h, (N : ℝ) * h + r]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 f [[0, (N : ℝ) * h]] x| ≤ ζ₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 f [[(N : ℝ) * h, (N : ℝ) * h + r]] x| ≤ ζ₂)
    (h₁ : IntervalIntegrable f volume 0 ((N : ℝ) * h))
    (h₂ : IntervalIntegrable f volume ((N : ℝ) * h) ((N : ℝ) * h + r))
    (hf0 : f 0 = 0) (hfend : f ((N : ℝ) * h + r) = 0) :
    |h * (∑ j ∈ Finset.range (N + 1), f ((j : ℝ) * h)) -
        (∫ x in 0..(N : ℝ) * h + r, f x)| ≤
      h ^ 2 * (K * ζ₁ / 12 + ζ₂ / 12 + M / 2) := by
  have hbase := abs_gridSampleSum_sub_integral_le f hN h₁c h₂c h₁ζ h₂ζ h₁ h₂ hf0 hfend
  grw [hbase]
  have hNh : 0 ≤ (N : ℝ) * h := by positivity
  have hfirst : |(N : ℝ) * h| ^ 3 * ζ₁ / (12 * (N : ℝ) ^ 2) ≤
      h ^ 2 * (K * ζ₁ / 12) := by
    rw [abs_of_nonneg hNh]
    calc
      ((N : ℝ) * h) ^ 3 * ζ₁ / (12 * (N : ℝ) ^ 2) =
          ((N : ℝ) * h) * h ^ 2 * ζ₁ / 12 := by
            field_simp
      _ ≤ h ^ 2 * (K * ζ₁ / 12) := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
        nlinarith [mul_nonneg (sq_nonneg h) hz₁]
  have hsecond : |r| ^ 3 * ζ₂ / 12 ≤ h ^ 2 * (ζ₂ / 12) := by
    rw [abs_of_nonneg hr0]
    have hr3 : r ^ 3 ≤ h ^ 2 := by
      have : r ^ 3 ≤ h ^ 3 := by gcongr
      have hh3 : h ^ 3 ≤ h ^ 2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
      linarith
    calc
      r ^ 3 * ζ₂ / 12 ≤ h ^ 2 * ζ₂ / 12 := by gcongr
      _ = h ^ 2 * (ζ₂ / 12) := by ring
  have hend : |h - r| / 2 * |f ((N : ℝ) * h)| ≤ h ^ 2 * (M / 2) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hrh)]
    calc
      (h - r) / 2 * |f ((N : ℝ) * h)| ≤ (h - r) / 2 * (M * r) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ h ^ 2 * (M / 2) := by
        have hprod : (h - r) * r ≤ h ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hrh) hr0]
        nlinarith [mul_nonneg hM (le_of_lt (by positivity : (0 : ℝ) < h))]
  linarith

end RayleighKernel.Discrete
