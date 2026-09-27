import RayleighKernel.Discrete.RiemannSums
import RayleighKernel.Discrete.Defs

noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory
open scoped Interval

namespace RayleighKernel.Discrete

def meshCount (K h : ℝ) : ℕ := ⌊K / h⌋₊
def meshRemainder (K h : ℝ) : ℝ := K - (meshCount K h : ℝ) * h

theorem meshCount_mul_add_remainder {K h : ℝ} (_hh : 0 < h) (_hK : 0 ≤ K) :
    (meshCount K h : ℝ) * h + meshRemainder K h = K := by simp [meshRemainder]

theorem meshRemainder_nonneg {K h : ℝ} (hh : 0 < h) (hK : 0 ≤ K) :
    0 ≤ meshRemainder K h := by
  unfold meshRemainder meshCount
  have hf := Nat.floor_le (show 0 ≤ K / h by positivity)
  rw [sub_nonneg]
  exact (le_div_iff₀ hh).mp hf

theorem meshRemainder_lt {K h : ℝ} (hh : 0 < h) (_hK : 0 ≤ K) :
    meshRemainder K h < h := by
  unfold meshRemainder meshCount
  have hf : K / h < (⌊K / h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (K / h)
  have hf' := (div_lt_iff₀ hh).mp hf
  nlinarith

theorem meshCount_pos {K h : ℝ} (hh : 0 < h) (_hK : 0 ≤ K) (hKle : h ≤ K) :
    0 < meshCount K h := by
  unfold meshCount
  rw [Nat.floor_pos]
  have : (1 : ℝ) * h ≤ K := by simpa using hKle
  exact (le_div_iff₀ hh).2 this

theorem meshCount_mul_le {K h : ℝ} (hh : 0 < h) (hK : 0 ≤ K) :
    (meshCount K h : ℝ) * h ≤ K := by
  calc
    (meshCount K h : ℝ) * h ≤ (meshCount K h : ℝ) * h + meshRemainder K h :=
      le_add_of_nonneg_right (meshRemainder_nonneg hh hK)
    _ = K := meshCount_mul_add_remainder hh hK

theorem meshRemainder_le {K h : ℝ} (hh : 0 < h) (hK : 0 ≤ K) :
    meshRemainder K h ≤ h := (meshRemainder_lt hh hK).le

def sampledKernel (h : ℝ) (f : ℝ → ℝ) : Kernel := fun j => h * f ((j : ℝ) * h)
@[simp] theorem sampledKernel_apply (h : ℝ) (f : ℝ → ℝ) (j : ℕ) :
    sampledKernel h f j = h * f ((j : ℝ) * h) := rfl

theorem sampledKernel_nonneg {h : ℝ} {f : ℝ → ℝ} (hh : 0 ≤ h)
    (hf : ∀ x, 0 ≤ f x) : ∀ j, 0 ≤ sampledKernel h f j := by
  intro j; exact mul_nonneg hh (hf _)

theorem sampledKernel_tail {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (_hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) {j : ℕ} (hj : meshCount K h < j) :
    sampledKernel h f j = 0 := by
  have hj' : meshCount K h + 1 ≤ j := Nat.succ_le_iff.mpr hj
  have hfloor : (K / h) < (meshCount K h : ℝ) + 1 := Nat.lt_floor_add_one (K / h)
  have hjreal : (meshCount K h : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj'
  have : K / h < (j : ℝ) := lt_of_lt_of_le hfloor hjreal
  have hKj : K ≤ (j : ℝ) * h := by
    exact (div_lt_iff₀ hh).mp this |>.le
  simp [sampledKernel, hf _ hKj]

theorem sampledKernel_summable {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) : Summable (sampledKernel h f) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount K h + 1))
  intro j hj
  apply sampledKernel_tail hh hK hf
  exact Nat.lt_of_not_ge (by simpa using hj)

theorem sampledKernel_square_summable {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) : Summable (fun j => (sampledKernel h f j) ^ 2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount K h + 1))
  intro j hj
  rw [sampledKernel_tail hh hK hf (Nat.lt_of_not_ge (by simpa using hj))]
  simp

theorem sampledKernel_firstMoment_summable {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    Summable (fun j : ℕ => (j : ℝ) * sampledKernel h f j) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount K h + 1))
  intro j hj
  rw [sampledKernel_tail hh hK hf (Nat.lt_of_not_ge (by simpa using hj))]
  simp

theorem sampledKernel_difference_square_summable {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h)
    (hK : 0 ≤ K) (hf : ∀ x, K ≤ x → f x = 0) :
    Summable (fun j => (difference (sampledKernel h f) j) ^ 2) := by
  apply summable_of_ne_finset_zero (s := Finset.range (meshCount K h + 2))
  intro j hj
  cases j with
  | zero => exact False.elim (hj (by simp))
  | succ k =>
    simp only [difference]
    have hk : meshCount K h < k := by
      have : meshCount K h + 2 ≤ k + 1 := by exact Nat.succ_le_iff.mpr (by simpa using hj)
      omega
    rw [sampledKernel_tail hh hK hf (by omega), sampledKernel_tail hh hK hf hk]
    simp

theorem mass_sampledKernel {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    mass (sampledKernel h f) = h * ∑ j ∈ Finset.range (meshCount K h + 1), f ((j : ℝ) * h) := by
  rw [mass, tsum_eq_sum (s := Finset.range (meshCount K h + 1))]
  · simp only [sampledKernel]
    rw [Finset.mul_sum]
  intro j hj
  exact sampledKernel_tail hh hK hf (Nat.lt_of_not_ge (by simpa using hj))

theorem firstMoment_sampledKernel {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    h * firstMoment (sampledKernel h f) = h * ∑ j ∈ Finset.range (meshCount K h + 1),
      ((j : ℝ) * h) * f ((j : ℝ) * h) := by
  rw [firstMoment, tsum_eq_sum (s := Finset.range (meshCount K h + 1))]
  · simp only [sampledKernel]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  intro j hj
  have hz := sampledKernel_tail hh hK hf (Nat.lt_of_not_ge (by simpa using hj))
  simp only [sampledKernel] at hz ⊢
  rcases mul_eq_zero.mp hz with hzero | hzero
  · simp [hzero]
  · simp [hzero]

theorem sampledGridSum_sub_integral_le_mul_h_sq
    (f : ℝ → ℝ) {K h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hKle : h ≤ K)
    {ζ₁ ζ₂ M : ℝ} (hz₁ : 0 ≤ ζ₁) (hz₂ : 0 ≤ ζ₂) (hM : 0 ≤ M)
    (hf : |f ((meshCount K h : ℝ) * h)| ≤ M * meshRemainder K h)
    (h₁c : ContDiffOn ℝ 2 f [[0, (meshCount K h : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 f [[(meshCount K h : ℝ) * h, K]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 f [[0, (meshCount K h : ℝ) * h]] x| ≤ ζ₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 f [[(meshCount K h : ℝ) * h, K]] x| ≤ ζ₂)
    (h₁ : IntervalIntegrable f volume 0 ((meshCount K h : ℝ) * h))
    (h₂ : IntervalIntegrable f volume ((meshCount K h : ℝ) * h) K)
    (hf0 : f 0 = 0) (hfK : f K = 0) :
    |h * (∑ j ∈ Finset.range (meshCount K h + 1), f ((j : ℝ) * h)) -
        (∫ x in 0..K, f x)| ≤
      h ^ 2 * (K * ζ₁ / 12 + ζ₂ / 12 + M / 2) := by
  have hK : 0 ≤ K := le_trans (le_of_lt hh) hKle
  have hN : 0 < meshCount K h := meshCount_pos hh hK hKle
  have hr0 : 0 ≤ meshRemainder K h := meshRemainder_nonneg hh hK
  have hrh : meshRemainder K h ≤ h := meshRemainder_le hh hK
  have hdecomp := meshCount_mul_add_remainder hh hK
  have hfend : f ((meshCount K h : ℝ) * h + meshRemainder K h) = 0 := by
    simpa [hdecomp] using hfK
  have h₂c' : ContDiffOn ℝ 2 f
      [[(meshCount K h : ℝ) * h, (meshCount K h : ℝ) * h + meshRemainder K h]] := by
    simpa [hdecomp] using h₂c
  have h₂ζ' : ∀ x, |iteratedDerivWithin 2 f
      [[(meshCount K h : ℝ) * h, (meshCount K h : ℝ) * h + meshRemainder K h]] x| ≤ ζ₂ := by
    simpa [hdecomp] using h₂ζ
  have h₂' : IntervalIntegrable f volume ((meshCount K h : ℝ) * h)
      ((meshCount K h : ℝ) * h + meshRemainder K h) := by
    simpa [hdecomp] using h₂
  simpa [hdecomp] using gridSampleSum_sub_integral_le_mul_h_sq f hN hh hr0 hrh hh1
    (meshCount_mul_le hh hK) hz₁ hz₂ hM hf h₁c h₂c' h₁ζ h₂ζ' h₁ h₂' hf0 hfend

theorem mass_sampledKernel_sub_integral_le_mul_h_sq
    {K h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hKle : h ≤ K)
    {f : ℝ → ℝ} (hfK : f K = 0) (hf_tail : ∀ x, K ≤ x → f x = 0)
    {ζ₁ ζ₂ M : ℝ} (hz₁ : 0 ≤ ζ₁) (hz₂ : 0 ≤ ζ₂) (hM : 0 ≤ M)
    (hf : |f ((meshCount K h : ℝ) * h)| ≤ M * meshRemainder K h)
    (h₁c : ContDiffOn ℝ 2 f [[0, (meshCount K h : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 f [[(meshCount K h : ℝ) * h, K]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 f [[0, (meshCount K h : ℝ) * h]] x| ≤ ζ₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 f [[(meshCount K h : ℝ) * h, K]] x| ≤ ζ₂)
    (h₁ : IntervalIntegrable f volume 0 ((meshCount K h : ℝ) * h))
    (h₂ : IntervalIntegrable f volume ((meshCount K h : ℝ) * h) K)
    (hf0 : f 0 = 0) :
    |mass (sampledKernel h f) - ∫ x in 0..K, f x| ≤
      h ^ 2 * (K * ζ₁ / 12 + ζ₂ / 12 + M / 2) := by
  rw [mass_sampledKernel hh (le_trans (le_of_lt hh) hKle) hf_tail]
  exact sampledGridSum_sub_integral_le_mul_h_sq f hh hh1 hKle hz₁ hz₂ hM hf
     h₁c h₂c h₁ζ h₂ζ h₁ h₂ hf0 hfK

theorem firstMoment_sampledKernel_sub_integral_le_mul_h_sq
    {K h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hKle : h ≤ K)
    {f : ℝ → ℝ} (hf_tail : ∀ x, K ≤ x → f x = 0)
    {g : ℝ → ℝ} (hgK : g K = 0) {η₁ η₂ M₁ : ℝ}
    (hgf : ∀ x, g x = x * f x)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hM₁ : 0 ≤ M₁)
    (hg : |g ((meshCount K h : ℝ) * h)| ≤ M₁ * meshRemainder K h)
    (h₁c : ContDiffOn ℝ 2 g [[0, (meshCount K h : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 g [[(meshCount K h : ℝ) * h, K]])
    (h₁ζ : ∀ x, |iteratedDerivWithin 2 g [[0, (meshCount K h : ℝ) * h]] x| ≤ η₁)
    (h₂ζ : ∀ x, |iteratedDerivWithin 2 g [[(meshCount K h : ℝ) * h, K]] x| ≤ η₂)
    (h₁ : IntervalIntegrable g volume 0 ((meshCount K h : ℝ) * h))
    (h₂ : IntervalIntegrable g volume ((meshCount K h : ℝ) * h) K)
    (hg0 : g 0 = 0) :
    |h * firstMoment (sampledKernel h f) - ∫ x in 0..K, g x| ≤
      h ^ 2 * (K * η₁ / 12 + η₂ / 12 + M₁ / 2) := by
  rw [firstMoment_sampledKernel hh (le_trans (le_of_lt hh) hKle) hf_tail]
  have hsum := sampledGridSum_sub_integral_le_mul_h_sq g hh hh1 hKle hη₁ hη₂ hM₁ hg
    h₁c h₂c h₁ζ h₂ζ h₁ h₂ hg0 hgK
  convert hsum using 1
  congr 1
  rw [Finset.sum_congr rfl]
  intro j hj
  rw [hgf]

end RayleighKernel.Discrete
