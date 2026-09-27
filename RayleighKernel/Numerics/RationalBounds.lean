import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential

noncomputable section

namespace RayleighKernel.Numerics

def expTaylor (n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range n, z^m / m.factorial

private theorem exp_bound_re (n : ℕ) (x : ℝ)
    (h : ‖(x : ℂ) * Complex.I‖ / n.succ ≤ 1 / 2) :
    |(Complex.exp ((x : ℂ) * Complex.I) - expTaylor n ((x : ℂ) * Complex.I)).re| ≤
      ‖(x : ℂ) * Complex.I‖ ^ n / n.factorial * 2 := by
  apply le_trans (Complex.abs_re_le_norm _)
  exact Complex.exp_bound' h

private theorem exp_bound_im (n : ℕ) (x : ℝ)
    (h : ‖(x : ℂ) * Complex.I‖ / n.succ ≤ 1 / 2) :
    |(Complex.exp ((x : ℂ) * Complex.I) - expTaylor n ((x : ℂ) * Complex.I)).im| ≤
      ‖(x : ℂ) * Complex.I‖ ^ n / n.factorial * 2 := by
  apply le_trans (Complex.abs_im_le_norm _)
  exact Complex.exp_bound' h

theorem norm_real_mul_I (x : ℝ) : ‖(x : ℂ) * Complex.I‖ = |x| := by
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I]
  simp [Real.norm_eq_abs]

theorem cos_expTaylor_error (n : ℕ) (x : ℝ)
    (h : ‖(x : ℂ) * Complex.I‖ / n.succ ≤ 1 / 2) :
    |Real.cos x - (expTaylor n ((x : ℂ) * Complex.I)).re| ≤
      ‖(x : ℂ) * Complex.I‖ ^ n / n.factorial * 2 := by
  have h' := exp_bound_re n x h
  simpa [map_sub, Complex.exp_ofReal_mul_I_re, sub_eq_add_neg] using h'

theorem sin_expTaylor_error (n : ℕ) (x : ℝ)
    (h : ‖(x : ℂ) * Complex.I‖ / n.succ ≤ 1 / 2) :
    |Real.sin x - (expTaylor n ((x : ℂ) * Complex.I)).im| ≤
      ‖(x : ℂ) * Complex.I‖ ^ n / n.factorial * 2 := by
  have h' := exp_bound_im n x h
  simpa [map_sub, Complex.exp_ofReal_mul_I_im, sub_eq_add_neg] using h'

end RayleighKernel.Numerics
