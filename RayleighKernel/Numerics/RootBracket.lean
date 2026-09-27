import RayleighKernel.Numerics.RationalBounds
import RayleighKernel.Profile.Consistency
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace RayleighKernel.Numerics
open Set
open RayleighKernel.Profile

def tMinus : ℝ :=
  35701290278126360584735350083717233860170522483300 / 10^49
def tPlus : ℝ :=
  35701290278126360584735350083717233860170522483302 / 10^49

private def cMinus70 : ℝ :=
  -2126324073183650202671871717637868791530072070530110439953545962466080 / 10^70
private def cMinus70U : ℝ :=
  -2126324073183650202671871717637868791530072070530110439953545962466079 / 10^70
private def sMinus70 : ℝ :=
  9771322629808090160104783261569956702189382181691765675748848072427633 / 10^70
private def sMinus70U : ℝ :=
  9771322629808090160104783261569956702189382181691765675748848072427634 / 10^70
private def cPlus70 : ℝ :=
  -2126324073183650202671871717637868791530072070531087572216526771482090 / 10^70
private def cPlus70U : ℝ :=
  -2126324073183650202671871717637868791530072070531087572216526771482089 / 10^70
private def sPlus70 : ℝ :=
  9771322629808090160104783261569956702189382181691553043341529707407366 / 10^70
private def sPlus70U : ℝ :=
  9771322629808090160104783261569956702189382181691553043341529707407367 / 10^70

private def cMinus60 : ℝ := -212632407318365020267187171763786879153007207053011043995355 / 10^60
private def cMinus60U : ℝ := -212632407318365020267187171763786879153007207053011043995354 / 10^60
private def sMinus60 : ℝ := 977132262980809016010478326156995670218938218169176567574884 / 10^60
private def sMinus60U : ℝ := 977132262980809016010478326156995670218938218169176567574885 / 10^60
private def cPlus60 : ℝ := -212632407318365020267187171763786879153007207053108757221653 / 10^60
private def cPlus60U : ℝ := -212632407318365020267187171763786879153007207053108757221652 / 10^60
private def sPlus60 : ℝ := 977132262980809016010478326156995670218938218169155304334152 / 10^60
private def sPlus60U : ℝ := 977132262980809016010478326156995670218938218169155304334153 / 10^60

private theorem err80 (x : ℝ) (hx : x = tMinus / 2 ∨ x = tPlus / 2) :
    ‖(x : ℂ) * Complex.I‖ / 81 ≤ 1 / 2 := by
  rcases hx with rfl | rfl <;> rw [norm_real_mul_I] <;> norm_num [tMinus, tPlus]

private theorem cos_box_minus : cMinus60 < Real.cos (tMinus / 2) ∧ Real.cos (tMinus / 2) < cMinus60U := by
  let eps : ℝ := 1 / 10^65
  have he := cos_expTaylor_error 80 (tMinus / 2) (err80 _ (Or.inl rfl))
  rw [norm_real_mul_I] at he
  have he' : |Real.cos (tMinus / 2) - (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).re| < eps := by
    dsimp [eps]
    exact lt_of_le_of_lt he (by norm_num [tMinus, abs_of_nonneg])
  rw [abs_lt] at he'
  have hTaylorLow : cMinus70 < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).re := by
    norm_num [cMinus70, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hTaylorUp : (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).re < cMinus70U := by
    norm_num [cMinus70U, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hMarginLow : cMinus60 + eps < cMinus70 := by norm_num [cMinus60, cMinus70, eps]
  have hMarginUp : cMinus70U + eps < cMinus60U := by norm_num [cMinus70U, cMinus60U, eps]
  constructor
  · calc
      cMinus60 < cMinus70 - eps := by linarith
      _ < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).re - eps := by simpa using sub_lt_sub_right hTaylorLow eps
      _ < Real.cos (tMinus / 2) := by linarith [he'.1]
  · calc
      Real.cos (tMinus / 2) < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).re + eps := by linarith [he'.2]
      _ < cMinus70U + eps := by simpa [add_comm] using add_lt_add_right hTaylorUp eps
      _ < cMinus60U := hMarginUp

private theorem sin_box_minus : sMinus60 < Real.sin (tMinus / 2) ∧ Real.sin (tMinus / 2) < sMinus60U := by
  let eps : ℝ := 1 / 10^65
  have he := sin_expTaylor_error 80 (tMinus / 2) (err80 _ (Or.inl rfl))
  rw [norm_real_mul_I] at he
  have he' : |Real.sin (tMinus / 2) - (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).im| < eps := by
    dsimp [eps]
    exact lt_of_le_of_lt he (by norm_num [tMinus, abs_of_nonneg])
  rw [abs_lt] at he'
  have hTaylorLow : sMinus70 < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).im := by
    norm_num [sMinus70, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hTaylorUp : (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).im < sMinus70U := by
    norm_num [sMinus70U, tMinus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hMarginLow : sMinus60 + eps < sMinus70 := by norm_num [sMinus60, sMinus70, eps]
  have hMarginUp : sMinus70U + eps < sMinus60U := by norm_num [sMinus70U, sMinus60U, eps]
  constructor
  · calc
      sMinus60 < sMinus70 - eps := by linarith
      _ < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).im - eps := sub_lt_sub_right hTaylorLow _
      _ < Real.sin (tMinus / 2) := by linarith [he'.1]
  · calc
      Real.sin (tMinus / 2) < (expTaylor 80 (((tMinus / 2 : ℝ) : ℂ) * Complex.I)).im + eps := by linarith [he'.2]
      _ < sMinus70U + eps := by simpa [add_comm] using add_lt_add_right hTaylorUp eps
      _ < sMinus60U := hMarginUp

private theorem cos_box_plus : cPlus60 < Real.cos (tPlus / 2) ∧ Real.cos (tPlus / 2) < cPlus60U := by
  let eps : ℝ := 1 / 10^65
  have he := cos_expTaylor_error 80 (tPlus / 2) (err80 _ (Or.inr rfl))
  rw [norm_real_mul_I] at he
  have he' : |Real.cos (tPlus / 2) - (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).re| < eps := by
    dsimp [eps]
    exact lt_of_le_of_lt he (by norm_num [tPlus, abs_of_nonneg])
  rw [abs_lt] at he'
  have hTaylorLow : cPlus70 < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).re := by
    norm_num [cPlus70, tPlus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hTaylorUp : (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).re < cPlus70U := by
    norm_num [cPlus70U, tPlus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hMarginLow : cPlus60 + eps < cPlus70 := by norm_num [cPlus60, cPlus70, eps]
  have hMarginUp : cPlus70U + eps < cPlus60U := by norm_num [cPlus70U, cPlus60U, eps]
  constructor
  · calc
      cPlus60 < cPlus70 - eps := by linarith
      _ < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).re - eps := sub_lt_sub_right hTaylorLow _
      _ < Real.cos (tPlus / 2) := by linarith [he'.1]
  · calc
      Real.cos (tPlus / 2) < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).re + eps := by linarith [he'.2]
      _ < cPlus70U + eps := by simpa [add_comm] using add_lt_add_right hTaylorUp eps
      _ < cPlus60U := hMarginUp

private theorem sin_box_plus : sPlus60 < Real.sin (tPlus / 2) ∧ Real.sin (tPlus / 2) < sPlus60U := by
  let eps : ℝ := 1 / 10^65
  have he := sin_expTaylor_error 80 (tPlus / 2) (err80 _ (Or.inr rfl))
  rw [norm_real_mul_I] at he
  have he' : |Real.sin (tPlus / 2) - (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).im| < eps := by
    dsimp [eps]
    exact lt_of_le_of_lt he (by norm_num [tPlus, abs_of_nonneg])
  rw [abs_lt] at he'
  have hTaylorLow : sPlus70 < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).im := by
    norm_num [sPlus70, tPlus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hTaylorUp : (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).im < sPlus70U := by
    norm_num [sPlus70U, tPlus, expTaylor, Finset.sum_range_succ, Complex.ext_iff, pow_succ]
  have hMarginLow : sPlus60 + eps < sPlus70 := by norm_num [sPlus60, sPlus70, eps]
  have hMarginUp : sPlus70U + eps < sPlus60U := by norm_num [sPlus70U, sPlus60U, eps]
  constructor
  · calc
      sPlus60 < sPlus70 - eps := by linarith
      _ < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).im - eps := sub_lt_sub_right hTaylorLow _
      _ < Real.sin (tPlus / 2) := by linarith [he'.1]
  · calc
      Real.sin (tPlus / 2) < (expTaylor 80 (((tPlus / 2 : ℝ) : ℂ) * Complex.I)).im + eps := by linarith [he'.2]
      _ < sPlus70U + eps := by simpa [add_comm] using add_lt_add_right hTaylorUp eps
      _ < sPlus60U := hMarginUp

private theorem sin_half_minus_pos : 0 < Real.sin (tMinus / 2) := by
  have h := sin_box_minus
  have hs : 0 < sMinus60 := by norm_num [sMinus60]
  linarith

private theorem sin_half_plus_pos : 0 < Real.sin (tPlus / 2) := by
  have h := sin_box_plus
  have hs : 0 < sPlus60 := by norm_num [sPlus60]
  linarith
private def pMinusL : ℝ := 277689086562878566070656011804018081245941156941208438690 / 10^56
private def pMinusU : ℝ := 277689086562878566070656011804018081245941156941208438691 / 10^56
private def pPlusL : ℝ := 277689086562878566070656011804018081245941156941250182735 / 10^56
private def pPlusU : ℝ := 277689086562878566070656011804018081245941156941250182736 / 10^56

private def qAt (t p : ℝ) : ℝ := t^4 - 6*t^2*p + 3*p^3*(p-2)

private theorem lower_slope_corner_minus :
    (pMinusL - 2) * sMinus60U + tMinus * cMinus60U < 0 := by
  norm_num [pMinusL, tMinus, cMinus60U, sMinus60U]

private theorem upper_slope_corner_minus :
    0 < (pMinusU - 2) * sMinus60 + tMinus * cMinus60 := by
  norm_num [pMinusU, tMinus, cMinus60, sMinus60]

private theorem lower_slope_corner_plus :
    (pPlusL - 2) * sPlus60U + tPlus * cPlus60U < 0 := by
  norm_num [pPlusL, tPlus, cPlus60U, sPlus60U]

private theorem upper_slope_corner_plus :
    0 < (pPlusU - 2) * sPlus60 + tPlus * cPlus60 := by
  norm_num [pPlusU, tPlus, cPlus60, sPlus60]

private theorem p_bounds_basic :
    27/10 < pMinusL ∧ pMinusU < 29/10 ∧
    27/10 < pPlusL ∧ pPlusU < 29/10 := by
  norm_num [pMinusL, pMinusU, pPlusL, pPlusU]

private theorem qAt_tMinus_pMinusU : qAt tMinus pMinusU < 0 := by
  norm_num [qAt, tMinus, pMinusU]

private theorem qAt_tPlus_pPlusL : 0 < qAt tPlus pPlusL := by
  norm_num [qAt, tPlus, pPlusL]

private theorem qAt_strictMonoOn {t x y : ℝ} (ht : t^2 < 13)
    (hx : x ∈ Icc (27/10 : ℝ) (29/10))
    (hy : y ∈ Icc (27/10 : ℝ) (29/10)) (hxy : x < y) :
    qAt t x < qAt t y := by
  have hbase : (0 : ℝ) ≤ 27/10 := by norm_num
  have hx0 : 0 ≤ x := le_trans hbase hx.1
  have hy0 : 0 ≤ y := le_trans hbase hy.1
  have hxy0 : 0 ≤ y - x := le_of_lt (sub_pos.mpr hxy)
  have hx2 : (27/10 : ℝ)^2 ≤ x^2 := by
    nlinarith [sq_nonneg (x - 27/10), hx.1]
  have hy2 : (27/10 : ℝ)^2 ≤ y^2 := by
    nlinarith [sq_nonneg (y - 27/10), hy.1]
  have hx3 : (27/10 : ℝ)^3 ≤ x^3 := by
    have h := mul_le_mul hx2 hx.1 (by positivity) (by positivity)
    nlinarith
  have hy3 : (27/10 : ℝ)^3 ≤ y^3 := by
    have h := mul_le_mul hy2 hy.1 (by positivity) (by positivity)
    nlinarith
  have hy2x : (27/10 : ℝ)^3 ≤ y^2 * x := by
    have h := mul_le_mul hy2 hx.1 (by positivity) (by positivity)
    nlinarith
  have hyx2 : (27/10 : ℝ)^3 ≤ y * x^2 := by
    have h := mul_le_mul hy.1 hx2 (by positivity) (by positivity)
    nlinarith
  have hyx : (27/10 : ℝ)^2 ≤ y*x := by
    have h := mul_le_mul hy.1 hx.1 (by positivity) (by positivity)
    nlinarith
  have hsum : 2*t^2 <
      y^3 + y^2*x + y*x^2 + x^3 - 2*(y^2+y*x+x^2) := by
    nlinarith [ht, hx2, hy2, hx3, hy3, hy2x, hyx2, hyx]
  have hfac : 0 < -6*t^2 + 3*(y^3 + y^2*x + y*x^2 + x^3 -
      2*(y^2+y*x+x^2)) := by nlinarith
  have hdiff : qAt t y - qAt t x = (y-x) *
      (-6*t^2 + 3*(y^3 + y^2*x + y*x^2 + x^3 - 2*(y^2+y*x+x^2))) := by
    rw [qAt, qAt]
    ring
  have hpos : 0 < qAt t y - qAt t x := by
    rw [hdiff]
    exact mul_pos (sub_pos.mpr hxy) hfac
  linarith
private theorem initialSlope_tMinus_mem :
    initialSlope tMinus ∈ Ioo pMinusL pMinusU := by
  have hs := sin_half_minus_pos
  have hc := cos_box_minus
  have hsc := sin_box_minus
  have ht : 0 < tMinus := by norm_num [tMinus]
  have hp : 0 < pMinusL - 2 := by norm_num [pMinusL]
  have hl : (pMinusL - 2) * Real.sin (tMinus/2) +
      tMinus * Real.cos (tMinus/2) < 0 := by
    have h1 := mul_lt_mul_of_pos_left hsc.2 hp
    have h2 := mul_lt_mul_of_pos_left hc.2 ht
    linarith [lower_slope_corner_minus, h1, h2]
  have hpu : 0 < pMinusU - 2 := by norm_num [pMinusU]
  have hu : 0 < (pMinusU - 2) * Real.sin (tMinus/2) +
      tMinus * Real.cos (tMinus/2) := by
    have h1 := mul_lt_mul_of_pos_left hsc.1 hpu
    have h2 := mul_lt_mul_of_pos_left hc.1 ht
    linarith [upper_slope_corner_minus, h1, h2]
  rw [initialSlope, Real.cot_eq_cos_div_sin]
  constructor
  · have hc' : pMinusL * Real.sin (tMinus/2) <
        2 * Real.sin (tMinus/2) - tMinus * Real.cos (tMinus/2) := by linarith
    have heq : 2 - tMinus * (Real.cos (tMinus/2) / Real.sin (tMinus/2)) =
        (2 * Real.sin (tMinus/2) - tMinus * Real.cos (tMinus/2)) /
          Real.sin (tMinus/2) := by field_simp
    rw [heq]
    exact (lt_div_iff₀ hs).2 hc'
  · have hc' : (2 * Real.sin (tMinus/2) - tMinus * Real.cos (tMinus/2)) <
        pMinusU * Real.sin (tMinus/2) := by linarith
    have heq : 2 - tMinus * (Real.cos (tMinus/2) / Real.sin (tMinus/2)) =
        (2 * Real.sin (tMinus/2) - tMinus * Real.cos (tMinus/2)) /
          Real.sin (tMinus/2) := by field_simp
    rw [heq]
    exact (div_lt_iff₀ hs).2 hc'

private theorem initialSlope_tPlus_mem :
    initialSlope tPlus ∈ Ioo pPlusL pPlusU := by
  have hs := sin_half_plus_pos
  have hc := cos_box_plus
  have hsc := sin_box_plus
  have ht : 0 < tPlus := by norm_num [tPlus]
  have hp : 0 < pPlusL - 2 := by norm_num [pPlusL]
  have hl : (pPlusL - 2) * Real.sin (tPlus/2) +
      tPlus * Real.cos (tPlus/2) < 0 := by
    have h1 := mul_lt_mul_of_pos_left hsc.2 hp
    have h2 := mul_lt_mul_of_pos_left hc.2 ht
    linarith [lower_slope_corner_plus, h1, h2]
  have hpu : 0 < pPlusU - 2 := by norm_num [pPlusU]
  have hu : 0 < (pPlusU - 2) * Real.sin (tPlus/2) +
      tPlus * Real.cos (tPlus/2) := by
    have h1 := mul_lt_mul_of_pos_left hsc.1 hpu
    have h2 := mul_lt_mul_of_pos_left hc.1 ht
    linarith [upper_slope_corner_plus, h1, h2]
  rw [initialSlope, Real.cot_eq_cos_div_sin]
  constructor
  · have hc' : pPlusL * Real.sin (tPlus/2) <
        2 * Real.sin (tPlus/2) - tPlus * Real.cos (tPlus/2) := by linarith
    have heq : 2 - tPlus * (Real.cos (tPlus/2) / Real.sin (tPlus/2)) =
        (2 * Real.sin (tPlus/2) - tPlus * Real.cos (tPlus/2)) /
          Real.sin (tPlus/2) := by field_simp
    rw [heq]
    exact (lt_div_iff₀ hs).2 hc'
  · have hc' : (2 * Real.sin (tPlus/2) - tPlus * Real.cos (tPlus/2)) <
        pPlusU * Real.sin (tPlus/2) := by linarith
    have heq : 2 - tPlus * (Real.cos (tPlus/2) / Real.sin (tPlus/2)) =
        (2 * Real.sin (tPlus/2) - tPlus * Real.cos (tPlus/2)) /
          Real.sin (tPlus/2) := by field_simp
    rw [heq]
    exact (div_lt_iff₀ hs).2 hc'

theorem tMinus_lt_tPlus : tMinus < tPlus := by
  norm_num [tMinus, tPlus]

theorem consistencyPolynomial_tMinus_neg :
    consistencyPolynomial tMinus < 0 := by
  have ht : tMinus ^ 2 < 13 := by norm_num [tMinus]
  have hp := p_bounds_basic
  rcases hp with ⟨hmL, hmU, hpL, hpU⟩
  have hinterval : pMinusL < pMinusU := by norm_num [pMinusL, pMinusU]
  have hpm : initialSlope tMinus ∈ Icc (27/10 : ℝ) (29/10) :=
    ⟨le_of_lt (lt_of_lt_of_le hmL (initialSlope_tMinus_mem.1.le)),
      le_of_lt (lt_trans initialSlope_tMinus_mem.2 hmU)⟩
  have hpu : pMinusU ∈ Icc (27/10 : ℝ) (29/10) :=
    ⟨le_of_lt (lt_trans hmL hinterval), hmU.le⟩
  have hmono := qAt_strictMonoOn ht hpm hpu initialSlope_tMinus_mem.2
  have hq : qAt tMinus (initialSlope tMinus) < qAt tMinus pMinusU := hmono
  have hneg := qAt_tMinus_pMinusU
  change qAt tMinus (initialSlope tMinus) < 0
  linarith [hq, hneg]

theorem consistencyPolynomial_tPlus_pos :
    0 < consistencyPolynomial tPlus := by
  have ht : tPlus ^ 2 < 13 := by norm_num [tPlus]
  have hp := p_bounds_basic
  rcases hp with ⟨hmL, hmU, hpL, hpU⟩
  have hinterval : pPlusL < pPlusU := by norm_num [pPlusL, pPlusU]
  have hpl : pPlusL ∈ Icc (27/10 : ℝ) (29/10) :=
    ⟨hpL.le, le_of_lt (lt_trans hinterval hpU)⟩
  have hpp : initialSlope tPlus ∈ Icc (27/10 : ℝ) (29/10) :=
    ⟨le_of_lt (lt_trans hpL initialSlope_tPlus_mem.1),
      le_of_lt (lt_trans initialSlope_tPlus_mem.2 hpU)⟩
  have hmono := qAt_strictMonoOn ht hpl hpp initialSlope_tPlus_mem.1
  have hq : qAt tPlus pPlusL < qAt tPlus (initialSlope tPlus) := hmono
  have hpos := qAt_tPlus_pPlusL
  change 0 < qAt tPlus (initialSlope tPlus)
  linarith [hq, hpos]

theorem sqrt_twelve_lt_tMinus : Real.sqrt 12 < tMinus := by
  have hsqrt : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg 12
  have hsqrt_sq : (Real.sqrt 12) ^ 2 = 12 := by norm_num
  have ht : 0 < tMinus := by norm_num [tMinus]
  have ht_sq : 12 < tMinus ^ 2 := by norm_num [tMinus]
  nlinarith

theorem tPlus_lt_two_pi : tPlus < 2 * Real.pi := by
  have hpi := Real.pi_gt_d20
  norm_num [tPlus] at hpi ⊢
  nlinarith

theorem tStar_mem_rootBracket :
    Profile.tStar ∈ Set.Ioo tMinus tPlus := by
  have hminus_domain : tMinus ∈ Ico (Real.sqrt 12) (2 * Real.pi) := by
    exact ⟨sqrt_twelve_lt_tMinus.le,
      lt_trans tMinus_lt_tPlus tPlus_lt_two_pi⟩
  have hplus_domain : tPlus ∈ Ico (Real.sqrt 12) (2 * Real.pi) := by
    exact ⟨le_trans sqrt_twelve_lt_tMinus.le tMinus_lt_tPlus.le,
      tPlus_lt_two_pi⟩
  have hstar_domain : Profile.tStar ∈ Ico (Real.sqrt 12) (2 * Real.pi) := by
    exact ⟨Profile.sqrt_twelve_lt_tStar.le, Profile.tStar_lt_two_pi⟩
  constructor
  · by_contra h
    have hle : Profile.tStar ≤ tMinus := le_of_not_gt h
    rcases hle.eq_or_lt with heq | hlt
    · have hz : consistencyPolynomial tMinus = 0 := by
        simpa [heq] using Profile.consistencyPolynomial_tStar
      exact (ne_of_lt consistencyPolynomial_tMinus_neg) hz
    · have hmono := strictMonoOn_consistencyPolynomial hstar_domain hminus_domain hlt
      linarith [hmono, Profile.consistencyPolynomial_tStar,
        consistencyPolynomial_tMinus_neg]
  · by_contra h
    have hle : tPlus ≤ Profile.tStar := le_of_not_gt h
    rcases hle.eq_or_lt with heq | hlt
    · have hz : consistencyPolynomial tPlus = 0 := by
        simpa [heq] using Profile.consistencyPolynomial_tStar
      exact (ne_of_gt consistencyPolynomial_tPlus_pos) hz
    · have hmono := strictMonoOn_consistencyPolynomial hplus_domain hstar_domain hlt
      linarith [hmono, Profile.consistencyPolynomial_tStar,
        consistencyPolynomial_tPlus_pos]
end RayleighKernel.Numerics
