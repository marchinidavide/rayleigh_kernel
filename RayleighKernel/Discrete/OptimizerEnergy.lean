import RayleighKernel.Discrete.OptimizerSampling
import RayleighKernel.Variational
import RayleighKernel.Optimizer.Explicit
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace RayleighKernel.Discrete
open RayleighKernel.Analysis.HalfLineH1

theorem squareEnergy_sampledKernel
    {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    squareEnergy (sampledKernel h f) =
      h ^ 2 * ∑ j ∈ Finset.range (meshCount K h + 1),
        (f ((j : ℝ) * h)) ^ 2 := by
  rw [squareEnergy, tsum_eq_sum (s := Finset.range (meshCount K h + 1)) (fun j hj => by
    rw [sampledKernel_tail hh hK hf (Nat.lt_of_not_ge (by simpa using hj))]
    simp)]
  simp only [sampledKernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem differenceEnergy_sampledKernel_sum
    {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    differenceEnergy (sampledKernel h f) =
      ∑ j ∈ Finset.range (meshCount K h + 2),
        (difference (sampledKernel h f) j) ^ 2 := by
  rw [differenceEnergy]
  apply tsum_eq_sum (s := Finset.range (meshCount K h + 2))
  intro j hj
  cases j with
  | zero => exact False.elim (hj (by simp))
  | succ k =>
    simp only [difference_succ]
    have hk : meshCount K h < k := by
      have : meshCount K h + 2 ≤ k + 1 := by
        exact Nat.succ_le_iff.mpr (by simpa using hj)
      omega
    rw [sampledKernel_tail hh hK hf (by omega),
      sampledKernel_tail hh hK hf hk]
    simp

private theorem sum_range_succ_shift {α : Type*} [AddCommMonoid α]
    (g : ℕ → α) : ∀ n, ∑ j ∈ Finset.range (n + 1), g j =
      g 0 + ∑ j ∈ Finset.range n, g (j + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp [add_assoc]

private def optimizerCore (L x : ℝ) : ℝ :=
  (1 / (optimizerSupport L * Profile.I0Star)) * Profile.FStar (x / optimizerSupport L)

private theorem core_eq_profile_on_Icc {L : ℝ} (_hL : 0 < L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (optimizerSupport L)) :
    optimizerCore L x = optimizerProfile L x := by
  rw [optimizerCore, optimizerProfile_of_mem hx]

private theorem core_contDiff {L : ℝ} (_hL : 0 < L) :
    ContDiff ℝ 4 (optimizerCore L) := by
  unfold optimizerCore
  rw [show Profile.FStar = Profile.value Profile.tStar from funext Profile.FStar_apply]
  unfold Profile.value
  fun_prop

private theorem optimizerCore_deriv_eq {L : ℝ} (hL : 0 < L) (x : ℝ) :
    deriv (optimizerCore L) x =
      (1 / (optimizerSupport L * Profile.I0Star)) *
        (1 / optimizerSupport L) * Profile.slope Profile.tStar
          (x / optimizerSupport L) := by
  unfold optimizerCore
  rw [show Profile.FStar = Profile.value Profile.tStar from funext Profile.FStar_apply]
  have hinner : HasDerivAt (fun y : ℝ => y / optimizerSupport L)
      (1 / optimizerSupport L) x := by
    convert (hasDerivAt_id x).div_const (optimizerSupport L) using 1
    · funext y
      rfl
  have hout := (Profile.value_hasDerivAt Profile.tStar
      (x / optimizerSupport L)).comp x hinner
  have houter := hout.const_mul (1 / (optimizerSupport L * Profile.I0Star))
  have hden : optimizerSupport L * Profile.I0Star ≠ 0 :=
    mul_ne_zero (optimizerSupport_pos hL).ne' Profile.I0Star_pos.ne'
  simpa [Function.comp_def, hden, mul_assoc, mul_left_comm, mul_comm] using houter.deriv

private theorem profile_eq_rep {L : ℝ} (hL : 0 < L) :
    optimizerProfile L = (optimizer L hL).continuousRep := by
  funext x
  exact (continuousRep_optimizer hL x).symm

private theorem profile_deriv_sq_tail_zero {L : ℝ} (hL : 0 < L) :
    (fun x => (deriv (optimizerProfile L) x) ^ 2) =ᵐ[
      (volume : Measure ℝ).restrict (Ici (optimizerSupport L))] 0 := by
  rw [profile_eq_rep hL]
  filter_upwards [ae_restrict_mem measurableSet_Ici,
    ae_restrict_of_ae (Measure.ae_ne volume (optimizerSupport L))] with x hx hxeq
  have hxgt : optimizerSupport L < x := lt_of_le_of_ne hx (Ne.symm hxeq)
  have hev : (optimizer L hL).continuousRep =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hxgt] with y hy
    rw [continuousRep_optimizer hL y, optimizerProfile_eq_zero_of_support_le hL hy.le]
  rw [hev.deriv_eq]
  simp

private theorem profile_deriv_sq_integrable_Ici {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => (deriv (optimizerProfile L) x) ^ 2) (Ici 0) := by
  rw [profile_eq_rep hL]
  exact (optimizer L hL).deriv_continuousRep_sq_integrable.integrableOn

private theorem profile_Ici_energy {L : ℝ} (hL : 0 < L) :
    (∫ x in Ici 0, (deriv (optimizerProfile L) x) ^ 2) =
      (optimizer L hL).dirichletEnergy := by
  rw [profile_eq_rep hL]
  rw [← (optimizer L hL).dirichletEnergy_continuousRep]
  rfl

theorem intervalIntegral_sq_deriv_optimizerProfile
    {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, (deriv (optimizerProfile L) x)^2) =
      (optimizer L hL).dirichletEnergy := by
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (profile_deriv_sq_integrable_Ici hL)
    ((profile_deriv_sq_integrable_Ici hL).mono_set
      (Ici_subset_Ici.mpr (le_of_lt (optimizerSupport_pos hL))))]
  rw [profile_Ici_energy hL]
  have htail : (∫ x in Ici (optimizerSupport L),
      (deriv (optimizerProfile L) x) ^ 2) = 0 := by
    apply integral_eq_zero_of_ae
    exact profile_deriv_sq_tail_zero hL
  rw [htail, sub_zero]

private theorem core_deriv_eq_profile_deriv_ae {L : ℝ} (hL : 0 < L) :
    (fun x => deriv (optimizerCore L) x) =ᵐ[volume.restrict (uIoc 0 (optimizerSupport L))]
      (fun x => deriv (optimizerProfile L) x) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume 0),
    ae_restrict_of_ae (Measure.ae_ne volume (optimizerSupport L))] with x hx hx0 hxK
  have hxint : x ∈ Ioo (0 : ℝ) (optimizerSupport L) := by
    rw [uIoc_of_le (optimizerSupport_pos hL).le] at hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hxK⟩
  have hev : optimizerCore L =ᶠ[𝓝 x] optimizerProfile L := by
    filter_upwards [isOpen_Ioo.mem_nhds hxint] with y hy
    exact core_eq_profile_on_Icc hL ⟨hy.1.le, hy.2.le⟩
  exact hev.deriv_eq

private theorem intervalIntegral_sq_deriv_optimizerCore
    {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, (deriv (optimizerCore L) x)^2) =
      (optimizer L hL).dirichletEnergy := by
  rw [intervalIntegral.integral_congr_ae]
  · exact intervalIntegral_sq_deriv_optimizerProfile hL
  · rw [← ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [core_deriv_eq_profile_deriv_ae hL] with x hx
    exact congrArg (fun z : ℝ => z ^ 2) hx

theorem intervalIntegral_sq_optimizerProfile
    {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L,
      (optimizerProfile L x) ^ 2) =
      (optimizer L hL).squareEnergy := by
  rw [intervalIntegral.integral_of_le (optimizerSupport_pos hL).le]
  rw [← integral_Icc_eq_integral_Ioc]
  calc
    (∫ x in Icc (0 : ℝ) (optimizerSupport L), optimizerProfile L x ^ 2) =
        ∫ x in Icc (0 : ℝ) (optimizerSupport L),
          ((optimizer L hL).continuousRep x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [continuousRep_optimizer hL]
    _ = ∫ x : ℝ, ((optimizer L hL).continuousRep x) ^ 2 := by
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun x : ℝ => ((optimizer L hL).continuousRep x) ^ 2)
        (s := Icc (0 : ℝ) (optimizerSupport L)) (fun x hx => by
      by_cases hx0 : x ≤ 0
      · rw [continuousRep_eq_zero_of_nonpositive _ hx0]
        simp
      · have hxs : optimizerSupport L ≤ x := le_of_not_gt (fun hlt =>
          hx ⟨le_of_not_ge hx0, hlt.le⟩)
        rw [continuousRep_optimizer hL, optimizerProfile_eq_zero_of_support_le hL hxs]
        simp))
    _ = (optimizer L hL).squareEnergy := by
      calc
        (∫ x : ℝ, ((optimizer L hL).continuousRep x) ^ 2) =
            ∫ x : ℝ in halfLine, ((optimizer L hL).continuousRep x) ^ 2 := by
          exact (setIntegral_eq_integral_of_forall_compl_eq_zero
            (s := halfLine) (fun x hx => by
              rw [continuousRep_eq_zero_of_nonpositive _ (le_of_not_ge hx)]
              simp)).symm
        _ = (optimizer L hL).squareEnergy :=
          (optimizer L hL).squareEnergy_continuousRep

theorem differenceEnergy_sampledKernel
    {K h : ℝ} {f : ℝ → ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ∀ x, K ≤ x → f x = 0) :
    differenceEnergy (sampledKernel h f) =
      h ^ 2 * ((f 0) ^ 2 +
        ∑ j ∈ Finset.range (meshCount K h),
          (f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) ^ 2 +
        (f ((meshCount K h : ℝ) * h)) ^ 2) := by
  rw [differenceEnergy_sampledKernel_sum hh hK hf]
  simp only [difference]
  rw [sum_range_succ_shift]
  simp only [Nat.cast_zero, zero_mul, sampledKernel]
  rw [Finset.sum_range_succ]
  have htail : h * f ((↑(meshCount K h + 1) : ℝ) * h) = 0 := by
    rw [Nat.cast_add, Nat.cast_one]
    have hfloor : K / h < (meshCount K h : ℝ) + 1 := Nat.lt_floor_add_one (K / h)
    have hKx : K ≤ ((meshCount K h : ℝ) + 1) * h :=
      (div_lt_iff₀ hh).mp hfloor |>.le
    simp [hf _ hKx]
  have htail' : h * f ((↑(meshCount K h : ℕ) + 1) * h) = 0 := by
    simpa [Nat.cast_add] using htail
  simp only [Nat.cast_add, Nat.cast_one]
  rw [htail']
  simp only [zero_sub]
  have hsum :
      (∑ x ∈ Finset.range (meshCount K h),
        (h * f ((↑x + 1) * h) - h * f (↑x * h)) ^ 2) =
      h ^ 2 * ∑ x ∈ Finset.range (meshCount K h),
        (f ((↑x + 1) * h) - f (↑x * h)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

private theorem local_abs_forwardDifference_sub_deriv_le
    {f : ℝ → ℝ} {a h C : ℝ} (hh : 0 < h) (hf : ContDiff ℝ 2 f)
    (hC : ∀ x ∈ Icc a (a + h), |iteratedDeriv 2 f x| ≤ C) :
    |(f (a + h) - f a) / h - deriv f a| ≤ C * h := by
  have hab : a ≤ a + h := by linarith
  have hs : UniqueDiffOn ℝ (Icc a (a + h)) := uniqueDiffOn_Icc (by linarith)
  have hC' : ∀ x ∈ Icc a (a + h),
      ‖iteratedDerivWithin 2 f (Icc a (a + h)) x‖ ≤ C := by
    intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt) hx]
    simpa [Real.norm_eq_abs] using hC x hx
  have hfc : ContDiffOn ℝ (1 + 1) f (Icc a (a + h)) := by
    convert hf.contDiffOn using 1
    norm_num
  have ht := taylor_mean_remainder_bound (E := ℝ) (n := 1) hab hfc
    (show a + h ∈ Icc a (a + h) from ⟨hab, le_rfl⟩) hC'
  rw [taylor_within_apply] at ht
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    inv_one, Nat.factorial_one, Nat.cast_one, one_mul,
    iteratedDerivWithin_zero, iteratedDerivWithin_one] at ht
  have hderiv : derivWithin f (Icc a (a + h)) a = deriv f a :=
    (hf.differentiable (by norm_num)).differentiableAt.derivWithin
      (hs.uniqueDiffWithinAt ⟨le_rfl, hab⟩)
  rw [show (f (a + h) - f a) / h - deriv f a =
    (f (a + h) - (f a + h * deriv f a)) / h by field_simp; ring,
    abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).2
  have ht' : |f (a + h) - (f a + h * deriv f a)| ≤ C * (h * h) := by
    simpa [Real.norm_eq_abs, pow_two, ← hderiv] using ht
  convert ht' using 1
  ring_nf

private theorem local_square_sub_square_le_of_abs_le {x y B ε : ℝ}
    (hx : |x| ≤ B) (hy : |y| ≤ B) (he : |x - y| ≤ ε) :
    |x ^ 2 - y ^ 2| ≤ 2 * B * ε := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  have hs : |x + y| ≤ 2 * B := by
    rw [← Real.norm_eq_abs]
    calc
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ B + B := add_le_add hx hy
      _ = 2 * B := by ring
  have he0 : 0 ≤ ε := le_trans (abs_nonneg _) he
  calc
    |x - y| * |x + y| ≤ ε * (2 * B) :=
      mul_le_mul he hs (abs_nonneg _) (le_trans (abs_nonneg _) he)
    _ = 2 * B * ε := by ring

private theorem forwardDifferenceEnergy_sub_derivGridEnergy_le
    {f : ℝ → ℝ} {K h B C : ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hf : ContDiff ℝ 2 f)
    (hB : ∀ x ∈ Icc 0 K, |deriv f x| ≤ B)
    (hC : ∀ x ∈ Icc 0 K, |iteratedDeriv 2 f x| ≤ C) :
    |h * (∑ j ∈ Finset.range (meshCount K h),
        (((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2))
      - h * (∑ j ∈ Finset.range (meshCount K h),
        (deriv f ((j : ℝ) * h)) ^ 2)| ≤
      2 * K * (B + C * h) * C * h := by
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_rfl, hK⟩)
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, hK⟩)
  have hsum :
      |(∑ j ∈ Finset.range (meshCount K h),
          ((((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2) -
            (deriv f ((j : ℝ) * h)) ^ 2))| ≤
      (meshCount K h : ℝ) * (2 * (B + C * h) * (C * h)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (meshCount K h),
          |(((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2) -
            (deriv f ((j : ℝ) * h)) ^ 2| := by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (Finset.range (meshCount K h))
              (fun j => (((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2) -
                (deriv f ((j : ℝ) * h)) ^ 2))
      _ ≤ ∑ _j ∈ Finset.range (meshCount K h), 2 * (B + C * h) * (C * h) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j + 1 ≤ meshCount K h := Nat.succ_le_iff.mpr (by simpa using hj)
        have hx0 : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
        have hxK : (j : ℝ) * h ≤ K := by
          have hjN' : (j : ℝ) ≤ (meshCount K h : ℝ) := by
            exact_mod_cast (Nat.le_of_lt (by simpa using hj))
          nlinarith
        have hyK : ((j + 1 : ℕ) : ℝ) * h ≤ K := by
          have hjN' : ((j + 1 : ℕ) : ℝ) ≤ (meshCount K h : ℝ) := by
            exact_mod_cast hjN
          nlinarith
        have he : |(f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h -
            deriv f ((j : ℝ) * h)| ≤ C * h := by
          simpa [Nat.cast_add, add_mul] using
            (local_abs_forwardDifference_sub_deriv_le (a := (j : ℝ) * h)
              (C := C) hh hf (by
                intro x hx
                have hxK' : (j : ℝ) * h + h ≤ K := by
                  simpa [Nat.cast_add, add_mul] using hyK
                exact hC x ⟨le_trans hx0 hx.1, le_trans hx.2 hxK'⟩))
        have hq : |(f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h| ≤ B + C * h := by
          calc
            _ ≤ |(f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h -
                deriv f ((j : ℝ) * h)| + |deriv f ((j : ℝ) * h)| := by
              rw [show (f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h =
                ((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h -
                  deriv f ((j : ℝ) * h)) + deriv f ((j : ℝ) * h) by ring]
              have hnorm :=
                (norm_add_le
                  ((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h -
                    deriv f ((j : ℝ) * h))
                  (deriv f ((j : ℝ) * h)))
              convert hnorm using 1
              all_goals norm_num
            _ ≤ C * h + B := add_le_add he (hB _ ⟨hx0, hxK⟩)
            _ = B + C * h := by ring
        exact local_square_sub_square_le_of_abs_le hq
          (le_trans (hB _ ⟨hx0, hxK⟩) (by nlinarith [hC0, hh.le])) he
      _ = _ := by simp
  have hrewrite :
      h * (∑ j ∈ Finset.range (meshCount K h),
        (((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2))
        - h * (∑ j ∈ Finset.range (meshCount K h),
          (deriv f ((j : ℝ) * h)) ^ 2) =
      h * ((∑ j ∈ Finset.range (meshCount K h),
        (((f (((j + 1 : ℕ) : ℝ) * h) - f ((j : ℝ) * h)) / h) ^ 2))
        - (∑ j ∈ Finset.range (meshCount K h),
          (deriv f ((j : ℝ) * h)) ^ 2)) := by ring
  rw [hrewrite]
  calc
    |h * (_ - _)| ≤ h * ((meshCount K h : ℝ) * (2 * (B + C * h) * (C * h))) := by
      rw [abs_mul, abs_of_pos hh]
      simpa only [Finset.sum_sub_distrib] using
        (mul_le_mul_of_nonneg_left hsum hh.le)
    _ ≤ _ := by
      have hA : 0 ≤ 2 * (B + C * h) * (C * h) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hN hA]

private theorem leftGridSum_sub_integral_le_mul_h
    (g : ℝ → ℝ) {K h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hKle : h ≤ K)
    {Z G : ℝ} (hZ : 0 ≤ Z) (hG : 0 ≤ G)
     (hg : ∀ x ∈ Icc (0 : ℝ) K, |g x| ≤ G)
    (h₁c : ContDiffOn ℝ 2 g [[0, (meshCount K h : ℝ) * h]])
    (h₂c : ContDiffOn ℝ 2 g [[(meshCount K h : ℝ) * h, K]])
     (h₁Z : ∀ x, |iteratedDerivWithin 2 g [[0, (meshCount K h : ℝ) * h]] x| ≤ Z)
     (h₂Z : ∀ x, |iteratedDerivWithin 2 g [[(meshCount K h : ℝ) * h, K]] x| ≤ Z)
    (h₁ : IntervalIntegrable g volume 0 ((meshCount K h : ℝ) * h))
    (h₂ : IntervalIntegrable g volume ((meshCount K h : ℝ) * h) K) :
    |h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h)) -
        (∫ x in 0..K, g x)| ≤
      h ^ 2 * (K * Z / 12 + Z / 12) + 2 * G * h := by
  have hK : 0 ≤ K := le_trans (le_of_lt hh) hKle
  have hN : 0 < meshCount K h := meshCount_pos hh hK hKle
  have hr0 : 0 ≤ meshRemainder K h := meshRemainder_nonneg hh hK
  have hrh : meshRemainder K h ≤ h := meshRemainder_le hh hK
  have hdecomp := meshCount_mul_add_remainder hh hK
  have h₂c' : ContDiffOn ℝ 2 g
      [[(meshCount K h : ℝ) * h,
        (meshCount K h : ℝ) * h + meshRemainder K h]] := by
    simpa [hdecomp] using h₂c
  have h₂Z' : ∀ x, |iteratedDerivWithin 2 g
      [[(meshCount K h : ℝ) * h,
        (meshCount K h : ℝ) * h + meshRemainder K h]] x| ≤ Z := by
    simpa [hdecomp] using h₂Z
  have h₂' : IntervalIntegrable g volume ((meshCount K h : ℝ) * h)
      ((meshCount K h : ℝ) * h + meshRemainder K h) := by
    simpa [hdecomp] using h₂
  have hend : 0 + (meshCount K h : ℝ) * h + meshRemainder K h = K := by
    simpa only [zero_add] using hdecomp
  have herr := abs_shortenedTrapezoidalIntegral_sub_integral_le g hN 0 h
      (meshRemainder K h) Z Z (by simpa only [zero_add] using h₁c)
      (by simpa only [zero_add] using h₂c')
      (by simpa only [zero_add] using h₁Z)
      (by simpa only [zero_add] using h₂Z')
      (by simpa only [zero_add] using h₁)
      (by simpa only [zero_add] using h₂')
  have hquad : |shortenedTrapezoidalIntegral g (meshCount K h) 0 h
      (meshRemainder K h) - (∫ x in 0..K, g x)| ≤
      h ^ 2 * (K * Z / 12 + Z / 12) := by
    have herrK : |shortenedTrapezoidalIntegral g (meshCount K h) 0 h
        (meshRemainder K h) - (∫ x in 0..K, g x)| ≤
        |(meshCount K h : ℝ) * h| ^ 3 * Z /
            (12 * (meshCount K h : ℝ) ^ 2) +
          |meshRemainder K h| ^ 3 * Z / 12 := by
      simpa only [hend] using herr
    rw [abs_of_nonneg (show 0 ≤ (meshCount K h : ℝ) * h by positivity)] at herrK
    have hfirst : ((meshCount K h : ℝ) * h) ^ 3 * Z /
          (12 * (meshCount K h : ℝ) ^ 2) ≤ h ^ 2 * (K * Z / 12) := by
      calc
        ((meshCount K h : ℝ) * h) ^ 3 * Z /
              (12 * (meshCount K h : ℝ) ^ 2) =
            ((meshCount K h : ℝ) * h) * h ^ 2 * Z / 12 := by field_simp
        _ ≤ h ^ 2 * (K * Z / 12) := by
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
          nlinarith [mul_nonneg (sq_nonneg h) hZ, meshCount_mul_le hh hK]
    have hsecond : |meshRemainder K h| ^ 3 * Z / 12 ≤ h ^ 2 * (Z / 12) := by
      rw [abs_of_nonneg hr0]
      have hr3 : (meshRemainder K h) ^ 3 ≤ h ^ 2 := by
        have : (meshRemainder K h) ^ 3 ≤ h ^ 3 := by gcongr
        have hh3 : h ^ 3 ≤ h ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
        linarith
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
      nlinarith [mul_le_mul_of_nonneg_right hr3 hZ]
    calc
      _ ≤ _ := herrK.trans (add_le_add hfirst hsecond)
      _ = h ^ 2 * (K * Z / 12 + Z / 12) := by ring
  let T := shortenedTrapezoidalIntegral g (meshCount K h) 0 h (meshRemainder K h)
  let I := ∫ x in 0..K, g x
  have hexpand : T = h * (∑ j ∈ Finset.range (meshCount K h + 1),
      g ((j : ℝ) * h)) - h / 2 * g 0 +
      (meshRemainder K h - h) / 2 * g ((meshCount K h : ℝ) * h) +
      meshRemainder K h / 2 * g K := by
    dsimp [T]
    rw [shortenedTrapezoidalIntegral_grid_expansion g hN h (meshRemainder K h)]
    rw [show (meshCount K h : ℝ) * h + meshRemainder K h = K by exact hdecomp]
  have hrange : h * (∑ j ∈ Finset.range (meshCount K h),
      g ((j : ℝ) * h)) =
      h * (∑ j ∈ Finset.range (meshCount K h + 1), g ((j : ℝ) * h)) -
        h * g ((meshCount K h : ℝ) * h) := by
    rw [Finset.sum_range_succ]
    ring
  have hidentity : h * (∑ j ∈ Finset.range (meshCount K h),
      g ((j : ℝ) * h)) - I =
      (T - I) + h / 2 * g 0 -
        (h + meshRemainder K h) / 2 * g ((meshCount K h : ℝ) * h) -
        meshRemainder K h / 2 * g K := by
    rw [hrange, hexpand]
    dsimp [I]
    ring
  rw [hidentity]
  calc
    _ ≤ |T - I| + |h / 2 * g 0| +
          |(h + meshRemainder K h) / 2 * g ((meshCount K h : ℝ) * h)| +
          |meshRemainder K h / 2 * g K| := by
      let A := T - I
      let B := h / 2 * g 0
      let C := (h + meshRemainder K h) / 2 * g ((meshCount K h : ℝ) * h)
      let D := meshRemainder K h / 2 * g K
      change |A + B - C - D| ≤ |A| + |B| + |C| + |D|
      calc
        |A + B - C - D| = |(A + B) + (-C + -D)| := by
          congr 1
          ring
        _ ≤ |A + B| + |-C + -D| := abs_add_le _ _
        _ ≤ (|A| + |B|) + (|C| + |D|) := by
          gcongr
          · exact abs_add_le _ _
          · have := abs_add_le (-C) (-D)
            simpa only [abs_neg] using this
        _ = |A| + |B| + |C| + |D| := by ring
    _ ≤ h ^ 2 * (K * Z / 12 + Z / 12) + 2 * G * h := by
      have hB : |h / 2 * g 0| ≤ G * h / 2 := by
        rw [abs_mul]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (hg 0 ⟨le_rfl, hK⟩)
           (by positivity : (0 : ℝ) ≤ h / 2)]
      have hC : |(h + meshRemainder K h) / 2 *
          g ((meshCount K h : ℝ) * h)| ≤ G * h := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        calc
          (h + meshRemainder K h) / 2 * |g ((meshCount K h : ℝ) * h)| ≤
              (h + meshRemainder K h) / 2 * G :=
             mul_le_mul_of_nonneg_left (hg _ ⟨by positivity, meshCount_mul_le hh hK⟩)
               (by positivity)
          _ ≤ G * h := by nlinarith [mul_nonneg hG (sub_nonneg.mpr hrh)]
      have hD : |meshRemainder K h / 2 * g K| ≤ G * h / 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (hg K ⟨hK, le_rfl⟩) (by positivity :
          (0 : ℝ) ≤ meshRemainder K h / 2)]
      linarith [hquad, hB, hC, hD]

private theorem square_endpoint_control_of_deriv_bound_new {f : ℝ → ℝ} {N K M : ℝ}
    (hNK : N ≤ K) (_hM : 0 ≤ M) (hf : ∀ x ∈ Icc N K, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ico N K, |deriv f x| ≤ M) (hfK : f K = 0) :
    |f N| ≤ M * (K - N) := by
  rcases eq_or_lt_of_le hNK with rfl | hNK
  · simp [hfK]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hderiv x hx)
  have h' : |f N - f K| ≤ M * (K - N) := by
    simpa [abs_sub_comm] using h K ⟨hNK.le, le_rfl⟩
  rw [hfK, sub_zero] at h'
  exact h'

private def optimizerSquareCore (L x : ℝ) : ℝ := (optimizerCore L x) ^ 2

private theorem optimizerCore_zero {L : ℝ} (_hL : 0 < L) : optimizerCore L 0 = 0 := by
  simp [optimizerCore, Profile.FStar_apply, div_eq_mul_inv]

private theorem optimizerCore_endpoint_zero {L : ℝ} (hL : 0 < L) :
    optimizerCore L (optimizerSupport L) = 0 := by
  rw [optimizerCore, div_self (optimizerSupport_pos hL).ne', Profile.FStar_apply,
    Profile.value_one]
  · simp
  · exact (lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar).ne'
  · exact Profile.cos_ne_one_of_mem_Ioo_two_pi ⟨
      lt_trans (Real.sqrt_pos.2 (by norm_num)) Profile.sqrt_twelve_lt_tStar,
      Profile.tStar_lt_two_pi⟩

private theorem square_continuous_iteratedDeriv_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ ζ : ℝ, 0 ≤ ζ ∧ ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ ζ := by
  let g : ℝ → ℝ := fun x => |iteratedDeriv 2 f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) :=
    (hf.continuous_iteratedDeriv 2 (by norm_num)).continuousOn.abs
  obtain ⟨ζ, hζ⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hζ0 : 0 ≤ ζ := le_trans (norm_nonneg (g 0)) (hζ 0 ⟨le_rfl, hK.le⟩)
  refine ⟨ζ, hζ0, fun x hx => ?_⟩
  simpa [g, Real.norm_eq_abs] using hζ x hx

private theorem square_deriv_bound_exists {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 2 f) (hK : 0 < K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) K, |deriv f x| ≤ M := by
  let g : ℝ → ℝ := fun x => |deriv f x|
  have hg : ContinuousOn g (Icc (0 : ℝ) K) :=
    by simpa [g, iteratedDeriv_one] using
      (hf.continuous_iteratedDeriv 1 (by norm_num)).continuousOn.abs
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_rfl, hK.le⟩)
  refine ⟨M, hM0, fun x hx => ?_⟩
  simpa [g, iteratedDeriv_one, Real.norm_eq_abs] using hM x hx

private theorem square_iteratedDerivWithin_two_le_of_global_bound
    {f : ℝ → ℝ} {a b C : ℝ} (hf : ContDiff ℝ 2 f) (hab : a ≤ b)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ C) :
    ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ C := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · intro x
    by_cases hx : x = a
    · subst x
      rw [iteratedDerivWithin_succ, derivWithin_zero_of_not_accPt]
      · simp [hC]
      · intro ha
        rw [accPt_iff_frequently] at ha
        exact ha (Filter.Eventually.of_forall (by simp))
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure]
      · simpa using hC
      · simp [hx]
  rw [uIcc_of_lt hab]
  intro x
  by_cases hx : x ∈ Icc a b
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      hf.contDiffAt hx]
    exact hbound x hx
  · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
      (by rwa [closure_Icc]), abs_zero]
    exact hC

private theorem square_iteratedDerivWithin_two_le_of_fixed_bound
    {f : ℝ → ℝ} {K C t : ℝ} (hf : ContDiff ℝ 2 f) (_hK : 0 < K)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ Icc (0 : ℝ) K, |iteratedDeriv 2 f x| ≤ C)
    (ht : 0 ≤ t) (htK : t ≤ K) :
    (∀ x, |iteratedDerivWithin 2 f [[0, t]] x| ≤ C) ∧
      (∀ x, |iteratedDerivWithin 2 f [[t, K]] x| ≤ C) := by
  constructor
  · apply square_iteratedDerivWithin_two_le_of_global_bound hf ht hC
    intro x hx
    exact hbound x ⟨hx.1, le_trans hx.2 htK⟩
  · apply square_iteratedDerivWithin_two_le_of_global_bound hf htK hC
    intro x hx
    exact hbound x ⟨le_trans ht hx.1, hx.2⟩

private theorem optimizerSquareCore_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (optimizerSquareCore L) := by
  unfold optimizerSquareCore
  exact (core_contDiff hL).pow 2 |>.of_le (by norm_num)

private theorem optimizerDerivativeSquare_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (fun x => (deriv (optimizerCore L) x) ^ 2) := by
  have hd : ContDiff ℝ 3 (deriv (optimizerCore L)) :=
    (core_contDiff hL).deriv'
  exact (hd.pow 2).of_le (by norm_num)


private theorem optimizerSquareCore_zero {L : ℝ} (hL : 0 < L) :
    optimizerSquareCore L 0 = 0 := by
  simp [optimizerSquareCore, optimizerCore_zero hL]

private theorem optimizerSquareCore_endpoint_zero {L : ℝ} (hL : 0 < L) :
    optimizerSquareCore L (optimizerSupport L) = 0 := by
  simp [optimizerSquareCore, optimizerCore_endpoint_zero hL]

private theorem intervalIntegral_sq_optimizerCore
    {L : ℝ} (hL : 0 < L) :
    (∫ x in 0..optimizerSupport L, optimizerSquareCore L x) =
      (optimizer L hL).squareEnergy := by
  rw [intervalIntegral.integral_congr]
  · exact intervalIntegral_sq_optimizerProfile hL
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) (optimizerSupport L) := by
      simpa [uIcc_of_le (optimizerSupport_pos hL).le] using hx
    simp [optimizerSquareCore, core_eq_profile_on_Icc hL hx']

private theorem profile_square_sum_eq_core_square_sum
    {L h K : ℝ} (hL : 0 < L) (hh : 0 < h) (hK : 0 ≤ K)
    (hSK : K ≤ optimizerSupport L) :
    (∑ j ∈ Finset.range (meshCount K h + 1),
        (optimizerProfile L ((j : ℝ) * h)) ^ 2) =
      ∑ j ∈ Finset.range (meshCount K h + 1),
        (optimizerCore L ((j : ℝ) * h)) ^ 2 := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ meshCount K h := Nat.le_of_lt_succ (by
    simpa using Finset.mem_range.mp hj)
  have hjK : (j : ℝ) * h ≤ K := by
    calc
      (j : ℝ) * h ≤ (meshCount K h : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hjN) (le_of_lt hh)
      _ ≤ K := meshCount_mul_le hh hK
  rw [core_eq_profile_on_Icc hL ⟨by positivity, hjK.trans hSK⟩]

private theorem profile_grid_eq_core_grid_le
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    ∀ j, j ≤ meshCount (optimizerSupport L) h →
      optimizerProfile L ((j : ℝ) * h) = optimizerCore L ((j : ℝ) * h) := by
  intro j hj
  have hjK : (j : ℝ) * h ≤ optimizerSupport L := by
    calc
      (j : ℝ) * h ≤ (meshCount (optimizerSupport L) h : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le
      _ ≤ optimizerSupport L := meshCount_mul_le hh (optimizerSupport_pos hL).le
  exact (core_eq_profile_on_Icc hL ⟨by positivity, hjK⟩).symm

private theorem profile_difference_sum_eq_core_difference_sum
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
      (optimizerProfile L (((j + 1 : ℕ) : ℝ) * h) -
        optimizerProfile L ((j : ℝ) * h)) ^ 2) =
    ∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
      (optimizerCore L (((j + 1 : ℕ) : ℝ) * h) -
        optimizerCore L ((j : ℝ) * h)) ^ 2 := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j + 1 ≤ meshCount (optimizerSupport L) h :=
    Nat.succ_le_iff.mpr (by simpa using Finset.mem_range.mp hj)
  rw [profile_grid_eq_core_grid_le hL hh (j + 1) hjN,
    profile_grid_eq_core_grid_le hL hh j (Nat.le_trans (Nat.le_succ j) hjN)]

private theorem profile_terminal_eq_core_terminal
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    optimizerProfile L ((meshCount (optimizerSupport L) h : ℝ) * h) =
      optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h) := by
  exact profile_grid_eq_core_grid_le hL hh _ le_rfl

private theorem normalized_difference_energy_identity
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    differenceEnergy (sampledKernel h (optimizerProfile L)) / h ^ 3 =
      h * (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
        (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) -
          optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) +
      optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h) ^ 2 / h := by
  rw [differenceEnergy_sampledKernel hh (optimizerSupport_pos hL).le
    (fun x hx => optimizerProfile_eq_zero_of_support_le hL hx)]
  have hzero : optimizerProfile L 0 = optimizerCore L 0 := by
    simpa using profile_grid_eq_core_grid_le hL hh 0 (Nat.zero_le _)
  rw [hzero, optimizerCore_zero hL]
  rw [profile_difference_sum_eq_core_difference_sum hL hh,
    profile_terminal_eq_core_terminal hL hh]
  have hsum :
      (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
        (((optimizerCore L (h * ((j + 1 : ℕ) : ℝ)) -
          optimizerCore L (h * (j : ℝ))) / h) ^ 2)) =
      (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
        (optimizerCore L (h * ((j + 1 : ℕ) : ℝ)) -
          optimizerCore L (h * (j : ℝ))) ^ 2) / h ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp
  have hsum' :
      (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
        (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) -
          optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) =
      (∑ j ∈ Finset.range (meshCount (optimizerSupport L) h),
        (optimizerCore L (((j + 1 : ℕ) : ℝ) * h) -
          optimizerCore L ((j : ℝ) * h)) ^ 2) / h ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
  rw [hsum']
  field_simp [ne_of_gt hh]
  ring

private theorem optimizerCore_terminal_sq_div_le
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hB : 0 ≤ B)
    (hBbound : ∀ x ∈ Icc (0 : ℝ) (optimizerSupport L),
      |deriv (optimizerCore L) x| ≤ B) :
    optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h) ^ 2 / h ≤
      B ^ 2 * h := by
  have hK : 0 ≤ optimizerSupport L := (optimizerSupport_pos hL).le
  have hN : (meshCount (optimizerSupport L) h : ℝ) * h ≤ optimizerSupport L :=
    meshCount_mul_le hh hK
  have hN0 : 0 ≤ (meshCount (optimizerSupport L) h : ℝ) * h := by positivity
  have hend := square_endpoint_control_of_deriv_bound_new hN hB
    (fun _ _ => (core_contDiff hL).contDiffAt.differentiableAt (by norm_num))
    (fun x hx => hBbound x ⟨hN0.trans hx.1, hx.2.le⟩)
    (optimizerCore_endpoint_zero hL)
  have hr0 : 0 ≤ meshRemainder (optimizerSupport L) h :=
    meshRemainder_nonneg hh hK
  have hrh : meshRemainder (optimizerSupport L) h ≤ h :=
    meshRemainder_le hh hK
  have hrem : optimizerSupport L - (meshCount (optimizerSupport L) h : ℝ) * h =
      meshRemainder (optimizerSupport L) h := by
    linarith [meshCount_mul_add_remainder hh hK]
  have hend' : |optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h)| ≤
      B * meshRemainder (optimizerSupport L) h := by
    calc
      _ ≤ B * (optimizerSupport L - (meshCount (optimizerSupport L) h : ℝ) * h) := hend
      _ = _ := by rw [hrem]
  have hsq : |optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h)| ^ 2 ≤
      (B * meshRemainder (optimizerSupport L) h) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB hr0)).mpr hend'
  have hr2 : (meshRemainder (optimizerSupport L) h) ^ 2 ≤ h ^ 2 := by
    nlinarith
  have hmul : (B * meshRemainder (optimizerSupport L) h) ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hr2 (sq_nonneg B)
  apply (div_le_iff₀ hh).2
  have hsq' : optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h) ^ 2 ≤
      (B * meshRemainder (optimizerSupport L) h) ^ 2 := by
    simpa [abs_sq] using hsq
  have hfinal : optimizerCore L ((meshCount (optimizerSupport L) h : ℝ) * h) ^ 2 ≤
      B ^ 2 * h ^ 2 := hsq'.trans hmul
  nlinarith [hfinal]


theorem exists_optimizerProfile_squareEnergy_defect_bound
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerSupport L →
      |squareEnergy (sampledKernel h (optimizerProfile L)) / h -
        (optimizer L hL).squareEnergy| ≤ h ^ 2 * C := by
  let K := optimizerSupport L
  obtain ⟨ζ, hζ, hζbound⟩ := square_continuous_iteratedDeriv_bound
    (optimizerSquareCore_contDiff hL) (optimizerSupport_pos hL)
  obtain ⟨M, hM, hMbound⟩ := square_deriv_bound_exists
    (optimizerSquareCore_contDiff hL) (optimizerSupport_pos hL)
  let C := K * ζ / 12 + ζ / 12 + M / 2
  have hKpos : 0 < K := optimizerSupport_pos hL
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhl
  have hK : 0 ≤ K := hKpos.le
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hζs := square_iteratedDerivWithin_two_le_of_fixed_bound
    (optimizerSquareCore_contDiff hL) hKpos hζ hζbound hN0 hN
  have h₁c : ContDiffOn ℝ 2 (optimizerSquareCore L)
      [[0, (meshCount K h : ℝ) * h]] :=
    (optimizerSquareCore_contDiff hL).contDiffOn
  have h₂c : ContDiffOn ℝ 2 (optimizerSquareCore L)
      [[(meshCount K h : ℝ) * h, K]] :=
    (optimizerSquareCore_contDiff hL).contDiffOn
  have h₁ : IntervalIntegrable (optimizerSquareCore L) volume 0
      ((meshCount K h : ℝ) * h) :=
    (optimizerSquareCore_contDiff hL).continuous.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (optimizerSquareCore L) volume
      ((meshCount K h : ℝ) * h) K :=
    (optimizerSquareCore_contDiff hL).continuous.intervalIntegrable _ _
  have hderiv : ∀ x ∈ Ico ((meshCount K h : ℝ) * h) K,
      |deriv (optimizerSquareCore L) x| ≤ M := by
    intro x hx
    exact hMbound x ⟨hN0.trans hx.1, hx.2.le⟩
  have hfend : |optimizerSquareCore L ((meshCount K h : ℝ) * h)| ≤
      M * meshRemainder K h := by
    apply square_endpoint_control_of_deriv_bound_new hN hM
    · intro x hx
      exact (optimizerSquareCore_contDiff hL).contDiffAt.differentiableAt (by norm_num)
    · exact hderiv
    · exact optimizerSquareCore_endpoint_zero hL
  have hdef := sampledGridSum_sub_integral_le_mul_h_sq (optimizerSquareCore L)
    hh hh1 hhl hζ hζ hM hfend h₁c h₂c hζs.1 hζs.2 h₁ h₂
    (optimizerSquareCore_zero hL) (optimizerSquareCore_endpoint_zero hL)
  rw [intervalIntegral_sq_optimizerCore hL] at hdef
  rw [squareEnergy_sampledKernel hh hK
    (fun x hx => optimizerProfile_eq_zero_of_support_le hL hx)]
  simp only [K] at hdef ⊢
  rw [profile_square_sum_eq_core_square_sum hL hh hK le_rfl]
  have hhd : h ≠ 0 := ne_of_gt hh
  have hrewrite : h ^ 2 *
      (∑ j ∈ Finset.range (meshCount K h + 1),
        (optimizerCore L ((j : ℝ) * h)) ^ 2) / h =
      h * (∑ j ∈ Finset.range (meshCount K h + 1),
        (optimizerCore L ((j : ℝ) * h)) ^ 2) := by
    field_simp
  rw [hrewrite]
  simpa [optimizerSquareCore, C, K] using hdef

theorem exists_optimizerProfile_differenceEnergy_defect_bound
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      h ≤ optimizerSupport L →
      |differenceEnergy (sampledKernel h (optimizerProfile L)) / h ^ 3 -
        (optimizer L hL).dirichletEnergy| ≤ h * C := by
  let K := optimizerSupport L
  let g : ℝ → ℝ := fun x => (deriv (optimizerCore L) x) ^ 2
  obtain ⟨B, hB, hBbound⟩ := square_deriv_bound_exists
    ((core_contDiff hL).of_le (by norm_num)) (optimizerSupport_pos hL)
  obtain ⟨A, hA, hAbound⟩ := square_continuous_iteratedDeriv_bound
    ((core_contDiff hL).of_le (by norm_num)) (optimizerSupport_pos hL)
  obtain ⟨Z, hZ, hZbound⟩ := square_continuous_iteratedDeriv_bound
    (optimizerDerivativeSquare_contDiff hL) (optimizerSupport_pos hL)
  let C := 2 * K * (B + A) * A + (K * Z / 12 + Z / 12 + 2 * B ^ 2) + B ^ 2
  have hK : 0 ≤ K := (optimizerSupport_pos hL).le
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro h hh hh1 hhl
  have hN : (meshCount K h : ℝ) * h ≤ K := meshCount_mul_le hh hK
  have hN0 : 0 ≤ (meshCount K h : ℝ) * h := by positivity
  have hBbound' : ∀ x ∈ Icc (0 : ℝ) K, |deriv (optimizerCore L) x| ≤ B := by
    intro x hx
    exact hBbound x hx
  have hg : ∀ x ∈ Icc (0 : ℝ) K, |g x| ≤ B ^ 2 := by
    intro x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (abs_nonneg (deriv (optimizerCore L) x)) hB).2
      (hBbound' x hx)
    simpa [g] using hs
  have hfd := forwardDifferenceEnergy_sub_derivGridEnergy_le
    (f := optimizerCore L) hh hK ((core_contDiff hL).of_le (by norm_num))
    hBbound' hAbound
  have hfd' : |h * (∑ j ∈ Finset.range (meshCount K h),
      (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) - optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) -
      h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h))| ≤
      h * (2 * K * (B + A) * A) := by
    dsimp [g] at hfd ⊢
    calc
      _ ≤ 2 * K * (B + A * h) * A * h := hfd
      _ ≤ h * (2 * K * (B + A) * A) := by
        have hBA : B + A * h ≤ B + A := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hBA
          (by positivity : (0 : ℝ) ≤ 2 * K * A * h)]
  have hζs := square_iteratedDerivWithin_two_le_of_fixed_bound
    (optimizerDerivativeSquare_contDiff hL) (optimizerSupport_pos hL) hZ hZbound hN0 hN
  have hgrid := leftGridSum_sub_integral_le_mul_h g hh hh1 hhl hZ (sq_nonneg B)
    hg (optimizerDerivativeSquare_contDiff hL).contDiffOn
    (optimizerDerivativeSquare_contDiff hL).contDiffOn hζs.1 hζs.2
    ((optimizerDerivativeSquare_contDiff hL).continuous.intervalIntegrable _ _)
    ((optimizerDerivativeSquare_contDiff hL).continuous.intervalIntegrable _ _)
  have hgrid' : |h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h)) -
      (∫ x in 0..K, g x)| ≤ h * (K * Z / 12 + Z / 12 + 2 * B ^ 2) := by
    have hsq : h ^ 2 ≤ h := by
      nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
    calc
      _ ≤ h ^ 2 * (K * Z / 12 + Z / 12) + 2 * B ^ 2 * h := hgrid
      _ ≤ h * (K * Z / 12 + Z / 12 + 2 * B ^ 2) := by
        have hcoef : 0 ≤ K * Z / 12 + Z / 12 := by positivity
        nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hsq)]
  have hterm := optimizerCore_terminal_sq_div_le hL hh hB hBbound'
  rw [normalized_difference_energy_identity hL hh]
  rw [show (optimizer L hL).dirichletEnergy = ∫ x in 0..K, g x by
    dsimp [g, K]
    exact (intervalIntegral_sq_deriv_optimizerCore hL).symm]
  have hrewrite :
      h * (∑ j ∈ Finset.range (meshCount K h),
        (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) - optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) +
        optimizerCore L ((meshCount K h : ℝ) * h) ^ 2 / h -
        (∫ x in 0..K, g x) =
      (h * (∑ j ∈ Finset.range (meshCount K h),
        (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) - optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) -
        h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h))) +
      (h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h)) - (∫ x in 0..K, g x)) +
      optimizerCore L ((meshCount K h : ℝ) * h) ^ 2 / h := by
    dsimp [g]
    ring
  simp only [K] at hrewrite ⊢
  rw [hrewrite]
  calc
    _ ≤ h * (2 * K * (B + A) * A) + h * (K * Z / 12 + Z / 12 + 2 * B ^ 2) + B ^ 2 * h := by
      calc
        _ ≤ |h * (∑ j ∈ Finset.range (meshCount K h),
          (((optimizerCore L (((j + 1 : ℕ) : ℝ) * h) - optimizerCore L ((j : ℝ) * h)) / h) ^ 2)) -
          h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h))| +
          |h * (∑ j ∈ Finset.range (meshCount K h), g ((j : ℝ) * h)) - (∫ x in 0..K, g x)| +
          |optimizerCore L ((meshCount K h : ℝ) * h) ^ 2 / h| := by
            have htri : ∀ X Y T : ℝ, |X + Y + T| ≤ |X| + |Y| + |T| := by
              intro X Y T
              calc
                |X + Y + T| ≤ |X + Y| + |T| := abs_add_le _ _
                _ ≤ |X| + |Y| + |T| := by
                  gcongr
                  exact abs_add_le _ _
            apply htri
        _ ≤ _ := by
           have ht : 0 ≤ optimizerCore L ((meshCount K h : ℝ) * h) ^ 2 / h :=
             div_nonneg (sq_nonneg _) hh.le
           rw [abs_of_nonneg ht]
           linarith [hfd', hgrid', hterm]
       _ ≤ h * C := by dsimp [C]; ring_nf; exact le_rfl

private theorem tendsto_of_abs_sub_le_mul_right
    {F : ℝ → ℝ} {a C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ δ →
      |F h - a| ≤ h * C) :
    Tendsto F (𝓝[>] 0) (𝓝 a) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    Ioo_mem_nhdsGT hεC] with h hδ' h1 hε'
  rw [Real.dist_eq]
  calc
    |F h - a| ≤ h * C := hbound hδ'.1 h1.2.le hδ'.2.le
    _ < h * (C + 1) := by
      nlinarith [mul_pos hδ'.1 (by norm_num : (0 : ℝ) < 1)]
    _ < ε := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hε'.2

private theorem tendsto_of_abs_sub_le_sq_mul_right
    {F : ℝ → ℝ} {a C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : ∀ {h : ℝ}, 0 < h → h ≤ 1 → h ≤ δ →
      |F h - a| ≤ h ^ 2 * C) :
    Tendsto F (𝓝[>] 0) (𝓝 a) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    Ioo_mem_nhdsGT hεC] with h hδ' h1 hε'
  rw [Real.dist_eq]
  have hsq : h ^ 2 ≤ h := by
    nlinarith [mul_nonneg h1.1.le (sub_nonneg.mpr h1.2.le)]
  calc
    |F h - a| ≤ h ^ 2 * C := hbound hδ'.1 h1.2.le hδ'.2.le
    _ ≤ h * C := mul_le_mul_of_nonneg_right hsq hC
    _ < h * (C + 1) := by
      nlinarith [mul_pos hδ'.1 (by norm_num : (0 : ℝ) < 1)]
    _ < ε := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hε'.2

theorem tendsto_squareEnergy_sampledKernel_div
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun h : ℝ => squareEnergy (sampledKernel h (optimizerProfile L)) / h)
      (𝓝[>] 0) (𝓝 (optimizer L hL).squareEnergy) := by
  obtain ⟨C, hC, hbound⟩ := exists_optimizerProfile_squareEnergy_defect_bound hL
  apply tendsto_of_abs_sub_le_sq_mul_right hC (optimizerSupport_pos hL)
  intro h hh hh1 hK
  exact hbound hh hh1 hK

theorem tendsto_differenceEnergy_sampledKernel_div
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun h : ℝ => differenceEnergy (sampledKernel h (optimizerProfile L)) / h ^ 3)
      (𝓝[>] 0) (𝓝 (optimizer L hL).dirichletEnergy) := by
  obtain ⟨C, hC, hbound⟩ := exists_optimizerProfile_differenceEnergy_defect_bound hL
  apply tendsto_of_abs_sub_le_mul_right hC (optimizerSupport_pos hL)
  intro h hh hh1 hK
  simpa using hbound hh hh1 hK

theorem tendsto_scaled_rayleighQuotient_sampledKernel
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun h : ℝ => (h⁻¹) ^ 2 * rayleighQuotient
        (sampledKernel h (optimizerProfile L)))
      (𝓝[>] 0) (𝓝 (optimizer L hL).rayleighQuotient) := by
  have hnum := tendsto_differenceEnergy_sampledKernel_div hL
  have hden := tendsto_squareEnergy_sampledKernel_div hL
  have hden_pos : 0 < (optimizer L hL).squareEnergy :=
    Analysis.HalfLineH1.squareEnergy_pos_of_mass_eq_one
      (optimizer_isAdmissible hL).mass_eq
  have hquot : Tendsto
      (fun h : ℝ =>
        (differenceEnergy (sampledKernel h (optimizerProfile L)) / h ^ 3) /
          (squareEnergy (sampledKernel h (optimizerProfile L)) / h))
      (𝓝[>] 0) (𝓝 ((optimizer L hL).dirichletEnergy /
        (optimizer L hL).squareEnergy)) := by
    exact hnum.div hden hden_pos.ne'
  have hpos : ∀ᶠ h in 𝓝[>] 0,
      0 < squareEnergy (sampledKernel h (optimizerProfile L)) / h := by
    exact hden (Ioi_mem_nhds hden_pos)
  apply hquot.congr'
  filter_upwards [hpos, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh hh1
  have hh0 : h ≠ 0 := ne_of_gt hh1.1
  have hS : squareEnergy (sampledKernel h (optimizerProfile L)) ≠ 0 := by
    intro hS
    rw [hS, zero_div] at hh
    linarith
  dsimp [rayleighQuotient]
  field_simp [hh0, hS]

end RayleighKernel.Discrete
