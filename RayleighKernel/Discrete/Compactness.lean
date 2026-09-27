import RayleighKernel.Discrete.Recovery
import RayleighKernel.Discrete.EnergyIdentities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open scoped BigOperators Interval
open RayleighKernel.Analysis
open RayleighKernel.Analysis.HalfLineH1

private def prev (w : Kernel) : Kernel
  | 0 => 0
  | k + 1 => w k

private theorem difference_eq_sub_prev (w : Kernel) (k : ℕ) :
    difference w k = w k - prev w k := by
  cases k <;> simp [prev]

private theorem sq_sub_sq_difference (w : Kernel) (k : ℕ) :
    (w k)^2 - (prev w k)^2 = difference w k * (w k + prev w k) := by
  rw [difference_eq_sub_prev]
  ring

private theorem sum_sq_sub_sq_prev (w : Kernel) (j : ℕ) :
    (w j)^2 = ∑ k ∈ Finset.range (j + 1),
      difference w k * (w k + prev w k) := by
  induction j with
  | zero => simp [prev, difference]; ring
  | succ j ih =>
      calc
        (w (j + 1))^2 = (w j)^2 +
            difference w (j + 1) * (w (j + 1) + prev w (j + 1)) := by
          rw [difference_eq_sub_prev]
          simp only [prev]
          ring
        _ = (∑ k ∈ Finset.range (j + 1),
            difference w k * (w k + prev w k)) +
            difference w (j + 1) * (w (j + 1) + prev w (j + 1)) := by rw [← ih]
        _ = _ := by
          symm
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Finset.sum_range_succ
              (fun k => difference w k * (w k + prev w k)) (j + 1))

private theorem finite_difference_sq_le {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), (difference w k)^2) ≤ differenceEnergy w := by
  exact hw.summable_difference_sq.sum_le_tsum
    (Finset.range (j + 1)) (fun k hk => sq_nonneg _)

private theorem finite_plus_sq_le_four {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), (w k + prev w k)^2) ≤ 4 * squareEnergy w := by
  have hp : ∀ k, (w k + prev w k)^2 ≤
      2 * (w k)^2 + 2 * (prev w k)^2 := by
    intro k
    nlinarith [sq_nonneg (w k - prev w k)]
  have hsum := Finset.sum_le_sum (s := Finset.range (j + 1)) (fun k hk => hp k)
  have hprev_eq : (∑ k ∈ Finset.range (j + 1), (prev w k)^2) =
      ∑ k ∈ Finset.range j, (w k)^2 := by
    clear hp hsum
    induction j with
    | zero => simp [prev]
    | succ j ih =>
        simpa [Finset.sum_range_succ, prev] using ih
  have hprev : (∑ k ∈ Finset.range (j + 1), (prev w k)^2) ≤ squareEnergy w := by
    rw [hprev_eq]
    exact hw.summable_sq.sum_le_tsum (Finset.range j) (fun k hk => sq_nonneg _)
  have hwfinite : (∑ k ∈ Finset.range (j + 1), (w k)^2) ≤ squareEnergy w :=
    hw.summable_sq.sum_le_tsum (Finset.range (j + 1)) (fun k hk => sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ Finset.range (j + 1),
        (2 * (w k)^2 + 2 * (prev w k)^2) := hsum
    _ = 2 * (∑ k ∈ Finset.range (j + 1), (w k)^2) +
        2 * (∑ k ∈ Finset.range (j + 1), (prev w k)^2) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 4 * squareEnergy w := by nlinarith

private theorem pointwise_fourth_le {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) (j : ℕ) :
    (w j)^4 ≤ 4 * differenceEnergy w * squareEnergy w := by
  have htel := sum_sq_sub_sq_prev w j
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1))
    (fun k => difference w k) (fun k => w k + prev w k)
  have hd := finite_difference_sq_le hw j
  have hp := finite_plus_sq_le_four hw j
  have hfour : (w j)^4 =
      (∑ k ∈ Finset.range (j + 1),
        difference w k * (w k + prev w k))^2 := by
    rw [show (w j)^4 = ((w j)^2)^2 by ring, htel]
  have hmul := mul_le_mul hd hp
    (Finset.sum_nonneg (fun k hk => sq_nonneg _)) hw.differenceEnergy_nonneg
  exact hfour.symm ▸ le_trans hc (by nlinarith [hmul])

theorem squareEnergy_cubed_le_four_mul_differenceEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (squareEnergy w)^3 ≤ 4 * differenceEnergy w := by
  have hS : 0 < squareEnergy w := hw.squareEnergy_pos
  have hN : 0 ≤ differenceEnergy w := hw.differenceEnergy_nonneg
  let M : ℝ := Real.sqrt (Real.sqrt (4 * differenceEnergy w * squareEnergy w))
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M^2 = Real.sqrt (4 * differenceEnergy w * squareEnergy w) := by
    dsimp [M]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hM4 : M^4 = 4 * differenceEnergy w * squareEnergy w := by
    rw [show M^4 = (M^2)^2 by ring, hM2, Real.sq_sqrt]
    positivity
  have hpoint : ∀ j, w j ≤ M := by
    intro j
    have hf := pointwise_fourth_le hw j
    have hsqrt : (Real.sqrt (4 * differenceEnergy w * squareEnergy w)) ^ 2 =
        4 * differenceEnergy w * squareEnergy w := Real.sq_sqrt (by positivity)
    have hsq : (w j)^2 ≤ M^2 := by nlinarith [hf, hsqrt, hM2]
    nlinarith [hw.nonnegative j]
  have hsum : squareEnergy w ≤ M * mass w := by
    rw [squareEnergy, mass]
    have hterm : ∀ j, (w j)^2 ≤ M * w j := by
      intro j
      nlinarith [hpoint j, hw.nonnegative j]
    have ht := hw.summable_sq.tsum_le_tsum (fun j => hterm j) (by
      exact hw.summable.mul_left M)
    simpa [← tsum_mul_left] using ht
  rw [hw.mass_eq] at hsum
  have hSnonneg : 0 ≤ squareEnergy w := hS.le
  have hpow : (squareEnergy w)^4 ≤ M^4 := by
    simpa using (pow_le_pow_left₀ hSnonneg hsum 4)
  have hcancel : squareEnergy w * (squareEnergy w)^3 ≤
      squareEnergy w * (4 * differenceEnergy w) := by
    nlinarith [hpow, hM4]
  nlinarith [hcancel, hS]

private theorem scaled_energy_bounds {h L Q : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    0 ≤ Q ∧ differenceEnergy w / (h^2 * squareEnergy w) ≤ Q ∧
      squareEnergy w / h ≤ 1 + 4 * Q := by
  have hh : 0 < h := hw.h_pos
  have hS : 0 < squareEnergy w := hw.squareEnergy_pos
  have hq : 0 ≤ rayleighQuotient w := hw.rayleighQuotient_nonneg
  have hQ0 : 0 ≤ Q := by
    have hi : 0 ≤ (h⁻¹)^2 := sq_nonneg _
    nlinarith [hQ, hq]
  have hscaled : differenceEnergy w / (h^2 * squareEnergy w) ≤ Q := by
    unfold rayleighQuotient at hQ
    field_simp [ne_of_gt hh, ne_of_gt hS] at hQ ⊢
    nlinarith [hQ]
  have hx_sq : (squareEnergy w / h)^2 ≤ 4 * Q := by
    have hs := squareEnergy_cubed_le_four_mul_differenceEnergy hw
    have hq' := hscaled
    field_simp [ne_of_gt hh, ne_of_gt hS] at hq' ⊢
    nlinarith [hs, hq']
  have hx : squareEnergy w / h ≤ 1 + 4 * Q := by
    have hx0 : 0 ≤ squareEnergy w / h := div_nonneg (le_of_lt hS) (le_of_lt hh)
    nlinarith [hx_sq]
  exact ⟨hQ0, hscaled, hx⟩

theorem interpolant_squareEnergy_le_of_scaled_rayleighQuotient_le
    {h L Q : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    (∫ x, (interpolant h w x)^2) ≤ 1 + 4 * Q := by
  obtain ⟨hQ0, hscaled, hx⟩ := scaled_energy_bounds hw hQ
  have hh : 0 < h := hw.h_pos
  have hN : 0 ≤ differenceEnergy w := hw.differenceEnergy_nonneg
  rw [integral_sq_interpolant hw]
  have hz : 0 ≤ differenceEnergy w / (6 * h) := by positivity
  nlinarith

theorem interpolant_dirichletEnergy_le_of_scaled_rayleighQuotient_le
    {h L Q : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    (∫ x, (deriv (interpolant h w) x)^2) ≤ Q * (1 + 4 * Q) := by
  obtain ⟨hQ0, hscaled, hx⟩ := scaled_energy_bounds hw hQ
  have hh : 0 < h := hw.h_pos
  have hS : 0 < squareEnergy w := hw.squareEnergy_pos
  rw [integral_sq_deriv_interpolant hw]
  have hrewrite : differenceEnergy w / h^3 =
      (differenceEnergy w / (h^2 * squareEnergy w)) * (squareEnergy w / h) := by
    field_simp [ne_of_gt hh, ne_of_gt hS]
  rw [hrewrite]
  exact mul_le_mul hscaled hx (by positivity) hQ0

theorem exists_interpolant_energy_bound_of_scaled_rayleighQuotient_le
    {h L Q : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∫ x, (interpolant h w x)^2) ≤ B ∧
      (∫ x, (deriv (interpolant h w) x)^2) ≤ B := by
  have hQ0 : 0 ≤ Q := (scaled_energy_bounds hw hQ).1
  let B : ℝ := (1 + 4 * Q) + Q * (1 + 4 * Q)
  refine ⟨B, ?_, ?_, ?_⟩
  · dsimp [B]
    positivity
  · exact (interpolant_squareEnergy_le_of_scaled_rayleighQuotient_le hw hQ).trans
      (by dsimp [B]; nlinarith)
  · exact (interpolant_dirichletEnergy_le_of_scaled_rayleighQuotient_le hw hQ).trans
      (by dsimp [B]; nlinarith [hQ0])

theorem exists_uniform_interpolant_energy_bound_of_scaled_rayleighQuotient_le
    {h : ℕ → ℝ} {L Q : ℝ} {w : ℕ → Kernel}
    (hw : ∀ n, IsAdmissible (h n) L (w n))
    (hQ : ∀ n, ((h n)⁻¹)^2 * rayleighQuotient (w n) ≤ Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ x, (interpolant (h n) (w n) x)^2) ≤ B ∧
      (∫ x, (deriv (interpolant (h n) (w n)) x)^2) ≤ B := by
  have hQ0 : 0 ≤ Q := (scaled_energy_bounds (hw 0) (hQ 0)).1
  let B : ℝ := (1 + 4 * Q) + Q * (1 + 4 * Q)
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    positivity
  · intro n
    refine ⟨?_, ?_⟩
    · exact (interpolant_squareEnergy_le_of_scaled_rayleighQuotient_le (hw n) (hQ n)).trans
        (by dsimp [B]; nlinarith)
    · exact (interpolant_dirichletEnergy_le_of_scaled_rayleighQuotient_le (hw n) (hQ n)).trans
        (by dsimp [B]; nlinarith [hQ0])

def interpolantH1Energy (h : ℝ) (w : Kernel) : ℝ :=
  (∫ x, (interpolant h w x)^2) +
    ∫ x, (deriv (interpolant h w) x)^2

theorem interpolantH1Energy_le_of_scaled_rayleighQuotient_le
    {h L Q : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (hQ : (h⁻¹)^2 * rayleighQuotient w ≤ Q) :
    interpolantH1Energy h w ≤ (1 + 4 * Q) + Q * (1 + 4 * Q) := by
  rw [interpolantH1Energy]
  have hs := interpolant_squareEnergy_le_of_scaled_rayleighQuotient_le hw hQ
  have hd := interpolant_dirichletEnergy_le_of_scaled_rayleighQuotient_le hw hQ
  have hQ0 := (scaled_energy_bounds hw hQ).1
  nlinarith

theorem eventually_interpolantH1Energy_le_of_nearMinimizer
    (L : ℝ) (hL : 0 < L)
    {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0))
    (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n,
      ((mesh n)⁻¹)^2 * rayleighQuotient (w n) ≤
        scaledDiscreteMinimum (mesh n) L + eps n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, interpolantH1Energy (mesh n) (w n) ≤ C := by
  let Q : ℝ := (optimizer L hL).rayleighQuotient + 2
  let C : ℝ := (1 + 4 * Q) + Q * (1 + 4 * Q)
  have hopt : 0 ≤ (optimizer L hL).rayleighQuotient :=
    (rayleighQuotient_pos_of_mass_eq_one
      (optimizer_isAdmissible hL).mass_eq).le
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    linarith
  have hmin : ∀ᶠ n in atTop,
      scaledDiscreteMinimum (mesh n) L ≤ (optimizer L hL).rayleighQuotient + 1 :=
    hmesh (eventually_scaledDiscreteMinimum_le_add L hL
      (by norm_num : (0 : ℝ) < 1))
  have heps' : ∀ᶠ n in atTop, eps n < 1 :=
    heps (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · filter_upwards [hmin, heps'] with n hnmin hneps
    apply interpolantH1Energy_le_of_scaled_rayleighQuotient_le (hw n)
    dsimp [Q]
    have hbound := hnear n
    linarith

theorem interpolant_zero_sq_le_mul_dirichletEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (interpolant h w 0)^2 ≤ h * (∫ x, (deriv (interpolant h w) x)^2) := by
  have hh := hw.h_pos
  have h0 : (w 0)^2 ≤ differenceEnergy w := by
    rw [differenceEnergy]
    simpa [difference_zero] using
      (hw.summable_difference_sq.sum_le_tsum (Finset.range 1)
        (fun k hk => sq_nonneg (difference w k)))
  rw [interpolant_zero hh, integral_sq_deriv_interpolant hw]
  field_simp [ne_of_gt hh]
  nlinarith

theorem tendsto_interpolant_zero_of_tendsto_mesh_of_dirichletEnergy_le
    {h : ℕ → ℝ} {L B : ℝ} {w : ℕ → Kernel}
    (hh : Tendsto h atTop (𝓝[>] 0))
    (hw : ∀ n, IsAdmissible (h n) L (w n))
    (hB : ∀ n, (∫ x, (deriv (interpolant (h n) (w n)) x)^2) ≤ B) :
    Tendsto (fun n => interpolant (h n) (w n) 0) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := by
    have hE : 0 ≤ (∫ x, (deriv (interpolant (h 0) (w 0)) x)^2) := by
      rw [integral_sq_deriv_interpolant (hw 0)]
      exact div_nonneg (hw 0).differenceEnergy_nonneg
        (le_of_lt (pow_pos (hw 0).h_pos 3))
    linarith [hB 0]
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := ε^2 / (B + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (sq_pos_of_pos hε) (by linarith)
  have hev : ∀ᶠ n in atTop, h n ∈ Ioo 0 δ :=
    hh (Ioo_mem_nhdsGT hδ)
  filter_upwards [hev] with n hn
  have hsq := interpolant_zero_sq_le_mul_dirichletEnergy (hw n)
  have henergy := hB n
  have hnon : 0 ≤ interpolant (h n) (w n) 0 :=
    interpolant_nonneg (hw n).h_pos (hw n).nonnegative 0
  have hsqε : (interpolant (h n) (w n) 0)^2 < ε^2 := by
    have hmul : h n * B ≤ h n * (B + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hn.1)
    have hlt : h n * (B + 1) < ε^2 := by
      apply (lt_div_iff₀ (by linarith : 0 < B + 1)).mp
      simpa [δ] using hn.2
    nlinarith
  rw [dist_zero_right]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg hnon]
  nlinarith [sq_nonneg (interpolant (h n) (w n) 0)]

private theorem telescoping_Ioc {w : Kernel} {i j : ℕ} (hij : i ≤ j) :
    w j - w i = ∑ k ∈ Finset.Ioc i j, difference w k := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      rw [Finset.sum_Ioc_succ_top hj]
      rw [difference_succ]
      rw [← ih]
      ring

private theorem node_sub_node_sq_le_nat_sub_mul_differenceEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) {i j : ℕ} (hij : i ≤ j) :
    (w j - w i)^2 ≤ (j - i : ℝ) * differenceEnergy w := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioc i j)
    (fun k => difference w k) (fun _ => (1 : ℝ))
  have hs : (∑ k ∈ Finset.Ioc i j, (difference w k)^2) ≤ differenceEnergy w :=
    hw.summable_difference_sq.sum_le_tsum (Finset.Ioc i j) (fun k hk => sq_nonneg _)
  have hcard : (∑ _k ∈ Finset.Ioc i j, (1 : ℝ)^2) = (j - i : ℝ) := by
    rw [show (∑ _k ∈ Finset.Ioc i j, (1 : ℝ)^2) = (Finset.Ioc i j).card by simp]
    rw [Nat.card_Ioc]
    simp [Nat.cast_sub hij]
  rw [show w j - w i = ∑ k ∈ Finset.Ioc i j, difference w k from telescoping_Ioc hij]
  have hnon : 0 ≤ (j : ℝ) - i := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    simp
  calc
    (∑ k ∈ Finset.Ioc i j, difference w k) ^ 2 ≤
        (∑ k ∈ Finset.Ioc i j, (difference w k)^2) *
          ∑ k ∈ Finset.Ioc i j, (1 : ℝ)^2 := by simpa using hc
    _ = (j - i : ℝ) * (∑ k ∈ Finset.Ioc i j, (difference w k)^2) := by rw [hcard]; ring
    _ ≤ (j - i : ℝ) * differenceEnergy w := by
      exact mul_le_mul_of_nonneg_left hs hnon

private theorem ordered_interpolant_node_sub_node_sq_le_mul_dirichletEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) {i j : ℕ} (hij : i ≤ j) :
    (interpolant h w ((j : ℝ) * h) -
      interpolant h w ((i : ℝ) * h)) ^ 2 ≤
      |((j : ℝ) * h) - ((i : ℝ) * h)| *
        (∫ x, (deriv (interpolant h w) x)^2) := by
  have hh := hw.h_pos
  rw [interpolant_node hh j, interpolant_node hh i,
    integral_sq_deriv_interpolant hw]
  have hd : 0 ≤ (j : ℝ) - (i : ℝ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    simp
  have habs : |((j : ℝ) * h) - ((i : ℝ) * h)| = (j - i : ℝ) * h := by
    rw [show ((j : ℝ) * h) - ((i : ℝ) * h) = ((j : ℝ) - (i : ℝ)) * h by ring,
      abs_of_nonneg (mul_nonneg hd hh.le)]
  rw [habs]
  have hmain := node_sub_node_sq_le_nat_sub_mul_differenceEnergy hw hij
  field_simp [ne_of_gt hh]
  nlinarith

theorem interpolant_node_sub_node_sq_le_mul_dirichletEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (i j : ℕ) :
    (interpolant h w ((j : ℝ) * h) -
      interpolant h w ((i : ℝ) * h)) ^ 2 ≤
      |((j : ℝ) * h) - ((i : ℝ) * h)| *
        (∫ x, (deriv (interpolant h w) x)^2) := by
  rcases le_total i j with hij | hji
  · exact ordered_interpolant_node_sub_node_sq_le_mul_dirichletEnergy hw hij
  · rw [show (interpolant h w ((j : ℝ) * h) - interpolant h w ((i : ℝ) * h)) ^ 2 =
        (interpolant h w ((i : ℝ) * h) - interpolant h w ((j : ℝ) * h)) ^ 2 by ring]
    rw [abs_sub_comm]
    exact ordered_interpolant_node_sub_node_sq_le_mul_dirichletEnergy hw hji

private theorem difference_sq_le_differenceEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) (k : ℕ) :
    (difference w k)^2 ≤ differenceEnergy w := by
  rw [differenceEnergy]
  simpa using hw.summable_difference_sq.sum_le_tsum ({k})
    (fun j hj => sq_nonneg (difference w j))

private theorem interpolant_sub_left_node_sq_le_mul_dirichletEnergy
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (i : ℕ) {x : ℝ}
    (hx : x ∈ Ico ((i : ℝ) * h) ((i + 1 : ℕ) * h)) :
    (interpolant h w x - interpolant h w ((i : ℝ) * h))^2 ≤
      h * (∫ z, (deriv (interpolant h w) z)^2) := by
  have hh := hw.h_pos
  have hleft : 0 ≤ x - (i : ℝ) * h := sub_nonneg.mpr hx.1
  have hright : x - (i : ℝ) * h ≤ h := by
    have hi := hx.2
    norm_num [Nat.cast_add, add_mul] at hi ⊢
    linarith
  rw [interpolant_cell hh i hx, interpolant_node hh i,
    show w (i + 1) - w i = difference w (i + 1) by rfl,
    integral_sq_deriv_interpolant hw]
  have hd := difference_sq_le_differenceEnergy hw (i + 1)
  have ht : (x - (i : ℝ) * h)^2 ≤ h^2 := by
    nlinarith [sq_nonneg (x - (i : ℝ) * h), sq_nonneg (h - (x - (i : ℝ) * h))]
  have hp : (x - (i : ℝ) * h)^2 * (difference w (i + 1))^2 ≤
      h^2 * differenceEnergy w := by
    exact mul_le_mul ht hd (sq_nonneg _) (by positivity)
  field_simp [ne_of_gt hh]
  nlinarith [hp]

private theorem mem_floor_cell {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    x ∈ Ico (((⌊x / h⌋₊ : ℕ) : ℝ) * h)
      (((⌊x / h⌋₊ + 1 : ℕ) : ℝ) * h) := by
  have hxph : 0 ≤ x / h := by positivity
  constructor
  · exact (le_div_iff₀ hh).mp (Nat.floor_le hxph)
  · have hf := Nat.lt_floor_add_one (x / h)
    norm_num [Nat.cast_add, add_mul] at hf ⊢
    simpa [Nat.cast_add, add_mul] using (div_lt_iff₀ hh).mp hf

private theorem floor_mesh_node_distance_le {h x y : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |(((⌊y / h⌋₊ : ℕ) : ℝ) * h) -
      (((⌊x / h⌋₊ : ℕ) : ℝ) * h)| ≤ |y - x| + 2 * h := by
  let i : ℕ := ⌊x / h⌋₊
  let j : ℕ := ⌊y / h⌋₊
  have hxi : x ∈ Ico ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h) := by
    simpa [i] using (mem_floor_cell hh hx)
  have hyj : y ∈ Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) := by
    simpa [j] using (mem_floor_cell hh hy)
  have hxi_lower : (i : ℝ) * h ≤ x := hxi.1
  have hyj_lower : (j : ℝ) * h ≤ y := hyj.1
  have hxi_upper : x < (i : ℝ) * h + h := by
    have ht := hxi.2
    norm_num [Nat.cast_add, add_mul] at ht ⊢
    exact ht
  have hyj_upper : y < (j : ℝ) * h + h := by
    have ht := hyj.2
    norm_num [Nat.cast_add, add_mul] at ht ⊢
    exact ht
  change |(j : ℝ) * h - (i : ℝ) * h| ≤ |y - x| + 2 * h
  rw [abs_le]
  constructor
  · have hneg : -(y - x) ≤ |y - x| := neg_le_abs (y - x)
    linarith
  · have habs : y - x ≤ |y - x| := le_abs_self (y - x)
    linarith

theorem interpolant_sub_sq_le_mesh_modulus
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (interpolant h w y - interpolant h w x)^2 ≤
      3 * (|y - x| + 4 * h) *
        (∫ z, (deriv (interpolant h w) z)^2) := by
  let i : ℕ := ⌊x / h⌋₊
  let j : ℕ := ⌊y / h⌋₊
  let E : ℝ := ∫ z, (deriv (interpolant h w) z)^2
  have hxi : x ∈ Ico ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h) := by
    simpa [i] using (mem_floor_cell hw.h_pos hx)
  have hyj : y ∈ Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) := by
    simpa [j] using (mem_floor_cell hw.h_pos hy)
  have ha : (interpolant h w y - interpolant h w ((j : ℝ) * h))^2 ≤ h * E := by
    simpa [E] using interpolant_sub_left_node_sq_le_mul_dirichletEnergy hw j hyj
  have hb : (interpolant h w ((j : ℝ) * h) - interpolant h w ((i : ℝ) * h))^2 ≤
      |(j : ℝ) * h - (i : ℝ) * h| * E := by
    simpa [E] using interpolant_node_sub_node_sq_le_mul_dirichletEnergy hw i j
  have hc0 : (interpolant h w x - interpolant h w ((i : ℝ) * h))^2 ≤ h * E := by
    simpa [E] using interpolant_sub_left_node_sq_le_mul_dirichletEnergy hw i hxi
  have hc : (interpolant h w ((i : ℝ) * h) - interpolant h w x)^2 ≤ h * E := by
    calc
      (interpolant h w ((i : ℝ) * h) - interpolant h w x)^2 =
          (interpolant h w x - interpolant h w ((i : ℝ) * h))^2 := by ring
      _ ≤ h * E := hc0
  have hE : 0 ≤ E := by
    dsimp [E]
    rw [integral_sq_deriv_interpolant hw]
    exact div_nonneg hw.differenceEnergy_nonneg (pow_pos hw.h_pos 3).le
  have hd : |(j : ℝ) * h - (i : ℝ) * h| ≤ |y - x| + 2 * h := by
    simpa [i, j] using floor_mesh_node_distance_le hw.h_pos hx hy
  let a : ℝ := interpolant h w y - interpolant h w ((j : ℝ) * h)
  let b : ℝ := interpolant h w ((j : ℝ) * h) - interpolant h w ((i : ℝ) * h)
  let c : ℝ := interpolant h w ((i : ℝ) * h) - interpolant h w x
  have hthree : (a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hsum : a^2 + b^2 + c^2 ≤ (2 * h + |(j : ℝ) * h - (i : ℝ) * h|) * E := by
    dsimp [a, b, c] at *
    nlinarith
  have hnodeMul : |(j : ℝ) * h - (i : ℝ) * h| * E ≤
      (|y - x| + 2 * h) * E :=
    mul_le_mul_of_nonneg_right hd hE
  have hcoef : (2 * h + |(j : ℝ) * h - (i : ℝ) * h|) * E ≤
      (|y - x| + 4 * h) * E := by
    have hhE : 0 ≤ h * E := mul_nonneg hw.h_pos.le hE
    nlinarith [hnodeMul]
  have hfinal : (a + b + c)^2 ≤ 3 * (|y - x| + 4 * h) * E := by
    nlinarith [hthree, hsum, hcoef]
  calc
    (interpolant h w y - interpolant h w x)^2 = (a + b + c)^2 := by
      dsimp [a, b, c]
      ring
    _ ≤ 3 * (|y - x| + 4 * h) * E := hfinal
    _ = 3 * (|y - x| + 4 * h) * (∫ z, (deriv (interpolant h w) z)^2) := by rfl
end RayleighKernel.Discrete
