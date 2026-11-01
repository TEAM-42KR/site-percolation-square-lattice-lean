import SitePerc.Base
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Uniform sampling with replacement on a finite board

The sample space is the set of words of length `m`, not a product of
independent completed-site indicators. All configurations below are images
of those words under the range map.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SitePerc

abbrev DrawsM (n m : ℕ) := Fin m → Board n

noncomputable def completedM (n m : ℕ) (draw : DrawsM n m) :
    Configuration (Board n) := by
  classical
  exact fun v => decide (∃ i, draw i = v)

noncomputable def roadLawM (n m : ℕ) : Measure (DrawsM n m) :=
  (Fintype.card (DrawsM n m) : ℝ≥0∞)⁻¹ • Measure.count

noncomputable def roadDensityM (n m : ℕ) (draw : DrawsM n m) : ℝ :=
  (largestCluster (boardGraph n) (completedM n m draw) : ℝ) / (n + 1) ^ 2

noncomputable def occupiedM (n m : ℕ) (draw : DrawsM n m) : Finset (Board n) := by
  classical
  exact Finset.univ.image draw

noncomputable def occupancyDensityM (n m : ℕ) (draw : DrawsM n m) : ℝ :=
  ((occupiedM n m draw).card : ℝ) / (n + 1) ^ 2

noncomputable def completionParameter (c : ℝ) (hc : 0 ≤ c) : Parameter :=
  ⟨1 - Real.exp (-c), by
    constructor
    · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc)
      linarith
    · have h := Real.exp_pos (-c)
      linarith⟩

def configurationLE {A : Type} (ω η : Configuration A) : Prop :=
  ∀ v, ω v = true → η v = true

def increasingEvent {A : Type} (U : Set (Configuration A)) : Prop :=
  ∀ ω η, configurationLE ω η → ω ∈ U → η ∈ U

namespace Occupancy

open scoped Classical

noncomputable def uniformLaw (A : Type) [Fintype A] [MeasurableSpace A] : Measure A :=
  (Fintype.card A : ℝ≥0∞)⁻¹ • Measure.count

noncomputable def average {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

noncomputable def rangeFinset {A : Type} [DecidableEq A] {m : ℕ}
    (w : Fin m → A) : Finset A := Finset.univ.image w

noncomputable def emptyIndicator {A : Type} [DecidableEq A] {m : ℕ}
    (v : A) (w : Fin m → A) : ℝ := if v ∉ rangeFinset w then 1 else 0

noncomputable def sampleLaw (A : Type) [Fintype A] [MeasurableSpace A] (m : ℕ) :
    Measure (Fin m → A) := uniformLaw (Fin m → A)

noncomputable def wordConfiguration {A : Type} [Fintype A] {m : ℕ}
    (w : Fin m → A) : Configuration A := fun v => decide (∃ i, w i = v)

noncomputable def openFinset {A : Type} [Fintype A] (ω : Configuration A) : Finset A :=
  Finset.univ.filter (fun v => ω v = true)

def relabel {A : Type} (e : Equiv.Perm A) (ω : Configuration A) : Configuration A :=
  fun v => ω (e.symm v)

noncomputable def symmetrize {A : Type} [Fintype A]
    (f : Configuration A → ℝ) (ω : Configuration A) : ℝ :=
  average (fun e : Equiv.Perm A => f (relabel e ω))

theorem uniformLaw_apply (A : Type) [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (s : Set A) :
    uniformLaw A s = (s.toFinite.toFinset.card : ℝ≥0∞) / Fintype.card A := by
  rw [uniformLaw, Measure.smul_apply, smul_eq_mul, Measure.count_apply_finite s s.toFinite]
  exact mul_comm _ _

private theorem uniformLaw_filter (A : Type) [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (P : A → Prop) [DecidablePred P] :
    uniformLaw A {a | P a} =
      ((Finset.univ.filter P).card : ℝ≥0∞) / Fintype.card A := by
  classical
  rw [uniformLaw_apply]
  have h : {a | P a}.toFinite.toFinset = Finset.univ.filter P := by ext; simp
  rw [h]

instance uniformLaw_probability (A : Type) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    IsProbabilityMeasure (uniformLaw A) := by
  constructor
  rw [uniformLaw_apply]
  have h : (Set.univ : Set A).toFinite.toFinset = Finset.univ := by ext; simp
  rw [h, Finset.card_univ]
  exact ENNReal.div_self (by simp [Fintype.card_ne_zero]) (by simp)

instance sampleLaw_probability (A : Type) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ) :
    IsProbabilityMeasure (sampleLaw A m) := uniformLaw_probability _

private theorem uniformLaw_real_filter (A : Type) [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (P : A → Prop) [DecidablePred P] :
    (uniformLaw A).real {a | P a} =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card A := by
  classical
  simp [measureReal_def, uniformLaw_filter, ENNReal.toReal_div]

private theorem avoidance_card (A : Type) [Fintype A] [DecidableEq A]
    (m : ℕ) (s : Finset A) :
    (Finset.univ.filter (fun w : Fin m → A => ∀ i, w i ∉ s)).card =
      (Fintype.card A - s.card)^m := by
  have h : (Finset.univ.filter (fun w : Fin m → A => ∀ i, w i ∉ s)) =
      Fintype.piFinset (fun _ : Fin m => sᶜ) := by
    ext w
    simp
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_compl]

 theorem avoidance_probability (A : Type) [Fintype A] [Nonempty A]
    [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (s : Finset A) :
    (sampleLaw A m).real {w | ∀ i, w i ∉ s} =
      (1 - (s.card : ℝ) / Fintype.card A)^m := by
  rw [sampleLaw, uniformLaw_real_filter, avoidance_card]
  simp only [Nat.cast_pow, Fintype.card_fun, Fintype.card_fin]
  rw [← div_pow, Nat.cast_sub (Finset.card_le_univ s), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero (α := A))]

private theorem rangeFinset_map {A : Type} [Fintype A] [DecidableEq A]
    {m : ℕ} (w : Fin m → A) (e : Equiv.Perm A) :
    rangeFinset (fun i => e (w i)) = (rangeFinset w).map e.toEmbedding := by
  ext x
  simp [rangeFinset, Equiv.apply_eq_iff_eq_symm_apply]

private theorem range_fiber_card_eq (A : Type) [Fintype A] [DecidableEq A]
    (m : ℕ) (s t : Finset A) (h : s.card = t.card) :
    (Finset.univ.filter (fun w : Fin m → A => rangeFinset w = s)).card =
      (Finset.univ.filter (fun w : Fin m → A => rangeFinset w = t)).card := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t h
  refine Finset.card_equiv (Equiv.piCongrRight fun _ : Fin m => e) ?_
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change rangeFinset w = s ↔ rangeFinset (fun i => e (w i)) = t
  rw [rangeFinset_map, ← he]
  exact Finset.map_injective e.toEmbedding |>.eq_iff.symm

private theorem range_count_card (A : Type) [Fintype A] [DecidableEq A]
    (m : ℕ) (s : Finset A) :
    (Finset.univ.filter (fun w : Fin m → A => (rangeFinset w).card = s.card)).card =
      (Fintype.card A).choose s.card *
        (Finset.univ.filter (fun w : Fin m → A => rangeFinset w = s)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin m → A))
    ((Finset.univ : Finset A).powersetCard s.card) rangeFinset
  have hmem (w : Fin m → A) :
      rangeFinset w ∈ (Finset.univ : Finset A).powersetCard s.card ↔
        (rangeFinset w).card = s.card := by simp
  simp only [hmem] at h
  rw [← h]
  calc
    ∑ t ∈ (Finset.univ : Finset A).powersetCard s.card,
      (Finset.univ.filter (fun w : Fin m → A => rangeFinset w = t)).card =
        ∑ _t ∈ (Finset.univ : Finset A).powersetCard s.card,
          (Finset.univ.filter (fun w : Fin m → A => rangeFinset w = s)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      exact range_fiber_card_eq A m t s (Finset.mem_powersetCard.mp ht).2
    _ = _ := by simp

 theorem conditional_uniform (A : Type) [Fintype A] [Nonempty A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ) (s : Finset A) :
    sampleLaw A m {w | rangeFinset w = s} =
      sampleLaw A m {w | (rangeFinset w).card = s.card} /
        (Nat.choose (Fintype.card A) s.card : ℝ≥0∞) := by
  have hn : (Nat.choose (Fintype.card A) s.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Finset.card_le_univ s)).ne'
  rw [sampleLaw, uniformLaw_filter, uniformLaw_filter]
  apply (ENNReal.eq_div_iff hn (by simp)).2
  rw [range_count_card, Nat.cast_mul, mul_div_assoc]

private theorem emptyIndicator_integral (A : Type) [Fintype A] [Nonempty A]
    [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (v : A) :
    (∫ w, emptyIndicator v w ∂sampleLaw A m) =
      (1 - 1 / (Fintype.card A : ℝ))^m := by
  have heq : (emptyIndicator v : (Fin m → A) → ℝ) =
      {w : Fin m → A | ∀ i, w i ∉ ({v} : Finset A)}.indicator 1 := by
    funext w
    simp [emptyIndicator, rangeFinset, eq_comm, Set.indicator]
  rw [heq, integral_indicator_one (by measurability), avoidance_probability]
  simp

private theorem emptyIndicator_product_integral (A : Type) [Fintype A] [Nonempty A]
    [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (v u : A) (hvu : v ≠ u) :
    (∫ w : Fin m → A, emptyIndicator v w * emptyIndicator u w ∂sampleLaw A m) =
      (1 - 2 / (Fintype.card A : ℝ))^m := by
  have heq : (fun w : Fin m → A => emptyIndicator v w * emptyIndicator u w) =
      {w : Fin m → A | ∀ i, w i ∉ ({v, u} : Finset A)}.indicator 1 := by
    funext w
    by_cases hv : ∃ i, w i = v <;> by_cases hu : ∃ i, w i = u <;>
      simp_all [emptyIndicator, rangeFinset, Set.indicator, not_exists, forall_and,
        eq_comm, ← not_or, exists_or]
  rw [heq, integral_indicator_one (by measurability), avoidance_probability]
  simp [hvu]

private theorem emptyIndicator_covariance_nonpos (A : Type) [Fintype A] [Nonempty A]
    [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (m : ℕ) (v u : A) (hvu : v ≠ u) :
    covariance (emptyIndicator v : (Fin m → A) → ℝ) (emptyIndicator u)
      (sampleLaw A m) ≤ 0 := by
  rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete]
  change (∫ w : Fin m → A, emptyIndicator v w * emptyIndicator u w ∂sampleLaw A m) -
    (∫ w : Fin m → A, emptyIndicator v w ∂sampleLaw A m) *
    (∫ w : Fin m → A, emptyIndicator u w ∂sampleLaw A m) ≤ 0
  rw [emptyIndicator_product_integral A m v u hvu,
    emptyIndicator_integral, emptyIndicator_integral]
  have hN : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have htwo : (2 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 2 ≤ Fintype.card A by
      simpa [hvu] using Finset.card_le_univ ({v, u} : Finset A))
  have hq : 0 ≤ 1 - 2 / (Fintype.card A : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one hN).mpr htwo)
  have hbase : 1 - 2 / (Fintype.card A : ℝ) ≤
      (1 - 1 / (Fintype.card A : ℝ))^2 := by
    simp only [div_eq_mul_inv]
    nlinarith [sq_nonneg ((Fintype.card A : ℝ)⁻¹)]
  have hpow := pow_le_pow_left₀ hq hbase m
  rw [← pow_mul, Nat.mul_comm 2 m, pow_mul, pow_two] at hpow
  linarith

private theorem emptyIndicator_sum (A : Type) [Fintype A] [DecidableEq A]
    (m : ℕ) (w : Fin m → A) :
    ∑ v, emptyIndicator v w = (Fintype.card A : ℝ) - (rangeFinset w).card := by
  calc
    ∑ v, emptyIndicator v w =
        ∑ v ∈ (rangeFinset w)ᶜ, (1 : ℝ) := by
      have hc : (rangeFinset w)ᶜ = Finset.univ.filter (fun v => v ∉ rangeFinset w) := by
        ext; simp
      rw [hc, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      simp [emptyIndicator]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_compl]
      exact Nat.cast_sub (Finset.card_le_univ _)

 theorem occupancy_moments (A : Type) [Fintype A] [Nonempty A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ) :
    (∫ w, ((rangeFinset w).card : ℝ) ∂sampleLaw A m) =
      Fintype.card A * (1 - (1 - 1 / (Fintype.card A : ℝ))^m) ∧
    variance (fun w : Fin m → A => ((rangeFinset w).card : ℝ)) (sampleLaw A m) ≤
      (Fintype.card A : ℝ) / 4 := by
  have heq : (fun w : Fin m → A => ((rangeFinset w).card : ℝ)) =
      fun w => (Fintype.card A : ℝ) - ∑ v, emptyIndicator v w := by
    funext w
    rw [emptyIndicator_sum]
    ring
  constructor
  · rw [heq, integral_sub (integrable_const _) (Integrable.of_finite),
      integral_const, probReal_univ, one_smul, integral_finsetSum]
    · simp_rw [emptyIndicator_integral]
      simp
      ring
    · intro v _
      exact Integrable.of_finite
  · rw [heq, variance_const_sub (.of_discrete), variance_fun_sum (fun _ => MemLp.of_discrete)]
    calc
      ∑ v : A, ∑ u : A, covariance (emptyIndicator v : (Fin m → A) → ℝ)
          (emptyIndicator u) (sampleLaw A m) ≤
          ∑ v : A, ∑ u : A, if v = u then (1 / 4 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro u _
        by_cases h : v = u
        · subst u
          simp only [ite_true]
          rw [covariance_self (.of_discrete)]
          have hb := variance_le_sq_of_bounded
            (μ := sampleLaw A m) (X := emptyIndicator v)
            (a := 0) (b := 1) (Filter.Eventually.of_forall (fun w => by
              unfold emptyIndicator
              split_ifs <;> norm_num)) (.of_discrete)
          norm_num at hb ⊢
          exact hb
        · simp only [h, ite_false]
          exact emptyIndicator_covariance_nonpos A m v u h
      _ = _ := by simp [div_eq_mul_inv]

private theorem board_card (n : ℕ) : Fintype.card (Board n) = (n + 1)^2 := by
  simp [Board, pow_two]

private theorem board_size_pos (n : ℕ) : (0 : ℝ) < (n + 1 : ℝ)^2 := by positivity

private theorem board_size_tendsto :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^2) atTop atTop := by
  refine tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ)]

 theorem vacancy_limit (m : ℕ → ℕ) (c : ℝ)
    (hm : Tendsto (fun n => (m n : ℝ) / (n + 1 : ℝ)^2) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ)^2)^(m n)) atTop
      (𝓝 (Real.exp (-c))) := by
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℝ)^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp board_size_tendsto
  have hne : Tendsto (fun n : ℕ => -((n + 1 : ℝ)^2)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hinv.neg
    · exact Filter.Eventually.of_forall (fun n => by simp [ne_of_gt (board_size_pos n)])
  have hs := (Real.hasDerivAt_log (x := (1 : ℝ)) (by norm_num)).tendsto_slope_zero.comp hne
  have hlog : Tendsto (fun n : ℕ => -(n + 1 : ℝ)^2 *
      Real.log (1 - 1 / (n + 1 : ℝ)^2)) atTop (𝓝 (1 : ℝ)) := by
    simpa [Function.comp_def, smul_eq_mul, one_div, sub_eq_add_neg] using hs
  have hexponent : Tendsto (fun n : ℕ => (m n : ℝ) *
      Real.log (1 - 1 / (n + 1 : ℝ)^2)) atTop (𝓝 (-c)) := by
    convert (hm.mul hlog).neg using 1
    · funext n
      have hN := ne_of_gt (board_size_pos n)
      field_simp
    · ring
  have he := Real.continuous_exp.continuousAt.tendsto.comp hexponent
  apply he.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  change Real.exp ((m n : ℝ) * Real.log (1 - 1 / (n + 1 : ℝ)^2)) = _
  rw [Real.exp_nat_mul, Real.exp_log]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (1 : ℝ) < (n + 1 : ℝ)^2 := by nlinarith
  exact sub_pos.mpr ((div_lt_one (board_size_pos n)).mpr hN)

private theorem occupancy_density_mean (n m : ℕ) :
    (∫ w, occupancyDensityM n m w ∂roadLawM n m) =
      1 - (1 - 1 / (n + 1 : ℝ)^2)^m := by
  have h := (occupancy_moments (Board n) m).1
  have hN := ne_of_gt (board_size_pos n)
  change (∫ w : DrawsM n m, ((rangeFinset w).card : ℝ) / (n + 1 : ℝ)^2
    ∂sampleLaw (Board n) m) = _
  rw [integral_div, h, board_card]
  push_cast
  exact mul_div_cancel_left₀ _ hN

private theorem occupancy_density_variance (n m : ℕ) :
    variance (occupancyDensityM n m) (roadLawM n m) ≤ 1 / (4 * (n + 1 : ℝ)^2) := by
  have h := (occupancy_moments (Board n) m).2
  have hN := ne_of_gt (board_size_pos n)
  change variance (fun w : DrawsM n m => ((rangeFinset w).card : ℝ) / (n + 1 : ℝ)^2)
    (sampleLaw (Board n) m) ≤ _
  simp only [div_eq_mul_inv, variance_mul_const]
  have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (((n + 1 : ℝ)^2)⁻¹))
  simp only [board_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h'
  convert h' using 1 <;> field_simp <;> ring

private theorem occupancy_concentration (n m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    roadLawM n m {w | ε ≤ |occupancyDensityM n m w -
      (1 - (1 - 1 / (n + 1 : ℝ)^2)^m)|} ≤
      ENNReal.ofReal (1 / (4 * ε^2 * (n + 1 : ℝ)^2)) := by
  letI : IsProbabilityMeasure (roadLawM n m) := sampleLaw_probability (Board n) m
  have h := meas_ge_le_variance_div_sq
    (μ := roadLawM n m) (X := occupancyDensityM n m) MemLp.of_discrete hε
  rw [occupancy_density_mean] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hv := div_le_div_of_nonneg_right (occupancy_density_variance n m) (sq_nonneg ε)
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hv

private theorem average_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    average (fun _ : A => c) = c := by
  simp [average, Fintype.card_ne_zero]

private theorem average_mono {A : Type} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

private theorem average_equiv {A : Type} [Fintype A] (e : Equiv.Perm A) (f : A → ℝ) :
    average (fun a => f (e a)) = average f := by
  unfold average
  exact congrArg (fun r : ℝ => r / (Fintype.card A : ℝ)) (Equiv.sum_comp e f)

private theorem relabel_comp {A : Type} (e f : Equiv.Perm A) (ω : Configuration A) :
    relabel e (relabel f ω) = relabel (e * f) ω := by
  rfl

private theorem mem_openFinset {A : Type} [Fintype A]
    (ω : Configuration A) (v : A) : v ∈ openFinset ω ↔ ω v = true := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ v))

private theorem openFinset_relabel {A : Type} [Fintype A] [DecidableEq A]
    (e : Equiv.Perm A) (ω : Configuration A) :
    openFinset (relabel e ω) = (openFinset ω).map e.toEmbedding := by
  ext v
  constructor
  · intro hv
    have hv' := (mem_openFinset _ _).mp hv
    apply Finset.mem_map.mpr
    exact ⟨e.symm v, (mem_openFinset ω _).mpr hv', by simp⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    apply (mem_openFinset _ _).mpr
    change ω (e.symm (e u)) = true
    rw [e.symm_apply_apply]
    exact (mem_openFinset _ _).mp hu

private theorem symmetrize_relabel {A : Type} [Fintype A]
    (f : Configuration A → ℝ) (e : Equiv.Perm A) (ω : Configuration A) :
    symmetrize f (relabel e ω) = symmetrize f ω := by
  unfold symmetrize
  simp_rw [relabel_comp]
  exact average_equiv (Equiv.mulRight e) (fun σ => f (relabel σ ω))

private theorem symmetrize_mono {A : Type} [Fintype A]
    (f : Configuration A → ℝ)
    (hf : ∀ ω η, configurationLE ω η → f ω ≤ f η)
    (ω η : Configuration A) (h : configurationLE ω η) :
    symmetrize f ω ≤ symmetrize f η := by
  apply average_mono
  intro e
  apply hf
  intro v hv
  exact h (e.symm v) hv

private theorem symmetrize_card_mono {A : Type} [Fintype A] [DecidableEq A]
    (f : Configuration A → ℝ)
    (hf : ∀ ω η, configurationLE ω η → f ω ≤ f η)
    (ω η : Configuration A) (hcard : (openFinset ω).card ≤ (openFinset η).card) :
    symmetrize f ω ≤ symmetrize f η := by
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq (openFinset ω) s hscard.symm
  have hle : configurationLE (relabel e ω) η := by
    intro v hv
    have hmem : v ∈ openFinset (relabel e ω) := by simp [openFinset, hv]
    rw [openFinset_relabel, he] at hmem
    simpa [openFinset] using hs hmem
  rw [← symmetrize_relabel f e ω]
  exact symmetrize_mono f hf _ _ hle

private theorem symmetrize_bounds {A : Type} [Fintype A]
    (f : Configuration A → ℝ) (hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1)
    (ω : Configuration A) : 0 ≤ symmetrize f ω ∧ symmetrize f ω ≤ 1 := by
  constructor
  · rw [← average_const (A := Equiv.Perm A) (0 : ℝ)]
    exact average_mono (fun e => (hf _).1)
  · rw [← average_const (A := Equiv.Perm A) (1 : ℝ)]
    exact average_mono (fun e => (hf _).2)

private theorem symmetrize_integral {A : Type} [Fintype A]
    (μ : Measure (Configuration A)) [IsProbabilityMeasure μ]
    (hμ : ∀ e : Equiv.Perm A, μ.map (relabel e) = μ)
    (f : Configuration A → ℝ) :
    (∫ ω, symmetrize f ω ∂μ) = ∫ ω, f ω ∂μ := by
  have hi (e : Equiv.Perm A) : (∫ ω, f (relabel e ω) ∂μ) = ∫ ω, f ω ∂μ := by
    rw [← integral_map (.of_discrete) (.of_discrete), hμ e]
  change (∫ ω, (∑ e : Equiv.Perm A, f (relabel e ω)) /
    Fintype.card (Equiv.Perm A) ∂μ) = _
  rw [integral_div, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [hi]
  simp [Fintype.card_ne_zero]

private theorem integral_boole {X : Type} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) (P : X → Prop) :
    (∫ x, (if P x then (1 : ℝ) else 0) ∂μ) = μ.real {x | P x} := by
  exact integral_indicator_one (by measurability)

 theorem exchangeable_comparison (A : Type) [Fintype A] [DecidableEq A]
    (μ ν : Measure (Configuration A)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ e : Equiv.Perm A, μ.map (relabel e) = μ)
    (hν : ∀ e : Equiv.Perm A, ν.map (relabel e) = ν)
    (t : ℝ) (U : Set (Configuration A)) (hU : increasingEvent U) :
    μ U ≤ ν U + μ {ω | t < ((openFinset ω).card : ℝ)} +
      ν {ω | ((openFinset ω).card : ℝ) < t} := by
  let f : Configuration A → ℝ := U.indicator 1
  have hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1 := by
    intro ω
    simp only [f, Set.indicator]
    split_ifs <;> norm_num
  have hfmono : ∀ ω η, configurationLE ω η → f ω ≤ f η := by
    intro ω η h
    by_cases hω : ω ∈ U
    · simp [f, hω, hU ω η h hω]
    · simp [f, hω, (hf η).1]
  have hpoint (ω η : Configuration A) :
      symmetrize f ω ≤ symmetrize f η +
        (if t < ((openFinset ω).card : ℝ) then (1 : ℝ) else 0) +
        (if ((openFinset η).card : ℝ) < t then (1 : ℝ) else 0) := by
    have hbω := symmetrize_bounds f hf ω
    have hbη := symmetrize_bounds f hf η
    by_cases hω : t < ((openFinset ω).card : ℝ)
    · simp only [hω, ite_true]
      split_ifs <;> linarith
    by_cases hη : ((openFinset η).card : ℝ) < t
    · simp only [hω, hη, ite_false, ite_true]
      linarith
    · simp only [hω, hη, ite_false, add_zero]
      apply symmetrize_card_mono f hfmono
      exact_mod_cast (le_trans (le_of_not_gt hω) (le_of_not_gt hη))
  have hfirst (ω : Configuration A) :
      symmetrize f ω ≤ (∫ η, symmetrize f η ∂ν) +
        (if t < ((openFinset ω).card : ℝ) then (1 : ℝ) else 0) +
        ν.real {η | ((openFinset η).card : ℝ) < t} := by
    have h := integral_mono (μ := ν) Integrable.of_finite Integrable.of_finite (hpoint ω)
    simpa only [integral_add Integrable.of_finite Integrable.of_finite,
      integral_const, probReal_univ, one_smul, integral_boole] using h
  have hr := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hfirst
  simp only [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const, probReal_univ, one_smul, integral_boole,
    symmetrize_integral μ hμ f, symmetrize_integral ν hν f,
    f] at hr
  rw [integral_indicator_one U.toFinite.measurableSet,
    integral_indicator_one U.toFinite.measurableSet] at hr
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa [measureReal_def, ENNReal.toReal_add] using hr

private theorem uniformLaw_map_equiv (X : Type) [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (e : Equiv.Perm X) :
    (uniformLaw X).map e = uniformLaw X := by
  ext s hs
  rw [Measure.map_apply (.of_discrete) hs, uniformLaw_apply, uniformLaw_apply]
  have hc : (e ⁻¹' s).toFinite.toFinset.card = s.toFinite.toFinset.card := by
    apply Finset.card_equiv e
    intro x
    simp
  rw [hc]

 theorem completed_law_exchangeable (n m : ℕ) (e : Equiv.Perm (Board n)) :
    ((roadLawM n m).map (completedM n m)).map (relabel e) =
      (roadLawM n m).map (completedM n m) := by
  let ew : Equiv.Perm (DrawsM n m) := Equiv.piCongrRight (fun _ : Fin m => e)
  have heq : (relabel e) ∘ (completedM n m) = (completedM n m) ∘ ew := by
    funext w v
    simp [completedM, relabel, ew, Equiv.apply_eq_iff_eq_symm_apply]
  rw [Measure.map_map (.of_discrete) (.of_discrete), heq,
    ← Measure.map_map (.of_discrete) (.of_discrete)]
  change (uniformLaw (DrawsM n m) |>.map ew).map (completedM n m) = _
  rw [uniformLaw_map_equiv]
  rfl

 theorem site_law_exchangeable (A : Type) (p : Parameter) (e : Equiv.Perm A) :
    (siteMeasure (A := A) p).map (relabel e) = siteMeasure p := by
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : A => Bool) e)) = relabel e := by
    funext ω v
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, relabel]
  simpa only [he, siteMeasure] using
    Measure.infinitePi_map_piCongrLeft (fun _ : A => bernoulliMeasure true false p) e

private theorem openFinset_card_sum {A : Type} [Fintype A] (ω : Configuration A) :
    ((openFinset ω).card : ℝ) = ∑ v, if ω v = true then (1 : ℝ) else 0 := by
  simp only [openFinset, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem iid_occupancy_moments (A : Type) [Fintype A] (p : Parameter) :
    (∫ ω : Configuration A, ((openFinset ω).card : ℝ) ∂siteMeasure p) =
      Fintype.card A * p.val ∧
    variance (fun ω : Configuration A => ((openFinset ω).card : ℝ)) (siteMeasure p) ≤
      (Fintype.card A : ℝ) / 4 := by
  let b : Bool → ℝ := fun x => if x = true then 1 else 0
  have heq : (fun ω : Configuration A => ((openFinset ω).card : ℝ)) =
      fun ω => ∑ v : A, b (ω v) := by
    funext ω
    exact openFinset_card_sum ω
  have hi (v : A) : (∫ ω : Configuration A, b (ω v) ∂siteMeasure p) = p.val := by
    change (∫ ω : Configuration A, b (ω v)
      ∂Measure.infinitePi (fun _ : A => bernoulliMeasure true false p)) = _
    rw [← integral_map (measurable_pi_apply v).aemeasurable (.of_discrete),
      Measure.infinitePi_map_eval]
    simp [integral_bernoulliMeasure, b]
  constructor
  · rw [heq, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp_rw [hi]
    simp
  · have heq' : (fun ω : Configuration A => ∑ v : A, b (ω v)) =
        ∑ v : A, fun ω : Configuration A => b (ω v) := by
      ext ω
      simp
    rw [heq, heq', siteMeasure, Measure.infinitePi_eq_pi,
      variance_sum_pi (fun _ => MemLp.of_discrete)]
    have hb : variance b (bernoulliMeasure true false p) ≤ (1 / 4 : ℝ) := by
      have h := variance_le_sq_of_bounded
        (μ := bernoulliMeasure true false p) (X := b)
        (a := 0) (b := 1) (Filter.Eventually.of_forall (fun x => by
          unfold b
          split_ifs <;> norm_num)) (.of_discrete)
      norm_num at h ⊢
      exact h
    calc
      ∑ _v : A, variance b (bernoulliMeasure true false p) ≤ ∑ _v : A, (1 / 4 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => hb)
      _ = _ := by simp [div_eq_mul_inv]

private theorem iid_occupancy_concentration (n : ℕ) (p : Parameter) (ε : ℝ) (hε : 0 < ε) :
    siteMeasure p {ω : Configuration (Board n) |
      ε ≤ |((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2 - p.val|} ≤
      ENNReal.ofReal (1 / (4 * ε^2 * (n + 1 : ℝ)^2)) := by
  let X : Configuration (Board n) → ℝ := fun ω => ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2
  have hmean : (∫ ω, X ω ∂siteMeasure p) = p.val := by
    rw [show X = (fun ω => ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2) from rfl,
      integral_div, (iid_occupancy_moments (Board n) p).1, board_card]
    push_cast
    exact mul_div_cancel_left₀ _ (ne_of_gt (board_size_pos n))
  have hvar : variance X (siteMeasure p) ≤ 1 / (4 * (n + 1 : ℝ)^2) := by
    change variance (fun ω : Configuration (Board n) =>
      ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2) (siteMeasure p) ≤ _
    simp only [div_eq_mul_inv, variance_mul_const]
    have h := mul_le_mul_of_nonneg_right (iid_occupancy_moments (Board n) p).2
      (sq_nonneg (((n + 1 : ℝ)^2)⁻¹))
    simp only [board_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h
    convert h using 1 <;> field_simp <;> ring
  have h := meas_ge_le_variance_div_sq (μ := siteMeasure p) (X := X) MemLp.of_discrete hε
  rw [hmean] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hv := div_le_div_of_nonneg_right hvar (sq_nonneg ε)
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hv

 theorem iid_occupancy_lln (p : Parameter) :
    ConvergesInProbability (fun n => siteMeasure (A := Board n) p)
      (fun n ω => ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2) p.val := by
  intro ε hε
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℝ)^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp board_size_tendsto
  have hr : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (1 / (4 * ε^2 * (n + 1 : ℝ)^2))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (hinv.const_mul ((4 * ε^2)⁻¹))
    simpa [div_eq_mul_inv, mul_comm] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Filter.Eventually.of_forall (fun _ => bot_le))
  apply Filter.Eventually.of_forall
  intro n
  refine (measure_mono ?_).trans (iid_occupancy_concentration n p ε hε)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  exact le_of_lt hω

private theorem cip_upper_tail {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) (Y : ∀ n, X n → ℝ) (a t : ℝ)
    (h : ConvergesInProbability μ Y a) (ht : a < t) :
    Tendsto (fun n => μ n {x | t < Y n x}) atTop (𝓝 0) := by
  have h0 := h (t - a) (sub_pos.mpr ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Filter.Eventually.of_forall (fun _ => bot_le))
  apply Filter.Eventually.of_forall
  intro n
  apply measure_mono
  intro x hx
  change t < Y n x at hx
  change t - a < |Y n x - a|
  exact lt_of_lt_of_le (sub_lt_sub_right hx a) (le_abs_self _)

private theorem cip_lower_tail {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) (Y : ∀ n, X n → ℝ) (a t : ℝ)
    (h : ConvergesInProbability μ Y a) (ht : t < a) :
    Tendsto (fun n => μ n {x | Y n x < t}) atTop (𝓝 0) := by
  have h0 := h (a - t) (sub_pos.mpr ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Filter.Eventually.of_forall (fun _ => bot_le))
  apply Filter.Eventually.of_forall
  intro n
  apply measure_mono
  intro x hx
  change Y n x < t at hx
  change a - t < |Y n x - a|
  have hle := neg_le_abs (Y n x - a)
  linarith

private theorem openFinset_completedM (n m : ℕ) (w : DrawsM n m) :
    openFinset (completedM n m w) = occupiedM n m w := by
  ext v
  rw [mem_openFinset]
  simp [completedM, occupiedM]

private theorem exchangeable_density_comparison (n : ℕ)
    (μ ν : Measure (Configuration (Board n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ e : Equiv.Perm (Board n), μ.map (relabel e) = μ)
    (hν : ∀ e : Equiv.Perm (Board n), ν.map (relabel e) = ν)
    (t : ℝ) (U : Set (Configuration (Board n))) (hU : increasingEvent U) :
    μ U ≤ ν U + μ {ω | t < ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2} +
      ν {ω | ((openFinset ω).card : ℝ) / (n + 1 : ℝ)^2 < t} := by
  have h := exchangeable_comparison (Board n) μ ν hμ hν (t * (n + 1 : ℝ)^2) U hU
  simpa only [← lt_div_iff₀ (board_size_pos n),
    ← div_lt_iff₀ (board_size_pos n)] using h

end Occupancy

instance roadLawM_probability (n m : ℕ) : IsProbabilityMeasure (roadLawM n m) :=
  Occupancy.uniformLaw_probability (DrawsM n m)

theorem road_event_measurable (n m : ℕ) (s : Set (DrawsM n m)) : MeasurableSet s :=
  s.toFinite.measurableSet

theorem board_event_measurable (n : ℕ) (s : Set (Configuration (Board n))) :
    MeasurableSet s := s.toFinite.measurableSet

theorem occupancy_lln (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / (n + 1 : ℝ)^2) atTop (𝓝 c)) :
    ConvergesInProbability (fun n => roadLawM n (m n))
      (fun n => occupancyDensityM n (m n)) (1 - Real.exp (-c)) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hcenter : Tendsto (fun n : ℕ => 1 - (1 - 1 / (n + 1 : ℝ)^2)^(m n))
      atTop (𝓝 (1 - Real.exp (-c))) :=
    tendsto_const_nhds.sub (Occupancy.vacancy_limit m c hm)
  have hclose : ∀ᶠ n : ℕ in atTop,
      |(1 - (1 - 1 / (n + 1 : ℝ)^2)^(m n)) - (1 - Real.exp (-c))| < ε / 2 := by
    have ht := (hcenter.sub_const (1 - Real.exp (-c))).abs
    have hz : (1 - Real.exp (-c)) - (1 - Real.exp (-c)) = (0 : ℝ) := sub_self _
    rw [hz, abs_zero] at ht
    exact (tendsto_order.mp ht).2 _ hε2
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℝ)^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Occupancy.board_size_tendsto
  have hr : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (1 / (4 * (ε / 2)^2 * (n + 1 : ℝ)^2))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (hinv.const_mul ((4 * (ε / 2)^2)⁻¹))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [hclose] with n hn
  apply (measure_mono (show
    {w | ε < |occupancyDensityM n (m n) w - (1 - Real.exp (-c))|} ⊆
    {w | ε / 2 ≤ |occupancyDensityM n (m n) w -
      (1 - (1 - 1 / (n + 1 : ℝ)^2)^(m n))|} from ?_)).trans
      (Occupancy.occupancy_concentration n (m n) (ε / 2) hε2)
  intro w hw
  have ht := abs_sub_le (occupancyDensityM n (m n) w)
    (1 - (1 - 1 / (n + 1 : ℝ)^2)^(m n)) (1 - Real.exp (-c))
  change ε < |occupancyDensityM n (m n) w - (1 - Real.exp (-c))| at hw
  change ε / 2 ≤ _
  linarith

theorem occupancy_sandwich (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / (n + 1 : ℝ)^2) atTop (𝓝 c))
    (pMinus pPlus : Parameter)
    (hMinus : pMinus.val < 1 - Real.exp (-c))
    (hPlus : 1 - Real.exp (-c) < pPlus.val) :
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n (U : Set (Configuration (Board n))), increasingEvent U →
        siteMeasure pMinus U ≤
          roadLawM n (m n) {w | completedM n (m n) w ∈ U} + err n ∧
        roadLawM n (m n) {w | completedM n (m n) w ∈ U} ≤
          siteMeasure pPlus U + err n := by
  let r : ℝ := 1 - Real.exp (-c)
  let tMinus : ℝ := (pMinus.val + r) / 2
  let tPlus : ℝ := (r + pPlus.val) / 2
  have htM : pMinus.val < tMinus ∧ tMinus < r := by dsimp [tMinus, r]; constructor <;> linarith
  have htP : r < tPlus ∧ tPlus < pPlus.val := by dsimp [tPlus, r]; constructor <;> linarith
  let bMinus (n : ℕ) := siteMeasure pMinus {ω : Configuration (Board n) |
    tMinus < ((Occupancy.openFinset ω).card : ℝ) / (n + 1 : ℝ)^2}
  let aMinus (n : ℕ) := roadLawM n (m n) {w | occupancyDensityM n (m n) w < tMinus}
  let aPlus (n : ℕ) := roadLawM n (m n) {w | tPlus < occupancyDensityM n (m n) w}
  let bPlus (n : ℕ) := siteMeasure pPlus {ω : Configuration (Board n) |
    ((Occupancy.openFinset ω).card : ℝ) / (n + 1 : ℝ)^2 < tPlus}
  let err (n : ℕ) := bMinus n + aMinus n + aPlus n + bPlus n
  have hbM : Tendsto bMinus atTop (𝓝 0) :=
    Occupancy.cip_upper_tail _ _ _ _ (Occupancy.iid_occupancy_lln pMinus) htM.1
  have haM : Tendsto aMinus atTop (𝓝 0) :=
    Occupancy.cip_lower_tail _ _ _ _ (occupancy_lln m c hc hm) htM.2
  have haP : Tendsto aPlus atTop (𝓝 0) :=
    Occupancy.cip_upper_tail _ _ _ _ (occupancy_lln m c hc hm) htP.1
  have hbP : Tendsto bPlus atTop (𝓝 0) :=
    Occupancy.cip_lower_tail _ _ _ _ (Occupancy.iid_occupancy_lln pPlus) htP.2
  refine ⟨err, by simpa using ((hbM.add haM).add haP).add hbP, ?_⟩
  intro n U hU
  let μ : Measure (Configuration (Board n)) := (roadLawM n (m n)).map (completedM n (m n))
  have hμ : ∀ e : Equiv.Perm (Board n), μ.map (Occupancy.relabel e) = μ :=
    Occupancy.completed_law_exchangeable n (m n)
  have hμU : μ U = roadLawM n (m n) {w | completedM n (m n) w ∈ U} := by
    exact Measure.map_apply (.of_discrete) U.toFinite.measurableSet
  have hμM : μ {ω | ((Occupancy.openFinset ω).card : ℝ) / (n + 1 : ℝ)^2 < tMinus} =
      aMinus n := by
    rw [Measure.map_apply (.of_discrete) (.of_discrete)]
    congr 1
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Occupancy.openFinset_completedM,
      occupancyDensityM]
  have hμP : μ {ω | tPlus < ((Occupancy.openFinset ω).card : ℝ) / (n + 1 : ℝ)^2} =
      aPlus n := by
    rw [Measure.map_apply (.of_discrete) (.of_discrete)]
    congr 1
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Occupancy.openFinset_completedM,
      occupancyDensityM]
  constructor
  · have h := Occupancy.exchangeable_density_comparison n (siteMeasure pMinus) μ
      (Occupancy.site_law_exchangeable (Board n) pMinus) hμ tMinus U hU
    rw [hμU, hμM] at h
    change siteMeasure pMinus U ≤ _ + bMinus n + aMinus n at h
    calc
      siteMeasure pMinus U ≤ _ := h
      _ ≤ roadLawM n (m n) {w | completedM n (m n) w ∈ U} + err n := by
        dsimp [err]
        simp only [add_assoc]
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · have h := Occupancy.exchangeable_density_comparison n μ (siteMeasure pPlus)
      hμ (Occupancy.site_law_exchangeable (Board n) pPlus) tPlus U hU
    rw [hμU, hμP] at h
    change roadLawM n (m n) {w | completedM n (m n) w ∈ U} ≤ _ + aPlus n + bPlus n at h
    calc
      roadLawM n (m n) {w | completedM n (m n) w ∈ U} ≤ _ := h
      _ ≤ siteMeasure pPlus U + err n := by
        have herr : aPlus n + bPlus n ≤ err n := by
          dsimp [err]
          calc
            aPlus n + bPlus n ≤ (bMinus n + aMinus n) + (aPlus n + bPlus n) :=
              le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ bMinus n + aMinus n from bot_le)
            _ = _ := by ac_rfl
        simpa only [add_assoc, add_comm, add_left_comm] using
          add_le_add_left herr (siteMeasure pPlus U)

private theorem occupancy_c_one_ratio :
    Tendsto (fun n : ℕ => (((n + 1)^2 : ℕ) : ℝ) / (n + 1 : ℝ)^2) atTop (𝓝 1) := by
  have heq : (fun n : ℕ => (((n + 1)^2 : ℕ) : ℝ) / (n + 1 : ℝ)^2) =
      fun _ : ℕ => (1 : ℝ) := by
    funext n
    push_cast
    exact div_self (ne_of_gt (Occupancy.board_size_pos n))
  rw [heq]
  exact tendsto_const_nhds

theorem occupancy_lln_c_one :
    ConvergesInProbability roadLaw
      (fun n draw => occupancyDensityM n ((n+1)^2) draw) roadParameter.val := by
  change ConvergesInProbability (fun n => roadLawM n ((n + 1)^2))
    (fun n draw => occupancyDensityM n ((n + 1)^2) draw) (1 - Real.exp (-1))
  exact occupancy_lln (fun n => (n + 1)^2) 1 (by norm_num) occupancy_c_one_ratio

theorem occupancy_sandwich_c_one (pMinus pPlus : Parameter)
    (hMinus : pMinus.val < roadParameter.val)
    (hPlus : roadParameter.val < pPlus.val) :
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n (U : Set (Configuration (Board n))), increasingEvent U →
        siteMeasure pMinus U ≤ roadLaw n {w | completed n w ∈ U} + err n ∧
        roadLaw n {w | completed n w ∈ U} ≤ siteMeasure pPlus U + err n := by
  have hlaw (n : ℕ) : roadLawM n ((n + 1)^2) = roadLaw n := rfl
  have hconfig (n : ℕ) : completedM n ((n + 1)^2) = completed n := rfl
  simpa only [hlaw, hconfig] using
    occupancy_sandwich (fun n => (n + 1)^2) 1 (by norm_num) occupancy_c_one_ratio
      pMinus pPlus hMinus hPlus

#print axioms Occupancy.uniformLaw_apply
#print axioms Occupancy.avoidance_probability
#print axioms Occupancy.conditional_uniform
#print axioms Occupancy.occupancy_moments
#print axioms Occupancy.vacancy_limit
#print axioms Occupancy.exchangeable_comparison
#print axioms Occupancy.completed_law_exchangeable
#print axioms Occupancy.site_law_exchangeable
#print axioms Occupancy.iid_occupancy_lln
#print axioms occupancy_lln
#print axioms occupancy_sandwich
#print axioms occupancy_lln_c_one
#print axioms occupancy_sandwich_c_one

end SitePerc
