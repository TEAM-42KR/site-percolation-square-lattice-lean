import SitePerc.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Exact finite Bernoulli laws

This module connects a finite configuration enumeration to the actual site
measure.  The extraction function is arbitrary; its graph-specific meaning
and the implementation of an enumerator belong to its caller.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SitePerc

/-- Number of open coordinates in a finite complete configuration. -/
def openCount {A : Type} [Fintype A] (ω : Configuration A) : ℕ :=
  (Finset.univ.filter (fun a => ω a = true)).card

/-- Number of closed coordinates in a finite complete configuration. -/
def closedCount {A : Type} [Fintype A] (ω : Configuration A) : ℕ :=
  (Finset.univ.filter (fun a => ω a = false)).card

/-- The exact Bernoulli weight of a complete finite configuration. -/
noncomputable def configWeight {A : Type} [Fintype A]
    (p : Parameter) (ω : Configuration A) : ℝ :=
  p.val ^ openCount ω * (1 - p.val) ^ closedCount ω

namespace FiniteLaw

/-- A finite PMF, recorded by the real values of its point masses. -/
noncomputable def ofPMF {S : Type} [Fintype S] (μ : PMF S) : FiniteLaw S where
  mass s := (μ s).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  total := by
    rw [← ENNReal.toReal_sum (fun s _ => μ.apply_ne_top s)]
    have h : ∑ s, μ s = 1 := by simpa using μ.tsum_coe
    rw [h, ENNReal.toReal_one]

/-- A genuine finite probability measure, recorded by its real singleton masses. -/
noncomputable def ofMeasure {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ] :
    FiniteLaw S where
  mass s := (μ {s}).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  total := by
    simpa [measureReal_def] using
      (sum_measureReal_singleton (μ := μ) (Finset.univ : Finset S))

/-- Recover a probability mass function from a normalized finite real law. -/
noncomputable def toPMF {S : Type} [Fintype S] (ν : FiniteLaw S) : PMF S :=
  PMF.ofFintype (fun s => ENNReal.ofReal (ν.mass s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => ν.nonnegative s),
      ν.total, ENNReal.ofReal_one])

end FiniteLaw

/-- The actual finite law of an arbitrary state extraction.  No measurable
structure on the state type is needed: every fiber in the finite configuration
space is measurable.  In particular the law is not an unverified input table. -/
noncomputable def finiteStateLaw {A S : Type} [Fintype A] [Fintype S]
    (p : Parameter) (X : Configuration A → S) : FiniteLaw S where
  mass s := (siteMeasure p (X ⁻¹' {s})).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  total := by
    classical
    simpa [measureReal_def] using
      (sum_measureReal_preimage_singleton (μ := siteMeasure p) (f := X)
        (Finset.univ : Finset S) (fun s _ => (Set.toFinite (X ⁻¹' {s})).measurableSet))

/-- The actual real singleton mass is its exact Bernoulli weight, including
both endpoint parameters. -/
theorem siteMeasure_singleton_toReal {A : Type} [Fintype A]
    (p : Parameter) (ω : Configuration A) :
    (siteMeasure p {ω}).toReal = configWeight p ω := by
  classical
  have hsingle (a : A) :
      (bernoulliMeasure true false p {ω a}).toReal =
        if ω a = true then p.val else 1 - p.val := by
    cases hw : ω a <;> simp [hw, measureReal_def]
  rw [siteMeasure, Measure.infinitePi_singleton_of_fintype, ENNReal.toReal_prod]
  simp_rw [hsingle]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Bool.not_eq_true]
  rfl

/-- The ENNReal singleton formula for the actual site measure. -/
theorem siteMeasure_singleton {A : Type} [Fintype A]
    (p : Parameter) (ω : Configuration A) :
    siteMeasure p {ω} = ENNReal.ofReal (configWeight p ω) := by
  rw [← siteMeasure_singleton_toReal p ω]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- The actual state law is the full configuration sum, state by state. -/
theorem finiteStateLaw_mass {A S : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] (p : Parameter) (X : Configuration A → S) (s : S) :
    (finiteStateLaw p X).mass s =
      ∑ ω : Configuration A, if X ω = s then configWeight p ω else 0 := by
  classical
  let F := Finset.univ.filter (fun ω : Configuration A => X ω = s)
  have hset : (F : Set (Configuration A)) = X ⁻¹' {s} := by
    ext ω
    simp [F]
  have hsum : (∑ ω ∈ F, (siteMeasure p {ω}).toReal) =
      (siteMeasure p (X ⁻¹' {s})).toReal := by
    simpa only [measureReal_def, hset] using
      (sum_measureReal_singleton (μ := siteMeasure p) F)
  change (siteMeasure p (X ⁻¹' {s})).toReal = _
  rw [← hsum]
  simp_rw [siteMeasure_singleton_toReal]
  exact Finset.sum_filter _ _

/-- Each singleton of the actual pushforward is the full exact configuration
sum.  Finite state extraction functions are automatically measurable. -/
theorem siteMeasure_map_singleton {A S : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : Parameter) (X : Configuration A → S) (s : S) :
    (siteMeasure p).map X {s} = ENNReal.ofReal
      (∑ ω : Configuration A, if X ω = s then configWeight p ω else 0) := by
  rw [Measure.map_apply (measurable_of_finite X) (measurableSet_singleton s)]
  rw [← finiteStateLaw_mass p X s]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

namespace FiniteLaw

/-- Real finite-law conversion loses no information from a finite PMF. -/
theorem ofPMF_toPMF {S : Type} [Fintype S] (μ : PMF S) :
    (ofPMF μ).toPMF = μ := by
  apply PMF.ext
  intro s
  change ENNReal.ofReal (μ s).toReal = μ s
  exact ENNReal.ofReal_toReal (μ.apply_ne_top s)

/-- Exact finite-set sums for the PMF-to-real-law interface. -/
theorem ofPMF_sum {S : Type} [Fintype S] (μ : PMF S) (U : Finset S) :
    (∑ s ∈ U, (ofPMF μ).mass s) = (∑ s ∈ U, μ s).toReal := by
  change (∑ s ∈ U, (μ s).toReal) = _
  exact (ENNReal.toReal_sum (fun s _ => μ.apply_ne_top s)).symm

/-- Recover the original measure, not just a real singleton table. -/
theorem ofMeasure_toPMF_toMeasure {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ] :
    (ofMeasure μ).toPMF.toMeasure = μ := by
  apply Measure.ext_of_singleton
  intro s
  rw [PMF.toMeasure_apply_singleton _ s (measurableSet_singleton s)]
  change ENNReal.ofReal (μ {s}).toReal = μ {s}
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end FiniteLaw

/-- The recovered state PMF has exactly the actual pushforward measure. -/
theorem finiteStateLaw_toPMF_toMeasure {A S : Type} [Fintype A] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : Parameter) (X : Configuration A → S) :
    (finiteStateLaw p X).toPMF.toMeasure = (siteMeasure p).map X := by
  apply Measure.ext_of_singleton
  intro s
  rw [PMF.toMeasure_apply_singleton _ s (measurableSet_singleton s),
    Measure.map_apply (measurable_of_finite X) (measurableSet_singleton s)]
  change ENNReal.ofReal (siteMeasure p (X ⁻¹' {s})).toReal = _
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Finite real upper-set inequalities imply actual upper-event measure
inequalities.  All events in this finite discrete state space are measurable. -/
theorem finiteDominates_measure_le {S : Type} [Fintype S] [Preorder S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν μ : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (h : finiteDominates (FiniteLaw.ofMeasure ν) (FiniteLaw.ofMeasure μ))
    (U : Set S) (hU : ∀ x y, x ∈ U → x ≤ y → y ∈ U) : ν U ≤ μ U := by
  classical
  have hν : (∑ s ∈ U.toFinset, (FiniteLaw.ofMeasure ν).mass s) =
      (ν U).toReal := by
    change (∑ s ∈ U.toFinset, (ν {s}).toReal) = _
    simpa only [measureReal_def, Set.coe_toFinset] using
      (sum_measureReal_singleton (μ := ν) U.toFinset)
  have hμ : (∑ s ∈ U.toFinset, (FiniteLaw.ofMeasure μ).mass s) =
      (μ U).toReal := by
    change (∑ s ∈ U.toFinset, (μ {s}).toReal) = _
    simpa only [measureReal_def, Set.coe_toFinset] using
      (sum_measureReal_singleton (μ := μ) U.toFinset)
  apply (ENNReal.toReal_le_toReal (measure_ne_top ν U) (measure_ne_top μ U)).mp
  rw [← hν, ← hμ]
  exact h U.toFinset (by simpa only [Set.mem_toFinset] using hU)

/-- Apply finite domination to the actual finite state laws without assuming
any law-table identification or measurable structure on the state type. -/
theorem finiteStateLaw_domination {A B S : Type} [Fintype A] [Fintype B]
    [Fintype S] [Preorder S] (p q : Parameter)
    (X : Configuration A → S) (Y : Configuration B → S)
    (h : finiteDominates (finiteStateLaw p X) (finiteStateLaw q Y))
    (U : Set S) (hU : ∀ x y, x ∈ U → x ≤ y → y ∈ U) :
    siteMeasure p (X ⁻¹' U) ≤ siteMeasure q (Y ⁻¹' U) := by
  classical
  have hX : (∑ s ∈ U.toFinset, (finiteStateLaw p X).mass s) =
      (siteMeasure p (X ⁻¹' U)).toReal := by
    change (∑ s ∈ U.toFinset, (siteMeasure p (X ⁻¹' {s})).toReal) = _
    simpa only [measureReal_def, Set.coe_toFinset] using
      (sum_measureReal_preimage_singleton (μ := siteMeasure p) (f := X)
        U.toFinset (fun s _ => (Set.toFinite (X ⁻¹' {s})).measurableSet))
  have hY : (∑ s ∈ U.toFinset, (finiteStateLaw q Y).mass s) =
      (siteMeasure q (Y ⁻¹' U)).toReal := by
    change (∑ s ∈ U.toFinset, (siteMeasure q (Y ⁻¹' {s})).toReal) = _
    simpa only [measureReal_def, Set.coe_toFinset] using
      (sum_measureReal_preimage_singleton (μ := siteMeasure q) (f := Y)
        U.toFinset (fun s _ => (Set.toFinite (Y ⁻¹' {s})).measurableSet))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← hX, ← hY]
  exact h U.toFinset (by simpa only [Set.mem_toFinset] using hU)

/-- Finite Strassen can consume a finite PMF by passing to its real law;
upper-set comparisons are equivalent in the two representations. -/
theorem finiteDominates_ofPMF_iff {S : Type} [Fintype S] [Preorder S]
    (ν μ : PMF S) :
    finiteDominates (FiniteLaw.ofPMF ν) (FiniteLaw.ofPMF μ) ↔
      ∀ U : Finset S, (∀ x y, x ∈ U → x ≤ y → y ∈ U) →
        ∑ s ∈ U, ν s ≤ ∑ s ∈ U, μ s := by
  unfold finiteDominates
  simp_rw [FiniteLaw.ofPMF_sum]
  constructor
  · intro h U hU
    exact (ENNReal.toReal_le_toReal
      (by simp [ ν.apply_ne_top])
      (by simp [ μ.apply_ne_top])).mp (h U hU)
  · intro h U hU
    exact (ENNReal.toReal_le_toReal
      (by simp [ ν.apply_ne_top])
      (by simp [ μ.apply_ne_top])).mpr (h U hU)

end SitePerc

#print axioms SitePerc.siteMeasure_singleton_toReal
#print axioms SitePerc.siteMeasure_singleton
#print axioms SitePerc.finiteStateLaw_mass
#print axioms SitePerc.siteMeasure_map_singleton
#print axioms SitePerc.FiniteLaw.ofPMF_toPMF
#print axioms SitePerc.FiniteLaw.ofPMF_sum
#print axioms SitePerc.FiniteLaw.ofMeasure_toPMF_toMeasure
#print axioms SitePerc.finiteStateLaw_toPMF_toMeasure
#print axioms SitePerc.finiteDominates_measure_le
#print axioms SitePerc.finiteStateLaw_domination
#print axioms SitePerc.finiteDominates_ofPMF_iff
