import SitePerc.Base
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Independence.InfinitePi

/-!
# Elementary foundations for Bernoulli site percolation

The probability space is the infinite independent Bernoulli product defined in
`SitePerc.Base`. Events and critical probability below use those definitions
without additional percolation assumptions.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SitePerc

/-- The symmetrization in `fromRel` does not change the intended site edges. -/
theorem siteGraph_adj_iff {A : Type} (G : SimpleGraph A) (ω : Configuration A)
    (u v : A) :
    (siteGraph G ω).Adj u v ↔ G.Adj u v ∧ ω u = true ∧ ω v = true := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

/-- Open connectivity is a countable union of finite, all-open walk witnesses. -/
theorem openCluster_mem_iff {A : Type} (G : SimpleGraph A) (ω : Configuration A)
    (v w : A) :
    w ∈ openCluster G ω v ↔ ∃ W : G.Walk v w, ∀ x ∈ W.support, ω x = true := by
  constructor
  · rintro ⟨hw, ⟨W⟩⟩
    have hle : siteGraph G ω ≤ G := fun u v h => (siteGraph_adj_iff G ω u v).mp h |>.1
    refine ⟨W.mapLe hle, ?_⟩
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    induction W with
    | nil => simpa using hw
    | @cons u z w ha W ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ((siteGraph_adj_iff G ω _ _).mp ha).2.1
      · exact ih hw x hx
  · rintro ⟨W, ho⟩
    induction W with
    | nil => exact ⟨ho _ (by simp), SimpleGraph.Reachable.refl _⟩
    | @cons u z w ha W ih =>
      have ht : ∀ x ∈ W.support, ω x = true :=
        fun x hx => ho x (List.mem_cons_of_mem u hx)
      obtain ⟨hw, hr⟩ := ih ht
      exact ⟨hw, ((siteGraph_adj_iff G ω u z).mpr
        ⟨ha, ho _ (by simp), ht _ W.start_mem_support⟩).reachable.trans hr⟩

/-- Open-cluster membership is a measurable event on a countable graph. -/
theorem openCluster_mem_measurable {A : Type} [Countable A]
    (G : SimpleGraph A) (v w : A) :
    MeasurableSet {ω : Configuration A | w ∈ openCluster G ω v} := by
  classical
  haveI : Countable (G.Walk v w) := SimpleGraph.Walk.support_injective.countable
  have heq : {ω : Configuration A | w ∈ openCluster G ω v} =
      ⋃ W : G.Walk v w, {ω | ∀ x ∈ W.support, ω x = true} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, openCluster_mem_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro W
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
    measurableSet_setOfPred.mpr
      ((measurable_pi_apply x : Measurable (fun ω : Configuration A => ω x)).eq_const true)

/-- The entire open cluster is a measurable random subset. -/
theorem openCluster_measurable {A : Type} [Countable A]
    (G : SimpleGraph A) (v : A) :
    Measurable (fun ω : Configuration A => openCluster G ω v) := by
  apply Measurable.of_mem
  intro w
  exact measurableSet_setOfPred.mp (openCluster_mem_measurable G v w)

/-- The infinite-cluster event is measurable; no local finiteness is needed. -/
theorem infiniteAt_measurable (G : SimpleGraph Vertex) (v : Vertex) :
    MeasurableSet (infiniteAt G v) := by
  exact ((measurable_pi_apply v) (measurableSet_singleton true)).inter
    (MeasurableSet.setOfPred_infinite.preimage (openCluster_measurable G v))

/-- Existence of an infinite cluster is a countable union of measurable events. -/
theorem infiniteExists_measurable (G : SimpleGraph Vertex) :
    MeasurableSet (infiniteExists G) := by
  have heq : infiniteExists G = ⋃ v, infiniteAt G v := by
    ext ω
    simp [infiniteExists]
  rw [heq]
  exact MeasurableSet.iUnion (infiniteAt_measurable G)

/-- Directly from the origin-based definition of the critical probability. -/
theorem pc_le_of_theta (p : Parameter) (h : 0 < theta square p (0, 0)) :
    pcSite ≤ p.val := by
  apply csInf_le
  · exact ⟨0, fun x hx => by obtain ⟨hx, _⟩ := hx; exact hx.1⟩
  · exact ⟨p.property, h⟩

/-- Any injective subfamily of iid sites still has the Bernoulli product law. -/
theorem siteMeasure_map_injective {A B : Type} (p : Parameter) (f : A → B)
    (hf : Function.Injective f) :
    (siteMeasure (A := B) p).map (fun ω a => ω (f a)) = siteMeasure p := by
  exact Measure.map_infinitePi_infinitePi_of_inj hf

/-- Square-lattice adjacency is preserved by every integer translation. -/
theorem square_adj_translate (z u v : Vertex) :
    square.Adj (u + z) (v + z) ↔ square.Adj u v := by
  simp only [square, SimpleGraph.fromRel_adj, ne_eq, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

/-- The Bernoulli square-lattice percolation probability is independent of root. -/
theorem theta_square_eq (p : Parameter) (v : Vertex) :
    theta square p v = theta square p (0, 0) := by
  let e : Vertex ≃ Vertex := Equiv.addRight v
  let T : Configuration Vertex → Configuration Vertex := fun ω a => ω (e a)
  have hm : Measurable T := by fun_prop
  have e0 : e (0, 0) = v := by change (0 : Vertex) + v = v; exact zero_add v
  have ei0 : e.symm v = (0, 0) := by
    apply e.injective
    rw [e.apply_symm_apply, e0]
  have hevent : T ⁻¹' infiniteAt square (0, 0) = infiniteAt square v := by
    ext ω
    let φ : siteGraph square (T ω) ≃g siteGraph square ω :=
      { toEquiv := e
        map_rel_iff' := by
          intro a b
          simp only [siteGraph_adj_iff, T]
          exact and_congr (square_adj_translate v a b) Iff.rfl }
    have himage : e '' openCluster square (T ω) (0, 0) =
        openCluster square ω v := by
      ext w
      constructor
      · rintro ⟨a, ⟨ha, hr⟩, rfl⟩
        refine ⟨ha, ?_⟩
        have ht : (siteGraph square ω).Reachable (e (0, 0)) (e a) := hr.map φ.toHom
        simpa only [e0] using ht
      · rintro ⟨hw, hr⟩
        refine ⟨e.symm w, ⟨?_, ?_⟩, e.apply_symm_apply w⟩
        · simpa [T] using hw
        · have ht : (siteGraph square (T ω)).Reachable (e.symm v) (e.symm w) :=
            hr.map φ.symm.toHom
          simpa only [ei0] using ht
    have hinf : (openCluster square (T ω) (0, 0)).Infinite ↔
        (openCluster square ω v).Infinite := by
      rw [← himage]
      exact (Set.infinite_image_iff e.injective.injOn).symm
    change (ω (e (0, 0)) = true ∧ _) ↔ (ω v = true ∧ _)
    rw [e0]
    exact ⟨fun h => ⟨h.1, hinf.mp h.2⟩, fun h => ⟨h.1, hinf.mpr h.2⟩⟩
  calc
    theta square p v = siteMeasure p (T ⁻¹' infiniteAt square (0, 0)) := by
      rw [hevent]; rfl
    _ = (siteMeasure p).map T (infiniteAt square (0, 0)) :=
      (Measure.map_apply hm (infiniteAt_measurable square (0, 0))).symm
    _ = theta square p (0, 0) := by
      rw [show (siteMeasure p).map T = siteMeasure p from
        siteMeasure_map_injective p e e.injective]
      rfl

/-- Countability and translation invariance turn existence into origin positivity. -/
theorem square_exists_to_origin (p : Parameter)
    (h : 0 < infiniteProbability square p) : 0 < theta square p (0, 0) := by
  have heq : infiniteExists square = ⋃ v, infiniteAt square v := by
    ext ω
    simp [infiniteExists]
  have hp : siteMeasure p (⋃ v, infiniteAt square v) ≠ 0 := by
    rw [← heq]
    exact ne_of_gt h
  obtain ⟨v, hv⟩ := exists_measure_pos_of_not_measure_iUnion_null hp
  change 0 < theta square p v at hv
  simpa only [theta_square_eq p v] using hv

/-- The common-uniform threshold map is measurable. -/
theorem threshold_measurable (p : Parameter) :
    Measurable (fun u : Parameter => if u ≤ p then true else false) := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- A thresholded uniform point has exactly the prescribed Bernoulli law. -/
theorem threshold_law (p : Parameter) :
    (volume : Measure Parameter).map (fun u : Parameter => if u ≤ p then true else false) =
      bernoulliMeasure true false p := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (threshold_measurable p) (measurableSet_singleton b)]
  cases b with
  | false =>
    have heq : (fun u : Parameter => if u ≤ p then true else false) ⁻¹' {false} =
        Set.Ioi p := by ext u; simp
    rw [heq, unitInterval.volume_Ioi]
    simp [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq, unitInterval.coe_symm_eq]
  | true =>
    have heq : (fun u : Parameter => if u ≤ p then true else false) ⁻¹' {true} =
        Set.Iic p := by ext u; simp
    rw [heq, unitInterval.volume_Iic]
    simp [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq]

/-- Simultaneous uniform thresholds realize the genuine infinite iid site law. -/
theorem siteMeasure_threshold {A : Type} (p : Parameter) :
    (Measure.infinitePi (fun _ : A => (volume : Measure Parameter))).map
      (fun u a => if u a ≤ p then true else false) = siteMeasure p := by
  rw [Measure.infinitePi_map_pi _ (fun _ => threshold_measurable p)]
  simp only [threshold_law, siteMeasure]

/-- Monotonicity of all measurable increasing site events, from an explicit coupling. -/
theorem siteMeasure_mono {A : Type} (p q : Parameter) (hpq : p.val ≤ q.val)
    (U : Set (Configuration A)) (hU : MeasurableSet U)
    (hupper : ∀ ω η : Configuration A,
      (∀ a, ω a = true → η a = true) → ω ∈ U → η ∈ U) :
    siteMeasure p U ≤ siteMeasure q U := by
  classical
  let μ : Measure (A → Parameter) := Measure.infinitePi (fun _ => volume)
  let fp : (A → Parameter) → Configuration A := fun u a => if u a ≤ p then true else false
  let fq : (A → Parameter) → Configuration A := fun u a => if u a ≤ q then true else false
  have hmp : Measurable fp := Measurable.of_eval fun a =>
    (threshold_measurable p).comp (measurable_pi_apply a)
  have hmq : Measurable fq := Measurable.of_eval fun a =>
    (threshold_measurable q).comp (measurable_pi_apply a)
  rw [← siteMeasure_threshold p, ← siteMeasure_threshold q,
    Measure.map_apply hmp hU, Measure.map_apply hmq hU]
  apply measure_mono
  intro u hu
  apply hupper (fp u) (fq u) ?_ hu
  intro a ha
  have hp : u a ≤ p := by simpa [fp] using ha
  have hq : u a ≤ q := le_trans hp hpq
  simp [fq, hq]

/-- An infinite open cluster cannot be destroyed by opening more sites. -/
theorem infiniteAt_mono {A : Type} (G : SimpleGraph A) (v : A)
    (ω η : Configuration A) (hop : ∀ a, ω a = true → η a = true) :
    ω ∈ infiniteAt G v → η ∈ infiniteAt G v := by
  rintro ⟨ho, hi⟩
  refine ⟨hop v ho, hi.mono ?_⟩
  intro w hw
  obtain ⟨W, hW⟩ := (openCluster_mem_iff G ω v w).mp hw
  exact (openCluster_mem_iff G η v w).mpr ⟨W, fun x hx => hop x (hW x hx)⟩

/-- The percolation probability is monotone in the Bernoulli parameter. -/
theorem theta_mono (G : SimpleGraph Vertex) (v : Vertex)
    (p q : Parameter) (hpq : p.val ≤ q.val) : theta G p v ≤ theta G q v := by
  exact siteMeasure_mono p q hpq (infiniteAt G v) (infiniteAt_measurable G v)
    (fun ω η hop => infiniteAt_mono G v ω η hop)

/-- The zero-parameter site law is concentrated on the all-closed field. -/
theorem siteMeasure_zero {A : Type} :
    siteMeasure (A := A) 0 = Measure.dirac (fun _ => false) := by
  simp [siteMeasure]

/-- The unit-parameter site law is concentrated on the all-open field. -/
theorem siteMeasure_one {A : Type} :
    siteMeasure (A := A) 1 = Measure.dirac (fun _ => true) := by
  simp [siteMeasure]

/-- A closed origin cannot percolate at parameter zero. -/
theorem theta_zero (G : SimpleGraph Vertex) (v : Vertex) : theta G 0 v = 0 := by
  rw [theta, siteMeasure_zero]
  simp [infiniteAt]

/-- The nonnegative horizontal ray gives percolation at parameter one. -/
theorem theta_square_one : theta square 1 (0, 0) = 1 := by
  have hreach : ∀ n : ℕ,
      (siteGraph square (fun _ => true)).Reachable (0, 0) ((n : ℤ), 0) := by
    intro n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      apply (siteGraph_adj_iff square (fun _ => true) _ _).mpr
      refine ⟨?_, rfl, rfl⟩
      simp [square, SimpleGraph.fromRel_adj, Nat.cast_add, Nat.cast_one]
  have hinj : Function.Injective (fun n : ℕ => ((n : ℤ), (0 : ℤ))) := by
    intro n m h
    exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  have hfull : (fun _ : Vertex => true) ∈ infiniteAt square (0, 0) := by
    refine ⟨rfl, (Set.infinite_range_of_injective hinj).mono ?_⟩
    rintro w ⟨n, rfl⟩
    exact ⟨rfl, hreach n⟩
  rw [theta, siteMeasure_one]
  simp [hfull]

/-- Every parameter strictly above the infimum has positive origin probability. -/
theorem theta_pos_of_pc_lt (p : Parameter) (h : pcSite < p.val) :
    0 < theta square p (0, 0) := by
  let S : Set ℝ := {r | ∃ hr : r ∈ Set.Icc (0 : ℝ) 1,
    0 < theta square ⟨r, hr⟩ (0, 0)}
  have hne : S.Nonempty := by
    refine ⟨(1 : Parameter).val, (1 : Parameter).property, ?_⟩
    rw [theta_square_one]
    exact zero_lt_one
  have hbdd : BddBelow S := ⟨0, fun r hr => by
    obtain ⟨hr, _⟩ := hr
    exact hr.1⟩
  have hs : sInf S < p.val := h
  obtain ⟨r, ⟨hr, hθ⟩, hrp⟩ := (csInf_lt_iff hbdd hne).mp hs
  exact lt_of_lt_of_le hθ (theta_mono square (0, 0) ⟨r, hr⟩ p hrp.le)

/-- The real-valued supercritical percolation probability is strictly positive. -/
theorem theta_positive_above_pc (p : Parameter) (h : pcSite < p.val) :
    0 < thetaReal p := by
  exact ENNReal.toReal_pos (ne_of_gt (theta_pos_of_pc_lt p h))
    (measure_ne_top (siteMeasure p) (infiniteAt square (0, 0)))

/-- The positive-probability parameter set is nonempty and contained in [0,1]. -/
theorem pcSite_nonneg : 0 ≤ pcSite := by
  apply le_csInf
  · refine ⟨(1 : Parameter).val, (1 : Parameter).property, ?_⟩
    rw [theta_square_one]
    exact zero_lt_one
  · rintro r ⟨hr, _⟩
    exact hr.1

/-- Parameter one bounds the critical probability from above. -/
theorem pcSite_le_one : pcSite ≤ 1 := by
  have h : 0 < theta square 1 (0, 0) := by rw [theta_square_one]; exact zero_lt_one
  exact pc_le_of_theta 1 h

/-- All strictly subcritical parameters have zero origin probability. -/
theorem theta_eq_zero_of_lt_pc (p : Parameter) (h : p.val < pcSite) :
    theta square p (0, 0) = 0 := by
  by_contra hn
  have hp : 0 < theta square p (0, 0) := pos_iff_ne_zero.mpr hn
  exact (not_le_of_gt h) (pc_le_of_theta p hp)

/-- The infimum-of-positive and supremum-of-zero definitions agree exactly. -/
theorem pcSite_eq_sSup_zero :
    pcSite = sSup {p : ℝ | ∃ hp : p ∈ Set.Icc (0 : ℝ) 1,
      theta square ⟨p, hp⟩ (0, 0) = 0} := by
  let Z : Set ℝ := {p | ∃ hp : p ∈ Set.Icc (0 : ℝ) 1,
    theta square ⟨p, hp⟩ (0, 0) = 0}
  have hzero : (0 : ℝ) ∈ Z := ⟨(0 : Parameter).property, theta_zero square (0, 0)⟩
  have hne : Z.Nonempty := ⟨0, hzero⟩
  have hbdd : BddAbove Z := ⟨1, fun r hr => by obtain ⟨hr, _⟩ := hr; exact hr.2⟩
  have hnonneg : 0 ≤ sSup Z := le_csSup hbdd hzero
  change pcSite = sSup Z
  apply le_antisymm
  · by_contra hn
    have hgap : sSup Z < pcSite := lt_of_not_ge hn
    obtain ⟨r, hsr, hrp⟩ := exists_between hgap
    have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans hnonneg hsr.le, le_trans hrp.le pcSite_le_one⟩
    have hz : r ∈ Z := ⟨hr, theta_eq_zero_of_lt_pc ⟨r, hr⟩ hrp⟩
    exact (not_lt_of_ge (le_csSup hbdd hz)) hsr
  · apply csSup_le hne
    rintro r ⟨hr, hz⟩
    by_contra hn
    have hp := theta_pos_of_pc_lt ⟨r, hr⟩ (lt_of_not_ge hn)
    rw [hz] at hp
    exact (lt_irrefl 0) hp

end SitePerc
