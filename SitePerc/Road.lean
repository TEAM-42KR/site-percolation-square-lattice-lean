import SitePerc.Base
import SitePerc.Foundations
import SitePerc.Occupancy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Largest clusters and the random-completion application

This file uses nearest-neighbour connectivity inside the finite board.
Classical percolation inputs are explicit theorem arguments, never axioms.
The board side is `n+1`, a harmless reindexing of the positive side lengths.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SitePerc

/-- The natural embedding of a finite board into the square lattice. -/
def roadBoardEmbedding (n : ℕ) (v : Board n) : Vertex :=
  (v.1.val, v.2.val)

/-- `|C(v)| ≥ k`, expressed by a finite witness so infinite clusters also qualify. -/
def subcriticalVolumeEvent (v : Vertex) (k : ℕ) : Set (Configuration Vertex) :=
  {ω | ∃ s : Finset Vertex, (∀ w ∈ s, w ∈ openCluster square ω v) ∧ k ≤ s.card}

/-- Classical input (3), in the relative topology of the parameter interval. -/
def ThetaContinuousAbovePc : Prop :=
  ∀ p : Parameter, pcSite < p.val → ContinuousAt thetaReal p

/-- Classical input (4): the usual uniform-in-the-root exponential volume tail. -/
def SubcriticalExponentialVolumeTail : Prop :=
  ∀ p : Parameter, 0 < p.val → p.val < pcSite →
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ (v : Vertex) (k : ℕ),
      siteMeasure p (subcriticalVolumeEvent v k) ≤
        ENNReal.ofReal (C * Real.exp (-a * k))

/-- Classical input (5): van den Berg--Ermakov (1996), Theorem 1.1, p. 200.
This is the site-critical lower bound itself, not a completion-time conclusion. -/
def VanDenBergErmakov1996LowerBound : Prop :=
  (139 / 250 : ℝ) < pcSite

/-- Opening additional vertices preserves every open edge. -/
theorem road_siteGraph_mono {A : Type} (G : SimpleGraph A)
    {ω η : Configuration A} (h : ∀ v, ω v = true → η v = true) :
    siteGraph G ω ≤ siteGraph G η := by
  intro u v huv
  rw [siteGraph, SimpleGraph.fromRel_adj] at huv ⊢
  rcases huv with ⟨hne, huv | hvu⟩
  · exact ⟨hne, Or.inl ⟨huv.1, h u huv.2.1, h v huv.2.2⟩⟩
  · exact ⟨hne, Or.inr ⟨hvu.1, h v hvu.2.1, h u hvu.2.2⟩⟩

/-- Equation (6.1): every old component lies inside a new component. -/
theorem largestCluster_mono {A : Type} [Fintype A] (G : SimpleGraph A)
    {ω η : Configuration A} (h : ∀ v, ω v = true → η v = true) :
    largestCluster G ω ≤ largestCluster G η := by
  classical
  unfold largestCluster
  apply Finset.sup_le
  intro v _
  refine le_trans (Finset.card_le_card (s := Finset.univ.filter (fun w =>
    ω w = true ∧ (siteGraph G ω).Reachable v w))
    (t := Finset.univ.filter (fun w =>
    η w = true ∧ (siteGraph G η).Reachable v w)) ?_)
    (Finset.le_sup (f := fun u : A => (Finset.univ.filter (fun w =>
      η w = true ∧ (siteGraph G η).Reachable u w)).card) (Finset.mem_univ v))
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact ⟨h w hw.1, hw.2.mono (road_siteGraph_mono G h)⟩

/-- A finite union bound; no independence or event measurability is needed. -/
theorem largestCluster_tail_union_bound {A : Type} [Fintype A] (G : SimpleGraph A)
    (μ : Measure (Configuration A)) (k : ℕ) :
    μ {ω | k < largestCluster G ω} ≤
      ∑ v : A, μ {ω | k < (by classical exact
        (Finset.univ.filter (fun w => ω w = true ∧
          (siteGraph G ω).Reachable v w)).card : ℕ)} := by
  classical
  apply le_trans (measure_mono ?_) (measure_iUnion_fintype_le μ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, largestCluster, Finset.lt_sup_iff] at hω
  obtain ⟨v, _, hv⟩ := hω
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

/-- The elementary strict gap used for one completion per cell. -/
theorem rational_gap : (79 / 125 : ℝ) < roadParameter.val := by
  have he : (125 / 46 : ℝ) < Real.exp 1 := by
    have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at hs
    linarith
  have hi : (Real.exp 1)⁻¹ < (46 / 125 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).2
    nlinarith
  change (79 / 125 : ℝ) < 1 - Real.exp (-1)
  rw [Real.exp_neg]
  linarith

/-- The analytic part of the subcritical union bound. -/
theorem logarithmic_union_decay (C a K : ℝ) (h : 2 < a * K) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * C *
      Real.exp (-a * (K * Real.log ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hl := Real.tendsto_log_atTop.comp hs
  have hd : 0 < a * K - 2 := by linarith
  have hz := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hl.const_mul_atTop hd)
  have heq (n : ℕ) : ((n : ℝ) + 1) ^ 2 * C *
      Real.exp (-a * (K * Real.log ((n : ℝ) + 1))) =
      C * Real.exp (-((a * K - 2) * Real.log ((n : ℝ) + 1))) := by
    have hx : 0 < (n : ℝ) + 1 := by positivity
    rw [show ((n : ℝ) + 1) ^ 2 =
      Real.exp (2 * Real.log ((n : ℝ) + 1)) by
        rw [show (2 : ℝ) * Real.log ((n : ℝ) + 1) =
          Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1) by ring,
          Real.exp_add, Real.exp_log hx]
        ring]
    rw [mul_comm _ C, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simpa only [heq, Function.comp_def, mul_zero] using hz.const_mul C

/-- Restricting a genuine iid product law preserves the iid marginal law. -/
theorem road_siteMeasure_map_injective {A B : Type} (f : A → B)
    (hf : Function.Injective f) (p : Parameter) :
    (siteMeasure (A := B) p).map (fun ω v => ω (f v)) =
      siteMeasure (A := A) p := by
  let e := Equiv.ofInjective f hf
  have hr : (siteMeasure (A := B) p).map (Set.range f).domRestrict =
      siteMeasure (A := Set.range f) p :=
    Measure.infinitePi_map_restrict' _
  have he : (siteMeasure (A := Set.range f) p).map
      (MeasurableEquiv.piCongrLeft (fun _ : A => Bool) e.symm) =
      siteMeasure (A := A) p :=
    Measure.infinitePi_map_piCongrLeft
      (fun _ : A => bernoulliMeasure true false p) e.symm
  rw [← hr, Measure.map_map (by fun_prop) (by fun_prop)] at he
  convert he using 1
  congr 1
  funext ω v
  simpa [Function.comp_def, e] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : A => Bool) e.symm
      ((Set.range f).domRestrict ω) (e v)).symm

/-- Complementation costs no additional error, even for different sample spaces. -/
theorem road_complement_transfer {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (e : ℝ≥0∞) (h : ν t ≤ μ s + e) : μ sᶜ ≤ ν tᶜ + e := by
  apply ENNReal.le_of_add_le_add_right (measure_ne_top ν t)
  calc
    μ sᶜ + ν t ≤ μ sᶜ + (μ s + e) := add_le_add le_rfl h
    _ = (μ s + μ sᶜ) + e := by ac_rfl
    _ = 1 + e := by rw [measure_add_measure_compl hs, measure_univ]
    _ = (ν t + ν tᶜ) + e := by rw [measure_add_measure_compl ht, measure_univ]
    _ = (ν tᶜ + e) + ν t := by ac_rfl

/-- Continuity provides strictly bracketing supercritical parameters. -/
theorem road_continuous_parameter_sandwich (r : Parameter)
    (hr : 0 < r.val) (hr1 : r.val < 1) (hpc : pcSite < r.val)
    (hc : ContinuousAt thetaReal r) (ε : ℝ) (hε : 0 < ε) :
    ∃ l u : Parameter, pcSite < l.val ∧ l.val < r.val ∧ r.val < u.val ∧
      |thetaReal l - thetaReal r| < ε ∧ |thetaReal u - thetaReal r| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let d := min (δ / 2) (min ((r.val - pcSite) / 2)
    (min (r.val / 2) ((1 - r.val) / 2)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hdp : d ≤ (r.val - pcSite) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hdr : d ≤ r.val / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd1 : d ≤ (1 - r.val) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  let l : Parameter := ⟨r.val - d, by constructor <;> linarith [r.property.2]⟩
  let u : Parameter := ⟨r.val + d, by constructor <;> linarith⟩
  have hld : dist l r < δ := by
    change |(r.val - d) - r.val| < δ
    rw [show (r.val - d) - r.val = -d by ring, abs_neg, abs_of_pos hd]
    exact hdδ
  have hud : dist u r < δ := by
    change |(r.val + d) - r.val| < δ
    rw [show (r.val + d) - r.val = d by ring, abs_of_pos hd]
    exact hdδ
  refine ⟨l, u, ?_, ?_, ?_, ?_, ?_⟩
  · change pcSite < r.val - d
    linarith
  · change r.val - d < r.val
    linarith
  · change r.val < r.val + d
    linarith
  · simpa only [Real.dist_eq] using hclose hld
  · simpa only [Real.dist_eq] using hclose hud

/-- The symmetrized graph definition records precisely two open endpoints. -/
theorem road_siteGraph_adj_iff {A : Type} (G : SimpleGraph A)
    (ω : Configuration A) (u v : A) :
    (siteGraph G ω).Adj u v ↔ G.Adj u v ∧ ω u = true ∧ ω v = true := by
  rw [siteGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

/-- No distinct finite-board vertices are identified. -/
theorem road_boardEmbedding_injective (n : ℕ) :
    Function.Injective (roadBoardEmbedding n) := by
  intro u v h
  apply Prod.ext
  · apply Fin.ext
    have he := congrArg Prod.fst h
    dsimp [roadBoardEmbedding] at he
    exact_mod_cast he
  · apply Fin.ext
    have he := congrArg Prod.snd h
    dsimp [roadBoardEmbedding] at he
    exact_mod_cast he

/-- All finite-board edges are genuine lattice edges. -/
theorem road_boardEmbedding_adj (n : ℕ) {u v : Board n}
    (h : (boardGraph n).Adj u v) :
    square.Adj (roadBoardEmbedding n u) (roadBoardEmbedding n v) := by
  rw [boardGraph, SimpleGraph.fromRel_adj] at h
  rw [square, SimpleGraph.fromRel_adj]
  refine ⟨fun he => h.1 (road_boardEmbedding_injective n he), ?_⟩
  have hm (x y : Board n)
      (hxy : (y.1.val = x.1.val + 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2.val = x.2.val + 1)) :
      ((roadBoardEmbedding n y).1 = (roadBoardEmbedding n x).1 + 1 ∧
        (roadBoardEmbedding n y).2 = (roadBoardEmbedding n x).2) ∨
      ((roadBoardEmbedding n y).1 = (roadBoardEmbedding n x).1 ∧
        (roadBoardEmbedding n y).2 = (roadBoardEmbedding n x).2 + 1) := by
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨by dsimp [roadBoardEmbedding]; exact_mod_cast hx,
        by dsimp [roadBoardEmbedding]; exact congrArg (fun z : Fin (n+1) => (z.val : ℤ)) hy⟩
    · exact Or.inr ⟨by dsimp [roadBoardEmbedding]; exact congrArg (fun z : Fin (n+1) => (z.val : ℤ)) hx,
        by dsimp [roadBoardEmbedding]; exact_mod_cast hy⟩
  exact h.2.elim (fun he => Or.inl (hm u v he)) (fun he => Or.inr (hm v u he))

/-- Infinite-volume exponential tails imply the literal finite-board union bound. -/
theorem road_iid_largest_tail (p : Parameter) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ (v : Vertex) (k : ℕ),
      siteMeasure p (subcriticalVolumeEvent v k) ≤
        ENNReal.ofReal (C * Real.exp (-a * k)))
    (n : ℕ) (t : ℝ) (_ht : 0 ≤ t) :
    siteMeasure (A := Board n) p {ω | t < (largestCluster (boardGraph n) ω : ℝ)} ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * C * Real.exp (-a * t)) := by
  classical
  let R : Configuration Vertex → Configuration (Board n) :=
    fun ω v => ω (roadBoardEmbedding n v)
  have hR : Measurable R := by fun_prop
  have hRm := road_siteMeasure_map_injective (roadBoardEmbedding n)
    (road_boardEmbedding_injective n) p
  have hE : MeasurableSet {ω : Configuration (Board n) |
      t < (largestCluster (boardGraph n) ω : ℝ)} := (Set.toFinite _).measurableSet
  have hinc : R ⁻¹' {ω | t < (largestCluster (boardGraph n) ω : ℝ)} ⊆
      ⋃ v : Board n, subcriticalVolumeEvent (roadBoardEmbedding n v) ⌈t⌉₊ := by
    intro ω hω
    change t < (largestCluster (boardGraph n) (R ω) : ℝ) at hω
    let s (v : Board n) := Finset.univ.filter (fun w =>
      R ω w = true ∧ (siteGraph (boardGraph n) (R ω)).Reachable v w)
    obtain ⟨v, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ
      (Finset.univ_nonempty : (Finset.univ : Finset (Board n)).Nonempty)
      (fun v => (s v).card)
    have hm : largestCluster (boardGraph n) (R ω) = (s v).card := hmax
    have hk : ⌈t⌉₊ ≤ (s v).card := Nat.ceil_le.mpr (le_of_lt (by simpa only [hm] using hω))
    let φ : siteGraph (boardGraph n) (R ω) →g siteGraph square ω :=
      { toFun := roadBoardEmbedding n
        map_rel' := by
          intro u v huv
          rw [road_siteGraph_adj_iff] at huv ⊢
          exact ⟨road_boardEmbedding_adj n huv.1, huv.2⟩ }
    refine Set.mem_iUnion.mpr ⟨v, ?_⟩
    refine ⟨(s v).image (roadBoardEmbedding n), ?_, ?_⟩
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hz' := (Finset.mem_filter.mp hz).2
      exact ⟨hz'.1, hz'.2.map φ⟩
    · rw [Finset.card_image_of_injective _ (road_boardEmbedding_injective n)]
      exact hk
  calc
    siteMeasure (A := Board n) p {ω | t < (largestCluster (boardGraph n) ω : ℝ)} =
        siteMeasure (A := Vertex) p
          (R ⁻¹' {ω | t < (largestCluster (boardGraph n) ω : ℝ)}) := by
      rw [← hRm, Measure.map_apply hR hE]
    _ ≤ siteMeasure p (⋃ v : Board n,
        subcriticalVolumeEvent (roadBoardEmbedding n v) ⌈t⌉₊) := measure_mono hinc
    _ ≤ ∑ v : Board n, siteMeasure p
        (subcriticalVolumeEvent (roadBoardEmbedding n v) ⌈t⌉₊) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _v : Board n, ENNReal.ofReal (C * Real.exp (-a * t)) := by
      apply Finset.sum_le_sum
      intro v _
      refine (htail (roadBoardEmbedding n v) ⌈t⌉₊).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.le_ceil t]
    _ = ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * C * Real.exp (-a * t)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : Fintype.card (Board n) = (n + 1) ^ 2 := by simp [Board, pow_two]
      rw [hcard, ← ENNReal.ofReal_natCast]
      push_cast
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Turning a vanishing exceptional probability into a high-probability statement. -/
theorem road_probability_complement_limit {A : ℕ → Type}
    [∀ n, MeasurableSpace (A n)] (μ : ∀ n, Measure (A n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Set (A n))
    (hs : ∀ n, MeasurableSet (s n))
    (h : Tendsto (fun n => μ n (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (s n)ᶜ) atTop (𝓝 1) := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h
    (Or.inl (by norm_num))
  simpa only [measure_compl (hs _) (measure_ne_top _ _), measure_univ, tsub_zero] using ht

/-- The subcritical iid largest cluster is logarithmic with high probability. -/
theorem road_iid_subcritical_logarithmic (tail : SubcriticalExponentialVolumeTail)
    (p : Parameter) (hp0 : 0 < p.val) (hp : p.val < pcSite) :
    ∃ K : ℝ, 0 < K ∧ Tendsto (fun n : ℕ => siteMeasure (A := Board n) p
      {ω | (largestCluster (boardGraph n) ω : ℝ) ≤ K * Real.log ((n : ℝ) + 1)})
      atTop (𝓝 1) := by
  obtain ⟨C, a, hC, ha, htail⟩ := tail p hp0 hp
  let K : ℝ := 3 / a
  have hK : 0 < K := div_pos (by norm_num) ha
  have hKa : 2 < a * K := by dsimp [K]; field_simp; linarith
  have hz : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * C *
      Real.exp (-a * (K * Real.log ((n : ℝ) + 1))))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (logarithmic_union_decay C a K hKa)
  have hb (n : ℕ) : siteMeasure (A := Board n) p
      {ω | K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)} ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * C *
        Real.exp (-a * (K * Real.log ((n : ℝ) + 1)))) :=
    road_iid_largest_tail p C a hC.le ha htail n _
      (mul_nonneg hK.le (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])))
  have hb0 := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hz
    (Eventually.of_forall (fun _ => bot_le)) (Eventually.of_forall hb)
  refine ⟨K, hK, ?_⟩
  have hgood := road_probability_complement_limit
    (fun n => siteMeasure (A := Board n) p)
    (fun n => {ω | K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)})
    (fun _ => (Set.toFinite _).measurableSet) hb0
  simpa only [Set.compl_ofPred, not_lt] using hgood

/-- The exact, nonnumerical threshold conversion in Corollary 1.3. -/
theorem road_rho_gt_iff (p c : ℝ) (hp : p < 1) :
    p < 1 - Real.exp (-c) ↔ -Real.log (1 - p) < c := by
  have hp' : 0 < 1 - p := by linarith
  constructor
  · intro h
    have hl := Real.strictMonoOn_log (Real.exp_pos (-c)) hp' (show Real.exp (-c) < 1-p by linarith)
    rw [Real.log_exp] at hl
    linarith
  · intro h
    have he := Real.exp_lt_exp.mpr (show -c < Real.log (1-p) by linarith)
    rw [Real.exp_log hp'] at he
    linarith

/-- The normalized finite-board largest-cluster observable is increasing. -/
theorem road_iidDensity_mono (n : ℕ) {ω η : Configuration (Board n)}
    (h : ∀ v, ω v = true → η v = true) : iidDensity n ω ≤ iidDensity n η := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast largestCluster_mono (boardGraph n) h

/-- Quantitative probability squeeze, including the lower tail by complementation. -/
theorem road_density_deviation_bound {A B : Type} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (νm νp : Measure B) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure νm] [IsProbabilityMeasure νp]
    (X : A → ℝ) (Y : B → ℝ) (a b d ε : ℝ) (hε : 0 < ε)
    (hb : |b - a| < ε / 2) (hd : |d - a| < ε / 2) (e : ℝ≥0∞)
    (hl : νm {y | a - ε < Y y} ≤ μ {x | a - ε < X x} + e)
    (hu : μ {x | a + ε < X x} ≤ νp {y | a + ε < Y y} + e) :
    μ {x | ε < |X x - a|} ≤
      (νm {y | ε / 2 < |Y y - b|} + νp {y | ε / 2 < |Y y - d|}) + (e + e) := by
  have hbad : {x | ε < |X x - a|} ⊆ {x | a - ε < X x}ᶜ ∪ {x | a + ε < X x} := by
    intro x hx
    change ¬(a - ε < X x) ∨ a + ε < X x
    by_cases hlo : X x ≤ a - ε
    · exact Or.inl (not_lt_of_ge hlo)
    · right
      by_contra hup
      have hbound : |X x - a| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
      exact (not_le_of_gt hx) hbound
  have hlbad : {y | a - ε < Y y}ᶜ ⊆ {y | ε / 2 < |Y y - b|} := by
    intro y hy
    change ¬(a - ε < Y y) at hy
    have hba := (abs_lt.mp hb).1
    have hh : ε / 2 < b - Y y := by linarith
    exact hh.trans_le (by rw [abs_sub_comm]; exact le_abs_self _)
  have hubad : {y | a + ε < Y y} ⊆ {y | ε / 2 < |Y y - d|} := by
    intro y hy
    change a + ε < Y y at hy
    have hda := (abs_lt.mp hd).2
    have hh : ε / 2 < Y y - d := by linarith
    exact hh.trans_le (le_abs_self _)
  have hc := road_complement_transfer μ νm
    {x | a - ε < X x} {y | a - ε < Y y}
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet e hl
  calc
    μ {x | ε < |X x - a|} ≤ μ ({x | a - ε < X x}ᶜ ∪ {x | a + ε < X x}) :=
      measure_mono hbad
    _ ≤ μ {x | a - ε < X x}ᶜ + μ {x | a + ε < X x} := measure_union_le _ _
    _ ≤ (νm {y | a - ε < Y y}ᶜ + e) + (νp {y | a + ε < Y y} + e) := add_le_add hc hu
    _ ≤ (νm {y | ε / 2 < |Y y - b|} + e) + (νp {y | ε / 2 < |Y y - d|} + e) :=
      add_le_add (add_le_add (measure_mono hlbad) le_rfl)
        (add_le_add (measure_mono hubad) le_rfl)
    _ = _ := by ac_rfl

/-- Manuscript Theorem 1.2(a), using the proved occupancy sandwich. -/
theorem road_theorem12a (density : SupercriticalGiantDensity)
    (continuous : ThetaContinuousAbovePc) (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) + 1) ^ 2) atTop (𝓝 c))
    (hpc : pcSite < 1 - Real.exp (-c)) :
    ConvergesInProbability (fun n => roadLawM n (m n))
      (fun n => roadDensityM n (m n)) (thetaReal (completionParameter c hc.le)) ∧
      0 < thetaReal (completionParameter c hc.le) := by
  have hsand := occupancy_sandwich m c hc hm
  let r := completionParameter c hc.le
  have hr : 0 < r.val := by
    have he : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    change 0 < 1 - Real.exp (-c)
    linarith
  have hr1 : r.val < 1 := by
    change 1 - Real.exp (-c) < 1
    linarith [Real.exp_pos (-c)]
  have hpr : pcSite < r.val := hpc
  constructor
  · intro ε hε
    obtain ⟨l, u, hpl, hlr, hru, hθl, hθu⟩ :=
      road_continuous_parameter_sandwich r hr hr1 hpr (continuous r hpr)
        (ε / 2) (half_pos hε)
    obtain ⟨err, herr, hs⟩ := hsand l u hlr hru
    have hdl := density l hpl (ε / 2) (half_pos hε)
    have hdu := density u (hpr.trans hru) (ε / 2) (half_pos hε)
    have hb (n : ℕ) :
        roadLawM n (m n) {w | ε < |roadDensityM n (m n) w - thetaReal r|} ≤
        (siteMeasure l {ω | ε / 2 < |iidDensity n ω - thetaReal l|} +
          siteMeasure u {ω | ε / 2 < |iidDensity n ω - thetaReal u|}) + (err n + err n) := by
      apply road_density_deviation_bound (roadLawM n (m n))
        (siteMeasure l) (siteMeasure u) (fun w => roadDensityM n (m n) w)
        (iidDensity n) (thetaReal r) (thetaReal l) (thetaReal u) ε hε hθl hθu (err n)
      · have hinc : increasingEvent {ω : Configuration (Board n) |
            thetaReal r - ε < iidDensity n ω} := by
          intro ω η hωη hω
          exact lt_of_lt_of_le hω (road_iidDensity_mono n hωη)
        exact (hs n _ hinc).1
      · have hinc : increasingEvent {ω : Configuration (Board n) |
            thetaReal r + ε < iidDensity n ω} := by
          intro ω η hωη hω
          exact lt_of_lt_of_le hω (road_iidDensity_mono n hωη)
        exact (hs n _ hinc).2
    have hsum : Tendsto (fun n =>
        (siteMeasure l {ω | ε / 2 < |iidDensity n ω - thetaReal l|} +
          siteMeasure u {ω | ε / 2 < |iidDensity n ω - thetaReal u|}) + (err n + err n))
        atTop (𝓝 0) := by
      simpa only [zero_add] using (hdl.add hdu).add (herr.add herr)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hsum
      (Eventually.of_forall (fun _ => bot_le)) (Eventually.of_forall hb)
  · exact theta_positive_above_pc r hpr

/-- Manuscript Theorem 1.2(b), using the proved occupancy sandwich. -/
theorem road_theorem12b (tail : SubcriticalExponentialVolumeTail)
    (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) + 1) ^ 2) atTop (𝓝 c))
    (hpc : 1 - Real.exp (-c) < pcSite) :
    ∃ K : ℝ, 0 < K ∧ Tendsto (fun n : ℕ => roadLawM n (m n)
      {w | (largestCluster (boardGraph n) (completedM n (m n) w) : ℝ) ≤
        K * Real.log ((n : ℝ) + 1)}) atTop (𝓝 1) := by
  have hsand := occupancy_sandwich m c hc hm
  let ρ := 1 - Real.exp (-c)
  have hρ : 0 < ρ := by
    have he : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [ρ]
    linarith
  let u : Parameter := ⟨(ρ + pcSite) / 2, by constructor <;> linarith [pcSite_le_one]⟩
  let l : Parameter := ⟨0, by norm_num⟩
  have hρu : ρ < u.val := by change ρ < (ρ + pcSite) / 2; linarith
  have hu0 : 0 < u.val := hρ.trans hρu
  have hupc : u.val < pcSite := by change (ρ + pcSite) / 2 < pcSite; linarith
  obtain ⟨err, herr, hs⟩ := hsand l u hρ hρu
  obtain ⟨K, hK, hiid⟩ := road_iid_subcritical_logarithmic tail u hu0 hupc
  have hiidbad : Tendsto (fun n : ℕ => siteMeasure (A := Board n) u
      {ω | K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)})
      atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hiid
      (Or.inl (by norm_num))
    have heq (n : ℕ) : siteMeasure (A := Board n) u
        {ω | K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)} =
        1 - siteMeasure (A := Board n) u
        {ω | (largestCluster (boardGraph n) ω : ℝ) ≤ K * Real.log ((n : ℝ) + 1)} := by
      rw [← measure_univ (μ := siteMeasure (A := Board n) u), ← measure_compl
        (Set.toFinite _).measurableSet (measure_ne_top _ _)]
      congr 1
      ext ω
      simp
    simpa only [heq, tsub_self] using hh
  have hbound (n : ℕ) : roadLawM n (m n)
      {w | K * Real.log ((n : ℝ) + 1) <
        (largestCluster (boardGraph n) (completedM n (m n) w) : ℝ)} ≤
      siteMeasure (A := Board n) u
      {ω | K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)} + err n := by
    have hinc : increasingEvent {ω : Configuration (Board n) |
        K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ)} := by
      intro ω η hωη hω
      change K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) ω : ℝ) at hω
      change K * Real.log ((n : ℝ) + 1) < (largestCluster (boardGraph n) η : ℝ)
      have hcard : (largestCluster (boardGraph n) ω : ℝ) ≤
          (largestCluster (boardGraph n) η : ℝ) := by
        exact_mod_cast largestCluster_mono (boardGraph n) hωη
      exact lt_of_lt_of_le hω hcard
    exact (hs n _ hinc).2
  have hbad : Tendsto (fun n : ℕ => roadLawM n (m n)
      {w | K * Real.log ((n : ℝ) + 1) <
        (largestCluster (boardGraph n) (completedM n (m n) w) : ℝ)}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      (by simpa only [zero_add] using hiidbad.add herr)
      (Eventually.of_forall (fun _ => bot_le)) (Eventually.of_forall hbound)
  refine ⟨K, hK, ?_⟩
  have hgood := road_probability_complement_limit (fun n => roadLawM n (m n))
    (fun n => {w | K * Real.log ((n : ℝ) + 1) <
      (largestCluster (boardGraph n) (completedM n (m n) w) : ℝ)})
    (fun _ => (Set.toFinite _).measurableSet) hbad
  simpa only [Set.compl_ofPred, not_lt] using hgood

/-- Exact rational rounding of the logarithmic lower threshold. -/
theorem road_log_lower_numeric :
    (81193 / 100000 : ℝ) < -Real.log (111 / 250 : ℝ) := by
  have he : Real.exp (81193 / 100000 : ℝ) < (250 / 111 : ℝ) := by
    have hs := Real.exp_bound'
      (show (0 : ℝ) ≤ 81193 / 100000 by norm_num)
      (show (81193 / 100000 : ℝ) ≤ 1 by norm_num)
      (show (0 : ℕ) < 10 by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hs
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos (81193 / 100000 : ℝ)) he
  rw [Real.log_exp, show (250 / 111 : ℝ) = (111 / 250 : ℝ)⁻¹ by norm_num,
    Real.log_inv] at hlog
  exact hlog

/-- Corollary 1.3(c)'s strict lower bound from the fifth classical site input. -/
theorem road_criticalCompletionTime_lower (lower : VanDenBergErmakov1996LowerBound)
    (hsite : pcSite ≤ (79 / 125 : ℝ)) :
    (81193 / 100000 : ℝ) < -Real.log (1 - pcSite) := by
  have hpc1 : pcSite < 1 := lt_of_le_of_lt hsite (by norm_num)
  have harg : 1 - pcSite < (111 / 250 : ℝ) := by
    change (139 / 250 : ℝ) < pcSite at lower
    linarith
  have hlog := Real.log_lt_log (sub_pos.mpr hpc1) harg
  linarith [road_log_lower_numeric]

/-- The upper critical-time part of Corollary 1.3(c), without an external lower bound. -/
theorem road_criticalCompletionTime_upper (hsite : pcSite ≤ (79 / 125 : ℝ)) :
    -Real.log (1 - pcSite) ≤ -Real.log (46 / 125 : ℝ) ∧
    -Real.log (46 / 125 : ℝ) < (99968 / 100000 : ℝ) := by
  constructor
  · have harg : (46 / 125 : ℝ) ≤ 1 - pcSite := by linarith
    have hlog := Real.log_le_log (show (0 : ℝ) < 46 / 125 by norm_num) harg
    linarith
  · have he : (125 / 46 : ℝ) < Real.exp (99968 / 100000 : ℝ) := by
      have hs := Real.sum_le_exp_of_nonneg
        (show (0 : ℝ) ≤ 99968 / 100000 by norm_num) 9
      norm_num [Finset.sum_range_succ, Nat.factorial] at hs
      linarith
    have hlog := Real.log_lt_log (show (0 : ℝ) < 125 / 46 by norm_num) he
    rw [Real.log_exp, show (125 / 46 : ℝ) = (46 / 125 : ℝ)⁻¹ by norm_num,
      Real.log_inv] at hlog
    exact hlog

/-- Corollary 1.3(a,b): both time ranges and the exact original one-draw-per-cell model. -/
theorem road_corollary13ab (density : SupercriticalGiantDensity)
    (continuous : ThetaContinuousAbovePc) (hsite : pcSite ≤ (79 / 125 : ℝ)) :
    (∀ (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c),
      Tendsto (fun n => (m n : ℝ) / ((n : ℝ) + 1) ^ 2) atTop (𝓝 c) →
      -Real.log (1 - (666894 / 1000000 : ℝ)) < c →
      ConvergesInProbability (fun n => roadLawM n (m n))
        (fun n => roadDensityM n (m n)) (thetaReal (completionParameter c hc.le)) ∧
        0 < thetaReal (completionParameter c hc.le)) ∧
    (∀ (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c),
      Tendsto (fun n => (m n : ℝ) / ((n : ℝ) + 1) ^ 2) atTop (𝓝 c) →
      -Real.log (46 / 125 : ℝ) < c →
      ConvergesInProbability (fun n => roadLawM n (m n))
        (fun n => roadDensityM n (m n)) (thetaReal (completionParameter c hc.le)) ∧
        0 < thetaReal (completionParameter c hc.le)) ∧
    ConvergesInProbability roadLaw roadDensity (thetaReal roadParameter) ∧
      0 < thetaReal roadParameter := by
  refine ⟨?_, ?_, ?_⟩
  · intro m c hc hm ht
    have hρ : (666894 / 1000000 : ℝ) < 1 - Real.exp (-c) :=
      (road_rho_gt_iff _ c (by norm_num)).2 ht
    have hpc : pcSite < 1 - Real.exp (-c) :=
      lt_of_le_of_lt (hsite.trans (by norm_num)) hρ
    exact road_theorem12a density continuous m c hc hm hpc
  · intro m c hc hm ht
    have ht' : -Real.log (1 - (79 / 125 : ℝ)) < c := by
      simpa only [show (1 : ℝ) - 79 / 125 = 46 / 125 by norm_num] using ht
    have hρ : (79 / 125 : ℝ) < 1 - Real.exp (-c) :=
      (road_rho_gt_iff _ c (by norm_num)).2 ht'
    exact road_theorem12a density continuous m c hc hm (lt_of_le_of_lt hsite hρ)
  · have hm : Tendsto (fun n : ℕ => (((n + 1)^2 : ℕ) : ℝ) / ((n : ℝ) + 1)^2)
        atTop (𝓝 1) := by
      convert (tendsto_const_nhds (x := (1 : ℝ)) :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
      funext n
      push_cast
      exact div_self (by positivity)
    have hpc : pcSite < 1 - Real.exp (-1) := lt_of_le_of_lt hsite rational_gap
    have h := road_theorem12a density continuous (fun n => (n+1)^2) 1
      (by norm_num) hm hpc
    change ConvergesInProbability roadLaw roadDensity (thetaReal roadParameter) ∧
      0 < thetaReal roadParameter at h
    exact h

#print axioms road_log_lower_numeric
#print axioms road_criticalCompletionTime_lower
#print axioms road_corollary13ab
#print axioms road_criticalCompletionTime_upper
#print axioms road_theorem12a
#print axioms road_theorem12b
#print axioms road_iidDensity_mono
#print axioms road_density_deviation_bound
#print axioms road_probability_complement_limit
#print axioms road_iid_subcritical_logarithmic
#print axioms road_rho_gt_iff
#print axioms road_iid_largest_tail
#print axioms road_siteGraph_adj_iff
#print axioms road_boardEmbedding_injective
#print axioms road_boardEmbedding_adj
#print axioms road_siteMeasure_map_injective
#print axioms road_complement_transfer
#print axioms road_continuous_parameter_sandwich
#print axioms largestCluster_tail_union_bound
#print axioms largestCluster_mono
#print axioms rational_gap
#print axioms logarithmic_union_decay

end SitePerc

open SitePerc in
/-- The full road theorem and its rigorous corollary, with the fifth classical
site-critical lower bound explicit and the final site upper bound retained. -/
theorem SitePercUpper.Lean.RoadMain
    (density : SitePerc.SupercriticalGiantDensity)
    (continuous : SitePerc.ThetaContinuousAbovePc)
    (tail : SitePerc.SubcriticalExponentialVolumeTail)
    (lower : SitePerc.VanDenBergErmakov1996LowerBound)
    (hsite : SitePerc.pcSite ≤ (79 / 125 : ℝ)) :
    (∀ (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c),
      Filter.Tendsto (fun n => (m n : ℝ) / ((n : ℝ) + 1)^2) Filter.atTop (nhds c) →
      (SitePerc.pcSite < 1 - Real.exp (-c) →
        SitePerc.ConvergesInProbability (fun n => SitePerc.roadLawM n (m n))
          (fun n => SitePerc.roadDensityM n (m n))
          (SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
          0 < SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
      (1 - Real.exp (-c) < SitePerc.pcSite →
        ∃ K : ℝ, 0 < K ∧ Filter.Tendsto (fun n : ℕ => SitePerc.roadLawM n (m n)
          {w | (SitePerc.largestCluster (SitePerc.boardGraph n)
            (SitePerc.completedM n (m n) w) : ℝ) ≤ K * Real.log ((n : ℝ)+1)})
          Filter.atTop (nhds 1))) ∧
    (∀ (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c),
      Filter.Tendsto (fun n => (m n : ℝ) / ((n : ℝ)+1)^2) Filter.atTop (nhds c) →
      -Real.log (1 - (666894 / 1000000 : ℝ)) < c →
      SitePerc.ConvergesInProbability (fun n => SitePerc.roadLawM n (m n))
        (fun n => SitePerc.roadDensityM n (m n))
        (SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
        0 < SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
    (∀ (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c),
      Filter.Tendsto (fun n => (m n : ℝ) / ((n : ℝ)+1)^2) Filter.atTop (nhds c) →
      -Real.log (46 / 125 : ℝ) < c →
      SitePerc.ConvergesInProbability (fun n => SitePerc.roadLawM n (m n))
        (fun n => SitePerc.roadDensityM n (m n))
        (SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
        0 < SitePerc.thetaReal (SitePerc.completionParameter c hc.le)) ∧
    (SitePerc.ConvergesInProbability SitePerc.roadLaw SitePerc.roadDensity
      (SitePerc.thetaReal SitePerc.roadParameter) ∧
      0 < SitePerc.thetaReal SitePerc.roadParameter) ∧
    (∀ c : ℝ, SitePerc.pcSite < 1 - Real.exp (-c) ↔
      -Real.log (1 - SitePerc.pcSite) < c) ∧
    ((81193 / 100000 : ℝ) < -Real.log (1 - SitePerc.pcSite) ∧
      -Real.log (1 - SitePerc.pcSite) ≤ (99968 / 100000 : ℝ)) := by
  rcases road_corollary13ab density continuous hsite with ⟨hca, hcb, hc1⟩
  refine ⟨?_, hca, hcb, hc1, ?_, ?_⟩
  · intro m c hc hm
    exact ⟨road_theorem12a density continuous m c hc hm,
      road_theorem12b tail m c hc hm⟩
  · intro c
    exact road_rho_gt_iff pcSite c (lt_of_le_of_lt hsite (by norm_num))
  · exact ⟨road_criticalCompletionTime_lower lower hsite,
      (road_criticalCompletionTime_upper hsite).1.trans
        (road_criticalCompletionTime_upper hsite).2.le⟩

#print axioms SitePercUpper.Lean.RoadMain
