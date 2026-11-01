import SitePerc.Base
import SitePerc.FiniteOrder
import SitePerc.FiniteProbability
import SitePerc.Geometry
import SitePerc.Foundations
import Mathlib.Order.Antisymmetrization
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
Finite-region site substitution. Boundary states retain open/closed information.
Only existence of an infinite cluster is compared; no interior-root comparison is made.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SitePerc

lemma substitution_siteGraph_adj_iff {A : Type} (G : SimpleGraph A)
    (ξ : Configuration A) (u v : A) :
    (siteGraph G ξ).Adj u v ↔ G.Adj u v ∧ ξ u = true ∧ ξ v = true := by
  rw [siteGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
  · rintro ⟨h, hu, hv⟩
    exact ⟨h.ne, Or.inl ⟨h, hu, hv⟩⟩

/-- Finite local connections suffice for global infinite-cluster existence.
The proof uses finite walks and finite fibers, not an unproved infinite-ray lemma. -/
theorem substitution_finite_region_gluing {I C : Type} [Fintype C]
    (G H : SimpleGraph (I × C)) (ξ ω : Configuration (I × C)) (b : C → Prop)
    (cross : ∀ i j : I, i ≠ j → ∀ u v : C, G.Adj (i,u) (j,v) →
      H.Adj (i,u) (j,v) ∧ b u ∧ b v)
    (opened : ∀ i u, b u → ξ (i,u) = true → ω (i,u) = true)
    (localConn : ∀ i u v, b u → b v → ξ (i,u) = true → ξ (i,v) = true →
      (siteGraph (G.comap (fun u => (i,u))) (fun u => ξ (i,u))).Reachable u v →
      (siteGraph H ω).Reachable (i,u) (i,v)) :
    ξ ∈ infiniteExists G → ω ∈ infiniteExists H := by
  classical
  let SG := siteGraph G ξ
  let SH := siteGraph H ω
  have edgeG (x y : I × C) : SG.Adj x y ↔
      G.Adj x y ∧ ξ x = true ∧ ξ y = true :=
    substitution_siteGraph_adj_iff G ξ x y
  have edgeH (x y : I × C) : SH.Adj x y ↔
      H.Adj x y ∧ ω x = true ∧ ω y = true :=
    substitution_siteGraph_adj_iff H ω x y
  have tileEdge (i : I) (u v : C) (h : SG.Adj (i,u) (i,v)) :
      (siteGraph (G.comap (fun u => (i,u))) (fun u => ξ (i,u))).Adj u v := by
    rw [substitution_siteGraph_adj_iff, SimpleGraph.comap_adj]
    have hh := (edgeG _ _).mp h
    exact hh
  -- A source walk starting on the boundary always has a target-connected boundary
  -- anchor in its terminal tile.
  have anchor (i₀ : I) (u₀ : C) (hb₀ : b u₀) (ho₀ : ξ (i₀,u₀) = true)
      (y : I × C) (hr : SG.Reachable (i₀,u₀) y) :
      ∃ c : C, b c ∧ ξ (y.1,c) = true ∧ SH.Reachable (i₀,u₀) (y.1,c) ∧
        (siteGraph (G.comap (fun u => (y.1,u))) (fun u => ξ (y.1,u))).Reachable
          c y.2 := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact ⟨u₀, hb₀, ho₀, .rfl, .rfl⟩
    | @tail y z hr hyz ih =>
      obtain ⟨c, hbc, hoc, hrc, hlocal⟩ := ih
      obtain ⟨iy, uy⟩ := y
      obtain ⟨iz, uz⟩ := z
      have hed := (edgeG _ _).mp hyz
      by_cases hij : iy = iz
      · subst iz
        exact ⟨c, hbc, hoc, hrc, hlocal.trans (tileEdge iy uy uz hyz).reachable⟩
      · obtain ⟨hh, hby, hbz⟩ := cross iy iz hij uy uz hed.1
        have hy : SH.Reachable (i₀,u₀) (iy,uy) :=
          hrc.trans (localConn iy c uy hbc hby hoc hed.2.1 hlocal)
        have hz : SH.Reachable (i₀,u₀) (iz,uz) := hy.trans
          ((edgeH _ _).mpr ⟨hh, opened iy uy hby hed.2.1,
            opened iz uz hbz hed.2.2⟩).reachable
        exact ⟨uz, hbz, hed.2.2, hz, .rfl⟩
  have boundaryInfinite (i₀ : I) (u₀ : C) (hb₀ : b u₀)
      (ho₀ : ξ (i₀,u₀) = true) (hInf : (openCluster G ξ (i₀,u₀)).Infinite) :
      (openCluster H ω (i₀,u₀)).Infinite := by
    by_contra hfin
    have hf : (openCluster H ω (i₀,u₀)).Finite := Set.not_infinite.mp hfin
    have htiles := hf.image Prod.fst
    have hall : (openCluster G ξ (i₀,u₀)) ⊆
        (Prod.fst '' openCluster H ω (i₀,u₀)) ×ˢ (Set.univ : Set C) := by
      intro y hy
      obtain ⟨c, hbc, hoc, hrc, _⟩ := anchor i₀ u₀ hb₀ ho₀ y hy.2
      exact ⟨⟨(y.1,c), ⟨opened y.1 c hbc hoc, hrc⟩, rfl⟩, Set.mem_univ _⟩
    exact hInf ((htiles.prod Set.finite_univ).subset hall)
  -- Every infinite source component meets the boundary: otherwise it is confined
  -- to the finite tile of its starting point.
  have boundaryReach (x y : I × C) (hr : SG.Reachable x y) (hne : x.1 ≠ y.1) :
      ∃ z : I × C, b z.2 ∧ ξ z = true ∧ SG.Reachable x z := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact (hne rfl).elim
    | @tail y z hr hyz ih =>
      by_cases hxy : x.1 = y.1
      · have hyz' : y.1 ≠ z.1 := fun h => hne (hxy.trans h)
        have hed := (edgeG _ _).mp hyz
        have hb := (cross y.1 z.1 hyz' y.2 z.2 hed.1).2.2
        exact ⟨z, hb, hed.2.2,
          (SimpleGraph.reachable_iff_reflTransGen _ _).mpr (hr.tail hyz)⟩
      · exact ih hxy
  rintro ⟨x, hxopen, hxinf⟩
  have htile : ({x.1} ×ˢ (Set.univ : Set C)).Finite :=
    (Set.finite_singleton _).prod Set.finite_univ
  have houtside : ∃ y ∈ openCluster G ξ x, x.1 ≠ y.1 := by
    by_contra h
    push_neg at h
    apply hxinf
    exact htile.subset (fun y hy => ⟨by simpa using (h y hy).symm, Set.mem_univ _⟩)
  obtain ⟨y, hy, hxy⟩ := houtside
  obtain ⟨z, hbz, hoz, hreach⟩ := boundaryReach x y hy.2 hxy
  have hzeq : openCluster G ξ z = openCluster G ξ x := by
    ext w
    exact ⟨fun hw => ⟨hw.1, hreach.trans hw.2⟩,
      fun hw => ⟨hw.1, hreach.symm.trans hw.2⟩⟩
  refine ⟨z, opened z.1 z.2 hbz hoz, ?_⟩
  apply boundaryInfinite z.1 z.2 hbz hoz
  simpa [hzeq] using hxinf

#print axioms substitution_finite_region_gluing

/-- Explicit conditional recovery for a discrete image law, including zero-mass fibers. -/
theorem substitution_pmf_conditional_recovery {A S : Type} (ν : PMF A) (f : A → S) :
    ∃ κ : S → PMF A, (ν.map f).bind κ = ν ∧
      ∀ s ∈ (ν.map f).support, ∀ a ∈ (κ s).support, f a = s := by
  classical
  let κ : S → PMF A := fun s => if hs : s ∈ (ν.map f).support then
    ν.filter {a | f a = s} (by
      obtain ⟨a, ha, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      exact ⟨a, heq, ha⟩)
    else ν
  have hden (s : S) :
      (∑' a, ({a | f a = s} : Set A).indicator ν a) = (ν.map f) s := by
    simp only [PMF.map_apply, Set.indicator_apply, Set.mem_setOf_eq, eq_comm]
  refine ⟨κ, ?_, ?_⟩
  · apply PMF.ext
    intro a
    rw [PMF.bind_apply]
    rw [tsum_eq_single (f a)]
    · by_cases hs : f a ∈ (ν.map f).support
      · have hk : κ (f a) a = ν a * ((ν.map f) (f a))⁻¹ := by
          simp only [κ, dif_pos hs, PMF.filter_apply]
          rw [hden]
          simp
        rw [hk]
        calc
          (ν.map f) (f a) * (ν a * ((ν.map f) (f a))⁻¹) =
              ν a * ((ν.map f) (f a) * ((ν.map f) (f a))⁻¹) := by ac_rfl
          _ = ν a := by
            rw [ENNReal.mul_inv_cancel hs ((ν.map f).apply_ne_top _), mul_one]
      · have hm : (ν.map f) (f a) = 0 := not_ne_iff.mp hs
        have ha : ν a = 0 := by
          by_contra h
          exact hs ((PMF.mem_support_map_iff _ _ _).mpr ⟨a, h, rfl⟩)
        simp [hm, ha]
    · intro s hsa
      by_cases hs : s ∈ (ν.map f).support
      · have hk : κ s a = 0 := by
          simp only [κ, dif_pos hs]
          apply PMF.filter_apply_eq_zero_of_notMem
          exact fun h => hsa h.symm
        simp [hk]
      · have hm : (ν.map f) s = 0 := not_ne_iff.mp hs
        simp [hm]
  · intro s hs a ha
    simp only [κ, dif_pos hs] at ha
    exact (PMF.mem_support_filter_iff _).mp ha |>.1

#print axioms substitution_pmf_conditional_recovery

/-- Restore full configurations from a monotone state coupling. -/
theorem substitution_pmf_coupling_recovery {A B S : Type}
    (ν : PMF A) (μ : PMF B) (f : A → S) (g : B → S) (R : S → S → Prop)
    (π : PMF (S × S)) (hfst : π.map Prod.fst = ν.map f)
    (hsnd : π.map Prod.snd = μ.map g) (hrel : ∀ z ∈ π.support, R z.1 z.2) :
    ∃ ρ : PMF (A × B), ρ.map Prod.fst = ν ∧ ρ.map Prod.snd = μ ∧
      ∀ z ∈ ρ.support, R (f z.1) (g z.2) := by
  classical
  obtain ⟨κ, hκ, hκfiber⟩ := substitution_pmf_conditional_recovery ν f
  obtain ⟨η, hη, hηfiber⟩ := substitution_pmf_conditional_recovery μ g
  let ρ : PMF (A × B) := π.bind fun s =>
    (κ s.1).bind fun a => (η s.2).map fun b => (a,b)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · calc
      ρ.map Prod.fst = π.bind (fun s => κ s.1) := by
        simp only [ρ, PMF.map_bind, PMF.map_comp]
        change (π.bind fun s => (κ s.1).bind fun a =>
          (η s.2).map (Function.const B a)) = _
        simp only [PMF.map_const, PMF.bind_pure]
      _ = (π.map Prod.fst).bind κ := (PMF.bind_map _ _ _).symm
      _ = ν := by rw [hfst, hκ]
  · calc
      ρ.map Prod.snd = π.bind (fun s => η s.2) := by
        simp only [ρ, PMF.map_bind, PMF.map_comp]
        change (π.bind fun s => (κ s.1).bind fun _ => (η s.2).map id) = _
        simp only [PMF.map_id, PMF.bind_const]
      _ = (π.map Prod.snd).bind η := (PMF.bind_map _ _ _).symm
      _ = μ := by rw [hsnd, hη]
  · intro z hz
    obtain ⟨s, hs, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨a, ha, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hs₁ : s.1 ∈ (ν.map f).support := by
      rw [← hfst]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨s, hs, rfl⟩
    have hs₂ : s.2 ∈ (μ.map g).support := by
      rw [← hsnd]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨s, hs, rfl⟩
    simpa only [hκfiber s.1 hs₁ a ha, hηfiber s.2 hs₂ b hb] using hrel s hs

#print axioms substitution_pmf_coupling_recovery

/-- Genuine independent infinite regional products preserve both marginals and
simultaneously enforce the regional coupling relations. -/
theorem substitution_independent_regional_product {I A B : Type}
    [Countable I] [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (ν : I → PMF A) (μ : I → PMF B) (ρ : I → PMF (A × B))
    (R : I → A → B → Prop)
    (hfst : ∀ i, (ρ i).map Prod.fst = ν i)
    (hsnd : ∀ i, (ρ i).map Prod.snd = μ i)
    (hrel : ∀ i z, z ∈ (ρ i).support → R i z.1 z.2) :
    (Measure.infinitePi (fun i => (ρ i).toMeasure)).map (fun z i => (z i).1) =
        Measure.infinitePi (fun i => (ν i).toMeasure) ∧
    (Measure.infinitePi (fun i => (ρ i).toMeasure)).map (fun z i => (z i).2) =
        Measure.infinitePi (fun i => (μ i).toMeasure) ∧
    (∀ᵐ z ∂(Measure.infinitePi (fun i => (ρ i).toMeasure)),
      ∀ i, R i (z i).1 (z i).2) := by
  classical
  constructor
  · rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
    congr 1
    funext i
    rw [PMF.toMeasure_map Prod.fst _ measurable_fst, hfst]
  constructor
  · rw [Measure.infinitePi_map_pi _ (fun _ => measurable_snd)]
    congr 1
    funext i
    rw [PMF.toMeasure_map Prod.snd _ measurable_snd, hsnd]
  · rw [ae_all_iff]
    intro i
    have hm : MeasurableSet {z : A × B | R i z.1 z.2} :=
      (Set.to_countable _).measurableSet
    have he : ∀ᵐ z ∂(ρ i).toMeasure, R i z.1 z.2 :=
      (mem_ae_iff_prob_eq_one hm).mpr
        ((PMF.toMeasure_apply_eq_one_iff _ hm).mpr (hrel i))
    have hmap := Measure.infinitePi_map_eval (fun i => (ρ i).toMeasure) i
    rw [← hmap] at he
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable he

#print axioms substitution_independent_regional_product

/-- Reassembling independent Bernoulli tiles gives precisely the original site law. -/
theorem substitution_bernoulli_regional_reassembly {I C V : Type}
    (p : Parameter) (e : (I × C) ≃ V) :
    (Measure.infinitePi (fun _ : I => siteMeasure (A := C) p)).map
        (fun z v => z (e.symm v).1 (e.symm v).2) = siteMeasure (A := V) p := by
  let uncurry : (I → C → Bool) → (I × C → Bool) :=
    (MeasurableEquiv.curry I C Bool).symm
  let reindex : (I × C → Bool) → (V → Bool) :=
    MeasurableEquiv.piCongrLeft (fun _ : V => Bool) e
  have hcomp : (fun (z : I → C → Bool) v => z (e.symm v).1 (e.symm v).2) =
      reindex ∘ uncurry := by
    ext z v
    obtain ⟨a, rfl⟩ := e.surjective v
    simp [reindex, uncurry, Function.comp_def, Function.uncurry,
      MeasurableEquiv.coe_piCongrLeft]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have hcurry : (Measure.infinitePi (fun _ : I => siteMeasure (A := C) p)).map
      uncurry = siteMeasure (A := I × C) p := by
    exact Measure.infinitePi_map_curry_symm (fun _ : I =>
      fun _ : C => bernoulliMeasure true false p)
  rw [hcurry]
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : V => bernoulliMeasure true false p) e

#print axioms substitution_bernoulli_regional_reassembly

/-- Infinitude of open clusters is preserved by a genuine bijective relabeling. -/
theorem substitution_infiniteExists_reindex {A B : Type} (e : A ≃ B)
    (G : SimpleGraph B) (ξ : Configuration B) :
    (ξ ∘ e) ∈ infiniteExists (G.comap e) ↔ ξ ∈ infiniteExists G := by
  let φ : siteGraph (G.comap e) (ξ ∘ e) ≃g siteGraph G ξ :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        simp only [substitution_siteGraph_adj_iff, SimpleGraph.comap_adj,
          Function.comp_apply] }
  have hr (u v : A) : (siteGraph G ξ).Reachable (e u) (e v) ↔
      (siteGraph (G.comap e) (ξ ∘ e)).Reachable u v :=
    SimpleGraph.Iso.reachable_iff (φ := φ)
  have hcluster (u : A) :
      e '' openCluster (G.comap e) (ξ ∘ e) u = openCluster G ξ (e u) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, (hr u w).mpr hw.2⟩
    · intro hv
      obtain ⟨w, rfl⟩ := e.surjective v
      exact ⟨w, ⟨hv.1, (hr u w).mp hv.2⟩, rfl⟩
  constructor
  · rintro ⟨u, hu, hInf⟩
    refine ⟨e u, hu, ?_⟩
    rw [← hcluster]
    exact hInf.image e.injective.injOn
  · rintro ⟨v, hv, hInf⟩
    obtain ⟨u, rfl⟩ := e.surjective v
    refine ⟨u, hv, ?_⟩
    exact Set.Infinite.of_image e (by simpa only [hcluster] using hInf)

#print axioms substitution_infiniteExists_reindex

/-- Deterministic substitution using the actual recorded tile boundary states. -/
theorem substitution_statewise_exists (m : ℕ) (shift : Vertex)
    (G H : SimpleGraph Vertex) (geometry : substitutionGeometry m shift G H)
    (e : (Vertex × Cell m) ≃ Vertex)
    (he : ∀ i u, e (i,u) = embed m shift i u)
    (ξ ω : Vertex → Configuration (Cell m))
    (hstate : ∀ i, stateLE (localState G m shift i (ξ i))
      (localState H m shift i (ω i))) :
    (fun v => ξ (e.symm v).1 (e.symm v).2) ∈ infiniteExists G →
    (fun v => ω (e.symm v).1 (e.symm v).2) ∈ infiniteExists H := by
  classical
  let ξ₀ : Configuration (Vertex × Cell m) := Function.uncurry ξ
  let ω₀ : Configuration (Vertex × Cell m) := Function.uncurry ω
  have hpull (J : SimpleGraph Vertex) (i : Vertex) :
      (J.comap e).comap (fun u : Cell m => (i,u)) = tileGraph J m shift i := by
    ext u v
    simp only [SimpleGraph.comap_adj, tileGraph, he]
  have hcross : ∀ i j : Vertex, i ≠ j → ∀ u v : Cell m,
      (G.comap e).Adj (i,u) (j,v) → (H.comap e).Adj (i,u) (j,v) ∧
      (u.1.val = 0 ∨ u.1.val + 1 = m ∨ u.2.val = 0 ∨ u.2.val + 1 = m) ∧
      (v.1.val = 0 ∨ v.1.val + 1 = m ∨ v.2.val = 0 ∨ v.2.val + 1 = m) := by
    intro i j hij u v h
    have hg : G.Adj (embed m shift i u) (embed m shift j v) := by
      simpa only [SimpleGraph.comap_adj, he] using h
    have hx := geometry i j hij u v
    exact ⟨by simpa only [SimpleGraph.comap_adj, he] using hx.1.mp hg,
      hx.2 (Or.inl hg)⟩
  have hopen : ∀ i u,
      (u.1.val = 0 ∨ u.1.val + 1 = m ∨ u.2.val = 0 ∨ u.2.val + 1 = m) →
      ξ₀ (i,u) = true → ω₀ (i,u) = true := by
    intro i u hu ho
    exact (hstate i).1 ⟨u, hu⟩ ho
  have hlocal : ∀ i u v,
      (u.1.val = 0 ∨ u.1.val + 1 = m ∨ u.2.val = 0 ∨ u.2.val + 1 = m) →
      (v.1.val = 0 ∨ v.1.val + 1 = m ∨ v.2.val = 0 ∨ v.2.val + 1 = m) →
      ξ₀ (i,u) = true → ξ₀ (i,v) = true →
      (siteGraph ((G.comap e).comap (fun u => (i,u))) (fun u => ξ₀ (i,u))).Reachable u v →
      (siteGraph (H.comap e) ω₀).Reachable (i,u) (i,v) := by
    intro i u v hu hv hou hov hr
    have hrG : (siteGraph (tileGraph G m shift i) (ξ i)).Reachable u v := by
      simpa only [hpull, ξ₀, Function.uncurry] using hr
    have hconn : (localState G m shift i (ξ i)).connected ⟨u,hu⟩ ⟨v,hv⟩ = true :=
      decide_eq_true hrG
    have hconnH := (hstate i).2 ⟨u,hu⟩ ⟨v,hv⟩ hou hov hconn
    have hrH : (siteGraph (tileGraph H m shift i) (ω i)).Reachable u v :=
      of_decide_eq_true hconnH
    let ψ : siteGraph ((H.comap e).comap (fun u : Cell m => (i,u))) (ω i) →g
        siteGraph (H.comap e) ω₀ :=
      { toFun := fun u => (i,u)
        map_rel' := by
          intro a c hac
          simpa only [substitution_siteGraph_adj_iff, SimpleGraph.comap_adj,
            ω₀, Function.uncurry] using hac }
    apply SimpleGraph.Reachable.map ψ
    simpa only [hpull] using hrH
  have htransfer := substitution_finite_region_gluing (G.comap e) (H.comap e)
    ξ₀ ω₀ (fun u : Cell m =>
      u.1.val = 0 ∨ u.1.val + 1 = m ∨ u.2.val = 0 ∨ u.2.val + 1 = m)
    hcross hopen hlocal
  have hξ : (fun v => ξ (e.symm v).1 (e.symm v).2) ∘ e = ξ₀ := by
    ext x
    simp [ξ₀, Function.comp_def, Function.uncurry]
  have hω : (fun v => ω (e.symm v).1 (e.symm v).2) ∘ e = ω₀ := by
    ext x
    simp [ω₀, Function.comp_def, Function.uncurry]
  intro h
  apply (substitution_infiniteExists_reindex e H _).mp
  rw [hω]
  apply htransfer
  rw [← hξ]
  exact (substitution_infiniteExists_reindex e G _).mpr h

#print axioms substitution_statewise_exists

/-- Finite real-law Strassen, with an actual PMF coupling as output. -/
theorem substitution_finite_monotone_pmf_coupling {S : Type} [Fintype S] [Preorder S]
    (ν μ : PMF S)
    (h : ∀ U : Finset S, (∀ x y, x ∈ U → x ≤ y → y ∈ U) →
      ∑ s ∈ U, (ν s).toReal ≤ ∑ s ∈ U, (μ s).toReal) :
    ∃ π : PMF (S × S), π.map Prod.fst = ν ∧ π.map Prod.snd = μ ∧
      ∀ z ∈ π.support, z.1 ≤ z.2 := by
  classical
  obtain ⟨w, hn, hr, hc, ho⟩ := finite_strassen
    (FiniteLaw.ofPMF ν) (FiniteLaw.ofPMF μ) h
  have hrow (x : S) : ∑ y, ENNReal.ofReal (w x y) = ν x := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hn x y), hr]
    exact ENNReal.ofReal_toReal (ν.apply_ne_top x)
  have hcol (y : S) : ∑ x, ENNReal.ofReal (w x y) = μ y := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hn x y), hc]
    exact ENNReal.ofReal_toReal (μ.apply_ne_top y)
  let π : PMF (S × S) := PMF.ofFintype (fun z => ENNReal.ofReal (w z.1 z.2)) (by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    simpa only [tsum_fintype] using ν.tsum_coe)
  refine ⟨π, ?_, ?_, ?_⟩
  · apply PMF.ext
    intro x
    simp only [π, PMF.map_apply, PMF.ofFintype_apply, tsum_fintype,
      Fintype.sum_prod_type, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simpa using hrow x
  · apply PMF.ext
    intro y
    simp only [π, PMF.map_apply, PMF.ofFintype_apply, tsum_fintype,
      Fintype.sum_prod_type]
    simpa using hcol y
  · intro z hz
    apply ho z.1 z.2
    apply ENNReal.ofReal_pos.mp
    exact pos_iff_ne_zero.mpr hz

#print axioms substitution_finite_monotone_pmf_coupling

/-- Boundary-law domination produces a coupling of complete Bernoulli tile
configurations, with internal configurations actually recovered. -/
theorem substitution_boundary_configuration_coupling (m : ℕ) (shift : Vertex)
    (G H : SimpleGraph Vertex) (q p : Parameter)
    (localDom : boundaryDominates m shift G H q p) (i : Vertex) :
    ∃ ρ : PMF (Configuration (Cell m) × Configuration (Cell m)),
      ρ.map Prod.fst = (siteMeasure (A := Cell m) q).toPMF ∧
      ρ.map Prod.snd = (siteMeasure (A := Cell m) p).toPMF ∧
      ∀ z ∈ ρ.support, stateLE (localState G m shift i z.1)
        (localState H m shift i z.2) := by
  classical
  let S := BoundaryState (Boundary m)
  letI : Fintype S := Fintype.ofEquiv
    ((Boundary m → Bool) × (Boundary m → Boundary m → Bool))
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.opened, x.connected)
      left_inv := by rintro ⟨x,y⟩; rfl
      right_inv := by rintro ⟨x,y⟩; rfl }
  letI : Preorder S :=
    { le := stateLE
      le_refl := fun _ => ⟨fun _ h => h, fun _ _ _ _ h => h⟩
      le_trans := fun s t u hst htu =>
        ⟨fun b hb => htu.1 b (hst.1 b hb),
          fun b c hb hc hbc => htu.2 b c (hst.1 b hb) (hst.1 c hc)
            (hst.2 b c hb hc hbc)⟩ }
  let ν := (siteMeasure (A := Cell m) q).toPMF
  let μ := (siteMeasure (A := Cell m) p).toPMF
  let f : Configuration (Cell m) → S := localState G m shift i
  let g : Configuration (Cell m) → S := localState H m shift i
  have hdom : ∀ U : Finset S, (∀ x y, x ∈ U → x ≤ y → y ∈ U) →
      ∑ s ∈ U, ((ν.map f) s).toReal ≤ ∑ s ∈ U, ((μ.map g) s).toReal := by
    letI : MeasurableSpace S := ⊤
    letI : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
    have hmass (κ : PMF S) (U : Finset S) :
        ∑ s ∈ U, (κ s).toReal = (κ.toMeasure (U : Set S)).toReal := by
      rw [PMF.toMeasure_apply_finset]
      exact (ENNReal.toReal_sum (fun s _ => κ.apply_ne_top s)).symm
    intro U hU
    have hf : (ν.map f).toMeasure (U : Set S) = siteMeasure q (f ⁻¹' (U : Set S)) := by
      rw [PMF.toMeasure_map_apply f ν (U : Set S) (measurable_of_countable f) (by trivial)]
      exact congrArg (fun κ : Measure (Configuration (Cell m)) => κ (f ⁻¹' (U : Set S)))
        (Measure.toPMF_toMeasure (siteMeasure q))
    have hg : (μ.map g).toMeasure (U : Set S) = siteMeasure p (g ⁻¹' (U : Set S)) := by
      rw [PMF.toMeasure_map_apply g μ (U : Set S) (measurable_of_countable g) (by trivial)]
      exact congrArg (fun κ : Measure (Configuration (Cell m)) => κ (g ⁻¹' (U : Set S)))
        (Measure.toPMF_toMeasure (siteMeasure p))
    rw [hmass, hmass, hf, hg]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact localDom i (U : Set S) (fun x y hx hxy => hU x y hx hxy)
  obtain ⟨π, hfst, hsnd, hrel⟩ :=
    substitution_finite_monotone_pmf_coupling (ν.map f) (μ.map g) hdom
  exact substitution_pmf_coupling_recovery ν μ f g stateLE π hfst hsnd hrel

#print axioms substitution_boundary_configuration_coupling

/-- The general site substitution theorem. All coupling, infinite-product,
internal-recovery and graph-gluing ingredients are proved above. -/
theorem substitution_exists (m : ℕ) (hm : 0 < m) (shift : Vertex)
    (G H : SimpleGraph Vertex) (q p : Parameter)
    (geometry : substitutionGeometry m shift G H)
    (localDom : boundaryDominates m shift G H q p) :
    infiniteProbability G q ≤ infiniteProbability H p := by
  classical
  choose ρ hfst hsnd hrel using
    (fun i : Vertex => substitution_boundary_configuration_coupling m shift G H q p localDom i)
  let P := Measure.infinitePi (fun i : Vertex => (ρ i).toMeasure)
  let e : (Vertex × Cell m) ≃ Vertex := Equiv.ofBijective
    (fun t => embed m shift t.1 t.2) (embed_bijective m hm shift)
  let assemble : (Vertex → Configuration (Cell m)) → Configuration Vertex :=
    fun z v => z (e.symm v).1 (e.symm v).2
  let first : (Vertex → Configuration (Cell m) × Configuration (Cell m)) →
      Vertex → Configuration (Cell m) := fun z i => (z i).1
  let second : (Vertex → Configuration (Cell m) × Configuration (Cell m)) →
      Vertex → Configuration (Cell m) := fun z i => (z i).2
  let ξ := assemble ∘ first
  let ω := assemble ∘ second
  have ma : Measurable assemble := by
    apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply (e.symm v).2).comp (measurable_pi_apply (e.symm v).1)
  have mf : Measurable first := measurable_pi_iff.mpr
    (fun i => measurable_fst.comp (measurable_pi_apply i))
  have ms : Measurable second := measurable_pi_iff.mpr
    (fun i => measurable_snd.comp (measurable_pi_apply i))
  have mξ : Measurable ξ := ma.comp mf
  have mω : Measurable ω := ma.comp ms
  have hprod := substitution_independent_regional_product
    (fun _ : Vertex => (siteMeasure (A := Cell m) q).toPMF)
    (fun _ : Vertex => (siteMeasure (A := Cell m) p).toPMF) ρ
    (fun i ξ ω => stateLE (localState G m shift i ξ) (localState H m shift i ω))
    hfst hsnd (fun i z hz => hrel i z hz)
  have hξ : P.map ξ = siteMeasure q := by
    rw [show ξ = assemble ∘ first from rfl, ← Measure.map_map ma mf]
    rw [show P.map first = _ from hprod.1]
    simp only [Measure.toPMF_toMeasure]
    exact substitution_bernoulli_regional_reassembly q e
  have hω : P.map ω = siteMeasure p := by
    rw [show ω = assemble ∘ second from rfl, ← Measure.map_map ma ms]
    rw [show P.map second = _ from hprod.2.1]
    simp only [Measure.toPMF_toMeasure]
    exact substitution_bernoulli_regional_reassembly p e
  have htransfer : ∀ᵐ z ∂P, ξ z ∈ infiniteExists G → ω z ∈ infiniteExists H := by
    filter_upwards [hprod.2.2] with z hz
    exact substitution_statewise_exists m shift G H geometry e (fun _ _ => rfl)
      (first z) (second z) hz
  calc
    infiniteProbability G q = P (ξ ⁻¹' infiniteExists G) := by
      change siteMeasure q (infiniteExists G) = _
      rw [← hξ, Measure.map_apply mξ (infiniteExists_measurable G)]
    _ ≤ P (ω ⁻¹' infiniteExists H) := measure_mono_ae htransfer
    _ = infiniteProbability H p := by
      change _ = siteMeasure p (infiniteExists H)
      rw [← hω, Measure.map_apply mω (infiniteExists_measurable H)]

#print axioms substitution_exists

end SitePerc
