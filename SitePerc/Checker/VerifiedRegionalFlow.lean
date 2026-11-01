import SitePerc.Checker.RegionalFlowSoundness
import SitePerc.Checker.RationalMass
import SitePerc.Checker.LawProbability
import SitePerc.Checker.RegionalOrbitLaw
import SitePerc.Checker.PrunedDefs
import SitePerc.Checker.InjectedFlow

/-!
# Actual regional flow certificates imply actual Bernoulli domination

The finite computation supplies exact coefficient identities and successful
execution of the actual byte checker. Neither is a classical percolation input.
The table identity below is statewise over every full Boolean configuration.
-/

open scoped BigOperators

namespace SitePerc.Checker

/-- The exact statewise meaning of the three actual regional coefficient columns. -/
structure ExactRegionalLaws (m : Nat) (laws : LawData) : Prop where
  columns_size : laws.columns.size = 3
  shape : ∀ mode : Fin 3, CountShape (m*m) laws.columns[mode.val]!
  coefficients : ∀ (mode : Fin 3) (key k : Nat), k ≤ m*m →
    coefficient (m*m) laws.columns[mode.val]! key k =
      ∑ mask ∈ Finset.range (2^(m*m)),
        if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m)
            (regionalPerms m) mask = key ∧ openCount (m*m) mask = k then 1 else 0

/-- Exactly the first six-by-six parameters used by the regional driver. -/
def verifiedStageOneParams : StageParams := ⟨1,5001,10000,0,117,200,2^100⟩

/-- Exactly the second six-by-six parameters used by the regional driver. -/
def verifiedStageTwoParams : StageParams := ⟨2,117,200,0,79,125,2^100⟩

/-- The actual regional Bernoulli boundary-state law, not a supplied mass table. -/
noncomputable def regionalStateLaw (m : Nat) (hm : RegionalSize m)
    (mode : Fin 3) (p : Parameter) : FiniteLaw (BoundaryState (Fin (squareBoundary m).size)) :=
  finiteStateLaw p (regionalState m hm mode)

/-- The actual law on the genuine group-orbit quotient. -/
noncomputable def regionalOrbitLaw (m : Nat) (hm : RegionalSize m)
    (mode : Fin 3) (p : Parameter) : FiniteLaw (RegionalOrbit m hm) :=
  finiteLawMap (regionalStateLaw m hm mode p) (regionalOrbitProjection m hm)

/-- Interpret each actual parsed node as its actual boundary-state orbit. -/
def parsedRegionalOrbit (m : Nat) (hm : RegionalSize m) (nodes : ByteArray)
    (i : Fin (natLE nodes 16 8)) : RegionalOrbit m hm :=
  regionalOrbitProjection m hm (decodeState (squareBoundary m).size
    (regionalNodeAt nodes i.val).key)

/-- Exactly the integer node/arc data read by the actual regional checker. -/
def parsedRegionalFlowData (p : StageParams) (nodes edges : ByteArray)
    (hM : 0 < natLE nodes 16 8) : IntegerFlowData (Fin (natLE nodes 16 8)) where
  scale := p.scale
  bottom := ⟨0,hM⟩
  supply := parsedRegionalSupply nodes
  capacity i := (regionalNodeAt nodes i.val).capacity
  absorbed := parsedRegionalAbsorbed nodes
  edge := sparseEdge (parsedRegionalArcs edges)

/-- A finite pushforward of the actual Bernoulli state law is the actual composite law. -/
theorem finiteStateLaw_map_comp {A S Q : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
    (p : Parameter) (X : Configuration A → S) (f : S → Q) (q : Q) :
    (finiteLawMap (finiteStateLaw p X) f).mass q =
      (finiteStateLaw p (fun ω => f (X ω))).mass q := by
  classical
  rw [finiteStateLaw_mass]
  change (∑ s, if f s = q then (finiteStateLaw p X).mass s else 0) = _
  calc
    _ = ∑ s, ∑ ω : Configuration A,
        if f s = q ∧ X ω = s then configWeight p ω else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : f s = q <;> simp [h, finiteStateLaw_mass]
    _ = ∑ ω : Configuration A, ∑ s,
        if f s = q ∧ X ω = s then configWeight p ω else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.sum_eq_single (X ω)]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp

/-- Exact statewise coefficients give the actual Bernoulli mass of one genuine fiber. -/
theorem C7_exact_fiber_mass {S : Type} [Fintype S] [DecidableEq S]
    (n : Nat) (es : List Edge) (boundary : Array Nat) (ps : Array (Array Nat))
    (expected : CountMap) (p : Parameter) (key : Nat)
    (X : Configuration (Fin n) → S) (s : S)
    (fiber : ∀ mask : Nat, configurationKey n es boundary ps mask = key ↔
      X (fun v => mask.testBit v.val) = s)
    (counts : ∀ k ≤ n, coefficient n expected key k =
      ∑ mask ∈ Finset.range (2^n),
        if configurationKey n es boundary ps mask = key ∧ openCount n mask = k then 1 else 0) :
    (finiteStateLaw p X).mass s =
      ∑ k ∈ Finset.range (n+1),
        ((expected.getD key (Array.replicate (n+1) 0))[k]! : ℝ) *
          p.val^k * (1-p.val)^(n-k) := by
  classical
  rw [finiteStateLaw_mass_eq_range]
  symm
  calc
    _ = ∑ k ∈ Finset.range (n+1), ∑ mask ∈ Finset.range (2^n),
        if configurationKey n es boundary ps mask = key ∧ openCount n mask = k then
          p.val^k * (1-p.val)^(n-k) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      change coefficient n expected key k * p.val^k * (1-p.val)^(n-k) = _
      rw [counts k hk']
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mask _
      split <;> simp_all
    _ = ∑ mask ∈ Finset.range (2^n), ∑ k ∈ Finset.range (n+1),
        if configurationKey n es boundary ps mask = key ∧ openCount n mask = k then
          p.val^k * (1-p.val)^(n-k) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mask _
      simp only [fiber mask]
      have hk : openCount n mask ∈ Finset.range (n+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (openCount_le n mask))
      by_cases hs : X (fun v => mask.testBit v.val) = s
      · simp only [hs, true_and, ↓reduceIte]
        rw [Finset.sum_eq_single (openCount n mask)]
        · simp
        · intro k _ hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot hk).elim
      · simp [hs]

/-- Exact H canonical fibers discharge the extraction premise for the actual native key. -/
theorem regional_configurationKey_fiber (m : Nat) (hm : RegionalSize m) (mode : Fin 3)
    (key : Nat) (hv : validCanonical (squareBoundary m).size (regionalPerms m) key = true)
    (mask : Nat) :
    configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m) (regionalPerms m) mask = key ↔
      regionalOrbitProjection m hm (regionalState m hm mode (fun v => mask.testBit v.val)) =
        regionalOrbitProjection m hm (decodeState (squareBoundary m).size key) := by
  have hn : m*m < 64 := by rcases hm with rfl | rfl | rfl <;> norm_num
  have hb : ∀ x ∈ (squareBoundary m).toList, x < m*m := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < (squareBoundary m).size := by simpa using hi
    simpa only [getElem!_pos (squareBoundary m) i hi', Array.getElem_toList] using
      (regionalBoundaryData m hm).2.2.1 ⟨i,hi'⟩
  rw [configurationKey_semantics (m*m) hn (gridEdges m mode.val) (squareBoundary m) hb
    (regionalPerms m) mask]
  have hf := regional_canonical_fibers m hm
    (rootLabels (m*m) (gridEdges m mode.val) (squareBoundary m) mask)
    (r10Labels (squareBoundary m).size key) (by simp [rootLabels]) (by simp [r10Labels])
  rw [(validCanonical_semantics _ _ key hv).2.2.2.1,
    regional_rootLabels_extraction m hm mode mask] at hf
  exact hf

/-- Every valid table key has exactly the mass of its actual H orbit-law fiber. -/
theorem exact_regional_orbit_mass (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (exact : ExactRegionalLaws m laws) (mode : Fin 3) (p : Parameter) (key : Nat)
    (hv : validCanonical (squareBoundary m).size (regionalPerms m) key = true) :
    (regionalOrbitLaw m hm mode p).mass
      (regionalOrbitProjection m hm (decodeState (squareBoundary m).size key)) =
      ∑ k ∈ Finset.range (m*m+1),
        ((laws.columns[mode.val]!.getD key (Array.replicate (m*m+1) 0))[k]! : ℝ) *
          p.val^k * (1-p.val)^(m*m-k) := by
  rw [regionalOrbitLaw, regionalStateLaw, finiteStateLaw_map_comp]
  exact C7_exact_fiber_mass (m*m) (gridEdges m mode.val) (squareBoundary m)
    (regionalPerms m) laws.columns[mode.val]! p key
    (fun ω => regionalOrbitProjection m hm (regionalState m hm mode ω)) _
    (regional_configurationKey_fiber m hm mode key hv) (exact.coefficients mode key)

/-- The full-mask coefficient identity puts every actual source configuration in support. -/
theorem exact_regional_key_supported (m : Nat) (laws : LawData)
    (exact : ExactRegionalLaws m laws) (mode : Fin 3) (mask : Fin (2^(m*m))) :
    laws.columns[mode.val]!.contains
      (configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m) (regionalPerms m) mask.val) = true := by
  let key := configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m)
    (regionalPerms m) mask.val
  let k := openCount (m*m) mask.val
  have hk : k ≤ m*m := openCount_le _ _
  have hc := exact.coefficients mode key k hk
  have hpos : 0 < coefficient (m*m) laws.columns[mode.val]! key k := by
    rw [hc]
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (2^(m*m))) =>
      Nat.zero_le (if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m)
        (regionalPerms m) i = key ∧ openCount (m*m) i = k then 1 else 0))
      (Finset.mem_range.mpr mask.isLt)
    have : 1 ≤ ∑ i ∈ Finset.range (2^(m*m)),
        if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m)
          (regionalPerms m) i = key ∧ openCount (m*m) i = k then 1 else 0 := by
      simpa only [key,k,ite_true,and_self] using hle
    omega
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  cases he : (laws.columns[mode.val]!)[key]? with
  | none =>
    have hz : coefficient (m*m) laws.columns[mode.val]! key k = 0 := by
      simp only [coefficient,Std.HashMap.getD_eq_getD_getElem?,he,Option.getD_none]
      exact zeroCounts_get _ _ hk
    omega
  | some cs => rfl

/-- Parsed-array indexing is exactly the byte-record key at the same finite index. -/
theorem parsedRegionalKeys_get (nodes : ByteArray) (i : Fin (natLE nodes 16 8)) :
    (parsedRegionalKeys nodes)[i.val]! = (regionalNodeAt nodes i.val).key := by
  rw [getElem!_pos (parsedRegionalKeys nodes) i.val (by simp [parsedRegionalKeys,parsedRegionalNodes])]
  simp [parsedRegionalKeys,parsedRegionalNodes]

/-- The actual all-closed key represents a least orbit for the actual state order. -/
theorem regional_zero_orbit_le (m : Nat) (hm : RegionalSize m) (q : RegionalOrbit m hm) :
    regionalOrbitProjection m hm (decodeState (squareBoundary m).size 0) ≤ q := by
  have hu (b : Nat) : unpack b 0 = List.replicate b 0 := by
    induction b with
    | zero => rfl
    | succ b ih => simp [unpack,ih,List.replicate_succ]
  induction q using Quotient.inductionOn with
  | _ s =>
    apply (regionalOrbit_le_iff m hm _ s).mpr
    refine ⟨1, ?_⟩
    constructor
    · intro i hi
      have hz : (decodeState (squareBoundary m).size 0).opened i = false := by
        simp [decodeState,stateOfLabels,labelState,r10Labels,hu]
      rw [hz] at hi
      contradiction
    · intro i j hi _ _
      have hz : (decodeState (squareBoundary m).size 0).opened i = false := by
        simp [decodeState,stateOfLabels,labelState,r10Labels,hu]
      rw [hz] at hi
      contradiction

/-- The exact selected boundary permutation in a true keyLE guard proves orbit order. -/
theorem regional_keyLE_orbit_le (m : Nat) (hm : RegionalSize m) (src dst : Nat)
    (k : Fin (regionalPerms m).size)
    (h : keyLE (squareBoundary m).size src
      (moveKey (squareBoundary m).size (regionalPerms m)[k.val]! dst) = true) :
    regionalOrbitProjection m hm (decodeState (squareBoundary m).size src) ≤
      regionalOrbitProjection m hm (decodeState (squareBoundary m).size dst) := by
  let t : Fin (regionalVertexPerms m).size :=
    ⟨k.val, by rw [← (regionalPermutationData m hm).1]; exact k.isLt⟩
  let g : regionalActionGroup m hm :=
    ⟨(regionalVertexEquiv m hm t, regionalBoundaryIndexEquiv m hm t),
      Subgroup.subset_closure ⟨t,rfl⟩⟩
  have hb : (squareBoundary m).size ≤ 31 := by
    have hh := (regionalBoundaryData m hm).1
    rcases hm with rfl | rfl | rfl <;> omega
  apply (regionalOrbit_le_iff m hm _ _).mpr
  refine ⟨g⁻¹, ?_⟩
  exact moveKey_order_sound (squareBoundary m).size (regionalPerms m)[k.val]! src dst
    (regionalBoundaryIndexEquiv m hm t) (regionalBoundaryIndexEquiv_represents m hm t) hb h

/-- Actual C1-valid nodes name distinct genuine orbits, not merely distinct bytes. -/
theorem parsedRegionalOrbit_injective (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (p : StageParams) (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    Function.Injective (parsedRegionalOrbit m hm nodes) := by
  intro i j hij
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt checked
  have hi := (checkRegionalFlow_node_fields m laws p nodes edges receipt checked i).1
  have hj := (checkRegionalFlow_node_fields m laws p nodes edges receipt checked j).1
  have hk := regional_valid_key_orbit_injective m hm _ _ hi hj hij
  rw [← parsedRegionalKeys_get nodes i, ← parsedRegionalKeys_get nodes j] at hk
  apply Fin.ext
  apply (facts.keys_unique.getElem_inj_iff
    (hi := by simpa [facts.keys_size] using i.isLt)
    (hj := by simpa [facts.keys_size] using j.isLt)).mp
  simpa only [Array.getElem_toList,
    getElem!_pos (parsedRegionalKeys nodes) i.val (by simpa [facts.keys_size] using i.isLt),
    getElem!_pos (parsedRegionalKeys nodes) j.val (by simpa [facts.keys_size] using j.isLt)] using hk

/-- The actual checked bottom node is least in the full genuine orbit space. -/
theorem parsedRegionalOrbit_bottom_le (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (p : StageParams) (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (q : RegionalOrbit m hm) :
    parsedRegionalOrbit m hm nodes
      ⟨0,(checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1⟩ ≤ q := by
  have hz := (checkRegionalFlow_ok m laws p nodes edges receipt checked).bottom_index_zero
  rw [parsedRegionalKeys_get nodes
    ⟨0,(checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1⟩] at hz
  change regionalOrbitProjection m hm (decodeState _ (regionalNodeAt nodes 0).key) ≤ q
  rw [hz]
  exact regional_zero_orbit_le m hm q

/-- Every aggregate sparse edge is nonnegative, including repeated occurrences. -/
theorem parsedRegionalOrbit_edge_nonnegative (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (i j : Fin (natLE nodes 16 8)) : 0 ≤ sparseEdge (parsedRegionalArcs edges) i j := by
  have ha := (checkRegionalFlow_sparse_arcs m laws p nodes edges receipt checked).2
  unfold sparseEdge
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a,ha',rfl⟩ := List.mem_map.mp hx
  split
  · exact le_of_lt (ha a ha').1
  · exact le_rfl

/-- Positivity of an aggregate parsed edge implies actual orbit order. -/
theorem parsedRegionalOrbit_edge_increasing (m : Nat) (hm : RegionalSize m)
    (laws : LawData) (p : StageParams) (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (i j : Fin (natLE nodes 16 8))
    (hpos : 0 < sparseEdge (parsedRegionalArcs edges) i j) :
    parsedRegionalOrbit m hm nodes i ≤ parsedRegionalOrbit m hm nodes j := by
  have ha := (checkRegionalFlow_sparse_arcs m laws p nodes edges receipt checked).2
  by_contra hn
  have hz : sparseEdge (parsedRegionalArcs edges) i j = 0 := by
    unfold sparseEdge
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a,ha',rfl⟩ := List.mem_map.mp hx
    split
    · next heq =>
      obtain ⟨k,hk⟩ := (ha a ha').2
      rw [heq.1,heq.2,parsedRegionalKeys_get nodes i,parsedRegionalKeys_get nodes j] at hk
      exact False.elim (hn (regional_keyLE_orbit_le m hm _ _ k hk))
    · rfl
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos

/-- Exact coefficients plus checked C6 cover every actual source configuration orbit. -/
theorem checkRegionalFlow_actual_source_support (m : Nat) (hm : RegionalSize m)
    (laws : LawData) (exact : ExactRegionalLaws m laws) (p : StageParams)
    (refmode : Fin 3) (href : p.refcol = refmode.val)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (ω : Configuration (Fin (m*m))) :
    ∃ i : Fin (natLE nodes 16 8), regionalOrbitProjection m hm (regionalState m hm refmode ω) =
      parsedRegionalOrbit m hm nodes i := by
  classical
  obtain ⟨mask,hmask⟩ := (maskEquivConfiguration (m*m)).surjective ω
  let key := configurationKey (m*m) (gridEdges m refmode.val) (squareBoundary m)
    (regionalPerms m) mask.val
  have hs := exact_regional_key_supported m laws exact refmode mask
  change laws.columns[refmode.val]!.contains key = true at hs
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hs
  cases hcs : (laws.columns[refmode.val]!)[key]? with
  | none => simp [hcs] at hs
  | some cs =>
    have hmem : (key,cs) ∈ laws.columns[p.refcol]!.toList := by
      rw [href]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hcs
    obtain ⟨i,hi⟩ := checkRegionalFlow_source_complete m laws p nodes edges receipt checked (key,cs) hmem
    refine ⟨i, ?_⟩
    have hv := (checkRegionalFlow_node_fields m laws p nodes edges receipt checked i).1
    have hf := (regional_configurationKey_fiber m hm refmode _ hv mask.val).mp hi.symm
    change regionalOrbitProjection m hm (regionalState m hm refmode ω) = _
    rw [← hmask]
    exact hf

/-- Every orbit omitted from the parsed node list has zero actual source mass. -/
theorem checkRegionalFlow_missing_source_zero (m : Nat) (hm : RegionalSize m)
    (laws : LawData) (exact : ExactRegionalLaws m laws) (p : StageParams)
    (refmode : Fin 3) (href : p.refcol = refmode.val)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (q : Parameter) (s : RegionalOrbit m hm)
    (hs : s ∉ Set.range (parsedRegionalOrbit m hm nodes)) :
    (regionalOrbitLaw m hm refmode q).mass s = 0 := by
  classical
  rw [regionalOrbitLaw,regionalStateLaw,finiteStateLaw_map_comp,finiteStateLaw_mass]
  apply Finset.sum_eq_zero
  intro ω _
  have hne : regionalOrbitProjection m hm (regionalState m hm refmode ω) ≠ s := by
    intro heq
    obtain ⟨i,hi⟩ := checkRegionalFlow_actual_source_support m hm laws exact p refmode href
      nodes edges receipt checked ω
    exact hs ⟨i,hi.symm.trans heq⟩
  simp [hne]

/-- Exact rational checker arithmetic equals the actual orbit-fiber mass. -/
theorem exact_regional_rational_mass (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (exact : ExactRegionalLaws m laws) (mode : Fin 3) (p : Parameter)
    (a d : Nat) (hd : 0 < d) (ha : a ≤ d) (hp : p.val = (a : ℝ) / d)
    (key : Nat) (hv : validCanonical (squareBoundary m).size (regionalPerms m) key = true) :
    (numerator (laws.columns[mode.val]!.getD key (Array.replicate (m*m+1) 0))
      (weights (m*m) a d) : ℝ) / (d : ℝ)^(m*m) =
      (regionalOrbitLaw m hm mode p).mass
        (regionalOrbitProjection m hm (decodeState (squareBoundary m).size key)) := by
  rw [rational_numerator_eq_sum p (m*m) a d hd ha hp _ (exact.shape mode key)]
  exact (exact_regional_orbit_mass m hm laws exact mode p key hv).symm

/-- Checker success proves all integer-flow conditions in the actual pulled-back orbit order. -/
theorem parsedRegionalFlowData_valid (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (p : StageParams) (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    letI : Preorder (Fin (natLE nodes 16 8)) := Preorder.lift (parsedRegionalOrbit m hm nodes)
    (parsedRegionalFlowData p nodes edges
      (checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1).Valid := by
  letI : Preorder (Fin (natLE nodes 16 8)) := Preorder.lift (parsedRegionalOrbit m hm nodes)
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt checked
  refine ⟨facts.exact_parameters.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact parsedRegionalOrbit_bottom_le m hm laws p nodes edges receipt checked _
  · intro i
    exact Int.natCast_nonneg _
  · intro i
    exact Int.natCast_nonneg _
  · intro i
    have hi := checkRegionalFlow_node_fields m laws p nodes edges receipt checked i
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hi.2.2.2.2.1⟩
  · intro i j
    exact parsedRegionalOrbit_edge_nonnegative m laws p nodes edges receipt checked i j
  · intro i j hij
    exact parsedRegionalOrbit_edge_increasing m hm laws p nodes edges receipt checked i j hij
  · have hkey : (regionalNodeAt nodes 0).key = 0 := by
      simpa only [parsedRegionalKeys_get nodes ⟨0,facts.node_shape.1⟩] using facts.bottom_index_zero
    have hh := (checkRegionalFlow_node_fields m laws p nodes edges receipt checked
      ⟨0,facts.node_shape.1⟩).2.2.2.2.2.1
    change ((regionalNodeAt nodes 0).supply : Int) = 0
    simp only [hkey,beq_self_eq_true,↓reduceIte] at hh
    exact_mod_cast hh
  · exact checkRegionalFlow_conservation m laws p nodes edges receipt checked

/-- Exact source coefficients and the actual upward guard bound every represented non-bottom mass. -/
theorem parsedRegionalFlowData_source_bound (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (exact : ExactRegionalLaws m laws) (p : StageParams) (refmode : Fin 3)
    (href : p.refcol = refmode.val) (q : Parameter) (hq : q.val = (p.qnum : ℝ)/p.qden)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (i : Fin (natLE nodes 16 8))
    (hi : i ≠ (parsedRegionalFlowData p nodes edges
      (checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1).bottom) :
    (p.scale : ℝ) * (regionalOrbitLaw m hm refmode q).mass (parsedRegionalOrbit m hm nodes i) ≤
      ((parsedRegionalFlowData p nodes edges
        (checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1).supply i : ℝ) := by
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt checked
  obtain ⟨hv,_,_,_,_,hsource,_⟩ := checkRegionalFlow_node_fields m laws p nodes edges receipt checked i
  have hkey : (regionalNodeAt nodes i.val).key ≠ 0 := by
    intro hizero
    apply hi
    apply parsedRegionalOrbit_injective m hm laws p nodes edges receipt checked
    have hzero : (regionalNodeAt nodes 0).key = 0 := by
      simpa only [parsedRegionalKeys_get nodes ⟨0,facts.node_shape.1⟩] using facts.bottom_index_zero
    change regionalOrbitProjection m hm (decodeState _ (regionalNodeAt nodes i.val).key) =
      regionalOrbitProjection m hm (decodeState _ (regionalNodeAt nodes 0).key)
    rw [hizero,hzero]
  have hmass := exact_regional_rational_mass m hm laws exact refmode q p.qnum p.qden
    facts.exact_parameters.2.1 facts.exact_parameters.2.2.2.1 hq _ hv
  have hround := nat_upward_rounds_up p.scale
    (numerator (laws.columns[refmode.val]!.getD (regionalNodeAt nodes i.val).key
      (Array.replicate (m*m+1) 0)) (weights (m*m) p.qnum p.qden))
    (p.qden^(m*m)) (pow_pos facts.exact_parameters.2.1 (m*m))
  simp only [Nat.cast_pow] at hround
  rw [hmass] at hround
  change (p.scale : ℝ) * _ ≤ ((regionalNodeAt nodes i.val).supply : ℝ)
  rw [hsource]
  simpa only [href,beq_iff_eq,hkey,↓reduceIte,parsedRegionalOrbit] using hround

/-- Exact target coefficients and the actual floor guard bound every represented capacity. -/
theorem parsedRegionalFlowData_sink_bound (m : Nat) (hm : RegionalSize m) (laws : LawData)
    (exact : ExactRegionalLaws m laws) (p : StageParams) (tarmode : Fin 3)
    (htar : p.tarcol = tarmode.val) (r : Parameter) (hr : r.val = (p.pnum : ℝ)/p.pden)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (i : Fin (natLE nodes 16 8)) :
    ((parsedRegionalFlowData p nodes edges
      (checkRegionalFlow_ok m laws p nodes edges receipt checked).node_shape.1).capacity i : ℝ) ≤
      (p.scale : ℝ) * (regionalOrbitLaw m hm tarmode r).mass (parsedRegionalOrbit m hm nodes i) := by
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt checked
  obtain ⟨hv,_,_,_,_,_,hsink⟩ := checkRegionalFlow_node_fields m laws p nodes edges receipt checked i
  have hmass := exact_regional_rational_mass m hm laws exact tarmode r p.pnum p.pden
    facts.exact_parameters.2.2.1 facts.exact_parameters.2.2.2.2 hr _ hv
  have hround := nat_floor_rounds_down p.scale
    (numerator (laws.columns[tarmode.val]!.getD (regionalNodeAt nodes i.val).key
      (Array.replicate (m*m+1) 0)) (weights (m*m) p.pnum p.pden))
    (p.pden^(m*m)) (pow_pos facts.exact_parameters.2.2.1 (m*m))
  simp only [Nat.cast_pow] at hround
  rw [hmass] at hround
  change ((regionalNodeAt nodes i.val).capacity : ℝ) ≤ _
  rw [hsink]
  simpa only [htar,parsedRegionalOrbit] using hround

/-- Reuse the independently proved injective finite-flow adapter without target coverage. -/
theorem finiteDominates_of_injected_flow {I Q : Type} [Fintype I] [Fintype Q] [Preorder Q]
    (d : IntegerFlowData I) (f : I → Q) (hf : Function.Injective f) (ν μ : FiniteLaw Q)
    (valid : letI : Preorder I := Preorder.lift f; d.Valid)
    (bottom_le : ∀ q : Q, f d.bottom ≤ q)
    (source : ∀ i : I, i ≠ d.bottom → (d.scale : ℝ) * ν.mass (f i) ≤ (d.supply i : ℝ))
    (sink : ∀ i : I, (d.capacity i : ℝ) ≤ (d.scale : ℝ) * μ.mass (f i))
    (outside : ∀ q : Q, q ∉ Set.range f → ν.mass q = 0) : finiteDominates ν μ := by
  exact SitePerc.injected_flow_implies_domination d f hf ν μ valid bottom_le source sink outside

/-- Exact table semantics and actual checker success imply domination of the actual orbit laws. -/
theorem checkRegionalFlow_actual_orbit_domination (m : Nat) (hm : RegionalSize m)
    (laws : LawData) (exact : ExactRegionalLaws m laws) (params : StageParams)
    (refmode tarmode : Fin 3) (href : params.refcol = refmode.val) (htar : params.tarcol = tarmode.val)
    (q p : Parameter) (hq : q.val = (params.qnum : ℝ)/params.qden)
    (hp : p.val = (params.pnum : ℝ)/params.pden)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws params nodes edges = .ok receipt) :
    finiteDominates (regionalOrbitLaw m hm refmode q) (regionalOrbitLaw m hm tarmode p) := by
  have facts := checkRegionalFlow_ok m laws params nodes edges receipt checked
  let d := parsedRegionalFlowData params nodes edges facts.node_shape.1
  exact finiteDominates_of_injected_flow d (parsedRegionalOrbit m hm nodes)
    (parsedRegionalOrbit_injective m hm laws params nodes edges receipt checked)
    (regionalOrbitLaw m hm refmode q) (regionalOrbitLaw m hm tarmode p)
    (parsedRegionalFlowData_valid m hm laws params nodes edges receipt checked)
    (parsedRegionalOrbit_bottom_le m hm laws params nodes edges receipt checked)
    (parsedRegionalFlowData_source_bound m hm laws exact params refmode href q hq
      nodes edges receipt checked)
    (parsedRegionalFlowData_sink_bound m hm laws exact params tarmode htar p hp
      nodes edges receipt checked)
    (checkRegionalFlow_missing_source_zero m hm laws exact params refmode href
      nodes edges receipt checked q)

/-- Actual canonical fibers, invariance and C's orbit lift close the actual stateLE law comparison. -/
theorem checkRegionalFlow_actual_domination (m : Nat) (hm : RegionalSize m)
    (laws : LawData) (exact : ExactRegionalLaws m laws) (params : StageParams)
    (refmode tarmode : Fin 3) (href : params.refcol = refmode.val) (htar : params.tarcol = tarmode.val)
    (q p : Parameter) (hq : q.val = (params.qnum : ℝ)/params.qden)
    (hp : p.val = (params.pnum : ℝ)/params.pden)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow m laws params nodes edges = .ok receipt) :
    letI := regionalBoundaryPreorder (squareBoundary m).size
    finiteDominates (regionalStateLaw m hm refmode q) (regionalStateLaw m hm tarmode p) := by
  letI := regionalBoundaryPreorder (squareBoundary m).size
  apply monotoneCoupling_implies_domination
  exact regional_orbit_domination_lift m hm refmode tarmode q p
    (checkRegionalFlow_actual_orbit_domination m hm laws exact params refmode tarmode href htar
      q p hq hp nodes edges receipt checked)

/-- The fixed first six-by-six stage compares the genuine q0 and p1 regional state laws. -/
theorem verified_stage_one (laws : LawData) (exact : ExactRegionalLaws 6 laws)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow 6 laws verifiedStageOneParams nodes edges = .ok receipt) :
    letI := regionalBoundaryPreorder (squareBoundary 6).size
    finiteDominates (regionalStateLaw 6 (by decide) 1 q0)
      (regionalStateLaw 6 (by decide) 0 p1) := by
  exact checkRegionalFlow_actual_domination 6 (by decide) laws exact verifiedStageOneParams
    1 0 rfl rfl q0 p1 (by norm_num [q0,verifiedStageOneParams])
    (by norm_num [p1,verifiedStageOneParams]) nodes edges receipt checked

/-- The fixed second six-by-six stage compares the genuine p1 and p2 regional state laws. -/
theorem verified_stage_two (laws : LawData) (exact : ExactRegionalLaws 6 laws)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow 6 laws verifiedStageTwoParams nodes edges = .ok receipt) :
    letI := regionalBoundaryPreorder (squareBoundary 6).size
    finiteDominates (regionalStateLaw 6 (by decide) 2 p1)
      (regionalStateLaw 6 (by decide) 0 p2) := by
  exact checkRegionalFlow_actual_domination 6 (by decide) laws exact verifiedStageTwoParams
    2 0 rfl rfl p1 p2 (by norm_num [p1,verifiedStageTwoParams])
    (by norm_num [p2,verifiedStageTwoParams]) nodes edges receipt checked

/-- Exact actual first-stage finite computation implies the Base first boundary domination. -/
theorem verified_boundary_stage_one (laws : LawData) (exact : ExactRegionalLaws 6 laws)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow 6 laws verifiedStageOneParams nodes edges = .ok receipt) :
    boundaryDominates 6 (0,0) lineLattice intermediate q0 p1 := by
  exact regional_boundaryDom_stage1 q0 p1 (verified_stage_one laws exact nodes edges receipt checked)

/-- Exact actual second-stage finite computation implies the shifted Base boundary domination. -/
theorem verified_boundary_stage_two (laws : LawData) (exact : ExactRegionalLaws 6 laws)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (checked : checkRegionalFlow 6 laws verifiedStageTwoParams nodes edges = .ok receipt) :
    boundaryDominates 6 (3,3) intermediate square p1 p2 := by
  exact regional_boundaryDom_stage2 p1 p2 (verified_stage_two laws exact nodes edges receipt checked)

/-- Both Base stage inputs are consequences, not assumptions, of the finite certificates. -/
theorem verified_boundary_stages (laws : LawData) (exact : ExactRegionalLaws 6 laws)
    (nodes1 edges1 nodes2 edges2 : ByteArray) (receipt1 receipt2 : FlowReceipt)
    (checked1 : checkRegionalFlow 6 laws verifiedStageOneParams nodes1 edges1 = .ok receipt1)
    (checked2 : checkRegionalFlow 6 laws verifiedStageTwoParams nodes2 edges2 = .ok receipt2) :
    boundaryDominates 6 (0,0) lineLattice intermediate q0 p1 ∧
      boundaryDominates 6 (3,3) intermediate square p1 p2 := by
  exact ⟨verified_boundary_stage_one laws exact nodes1 edges1 receipt1 checked1,
    verified_boundary_stage_two laws exact nodes2 edges2 receipt2 checked2⟩

end SitePerc.Checker
