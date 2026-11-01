import SitePerc.Checker.RegionalDefs
import SitePerc.Checker.ParallelAll
import SitePerc.Checker.SparseFlow
import Mathlib.Tactic

/-!
# Soundness of actual regional flow parsing

The public interface starts with executable checker success.  Its parsed
finite-data conclusions do not assume a separate list of accepted guards.
Law identity, packed-state semantics, and geometric meaning are separate layers.
-/

open scoped BigOperators

namespace SitePerc.Checker

/-- A successful linear scan yields exact membership as well as uniqueness. -/
theorem regionalKeysScan_sound (keys : List Nat) (seen out : Std.HashMap Nat Unit)
    (h : regionalKeysScan keys seen = some out) :
    keys.Nodup ∧ (∀ key ∈ keys, seen.contains key = false) ∧
    ∀ key, out.contains key = true ↔ seen.contains key = true ∨ key ∈ keys := by
  induction keys generalizing seen out with
  | nil =>
    simp only [regionalKeysScan, Option.some.injEq] at h
    subst out
    simp
  | cons key keys ih =>
    by_cases hk : seen.contains key = true
    · simp [regionalKeysScan, hk] at h
    · have hfalse : seen.contains key = false := by simpa using hk
      simp only [regionalKeysScan, hk, ite_false] at h
      obtain ⟨hnodup, hdisjoint, hmember⟩ := ih (seen.insert key ()) out h
      have hnot : key ∉ keys := by
        intro hmem
        have heq := hdisjoint key hmem
        simp at heq
      refine ⟨List.nodup_cons.mpr ⟨hnot, hnodup⟩, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with heq | hmem
        · simpa only [heq] using hfalse
        · have heq := hdisjoint x hmem
          simpa only [Std.HashMap.contains_insert, Bool.or_eq_false_iff] using
            (Bool.or_eq_false_iff.mp (by simpa only [Std.HashMap.contains_insert] using heq)).2
      · intro x
        rw [hmember x]
        simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq,
          List.mem_cons]
        tauto

/-- Reflect exactly the executable node validity and mass-formula guards. -/
theorem regionalNodeGuard_sound (n b : Nat) (perms : Array (Array Nat))
    (p : StageParams) (ref tar : CountMap) (row : RegionalNode)
    (h : regionalNodeGuard n b perms p ref tar row = true) :
    validCanonical b perms row.key = true ∧
    row.supply < 2^127 ∧ row.capacity < 2^127 ∧ row.absorbed < 2^127 ∧
    row.absorbed ≤ row.capacity ∧
    row.supply = (if row.key == 0 then 0 else
      (p.scale * numerator (ref.getD row.key (Array.replicate (n+1) 0))
        (weights n p.qnum p.qden) + p.qden^n - 1) / p.qden^n) ∧
    row.capacity = p.scale * numerator
      (tar.getD row.key (Array.replicate (n+1) 0))
      (weights n p.pnum p.pden) / p.pden^n := by
  change (validCanonical b perms row.key &&
    decide (row.supply < 2^127) && decide (row.capacity < 2^127) &&
    decide (row.absorbed < 2^127) && decide (row.absorbed ≤ row.capacity) &&
    (row.supply == if row.key == 0 then 0 else
      (p.scale * numerator (ref.getD row.key (Array.replicate (n+1) 0))
        (weights n p.qnum p.qden) + p.qden^n - 1) / p.qden^n) &&
    (row.capacity == p.scale * numerator
      (tar.getD row.key (Array.replicate (n+1) 0))
      (weights n p.pnum p.pden) / p.pden^n)) = true at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using h

/-- Reflect endpoints, positivity, and the actual packed order guard. -/
theorem regionalArcGuard_sound (M b : Nat) (perms : Array (Array Nat))
    (keys : Array Nat) (arc : RegionalArc)
    (h : regionalArcGuard M b perms keys arc = true) :
    arc.src < M ∧ arc.dst < M ∧ arc.perm < perms.size ∧ arc.reserved = 0 ∧
    0 < arc.flow ∧ arc.flow < 2^127 ∧
    keyLE b keys[arc.src]!
      (moveKey b perms[arc.perm]! keys[arc.dst]!) = true := by
  simpa only [regionalArcGuard, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc] using h

/-- The complete node records read at the exact checked byte offsets. -/
def parsedRegionalNodes (nodes : ByteArray) : Array RegionalNode :=
  Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val

/-- The actual parsed key array, in node index order. -/
def parsedRegionalKeys (nodes : ByteArray) : Array Nat :=
  (parsedRegionalNodes nodes).map RegionalNode.key

/-- All arc records, including their exact permutation-index witnesses. -/
def parsedRegionalRawArcs (edges : ByteArray) : Array RegionalArc :=
  Array.ofFn fun j : Fin (natLE edges 8 8) => regionalArcAt edges j.val

/-- The exact sparse occurrences passed to the executable balance replay. -/
def parsedRegionalArcs (edges : ByteArray) : Array SparseArc :=
  (parsedRegionalRawArcs edges).map RegionalArc.toSparse

/-- Actual node supplies as exact integers. -/
def parsedRegionalSupply (nodes : ByteArray) (i : Fin (natLE nodes 16 8)) : Int :=
  (regionalNodeAt nodes i.val).supply

/-- Actual node absorptions as exact integers. -/
def parsedRegionalAbsorbed (nodes : ByteArray) (i : Fin (natLE nodes 16 8)) : Int :=
  (regionalNodeAt nodes i.val).absorbed

/-- The actual array from which the checker replays the sparse occurrences. -/
def parsedRegionalInitial (nodes : ByteArray) : Array Int :=
  (parsedRegionalNodes nodes).map (fun row => (row.supply : Int) - (row.absorbed : Int))

/-- Explicit successful-checker facts about the actual parsed input.  No
probability-law identity, codec semantics, or geometric theorem is included. -/
structure RegionalFlowFacts (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt) : Prop where
  geometry_checked : geometryChecks m = true
  law_shape : laws.n = m*m ∧ laws.b = (squareBoundary m).size ∧
    laws.graphs = 3 ∧ laws.columns.size = 3
  exact_parameters : 0 < p.scale ∧ 0 < p.qden ∧ 0 < p.pden ∧
    p.qnum ≤ p.qden ∧ p.pnum ≤ p.pden
  column_bounds : p.refcol < laws.columns.size ∧ p.tarcol < laws.columns.size
  node_header : 32 ≤ nodes.size ∧ binaryMagic nodes 0 "R10ANODE" = true ∧
    natLE nodes 8 4 = m*m ∧ natLE nodes 12 4 = (squareBoundary m).size
  node_shape : 0 < natLE nodes 16 8 ∧
    nodes.size = 32+64*(natLE nodes 16 8) ∧
    natLE nodes 24 4 = p.refcol ∧ natLE nodes 28 4 = p.tarcol
  edge_header : 16 ≤ edges.size ∧ binaryMagic edges 0 "R10AEDGE" = true
  edge_shape : edges.size = 16+32*(natLE edges 8 8)
  receipt_fields : receipt.nodes = natLE nodes 16 8 ∧ receipt.edges = natLE edges 8 8 ∧
    receipt.supply = ((parsedRegionalNodes nodes).toList.map RegionalNode.supply).sum ∧
    receipt.absorption = ((parsedRegionalNodes nodes).toList.map RegionalNode.absorbed).sum
  keys_size : (parsedRegionalKeys nodes).size = natLE nodes 16 8
  keys_unique : (parsedRegionalKeys nodes).toList.Nodup
  bottom_index_zero : (parsedRegionalKeys nodes)[0]! = 0
  nodes_checked : ∀ i : Fin (natLE nodes 16 8),
    regionalNodeGuard (m*m) (squareBoundary m).size (regionalPerms m) p
      laws.columns[p.refcol]! laws.columns[p.tarcol]! (regionalNodeAt nodes i.val) = true
  source_complete : ∀ pair ∈ laws.columns[p.refcol]!.toList,
    pair.1 ∈ (parsedRegionalKeys nodes).toList
  arcs_checked : ∀ j : Fin (natLE edges 8 8),
    regionalArcGuard (natLE nodes 16 8) (squareBoundary m).size
      (regionalPerms m) (parsedRegionalKeys nodes) (regionalArcAt edges j.val) = true
  replay_zero : (replayBalance (parsedRegionalInitial nodes)
    (parsedRegionalArcs edges)).all (· == 0) = true

set_option maxHeartbeats 1200000 in
/-- Actual successful execution yields the parsed finite-data contract.  All
byte, node, arc, support, and replay conditions come from the success premise. -/
theorem checkRegionalFlow_ok (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    RegionalFlowFacts m laws p nodes edges receipt := by
  unfold checkRegionalFlow at h
  simp only [reflectedArrayAll_eq_all] at h
  dsimp only [Id.run] at h
  by_cases hgeometry : (!geometryChecks m || laws.n != m*m || laws.b != (squareBoundary m).size || laws.graphs != 3 || laws.columns.size != 3) = true
  · simp only [ite_eq_left hgeometry] at h
    cases h
  simp only [ite_eq_right hgeometry] at h
  by_cases hparameters : (p.scale == 0 || p.qden == 0 || p.pden == 0 || decide (p.qnum > p.qden) || decide (p.pnum > p.pden)) = true
  · simp only [ite_eq_left hparameters] at h
    cases h
  simp only [ite_eq_right hparameters] at h
  by_cases hcolumns : (decide (p.refcol ≥ laws.columns.size) || decide (p.tarcol ≥ laws.columns.size)) = true
  · simp only [ite_eq_left hcolumns] at h
    cases h
  simp only [ite_eq_right hcolumns] at h
  by_cases hnodeheader : (decide (nodes.size < 32) || !binaryMagic nodes 0 "R10ANODE" || natLE nodes 8 4 != m*m || natLE nodes 12 4 != (squareBoundary m).size) = true
  · simp only [ite_eq_left hnodeheader] at h
    cases h
  simp only [ite_eq_right hnodeheader] at h
  by_cases hnodeshape : (natLE nodes 16 8 == 0 || nodes.size != 32+64*(natLE nodes 16 8) || natLE nodes 24 4 != p.refcol || natLE nodes 28 4 != p.tarcol) = true
  · simp only [ite_eq_left hnodeshape] at h
    cases h
  simp only [ite_eq_right hnodeshape] at h
  by_cases hedgeheader : (decide (edges.size < 16) || !binaryMagic edges 0 "R10AEDGE") = true
  · simp only [ite_eq_left hedgeheader] at h
    cases h
  simp only [ite_eq_right hedgeheader] at h
  by_cases hedgeshape : (edges.size != 16+32*(natLE edges 8 8)) = true
  · simp only [ite_eq_left hedgeshape] at h
    cases h
  simp only [ite_eq_right hedgeshape] at h
  by_cases hnodecheck : (!(Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val).all (regionalNodeGuardWithWeights (m*m) (squareBoundary m).size (regionalPerms m) p laws.columns[p.refcol]! laws.columns[p.tarcol]! (regionalMassWeights (m*m) p))) = true
  · simp only [ite_eq_left hnodecheck] at h
    cases h
  simp only [ite_eq_right hnodecheck] at h
  by_cases hbottom : (((Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val).map RegionalNode.key)[0]! != 0) = true
  · simp only [ite_eq_left hbottom] at h
    cases h
  simp only [ite_eq_right hbottom] at h
  cases hscan : regionalKeysScan (parsedRegionalKeys nodes).toList {} with
  | none =>
    simp only [parsedRegionalKeys, parsedRegionalNodes] at hscan
    simp only [hscan] at h
    cases h
  | some seen =>
    have hscan' := hscan
    simp only [parsedRegionalKeys, parsedRegionalNodes] at hscan'
    simp only [hscan'] at h
    by_cases hsource : (!laws.columns[p.refcol]!.toList.all (fun kv => seen.contains kv.1)) = true
    · simp only [ite_eq_left hsource] at h
      cases h
    simp only [ite_eq_right hsource] at h
    by_cases harccheck : (!(Array.ofFn fun j : Fin (natLE edges 8 8) => regionalArcAt edges j.val).all (regionalArcGuard (natLE nodes 16 8) (squareBoundary m).size (regionalPerms m) ((Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val).map RegionalNode.key))) = true
    · simp only [ite_eq_left harccheck] at h
      cases h
    simp only [ite_eq_right harccheck] at h
    by_cases hzero : (!(replayBalance ((Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val).map (fun row => (row.supply : Int) - (row.absorbed : Int))) ((Array.ofFn fun j : Fin (natLE edges 8 8) => regionalArcAt edges j.val).map RegionalArc.toSparse)).all (· == 0)) = true
    · simp only [ite_eq_left hzero] at h
      cases h
    simp only [ite_eq_right hzero] at h
    have hgeom : geometryChecks m = true ∧ laws.n = m*m ∧
        laws.b = (squareBoundary m).size ∧ laws.graphs = 3 ∧ laws.columns.size = 3 := by
      simpa only [Bool.or_eq_true, Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, bne_iff_ne, not_or, not_not, and_assoc]
        using hgeometry
    have hparams : 0 < p.scale ∧ 0 < p.qden ∧ 0 < p.pden ∧
        p.qnum ≤ p.qden ∧ p.pnum ≤ p.pden := by
      simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
        Nat.pos_iff_ne_zero, not_lt, and_assoc] using hparameters
    have hcols : p.refcol < laws.columns.size ∧ p.tarcol < laws.columns.size := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] using hcolumns
    have hnh : 32 ≤ nodes.size ∧ binaryMagic nodes 0 "R10ANODE" = true ∧
        natLE nodes 8 4 = m*m ∧ natLE nodes 12 4 = (squareBoundary m).size := by
      simpa only [Bool.or_eq_true, Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, bne_iff_ne, decide_eq_true_eq,
        not_or, not_not, not_lt, and_assoc] using hnodeheader
    have hns : 0 < natLE nodes 16 8 ∧ nodes.size = 32+64*(natLE nodes 16 8) ∧
        natLE nodes 24 4 = p.refcol ∧ natLE nodes 28 4 = p.tarcol := by
      simpa only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, not_or, not_not,
        Nat.pos_iff_ne_zero, and_assoc] using hnodeshape
    have heh : 16 ≤ edges.size ∧ binaryMagic edges 0 "R10AEDGE" = true := by
      simpa only [Bool.or_eq_true, Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, decide_eq_true_eq,
        not_or, not_not, not_lt, and_assoc] using hedgeheader
    have hes : edges.size = 16+32*(natLE edges 8 8) := by
      simpa only [bne_iff_ne, not_not] using hedgeshape
    have hrows : (parsedRegionalNodes nodes).all
        (regionalNodeGuard (m*m) (squareBoundary m).size (regionalPerms m) p
          laws.columns[p.refcol]! laws.columns[p.tarcol]!) = true := by
      change ((Array.ofFn fun i : Fin (natLE nodes 16 8) => regionalNodeAt nodes i.val).all
        (regionalNodeGuardWithWeights (m*m) (squareBoundary m).size (regionalPerms m) p
          laws.columns[p.refcol]! laws.columns[p.tarcol]! (regionalMassWeights (m*m) p))) = true
      simpa only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, not_not] using hnodecheck
    have hbot : (parsedRegionalKeys nodes)[0]! = 0 := by
      simpa only [bne_iff_ne, not_not, parsedRegionalKeys, parsedRegionalNodes] using hbottom
    have hseen : regionalKeysScan (parsedRegionalKeys nodes).toList {} = some seen := by
      simpa only [parsedRegionalKeys, parsedRegionalNodes] using hscan
    obtain ⟨hunique, _, hmember⟩ := regionalKeysScan_sound _ _ _ hseen
    have hsources : ∀ pair ∈ laws.columns[p.refcol]!.toList, seen.contains pair.1 = true := by
      exact List.all_eq_true.mp (by
        simpa only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, not_not] using hsource)
    have harcs : (parsedRegionalRawArcs edges).all
        (regionalArcGuard (natLE nodes 16 8) (squareBoundary m).size
          (regionalPerms m) (parsedRegionalKeys nodes)) = true := by
      simpa only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, not_not, parsedRegionalRawArcs,
        parsedRegionalKeys, parsedRegionalNodes] using harccheck
    refine ⟨hgeom.1, hgeom.2, hparams, hcols, hnh, hns, heh, hes, ?_,
      ?_, hunique, hbot, ?_, ?_, ?_, ?_⟩
    · have hr : receipt = ⟨natLE nodes 16 8, natLE edges 8 8,
          ((parsedRegionalNodes nodes).toList.map RegionalNode.supply).sum,
          ((parsedRegionalNodes nodes).toList.map RegionalNode.absorbed).sum⟩ := by
        simpa only [pure, Except.ok.injEq, parsedRegionalNodes] using h.symm
      simp [hr]
    · simp only [parsedRegionalKeys, parsedRegionalNodes, Array.size_map, Array.size_ofFn]
    · intro i
      simpa only [parsedRegionalNodes, Array.getElem_ofFn] using
        (Array.all_eq_true.mp hrows) i.val (by simpa [parsedRegionalNodes] using i.isLt)
    · intro pair hp
      have hh := (hmember pair.1).mp (hsources pair hp)
      simpa using hh
    · intro j
      simpa only [parsedRegionalRawArcs, Array.getElem_ofFn] using
        (Array.all_eq_true.mp harcs) j.val (by simpa [parsedRegionalRawArcs] using j.isLt)
    · simpa only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_false, not_not, parsedRegionalInitial, parsedRegionalNodes,
        parsedRegionalArcs, parsedRegionalRawArcs] using hzero

/-- The actual parsed initial array is precisely supply minus absorption. -/
theorem parsedRegionalInitial_eq (nodes : ByteArray) :
    parsedRegionalInitial nodes =
      replayInitial (parsedRegionalSupply nodes) (parsedRegionalAbsorbed nodes) := by
  unfold parsedRegionalInitial parsedRegionalNodes replayInitial
  rw [Array.map_ofFn]
  rfl

/-- Internal guard reflection for the exact parsed sparse occurrence array. -/
theorem parsedRegionalArcs_endpoints (M b : Nat) (perms : Array (Array Nat))
    (keys : Array Nat) (edges : ByteArray)
    (h : ∀ j : Fin (natLE edges 8 8),
      regionalArcGuard M b perms keys (regionalArcAt edges j.val) = true) :
    sparseEndpoints M (parsedRegionalArcs edges) := by
  intro arc hmem
  simp only [parsedRegionalArcs, parsedRegionalRawArcs, Array.toList_map,
    Array.toList_ofFn, List.mem_map, List.mem_ofFn] at hmem
  obtain ⟨raw, ⟨j, rfl⟩, rfl⟩ := hmem
  have hh := regionalArcGuard_sound M b perms keys (regionalArcAt edges j.val) (h j)
  exact ⟨hh.1, hh.2.1⟩

/-- Checker success alone supplies the endpoint and replay premises of the
previously proved exact sparse conservation theorem. -/
theorem checkRegionalFlow_conservation (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    ∀ i : Fin (natLE nodes 16 8),
      parsedRegionalSupply nodes i +
        ∑ j : Fin (natLE nodes 16 8), sparseEdge (parsedRegionalArcs edges) j i =
      parsedRegionalAbsorbed nodes i +
        ∑ j : Fin (natLE nodes 16 8), sparseEdge (parsedRegionalArcs edges) i j := by
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt h
  have bounds := parsedRegionalArcs_endpoints _ _ _ _ _ facts.arcs_checked
  have hz := facts.replay_zero
  rw [parsedRegionalInitial_eq] at hz
  exact replayBalance_all_zero_conservation _ _ _ bounds hz

/-- Canonicality, C4, and exact C5 formulas at every actual node index. -/
theorem checkRegionalFlow_node_fields (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (i : Fin (natLE nodes 16 8)) :
    let row := regionalNodeAt nodes i.val
    validCanonical (squareBoundary m).size (regionalPerms m) row.key = true ∧
    row.supply < 2^127 ∧ row.capacity < 2^127 ∧ row.absorbed < 2^127 ∧
    row.absorbed ≤ row.capacity ∧
    row.supply = (if row.key == 0 then 0 else (p.scale * numerator
      (laws.columns[p.refcol]!.getD row.key (Array.replicate (m*m+1) 0))
      (weights (m*m) p.qnum p.qden) + p.qden^(m*m) - 1) / p.qden^(m*m)) ∧
    row.capacity = p.scale * numerator
      (laws.columns[p.tarcol]!.getD row.key (Array.replicate (m*m+1) 0))
      (weights (m*m) p.pnum p.pden) / p.pden^(m*m) := by
  exact regionalNodeGuard_sound _ _ _ _ _ _ _
    ((checkRegionalFlow_ok m laws p nodes edges receipt h).nodes_checked i)

/-- Endpoint/flow bounds and the actual moveKey/keyLE guard at every arc index. -/
theorem checkRegionalFlow_arc_fields (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt)
    (j : Fin (natLE edges 8 8)) :
    let arc := regionalArcAt edges j.val
    arc.src < natLE nodes 16 8 ∧ arc.dst < natLE nodes 16 8 ∧
    arc.perm < (regionalPerms m).size ∧ arc.reserved = 0 ∧
    0 < arc.flow ∧ arc.flow < 2^127 ∧ keyLE (squareBoundary m).size
      (parsedRegionalKeys nodes)[arc.src]!
      (moveKey (squareBoundary m).size (regionalPerms m)[arc.perm]!
        (parsedRegionalKeys nodes)[arc.dst]!) = true := by
  exact regionalArcGuard_sound _ _ _ _ _
    ((checkRegionalFlow_ok m laws p nodes edges receipt h).arcs_checked j)

/-- C6 covers every source row, not merely its total mass or checksum. -/
theorem checkRegionalFlow_source_complete (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    ∀ pair ∈ laws.columns[p.refcol]!.toList, ∃ i : Fin (natLE nodes 16 8),
      (regionalNodeAt nodes i.val).key = pair.1 := by
  intro pair hp
  have hh := (checkRegionalFlow_ok m laws p nodes edges receipt h).source_complete pair hp
  simp only [parsedRegionalKeys, parsedRegionalNodes, Array.toList_map,
    Array.toList_ofFn, List.mem_map, List.mem_ofFn] at hh
  obtain ⟨row, ⟨i, rfl⟩, hi⟩ := hh
  exact ⟨i, hi⟩

/-- The actual parsed finite integer data, together with all premises of the
existing narrow sparse-flow conservation adapter, is a success witness.  This
does not assert packed-order semantics or any probability-law identity. -/
theorem checkRegionalFlow_integer_witness (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    ∃ d : IntegerFlowData (Fin (natLE nodes 16 8)),
      d.scale = p.scale ∧ d.bottom.val = 0 ∧
      d.supply = parsedRegionalSupply nodes ∧
      d.capacity = (fun i => ((regionalNodeAt nodes i.val).capacity : Int)) ∧
      d.absorbed = parsedRegionalAbsorbed nodes ∧
      d.edge = sparseEdge (parsedRegionalArcs edges) ∧
      sparseEndpoints (natLE nodes 16 8) (parsedRegionalArcs edges) ∧
      (replayBalance (replayInitial d.supply d.absorbed)
        (parsedRegionalArcs edges)).all (· == 0) = true ∧
      ∀ i : Fin (natLE nodes 16 8),
        d.supply i + ∑ j, d.edge j i = d.absorbed i + ∑ j, d.edge i j := by
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt h
  let d : IntegerFlowData (Fin (natLE nodes 16 8)) :=
    ⟨p.scale, ⟨0, facts.node_shape.1⟩, parsedRegionalSupply nodes,
      (fun i => ((regionalNodeAt nodes i.val).capacity : Int)),
      parsedRegionalAbsorbed nodes, sparseEdge (parsedRegionalArcs edges)⟩
  have bounds := parsedRegionalArcs_endpoints _ _ _ _ _ facts.arcs_checked
  have hz := facts.replay_zero
  rw [parsedRegionalInitial_eq] at hz
  refine ⟨d, rfl, rfl, rfl, rfl, rfl, rfl, bounds, hz, ?_⟩
  exact integerFlow_conservation_of_replayBalance d (parsedRegionalArcs edges)
    bounds (fun _ _ => rfl) hz

/-- Every actual sparse occurrence has a positive exact integer flow and the
same in-range permutation witness that was tested by the executable. -/
theorem checkRegionalFlow_sparse_arcs (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) (receipt : FlowReceipt)
    (h : checkRegionalFlow m laws p nodes edges = .ok receipt) :
    sparseEndpoints (natLE nodes 16 8) (parsedRegionalArcs edges) ∧
    ∀ a ∈ (parsedRegionalArcs edges).toList, 0 < a.2.2 ∧
      ∃ k : Fin (regionalPerms m).size,
        keyLE (squareBoundary m).size (parsedRegionalKeys nodes)[a.1]!
          (moveKey (squareBoundary m).size (regionalPerms m)[k.val]!
            (parsedRegionalKeys nodes)[a.2.1]!) = true := by
  have facts := checkRegionalFlow_ok m laws p nodes edges receipt h
  refine ⟨parsedRegionalArcs_endpoints _ _ _ _ _ facts.arcs_checked, ?_⟩
  intro a ha
  simp only [parsedRegionalArcs, parsedRegionalRawArcs, Array.toList_map,
    Array.toList_ofFn, List.mem_map, List.mem_ofFn] at ha
  obtain ⟨raw, ⟨j, rfl⟩, rfl⟩ := ha
  have hh := checkRegionalFlow_arc_fields m laws p nodes edges receipt h j
  refine ⟨?_, ⟨⟨(regionalArcAt edges j.val).perm, hh.2.2.1⟩, hh.2.2.2.2.2.2⟩⟩
  change (0 : Int) < ((regionalArcAt edges j.val).flow : Int)
  exact Int.natCast_pos.mpr hh.2.2.2.2.1

end SitePerc.Checker

#print axioms SitePerc.Checker.checkRegionalFlow_ok
#print axioms SitePerc.Checker.parsedRegionalInitial_eq
#print axioms SitePerc.Checker.parsedRegionalArcs_endpoints
#print axioms SitePerc.Checker.checkRegionalFlow_conservation
#print axioms SitePerc.Checker.checkRegionalFlow_node_fields
#print axioms SitePerc.Checker.checkRegionalFlow_arc_fields
#print axioms SitePerc.Checker.checkRegionalFlow_source_complete
#print axioms SitePerc.Checker.checkRegionalFlow_integer_witness
#print axioms SitePerc.Checker.checkRegionalFlow_sparse_arcs
#print axioms SitePerc.Checker.regionalKeysScan_sound
#print axioms SitePerc.Checker.regionalNodeGuard_sound
#print axioms SitePerc.Checker.regionalArcGuard_sound
