import SitePerc.Checker.ShardedDefs
import SitePerc.Checker.DirectSoundness
import Mathlib.Tactic

/-! Exact disjoint coverage and standard-axiom consumers of independently
native-checked persisted actual C7 shards. No native computation is invoked
by any theorem in this file. -/
open scoped BigOperators
namespace SitePerc.Checker

theorem boundaryShard_partition (m shards bm : Nat)
    (hbm : bm < boundaryShardTotal m) :
    ∃! p : Nat × Nat, p.1 < boundaryShardWorkers shards ∧
      p.2 < boundaryShardCount m shards p.1 ∧
      boundaryShardStart m shards p.1 + p.2 = bm := by
  let total := boundaryShardTotal m
  let w := boundaryShardWorkers shards
  let width := boundaryShardWidth m shards
  have hw : 0 < w := by dsimp [w, boundaryShardWorkers]; omega
  have cover : total ≤ w * width := ceil_partition_covers total w hw
  have ht : 0 < total := Nat.two_pow_pos _
  have hwidth : 0 < width := by
    by_contra hn
    have hz : width = 0 := by omega
    simp only [hz, Nat.mul_zero] at cover
    omega
  let q := bm / width
  let r := bm % width
  have hq : q < w := (Nat.div_lt_iff_lt_mul hwidth).mpr (lt_of_lt_of_le hbm cover)
  have hr : r < width := Nat.mod_lt _ hwidth
  have heq : q*width+r = bm := by
    dsimp [q,r]
    have h := Nat.mod_add_div bm width
    simpa [Nat.mul_comm, Nat.add_comm] using h
  have hrem : r < min width (total-q*width) := by omega
  change ∃! p : Nat × Nat, p.1 < w ∧ p.2 < min width (total-p.1*width) ∧ p.1*width+p.2 = bm
  refine ⟨(q,r), ⟨hq,hrem,heq⟩, ?_⟩
  intro p hp
  have hpwidth : p.2 < width := lt_of_lt_of_le hp.2.1 (min_le_left _ _)
  have hdiv : p.1 = q := by
    dsimp [q]
    rw [←hp.2.2, Nat.add_comm, Nat.add_mul_div_right _ _ hwidth,
      Nat.div_eq_of_lt hpwidth, Nat.zero_add]
  apply Prod.ext hdiv
  change p.2 = r
  have hsum := hp.2.2
  rw [hdiv] at hsum
  omega

theorem regionalShardPass_sound (m mode shards i : Nat) (stored : CountMap)
    (h : regionalShardPass m mode shards i stored = true) :
    Std.HashMap.Equiv stored (regionalShard m mode shards i) := by
  exact Std.HashMap.equiv_of_beq (Bool.and_eq_true_iff.mp h).2

theorem regionalShard_shape (m : Nat) (mode : Fin 3) (shards i : Nat) :
    CountShape (m*m) (regionalShard m mode.val shards i) := by
  unfold regionalShard enumerateBoundaryCubes
  exact (boundaryCubesLoop_valid (m*m) (gridEdges m mode.val) (squareBoundary m)
    (regionalPerms m) (interiorVertices m) (cubeBinomials (interiorVertices m).length)
    1 (boundaryShardCount m shards i) (boundaryShardStart m shards i) {} {} {}
    (countShape_empty (m*m)) (cacheValid_empty (squareBoundary m).size (regionalPerms m))).1

theorem regionalShard_coefficient (m : Nat) (hm : RegionalSize m)
    (mode : Fin 3) (shards i query k : Nat) (hk : k ≤ m*m) :
    coefficient (m*m) (regionalShard m mode.val shards i) query k =
      ∑ j ∈ Finset.range (boundaryShardCount m shards i),
        ∑ mask ∈ Finset.range (2^(interiorVertices m).length),
          if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m) (regionalPerms m)
              (cubePath (interiorVertices m)
                (embedBoundary (squareBoundary m) ((boundaryShardStart m shards i+j)%boundaryShardTotal m))
                (openCount (squareBoundary m).size
                  ((boundaryShardStart m shards i+j)%boundaryShardTotal m)) mask).1 = query ∧
            (cubePath (interiorVertices m)
                (embedBoundary (squareBoundary m) ((boundaryShardStart m shards i+j)%boundaryShardTotal m))
                (openCount (squareBoundary m).size
                  ((boundaryShardStart m shards i+j)%boundaryShardTotal m)) mask).2 = k
          then 1 else 0 := by
  let n := m*m
  let b := squareBoundary m
  let es := gridEdges m mode.val
  let ps := regionalPerms m
  let vs := interiorVertices m
  obtain ⟨hb,hinj,hps⟩ := regional_pruning_geometry m hm
  have hn : n < 64 := by rcases hm with rfl | rfl | rfl <;> decide
  have he : BoundedEdges n es := regional_grid_bounded m hm mode
  have hvalid : ∀ bm < 2^b.size, ValidCube n vs (embedBoundary b bm) := by
    intro bm hbm
    exact boundaryCube_valid m hm ⟨bm,hbm⟩
  have hslots : b.size+vs.length ≤ n := by
    have h := (squareBoundary_interior_perm m hm).length_eq
    have heq : b.size+vs.length = n := by
      simpa only [List.length_append,Array.length_toList,List.length_range] using h
    omega
  have hz : coefficient n ({} : CountMap) query k = 0 := by
    simp only [coefficient,Std.HashMap.getD_empty]
    exact zeroCounts_get n k hk
  have h := boundaryCubesLoop_coefficient n hn es b ps vs he hb hinj hps hvalid hslots
    1 (boundaryShardCount m shards i) (boundaryShardStart m shards i) {} {} {}
    (countShape_empty n) (cacheValid_empty b.size ps) query k hk
  rw [hz,Nat.zero_add] at h
  dsimp only [n,b,es,ps,vs] at h
  simp only [Nat.mul_one] at h
  unfold regionalShard enumerateBoundaryCubes
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro mask hmask
  split_ifs <;> simp_all [boundaryShardTotal]

theorem regionalShard_coefficient_partition (m : Nat) (hm : RegionalSize m)
    (mode : Fin 3) (shards query k : Nat) (hk : k ≤ m*m) :
    (∑ i : Fin (boundaryShardWorkers shards),
      coefficient (m*m) (regionalShard m mode.val shards i.val) query k) =
      ∑ mask ∈ Finset.range (2^(m*m)),
        if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m)
            (regionalPerms m) mask = query ∧ openCount (m*m) mask = k
        then 1 else 0 := by
  let w := boundaryShardWorkers shards
  let count := boundaryShardTotal m
  let width := boundaryShardWidth m shards
  have hmaps : (prunedParallel m mode.val shards count 0).toList =
      (List.range w).map (fun i => enumerateBoundaryCubes m mode.val
        (i*width) (min width (count-i*width)) 1) := by
    simp only [prunedParallel,Task.spawn,List.map_map]
    change ((List.range w).map (fun i => enumerateBoundaryCubes m mode.val
      (0+i*width*1) (min width (count-i*width)) 1)).toArray.toList = _
    simp only [Nat.zero_add,Nat.mul_one]
  dsimp only [count,boundaryShardTotal] at hmaps
  have h := prunedParallel_coefficients_correct m hm mode shards query k hk
  rw [sumCounts_coefficient (m*m) _ query k hk,
    Array.toList_map,hmaps] at h
  simp only [List.map_map] at h
  rw [sum_map_range] at h
  rw [←Fin.sum_univ_eq_sum_range] at h
  simpa only [Function.comp_apply,regionalShard,boundaryShardCount,boundaryShardStart,
    boundaryShardTotal,w,width,count] using h

theorem shardedRegionalLaws_exact (m : Nat) (hm : RegionalSize m)
    (shards : Nat) (data : ShardFamily shards) (checked : ShardReceipts m shards data) :
    ExactRegionalLaws m (shardedRegionalLaws m shards data) := by
  constructor
  · simp [shardedRegionalLaws]
  · intro mode
    have hc : (shardedRegionalLaws m shards data).columns[mode.val]! =
        shardedRegionalColumn m shards data mode := by
      rw [getElem!_pos _ _ (by simp [shardedRegionalLaws])]
      simp [shardedRegionalLaws]
    rw [hc,shardedRegionalColumn]
    exact mergeCountMaps_shape (m*m) _
  · intro mode query k hk
    have hc : (shardedRegionalLaws m shards data).columns[mode.val]! =
        shardedRegionalColumn m shards data mode := by
      rw [getElem!_pos _ _ (by simp [shardedRegionalLaws])]
      simp [shardedRegionalLaws]
    rw [hc,shardedRegionalColumn,mergeCountMaps_coefficient (m*m) _ query k hk,
      sumCounts_coefficient (m*m) _ query k hk,Array.toList_ofFn,List.map_ofFn,List.sum_ofFn]
    calc
      _ = ∑ i : Fin (boundaryShardWorkers shards),
          coefficient (m*m) (regionalShard m mode.val shards i.val) query k := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [Function.comp_apply]
        unfold coefficient
        rw [(regionalShardPass_sound m mode.val shards i.val (data mode i) (checked mode i)).getD_eq]
      _ = _ := regionalShard_coefficient_partition m hm mode shards query k hk

theorem shardedRegionalPass_boundary_stages
    (shards : Nat) (data : ShardFamily shards) (checked : ShardReceipts 6 shards data)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray)
    (h : shardedRegionalPass 6 shards data verifiedStageOneParams verifiedStageTwoParams
      nodesOne edgesOne nodesTwo edgesTwo = true) :
    boundaryDominates 6 (0,0) lineLattice intermediate q0 p1 ∧
      boundaryDominates 6 (3,3) intermediate square p1 p2 := by
  cases hone : checkRegionalFlow 6 (shardedRegionalLaws 6 shards data)
      verifiedStageOneParams nodesOne edgesOne with
  | error e =>
    simp only [shardedRegionalPass,shardedRegionalCheck,hone] at h
    change false = true at h
    cases h
  | ok one =>
    cases htwo : checkRegionalFlow 6 (shardedRegionalLaws 6 shards data)
        verifiedStageTwoParams nodesTwo edgesTwo with
    | error e =>
      simp only [shardedRegionalPass,shardedRegionalCheck,hone,htwo] at h
      change false = true at h
      cases h
    | ok two =>
      exact verified_boundary_stages (shardedRegionalLaws 6 shards data)
        (shardedRegionalLaws_exact 6 (Or.inr (Or.inr rfl)) shards data checked)
        nodesOne edgesOne nodesTwo edgesTwo one two hone htwo

#print axioms boundaryShard_partition
#print axioms regionalShardPass_sound
#print axioms regionalShard_shape
#print axioms regionalShard_coefficient
#print axioms regionalShard_coefficient_partition
#print axioms shardedRegionalLaws_exact
#print axioms shardedRegionalPass_boundary_stages
end SitePerc.Checker
