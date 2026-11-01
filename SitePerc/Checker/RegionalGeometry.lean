import SitePerc.Geometry
import SitePerc.Checker.RegionalDefs
import SitePerc.Checker.Connectivity
import Mathlib.Tactic

/-! Exact finite geometry of the executable regional checker. -/

set_option autoImplicit false

namespace SitePerc.Checker

/-- Row-major order: the first cell coordinate is horizontal. -/
def rowMajor (m : Nat) : Fin (m*m) ≃ Cell m :=
  finProdFinEquiv.symm.trans (Equiv.prodComm _ _)

/-- The three supported checker sizes. -/
def RegionalSize (m : Nat) : Prop := m = 2 ∨ m = 4 ∨ m = 6

instance (m : Nat) : Decidable (RegionalSize m) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Actual square perimeter, in row-major indices. -/
def rowPerimeter (m : Nat) (v : Fin (m*m)) : Prop :=
  (rowMajor m v).1.val = 0 ∨ (rowMajor m v).1.val+1 = m ∨
  (rowMajor m v).2.val = 0 ∨ (rowMajor m v).2.val+1 = m

instance (m : Nat) (v : Fin (m*m)) : Decidable (rowPerimeter m v) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- Explicit coordinate test for the ordinary square graph. -/
def regionalSquareAdj (m : Nat) (a b : Fin (m*m)) : Prop :=
  let x : Int := a.val % m
  let y : Int := a.val / m
  let u : Int := b.val % m
  let v : Int := b.val / m
  (u=x+1 ∧ v=y) ∨ (x=u+1 ∧ y=v) ∨ (u=x ∧ v=y+1) ∨ (x=u ∧ y=v+1)

/-- The executor's actual diagonal-retention rule. -/
def regionalKeep (m mode : Nat) (x y : Int) : Prop :=
  mode = 1 ∨ (mode = 2 ∧
    ((x+(if m=6 then 3 else 1)) % (m : Int) = (m : Int)-1 ∨
     (y+(if m=6 then 3 else 1)) % (m : Int) = (m : Int)-1))

/-- Coordinate formula for a checkerboard graph with the executable retention mode. -/
def regionalAdj (m mode : Nat) (a b : Fin (m*m)) : Prop :=
  let x : Int := a.val % m
  let y : Int := a.val / m
  let u : Int := b.val % m
  let v : Int := b.val / m
  regionalSquareAdj m a b ∨
    (u=x+1 ∧ v=y+1 ∧ (x+y)%2=0 ∧ regionalKeep m mode x y) ∨
    (x=u+1 ∧ y=v+1 ∧ (u+v)%2=0 ∧ regionalKeep m mode u v) ∨
    (u=x+1 ∧ y=v+1 ∧ (x+v)%2=0 ∧ regionalKeep m mode x v) ∨
    (x=u+1 ∧ v=y+1 ∧ (u+y)%2=0 ∧ regionalKeep m mode u y)

instance (m mode : Nat) (a b : Fin (m*m)) : Decidable (regionalAdj m mode a b) := by
  unfold regionalAdj regionalSquareAdj regionalKeep
  infer_instance

/-- Exact bounds, uniqueness and image of the actual boundary array. -/
def RegionalBoundaryData (m : Nat) : Prop :=
  (squareBoundary m).size = 4*m-4 ∧
  (squareBoundary m).toList.Nodup ∧
  (∀ i : Fin (squareBoundary m).size, (squareBoundary m)[i.val]! < m*m) ∧
  (∀ v : Fin (m*m), v.val ∈ (squareBoundary m).toList ↔ rowPerimeter m v)

/-- Concrete permutation certificates on the actual arrays, including adjacency iff,
not merely preservation of enumerated edges in one direction. -/
def RegionalPermutationData (m : Nat) : Prop :=
  (regionalPerms m).size = (regionalVertexPerms m).size ∧
  ∀ t : Fin (regionalVertexPerms m).size,
    let p := (regionalVertexPerms m)[t.val]!
    let q := (regionalPerms m)[t.val]!
    p.size = m*m ∧ q.size = (squareBoundary m).size ∧
    (∀ a : Fin (m*m), p[a.val]! < m*m) ∧
    (∀ a b : Fin (m*m), p[a.val]! = p[b.val]! → a=b) ∧
    (∀ mode : Fin 3, ∀ a b : Fin (m*m),
      edgeMember (gridEdges m mode.val) a.val b.val =
      edgeMember (gridEdges m mode.val) p[a.val]! p[b.val]!) ∧
    (∀ b : Fin (squareBoundary m).size, q[b.val]! < (squareBoundary m).size) ∧
    (∀ a b : Fin (squareBoundary m).size, q[a.val]! = q[b.val]! → a=b) ∧
    (∀ b : Fin (squareBoundary m).size,
      p[(squareBoundary m)[b.val]!]! = (squareBoundary m)[q[b.val]!]!)

instance (m : Nat) : Decidable (RegionalBoundaryData m) := by
  unfold RegionalBoundaryData
  infer_instance

instance (m : Nat) : Decidable (RegionalPermutationData m) := by
  unfold RegionalPermutationData
  infer_instance

@[simp] theorem rowMajor_fst (m : Nat) (v : Fin (m*m)) :
    (rowMajor m v).1.val = v.val % m := rfl

@[simp] theorem rowMajor_snd (m : Nat) (v : Fin (m*m)) :
    (rowMajor m v).2.val = v.val / m := rfl

@[simp] theorem rowMajor_symm_val (m : Nat) (u : Cell m) :
    ((rowMajor m).symm u).val = u.1.val+m*u.2.val := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem boundary_data_2 : RegionalBoundaryData 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem boundary_data_4 : RegionalBoundaryData 4 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem boundary_data_6 : RegionalBoundaryData 6 := by decide +kernel

/-- The actual perimeter traversal has no duplicate or omitted vertex. -/
theorem regionalBoundaryData (m : Nat) (hm : RegionalSize m) : RegionalBoundaryData m := by
  rcases hm with rfl | rfl | rfl
  · exact boundary_data_2
  · exact boundary_data_4
  · exact boundary_data_6

/-- A theorem-level rewrite removes well-founded sort reduction from finite checks.
The executable function itself remains unchanged. -/
private theorem commonAutomorphism_compute (m : Nat) : commonAutomorphism m =
    (fun p => (p.toList.insertionSort (· ≤ ·) == List.range (m*m)) &&
      (List.range 3).all (fun mode => (gridEdges m mode).all fun (u,v) =>
        edgeMember (gridEdges m mode) p[u]! p[v]!)) := by
  funext p
  unfold commonAutomorphism
  rw [List.mergeSort_eq_insertionSort]

private theorem regionalVertexPerms_compute (m : Nat) : regionalVertexPerms m =
    (candidateVertexPerms m).filter (fun p =>
      (p.toList.insertionSort (· ≤ ·) == List.range (m*m)) &&
      (List.range 3).all (fun mode => (gridEdges m mode).all fun (u,v) =>
        edgeMember (gridEdges m mode) p[u]! p[v]!)) := by
  unfold regionalVertexPerms
  rw [commonAutomorphism_compute]

/-- Small array certificate; edge preservation is derived from the actual filter. -/
private def RegionalPermutationFrame (m : Nat) : Prop :=
  (regionalPerms m).size = (regionalVertexPerms m).size ∧
  ∀ t : Fin (regionalVertexPerms m).size,
    let p := (regionalVertexPerms m)[t.val]!
    let q := (regionalPerms m)[t.val]!
    p.size = m*m ∧ q.size = (squareBoundary m).size ∧
    (∀ a : Fin (m*m), p[a.val]! < m*m) ∧
    (∀ a b : Fin (m*m), p[a.val]! = p[b.val]! → a=b) ∧
    (∀ b : Fin (squareBoundary m).size, q[b.val]! < (squareBoundary m).size) ∧
    (∀ a b : Fin (squareBoundary m).size, q[a.val]! = q[b.val]! → a=b) ∧
    (∀ b : Fin (squareBoundary m).size,
      p[(squareBoundary m)[b.val]!]! = (squareBoundary m)[q[b.val]!]!)

section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem grid_edges_2_0 : gridEdges 2 0 = [(2,3), (1,3), (0,2), (0,1)] := by decide +kernel

private theorem grid_edges_2_1 : gridEdges 2 1 = [(2,3), (1,3), (1,2), (0,3), (0,2), (0,1)] := by decide +kernel

private theorem grid_edges_2_2 : gridEdges 2 2 = [(2,3), (1,3), (1,2), (0,3), (0,2), (0,1)] := by decide +kernel

private theorem grid_edges_mode_2 (mode : Fin 3) : gridEdges 2 mode.val =
    if mode.val=0 then [(2,3), (1,3), (0,2), (0,1)]
    else if mode.val=1 then [(2,3), (1,3), (1,2), (0,3), (0,2), (0,1)]
    else [(2,3), (1,3), (1,2), (0,3), (0,2), (0,1)] := by
  fin_cases mode <;> simp only [grid_edges_2_0,grid_edges_2_1,grid_edges_2_2]
  all_goals decide +kernel

private theorem vertex_perms_2 : regionalVertexPerms 2 =
    #[#[0, 1, 2, 3],
      #[2, 3, 0, 1],
      #[1, 0, 3, 2],
      #[3, 2, 1, 0],
      #[0, 2, 1, 3],
      #[2, 0, 3, 1],
      #[1, 3, 0, 2],
      #[3, 1, 2, 0]] := by
  rw [regionalVertexPerms_compute]
  decide +kernel

private theorem boundary_perms_2 : regionalPerms 2 =
    #[#[0, 1, 2, 3],
      #[3, 2, 1, 0],
      #[1, 0, 3, 2],
      #[2, 3, 0, 1],
      #[0, 3, 2, 1],
      #[3, 0, 1, 2],
      #[1, 2, 3, 0],
      #[2, 1, 0, 3]] := by
  unfold regionalPerms
  rw [vertex_perms_2]
  decide +kernel

private theorem permutation_frame_2 : RegionalPermutationFrame 2 := by
  unfold RegionalPermutationFrame
  rw [vertex_perms_2,boundary_perms_2]
  decide +kernel

private theorem grid_edges_4_0 : gridEdges 4 0 = [(14,15), (13,14), (12,13), (11,15), (10,14), (10,11), (9,13), (9,10), (8,12), (8,9), (7,11), (6,10), (6,7), (5,9), (5,6), (4,8), (4,5), (3,7), (2,6), (2,3), (1,5), (1,2), (0,4), (0,1)] := by decide +kernel

private theorem grid_edges_4_1 : gridEdges 4 1 = [(14,15), (13,14), (12,13), (11,15), (11,14), (10,15), (10,14), (10,11), (9,13), (9,10), (9,12), (8,13), (8,12), (8,9), (7,11), (6,10), (6,7), (6,9), (5,10), (5,9), (5,6), (4,8), (4,5), (3,7), (3,6), (2,7), (2,6), (2,3), (1,5), (1,2), (1,4), (0,5), (0,4), (0,1)] := by decide +kernel

private theorem grid_edges_4_2 : gridEdges 4 2 = [(14,15), (13,14), (12,13), (11,15), (11,14), (10,15), (10,14), (10,11), (9,13), (9,10), (9,12), (8,13), (8,12), (8,9), (7,11), (6,10), (6,7), (5,9), (5,6), (4,8), (4,5), (3,7), (3,6), (2,7), (2,6), (2,3), (1,5), (1,2), (0,4), (0,1)] := by decide +kernel

private theorem grid_edges_mode_4 (mode : Fin 3) : gridEdges 4 mode.val =
    if mode.val=0 then [(14,15), (13,14), (12,13), (11,15), (10,14), (10,11), (9,13), (9,10), (8,12), (8,9), (7,11), (6,10), (6,7), (5,9), (5,6), (4,8), (4,5), (3,7), (2,6), (2,3), (1,5), (1,2), (0,4), (0,1)]
    else if mode.val=1 then [(14,15), (13,14), (12,13), (11,15), (11,14), (10,15), (10,14), (10,11), (9,13), (9,10), (9,12), (8,13), (8,12), (8,9), (7,11), (6,10), (6,7), (6,9), (5,10), (5,9), (5,6), (4,8), (4,5), (3,7), (3,6), (2,7), (2,6), (2,3), (1,5), (1,2), (1,4), (0,5), (0,4), (0,1)]
    else [(14,15), (13,14), (12,13), (11,15), (11,14), (10,15), (10,14), (10,11), (9,13), (9,10), (9,12), (8,13), (8,12), (8,9), (7,11), (6,10), (6,7), (5,9), (5,6), (4,8), (4,5), (3,7), (3,6), (2,7), (2,6), (2,3), (1,5), (1,2), (0,4), (0,1)] := by
  fin_cases mode <;> simp only [grid_edges_4_0,grid_edges_4_1,grid_edges_4_2]
  all_goals decide +kernel

private theorem vertex_perms_4 : regionalVertexPerms 4 =
    #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
      #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]] := by
  rw [regionalVertexPerms_compute]
  decide +kernel

private theorem boundary_perms_4 : regionalPerms 4 =
    #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
      #[0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]] := by
  unfold regionalPerms
  rw [vertex_perms_4]
  decide +kernel

private theorem permutation_frame_4 : RegionalPermutationFrame 4 := by
  unfold RegionalPermutationFrame
  rw [vertex_perms_4,boundary_perms_4]
  decide +kernel

private theorem grid_edges_6_0 : gridEdges 6 0 = [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (28,34), (28,29), (27,33), (27,28), (26,32), (26,27), (25,31), (25,26), (24,30), (24,25), (23,29), (22,28), (22,23), (21,27), (21,22), (20,26), (20,21), (19,25), (19,20), (18,24), (18,19), (17,23), (16,22), (16,17), (15,21), (15,16), (14,20), (14,15), (13,19), (13,14), (12,18), (12,13), (11,17), (10,16), (10,11), (9,15), (9,10), (8,14), (8,9), (7,13), (7,8), (6,12), (6,7), (5,11), (4,10), (4,5), (3,9), (3,4), (2,8), (2,3), (1,7), (1,2), (0,6), (0,1)] := by decide +kernel

private theorem grid_edges_6_1 : gridEdges 6 1 = [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (29,34), (28,35), (28,34), (28,29), (27,33), (27,28), (27,32), (26,33), (26,32), (26,27), (25,31), (25,26), (25,30), (24,31), (24,30), (24,25), (23,29), (22,28), (22,23), (22,27), (21,28), (21,27), (21,22), (20,26), (20,21), (20,25), (19,26), (19,25), (19,20), (18,24), (18,19), (17,23), (17,22), (16,23), (16,22), (16,17), (15,21), (15,16), (15,20), (14,21), (14,20), (14,15), (13,19), (13,14), (13,18), (12,19), (12,18), (12,13), (11,17), (10,16), (10,11), (10,15), (9,16), (9,15), (9,10), (8,14), (8,9), (8,13), (7,14), (7,13), (7,8), (6,12), (6,7), (5,11), (5,10), (4,11), (4,10), (4,5), (3,9), (3,4), (3,8), (2,9), (2,8), (2,3), (1,7), (1,2), (1,6), (0,7), (0,6), (0,1)] := by decide +kernel

private theorem grid_edges_6_2 : gridEdges 6 2 = [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (28,34), (28,29), (27,33), (27,28), (27,32), (26,33), (26,32), (26,27), (25,31), (25,26), (24,30), (24,25), (23,29), (22,28), (22,23), (21,27), (21,22), (20,26), (20,21), (19,25), (19,20), (18,24), (18,19), (17,23), (17,22), (16,23), (16,22), (16,17), (15,21), (15,16), (15,20), (14,21), (14,20), (14,15), (13,19), (13,14), (13,18), (12,19), (12,18), (12,13), (11,17), (10,16), (10,11), (9,15), (9,10), (8,14), (8,9), (7,13), (7,8), (6,12), (6,7), (5,11), (4,10), (4,5), (3,9), (3,4), (3,8), (2,9), (2,8), (2,3), (1,7), (1,2), (0,6), (0,1)] := by decide +kernel

private theorem grid_edges_mode_6 (mode : Fin 3) : gridEdges 6 mode.val =
    if mode.val=0 then [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (28,34), (28,29), (27,33), (27,28), (26,32), (26,27), (25,31), (25,26), (24,30), (24,25), (23,29), (22,28), (22,23), (21,27), (21,22), (20,26), (20,21), (19,25), (19,20), (18,24), (18,19), (17,23), (16,22), (16,17), (15,21), (15,16), (14,20), (14,15), (13,19), (13,14), (12,18), (12,13), (11,17), (10,16), (10,11), (9,15), (9,10), (8,14), (8,9), (7,13), (7,8), (6,12), (6,7), (5,11), (4,10), (4,5), (3,9), (3,4), (2,8), (2,3), (1,7), (1,2), (0,6), (0,1)]
    else if mode.val=1 then [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (29,34), (28,35), (28,34), (28,29), (27,33), (27,28), (27,32), (26,33), (26,32), (26,27), (25,31), (25,26), (25,30), (24,31), (24,30), (24,25), (23,29), (22,28), (22,23), (22,27), (21,28), (21,27), (21,22), (20,26), (20,21), (20,25), (19,26), (19,25), (19,20), (18,24), (18,19), (17,23), (17,22), (16,23), (16,22), (16,17), (15,21), (15,16), (15,20), (14,21), (14,20), (14,15), (13,19), (13,14), (13,18), (12,19), (12,18), (12,13), (11,17), (10,16), (10,11), (10,15), (9,16), (9,15), (9,10), (8,14), (8,9), (8,13), (7,14), (7,13), (7,8), (6,12), (6,7), (5,11), (5,10), (4,11), (4,10), (4,5), (3,9), (3,4), (3,8), (2,9), (2,8), (2,3), (1,7), (1,2), (1,6), (0,7), (0,6), (0,1)]
    else [(34,35), (33,34), (32,33), (31,32), (30,31), (29,35), (28,34), (28,29), (27,33), (27,28), (27,32), (26,33), (26,32), (26,27), (25,31), (25,26), (24,30), (24,25), (23,29), (22,28), (22,23), (21,27), (21,22), (20,26), (20,21), (19,25), (19,20), (18,24), (18,19), (17,23), (17,22), (16,23), (16,22), (16,17), (15,21), (15,16), (15,20), (14,21), (14,20), (14,15), (13,19), (13,14), (13,18), (12,19), (12,18), (12,13), (11,17), (10,16), (10,11), (9,15), (9,10), (8,14), (8,9), (7,13), (7,8), (6,12), (6,7), (5,11), (4,10), (4,5), (3,9), (3,4), (3,8), (2,9), (2,8), (2,3), (1,7), (1,2), (0,6), (0,1)] := by
  fin_cases mode <;> simp only [grid_edges_6_0,grid_edges_6_1,grid_edges_6_2]
  all_goals decide +kernel

private theorem vertex_perms_6 : regionalVertexPerms 6 =
    #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35],
      #[30, 31, 32, 33, 34, 35, 24, 25, 26, 27, 28, 29, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5],
      #[5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6, 17, 16, 15, 14, 13, 12, 23, 22, 21, 20, 19, 18, 29, 28, 27, 26, 25, 24, 35, 34, 33, 32, 31, 30],
      #[35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
      #[0, 6, 12, 18, 24, 30, 1, 7, 13, 19, 25, 31, 2, 8, 14, 20, 26, 32, 3, 9, 15, 21, 27, 33, 4, 10, 16, 22, 28, 34, 5, 11, 17, 23, 29, 35],
      #[30, 24, 18, 12, 6, 0, 31, 25, 19, 13, 7, 1, 32, 26, 20, 14, 8, 2, 33, 27, 21, 15, 9, 3, 34, 28, 22, 16, 10, 4, 35, 29, 23, 17, 11, 5],
      #[5, 11, 17, 23, 29, 35, 4, 10, 16, 22, 28, 34, 3, 9, 15, 21, 27, 33, 2, 8, 14, 20, 26, 32, 1, 7, 13, 19, 25, 31, 0, 6, 12, 18, 24, 30],
      #[35, 29, 23, 17, 11, 5, 34, 28, 22, 16, 10, 4, 33, 27, 21, 15, 9, 3, 32, 26, 20, 14, 8, 2, 31, 25, 19, 13, 7, 1, 30, 24, 18, 12, 6, 0]] := by
  rw [regionalVertexPerms_compute]
  decide +kernel

private theorem boundary_perms_6 : regionalPerms 6 =
    #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
      #[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 19, 18, 17, 16],
      #[5, 4, 3, 2, 1, 0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6],
      #[10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      #[0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
      #[15, 16, 17, 18, 19, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
      #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 1, 2, 3, 4],
      #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 19, 18, 17, 16, 15, 14, 13, 12, 11]] := by
  unfold regionalPerms
  rw [vertex_perms_6]
  decide +kernel

private theorem permutation_frame_6 : RegionalPermutationFrame 6 := by
  unfold RegionalPermutationFrame
  rw [vertex_perms_6,boundary_perms_6]
  decide +kernel

end

private theorem finite_relation_reflection {A : Type} [Finite A]
    (R : A → A → Prop) (f : A → A) (hf : Function.Injective f)
    (hp : ∀ a b, R a b → R (f a) (f b)) (a b : A) :
    R (f a) (f b) ↔ R a b := by
  classical
  let E := {x : A × A // R x.1 x.2}
  let F : E → E := fun x => ⟨(f x.1.1,f x.1.2),hp _ _ x.2⟩
  have hi : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact Prod.ext (hf (congrArg Prod.fst h')) (hf (congrArg Prod.snd h'))
  constructor
  · intro h
    obtain ⟨⟨⟨c,d⟩,hcd⟩,h⟩ := Finite.surjective_of_injective hi ⟨(f a,f b),h⟩
    have h' := congrArg Subtype.val h
    have hc : c = a := hf (congrArg Prod.fst h')
    have hd : d = b := hf (congrArg Prod.snd h')
    simpa only [hc,hd] using hcd
  · exact hp a b

private theorem edgeMember_symm (es : List Edge) (a b : Nat) :
    edgeMember es a b = edgeMember es b a := by
  simp only [edgeMember,or_comm]

private theorem regional_filter_preserves (m : Nat)
    (t : Fin (regionalVertexPerms m).size) (mode : Fin 3) (a b : Nat)
    (h : edgeMember (gridEdges m mode.val) a b = true) :
    edgeMember (gridEdges m mode.val)
      ((regionalVertexPerms m)[t.val]!)[ a]! ((regionalVertexPerms m)[t.val]!)[ b]! = true := by
  let p := (regionalVertexPerms m)[t.val]!
  have hm : p ∈ regionalVertexPerms m := by
    dsimp [p]
    rw [getElem!_pos (regionalVertexPerms m) t.val t.isLt]
    exact Array.getElem_mem t.isLt
  have hc := (Array.mem_filter.mp hm).2
  have hc' := (Bool.and_eq_true _ _).mp hc
  have hg := List.all_eq_true.mp hc'.2 mode.val (List.mem_range.mpr mode.isLt)
  have hp := List.all_eq_true.mp hg
  have h' : (a,b) ∈ gridEdges m mode.val ∨ (b,a) ∈ gridEdges m mode.val := of_decide_eq_true h
  rcases h' with h' | h'
  · exact hp (a,b) h'
  · rw [edgeMember_symm]
    exact hp (b,a) h'

/-- The filter's genuine preservation becomes an adjacency iff on a finite bijection. -/
theorem regionalPermutationData (m : Nat) (hm : RegionalSize m) : RegionalPermutationData m := by
  have hframe : RegionalPermutationFrame m := by
    rcases hm with rfl | rfl | rfl
    · exact permutation_frame_2
    · exact permutation_frame_4
    · exact permutation_frame_6
  refine ⟨hframe.1,?_⟩
  intro t
  obtain ⟨hs,hq,hb,hi,hqb,hqi,hcomm⟩ := hframe.2 t
  refine ⟨hs,hq,hb,hi,?_,hqb,hqi,hcomm⟩
  intro mode a b
  let f : Fin (m*m) → Fin (m*m) := fun a => ⟨((regionalVertexPerms m)[t.val]!)[ a.val]!,hb a⟩
  have hf : Function.Injective f := by
    intro a b h
    exact hi a b (congrArg Fin.val h)
  have he := finite_relation_reflection
    (fun a b : Fin (m*m) => edgeMember (gridEdges m mode.val) a.val b.val = true)
    f hf (fun a b h => regional_filter_preserves m t mode a.val b.val h) a b
  cases h1 : edgeMember (gridEdges m mode.val) a.val b.val <;>
    cases h2 : edgeMember (gridEdges m mode.val)
      ((regionalVertexPerms m)[t.val]!)[ a.val]! ((regionalVertexPerms m)[t.val]!)[ b.val]! <;>
    simp_all only [f,Bool.false_eq_true,iff_false,not_true_eq_false,iff_true]

private theorem regional_square_coordinates (a b : Vertex) : square.Adj a b ↔
    (b.1=a.1+1 ∧ b.2=a.2) ∨ (a.1=b.1+1 ∧ a.2=b.2) ∨
    (b.1=a.1 ∧ b.2=a.2+1) ∨ (a.1=b.1 ∧ a.2=b.2+1) := by
  simp only [square,SimpleGraph.fromRel_adj,ne_eq,Prod.ext_iff]
  omega

private theorem regional_diagonal_coordinates (keep : Vertex → Prop) (a b : Vertex) :
    (SimpleGraph.fromRel (diagonalRelation keep)).Adj a b ↔
    (b.1=a.1+1 ∧ b.2=a.2+1 ∧ (a.1+a.2)%2=0 ∧ keep a) ∨
    (a.1=b.1+1 ∧ a.2=b.2+1 ∧ (b.1+b.2)%2=0 ∧ keep b) ∨
    (b.1=a.1+1 ∧ a.2=b.2+1 ∧ (a.1+b.2)%2=0 ∧ keep (a.1,b.2)) ∨
    (a.1=b.1+1 ∧ b.2=a.2+1 ∧ (b.1+a.2)%2=0 ∧ keep (b.1,a.2)) := by
  constructor
  · rintro ⟨_,h|h⟩
    · rcases h with ⟨z,hz,hk,hd|hd⟩
      · rcases hd with ⟨rfl,rfl⟩
        exact Or.inl ⟨rfl,rfl,hz,hk⟩
      · rcases hd with ⟨rfl,rfl⟩
        exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl,hz,hk⟩))
    · rcases h with ⟨z,hz,hk,hd|hd⟩
      · rcases hd with ⟨rfl,rfl⟩
        exact Or.inr (Or.inl ⟨rfl,rfl,hz,hk⟩)
      · rcases hd with ⟨rfl,rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hz,hk⟩))
  · intro h
    have hn : a ≠ b := by
      intro he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      rcases h with h|h|h|h <;> omega
    refine ⟨hn,?_⟩
    rcases h with h|h|h|h
    · exact Or.inl ⟨a,h.2.2.1,h.2.2.2,Or.inl ⟨rfl,Prod.ext h.1 h.2.1⟩⟩
    · exact Or.inr ⟨b,h.2.2.1,h.2.2.2,Or.inl ⟨rfl,Prod.ext h.1 h.2.1⟩⟩
    · refine Or.inr ⟨(a.1,b.2),h.2.2.1,h.2.2.2,Or.inr ⟨?_,?_⟩⟩
      · apply Prod.ext <;> dsimp <;> omega
      · apply Prod.ext <;> dsimp <;> omega
    · refine Or.inl ⟨(b.1,a.2),h.2.2.1,h.2.2.2,Or.inr ⟨?_,?_⟩⟩
      · apply Prod.ext <;> dsimp <;> omega
      · apply Prod.ext <;> dsimp <;> omega

/-- The square graph commutes with row-major coordinates, at every shift and tile. -/
theorem tileGraph_square_rowMajor (m : Nat) (shift i : Vertex) (a b : Fin (m*m)) :
    (tileGraph square m shift i).Adj (rowMajor m a) (rowMajor m b) ↔
      regionalSquareAdj m a b := by
  simp only [tileGraph,SimpleGraph.comap_adj,regional_square_coordinates,embed,
    rowMajor_fst,rowMajor_snd,regionalSquareAdj]
  omega

private theorem stage1_line_coordinates (a b : Fin 36) :
    (tileGraph lineLattice 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      regionalAdj 6 1 a b := by
  simp only [tileGraph,SimpleGraph.comap_adj,lineLattice,decorated,
    SimpleGraph.sup_adj,regional_square_coordinates,regional_diagonal_coordinates,embed,
    rowMajor_fst,rowMajor_snd,regionalAdj,regionalSquareAdj,regionalKeep]
  norm_num

private theorem stage1_intermediate_coordinates (a b : Fin 36) :
    (tileGraph intermediate 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      regionalAdj 6 0 a b := by
  have haX := Nat.mod_lt a.val (show 0 < 6 by decide)
  have hbX := Nat.mod_lt b.val (show 0 < 6 by decide)
  have haY : a.val/6 < 6 := by omega
  have hbY : b.val/6 < 6 := by omega
  simp only [tileGraph,SimpleGraph.comap_adj,intermediate,decorated,
    SimpleGraph.sup_adj,regional_square_coordinates,regional_diagonal_coordinates,embed,
    rowMajor_fst,rowMajor_snd,regionalAdj,regionalSquareAdj,regionalKeep]
  norm_num
  omega

private theorem stage2_intermediate_coordinates (a b : Fin 36) :
    (tileGraph intermediate 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      regionalAdj 6 2 a b := by
  simp only [tileGraph,SimpleGraph.comap_adj,intermediate,decorated,
    SimpleGraph.sup_adj,regional_square_coordinates,regional_diagonal_coordinates,embed,
    rowMajor_fst,rowMajor_snd,regionalAdj,regionalSquareAdj,regionalKeep]
  norm_num
  repeat' first | apply or_congr | apply and_congr
  all_goals omega

private theorem stage2_square_coordinates (a b : Fin 36) :
    (tileGraph square 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      regionalAdj 6 0 a b := by
  rw [tileGraph_square_rowMajor]
  simp [regionalAdj,regionalKeep]

section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem grid_coordinates_2 (mode : Fin 3) (a b : Fin 4) :
    (edgeGraph 4 (gridEdges 2 mode.val)).Adj a b ↔ regionalAdj 2 mode.val a b := by
  fin_cases mode <;> fin_cases a <;>
    simp only [grid_edges_2_0,grid_edges_2_1,grid_edges_2_2,edgeGraph,
      SimpleGraph.fromRel_adj,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,
      regionalAdj,regionalSquareAdj,regionalKeep,Fin.val_mk] <;>
    norm_num <;> omega


end

/-- The proved stage-coordinate layer; finite edge-list identification is separate. -/
theorem regional_stage6_coordinate_semantics (a b : Fin 36) :
    ((tileGraph lineLattice 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔ regionalAdj 6 1 a b) ∧
    ((tileGraph intermediate 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔ regionalAdj 6 0 a b) ∧
    ((tileGraph intermediate 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔ regionalAdj 6 2 a b) ∧
    ((tileGraph square 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔ regionalAdj 6 0 a b) :=
  ⟨stage1_line_coordinates a b,stage1_intermediate_coordinates a b,
    stage2_intermediate_coordinates a b,stage2_square_coordinates a b⟩

/-- The actual finite boundary index, as a bounded vertex of the region. -/
def regionalBoundaryVertex (m : Nat) (hm : RegionalSize m)
    (i : Fin (squareBoundary m).size) : Fin (m*m) :=
  ⟨(squareBoundary m)[i.val]!, (regionalBoundaryData m hm).2.2.1 i⟩

/-- The actual boundary array, viewed in Base cell coordinates. -/
def regionalBoundaryMap (m : Nat) (hm : RegionalSize m)
    (i : Fin (squareBoundary m).size) : Boundary m := by
  refine ⟨rowMajor m (regionalBoundaryVertex m hm i),?_⟩
  apply (regionalBoundaryData m hm).2.2.2 (regionalBoundaryVertex m hm i) |>.mp
  dsimp [regionalBoundaryVertex]
  rw [getElem!_pos (squareBoundary m) i.val i.isLt]
  exact Array.getElem_mem_toList i.isLt

@[simp] theorem regionalBoundaryMap_index (m : Nat) (hm : RegionalSize m)
    (i : Fin (squareBoundary m).size) :
    ((rowMajor m).symm (regionalBoundaryMap m hm i).val).val = (squareBoundary m)[i.val]! := by
  simp only [regionalBoundaryMap,Equiv.symm_apply_apply,regionalBoundaryVertex]

theorem regionalBoundaryMap_bijective (m : Nat) (hm : RegionalSize m) :
    Function.Bijective (regionalBoundaryMap m hm) := by
  constructor
  · intro i j h
    have hv := congrArg (fun b : Boundary m => ((rowMajor m).symm b.val).val) h
    simp only [regionalBoundaryMap_index] at hv
    apply Fin.ext
    apply ((regionalBoundaryData m hm).2.1.getElem_inj_iff
      (i := i.val) (j := j.val)
      (hi := by simpa only [Array.length_toList] using i.isLt)
      (hj := by simpa only [Array.length_toList] using j.isLt)).mp
    simpa only [getElem!_pos (squareBoundary m) i.val i.isLt,
      getElem!_pos (squareBoundary m) j.val j.isLt,Array.getElem_toList] using hv
  · intro b
    let v := (rowMajor m).symm b.val
    have hv : rowPerimeter m v := by
      simpa only [v,rowPerimeter,Equiv.apply_symm_apply] using b.property
    have hmem := ((regionalBoundaryData m hm).2.2.2 v).mpr hv
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hmem
    have hi' : i < (squareBoundary m).size := by simpa only [Array.length_toList] using hi
    refine ⟨⟨i,hi'⟩,?_⟩
    apply Subtype.ext
    apply (rowMajor m).symm.injective
    apply Fin.ext
    simpa only [regionalBoundaryMap_index,getElem!_pos (squareBoundary m) i hi',
      Array.getElem_toList] using he

noncomputable def regionalBoundaryEquiv (m : Nat) (hm : RegionalSize m) :
    Fin (squareBoundary m).size ≃ Boundary m :=
  Equiv.ofBijective (regionalBoundaryMap m hm) (regionalBoundaryMap_bijective m hm)

@[simp] theorem regionalBoundaryEquiv_index (m : Nat) (hm : RegionalSize m)
    (i : Fin (squareBoundary m).size) :
    ((rowMajor m).symm (regionalBoundaryEquiv m hm i).val).val = (squareBoundary m)[i.val]! :=
  regionalBoundaryMap_index m hm i

/-- Exactly the actual twenty-entry traversal, in its stored order. -/
noncomputable def boundaryEquiv6 : Fin 20 ≃ Boundary 6 :=
  (finCongr (show 20 = (squareBoundary 6).size by decide +kernel)).trans
    (regionalBoundaryEquiv 6 (Or.inr (Or.inr rfl)))

@[simp] theorem boundaryEquiv6_index (i : Fin 20) :
    ((rowMajor 6).symm (boundaryEquiv6 i).val).val = (squareBoundary 6)[i.val]! := by
  exact regionalBoundaryEquiv_index 6 _ _

theorem regionalBoundaryEquivalence (m : Nat) (hm : RegionalSize m) :
    ∃ e : Fin (squareBoundary m).size ≃ Boundary m,
      ∀ i, ((rowMajor m).symm (e i).val).val = (squareBoundary m)[i.val]! :=
  ⟨regionalBoundaryEquiv m hm,regionalBoundaryEquiv_index m hm⟩

noncomputable def regionalVertexEquiv (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) : Equiv.Perm (Fin (m*m)) := by
  let h := (regionalPermutationData m hm).2 t
  let f : Fin (m*m) → Fin (m*m) := fun a => ⟨((regionalVertexPerms m)[t.val]!)[a.val]!,h.2.2.1 a⟩
  have hf : Function.Injective f := fun a b e => h.2.2.2.1 a b (congrArg Fin.val e)
  exact Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩

noncomputable def regionalBoundaryIndexEquiv (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) : Equiv.Perm (Fin (squareBoundary m).size) := by
  let h := (regionalPermutationData m hm).2 t
  let f : Fin (squareBoundary m).size → Fin (squareBoundary m).size :=
    fun a => ⟨((regionalPerms m)[t.val]!)[a.val]!,h.2.2.2.2.2.1 a⟩
  have hf : Function.Injective f := fun a b e => h.2.2.2.2.2.2.1 a b (congrArg Fin.val e)
  exact Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩

@[simp] theorem regionalVertexEquiv_apply (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) (a : Fin (m*m)) :
    (regionalVertexEquiv m hm t a).val = ((regionalVertexPerms m)[t.val]!)[a.val]! := rfl

@[simp] theorem regionalBoundaryIndexEquiv_apply (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) (a : Fin (squareBoundary m).size) :
    (regionalBoundaryIndexEquiv m hm t a).val = ((regionalPerms m)[t.val]!)[a.val]! := rfl

/-- This type is definitionally the codec's `RepresentsPermutation` contract. -/
theorem regionalBoundaryIndexEquiv_represents (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) :
    ((regionalPerms m)[t.val]!).size = (squareBoundary m).size ∧
      ∀ a, ((regionalPerms m)[t.val]!)[a.val]! = (regionalBoundaryIndexEquiv m hm t a).val :=
  ⟨((regionalPermutationData m hm).2 t).2.1,fun _ => rfl⟩

private theorem edgeGraph_adj_edgeMember (n : Nat) (es : List Edge) (a b : Fin n) :
    (edgeGraph n es).Adj a b ↔ a ≠ b ∧ edgeMember es a.val b.val = true := by
  simp [edgeGraph,SimpleGraph.fromRel_adj,edgeMember]

theorem regionalVertexEquiv_adj (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) (mode : Fin 3) (a b : Fin (m*m)) :
    (edgeGraph (m*m) (gridEdges m mode.val)).Adj
      (regionalVertexEquiv m hm t a) (regionalVertexEquiv m hm t b) ↔
    (edgeGraph (m*m) (gridEdges m mode.val)).Adj a b := by
  rw [edgeGraph_adj_edgeMember,edgeGraph_adj_edgeMember]
  simp only [regionalVertexEquiv_apply]
  rw [←((regionalPermutationData m hm).2 t).2.2.2.2.1 mode a b]
  constructor
  · rintro ⟨h,he⟩
    exact ⟨fun hab => h (congrArg (regionalVertexEquiv m hm t) hab),he⟩
  · rintro ⟨h,he⟩
    exact ⟨fun hab => h ((regionalVertexEquiv m hm t).injective hab),he⟩

noncomputable def regionalGraphIso (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) (mode : Fin 3) :
    edgeGraph (m*m) (gridEdges m mode.val) ≃g edgeGraph (m*m) (gridEdges m mode.val) where
  toEquiv := regionalVertexEquiv m hm t
  map_rel_iff' := regionalVertexEquiv_adj m hm t mode _ _

/-- The induced boundary permutation commutes with the actual traversal. -/
theorem regional_boundary_commutes (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) (b : Fin (squareBoundary m).size) :
    regionalVertexEquiv m hm t (regionalBoundaryVertex m hm b) =
      regionalBoundaryVertex m hm (regionalBoundaryIndexEquiv m hm t b) := by
  apply Fin.ext
  simp only [regionalVertexEquiv_apply,regionalBoundaryVertex,
    regionalBoundaryIndexEquiv_apply]
  exact ((regionalPermutationData m hm).2 t).2.2.2.2.2.2.2 b

theorem regionalPermutationWitnesses (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) :
    ∃ e : Equiv.Perm (Fin (m*m)), ∃ f : Equiv.Perm (Fin (squareBoundary m).size),
      ((regionalVertexPerms m)[t.val]!).size = m*m ∧
      ((regionalPerms m)[t.val]!).size = (squareBoundary m).size ∧
      (∀ a, ((regionalVertexPerms m)[t.val]!)[a.val]! = (e a).val) ∧
      (∀ b, ((regionalPerms m)[t.val]!)[b.val]! = (f b).val) ∧
      (∀ (mode : Fin 3) a b, (edgeGraph (m*m) (gridEdges m mode.val)).Adj (e a) (e b) ↔
        (edgeGraph (m*m) (gridEdges m mode.val)).Adj a b) :=
  ⟨regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t,
    ((regionalPermutationData m hm).2 t).1,((regionalPermutationData m hm).2 t).2.1,
    (fun _ => rfl),(fun _ => rfl),regionalVertexEquiv_adj m hm t⟩

/-- A pure bit-vector encoder; bit k records the kth Boolean. -/
def regionalBooleanMask (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => regionalBooleanMask f n ||| (if f n then 2^n else 0)

/-- The whole symmetric edge relation, with pair code n*u+v. -/
def regionalEdgeMask (n : Nat) : List Edge → Nat
  | [] => 0
  | (u,v)::es => regionalEdgeMask n es ||| 2^(n*u+v) ||| 2^(n*v+u)

/-- Pair decoding is a finite equivalence, not an unchecked table. -/
def regionalPair6 (k : Nat) : Fin 36 × Fin 36 :=
  finProdFinEquiv.symm ⟨k % 1296, Nat.mod_lt _ (by decide)⟩

/-- Coordinate relation encoded once, independently of the edge list. -/
def regionalCoordinateMask6 (mode : Nat) : Nat :=
  regionalBooleanMask
    (fun k => decide (regionalAdj 6 mode (regionalPair6 k).1 (regionalPair6 k).2)) 1296

private theorem booleanMask_testBit (f : Nat → Bool) (n i : Nat) :
    (regionalBooleanMask f n).testBit i = (decide (i<n) && f i) := by
  induction n with
  | zero => simp [regionalBooleanMask]
  | succ n ih =>
    rw [regionalBooleanMask,Nat.testBit_or,ih]
    by_cases h : i = n
    · subst i
      cases hf : f n <;> simp [hf,Nat.testBit_two_pow]
    · have hn : n ≠ i := Ne.symm h
      have hh : i<n+1 ↔ i<n := by omega
      cases hf : f n <;> simp [hf,Nat.testBit_two_pow,hn,hh]

private theorem edgeMask_testBit (n : Nat) (es : List Edge) (k : Nat) :
    (regionalEdgeMask n es).testBit k = true ↔
      ∃ e ∈ es, n*e.1+e.2 = k ∨ n*e.2+e.1 = k := by
  induction es with
  | nil => simp [regionalEdgeMask]
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    simp only [regionalEdgeMask,Nat.testBit_or,Nat.testBit_two_pow,
      Bool.or_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ((h|h)|h)
      · obtain ⟨e,he,hd⟩ := h
        exact ⟨e,List.mem_cons_of_mem _ he,hd⟩
      · exact ⟨(u,v),List.mem_cons_self,Or.inl h⟩
      · exact ⟨(u,v),List.mem_cons_self,Or.inr h⟩
    · rintro ⟨e,he,hd⟩
      rcases List.mem_cons.mp he with rfl|he
      · rcases hd with h|h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl ⟨e,he,hd⟩)

private theorem pair_code_eq {n : Nat} (u v a b : Fin n) :
    n*u.val+v.val = n*a.val+b.val ↔ u=a ∧ v=b := by
  constructor
  · intro h
    have hp : (finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n)) (u,v) =
        finProdFinEquiv (a,b) := by
      apply Fin.ext
      change v.val+n*u.val = b.val+n*a.val
      omega
    exact Prod.mk.inj (finProdFinEquiv.injective hp)
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem edgeMask_edgeMember (n : Nat) (es : List Edge)
    (hb : BoundedEdges n es) (a b : Fin n) :
    (regionalEdgeMask n es).testBit (n*a.val+b.val) = true ↔
      edgeMember es a.val b.val = true := by
  rw [edgeMask_testBit]
  simp only [edgeMember,decide_eq_true_eq]
  constructor
  · rintro ⟨e,he,h|h⟩
    · have h' := (pair_code_eq ⟨e.1,(hb e he).1⟩ ⟨e.2,(hb e he).2⟩ a b).mp h
      have heq : e = (a.val,b.val) := Prod.ext (congrArg Fin.val h'.1) (congrArg Fin.val h'.2)
      exact Or.inl (heq ▸ he)
    · have h' := (pair_code_eq ⟨e.2,(hb e he).2⟩ ⟨e.1,(hb e he).1⟩ a b).mp h
      have heq : e = (b.val,a.val) := Prod.ext (congrArg Fin.val h'.2) (congrArg Fin.val h'.1)
      exact Or.inr (heq ▸ he)
  · rintro (h|h)
    · exact ⟨(a.val,b.val),h,Or.inl rfl⟩
    · exact ⟨(b.val,a.val),h,Or.inr rfl⟩

private theorem coordinateMask_testBit (mode : Nat) (a b : Fin 36) :
    (regionalCoordinateMask6 mode).testBit (36*a.val+b.val) =
      decide (regionalAdj 6 mode a b) := by
  let k : Fin 1296 := finProdFinEquiv (a,b)
  have hk : k.val = 36*a.val+b.val := by
    change b.val+36*a.val = 36*a.val+b.val
    omega
  have hp : regionalPair6 k.val = (a,b) := by
    have hFin : (⟨k.val % 1296,Nat.mod_lt _ (by decide)⟩ : Fin 1296) = k :=
      Fin.ext (Nat.mod_eq_of_lt k.isLt)
    exact (congrArg (fun i : Fin 1296 => (finProdFinEquiv.symm i : Fin 36 × Fin 36)) hFin).trans
      (Equiv.symm_apply_apply _ (a,b))
  rw [←hk,regionalCoordinateMask6,booleanMask_testBit]
  simp only [k.isLt,decide_true,Bool.true_and,hp]

private theorem grid6_edges_bounded (mode : Fin 3) : BoundedEdges 36 (gridEdges 6 mode.val) := by
  have h : (gridEdges 6 mode.val).all (fun e => decide (e.1<36 ∧ e.2<36)) = true := by
    fin_cases mode <;> decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem regional_grid6_mask_exact (mode : Fin 3) :
    regionalEdgeMask 36 (gridEdges 6 mode.val) = regionalCoordinateMask6 mode.val := by
  fin_cases mode <;> decide +kernel

private theorem regionalAdj_ne {m mode : Nat} {a b : Fin (m*m)}
    (h : regionalAdj m mode a b) : a ≠ b := by
  intro he
  subst b
  simpa [regionalAdj,regionalSquareAdj] using h

theorem regional_grid6_coordinate_bridge (mode : Fin 3) (a b : Fin 36) :
    (edgeGraph 36 (gridEdges 6 mode.val)).Adj a b ↔ regionalAdj 6 mode.val a b := by
  have hbits := congrArg (fun z : Nat => z.testBit (36*a.val+b.val))
    (regional_grid6_mask_exact mode)
  have hrel : edgeMember (gridEdges 6 mode.val) a.val b.val = true ↔ regionalAdj 6 mode.val a b := by
    rw [←edgeMask_edgeMember 36 _ (grid6_edges_bounded mode) a b,
      hbits,coordinateMask_testBit,decide_eq_true_eq]
  have hgraph : (edgeGraph 36 (gridEdges 6 mode.val)).Adj a b ↔
      a ≠ b ∧ edgeMember (gridEdges 6 mode.val) a.val b.val = true := by
    simp [edgeGraph,SimpleGraph.fromRel_adj,edgeMember]
  rw [hgraph]
  exact ⟨fun h => hrel.mp h.2,fun h => ⟨regionalAdj_ne h,hrel.mpr h⟩⟩

/-- The original four concrete stage-graph obligations, with no graph-equivalence premise. -/
theorem regional_graph6_bridge (a b : Fin 36) :
    ((tileGraph lineLattice 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      (edgeGraph 36 (gridEdges 6 1)).Adj a b) ∧
    ((tileGraph intermediate 6 (0,0) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      (edgeGraph 36 (gridEdges 6 0)).Adj a b) ∧
    ((tileGraph intermediate 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      (edgeGraph 36 (gridEdges 6 2)).Adj a b) ∧
    ((tileGraph square 6 (3,3) (0,0)).Adj (rowMajor 6 a) (rowMajor 6 b) ↔
      (edgeGraph 36 (gridEdges 6 0)).Adj a b) :=
  ⟨((regional_stage6_coordinate_semantics a b).1).trans
      (regional_grid6_coordinate_bridge 1 a b).symm,
   ((regional_stage6_coordinate_semantics a b).2.1).trans
      (regional_grid6_coordinate_bridge 0 a b).symm,
   ((regional_stage6_coordinate_semantics a b).2.2.1).trans
      (regional_grid6_coordinate_bridge 2 a b).symm,
   ((regional_stage6_coordinate_semantics a b).2.2.2).trans
      (regional_grid6_coordinate_bridge 0 a b).symm⟩

#print axioms regionalBoundaryData
#print axioms regionalPermutationData
#print axioms regional_stage6_coordinate_semantics
#print axioms regionalBoundaryEquivalence
#print axioms regionalPermutationWitnesses
#print axioms regional_grid6_mask_exact
#print axioms regional_grid6_coordinate_bridge
#print axioms regional_graph6_bridge

end SitePerc.Checker
