import SitePerc.Checker.RegionalGeometry

/-! The actual listed regional permutation pairs form their generated subgroup. -/

set_option autoImplicit false

namespace SitePerc.Checker

/-- Pointwise finite data for identity and composition of the actual pair arrays. -/
private def OrbitArrayClosure (m : Nat) (ps qs : Array (Array Nat)) : Prop :=
  (∃ t : Fin ps.size,
    (∀ a : Fin (m*m), (ps[t.val]!)[a.val]! = a.val) ∧
    (∀ b : Fin (squareBoundary m).size, (qs[t.val]!)[b.val]! = b.val)) ∧
  (∀ s t : Fin ps.size, ∃ u : Fin ps.size,
    (∀ a : Fin (m*m), (ps[u.val]!)[a.val]! = (ps[s.val]!)[(ps[t.val]!)[a.val]!]!) ∧
    (∀ b : Fin (squareBoundary m).size,
      (qs[u.val]!)[b.val]! = (qs[s.val]!)[(qs[t.val]!)[b.val]!]!))

private instance (m : Nat) (ps qs : Array (Array Nat)) :
    Decidable (OrbitArrayClosure m ps qs) := by
  unfold OrbitArrayClosure
  infer_instance

/-- Replace the implementation's well-founded sort only by a proved equality. -/
private theorem orbit_vertex_perms_compute (m : Nat) : regionalVertexPerms m =
    (candidateVertexPerms m).filter (fun p =>
      (p.toList.insertionSort (· ≤ ·) == List.range (m*m)) &&
      (List.range 3).all (fun mode => (gridEdges m mode).all fun (u,v) =>
        edgeMember (gridEdges m mode) p[u]! p[v]!)) := by
  have hc : commonAutomorphism m =
      (fun p => (p.toList.insertionSort (· ≤ ·) == List.range (m*m)) &&
        (List.range 3).all (fun mode => (gridEdges m mode).all fun (u,v) =>
          edgeMember (gridEdges m mode) p[u]! p[v]!)) := by
    funext p
    unfold commonAutomorphism
    rw [List.mergeSort_eq_insertionSort]
  unfold regionalVertexPerms
  rw [hc]

section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem orbit_vertex_perms_2 : regionalVertexPerms 2 = candidateVertexPerms 2 := by
  rw [orbit_vertex_perms_compute]
  decide +kernel

private theorem orbit_vertex_perms_4 : regionalVertexPerms 4 =
    #[(candidateVertexPerms 4)[0]!, (candidateVertexPerms 4)[4]!] := by
  rw [orbit_vertex_perms_compute]
  decide +kernel

private theorem orbit_vertex_perms_6 : regionalVertexPerms 6 = candidateVertexPerms 6 := by
  rw [orbit_vertex_perms_compute]
  decide +kernel

private theorem orbit_boundary_perms_compute (m : Nat) : regionalPerms m =
    (regionalVertexPerms m).map (fun p => (squareBoundary m).map
      (fun v => (squareBoundary m).toList.idxOf p[v]!)) := rfl

private theorem orbit_array_closure_2 :
    OrbitArrayClosure 2 (regionalVertexPerms 2) (regionalPerms 2) := by
  rw [orbit_boundary_perms_compute,orbit_vertex_perms_2]
  decide +kernel

private theorem orbit_array_closure_4 :
    OrbitArrayClosure 4 (regionalVertexPerms 4) (regionalPerms 4) := by
  rw [orbit_boundary_perms_compute,orbit_vertex_perms_4]
  decide +kernel

private theorem orbit_array_closure_6 :
    OrbitArrayClosure 6 (regionalVertexPerms 6) (regionalPerms 6) := by
  rw [orbit_boundary_perms_compute,orbit_vertex_perms_6]
  decide +kernel

end

private theorem orbit_array_closure (m : Nat) (hm : RegionalSize m) :
    OrbitArrayClosure m (regionalVertexPerms m) (regionalPerms m) := by
  rcases hm with rfl | rfl | rfl
  · exact orbit_array_closure_2
  · exact orbit_array_closure_4
  · exact orbit_array_closure_6

/-- The identity is one of the actual listed pairs. -/
theorem regional_list_one (m : Nat) (hm : RegionalSize m) :
    ∃ t : Fin (regionalVertexPerms m).size,
      (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t) = 1 := by
  obtain ⟨t,hv,hb⟩ := (orbit_array_closure m hm).1
  refine ⟨t,Prod.ext ?_ ?_⟩
  · apply Equiv.ext
    intro a
    apply Fin.ext
    change (regionalVertexEquiv m hm t a).val = a.val
    simpa only [regionalVertexEquiv_apply] using hv a
  · apply Equiv.ext
    intro b
    apply Fin.ext
    change (regionalBoundaryIndexEquiv m hm t b).val = b.val
    simpa only [regionalBoundaryIndexEquiv_apply] using hb b

/-- Composition of the actual listed pairs is again an actual listed pair. -/
theorem regional_list_mul (m : Nat) (hm : RegionalSize m)
    (s t : Fin (regionalVertexPerms m).size) :
    ∃ u : Fin (regionalVertexPerms m).size,
      (regionalVertexEquiv m hm u,regionalBoundaryIndexEquiv m hm u) =
      (regionalVertexEquiv m hm s,regionalBoundaryIndexEquiv m hm s) *
      (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t) := by
  obtain ⟨u,hv,hb⟩ := (orbit_array_closure m hm).2 s t
  refine ⟨u,Prod.ext ?_ ?_⟩
  · apply Equiv.ext
    intro a
    apply Fin.ext
    change (regionalVertexEquiv m hm u a).val =
      (regionalVertexEquiv m hm s (regionalVertexEquiv m hm t a)).val
    simpa only [regionalVertexEquiv_apply] using hv a
  · apply Equiv.ext
    intro b
    apply Fin.ext
    change (regionalBoundaryIndexEquiv m hm u b).val =
      (regionalBoundaryIndexEquiv m hm s (regionalBoundaryIndexEquiv m hm t b)).val
    simpa only [regionalBoundaryIndexEquiv_apply] using hb b

/-- Finite identity/multiplication closure implies inverse closure, by finite surjectivity. -/
private theorem orbit_finite_inv_closed {G : Type} [Group G] [Finite G]
    (S : Set G) (hone : 1 ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a*b ∈ S)
    (a : G) (ha : a ∈ S) : a⁻¹ ∈ S := by
  let f : S → S := fun x => ⟨a*x.val,hmul a ha x.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective hf ⟨1,hone⟩
  have hprod : a*x.val = 1 := congrArg Subtype.val hx
  have he : x.val = a⁻¹ := by
    calc
      x.val = a⁻¹*(a*x.val) := by simp only [←mul_assoc,inv_mul_cancel,one_mul]
      _ = a⁻¹ := by rw [hprod,mul_one]
  exact he ▸ x.property

/-- Inverses of the actual listed pairs are again actual listed pairs. -/
theorem regional_list_inv (m : Nat) (hm : RegionalSize m)
    (t : Fin (regionalVertexPerms m).size) :
    ∃ u : Fin (regionalVertexPerms m).size,
      (regionalVertexEquiv m hm u,regionalBoundaryIndexEquiv m hm u) =
      (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t)⁻¹ := by
  let F := fun t : Fin (regionalVertexPerms m).size =>
    (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t)
  have h1 : 1 ∈ Set.range F := regional_list_one m hm
  have hmul : ∀ a ∈ Set.range F, ∀ b ∈ Set.range F, a*b ∈ Set.range F := by
    rintro a ⟨s,rfl⟩ b ⟨t,rfl⟩
    exact regional_list_mul m hm s t
  exact orbit_finite_inv_closed (Set.range F) h1 hmul (F t) ⟨t,rfl⟩

/-- The actual canonical list represents every element of its generated group. -/
theorem regional_generated_represented (m : Nat) (hm : RegionalSize m)
    (g : Equiv.Perm (Fin (m*m)) × Equiv.Perm (Fin (squareBoundary m).size))
    (hg : g ∈ Subgroup.closure (Set.range
      (fun t : Fin (regionalVertexPerms m).size =>
        (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t)))) :
    ∃ t, (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t) = g := by
  let S : Subgroup (Equiv.Perm (Fin (m*m)) × Equiv.Perm (Fin (squareBoundary m).size)) :=
    { carrier := Set.range (fun t : Fin (regionalVertexPerms m).size =>
        (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t))
      one_mem' := regional_list_one m hm
      mul_mem' := by
        rintro a b ⟨s,rfl⟩ ⟨t,rfl⟩
        exact regional_list_mul m hm s t
      inv_mem' := by
        rintro a ⟨t,rfl⟩
        exact regional_list_inv m hm t }
  exact ((Subgroup.closure_le S).mpr (show Set.range
      (fun t : Fin (regionalVertexPerms m).size =>
        (regionalVertexEquiv m hm t,regionalBoundaryIndexEquiv m hm t)) ⊆ S from
      fun _ h => h)) hg

#print axioms regional_list_one
#print axioms regional_list_mul
#print axioms regional_list_inv
#print axioms regional_generated_represented

end SitePerc.Checker
