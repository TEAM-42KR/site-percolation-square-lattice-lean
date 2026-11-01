import SitePerc.Checker.StateCodec

/-!
# Sound same-key pruning on Boolean subcubes

The order is pointwise inclusion of open vertices. It is not the numerical order
on binary masks. Every observation is that of the actual finite open graph.
-/

namespace SitePerc.Checker

/-- Pointwise-open inclusion on the actual finite vertex set. -/
def OpenLE (n : Nat) (lo hi : Nat → Bool) : Prop :=
  ∀ i : Fin n, lo i.val = true → hi i.val = true

/-- Boundary bits remain fixed while interior free coordinates vary. -/
def BoundaryFixed {n b : Nat} (v : Fin b → Fin n) (lo hi : Nat → Bool) : Prop :=
  ∀ i, lo (v i).val = hi (v i).val

/-- Opening vertices adds edges to the actual finite open graph. -/
theorem openGraph_mono (n : Nat) (es : List Edge) (lo hi : Nat → Bool)
    (h : OpenLE n lo hi) : openGraph n es lo ≤ openGraph n es hi := by
  intro i j hij
  obtain ⟨hne, he | he⟩ := hij
  · exact ⟨hne, Or.inl ⟨he.1, h i he.2.1, h j he.2.2⟩⟩
  · exact ⟨hne, Or.inr ⟨he.1, h j he.2.1, h i he.2.2⟩⟩

/-- Actual observed augmented states are monotone in pointwise-open inclusion. -/
theorem observedBoundaryState_mono (n b : Nat) (es : List Edge)
    (v : Fin b → Fin n) (lo hi : Nat → Bool) (h : OpenLE n lo hi) :
    stateLE (observedBoundaryState es lo v) (observedBoundaryState es hi v) := by
  classical
  constructor
  · intro i hi
    exact h (v i) hi
  · intro i j _ _ hij
    change decide ((openGraph n es lo).Reachable (v i) (v j)) = true at hij
    change decide ((openGraph n es hi).Reachable (v i) (v j)) = true
    exact decide_eq_true ((of_decide_eq_true hij).mono (openGraph_mono n es lo hi h))

/-- Full reachability observations, including their closed diagonal, are monotone. -/
theorem observedBoundaryState_connected_mono (n b : Nat) (es : List Edge)
    (v : Fin b → Fin n) (lo hi : Nat → Bool) (h : OpenLE n lo hi) (i j : Fin b) :
    (observedBoundaryState es lo v).connected i j = true →
      (observedBoundaryState es hi v).connected i j = true := by
  classical
  intro hij
  change decide ((openGraph n es lo).Reachable (v i) (v j)) = true at hij
  change decide ((openGraph n es hi).Reachable (v i) (v j)) = true
  exact decide_eq_true ((of_decide_eq_true hij).mono (openGraph_mono n es lo hi h))

/-- Equality of endpoint observations forces equality on the whole pointwise subcube. -/
theorem observation_sandwich (n b : Nat) (es : List Edge) (v : Fin b → Fin n)
    (lo ω hi : Nat → Bool) (hlo : OpenLE n lo ω) (hhi : OpenLE n ω hi)
    (heq : observedBoundaryState es lo v = observedBoundaryState es hi v) :
    observedBoundaryState es ω v = observedBoundaryState es lo v := by
  have hforward := observedBoundaryState_mono n b es v lo ω hlo
  have hbackward := observedBoundaryState_mono n b es v ω hi hhi
  change BoundaryState.mk _ _ = BoundaryState.mk _ _
  congr 1
  · funext i
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hw
      have hh := hbackward.1 i hw
      rw [← heq] at hh
      exact hh
    · exact hforward.1 i
  · funext i j
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hw
      have hh := observedBoundaryState_connected_mono n b es v ω hi hhi i j hw
      rw [← heq] at hh
      exact hh
    · exact observedBoundaryState_connected_mono n b es v lo ω hlo i j

/-- The fixed-boundary pruning contract, explicitly using a Boolean subcube. -/
theorem subcube_same_state (n b : Nat) (es : List Edge) (v : Fin b → Fin n)
    (lo ω hi : Nat → Bool) (hlo : OpenLE n lo ω) (hhi : OpenLE n ω hi)
    (_hboundary : BoundaryFixed v lo hi)
    (heq : observedBoundaryState es lo v = observedBoundaryState es hi v) :
    observedBoundaryState es ω v = observedBoundaryState es lo v := by
  exact observation_sandwich n b es v lo ω hi hlo hhi heq

/-- First-occurrence deduplication commutes with relabelling injective on this list. -/
theorem eraseDups_map_on (f : Nat → Nat) (xs : List Nat)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).eraseDups = xs.eraseDups.map f := by
  match xs with
  | [] => rfl
  | a :: as =>
    rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons]
    congr 1
    rw [List.filter_map]
    have hfilter : (as.filter fun x => !(f x == f a)) =
        as.filter (fun x => !(x == a)) := by
      apply List.filter_congr
      intro x hx
      have heq : f x = f a ↔ x = a :=
        ⟨hinj x (by simp [hx]) a (by simp), congrArg f⟩
      apply congrArg Bool.not
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using heq
    change ((as.filter fun x => !(f x == f a)).map f).eraseDups = _
    rw [hfilter]
    apply eraseDups_map_on f
    intro x hx y hy hxy
    exact hinj x (by simp [List.mem_filter.mp hx |>.1])
      y (by simp [List.mem_filter.mp hy |>.1]) hxy
termination_by xs.length
decreasing_by
  have h := List.length_filter_le (fun x => !(x == a)) as
  simp only [List.length_cons]
  omega

/-- An injective relabelling preserves each first-occurrence index. -/
theorem idxOf_map_on (f : Nat → Nat) (xs : List Nat) (a : Nat) (ha : a ∈ xs)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, ∀ z ∈ xs, f y = f z → y = z :=
      fun y hy z hz => hinj y (by simp [hy]) z (by simp [hz])
    by_cases hxa : x = a
    · simp [hxa]
    · have hfa : f x ≠ f a := fun h => hxa (hinj x (by simp) a ha h)
      have hat : a ∈ xs := by
        rcases List.mem_cons.mp ha with heq | hat
        · exact False.elim (hxa heq.symm)
        · exact hat
      simpa [List.idxOf_cons, hxa, hfa] using congrArg Nat.succ (ih hat htail)

/-- Normalized labels are invariant under a zero-preserving support-injective relabelling. -/
theorem normalize_map_on (f : Nat → Nat) (xs : List Nat)
    (hzero : ∀ x ∈ xs, f x = 0 ↔ x = 0)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    normalize (xs.map f) = normalize xs := by
  have hfilter : (xs.map f).filter (fun x => x != 0) =
      (xs.filter fun x => x != 0).map f := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x hx
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, bne_iff_ne]
    exact not_congr (hzero x hx)
  have hseen : ((xs.map f).filter (fun x => x != 0)).eraseDups =
      ((xs.filter fun x => x != 0).eraseDups).map f := by
    rw [hfilter]
    apply eraseDups_map_on f
    intro x hx y hy h
    exact hinj x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 h
  simp only [normalize, hseen, List.map_map]
  apply List.map_congr_left
  intro x hx
  change (if f x = 0 then 0 else
      (((xs.filter fun x => x != 0).eraseDups).map f).idxOf (f x) + 1) =
    (if x = 0 then 0 else ((xs.filter fun x => x != 0).eraseDups).idxOf x + 1)
  have hzx := hzero x hx
  by_cases hz : x = 0
  · rw [if_pos (hzx.mpr hz), if_pos hz]
  · have hfz : f x ≠ 0 := fun h => hz (hzx.mp h)
    simp only [hz, hfz, if_false, Function.comp_apply]
    congr 1
    apply idxOf_map_on f
    · simp [hx,hz]
    · intro y hy z hz h
      have hy' : y ∈ xs := (List.mem_filter.mp (List.mem_eraseDups.mp hy)).1
      have hz' : z ∈ xs := (List.mem_filter.mp (List.mem_eraseDups.mp hz)).1
      exact hinj y hy' z hz' h

/-- Equality of augmented label states includes exact equality of closed bits. -/
theorem stateOfLabels_zero_eq_iff (b : Nat) (xs ys : List Nat)
    (heq : stateOfLabels b xs = stateOfLabels b ys) (i : Fin b) :
    xs[i.val]! = 0 ↔ ys[i.val]! = 0 := by
  have h := congrArg (fun s : BoundaryState (Fin b) => s.opened i) heq
  simp only [stateOfLabels, labelState, decide_eq_decide] at h
  exact not_iff_not.mp h

/-- Open/closed bits and genuine connectivity determine all label-equality tests. -/
theorem stateOfLabels_label_eq_iff (b : Nat) (xs ys : List Nat)
    (heq : stateOfLabels b xs = stateOfLabels b ys) (i j : Fin b) :
    xs[i.val]! = xs[j.val]! ↔ ys[i.val]! = ys[j.val]! := by
  have hz := stateOfLabels_zero_eq_iff b xs ys heq
  have hc := congrArg (fun s : BoundaryState (Fin b) => s.connected i j) heq
  simp only [stateOfLabels, labelState, decide_eq_decide] at hc
  by_cases hij : i = j
  · subst j; simp
  · simp only [hij, false_or] at hc
    by_cases hi : xs[i.val]! = 0
    · have hyi := (hz i).mp hi
      simp only [hi, hyi, eq_comm (a := 0)]
      exact hz j
    · have hyi : ys[i.val]! ≠ 0 := fun h => hi ((hz i).mpr h)
      exact ⟨fun h => (hc.mp ⟨hi,h⟩).2, fun h => (hc.mpr ⟨hyi,h⟩).2⟩

/-- Equal augmented states have a zero-preserving injective relabelling of their support. -/
theorem relabel_of_stateOfLabels_eq (b : Nat) (xs ys : List Nat)
    (hx : xs.length = b) (hy : ys.length = b)
    (heq : stateOfLabels b xs = stateOfLabels b ys) :
    ∃ f : Nat → Nat, ys = xs.map f ∧
      (∀ x ∈ xs, f x = 0 ↔ x = 0) ∧
      (∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) := by
  let f : Nat → Nat := fun x => if x = 0 then 0 else ys[xs.idxOf x]!
  have hget (i : Fin b) : f xs[i.val]! = ys[i.val]! := by
    have hix : i.val < xs.length := by omega
    have him : xs[i.val]! ∈ xs := by rw [getElem!_pos xs i.val hix]; exact List.getElem_mem hix
    by_cases hz : xs[i.val]! = 0
    · simpa [f,hz] using ((stateOfLabels_zero_eq_iff b xs ys heq i).mp hz).symm
    · have hk : xs.idxOf xs[i.val]! < xs.length := List.idxOf_lt_length_of_mem him
      let k : Fin b := ⟨xs.idxOf xs[i.val]!, by omega⟩
      have hki : xs[k.val]! = xs[i.val]! := by
        rw [getElem!_pos xs k.val hk]
        exact List.getElem_idxOf hk
      have hyki := (stateOfLabels_label_eq_iff b xs ys heq k i).mp hki
      change (if xs[i.val]! = 0 then 0 else ys[xs.idxOf xs[i.val]!]!) = ys[i.val]!
      rw [if_neg hz]
      exact hyki
  have hm : ys = xs.map f := by
    apply List.ext_getElem
    · simp [hx,hy]
    · intro i hiy hix
      have hi : i < b := by omega
      have hix' : i < xs.length := by omega
      have hh := hget ⟨i,hi⟩
      rw [getElem!_pos xs i hix', getElem!_pos ys i hiy] at hh
      simpa only [List.getElem_map] using hh.symm
  refine ⟨f, hm, ?_, ?_⟩
  · intro x hxm
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hxm
    have hib : i < b := by omega
    rw [← getElem!_pos xs i hi, hget ⟨i,hib⟩]
    exact (stateOfLabels_zero_eq_iff b xs ys heq ⟨i,hib⟩).symm
  · intro x hxm y hym hxy
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hxm
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hym
    have hib : i < b := by omega
    have hjb : j < b := by omega
    rw [← getElem!_pos xs i hi, ← getElem!_pos xs j hj] at hxy ⊢
    rw [hget ⟨i,hib⟩,hget ⟨j,hjb⟩] at hxy
    exact (stateOfLabels_label_eq_iff b xs ys heq ⟨i,hib⟩ ⟨j,hjb⟩).mpr hxy

/-- A complete augmented-state equality gives exactly equal normalized vectors. -/
theorem normalize_eq_of_stateOfLabels_eq (b : Nat) (xs ys : List Nat)
    (hx : xs.length = b) (hy : ys.length = b)
    (heq : stateOfLabels b xs = stateOfLabels b ys) : normalize xs = normalize ys := by
  obtain ⟨f,rfl,hzero,hinj⟩ := relabel_of_stateOfLabels_eq b xs ys hx hy heq
  exact (normalize_map_on f xs hzero hinj).symm

/-- The normalization representative is injective at the level of actual augmented states. -/
theorem normalized_state_injective (b : Nat) (xs ys : List Nat)
    (hx : xs.length = b) (hy : ys.length = b) (hnx : normalize xs = xs)
    (hny : normalize ys = ys) (heq : stateOfLabels b xs = stateOfLabels b ys) : xs = ys := by
  rw [← hnx, ← hny]
  exact normalize_eq_of_stateOfLabels_eq b xs ys hx hy heq

/-- Permuting two equal augmented states preserves their equality. -/
theorem permuted_state_congr (b : Nat) (xs ys : List Nat) (p : Array Nat)
    (e : Equiv.Perm (Fin b)) (hp : RepresentsPermutation b p e)
    (heq : stateOfLabels b xs = stateOfLabels b ys) :
    stateOfLabels b (permute xs p) = stateOfLabels b (permute ys p) := by
  rw [stateOfLabels_permute b xs p e hp, stateOfLabels_permute b ys p e hp, heq]

/-- Exact canonical keys, rather than just decoded relations, respect observation equality. -/
theorem canonicalKey_eq_of_stateOfLabels_eq (b : Nat) (xs ys : List Nat)
    (ps : Array (Array Nat)) (hx : xs.length = b) (hy : ys.length = b)
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin b), RepresentsPermutation b p e)
    (heq : stateOfLabels b xs = stateOfLabels b ys) :
    canonicalKey xs ps = canonicalKey ys ps := by
  have hn := normalize_eq_of_stateOfLabels_eq b xs ys hx hy heq
  have hpkey (p : Array Nat) (hp : p ∈ ps.toList) :
      packR10 (normalize (permute xs p)) = packR10 (normalize (permute ys p)) := by
    obtain ⟨e,hpe⟩ := hps p hp
    apply congrArg packR10
    apply normalize_eq_of_stateOfLabels_eq b
    · simp [permute,hpe.1]
    · simp [permute,hpe.1]
    · exact permuted_state_congr b xs ys p e hpe heq
  have hfold (lst : List (Array Nat)) (hlst : ∀ p ∈ lst, p ∈ ps.toList) (init : Nat) :
      lst.foldl (fun best p => min best (packR10 (normalize (permute xs p)))) init =
      lst.foldl (fun best p => min best (packR10 (normalize (permute ys p)))) init := by
    induction lst generalizing init with
    | nil => rfl
    | cons p lst ih =>
      simp only [List.foldl_cons, hpkey p (hlst p (by simp))]
      exact ih (fun q hq => hlst q (by simp [hq])) _
  unfold canonicalKey
  rw [← Array.foldl_toList, ← Array.foldl_toList, hn]
  exact hfold ps.toList (fun _ h => h) _

/-- Exact normalized-state decoding requires the explicit radix-32 width bound. -/
theorem normalizedPackedKey_decode (b : Nat) (xs : List Nat)
    (hlen : xs.length = b) (hb : b ≤ 31) :
    decodeState b (packR10 (normalize xs)) = stateOfLabels b xs := by
  have hbound : ∀ x ∈ normalize xs, x < 32 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
    have hix : i < xs.length := by simpa using hi
    have hle : (normalize xs)[i]'hi ≤ b := by
      simpa only [hlen] using normalize_lt xs ⟨i,hix⟩
    omega
  have hdecode : r10Labels b (packR10 (normalize xs)) = normalize xs := by
    unfold r10Labels packR10
    have hl : (normalize xs).reverse.length = b := by simp [hlen]
    rw [← hl, unpack_pack _ (by simpa using hbound), List.reverse_reverse]
  rw [decodeState, hdecode, normalize_stateOfLabels b xs hlen]

/-- Valid normalized canonical keys cannot alias a single actual augmented state. -/
theorem validCanonical_decode_injective (b : Nat) (ps : Array (Array Nat)) (src dst : Nat)
    (hs : validCanonical b ps src = true) (ht : validCanonical b ps dst = true)
    (heq : decodeState b src = decodeState b dst) : src = dst := by
  have hsrc := validCanonical_semantics b ps src hs
  have hdst := validCanonical_semantics b ps dst ht
  apply r10Labels_injective_of_lt b src dst hsrc.1 hdst.1
  apply normalized_state_injective b
  · simp [r10Labels]
  · simp [r10Labels]
  · exact hsrc.2.2.1
  · exact hdst.2.2.1
  · exact heq

/-- The actual observed graph state determines the exact normalized UF-label vector. -/
theorem rootLabels_eq_normalized_of_observation_eq (n : Nat) (es : List Edge)
    (boundary : Array Nat) (src dst : Nat) (he : BoundedEdges n es)
    (hb : ∀ x ∈ boundary.toList, x < n)
    (hi : Function.Injective (boundaryEmbedding n boundary hb))
    (heq : observedBoundaryState es src.testBit (boundaryEmbedding n boundary hb) =
      observedBoundaryState es dst.testBit (boundaryEmbedding n boundary hb)) :
    normalize (rootLabels n es boundary src) = normalize (rootLabels n es boundary dst) := by
  apply normalize_eq_of_stateOfLabels_eq boundary.size
  · simp [rootLabels]
  · simp [rootLabels]
  · rw [rootLabels_state_eq_observed n es boundary src he hb hi,
      rootLabels_state_eq_observed n es boundary dst he hb hi, heq]

/-- Every intermediate subcube configuration has exactly the endpoint's normalized labels. -/
theorem subcube_same_normalized_rootLabels (n : Nat) (es : List Edge)
    (boundary : Array Nat) (lo mask hi : Nat) (he : BoundedEdges n es)
    (hb : ∀ x ∈ boundary.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n boundary hb))
    (hlo : OpenLE n lo.testBit mask.testBit) (hhi : OpenLE n mask.testBit hi.testBit)
    (hboundary : BoundaryFixed (boundaryEmbedding n boundary hb) lo.testBit hi.testBit)
    (heq : observedBoundaryState es lo.testBit (boundaryEmbedding n boundary hb) =
      observedBoundaryState es hi.testBit (boundaryEmbedding n boundary hb)) :
    normalize (rootLabels n es boundary mask) = normalize (rootLabels n es boundary lo) := by
  apply rootLabels_eq_normalized_of_observation_eq n es boundary mask lo he hb hinj
  exact subcube_same_state n boundary.size es (boundaryEmbedding n boundary hb)
    lo.testBit mask.testBit hi.testBit hlo hhi hboundary heq

/-- Same-key pruning holds for the exact canonical packed key of every subcube member. -/
theorem subcube_same_canonicalKey (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) (lo mask hi : Nat) (he : BoundedEdges n es)
    (hb : ∀ x ∈ boundary.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n boundary hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin boundary.size),
      RepresentsPermutation boundary.size p e)
    (hlo : OpenLE n lo.testBit mask.testBit) (hhi : OpenLE n mask.testBit hi.testBit)
    (hboundary : BoundaryFixed (boundaryEmbedding n boundary hb) lo.testBit hi.testBit)
    (heq : observedBoundaryState es lo.testBit (boundaryEmbedding n boundary hb) =
      observedBoundaryState es hi.testBit (boundaryEmbedding n boundary hb)) :
    canonicalKey (rootLabels n es boundary mask) ps =
      canonicalKey (rootLabels n es boundary lo) ps := by
  apply canonicalKey_eq_of_stateOfLabels_eq boundary.size
  · simp [rootLabels]
  · simp [rootLabels]
  · exact hps
  · rw [rootLabels_state_eq_observed n es boundary mask he hb hinj,
      rootLabels_state_eq_observed n es boundary lo he hb hinj]
    exact subcube_same_state n boundary.size es (boundaryEmbedding n boundary hb)
      lo.testBit mask.testBit hi.testBit hlo hhi hboundary heq

/-- Refinement interface: the existing native configurationKey is unchanged by pruning. -/
theorem subcube_same_configurationKey (n : Nat) (hn : n < 64) (es : List Edge)
    (boundary : Array Nat) (ps : Array (Array Nat)) (lo mask hi : Nat)
    (he : BoundedEdges n es) (hb : ∀ x ∈ boundary.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n boundary hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin boundary.size),
      RepresentsPermutation boundary.size p e)
    (hlo : OpenLE n lo.testBit mask.testBit) (hhi : OpenLE n mask.testBit hi.testBit)
    (hboundary : BoundaryFixed (boundaryEmbedding n boundary hb) lo.testBit hi.testBit)
    (heq : observedBoundaryState es lo.testBit (boundaryEmbedding n boundary hb) =
      observedBoundaryState es hi.testBit (boundaryEmbedding n boundary hb)) :
    configurationKey n es boundary ps mask = configurationKey n es boundary ps lo := by
  rw [configurationKey_semantics n hn es boundary hb ps mask,
    configurationKey_semantics n hn es boundary hb ps lo]
  exact subcube_same_canonicalKey n es boundary ps lo mask hi he hb hinj hps
    hlo hhi hboundary heq

end SitePerc.Checker
