import SitePerc.Base
import SitePerc.Checker.NativeDefs
import SitePerc.Checker.LawSoundness

/-!
# Packed augmented boundary states

The packed representation reserves label zero for a closed site. Equal positive
labels identify an open component. Connectivity is reflexive even at a closed
site, exactly as graph reachability is; distinct closed sites are not connected.
All order statements below use `SitePerc.stateLE`, not numerical key order.
-/

namespace SitePerc.Checker

/-- A labelled partition together with the independent open/closed bit. -/
def labelState {b : Nat} (a : Fin b → Nat) : BoundaryState (Fin b) where
  opened i := decide (a i ≠ 0)
  connected i j := decide (i = j ∨ a i ≠ 0 ∧ a i = a j)

/-- Total list interpretation; length conditions are proved at codec boundaries. -/
def stateOfLabels (b : Nat) (xs : List Nat) : BoundaryState (Fin b) :=
  labelState (fun i => xs[i.val]!)

/-- Binary rows use high-endian R10 order, unlike the little-endian unpacker. -/
def r10Labels (b key : Nat) : List Nat := (unpack b key).reverse

/-- The actual augmented boundary state denoted by a binary key. -/
def decodeState (b key : Nat) : BoundaryState (Fin b) :=
  stateOfLabels b (r10Labels b key)

/-- Pullback of both state fields along the same boundary permutation. -/
def reindexState {b : Nat} (e : Equiv.Perm (Fin b)) (s : BoundaryState (Fin b)) :
    BoundaryState (Fin b) where
  opened i := s.opened (e i)
  connected i j := s.connected (e i) (e j)

/-- An executable permutation array represents this actual finite equivalence. -/
def RepresentsPermutation (b : Nat) (p : Array Nat) (e : Equiv.Perm (Fin b)) : Prop :=
  p.size = b ∧ ∀ i : Fin b, p[i.val]! = (e i).val

/-- Distinct nonzero equal labels form complete components; zero is isolated. -/
def labelGraph {b : Nat} (a : Fin b → Nat) : SimpleGraph (Fin b) :=
  SimpleGraph.fromRel (fun i j => a i ≠ 0 ∧ a i = a j)

/-- Direct observation of the finite open graph at enumerated boundary vertices. -/
noncomputable def observedBoundaryState {n b : Nat} (es : List Edge) (ω : Nat → Bool)
    (v : Fin b → Fin n) : BoundaryState (Fin b) := by
  classical
  exact { opened := fun i => ω (v i).val
          connected := fun i j => decide ((openGraph n es ω).Reachable (v i) (v j)) }

/-- The boundary array interpreted as actual finite graph vertices. -/
def boundaryEmbedding (n : Nat) (boundary : Array Nat)
    (hb : ∀ x ∈ boundary.toList, x < n) : Fin boundary.size → Fin n :=
  fun i => ⟨boundary[i.val], hb _ (by
    have hmem := List.getElem_mem (show i.val < boundary.toList.length by simpa using i.isLt)
    simpa using hmem)⟩

/-- Proof-facing form of the checker's single block-map update. -/
def keyOrderStep (s t : Array Nat) (i : Nat) (st : Option Bool × Array Nat) :
    Id (ForInStep (Option Bool × Array Nat)) :=
  let M := st.2
  let a := s[i]!
  let c := t[i]!
  if a != 0 then
    if c == 0 then pure (.done (some false, M))
    else if M[a]! != 0 && M[a]! != c then pure (.done (some false, M))
    else pure (.yield (none, M.set! a c))
  else pure (.yield (none, M))

/-- Every processed open source block records a unique, nonzero target block. -/
def BlockMapRecords (s t : Array Nat) (processed : List Nat) (M : Array Nat) : Prop :=
  ∀ i ∈ processed, s[i]! ≠ 0 → t[i]! ≠ 0 ∧ M[s[i]!]! = t[i]!

@[simp] theorem decodeState_opened (b key : Nat) (i : Fin b) :
    (decodeState b key).opened i = true ↔ (r10Labels b key)[i.val]! ≠ 0 := by
  simp [decodeState, stateOfLabels, labelState]

@[simp] theorem decodeState_connected (b key : Nat) (i j : Fin b) :
    (decodeState b key).connected i j = true ↔
      i = j ∨ (r10Labels b key)[i.val]! ≠ 0 ∧
        (r10Labels b key)[i.val]! = (r10Labels b key)[j.val]! := by
  simp [decodeState, stateOfLabels, labelState]

/-- First-occurrence normalization preserves the full augmented state. -/
theorem normalize_stateOfLabels (b : Nat) (xs : List Nat) (hlen : xs.length = b) :
    stateOfLabels b (normalize xs) = stateOfLabels b xs := by
  have hz (i : Fin b) : (normalize xs)[i.val]! = 0 ↔ xs[i.val]! = 0 := by
    have hi : i.val < xs.length := by omega
    rw [getElem!_pos (normalize xs) i.val (by simp [hi]), getElem!_pos xs i.val hi]
    exact normalize_zero_iff xs ⟨i.val, hi⟩
  have he (i j : Fin b) (hi : xs[i.val]! ≠ 0) (hj : xs[j.val]! ≠ 0) :
      (normalize xs)[i.val]! = (normalize xs)[j.val]! ↔ xs[i.val]! = xs[j.val]! := by
    have hi' : i.val < xs.length := by omega
    have hj' : j.val < xs.length := by omega
    rw [getElem!_pos (normalize xs) i.val (by simp [hi']),
      getElem!_pos (normalize xs) j.val (by simp [hj']),
      getElem!_pos xs i.val hi', getElem!_pos xs j.val hj']
    exact normalize_eq_iff xs ⟨i.val,hi'⟩ ⟨j.val,hj'⟩
      (by simpa only [getElem!_pos xs i.val hi'] using hi)
      (by simpa only [getElem!_pos xs j.val hj'] using hj)
  change BoundaryState.mk _ _ = BoundaryState.mk _ _
  congr 1
  · funext i
    simp only [stateOfLabels, labelState, decide_eq_decide]
    exact not_congr (hz i)
  · funext i j
    simp only [stateOfLabels, labelState, decide_eq_decide]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, false_or]
      constructor
      · rintro ⟨hi, heq⟩
        have hi' : xs[i.val]! ≠ 0 := fun h => hi ((hz i).mpr h)
        have hj' : xs[j.val]! ≠ 0 := by
          intro hj
          exact hi (heq.trans ((hz j).mpr hj))
        exact ⟨hi', (he i j hi' hj').mp heq⟩
      · rintro ⟨hi, heq⟩
        have hj : xs[j.val]! ≠ 0 := fun h => hi (heq.trans h)
        exact ⟨fun h => hi ((hz i).mp h), (he i j hi hj).mpr heq⟩

/-- The label-state connectivity is genuine reachability in its component graph. -/
theorem labelState_reachable {b : Nat} (a : Fin b → Nat) (i j : Fin b) :
    (labelGraph a).Reachable i j ↔ (labelState a).connected i j = true := by
  constructor
  · rintro ⟨W⟩
    simp only [labelState, decide_eq_true_eq]
    induction W with
    | nil => exact Or.inl rfl
    | @cons i j k ha W ih =>
      have hs : a i ≠ 0 ∧ a i = a j := by
        obtain ⟨_, he | he⟩ := ha
        · exact he
        · exact ⟨fun hz => he.1 (he.2.trans hz), he.2.symm⟩
      rcases ih with h | ⟨_, hjk⟩
      · exact Or.inr ⟨hs.1, hs.2.trans (congrArg a h)⟩
      · exact Or.inr ⟨hs.1, hs.2.trans hjk⟩
  · intro h
    simp only [labelState, decide_eq_true_eq] at h
    rcases h with rfl | ⟨hi, hij⟩
    · exact SimpleGraph.Reachable.refl _
    · by_cases he : i = j
      · subst j; exact SimpleGraph.Reachable.refl _
      · exact (show (labelGraph a).Adj i j from ⟨he, Or.inl ⟨hi,hij⟩⟩).reachable

/-- An isolated open vertex is not confused with an isolated closed vertex. -/
theorem closed_singleton_ne_open_singleton :
    labelState (fun _ : Fin 1 => 0) ≠ labelState (fun _ : Fin 1 => 1) := by
  intro h
  have := congrArg (fun s : BoundaryState (Fin 1) => s.opened 0) h
  simp [labelState] at this

/-- Bounded binary keys have no unused high bits or alternative digit decode. -/
theorem pack_unpack_of_lt (b key : Nat) (hk : key < 32 ^ b) :
    pack (unpack b key) = key := by
  induction b generalizing key with
  | zero =>
    have : key = 0 := by simpa using hk
    simpa [this, unpack, pack]
  | succ b ih =>
    have hd : key / 32 < 32 ^ b := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).mpr
      simpa [pow_succ] using hk
    simp only [unpack, pack, ih _ hd]
    exact Nat.mod_add_div key 32

/-- C1's validity test includes the exact bounded, normalized canonical code. -/
theorem validCanonical_semantics (b : Nat) (ps : Array (Array Nat)) (key : Nat)
    (hv : validCanonical b ps key = true) :
    key < 32 ^ b ∧ b ≤ 31 ∧ normalize (r10Labels b key) = r10Labels b key ∧
      canonicalKey (r10Labels b key) ps = key ∧ packR10 (r10Labels b key) = key := by
  simp only [validCanonical, validLabels, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  refine ⟨hv.1.1, ?_, hv.1.2.2, hv.2, ?_⟩
  · simpa using hv.1.2.1
  · simpa only [packR10, r10Labels, List.reverse_reverse] using
      pack_unpack_of_lt b key hv.1.1

/-- The canonical-key gate rejects every high-bit alias before interpreting it. -/
theorem validCanonical_high_bits_zero (b : Nat) (ps : Array (Array Nat)) (key : Nat)
    (hv : validCanonical b ps key = true) : key / (32 ^ b) = 0 := by
  exact Nat.div_eq_of_lt (validCanonical_semantics b ps key hv).1

/-- A bounded key is uniquely determined by its decoded R10 label vector. -/
theorem r10Labels_injective_of_lt (b src dst : Nat)
    (hs : src < 32 ^ b) (ht : dst < 32 ^ b)
    (heq : r10Labels b src = r10Labels b dst) : src = dst := by
  have hs' : packR10 (r10Labels b src) = src := by
    simpa [packR10, r10Labels] using pack_unpack_of_lt b src hs
  have ht' : packR10 (r10Labels b dst) = dst := by
    simpa [packR10, r10Labels] using pack_unpack_of_lt b dst ht
  rw [← hs', ← ht', heq]

/-- Array permutations act by precisely the indicated finite reindexing. -/
theorem stateOfLabels_permute (b : Nat) (xs : List Nat) (p : Array Nat)
    (e : Equiv.Perm (Fin b)) (hp : RepresentsPermutation b p e) :
    stateOfLabels b (permute xs p) = reindexState e (stateOfLabels b xs) := by
  have hget (i : Fin b) : (permute xs p)[i.val]! = xs[(e i).val]! := by
    have hi : i.val < (permute xs p).length := by simp [permute, hp.1]
    rw [getElem!_pos (permute xs p) i.val hi]
    simp only [permute, List.getElem_map]
    have hpi : i.val < p.size := by rw [hp.1]; exact i.isLt
    have hg : p.toList[i.val]'(by simpa using hpi) = (e i).val := by
      rw [← getElem!_pos p.toList i.val (by simpa using hpi), Array.getElem!_toList]
      exact hp.2 i
    exact congrArg (fun k => xs[k]!) hg
  change BoundaryState.mk _ _ = BoundaryState.mk _ _
  congr 1
  · funext i
    simp only [hget]
    rfl
  · funext i j
    change decide (i = j ∨ (permute xs p)[i.val]! ≠ 0 ∧
      (permute xs p)[i.val]! = (permute xs p)[j.val]!) =
      decide (e i = e j ∨ xs[(e i).val]! ≠ 0 ∧ xs[(e i).val]! = xs[(e j).val]!)
    rw [hget i, hget j]
    simp only [e.injective.eq_iff]

/-- C8's moved key is the exact permuted boundary state, not a new partition. -/
theorem moveKey_reindex (b : Nat) (p : Array Nat) (key : Nat)
    (e : Equiv.Perm (Fin b)) (hp : RepresentsPermutation b p e) (hb : b ≤ 31) :
    decodeState b (moveKey b p key) = reindexState e (decodeState b key) := by
  let xs := permute (r10Labels b key) p
  have hlen : xs.length = b := by simp [xs, permute, hp.1]
  have hbound : ∀ x ∈ normalize xs, x < 32 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < xs.length := by simpa using hi
    have h := normalize_lt xs ⟨i,hi'⟩
    have hle : (normalize xs)[i]'hi ≤ b := by simpa only [hlen] using h
    omega
  have hdecode : r10Labels b (moveKey b p key) = normalize xs := by
    change (unpack b (pack (normalize xs).reverse)).reverse = normalize xs
    have hl : (normalize xs).reverse.length = b := by simp [hlen]
    rw [← hl, unpack_pack _ (by simpa using hbound), List.reverse_reverse]
  rw [decodeState, hdecode, normalize_stateOfLabels b xs hlen]
  exact stateOfLabels_permute b (r10Labels b key) p e hp

/-- The executable check is exactly the indicated early-exit block-map loop. -/
theorem keyLE_eq_loop (b src dst : Nat) :
    keyLE b src dst =
      let out := (forIn (List.range' 0 b)
        (none, Array.replicate 32 0)
        (keyOrderStep (r10Labels b src).toArray (r10Labels b dst).toArray) :
          Id (Option Bool × Array Nat)).run
      match out.1 with
      | some r => r
      | none => true := by
  simp only [keyLE, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  dsimp only [Id.run, bind, pure]
  let s := (r10Labels b src).toArray
  let t := (r10Labels b dst).toArray
  have hbody : (fun (i : Nat) (st : Option Bool × Array Nat) =>
      (if s[i]! != 0 then
        if t[i]! == 0 then ForInStep.done (some false, st.2)
        else if st.2[s[i]!]! != 0 && st.2[s[i]!]! != t[i]! then
          ForInStep.done (some false, st.2)
        else ForInStep.yield (none, st.2.set! s[i]! t[i]!)
      else ForInStep.yield (none, st.2) : Id (ForInStep (Option Bool × Array Nat)))) =
      keyOrderStep s t := by
    funext i st
    simp only [keyOrderStep]
    rfl
  have hloop := congrArg (fun f : Nat → (Option Bool × Array Nat) →
      Id (ForInStep (Option Bool × Array Nat)) =>
    (forIn (List.range' 0 b) (none, Array.replicate 32 0) f :
      Id (Option Bool × Array Nat))) hbody
  dsimp only [s, t, r10Labels] at hloop ⊢
  erw [hloop]
  cases ((forIn (List.range' 0 b) (none, Array.replicate 32 0)
    (keyOrderStep (unpack b src).reverse.toArray (unpack b dst).reverse.toArray) :
      Id (Option Bool × Array Nat))).1 <;> rfl

/-- A successful block-map update preserves every earlier block record. -/
theorem blockMapRecords_update (s t : Array Nat) (done : List Nat) (M : Array Nat)
    (i : Nat) (hsize : M.size = 32) (ha : s[i]! < 32) (ha0 : s[i]! ≠ 0)
    (hc : t[i]! ≠ 0) (hpass : ¬ (M[s[i]!]! ≠ 0 ∧ M[s[i]!]! ≠ t[i]!))
    (hinv : BlockMapRecords s t done M) :
    BlockMapRecords s t (done ++ [i]) (M.set! s[i]! t[i]!) := by
  intro j hj hj0
  rcases List.mem_append.mp hj with hj | hj
  · obtain ⟨htj, hmj⟩ := hinv j hj hj0
    refine ⟨htj, ?_⟩
    by_cases heq : s[i]! = s[j]!
    · have hold : M[s[i]!]! = t[j]! := by rw [heq]; exact hmj
      have hnonzero : M[s[i]!]! ≠ 0 := fun hz => htj (hold.symm.trans hz)
      have htarget : M[s[i]!]! = t[i]! := by
        by_contra hn
        exact hpass ⟨hnonzero,hn⟩
      rw [← heq, Array.getElem!_set!_self _ _ _ (by omega)]
      exact htarget.symm.trans hold
    · rw [Array.getElem!_set!_ne _ _ _ _ heq]
      exact hmj
  · have hji : j = i := by simpa using hj
    subst j
    exact ⟨hc, Array.getElem!_set!_self _ _ _ (by omega)⟩

/-- Successful termination certifies every processed and remaining coordinate. -/
theorem keyOrderLoop_sound (s t : Array Nat) (todo done : List Nat) (M : Array Nat)
    (hsize : M.size = 32) (hbound : ∀ i ∈ todo, s[i]! < 32)
    (hinv : BlockMapRecords s t done M)
    (hok : ((forIn todo (none, M) (keyOrderStep s t) :
      Id (Option Bool × Array Nat)).run).1 ≠ some false) :
    BlockMapRecords s t (done ++ todo)
      ((forIn todo (none, M) (keyOrderStep s t) :
        Id (Option Bool × Array Nat)).run).2 := by
  induction todo generalizing done M with
  | nil => simpa using hinv
  | cons i rest ih =>
    have hi : s[i]! < 32 := hbound i (by simp)
    have hrest : ∀ j ∈ rest, s[j]! < 32 := fun j hj => hbound j (by simp [hj])
    rw [List.forIn_cons] at hok ⊢
    by_cases ha : s[i]! ≠ 0
    · by_cases hc : t[i]! = 0
      · simp [keyOrderStep, ha, hc, bne_iff_ne, beq_iff_eq, Bool.and_eq_true] at hok
      · by_cases hpass : M[s[i]!]! ≠ 0 ∧ M[s[i]!]! ≠ t[i]!
        · simp [keyOrderStep, ha, hc, hpass, bne_iff_ne, beq_iff_eq, Bool.and_eq_true] at hok
        · simp [keyOrderStep, ha, hc, hpass, bne_iff_ne, beq_iff_eq, Bool.and_eq_true, Id.run, bind, pure] at hok ⊢
          have hnew := blockMapRecords_update s t done M i hsize hi ha hc hpass hinv
          have hh := ih (done ++ [i]) (M.set! s[i]! t[i]!)
            (by simpa using hsize) hrest hnew hok
          simpa only [List.append_assoc, List.singleton_append, Id.run, Array.set!] using hh
    · simp [keyOrderStep, ha, bne_iff_ne, beq_iff_eq, Bool.and_eq_true, Id.run, bind, pure] at hok ⊢
      have hnew : BlockMapRecords s t (done ++ [i]) M := by
        intro j hj hj0
        rcases List.mem_append.mp hj with hj | hj
        · exact hinv j hj hj0
        · have : j = i := by simpa using hj
          subst j
          exact False.elim (ha hj0)
      have hh := ih (done ++ [i]) M hsize hrest hnew hok
      simpa only [List.append_assoc, List.singleton_append, Id.run, Array.set!] using hh

/-- Every radix-32 digit of an unpacked key is in range, including leading zeros. -/
theorem unpack_labels_lt (b key : Nat) : ∀ x ∈ unpack b key, x < 32 := by
  induction b generalizing key with
  | zero => simp [unpack]
  | succ b ih =>
    intro x hx
    simp only [unpack, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ x hx

/-- C2's true flag implies the real augmented-state partial order. -/
theorem keyLE_stateLE (b src dst : Nat) (h : keyLE b src dst = true) :
    stateLE (decodeState b src) (decodeState b dst) := by
  let s := (r10Labels b src).toArray
  let t := (r10Labels b dst).toArray
  let out := (forIn (List.range' 0 b) (none, Array.replicate 32 0)
    (keyOrderStep s t) : Id (Option Bool × Array Nat)).run
  have hok : out.1 ≠ some false := by
    rw [keyLE_eq_loop] at h
    intro hf
    change (match out.1 with | some r => r | none => true) = true at h
    rw [hf] at h
    contradiction
  have hbound : ∀ i ∈ List.range' 0 b, s[i]! < 32 := by
    intro i hi
    have hi' : i < b := by simpa using (List.mem_range'.mp hi)
    have hentry : (r10Labels b src)[i]! < 32 := by
      apply unpack_labels_lt b src
      apply List.mem_reverse.mp
      have hi'' : i < (r10Labels b src).length := by simpa [r10Labels] using hi'
      rw [getElem!_pos (r10Labels b src) i hi'']
      exact List.getElem_mem hi''
    simpa [s] using hentry
  have hinv : BlockMapRecords s t [] (Array.replicate 32 0) := by simp [BlockMapRecords]
  have hall : BlockMapRecords s t (List.range' 0 b) out.2 := by
    simpa [out] using keyOrderLoop_sound s t (List.range' 0 b) []
      (Array.replicate 32 0) (by simp) hbound hinv hok
  have hpoint (i : Fin b) (hi : (r10Labels b src)[i.val]! ≠ 0) :
      (r10Labels b dst)[i.val]! ≠ 0 ∧
        out.2[(r10Labels b src)[i.val]!]! = (r10Labels b dst)[i.val]! := by
    have hh := hall i.val (by simp only [List.mem_range']; exact ⟨i.val,i.isLt,by simp⟩)
      (by simpa [s] using hi)
    simpa [s,t] using hh
  constructor
  · intro i hi
    exact (decodeState_opened b dst i).mpr
      (hpoint i ((decodeState_opened b src i).mp hi)).1
  · intro i j hi hj hc
    rcases (decodeState_connected b src i j).mp hc with heq | ⟨hi0,hlabels⟩
    · subst j
      exact (decodeState_connected b dst i i).mpr (Or.inl rfl)
    · obtain ⟨hti, hmi⟩ := hpoint i hi0
      obtain ⟨_, hmj⟩ := hpoint j ((decodeState_opened b src j).mp hj)
      exact (decodeState_connected b dst i j).mpr
        (Or.inr ⟨hti, hmi.symm.trans (by rw [hlabels]; exact hmj)⟩)

/-- A witness of order against a moved key compares the correctly reindexed state. -/
theorem moveKey_order_sound (b : Nat) (p : Array Nat) (src dst : Nat)
    (e : Equiv.Perm (Fin b)) (hp : RepresentsPermutation b p e) (hb : b ≤ 31)
    (ho : keyLE b src (moveKey b p dst) = true) :
    stateLE (decodeState b src) (reindexState e (decodeState b dst)) := by
  simpa only [moveKey_reindex b p dst e hp hb] using keyLE_stateLE b src _ ho

/-- A nontrivial path in the open graph has two open endpoints. -/
theorem openGraph_reachable_open_or_eq (n : Nat) (es : List Edge) (ω : Nat → Bool)
    (i j : Fin n) (h : (openGraph n es ω).Reachable i j) :
    i = j ∨ ω i.val = true ∧ ω j.val = true := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | @tail j k h hstep ih =>
    have hop : ω j.val = true ∧ ω k.val = true := by
      obtain ⟨_, hs | hs⟩ := hstep
      · exact hs.2
      · exact ⟨hs.2.2,hs.2.1⟩
    rcases ih with heq | ⟨hi,_⟩
    · subst j; exact Or.inr hop
    · exact Or.inr ⟨hi,hop.2⟩

/-- Actual UF root labels denote exactly the graph's observed boundary state. -/
theorem rootLabelState_eq_observed (n b : Nat) (es : List Edge) (ω : Nat → Bool)
    (v : Fin b → Fin n) (he : BoundedEdges n es) (hv : Function.Injective v) :
    labelState (fun i => if ω (v i).val then (components n es ω).rootD (v i).val + 1 else 0) =
      observedBoundaryState es ω v := by
  classical
  let a : Fin b → Nat := fun i =>
    if ω (v i).val then (components n es ω).rootD (v i).val + 1 else 0
  have hconn (i j : Fin b) :
      (i = j ∨ a i ≠ 0 ∧ a i = a j) ↔ (openGraph n es ω).Reachable (v i) (v j) := by
    constructor
    · rintro (rfl | ⟨hi,hij⟩)
      · exact SimpleGraph.Reachable.refl _
      · have hoi : ω (v i).val = true := by
          by_contra hno
          simp [a,hno] at hi
        have hoj : ω (v j).val = true := by
          by_contra hno
          simp [a,hoi,hno] at hij
        apply (components_correct n es ω he (v i) (v j)).mp
        change (components n es ω).rootD (v i).val = (components n es ω).rootD (v j).val
        simpa [a,hoi,hoj] using hij
    · intro hr
      rcases openGraph_reachable_open_or_eq n es ω (v i) (v j) hr with hij | ⟨hoi,hoj⟩
      · exact Or.inl (hv hij)
      · refine Or.inr ⟨by simp [a,hoi], ?_⟩
        have hh := (components_correct n es ω he (v i) (v j)).mpr hr
        change (components n es ω).rootD (v i).val = (components n es ω).rootD (v j).val at hh
        simpa [a,hoi,hoj] using congrArg (fun k : Nat => k+1) hh
  change BoundaryState.mk _ _ = BoundaryState.mk _ _
  congr 1
  · funext i
    change decide (a i ≠ 0) = ω (v i).val
    cases hi : ω (v i).val <;> simp [a,hi]
  · funext i j
    change decide (i = j ∨ a i ≠ 0 ∧ a i = a j) =
      decide ((openGraph n es ω).Reachable (v i) (v j))
    simpa only [decide_eq_decide] using hconn i j

/-- The list used by the raw-key encoder reads precisely the actual boundary UF roots. -/
theorem rootLabels_get (n : Nat) (es : List Edge) (boundary : Array Nat) (mask : Nat)
    (i : Fin boundary.size) :
    (rootLabels n es boundary mask)[i.val]! =
      if mask.testBit boundary[i.val] then
        (components n es mask.testBit).rootD boundary[i.val] + 1 else 0 := by
  rw [getElem!_pos (rootLabels n es boundary mask) i.val
    (by simpa [rootLabels] using i.isLt)]
  simp [rootLabels]

/-- The raw root-label state is an actual open-graph BoundaryState, including closed sites. -/
theorem rootLabels_state_eq_observed (n : Nat) (es : List Edge) (boundary : Array Nat)
    (mask : Nat) (he : BoundedEdges n es) (hb : ∀ x ∈ boundary.toList, x < n)
    (hi : Function.Injective (boundaryEmbedding n boundary hb)) :
    stateOfLabels boundary.size (rootLabels n es boundary mask) =
      observedBoundaryState es mask.testBit (boundaryEmbedding n boundary hb) := by
  have hlabels : (fun i : Fin boundary.size => (rootLabels n es boundary mask)[i.val]!) =
      (fun i : Fin boundary.size => if mask.testBit (boundaryEmbedding n boundary hb i).val then
        (components n es mask.testBit).rootD (boundaryEmbedding n boundary hb i).val + 1 else 0) := by
    funext i
    exact rootLabels_get n es boundary mask i
  rw [stateOfLabels, hlabels]
  exact rootLabelState_eq_observed n boundary.size es mask.testBit _ he hi

end SitePerc.Checker
