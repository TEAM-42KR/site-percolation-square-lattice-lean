import SitePerc.Checker.PrunedDefs
import SitePerc.Checker.CheckerSoundness
import SitePerc.Checker.BinomialCubes
import SitePerc.Checker.CubeConfigurations
import SitePerc.Checker.SubcubePruning
import SitePerc.Checker.RegionalGeometry
import Mathlib.Tactic

namespace SitePerc.Checker

/-- Memoization changes neither the exact coefficient map nor the traversal
statistics; its validity is carried through both recursive children. -/
theorem enumerateCubeMemo_refines (rows : Array (Array Nat)) (n : Nat)
    (es : List Edge) (b : Array Nat) (ps : Array (Array Nat)) (cap : Nat)
    (vs : List Nat) (base k raw : Nat) (lo hi : List Nat)
    (law : CountMap) (cache : KeyCache) (st : CubeStats)
    (hr : raw = rawRootKey n es b base) (hc : CacheValid b.size ps cache) :
    let r := enumerateCubeMemo rows n es b ps cap vs base k raw lo hi law cache st
    let s := enumerateCube rows n es b ps vs base k lo hi law st
    r.1 = s.1 ∧ r.2.2 = s.2 ∧ CacheValid b.size ps r.2.1 := by
  induction vs generalizing base k raw lo hi law cache st with
  | nil =>
    simp only [enumerateCubeMemo,enumerateCube]
    split
    · have hv : CacheValid b.size ps (if cache.size > cap then {} else cache) := by
        split
        · exact cacheValid_empty _ _
        · exact hc
      have hh := cacheKey_sound b.size ps raw _ hv
      rcases hres : cacheKey b.size ps raw (if cache.size > cap then {} else cache) with ⟨key,cache'⟩
      rw [hres] at hh
      simp only [Prod.fst,Prod.snd] at hh
      have hk : key = configurationKey n es b ps base := by
        simpa only [configurationKey,hr] using hh.1
      simp only [hk,Prod.fst,Prod.snd]
      exact ⟨trivial,trivial,hh.2⟩
    · exact ⟨rfl,rfl,hc⟩
  | cons v vs ih =>
    simp only [enumerateCubeMemo,enumerateCube]
    split
    · have hv : CacheValid b.size ps (if cache.size > cap then {} else cache) := by
        split
        · exact cacheValid_empty _ _
        · exact hc
      have hh := cacheKey_sound b.size ps raw _ hv
      rcases hres : cacheKey b.size ps raw (if cache.size > cap then {} else cache) with ⟨key,cache'⟩
      rw [hres] at hh
      simp only [Prod.fst,Prod.snd] at hh
      have hk : key = configurationKey n es b ps base := by
        simpa only [configurationKey,hr] using hh.1
      simp only [hk,Prod.fst,Prod.snd]
      exact ⟨trivial,trivial,hh.2⟩
    · have h1 := ih base k raw lo (normalize (rootLabels n es b (base+freeBits vs)))
        law cache ⟨st.visited+1,st.collapsed,st.represented⟩ hr hc
      dsimp only at h1
      generalize hleft : enumerateCubeMemo rows n es b ps cap vs base k raw lo
        (normalize (rootLabels n es b (base+freeBits vs))) law cache
        ⟨st.visited+1,st.collapsed,st.represented⟩ = left at h1 ⊢
      rcases left with ⟨law',cache',st'⟩
      have h2 := ih (base+2^v) (k+1) (packBase 64 (rootLabels n es b (base+2^v)))
        (normalize (rootLabels n es b (base+2^v))) hi law' cache' st' rfl h1.2.2
      dsimp only at h2
      dsimp only [Prod.fst,Prod.snd] at h1 ⊢
      rw [←h1.1,←h1.2.1]
      exact h2

/-- The direct Boolean-leaf form of the reference's exact variable order. -/
def cubeBoolMask : List Nat → Nat → List Bool → Nat
  | [], base, _ => base
  | _::_, base, [] => base
  | v::vs, base, b::bs => cubeBoolMask vs (if b then base+2^v else base) bs

def boolBits : List Bool → Nat
  | [] => 0
  | b::bs => Nat.bit b (boolBits bs)

theorem cubeBoolMask_eq_path (vs : List Nat) (base : Nat) (bs : List Bool) :
    cubeBoolMask vs base bs = (cubePath vs base 0 (boolBits bs)).1 := by
  induction vs generalizing base bs with
  | nil => rfl
  | cons v vs ih =>
    cases bs with
    | nil =>
      rw [cubePath_eq]
      simp [cubeBoolMask,boolBits,placedMask]
    | cons b bs =>
      cases b <;> simp [cubeBoolMask,boolBits,cubePath,Nat.bit,ih]
      rw [cubePath_eq,cubePath_eq]
      have hb : (2 * boolBits bs + 1) / 2 = boolBits bs := by omega
      rw [hb]

theorem cubeBoolMask_eq_placed (vs : List Nat) (base : Nat) (bs : List Bool) :
    cubeBoolMask vs base bs = base + placedMask vs (boolBits bs) := by
  rw [cubeBoolMask_eq_path,cubePath_eq]

theorem cubeReference_shape (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (vs : List Nat) (base k : Nat) (law : CountMap)
    (hs : CountShape n law) : CountShape n (cubeReference n es b ps vs base k law) := by
  induction vs generalizing base k law with
  | nil => exact countShape_bump _ _ _ _ _ hs
  | cons v vs ih =>
    exact ih _ _ _ (ih _ _ _ hs)

theorem cubeReference_coefficient (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (vs : List Nat) (base baseOpen : Nat) (law : CountMap)
    (hs : CountShape n law) (hslots : baseOpen+vs.length ≤ n) (query k : Nat) (hk : k ≤ n) :
    coefficient n (cubeReference n es b ps vs base baseOpen law) query k =
      coefficient n law query k + cubeBinarySum vs.length (fun bs =>
        if configurationKey n es b ps (cubeBoolMask vs base bs) = query ∧
          baseOpen + bs.count true = k then 1 else 0) := by
  induction vs generalizing base baseOpen law with
  | nil =>
    simp only [cubeReference,cubeBinarySum,List.length_nil,cubeBoolMask,
      List.count_nil,Nat.add_zero]
    rw [coefficient_bump n _ baseOpen 1 law (by simpa using hslots) hs query k hk]
    simp [eq_comm]
  | cons v vs ih =>
    simp only [cubeReference,List.length_cons,cubeBinarySum]
    rw [ih (base+2^v) (baseOpen+1) _ (cubeReference_shape n es b ps vs base baseOpen law hs)
      (by simp only [List.length_cons] at hslots; omega),
      ih base baseOpen law hs (by simp only [List.length_cons] at hslots; omega)]
    simp only [cubeBoolMask,Bool.false_eq_true,↓reduceIte,Bool.true_eq,
      List.count_cons,Bool.false_beq,Bool.true_beq,Bool.not_true,Nat.add_zero,
      Nat.add_assoc,Nat.add_comm 1]

theorem countShape_bumpCube (rows : Array (Array Nat)) (n key k free : Nat)
    (law : CountMap) (hs : CountShape n law) : CountShape n (bumpCube rows n key k free law) := by
  intro query
  unfold bumpCube
  rw [Std.HashMap.getD_insert]
  split
  · simp
  · exact hs query

theorem enumerateCube_shape (rows : Array (Array Nat)) (n : Nat) (es : List Edge)
    (b : Array Nat) (ps : Array (Array Nat)) (vs : List Nat) (base k : Nat)
    (lo hi : List Nat) (law : CountMap) (st : CubeStats) (hs : CountShape n law) :
    CountShape n (enumerateCube rows n es b ps vs base k lo hi law st).1 := by
  induction vs generalizing base k lo hi law st with
  | nil =>
    simp only [enumerateCube]
    split
    · exact countShape_bumpCube _ _ _ _ _ _ hs
    · exact countShape_bump _ _ _ _ _ hs
  | cons v vs ih =>
    simp only [enumerateCube]
    split
    · exact countShape_bumpCube _ _ _ _ _ _ hs
    · exact ih _ _ _ _ _ _ (ih _ _ _ _ _ _ hs)

/-- The executable guard is equality of normalized *unquotiented* endpoint
partitions, never equality of orbit-canonical keys alone. -/
theorem pruning_key_constant (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (ps : Array (Array Nat)) (vs : List Nat) (base : Nat)
    (hv : ValidCube n vs base) (he : BoundedEdges n es)
    (hb : ∀ x ∈ b.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n b hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin b.size), RepresentsPermutation b.size p e)
    (heq : normalize (rootLabels n es b base) =
      normalize (rootLabels n es b (base+freeBits vs))) (bs : List Bool) :
    configurationKey n es b ps (cubeBoolMask vs base bs) = configurationKey n es b ps base := by
  have hs : stateOfLabels b.size (rootLabels n es b base) =
      stateOfLabels b.size (rootLabels n es b (base+freeBits vs)) := by
    rw [←normalize_stateOfLabels b.size _ (by simp [rootLabels]),
      ←normalize_stateOfLabels b.size (rootLabels n es b (base+freeBits vs)) (by simp [rootLabels]),heq]
  have ho : observedBoundaryState es base.testBit (boundaryEmbedding n b hb) =
      observedBoundaryState es (base+freeBits vs).testBit (boundaryEmbedding n b hb) := by
    rw [←rootLabels_state_eq_observed n es b base he hb hinj,
      ←rootLabels_state_eq_observed n es b (base+freeBits vs) he hb hinj]
    exact hs
  have hboundary : BoundaryFixed (boundaryEmbedding n b hb) base.testBit
      (base+freeBits vs).testBit := by
    intro i
    exact congrArg (fun state => state.opened i) ho
  apply subcube_same_configurationKey n hn es b ps base (cubeBoolMask vs base bs)
    (base+freeBits vs) he hb hinj hps _ _ hboundary ho
  · intro i hi
    rw [cubeBoolMask_eq_placed]
    exact (validCube_assignment_bounds hv (boolBits bs) i.val).1 hi
  · intro i hi
    rw [cubeBoolMask_eq_placed] at hi
    exact (validCube_assignment_bounds hv (boolBits bs) i.val).2 hi

/-- Every coefficient of the optimized endpoint-pruning computation is the
complete Boolean-tree coefficient, with no producer or total-mass premise. -/
theorem enumerateCube_coefficient (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (ps : Array (Array Nat)) (maxFree : Nat)
    (he : BoundedEdges n es) (hb : ∀ x ∈ b.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n b hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin b.size), RepresentsPermutation b.size p e)
    (vs : List Nat) (base baseOpen : Nat) (lo hi : List Nat) (law : CountMap) (st : CubeStats)
    (hv : ValidCube n vs base) (hs : CountShape n law)
    (hslots : baseOpen+vs.length ≤ n) (hmax : vs.length ≤ maxFree)
    (hlo : lo = normalize (rootLabels n es b base))
    (hhi : hi = normalize (rootLabels n es b (base+freeBits vs)))
    (query k : Nat) (hk : k ≤ n) :
    coefficient n (enumerateCube (cubeBinomials maxFree) n es b ps vs base baseOpen lo hi law st).1 query k =
      coefficient n law query k + cubeBinarySum vs.length (fun bs =>
        if configurationKey n es b ps (cubeBoolMask vs base bs) = query ∧
          baseOpen + bs.count true = k then 1 else 0) := by
  induction vs generalizing base baseOpen lo hi law st with
  | nil =>
    simp only [enumerateCube]
    split
    · next hguard =>
      have heq : normalize (rootLabels n es b base) = normalize (rootLabels n es b (base+freeBits [])) :=
        hlo.symm.trans ((beq_iff_eq.mp hguard).trans hhi)
      exact coefficient_bumpCube_eq_binarySum n maxFree _ baseOpen 0 law query k hmax hk
        (fun bs => configurationKey n es b ps (cubeBoolMask [] base bs))
        (fun bs _ => pruning_key_constant n hn es b ps [] base hv he hb hinj hps heq bs)
    · simp only [cubeBinarySum,List.length_nil,cubeBoolMask,List.count_nil,Nat.add_zero]
      rw [coefficient_bump n _ baseOpen 1 law (by simpa using hslots) hs query k hk]
      simp [eq_comm]
  | cons v vs ih =>
    simp only [enumerateCube]
    split
    · next hguard =>
      have heq : normalize (rootLabels n es b base) = normalize (rootLabels n es b (base+freeBits (v::vs))) :=
        hlo.symm.trans ((beq_iff_eq.mp hguard).trans hhi)
      exact coefficient_bumpCube_eq_binarySum n maxFree _ baseOpen (v::vs).length law query k hmax hk
        (fun bs => configurationKey n es b ps (cubeBoolMask (v::vs) base bs))
        (fun bs _ => pruning_key_constant n hn es b ps (v::vs) base hv he hb hinj hps heq bs)
    · have hslots0 : baseOpen+vs.length ≤ n := by simp only [List.length_cons] at hslots; omega
      have hslots1 : baseOpen+1+vs.length ≤ n := by simp only [List.length_cons] at hslots; omega
      have hmax' : vs.length ≤ maxFree := by simp only [List.length_cons] at hmax; omega
      have hl := ih base baseOpen lo (normalize (rootLabels n es b (base+freeBits vs))) law
        ⟨st.visited+1,st.collapsed,st.represented⟩
        (validCube_closed hv) hs hslots0 hmax' hlo rfl
      let left := enumerateCube (cubeBinomials maxFree) n es b ps vs base baseOpen lo
        (normalize (rootLabels n es b (base+freeBits vs))) law
        ⟨st.visited+1,st.collapsed,st.represented⟩
      have hleftshape : CountShape n left.1 := enumerateCube_shape _ _ _ _ _ _ _ _ _ _ _ _ hs
      have hhi' : hi = normalize (rootLabels n es b (base+2^v+freeBits vs)) := by
        simpa only [freeBits,Nat.add_assoc] using hhi
      have hr := ih (base+2^v) (baseOpen+1) (normalize (rootLabels n es b (base+2^v))) hi
        left.1 left.2 (validCube_open hv) hleftshape hslots1 hmax' rfl hhi'
      change coefficient n (enumerateCube (cubeBinomials maxFree) n es b ps vs
        (base+2^v) (baseOpen+1) (normalize (rootLabels n es b (base+2^v))) hi left.1 left.2).1 query k = _
      rw [hr]
      change coefficient n (enumerateCube (cubeBinomials maxFree) n es b ps vs base baseOpen lo
        (normalize (rootLabels n es b (base+freeBits vs))) law
        ⟨st.visited+1,st.collapsed,st.represented⟩).1 query k + _ = _
      rw [hl]
      simp only [cubeBinarySum,List.length_cons,cubeBoolMask,Bool.false_eq_true,↓reduceIte,
        List.count_cons,Bool.false_beq,Bool.true_beq,Bool.not_true,Nat.add_zero,
        Nat.add_assoc,Nat.add_comm 1]

/-- The optimized path is an exact coefficient refinement of the full
reference tree. Extra statistics and cache data never weaken the conclusion. -/
theorem enumerateCube_refines_reference (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (ps : Array (Array Nat)) (maxFree : Nat)
    (he : BoundedEdges n es) (hb : ∀ x ∈ b.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n b hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin b.size), RepresentsPermutation b.size p e)
    (vs : List Nat) (base baseOpen : Nat) (lo hi : List Nat) (law : CountMap) (st : CubeStats)
    (hv : ValidCube n vs base) (hs : CountShape n law)
    (hslots : baseOpen+vs.length ≤ n) (hmax : vs.length ≤ maxFree)
    (hlo : lo = normalize (rootLabels n es b base))
    (hhi : hi = normalize (rootLabels n es b (base+freeBits vs)))
    (query k : Nat) (hk : k ≤ n) :
    coefficient n (enumerateCube (cubeBinomials maxFree) n es b ps vs base baseOpen lo hi law st).1 query k =
      coefficient n (cubeReference n es b ps vs base baseOpen law) query k := by
  rw [enumerateCube_coefficient n hn es b ps maxFree he hb hinj hps vs base baseOpen lo hi law st
    hv hs hslots hmax hlo hhi query k hk,
    cubeReference_coefficient n es b ps vs base baseOpen law hs hslots query k hk]

theorem sum_range_twice (f : Nat → Nat) (n : Nat) :
    (∑ i ∈ Finset.range (2*n), f i) =
      (∑ i ∈ Finset.range n, f (2*i)) + (∑ i ∈ Finset.range n, f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,show 2*n+2 = (2*n+1)+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ,Finset.sum_range_succ]
    omega

theorem cubePath_even (v : Nat) (vs : List Nat) (base k i : Nat) :
    cubePath (v::vs) base k (2*i) = cubePath vs base k i := by
  simp [cubePath,Nat.testBit_zero,Nat.mul_comm]

theorem cubePath_odd (v : Nat) (vs : List Nat) (base k i : Nat) :
    cubePath (v::vs) base k (2*i+1) = cubePath vs (base+2^v) (k+1) i := by
  have hd : (2*i+1)/2 = i := by omega
  simp [cubePath,Nat.testBit_zero,hd,Nat.add_mod,Nat.mul_mod]

theorem cubeReference_coefficient_range (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (vs : List Nat) (base baseOpen : Nat) (law : CountMap)
    (hs : CountShape n law) (hslots : baseOpen+vs.length ≤ n) (query k : Nat) (hk : k ≤ n) :
    coefficient n (cubeReference n es b ps vs base baseOpen law) query k =
      coefficient n law query k + ∑ mask ∈ Finset.range (2^vs.length),
        if configurationKey n es b ps (cubePath vs base baseOpen mask).1 = query ∧
          (cubePath vs base baseOpen mask).2 = k then 1 else 0 := by
  induction vs generalizing base baseOpen law with
  | nil =>
    simp only [cubeReference,List.length_nil,pow_zero,Finset.sum_range_one,cubePath]
    rw [coefficient_bump n _ baseOpen 1 law (by simpa using hslots) hs query k hk]
    simp [eq_comm]
  | cons v vs ih =>
    rw [cubeReference,
      ih (base+2^v) (baseOpen+1) _ (cubeReference_shape n es b ps vs base baseOpen law hs)
        (by simp only [List.length_cons] at hslots; omega),
      ih base baseOpen law hs (by simp only [List.length_cons] at hslots; omega)]
    simp only [List.length_cons,pow_succ',sum_range_twice,cubePath_even,cubePath_odd]
    omega

theorem boundaryCubesLoop_valid (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (vs : List Nat) (rows : Array (Array Nat))
    (stride count start : Nat) (law : CountMap) (cache : KeyCache) (st : CubeStats)
    (hs : CountShape n law) (hc : CacheValid b.size ps cache) :
    let r := boundaryCubesLoop n es b ps vs rows stride count start law cache st
    CountShape n r.1 ∧ CacheValid b.size ps r.2.1 := by
  induction count generalizing start law cache st with
  | zero => exact ⟨hs,hc⟩
  | succ count ih =>
    let bm := start % (2^b.size)
    let base := embedBoundary b bm
    let lo := normalize (rootLabels n es b base)
    let hi := normalize (rootLabels n es b (base+freeBits vs))
    let r := enumerateCubeMemo rows n es b ps 1000000 vs base (openCount b.size bm)
      (rawRootKey n es b base) lo hi law cache st
    have hm := enumerateCubeMemo_refines rows n es b ps 1000000 vs base
      (openCount b.size bm) (rawRootKey n es b base) lo hi law cache st rfl hc
    have hshape : CountShape n r.1 := by
      rw [show r.1 = (enumerateCube rows n es b ps vs base (openCount b.size bm) lo hi law st).1 from hm.1]
      exact enumerateCube_shape _ _ _ _ _ _ _ _ _ _ _ _ hs
    exact ih (start+stride) r.1 r.2.1 r.2.2 hshape hm.2.2

theorem boundaryCubesLoop_coefficient (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (ps : Array (Array Nat)) (vs : List Nat)
    (he : BoundedEdges n es) (hb : ∀ x ∈ b.toList, x < n)
    (hinj : Function.Injective (boundaryEmbedding n b hb))
    (hps : ∀ p ∈ ps.toList, ∃ e : Equiv.Perm (Fin b.size), RepresentsPermutation b.size p e)
    (hvalid : ∀ bm < 2^b.size, ValidCube n vs (embedBoundary b bm))
    (hslots : b.size+vs.length ≤ n)
    (stride count start : Nat) (law : CountMap) (cache : KeyCache) (st : CubeStats)
    (hs : CountShape n law) (hc : CacheValid b.size ps cache)
    (query k : Nat) (hk : k ≤ n) :
    coefficient n (boundaryCubesLoop n es b ps vs (cubeBinomials vs.length)
      stride count start law cache st).1 query k =
      coefficient n law query k + ∑ i ∈ Finset.range count,
        ∑ mask ∈ Finset.range (2^vs.length),
          if configurationKey n es b ps (cubePath vs (embedBoundary b ((start+i*stride)%(2^b.size)))
              (openCount b.size ((start+i*stride)%(2^b.size))) mask).1 = query ∧
            (cubePath vs (embedBoundary b ((start+i*stride)%(2^b.size)))
              (openCount b.size ((start+i*stride)%(2^b.size))) mask).2 = k then 1 else 0 := by
  induction count generalizing start law cache st with
  | zero => simp [boundaryCubesLoop]
  | succ count ih =>
    let rows := cubeBinomials vs.length
    let bm := start % (2^b.size)
    let base := embedBoundary b bm
    let k0 := openCount b.size bm
    let lo := normalize (rootLabels n es b base)
    let hi := normalize (rootLabels n es b (base+freeBits vs))
    let r := enumerateCubeMemo rows n es b ps 1000000 vs base k0
      (rawRootKey n es b base) lo hi law cache st
    have hm := enumerateCubeMemo_refines rows n es b ps 1000000 vs base k0
      (rawRootKey n es b base) lo hi law cache st rfl hc
    have hshape : CountShape n r.1 := by
      rw [show r.1 = (enumerateCube rows n es b ps vs base k0 lo hi law st).1 from hm.1]
      exact enumerateCube_shape _ _ _ _ _ _ _ _ _ _ _ _ hs
    have hslot0 : k0+vs.length ≤ n := by
      have hk0 := openCount_le b.size bm
      omega
    have hthis : coefficient n r.1 query k = coefficient n law query k +
        ∑ mask ∈ Finset.range (2^vs.length),
          if configurationKey n es b ps (cubePath vs base k0 mask).1 = query ∧
            (cubePath vs base k0 mask).2 = k then 1 else 0 := by
      rw [show r.1 = (enumerateCube rows n es b ps vs base k0 lo hi law st).1 from hm.1]
      rw [enumerateCube_refines_reference n hn es b ps vs.length he hb hinj hps
        vs base k0 lo hi law st (hvalid bm (Nat.mod_lt _ (Nat.two_pow_pos _))) hs
        hslot0 (Nat.le_refl _) rfl rfl query k hk,
        cubeReference_coefficient_range n es b ps vs base k0 law hs hslot0 query k hk]
    change coefficient n (boundaryCubesLoop n es b ps vs rows stride count (start+stride)
      r.1 r.2.1 r.2.2).1 query k = _
    rw [ih (start+stride) r.1 r.2.1 r.2.2 hshape hm.2.2,hthis,Finset.sum_range_succ']
    simp only [Nat.zero_mul,Nat.add_zero]
    dsimp only [rows,bm,base,k0]
    let f : Nat → Nat := fun x => ∑ mask ∈ Finset.range (2^vs.length),
      if configurationKey n es b ps (cubePath vs (embedBoundary b (x%(2^b.size)))
          (openCount b.size (x%(2^b.size))) mask).1 = query ∧
        (cubePath vs (embedBoundary b (x%(2^b.size)))
          (openCount b.size (x%(2^b.size))) mask).2 = k then 1 else 0
    change (coefficient n law query k + f start) +
      (∑ i ∈ Finset.range count, f (start+stride+i*stride)) =
      coefficient n law query k + ((∑ i ∈ Finset.range count, f (start+(i+1)*stride)) + f start)
    have htail : (∑ i ∈ Finset.range count, f (start+stride+i*stride)) =
        ∑ i ∈ Finset.range count, f (start+(i+1)*stride) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hshift : start+stride+i*stride = start+(i+1)*stride := by
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [hshift]
    omega

theorem regional_grid_bounded (m : Nat) (hm : RegionalSize m) (mode : Fin 3) :
    BoundedEdges (m*m) (gridEdges m mode.val) := by
  have hcheck : (gridEdges m mode.val).all (fun e => decide (e.1 < m*m ∧ e.2 < m*m)) = true := by
    rcases hm with rfl | rfl | rfl <;> fin_cases mode <;> decide +kernel
  intro e he
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) e he)

theorem regional_pruning_geometry (m : Nat) (hm : RegionalSize m) :
    ∃ hb : ∀ x ∈ (squareBoundary m).toList, x < m*m,
      Function.Injective (boundaryEmbedding (m*m) (squareBoundary m) hb) ∧
      (∀ p ∈ (regionalPerms m).toList, ∃ e : Equiv.Perm (Fin (squareBoundary m).size),
        RepresentsPermutation (squareBoundary m).size p e) := by
  let b := squareBoundary m
  have hp := squareBoundary_interior_perm m hm
  have hn : (b.toList ++ interiorVertices m).Nodup := hp.nodup_iff.mpr List.nodup_range
  have hb : ∀ x ∈ b.toList, x < m*m := by
    intro x hx
    exact List.mem_range.mp (hp.mem_iff.mp (List.mem_append_left _ hx))
  refine ⟨hb,?_,?_⟩
  · intro i j hij
    have hget : b.toList.get ⟨i.val,by simpa only [b,Array.length_toList] using i.isLt⟩ =
        b.toList.get ⟨j.val,by simpa only [b,Array.length_toList] using j.isLt⟩ := by
      simpa [boundaryEmbedding] using congrArg Fin.val hij
    have heq := (List.nodup_append.mp hn).1.injective_get hget
    exact Fin.ext (congrArg Fin.val heq)
  · intro p hp
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    have hsize := (regionalPermutationData m hm).1
    let t : Fin (regionalVertexPerms m).size := ⟨i.val,by simpa [←hsize] using i.isLt⟩
    have hlookup : (regionalPerms m)[t.val]! = p := by
      have hib : i.val < (regionalPerms m).size := by simpa using i.isLt
      change (regionalPerms m)[i.val]! = p
      rw [getElem!_pos (regionalPerms m) i.val hib]
      simpa only [List.get_eq_getElem,Array.getElem_toList] using hi
    refine ⟨regionalBoundaryIndexEquiv m hm t,?_⟩
    rw [←hlookup]
    exact regionalBoundaryIndexEquiv_represents m hm t

theorem square_cubePath_sum (m : Nat) (hm : RegionalSize m) (F : Nat → Nat → Nat) :
    (∑ bm : Fin (2^(squareBoundary m).size),
      ∑ im : Fin (2^(interiorVertices m).length),
        F (cubePath (interiorVertices m) (embedBoundary (squareBoundary m) bm.val)
            (openCount (squareBoundary m).size bm.val) im.val).1
          (cubePath (interiorVertices m) (embedBoundary (squareBoundary m) bm.val)
            (openCount (squareBoundary m).size bm.val) im.val).2) =
    ∑ mask : Fin (2^(m*m)), F mask.val (openCount (m*m) mask.val) := by
  have hm' : m = 2 ∨ m = 4 ∨ m = 6 := hm
  simp_rw [cubePath_boundary_exact m hm']
  have h := Equiv.sum_comp (boundaryCubeEquiv m hm')
    (fun mask => F mask.val (openCount (m*m) mask.val))
  rw [Fintype.sum_prod_type] at h
  exact h

/-- Full actual supported-square C7 path: all Boolean cubes, memo resets,
outer tail-loop accumulation and Task chunks, at every individual key/k. -/
theorem prunedParallel_coefficients_correct (m : Nat) (hm : RegionalSize m)
    (mode : Fin 3) (workers query k : Nat) (hk : k ≤ m*m) :
    (sumCounts (m*m)
      ((prunedParallel m mode.val workers (2^(squareBoundary m).size) 0).map Prod.fst) query)[k]! =
      ∑ mask ∈ Finset.range (2^(m*m)),
        if configurationKey (m*m) (gridEdges m mode.val) (squareBoundary m) (regionalPerms m) mask = query ∧
          openCount (m*m) mask = k then 1 else 0 := by
  have hm' : m = 2 ∨ m = 4 ∨ m = 6 := hm
  let n := m*m
  let b := squareBoundary m
  let es := gridEdges m mode.val
  let ps := regionalPerms m
  let vs := interiorVertices m
  let count := 2^b.size
  let w := max 1 workers
  let width := (count+w-1)/w
  let maps := (prunedParallel m mode.val workers count 0).map Prod.fst
  obtain ⟨hb,hinj,hps⟩ := regional_pruning_geometry m hm
  have hn : n < 64 := by rcases hm' with rfl | rfl | rfl <;> decide
  have he : BoundedEdges n es := regional_grid_bounded m hm mode
  have hvalid : ∀ bm < count, ValidCube n vs (embedBoundary b bm) := by
    intro bm hbm
    exact boundaryCube_valid m hm' ⟨bm,hbm⟩
  have hslots : b.size+vs.length ≤ n := by
    have h := (squareBoundary_interior_perm m hm').length_eq
    have heq : b.size+vs.length = n := by
      simpa only [List.length_append,Array.length_toList,List.length_range] using h
    omega
  have hz : coefficient n ({} : CountMap) query k = 0 := by
    simp only [coefficient,Std.HashMap.getD_empty]
    exact zeroCounts_get n k hk
  have hmaps : maps.toList = (List.range w).map (fun i =>
      (boundaryCubesLoop n es b ps vs (cubeBinomials vs.length) 1
        (min width (count-i*width)) (i*width) {} {} {}).1) := by
    have hv : (prunedParallel m mode.val workers count 0).toList =
        (List.range w).map (fun i => enumerateBoundaryCubes m mode.val (i*width)
          (min width (count-i*width)) 1) := by
      simp only [prunedParallel,Task.spawn,List.map_map]
      change ((List.range w).map (fun i => enumerateBoundaryCubes m mode.val
        (0+i*width*1) (min width (count-i*width)) 1)).toArray.toList = _
      simp only [List.toList_toArray,Nat.zero_add,Nat.mul_one]
    rw [show maps = (prunedParallel m mode.val workers count 0).map Prod.fst from rfl,
      Array.toList_map,hv,List.map_map]
    apply List.map_congr_left
    intro i hi
    rfl
  let F : Nat → Nat := fun bm => ∑ mask ∈ Finset.range (2^vs.length),
    if configurationKey n es b ps (cubePath vs (embedBoundary b (bm%count))
        (openCount b.size (bm%count)) mask).1 = query ∧
      (cubePath vs (embedBoundary b (bm%count)) (openCount b.size (bm%count)) mask).2 = k then 1 else 0
  have hcoeff : (sumCounts n maps query)[k]! = ∑ bm ∈ Finset.range count, F bm := by
    rw [sumCounts_coefficient n maps query k hk,hmaps,List.map_map,sum_map_range]
    calc
      _ = ∑ i ∈ Finset.range w, ∑ j ∈ Finset.range (min width (count-i*width)), F (i*width+j) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [F,count,Function.comp_apply,hz,Nat.zero_add,Nat.mul_one] using
          boundaryCubesLoop_coefficient n hn es b ps vs he hb hinj hps hvalid hslots
            1 (min width (count-i*width)) (i*width) {} {} {} (countShape_empty n)
            (cacheValid_empty b.size ps) query k hk
      _ = _ := by
        have h := sum_clipped_blocks F width count w
        have hw : 0 < w := by dsimp only [w]; omega
        rw [min_eq_left (ceil_partition_covers count w hw)] at h
        exact h
  change (sumCounts n maps query)[k]! = _
  rw [hcoeff]
  calc
    _ = ∑ bm : Fin count, ∑ im : Fin (2^vs.length),
        if configurationKey n es b ps (cubePath vs (embedBoundary b bm.val)
            (openCount b.size bm.val) im.val).1 = query ∧
          (cubePath vs (embedBoundary b bm.val) (openCount b.size bm.val) im.val).2 = k then 1 else 0 := by
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro bm _
      dsimp only [F]
      rw [Nat.mod_eq_of_lt bm.isLt]
      exact (Fin.sum_univ_eq_sum_range (fun mask : Nat =>
        if configurationKey n es b ps (cubePath vs (embedBoundary b bm.val)
            (openCount b.size bm.val) mask).1 = query ∧
          (cubePath vs (embedBoundary b bm.val) (openCount b.size bm.val) mask).2 = k then 1 else 0)
        (2^vs.length)).symm
    _ = ∑ mask : Fin (2^n),
        if configurationKey n es b ps mask.val = query ∧ openCount n mask.val = k then 1 else 0 :=
      square_cubePath_sum m hm (fun mask kk => if configurationKey n es b ps mask = query ∧ kk = k then 1 else 0)
    _ = _ := Fin.sum_univ_eq_sum_range (fun mask : Nat =>
      if configurationKey n es b ps mask = query ∧ openCount n mask = k then 1 else 0) (2^n)

#print axioms prunedParallel_coefficients_correct
#print axioms boundaryCubesLoop_coefficient
#print axioms enumerateCube_coefficient
#print axioms enumerateCube_refines_reference
#print axioms enumerateCubeMemo_refines
end SitePerc.Checker
