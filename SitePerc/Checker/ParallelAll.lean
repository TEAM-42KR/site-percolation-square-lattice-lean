import SitePerc.Checker.ParallelDefs
import SitePerc.Checker.CheckerSoundness
import Mathlib.Tactic

namespace SitePerc.Checker

theorem rangeAll_eq_true (f : Nat → Bool) (count start : Nat) :
    rangeAll f count start = true ↔ ∀ j < count, f (start+j) = true := by
  induction count generalizing start with
  | zero => simp [rangeAll]
  | succ count ih =>
    rw [rangeAll,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨h0,hs⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs j (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega),fun j hj => by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (j+1) (by omega)⟩

theorem parallelArrayAll_eq_all {α : Type} (workers : Nat) (xs : Array α)
    (predicate : α → Bool) : parallelArrayAll workers xs predicate = xs.all predicate := by
  apply Bool.eq_iff_iff.mpr
  let w := max 1 workers
  let width := (xs.size+w-1)/w
  have hw : 0 < w := by dsimp [w]; omega
  have cover : xs.size ≤ w*width := ceil_partition_covers xs.size w hw
  have expand : parallelArrayAll workers xs predicate = true ↔
      ∀ i < w, ∀ j < width,
        (if h : i*width+j < xs.size then predicate xs[i*width+j] else true) = true := by
    change ((List.range w).map (fun i => Task.spawn (prio:=Task.Priority.dedicated) fun _ =>
      rangeAll (fun j => if h : i*width+j < xs.size then predicate xs[i*width+j] else true)
        width 0)).all Task.get = true ↔ _
    rw [List.all_map]
    simp only [Task.spawn,Task.get,List.all_eq_true,List.mem_range,Function.comp_apply,rangeAll_eq_true,Nat.zero_add]
  rw [expand,Array.all_eq_true]
  constructor
  · intro h i hi
    have hwidth : 0 < width := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hsize : xs.size ≤ 0 := by simpa only [hz,Nat.mul_zero] using cover
      exact Nat.not_lt_of_ge hsize (Nat.zero_lt_of_lt hi)
    have hdiv : i/width < w := by
      apply (Nat.div_lt_iff_lt_mul hwidth).mpr
      omega
    have hs := h (i/width) hdiv (i%width) (Nat.mod_lt i hwidth)
    have he : i/width*width+i%width = i := by simpa [Nat.mul_comm] using Nat.div_add_mod i width
    simp only [he,dif_pos hi] at hs
    exact hs
  · intro h i hi j hj
    split
    · next hidx => exact h _ hidx
    · rfl

@[simp] theorem reflectedArrayAll_eq_all {α : Type} (xs : Array α)
    (predicate : α → Bool) : reflectedArrayAll xs predicate = xs.all predicate := by
  unfold reflectedArrayAll
  split
  · rfl
  · exact parallelArrayAll_eq_all _ _ _

#print axioms parallelArrayAll_eq_all
#print axioms reflectedArrayAll_eq_all
end SitePerc.Checker
