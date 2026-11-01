import SitePerc.Checker.ConnectivityDefs
import Mathlib.Tactic

/-! Pure, kernel-checked connectivity core.  The native implementation is exactly
    this source; no foreign implementation is substituted. -/
namespace SitePerc.Checker
open Batteries





@[simp] theorem initUF_size (n : Nat) : (initUF n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [initUF, UnionFind.size] using congrArg Nat.succ ih

@[simp] theorem initUF_equiv (n a b : Nat) :
    UnionFind.Equiv (initUF n) a b ↔ a = b := by
  induction n with
  | zero => simp [initUF]
  | succ n ih => simpa [initUF] using ih



@[simp] theorem merge_size (u : UnionFind) (a b : Nat) :
    (merge u a b).size = u.size := by
  unfold merge
  split
  · simp [UnionFind.union, UnionFind.link, UnionFind.size]
  · rfl

theorem merge_equiv (u : UnionFind) (x y a b : Nat)
    (h : x < u.size ∧ y < u.size) :
    UnionFind.Equiv (merge u x y) a b ↔
      UnionFind.Equiv u a b ∨
      UnionFind.Equiv u a x ∧ UnionFind.Equiv u y b ∨
      UnionFind.Equiv u a y ∧ UnionFind.Equiv u x b := by
  simpa only [merge, dif_pos h] using
    (UnionFind.equiv_union (self:=u) (x:=⟨x,h.1⟩) (y:=⟨y,h.2⟩) (a:=a) (b:=b))



@[simp] theorem components_size (n : Nat) (es : List Edge) (ω : Nat → Bool) :
    (components n es ω).size = n := by
  induction es with
  | nil => simp [components]
  | cons e es ih => rcases e with ⟨a,b⟩; simp [components, ih]; split <;> simp [ih]



/-- Insertion never destroys any already established component equality. -/
theorem components_mono (n : Nat) (e : Edge) (es : List Edge) (ω : Nat → Bool)
    (a b : Nat) :
    UnionFind.Equiv (components n es ω) a b →
      UnionFind.Equiv (components n (e::es) ω) a b := by
  rcases e with ⟨x,y⟩
  intro h
  simp only [components]
  split
  · unfold merge; split
    · exact UnionFind.equiv_union.mpr (Or.inl h)
    · exact h
  · exact h

/-- Every open graph edge is merged; this is pointwise, not a total-mass test. -/
theorem components_edge (n : Nat) (es : List Edge) (ω : Nat → Bool)
    (hb : BoundedEdges n es) (e : Edge) (he : e ∈ es)
    (ho : ω e.1 = true ∧ ω e.2 = true) :
    UnionFind.Equiv (components n es ω) e.1 e.2 := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases f with ⟨x,y⟩
    rcases List.mem_cons.mp he with h | h
    · subst e
      have hv := hb (x,y) (by simp)
      simp only [components, ho.1, ho.2, Bool.and_self, ↓reduceIte]
      exact (merge_equiv _ x y x y (by simpa using hv)).mpr
        (Or.inr (Or.inl ⟨rfl,rfl⟩))
    · exact components_mono n (x,y) es ω _ _
        (ih (fun e he => hb e (by simp [he])) h)

/-- Least-equivalence semantics of the union-find fold. -/
theorem components_sound_relation (n : Nat) (es : List Edge) (ω : Nat → Bool)
    (hb : BoundedEdges n es) (R : Fin n → Fin n → Prop)
    (hr : Equivalence R)
    (hedge : ∀ a b : Fin n, (a.val,b.val) ∈ es →
      ω a.val = true → ω b.val = true → R a b)
    (a b : Fin n) :
    UnionFind.Equiv (components n es ω) a.val b.val → R a b := by
  induction es generalizing a b with
  | nil =>
    intro h
    have : a = b := Fin.ext ((initUF_equiv n _ _).mp h)
    subst b
    exact hr.refl a
  | cons e es ih =>
    rcases e with ⟨x,y⟩
    have hv := hb (x,y) (by simp)
    have hb' : BoundedEdges n es := fun e he => hb e (by simp [he])
    have he' : ∀ a b : Fin n, (a.val,b.val) ∈ es →
        ω a.val = true → ω b.val = true → R a b :=
      fun a b he => hedge a b (by simp [he])
    simp only [components]
    split
    · next ho =>
      have hop : ω x = true ∧ ω y = true := by simpa only [Bool.and_eq_true] using ho
      intro h
      rcases (merge_equiv _ x y _ _ (by simpa using hv)).mp h with h | ⟨hax,hyb⟩ | ⟨hay,hxb⟩
      · exact ih hb' he' a b h
      · exact hr.trans (ih hb' he' a ⟨x,hv.1⟩ hax)
          (hr.trans (hedge ⟨x,hv.1⟩ ⟨y,hv.2⟩ (by simp) hop.1 hop.2) (ih hb' he' ⟨y,hv.2⟩ b hyb))
      · exact hr.trans (ih hb' he' a ⟨y,hv.2⟩ hay)
          (hr.trans (hr.symm (hedge ⟨x,hv.1⟩ ⟨y,hv.2⟩ (by simp) hop.1 hop.2)) (ih hb' he' ⟨x,hv.1⟩ b hxb))
    · exact ih hb' he' a b

/-- Generic C7 semantic bridge: exact graph reachability, for arbitrary size,
    bounded edge list and Boolean configuration. -/
theorem components_correct (n : Nat) (es : List Edge) (ω : Nat → Bool)
    (hb : BoundedEdges n es) (a b : Fin n) :
    UnionFind.Equiv (components n es ω) a.val b.val ↔
      (openGraph n es ω).Reachable a b := by
  constructor
  · apply components_sound_relation n es ω hb _ (openGraph n es ω).reachable_is_equivalence
    intro x y he hx hy
    by_cases hxy : x = y
    · subst y; exact .rfl
    · exact SimpleGraph.Adj.reachable (by simp [openGraph, SimpleGraph.fromRel_adj, hxy, he, hx, hy])
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | @tail b c hbc hac ih =>
      apply UnionFind.Equiv.trans ih
      have he := (show b ≠ c ∧
        (((b.val,c.val) ∈ es ∧ ω b.val = true ∧ ω c.val = true) ∨
         ((c.val,b.val) ∈ es ∧ ω c.val = true ∧ ω b.val = true)) from by
          simpa only [openGraph, SimpleGraph.fromRel_adj] using hac)
      rcases he.2 with ⟨he,hb',hc'⟩ | ⟨he,hc',hb'⟩
      · exact components_edge n es ω hb (b.val,c.val) he ⟨hb',hc'⟩
      · exact (components_edge n es ω hb (c.val,b.val) he ⟨hc',hb'⟩).symm

#print axioms components_correct
end SitePerc.Checker
