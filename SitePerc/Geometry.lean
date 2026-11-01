import SitePerc.Base
import Mathlib.Tactic

/-! Integer tile geometry and the square-bond/line-lattice correspondence. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false

namespace SitePerc

/-- Division with remainder recovers the tile coordinate. -/
theorem tile_axis_quotient (m : ℕ) (hm : 0 < m) (i : ℤ) (u : Fin m) :
    ((m : ℤ) * i + (u.val : ℤ)) / m = i := by
  have hm0 : (m : ℤ) ≠ 0 := by omega
  rw [Int.mul_add_ediv_left i _ hm0, Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast u.isLt)]
  omega

/-- A positive-size translated tiling is a genuine partition of all integer sites. -/
theorem embed_bijective (m : ℕ) (hm : 0 < m) (shift : Vertex) :
    Function.Bijective (fun t : Vertex × Cell m => embed m shift t.1 t.2) := by
  constructor
  · rintro ⟨i,u⟩ ⟨j,v⟩ h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [embed] at hx hy
    have hx' : (m : ℤ) * i.1 + (u.1.val : ℤ) = m * j.1 + (v.1.val : ℤ) := by omega
    have hy' : (m : ℤ) * i.2 + (u.2.val : ℤ) = m * j.2 + (v.2.val : ℤ) := by omega
    have hix : i.1 = j.1 := by
      simpa only [tile_axis_quotient m hm] using congrArg (fun a : ℤ => a / m) hx'
    have hiy : i.2 = j.2 := by
      simpa only [tile_axis_quotient m hm] using congrArg (fun a : ℤ => a / m) hy'
    have hi : i = j := Prod.ext hix hiy
    have hu : u = v := by
      apply Prod.ext <;> apply Fin.ext
      · simp only [hix] at hx'
        omega
      · simp only [hiy] at hy'
        omega
    exact Prod.ext hi hu
  · intro x
    have hmz : (0 : ℤ) < m := by exact_mod_cast hm
    have rem (a : ℤ) : (a % (m : ℤ)).toNat < m := by
      have h0 := Int.emod_nonneg a (ne_of_gt hmz)
      have h1 := Int.emod_lt_of_pos a hmz
      omega
    refine ⟨(((x.1-shift.1)/(m : ℤ), (x.2-shift.2)/(m : ℤ)),
      (⟨((x.1-shift.1) % (m : ℤ)).toNat, rem _⟩,
       ⟨((x.2-shift.2) % (m : ℤ)).toNat, rem _⟩)), ?_⟩
    apply Prod.ext <;> dsimp [embed]
    · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hmz))]
      have h := Int.mul_ediv_add_emod (x.1-shift.1) (m : ℤ)
      omega
    · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hmz))]
      have h := Int.mul_ediv_add_emod (x.2-shift.2) (m : ℤ)
      omega

/-- Forward map is exactly `embed`; its inverse is the unique tile decomposition. -/
noncomputable def tileEquiv (m : ℕ) (hm : 0 < m) (shift : Vertex) :
    (Vertex × Cell m) ≃ Vertex :=
  Equiv.ofBijective (fun t => embed m shift t.1 t.2) (embed_bijective m hm shift)

@[simp] theorem tileEquiv_apply (m : ℕ) (hm : 0 < m) (shift : Vertex)
    (t : Vertex × Cell m) : tileEquiv m hm shift t = embed m shift t.1 t.2 := rfl

/-- Every decorated edge changes each coordinate by at most one. -/
theorem decorated_adj_near {keep : Vertex → Prop} {a b : Vertex}
    (h : (decorated keep).Adj a b) :
    a.1 ≤ b.1+1 ∧ b.1 ≤ a.1+1 ∧ a.2 ≤ b.2+1 ∧ b.2 ≤ a.2+1 := by
  rcases h with h | h
  · rcases h with ⟨_, (h | h)⟩ <;> rcases h with h | h <;> omega
  · rcases h with ⟨_, (h | h)⟩
    all_goals
      rcases h with ⟨z, _, _, h | h⟩
      all_goals
        rcases h with ⟨rfl,rfl⟩
        dsimp
        omega

/-- A nearest- or diagonal-neighbour edge crossing two six-tiles has perimeter endpoints. -/
theorem six_cross_perimeter (shift i j : Vertex) (hij : i ≠ j) (u v : Cell 6)
    (h : let a := embed 6 shift i u; let b := embed 6 shift j v;
      a.1 ≤ b.1+1 ∧ b.1 ≤ a.1+1 ∧ a.2 ≤ b.2+1 ∧ b.2 ≤ a.2+1) :
    (u.1.val = 0 ∨ u.1.val+1 = 6 ∨ u.2.val = 0 ∨ u.2.val+1 = 6) ∧
    (v.1.val = 0 ∨ v.1.val+1 = 6 ∨ v.2.val = 0 ∨ v.2.val+1 = 6) := by
  have hi : ¬(i.1 = j.1 ∧ i.2 = j.2) := fun e => hij (Prod.ext e.1 e.2)
  have hu1 := u.1.isLt
  have hu2 := u.2.isLt
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  dsimp [embed] at h
  norm_num only [Nat.cast_ofNat] at h
  constructor <;> omega

private theorem stage1_cross_diagonal (i j : Vertex) (hij : i ≠ j) (u v : Cell 6)
    (h : diagonalRelation (fun _ => True) (embed 6 (0,0) i u) (embed 6 (0,0) j v)) :
    diagonalRelation (fun z => z.1 % 6 = 5 ∨ z.2 % 6 = 5)
      (embed 6 (0,0) i u) (embed 6 (0,0) j v) := by
  rcases h with ⟨z, hz, _, hd⟩
  refine ⟨z, hz, ?_, hd⟩
  have hi : ¬(i.1 = j.1 ∧ i.2 = j.2) := fun e => hij (Prod.ext e.1 e.2)
  have hu1 := u.1.isLt
  have hu2 := u.2.isLt
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  rcases hd with ⟨hu,hv⟩ | ⟨hu,hv⟩
  all_goals
    have huX := congrArg Prod.fst hu
    have huY := congrArg Prod.snd hu
    have hvX := congrArg Prod.fst hv
    have hvY := congrArg Prod.snd hv
    dsimp [embed] at huX huY hvX hvY
    norm_num only [Nat.cast_ofNat] at huX huY hvX hvY
    omega

private theorem stage2_no_cross_diagonal (i j : Vertex) (hij : i ≠ j) (u v : Cell 6) :
    ¬diagonalRelation (fun z => z.1 % 6 = 5 ∨ z.2 % 6 = 5)
      (embed 6 (3,3) i u) (embed 6 (3,3) j v) := by
  rintro ⟨z, hz, hk, hd⟩
  have hi : ¬(i.1 = j.1 ∧ i.2 = j.2) := fun e => hij (Prod.ext e.1 e.2)
  have hu1 := u.1.isLt
  have hu2 := u.2.isLt
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  rcases hd with ⟨hu,hv⟩ | ⟨hu,hv⟩
  all_goals
    have huX := congrArg Prod.fst hu
    have huY := congrArg Prod.snd hu
    have hvX := congrArg Prod.fst hv
    have hvY := congrArg Prod.snd hv
    dsimp [embed] at huX huY hvX hvY
    norm_num only [Nat.cast_ofNat] at huX huY hvX hvY
    omega

/-- Stage one, on all integer tiles, not a finite-window check. -/
theorem stage1_geometry : substitutionGeometry 6 (0,0) lineLattice intermediate := by
  intro i j hij u v
  constructor
  · constructor
    · rintro (hs | ⟨hne, hd | hd⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨hne, Or.inl (stage1_cross_diagonal i j hij u v hd)⟩
      · exact Or.inr ⟨hne, Or.inr (stage1_cross_diagonal j i hij.symm v u hd)⟩
    · rintro (hs | ⟨hne, hd | hd⟩)
      · exact Or.inl hs
      · rcases hd with ⟨z,hz,_,h⟩
        exact Or.inr ⟨hne, Or.inl ⟨z,hz,True.intro,h⟩⟩
      · rcases hd with ⟨z,hz,_,h⟩
        exact Or.inr ⟨hne, Or.inr ⟨z,hz,True.intro,h⟩⟩
  · intro h
    rcases h with h | h
    · exact six_cross_perimeter _ _ _ hij _ _ (decorated_adj_near h)
    · exact six_cross_perimeter _ _ _ hij _ _ (decorated_adj_near h)

/-- Stage two, using the actual shifted periodic intermediate lattice. -/
theorem stage2_geometry : substitutionGeometry 6 (3,3) intermediate square := by
  intro i j hij u v
  constructor
  · constructor
    · rintro (hs | ⟨_, hd | hd⟩)
      · exact hs
      · exact (stage2_no_cross_diagonal i j hij u v hd).elim
      · exact (stage2_no_cross_diagonal j i hij.symm v u hd).elim
    · exact Or.inl
  · intro h
    rcases h with h | h
    · exact six_cross_perimeter _ _ _ hij _ _ (decorated_adj_near h)
    · exact six_cross_perimeter _ _ _ hij _ _
        (decorated_adj_near (keep := fun _ => True) (Or.inl h))

/-- Translation by an arbitrary six-period vector. -/
def translateSix (i v : Vertex) : Vertex := (v.1+6*i.1,v.2+6*i.2)

private theorem square_translateSix (i a b : Vertex) :
    square.Adj (translateSix i a) (translateSix i b) ↔ square.Adj a b := by
  simp only [square, SimpleGraph.fromRel_adj, translateSix, ne_eq, Prod.ext_iff]
  omega

private theorem diagonal_translateSix {i : Vertex} (keep : Vertex → Prop)
    (hk : ∀ z, keep (translateSix i z) ↔ keep z) (a b : Vertex) :
    diagonalRelation keep (translateSix i a) (translateSix i b) ↔ diagonalRelation keep a b := by
  constructor
  · rintro ⟨z,hz,hkeep,hd⟩
    let w : Vertex := (z.1-6*i.1,z.2-6*i.2)
    have hwz : translateSix i w = z := by apply Prod.ext <;> dsimp [w,translateSix] <;> omega
    refine ⟨w, by dsimp [w]; omega, (hk w).mp (hwz.symm ▸ hkeep), ?_⟩
    rcases hd with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · left
      constructor <;> apply Prod.ext
      all_goals
        have haX := congrArg Prod.fst ha
        have haY := congrArg Prod.snd ha
        have hbX := congrArg Prod.fst hb
        have hbY := congrArg Prod.snd hb
        dsimp [translateSix,w] at *
        omega
    · right
      constructor <;> apply Prod.ext
      all_goals
        have haX := congrArg Prod.fst ha
        have haY := congrArg Prod.snd ha
        have hbX := congrArg Prod.fst hb
        have hbY := congrArg Prod.snd hb
        dsimp [translateSix,w] at *
        omega
  · rintro ⟨z,hz,hkeep,hd⟩
    refine ⟨translateSix i z, by dsimp [translateSix]; omega, (hk z).mpr hkeep, ?_⟩
    rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left
      constructor
      · rfl
      · apply Prod.ext <;> dsimp [translateSix] <;> omega
    · right
      constructor <;> apply Prod.ext <;> dsimp [translateSix] <;> omega

private theorem decorated_translateSix {i : Vertex} (keep : Vertex → Prop)
    (hk : ∀ z, keep (translateSix i z) ↔ keep z) (a b : Vertex) :
    (decorated keep).Adj (translateSix i a) (translateSix i b) ↔ (decorated keep).Adj a b := by
  simp only [decorated, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj,
    square_translateSix, diagonal_translateSix keep hk]
  have hn : translateSix i a = translateSix i b ↔ a = b := by
    simp only [translateSix,Prod.mk.injEq,Prod.ext_iff]
    omega
  simp only [ne_eq,hn]

private theorem embed_six_translate (shift i : Vertex) (u : Cell 6) :
    embed 6 shift i u = translateSix i (embed 6 shift (0,0) u) := by
  apply Prod.ext <;> dsimp [embed,translateSix] <;> omega

/-- Every six-tile has exactly the same finite line-lattice graph. -/
theorem tileGraph_lineLattice_periodic (shift i : Vertex) :
    tileGraph lineLattice 6 shift i = tileGraph lineLattice 6 shift (0,0) := by
  ext u v
  change lineLattice.Adj (embed 6 shift i u) (embed 6 shift i v) ↔ _
  rw [embed_six_translate shift i u, embed_six_translate shift i v]
  exact decorated_translateSix (fun _ => True) (by simp) _ _

/-- In particular, the five-square stage-two graph is the same in every tile. -/
theorem tileGraph_intermediate_periodic (shift i : Vertex) :
    tileGraph intermediate 6 shift i = tileGraph intermediate 6 shift (0,0) := by
  ext u v
  change intermediate.Adj (embed 6 shift i u) (embed 6 shift i v) ↔ _
  rw [embed_six_translate shift i u, embed_six_translate shift i v]
  apply decorated_translateSix
  intro z
  dsimp [translateSix]
  omega

/-- Every six-tile has exactly the same ordinary square graph. -/
theorem tileGraph_square_periodic (shift i : Vertex) :
    tileGraph square 6 shift i = tileGraph square 6 shift (0,0) := by
  ext u v
  change square.Adj (embed 6 shift i u) (embed 6 shift i v) ↔ _
  rw [embed_six_translate shift i u, embed_six_translate shift i v]
  exact square_translateSix _ _ _

/-- Oriented east/north edge: its initial vertex. -/
def bondStart (e : BondIndex) : Vertex := e.1

/-- Oriented east/north edge: its final vertex. -/
def bondEnd (e : BondIndex) : Vertex :=
  if e.2 then (e.1.1+1,e.1.2) else (e.1.1,e.1.2+1)

/-- Incidence in the underlying square lattice. -/
def bondIncident (e : BondIndex) (v : Vertex) : Prop := v = bondStart e ∨ v = bondEnd e

def bondsShare (e f : BondIndex) : Prop :=
  bondStart e = bondStart f ∨ bondStart e = bondEnd f ∨
  bondEnd e = bondStart f ∨ bondEnd e = bondEnd f

/-- The genuine line graph of square-lattice edges, indexed without edge quotients. -/
def squareBondLine : SimpleGraph BondIndex where
  Adj e f := e ≠ f ∧ bondsShare e f
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Midpoint rotation and translation, in integral coordinates. -/
def bondToSite (e : BondIndex) : Vertex :=
  if e.2 then (e.1.1+e.1.2+1,e.1.2-e.1.1)
  else (e.1.1+e.1.2+1,e.1.2-e.1.1+1)

theorem bondToSite_bijective : Function.Bijective bondToSite := by
  constructor
  · rintro ⟨⟨a,b⟩,d⟩ ⟨⟨c,e⟩,f⟩ h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    cases d <;> cases f <;> simp [bondToSite] at hx hy ⊢ <;> omega
  · rintro ⟨x,y⟩
    by_cases h : (x+y) % 2 = 0
    · refine ⟨(((x-y)/2,(x+y-2)/2),false), ?_⟩
      simp only [bondToSite, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
      constructor <;> omega
    · refine ⟨(((x-y-1)/2,(x+y-1)/2),true), ?_⟩
      simp only [bondToSite, ↓reduceIte, Prod.mk.injEq]
      constructor <;> omega

noncomputable def bondSiteEquiv : BondIndex ≃ Vertex :=
  Equiv.ofBijective bondToSite bondToSite_bijective

@[simp] theorem bondSiteEquiv_apply (e : BondIndex) : bondSiteEquiv e = bondToSite e := rfl

private theorem square_adj_coordinates (a b : Vertex) : square.Adj a b ↔
    (b.1=a.1+1 ∧ b.2=a.2) ∨ (a.1=b.1+1 ∧ a.2=b.2) ∨
    (b.1=a.1 ∧ b.2=a.2+1) ∨ (a.1=b.1 ∧ a.2=b.2+1) := by
  simp only [square, SimpleGraph.fromRel_adj, ne_eq, Prod.ext_iff]
  omega

private theorem diagonal_adj_coordinates (a b : Vertex) :
    (SimpleGraph.fromRel (diagonalRelation (fun _ => True))).Adj a b ↔
    (b.1=a.1+1 ∧ b.2=a.2+1 ∧ (a.1+a.2)%2=0) ∨
    (a.1=b.1+1 ∧ a.2=b.2+1 ∧ (a.1+a.2)%2=0) ∨
    (b.1=a.1+1 ∧ a.2=b.2+1 ∧ (a.1+a.2)%2=1) ∨
    (a.1=b.1+1 ∧ b.2=a.2+1 ∧ (a.1+a.2)%2=1) := by
  constructor
  · rintro ⟨_, h | h⟩
    all_goals
      rcases h with ⟨z,hz,_,hd | hd⟩
      all_goals
        rcases hd with ⟨ha,hb⟩
        have haX := congrArg Prod.fst ha
        have haY := congrArg Prod.snd ha
        have hbX := congrArg Prod.fst hb
        have hbY := congrArg Prod.snd hb
        dsimp at haX haY hbX hbY
        omega
  · intro h
    have hne : a ≠ b := by
      intro he
      have hX := congrArg Prod.fst he
      have hY := congrArg Prod.snd he
      omega
    refine ⟨hne, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl ⟨a,h.2.2,True.intro,Or.inl ⟨rfl, Prod.ext h.1 h.2.1⟩⟩
    · exact Or.inr ⟨b,by omega,True.intro,Or.inl ⟨rfl, Prod.ext h.1 h.2.1⟩⟩
    · refine Or.inr ⟨(a.1,b.2),by dsimp; omega,True.intro,Or.inr ⟨?_,?_⟩⟩
      · apply Prod.ext <;> dsimp <;> omega
      · apply Prod.ext <;> dsimp <;> omega
    · refine Or.inl ⟨(b.1,a.2),by dsimp; omega,True.intro,Or.inr ⟨?_,?_⟩⟩
      · apply Prod.ext <;> dsimp <;> omega
      · apply Prod.ext <;> dsimp <;> omega

/-- Explicit adjacency formula for the actual checkerboard line lattice. -/
theorem lineLattice_adj_coordinates (a b : Vertex) : lineLattice.Adj a b ↔
    ((b.1=a.1+1 ∧ b.2=a.2) ∨ (a.1=b.1+1 ∧ a.2=b.2) ∨
     (b.1=a.1 ∧ b.2=a.2+1) ∨ (a.1=b.1 ∧ a.2=b.2+1)) ∨
    ((b.1=a.1+1 ∧ b.2=a.2+1 ∧ (a.1+a.2)%2=0) ∨
     (a.1=b.1+1 ∧ a.2=b.2+1 ∧ (a.1+a.2)%2=0) ∨
     (b.1=a.1+1 ∧ a.2=b.2+1 ∧ (a.1+a.2)%2=1) ∨
     (a.1=b.1+1 ∧ b.2=a.2+1 ∧ (a.1+a.2)%2=1)) := by
  rw [lineLattice, decorated, SimpleGraph.sup_adj, square_adj_coordinates, diagonal_adj_coordinates]

/-- Adjacency is precisely shared-endpoint incidence of two different square bonds. -/
theorem bondToSite_adj_iff (e f : BondIndex) :
    lineLattice.Adj (bondToSite e) (bondToSite f) ↔ squareBondLine.Adj e f := by
  rw [lineLattice_adj_coordinates]
  rcases e with ⟨⟨a,b⟩,d⟩
  rcases f with ⟨⟨c,e⟩,f⟩
  cases d <;> cases f <;>
    simp only [bondToSite, Bool.false_eq_true, ↓reduceIte, squareBondLine, bondsShare,
      bondStart, bondEnd, ne_eq, Prod.mk.injEq]
  all_goals
    constructor
    · intro h
      rcases h with (h | h | h | h) | (h | h | h | h)
      all_goals
        constructor
        · intro he
          simp only [Bool.false_eq_true, Bool.true_eq_false, and_true, and_false] at he <;> omega
        · omega
    · rintro ⟨hne, h | h | h | h⟩
      all_goals
        simp only [Bool.false_eq_true, Bool.true_eq_false, and_true, and_false] at hne
        first
        | (refine Or.inl (Or.inl ⟨?_,?_⟩) <;> omega)
        | (refine Or.inl (Or.inr (Or.inl ⟨?_,?_⟩)) <;> omega)
        | (refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_,?_⟩))) <;> omega)
        | (refine Or.inl (Or.inr (Or.inr (Or.inr ⟨?_,?_⟩))) <;> omega)
        | (refine Or.inr (Or.inl ⟨?_,?_,?_⟩) <;> omega)
        | (refine Or.inr (Or.inr (Or.inl ⟨?_,?_,?_⟩)) <;> omega)
        | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_,?_,?_⟩))) <;> omega)
        | (refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_,?_,?_⟩))) <;> omega)

/-- An isomorphism of the genuine infinite graphs, before imposing a configuration. -/
noncomputable def bondLineIso : squareBondLine ≃g lineLattice where
  toEquiv := bondSiteEquiv
  map_rel_iff' := bondToSite_adj_iff _ _

private theorem geometry_siteGraph_adj_iff {A : Type} (G : SimpleGraph A)
    (ω : Configuration A) (u v : A) :
    (siteGraph G ω).Adj u v ↔ G.Adj u v ∧ ω u = true ∧ ω v = true := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm,h.2.2,h.2.1⟩
  · intro h
    exact ⟨h.1.ne,Or.inl h⟩

/-- An open bond is exactly one edge of the configured square graph. -/
theorem bondGraph_adj_incidence (ω : Configuration BondIndex) (u v : Vertex) :
    (bondGraph ω).Adj u v ↔ ∃ e : BondIndex, ω e = true ∧
      ((u = bondStart e ∧ v = bondEnd e) ∨ (u = bondEnd e ∧ v = bondStart e)) := by
  constructor
  · rintro ⟨_, (h | h) | (h | h)⟩
    · exact ⟨(u,true),h.2,Or.inl ⟨rfl,h.1⟩⟩
    · exact ⟨(u,false),h.2,Or.inl ⟨rfl,h.1⟩⟩
    · exact ⟨(v,true),h.2,Or.inr ⟨h.1,rfl⟩⟩
    · exact ⟨(v,false),h.2,Or.inr ⟨h.1,rfl⟩⟩
  · rintro ⟨⟨⟨a,b⟩,d⟩,he,hd⟩
    cases d <;> rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [bondGraph,SimpleGraph.fromRel_adj,bondStart,bondEnd,he,Prod.mk.injEq]

private theorem open_bond_reachable (ω : Configuration BondIndex) (e : BondIndex)
    (he : ω e = true) : (bondGraph ω).Reachable (bondStart e) (bondEnd e) :=
  ((bondGraph_adj_incidence ω _ _).mpr ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩).reachable

private theorem open_bond_incident_reachable (ω : Configuration BondIndex) (e : BondIndex)
    (he : ω e = true) {v : Vertex} (h : bondIncident e v) :
    (bondGraph ω).Reachable (bondStart e) v := by
  rcases h with rfl | rfl
  · exact .rfl
  · exact open_bond_reachable ω e he

private theorem bondsShare_of_common {e f : BondIndex} {v : Vertex}
    (he : bondIncident e v) (hf : bondIncident f v) : bondsShare e f := by
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Or.inl (he.symm.trans hf)
  · exact Or.inr (Or.inl (he.symm.trans hf))
  · exact Or.inr (Or.inr (Or.inl (he.symm.trans hf)))
  · exact Or.inr (Or.inr (Or.inr (he.symm.trans hf)))

private theorem open_bonds_share_reachable (ω : Configuration BondIndex) (e f : BondIndex)
    (he : ω e = true) (hf : ω f = true) (hs : bondsShare e f) :
    (siteGraph squareBondLine ω).Reachable e f := by
  classical
  by_cases h : e = f
  · subst f
    exact .rfl
  · exact ((geometry_siteGraph_adj_iff squareBondLine ω e f).mpr ⟨⟨h,hs⟩,he,hf⟩).reachable

private theorem line_adj_to_bond_reachable (ω : Configuration BondIndex) {e f : BondIndex}
    (h : (siteGraph squareBondLine ω).Adj e f) :
    (bondGraph ω).Reachable (bondStart e) (bondStart f) := by
  obtain ⟨⟨_,hs⟩,he,hf⟩ := (geometry_siteGraph_adj_iff _ _ _ _).mp h
  have pe := open_bond_reachable ω e he
  have pf := open_bond_reachable ω f hf
  rcases hs with h | h | h | h
  · rw [h]
  · simpa only [h] using pf.symm
  · simpa only [h] using pe
  · exact pe.trans (by simpa only [h] using pf.symm)

/-- A finite open line-graph walk projects to finite bond connectivity. -/
theorem line_reachable_to_bond_reachable (ω : Configuration BondIndex) {e f : BondIndex}
    (h : (siteGraph squareBondLine ω).Reachable e f) :
    (bondGraph ω).Reachable (bondStart e) (bondStart f) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact .rfl
  | tail _ ha ih => exact ih.trans (line_adj_to_bond_reachable ω ha)

/-- A finite open bond walk lifts to line connectivity, retaining an incident open edge. -/
theorem bond_reachable_to_line (ω : Configuration BondIndex) (e : BondIndex)
    (he : ω e = true) {v : Vertex} (h : (bondGraph ω).Reachable (bondStart e) v) :
    ∃ f : BondIndex, ω f = true ∧ bondIncident f v ∧
      (siteGraph squareBondLine ω).Reachable e f := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨e,he,Or.inl rfl,.rfl⟩
  | @tail y z _ hyz ih =>
    obtain ⟨f,hf,hfy,hr⟩ := ih
    obtain ⟨g,hg,hd⟩ := (bondGraph_adj_incidence ω y z).mp hyz
    have hgy : bondIncident g y := by
      rcases hd with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hgz : bondIncident g z := by
      rcases hd with h | h
      · exact Or.inr h.2
      · exact Or.inl h.2
    exact ⟨g,hg,hgz,hr.trans (open_bonds_share_reachable ω f g hf hg
      (bondsShare_of_common hfy hgy))⟩

/-- Infinite edge components and infinite vertex components are equivalent.
The forward direction uses the two-element fibers of the initial-vertex map;
the reverse direction covers the vertex component by its two endpoint images. -/
theorem open_bond_infinite_iff (ω : Configuration BondIndex) (e : BondIndex)
    (he : ω e = true) :
    (openCluster squareBondLine ω e).Infinite ↔
      {v : Vertex | (bondGraph ω).Reachable (bondStart e) v}.Infinite := by
  constructor
  · intro hi hfin
    apply hi
    apply (hfin.prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
    intro f hf
    exact ⟨line_reachable_to_bond_reachable ω hf.2,Set.mem_univ _⟩
  · intro hi hfin
    apply hi
    apply ((hfin.image bondStart).union (hfin.image bondEnd)).subset
    intro v hv
    obtain ⟨f,hf,hfv,hr⟩ := bond_reachable_to_line ω e he hv
    rcases hfv with h | h
    · exact Or.inl ⟨f,⟨hf,hr⟩,h.symm⟩
    · exact Or.inr ⟨f,⟨hf,hr⟩,h.symm⟩

/-- Pathwise existence-event equality, with no infinite-ray hypothesis. -/
theorem bond_infinite_iff_line (ω : Configuration BondIndex) :
    (∃ v : Vertex, {w | (bondGraph ω).Reachable v w}.Infinite) ↔
      ω ∈ infiniteExists squareBondLine := by
  constructor
  · rintro ⟨v,hi⟩
    have hex : ∃ e : BondIndex, ω e = true ∧ bondIncident e v := by
      classical
      by_contra hn
      apply hi
      apply (Set.finite_singleton v).subset
      intro w hw
      obtain ⟨W⟩ := hw
      cases W with
      | nil => rfl
      | cons ha _ =>
        obtain ⟨e,he,hd⟩ := (bondGraph_adj_incidence ω _ _).mp ha
        apply False.elim
        apply hn
        refine ⟨e,he,?_⟩
        rcases hd with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
    obtain ⟨e,he,hev⟩ := hex
    have hr := open_bond_incident_reachable ω e he hev
    refine ⟨e,he,(open_bond_infinite_iff ω e he).mpr (hi.mono ?_)⟩
    intro w hw
    exact hr.trans hw
  · rintro ⟨e,he,hi⟩
    exact ⟨bondStart e,(open_bond_infinite_iff ω e he).mp hi⟩

/-- The measurable coordinate permutation induced by the actual edge bijection. -/
noncomputable def bondConfigurationEquiv :
    Configuration BondIndex ≃ᵐ Configuration Vertex :=
  MeasurableEquiv.piCongrLeft (fun _ : Vertex => Bool) bondSiteEquiv

@[simp] theorem bondConfigurationEquiv_apply (ω : Configuration BondIndex) (e : BondIndex) :
    bondConfigurationEquiv ω (bondToSite e) = ω e := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Vertex => Bool) bondSiteEquiv ω e

/-- The graph isomorphism commutes with the actual open configurations. -/
noncomputable def bondOpenLineIso (ω : Configuration BondIndex) :
    siteGraph squareBondLine ω ≃g siteGraph lineLattice (bondConfigurationEquiv ω) where
  toEquiv := bondSiteEquiv
  map_rel_iff' := by
    intro e f
    simp only [geometry_siteGraph_adj_iff,bondSiteEquiv_apply,
      bondConfigurationEquiv_apply,bondToSite_adj_iff]

/-- Entire clusters correspond, not merely finite induced subgraphs. -/
theorem bond_cluster_image (ω : Configuration BondIndex) (e : BondIndex) :
    bondToSite '' openCluster squareBondLine ω e =
      openCluster lineLattice (bondConfigurationEquiv ω) (bondToSite e) := by
  ext v
  obtain ⟨f,rfl⟩ := bondToSite_bijective.surjective v
  constructor
  · rintro ⟨g,hg,hgf⟩
    have hgf' : g = f := bondToSite_bijective.injective hgf
    subst g
    exact ⟨by simpa only [bondConfigurationEquiv_apply] using hg.1,
      (SimpleGraph.Iso.reachable_iff (φ := bondOpenLineIso ω)).mpr hg.2⟩
  · intro hv
    exact ⟨f,⟨by simpa only [bondConfigurationEquiv_apply] using hv.1,
      (SimpleGraph.Iso.reachable_iff (φ := bondOpenLineIso ω)).mp hv.2⟩,rfl⟩

/-- Reindexing preserves the existence of an infinite open cluster, pathwise. -/
theorem bondConfiguration_infiniteExists_iff (ω : Configuration BondIndex) :
    bondConfigurationEquiv ω ∈ infiniteExists lineLattice ↔
      ω ∈ infiniteExists squareBondLine := by
  constructor
  · rintro ⟨v,hv,hi⟩
    obtain ⟨e,rfl⟩ := bondToSite_bijective.surjective v
    refine ⟨e,by simpa only [bondConfigurationEquiv_apply] using hv,?_⟩
    apply (Set.infinite_image_iff bondToSite_bijective.injective.injOn).mp
    rw [bond_cluster_image]
    exact hi
  · rintro ⟨e,he,hi⟩
    refine ⟨bondToSite e,by simpa only [bondConfigurationEquiv_apply] using he,?_⟩
    rw [←bond_cluster_image]
    exact hi.image bondToSite_bijective.injective.injOn

/-- Infinite iid product laws are preserved by this explicit bond/site reindexing. -/
theorem bondConfigurationEquiv_measure (p : Parameter) :
    (siteMeasure (A := BondIndex) p).map bondConfigurationEquiv =
      siteMeasure (A := Vertex) p := by
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Vertex => bernoulliMeasure true false p) bondSiteEquiv

/-- Square-bond and checkerboard line-site percolation have identical infinity probabilities. -/
theorem line_graph_equivalence (p : Parameter) :
    bondInfiniteProbability p = infiniteProbability lineLattice p := by
  unfold bondInfiniteProbability infiniteProbability
  rw [←bondConfigurationEquiv_measure p, MeasurableEquiv.map_apply]
  congr 1
  ext ω
  exact (bond_infinite_iff_line ω).trans (bondConfiguration_infiniteExists_iff ω).symm

#print axioms stage1_geometry
#print axioms stage2_geometry
#print axioms line_graph_equivalence
#print axioms embed_bijective
#print axioms tileGraph_lineLattice_periodic
#print axioms tileGraph_intermediate_periodic
#print axioms tileGraph_square_periodic

end SitePerc
