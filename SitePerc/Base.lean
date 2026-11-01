import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SitePerc

abbrev Vertex := ℤ × ℤ
abbrev Configuration (A : Type) := A → Bool
abbrev Parameter := {p : ℝ // p ∈ Set.Icc (0 : ℝ) 1}

noncomputable def siteMeasure {A : Type} (p : Parameter) :
    Measure (Configuration A) :=
  Measure.infinitePi (fun _ : A => bernoulliMeasure true false p)

instance siteMeasure_probability {A : Type} (p : Parameter) :
    IsProbabilityMeasure (siteMeasure (A := A) p) := by
  unfold siteMeasure
  infer_instance

def square : SimpleGraph Vertex :=
  SimpleGraph.fromRel (fun u v =>
    (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1))

def diagonalRelation (keep : Vertex → Prop) (u v : Vertex) : Prop :=
  ∃ z : Vertex, (z.1 + z.2) % 2 = 0 ∧ keep z ∧
    ((u = z ∧ v = (z.1 + 1, z.2 + 1)) ∨
     (u = (z.1 + 1, z.2) ∧ v = (z.1, z.2 + 1)))

def decorated (keep : Vertex → Prop) : SimpleGraph Vertex :=
  square ⊔ SimpleGraph.fromRel (diagonalRelation keep)

def lineLattice : SimpleGraph Vertex := decorated (fun _ => True)
def intermediate : SimpleGraph Vertex :=
  decorated (fun z => z.1 % 6 = 5 ∨ z.2 % 6 = 5)

def siteGraph {A : Type} (G : SimpleGraph A) (ω : Configuration A) : SimpleGraph A :=
  SimpleGraph.fromRel (fun u v => G.Adj u v ∧ ω u = true ∧ ω v = true)

def openCluster {A : Type} (G : SimpleGraph A) (ω : Configuration A) (v : A) : Set A :=
  {w | ω w = true ∧ (siteGraph G ω).Reachable v w}

def infiniteAt {A : Type} (G : SimpleGraph A) (v : A) : Set (Configuration A) :=
  {ω | ω v = true ∧ (openCluster G ω v).Infinite}

def infiniteExists {A : Type} (G : SimpleGraph A) : Set (Configuration A) :=
  {ω | ∃ v, ω ∈ infiniteAt G v}

noncomputable def theta (G : SimpleGraph Vertex) (p : Parameter) (v : Vertex) : ℝ≥0∞ :=
  siteMeasure p (infiniteAt G v)
noncomputable def infiniteProbability (G : SimpleGraph Vertex) (p : Parameter) : ℝ≥0∞ :=
  siteMeasure p (infiniteExists G)

noncomputable def pcSite : ℝ :=
  sInf {p : ℝ | ∃ hp : p ∈ Set.Icc (0 : ℝ) 1,
    0 < theta square ⟨p, hp⟩ (0, 0)}

abbrev Cell (m : ℕ) := Fin m × Fin m
abbrev Boundary (m : ℕ) := {v : Cell m //
  v.1.val = 0 ∨ v.1.val + 1 = m ∨ v.2.val = 0 ∨ v.2.val + 1 = m}

def embed (m : ℕ) (shift i : Vertex) (u : Cell m) : Vertex :=
  ((m : ℤ) * i.1 + shift.1 + u.1.val,
   (m : ℤ) * i.2 + shift.2 + u.2.val)

def tileGraph (G : SimpleGraph Vertex) (m : ℕ) (shift i : Vertex) : SimpleGraph (Cell m) :=
  G.comap (embed m shift i)

structure BoundaryState (B : Type) where
  opened : B → Bool
  connected : B → B → Bool

def stateLE {B : Type} (s t : BoundaryState B) : Prop :=
  (∀ b, s.opened b = true → t.opened b = true) ∧
  (∀ b c, s.opened b = true → s.opened c = true →
    s.connected b c = true → t.connected b c = true)

def stateUpper {B : Type} (U : Set (BoundaryState B)) : Prop :=
  ∀ s t, s ∈ U → stateLE s t → t ∈ U

noncomputable def localState (G : SimpleGraph Vertex) (m : ℕ) (shift i : Vertex)
    (ω : Configuration (Cell m)) : BoundaryState (Boundary m) := by
  classical
  exact { opened := fun b => ω b.val
          connected := fun b c => decide
            ((siteGraph (tileGraph G m shift i) ω).Reachable b.val c.val) }

def boundaryDominates (m : ℕ) (shift : Vertex) (G H : SimpleGraph Vertex)
    (q p : Parameter) : Prop :=
  ∀ i (U : Set (BoundaryState (Boundary m))), stateUpper U →
    siteMeasure q (localState G m shift i ⁻¹' U) ≤
    siteMeasure p (localState H m shift i ⁻¹' U)

def substitutionGeometry (m : ℕ) (shift : Vertex) (G H : SimpleGraph Vertex) : Prop :=
  ∀ i j : Vertex, i ≠ j → ∀ u v : Cell m,
    (G.Adj (embed m shift i u) (embed m shift j v) ↔
      H.Adj (embed m shift i u) (embed m shift j v)) ∧
    ((G.Adj (embed m shift i u) (embed m shift j v) ∨
      H.Adj (embed m shift i u) (embed m shift j v)) →
      (u.1.val = 0 ∨ u.1.val + 1 = m ∨ u.2.val = 0 ∨ u.2.val + 1 = m) ∧
      (v.1.val = 0 ∨ v.1.val + 1 = m ∨ v.2.val = 0 ∨ v.2.val + 1 = m))

structure FiniteLaw (S : Type) [Fintype S] where
  mass : S → ℝ
  nonnegative : ∀ s, 0 ≤ mass s
  total : ∑ s, mass s = 1

def finiteDominates {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) : Prop :=
  ∀ U : Finset S, (∀ x y, x ∈ U → x ≤ y → y ∈ U) →
    ∑ s ∈ U, ν.mass s ≤ ∑ s ∈ U, μ.mass s

def monotoneCoupling {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) : Prop :=
  ∃ π : S → S → ℝ, (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y, π x y = ν.mass x) ∧
    (∀ y, ∑ x, π x y = μ.mass y) ∧ (∀ x y, 0 < π x y → x ≤ y)

structure RoundedFlow {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) where
  scale : ℕ
  scale_positive : 0 < scale
  bottom : S
  bottom_le : ∀ s, bottom ≤ s
  supply : S → ℤ
  capacity : S → ℤ
  absorbed : S → ℤ
  edge : S → S → ℤ
  supply_nonnegative : ∀ s, 0 ≤ supply s
  capacity_nonnegative : ∀ s, 0 ≤ capacity s
  absorbed_bounds : ∀ s, 0 ≤ absorbed s ∧ absorbed s ≤ capacity s
  edge_nonnegative : ∀ x y, 0 ≤ edge x y
  edge_increasing : ∀ x y, 0 < edge x y → x ≤ y
  bottom_supply : supply bottom = 0
  source_rounds_up : ∀ s, s ≠ bottom → (scale : ℝ) * ν.mass s ≤ supply s
  sink_rounds_down : ∀ s, (capacity s : ℝ) ≤ (scale : ℝ) * μ.mass s
  conservation : ∀ s, supply s + ∑ x, edge x s = absorbed s + ∑ y, edge s y

noncomputable def orbitMass {S Q : Type} [Fintype S] [DecidableEq Q]
    (w : S → ℝ) (quot : S → Q) (a : Q) : ℝ := ∑ s, if quot s = a then w s else 0

abbrev D4 := DihedralGroup 4

abbrev BondIndex := Vertex × Bool

def bondGraph (ω : Configuration BondIndex) : SimpleGraph Vertex :=
  SimpleGraph.fromRel (fun u v =>
    (v = (u.1 + 1, u.2) ∧ ω (u, true) = true) ∨
    (v = (u.1, u.2 + 1) ∧ ω (u, false) = true))

noncomputable def bondInfiniteProbability (p : Parameter) : ℝ≥0∞ :=
  siteMeasure p {ω | ∃ v : Vertex, {w | (bondGraph ω).Reachable v w}.Infinite}

def KestenAboveHalf : Prop :=
  ∀ p : Parameter, (1 / 2 : ℝ) < p.val → 0 < bondInfiniteProbability p

noncomputable def q0 : Parameter := ⟨5001 / 10000, by norm_num⟩
noncomputable def p1 : Parameter := ⟨117 / 200, by norm_num⟩
noncomputable def p2 : Parameter := ⟨79 / 125, by norm_num⟩

abbrev Board (n : ℕ) := Fin (n + 1) × Fin (n + 1)
abbrev Draws (n : ℕ) := Fin ((n + 1) ^ 2) → Board n

def boardGraph (n : ℕ) : SimpleGraph (Board n) :=
  SimpleGraph.fromRel (fun u v =>
    (v.1.val = u.1.val + 1 ∧ v.2 = u.2) ∨
    (v.1 = u.1 ∧ v.2.val = u.2.val + 1))

noncomputable def largestCluster {A : Type} [Fintype A]
    (G : SimpleGraph A) (ω : Configuration A) : ℕ := by
  classical
  exact Finset.univ.sup (fun v =>
    (Finset.univ.filter (fun w => ω w = true ∧ (siteGraph G ω).Reachable v w)).card)

noncomputable def completed (n : ℕ) (draw : Draws n) : Configuration (Board n) := by
  classical
  exact fun v => decide (∃ i, draw i = v)

noncomputable def roadLaw (n : ℕ) : Measure (Draws n) :=
  (Fintype.card (Draws n) : ℝ≥0∞)⁻¹ • Measure.count

noncomputable def roadDensity (n : ℕ) (draw : Draws n) : ℝ :=
  (largestCluster (boardGraph n) (completed n draw) : ℝ) / (n + 1) ^ 2
noncomputable def iidDensity (n : ℕ) (ω : Configuration (Board n)) : ℝ :=
  (largestCluster (boardGraph n) ω : ℝ) / (n + 1) ^ 2
noncomputable def thetaReal (p : Parameter) : ℝ := (theta square p (0, 0)).toReal

def ConvergesInProbability {A : ℕ → Type} [∀ n, MeasurableSpace (A n)]
    (μ : ∀ n, Measure (A n)) (X : ∀ n, A n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {x | ε < |X n x - a|}) atTop (𝓝 0)

def SupercriticalGiantDensity : Prop :=
  ∀ p : Parameter, pcSite < p.val →
    ConvergesInProbability (fun n => siteMeasure (A := Board n) p) iidDensity (thetaReal p)

noncomputable def roadParameter : Parameter :=
  ⟨1 - Real.exp (-1), by
    constructor
    · have h := (Real.exp_le_one_iff).mpr (show (-1 : ℝ) ≤ 0 by norm_num)
      linarith
    · have h := Real.exp_pos (-1)
      linarith⟩

end SitePerc
