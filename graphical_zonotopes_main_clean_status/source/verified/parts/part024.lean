module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

public import verified.parts.part023
import all verified.parts.part023

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart347
/- Source: Papers/GraphicalZonotopes/FourColorResource.lean -/







@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

def total (a : Fin 4 → ℕ) : ℕ := ∑ i,a i

def Balanced (a : Fin 4 → ℕ) : Prop :=
  (∀ i,0< a i) ∧ ∀ i,3*a i+3≤2*total a

theorem total_ge_four {a : Fin 4 → ℕ} (ha : ∀ i,0< a i) : 4≤ total a := by
  calc
    4=∑ i : Fin 4,(1 : ℕ) := by simp
    _≤ total a := sum_le_sum (fun i _ => ha i)

theorem total_update (a : Fin 4 → ℕ) (i : Fin 4) (k : ℕ) :
    total (update a i k)+a i=total a+k := by
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem pair_bound {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (i j : Fin 4) (hij : i≠ j) : a i+a j+2≤ total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> fin_cases j <;> simp [total,Fin.sum_univ_succ] at hij ⊢ <;> omega

theorem eq_one_of_total_four {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (hN : total a=4) : a=(fun _ => 1) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have hs : a 0+(a 1+(a 2+a 3))=4 := by
    simpa [total,Fin.sum_univ_succ] using hN
  have hall : a 0=1 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 :=
    ⟨by omega,by omega,by omega,by omega⟩
  funext i
  fin_cases i
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

/-- Removing one vertex from a largest part preserves the exact balance
inequalities. Reversing this removal gives strictly positive capacity in the
part to which the vertex is subsequently added. -/
theorem remove_largest {a : Fin 4 → ℕ} (ha : Balanced a) (hN : 4< total a) :
    ∃ i : Fin 4,1< a i ∧
      Balanced (update a i (a i-1)) ∧
      total (update a i (a i-1))+1=total a ∧
      3*(update a i (a i-1) i)+3<2*total (update a i (a i-1)) := by
  obtain ⟨i,_,hmax⟩ := exists_max_image (univ : Finset (Fin 4)) a (by simp)
  have hm : ∀ j,a j≤ a i := fun j => hmax j (mem_univ _)
  have hi : 1< a i := by
    by_contra hni
    have hs : total a≤4 := by
      calc
        total a≤∑ j : Fin 4,(1 : ℕ) := sum_le_sum (fun j _ => by have h := hm j;omega)
        _=4 := by simp
    omega
  let b := update a i (a i-1)
  have htotal : total b+1=total a := by
    have h := total_update a i (a i-1)
    dsimp only [b]
    omega
  have hbi : b i=a i-1 := by simp [b]
  have hb : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rw [hbi];omega
      · simpa [b,update_of_ne hji] using ha.1 j
    · intro j
      by_cases hji : j=i
      · subst j
        have h := ha.2 i
        rw [hbi]
        omega
      · have hp := pair_bound ha.1 i j (Ne.symm hji)
        have hmi := hm j
        have hjpos := ha.1 j
        have hbjeq : b j=a j := by simp [b,update_of_ne hji]
        rw [hbjeq]
        omega
  refine ⟨i,hi,hb,htotal,?_⟩
  have h := ha.2 i
  change 3*b i+3<2*total b
  rw [hbi]
  omega

/-- A finite sequence of color additions, starting with one vertex of each
color and using a color only when its triangle capacity is positive. -/
inductive Schedule : (Fin 4 → ℕ) → Prop
  | initial : Schedule (fun _ => 1)
  | add {a : Fin 4 → ℕ} (h : Schedule a) (i : Fin 4)
      (hcapacity : 3*a i+3<2*total a) : Schedule (update a i (a i+1))

/-- Every positive, balanced four-part size vector has a valid unbounded
attachment schedule. No bound on any part size is imposed. -/
theorem schedule_of_balanced {a : Fin 4 → ℕ} (ha : Balanced a) : Schedule a := by
  suffices ∀ N : ℕ,∀ a : Fin 4 → ℕ,total a=N → Balanced a → Schedule a from
    this (total a) a rfl ha
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a hN ha
    by_cases hfour : total a=4
    · rw [eq_one_of_total_four ha.1 hfour]
      exact Schedule.initial
    · have hgt : 4< total a := by have h := total_ge_four ha.1;omega
      obtain ⟨i,hi,hb,hbN,hcap⟩ := remove_largest ha hgt
      let b := update a i (a i-1)
      have hs : Schedule b := ih (total b) (by dsimp only [b];omega) b rfl hb
      have hstep := Schedule.add hs i hcap
      have he : update b i (b i+1)=a := by
        funext j
        by_cases hji : j=i
        · subst j
          simp only [b,update_self]
          omega
        · simp [b,update_of_ne hji]
      rwa [he] at hstep

end GraphicalZonotopes.FourColorResource

end
end
end BundlePart347

section BundlePart348
/- Source: Papers/GraphicalZonotopes/FourPartThreeTreeCounts.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.FourPartThreeTreeCounts
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def Proper (c : V → Fin 4) (G : SimpleGraph V) : Prop :=
  ∀ u v,G.Adj u v → c u≠ c v

def Avoids (c : V → Fin 4) (i : Fin 4) (T : Finset V) : Prop :=
  ∀ v∈T,c v≠ i

def missingFacet (c : V → Fin 4) (i : Fin 4) (D : Finset V) : Finset V :=
  D.filter (fun v => c v≠ i)

def avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4) (i : Fin 4) :
    Finset (Finset V) := (triangles G).filter (Avoids c i)

@[simp] theorem mem_avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4)
    (i : Fin 4) (T : Finset V) :
    T∈avoidingTriangles G c i ↔ T.card=3 ∧ G.IsClique T ∧ Avoids c i T := by
  simp only [avoidingTriangles,mem_filter,mem_triangles,and_assoc]

theorem color_injective_on_clique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : G.IsClique D) : Set.InjOn c D := by
  intro u hu v hv he
  by_contra huv
  exact hc u v (hD hu hv huv) he

theorem color_count_tetrahedron {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (D.filter (fun v => c v=i)).card=1 := by
  have hinj := color_injective_on_clique hc hcl
  have himage : (D.image c).card=4 := (card_image_iff.mpr hinj).trans hD
  have hsurj : D.image c=univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using himage.ge)
  have hi : i∈D.image c := by rw [hsurj]; simp
  obtain ⟨v,hv,hvi⟩ := mem_image.mp hi
  have he : D.filter (fun u => c u=i)={v} := by
    ext u
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨hu,hui⟩
      exact hinj hu hv (hui.trans hvi.symm)
    · rintro rfl
      exact ⟨hv,hvi⟩
  rw [he,card_singleton]

theorem missingFacet_card {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (missingFacet c i D).card=3 := by
  have h1 := color_count_tetrahedron hc hD hcl i
  have hsum := card_filter_add_card_filter_not (s := D) (fun v => c v=i)
  change (D.filter (fun v => c v=i)).card+(missingFacet c i D).card=D.card at hsum
  omega

theorem missingFacet_avoids (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    Avoids c i (missingFacet c i D) := fun v hv => (mem_filter.mp hv).2

theorem missingFacet_subset (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    missingFacet c i D⊆D := filter_subset _ _

theorem missingFacet_clique {G : SimpleGraph V} {c : V → Fin 4}
    {D : Finset V} (hcl : G.IsClique D) (i : Fin 4) :
    G.IsClique (missingFacet c i D) := by
  intro u hu v hv huv
  exact hcl (missingFacet_subset c i D hu) (missingFacet_subset c i D hv) huv

theorem avoiding_triangle_unique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D T : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (hT : T.card=3) (hTD : T⊆D) {i : Fin 4} (havoid : Avoids c i T) :
    T=missingFacet c i D := by
  apply eq_of_subset_of_card_le
  · intro v hv
    exact mem_filter.mpr ⟨hTD hv,havoid v hv⟩
  · rw [missingFacet_card hc hD hcl,hT]

theorem avoidingTriangles_mono {G H : SimpleGraph V} (hGH : G≤ H)
    (c : V → Fin 4) (i : Fin 4) :
    avoidingTriangles G c i⊆avoidingTriangles H c i := by
  intro T hT
  obtain ⟨ht,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (mem_avoidingTriangles _ _ _ _).mpr
    ⟨ht,fun u hu v hv huv => hGH (hcl hu hv huv),ha⟩

theorem missingFacet_mem {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : missingFacet c i D∈avoidingTriangles G c i :=
  (mem_avoidingTriangles _ _ _ _).mpr
    ⟨missingFacet_card hc hD hcl i,missingFacet_clique hcl i,missingFacet_avoids c i D⟩

theorem avoiding_subsets_singleton {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) :
    (avoidingTriangles G c i).filter (fun T => T⊆D)={missingFacet c i D} := by
  ext T
  simp only [mem_filter,mem_singleton]
  constructor
  · rintro ⟨hT,hTD⟩
    obtain ⟨ht,_,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    exact avoiding_triangle_unique hc hD hcl ht hTD ha
  · rintro rfl
    exact ⟨missingFacet_mem hc hD hcl i,missingFacet_subset c i D⟩

theorem avoidingTriangles_cliqueGraph {D : Finset V} (hD : D.card=4)
    {c : V → Fin 4} (hc : Proper c (cliqueGraph D)) (i : Fin 4) :
    avoidingTriangles (cliqueGraph D) c i={missingFacet c i D} := by
  have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
  rw [← avoiding_subsets_singleton hc hD hcl i]
  symm
  apply filter_eq_self.mpr
  intro T hT
  have hh := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (ThreeTreeOn.tetrahedron D hD).clique_subset_active (by omega) hh.2.1

theorem avoidingTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    {c : V → Fin 4} (hc : Proper c (G⊔attachmentStar u T)) (i : Fin 4) :
    avoidingTriangles (G⊔attachmentStar u T) c i =
      if i=c u then avoidingTriangles G c i
      else insert (missingFacet c i (insert u T)) (avoidingTriangles G c i) := by
  have huT : u∉T := fun hm => hu (hTS hm)
  have hD : (insert u T).card=4 := by rw [card_insert_of_notMem huT,hT]
  have hDcl := attached_tetrahedron_clique h hu hTS hcl
  have hM := missingFacet_mem hc hD hDcl i
  have hold := avoidingTriangles_mono (show G≤ G⊔attachmentStar u T from le_sup_left) c i
  ext A
  by_cases hi : i=c u
  · simp only [if_pos hi]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      have huA : u∉A := fun hm => havoid u hm hi.symm
      exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · exact fun hA => hold hA
  · simp only [if_neg hi,mem_insert]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      by_cases huA : u∈A
      · left
        apply avoiding_triangle_unique hc hD hDcl ha _ havoid
        intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr ((attached_vertex_adj_iff h hu hTS v).mp
            (hacl huA hv (Ne.symm hvu))))
      · right
        exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · rintro (rfl | hA)
      · exact hM
      · exact hold hA

theorem missingFacet_not_old {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    {c : V → Fin 4} {i : Fin 4} (hi : i≠ c u) :
    missingFacet c i (insert u T)∉avoidingTriangles G c i := by
  intro hM
  obtain ⟨hm,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hM
  have hsub := h.clique_subset_active (by omega) hcl
  exact hu (hsub (mem_filter.mpr ⟨mem_insert_self _ _,Ne.symm hi⟩))

/-- The exact number of triangles missing color i is |S|−n_i−2,
expressed without truncated subtraction. -/
theorem avoiding_triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    (avoidingTriangles G c i).card+(S.filter (fun v => c v=i)).card+2=S.card := by
  induction h with
  | tetrahedron D hD =>
    have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
    rw [avoidingTriangles_cliqueGraph hD hc,card_singleton,color_count_tetrahedron hc hD hcl,hD]
  | @attach S G h u hu T hT hTS hcl ih =>
    have hcG : Proper c G := fun v w hvw => hc v w (Or.inl hvw)
    have hold := ih hcG
    have htri := avoidingTriangles_after_attachment h hu hT hTS hcl hc i
    rw [htri,card_insert_of_notMem hu]
    by_cases hi : i=c u
    · rw [if_pos hi]
      have hcolor : ((insert u S).filter (fun v => c v=i)).card=
          (S.filter (fun v => c v=i)).card+1 := by
        rw [filter_insert]
        simp [hi,hu]
      rw [hcolor]
      omega
    · rw [if_neg hi,card_insert_of_notMem (missingFacet_not_old h hu hi)]
      have hcolor : (insert u S).filter (fun v => c v=i)=S.filter (fun v => c v=i) := by
        simp [filter_insert,Ne.symm hi]
      rw [hcolor]
      omega

/-- Every tetrahedron contributes exactly one incidence to triangles missing
each fixed color, so this sum is the actual tetrahedron count. -/
theorem incidence_sum {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T=S.card-3 := by
  have hcount : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)=
      ∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card := by
    simp only [triangleMultiplicity,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  rw [hcount]
  calc
    (∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card)=
        ∑ _D∈tetrahedra G,1 := by
      apply sum_congr rfl
      intro D hD
      obtain ⟨hd,hcl⟩ := (mem_filter.mp hD).2
      rw [avoiding_subsets_singleton hc hd hcl,card_singleton]
    _ = (tetrahedra G).card := by simp
    _ = S.card-3 := h.tetrahedra_card

theorem capacity_nonnegative {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (hA : Admissible G) (i : Fin 4) :
    (0 : ℤ)≤2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  have hb : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)≤
      3*(avoidingTriangles G c i).card := by
    calc
      _ ≤ ∑ _T∈avoidingTriangles G c i,3 := by
        apply sum_le_sum
        intro T hT
        obtain ⟨ht,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
        exact hA T ht hcl
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem free_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (i : Fin 4)
    (hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3) :
    ∃ T : Finset V,T.card=3 ∧ G.IsClique T ∧ Avoids c i T ∧
      triangleMultiplicity G T<3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  by_contra hn
  have hge : ∀ T∈avoidingTriangles G c i,3≤ triangleMultiplicity G T := by
    intro T hT
    obtain ⟨hcard,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    by_contra hlt
    exact hn ⟨T,hcard,hcl,ha,by omega⟩
  have hb : 3*(avoidingTriangles G c i).card≤
      ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T := by
    calc
      _ = ∑ _T∈avoidingTriangles G c i,3 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hge
  omega

end GraphicalZonotopes.FourPartThreeTreeCounts

end
end
end BundlePart348

section BundlePart349
/- Source: Papers/GraphicalZonotopes/AdmissibleAttachment.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adding a tetrahedron at a triangle with a free incidence slot preserves
admissibility on every old and new triangle. -/
theorem ThreeTreeOn.admissible_attach {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hA : Admissible G) {u : V} (hu : u∉S)
    {T : Finset V} (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    (hfree : triangleMultiplicity G T<3) : Admissible (G⊔attachmentStar u T) := by
  intro U hU hcU
  rw [triangleMultiplicity_after_attachment h hu hT hTS hcl]
  by_cases huU : u∈U
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huU]
    split_ifs <;> omega
  · have hold : G.IsClique U := clique_before_attachment huU hcU
    have hb := hA U hU hold
    by_cases hsub : U⊆insert u T
    · have hUT : U⊆T := by
        intro v hv
        have hm := hsub hv
        rcases mem_insert.mp hm with he | he
        · exact False.elim (huU (he ▸ hv))
        · exact he
      have heq : U=T := eq_of_subset_of_card_le hUT (by omega)
      subst U
      rw [if_pos hsub]
      omega
    · rw [if_neg hsub]
      omega

theorem proper_attachment {c : V → Fin 4} {G : SimpleGraph V}
    (hc : FourPartThreeTreeCounts.Proper c G) {u : V} {T : Finset V}
    (havoid : FourPartThreeTreeCounts.Avoids c (c u) T) :
    FourPartThreeTreeCounts.Proper c (G⊔attachmentStar u T) := by
  intro v w h
  rcases h with h | h
  · exact hc v w h
  · rcases h.2 with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Ne.symm (havoid w hw)
    · exact havoid v hv

theorem sum_color_counts (S : Finset V) (c : V → Fin 4) :
    (∑ i : Fin 4,(S.filter (fun v => c v=i)).card)=S.card := by
  simpa using sum_card_fiberwise_eq_card_filter S (univ : Finset (Fin 4)) c

theorem color_count_insert (S : Finset V) (c : V → Fin 4) {u : V} (hu : u∉S)
    (i : Fin 4) : ((insert u S).filter (fun v => c v=i)).card=
      (S.filter (fun v => c v=i)).card+(if c u=i then 1 else 0) := by
  rw [filter_insert]
  split_ifs with hi
  · rw [card_insert_of_notMem (fun hm => hu (mem_filter.mp hm).1)]
  · simp

end GraphicalZonotopes

end
end
end BundlePart349

section BundlePart350
/- Source: Papers/GraphicalZonotopes/FourPartSpanning.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourPartSpanning
open Finset Function FourColorResource FourPartThreeTreeCounts
variable {V : Type*} [Fintype V] [DecidableEq V]

def colorSize (c : V → Fin 4) (i : Fin 4) : ℕ :=
  ((univ : Finset V).filter (fun v => c v=i)).card

/-- Realize a complete color schedule inside any fixed finite ambient vertex
set with enough vertices in each color. All unused vertices remain isolated. -/
theorem realize_schedule (c : V → Fin 4) {a : Fin 4 → ℕ} (hs : Schedule a) :
    (∀ i,a i≤ colorSize c i) →
      ∃ S : Finset V,∃ G : SimpleGraph V,ThreeTreeOn S G ∧ Admissible G ∧ Proper c G ∧
        ∀ i,(S.filter (fun v => c v=i)).card=a i := by
  induction hs with
  | initial =>
    intro hbound
    have hw : ∀ i : Fin 4,∃ v : V,c v=i := by
      intro i
      obtain ⟨v,hv⟩ := card_pos.mp (show 0<((univ : Finset V).filter (fun v => c v=i)).card from
        lt_of_lt_of_le Nat.zero_lt_one (hbound i))
      exact ⟨v,(mem_filter.mp hv).2⟩
    choose w hw using hw
    let S := (univ : Finset (Fin 4)).image w
    have hwinj : Injective w := by
      intro i j he
      have h := congrArg c he
      rwa [hw i,hw j] at h
    have hS : S.card=4 := by simp [S,card_image_of_injective _ hwinj]
    have hc : Proper c (cliqueGraph S) := by
      intro u v h he
      obtain ⟨i,_,hi⟩ := mem_image.mp h.2.1
      obtain ⟨j,_,hj⟩ := mem_image.mp h.2.2
      have hij : i=j := by rw [← hw i,← hw j,hi,hj];exact he
      exact h.1 (hi.symm.trans ((congrArg w hij).trans hj))
    have hcl : (cliqueGraph S).IsClique S := fun u hu v hv huv => ⟨huv,hu,hv⟩
    refine ⟨S,cliqueGraph S,ThreeTreeOn.tetrahedron S hS,?_,hc,?_⟩
    · intro T hT ht
      unfold triangleMultiplicity
      calc
        ((tetrahedra (cliqueGraph S)).filter (fun C => T⊆C)).card≤
            (tetrahedra (cliqueGraph S)).card := card_filter_le _ _
        _=1 := by rw [tetrahedra_cliqueGraph hS,card_singleton]
        _≤3 := by omega
    · exact fun i => color_count_tetrahedron hc hS hcl i
  | @add a hs i hcapacity ih =>
    intro hbound
    have holdbound : ∀ j,a j≤ colorSize c j := by
      intro j
      have h := hbound j
      by_cases hji : j=i
      · subst j;simp only [update_self] at h;omega
      · simpa only [update_of_ne hji] using h
    obtain ⟨S,G,h3,hA,hc,hcounts⟩ := ih holdbound
    have hsize : S.card=total a := by
      rw [← sum_color_counts S c]
      exact sum_congr rfl (fun j _ => hcounts j)
    have hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
      rw [hcounts i,hsize]
      omega
    obtain ⟨T,hT,hcl,havoid,hfree⟩ := free_triangle h3 hc i hpos
    have hTS : T⊆S := h3.clique_subset_active (by omega) hcl
    have hex : ∃ u : V,c u=i ∧ u∉S := by
      by_contra hn
      have hsub : (univ : Finset V).filter (fun v => c v=i)⊆S.filter (fun v => c v=i) := by
        intro u hu
        have hcu := (mem_filter.mp hu).2
        have huS : u∈S := by
          by_contra hnot
          exact hn ⟨u,hcu,hnot⟩
        exact mem_filter.mpr ⟨huS,hcu⟩
      have hcard := card_le_card hsub
      rw [hcounts i] at hcard
      have hi := hbound i
      simp only [update_self] at hi
      change a i+1≤((univ : Finset V).filter (fun v => c v=i)).card at hi
      omega
    obtain ⟨u,hcu,hu⟩ := hex
    refine ⟨insert u S,G⊔attachmentStar u T,h3.attach u hu T hT hTS hcl,
      h3.admissible_attach hA hu hT hTS hcl hfree,?_,?_⟩
    · apply proper_attachment hc
      simpa only [hcu] using havoid
    · intro j
      rw [color_count_insert S c hu j,hcounts j,hcu]
      by_cases hji : j=i
      · subst j;simp
      · simp [update_of_ne hji,Ne.symm hji]

/-- The exact arithmetic balance condition gives an actual admissible
spanning 3-tree inside the graph of different colors. -/
theorem spanning_of_balanced_colors (c : V → Fin 4)
    (ha : Balanced (colorSize c)) :
    ∃ G : SimpleGraph V,IsThreeTree G ∧ Admissible G ∧ Proper c G := by
  obtain ⟨S,G,h3,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced ha) (fun _ => le_rfl)
  have hcard : S.card=(univ : Finset V).card := by
    rw [← sum_color_counts S c,← sum_color_counts (univ : Finset V) c]
    exact sum_congr rfl (fun i _ => hcounts i)
  have hS : S=univ := eq_of_subset_of_card_le (subset_univ S) hcard.ge
  rw [hS] at h3
  exact ⟨G,h3,hA,hc⟩

theorem sigma_colorSize (a : Fin 4 → ℕ) (i : Fin 4) :
    colorSize (fun v : Σ j : Fin 4,Fin (a j) => v.1) i=a i := by
  let e : {v : (Σ j : Fin 4,Fin (a j)) // v.1=i} ≃ Fin (a i) :=
    { toFun := fun v => by rcases v with ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;exact b
      invFun := fun b => ⟨⟨i,b⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;rfl
      right_inv := by intro b;rfl }
  have h := Fintype.card_congr e
  simpa [colorSize,Fintype.card_subtype] using h

/-- Spanning existence, with the literal maximum part-size inequality. -/
theorem four_partite_spanning_iff (a : Fin 4 → ℕ) (ha : ∀ i,1≤ a i) :
    HasAdmissibleSpanningThreeTree (fourPartite a) ↔
      3*(univ.sup a)≤2*(∑ i,a i)-3 := by
  have htotal : Fintype.card (Σ i : Fin 4,Fin (a i))=∑ i,a i := by simp
  have hN : 4≤ total a := total_ge_four ha
  constructor
  · rintro ⟨G,hG,h3,hA⟩
    have hc : Proper (fun v : Σ i : Fin 4,Fin (a i) => v.1) G :=
      fun u v huv => hG huv
    have hbounds : ∀ i,3*a i+3≤2*total a := by
      intro i
      have h := capacity_nonnegative h3 hc hA i
      change (0 : ℤ)≤2*((univ : Finset (Σ i : Fin 4,Fin (a i))).card : ℤ)-
        3*(colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1) i : ℤ)-3 at h
      rw [sigma_colorSize,card_univ,htotal] at h
      dsimp [total]
      omega
    obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
    have hb := hbounds i
    rw [he]
    dsimp [total] at hb
    omega
  · intro hb
    have hbal : Balanced a := by
      refine ⟨ha,?_⟩
      intro i
      have hi : a i≤ univ.sup a := le_sup (mem_univ _)
      dsimp [total] at *
      omega
    have hcolors : Balanced (colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)) := by
      have he : colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)=a := funext (sigma_colorSize a)
      rwa [he]
    obtain ⟨G,h3,hA,hc⟩ := spanning_of_balanced_colors _ hcolors
    exact ⟨G,fun u v huv => hc u v huv,h3,hA⟩

end GraphicalZonotopes.FourPartSpanning

end
end
end BundlePart350

section BundlePart351
/- Source: Papers/GraphicalZonotopes/FourPartCapacity.lean -/





@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

theorem single_plus_three_le_total {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (i : Fin 4) : a i+3≤ total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem other_parts_mono {a b : Fin 4 → ℕ} (hba : ∀ i,b i≤ a i) (i : Fin 4) :
    total b-b i≤ total a-a i := by
  have h0 := hba 0
  have h1 := hba 1
  have h2 := hba 2
  have h3 := hba 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

/-- Every balanced active part vector obeys the exact restricted-dimension
bound, even when its largest part differs from the ambient largest part. -/
theorem balanced_dimension_bound {a b : Fin 4 → ℕ}
    (ha : ∀ i,0< a i) (hb : Balanced b) (hba : ∀ i,b i≤ a i) :
    total b-1≤ min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have htotal : total b≤ total a := sum_le_sum (fun i _ => hba i)
  have hother := other_parts_mono hba i
  have hbi := single_plus_three_le_total hb.1 i
  have hai := single_plus_three_le_total ha i
  have hbal := hb.2 i
  rw [he]
  apply le_min
  · omega
  · omega

/-- Truncating one largest part is always optimal. The vector still has all
four positive parts and admits the complete unbounded attachment schedule. -/
theorem optimal_balanced_subcounts (a : Fin 4 → ℕ) (ha : ∀ i,0< a i) :
    ∃ b : Fin 4 → ℕ,Balanced b ∧ (∀ i,b i≤ a i) ∧
      total b-1=min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have hmax : ∀ j,a j≤ a i := by intro j;rw [← he];exact le_sup (mem_univ _)
  let s := total a-a i
  have hsum : a i+s=total a := by
    have h := single_plus_three_le_total ha i
    dsimp [s]
    omega
  have hs : 3≤ s := by have h := single_plus_three_le_total ha i;dsimp [s];omega
  let k := min (a i) (2*s-3)
  have hkpos : 0< k := by have hi := ha i;dsimp [k];omega
  have hkai : k≤ a i := min_le_left _ _
  have hks : k≤2*s-3 := min_le_right _ _
  let b := update a i k
  have hbi : b i=k := by simp [b]
  have hbtotal : total b=s+k := by
    have h := total_update a i k
    change total b+a i=total a+k at h
    omega
  have hbjmax : ∀ j,b j≤ k := by
    intro j
    by_cases hji : j=i
    · subst j;rw [hbi]
    · have hp := pair_bound ha i j (Ne.symm hji)
      have hm := hmax j
      have hj := ha j
      have hjs : a j≤2*s-3 := by omega
      have hmin : a j≤ k := le_min hm hjs
      simpa [b,update_of_ne hji] using hmin
  have hbal : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rwa [hbi]
      · simpa [b,update_of_ne hji] using ha j
    · intro j
      have h := hbjmax j
      rw [hbtotal]
      omega
  refine ⟨b,hbal,?_,?_⟩
  · intro j
    by_cases hji : j=i
    · subst j;rwa [hbi]
    · simp [b,update_of_ne hji]
  · rw [he,hbtotal]
    change s+k-1=min (total a-1) (3*s-4)
    by_cases hcase : a i≤2*s-3
    · have hk : k=a i := min_eq_left hcase
      rw [hk]
      omega
    · have hk : k=2*s-3 := min_eq_right (by omega)
      rw [hk]
      omega

end GraphicalZonotopes.FourColorResource

end
end
end BundlePart351

section BundlePart352
/- Source: Papers/GraphicalZonotopes/FourPartSpectrum.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset FourColorResource FourPartThreeTreeCounts FourPartSpanning

/-- The restricted dimension invariant agrees with the ordinary-polytope
notion of indecomposability. The required GP presentation is derived from the
actual weak Minkowski sum for each individual candidate. -/
theorem maximumThreeTreeSupportDimension_eq_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    maximumThreeTreeSupportDimension G=
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumThreeTreeSupportDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hw,hT,hd⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
    obtain ⟨hn,hs,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hs,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,
      ⟨t,ht,R,hR,hRc,hnR,he⟩,hT,hd⟩

/-- The color capacity bound applies to the actual support of every real
indecomposable weak summand. Full dimension on that active support is derived. -/
theorem four_partite_threeTree_dimension_bound (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) {Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)))
    {S : Finset (Σ i : Fin 4,Fin (a i))}
    (hT : ThreeTreeOn S (actualDirectionGraph Q)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
  obtain ⟨hfn,hfs,hbody,hgraph,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzg : Graphical (fourPartite a) z := by
    intro u v huv hnon T hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon T hu hv
  have hactual : actualDirectionGraph (basePolytope z)=actualDirectionGraph Q := by
    rw [actualDirectionGraph_normalize,← hbody]
  have hTz : ThreeTreeOn S (actualDirectionGraph (basePolytope z)) := by
    rwa [hactual]
  have hne : z≠0 := threeTree_actual_nonzero hzn.1 hzs hTz
  have hz : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hd,hA⟩ := threeTree_actual_dimension_admissible hz hTz
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hc : Proper c (actualDirectionGraph (basePolytope z)) := by
    intro u v huv heq
    obtain ⟨huv',T,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta hzn.1 hzs u v).mp huv
    apply hd (hzg u v huv' ?_ T hu hv)
    exact fun h => h heq
  let b : Fin 4 → ℕ := fun i => (S.filter (fun v => c v=i)).card
  have htotal : total b=S.card := sum_color_counts S c
  have hb : Balanced b := by
    constructor
    · obtain ⟨C,hC⟩ := hTz.tetrahedra_nonempty
      have hcard : C.card=4 := (mem_filter.mp hC).2.1
      have hcl : (actualDirectionGraph (basePolytope z)).IsClique C := (mem_filter.mp hC).2.2
      have hCS : C⊆S := hTz.clique_subset_active (by omega) hcl
      intro i
      have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) hCS)
      rw [color_count_tetrahedron hc hcard hcl i] at hle
      exact lt_of_lt_of_le Nat.zero_lt_one hle
    · intro i
      have hcap := capacity_nonnegative hTz hc hA i
      change (0 : ℤ)≤2*(S.card : ℤ)-3*(b i : ℤ)-3 at hcap
      rw [htotal]
      omega
  have hba : ∀ i,b i≤ a i := by
    intro i
    have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) (subset_univ S))
    change b i≤ colorSize c i at hle
    simpa only [c,sigma_colorSize] using hle
  have hbound := balanced_dimension_bound (fun i => by have h := ha i;omega) hb hba
  rw [htotal] at hbound
  have hdQ : Module.finrank ℝ (vectorSpan ℝ Q)=S.card-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody] at hd
    exact hd
  rw [hdQ]
  exact hbound

/-- Optimal balanced subcounts produce a genuine integral polytope whose
actual direction graph is a 3-tree on exactly the constructed active vertices. -/
theorem four_partite_threeTree_dimension_attained (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
      IsFinitePolytope Q ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
      (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=
        min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨b,hb,hba,hopt⟩ := optimal_balanced_subcounts a (fun i => by have h := ha i;omega)
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hcap : ∀ i,b i≤ colorSize c i := by
    intro i
    simpa only [c,sigma_colorSize] using hba i
  obtain ⟨S,G,hT,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced hb) hcap
  have hsize : S.card=total b := by
    rw [← sum_color_counts S c]
    exact sum_congr rfl (fun i _ => hcounts i)
  obtain ⟨f,hf,hint,hd,hactual,hgraph⟩ := admissible_threeTree_active_witness hT hA
  have hgg : Graphical (fourPartite a) f := by
    intro u v huv hnon T hu hv
    exact hgraph u v huv (fun h => hnon (hc u v h)) T hu hv
  have hgp : IsGeneralizedPermutahedron (basePolytope f) := ⟨f,hf.1.1,hf.2.1,rfl⟩
  refine ⟨basePolytope f,hgp.finitePolytope,hint.basePolytope hf.1.1 hf.2.1,
    hf.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hgg,
    ⟨S,?_⟩,?_⟩
  · rwa [hactual]
  · rw [hd,hsize]
    exact hopt

/-- The exact restricted maximum in Theorem 8.9, including all real weak
summands and without any ambient full-dimension hypothesis. -/
theorem maximum_threeTree_support_fourPartite (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) :
    maximumThreeTreeSupportDimension (fourPartite a)=
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let k := min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4)
  let D : Set ℕ := {d | ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
    IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
    (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}
  have hbound : ∀ d∈D,d≤ k := by
    rintro d ⟨Q,hQ,hi,hw,⟨S,hT⟩,hd⟩
    rw [← hd]
    exact four_partite_threeTree_dimension_bound a ha hQ hi hw hT
  have hk : k∈D := by
    obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩ := four_partite_threeTree_dimension_attained a ha
    exact ⟨Q,hQ,hi,hw,hT,hd⟩
  change sSup D=k
  exact le_antisymm (csSup_le ⟨k,hk⟩ hbound) (le_csSup ⟨k,hbound⟩ hk)

/-- Both assertions of the printed Theorem 8.9, with every positive part
size and the actual-support definition of its restricted dimension invariant. -/
theorem four_partite_spanning_threeTrees : Targets.FourPartiteSpanningThreeTrees := by
  intro a ha
  exact ⟨four_partite_spanning_iff a ha,maximum_threeTree_support_fourPartite a ha⟩

end GraphicalZonotopes

end
end
end BundlePart352

section BundlePart353
/- Source: Papers/GraphicalZonotopes/TwoHubAttainment.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An integral graphical extreme function with its genuine affine
dimension. Unlike `LatticeExtremeAt`, this predicate specifies no dilation. -/
def IntegralGraphicalExtremeAt (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d

theorem LatticeExtremeAt.integralGraphical {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩:=h
  exact ⟨f,hn,hi,he,hG,hd⟩

theorem IntegralGraphicalExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) (e : V↪W) (hGH : G≤ H.comap e) :
    IntegralGraphicalExtremeAt H d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  refine ⟨extend e f,extend_translationNormalized e hn,extend_integer e hi,
    extend_extreme e he,extend_graphical e (hG.mono_graph hGH),?_⟩
  rw [finrank_vectorSpan_extend e hn,hd]

theorem IntegralGraphicalExtremeAt.polytope {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) :
    ∃ Q : Set (V→ℝ),IsFinitePolytope Q ∧ LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  have hgp : IsGeneralizedPermutahedron (basePolytope f):=⟨f,hn.1,he.2.1,rfl⟩
  exact ⟨basePolytope f,hgp.finitePolytope,hi.basePolytope hn.1 he.2.1,
    he.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG,hd⟩

theorem IntegralGraphicalExtremeAt.dimension_le {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) : d≤ maximumIndecomposableDimension G := by
  obtain ⟨Q,hf,hl,hi,hw,hd⟩:=h.polytope
  rw [←hd]
  exact dimension_le_maximum hf hi hw

/-- Extracting the integral normalized support function preserves dimension
and exposes every hypothesis needed to transfer a lattice witness. -/
theorem integralGraphicalExtremeAt_of_polytope {G : SimpleGraph V} {d : ℕ}
    (hdpos : 0< d) {Q : Set (V→ℝ)} (hQ : IsFinitePolytope Q) (hl : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : Module.finrank ℝ (vectorSpan ℝ Q)=d) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨M,hM,R,hR,hRc,hnR,hQR⟩:=hw
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩:=actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR hM.le hQR
  let f:=lowerSupport Q
  let z:=normalize f
  have hn : TranslationNormalized z:=normalize_translationNormalized hfn
  have hint : IntegerValued z:=(hl.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z:=by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=d := by
    rw [vectorSpan_basePolytope_normalize,←hbody]
    exact hd
  have hz : z≠0:=by
    intro he
    rw [he,basePolytope_zero,vectorSpan_singleton,finrank_bot] at hzd
    omega
  have he:=MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hz (hbody ▸ hi)
  exact ⟨z,hn,hint,he,hzg,hzd⟩

namespace TwoHub

theorem twoSingleton_card (p b : ℕ) :
    Fintype.card (Σ i : Fin 4,Fin (![1,1,p,b] i))=p+b+2 := by
  simp [Fintype.card_sigma,Fin.sum_univ_succ]
  omega

theorem part_sum (p b : ℕ) : (∑ i : Fin 4,(![1,1,p,b] i))=p+b+2 := by
  simp [Fin.sum_univ_succ]
  omega

theorem part_sup (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) :
    univ.sup (![1,1,p,b])=b := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    fin_cases i <;> simp <;> omega
  · have h:=le_sup (f:=(![1,1,p,b])) (mem_univ (3 : Fin 4))
    simpa using h

/-- The complete low range is supplied by the already verified four-partite
3-tree spectrum. No finite-parameter enumeration is used. -/
theorem low_range_attainment (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) (hb : b≤2*p+1) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩:=four_partite_threeTree_dimension_attained (![1,1,p,b])
    (by intro i;fin_cases i <;> simp <;> omega)
  rw [part_sum,part_sup p b hp hpb] at hd
  have he : min (p+b+2-1) (3*(p+b+2-b)-4)=p+b+1:=by omega
  rw [he] at hd
  exact integralGraphicalExtremeAt_of_polytope (by omega) hQ hl hi hw hd

/-- A proper partition with k cells yields an integral witness on exactly
k+p vertices in the last independent part. -/
theorem partition_attainment {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : PartitionData I) :
    IntegralGraphicalExtremeAt
      (twoSingletonGraph (Fintype.card I) (P.cells.card+Fintype.card I))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
  have h : IntegralGraphicalExtremeAt (graph (I:=I) (J:=P.Index))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
    refine ⟨P.construction,P.construction_normalized,P.construction_integer,
      P.construction_extreme,P.construction_graphical,?_⟩
    have hd:=P.construction_fullDimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope P.construction))=
      Fintype.card (Hub I⊕P.Index)-1 at hd
    rw [hd]
    simp only [Hub,PartitionData.Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_coe]
    omega
  let e:=graphIso (I:=I) (J:=P.Index)
  have hmap : graph (I:=I) (J:=P.Index)≤
      (twoSingletonGraph (Fintype.card I) (Fintype.card P.Index)).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=h.embed e.toEquiv.toEmbedding hmap
  have hcard : Fintype.card P.Index=P.cells.card+Fintype.card I := by
    simp [PartitionData.Index]
  exact Eq.mp (congrArg (fun b : ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph (Fintype.card I) b)
    (Fintype.card I+P.cells.card+Fintype.card I+1)) hcard) he

theorem intermediate_attainment (p b : ℕ) (hp : 1≤ p)
    (hlo : 2*p+1≤ b) (hhi : b≤2^p+p) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  obtain ⟨F,hF,hcard,huses,hproper⟩:=CubePartition.exists_proper_card (I:=Fin p) (b-p)
    (by simp only [Fintype.card_fin];omega) (by simp only [Fintype.card_fin];omega)
  let P : PartitionData (Fin p):=⟨F,hF,hproper,huses⟩
  have he:=partition_attainment P
  have hbc : F.card+p=b:=by omega
  have hd : p+F.card+p+1=p+b+1:=by omega
  have hdim : Fintype.card (Fin p)+P.cells.card+Fintype.card (Fin p)+1=p+b+1 := by
    simpa only [Fintype.card_fin,P] using hd
  have hpars : (Fintype.card (Fin p),P.cells.card+Fintype.card (Fin p))=(p,b) := by
    simp only [Fintype.card_fin,P,hbc]
  rw [hdim] at he
  exact Eq.mp (congrArg (fun x : ℕ×ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph x.1 x.2) (p+b+1)) hpars) he

/-- Enlarging the last part preserves the saturated integral witness by
adding zero coordinates to its support function. -/
theorem saturated_attainment (p b : ℕ) (hp : 1≤ p) (hb : 2^p+p≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (2^p+2*p+1) := by
  have h:=(exponential_lattice_summand p hp).integralGraphical
  let e₀:=vertexEmbedding (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb)
  let e₁:=(finGraphIso p (2^p+p)).symm.toEquiv.toEmbedding
  let e₂:=(finGraphIso p b).toEquiv.toEmbedding
  let e:=e₁.trans (e₀.trans e₂)
  have hmap : twoSingletonGraph p (2^p+p)≤(twoSingletonGraph p b).comap e := by
    intro x y hxy
    have h₁ : (graph (I:=Fin p) (J:=Fin (2^p+p))).Adj (e₁ x) (e₁ y) :=
      (finGraphIso p (2^p+p)).symm.map_adj_iff.mpr hxy
    have h₀:=graph_le_comap (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb) h₁
    exact (finGraphIso p b).map_adj_iff.mpr h₀
  exact h.embed e hmap

theorem ordered_attainment (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (min (p+b+1) (2^p+2*p+1)) := by
  by_cases hb : b≤2*p+1
  · have he : p+b+1≤2^p+2*p+1 := by
      have hpow : p+1≤2^p:=Nat.lt_two_pow_self (n:=p)
      omega
    rw [min_eq_left he]
    exact low_range_attainment p b hp hpb hb
  · by_cases hs : b≤2^p+p
    · rw [min_eq_left (by omega)]
      exact intermediate_attainment p b hp (by omega) hs
    · rw [min_eq_right (by omega)]
      exact saturated_attainment p b hp (by omega)

theorem all_attainment (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b)
      (min (p+b+1) (2^(min p b)+2*min p b+1)) := by
  by_cases hpb : p≤ b
  · simpa only [min_eq_left hpb] using ordered_attainment p b hp hpb
  · have hbp : b≤ p:=by omega
    have h:=ordered_attainment b p hb hbp
    let e:=twoSingletonSwap b p
    have hmap : twoSingletonGraph b p≤(twoSingletonGraph p b).comap e:=by
      intro x y hxy
      exact e.map_adj_iff.mpr hxy
    have he:=h.embed e.toEquiv.toEmbedding hmap
    simpa only [min_eq_right hbp,Nat.add_comm b p] using he

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart353

section BundlePart354
/- Source: Papers/GraphicalZonotopes/TwoHubCapacity.lean -/







/-! # The separator upper bound for the two-singleton family

The boundary is the two distinguished vertices together with the first
independent part.  We count its rows exactly and exhibit all the boundary
cliques needed for the sharp capacity estimate.  No assumption is made that
the private coefficients of an extreme summand are nonzero.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section
namespace GraphicalZonotopes.TwoHub.Capacity
open Finset
open scoped BigOperators Classical

abbrev Vertex (p b : ℕ) := (Bool ⊕ Fin p) ⊕ Fin b

local instance vertexOrder (p b : ℕ) : LinearOrder (Vertex p b) :=
  inferInstanceAs (LinearOrder ((Bool ⊕ₗ Fin p) ⊕ₗ Fin b))

local instance vertexLT (p b : ℕ) : LT (Vertex p b) :=
  (vertexOrder p b).toLT

local instance vertexDecidableEq (p b : ℕ) : DecidableEq (Vertex p b) :=
  (vertexOrder p b).toDecidableEq

abbrev G (p b : ℕ) := TwoHub.graph (I := Fin p) (J := Fin b)
def anchor (p b : ℕ) (t : Bool) : Vertex p b := .inl (.inl t)
def a (p b : ℕ) : Vertex p b := anchor p b false
def z (p b : ℕ) : Vertex p b := anchor p b true
def u (p b : ℕ) (i : Fin p) : Vertex p b := .inl (.inr i)
def boundary (p b : ℕ) : Finset (Vertex p b) :=
  univ.image (Sum.inl : Bool ⊕ Fin p → Vertex p b)
def privatePart (p b : ℕ) (j : Fin b) : Finset (Vertex p b) := {Sum.inr j}

@[simp] theorem boundary_card (p b : ℕ) : (boundary p b).card = p+2 := by
  rw [boundary,card_image_of_injective _ Sum.inl_injective]
  simp [Nat.add_comm]

@[simp] theorem mem_boundary_inl (p b : ℕ) (x : Bool ⊕ Fin p) :
    Sum.inl x ∈ boundary p b := by simp [boundary]

@[simp] theorem not_mem_boundary_inr (p b : ℕ) (j : Fin b) :
    Sum.inr j ∉ boundary p b := by simp [boundary]

theorem boundary_order (p b : ℕ) (x y : Bool ⊕ Fin p) :
    (Sum.inl x : Vertex p b) < Sum.inl y ↔
      (toLex x : Bool ⊕ₗ Fin p) < toLex y := Sum.lex_inl_inl

theorem partition (p b : ℕ) :
    Separator.Partition (G p b) (boundary p b) (privatePart p b) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro x hx hp
    have he : x=Sum.inr j := mem_singleton.mp hp
    subst x
    exact not_mem_boundary_inr p b j hx
  private_disjoint := by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (Sum.inr_injective he))
  cover x := by
    cases x with
    | inl x => exact Or.inl (mem_boundary_inl p b x)
    | inr j => exact Or.inr ⟨j,mem_singleton_self _⟩
  no_cross_edge := by
    intro i j x y hx hy hxy
    have hx' : x=Sum.inr i := mem_singleton.mp hx
    have hy' : y=Sum.inr j := mem_singleton.mp hy
    subst x
    subst y
    exact False.elim (hxy rfl)

abbrev EdgeCode (p : ℕ) := Unit ⊕ (Bool × Fin p)

def edgePair (p b : ℕ) : EdgeCode p → Vertex p b × Vertex p b
  | .inl _ => (a p b,z p b)
  | .inr (t,i) => (anchor p b t,u p b i)

theorem edgePair_valid (p b : ℕ) (c : EdgeCode p) :
    (edgePair p b c).1 < (edgePair p b c).2 ∧
      (G p b).Adj (edgePair p b c).1 (edgePair p b c).2 ∧
      (edgePair p b c).1 ∈ boundary p b ∧
      (edgePair p b c).2 ∈ boundary p b := by
  rcases c with c | ⟨t,i⟩
  · simp [edgePair,a,z,anchor,boundary_order,Sum.Lex.toLex_lt_toLex,
      G,TwoHub.graph,TwoHub.color]
  · cases t <;> simp [edgePair,anchor,u,boundary_order,
      Sum.Lex.toLex_lt_toLex,G,TwoHub.graph,TwoHub.color]

def boundaryEdgeOfCode (p b : ℕ) (c : EdgeCode p) :
    Separator.BoundaryEdge (G p b) (boundary p b) :=
  ⟨⟨edgePair p b c,(edgePair_valid p b c).1,(edgePair_valid p b c).2.1⟩,
    (edgePair_valid p b c).2.2⟩

theorem edgePair_injective (p b : ℕ) : Function.Injective (edgePair p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp [edgePair,a,z,anchor,u] at h
  · simp [edgePair,a,z,anchor,u] at h
  · simpa [edgePair,anchor,u] using h

theorem boundaryEdgeOfCode_bijective (p b : ℕ) :
    Function.Bijective (boundaryEdgeOfCode p b) := by
  constructor
  · intro c d h
    apply edgePair_injective p b
    exact congrArg (fun e : Separator.BoundaryEdge (G p b) (boundary p b) => e.1.1) h
  · rintro ⟨⟨⟨x,y⟩,hlt,hadj⟩,hx,hy⟩
    obtain ⟨x,_,rfl⟩ := mem_image.mp hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hy
    rw [boundary_order] at hlt
    rcases x with t | i <;> rcases y with s | j
    · cases t <;> cases s
      all_goals try simp [Sum.Lex.toLex_lt_toLex,Bool.lt_iff] at hlt
      refine ⟨.inl (),?_⟩
      rfl
    · refine ⟨.inr (t,j),?_⟩
      rfl
    · simp [Sum.Lex.toLex_lt_toLex] at hlt
    · exact False.elim (hadj rfl)

def boundaryEdgeEquiv (p b : ℕ) :
    EdgeCode p ≃ Separator.BoundaryEdge (G p b) (boundary p b) :=
  Equiv.ofBijective (boundaryEdgeOfCode p b) (boundaryEdgeOfCode_bijective p b)

theorem common_boundary_az (p b : ℕ) :
    commonNeighbors (G p b) (a p b) (z p b) ∩ boundary p b =
      univ.image (u p b) := by
  ext x
  rcases x with (t | i) | j
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [u]

theorem common_boundary_anchor (p b : ℕ) (t : Bool) (i : Fin p) :
    commonNeighbors (G p b) (anchor p b t) (u p b i) ∩ boundary p b =
      {anchor p b (!t)} := by
  ext x
  rcases x with (s | j) | j
  · cases t <;> cases s <;>
      simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · simp [anchor]

theorem u_injective (p b : ℕ) : Function.Injective (u p b) := by
  intro i j h
  exact Sum.inr_injective (Sum.inl_injective h)

/-- The boundary has exactly `2^p + 4*p` elementary rows. -/
theorem boundary_rows_count (p b : ℕ) :
    (∑ e : Separator.BoundaryEdge (G p b) (boundary p b),
      2^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card) =
        2^p+4*p := by
  have he := Fintype.sum_equiv (boundaryEdgeEquiv p b)
    (fun c : EdgeCode p =>
      (2 : ℕ)^(commonNeighbors (G p b) (edgePair p b c).1
        (edgePair p b c).2 ∩ boundary p b).card)
    (fun e : Separator.BoundaryEdge (G p b) (boundary p b) =>
      (2 : ℕ)^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card)
    (fun _ => rfl)
  rw [←he]
  simp [EdgeCode,Fintype.sum_sum_type,edgePair,common_boundary_az,
    common_boundary_anchor,card_image_of_injective _ (u_injective p b),
    Fintype.sum_prod_type,Fintype.sum_bool,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] <;> omega

abbrev CliqueCode (p : ℕ) := Unit ⊕ (Fin 3 × Fin p)

def cliqueSet (p b : ℕ) : CliqueCode p → Finset (Vertex p b)
  | .inl _ => {a p b,z p b}
  | .inr (t,i) => if t=0 then {a p b,u p b i}
      else if t=1 then {z p b,u p b i} else {a p b,z p b,u p b i}

theorem u_mem_cliqueSet (p b : ℕ) (t : Fin 3) (i : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,i)) := by
  fin_cases t <;> simp [cliqueSet]

theorem u_mem_cliqueSet_iff (p b : ℕ) (t : Fin 3) (i j : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,j)) ↔ i=j := by
  fin_cases t <;> simp [cliqueSet,a,z,anchor,u]

theorem cliqueSet_injective (p b : ℕ) : Function.Injective (cliqueSet p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · have hj := u_mem_cliqueSet p b s j
    rw [←h] at hj
    simp [cliqueSet,a,z,anchor,u] at hj
  · have hi := u_mem_cliqueSet p b t i
    rw [h] at hi
    simp [cliqueSet,a,z,anchor,u] at hi
  · have hi := u_mem_cliqueSet p b t i
    rw [h,u_mem_cliqueSet_iff] at hi
    subst j
    have ha := congrArg (fun C : Finset (Vertex p b) => a p b ∈ C) h
    have hz := congrArg (fun C : Finset (Vertex p b) => z p b ∈ C) h
    fin_cases t <;> fin_cases s <;> try rfl
    all_goals simp [cliqueSet,a,z,anchor,u] at ha hz

theorem cliqueSet_mem (p b : ℕ) (c : CliqueCode p) :
    cliqueSet p b c ∈ Separator.boundaryCliques (G p b) (boundary p b) := by
  rcases c with c | ⟨t,i⟩
  · simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
      SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,
      G,TwoHub.graph,TwoHub.color]
  · fin_cases t <;>
      simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
        SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,u,
        G,TwoHub.graph,TwoHub.color]

theorem boundary_cliques_lower (p b : ℕ) :
    1+3*p ≤ (Separator.boundaryCliques (G p b) (boundary p b)).card := by
  have h := Fintype.card_le_of_injective
    (fun c : CliqueCode p =>
      (⟨cliqueSet p b c,cliqueSet_mem p b c⟩ :
        ↥(Separator.boundaryCliques (G p b) (boundary p b))))
    (fun c d h => cliqueSet_injective p b (congrArg Subtype.val h))
  simpa only [CliqueCode,Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_coe] using h

/-- The exact upper capacity bound, without nonzero-branch hypotheses. -/
theorem active_capacity (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Fintype.card (Gluing.ActiveBranch
      (((Separator.functionEquiv (partition p b)).symm f).2)) ≤ 2^p+p := by
  have h := Separator.separator_capacity_for_function (partition p b) f hf
  rw [boundary_rows_count] at h
  have hc := boundary_cliques_lower p b
  have hp : 0 < (2 : ℕ)^p := pow_pos (by decide) _
  omega

theorem extreme_dimension_bound (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f.1)) ≤ 2^p+2*p+1 := by
  have h := Separator.finrank_le_boundary_add_active (partition p b)
    (fun j => by simp [privatePart]) f hf.2.1
  rw [boundary_card] at h
  have hc := active_capacity p b f hf
  omega

theorem actual_summand_dimension_bound (p b : ℕ)
    {Q : Set (Vertex p b → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (G p b))) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply le_min
  · have h := weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  · obtain ⟨f,hf,hzero|hext,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      exact Nat.zero_le _
    · rw [hd]
      exact extreme_dimension_bound p b f hext

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (G p b) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [←hd]
  exact actual_summand_dimension_bound p b hQ hi hw

end GraphicalZonotopes.TwoHub.Capacity

end
end
end BundlePart354

section BundlePart355
/- Source: Papers/GraphicalZonotopes/TwoHubPrincipal.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^p+2*p+1) := by
  rw [←maximum_dimension_model_eq]
  exact Capacity.maximum_dimension_upper p b

theorem maximum_dimension_upper_symmetric (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  by_cases hpb : p≤ b
  · simpa only [min_eq_left hpb] using maximum_dimension_upper p b
  · have hbp : b≤ p:=by omega
    rw [maximum_dimension_swap]
    simpa only [min_eq_right hbp,Nat.add_comm b p] using maximum_dimension_upper b p

/-- The exact dimension formula of Theorem8.7, for all positive part
sizes, with no restriction to the explicit support pattern. -/
theorem maximum_dimension (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      min (p+b+1) (2^(min p b)+2*min p b+1) :=
  le_antisymm (maximum_dimension_upper_symmetric p b) (all_attainment p b hp hb).dimension_le

theorem full_dimension_arithmetic (p b : ℕ) :
    p+b+1≤2^(min p b)+2*min p b+1 ↔ max p b≤2^(min p b)+min p b := by
  by_cases h : p≤ b
  · simp only [min_eq_left h,max_eq_right h]
    omega
  · have hh : b≤ p:=by omega
    simp only [min_eq_right hh,max_eq_left hh]
    omega

theorem supports_full_iff (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    SupportsFullIndecomposable (twoSingletonGraph p b) ↔
      max p b≤2^(min p b)+min p b := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have hm:=(dimension_le_maximum hQ hi hw).trans (maximum_dimension_upper_symmetric p b)
    rw [hd,twoSingleton_card] at hm
    have hn : p+b+1≤2^(min p b)+2*min p b+1:=by omega
    exact (full_dimension_arithmetic p b).mp hn
  · intro h
    obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
    refine ⟨Q,hQ,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=_
    rw [hd,min_eq_left ((full_dimension_arithmetic p b).mpr h),twoSingleton_card]
    omega

/-- The dimension formula, exact full-dimensionality criterion, and lattice
attainment in the original coordinate model of the paper. -/
theorem two_singleton_classification : Targets.TwoSingletonClassification := by
  intro p b hp hb
  refine ⟨maximum_dimension p b hp hb,supports_full_iff p b hp hb,?_⟩
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,hi,hw,hd⟩

theorem twoSingleton_cliqueFree (p b : ℕ) : (twoSingletonGraph p b).CliqueFree 5 := by
  intro S hS
  have hinj : Function.Injective (fun v : S => v.1.1) := by
    intro x y he
    by_contra hne
    have hxy:=hS.1 x.2 y.2 (fun h => hne (Subtype.ext h))
    exact hxy he
  have hc:=Fintype.card_le_of_injective (fun v : S => v.1.1) hinj
  simp only [Fintype.card_coe,Fintype.card_fin] at hc
  rw [hS.2] at hc
  omega

/-- The whole printed Theorem8.4: an actual lattice summand at the explicit
integral dilation, and stabilization at every larger fourth part. -/
theorem exponential_family (p : ℕ) (hp : 1≤ p) :
    (twoSingletonGraph p (2^p+p)).CliqueFree 5 ∧
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      IsMinkowskiSummand Q ((((p-1)*2^p+2 : ℕ) : ℝ) •
        graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ∀ b : ℕ,2^p+p≤ b →
      maximumIndecomposableDimension (twoSingletonGraph p b)=2^p+2*p+1 := by
  refine ⟨twoSingleton_cliqueFree _ _,(exponential_lattice_summand p hp).polytope,?_⟩
  intro b hb
  have hpb : p≤ b:=(Nat.le_add_left p (2^p)).trans hb
  rw [maximum_dimension p b hp (by omega),min_eq_left hpb,min_eq_right (by omega)]

end GraphicalZonotopes.TwoHub

end
end
end BundlePart355

section BundlePart356
/- Source: Papers/GraphicalZonotopes/TwoHubLiteral.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open scoped Pointwise

/-- The supremum in Theorem8.7 uses precisely the paper's convention that
indecomposability tests finite polytopal Minkowski decompositions. -/
theorem classification_polytopal (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    (sSup {d : ℕ | ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
  exact maximum_dimension p b hp hb

theorem full_polytopal_iff (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b))) ↔
      max p b≤2^(min p b)+min p b := by
  rw [←supportsFullIndecomposable_iff_polytopal_weak]
  exact supports_full_iff p b hp hb

theorem lattice_polytopal_attainment (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=min (p+b+1) (2^(min p b)+2*min p b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩

/-- The lattice witness in Theorem8.4 has an actual finite polytopal
complement at exactly the stated dilation. -/
theorem exponential_polytopal_summand (p : ℕ) (hp : 1≤ p) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      ∃ R : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
        IsFinitePolytope R ∧ R.Nonempty ∧
        Q+R=((((p-1)*2^p+2 : ℕ) : ℝ) •
          graphicalZonotope (twoSingletonGraph p (2^p+p))) := by
  obtain ⟨Q,hl,hi,hd,hs⟩:=(exponential_lattice_summand p hp).polytope
  have hM : (0 : ℝ)<(((p-1)*2^p+2 : ℕ) : ℝ):=by positivity
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p))):=
    ⟨_,hM,hs⟩
  refine ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hl.finitePolytope hw).mp hi,hd,?_⟩
  exact (isMinkowskiSummand_graphical_iff_finite_complement hl.finitePolytope hM.le).mp hs

end GraphicalZonotopes.TwoHub

end
end
end BundlePart356

section BundlePart357
/- Source: Papers/GraphicalZonotopes/TwoHubConsequences.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem two_pow_gt_add_one (p : ℕ) (hp : 2 ≤ p) : p+1 < 2^p := by
  induction p,hp using Nat.le_induction with
  | base => decide
  | succ p hp ih =>
    rw [pow_succ]
    omega

/-- The exponential family has no spanning admissible 3-tree. The proof
uses the previously verified exact four-part spanning criterion, with every
part and every vertex retained. -/
theorem exponential_no_admissible_spanning (p : ℕ) (hp : 2 ≤ p) :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  have hpb : p ≤ 2^p+p := Nat.le_add_left p (2^p)
  intro h
  have hbound := (FourPartSpanning.four_partite_spanning_iff (![1,1,p,2^p+p])
    (by intro i; fin_cases i <;> simp <;> omega)).mp h
  rw [part_sum,part_sup p (2^p+p) hp1 hpb] at hbound
  have hpow := two_pow_gt_add_one p hp
  omega

/-- Corollary 8.5, with a lattice witness and the paper's ordinary
polytopal notion of indecomposability. -/
theorem paper_corollary_8_5 (p : ℕ) (hp : 2 ≤ p) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i)) → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨Q,hQ,hi,hd,R,hR,hnR,he⟩ := exponential_polytopal_summand p hp1
  refine ⟨⟨Q,hQ,hi,?_,?_⟩,exponential_no_admissible_spanning p hp⟩
  · unfold FullDimension
    rw [hd,twoSingleton_card]
    have hpow : 0 < (2 : ℕ)^p := by positivity
    omega
  · exact ⟨_,by positivity,R,hR.compact,hR.convex,hnR,he⟩

end GraphicalZonotopes.TwoHub

end
end
end BundlePart357

section BundlePart358
/- Source: Papers/GraphicalZonotopes/Reflection.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lower-support data of reflection through the origin. -/
def reflectedFunction (z : SetFunction V) (S : Finset V) : ℝ := z Sᶜ-z univ

theorem subsetSum_add_compl (x : V → ℝ) (S : Finset V) :
    subsetSum x S+subsetSum x Sᶜ=subsetSum x univ := by
  exact Finset.sum_add_sum_compl S x

@[simp] theorem subsetSum_neg (x : V → ℝ) (S : Finset V) :
    subsetSum (-x) S= -subsetSum x S := by
  simp [subsetSum]

theorem reflectedFunction_normalized (z : SetFunction V) : Normalized (reflectedFunction z) := by
  simp [Normalized,reflectedFunction]

theorem mem_basePolytope_reflected_iff {z : SetFunction V} (hz : Normalized z) (x : V → ℝ) :
    x∈basePolytope (reflectedFunction z) ↔ -x∈basePolytope z := by
  constructor
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      simpa [reflectedFunction, show z ∅ = 0 from hz] using h
    refine ⟨by rw [subsetSum_neg,htotal,neg_neg],?_⟩
    intro S
    have h := hx.2 Sᶜ
    change z (Sᶜ)ᶜ-z univ≤ subsetSum x Sᶜ at h
    rw [compl_compl] at h
    have hc := subsetSum_add_compl x S
    rw [htotal] at hc
    rw [subsetSum_neg]
    linarith
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      rw [subsetSum_neg] at h
      linarith
    refine ⟨?_,?_⟩
    · simpa [reflectedFunction, show z ∅ = 0 from hz] using htotal
    · intro S
      have h := hx.2 Sᶜ
      rw [subsetSum_neg] at h
      have hc := subsetSum_add_compl x S
      rw [htotal] at hc
      change z Sᶜ-z univ≤ subsetSum x S
      linarith

/-- Exact reflection as an equality of ordinary convex-body point sets. -/
theorem basePolytope_reflected {z : SetFunction V} (hz : Normalized z) :
    basePolytope (reflectedFunction z)=(-1 : ℝ) • basePolytope z := by
  ext x
  constructor
  · intro hx
    refine ⟨-x,(mem_basePolytope_reflected_iff hz x).mp hx,?_⟩
    simp
  · rintro ⟨y,hy,rfl⟩
    apply (mem_basePolytope_reflected_iff hz _).mpr
    simpa using hy

/-- An explicit complement identity on set functions yields the exact
translated-reflection identity for the polytopes, without geometric shortcuts. -/
theorem basePolytope_eq_translate_reflection {z w : SetFunction V}
    (hz : Normalized z) (t : V → ℝ)
    (he : reflectedFunction z=w-modular t) :
    basePolytope w=({t} : Set (V → ℝ))+(-1 : ℝ) • basePolytope z := by
  have hw : w=reflectedFunction z+modular t := by rw [he,sub_add_cancel]
  rw [hw,basePolytope_translate,basePolytope_reflected hz]

end GraphicalZonotopes

end
end
end BundlePart358

section BundlePart359
/- Source: Papers/GraphicalZonotopes/DoubledSymmetry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem two_choose_two_int (n : ℕ) :
    2*(n.choose 2 : ℤ)=(n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' n 1
    rw [hc]
    push_cast
    nlinarith

@[simp] theorem firstSet_compl (S : Finset (I×Fin 2)) : firstSet Sᶜ=(firstSet S)ᶜ := by
  ext i
  simp
@[simp] theorem secondSet_compl (S : Finset (I×Fin 2)) : secondSet Sᶜ=(secondSet S)ᶜ := by
  ext i
  simp
@[simp] theorem firstSet_univ : firstSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp
@[simp] theorem secondSet_univ : secondSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp

theorem double_count_compl (S : Finset (I×Fin 2)) :
    ((firstSet Sᶜ∩secondSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-(S.card : ℤ)+((firstSet S∩secondSet S).card : ℤ) := by
  have hU : firstSet Sᶜ∩secondSet Sᶜ=(firstSet S∪secondSet S)ᶜ := by
    ext i
    simp
  have hcard := card_union_add_card_inter (firstSet S) (secondSet S)
  have hbound := card_le_univ (firstSet S∪secondSet S)
  rw [hU,card_compl,Nat.cast_sub hbound]
  have hc : ((firstSet S∪secondSet S).card : ℤ)+
      ((firstSet S∩secondSet S).card : ℤ)=((firstSet S).card : ℤ)+((secondSet S).card : ℤ) :=
    by exact_mod_cast hcard
  rw [card_eq_first_add_second]
  push_cast
  omega

theorem integerData_univ :
    integerData (univ : Finset (I×Fin 2))=
      2*(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(Fintype.card I : ℤ) := by
  have h := integerData_count_identity (univ : Finset (I×Fin 2))
  simp only [firstSet_univ,secondSet_univ,inter_self,card_univ,Fintype.card_prod,
    Fintype.card_fin] at h
  have hc := two_choose_two_int (Fintype.card I*2)
  push_cast at h hc
  nlinarith

theorem integerData_compl (S : Finset (I×Fin 2)) :
    integerData Sᶜ=integerData S+integerData (univ : Finset (I×Fin 2))-
      2*(((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ)) := by
  have hS := integerData_count_identity S
  have hC := integerData_count_identity Sᶜ
  have hcard : (Sᶜ.card : ℤ)=2*(Fintype.card I : ℤ)-(S.card : ℤ) := by
    rw [card_compl,Nat.cast_sub (card_le_univ S)]
    simp [Fintype.card_prod,mul_comm]
  have hfirst : ((firstSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-((firstSet S).card : ℤ) := by
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))]
  rw [double_count_compl,hfirst] at hC
  have h2S := two_choose_two_int S.card
  have h2C := two_choose_two_int Sᶜ.card
  rw [hcard] at h2C
  rw [integerData_univ]
  nlinarith

theorem graphFunction_compl (S : Finset (I×Fin 2)) :
    graphFunction (graph I) Sᶜ-graphFunction (graph I) univ=
      graphFunction (graph I) S-2*((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (integerData_compl S)
  push_cast at h
  simp only [cast_integerData,modular,subsetSum] at h
  have hs : (∑ v∈S,(firstWeight v : ℝ))=((firstSet S).card : ℝ) := by
    exact_mod_cast firstWeight_sum S
  have hc : (∑ v∈Sᶜ,(firstWeight v : ℝ))=
      (Fintype.card I : ℝ)-((firstSet S).card : ℝ) := by
    have hh := firstWeight_sum Sᶜ
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))] at hh
    exact_mod_cast hh
  have hu : (∑ v : I×Fin 2,(firstWeight v : ℝ))=(Fintype.card I : ℝ) := by
    have hh := firstWeight_sum (univ : Finset (I×Fin 2))
    simp only [firstSet_univ,card_univ] at hh
    exact_mod_cast hh
  rw [hs,hc,hu] at h
  linarith

theorem floor_reflection_even (m M d : ℤ) (hM : Even M) :
    (m+M-2*d)/2-M/2=m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem floor_reflection_odd (m M d : ℤ) (hM : Odd M) :
    (m+M-2*d)/2-M/2=m-m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem integerData_univ_even (hI : Even (Fintype.card I)) :
    Even (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=(k : ℤ)+(k : ℤ) := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

theorem integerData_univ_odd (hI : Odd (Fintype.card I)) :
    Odd (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=2*(k : ℤ)+1 := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

def firstReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1+(firstWeight v : ℝ)
def secondReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1-(firstWeight v : ℝ)
def differenceReflectionVector (_ : I×Fin 2) : ℝ := (Fintype.card I : ℝ)-1

theorem modular_firstReflectionVector (S : Finset (I×Fin 2)) :
    modular firstReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)+((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,firstReflectionVector,sum_add_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_secondReflectionVector (S : Finset (I×Fin 2)) :
    modular secondReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)-((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,secondReflectionVector,sum_sub_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_differenceReflectionVector (S : Finset (I×Fin 2)) :
    modular differenceReflectionVector S=((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  simp [modular,subsetSum,differenceReflectionVector,mul_comm] <;> ring

theorem reflected_setFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=setFunction-modular firstReflectionVector := by
  funext S
  have h := floor_reflection_even (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_even hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  simpa only [reflectedFunction,setFunction,Pi.sub_apply,modular_firstReflectionVector] using hc

theorem reflected_complementFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (complementFunction (I := I))=
      complementFunction-modular secondReflectionVector := by
  funext S
  have hz := congrFun (reflected_setFunction_even hI) S
  change setFunction Sᶜ-setFunction univ=setFunction S-modular firstReflectionVector S at hz
  have hg := graphFunction_compl S
  simp only [reflectedFunction,complementFunction,Pi.sub_apply]
  rw [modular_firstReflectionVector] at hz
  rw [modular_secondReflectionVector]
  linarith

theorem reflected_setFunction_odd (hI : Odd (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=
      complementFunction-modular differenceReflectionVector := by
  funext S
  have h := floor_reflection_odd (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_odd hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  rw [cast_integerData] at hc
  have hw : modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S=((firstSet S).card : ℝ) := by
    change (∑ v∈S,(firstWeight v : ℝ))=_
    exact_mod_cast firstWeight_sum S
  rw [hw] at hc
  change setFunction Sᶜ-setFunction univ=
    (graphFunction (graph I) S-setFunction S)-modular differenceReflectionVector S
  rw [modular_differenceReflectionVector]
  change (((integerData Sᶜ/2 : ℤ) : ℝ)-((integerData univ/2 : ℤ) : ℝ))=_
  dsimp only [setFunction]
  linarith

theorem polytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (polytope (I := I)) := by
  exact ⟨firstReflectionVector,basePolytope_eq_translate_reflection
    setFunction_translationNormalized.1 firstReflectionVector (reflected_setFunction_even hI)⟩

theorem complementPolytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (complementPolytope (I := I)) := by
  exact ⟨secondReflectionVector,basePolytope_eq_translate_reflection
    complementFunction_translationNormalized.1 secondReflectionVector
    (reflected_complementFunction_even hI)⟩

theorem complementPolytope_reflection (hI : Odd (Fintype.card I)) :
    complementPolytope (I := I)=
      ({differenceReflectionVector} : Set ((I×Fin 2) → ℝ))+(-1 : ℝ) • polytope :=
  basePolytope_eq_translate_reflection setFunction_translationNormalized.1
    differenceReflectionVector (reflected_setFunction_odd hI)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart359

section BundlePart360
/- Source: Papers/GraphicalZonotopes/DoubledPrincipal.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open scoped Pointwise

/-- The full Theorem9.8, with both actual lattice summands, both geometric
indecomposabilities, their full dimensions and complete actual root-direction
graphs, every Boolean elemental slack, and the two parity-specific symmetry
conclusions. -/
def PrincipalBooleanPhaseClaim : Prop :=
  ∀ r : ℕ,4≤ r → ∃ Q R : Set ((Fin r×Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R=graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q=doubledPartGraph r ∧ actualDirectionGraph R=doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t,R=({t} : Set ((Fin r×Fin 2) → ℝ))+(-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r)=
      Q+(-1 : ℝ) • Q+({fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r×Fin 2) → ℝ)))

/-- A uniform floor-half construction proves all parity cases without a
restriction on r. Its finite four-bit coefficient identity is applied to
every four-clique through the explicit Möbius formula. -/
theorem principal_boolean_phase_theorem : PrincipalBooleanPhaseClaim := by
  intro r hr
  have h4 : 4≤ Fintype.card (Fin r) := by simpa using hr
  have h3 : 3≤ Fintype.card (Fin r) := by simpa using (show 3≤ r by omega)
  have hgraph : graph (Fin r)=doubledPartGraph r := rfl
  refine ⟨polytope (I := Fin r),complementPolytope (I := Fin r),
    polytope_lattice,complementPolytope_lattice,
    polytope_indecomposable h4,complementPolytope_indecomposable h4,
    polytope_fullDimension h3,complementPolytope_fullDimension h3,?_,?_,?_,
    polytope_booleanElemental,complementPolytope_booleanElemental,?_,?_,?_⟩
  · simpa only [hgraph] using (polytope_add_complement (I := Fin r))
  · exact (polytope_actualDirectionGraph h3).trans hgraph
  · exact (complementPolytope_actualDirectionGraph h3).trans hgraph
  · intro he
    have he' : Even (Fintype.card (Fin r)) := by simpa using he
    exact ⟨polytope_centrallySymmetric he',complementPolytope_centrallySymmetric he'⟩
  · intro ho
    exact ⟨differenceReflectionVector,
      complementPolytope_reflection (by simpa using ho)⟩
  · intro ho
    have he := complementPolytope_reflection (I := Fin r) (by simpa using ho)
    have ht : (differenceReflectionVector (I := Fin r))=
        (fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)) := by
      funext v
      simp only [differenceReflectionVector,Fintype.card_fin]
      rw [Nat.cast_sub (show 1≤ r by omega),Nat.cast_one]
    rw [ht] at he
    rw [← hgraph,← polytope_add_complement,he]
    ac_rfl

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart360

section BundlePart361
/- Source: Papers/GraphicalZonotopes/UnitLatticeSharp.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The entire statement of Theorem 9.5: the unrestricted classification and
its actual seven-dimensional lattice equality witness. -/
theorem unit_lattice_classification_sharp :
    Targets.UnitLatticeClassification ∧
      ∃ Q : Set ((Fin 4×Fin 2) → ℝ),LatticePolytope Q ∧
        MinkowskiIndecomposable Q ∧ Module.finrank ℝ (vectorSpan ℝ Q)=7 ∧
        IsMinkowskiSummand Q (graphicalZonotope (doubledPartGraph 4)) ∧
        actualDirectionGraph Q=doubledPartGraph 4 := by
  obtain ⟨Q,R,hQ,hR,hiQ,hiR,hdQ,hdR,he,hgraph,hgraphR,hrest⟩ :=
    DoubledParts.principal_boolean_phase_theorem 4 (by norm_num)
  exact ⟨unit_lattice_classification,Q,hQ,hiQ,
    by simpa only [FullDimension,Fintype.card_prod,Fintype.card_fin] using hdQ,
    ⟨R,hR.compact,hR.convex,hiR.1,he⟩,hgraph⟩

end GraphicalZonotopes

end
end
end BundlePart361

section BundlePart362
/- Source: Audit/AllResults.lean -/






/-! # Complete principal-result audit entry point

Every import is a genuine mathematical source module. No result is assumed here.
-/



















#print axioms GraphicalZonotopes.Path.principal_path_theorem
#print axioms GraphicalZonotopes.Path.polytope_defining_equations
#print axioms GraphicalZonotopes.Path.polytope_defining_equations_real
#print axioms GraphicalZonotopes.Path.polytope_defining_equations_sums
#print axioms GraphicalZonotopes.Path.setFunction_expansion
#print axioms GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction
#print axioms GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete
#print axioms GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal
#print axioms GraphicalZonotopes.sharp_direction_bounds
#print axioms GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root
#print axioms GraphicalZonotopes.root_parallel_pair_eq
#print axioms GraphicalZonotopes.direction_bounds_polytopal
#print axioms GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra
#print axioms GraphicalZonotopes.edge_bound_of_connected_tetrahedra
#print axioms GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra
#print axioms GraphicalZonotopes.Path.setFunction_eq_booleanFormula
#print axioms GraphicalZonotopes.Path.polytope_boolean_defining_equations
#print axioms GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem
#print axioms GraphicalZonotopes.BooleanFourier.boolean_face_line
#print axioms GraphicalZonotopes.BooleanFourier.faceKernel_finrank
#print axioms GraphicalZonotopes.threeTree_classification_polytopal
#print axioms GraphicalZonotopes.threeTree_classification
#print axioms GraphicalZonotopes.threeTree_classification_literal
#print axioms GraphicalZonotopes.admissible_threeTree_lattice_witness
#print axioms GraphicalZonotopes.threeTree_lattice_dilation_sharp
#print axioms GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal
#print axioms GraphicalZonotopes.Separator.induced_separator_capacity_finite
#print axioms GraphicalZonotopes.Separator.positive_response_gluing_finite
#print axioms GraphicalZonotopes.Separator.clique_separator_capacity_finite
#print axioms GraphicalZonotopes.unit_lattice_classification_sharp
#print axioms GraphicalZonotopes.unit_lattice_classification_polytopal
#print axioms GraphicalZonotopes.unit_translated_lattice_classification_polytopal
#print axioms GraphicalZonotopes.threeTree_translated_lattice_lower_bound
#print axioms GraphicalZonotopes.FourPartCompletion.cartesian_completion
#print axioms GraphicalZonotopes.four_partite_spanning_threeTrees
#print axioms GraphicalZonotopes.four_partite_threeTree_dimension_attained
#print axioms GraphicalZonotopes.threeTree_actual_dimension_admissible
#print axioms GraphicalZonotopes.admissible_threeTree_active_witness
#print axioms GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal
#print axioms GraphicalZonotopes.optimal_k5_free_dilation
#print axioms GraphicalZonotopes.optimal_k5_free_dilation_attained
#print axioms GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal
#print axioms GraphicalZonotopes.DoubledParts.one_singleton_decomposition
#print axioms GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition
#print axioms GraphicalZonotopes.boolean_decomposition_every_dimension
#print axioms GraphicalZonotopes.BooleanModule.small_count_lattice_books
#print axioms GraphicalZonotopes.BooleanModule.one_outer_lattice_book
#print axioms GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1
#print axioms GraphicalZonotopes.DiamondBook.maximum_dimension
#print axioms GraphicalZonotopes.DiamondBook.diamond_witness_multipartite
#print axioms GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree
#print axioms GraphicalZonotopes.BooleanModule.positive_star_interpolation
#print axioms GraphicalZonotopes.BooleanModule.negative_star_interpolation
#print axioms GraphicalZonotopes.BooleanModule.threshold_book_interval
#print axioms GraphicalZonotopes.BooleanModule.book_upper_interval
#print axioms GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal
#print axioms GraphicalZonotopes.not_fullLatticeSummandAt_zero
#print axioms GraphicalZonotopes.PathJoin.corollary_nine_four
#print axioms GraphicalZonotopes.PathJoin.appendix_B_one
#print axioms GraphicalZonotopes.clique_book_classification
#print axioms GraphicalZonotopes.clique_book_classification_polytopal
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric
#print axioms GraphicalZonotopes.saturatedHubNeighbors_closed_formula
#print axioms GraphicalZonotopes.SparseFamily.paper_theorem_8_2
#print axioms GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal
#print axioms GraphicalZonotopes.TwoHub.exponential_lattice_summand
#print axioms GraphicalZonotopes.TwoHub.exponential_family
#print axioms GraphicalZonotopes.TwoHub.exponential_polytopal_summand
#print axioms GraphicalZonotopes.TwoHub.two_singleton_classification
#print axioms GraphicalZonotopes.TwoHub.classification_polytopal
#print axioms GraphicalZonotopes.TwoHub.full_polytopal_iff
#print axioms GraphicalZonotopes.TwoHub.lattice_polytopal_attainment
#print axioms GraphicalZonotopes.partial_threeTree_piecewise_maximum
#print axioms GraphicalZonotopes.partial_threeTree_full_dimension_spectrum
#print axioms GraphicalZonotopes.threeTree_dimension_and_spectrum
#print axioms GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite
#print axioms GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite
#print axioms GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected
#print axioms GraphicalZonotopes.weak_summand_exposed_edge_direction
#print axioms GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal
#print axioms GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement
#print axioms GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement
#print axioms GraphicalZonotopes.partial_threeTree_polytope_support
#print axioms GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula
#print axioms GraphicalZonotopes.TwoHub.paper_corollary_8_5
#print axioms GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le
#print axioms GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian
#print axioms GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite
#print axioms GraphicalZonotopes.actualEdgeDirectionLines_finite
#print axioms GraphicalZonotopes.directionCount_eq_geometric_line_count
#print axioms GraphicalZonotopes.three_hub_book_maximum
#print axioms GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree
#print axioms GraphicalZonotopes.TreeJoin.maximum_dimension
#print axioms GraphicalZonotopes.TreeJoin.supports_full_iff
#print axioms GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join
#print axioms GraphicalZonotopes.SparseFamily.complete_family
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper
#print axioms GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq
#print axioms GraphicalZonotopes.TwoHub.decision_tree_lattice_summand
#print axioms GraphicalZonotopes.TwoHub.paper_lemma_8_6

end BundlePart362
