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

public import verified.parts.part005
import all verified.parts.part005

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart63
/- Source: Papers/GraphicalZonotopes/ThreeTreeStates.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_opposite {C T : Finset V} (hC : C.card=4) (hT : T.card=3)
    (hTC : T⊆C) : ∃ r : ↥C,C.erase r.1=T := by
  have hcard : (C\T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
  obtain ⟨r,hr⟩ := card_eq_one.mp hcard
  have hrmem : r∈C\T := by rw [hr]; simp
  obtain ⟨hrC,hrT⟩ := mem_sdiff.mp hrmem
  refine ⟨⟨r,hrC⟩,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxr,hxC⟩ := mem_erase.mp hx
    by_contra hxT
    have hxs : x∈C\T := mem_sdiff.mpr ⟨hxC,hxT⟩
    rw [hr,mem_singleton] at hxs
    exact hxr hxs
  · intro hxT
    exact mem_erase.mpr ⟨fun hxr => hrT (by simpa only [hxr] using hxT),hTC hxT⟩

def opposite (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (opposite G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    (opposite G C T hTC).1∉T.1 := by
  rw [← opposite_spec G C T hTC]
  exact notMem_erase _ _

abbrev CliqueState (G : SimpleGraph V) (C : ↥(tetrahedra G)) :=
  FourState (fun p : ↥C.1 => C.1.erase p.1∈internalTriangles G)

abbrev IncidentClique (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

abbrev TriangleLocalState (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  TriangleState (IncidentClique G T) ↥T.1

def cliquePort (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) : ↥T.1 → Bool :=
  fun j => s.row (opposite G C T hTC) ⟨j.1,hTC j.2⟩

theorem cliquePort_nonconstant (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) :
    NonconstantBits (cliquePort G C T hTC s) := by
  let p := opposite G C T hTC
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  obtain ⟨⟨j,hjp,hj⟩,⟨k,hkp,hk⟩⟩ := s.nonconstant p hp
  have hjT : j.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hjp (Subtype.ext he),j.2⟩
  have hkT : k.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hkp (Subtype.ext he),k.2⟩
  exact ⟨⟨⟨j.1,hjT⟩,hj⟩,⟨⟨k.1,hkT⟩,hk⟩⟩

theorem cliqueState_extend (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1)
    (v : ↥T.1 → Bool) (hv : NonconstantBits v) :
    ∃ s : CliqueState G C,cliquePort G C T hTC s=v := by
  classical
  let p := opposite G C T hTC
  let input : ↥C.1 → Bool := fun j => if hj : j.1∈T.1 then v ⟨j.1,hj⟩ else false
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  have hnot := opposite_notMem G C T hTC
  have hin : NonconstantAt input p := by
    obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩ := hv
    refine ⟨⟨⟨j.1,hTC j.2⟩,?_,?_⟩,⟨⟨k.1,hTC k.2⟩,?_,?_⟩⟩
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ j.2)
    · simpa only [input,dif_pos j.2] using hj
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ k.2)
    · simpa only [input,dif_pos k.2] using hk
  have hc : Fintype.card ↥C.1=4 := by
    rw [Fintype.card_coe]
    exact (mem_filter.mp C.2).2.1
  obtain ⟨s,hs⟩ := fourState_extend hc
    (fun q : ↥C.1 => C.1.erase q.1∈internalTriangles G) p hp input hin
  refine ⟨s,?_⟩
  funext j
  have hjp : (⟨j.1,hTC j.2⟩ : ↥C.1)≠ p := by
    intro he
    exact hnot ((congrArg Subtype.val he) ▸ j.2)
  change s.row p ⟨j.1,hTC j.2⟩=v j
  rw [hs _ hjp]
  simp only [input,dif_pos j.2]

def incidentCliqueEquiv (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    IncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidentClique_card (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (incidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem incidentClique_card_two_or_three (G : SimpleGraph V) (hG : Admissible G)
    (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=2 ∨ Fintype.card (IncidentClique G T)=3 := by
  obtain ⟨hT,hlo⟩ := mem_internalTriangles.mp T.2
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  have hhi := hG T.1 hc hcl
  rw [incidentClique_card]
  omega

def LocalState (G : SimpleGraph V) : InternalIncidenceNode G → Type _
  | Sum.inl C => CliqueState G C
  | Sum.inr T => TriangleLocalState G T

abbrev PortColor (G : SimpleGraph V) := Option (Σ T : ↥(internalTriangles G),↥T.1 → Bool)

def localPort (G : SimpleGraph V) (x y : InternalIncidenceNode G) :
    LocalState G x → PortColor G :=
  match x,y with
  | Sum.inl C,Sum.inr T => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,cliquePort G C T hTC s⟩ else none
  | Sum.inr T,Sum.inl C => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,s.row ⟨C,hTC⟩⟩ else none
  | _,_ => fun _ => none

theorem localState_nonempty (G : SimpleGraph V) (hG : Admissible G)
    (N : InternalIncidenceNode G) : Nonempty (LocalState G N) := by
  classical
  cases N with
  | inl C =>
    exact fourState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_filter.mp C.2).2.1) _
  | inr T =>
    exact triangleState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
      (incidentClique_card_two_or_three G hG T)

theorem localState_matching (G : SimpleGraph V) (hG : Admissible G)
    (x y : InternalIncidenceNode G) (hxy : (internalIncidence G).Adj x y)
    (t : LocalState G y) :
    ∃ s : LocalState G x,localPort G x y s=localPort G y x t := by
  classical
  cases x with
  | inl C =>
    cases y with
    | inl D => exact False.elim hxy
    | inr T =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := cliqueState_extend G C T hTC (t.row ⟨C,hTC⟩)
        (t.nonconstant ⟨C,hTC⟩)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩
  | inr T =>
    cases y with
    | inr U => exact False.elim hxy
    | inl C =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := triangleState_extend (by
        rw [Fintype.card_coe]
        exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
        (incidentClique_card_two_or_three G hG T) (⟨C,hTC⟩ : IncidentClique G T)
        (cliquePort G C T hTC t) (cliquePort_nonconstant G C T hTC t)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩

/-- Actual compatible rows on every clique and every internal triangle,
including the one-dimensional real relation at each triangle. -/
structure CompatibleRows (G : SimpleGraph V) where
  clique : ∀ C : ↥(tetrahedra G),CliqueState G C
  triangle : ∀ T : ↥(internalTriangles G),TriangleLocalState G T
  port_eq : ∀ (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1),
    cliquePort G C T hTC (clique C)=(triangle T).row ⟨C,hTC⟩

theorem compatibleRows_exists {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hG : Admissible G) : Nonempty (CompatibleRows G) := by
  classical
  obtain ⟨s,hs⟩ := tree_compatible_states (internalIncidence G) h.internalIncidence_isTree
    (LocalState G) (localState_nonempty G hG) (PortColor G) (localPort G)
    (localState_matching G hG)
  refine ⟨{
    clique := fun C => s (Sum.inl C)
    triangle := fun T => s (Sum.inr T)
    port_eq := ?_ }⟩
  intro C T hTC
  have he := hs (Sum.inl C) (Sum.inr T) hTC
  simp only [localPort,dif_pos hTC] at he
  exact sigma_mk_injective (Option.some.inj he)

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart63

section BundlePart64
/- Source: Papers/GraphicalZonotopes/ThreeTreeColumns.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev AllIncidentClique (G : SimpleGraph V) (T : ↥(triangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

def faceMissing (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(triangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1 (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (faceMissing G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    (faceMissing G C T hTC).1∉T.1 := by
  rw [← faceMissing_spec G C T hTC]
  exact notMem_erase _ _

def faceRow (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (C : AllIncidentClique G T) (j : ↥T.1) : Bool :=
  (s.clique C.1).row (faceMissing G C.1 T C.2) ⟨j.1,C.2 j.2⟩

def columnValue (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (j : ↥T.1) : ℝ :=
  ∑ C : AllIncidentClique G T,realBit (faceRow G s T C j)

def allIncidentCliqueEquiv (G : SimpleGraph V) (T : ↥(triangles G)) :
    AllIncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem allIncidentClique_card (G : SimpleGraph V) (T : ↥(triangles G)) :
    Fintype.card (AllIncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (allIncidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem internal_column (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (hT : T.1∈internalTriangles G) (j : ↥T.1) :
    columnValue G s T j=((s.triangle ⟨T.1,hT⟩).degree : ℝ) := by
  let T' : ↥(internalTriangles G) := ⟨T.1,hT⟩
  have he : ∀ C : AllIncidentClique G T,
      faceRow G s T C j=(s.triangle T').row C j := by
    intro C
    exact congrArg (fun f : ↥T.1 → Bool => f j) (s.port_eq C.1 T' C.2)
  unfold columnValue
  simp_rw [he]
  exact (s.triangle T').sum_row j

/-- The column sums on every actual triangle, including the leaf
triangles, are constants in {0,1,2}. The leaf case is proved from its actual
single incident tetrahedron, rather than assigned an unproved response. -/
theorem column_constant {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    ∃ d : ℕ,(d=0 ∨ d=1 ∨ d=2) ∧ ∀ j : ↥T.1,columnValue G s T j=(d : ℝ) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · refine ⟨(s.triangle ⟨T.1,hT⟩).degree,?_,internal_column G s T hT⟩
    exact Or.inr (s.triangle ⟨T.1,hT⟩).degree_mem
  · have htri := mem_triangles.mp T.2
    obtain ⟨C,hC,hTC⟩ := h.triangle_extends htri.1 htri.2
    have hpos : 0< triangleMultiplicity G T.1 := by
      apply card_pos.mpr
      exact ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
    have hsmall : ¬2≤ triangleMultiplicity G T.1 := fun hcount =>
      hT (mem_internalTriangles.mpr ⟨T.2,hcount⟩)
    have hone : Fintype.card (AllIncidentClique G T)=1 := by
      rw [allIncidentClique_card]
      omega
    obtain ⟨C₀,hunique⟩ := Fintype.card_eq_one_iff.mp hone
    let p := faceMissing G C₀.1 T C₀.2
    have hleaf : C₀.1.1.erase p.1∉internalTriangles G := by
      rw [faceMissing_spec G C₀.1 T C₀.2]
      exact hT
    obtain ⟨b,hb⟩ := (s.clique C₀.1).constant p hleaf
    have hcol : ∀ j : ↥T.1,columnValue G s T j=realBit b := by
      intro j
      unfold columnValue
      rw [sum_eq_single C₀]
      · apply congrArg realBit
        apply hb
        intro he
        exact faceMissing_notMem G C₀.1 T C₀.2
          ((congrArg Subtype.val he) ▸ j.2)
      · intro D hD hne
        exact False.elim (hne (hunique D))
      · intro hn
        exact False.elim (hn (mem_univ C₀))
    cases hbval : b
    · exact ⟨0,Or.inl rfl,fun j => by simpa [hbval,realBit] using hcol j⟩
    · exact ⟨1,Or.inr (Or.inl rfl),fun j => by simpa [hbval,realBit] using hcol j⟩

def triangleWeight {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) : ℕ :=
  Classical.choose (column_constant h s T)

theorem triangleWeight_mem {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    triangleWeight h s T=0 ∨ triangleWeight h s T=1 ∨ triangleWeight h s T=2 :=
  (Classical.choose_spec (column_constant h s T)).1

theorem column_eq_triangleWeight {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (T : ↥(triangles G)) (j : ↥T.1) :
    columnValue G s T j=(triangleWeight h s T : ℝ) :=
  (Classical.choose_spec (column_constant h s T)).2 j

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart64

section BundlePart65
/- Source: Papers/GraphicalZonotopes/EdgeCoordinates.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unordered graph edges and two-element clique sets are exactly equivalent
coordinate systems, including their finite sums. -/
theorem sym2_toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f he
  apply Sym2.ext
  intro v
  apply Iff.of_eq
  simpa only [Sym2.mem_toFinset] using congrArg (fun C : Finset V => v∈C) he

theorem edgeFamily_eq_image_edgeFinset (G : SimpleGraph V) :
    edgeFamily G=G.edgeFinset.image Sym2.toFinset := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G C).mp hC
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G hab).mp hC
    exact mem_image.mpr ⟨s(a,b),G.mem_edgeFinset.mpr hadj,Sym2.toFinset_mk_eq⟩
  · rintro hC
    obtain ⟨e,he,rfl⟩ := mem_image.mp hC
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq]
    have hadj := G.mem_edgeFinset.mp he
    exact (pair_mem_edgeFamily G (G.ne_of_adj hadj)).mpr hadj

theorem sum_edgeFamily_eq (G : SimpleGraph V) (f : Finset V → ℝ) :
    (∑ C∈edgeFamily G,f C)=∑ e∈G.edgeFinset,f e.toFinset := by
  rw [edgeFamily_eq_image_edgeFinset,sum_image]
  exact fun e he d hd h => sym2_toFinset_injective h

end GraphicalZonotopes

end
end
end BundlePart65

section BundlePart66
/- Source: Papers/GraphicalZonotopes/TetrahedronPairWeights.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

structure ComplementPair (C E : Finset V) where
  first : ↥C
  second : ↥C
  ne : first≠ second
  erase_eq : (C.erase first.1).erase second.1=E

theorem complementPair_nonempty {C E : Finset V} (hC : C.card=4) (hE : E.card=2)
    (hEC : E⊆C) : Nonempty (ComplementPair C E) := by
  have hc : (C\E).card=2 := by rw [card_sdiff_of_subset hEC,hC,hE]
  obtain ⟨a,b,hab,he⟩ := card_eq_two.mp hc
  have ha : a∈C\E := by rw [he]; simp
  have hb : b∈C\E := by rw [he]; simp
  refine ⟨⟨⟨a,(mem_sdiff.mp ha).1⟩,⟨b,(mem_sdiff.mp hb).1⟩,
    (fun h => hab (congrArg Subtype.val h)),?_⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxb,hx'⟩ := mem_erase.mp hx
    obtain ⟨hxa,hxC⟩ := mem_erase.mp hx'
    by_contra hxE
    have hm : x∈C\E := mem_sdiff.mpr ⟨hxC,hxE⟩
    rw [he,mem_insert,mem_singleton] at hm
    exact hm.elim hxa hxb
  · intro hxE
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,hEC hxE⟩⟩
    · intro hxb
      exact (mem_sdiff.mp hb).2 (by simpa only [hxb] using hxE)
    · intro hxa
      exact (mem_sdiff.mp ha).2 (by simpa only [hxa] using hxE)

def complementPair (G : SimpleGraph V) (C : ↥(tetrahedra G)) (E : Finset V)
    (hE : E.card=2) (hEC : E⊆C.1) : ComplementPair C.1 E :=
  Classical.choice (complementPair_nonempty (mem_filter.mp C.2).2.1 hE hEC)

theorem ComplementPair.pair_eq_complement {C E : Finset V} (p : ComplementPair C E) :
    ({p.first.1,p.second.1} : Finset V)=C\E := by
  conv_rhs => rw [← p.erase_eq]
  ext x
  by_cases hxa : x=p.first.1 <;> by_cases hxb : x=p.second.1 <;>
    simp [hxa,hxb,p.first.2,p.second.2]

theorem ComplementPair.unordered_eq {C E : Finset V} (p q : ComplementPair C E) :
    s(p.first.1,p.second.1)=s(q.first.1,q.second.1) := by
  apply sym2_toFinset_injective
  simp only [Sym2.toFinset_mk_eq,p.pair_eq_complement,q.pair_eq_complement]

def ComplementPair.maximum {C E : Finset V} (p : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : ℤ :=
  max (RootedResponse.integerBit (row p.first p.second)) (RootedResponse.integerBit (row p.second p.first))

theorem ComplementPair.maximum_eq {C E : Finset V} (p q : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : p.maximum row=q.maximum row := by
  rcases Sym2.eq_iff.mp (p.unordered_eq q) with h | h
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.first := Subtype.ext ha
    have hb' : p.second=q.second := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb']
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.second := Subtype.ext ha
    have hb' : p.second=q.first := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb',max_comm]

theorem ComplementPair.maximum_zero_or_one {C E : Finset V}
    (p : ComplementPair C E) (row : ↥C → ↥C → Bool) :
    p.maximum row=0 ∨ p.maximum row=1 := by
  unfold ComplementPair.maximum
  cases row p.first p.second <;> cases row p.second p.first <;> norm_num [RootedResponse.integerBit]

abbrev IncidentPairClique (G : SimpleGraph V) (E : Finset V) :=
  {C : ↥(tetrahedra G) // E⊆C.1}

def pairWeight (G : SimpleGraph V) (s : CompatibleRows G) (E : Finset V)
    (hE : E.card=2) : ℤ :=
  ∑ C : IncidentPairClique G E,
    (complementPair G C.1 E hE C.2).maximum (s.clique C.1).row

theorem pairWeight_nonneg (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) : 0≤ pairWeight G s E hE := by
  apply sum_nonneg
  intro C hC
  rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
    simp [h]

theorem pairWeight_le_incident (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) :
    pairWeight G s E hE≤(Fintype.card (IncidentPairClique G E) : ℤ) := by
  calc
    pairWeight G s E hE≤∑ _ : IncidentPairClique G E,(1:ℤ) := by
      apply sum_le_sum
      intro C hC
      rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
        simp [h]
    _=(Fintype.card (IncidentPairClique G E) : ℤ) := by simp

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart66

section BundlePart67
/- Source: Papers/GraphicalZonotopes/ThreeTreeCoefficients.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual integral Möbius vector of the construction: every
tetrahedron has coefficient one, a triangle has the negative common column
sum, and an edge has the sum of its local maxima. All other coordinates
vanish, including the translation coordinates. -/
def coefficients {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := fun C =>
  if hC : C∈tetrahedra G then 1
  else if hT : C∈triangles G then -(triangleWeight h s ⟨C,hT⟩ : ℝ)
  else if hE : C∈edgeFamily G then (pairWeight G s C ((mem_edgeFamily G C).mp hE).1 : ℝ)
  else 0

theorem coefficients_tetrahedron {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {C : Finset V}
    (hC : C∈tetrahedra G) : coefficients h s C=1 := by
  simp only [coefficients,dif_pos hC]

theorem coefficients_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) : coefficients h s T= -(triangleWeight h s ⟨T,hT⟩ : ℝ) := by
  have hnot : T∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    have h3 := (mem_triangles.mp hT).1
    omega
  simp only [coefficients,dif_neg hnot,dif_pos hT]

theorem coefficients_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {E : Finset V}
    (hE : E∈edgeFamily G) :
    coefficients h s E=(pairWeight G s E ((mem_edgeFamily G E).mp hE).1 : ℝ) := by
  have h2 := ((mem_edgeFamily G E).mp hE).1
  have hnot4 : E∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    omega
  have hnot3 : E∉triangles G := by
    intro hm
    have h3 := (mem_triangles.mp hm).1
    omega
  simp only [coefficients,dif_neg hnot4,dif_neg hnot3,dif_pos hE]

theorem coefficients_triangle_values {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) :
    coefficients h s T=0 ∨ coefficients h s T= -1 ∨ coefficients h s T= -2 := by
  rw [coefficients_triangle h s hT]
  rcases triangleWeight_mem h s ⟨T,hT⟩ with hd | hd | hd <;> rw [hd] <;> norm_num

theorem coefficients_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : CliqueSupported G (coefficients h s) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro v
    simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro C u v hu hv huv hnon
    have h4 : C∉tetrahedra G := by
      intro hm
      exact hnon ((mem_filter.mp hm).2.2 hu hv huv)
    have h3 : C∉triangles G := by
      intro hm
      exact hnon ((mem_triangles.mp hm).2 hu hv huv)
    have h2 : C∉edgeFamily G := by
      intro hm
      exact hnon (((mem_edgeFamily G C).mp hm).2 u hu v hv huv)
    simp only [coefficients,dif_neg h4,dif_neg h3,dif_neg h2]

theorem coefficients_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (coefficients h s) := by
  classical
  intro C
  unfold coefficients
  split
  · exact ⟨1,by norm_num⟩
  · split
    · rename_i hT
      exact ⟨-(triangleWeight h s ⟨C,hT⟩ : ℤ),by simp⟩
    · split
      · rename_i hE
        exact ⟨pairWeight G s C ((mem_edgeFamily G C).mp hE).1,rfl⟩
      · exact ⟨0,by norm_num⟩

def setFunction {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := zeta (coefficients h s)

theorem setFunction_normalized_graphical {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    TranslationNormalized (setFunction h s) ∧ Graphical G (setFunction h s) :=
  (cliqueSupported_iff G _).mp (coefficients_cliqueSupported h s)

theorem setFunction_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (setFunction h s) :=
  zeta_integerValued (coefficients_integerValued h s)

theorem setFunction_mobius {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    mobius (setFunction h s)=coefficients h s := mobius_zeta _

theorem setFunction_ne_zero {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : setFunction h s≠0 := by
  intro hz
  have hy : coefficients h s=0 := by
    apply zeta_injective
    rw [show zeta (coefficients h s)=0 from hz]
    ext C
    simp [zeta]
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  have he := coefficients_tetrahedron h s hC
  rw [hy] at he
  norm_num at he

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart67

section BundlePart68
/- Source: Papers/GraphicalZonotopes/ThreeTreeLink.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph induced on the common neighbors of an edge, with all other
ambient vertices isolated. This ambient form avoids deleting any zero weights
when the link is used as a Boolean interaction graph. -/
def edgeLink (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj u a ∧ G.Adj v a ∧ G.Adj u b ∧ G.Adj v b
  symm := ⟨fun a b h => ⟨G.adj_symm h.1,h.2.2.2.1,h.2.2.2.2,h.2.1,h.2.2.1⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

@[simp] theorem edgeLink_comm (G : SimpleGraph V) (u v : V) :
    edgeLink G u v=edgeLink G v u := by
  ext a b
  simp only [edgeLink]
  tauto

theorem isAcyclic_cliqueGraph_of_card_le_two {C : Finset V} (hC : C.card≤2) :
    (cliqueGraph C).IsAcyclic := by
  by_cases htwo : C.card=2
  · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp htwo
    have he : cliqueGraph ({a,b} : Finset V)=SimpleGraph.edge a b := by
      ext x y
      simp only [cliqueGraph,mem_insert,mem_singleton,SimpleGraph.edge_adj]
      constructor
      · rintro ⟨hxy,hx,hy⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (hxy rfl)
        · exact ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩
        · exact ⟨Or.inr ⟨rfl,rfl⟩,hxy⟩
        · exact False.elim (hxy rfl)
      · rintro ⟨hxy,hne⟩
        rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hab,Ne.symm hab]
    rw [he]
    have h := SimpleGraph.IsAcyclic.sup_edge_of_not_reachable
      (G:=(⊥ : SimpleGraph V)) (u:=a) (v:=b)
      (by simpa only [SimpleGraph.reachable_bot] using hab) SimpleGraph.isAcyclic_bot
    simpa only [bot_sup_eq] using h
  · have hone : C.card≤1 := by omega
    have he : cliqueGraph C=(⊥ : SimpleGraph V) := by
      ext a b
      simp only [SimpleGraph.bot_adj,iff_false]
      intro h
      exact h.1 ((card_le_one.mp hone) a h.2.1 b h.2.2)
    rw [he]
    exact SimpleGraph.isAcyclic_bot

theorem adj_before_attachment {G : SimpleGraph V} {w a b : V} {T : Finset V}
    (ha : a≠ w) (hb : b≠ w) (hab : (G⊔attachmentStar w T).Adj a b) : G.Adj a b := by
  rcases hab with h | h
  · exact h
  · rcases h.2 with ⟨he,_⟩ | ⟨he,_⟩
    · exact False.elim (ha he)
    · exact False.elim (hb he)

theorem edgeLink_new_le_clique {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {w : V} (hw : w∉S) {T : Finset V} (hTS : T⊆S)
    (v : V) : edgeLink (G⊔attachmentStar w T) w v≤ cliqueGraph (T.erase v) := by
  intro a b hab
  have ha := (attached_vertex_adj_iff h hw hTS a).mp hab.2.1
  have hb := (attached_vertex_adj_iff h hw hTS b).mp hab.2.2.2.1
  exact ⟨(G⊔attachmentStar w T).ne_of_adj hab.1,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1),ha⟩,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2),hb⟩⟩

theorem ThreeTreeOn.edgeLink_acyclic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u v : V} (huv : G.Adj u v) :
    (edgeLink G u v).IsAcyclic := by
  induction h generalizing u v with
  | tetrahedron C hC =>
    have hu := huv.2.1
    have hv := huv.2.2
    have hne := huv.1
    have hcard : ((C.erase u).erase v).card≤2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hv⟩),card_erase_of_mem hu,hC]
    apply (isAcyclic_cliqueGraph_of_card_le_two hcard).anti
    intro a b hab
    refine ⟨hab.1.1,?_,?_⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.1.1,
        mem_erase.mpr ⟨Ne.symm hab.2.1.1,hab.1.2.1⟩⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.2.2.1,
        mem_erase.mpr ⟨Ne.symm hab.2.2.2.1.1,hab.1.2.2⟩⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    by_cases huw : u=w
    · subst u
      have hv := (attached_vertex_adj_iff h hw hTS v).mp huv
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase v) (by
        rw [card_erase_of_mem hv,hT])).anti
      exact edgeLink_new_le_clique h hw hTS v
    by_cases hvw : v=w
    · subst v
      rw [edgeLink_comm]
      have hu := (attached_vertex_adj_iff h hw hTS u).mp
        ((G⊔attachmentStar w T).adj_symm huv)
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase u) (by
        rw [card_erase_of_mem hu,hT])).anti
      exact edgeLink_new_le_clique h hw hTS u
    have hold := adj_before_attachment huw hvw huv
    have hi := ih (u:=u) (v:=v) hold
    by_cases hboth : u∈T ∧ v∈T
    · have hne : u≠ v := G.ne_of_adj hold
      have hcard : ((T.erase u).erase v).card=1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hboth.2⟩),
          card_erase_of_mem hboth.1,hT]
      obtain ⟨r,hr⟩ := card_eq_one.mp hcard
      have hrmem : r∈(T.erase u).erase v := by rw [hr]; simp
      have hrT := mem_of_mem_erase (mem_of_mem_erase hrmem)
      have hrw : r≠ w := by intro he; subst r; exact hw (hTS hrT)
      have hnotreach : ¬(edgeLink G u v).Reachable w r := by
        intro hreach
        obtain ⟨x,hx⟩ := hreach.nonempty_neighborSet_left (Ne.symm hrw)
        exact hw (h.edges_supported hx.1).1
      have hforest := hi.sup_edge_of_not_reachable hnotreach
      apply hforest.anti
      intro a b hab
      by_cases haw : a=w
      · subst a
        right
        have hbT := (attached_vertex_adj_iff h hw hTS b).mp hab.1
        have hbu := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.1)
        have hbv := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2)
        have hb : b∈(T.erase u).erase v := mem_erase.mpr ⟨hbv,mem_erase.mpr ⟨hbu,hbT⟩⟩
        rw [hr,mem_singleton] at hb
        subst b
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,Ne.symm hrw⟩
      by_cases hbw : b=w
      · subst b
        right
        have haT := (attached_vertex_adj_iff h hw hTS a).mp
          ((G⊔attachmentStar w T).adj_symm hab.1)
        have hau := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.1)
        have hav := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1)
        have ha : a∈(T.erase u).erase v := mem_erase.mpr ⟨hav,mem_erase.mpr ⟨hau,haT⟩⟩
        rw [hr,mem_singleton] at ha
        subst a
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hrw⟩
      exact Or.inl ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩
    · apply hi.anti
      intro a b hab
      have haw : a≠ w := by
        intro he
        subst a
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.1)⟩
      have hbw : b≠ w := by
        intro he
        subst b
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.2)⟩
      exact ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩

end GraphicalZonotopes

end
end
end BundlePart68

section BundlePart69
/- Source: Papers/GraphicalZonotopes/ForestSigns.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSign (x : ℝ) : Prop := x=1 ∨ x=-1

theorem IsSign.mul {x y : ℝ} (hx : IsSign x) (hy : IsSign y) : IsSign (x*y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [IsSign]

theorem IsSign.sq {x : ℝ} (hx : IsSign x) : x^2=1 := by
  rcases hx with rfl | rfl <;> norm_num

/-- Every assignment of signs to the edges of a finite forest is realized
as products of vertex signs. The proof deletes one bridge and flips precisely
one of its two components; it includes disconnected and empty forests. -/
theorem exists_vertex_signs (G : SimpleGraph V) (hG : G.IsAcyclic)
    (ρ : V → V → ℝ) (hρ : ∀ u v,G.Adj u v → IsSign (ρ u v))
    (hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u) :
    ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,G.Adj u v → σ u*σ v=ρ u v := by
  classical
  suffices h : ∀ n (H : SimpleGraph V),H.edgeFinset.card=n → H.IsAcyclic →
      (∀ u v,H.Adj u v → IsSign (ρ u v)) →
      (∀ u v,H.Adj u v → ρ u v=ρ v u) →
      ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,H.Adj u v → σ u*σ v=ρ u v from
    h _ G rfl hG hρ hρsym
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hcard hH hρ hρsym
    by_cases hbot : H=⊥
    · subst H
      exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
    · obtain ⟨e,he⟩ := H.edgeFinset_nonempty.mpr hbot
      obtain ⟨u,v⟩ := e
      have huv : H.Adj u v := (H.mem_edgeFinset.mp he)
      let H' := H.deleteEdges ({s(u,v)} : Finset (Sym2 V))
      have hle : H' ≤ H := H.deleteEdges_le _
      have hlt : H'.edgeFinset.card< n := by
        change (H.deleteEdges ({s(u,v)} : Finset (Sym2 V))).edgeFinset.card< n
        rw [SimpleGraph.edgeFinset_deleteEdges,sdiff_singleton_eq_erase]
        have hh : (H.edgeFinset.erase s(u,v)).card < H.edgeFinset.card :=
          card_erase_lt_of_mem (show s(u,v) ∈ H.edgeFinset from he)
        exact hh.trans_eq (by simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard)
      obtain ⟨σ,hσ,hσedge⟩ := ih _ hlt H' (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]) (hH.anti hle)
        (fun x y hxy => hρ x y (hle hxy)) (fun x y hxy => hρsym x y (hle hxy))
      have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hH) huv
      have hnotuv : ¬H'.Reachable u v := by
        simpa only [H', Finset.coe_singleton] using SimpleGraph.isBridge_iff.mp hbridge
      have hnotvu : ¬H'.Reachable v u := fun h => hnotuv h.symm
      let a : ℝ := ρ u v*σ u*σ v
      have ha : IsSign a := ((hρ u v huv).mul (hσ u)).mul (hσ v)
      let τ : V → ℝ := fun w => if H'.Reachable v w then a*σ w else σ w
      have hτ : ∀ w,IsSign (τ w) := by
        intro w
        dsimp [τ]
        split
        · exact ha.mul (hσ w)
        · exact hσ w
      have huvτ : τ u*τ v=ρ u v := by
        simp only [τ,if_neg hnotvu,SimpleGraph.Reachable.rfl,if_pos]
        dsimp [a]
        calc
          σ u*((ρ u v*σ u*σ v)*σ v)=ρ u v*(σ u)^2*(σ v)^2 := by ring
          _=ρ u v := by rw [(hσ u).sq,(hσ v).sq]; ring
      refine ⟨τ,hτ,?_⟩
      intro x y hxy
      by_cases heq : s(x,y)=s(u,v)
      · rcases Sym2.eq_iff.mp heq with heq | heq
        · obtain ⟨rfl,rfl⟩ := heq
          exact huvτ
        · obtain ⟨rfl,rfl⟩ := heq
          simpa only [mul_comm, hρsym _ _ hxy] using huvτ
      · have hxy' : H'.Adj x y := by
          refine ⟨hxy, ?_⟩
          intro he
          have hm := he.1
          change s(x,y) ∈ ({s(u,v)} : Finset (Sym2 V)) at hm
          exact heq (Finset.mem_singleton.mp hm)
        have hr : H'.Reachable v x ↔ H'.Reachable v y :=
          ⟨fun h => h.trans hxy'.reachable,fun h => h.trans hxy'.symm.reachable⟩
        by_cases hx : H'.Reachable v x
        · have hy := hr.mp hx
          simp only [τ,if_pos hx,if_pos hy]
          calc
            (a*σ x)*(a*σ y)=a^2*(σ x*σ y) := by ring
            _=ρ x y := by rw [ha.sq,hσedge x y hxy',one_mul]
        · have hy : ¬H'.Reachable v y := fun h => hx (hr.mpr h)
          simp only [τ,if_neg hx,if_neg hy]
          exact hσedge x y hxy'

end ForestSigns
end GraphicalZonotopes

end
end
end BundlePart69

section BundlePart70
/- Source: Papers/GraphicalZonotopes/ForestOscillation.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeProduct (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u*x v,fun _ _ => mul_comm _ _⟩

@[simp] theorem edgeProduct_pair (x : V → ℝ) (u v : V) :
    edgeProduct x s(u,v)=x u*x v := rfl

def spinToBit (σ : V → ℝ) (v : V) : ℝ := (1+σ v)/2

theorem spinToBit_boolean {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,spinToBit σ v=0 ∨ spinToBit σ v=1 := by
  intro v
  rcases hσ v with h | h <;> simp [spinToBit,h]

theorem neg_signs {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,IsSign ((-σ) v) := by
  intro v
  rcases hσ v with h | h <;> simp [IsSign,h]

theorem edgeProduct_spin_complement (σ : V → ℝ) (e : Sym2 V) :
    edgeProduct (spinToBit σ) e+edgeProduct (spinToBit (-σ)) e=
      (1+edgeProduct σ e)/2 := by
  obtain ⟨u,v⟩ := e
  simp only [edgeProduct_pair,spinToBit,Pi.neg_apply]
  ring

def quadratic (G : SimpleGraph V) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ)
    (x : V → ℝ) : ℝ :=
  c+(∑ v,l v*x v)+∑ e ∈ G.edgeFinset,w e*edgeProduct x e

theorem quadratic_spin_complement (G : SimpleGraph V) (c : ℝ)
    (l : V → ℝ) (w : Sym2 V → ℝ) (σ : V → ℝ) :
    quadratic G c l w (spinToBit σ)+quadratic G c l w (spinToBit (-σ))=
      2*c+(∑ v,l v)+(1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
  have hlin : (∑ v,l v*spinToBit σ v)+(∑ v,l v*spinToBit (-σ) v)=∑ v,l v := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    simp only [spinToBit,Pi.neg_apply]
    ring
  have hquad : (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit σ) e)+
      (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit (-σ)) e)=
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
    rw [← sum_add_distrib,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro e he
    rw [← mul_add,edgeProduct_spin_complement]
    ring
  unfold quadratic
  linarith

def coefficientSign (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  if 0 ≤ w s(u,v) then 1 else -1

theorem coefficientSign_isSign (w : Sym2 V → ℝ) (u v : V) :
    IsSign (coefficientSign w u v) := by
  unfold coefficientSign
  split <;> simp [IsSign]

theorem coefficientSign_symm (w : Sym2 V → ℝ) (u v : V) :
    coefficientSign w u v=coefficientSign w v u := by
  simp only [coefficientSign,Sym2.eq_swap]

theorem weight_mul_coefficientSign (w : Sym2 V → ℝ) (u v : V) :
    w s(u,v)*coefficientSign w u v=|w s(u,v)| := by
  by_cases h : 0 ≤ w s(u,v)
  · simp [coefficientSign,h,abs_of_nonneg h]
  · simp [coefficientSign,h,abs_of_neg (lt_of_not_ge h)]

theorem exists_energy_extrema (G : SimpleGraph V) (hG : G.IsAcyclic)
    (w : Sym2 V → ℝ) :
    ∃ σ τ : V → ℝ,(∀ v,IsSign (σ v)) ∧ (∀ v,IsSign (τ v)) ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct σ e)=∑ e ∈ G.edgeFinset,|w e| ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct τ e)=-(∑ e ∈ G.edgeFinset,|w e|) := by
  obtain ⟨σ,hσ,hσe⟩ := exists_vertex_signs G hG (coefficientSign w)
    (fun u v _ => coefficientSign_isSign w u v)
    (fun u v _ => coefficientSign_symm w u v)
  obtain ⟨τ,hτ,hτe⟩ := exists_vertex_signs G hG (fun u v => -coefficientSign w u v)
    (fun u v _ => by
      rcases coefficientSign_isSign w u v with h | h <;> simp [IsSign,h])
    (fun u v _ => by rw [coefficientSign_symm w u v])
  refine ⟨σ,τ,hσ,hτ,?_,?_⟩
  · apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hσe u v (G.mem_edgeFinset.mp he),weight_mul_coefficientSign]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hτe u v (G.mem_edgeFinset.mp he),mul_neg,
      weight_mul_coefficientSign]

/-- Lemma9.3 in its full real-coefficient form: a quadratic Boolean
polynomial whose interaction graph is a forest has oscillation at least half
the total absolute interaction weight. Arbitrary linear and constant terms
are retained. -/
theorem quadratic_oscillation_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (lo hi : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      lo ≤ quadratic G c l w x ∧ quadratic G c l w x ≤ hi) :
    (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|) ≤ hi-lo := by
  obtain ⟨σ,τ,hσ,hτ,hmax,hmin⟩ := exists_energy_extrema G hG w
  have hσplus := hbound (spinToBit σ) (spinToBit_boolean hσ)
  have hσminus := hbound (spinToBit (-σ)) (spinToBit_boolean (neg_signs hσ))
  have hτplus := hbound (spinToBit τ) (spinToBit_boolean hτ)
  have hτminus := hbound (spinToBit (-τ)) (spinToBit_boolean (neg_signs hτ))
  have hfirst := quadratic_spin_complement G c l w σ
  have hsecond := quadratic_spin_complement G c l w τ
  rw [hmax] at hfirst
  rw [hmin] at hsecond
  linarith

end ForestSigns
end GraphicalZonotopes

end
end
end BundlePart70

section BundlePart71
/- Source: Papers/GraphicalZonotopes/QuadraticSetFunctions.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete degree-two expansion, retaining arbitrary constant and
linear coefficients. This is a finite identity, valid on every ground set. -/
theorem zeta_degree_two (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0) (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+∑ C∈S.powersetCard 2,g C := by
  let N:=max (S.card+1) 3
  let F : ℕ → ℝ := fun j => ∑ C∈S.powersetCard j,g C
  have hlarge : ∑ j∈range (S.card+1),F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_left _ _))
    intro j hj hsmall
    have hcard : S.card< j := by
      have hn : ¬j< S.card+1 := by simpa only [mem_range] using hsmall
      omega
    simp only [F,(powersetCard_eq_empty.mpr hcard),sum_empty]
  have hshort : ∑ j∈range 3,F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_right _ _))
    intro j hj hsmall
    have hthree : 3≤ j := by simpa only [mem_range,not_lt] using hsmall
    apply sum_eq_zero
    intro C hC
    exact hdegree C (by have hc:=(mem_powersetCard.mp hC).2; omega)
  unfold zeta
  rw [sum_powerset,hlarge,← hshort]
  simp only [F,sum_range_succ,sum_range_zero,zero_add,powersetCard_zero,
    sum_singleton,powersetCard_one,sum_map] <;> rfl

/-- The actual interaction graph can omit every pair whose coefficient is
zero; no additional equality is imposed on the linear or constant terms. -/
theorem zeta_degree_two_on_graph (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+
      ∑ e∈G.edgeFinset,if e.toFinset⊆S then g e.toFinset else 0 := by
  rw [zeta_degree_two g hdegree S]
  congr 1
  have hp : (edgeFamily G).filter (fun C => C⊆S)⊆S.powersetCard 2 := by
    intro C hC
    obtain ⟨hC,hCS⟩ := mem_filter.mp hC
    exact mem_powersetCard.mpr ⟨hCS,((mem_edgeFamily G C).mp hC).1⟩
  have he : (∑ C∈(edgeFamily G).filter (fun C => C⊆S),g C)=
      ∑ C∈S.powersetCard 2,g C := by
    apply sum_subset hp
    intro C hC hnot
    have hCS := (mem_powersetCard.mp hC).1
    apply hgraph C (mem_powersetCard.mp hC).2
    intro hedge
    exact hnot (mem_filter.mpr ⟨hedge,hCS⟩)
  rw [← he,sum_filter,sum_edgeFamily_eq]

def booleanSupport (x : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun v => x v=1)

@[simp] theorem mem_booleanSupport (x : V → ℝ) (v : V) :
    v∈booleanSupport x ↔ x v=1 := by
  classical
  simp [booleanSupport]

theorem zeta_eq_boolean_quadratic (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (x : V → ℝ) (hx : ∀ v,x v=0 ∨ x v=1) :
    zeta g (booleanSupport x)=ForestSigns.quadratic G (g ∅)
      (fun v => g {v}) (fun e => g e.toFinset) x := by
  classical
  rw [zeta_degree_two_on_graph G g hdegree hgraph]
  unfold ForestSigns.quadratic
  have hlinear : (∑ v∈booleanSupport x,g {v})=∑ v,g {v}*x v := by
    rw [booleanSupport,sum_filter]
    apply sum_congr rfl
    intro v hv
    rcases hx v with he | he <;> simp [he]
  have hquad : (∑ e∈G.edgeFinset,if e.toFinset⊆booleanSupport x then g e.toFinset else 0)=
      ∑ e∈G.edgeFinset,g e.toFinset*ForestSigns.edgeProduct x e := by
    apply sum_congr rfl
    intro e he
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq,ForestSigns.edgeProduct_pair]
    rcases hx a with ha | ha <;> rcases hx b with hb | hb <;>
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb]
  rw [hlinear,hquad]

end GraphicalZonotopes

end
end
end BundlePart71

section BundlePart72
/- Source: Papers/GraphicalZonotopes/ConditionalQuadratic.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CliqueSupported.clique_of_nonzero {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) : G.IsClique C := by
  intro u hu v hv huv
  by_contra hnot
  exact hC (hy.2.2 C u v hu hv huv hnot)

/-- Möbius coefficients of an elemental row, with its two endpoint variables
removed. The discarded coordinates are explicitly zero, not quotiented out. -/
def edgeCoefficients (y : SetFunction V) (u v : V) : SetFunction V := fun C =>
  if u∉C ∧ v∉C then y (insert u (insert v C)) else 0

theorem edgeCoefficients_degree_two {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠ v) (C : Finset V) (hC : 2< C.card) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hnonzero
    have hbound := hfour _ (hy.clique_of_nonzero hnonzero)
    rw [card_insert_of_notMem (by simp [huv,he.1]),card_insert_of_notMem he.2] at hbound
    omega
  · simp [edgeCoefficients,he]

theorem edgeCoefficients_graph {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {u v : V} (huv : u≠ v)
    (C : Finset V) (hC : C.card=2) (hnot : C∉edgeFamily (edgeLink G u v)) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hn
    have hcl := hy.clique_of_nonzero hn
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hC
    have hua : u≠ a := fun h => he.1 (by simp [h])
    have hub : u≠ b := fun h => he.1 (by simp [h])
    have hva : v≠ a := fun h => he.2 (by simp [h])
    have hvb : v≠ b := fun h => he.2 (by simp [h])
    apply hnot
    apply (pair_mem_edgeFamily (edgeLink G u v) hab).mpr
    exact ⟨hcl (by simp) (by simp) hab,
      hcl (by simp) (by simp) hua,hcl (by simp) (by simp) hva,
      hcl (by simp) (by simp) hub,hcl (by simp) (by simp) hvb⟩
  · simp [edgeCoefficients,he]

theorem zeta_erase_of_containing_zero (g : SetFunction V) (u : V)
    (hz : ∀ C : Finset V,u∈C → g C=0) (S : Finset V) :
    zeta g S=zeta g (S.erase u) := by
  classical
  symm
  apply sum_subset (powerset_mono.mpr (erase_subset _ _))
  intro C hC hnot
  apply hz C
  by_contra hu
  apply hnot
  apply mem_powerset.mpr
  intro v hv
  exact mem_erase.mpr ⟨fun he => hu (he ▸ hv),(mem_powerset.mp hC) hv⟩

theorem edgeCoefficients_zeta {y : SetFunction V} {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    zeta (edgeCoefficients y u v) S=delta (zeta y) u v S := by
  classical
  rw [delta_zeta huv hu hv]
  apply sum_bij (fun C _ => insert u (insert v C))
  · intro C hC
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset_insert _
      (insert_subset_insert _ (mem_powerset.mp hC))),by simp⟩
  · intro C hC D hD he
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    have huD : u∉D := notMem_mono (mem_powerset.mp hD) hu
    have hvD : v∉D := notMem_mono (mem_powerset.mp hD) hv
    have hh:=congrArg (fun A : Finset V => (A.erase u).erase v) he
    simpa [huv,huC,hvC,huD,hvD] using hh
  · intro D hD
    obtain ⟨hsub,huD,hvD⟩ := mem_filter.mp hD
    refine ⟨(D.erase u).erase v,?_,?_⟩
    · apply mem_powerset.mpr
      intro w hw
      have hwD := mem_of_mem_erase (mem_of_mem_erase hw)
      have hwu := ne_of_mem_erase (mem_of_mem_erase hw)
      have hwv := ne_of_mem_erase hw
      have hm := (mem_powerset.mp hsub) hwD
      simpa only [mem_insert,hwu,hwv,false_or] using hm
    · ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,huD,hvD]
  · intro C hC
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    simp [edgeCoefficients,huC,hvC]

/-- Every elemental row of four-clique-supported data is the literal
quadratic Boolean polynomial on the common-neighbor graph. -/
theorem edgeCoefficients_boolean_quadratic {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠ v) (x : V → ℝ) (hx : ∀ w,x w=0 ∨ x w=1) :
    ForestSigns.quadratic (edgeLink G u v) (edgeCoefficients y u v ∅)
      (fun w => edgeCoefficients y u v {w})
      (fun e => edgeCoefficients y u v e.toFinset) x=
      delta (zeta y) u v (((booleanSupport x).erase u).erase v) := by
  rw [← zeta_eq_boolean_quadratic (edgeLink G u v) (edgeCoefficients y u v)
    (edgeCoefficients_degree_two hy hfour huv) (edgeCoefficients_graph hy huv) x hx]
  rw [zeta_erase_of_containing_zero _ u (by
    intro C hC; simp [edgeCoefficients,hC])]
  rw [zeta_erase_of_containing_zero _ v (by
    intro C hC; simp [edgeCoefficients,hC])]
  exact edgeCoefficients_zeta huv (by simp) (by simp)

end GraphicalZonotopes

end
end
end BundlePart72

section BundlePart73
/- Source: Papers/GraphicalZonotopes/CliqueLinkEquivalence.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linkPair_excludes_endpoints {G : SimpleGraph V} {u v : V} {E : Finset V}
    (hE : E∈edgeFamily (edgeLink G u v)) : u∉E ∧ v∉E := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  exact ⟨by simp [G.ne_of_adj he.2.1,G.ne_of_adj he.2.2.2.1],
    by simp [G.ne_of_adj he.2.2.1,G.ne_of_adj he.2.2.2.2]⟩

theorem tetrahedron_of_linkPair {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {E : Finset V} (hE : E∈edgeFamily (edgeLink G u v)) :
    insert u (insert v E)∈tetrahedra G := by
  classical
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  have hua := G.ne_of_adj he.2.1
  have hub := G.ne_of_adj he.2.2.2.1
  have hva := G.ne_of_adj he.2.2.1
  have hvb := G.ne_of_adj he.2.2.2.2
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · simp [huv.ne,hua,hub,hva,hvb,hab]
  · intro x hx y hy hxy
    change x ∈ (insert u (insert v {a,b}) : Finset V) at hx
    change y ∈ (insert u (insert v {a,b}) : Finset V) at hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact False.elim (hxy rfl) | exact huv | exact huv.symm |
        exact he.1 | exact he.1.symm | exact he.2.1 | exact he.2.1.symm |
        exact he.2.2.1 | exact he.2.2.1.symm | exact he.2.2.2.1 |
        exact he.2.2.2.1.symm | exact he.2.2.2.2 | exact he.2.2.2.2.symm

theorem linkPair_of_tetrahedron {G : SimpleGraph V} {u v : V} (huv : u≠ v)
    {C : Finset V} (hC : C∈tetrahedra G) (huC : u∈C) (hvC : v∈C) :
    (C.erase u).erase v∈edgeFamily (edgeLink G u v) := by
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  apply (mem_edgeFamily _ _).mpr
  refine ⟨?_,?_⟩
  · rw [card_erase_of_mem (mem_erase.mpr ⟨huv.symm,hvC⟩),
      card_erase_of_mem huC,hc]
  · intro a ha b hb hab
    obtain ⟨hav,ha'⟩ := mem_erase.mp ha
    obtain ⟨hau,haC⟩ := mem_erase.mp ha'
    obtain ⟨hbv,hb'⟩ := mem_erase.mp hb
    obtain ⟨hbu,hbC⟩ := mem_erase.mp hb'
    exact ⟨hcl haC hbC hab,hcl huC haC hau.symm,hcl hvC haC hav.symm,
      hcl huC hbC hbu.symm,hcl hvC hbC hbv.symm⟩

def tetrahedraContaining (G : SimpleGraph V) (u v : V) : Finset (Finset V) := by
  classical
  exact (tetrahedra G).filter (fun C => u∈C ∧ v∈C)

/-- Every tetrahedron through an actual edge corresponds to exactly one
edge of its common-neighbor graph, with no omitted interaction or duplicate
coefficient. This is the coordinate dictionary used by the Boolean kernel
and lattice-oscillation arguments. -/
def tetrahedronLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    ↥(tetrahedraContaining G u v) ≃ ↥(edgeFamily (edgeLink G u v)) where
  toFun C := ⟨(C.1.erase u).erase v,linkPair_of_tetrahedron huv.ne
    (mem_filter.mp C.2).1 (mem_filter.mp C.2).2.1 (mem_filter.mp C.2).2.2⟩
  invFun E := ⟨insert u (insert v E.1),mem_filter.mpr
    ⟨tetrahedron_of_linkPair huv E.2,by simp,by simp⟩⟩
  left_inv C := by
    apply Subtype.ext
    have huC := (mem_filter.mp C.2).2.1
    have hvC := (mem_filter.mp C.2).2.2
    ext x
    by_cases hxu : x=u <;> by_cases hxv : x=v <;> simp [hxu,hxv,huC,hvC]
  right_inv E := by
    apply Subtype.ext
    obtain ⟨huE,hvE⟩ := linkPair_excludes_endpoints E.2
    simp [huv.ne,huE,hvE]

theorem tetrahedronLink_card (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    (tetrahedraContaining G u v).card=(edgeLink G u v).edgeFinset.card := by
  have he := Fintype.card_congr (tetrahedronLinkEquiv G huv)
  simp only [Fintype.card_coe] at he
  rw [he,edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

end GraphicalZonotopes

end
end
end BundlePart73

section BundlePart74
/- Source: Papers/GraphicalZonotopes/ThreeTreeEdgeCoordinates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ComplementPair.ne_val {C E : Finset V} (p : ComplementPair C E) :
    p.first.1≠ p.second.1 := fun he => p.ne (Subtype.ext he)

theorem ComplementPair.first_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.first.1∉E := by
  simpa only [p.erase_eq] using
    (show p.first.1 ∉ (C.erase p.first.1).erase p.second.1 from by simp)

theorem ComplementPair.second_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.second.1∉E := by
  simpa only [p.erase_eq] using
    (show p.second.1 ∉ (C.erase p.first.1).erase p.second.1 from notMem_erase _ _)

theorem ComplementPair.mem_complement_iff {C E : Finset V}
    (p : ComplementPair C E) (w : V) :
    w∈C ∧ w∉E ↔ w=p.first.1 ∨ w=p.second.1 := by
  rw [← mem_sdiff,← p.pair_eq_complement]
  simp only [mem_insert,mem_singleton]

theorem ComplementPair.erase_first {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.first.1=insert p.second.1 E := by
  simpa only [p.erase_eq] using
    (insert_erase (mem_erase.mpr ⟨p.ne_val.symm,p.second.2⟩)).symm

theorem ComplementPair.erase_second {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.second.1=insert p.first.1 E := by
  have he : (C.erase p.second.1).erase p.first.1 = E := by
    rw [erase_right_comm]
    exact p.erase_eq
  simpa only [he] using (insert_erase (mem_erase.mpr ⟨p.ne_val,p.first.2⟩)).symm

/-- The linear coefficient contributed by one tetrahedron to the
elemental row at its complementary pair. This is expressed on every
ambient vertex, with exact zeros off the two remaining vertices. -/
def pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
  else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second)
  else 0

theorem pairLinear_eq_zero_of_notMem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∉C.1.1) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠ p.first.1 := fun he => hw (he.symm ▸ p.first.2)
  have hb : w≠ p.second.1 := fun he => hw (he.symm ▸ p.second.2)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

theorem pairLinear_eq_zero_of_mem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∈E) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠ p.first.1 := fun he => p.first_notMem (he ▸ hw)
  have hb : w≠ p.second.1 := fun he => p.second_notMem (he ▸ hw)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

def pairTriangleIncidenceEquiv (G : SimpleGraph V) (E : Finset V) (w : V)
    (hT : insert w E∈triangles G) :
    AllIncidentClique G ⟨insert w E,hT⟩ ≃
      {C : IncidentPairClique G E // w∈C.1.1} where
  toFun C:=⟨⟨C.1,(subset_insert w E).trans C.2⟩,C.2 (mem_insert_self _ _)⟩
  invFun C:=⟨C.1.1,insert_subset_iff.mpr ⟨C.2,C.1.2⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem faceRow_eq_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G)
    (D : AllIncidentClique G ⟨insert w E,hT⟩) :
    realBit (faceRow G s ⟨insert w E,hT⟩ D ⟨w,mem_insert_self _ _⟩)=
      pairLinear G s E hE ((pairTriangleIncidenceEquiv G E w hT) D).1 w := by
  let C:=((pairTriangleIncidenceEquiv G E w hT) D).1
  let p:=complementPair G C.1 E hE C.2
  have hwC : w∈C.1.1:=D.2 (mem_insert_self _ _)
  change realBit ((s.clique C.1).row (faceMissing G C.1 ⟨insert w E,hT⟩ D.2) ⟨w,hwC⟩) =
    if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0
  rcases (p.mem_complement_iff w).mp ⟨hwC,hw⟩ with ha | hb
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.second := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.second.1
      rw [p.erase_second,ha]
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.first:=Subtype.ext ha
    rw [hm, if_pos ha]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.second j)) hwv
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.first := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.first.1
      rw [p.erase_first,hb]
    have hna : w≠ p.first.1 := by rw [hb]; exact p.ne_val.symm
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.second:=Subtype.ext hb
    rw [hm, if_neg hna, if_pos hb]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.first j)) hwv

/-- Every actual triangle column is exactly the sum of its contributions
from tetrahedra incident with a fixed edge of that triangle. -/
theorem column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G) :
    columnValue G s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩=
      ∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
  classical
  unfold columnValue
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        pairLinear G s E hE C.1 w :=
      Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT) _ _
        (faceRow_eq_pairLinear G s E hE w hw hT)
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => pairLinear G s E hE C w)).symm
    _=∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      exact pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩))

theorem coefficients_insert_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) :
    coefficients h s (insert w E)=
      -(∑ C : IncidentPairClique G E,pairLinear G s E hE C w) := by
  classical
  by_cases hT : insert w E∈triangles G
  · rw [coefficients_triangle h s hT,
      ← column_eq_triangleWeight h s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩,
      column_eq_sum_pairLinear G s E hE w hw hT]
  · have hzero : coefficients h s (insert w E)=0 := by
      by_contra hn
      have hcl:=(coefficients_cliqueSupported h s).clique_of_nonzero hn
      exact hT (mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],hcl⟩)
    rw [hzero]
    symm
    rw [neg_eq_zero]
    apply sum_eq_zero
    intro C hC
    apply pairLinear_eq_zero_of_notMem G s E hE C w
    intro hwC
    apply hT
    refine mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],?_⟩
    have hs : insert w E ⊆ C.1.1 := insert_subset_iff.mpr ⟨hwC,C.2⟩
    intro a ha b hb hab
    exact (mem_filter.mp C.1.2).2.2 (hs ha) (hs hb) hab

theorem pairLinear_sum (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) :
    (∑ w,pairLinear G s E hE C w*x w)=
      let p:=complementPair G C.1 E hE C.2
      realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
      realBit ((s.clique C.1).row p.first p.second)*x p.second.1 := by
  let p:=complementPair G C.1 E hE C.2
  calc
    _=pairLinear G s E hE C p.first.1*x p.first.1+
        pairLinear G s E hE C p.second.1*x p.second.1 := by
      apply sum_eq_add_of_mem p.first.1 p.second.1 (mem_univ _) (mem_univ _) p.ne_val
      intro w hw hne
      dsimp only [p] at hne
      simp only [pairLinear,hne.1,hne.2,ite_false,zero_mul]
    _=_ := by
      have hp := p.ne_val.symm
      dsimp only [p] at hp ⊢
      simp only [pairLinear,ite_true,hp,ite_false]

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart74

section BundlePart75
/- Source: Papers/GraphicalZonotopes/ThreeTreeFactorization.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFinsetFamilyEquiv (G : SimpleGraph V) : ↥G.edgeFinset ≃ ↥(edgeFamily G) :=
  Equiv.ofBijective (fun e => ⟨e.1.toFinset,by
    rw [edgeFamily_eq_image_edgeFinset]
    exact mem_image.mpr ⟨e.1,e.2,rfl⟩⟩) (by
    constructor
    · intro e f hef
      exact Subtype.ext (sym2_toFinset_injective (congrArg Subtype.val hef))
    · intro E
      have hE:=E.2
      simp only [edgeFamily_eq_image_edgeFinset] at hE
      obtain ⟨e,he,heE⟩:=mem_image.mp hE
      exact ⟨⟨e,he⟩,Subtype.ext heE⟩)

def incidentPairContainingEquiv (G : SimpleGraph V) (u v : V) :
    IncidentPairClique G {u,v} ≃ ↥(tetrahedraContaining G u v) where
  toFun C:=⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2 (by simp),C.2 (by simp)⟩⟩
  invFun C:=⟨⟨C.1,(mem_filter.mp C.2).1⟩,by
    simpa only [insert_subset_iff,singleton_subset_iff] using (mem_filter.mp C.2).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- The summation over actual incident tetrahedra is exactly the summation
over actual edges of the common-neighbor graph. -/
def pairLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    IncidentPairClique G {u,v} ≃ ↥(edgeLink G u v).edgeFinset :=
  ((incidentPairContainingEquiv G u v).trans (tetrahedronLinkEquiv G huv)).trans
    (edgeFinsetFamilyEquiv (edgeLink G u v)).symm

theorem pairLinkEquiv_toFinset (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    ((pairLinkEquiv G huv C).1).toFinset=(C.1.1.erase u).erase v := by
  exact congrArg Subtype.val
    ((edgeFinsetFamilyEquiv (edgeLink G u v)).apply_symm_apply
      ((tetrahedronLinkEquiv G huv) ((incidentPairContainingEquiv G u v) C)))

theorem pairLinkEquiv_eq (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      s(p.first.1,p.second.1) := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  apply sym2_toFinset_injective
  rw [pairLinkEquiv_toFinset,Sym2.toFinset_mk_eq,p.pair_eq_complement]
  ext w
  simp only [mem_erase,mem_sdiff,mem_insert,mem_singleton,not_or]
  tauto

theorem edgeCoefficients_constant {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    edgeCoefficients (coefficients h s) u v ∅=
      ∑ C : IncidentPairClique G {u,v},
        ((complementPair G C.1 {u,v} (by simp [huv.ne]) C.2).maximum
          (s.clique C.1).row : ℝ) := by
  rw [edgeCoefficients,if_pos (by simp)]
  simp only [insert_empty_eq]
  rw [coefficients_pair h s ((pair_mem_edgeFamily G huv.ne).mpr huv)]
  simp only [pairWeight,Int.cast_sum]

theorem edgeCoefficients_linear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (w : V) :
    edgeCoefficients (coefficients h s) u v {w}=
      -(∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w) := by
  classical
  by_cases hw : w∈({u,v} : Finset V)
  · have hs : ∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w=0 := by
      exact sum_eq_zero (fun C _ => pairLinear_eq_zero_of_mem G s _ _ C w hw)
    rw [hs,neg_zero]
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [edgeCoefficients]
  · have hwu : w≠ u := fun he => hw (by simp [he])
    have hwv : w≠ v := fun he => hw (by simp [he])
    rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])]
    have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
      ext a
      simp only [mem_insert,mem_singleton]
      tauto
    rw [he]
    exact coefficients_insert_pair h s _ (by simp [huv.ne]) w hw

theorem edgeCoefficients_quadratic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (e : ↥(edgeLink G u v).edgeFinset) :
    edgeCoefficients (coefficients h s) u v e.1.toFinset=1 := by
  have hE : e.1.toFinset∈edgeFamily (edgeLink G u v):=
    ((edgeFinsetFamilyEquiv (edgeLink G u v)) e).2
  obtain ⟨hu,hv⟩:=linkPair_excludes_endpoints hE
  rw [edgeCoefficients,if_pos ⟨hu,hv⟩]
  exact coefficients_tetrahedron h s (tetrahedron_of_linkPair huv hE)

def pairFactor (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  (p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*x p.second.1-
    realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
    x p.first.1*x p.second.1

/-- The exact polynomial identity, before restricting coordinates to the
Boolean cube. Its constant, every ambient linear coefficient, and every
quadratic interaction are proved from the actual Möbius vector. -/
theorem quadratic_eq_sum_pairFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → ℝ) :
    ForestSigns.quadratic (edgeLink G u v)
      (edgeCoefficients (coefficients h s) u v ∅)
      (fun w => edgeCoefficients (coefficients h s) u v {w})
      (fun e => edgeCoefficients (coefficients h s) u v e.toFinset) x=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C x := by
  classical
  let pc : (C : IncidentPairClique G {u,v}) → ComplementPair C.1.1 {u,v}:=
    fun C => complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hlin : (∑ w,edgeCoefficients (coefficients h s) u v {w}*x w)=
      -(∑ C : IncidentPairClique G {u,v},
        (realBit ((s.clique C.1).row (pc C).second (pc C).first)*x (pc C).first.1+
        realBit ((s.clique C.1).row (pc C).first (pc C).second)*x (pc C).second.1)) := by
    simp_rw [edgeCoefficients_linear h s huv,neg_mul,sum_mul]
    rw [sum_neg_distrib,sum_comm]
    simp_rw [pairLinear_sum]
    rfl
  have hquad :
      (∑ e∈(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.toFinset*ForestSigns.edgeProduct x e)=
      ∑ C : IncidentPairClique G {u,v},x (pc C).first.1*x (pc C).second.1 := by
    rw [← sum_coe_sort]
    have hw : ∀ e : ↥(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.1.toFinset=1:=
      edgeCoefficients_quadratic h s huv
    simp_rw [hw,one_mul]
    symm
    apply Fintype.sum_equiv (pairLinkEquiv G huv)
    intro C
    rw [pairLinkEquiv_eq,ForestSigns.edgeProduct_pair]
  unfold ForestSigns.quadratic
  rw [edgeCoefficients_constant h s huv,hlin,hquad]
  simp only [pairFactor]
  rw [← sub_eq_add_neg,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  dsimp only [pc]
  ring

theorem pairFactor_zero_or_one (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → Bool) :
    pairFactor G s E hE C (fun w => realBit (x w))=0 ∨
      pairFactor G s E hE C (fun w => realBit (x w))=1 := by
  let p:=complementPair G C.1 E hE C.2
  change ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0) ∨
    ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=1)
  unfold ComplementPair.maximum
  cases (s.clique C.1).row p.first p.second <;>
    cases (s.clique C.1).row p.second p.first <;>
    cases x p.first.1 <;> cases x p.second.1 <;>
    norm_num [realBit,RootedResponse.integerBit]

/-- Every elemental slack is the literal sum of the Boolean local factors.
Endpoint erasure only expresses that a conditioning set omits those endpoints. -/
theorem elemental_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ∑ C : IncidentPairClique G {u,v},
        pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w)) := by
  unfold setFunction
  rw [← edgeCoefficients_boolean_quadratic (coefficients_cliqueSupported h s)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit])]
  exact quadratic_eq_sum_pairFactor h s huv _

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart75

section BundlePart76
/- Source: Papers/GraphicalZonotopes/ThreeTreeSharedEdges.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tetrahedra_mono {G H : SimpleGraph V} (h : G≤ H) :
    tetrahedra G⊆tetrahedra H := by
  classical
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  exact mem_filter.mpr ⟨mem_univ _,hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

theorem triangleMultiplicity_mono {G H : SimpleGraph V} (h : G≤ H) (T : Finset V) :
    triangleMultiplicity G T≤ triangleMultiplicity H T := by
  classical
  apply card_le_card
  intro C hC
  obtain ⟨hC,hTC⟩ := mem_filter.mp hC
  exact mem_filter.mpr ⟨tetrahedra_mono h hC,hTC⟩

theorem internalTriangles_mono {G H : SimpleGraph V} (h : G≤ H) :
    internalTriangles G⊆internalTriangles H := by
  intro T hT
  obtain ⟨hT,hcount⟩ := mem_internalTriangles.mp hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_internalTriangles.mpr
    ⟨mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩,
      hcount.trans (triangleMultiplicity_mono h T)⟩

/-- A running-intersection consequence for all actual tetrahedra: if two
distinct cliques contain a set E, the first clique has a shared triangular
face containing E. In particular, an edge contained in several tetrahedra
meets an internal face at every tetrahedron containing it. -/
theorem ThreeTreeOn.shared_face_containing {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D E : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠ D)
    (hEC : E⊆C) (hED : E⊆D) :
    ∃ T∈internalTriangles G,E⊆T ∧ T⊆C := by
  classical
  induction h generalizing C D E with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    exact False.elim (hCD (hC.trans hD.symm))
  | @attach S G h u hu A hA hAS hcA ih =>
    let H := G⊔attachmentStar u A
    have hmono : G≤ H := le_sup_left
    obtain ⟨K,hK,hAK⟩ := h.triangle_extends hA hcA
    have hnew : insert u A∈tetrahedra H := by
      rw [tetrahedra_after_attachment h hu hA hAS hcA]
      exact mem_insert_self _ _
    have hnewK : insert u A≠ K := by
      intro he
      apply attached_tetrahedron_not_old h hu (T := A)
      simpa only [he] using hK
    have hshared : A∈internalTriangles H := internal_triangle_of_shared hnew
      (tetrahedra_mono hmono hK) hnewK hA (subset_insert _ _) hAK
    have hav : ∀ L∈tetrahedra G,u∉L := by
      intro L hL hum
      have hc := (mem_filter.mp hL).2
      exact hu (h.clique_subset_active (by omega) hc.2 hum)
    have hsubsetA : ∀ L∈tetrahedra G,E⊆L → E⊆insert u A → E⊆A := by
      intro L hL hEL hEN v hv
      rcases mem_insert.mp (hEN hv) with he | hvA
      · exact False.elim (hav L hL (he ▸ hEL hv))
      · exact hvA
    rw [tetrahedra_after_attachment h hu hA hAS hcA] at hC hD
    rcases mem_insert.mp hC with hC | hC
    · subst C
      rcases mem_insert.mp hD with hD | hD
      · exact False.elim (hCD hD.symm)
      · exact ⟨A,hshared,hsubsetA D hD hED hEC,subset_insert _ _⟩
    · rcases mem_insert.mp hD with hD | hD
      · subst D
        have hEA : E⊆A := hsubsetA C hC hEC hED
        by_cases hCK : C=K
        · exact ⟨A,hshared,hEA,by simpa only [hCK] using hAK⟩
        · obtain ⟨T,hT,hET,hTC⟩ := ih hC hK hCK hEC (hEA.trans hAK)
          exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩
      · obtain ⟨T,hT,hET,hTC⟩ := ih hC hD hCD hEC hED
        exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩

end GraphicalZonotopes

end
end
end BundlePart76

section BundlePart77
/- Source: Papers/GraphicalZonotopes/ForestZeroKernel.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero of the sum of the nonnegative factors `xy` and
`(1-x)(1-y)`: every edge has an endpoint equal to its specified bit. -/
def CoversLabels (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : Prop :=
  ∀ u v,G.Adj u v → x u=b s(u,v) ∨ x v=b s(u,v)

def bitSign (b : Bool) : ℝ := if b then 1 else -1

def signBit (s : ℝ) : Bool := decide (s=1)

theorem bitSign_isSign (b : Bool) : ForestSigns.IsSign (bitSign b) := by
  cases b <;> simp [bitSign,ForestSigns.IsSign]

@[simp] theorem signBit_bitSign (b : Bool) : signBit (bitSign b)=b := by
  cases b <;> norm_num [signBit,bitSign]

theorem signBit_covers_of_neg_product {s t : ℝ}
    (hs : ForestSigns.IsSign s) (ht : ForestSigns.IsSign t)
    (hst : s*t=-1) (b : Bool) : signBit s=b ∨ signBit t=b := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    cases b
  all_goals try (norm_num [signBit] at hst)
  all_goals norm_num [signBit]

/-- Opposite signs on every forest edge give a zero independently of the
choice of edge labels. Empty and disconnected forests are included. -/
theorem exists_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,CoversLabels G b x := by
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG (fun _ _ => -1)
    (by intro u v huv; exact Or.inr rfl) (by intro u v huv; rfl)
  refine ⟨fun v => signBit (σ v),?_⟩
  intro u v huv
  exact signBit_covers_of_neg_product (hσ u) (hσ v) (hσe u v huv) _

/-- For every vertex of a forest, the common zero locus contains two
points differing at that vertex alone. In particular the zero locus spans
the full affine Boolean coordinate space; this does not follow merely from
the existence of a single zero. -/
theorem exists_flippable_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (r : V) :
    ∃ x : V → Bool,∀ a : Bool,CoversLabels G b (Function.update x r a) := by
  let ρ : V → V → ℝ := fun u v =>
    if u=r ∨ v=r then bitSign (b s(u,v)) else -1
  have hρ : ∀ u v,G.Adj u v → ForestSigns.IsSign (ρ u v) := by
    intro u v huv
    dsimp [ρ]
    split
    · exact bitSign_isSign _
    · exact Or.inr rfl
  have hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u := by
    intro u v huv
    simp only [ρ,or_comm,Sym2.eq_swap]
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG ρ hρ hρsym
  let τ : V → ℝ := fun v => σ r*σ v
  have hτ : ∀ v,ForestSigns.IsSign (τ v) := fun v => (hσ r).mul (hσ v)
  have hneighbor : ∀ v,G.Adj r v → signBit (τ v)=b s(r,v) := by
    intro v hrv
    have he := hσe r v hrv
    have he' : τ v=bitSign (b s(r,v)) := by
      dsimp only [ρ] at he
      rw [if_pos (Or.inl rfl)] at he
      simpa only [τ] using he
    rw [he',signBit_bitSign]
  have hoff : ∀ u v,G.Adj u v → u≠ r → v≠ r →
      signBit (τ u)=b s(u,v) ∨ signBit (τ v)=b s(u,v) := by
    intro u v huv hur hvr
    have hprod : τ u*τ v=-1 := by
      calc
        τ u*τ v=(σ r)^2*(σ u*σ v) := by dsimp [τ]; ring
        _=-1 := by rw [(hσ r).sq,hσe u v huv]; simp [ρ,hur,hvr]
    exact signBit_covers_of_neg_product (hτ u) (hτ v) hprod _
  refine ⟨fun v => signBit (τ v),?_⟩
  intro a u v huv
  by_cases hur : u=r
  · subst u
    have hvr : v≠ r := huv.ne.symm
    exact Or.inr (by simpa only [Function.update_of_ne hvr] using hneighbor v huv)
  · by_cases hvr : v=r
    · subst v
      exact Or.inl (by
        simpa only [Function.update_of_ne hur,Sym2.eq_swap] using hneighbor u huv.symm)
    · simpa only [Function.update_of_ne hur,Function.update_of_ne hvr] using
        hoff u v huv hur hvr

def affineValue (c : ℝ) (l : V → ℝ) (x : V → Bool) : ℝ :=
  c+∑ v,l v*RootedResponse.realBit (x v)

theorem affineValue_update_difference (c : ℝ) (l : V → ℝ)
    (x : V → Bool) (r : V) :
    affineValue c l (Function.update x r true)-
      affineValue c l (Function.update x r false)=l r := by
  calc
    affineValue c l (Function.update x r true)-
        affineValue c l (Function.update x r false)=
        ∑ v,(l v*RootedResponse.realBit ((Function.update x r true) v)-
          l v*RootedResponse.realBit ((Function.update x r false) v)) := by
      rw [sum_sub_distrib]
      unfold affineValue
      ring
    _=l r := by
      rw [sum_eq_single r]
      · simp [RootedResponse.realBit]
      · intro v hv hvr
        simp only [Function.update_of_ne hvr,sub_self]
      · intro hr
        exact False.elim (hr (mem_univ r))

/-- No nonzero affine functional vanishes on the entire zero locus of a
sum of labelled-edge factors on a finite forest. Together with subtraction
of the known quadratic coefficients, this identifies the full quadratic
tight kernel, rather than only a selected set of zero rows. -/
theorem affine_vanishing_iff (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) :
    (∀ x,CoversLabels G b x → affineValue c l x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  constructor
  · intro hzero
    have hl : ∀ r,l r=0 := by
      intro r
      obtain ⟨x,hx⟩ := exists_flippable_cover G hG b r
      have hfalse := hzero _ (hx false)
      have htrue := hzero _ (hx true)
      have hd := affineValue_update_difference c l x r
      rw [hfalse,htrue] at hd
      linarith
    obtain ⟨x,hx⟩ := exists_cover G hG b
    have hc := hzero x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero] at hc
    exact ⟨hc,hl⟩
  · rintro ⟨rfl,hl⟩ x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero]

end ForestZeros
end GraphicalZonotopes

end
end
end BundlePart77

section BundlePart78
/- Source: Papers/GraphicalZonotopes/ForestFactorKernel.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each edge has quadratic coefficient one. Its lower coefficients are
fixed by its bit: `xy` for zero, `(1-x)(1-y)` for one. -/
def edgeFactor (b : Sym2 V → Bool) (x : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    if b s(u,v) then
      (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
    else RootedResponse.realBit (x u)*RootedResponse.realBit (x v),by
      intro u v
      simp only [Sym2.eq_swap,mul_comm]⟩

@[simp] theorem edgeFactor_pair (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=
      if b s(u,v) then
        (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
      else RootedResponse.realBit (x u)*RootedResponse.realBit (x v) := rfl

theorem edgeFactor_zero_or_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e=0 ∨ edgeFactor b x e=1 := by
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

theorem edgeFactor_nonneg (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    0≤ edgeFactor b x e := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_le_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e≤1 := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_pair_eq_zero (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=0 ↔ x u=b s(u,v) ∨ x v=b s(u,v) := by
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

def totalFactor (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : ℝ :=
  ∑ e∈G.edgeFinset,edgeFactor b x e

theorem totalFactor_nonneg (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    0≤ totalFactor G b x := by
  exact sum_nonneg (fun e he => edgeFactor_nonneg b x e)

theorem totalFactor_le_card (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    totalFactor G b x≤(G.edgeFinset.card : ℝ) := by
  calc
    totalFactor G b x≤∑ e∈G.edgeFinset,(1:ℝ) :=
      sum_le_sum (fun e he => edgeFactor_le_one b x e)
    _=(G.edgeFinset.card : ℝ) := by simp

theorem totalFactor_eq_zero_iff (G : SimpleGraph V) (b : Sym2 V → Bool)
    (x : V → Bool) : totalFactor G b x=0 ↔ CoversLabels G b x := by
  rw [totalFactor,sum_eq_zero_iff_of_nonneg (fun e he => edgeFactor_nonneg b x e)]
  constructor
  · intro h u v huv
    exact (edgeFactor_pair_eq_zero b x u v).mp (h _ (G.mem_edgeFinset.mpr huv))
  · intro h e he
    obtain ⟨u,v⟩ := e
    exact (edgeFactor_pair_eq_zero b x u v).mpr (h u v (G.mem_edgeFinset.mp he))

theorem totalFactor_has_zero (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,totalFactor G b x=0 := by
  obtain ⟨x,hx⟩ := exists_cover G hG b
  exact ⟨x,(totalFactor_eq_zero_iff G b x).mpr hx⟩

/-- An actual nonempty interaction graph has a strictly positive slack.
There is no cancellation argument here: one selected factor is one and all
other factors are nonnegative. -/
theorem totalFactor_has_positive (G : SimpleGraph V) (hG : G≠⊥)
    (b : Sym2 V → Bool) : ∃ x,0< totalFactor G b x := by
  obtain ⟨e,he⟩ := G.edgeFinset_nonempty.mpr hG
  let x : V → Bool := fun _ => !(b e)
  have hone : edgeFactor b x e=1 := by
    obtain ⟨u,v⟩ := e
    rw [edgeFactor_pair]
    dsimp [x]
    cases b s(u,v) <;> norm_num [RootedResponse.realBit]
  have hle : edgeFactor b x e≤ totalFactor G b x :=
    single_le_sum (fun f hf => edgeFactor_nonneg b x f) he
  refine ⟨x,?_⟩
  rw [hone] at hle
  linarith

/-- These are unrestricted real quadratic variations written in the
edge-factor basis plus their affine remainder. The coefficients on distinct
edges remain completely independent. -/
def factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) : ℝ :=
  affineValue c l x+∑ e∈G.edgeFinset,w e*edgeFactor b x e

theorem weightedFactors_zero (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) (hx : CoversLabels G b x) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=0 := by
  apply sum_eq_zero
  intro e he
  obtain ⟨u,v⟩ := e
  rw [(edgeFactor_pair_eq_zero b x u v).mpr (hx u v (G.mem_edgeFinset.mp he)),mul_zero]

/-- The entire tight kernel of the positive unit-weight forest polynomial:
the arbitrary quadratic edge coefficients survive, and every affine
remainder vanishes. The equivalence uses every zero row of the actual
polynomial and has no rank or private-kernel assumption. -/
theorem factor_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 → factorCoordinates G b c l w x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  rw [← affine_vanishing_iff G hG b c l]
  constructor
  · intro h x hx
    have hz := h x ((totalFactor_eq_zero_iff G b x).mpr hx)
    simpa only [factorCoordinates,weightedFactors_zero G b w x hx,add_zero] using hz
  · intro h x hx
    have hx' := (totalFactor_eq_zero_iff G b x).mp hx
    simp only [factorCoordinates,h x hx',weightedFactors_zero G b w x hx',add_zero]

def endpointSum (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u+x v,fun _ _ => add_comm _ _⟩

@[simp] theorem endpointSum_pair (x : V → ℝ) (u v : V) :
    endpointSum x s(u,v)=x u+x v := rfl

def constantWeight (G : SimpleGraph V) (b : Sym2 V → Bool) (w : Sym2 V → ℝ) : ℝ :=
  ∑ e∈G.edgeFinset,if b e then w e else 0

def incidentWeight (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e∈G.edgeFinset,if b e ∧ v∈e.toFinset then w e else 0

theorem incidentWeight_sum (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → ℝ) :
    (∑ v,incidentWeight G b w v*x v)=
      ∑ e∈G.edgeFinset,if b e then w e*endpointSum x e else 0 := by
  simp_rw [incidentWeight,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  have huv : u≠ v := (G.mem_edgeFinset.mp he).ne
  cases hb : b s(u,v)
  · simp [hb]
  · simp only [hb,Bool.coe_true,true_and,ite_true,ite_mul,zero_mul]
    rw [sum_ite_mem_eq]
    simp [Sym2.toFinset_mk_eq, huv, endpointSum_pair, mul_add]

theorem weightedFactors_expansion (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=
      (∑ e∈G.edgeFinset,w e*ForestSigns.edgeProduct
        (fun v => RootedResponse.realBit (x v)) e)+constantWeight G b w-
        ∑ v,incidentWeight G b w v*RootedResponse.realBit (x v) := by
  rw [incidentWeight_sum]
  unfold constantWeight
  rw [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair,ForestSigns.edgeProduct_pair,endpointSum_pair]
  cases b s(u,v) <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Every ordinary quadratic polynomial on this graph has an exact
factor-coordinate representation. Thus the preceding kernel theorem loses
no constant, linear, or quadratic variations. -/
theorem quadratic_eq_factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) :
    ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=
      factorCoordinates G b (c-constantWeight G b w)
        (fun v => l v+incidentWeight G b w v) w x := by
  unfold factorCoordinates affineValue ForestSigns.quadratic
  rw [weightedFactors_expansion]
  simp_rw [add_mul]
  rw [sum_add_distrib]
  ring

/-- Full ordinary-coefficient form of the forest tight-kernel theorem.
All coefficients are arbitrary real numbers, and all Boolean zero rows of
the actual unit-weight polynomial are retained. -/
theorem ordinary_quadratic_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 →
      ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=0) ↔
      c=constantWeight G b w ∧ ∀ v,l v= -incidentWeight G b w v := by
  simp_rw [quadratic_eq_factorCoordinates G b c l w]
  rw [factor_tight_kernel G hG b]
  constructor
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by have hv := hl v; linarith⟩
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by rw [hl v]; ring⟩

end ForestZeros
end GraphicalZonotopes

end
end
end BundlePart78

section BundlePart79
/- Source: Papers/GraphicalZonotopes/ThreeTreeGoodEdges.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A good edge is one contained in at least two actual tetrahedra. -/
def GoodPair (G : SimpleGraph V) (E : Finset V) : Prop :=
  2≤ Fintype.card (IncidentPairClique G E)

theorem goodPair_faces_agree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (hg : GoodPair G E) (C : IncidentPairClique G E) :
    let p:=complementPair G C.1 E hE C.2
    (s.clique C.1).row p.first p.second=(s.clique C.1).row p.second p.first := by
  classical
  let p:=complementPair G C.1 E hE C.2
  have hc : 1<(univ : Finset (IncidentPairClique G E)).card := by
    simpa only [card_univ] using (show 1< Fintype.card (IncidentPairClique G E) by
      exact lt_of_lt_of_le (by decide : 1<2) hg)
  obtain ⟨D,hD,hDC⟩:=exists_mem_ne hc C
  have hCD : C.1.1≠ D.1.1 := by
    intro he
    exact hDC (Subtype.ext (Subtype.ext he.symm))
  obtain ⟨T,hT,hET,hTC⟩:=h.shared_face_containing C.1.2 D.1.2 hCD C.2 D.2
  have ht3:=(mem_triangles.mp (mem_internalTriangles.mp hT).1).1
  obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp C.1.2).2.1 ht3 hTC
  have hrT : r.1∉T := by rw [← hr]; exact notMem_erase _ _
  have hrE : r.1∉E:=fun he => hrT (hET he)
  have hi : C.1.1.erase p.first.1∈internalTriangles G ∨
      C.1.1.erase p.second.1∈internalTriangles G := by
    rcases (p.mem_complement_iff r.1).mp ⟨r.2,hrE⟩ with he | he
    · left
      rw [← he,hr]
      exact hT
    · right
      rw [← he,hr]
      exact hT
  exact (s.clique C.1).agree p.first p.second p.ne hi

def linkBit (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (e : Sym2 V) : Bool :=
  if he : e∈(edgeLink G u v).edgeFinset then
    let C:=(pairLinkEquiv G huv).symm ⟨e,he⟩
    let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
    (s.clique C.1).row p.first p.second
  else false

theorem linkBit_at_clique (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (C : IncidentPairClique G {u,v}) :
    linkBit G s huv (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      (s.clique C.1).row p.first p.second := by
  simp only [linkBit,dif_pos (pairLinkEquiv G huv C).2]
  let F : IncidentPairClique G {u,v} → Bool := fun D =>
    let p:=complementPair G D.1 {u,v} (by simp [huv.ne]) D.2
    (s.clique D.1).row p.first p.second
  change F ((pairLinkEquiv G huv).symm ((pairLinkEquiv G huv) C)) = F C
  rw [Equiv.symm_apply_apply]

theorem pairFactor_eq_edgeFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (C : IncidentPairClique G {u,v}) (x : V → Bool) :
    pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w))=
      ForestZeros.edgeFactor (linkBit G s huv) x (pairLinkEquiv G huv C).1 := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have he:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hb:=linkBit_at_clique G s huv C
  rw [pairLinkEquiv_eq] at hb ⊢
  rw [ForestZeros.edgeFactor_pair,hb]
  change ((p.maximum (s.clique C.1).row : ℤ) : ℝ)-
      realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
      realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
      realBit (x p.first.1)*realBit (x p.second.1)=
      if (s.clique C.1).row p.first p.second then
        (1-realBit (x p.first.1))*(1-realBit (x p.second.1))
      else realBit (x p.first.1)*realBit (x p.second.1)
  unfold ComplementPair.maximum
  rw [← he]
  cases (s.clique C.1).row p.first p.second <;>
    cases x p.first.1 <;> cases x p.second.1 <;> norm_num [realBit,RootedResponse.integerBit]

/-- For a good edge the constructed elemental row is exactly the
positive unit-weight forest polynomial. This identifies its entire zero
locus, including every ambient Boolean coordinate. -/
theorem elemental_good_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ForestZeros.totalFactor (edgeLink G u v) (linkBit G s huv) x := by
  rw [elemental_factorization h s huv x]
  simp_rw [pairFactor_eq_edgeFactor h s huv hg]
  unfold ForestZeros.totalFactor
  conv_rhs => rw [← sum_coe_sort]
  exact (pairLinkEquiv G huv).sum_comp
    (fun e => ForestZeros.edgeFactor (linkBit G s huv) x e.1)

def TightVariation (z f : SetFunction V) : Prop :=
  ∀ u v,u≠ v → ∀ A,u∉A → v∉A → delta z u v A=0 → delta f u v A=0

theorem tightVariation_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    CliqueSupported G (mobius f) := by
  apply (mobius_cliqueSupported_iff G f).mpr
  refine ⟨hn,?_⟩
  intro u v huv hnon A hu hv
  exact hf u v huv A hu hv ((setFunction_normalized_graphical h s).2 u v huv hnon A hu hv)

/-- A complete ordinary-coefficient kernel equation for each good edge.
No scalar relation is assumed for the tetrahedral coefficients of the
variation; they remain arbitrary real numbers in the displayed sums. -/
theorem good_edge_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {u v : V} (huv : G.Adj u v) (hg : GoodPair G {u,v}) :
    edgeCoefficients (mobius f) u v ∅=
      ForestZeros.constantWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) ∧
    ∀ w,edgeCoefficients (mobius f) u v {w}=
      -ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) w := by
  apply (ForestZeros.ordinary_quadratic_tight_kernel (edgeLink G u v)
    (h.edgeLink_acyclic huv) (linkBit G s huv) _ _ _).mp
  intro x hx
  rw [edgeCoefficients_boolean_quadratic (tightVariation_cliqueSupported h s hn hf)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit]),zeta_mobius]
  apply hf u v huv.ne _ (by simp) (by simp)
  rw [elemental_good_factorization h s huv hg x]
  exact hx

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart79
