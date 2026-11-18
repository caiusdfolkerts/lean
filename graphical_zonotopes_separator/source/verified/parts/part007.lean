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

public import verified.parts.part006
import all verified.parts.part006

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart80
/- Source: Papers/GraphicalZonotopes/ThreeTreeKernelColumns.lean -/




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

theorem weighted_column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (lam : ↥(tetrahedra G) → ℝ) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) (T : Finset V) (hT : T∈triangles G)
    (he : T=insert w E) (hwT : w∈T) :
    (∑ C : AllIncidentClique G ⟨T,hT⟩,
      lam C.1*realBit (faceRow G s ⟨T,hT⟩ C ⟨w,hwT⟩))=
      ∑ C : IncidentPairClique G E,lam C.1*pairLinear G s E hE C w := by
  classical
  subst T
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        lam C.1.1*pairLinear G s E hE C.1 w := by
      apply Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT)
      intro C
      rw [faceRow_eq_pairLinear G s E hE w hw hT C]
      rfl
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        lam C.1*pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => lam C.1*pairLinear G s E hE C w)).symm
    _=_ := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      rw [pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩)),mul_zero]

theorem edgeCoefficients_at_clique (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (y : SetFunction V) (C : IncidentPairClique G {u,v}) :
    edgeCoefficients y u v ((pairLinkEquiv G huv C).1).toFinset=y C.1.1 := by
  rw [pairLinkEquiv_toFinset,edgeCoefficients,if_pos (by simp)]
  have hu : u∈C.1.1:=C.2 (by simp)
  have hv : v∈C.1.1:=C.2 (by simp)
  have he : insert u (insert v ((C.1.1.erase u).erase v))=C.1.1 := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,hu,hv]
  rw [he]

/-- The forest-kernel linear coefficient is the actual weighted sum of
the incident tetrahedron face bits, with arbitrary real tetrahedron weights. -/
theorem incidentWeight_eq_pairLinear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (y : SetFunction V) (w : V) :
    ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
      (fun e => edgeCoefficients y u v e.toFinset) w=
      ∑ C : IncidentPairClique G {u,v},y C.1.1*
        pairLinear G s {u,v} (by simp [huv.ne]) C w := by
  classical
  unfold ForestZeros.incidentWeight
  rw [← sum_coe_sort]
  symm
  apply Fintype.sum_equiv (pairLinkEquiv G huv)
  intro C
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hagree:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hbit:=linkBit_at_clique G s huv C
  dsimp only
  rw [edgeCoefficients_at_clique G huv y C,hbit,pairLinkEquiv_eq,Sym2.toFinset_mk_eq]
  change y C.1.1*(if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0)=
      if (s.clique C.1).row p.first p.second = true ∧ w ∈ ({p.first.1,p.second.1} : Finset V)
      then y C.1.1 else 0
  change (s.clique C.1).row p.first p.second = (s.clique C.1).row p.second p.first at hagree
  rw [← hagree]
  by_cases hwa : w=p.first.1 <;> by_cases hwb : w=p.second.1 <;>
    cases (s.clique C.1).row p.first p.second <;>
    simp [hwa,hwb,realBit]

theorem good_pair_linear_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (E : Finset V) (hE : E∈edgeFamily G) (hg : GoodPair G E)
    (w : V) (hw : w∉E) :
    mobius f (insert w E)=
      -(∑ C : IncidentPairClique G E,mobius f C.1.1*
        pairLinear G s E ((mem_edgeFamily G E).mp hE).1 C w) := by
  obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp ((mem_edgeFamily G E).mp hE).1
  have hedge:=(pair_mem_edgeFamily G huv).mp hE
  have hlin:=(good_edge_tight_kernel h s hn hf hedge hg).2 w
  rw [incidentWeight_eq_pairLinear h s hedge hg] at hlin
  have hwu : w≠ u:=fun he => hw (by simp [he])
  have hwv : w≠ v:=fun he => hw (by simp [he])
  rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])] at hlin
  have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
    ext a
    simp only [mem_insert,mem_singleton]
    tauto
  simpa only [he] using hlin

theorem goodPair_of_internalTriangle (G : SimpleGraph V) (T : ↥(internalTriangles G))
    (E : Finset V) (hET : E⊆T.1) : GoodPair G E := by
  have hlow:=(mem_internalTriangles.mp T.2).2
  rw [← incidentClique_card G T] at hlow
  apply hlow.trans
  apply Fintype.card_le_of_injective
    (fun C : IncidentClique G T => (⟨C.1,hET.trans C.2⟩ : IncidentPairClique G E))
  intro C D he
  apply Subtype.ext
  simpa only using congrArg (fun x : IncidentPairClique G E => x.1) he

/-- Each internal triangle sees a constant weighted response across all
three of its edge coordinates. The equation is derived from the complete
zero rows of the actual constructed polytope. -/
theorem internal_triangle_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (j : ↥T.1) :
    (∑ C : IncidentClique G T,mobius f C.1.1*realBit ((s.triangle T).row C j))=
      -mobius f T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp (mem_internalTriangles.mp T.2).1).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp (mem_internalTriangles.mp T.2).1).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have hlin:=good_pair_linear_relation h s hn hf E hE
    (goodPair_of_internalTriangle G T E (erase_subset _ _)) j.1 hjE
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 (mem_internalTriangles.mp T.2).1 he j.2
  have hport : ∀ C : IncidentClique G T,
      faceRow G s ⟨T.1,(mem_internalTriangles.mp T.2).1⟩ C j=(s.triangle T).row C j := by
    intro C
    exact congrArg (fun r : ↥T.1 → Bool => r j) (s.port_eq C.1 T C.2)
  simp_rw [hport] at hcol
  rw [← hcol] at hlin
  linarith

theorem incident_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (C D : IncidentClique G T) :
    mobius f C.1.1=mobius f D.1.1 :=
  (s.triangle T).kernel (fun C => mobius f C.1.1) (-mobius f T.1)
    (internal_triangle_relation h s hn hf T) C D

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart80

section BundlePart81
/- Source: Papers/GraphicalZonotopes/ThreeTreeKernelRigidity.lean -/




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

theorem adjacent_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {C D : Finset V} (hCD : (TriangleComponents.cliqueGraph G).Adj C D) :
    mobius f C=mobius f D := by
  obtain ⟨T,hTsub,hTcard⟩:=exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C:=hTsub.trans inter_subset_left
  have hTD : T⊆D:=hTsub.trans inter_subset_right
  have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.1,hCD.2.2.1⟩
  have hD : D∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.2.1,hCD.2.2.2.1⟩
  have hT:=internal_triangle_of_shared hC hD hCD.2.2.2.2.1 hTcard hTC hTD
  exact incident_clique_scales_equal h s hn hf ⟨T,hT⟩ ⟨⟨C,hC⟩,hTC⟩ ⟨⟨D,hD⟩,hTD⟩

/-- Every actual tetrahedral coefficient of a tight variation is a common
real scalar. Propagation uses paths in the graph of all actual tetrahedra,
not a selected subfamily. -/
theorem all_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,∀ C∈tetrahedra G,mobius f C=a := by
  obtain ⟨C₀,hC₀⟩:=h.tetrahedra_nonempty
  refine ⟨mobius f C₀,?_⟩
  intro C hC
  have hp:=h.tetrahedra_reachable hC hC₀
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  induction hp with
  | refl => rfl
  | @tail D E hD hDE ih =>
    have hmD : D ∈ tetrahedra G := mem_filter.mpr ⟨mem_univ _,hDE.1,hDE.2.2.1⟩
    exact (ih hmD).trans (adjacent_clique_scales_equal h s hn hf hDE)

theorem triangle_coefficient_of_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a)
    (T : ↥(triangles G)) (j : ↥T.1) (hg : GoodPair G (T.1.erase j.1)) :
    mobius f T.1=a*coefficients h s T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp T.2).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp T.2).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  have hlin:=good_pair_linear_relation h s hn hf E hE hg j.1 hjE
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 T.2 he j.2
  rw [← hcol] at hlin
  have hweights : ∀ C : AllIncidentClique G T,mobius f C.1.1=a:=fun C => ha C.1.1 C.1.2
  simp_rw [hweights] at hlin
  rw [← mul_sum] at hlin
  change mobius f T.1= -(a*columnValue G s T j) at hlin
  rw [column_eq_triangleWeight h s T j] at hlin
  rw [coefficients_triangle h s T.2,hlin]
  ring

/-- If the 3-tree has at least two tetrahedra, every triangle contains a
good edge. For a leaf triangle, use its intersection with an internal face
of its unique incident tetrahedron. -/
theorem triangle_has_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hm : 2≤(tetrahedra G).card) (T : ↥(triangles G)) :
    ∃ j : ↥T.1,GoodPair G (T.1.erase j.1) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · obtain ⟨w,hw⟩:=card_pos.mp (by rw [(mem_triangles.mp T.2).1]; decide)
    exact ⟨⟨w,hw⟩,goodPair_of_internalTriangle G ⟨T.1,hT⟩ _ (erase_subset _ _)⟩
  · obtain ⟨C,hC,hTC⟩:=h.triangle_extends (mem_triangles.mp T.2).1 (mem_triangles.mp T.2).2
    obtain ⟨D,hD,hDC⟩:=exists_mem_ne (show 1<(tetrahedra G).card by omega) C
    obtain ⟨F,hF,hEF,hFC⟩:=h.shared_face_containing hC hD hDC.symm
      (E:=∅) (empty_subset _) (empty_subset _)
    have hFcard:=(mem_triangles.mp (mem_internalTriangles.mp hF).1).1
    obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp hC).2.1 hFcard hFC
    have hrT : r.1∈T.1 := by
      by_contra hrT
      have hTF : T.1⊆F := by
        rw [← hr]
        intro w hw
        exact mem_erase.mpr ⟨fun he => hrT (he ▸ hw),hTC hw⟩
      have he : T.1=F:=eq_of_subset_of_card_le hTF (by
        rw [(mem_triangles.mp T.2).1,hFcard])
      exact hT (he.symm ▸ hF)
    refine ⟨⟨r.1,hrT⟩,goodPair_of_internalTriangle G ⟨F,hF⟩ _ ?_⟩
    simpa only [← hr] using erase_subset_erase r.1 hTC

theorem all_triangle_coefficients_scaled {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ T∈triangles G,mobius f T=a*coefficients h s T := by
  intro T hT
  obtain ⟨j,hj⟩:=triangle_has_good_pair h hm ⟨T,hT⟩
  exact triangle_coefficient_of_good_pair h s hn hf a ha ⟨T,hT⟩ j hj

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart81

section BundlePart82
/- Source: Papers/GraphicalZonotopes/ThreeTreeMaximal.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every clique in the active vertex set of a 3-tree extends to an
actual tetrahedron. This includes empty sets, vertices and edges, rather
than only the triangular separators used in the construction. -/
theorem ThreeTreeOn.clique_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C : Finset V} (hCS : C⊆S) (hC : G.IsClique C) :
    ∃ D∈tetrahedra G,C⊆D := by
  classical
  induction h generalizing C with
  | tetrahedron A hA =>
    exact ⟨A,by rw [tetrahedra_cliqueGraph hA]; simp,hCS⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huC : u∈C
    · refine ⟨insert u A,?_,?_⟩
      · rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_self _ _
      · intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hC huC hv (Ne.symm hvu))))
    · have hCold : C⊆S := by
        intro v hv
        rcases mem_insert.mp (hCS hv) with he | hvS
        · exact False.elim (huC (he ▸ hv))
        · exact hvS
      obtain ⟨D,hD,hCD⟩ := ih hCold (clique_before_attachment huC hC)
      exact ⟨D,by
        rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_of_mem hD,hCD⟩

/-- In the full 3-tree, the finite tetrahedra used by the coefficient
formalization are exactly the ordinary maximal cliques of the paper. -/
theorem IsThreeTree.maximalClique_iff {G : SimpleGraph V} (h : IsThreeTree G)
    (C : Finset V) : Maximal G.IsClique (C : Set V) ↔ C∈tetrahedra G := by
  classical
  constructor
  · intro hmax
    obtain ⟨D,hD,hCD⟩ := h.clique_extends (subset_univ C) hmax.1
    have hDC : D⊆C := hmax.2 (mem_filter.mp hD).2.2 hCD
    have he : C=D := subset_antisymm hCD hDC
    simpa only [he] using hD
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
    apply SimpleGraph.IsMaximumClique.isMaximalClique C
    refine ⟨hcl,?_⟩
    intro D hD
    rw [hc]
    exact h.clique_card_le_four hD

end GraphicalZonotopes

end
end
end BundlePart82

section BundlePart83
/- Source: Papers/GraphicalZonotopes/ThreeTreeConstructionBounds.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def contextBits (A : Finset V) (w : V) : Bool := decide (w∈A)

theorem booleanSupport_contextBits (A : Finset V) :
    booleanSupport (fun w => realBit (contextBits A w))=A := by
  ext w
  by_cases hw : w∈A <;> simp [booleanSupport,contextBits,realBit,hw]

theorem elemental_factorization_context {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C
        (fun w => realBit (contextBits A w)) := by
  simpa only [booleanSupport_contextBits,erase_eq_of_notMem hu,erase_eq_of_notMem hv]
    using elemental_factorization h s huv (contextBits A)

theorem elemental_bounds_incident {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    0≤ delta (setFunction h s) u v A ∧
      delta (setFunction h s) u v A≤(Fintype.card (IncidentPairClique G {u,v}) : ℝ) := by
  rw [elemental_factorization_context h s huv A hu hv]
  constructor
  · apply sum_nonneg
    intro C hC
    rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
      with he | he <;> simp only [he] <;> norm_num
  · calc
      _≤∑ _ : IncidentPairClique G {u,v},(1 : ℝ) := by
        apply sum_le_sum
        intro C hC
        rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
          with he | he <;> simp only [he] <;> norm_num
      _=_ := by simp

theorem incidentPairClique_card_le {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (E : Finset V) :
    Fintype.card (IncidentPairClique G E)≤ S.card-3 := by
  calc
    _≤ Fintype.card ↥(tetrahedra G) :=
      Fintype.card_le_of_injective (fun C => C.1) (fun C D he => Subtype.ext he)
    _=S.card-3 := by rw [Fintype.card_coe,h.tetrahedra_card]

/-- The original unbounded graph, with all of its conditioning sets,
satisfies the full supermodular inequalities. No subset of rows is used. -/
theorem setFunction_supermodular {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : Supermodular (setFunction h s) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv A hu hv
  by_cases hedge : G.Adj u v
  · exact (elemental_bounds_incident h s hedge A hu hv).1
  · rw [(setFunction_normalized_graphical h s).2 u v huv hedge A hu hv]

theorem elemental_bound {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A≤((S.card-3 : ℕ) : ℝ) := by
  apply (elemental_bounds_incident h s huv A hu hv).2.trans
  exact_mod_cast incidentPairClique_card_le h ({u,v} : Finset V)

theorem setFunction_lattice {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : LatticePolytope (basePolytope (setFunction h s)) :=
  (setFunction_integerValued h s).basePolytope (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s)

/-- The construction is an actual summand of the stated dilation of the
ordinary graphical zonotope, including its compact convex complement. -/
theorem setFunction_actual_summand {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    IsMinkowskiSummand (basePolytope (setFunction h s))
      (((S.card-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  apply (isMinkowskiSummand_graphical_iff (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s) (Nat.cast_nonneg _)).mpr
  exact ⟨(setFunction_normalized_graphical h s).2,
    fun u v huv hedge A hu hv => elemental_bound h s hedge A hu hv⟩

/-- A coefficient-one tetrahedron forces a nonzero elemental row at each
of its edges. Nonnegativity then makes that row strictly positive. -/
theorem exists_positive_edge_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ 0< delta (setFunction h s) u v A := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ A : Finset V,u∉A → v∉A → delta (setFunction h s) u v A=0 := by
    intro A hu hv
    exact le_antisymm (hn A hu hv) ((setFunction_supermodular h s).elemental u v huv.ne A hu hv)
  have hy := (nonedge_coefficients_zero_iff (coefficients h s) huv.ne).mp hz
  obtain ⟨C,hC,hEC⟩ := h.clique_extends
    (C:=({u,v} : Finset V)) (by
      simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
    (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
  have hc:=hy C (hEC (by simp)) (hEC (by simp))
  rw [coefficients_tetrahedron h s hC] at hc
  norm_num at hc

theorem setFunction_direction_graph {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    actualDirectionGraph (basePolytope (setFunction h s))=G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hadd⟩:=setFunction_actual_summand h s
    exact basePolytope_summand_actualRootEdge (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) G (Nat.cast_nonneg _) R hadd he
  · intro huv
    obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
    exact exposedSegment_of_positive_delta (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) huv.ne hu hv hpos

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart83

section BundlePart84
/- Source: Papers/GraphicalZonotopes/ThreeTreeTightKernel.lean -/






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

theorem zeta_pairSupported_delta_unordered (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S = y {u,v} := by
  rw [delta_zeta huv hu hv]
  refine Finset.sum_eq_single (s := (insert u (insert v S)).powerset.filter
    (fun C => u ∈ C ∧ v ∈ C)) (f := y) ({u,v} : Finset V) ?_ ?_
  · intro C hC hne
    apply hy C
    intro hcard
    have hmem := (mem_filter.mp hC).2
    have hsub : ({u,v} : Finset V) ⊆ C :=
      insert_subset hmem.1 (singleton_subset_iff.mpr hmem.2)
    have he : ({u,v} : Finset V) = C := eq_of_subset_of_card_le hsub (by
      simpa [huv] using le_of_eq hcard)
    exact hne he.symm
  · intro hnot
    exact False.elim (hnot (by simp))

theorem pairFactor_has_zero (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) :
    ∃ x : V → Bool,pairFactor G s E hE C (fun w => realBit (x w))=0 := by
  let p:=complementPair G C.1 E hE C.2
  let a:=(s.clique C.1).row p.first p.second
  let b:=(s.clique C.1).row p.second p.first
  let x : V → Bool:=Function.update (fun _ => a) p.first.1 b
  refine ⟨x,?_⟩
  have hx1 : x p.first.1=b:=by simp [x]
  have hx2 : x p.second.1=a:=Function.update_of_ne p.ne_val.symm _ _
  change ((max (RootedResponse.integerBit a) (RootedResponse.integerBit b) : ℤ) : ℝ)-
    realBit a*realBit (x p.second.1)-realBit b*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0
  rw [hx1,hx2]
  cases a <;> cases b <;> norm_num [realBit,RootedResponse.integerBit]

theorem edge_has_zero_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ delta (setFunction h s) u v A=0 := by
  classical
  by_cases hg : GoodPair G {u,v}
  · obtain ⟨x,hx⟩:=ForestZeros.totalFactor_has_zero (edgeLink G u v)
      (h.edgeLink_acyclic huv) (linkBit G s huv)
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_good_factorization h s huv hg x]
    exact hx
  · obtain ⟨D,hD,hED⟩:=h.clique_extends (C:=({u,v} : Finset V))
      (by simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
      (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
    let C : IncidentPairClique G {u,v}:=⟨⟨D,hD⟩,hED⟩
    have hpos : 0< Fintype.card (IncidentPairClique G {u,v}):=
      Fintype.card_pos_iff.mpr ⟨C⟩
    have hone : Fintype.card (IncidentPairClique G {u,v})=1 := by
      unfold GoodPair at hg
      omega
    have hsub : Subsingleton (IncidentPairClique G {u,v}):=
      Fintype.card_le_one_iff_subsingleton.mp hone.le
    obtain ⟨x,hx⟩:=pairFactor_has_zero G s {u,v} (by simp [huv.ne]) C
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_factorization h s huv x]
    rw [sum_eq_single C]
    · exact hx
    · intro D hD hDC
      exact False.elim (hDC (hsub.elim _ _))
    · intro hn
      exact False.elim (hn (mem_univ C))

theorem cliqueSupported_zero_of_not_clique {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hc : ¬G.IsClique C) : y C=0 := by
  by_contra hn
  exact hc (hy.clique_of_nonzero hn)

/-- After recovering every actual tetrahedron and triangle coefficient,
the full Möbius residual is supported on pairs. No clique or higher-degree
coordinates are omitted from this assertion. -/
theorem residual_pair_supported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ C,C.card≠2 → (mobius f-a • coefficients h s) C=0 := by
  have hy:=tightVariation_cliqueSupported h s hn hf
  have hz:=coefficients_cliqueSupported h s
  have htri:=all_triangle_coefficients_scaled h s hm hn hf a ha
  intro C hc2
  change mobius f C-a*coefficients h s C=0
  by_cases hcl : G.IsClique C
  · have hcard:=h.clique_card_le_four hcl
    have hc : C.card=0 ∨ C.card=1 ∨ C.card=3 ∨ C.card=4 := by omega
    rcases hc with hc | hc | hc | hc
    · have he : C=∅:=card_eq_zero.mp hc
      rw [he,hy.1,hz.1,mul_zero,sub_zero]
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hc
      rw [hy.2.1 v,hz.2.1 v,mul_zero,sub_zero]
    · rw [htri C (mem_triangles.mpr ⟨hc,hcl⟩),sub_self]
    · have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hc,hcl⟩
      rw [ha C hC,coefficients_tetrahedron h s hC,mul_one,sub_self]
  · rw [cliqueSupported_zero_of_not_clique hy hcl,
      cliqueSupported_zero_of_not_clique hz hcl,mul_zero,sub_zero]

/-- The complete normalized tight kernel for the constructed ray on any
3-tree with at least two tetrahedra. All real set functions are quantified,
and support is deduced from the original nonedge zero rows. -/
theorem complete_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,f=a • setFunction h s := by
  classical
  obtain ⟨a,ha⟩:=all_clique_scales_equal h s hn hf
  let y:=mobius f-a • coefficients h s
  have hyp : ∀ C,C.card≠2 → y C=0:=residual_pair_supported h s hm hn hf a ha
  have hyf:=tightVariation_cliqueSupported h s hn hf
  have hyz:=coefficients_cliqueSupported h s
  have hzeta : zeta y=f-a • setFunction h s := by
    change zetaLinear (mobius f-a • coefficients h s)=_
    rw [map_sub,map_smul]
    change zeta (mobius f)-a • zeta (coefficients h s)=_
    rw [zeta_mobius]
    rfl
  have hy0 : y=0 := by
    funext C
    by_cases hc2 : C.card=2
    · obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc2
      by_cases hedge : G.Adj u v
      · obtain ⟨A,hu,hv,hA⟩:=edge_has_zero_slack h s hedge
        have hvar:=hf u v huv A hu hv hA
        have hrow:=zeta_pairSupported_delta_unordered y hyp huv hu hv
        rw [hzeta,delta_sub,delta_smul,hvar,hA,mul_zero,sub_zero] at hrow
        exact hrow.symm
      · change mobius f {u,v}-a*coefficients h s {u,v}=0
        rw [hyf.2.2 {u,v} u v (by simp) (by simp) huv hedge,
          hyz.2.2 {u,v} u v (by simp) (by simp) huv hedge,mul_zero,sub_zero]
    · exact hyp C hc2
  refine ⟨a,sub_eq_zero.mp ?_⟩
  rw [← hzeta,hy0]
  exact (zeta_eq_zero_iff _).mpr rfl

theorem setFunction_extreme {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card) :
    ExtremeSupermodular (setFunction h s) :=
  extremeSupermodular_of_tightEquations (setFunction_normalized_graphical h s).1
    (setFunction_supermodular h s) (setFunction_ne_zero h s)
    (complete_tight_kernel h s hm)

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart84

section BundlePart85
/- Source: Papers/GraphicalZonotopes/SimplexRay.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem setMonomial_translationNormalized {C : Finset V} (hC : 2≤ C.card) :
    TranslationNormalized (setMonomial C) := by
  refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
  intro v
  have hnot : ¬C⊆{v} := by
    intro hs
    have hc:=card_le_card hs
    simp only [card_singleton] at hc
    omega
  simp only [setMonomial,if_neg hnot]

theorem setMonomial_graphical (C : Finset V) : Graphical (cliqueGraph C) (setMonomial C) := by
  intro u v huv hnon A hu hv
  rw [delta_setMonomial huv hu hv]
  apply if_neg
  rintro ⟨huC,hvC,hsub⟩
  exact hnon ⟨huv,huC,hvC⟩

theorem zeta_single_coefficient (C : Finset V) (a : ℝ) :
    zeta (fun D : Finset V => if D=C then a else 0)=a • setMonomial C := by
  funext A
  by_cases hCA : C⊆A <;> simp [zeta,setMonomial,hCA]

theorem mobius_setMonomial (C : Finset V) :
    mobius (setMonomial C)=(fun D => if D=C then 1 else 0) := by
  have he:=zeta_single_coefficient C 1
  simp only [one_smul] at he
  rw [← he,mobius_zeta]

/-- The simplex ray has its complete normalized tight kernel in every
ambient dimension. The proof retains every proper-subset equation, including
coordinates outside the simplex's support. -/
theorem setMonomial_tight_kernel {C : Finset V} (hC : 2≤ C.card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : ThreeTreeStates.TightVariation (setMonomial C) f) :
    ∃ a : ℝ,f=a • setMonomial C := by
  classical
  have hgraph : Graphical (cliqueGraph C) f := by
    intro u v huv hnon A hu hv
    exact hf u v huv A hu hv (setMonomial_graphical C u v huv hnon A hu hv)
  have hy : CliqueSupported (cliqueGraph C) (mobius f):=
    (mobius_cliqueSupported_iff _ f).mpr ⟨hn,hgraph⟩
  have hzero : ∀ D : Finset V,D≠ C → mobius f D=0 := by
    intro D
    refine Finset.strongInductionOn D ?_
    intro D ih
    intro hDC
    by_cases hd0 : D.card=0
    · rw [card_eq_zero.mp hd0]
      exact hy.1
    by_cases hd1 : D.card=1
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hd1
      exact hy.2.1 v
    by_contra hnonzero
    have hd2 : 2≤ D.card:=by omega
    have hcl:=hy.clique_of_nonzero hnonzero
    have hDCsub : D⊆C := by
      intro u hu
      obtain ⟨v,hv,hvu⟩:=exists_mem_ne (show 1< D.card by omega) u
      exact (hcl hu hv hvu.symm).2.1
    have hnot : ¬C⊆D:=fun hCD => hDC (subset_antisymm hDCsub hCD)
    obtain ⟨u,huD,v,hvD,huv⟩:=one_lt_card.mp (show 1< D.card by omega)
    let A:=(D.erase u).erase v
    have huA : u∉A:=by simp [A]
    have hvA : v∉A:=by simp [A]
    have he : insert u (insert v A)=D := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv,huD,hvD]
    have hrow : delta (setMonomial C) u v A=0 := by
      rw [delta_setMonomial huv huA hvA,he]
      simp only [hnot,and_false,ite_false]
    have hvar:=hf u v huv A huA hvA hrow
    rw [← zeta_mobius f,delta_zeta huv huA hvA,he] at hvar
    rw [sum_eq_single D] at hvar
    · exact hnonzero hvar
    · intro B hB hBD
      have hBDsub:=(mem_powerset.mp (mem_filter.mp hB).1)
      apply ih B (Finset.ssubset_iff_subset_ne.mpr ⟨hBDsub,hBD⟩)
      intro hBC
      exact hnot (hBC ▸ hBDsub)
    · intro hDnot
      exact False.elim (hDnot (by simp [huD,hvD]))
  let a:=mobius f C
  have hyEq : mobius f=(fun D => if D=C then a else 0) := by
    funext D
    by_cases hDC : D=C
    · simp only [hDC,ite_true,a]
    · simp only [if_neg hDC,hzero D hDC]
  refine ⟨a,?_⟩
  rw [← zeta_mobius f,hyEq]
  exact zeta_single_coefficient C a

theorem setMonomial_extreme {C : Finset V} (hC : 2≤ C.card) :
    ExtremeSupermodular (setMonomial C) := by
  apply extremeSupermodular_of_tightEquations (setMonomial_translationNormalized hC)
    (setMonomial_supermodular C)
  · intro he
    have hx:=congrFun he C
    norm_num [setMonomial] at hx
  · exact setMonomial_tight_kernel hC

end GraphicalZonotopes

end
end
end BundlePart85

section BundlePart86
/- Source: Papers/GraphicalZonotopes/ThreeTreeConstruction.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.roots_mem {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (W : Submodule ℝ (V → ℝ))
    (hW : ∀ u v,G.Adj u v → basisVector u-basisVector v∈W) :
    ∀ u∈S,∀ v∈S,basisVector u-basisVector v∈W := by
  revert hW
  induction h with
  | tetrahedron C hC =>
    intro hW u hu v hv
    by_cases huv : u=v
    · simp [huv]
    · exact hW u v ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    intro hW u hu v hv
    have hi:=ih (fun u v huv => hW u v (Or.inl huv))
    obtain ⟨a,ha⟩:=card_pos.mp (show 0< T.card by omega)
    have hwa:=hW w a ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    rcases mem_insert.mp hu with huw | huS
    · subst u
      rcases mem_insert.mp hv with hvw | hvS
      · subst v
        simp
      · have hp:=W.add_mem hwa (hi a (hTS ha) v hvS)
        convert hp using 1 <;> module
    · rcases mem_insert.mp hv with hvw | hvS
      · subst v
        have hp:=W.sub_mem (hi u huS a (hTS ha)) hwa
        convert hp using 1 <;> module
      · exact hi u huS v hvS

theorem ThreeTreeOn.eq_cliqueGraph_of_card_four {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hS : S.card=4) : G=cliqueGraph S := by
  induction h with
  | tetrahedron C hC => rfl
  | @attach S G h w hw T hT hTS hcl ih =>
    have hlo:=h.active_card_ge_four
    rw [card_insert_of_notMem hw] at hS
    omega

namespace ThreeTreeStates

theorem setFunction_fullDimension {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : IsThreeTree G) (s : CompatibleRows G) :
    FullDimension (basePolytope (setFunction h s)) := by
  have hn4 : 4≤ n:=by simpa only [card_univ,Fintype.card_fin] using h.active_card_ge_four
  have hn:=(setFunction_normalized_graphical h s).1.1
  have hs:=setFunction_supermodular h s
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hn hs)
  intro i
  apply h.roots_mem (vectorSpan ℝ (basePolytope (setFunction h s))) _ _ (mem_univ _) _ (mem_univ _)
  intro u v huv
  obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
  exact root_mem_vectorSpan_of_delta_ne_zero hn hs huv.ne hu hv hpos.ne'

end ThreeTreeStates

theorem complete_simplex_fullDimension {n : ℕ} (hn : 2≤ n) :
    FullDimension (basePolytope (setMonomial (univ : Finset (Fin n)))) := by
  have hzn:=(setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
    (by simpa using hn)).1
  have hzs:=setMonomial_supermodular (univ : Finset (Fin n))
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hzn hzs)
  intro i
  let u : Fin n:=⟨i.val,by omega⟩
  let v : Fin n:=⟨i.val+1,by omega⟩
  have huv : u≠ v:=by intro he; have he':=congrArg Fin.val he; dsimp [u,v] at he'; omega
  let A:=(univ.erase u).erase v
  have hu : u∉A:=by simp [A]
  have hv : v∉A:=by simp [A]
  have he : insert u (insert v A)=univ := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
  apply root_mem_vectorSpan_of_delta_ne_zero hzn hzs huv hu hv
  rw [delta_setMonomial huv hu hv,he]
  norm_num

theorem complete_simplex_direction_graph {n : ℕ} (hn : 2≤ n) :
    actualDirectionGraph (basePolytope (setMonomial (univ : Finset (Fin n)) ))=
      cliqueGraph (univ : Finset (Fin n)) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    exact ⟨he.1,mem_univ _,mem_univ _⟩
  · intro huv
    let A:=(univ.erase u).erase v
    have hu : u∉A:=by simp [A]
    have hv : v∉A:=by simp [A]
    have he : insert u (insert v A)=univ := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
    apply exposedSegment_of_positive_delta
      (setMonomial_translationNormalized (C:=(univ : Finset (Fin n))) (by simpa using hn)).1
      (setMonomial_supermodular _) huv.1 hu hv
    rw [delta_setMonomial huv.1 hu hv,he]
    norm_num

/-- The complete quantitative existence assertion of Theorem6.1. This is
the actual integral Möbius vector, all graph directions, full affine
dimension, and the literal (n−3)-zonotope summand, for every n≥4. -/
theorem admissible_threeTree_construction {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      (∀ C∈tetrahedra G,mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  classical
  by_cases hn4 : n=4
  · have hGraph : G=cliqueGraph (univ : Finset (Fin n)):=
      hG.eq_cliqueGraph_of_card_four (by simpa using hn4)
    let z:=setMonomial (univ : Finset (Fin n))
    refine ⟨z,setMonomial_extreme (by simpa using (show 2≤ n by omega)),?_,?_,?_,
      complete_simplex_fullDimension (by omega),?_,?_⟩
    · rw [mobius_setMonomial]
      intro C
      by_cases hC : C=univ
      · exact ⟨1,by simp [hC]⟩
      · exact ⟨0,by simp [hC]⟩
    · intro C hC
      rw [hGraph,tetrahedra_cliqueGraph (by simpa using hn4),mem_singleton] at hC
      rw [mobius_setMonomial]
      simp [hC]
    · intro T ht hcl
      left
      rw [mobius_setMonomial]
      have hne : T≠ univ := by
        intro he
        have hc:=congrArg Finset.card he
        simp only [ht,card_univ,Fintype.card_fin] at hc
        omega
      simp [hne]
    · rw [hGraph]
      exact complete_simplex_direction_graph (by omega)
    · apply (isMinkowskiSummand_graphical_iff
        (setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
          (by simpa using (show 2≤ n by omega))).1
        (setMonomial_supermodular _) (Nat.cast_nonneg _)).mpr
      refine ⟨by rw [hGraph]; exact setMonomial_graphical _,?_⟩
      intro u v huv hedge A hu hv
      rw [delta_setMonomial huv hu hv]
      have he : (n-3 : ℕ)=1 := by omega
      rw [he]
      split <;> norm_num
  · obtain ⟨s⟩:=ThreeTreeStates.compatibleRows_exists hG hA
    have hm : 2≤(tetrahedra G).card := by
      rw [hG.tetrahedra_card,card_univ,Fintype.card_fin]
      omega
    refine ⟨ThreeTreeStates.setFunction hG s,
      ThreeTreeStates.setFunction_extreme hG s hm,?_,?_,?_,
      ThreeTreeStates.setFunction_fullDimension hG s,
      ThreeTreeStates.setFunction_direction_graph hG s,?_⟩
    · rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_integerValued hG s
    · intro C hC
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_tetrahedron hG s hC
    · intro T ht hcl
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_triangle_values hG s (mem_triangles.mpr ⟨ht,hcl⟩)
    · simpa only [card_univ,Fintype.card_fin] using ThreeTreeStates.setFunction_actual_summand hG s

end GraphicalZonotopes

end
end
end BundlePart86

section BundlePart87
/- Source: Papers/GraphicalZonotopes/GraphComponentExtension.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace VertexExtension
variable {V : Type*} {W : Type*}

/-- Add one vertex, with exactly the specified neighbors. The old vertex
type is retained as `some`, and the new vertex is `none`. -/
def graph (G : SimpleGraph V) (N : Set V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | none,some v => v∈N
    | some v,none => v∈N
    | some v,some w => G.Adj v w
    | none,none => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp [G.irrefl]⟩

def someHom (G : SimpleGraph V) (N : Set V) : G →g graph G N where
  toFun := Option.some
  map_rel' := fun h => h

/-- A label constant on each edge descends to the actual connected-component
quotient. In particular, this does not assert that the labels define a graph
homomorphism, which would fail when an edge is collapsed to one vertex. -/
def componentLift (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) : G.ConnectedComponent → W :=
  Quot.lift f (by
    intro u v hp
    rw [SimpleGraph.reachable_eq_reflTransGen] at hp
    induction hp with
    | refl => rfl
    | @tail v w hp hvw ih => exact ih.trans (hf v w hvw))

@[simp] theorem componentLift_mk (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) (u : V) :
    componentLift G f hf (G.connectedComponentMk u)=f u := rfl

def oldLabel (G : SimpleGraph V) (v₀ : V) : Option V → G.ConnectedComponent
  | none => G.connectedComponentMk v₀
  | some v => G.connectedComponentMk v

theorem oldLabel_adj (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    ∀ a b,(graph G N).Adj a b → oldLabel G v₀ a=oldLabel G v₀ b := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact False.elim hab
    | some v =>
      by_cases he : v₀=v
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hv₀ hab he).reachable
  | some u =>
    cases b with
    | none =>
      by_cases he : u=v₀
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hab hv₀ he).reachable
    | some v =>
        change G.Adj u v at hab
        exact SimpleGraph.ConnectedComponent.sound hab.reachable

/-- Attaching a vertex to a nonempty clique preserves all actual connected
components, including any other disconnected components of the old graph. -/
def componentEquiv (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    (graph G N).ConnectedComponent ≃ G.ConnectedComponent where
  toFun := componentLift (graph G N) (oldLabel G v₀) (oldLabel_adj G N v₀ hv₀ hN)
  invFun := SimpleGraph.ConnectedComponent.map (someHom G N)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v with
    | none =>
      exact SimpleGraph.ConnectedComponent.sound
        (show (graph G N).Reachable (some v₀) none from
          (SimpleGraph.Adj.reachable (show (graph G N).Adj (some v₀) none from hv₀)))
    | some v => rfl
  right_inv := by
    intro c
    exact c.ind (fun _ => rfl)

theorem component_card (G : SimpleGraph V) (N : Set V)
    (hne : N.Nonempty) (hN : G.IsClique N) :
    Nat.card (graph G N).ConnectedComponent=Nat.card G.ConnectedComponent := by
  obtain ⟨v₀,hv₀⟩:=hne
  exact Nat.card_congr (componentEquiv G N v₀ hv₀ hN)

def isolatedLabel (G : SimpleGraph V) : Option V → Option G.ConnectedComponent
  | none => none
  | some v => some (G.connectedComponentMk v)

theorem isolatedLabel_adj (G : SimpleGraph V) :
    ∀ a b,(graph G ∅).Adj a b → isolatedLabel G a=isolatedLabel G b := by
  intro a b hab
  cases a <;> cases b
  · exact False.elim hab
  · exact False.elim hab
  · exact False.elim hab
  · rename_i u v
    change G.Adj u v at hab
    exact congrArg Option.some (SimpleGraph.ConnectedComponent.sound hab.reachable)

/-- Adding an isolated vertex adds exactly one new connected component. -/
def isolatedComponentEquiv (G : SimpleGraph V) :
    (graph G ∅).ConnectedComponent ≃ Option G.ConnectedComponent where
  toFun := componentLift (graph G ∅) (isolatedLabel G) (isolatedLabel_adj G)
  invFun := fun c => match c with
    | none => (graph G ∅).connectedComponentMk none
    | some c => c.map (someHom G ∅)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v <;> rfl
  right_inv := by
    intro c
    cases c with
    | none => rfl
    | some c => exact c.ind (fun _ => rfl)

theorem isolated_component_card (G : SimpleGraph V) [Finite V] :
    Nat.card (graph G ∅).ConnectedComponent=Nat.card G.ConnectedComponent+1 := by
  classical
  letI : Fintype G.ConnectedComponent:=Fintype.ofFinite _
  rw [Nat.card_congr (isolatedComponentEquiv G),Nat.card_eq_fintype_card,
    Fintype.card_option,Nat.card_eq_fintype_card]

theorem connected (G : SimpleGraph V) (N : Set V)
    (hG : G.Connected) (hne : N.Nonempty) : (graph G N).Connected := by
  obtain ⟨v₀,hv₀⟩:=hne
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none,?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.rfl
  | some v =>
    exact (SimpleGraph.Adj.reachable (show (graph G N).Adj none (some v₀) from hv₀)).trans
      ((hG v₀ v).map (someHom G N))

theorem connected_component_card_one {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card G.ConnectedComponent=1 := by
  letI : Nonempty V:=hG.nonempty
  letI : Subsingleton G.ConnectedComponent:=hG.preconnected.subsingleton_connectedComponent
  exact Nat.card_unique

end VertexExtension
end GraphicalZonotopes

end
end
end BundlePart87

section BundlePart88
/- Source: Papers/GraphicalZonotopes/ActiveDeletion.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete vertices from the actual active graph. Ambient isolated vertices
outside `S` are not included in this graph's vertex type. -/
def activeDelete (G : SimpleGraph V) (S D : Finset V) :
    SimpleGraph {v : V // v∈S ∧ v∉D} := G.induce {v | v∈S ∧ v∉D}

def activeAttachEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∉D) :
    Option {v : V // v∈S ∧ v∉D} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun x := match x with
    | none => ⟨u,mem_insert_self _ _,huD⟩
    | some v => ⟨v.1,mem_insert_of_mem v.2.1,v.2.2⟩
  invFun v := if hv : v.1=u then none else
    some ⟨v.1,(mem_insert.mp v.2.1).resolve_left hv,v.2.2⟩
  left_inv := by
    intro x
    cases x with
    | none => simp
    | some v =>
      have hv : v.1≠ u:=fun he => hu (he ▸ v.2.1)
      simp [hv]
  right_inv := by
    intro v
    by_cases hv : v.1=u
    · simp only [dif_pos hv]
      exact Subtype.ext hv.symm
    · simp only [dif_neg hv]

/-- The exact graph after a new vertex survives deletion: it is the old
deleted graph with one vertex attached to the surviving attachment clique. -/
def activeAttachIso {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) (A : Finset V) (hAS : A⊆S)
    (D : Finset V) (huD : u∉D) :
    VertexExtension.graph (activeDelete G S D) {v | v.1∈A} ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeAttachEquiv hu D huD
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj u u ↔ False
        simp
      | some v =>
        change (G⊔attachmentStar u A).Adj u v.1 ↔ v.1∈A
        exact attached_vertex_adj_iff h hu hAS v.1
    | some v =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj v.1 u ↔ v.1∈A
        rw [SimpleGraph.adj_comm]
        exact attached_vertex_adj_iff h hu hAS v.1
      | some w =>
        change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
        constructor
        · exact adj_before_attachment (fun he => hu (he ▸ v.2.1))
            (fun he => hu (he ▸ w.2.1))
        · exact Or.inl

def activeRemovedEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∈D) :
    {v : V // v∈S ∧ v∉D.erase u} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun v := ⟨v.1,mem_insert_of_mem v.2.1,by
    intro hvD
    exact v.2.2 (mem_erase.mpr ⟨fun he => hu (he ▸ v.2.1),hvD⟩)⟩
  invFun v := ⟨v.1,(mem_insert.mp v.2.1).resolve_left
    (fun he => v.2.2 (he.symm ▸ huD)),fun hv => v.2.2 (mem_of_mem_erase hv)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- If the newly attached vertex is deleted, no new edge survives. Removing
that vertex from the deletion set gives precisely the old induced graph. -/
def activeRemovedIso {S : Finset V} {G : SimpleGraph V} {u : V} (hu : u∉S)
    (A D : Finset V) (huD : u∈D) :
    activeDelete G S (D.erase u) ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeRemovedEquiv hu D huD
  map_rel_iff' := by
    intro v w
    change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
    exact ⟨adj_before_attachment (fun he => hu (he ▸ v.2.1))
      (fun he => hu (he ▸ w.2.1)),Or.inl⟩

theorem active_neighbors_nonempty {S A D : Finset V} (hAS : A⊆S)
    (hcard : D.card< A.card) :
    ({v : {v : V // v∈S ∧ v∉D} | v.1∈A} : Set _).Nonempty := by
  have hnot : ¬A⊆D:=fun h => Nat.not_lt_of_ge (card_le_card h) hcard
  obtain ⟨v,hvA,hvD⟩:=not_subset.mp hnot
  exact ⟨⟨v,hAS hvA,hvD⟩,hvA⟩

theorem active_neighbors_clique {G : SimpleGraph V} {S A D : Finset V}
    (hA : G.IsClique A) :
    (activeDelete G S D).IsClique {v | v.1∈A} := by
  intro v hv w hw hvw
  exact hA hv hw (fun he => hvw (Subtype.ext he))

theorem cliqueGraph_activeDelete_connected (C D : Finset V) (hcard : D.card< C.card) :
    (activeDelete (cliqueGraph C) C D).Connected := by
  have hn : ¬C⊆D:=fun hs => Nat.not_lt_of_ge (card_le_card hs) hcard
  obtain ⟨v,hvC,hvD⟩:=not_subset.mp hn
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨v,hvC,hvD⟩,?_⟩
  intro w
  by_cases he : v=w.1
  · have he' : (⟨v,hvC,hvD⟩ : {v : V // v∈C ∧ v∉D})=w:=Subtype.ext he
    rw [he']
  · exact SimpleGraph.Adj.reachable ⟨he,hvC,w.2.1⟩

/-- Deleting at most two vertices from a 3-tree leaves its active graph
connected. The deletion set is arbitrary; it need not lie inside `S`. -/
theorem ThreeTreeOn.delete_at_most_two_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (D : Finset V) (hD : D.card≤2) :
    (activeDelete G S D).Connected := by
  induction h generalizing D with
  | tetrahedron C hC =>
    exact cliqueGraph_activeDelete_connected C D (by omega)
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huD : u∈D
    · exact (activeRemovedIso (G:=G) hu A D huD).connected_iff.mp
        (ih (D.erase u) ((card_erase_le (s:=D) (a:=u)).trans hD))
    · exact (activeAttachIso h hu A hAS D huD).connected_iff.mp
        (VertexExtension.connected _ _ (ih D hD)
          (active_neighbors_nonempty hAS (by omega)))

theorem activeDelete_univ_components (G : SimpleGraph V) (D : Finset V) :
    Nat.card (activeDelete G univ D).ConnectedComponent=
      Nat.card (G.induce ((D : Set V)ᶜ)).ConnectedComponent := by
  let e : {v : V // v∈(univ : Finset V) ∧ v∉D} ≃ {v : V // v∉D} :=
    { toFun := fun v => ⟨v.1,v.2.2⟩
      invFun := fun v => ⟨v.1,mem_univ _,v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let iso : activeDelete G univ D ≃g G.induce ((D : Set V)ᶜ) :=
    { toEquiv := e
      map_rel_iff' := by intro v w; rfl }
  exact Nat.card_congr iso.connectedComponentEquiv

end GraphicalZonotopes

end
end
end BundlePart88

section BundlePart89
/- Source: Papers/GraphicalZonotopes/ThreeTreeDeletion.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangleMultiplicity_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) (T : Finset V) :
    triangleMultiplicity (G⊔attachmentStar u A) T=
      triangleMultiplicity G T+if T⊆insert u A then 1 else 0 := by
  classical
  simp only [triangleMultiplicity,tetrahedra_after_attachment h hu hA hAS hcA,
    filter_insert]
  split_ifs with ht
  · rw [card_insert_of_notMem (by
      intro hm
      exact attached_tetrahedron_not_old h hu (mem_filter.mp hm).1)]
  · simp

theorem ThreeTreeOn.triangleMultiplicity_eq_zero_of_outside
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) {T : Finset V} (huT : u∈T) :
    triangleMultiplicity G T=0 := by
  classical
  unfold triangleMultiplicity
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro C hC hTC
  obtain ⟨hc,hcl⟩:=(mem_filter.mp hC).2
  exact hu (h.clique_subset_active (by omega) hcl (hTC huT))

/-- The exact separator dictionary for every triangle of a 3-tree, proved
on the actual active vertex type. Thus unused ambient vertices cannot create
spurious components in the induction. -/
theorem ThreeTreeOn.triangle_components_eq_multiplicity
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (activeDelete G S T).ConnectedComponent=triangleMultiplicity G T := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    have hTC:=(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    rw [VertexExtension.connected_component_card_one
      (cliqueGraph_activeDelete_connected C T (by omega))]
    simp only [triangleMultiplicity,tetrahedra_cliqueGraph hC]
    rw [Finset.filter_singleton]
    simp only [if_pos hTC, Finset.card_singleton]
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u∈T
    · have hTsub : T⊆insert u A := by
        intro v hv
        by_cases he : v=u
        · exact mem_insert.mpr (Or.inl he)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm he))))
      have hconn : (activeDelete (G⊔attachmentStar u A) (insert u S) T).Connected :=
        (activeRemovedIso (G:=G) hu A T huT).connected_iff.mp
          (h.delete_at_most_two_connected (T.erase u) (by
            rw [card_erase_of_mem huT,hT]))
      rw [VertexExtension.connected_component_card_one hconn,
        triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu huT,if_pos hTsub]
    · have hcOld : G.IsClique T:=clique_before_attachment huT hcT
      have hnewcard := Nat.card_congr
        (activeAttachIso h hu A hAS T huT).connectedComponentEquiv
      rw [← hnewcard,triangleMultiplicity_after_attachment h hu hA hAS hcA]
      by_cases hTA : T=A
      · subst T
        have hN : ({v : {v : V // v∈S ∧ v∉A} | v.1∈A} : Set _)=∅ := by
          ext v
          exact ⟨fun hv => v.2.2 hv,False.elim⟩
        rw [hN,VertexExtension.isolated_component_card,
          ih A hA hcA,if_pos (subset_insert _ _)]
      · have hnot : ¬A⊆T := by
          intro hAT
          exact hTA (eq_of_subset_of_card_le hAT (by omega)).symm
        obtain ⟨v,hvA,hvT⟩:=not_subset.mp hnot
        have hN : ({v : {v : V // v∈S ∧ v∉T} | v.1∈A} : Set _).Nonempty :=
          ⟨⟨v,hAS hvA,hvT⟩,hvA⟩
        have hnotSub : ¬T⊆insert u A := by
          intro ht
          have htA : T⊆A := by
            intro w hw
            exact (mem_insert.mp (ht hw)).resolve_left (fun he => huT (he ▸ hw))
          exact hTA (eq_of_subset_of_card_le htA (by omega))
        rw [VertexExtension.component_card _ _ hN (active_neighbors_clique hcA),
          ih T hT hcOld,if_neg hnotSub,Nat.add_zero]

/-- Literal vertex deletion on a full 3-tree has exactly one component per
maximal tetrahedron containing the deleted triangle. -/
theorem IsThreeTree.triangle_components_eq_multiplicity {G : SimpleGraph V}
    (hG : IsThreeTree G) (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent=triangleMultiplicity G T := by
  rw [← activeDelete_univ_components]
  exact ThreeTreeOn.triangle_components_eq_multiplicity hG T hT hcT

theorem IsThreeTree.admissible_iff_triangle_deletion {G : SimpleGraph V}
    (hG : IsThreeTree G) :
    Admissible G ↔ ∀ T : Finset V,T.card=3 → G.IsClique T →
      Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent≤3 := by
  constructor
  · intro h T ht hc
    rw [hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc
  · intro h T ht hc
    rw [← hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc

end GraphicalZonotopes

end
end
end BundlePart89

section BundlePart90
/- Source: Papers/GraphicalZonotopes/Gluing.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
An abstract finite-inequality version of positive response gluing. Internal rows
and all boundary choices are retained. The private hypothesis is the actual kernel
of internal zero rows and differences of minimizing boundary rows.
-/
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators

variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j, Fintype (K j)] [∀ j, Fintype (I j)] [∀ j, Fintype (X j)]
variable [DecidableEq J]

abbrev Global (J : Type*) (K : J → Type*) (D : Type*) := (D → ℝ) × (∀ j, K j → ℝ)
abbrev Row (B J : Type*) (I X : J → Type*) := (Σ j, I j) ⊕ (B × (∀ j, X j))

structure Data (B J : Type*) (K : J → Type*) (D : Type*) (I X : J → Type*) where
  boundary : (D → ℝ) →ₗ[ℝ] (B → ℝ)
  internal : (j : J) → I j → (K j → ℝ) →ₗ[ℝ] ℝ
  response : (j : J) → B → X j → (K j → ℝ) →ₗ[ℝ] ℝ

def Data.row (M : Data B J K D I X) : Row B J I X → Global J K D →ₗ[ℝ] ℝ
  | Sum.inl ⟨j, i⟩ =>
    { toFun := fun y => M.internal j i (y.2 j)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  | Sum.inr (b, x) =>
    { toFun := fun y => M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j)
      map_add' := by intros; simp [Finset.sum_add_distrib]; ring
      map_smul' a y := by
        change M.boundary (a • y.1) b + (∑ j, M.response j b (x j) (a • y.2 j)) =
          a * (M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j))
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        rw [mul_add, Finset.mul_sum] }

/-- The complete private equations at a branch point. -/
def Data.PrivateKernel (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
    (j : J) (g : K j → ℝ) : Prop :=
  (∀ i, M.internal j i (f j) = 0 → M.internal j i g = 0) ∧
    ∀ b x y, M.response j b x (f j) = m j b → M.response j b y (f j) = m j b →
      M.response j b x g = M.response j b y g

def Data.Closure (M : Data B J K D I X) (m : J → B → ℝ)
    (z : D → ℝ) (c : J → ℝ) : Prop :=
  ∀ b, M.boundary z b + ∑ j, c j * m j b = 0

def assemble (z : D → ℝ) (c : J → ℝ) (f : ∀ j, K j → ℝ) : Global J K D :=
  (z, fun j => c j • f j)

variable (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
variable (hmin : ∀ j b x, m j b ≤ M.response j b x (f j))
variable (hatt : ∀ j b, ∃ x, M.response j b x (f j) = m j b)
variable (hinternal : ∀ j i, 0 ≤ M.internal j i (f j))
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j, 0 < lam j)
variable (hclose : M.Closure m z lam)

include hclose in
/-- The closing relation turns every boundary row into a sum of nonnegative
excesses above genuine conditional minima. -/
theorem row_boundary_eq_excess (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) =
      ∑ j, lam j * (M.response j b (x j) (f j) - m j b) := by
  have hc := hclose b
  simp only [Data.row, assemble, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, smul_eq_mul, Pi.smul_apply]
  simp only [mul_sub, sum_sub_distrib]
  linarith

include hmin hinternal hlam hclose in
theorem assembled_nonnegative : Polyhedral.Nonnegative M.row (assemble z lam f) := by
  intro r
  rcases r with ⟨j, i⟩ | ⟨b, x⟩
  · change 0 ≤ M.internal j i (lam j • f j)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hlam j).le (hinternal j i)
  · rw [row_boundary_eq_excess M f m z lam hclose]
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))

include hmin hlam hclose in
/-- With strictly positive branch scales, a boundary row is tight exactly when
each branch independently minimizes its contribution. -/
theorem boundary_tight_iff (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) = 0 ↔
      ∀ j, M.response j b (x j) (f j) = m j b := by
  rw [row_boundary_eq_excess M f m z lam hclose]
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ lam j * (M.response j b (x j) (f j) - m j b) :=
    fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))
  rw [sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h j
    have hj := h j (mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (ne_of_gt (hlam j)))
  · intro h j hj
    rw [h j, sub_self, mul_zero]

/-- Varying only one branch choice isolates exactly that branch's response
change. This uses every global boundary row, not a selected submatrix. -/
theorem row_boundary_update_difference (g : Global J K D) (b : B) (x : ∀ j, X j)
    (j : J) (a a' : X j) :
    M.row (Sum.inr (b, Function.update x j a)) g -
      M.row (Sum.inr (b, Function.update x j a')) g =
        M.response j b a (g.2 j) - M.response j b a' (g.2 j) := by
  classical
  simp only [Data.row, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a k) (g.2 k)) -
      (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a' k) (g.2 k)) =
        ∑ k, (M.response k b (Function.update x j a k) (g.2 k) -
          M.response k b (Function.update x j a' k) (g.2 k)) by rw [sum_sub_distrib]; ring]
  rw [sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [Function.update_of_ne hkj]
  · simp

include hmin hatt hlam hclose in
/-- Every branch's complete private equations are inherited from the complete
global tight kernel. -/
theorem privateKernel_of_global {g : Global J K D}
    (hg : g ∈ Polyhedral.tightKernel M.row (assemble z lam f)) (j : J) :
    M.PrivateKernel f m j (g.2 j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i hi
    have hrow : M.row (Sum.inl ⟨j, i⟩) (assemble z lam f) = 0 := by
      change M.internal j i (lam j • f j) = 0
      rw [map_smul, hi, smul_zero]
    exact hg _ hrow
  · intro b a a' ha ha'
    choose x hx using fun k : J => hatt k b
    have hx1 : ∀ k, M.response k b (Function.update x j a k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha
      · simpa [Function.update_of_ne hkj] using hx k
    have hx2 : ∀ k, M.response k b (Function.update x j a' k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha'
      · simpa [Function.update_of_ne hkj] using hx k
    have h1 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx1)
    have h2 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx2)
    have hdiff := row_boundary_update_difference M g b x j a a'
    rw [h1, h2] at hdiff
    linarith

variable (hprivate : ∀ j g, M.PrivateKernel f m j g → ∃ c : ℝ, g = c • f j)

include hmin hatt hlam hclose hprivate in
/-- Exact reconstruction of the complete tight kernel by branch scales and
boundary closure, including all boundary and all unused private coordinates. -/
theorem tightKernel_iff {g : Global J K D} :
    g ∈ Polyhedral.tightKernel M.row (assemble z lam f) ↔
      ∃ c : J → ℝ, (∀ j, g.2 j = c j • f j) ∧ M.Closure m g.1 c := by
  constructor
  · intro hg
    have hsc : ∀ j, ∃ c : ℝ, g.2 j = c • f j :=
      fun j => hprivate j (g.2 j) (privateKernel_of_global M f m hmin hatt z lam hlam hclose hg j)
    choose c hc using hsc
    refine ⟨c, hc, ?_⟩
    intro b
    choose x hx using fun j : J => hatt j b
    have ht := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mpr hx
    have hgzero := hg _ ht
    change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0 at hgzero
    simpa only [hc, map_smul, smul_eq_mul, hx] using hgzero
  · rintro ⟨c, hc, hcl⟩ r hr
    rcases r with ⟨j, i⟩ | ⟨b, x⟩
    · change M.internal j i (lam j • f j) = 0 at hr
      rw [map_smul, smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (g.2 j) = 0
      rw [hc j, map_smul, hi, smul_zero]
    · have hx := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mp hr
      change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0
      simpa only [hc, map_smul, smul_eq_mul, hx] using hcl b


def responseLinear (m : J → B → ℝ) : (J → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun c := fun b => ∑ j, c j * m j b
  map_add' c d := by ext b; simp [add_mul, sum_add_distrib]
  map_smul' a c := by ext b; simp [mul_assoc, mul_sum]

def Data.closureLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    ((D → ℝ) × (J → ℝ)) →ₗ[ℝ] (B → ℝ) where
  toFun y := M.boundary y.1 + responseLinear m y.2
  map_add' x y := by simp; abel
  map_smul' a x := by simp [smul_add]

def Data.closedRelations (M : Data B J K D I X) (m : J → B → ℝ) :
    Submodule ℝ ((D → ℝ) × (J → ℝ)) := LinearMap.ker (M.closureLinear m)

@[simp] theorem mem_closedRelations (w : D → ℝ) (c : J → ℝ) :
    (w, c) ∈ M.closedRelations m ↔ M.Closure m w c := by
  simp only [Data.closedRelations, LinearMap.mem_ker, Data.closureLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Data.Closure, responseLinear, Pi.add_apply,
    funext_iff, Pi.zero_apply]

def Data.relationLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    (J → ℝ) →ₗ[ℝ] ((B → ℝ) ⧸ LinearMap.range M.boundary) :=
  (LinearMap.range M.boundary).mkQ ∘ₗ responseLinear m

theorem closure_mem_relationKernel {w : D → ℝ} {c : J → ℝ}
    (hc : M.Closure m w c) : c ∈ LinearMap.ker (M.relationLinear m) := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  refine ⟨-w, ?_⟩
  ext b
  have h := hc b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk]
  linarith

theorem exists_closure_of_relationKernel {c : J → ℝ}
    (hc : c ∈ LinearMap.ker (M.relationLinear m)) : ∃ w, M.Closure m w c := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0 at hc
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨-w, ?_⟩
  intro b
  have h := congrFun hw b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk] at h ⊢
  linarith

variable (hfinj : ∀ j, f j ≠ 0)

def closedToTight : M.closedRelations m →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 y.1.2 f,
    (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mpr
      ⟨y.1.2, fun _ => rfl, (mem_closedRelations M m _ _).mp y.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, smul_smul, mul_assoc]

include hfinj in
theorem closedToTight_injective : Function.Injective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j) he
    change x.1.2 j • f j = y.1.2 j • f j at h
    have hnonzero : ∃ k, f j k ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hfinj j (funext hn)
    obtain ⟨k, hk⟩ := hnonzero
    have hh := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

theorem closedToTight_surjective : Function.Surjective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
  intro g
  obtain ⟨c, hc, hcl⟩ := (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mp g.2
  refine ⟨⟨(g.1.1, c), (mem_closedRelations M m _ _).mpr hcl⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    exact (hc j).symm

def closedTightEquiv : M.closedRelations m ≃ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) :=
  LinearEquiv.ofBijective (closedToTight M f m hmin hatt z lam hlam hclose hprivate)
    ⟨closedToTight_injective M f m hmin hatt z lam hlam hclose hprivate hfinj,
      closedToTight_surjective M f m hmin hatt z lam hlam hclose hprivate⟩

variable (hboundary : Function.Injective M.boundary)

def closedToRelation : M.closedRelations m →ₗ[ℝ] LinearMap.ker (M.relationLinear m) where
  toFun y := ⟨y.1.2, closure_mem_relationKernel M m ((mem_closedRelations M m _ _).mp y.2)⟩
  map_add' x y := rfl
  map_smul' a x := rfl

include hboundary in
theorem closedToRelation_injective : Function.Injective (closedToRelation M m) := by
  intro x y hxy
  have hc : x.1.2 = y.1.2 := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · apply hboundary
    ext b
    have hx := ((mem_closedRelations M m _ _).mp x.2) b
    have hy := ((mem_closedRelations M m _ _).mp y.2) b
    rw [hc] at hx
    linarith
  · exact hc

theorem closedToRelation_surjective : Function.Surjective (closedToRelation M m) := by
  intro c
  obtain ⟨w, hw⟩ := exists_closure_of_relationKernel M m c.2
  exact ⟨⟨(w, c.1), (mem_closedRelations M m _ _).mpr hw⟩, rfl⟩

def closedRelationEquiv : M.closedRelations m ≃ₗ[ℝ] LinearMap.ker (M.relationLinear m) :=
  LinearEquiv.ofBijective (closedToRelation M m)
    ⟨closedToRelation_injective M m hboundary, closedToRelation_surjective M m⟩

/-- The exact linear equivalence asserted by response gluing: every global tight
variation corresponds to exactly one relation among branch response classes. -/
def tightRelationEquiv : Polyhedral.tightKernel M.row (assemble z lam f) ≃ₗ[ℝ]
    LinearMap.ker (M.relationLinear m) :=
  (closedTightEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj).symm.trans
    (closedRelationEquiv M m hboundary)

include hmin hatt hlam hclose hprivate hfinj hboundary in
/-- The dimension assertion holds for the complete tight kernel, including all
rows, with the boundary quotient and branch scales explicitly constructed. -/
theorem tightKernel_finrank_eq_relationKernel :
    Module.finrank ℝ (Polyhedral.tightKernel M.row (assemble z lam f)) =
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) :=
  (tightRelationEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj hboundary).finrank_eq


include hlam hfinj in
theorem assemble_ne_zero [Nonempty J] : assemble z lam f ≠ 0 := by
  intro he
  obtain ⟨j⟩ := ‹Nonempty J›
  have h := congrArg (fun g : Global J K D => g.2 j) he
  change lam j • f j = 0 at h
  exact hfinj j ((smul_eq_zero.mp h).resolve_left (ne_of_gt (hlam j)))

include hmin hatt hinternal hlam hclose hprivate hfinj hboundary in
/-- The extremality equivalence in the positive response gluing theorem. The
finite inequality cone is required to be pointed, as the normalized graphical
cone is by its proved zero-elemental-difference criterion. -/
theorem extreme_iff_relation_finrank_one
    (hpointed : Polyhedral.Pointed M.row) :
    Polyhedral.ExtremeRay M.row (assemble z lam f) ↔
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1 := by
  classical
  by_cases hJ : Nonempty J
  · letI := hJ
    have hn := assemble_ne_zero f z lam hlam hfinj
    have hdim := tightKernel_finrank_eq_relationKernel M f m hmin hatt z lam hlam hclose
      hprivate hfinj hboundary
    constructor
    · intro he
      rw [← hdim, he.tightKernel_eq_span]
      exact finrank_span_singleton hn
    · intro hd
      apply Polyhedral.extremeRay_of_tightKernel hpointed
        (assembled_nonnegative M f m hmin hinternal z lam hlam hclose) hn
      exact eq_span_singleton_of_mem_of_finrank_eq_one (hdim.trans hd)
        (Polyhedral.self_mem_tightKernel M.row (assemble z lam f)) hn
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    have hz0 : z = 0 := by
      apply hboundary
      ext b
      have h := hclose b
      simpa using h
    have hp0 : assemble z lam f = 0 := by
      apply Prod.ext
      · exact hz0
      · funext j
        exact isEmptyElim j
    have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_of_isEmpty] at hk
    constructor
    · intro he
      exact False.elim (he.2.1 hp0)
    · intro hd
      omega

include hlam hclose in
/-- In the extreme case the relation line is exactly the line through the
strictly positive vector of the construction. -/
theorem relationKernel_eq_span_scales
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    LinearMap.ker (M.relationLinear m) = Submodule.span ℝ {lam} := by
  have hmem := closure_mem_relationKernel M m hclose
  have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
  rw [hd, Module.finrank_fintype_fun_eq_card] at hk
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hne : lam ≠ 0 := by
    intro h
    obtain ⟨j⟩ := ‹Nonempty J›
    have hp := hlam j
    rw [h] at hp
    simp at hp
  exact eq_span_singleton_of_mem_of_finrank_eq_one hd hmem hne

include hboundary in
/-- The sharp universal branch-count bound follows from the dimension of the
boundary response quotient, with its boundary-coordinate subtraction justified
by injectivity of the boundary slack map. -/
theorem branch_count_le_capacity
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    Fintype.card J ≤ Fintype.card B - Fintype.card D + 1 := by
  have hrn := (LinearMap.ker (M.relationLinear m)).finrank_quotient_add_finrank
  rw [(M.relationLinear m).quotKerEquivRange.finrank_eq, hd,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hrle := Submodule.finrank_le (LinearMap.range (M.relationLinear m))
  have hquot := (LinearMap.range M.boundary).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hboundary, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hquot
  omega

end Gluing
end GraphicalZonotopes

end
end
end BundlePart90

section BundlePart91
/- Source: Papers/GraphicalZonotopes/SeparatorCoordinates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- A partition of the private vertices across an induced boundary. These
conditions are precisely disjoint coverage and absence of edges between
private parts; no clique or rigidity assumption is made on the boundary. -/
structure Partition (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) : Prop where
  boundary_disjoint : ∀ j,Disjoint B (A j)
  private_disjoint : Pairwise (fun j k => Disjoint (A j) (A k))
  cover : ∀ v : V,v∈B ∨ ∃ j,v∈A j
  no_cross_edge : ∀ j k u v,u∈A j → v∈A k → G.Adj u v → j=k

variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Every clique not contained in the boundary has one and only one private
branch. This exhausts all original Möbius coordinates. -/
theorem Partition.clique_unique_branch (h : Partition G B A)
    (C : CliqueIndex G) (hC : ¬C.1⊆B) : ∃! j : J,C.1⊆B∪A j := by
  obtain ⟨u,huC,huB⟩ := Finset.not_subset.mp hC
  obtain ⟨j,huj⟩ := (h.cover u).resolve_left huB
  have hsub : C.1⊆B∪A j := by
    intro v hvC
    by_cases hvB : v∈B
    · exact mem_union_left _ hvB
    · obtain ⟨k,hvk⟩ := (h.cover v).resolve_left hvB
      by_cases hjk : j=k
      · subst k
        exact mem_union_right _ hvk
      · have huv : u≠ v := by
          intro he
          have hdis := Finset.disjoint_left.mp (h.private_disjoint hjk)
          exact hdis (he ▸ huj) hvk
        have hedge := C.2.2 huC hvC huv
        exact False.elim (hjk (h.no_cross_edge j k u v huj hvk hedge))
  refine ⟨j,hsub,?_⟩
  intro k hk
  have huk : u∈A k := (mem_union.mp (hk huC)).resolve_left huB
  by_contra hkj
  exact Finset.disjoint_left.mp (h.private_disjoint hkj) huk huj

abbrev boundaryIndex (G : SimpleGraph V) (B : Finset V) :=
  {C : CliqueIndex G // C.1⊆B}

abbrev privateIndex (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {C : CliqueIndex G // ¬C.1⊆B ∧ C.1⊆B∪A j}

noncomputable instance boundaryIndexFintype : Fintype (boundaryIndex G B) := by
  classical
  unfold boundaryIndex
  infer_instance

noncomputable instance privateIndexFintype (j : J) : Fintype (privateIndex G B A j) := by
  classical
  unfold privateIndex
  infer_instance

def branchOf (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) : J :=
  Classical.choose (h.clique_unique_branch C hC)

theorem branchOf_spec (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) :
    C.1⊆B∪A (branchOf h C hC) :=
  (Classical.choose_spec (h.clique_unique_branch C hC)).1

theorem branchOf_eq (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B)
    {j : J} (hj : C.1⊆B∪A j) : branchOf h C hC=j := by
  exact ((Classical.choose_spec (h.clique_unique_branch C hC)).2 j hj).symm

def classify (h : Partition G B A) (C : CliqueIndex G) :
    boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) := by
  classical
  exact if hC : C.1⊆B then Sum.inl ⟨C,hC⟩ else
    Sum.inr ⟨branchOf h C hC,⟨C,hC,branchOf_spec h C hC⟩⟩

def forget : boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) → CliqueIndex G
  | Sum.inl C => C.1
  | Sum.inr ⟨_,C⟩ => C.1

@[simp] theorem forget_classify (h : Partition G B A) (C : CliqueIndex G) :
    forget (classify h C)=C := by
  classical
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_boundary (h : Partition G B A) (C : boundaryIndex G B) :
    classify h C.1=Sum.inl C := by
  classical
  simp [classify,C.2]

@[simp] theorem classify_private (h : Partition G B A) (j : J)
    (C : privateIndex G B A j) : classify h C.1=Sum.inr ⟨j,C⟩ := by
  classical
  unfold classify
  rw [dif_neg C.2.1]
  have hj := branchOf_eq h C.1 C.2.1 C.2.2
  congr 1
  apply Sigma.ext hj
  change (⟨C.1, _⟩ : {D : CliqueIndex G // ¬D.1⊆B ∧ D.1⊆B∪A (branchOf h C.1 C.2.1)}) ≍ C
  exact (Subtype.heq_iff_coe_eq (by intro D; rw [hj])).mpr rfl

/-- Exact reindexing of every clique coordinate into one boundary coordinate
or one private coordinate. No zero slots or exceptional cliques are omitted. -/
def indexEquiv (h : Partition G B A) :
    CliqueIndex G ≃ boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) where
  toFun := classify h
  invFun := forget
  left_inv := forget_classify h
  right_inv c := by
    cases c with
    | inl C => exact classify_boundary h C
    | inr C => rcases C with ⟨j,C⟩; exact classify_private h j C

def joinCoordinates (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) :
    CliqueIndex G → ℝ := fun C =>
  match classify h C with
  | Sum.inl D => x.1 D
  | Sum.inr ⟨j,D⟩ => x.2 j D

@[simp] theorem joinCoordinates_boundary (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (C : boundaryIndex G B) : joinCoordinates h x C.1=x.1 C := by
  simp only [joinCoordinates,classify_boundary]

@[simp] theorem joinCoordinates_private (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (j : J) (C : privateIndex G B A j) : joinCoordinates h x C.1=x.2 j C := by
  simp only [joinCoordinates,classify_private]

/-- The complete linear coordinate dictionary, before inequalities are
translated. This is an actual equivalence, rather than a dimension assumption. -/
def coordinateEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      (CliqueIndex G → ℝ) where
  toFun := joinCoordinates h
  invFun y := (fun C => y C.1,fun _ C => y C.1)
  left_inv x := by
    apply Prod.ext
    · funext C
      exact joinCoordinates_boundary h x C
    · funext j C
      exact joinCoordinates_private h x j C
  right_inv y := by
    funext C
    have hf := forget_classify h C
    unfold joinCoordinates
    cases hc : classify h C with
    | inl D =>
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
    | inr D =>
      rcases D with ⟨j,D⟩
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
  map_add' x y := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]
  map_smul' a x := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]

/-- Composition with the actual graphical Möbius equivalence gives the
original normalized set functions, not an abstract stand-in cone. -/
def functionEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      graphicalFunctionSpace G :=
  (coordinateEquiv h).trans (graphicalCoordinatesEquiv G)

/-- The graph after deleting the boundary, with its usual induced adjacency. -/
def outsideGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph {v : V // v∉B} :=
  G.induce {v : V | v∉B}

def componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ hv : v∉B,
    (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c)

@[simp] theorem mem_componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) (v : V) :
    v∈componentPart G B c ↔ ∃ hv : v∉B,
      (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c := by
  classical
  simp [componentPart]

noncomputable instance componentFintype (G : SimpleGraph V) (B : Finset V) :
    Fintype ((outsideGraph G B).ConnectedComponent) := Fintype.ofFinite _

/-- Every actual induced separator supplies the partition used by the
coordinate dictionary, including empty boundaries and no private vertices. -/
theorem componentPartition (G : SimpleGraph V) (B : Finset V) :
    Partition G B (componentPart G B) := by
  classical
  constructor
  · intro c
    apply Finset.disjoint_left.mpr
    intro v hvB hvc
    obtain ⟨hv,_⟩ := (mem_componentPart G B c v).mp hvc
    exact hv hvB
  · intro c d hcd
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    obtain ⟨hv,hc⟩ := (mem_componentPart G B c v).mp hvc
    obtain ⟨hv',hd⟩ := (mem_componentPart G B d v).mp hvd
    exact hcd (hc.symm.trans hd)
  · intro v
    by_cases hv : v∈B
    · exact Or.inl hv
    · refine Or.inr ⟨(outsideGraph G B).connectedComponentMk ⟨v,hv⟩,?_⟩
      exact (mem_componentPart G B _ v).mpr ⟨hv,rfl⟩
  · intro c d u v hu hv hadj
    obtain ⟨huB,huc⟩ := (mem_componentPart G B c u).mp hu
    obtain ⟨hvB,hvd⟩ := (mem_componentPart G B d v).mp hv
    have he : (outsideGraph G B).connectedComponentMk ⟨u,huB⟩=
        (outsideGraph G B).connectedComponentMk ⟨v,hvB⟩ :=
      SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)
    exact huc.symm.trans (he.trans hvd)

end Separator
end GraphicalZonotopes

end
end
end BundlePart91

section BundlePart92
/- Source: Papers/GraphicalZonotopes/CoefficientSupport.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set of variables containing the support of every nonzero Möbius slot. -/
def CoefficientSupportedOn (T : Finset V) (y : SetFunction V) : Prop :=
  ∀ C : Finset V,¬C⊆T → y C=0

/-- Conditioning outside a coefficient support has no effect on any genuine
elemental difference. The endpoints need not themselves lie in the support. -/
theorem delta_zeta_inter_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=delta (zeta y) u v (S∩T) := by
  classical
  have hu' : u∉S∩T := fun h => hu (mem_inter.mp h).1
  have hv' : v∉S∩T := fun h => hv (mem_inter.mp h).1
  rw [zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,
    delta_setMonomial huv hu' hv']
  by_cases hCT : C⊆T
  · have he : C⊆insert u (insert v S) ↔ C⊆insert u (insert v (S∩T)) := by
      constructor
      · intro h w hwC
        have hw := h hwC
        simp only [mem_insert] at hw ⊢
        rcases hw with hwu | hwv | hwS
        · exact Or.inl hwu
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,hCT hwC⟩))
      · exact fun h => h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))
    simp only [he]
  · rw [hy C hCT]
    simp

/-- A variable outside the coefficient support cannot occur in a nonzero
edge slack. This uses the full Möbius transform, not a selected row family. -/
theorem delta_zeta_zero_of_outside_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠ v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=0 := by
  apply (nonedge_coefficients_zero_iff y huv).mpr ?_ S hu hv
  intro C huC hvC
  exact hy C (fun h => huT (h huC))

theorem delta_inter_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=delta z u v (S∩T) := by
  simpa only [zeta_mobius] using delta_zeta_inter_support hz huv hu hv

theorem delta_zero_of_outside_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠ v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=0 := by
  simpa only [zeta_mobius] using delta_zeta_zero_of_outside_support hz huv huT hu hv

end GraphicalZonotopes

end
end
end BundlePart92

section BundlePart93
/- Source: Papers/GraphicalZonotopes/SeparatorPieces.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

abbrev Coordinates (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) :=
  (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)

def boundaryEmbed : (boundaryIndex G B → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun z := (z,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def privateEmbed (j : J) : (privateIndex G B A j → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun g := (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)
  map_add' f g := by
    apply Prod.ext
    · simp
    · exact map_add (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) f g
  map_smul' a f := by
    apply Prod.ext
    · simp
    · exact map_smul (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) a f

def globalFunctionMap (h : Partition G B A) : Coordinates G B A →ₗ[ℝ] SetFunction V :=
  (graphicalFunctionSpace G).subtype.comp (functionEquiv h).toLinearMap

def boundaryFunctionMap (h : Partition G B A) :
    (boundaryIndex G B → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp boundaryEmbed

def privateFunctionMap (h : Partition G B A) (j : J) :
    (privateIndex G B A j → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp (privateEmbed j)

theorem coordinates_decompose (x : Coordinates G B A) :
    x=boundaryEmbed x.1+∑ j : J,privateEmbed j (x.2 j) := by
  classical
  apply Prod.ext
  · simp [boundaryEmbed,privateEmbed, Prod.fst_sum, Prod.snd_sum]
  · funext j C
    simp [boundaryEmbed,privateEmbed,LinearMap.single_apply,Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]

/-- The full original function is the sum of its boundary function and every
private branch function, with no discarded Möbius coordinates. -/
theorem function_decompose (h : Partition G B A) (x : Coordinates G B A) :
    globalFunctionMap h x=boundaryFunctionMap h x.1+
      ∑ j : J,privateFunctionMap h j (x.2 j) := by
  have he := congrArg (globalFunctionMap h) (coordinates_decompose x)
  simpa only [map_add,map_sum,boundaryFunctionMap,privateFunctionMap,
    LinearMap.comp_apply] using he

@[simp] theorem mobius_globalFunctionMap (h : Partition G B A) (x : Coordinates G B A) :
    mobius (globalFunctionMap h x)=coefficientsFromCoordinates G (joinCoordinates h x) := by
  change mobius (zeta (coefficientsFromCoordinates G (joinCoordinates h x)))=_
  exact mobius_zeta _

theorem boundaryFunction_supported (h : Partition G B A) (z : boundaryIndex G B → ℝ) :
    CoefficientSupportedOn B (mobius (boundaryFunctionMap h z)) := by
  classical
  intro C hCB
  change mobius (globalFunctionMap h (z,0)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_supported (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) :
    CoefficientSupportedOn (B∪A j) (mobius (privateFunctionMap h j g)) := by
  classical
  intro C hCA
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B := fun hc => hCA (hc.trans subset_union_left)
    have hbranch : branchOf h ⟨C,hcl⟩ hCB≠ j := by
      intro he
      have hc := branchOf_spec h ⟨C,hcl⟩ hCB
      rw [he] at hc
      exact hCA hc
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB,
      LinearMap.single_apply,Pi.single_eq_of_ne hbranch]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_boundary_coefficients_zero (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {C : Finset V} (hCB : C⊆B) :
    mobius (privateFunctionMap h j g) C=0 := by
  classical
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C <;>
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]

/-- On a private edge, the boundary contribution and every other branch
contribution vanish for all conditioning sets. -/
theorem delta_private_edge_decompose (h : Partition G B A) (x : Coordinates G B A)
    (j : J) {u v : V} (huA : u∈A j) (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (globalFunctionMap h x) u v S=
      delta (privateFunctionMap h j (x.2 j)) u v S := by
  classical
  have huB : u∉B := fun hB => Finset.disjoint_left.mp (h.boundary_disjoint j) hB huA
  rw [function_decompose,delta_add,delta_sum]
  rw [delta_zero_of_outside_mobius_support (boundaryFunction_supported h x.1) huv huB hu hv,
    zero_add]
  apply sum_eq_single j
  · intro k hk hkj
    have huBA : u∉B∪A k := by
      intro hm
      rcases mem_union.mp hm with hB | hkA
      · exact huB hB
      · exact Finset.disjoint_left.mp (h.private_disjoint hkj) hkA huA
    exact delta_zero_of_outside_mobius_support (privateFunction_supported h k (x.2 k))
      huv huBA hu hv
  · simp

/-- Every private response depends only on its actual branch conditioning
bits, as required by the separator row model. -/
theorem delta_private_inter (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (privateFunctionMap h j g) u v S=
      delta (privateFunctionMap h j g) u v (S∩(B∪A j)) :=
  delta_inter_mobius_support (privateFunction_supported h j g) huv hu hv

end Separator
end GraphicalZonotopes

end
end
end BundlePart93
