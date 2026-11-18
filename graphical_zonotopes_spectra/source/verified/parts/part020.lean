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

public import verified.parts.part019
import all verified.parts.part019

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart282
/- Source: Papers/GraphicalZonotopes/FourPartCompletion.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes.FourPartCompletion
open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

def vertices (v : Fin 4 → V) : Finset V := univ.image v

def Face (C : Finset (Finset V)) (v : Fin 4 → V) : Prop := vertices v ∈ C

def Thin (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v i y) → x=y

def SquareClosed (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i j, i≠ j → ∀ x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v j y) →
    x≠ y ∧ Face C (update (update v i x) j y)

@[simp] theorem mem_vertices (v : Fin 4 → V) (x : V) :
    x ∈ vertices v ↔ ∃ i, v i=x := by simp [vertices]

theorem self_mem_vertices (v : Fin 4 → V) (i : Fin 4) : v i∈vertices v :=
  (mem_vertices v _).mpr ⟨i,rfl⟩

theorem vertices_card (v : Fin 4 → V) (hv : Injective v) : (vertices v).card=4 := by
  simp [vertices, card_image_of_injective _ hv]

theorem vertices_update (v : Fin 4 → V) (hv : Injective v) (i : Fin 4) (x : V) :
    vertices (update v i x)=insert x ((vertices v).erase (v i)) := by
  ext a
  simp only [mem_vertices,mem_insert,mem_erase]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j; exact Or.inl (by simpa using hj.symm)
    · right
      have hval : v j=a := by simpa [update_of_ne hji] using hj
      exact ⟨fun he => hji (hv (hval.trans he)),⟨j,hval⟩⟩
  · rintro (rfl | ⟨ha,j,hj⟩)
    · exact ⟨i,by simp⟩
    · refine ⟨j,?_⟩
      have hji : j≠ i := fun he => ha (by simpa [he] using hj.symm)
      simpa [update_of_ne hji] using hj

def rootParts (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) : Finset V :=
  insert (v i) (univ.filter (fun x => x∉vertices v ∧ Face C (update v i x)))

@[simp] theorem mem_rootParts (C : Finset (Finset V)) (v : Fin 4 → V)
    (i : Fin 4) (x : V) :
    x∈rootParts C v i ↔ x=v i ∨ x∉vertices v ∧ Face C (update v i x) := by
  simp [rootParts]

theorem root_mem_part (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) :
    v i∈rootParts C v i := (mem_rootParts _ _ _ _).mpr (Or.inl rfl)

theorem rootParts_small {C : Finset (Finset V)} (hthin : Thin C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) (i : Fin 4) :
    (rootParts C v i).card=1 ∨ (rootParts C v i).card=2 := by
  let A := univ.filter (fun x => x∉vertices v ∧ Face C (update v i x))
  have hsub : A.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    exact hthin v hv hf i x y hx'.1 hy'.1 hx'.2 hy'.2)
  have hnot : v i∉A := by
    intro h
    exact (mem_filter.mp h).2.1 (self_mem_vertices v i)
  have hc : (rootParts C v i).card=A.card+1 := card_insert_of_notMem hnot
  omega

theorem rootParts_disjoint {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) :
    ∀ i j, i≠ j → Disjoint (rootParts C v i) (rootParts C v j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases (mem_rootParts _ _ _ _).mp hxi with rfl | ⟨hxi,hfi⟩
  · rcases (mem_rootParts _ _ _ _).mp hxj with he | ⟨hn,_⟩
    · exact hij (hv he)
    · exact hn (self_mem_vertices v i)
  · rcases (mem_rootParts _ _ _ _).mp hxj with rfl | ⟨hxj,hfj⟩
    · exact hxi (self_mem_vertices v j)
    · exact (hsq v hv hf i j hij x x hxi hxj hfi hfj).1 rfl

theorem injective_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠ j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i) : Injective v := by
  intro i j he
  by_contra hij
  exact (disjoint_left.mp (hA i j hij)) (hv i) (by rw [he]; exact hv j)

def patch (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) : V :=
  if i∈S then w i else v i

@[simp] theorem patch_empty (v w : Fin 4 → V) : patch v w ∅=v := by
  funext i; simp [patch]

theorem patch_insert (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) :
    patch v w (insert i S)=update (patch v w S) i (w i) := by
  funext j
  by_cases hji : j=i <;> simp [patch,hji]

theorem patch_mem_parts {A : Fin 4 → Finset V} {v w : Fin 4 → V}
    (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i) (S : Finset (Fin 4)) :
    ∀ i,patch v w S i∈A i := by
  intro i
  by_cases hi : i∈S <;> simp [patch,hi,hv i,hw i]

theorem outside_patch {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠ j → Disjoint (A i) (A j))
    {v w : Fin 4 → V} (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i)
    (S : Finset (Fin 4)) {i : Fin 4} (hi : i∉S) (hne : w i≠ v i) :
    w i∉vertices (patch v w S) := by
  rintro hx
  obtain ⟨j,hj⟩ := (mem_vertices _ _).mp hx
  have hm := patch_mem_parts hv hw S j
  by_cases hij : i=j
  · subst j
    exact hne (by simpa [patch,hi] using hj.symm)
  · exact (disjoint_left.mp (hA i j hij)) (hw i) (hj ▸ hm)

/-- Every independent combination of the root's elementary replacements is
present. The proof transports each remaining replacement across a square. -/
theorem fill_product {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i) : Face C w := by
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  let D : Finset (Fin 4) := univ.filter (fun i => w i≠ v i)
  have hD (i : Fin 4) : i∈D ↔ w i≠ v i := by simp [D]
  have hfill : ∀ S : Finset (Fin 4),S⊆D →
      Face C (patch v w S) ∧
      ∀ i∈D,i∉S → Face C (update (patch v w S) i (w i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simpa using hf,?_⟩
      intro i hi _
      have hn := (hD i).mp hi
      have hm := (mem_rootParts C v i (w i)).mp (hw i)
      simpa using (hm.resolve_left hn).2
    | @insert i S hi ih =>
      intro hSD
      have hS : S⊆D := fun j hj => hSD (mem_insert_of_mem hj)
      have hiD : i∈D := hSD (mem_insert_self _ _)
      obtain ⟨hface,hedge⟩ := ih hS
      have hnext := hedge i hiD hi
      refine ⟨by simpa [patch_insert] using hnext,?_⟩
      intro j hjD hj
      have hji : j≠ i := fun he => hj (by simp [he])
      have hjS : j∉S := fun hm => hj (mem_insert_of_mem hm)
      have hwi := outside_patch hA hvA hw S hi ((hD i).mp hiD)
      have hwj := outside_patch hA hvA hw S hjS ((hD j).mp hjD)
      have hinj := injective_of_parts hA (patch_mem_parts hvA hw S)
      have hsquare := (hsq _ hinj hface i j hji.symm (w i) (w j)
        hwi hwj hnext (hedge j hjD hjS)).2
      simpa [patch_insert] using hsquare
  have he : patch v w D=w := by
    funext i
    by_cases hi : w i=v i <;> simp [patch,D,hi]
  rw [← he]
  exact (hfill D (Subset.refl _)).1

theorem outside_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j,i≠ j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i)
    {i : Fin 4} {x : V} (hx : x∈A i) (hne : x≠ v i) :
    x∉vertices v := by
  rintro hm
  obtain ⟨j,hj⟩ := (mem_vertices v x).mp hm
  by_cases hij : i=j
  · subst j; exact hne hj.symm
  · exact (disjoint_left.mp (hA i j hij)) hx (hj ▸ hv j)

def changed (v w : Fin 4 → V) : Finset (Fin 4) := univ.filter (fun i => w i≠ v i)

@[simp] theorem mem_changed (v w : Fin 4 → V) (i : Fin 4) :
    i∈changed v w ↔ w i≠ v i := by simp [changed]

theorem changed_update (v w : Fin 4 → V) (j : Fin 4) :
    changed v (update w j (v j))=(changed v w).erase j := by
  ext i
  by_cases hij : i=j <;> simp [changed,hij]

/-- Any new facet adjacent to the root cube stays within its four parts.
An alleged new vertex is transported back to the root by square closure. -/
theorem replacement_mem_part {C : Finset (Finset V)}
    (hthin : Thin C) (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i)
    (i : Fin 4) (x : V) (hx : x∉vertices w)
    (hfx : Face C (update w i x)) : x∈rootParts C v i := by
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  have hmain : ∀ n : ℕ,∀ w : Fin 4 → V,(changed v w).card=n →
      (∀ i,w i∈A i) → ∀ i x,x∉vertices w →
      Face C (update w i x) → x∈A i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hc hw i x hx hfx
      have hwi : Injective w := injective_of_parts hA hw
      have hfw : Face C w := fill_product hsq hv hf hw
      by_cases hival : w i=v i
      · by_cases he : w=v
        · subst w
          exact (mem_rootParts C v i x).mpr (Or.inr ⟨hx,hfx⟩)
        · obtain ⟨j,hj⟩ : ∃ j,w j≠ v j := by
            by_contra h
            push_neg at h
            exact he (funext h)
          have hij : i≠ j := by intro h; subst j; exact hj hival
          let w' := update w j (v j)
          have hw' : ∀ k,w' k∈A k := by
            intro k
            by_cases hkj : k=j
            · subst k; simpa [w'] using hvA j
            · simpa [w',update_of_ne hkj] using hw k
          have hvj : v j∉vertices w := outside_of_parts hA hw (hvA j) (Ne.symm hj)
          have hfw' : Face C w' := fill_product hsq hv hf hw'
          have hs := hsq w hwi hfw i j hij x (v j) hx hvj hfx hfw'
          have hx' : x∉vertices w' := by
            rw [show vertices w'=insert (v j) ((vertices w).erase (w j)) from
              vertices_update w hwi j (v j)]
            intro hm
            rcases mem_insert.mp hm with he | he
            · exact hs.1 he
            · exact hx (mem_of_mem_erase he)
          have hfx' : Face C (update w' i x) := by
            simpa only [w',update_comm hij] using hs.2
          have hlt : (changed v w').card< n := by
            rw [show changed v w'=(changed v w).erase j from changed_update v w j]
            rw [← hc]
            exact card_erase_lt_of_mem ((mem_changed v w j).mpr hj)
          exact ih _ hlt w' rfl hw' i x hx' hfx'
      · have hvi : v i∉vertices w := outside_of_parts hA hw (hvA i) (Ne.symm hival)
        have hback : Face C (update w i (v i)) := by
          apply fill_product hsq hv hf
          change ∀ j,update w i (v i) j∈A j
          intro j
          by_cases hji : j=i
          · subst j; simp only [update_self]; exact hvA i
          · rw [update_of_ne hji]; exact hw j
        have he := hthin w hwi hfw i x (v i) hx hvi hfx hback
        simpa [he] using hvA i
  exact hmain _ w rfl hw i x hx hfx

theorem adjacent_replacement {D E : Finset V}
    (hD : D.card=4) (hE : E.card=4) (hne : D≠ E)
    (hinter : 3≤(D∩E).card) :
    ∃ u∈D,∃ x,x∉D ∧ E=insert x (D.erase u) := by
  have hle : (D∩E).card≤4 := (card_le_card inter_subset_left).trans_eq hD
  have hne4 : (D∩E).card≠4 := by
    intro he
    have hDI : D∩E=D := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hDE : D⊆E := by rw [← hDI]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hDE (by omega))
  have hthree : (D∩E).card=3 := by omega
  have hdiffD : (D\E).card=1 := by
    have hh := card_sdiff_add_card_inter D E
    omega
  have hdiffE : (E\D).card=1 := by
    have hh := card_sdiff_add_card_inter E D
    rw [inter_comm E D] at hh
    omega
  obtain ⟨u,hu⟩ := card_eq_one.mp hdiffD
  obtain ⟨x,hx⟩ := card_eq_one.mp hdiffE
  have hum : u∈D\E := by rw [hu]; simp
  have hxm : x∈E\D := by rw [hx]; simp
  refine ⟨u,(mem_sdiff.mp hum).1,x,(mem_sdiff.mp hxm).2,?_⟩
  ext a
  constructor
  · intro ha
    by_cases haD : a∈D
    · apply mem_insert_of_mem
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hum).2 (he ▸ ha),haD⟩
    · have he : a=x := by
        have hm : a∈E\D := mem_sdiff.mpr ⟨ha,haD⟩
        rw [hx] at hm
        exact mem_singleton.mp hm
      exact mem_insert.mpr (Or.inl he)
  · intro ha
    rcases mem_insert.mp ha with rfl | ha
    · exact (mem_sdiff.mp hxm).1
    · by_contra hn
      have hm : a∈D\E := mem_sdiff.mpr ⟨mem_of_mem_erase ha,hn⟩
      rw [hu] at hm
      exact (mem_erase.mp ha).1 (mem_singleton.mp hm)

theorem exists_vertices {D : Finset V} (hD : D.card=4) :
    ∃ v : Fin 4 → V,Injective v ∧ vertices v=D := by
  let e : Fin 4 ≃ D := (Finset.equivFinOfCardEq hD).symm
  let v : Fin 4 → V := fun i => (e i).val
  refine ⟨v,Subtype.val_injective.comp e.injective,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := (mem_vertices v x).mp hx
    exact (e i).property
  · intro hx
    apply (mem_vertices v x).mpr
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

/-- A connected family of tetrahedra with thin facets and commuting
facet replacements is exactly the Cartesian product of four parts of size
one or two. No bound on the ambient finite vertex type is assumed. -/
theorem cartesian_completion (C : Finset (Finset V))
    (hfour : ∀ D∈C,D.card=4) (hne : C.Nonempty)
    (hconn : (tetrahedronGraph C).Preconnected)
    (hthin : Thin C) (hsq : SquareClosed C) :
    ∃ A : Fin 4 → Finset V,
      (∀ i,(A i).card=1 ∨ (A i).card=2) ∧
      (∀ i j,i≠ j → Disjoint (A i) (A j)) ∧
      ∀ D : Finset V,D∈C ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w := by
  obtain ⟨D₀,hD₀⟩ := hne
  obtain ⟨v,hv,hev⟩ := exists_vertices (hfour D₀ hD₀)
  have hf : Face C v := by simpa [Face,hev] using hD₀
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  let P : {D : Finset V // D∈C} → Prop :=
    fun D => ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D.val=vertices w
  have hroot : P ⟨D₀,hD₀⟩ := ⟨v,root_mem_part C v,hev.symm⟩
  have hstep : ∀ D E : {D : Finset V // D∈C},
      (tetrahedronGraph C).Adj D E → P D → P E := by
    intro D E hadj hPD
    obtain ⟨w,hw,hew⟩ := hPD
    have hwi : Injective w := injective_of_parts hA hw
    have hDE : D.val≠ E.val := fun he => hadj.1 (Subtype.ext he)
    obtain ⟨u,hu,x,hx,he⟩ := adjacent_replacement
      (hfour _ D.property) (hfour _ E.property) hDE hadj.2
    rw [hew] at hu hx he
    obtain ⟨i,hi⟩ := (mem_vertices w u).mp hu
    subst u
    have hrep : E.val=vertices (update w i x) := by
      rw [vertices_update w hwi i x]
      exact he
    have hfx : Face C (update w i x) := by
      rw [Face,← hrep]
      exact E.property
    have hxi := replacement_mem_part hthin hsq hv hf hw i x hx hfx
    refine ⟨update w i x,?_,hrep⟩
    intro j
    change update w i x j∈A j
    by_cases hji : j=i
    · subst j; simp only [update_self]; exact hxi
    · rw [update_of_ne hji]; exact hw j
  refine ⟨A,rootParts_small hthin hv hf,hA,?_⟩
  intro D
  constructor
  · intro hD
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (hconn ⟨D₀,hD₀⟩ ⟨D,hD⟩)
    have hclosed : ∀ E : {E : Finset V // E∈C},
        Relation.ReflTransGen (tetrahedronGraph C).Adj ⟨D₀,hD₀⟩ E → P E := by
      intro E hr
      induction hr with
      | refl => exact hroot
      | tail _ ha ih => exact hstep _ _ ha ih
    exact hclosed ⟨D,hD⟩ hr
  · rintro ⟨w,hw,rfl⟩
    exact fill_product hsq hv hf hw

end GraphicalZonotopes.FourPartCompletion

end
end
end BundlePart282

section BundlePart283
/- Source: Papers/GraphicalZonotopes/UnitFamilyStructure.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.UnitFamilyStructure
open Finset Function FourPartCompletion BooleanFourPartStructure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {y : SetFunction V} {C : Finset (Finset V)}

theorem update_injective (v : Fin 4 → V) (hv : Injective v)
    (i : Fin 4) (x : V) (hx : x∉vertices v) : Injective (update v i x) := by
  intro a b he
  by_cases hai : a=i
  · subst a
    by_cases hbi : b=i
    · exact hbi.symm
    · have hxb : x=v b := by simpa [update_of_ne hbi] using he
      exact False.elim (hx (hxb.symm ▸ self_mem_vertices v b))
  · by_cases hbi : b=i
    · subst b
      have hax : v a=x := by simpa [update_of_ne hai] using he
      exact False.elim (hx (hax ▸ self_mem_vertices v a))
    · apply hv
      simpa [update_of_ne hai,update_of_ne hbi] using he

theorem thin_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C := by
  intro v hv hf i x z hx hz hX hZ
  by_contra hxz
  have hvi := self_mem_vertices v i
  have hD := vertices_card v hv
  have hT : ((vertices v).erase (v i)).card=3 := by rw [card_erase_of_mem hvi,hD]
  have hbase : y (insert (v i) ((vertices v).erase (v i)))≠0 := by
    rw [insert_erase hvi]
    exact ((hC _).mp hf).2
  have hx' : x∉(vertices v).erase (v i) := fun h => hx (mem_of_mem_erase h)
  have hz' : z∉(vertices v).erase (v i) := fun h => hz (mem_of_mem_erase h)
  have hix : v i≠ x := fun he => hx (he ▸ hvi)
  have hiz : v i≠ z := fun he => hz (he ▸ hvi)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv i z] at h
  exact three_extensions_impossible hG hy hb hT (by simp) hx' hz' hix hiz hxz hbase hX' hZ'

theorem squareClosed_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : SquareClosed C := by
  intro v hv hf i j hij x z hx hz hX hZ
  have hvi := self_mem_vertices v i
  have hvj := self_mem_vertices v j
  have hvij : v i≠ v j := fun he => hij (hv he)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v j)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv j z] at h
  obtain ⟨hxz,hnew⟩ := replacement_square hG hy hb (vertices_card v hv)
    ((hC _).mp hf).2 hvi hvj hvij hx hz hX' hZ'
  refine ⟨hxz,?_⟩
  have hvx : Injective (update v i x) := update_injective v hv i x hx
  have hznew : z∉vertices (update v i x) := by
    rw [vertices_update v hv i x]
    intro h
    rcases mem_insert.mp h with he | he
    · exact hxz he.symm
    · exact hz (mem_of_mem_erase he)
  apply (hC _).mpr
  refine ⟨vertices_card _ (update_injective _ hvx j z hznew),?_⟩
  have hvjx : v j≠ x := fun he => hx (he ▸ hvj)
  have he : vertices (update (update v i x) j z)=
      insert z (insert x (((vertices v).erase (v i)).erase (v j))) := by
    rw [vertices_update _ hvx j z,vertices_update v hv i x]
    simp only [update_of_ne (Ne.symm hij),erase_insert_of_ne (Ne.symm hvjx)]
  rwa [he]

/-- Exactly the two local structural properties required by the global
Cartesian completion theorem, for the actual nonzero coefficient family. -/
theorem structure_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C ∧ SquareClosed C :=
  ⟨thin_of_boolean hG hy hb hC,squareClosed_of_boolean hG hy hb hC⟩

end GraphicalZonotopes.UnitFamilyStructure

end
end
end BundlePart283

section BundlePart284
/- Source: Papers/GraphicalZonotopes/UnitLatticeGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- Integer lower-support values give integer elemental slacks in every context. -/
theorem integer_delta {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hz : IntegerValued z) (u v : V) (S : Finset V) :
    ∃ k : ℤ, delta z u v S = (k : ℝ) := by
  obtain ⟨a,ha⟩ := hz (insert u (insert v S))
  obtain ⟨b,hb⟩ := hz S
  obtain ⟨c,hc⟩ := hz (insert u S)
  obtain ⟨d,hd⟩ := hz (insert v S)
  refine ⟨a+b-c-d,?_⟩
  simp only [delta,ha,hb,hc,hd,Int.cast_add,Int.cast_sub]
  ring

theorem integer_between_zero_one {x : ℝ} (hx : ∃ k : ℤ,x=(k : ℝ))
    (h0 : 0≤ x) (h1 : x≤1) : x=0 ∨ x=1 := by
  obtain ⟨k,rfl⟩ := hx
  have hk0 : (0 : ℤ)≤ k := by exact_mod_cast h0
  have hk1 : k≤(1 : ℤ) := by exact_mod_cast h1
  have hk : k=0 ∨ k=1 := by omega
  rcases hk with rfl | rfl <;> norm_num

/-- Exact coefficient data extracted from the actual polytope hypotheses of
Theorem 9.5. These are proved conclusions, not assumptions added to that theorem. -/
structure CoefficientModel {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Set (Fin n → ℝ)) where
  function : SetFunction (Fin n)
  extreme : ExtremeSupermodular function
  integer : IntegerValued (mobius function)
  supported : CliqueSupported G (mobius function)
  boolean : ∀ u v : Fin n,u≠ v → ∀ S : Finset (Fin n),u∉S → v∉S →
    delta (zeta (mobius function)) u v S=0 ∨ delta (zeta (mobius function)) u v S=1
  nonempty : (family (mobius function)).Nonempty
  connected : (tetrahedronGraph (family (mobius function))).Preconnected
  covers : (family (mobius function)).biUnion id=univ
  directions : actualDirectionGraph Q=edgeGraph (mobius function)

/-- Unit dilation forces every integral elemental slack to be Boolean. The
proof retains the given ambient graph, all vertices, and the original translation. -/
theorem coefficient_model {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hcover,hactual⟩ := full_refined_support hn hG hext hzg hdim
  refine ⟨⟨z,hext,hzi.mobius,(mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩,
    ?_,hF,hconn,hcover,?_⟩⟩
  · intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  · rw [actualDirectionGraph_normalize,← hbody] at hactual
    exact hactual

/-- The ordinary polytope definition of indecomposability gives exactly the
same coefficient model; the necessary GP presentation is derived from the sum. -/
theorem coefficient_model_polytopal {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart284

section BundlePart285
/- Source: Papers/GraphicalZonotopes/LatticeTranslation.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lattice polytopes are allowed arbitrary real translations. -/
def TranslatedLatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ (P : Set (V → ℝ)) (t : V → ℝ), LatticePolytope P ∧ Q=t+ᵥP

theorem lowerSupport_vadd {Q : Set (V → ℝ)} (hQ : IsCompact Q)
    (hne : Q.Nonempty) (t : V → ℝ) :
    lowerSupport (t+ᵥQ)=modular t+lowerSupport Q := by
  rw [← singleton_add_eq_vadd,lowerSupport_add isCompact_singleton hQ (Set.singleton_nonempty _) hne]
  congr 1
  funext S
  simp [lowerSupport,modular]

theorem TranslatedLatticePolytope.compact {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : IsCompact Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  rw [← singleton_add_eq_vadd]
  exact isCompact_singleton.add hP.compact

theorem TranslatedLatticePolytope.convex {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : Convex ℝ Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  exact hP.convex.vadd t

theorem TranslatedLatticePolytope.integer_normalize_lowerSupport {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) (hne : Q.Nonempty) :
    IntegerValued (normalize (lowerSupport Q)) := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  have hnP : P.Nonempty := by
    obtain ⟨x,y,hy,hxy⟩ := hne
    exact ⟨y,hy⟩
  rw [lowerSupport_vadd hP.compact hnP,normalize_add,normalize_modular,zero_add]
  exact (hP.lowerSupport_integerValued hnP).normalize

theorem threeTree_integral_normalized_four_coefficients {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    ∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular (normalize f) := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  have hnormgraph : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hall := (threeTree_all_tetrahedra_nonzero hn hG hext hnormgraph hdim).2
  have hint := hint.mobius
  intro C hC
  obtain ⟨k,hk⟩ := hint C
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  rw [mobius_four_normalize hc] at hk
  refine ⟨k,?_,hk⟩
  intro hzero
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  have hnonzero := hall C hC
  rw [mobius_four_normalize hc] at hnonzero
  exact hnonzero (by simpa [hzero] using hk)

theorem threeTree_integral_normalized_lower_bound {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤ a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤ a := by
  classical
  have hcoeff := threeTree_integral_normalized_four_coefficients (by omega : 4≤ n) hG hQ hcQ hint hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  let z:=normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hint
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hzb : ∀ u v,u≠ v → G.Adj u v → ∀ S,u∉S → v∉S → delta z u v S≤ a := by
    intro u v huv hadj S hu hv
    rw [delta_normalize f huv hu hv]
    exact hbound u v huv hadj S hu hv
  have hedge : ∀ e∈edgeFamily G,
      (Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ)≤ a := by
    intro e he
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G e).mp he
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G huv).mp he
    have hb := threeTree_integral_slack_bound hG hzs hzi hzy hzb hadj
    have hs : (∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),
        |mobius z C|)=
        ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),|mobius f C| := by
      apply sum_congr rfl
      intro C hC
      have hc : C.card=4 := (mem_filter.mp (mem_filter.mp hC).1).2.1
      rw [mobius_four_normalize hc]
    rwa [hs] at hb
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hall⟩ := threeTree_all_tetrahedra_nonzero (by omega : 4≤ n) hG hext hzg hdim
  have hconn := (full_refined_support (by omega : 4≤ n) hG.cliqueFree_five hext hzg hdim).2.1
  rw [hF] at hconn
  have hnum : 3≤(tetrahedra G).card := by
    have hc:=hG.tetrahedra_card
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨e,hecard,hemany⟩ := connected_tetrahedra_pair_multiplicity (tetrahedra G)
    (fun C hC => (mem_filter.mp hC).2.1) hconn hnum
  have heG : e∈edgeFamily G := by
    obtain ⟨C,hC⟩ := card_pos.mp (show 0<((tetrahedra G).filter (fun C => e⊆C)).card by omega)
    obtain ⟨hC,heC⟩ := mem_filter.mp hC
    have hc := (mem_filter.mp hC).2.2
    exact (mem_edgeFamily G e).mpr ⟨hecard,fun u hu v hv huv => hc (heC hu) (heC hv) huv⟩
  have hsum : (3 : ℝ)≤
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C| := by
    calc
      (3 : ℝ)≤(((tetrahedra G).filter (fun C => e⊆C)).card : ℝ) := by exact_mod_cast hemany
      _ = ∑ C∈(tetrahedra G).filter (fun C => e⊆C),(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro C hC
        obtain ⟨k,hk,hvalue⟩ := hcoeff C (mem_filter.mp hC).1
        rw [hvalue]
        have hpos : (0 : ℤ) < abs k := abs_pos.mpr hk
        have hone : (1 : ℤ) ≤ abs k := by omega
        exact_mod_cast hone
  have hceil : (2 : ℤ)≤ Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) := by
    have hh : (1 : ℤ)< Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) :=
      Int.lt_ceil.mpr (by norm_num; linarith)
    omega
  have hcast : (2 : ℝ)≤(Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ) := by exact_mod_cast hceil
  exact ⟨hcast.trans (hedge e heG),hcoeff,hedge⟩

/-- Theorem 9.1 in the full translation-invariant range explicitly stated in
its introduction: every real translate of a lattice polytope is permitted.
All tetrahedral coefficients and every edgewise ceiling retain their literal
values on the original translated body. -/
theorem threeTree_translated_lattice_lower_bound {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤ a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤ a := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  exact threeTree_integral_normalized_lower_bound hn hG hQ.compact hQ.convex
    (hQ.integer_normalize_lowerSupport hi.1)
    ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd ha ⟨R,hR,hcR,hnR,he⟩

end GraphicalZonotopes

end
end
end BundlePart285

section BundlePart286
/- Source: Papers/GraphicalZonotopes/UnitTranslatedGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- The unit-lattice coefficient model extends to arbitrary real translations.
Its Möbius coefficients and Boolean rows come from integral normalized support. -/
theorem coefficient_model_translated {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hQ.integer_normalize_lowerSupport hi.1
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hcover,hactual⟩ := full_refined_support hn hG hext hzg hdim
  refine ⟨⟨z,hext,hzi.mobius,(mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩,
    ?_,hF,hconn,hcover,?_⟩⟩
  · intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  · rw [actualDirectionGraph_normalize,← hbody] at hactual
    exact hactual

/-- The ordinary polytope definition of indecomposability gives exactly the
same coefficient model; the necessary GP presentation is derived from the sum. -/
theorem coefficient_model_translated_polytopal {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model_translated hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart286

section BundlePart287
/- Source: Papers/GraphicalZonotopes/FourPartGraphRecognition.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace FourPartGraphRecognition
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

structure FourParts (V : Type*) [Fintype V] [DecidableEq V] where
  parts : Fin 4 → Finset V
  nonempty : ∀ i,(parts i).Nonempty
  disjoint : ∀ i j,i≠ j → Disjoint (parts i) (parts j)
  covers : ∀ v : V,∃ i,v∈parts i

namespace FourParts
variable (P : FourParts V)

def color (v : V) : Fin 4 := Classical.choose (P.covers v)

theorem color_mem (v : V) : v∈P.parts (P.color v) := Classical.choose_spec (P.covers v)

theorem color_eq_of_mem {v : V} {i : Fin 4} (hv : v∈P.parts i) : P.color v=i := by
  by_contra hi
  exact Finset.disjoint_left.mp (P.disjoint _ _ hi) (P.color_mem v) hv

def chosen (i : Fin 4) : V := Classical.choose (P.nonempty i)

theorem chosen_mem (i : Fin 4) : P.chosen i∈P.parts i := Classical.choose_spec (P.nonempty i)

theorem different_of_mem {i j : Fin 4} (hij : i≠ j) {u v : V}
    (hu : u∈P.parts i) (hv : v∈P.parts j) : u≠ v := by
  intro he
  exact Finset.disjoint_left.mp (P.disjoint i j hij) hu (he.symm ▸ hv)

def transversal (u v : V) : Fin 4 → V :=
  fun i => if i=P.color u then u else if i=P.color v then v else P.chosen i

theorem transversal_mem (u v : V) (i : Fin 4) : P.transversal u v i∈P.parts i := by
  unfold transversal
  split_ifs with hi hj
  · simpa only [hi] using P.color_mem u
  · simpa only [hj] using P.color_mem v
  · exact P.chosen_mem i

theorem transversal_left (u v : V) : P.transversal u v (P.color u)=u := by
  simp [transversal]

theorem transversal_right {u v : V} (h : P.color u≠ P.color v) :
    P.transversal u v (P.color v)=v := by simp [transversal,Ne.symm h]

theorem choice_injective (w : Fin 4 → V) (hw : ∀ i,w i∈P.parts i) :
    Function.Injective w := by
  intro i j he
  by_contra hij
  exact P.different_of_mem hij (hw i) (hw j) he

def coordinateEquiv : (Σ i : Fin 4,Fin ((P.parts i).card)) ≃ V := by
  let e (i : Fin 4) : Fin ((P.parts i).card) ≃ {v : V // v∈P.parts i} :=
    Fintype.equivOfCardEq (by simp)
  let f : (Σ i : Fin 4,Fin ((P.parts i).card)) → V := fun x => (e x.1 x.2).1
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hi : i=j := by
      have hci := P.color_eq_of_mem (e i a).2
      have hcj := P.color_eq_of_mem (e j b).2
      exact hci.symm.trans ((congrArg P.color he).trans hcj)
    subst j
    have hab : a=b := (e i).injective (Subtype.ext he)
    subst b
    rfl
  · intro v
    refine ⟨⟨P.color v,(e (P.color v)).symm ⟨v,P.color_mem v⟩⟩,?_⟩
    exact congrArg Subtype.val ((e (P.color v)).apply_symm_apply _)

theorem coordinateEquiv_mem (x : Σ i : Fin 4,Fin ((P.parts i).card)) :
    P.coordinateEquiv x∈P.parts x.1 := by
  change (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).1∈P.parts x.1
  exact (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).2

theorem card_eq : Fintype.card V=∑ i : Fin 4,(P.parts i).card := by
  rw [← Fintype.card_congr P.coordinateEquiv,Fintype.card_sigma]
  simp

theorem card_le_eight (hsize : ∀ i,(P.parts i).card≤2) : Fintype.card V≤8 := by
  rw [P.card_eq]
  calc
    ∑ i : Fin 4,(P.parts i).card ≤ ∑ _i : Fin 4,2 := sum_le_sum (fun i _ => hsize i)
    _ = 8 := by norm_num

end FourParts

def unionGraph (F : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u≠ v ∧ ∃ D∈F,u∈D ∧ v∈D
  symm := ⟨by rintro u v ⟨hne,D,hD,hu,hv⟩;exact ⟨Ne.symm hne,D,hD,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def ProductFamily (F : Finset (Finset V)) (A : Fin 4 → Finset V) : Prop :=
  ∀ D : Finset V,D∈F ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w

variable (P : FourParts V) (F : Finset (Finset V))

theorem unionGraph_adj_iff (hprod : ProductFamily F P.parts) (u v : V) :
    (unionGraph F).Adj u v ↔ P.color u≠ P.color v := by
  constructor
  · rintro ⟨hne,D,hD,hu,hv⟩ he
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    have hci : P.color u=i := P.color_eq_of_mem (hi ▸ hw i)
    have hcj : P.color v=j := P.color_eq_of_mem (hj ▸ hw j)
    have hij : i=j := hci.symm.trans (he.trans hcj)
    rw [← hij] at hj
    exact hne (hi.symm.trans hj)
  · intro hne
    refine ⟨fun he => hne (congrArg P.color he),univ.image (P.transversal u v),?_,?_,?_⟩
    · exact (hprod _).mpr ⟨P.transversal u v,P.transversal_mem u v,rfl⟩
    · exact mem_image.mpr ⟨P.color u,mem_univ _,P.transversal_left u v⟩
    · exact mem_image.mpr ⟨P.color v,mem_univ _,P.transversal_right hne⟩

theorem unionGraph_le {G : SimpleGraph V} (hcl : ∀ D∈F,G.IsClique D) : unionGraph F≤ G := by
  rintro u v ⟨hne,D,hD,hu,hv⟩
  exact hcl D hD hu hv hne

/-- A K5-free supergraph of a full four-part product has no additional edge:
any within-part edge, together with one vertex from each other part, is a K5. -/
theorem ambient_eq {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) : unionGraph F=G := by
  apply le_antisymm (unionGraph_le F hcl)
  intro u v huv
  apply (unionGraph_adj_iff P F hprod u v).mpr
  intro hecolor
  let w := P.transversal u u
  have hw : ∀ i,w i∈P.parts i := P.transversal_mem u u
  let D := univ.image w
  have hDF : D∈F := (hprod D).mpr ⟨w,hw,rfl⟩
  have hDc : D.card=4 := by
    dsimp only [D]
    rw [card_image_of_injective _ (P.choice_injective w hw)]
    simp
  have hvD : v∉D := by
    intro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    have hci : P.color v=i := P.color_eq_of_mem (hi ▸ hw i)
    have hii : i=P.color u := hci.symm.trans hecolor.symm
    have hwi : w i=u := by simpa only [hii] using P.transversal_left u u
    exact G.ne_of_adj huv (hwi.symm.trans hi)
  have hclE : G.IsClique ((insert v D : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hxD
    · rcases mem_insert.mp hy with rfl | hyD
      · exact False.elim (hxy rfl)
      · obtain ⟨i,_,hi⟩ := mem_image.mp hyD
        by_cases hii : i=P.color u
        · have hyu : y=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hyu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod x y).mpr
          have hcy : P.color y=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcy,← hecolor]
          exact Ne.symm hii
    · rcases mem_insert.mp hy with rfl | hyD
      · apply G.adj_symm
        obtain ⟨i,_,hi⟩ := mem_image.mp hxD
        by_cases hii : i=P.color u
        · have hxu : x=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hxu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod y x).mpr
          have hcx : P.color x=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcx,← hecolor]
          exact Ne.symm hii
      · exact hcl D hDF hxD hyD hxy
  have hb := hfour (insert v D) hclE
  rw [card_insert_of_notMem hvD,hDc] at hb
  omega

theorem graphIso {G : SimpleGraph V} (heq : unionGraph F=G)
    (hprod : ProductFamily F P.parts) :
    Nonempty (G ≃g fourPartite (fun i => (P.parts i).card)) := by
  let e := P.coordinateEquiv
  have iso : fourPartite (fun i => (P.parts i).card) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        rw [← heq,unionGraph_adj_iff P F hprod]
        rw [P.color_eq_of_mem (P.coordinateEquiv_mem x),P.color_eq_of_mem (P.coordinateEquiv_mem y)]
        rfl }
  exact ⟨iso.symm⟩

/-- The global family conclusion produces the precise ambient graph
classification, including its vertex bound and graph isomorphism. -/
theorem recognize {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hsize : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) :
    unionGraph F=G ∧ Fintype.card V≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  have heq := ambient_eq P F hprod hcl hfour
  exact ⟨heq,P.card_le_eight (fun i => by rcases hsize i with h | h <;> omega),
    (fun i => (P.parts i).card),hsize,graphIso P F heq hprod⟩

/-- A Cartesian family covering every vertex gives the needed literal
partition without adding an ambient coverage assumption. -/
theorem parts_of_cover (A : Fin 4 → Finset V)
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (hcover : F.biUnion id=univ) :
    ∃ P : FourParts V,P.parts=A := by
  refine ⟨⟨A,hne,hdis,?_⟩,rfl⟩
  intro v
  have hv : v∈F.biUnion id := by rw [hcover];exact mem_univ _
  obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
  obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
  obtain ⟨i,_,hi⟩ := mem_image.mp hv
  exact ⟨i,hi ▸ hw i⟩

end FourPartGraphRecognition
end GraphicalZonotopes

end
end
end BundlePart287

section BundlePart288
/- Source: Papers/GraphicalZonotopes/UnitLatticeClassification.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset RefinedTriangleComponents

namespace UnitLatticeGeometry

/-- The actual coefficient model has a Cartesian tetrahedral family. Its
coverage forces the entire ambient graph to be the corresponding four-partite
graph; no extra ambient edges or unused vertices remain. -/
theorem CoefficientModel.classification {n : ℕ} {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (M : CoefficientModel G Q) (hG : G.CliqueFree 5) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  let F := family (mobius M.function)
  have hmem : ∀ D,D∈F ↔ D.card=4 ∧ mobius M.function D≠0 := mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG M.supported M.boolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion F
    (fun D hD => ((hmem D).mp hD).1) M.nonempty M.connected hthin hsquare
  have hneA : ∀ i,(A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with he | he <;> omega
  obtain ⟨P,hP⟩ := FourPartGraphRecognition.parts_of_cover F A hneA hdis hprod M.covers
  have hproduct : FourPartGraphRecognition.ProductFamily F P.parts := by
    rw [hP]
    exact hprod
  have hsizeP : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2 := by
    rw [hP]
    exact hsize
  have hcl : ∀ D∈F,G.IsClique D := by
    intro D hD
    exact M.supported.clique_of_nonzero ((hmem D).mp hD).2
  obtain ⟨he,hcard,hiso⟩ := FourPartGraphRecognition.recognize P F hproduct hsizeP hcl
    (BooleanFourPartStructure.clique_card_le_four hG)
  have hedge : edgeGraph (mobius M.function)=FourPartGraphRecognition.unionGraph F := rfl
  exact ⟨M.directions.trans (hedge.trans he),by simpa using hcard,hiso⟩

end UnitLatticeGeometry

/-- Theorem 9.5, in its complete unit-summand range: all n≥4, the given
K5-free ambient graph, full dimension, and actual lattice polytopes. -/
theorem unit_lattice_classification : Targets.UnitLatticeClassification := by
  intro n hn G hG Q hQ hi hd hsum
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model hn hG hQ hi hd hsum
  exact M.classification hG

/-- The same theorem with the traditional polytope-only definition of
Minkowski indecomposability, whose equivalence is derived from the actual sum. -/
theorem unit_lattice_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

/-- Arbitrary real translations of lattice polytopes obey the same exact
classification, with every conclusion stated on the original translated body. -/
theorem unit_translated_lattice_classification {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated hn hG hQ hi hd hsum
  exact M.classification hG

theorem unit_translated_lattice_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

end GraphicalZonotopes

end
end
end BundlePart288

section BundlePart289
/- Source: Papers/GraphicalZonotopes/UnitLatticeDilation.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeDilation
open Finset
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A lattice summand at any real dilation strictly below two is already a
summand of the unscaled graphical zonotope. This is a consequence of integral
support values, not an integrality hypothesis on the dilation parameter. -/
theorem unit_summand_of_lt_two {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : LatticePolytope Q) (hnQ : Q.Nonempty) {a : ℝ} (ha : 0< a) (ha2 : a<2)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    IsMinkowskiSummand Q (graphicalZonotope G) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hn,hs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  rw [hbody]
  have hsum1 : IsMinkowskiSummand (basePolytope (lowerSupport Q))
      ((1 : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hn hs (by norm_num : (0 : ℝ)≤1)).mpr
    refine ⟨hgraph,?_⟩
    intro u v huv hadj S hu hv
    obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
    have hklt : (k : ℝ)<2 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha2
    have hklt' : k<(2 : ℤ) := by exact_mod_cast hklt
    rw [hk]
    exact_mod_cast (show k≤(1 : ℤ) by omega)
  simpa only [one_smul] using hsum1

/-- Every nontrivial full-dimensional lattice summand requires dilation at
least one, even when its complement and dilation parameter are arbitrary real. -/
theorem dilation_at_least_one {n : ℕ} (hn : 2≤ n) {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q) (hnQ : Q.Nonempty)
    (hd : FullDimension Q) {a : ℝ} (ha : 0< a)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) : 1≤ a := by
  by_contra hn1
  have ha1 : a<1 := lt_of_not_ge hn1
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  let f := lowerSupport Q
  have hzero : ∀ u v : Fin n,u≠ v → ∀ S : Finset (Fin n),u∉S → v∉S → delta f u v S=0 := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
      have hk0 : (0 : ℝ)≤ k := by rw [← hk];exact hfs.elemental u v huv S hu hv
      have hk1 : (k : ℝ)<1 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha1
      have hk0' : (0 : ℤ)≤ k := by exact_mod_cast hk0
      have hk1' : k<(1 : ℤ) := by exact_mod_cast hk1
      have hkeq : k=0 := by omega
      simpa only [hkeq,Int.cast_zero] using hk
    · exact hgraph u v huv hadj S hu hv
  have hz : normalize f=0 := by
    apply normalized_zero_elemental_eq_zero (normalize_translationNormalized hfn)
    intro u v huv S hu hv
    rw [delta_normalize f huv hu hv]
    exact hzero u v huv S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  rw [hz,basePolytope_zero] at hdim
  have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
      (⊥ : Submodule ℝ (Fin n → ℝ)) :=
    _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
  rw [hspan,_root_.finrank_bot] at hdim
  omega

end UnitLatticeDilation
end GraphicalZonotopes

end
end
end BundlePart289

section BundlePart290
/- Source: Papers/GraphicalZonotopes/OptimalK5FreeDilation.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- Corollary 9.12: exact attainment and the universal lower bound for every
K5-free ambient graph, all n≥4, and every positive real dilation. -/
theorem optimal_k5_free_dilation : Targets.OptimalK5FreeDilation := by
  intro n hn
  refine ⟨optimal_k5_free_dilation_attained hn,?_⟩
  intro G hG a ha hsum
  obtain ⟨Q,hQ,hi,hd,hs⟩ := hsum
  by_cases hn8 : n≤8
  · simpa only [if_pos hn8] using
      UnitLatticeDilation.dilation_at_least_one (by omega : 2≤ n) hQ hi.1 hd ha hs
  · rw [if_neg hn8]
    by_contra hn2
    have ha2 : a<2 := lt_of_not_ge hn2
    have hunit := UnitLatticeDilation.unit_summand_of_lt_two hQ hi.1 ha ha2 hs
    exact hn8 (unit_lattice_classification n hn G hG Q hQ hi hd hunit).2.1

/-- The universal bound in the ordinary polytopal convention. The actual
summand equation supplies the generalized-permutahedron presentation needed
for the equivalence of the two indecomposability conventions. -/
theorem optimal_k5_free_dilation_lower_bound_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5) {a : ℝ} (ha : 0< a)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    (if n≤8 then (1 : ℝ) else 2)≤ a := by
  obtain ⟨R,hR,hRc,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  have hi' : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  exact (optimal_k5_free_dilation n hn).2 G hG a ha
    ⟨Q,hQ,hi',hd,⟨R,hR,hRc,hnR,he⟩⟩

end GraphicalZonotopes

end
end
end BundlePart290

section BundlePart291
/- Source: Papers/GraphicalZonotopes/SmallCliqueDimension.lean -/





/-! # The low-dimensional cases of the partial-three-tree spectrum -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Triangle-free graphical cones have only segment rays. This uses the
complete nonnegative edge-coefficient decomposition, not a dimension premise. -/
theorem triangleFree_extreme_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hg : Graphical G z) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) ≤ 1 := by
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hzero : ∀ C : Finset V,C.card ≠ 2 → y C = 0 := by
    intro C hC
    apply coefficient_zero_of_not_clique hy C
    rintro ⟨hc,hcl⟩
    have hc3 : 3 ≤ C.card := by omega
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq hc3
    exact hG T ⟨fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv,hT⟩
  have hnonneg : ∀ C : Finset V,0 ≤ y C := by
    intro C
    by_cases hc : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
      have hh := hz.2.1.elemental u v huv ∅ (by simp) (by simp)
      rw [← zeta_mobius z,delta_zeta_empty _ huv] at hh
      exact hh
    · rw [hzero C hc]
  let p : Finset V → SetFunction V := fun C => y C • setMonomial C
  have hp : ∀ C,TranslationNormalized (p C) ∧ Supermodular (p C) := by
    intro C
    refine ⟨?_,(setMonomial_supermodular C).smul (hnonneg C)⟩
    by_cases hc : C.card = 2
    · have hn := setMonomial_translationNormalized (C := C) (by omega)
      exact ⟨by change y C*setMonomial C ∅=0; rw [hn.1,mul_zero],
        fun v => by change y C*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
    · simp only [p,hzero C hc,zero_smul]
      exact ⟨rfl,fun _ => rfl⟩
  have hsum : (∑ C,p C) = z := by
    rw [← zeta_mobius z,zeta_eq_sum_monomials]
  have hex : ∃ C,p C ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz.2.2.1 (hsum.symm.trans (sum_eq_zero (fun C _ => h C)))
  obtain ⟨C,hC⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand p (fun C => (hp C).1)
    (fun C => (hp C).2) hsum hC
  have hc : C.card = 2 := by
    by_contra hc
    exact hC (by simp only [p,hzero C hc,zero_smul])
  have hdep : DependsOn (p C) C := (setMonomial_dependsOn C).smul _
  rw [hscale] at hdep
  have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
    (DependsOn.of_smul (ne_of_gt ha) hdep)
  simpa only [hc] using hb

theorem triangleFree_summand_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 1 := by
  obtain ⟨z,hzs,hze,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  rcases hze with hz | hz
  · rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot]
    omega
  · exact triangleFree_extreme_dimension_le_one hG hz z.2.2

theorem triangleFree_maximum_dimension {G : SimpleGraph V} (hG : G.CliqueFree 3)
    (hE : ∃ u v : V,G.Adj u v) : maximumIndecomposableDimension G = 1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact triangleFree_summand_dimension_le_one hG hQ hi hw
  · obtain ⟨u,v,huv⟩ := hE
    have hcl : G.IsClique ({u,v} : Finset V) := by
      intro a ha b hb hab
      change a ∈ ({u,v} : Finset V) at ha
      change b ∈ ({u,v} : Finset V) at hb
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huv
      · exact huv.symm
      · exact False.elim (hab rfl)
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [card_pair huv.ne]) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,card_pair huv.ne] at hb
    exact hb

theorem edgeless_maximum_dimension {G : SimpleGraph V}
    (hG : ∀ u v : V,¬G.Adj u v) : maximumIndecomposableDimension G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  obtain ⟨z,hzs,hze,hqdim⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hz : z.1 = 0 := normalized_zero_elemental_eq_zero z.2.1
    (fun u v huv S hu hv => z.2.2 u v huv (hG u v) S hu hv)
  rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hqdim
  omega

theorem partial_threeTree_no_tetrahedron_dimension_le_two {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 2 := by
  by_contra hd
  have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by omega
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd3
  obtain ⟨C,hC⟩ := ht.tetrahedra_nonempty
  have hc := tetrahedra_mono (inducedOn_le G U) hC
  rw [hK] at hc
  exact notMem_empty C hc

theorem partial_threeTree_triangle_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    (hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T) :
    maximumIndecomposableDimension G = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_no_tetrahedron_dimension_le_two hG hK hQ hi hw
  · obtain ⟨T,hT,hcl⟩ := hT
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness (by omega) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,hT] at hb
    exact hb

/-- The complete piecewise dimension formula of Corollary 6.8. -/
def partialThreeTreeDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then maximumAdmissibleCliqueCount G+2
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem partial_threeTree_piecewise_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  unfold partialThreeTreeDimension
  by_cases hK : (tetrahedra G).Nonempty
  · rw [if_pos hK]
    exact partial_threeTree_maximum_dimension hG hK
  · rw [if_neg hK]
    have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [if_pos hT]
      exact partial_threeTree_triangle_maximum hG hKe hT
    · rw [if_neg hT]
      have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [if_pos hE]
        exact triangleFree_maximum_dimension hcf hE
      · rw [if_neg hE]
        exact edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)

/-- The full positive spectrum, including graphs with no tetrahedron. -/
theorem partial_threeTree_full_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hK : (tetrahedra G).Nonempty
  · apply partial_threeTree_dimension_spectrum hG hK d hd
    rwa [partial_threeTree_maximum_dimension hG hK] at hmax
  · have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [partial_threeTree_triangle_maximum hG hKe hT] at hmax
      obtain ⟨T,hT,hcl⟩ := hT
      obtain ⟨C,hCT,hC⟩ := exists_subset_card_eq (s := T) (n := d+1) (by omega)
      obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness (by omega : 2 ≤ C.card)
        (fun u hu v hv huv => hcl (hCT hu) (hCT hv) huv)
      exact ⟨Q,hQ,hi,hw,by omega⟩
    · have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [triangleFree_maximum_dimension hcf hE] at hmax
        have hd1 : d = 1 := by omega
        obtain ⟨u,v,huv⟩ := hE
        have hcl : G.IsClique ({u,v} : Finset V) := by
          intro a ha b hb hab
          change a ∈ ({u,v} : Finset V) at ha
          change b ∈ ({u,v} : Finset V) at hb
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact huv
          · exact huv.symm
          · exact False.elim (hab rfl)
        obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
          (by rw [card_pair huv.ne]) hcl
        refine ⟨Q,hQ,hi,hw,?_⟩
        simpa only [card_pair huv.ne,hd1] using hqdim
      · have hdim := edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)
        omega

end GraphicalZonotopes

end
end
end BundlePart291

section BundlePart292
/- Source: Papers/GraphicalZonotopes/PartialThreeTreePaperStatements.lean -/





/-! # Finite-graph formulations of Corollaries 6.6--6.8

An ordering of the finite vertex set is chosen inside each statement. It is
used only by the geometric coordinate machinery and is not an extra graph
hypothesis. The support and spectrum statements use ordinary polytopal
Minkowski indecomposability, with its equivalence proved for actual weak
summands before invoking the core results.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes

/-- Corollary 6.6 on every finite vertex type, with the actual direction
graph induced on its active coordinate set and no order assumption. -/
theorem partial_threeTree_support_classification_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ H : SimpleGraph V,
      (∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
      ∃ U : Finset V, H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG H
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,ha⟩
    exact (partial_threeTree_support_classification hG H).mp
      ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd,ha⟩
  · intro h
    obtain ⟨Q,hQ,hi,hw,hd,ha⟩ :=
      (partial_threeTree_support_classification hG H).mpr h
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd,ha⟩

/-- Corollary 6.8's complete piecewise maximum on arbitrary finite graphs:
`M(G)+2`, two, one, or zero according to tetrahedra, triangles, and edges. -/
theorem partial_threeTree_piecewise_maximum_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G →
      maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  exact fun G hG => partial_threeTree_piecewise_maximum hG

/-- Every positive dimension up to the sharp maximum occurs on every
partial three-tree, with an actual lattice polytope and the ordinary
polytopal indecomposability convention. -/
theorem partial_threeTree_full_dimension_spectrum_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ d : ℕ,
      1 ≤ d → d ≤ maximumIndecomposableDimension G →
      ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG d hd hmax
  obtain ⟨Q,hQ,hi,hw,hD⟩ := partial_threeTree_full_dimension_spectrum hG d hd hmax
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

end GraphicalZonotopes

end
end
end BundlePart292

section BundlePart293
/- Source: Papers/GraphicalZonotopes/PathPaperStatement.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped BigOperators

/-- Equation (3.1) with subtraction in the real numbers, exactly as in the
paper. The lower bound on n justifies the natural-subtraction cast used by
the uniform finite-window definition. -/
theorem polytope_defining_equations_real {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | subsetSum x Finset.univ = (n : ℝ)-2 ∧
      ∀ S, setFunction n S ≤ subsetSum x S} := by
  simpa only [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat] using
    polytope_defining_equations n

/-- The same literal statement in ordinary finite-sum notation. -/
theorem polytope_defining_equations_sums {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), setFunction n S ≤ ∑ i ∈ S, x i} := by
  simpa only [subsetSum] using polytope_defining_equations_real hn

end Path
end GraphicalZonotopes

end
end
end BundlePart293

section BundlePart294
/- Source: Papers/GraphicalZonotopes/PathBooleanStatement.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- The indicator of a triple is the product of its three membership bits,
even if some of the displayed vertices coincide. -/
theorem setMonomial_three_membershipBits {V : Type*} [DecidableEq V]
    (a b c : V) (S : Finset V) :
    setMonomial {a,b,c} S =
      membershipBit S a * membershipBit S b * membershipBit S c := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc]

/-- The analogous exact identity for the four-vertex term. -/
theorem setMonomial_four_membershipBits {V : Type*} [DecidableEq V]
    (a b c d : V) (S : Finset V) :
    setMonomial {a,b,c,d} S =
      membershipBit S a * membershipBit S b * membershipBit S c * membershipBit S d := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    by_cases hc : c ∈ S <;> by_cases hd : d ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc,hd]

namespace Path

/-- The displayed Boolean-product formula preceding equation (3.1), with
the paper's labels 1,...,n represented by the zero-based labels of Fin n. -/
def booleanFormula (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (∑ i : Fin (n-2), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2)) +
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3)) -
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2) *
      integerBit S ((i.val : ℤ)+3))

/-- The original coefficient construction and the paper's membership-bit
polynomial agree at every subset and every path length. -/
theorem setFunction_eq_booleanFormula (n : ℕ) : setFunction n = booleanFormula n := by
  funext S
  have h012 (i : Fin (n-2)) :
      setMonomial (window n i.val {0,1,2}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 2) i (by decide : 0 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 1 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 2 ≤ 2)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h023 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+2) *
          integerBit S ((i.val : ℤ)+3) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h0123 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,1,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3) := by
    rw [window_quad_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 1 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_four_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have he := congrFun (setFunction_expansion n) S
  simpa only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,h012,h023,h0123,
    booleanFormula] using he

/-- The complete defining equations using ordinary finite sums and the
literal membership-bit polynomial. -/
theorem polytope_boolean_defining_equations {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), booleanFormula n S ≤ ∑ i ∈ S, x i} := by
  rw [polytope_defining_equations_sums hn,setFunction_eq_booleanFormula]

end Path
end GraphicalZonotopes

end
end
end BundlePart294

section BundlePart295
/- Source: Papers/GraphicalZonotopes/PathJoinPolynomial.lean -/








/-!
# The endpoint-corrected path-join polynomial

The parameter `n` means that the path has `n+2` vertices. Thus every path
length in Appendix B is included. The ambient vertex set has `n+4`
vertices, with hubs 0,1 and path vertices 2,...,n+3.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

abbrev Vertex (n : ℕ) := Fin (n+4)
def hubA (n : ℕ) : Vertex n := ⟨0,by omega⟩
def hubB (n : ℕ) : Vertex n := ⟨1,by omega⟩
def vertex {n : ℕ} (i : Fin (n+2)) : Vertex n := ⟨i.val+2,by omega⟩

@[simp] theorem hubA_ne_hubB (n : ℕ) : hubA n ≠ hubB n := by
  simp [hubA,hubB,Fin.ext_iff]
@[simp] theorem hubB_ne_hubA (n : ℕ) : hubB n ≠ hubA n := Ne.symm (hubA_ne_hubB n)
@[simp] theorem vertex_ne_hubA {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubA n := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+2=0 at hv
  omega
@[simp] theorem vertex_ne_hubB {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubB n := by
  simp [vertex,hubB,Fin.ext_iff]
@[simp] theorem hubA_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubA n ≠ vertex i :=
  Ne.symm (vertex_ne_hubA i)
@[simp] theorem hubB_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubB n ≠ vertex i :=
  Ne.symm (vertex_ne_hubB i)
@[simp] theorem vertex_inj {n : ℕ} {i j : Fin (n+2)} : vertex i=vertex j ↔ i=j := by
  simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_left_ne_right {n : ℕ} (i : Fin (n+1)) :
    vertex i.castSucc ≠ vertex i.succ := by simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_right_ne_left {n : ℕ} (i : Fin (n+1)) :
    vertex i.succ ≠ vertex i.castSucc := Ne.symm (vertex_left_ne_right i)

theorem vertex_cases {n : ℕ} (v : Vertex n) :
    v=hubA n ∨ v=hubB n ∨ ∃ i : Fin (n+2),v=vertex i := by
  by_cases ha : v.val=0
  · exact Or.inl (Fin.ext ha)
  by_cases hb : v.val=1
  · exact Or.inr (Or.inl (Fin.ext hb))
  refine Or.inr (Or.inr ⟨⟨v.val-2,by omega⟩,?_⟩)
  apply Fin.ext
  simp only [vertex]
  omega

/-- The literal graph K₂ * P_(n+2), with its labelled hubs and path. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := u≠ v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,by tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (n : ℕ) : DecidableRel (graph n).Adj := fun u v =>
  inferInstanceAs (Decidable (u≠ v ∧
    (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)))

@[simp] theorem graph_hubA {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubA n) v ↔ hubA n≠ v := by simp [graph,hubA]
@[simp] theorem graph_hubB {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubB n) v ↔ hubB n≠ v := by simp [graph,hubB]
@[simp] theorem graph_vertices {n : ℕ} (i j : Fin (n+2)) :
    (graph n).Adj (vertex i) (vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  change (vertex i≠ vertex j ∧
    (i.val+2<2 ∨ j.val+2<2 ∨ i.val+2+1=j.val+2 ∨ j.val+2+1=i.val+2)) ↔ _
  rw [Ne,vertex_inj]
  simp only [Fin.ext_iff]
  omega

/-- Every clique of cardinality at least two has exactly one of these
coordinate shapes: the hub edge, a spoke/hub triangle, or a path edge
with any subset of its two hubs. -/
abbrev Slot (n : ℕ) := Unit ⊕ (Fin 3 × Fin (n+2)) ⊕ (Fin 4 × Fin (n+1))

def clique {n : ℕ} : Slot n → Finset (Vertex n)
  | .inl _ => {hubA n,hubB n}
  | .inr (.inl (r,i)) =>
    if r=0 then {hubA n,vertex i}
    else if r=1 then {hubB n,vertex i}
    else {hubA n,hubB n,vertex i}
  | .inr (.inr (r,i)) =>
    if r=0 then {vertex i.castSucc,vertex i.succ}
    else if r=1 then {hubA n,vertex i.castSucc,vertex i.succ}
    else if r=2 then {hubB n,vertex i.castSucc,vertex i.succ}
    else {hubA n,hubB n,vertex i.castSucc,vertex i.succ}

theorem clique_card_ge_two {n : ℕ} (i : Slot n) : 2≤(clique i).card := by
  rcases i with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique]
  · fin_cases r <;> simp [clique,Finset.card_pair (vertex_left_ne_right i)]

theorem clique_isClique {n : ℕ} (i : Slot n) : (graph n).IsClique (clique i) := by
  have insA {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubA n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hav => graph_hubA.mpr hav)
  have insB {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubB n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hbv => graph_hubB.mpr hbv)
  have one (v : Vertex n) : (graph n).IsClique ({v} : Finset (Vertex n)) := by
    simpa only [Finset.coe_singleton] using (graph n).isClique_singleton v
  have pair (j : Fin (n+1)) :
      (graph n).IsClique ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [Finset.coe_pair,SimpleGraph.isClique_pair]
    intro hj
    apply (graph_vertices _ _).mpr
    exact Or.inl rfl
  rcases i with w | ⟨r,i⟩ | ⟨r,i⟩
  · exact insA (one (hubB n))
  · fin_cases r
    · exact insA (one (vertex i))
    · exact insB (one (vertex i))
    · exact insA (insB (one (vertex i)))
  · fin_cases r
    · exact pair i
    · exact insA (pair i)
    · exact insB (pair i)
    · exact insA (insB (pair i))

def coefficient (n : ℕ) : Slot n → ℝ
  | .inl _ => ((n+2)/2 : ℕ)
  | .inr (.inl (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i=0 then 0 else 1)
    else if i=0 then 0 else -1
  | .inr (.inr (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i.val%2=0 then -1 else 0)
    else if r=2 then (if i.val%2=0 then 0 else -1)
    else 1

def setFunction (n : ℕ) : SetFunction (Vertex n) :=
  FiniteMonomial.polynomial clique (coefficient n)

theorem normalized (n : ℕ) : TranslationNormalized (setFunction n) :=
  FiniteMonomial.polynomial_normalized clique clique_card_ge_two _

theorem graphical (n : ℕ) : Graphical (graph n) (setFunction n) :=
  FiniteMonomial.polynomial_graphical clique clique_isClique _

end GraphicalZonotopes.PathJoin

end
end
end BundlePart295

section BundlePart296
/- Source: Papers/GraphicalZonotopes/PathJoinCliques.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset

def privatePart {n : ℕ} (C : Finset (Vertex n)) : Finset (Vertex n) :=
  (C.erase (hubA n)).erase (hubB n)

@[simp] theorem privatePart_hub {n : ℕ} :
    privatePart (clique (.inl () : Slot n))=∅ := by simp [privatePart,clique]

@[simp] theorem privatePart_single {n : ℕ} (r : Fin 3) (i : Fin (n+2)) :
    privatePart (clique (.inr (.inl (r,i)) : Slot n))={vertex i} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem privatePart_pair {n : ℕ} (r : Fin 4) (i : Fin (n+1)) :
    privatePart (clique (.inr (.inr (r,i)) : Slot n))=
      {vertex i.castSucc,vertex i.succ} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem vertex_mem_privatePart {n : ℕ} (C : Finset (Vertex n))
    (i : Fin (n+2)) : vertex i∈privatePart C ↔ vertex i∈C := by
  simp [privatePart]

theorem eq_of_privatePart {n : ℕ} {C D : Finset (Vertex n)}
    (hp : privatePart C=privatePart D)
    (ha : hubA n∈C ↔ hubA n∈D) (hb : hubB n∈C ↔ hubB n∈D) : C=D := by
  ext v
  rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
  · exact ha
  · exact hb
  · rw [← vertex_mem_privatePart C i,← vertex_mem_privatePart D i,hp]

theorem pathPair_injective {n : ℕ} : Function.Injective
    (fun i : Fin (n+1) => ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))) := by
  intro i j h
  change ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))=
    {vertex j.castSucc,vertex j.succ} at h
  have hl : vertex i.castSucc ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  have hr : vertex i.succ ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  simp only [mem_insert,mem_singleton,vertex_inj,Fin.ext_iff,vertex,
    Fin.val_castSucc,Fin.val_succ] at hl hr
  apply Fin.ext
  omega

theorem clique_injective {n : ℕ} : Function.Injective (clique (n := n)) := by
  intro x y h
  have hp := congrArg privatePart h
  have ha : hubA n∈clique x ↔ hubA n∈clique y := by rw [h]
  have hb : hubB n∈clique x ↔ hubB n∈clique y := by rw [h]
  rcases x with u | ⟨r,i⟩ | ⟨r,i⟩ <;>
    rcases y with v | ⟨s,j⟩ | ⟨s,j⟩
  · cases u; cases v; rfl
  · cases u; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp).elim
  · cases u; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex j.castSucc∈(∅ : Finset (Vertex n)) := by rw [hp]; simp
    simp at hm
  · cases v; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp.symm).elim
  · simp only [privatePart_single,Finset.singleton_inj,vertex_inj] at hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right j)] at hc
    omega
  · cases v; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex i.castSucc∈(∅ : Finset (Vertex n)) := by rw [← hp]; simp
    simp at hm
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right i)] at hc
    omega
  · simp only [privatePart_pair] at hp
    have hij := pathPair_injective hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl

theorem privatePart_vertex {n : ℕ} {C : Finset (Vertex n)} {v : Vertex n}
    (hv : v∈privatePart C) : ∃ i : Fin (n+2),v=vertex i := by
  have hA : v≠ hubA n := (mem_erase.mp (mem_erase.mp hv).2).1
  have hB : v≠ hubB n := (mem_erase.mp hv).1
  rcases vertex_cases v with ha | hb | hi
  · exact (hA ha).elim
  · exact (hB hb).elim
  · exact hi

theorem privatePart_subset {n : ℕ} (C : Finset (Vertex n)) : privatePart C⊆C :=
  (erase_subset _ _).trans (erase_subset _ _)

theorem privatePart_card_le_two {n : ℕ} {C : Finset (Vertex n)}
    (hC : (graph n).IsClique C) : (privatePart C).card≤2 := by
  by_contra hn
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp (Nat.lt_of_not_ge hn)
  obtain ⟨i,rfl⟩ := privatePart_vertex hu
  obtain ⟨j,rfl⟩ := privatePart_vertex hv
  obtain ⟨k,rfl⟩ := privatePart_vertex hw
  have hij := (graph_vertices i j).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hv) huv)
  have hik := (graph_vertices i k).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hw) huw)
  have hjk := (graph_vertices j k).mp
    (hC (privatePart_subset C hv) (privatePart_subset C hw) hvw)
  omega

theorem adjacent_pair_index {n : ℕ} {i j : Fin (n+2)}
    (hij : (graph n).Adj (vertex i) (vertex j)) :
    ∃ k : Fin (n+1),({vertex i,vertex j} : Finset (Vertex n))=
      {vertex k.castSucc,vertex k.succ} := by
  rcases (graph_vertices i j).mp hij with h | h
  · let k : Fin (n+1) := ⟨i.val,by omega⟩
    have hi : k.castSucc=i := Fin.ext rfl
    have hj : k.succ=j := Fin.ext h
    exact ⟨k,by rw [hi,hj]⟩
  · let k : Fin (n+1) := ⟨j.val,by omega⟩
    have hj : k.castSucc=j := Fin.ext rfl
    have hi : k.succ=i := Fin.ext h
    exact ⟨k,by rw [hi,hj]; exact pair_comm _ _⟩

theorem clique_covers {n : ℕ} (C : Finset (Vertex n))
    (hC : IsCliqueCoordinate (graph n) C) : ∃ i : Slot n,clique i=C := by
  have hcard := hC.1
  have hcl := hC.2
  have hp_le := privatePart_card_le_two hcl
  by_cases h0 : (privatePart C).card=0
  · have hp0 : privatePart C=∅ := card_eq_zero.mp h0
    have hsub : C⊆{hubA n,hubB n} := by
      intro v hv
      rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
      · simp
      · simp
      · have hm : vertex i∈privatePart C := (vertex_mem_privatePart C i).mpr hv
        rw [hp0] at hm
        exact (notMem_empty _ hm).elim
    have he : C={hubA n,hubB n} := eq_of_subset_of_card_le hsub (by simpa using hcard)
    exact ⟨.inl (),he.symm⟩
  by_cases h1 : (privatePart C).card=1
  · obtain ⟨v,hp⟩ := card_eq_one.mp h1
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hv
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inl (2,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (0,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (1,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · have he : C={vertex i} := eq_of_privatePart (by simpa [privatePart] using hp)
        (by simp [ha]) (by simp [hb])
      rw [he,card_singleton] at hcard
      omega
  · have h2 : (privatePart C).card=2 := by omega
    obtain ⟨u,v,huv,hp⟩ := card_eq_two.mp h2
    have hu : u∈privatePart C := by rw [hp]; simp
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hu
    obtain ⟨j,rfl⟩ := privatePart_vertex hv
    have hadj := hcl (privatePart_subset C hu) (privatePart_subset C hv) huv
    obtain ⟨k,hk⟩ := adjacent_pair_index hadj
    rw [hk] at hp
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inr (3,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (1,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (2,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (0,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]

theorem graphical_coordinates {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (hG : Graphical (graph n) f) :
    f=FiniteMonomial.polynomial clique (fun i => mobius f (clique i)) :=
  FiniteMonomial.graphical_eq_polynomial clique clique_injective clique_covers hn hG

end GraphicalZonotopes.PathJoin

end
end
end BundlePart296

section BundlePart297
/- Source: Papers/GraphicalZonotopes/PathJoinSlacks.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def bit {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : ℝ := if v∈S then 1 else 0

theorem bit_cases {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) :
    bit v S=0 ∨ bit v S=1 := by
  by_cases h : v∈S <;> simp [bit,h]

theorem bit_nonneg {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : 0≤ bit v S := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem bit_le_one {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : bit v S≤1 := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem delta_clique_hub {n : ℕ} (s : Slot n) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setMonomial (clique s)) (hubA n) (hubB n) S =
      match s with
      | .inl _ => 1
      | .inr (.inl (r,i)) => if r=2 then bit (vertex i) S else 0
      | .inr (.inr (r,i)) =>
        if r=3 then bit (vertex i.castSucc) S*bit (vertex i.succ) S else 0 := by
  rw [delta_setMonomial (hubA_ne_hubB n) ha hb]
  rcases s with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    by_cases hl : vertex i.castSucc∈S <;> by_cases hr : vertex i.succ∈S <;>
      simp [hl,hr]

theorem delta_polynomial_hub {n : ℕ} (x : Slot n → ℝ) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubA n) (hubB n) S =
      x (.inl ()) +
        ∑ i : Fin (n+2),x (.inr (.inl (2,i)))*bit (vertex i) S +
        ∑ i : Fin (n+1),x (.inr (.inr (3,i)))*
          bit (vertex i.castSucc) S*bit (vertex i.succ) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_hub _ _ ha hb]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_assoc,add_assoc]

theorem delta_hub {n : ℕ} (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setFunction n) (hubA n) (hubB n) S = ((n+2)/2 : ℕ) -
      ∑ i : Fin (n+1),(1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S := by
  rw [setFunction,delta_polynomial_hub _ _ ha hb]
  have hsum : (∑ i : Fin (n+2),
      coefficient n (.inr (.inl (2,i)))*bit (vertex i) S) =
      -∑ i : Fin (n+1),bit (vertex i.succ) S := by
    rw [Fin.sum_univ_succ]
    simp [coefficient,Fin.succ_ne_zero,Finset.sum_neg_distrib]
  rw [hsum]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_false,one_mul]
  simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
  ring

theorem path_vertices_mem_pair_iff {n : ℕ} (r : Fin 4) (j : Fin (n+1))
    (i : Fin (n+2)) :
    vertex i∈clique (.inr (.inr (r,j)) : Slot n) ↔ i=j.castSucc ∨ i=j.succ := by
  fin_cases r <;> simp [clique]

theorem delta_clique_path {n : ℕ} (s : Slot n) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setMonomial (clique s)) (vertex i.castSucc) (vertex i.succ) S =
      match s with
      | .inl _ => 0
      | .inr (.inl _) => 0
      | .inr (.inr (r,j)) =>
        if j=i then
          if r=0 then 1 else if r=1 then bit (hubA n) S
          else if r=2 then bit (hubB n) S else bit (hubA n) S*bit (hubB n) S
        else 0 := by
  rw [delta_setMonomial (vertex_left_ne_right i) hl hr]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · have hne : i.castSucc≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
    fin_cases r <;> simp [clique,vertex_inj]
    all_goals intro h0 h1; exact (hne (h0.trans h1.symm)).elim
  · by_cases he : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      by_cases ha : hubA n∈S <;> by_cases hb : hubB n∈S <;> simp [ha,hb]
    · have hnot : ¬(vertex i.castSucc∈clique (.inr (.inr (r,j)) : Slot n) ∧
          vertex i.succ∈clique (.inr (.inr (r,j)) : Slot n)) := by
        intro h
        have h0 := (path_vertices_mem_pair_iff r j i.castSucc).mp h.1
        have h1 := (path_vertices_mem_pair_iff r j i.succ).mp h.2
        simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at h0 h1
        apply he
        apply Fin.ext
        omega
      simp only [he,ite_false]
      apply if_neg
      intro h
      exact hnot ⟨h.1,h.2.1⟩

theorem delta_polynomial_path {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (FiniteMonomial.polynomial clique x) (vertex i.castSucc) (vertex i.succ) S =
      x (.inr (.inr (0,i))) + x (.inr (.inr (1,i)))*bit (hubA n) S +
      x (.inr (.inr (2,i)))*bit (hubB n) S +
      x (.inr (.inr (3,i)))*bit (hubA n) S*bit (hubB n) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_path _ _ _ hl hr]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_ite,mul_assoc,add_assoc]

theorem delta_path {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S =
      1 - (if i.val%2=0 then bit (hubA n) S else bit (hubB n) S) +
        bit (hubA n) S*bit (hubB n) S := by
  rw [setFunction,delta_polynomial_path _ _ _ hl hr]
  by_cases he : i.val%2=0 <;> simp [coefficient,he] <;> ring

theorem delta_path_boolean {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=0 ∨
      delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=1 := by
  rw [delta_path i S hl hr]
  rcases bit_cases (hubA n) S with ha | ha <;>
    rcases bit_cases (hubB n) S with hb | hb <;>
      by_cases he : i.val%2=0 <;> simp [ha,hb,he]

end GraphicalZonotopes.PathJoin

end
end
end BundlePart297
