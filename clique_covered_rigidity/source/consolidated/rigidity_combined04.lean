module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined03
import all consolidated.rigidity_combined03
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityStressStarRank.lean -/




@[expose] public section

/-!
# The full stress-star dimension is degree minus deletion rank

Deleting all bars at a vertex leaves its three velocity coordinates
free.  The remaining motion kernel is explicitly equivalent to the
deleted framework kernel times those coordinates.  On the dual side,
restriction of an actual stress to its incident bars has kernel exactly
the zero-extended deleted stress space.  Rank-nullity gives the paper's
identity without a matroid-rank or stress-count assumption.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def isolateVertex (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := by constructor; rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩
  loopless := by constructor; intro a; rintro ⟨h, _⟩; exact G.loopless.irrefl a h

theorem isolateVertex_le (G : SimpleGraph V) (v : V) : isolateVertex G v ≤ G :=
  fun _ _ h => h.1

theorem subgraphEdgeSet_isolateVertex (G : SimpleGraph V) (v : V) :
    subgraphEdgeSet G (isolateVertex G v) = {e : Edge G | v ∉ e.val} := by
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := he
      change (G.Adj a b ∧ a ≠ v ∧ b ≠ v) ↔ _
      simp [hab, Sym2.mem_iff, ne_comm]

def isolateVertexKernelEquiv (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    (rigidityOperator (isolateVertex G v) p).ker ≃ₗ[ℝ]
      ((rigidityOperator (deletedGraph G v) (deletedPlacement p v)).ker × Vec3) where
  toFun u := (⟨fun a => u.val a.val, by
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b hab
    exact (isInfinitesimalMotion_iff (isolateVertex G v) p u.val).mp u.property
      a.val b.val ⟨hab, a.property, b.property⟩⟩, u.val v)
  invFun u := ⟨fun a => if ha : a = v then u.2 else u.1.val ⟨a, ha⟩, by
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    rintro a b ⟨hab, ha, hb⟩
    have h := (isInfinitesimalMotion_iff (deletedGraph G v)
      (deletedPlacement p v) u.1.val).mp u.1.property ⟨a, ha⟩ ⟨b, hb⟩ hab
    simpa only [edgeConstraint, deletedPlacement, dif_neg ha, dif_neg hb] using h⟩
  left_inv u := by
    apply Subtype.ext
    funext a
    by_cases ha : a = v
    · subst a
      simp
    · simp [ha]
  right_inv u := by
    apply Prod.ext
    · apply Subtype.ext
      funext a
      simp [a.property]
    · simp
  map_add' u w := by apply Prod.ext <;> rfl
  map_smul' a u := by apply Prod.ext <;> rfl

theorem rigidityRank_isolateVertex (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    rigidityRank (isolateVertex G v) p =
      rigidityRank (deletedGraph G v) (deletedPlacement p v) := by
  have hk := (isolateVertexKernelEquiv G p v).finrank_eq
  rw [Module.finrank_prod] at hk
  have hV := (rigidityOperator (isolateVertex G v) p).finrank_range_add_finrank_ker
  have hD := (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).finrank_range_add_finrank_ker
  have hcard : Fintype.card (DeletedVertex v) + 1 = Fintype.card V := by
    have h := Fintype.card_subtype_compl (fun w : V => w = v)
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    simp only [Fintype.card_subtype_eq] at h
    change Fintype.card (DeletedVertex v) = Fintype.card V - 1 at h
    omega
  rw [finrank_velocity] at hV hD
  have h3 : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  rw [h3] at hk
  change Fintype.card (VertexPin.DeletedVertex v) + 1 = Fintype.card V at hcard
  change Module.finrank ℝ (rigidityOperator (isolateVertex G v) p).range =
    Module.finrank ℝ (rigidityOperator (deletedGraph G v) (deletedPlacement p v)).range
  omega

def stressStarKernelEquiv (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    ((starRestriction G v).domRestrict (StressSpace G p)).ker ≃ₗ[ℝ]
      supportedOn (StressSpace G p) {e : Edge G | v ∉ e.val} where
  toFun ω := ⟨ω.val.val, ω.val.property, by
    intro e he
    have hv : v ∈ e.val := not_not.mp he
    exact congrFun (LinearMap.mem_ker.mp ω.property) ⟨e, hv⟩⟩
  invFun ω := ⟨⟨ω.val, ω.property.1⟩, by
    rw [LinearMap.mem_ker]
    ext e
    exact ω.property.2 e.val (fun hn => hn e.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem stressStar_finrank_add_deletedStress (G : SimpleGraph V)
    (p : Placement V 3) (v : V) :
    Module.finrank ℝ (stressStarCode G v (StressSpace G p)) +
      Module.finrank ℝ (StressSpace (isolateVertex G v) p) =
        Module.finrank ℝ (StressSpace G p) := by
  have h := ((starRestriction G v).domRestrict (StressSpace G p)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,
    (stressStarKernelEquiv G p v).finrank_eq] at h
  have hi := (subgraphStressEquiv (isolateVertex_le G v) p).finrank_eq
  rw [subgraphEdgeSet_isolateVertex] at hi
  rw [← hi] at h
  exact h

theorem card_isolateVertex_edges_add_degree (G : SimpleGraph V) (v : V) :
    Fintype.card (Edge (isolateVertex G v)) + G.degree v = Fintype.card (Edge G) := by
  have hi := Fintype.card_congr (subgraphEdgeEquiv (isolateVertex_le G v))
  rw [subgraphEdgeSet_isolateVertex] at hi
  have hs := Fintype.card_congr (Equiv.Set.sumCompl {e : Edge G | v ∈ e.val})
  rw [Fintype.card_sum] at hs
  change Fintype.card (IncidentEdge G v) +
    Fintype.card {e : Edge G | v ∉ e.val} = Fintype.card (Edge G) at hs
  rw [card_incidentEdge_eq_degree] at hs
  simp only [← Nat.card_eq_fintype_card] at hi hs ⊢
  omega

/-- Exact identity before taking generic ranks. -/
theorem stressStar_finrank_add_rank (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    Module.finrank ℝ (stressStarCode G v (StressSpace G p)) + rigidityRank G p =
      G.degree v + rigidityRank (deletedGraph G v) (deletedPlacement p v) := by
  have hs := stressStar_finrank_add_deletedStress G p v
  have hG := rigidityRank_add_stress_dimension G p
  have hD := rigidityRank_add_stress_dimension (isolateVertex G v) p
  have hc := card_isolateVertex_edges_add_degree G v
  rw [rigidityRank_isolateVertex] at hD
  omega

/-- The literal star-image dimension in Corollary 2.2. -/
theorem stressStar_finrank_eq_degree_sub_deletionRankDrop
    (G : SimpleGraph V) (p : Placement V 3) (hp : IsGenericPlacement p) (v : V) :
    Module.finrank ℝ (stressStarCode G v (StressSpace G p)) =
      G.degree v - deletionRankDrop G v := by
  have h := stressStar_finrank_add_rank G p v
  have hd := generic_deletedPlacement p hp v
  have hle : genericRigidityRank (deletedGraph G v) 3 ≤ genericRigidityRank G 3 := by
    have hmono := rigidityRank_mono (isolateVertex_le G v) p
    rwa [rigidityRank_isolateVertex, hp, hd] at hmono
  rw [hp, hd] at h
  unfold deletionRankDrop
  omega

/-- Corollary 2.2's full displayed bound with the paper's deletion-rank
parameter, derived from the actual generic matrix and actual stresses. -/
theorem corollary_two_two_rankContribution (G : SimpleGraph V) (v : V) :
    (G.degree v : ℝ) / 2 - bound 4 (G.degree v - deletionRankDrop G v) ≤
      rankContribution G v := by
  obtain ⟨p, hp, hgeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  have h := rankContribution_ge_degree_half_sub_bound_star G p hp hgeom v
  rwa [stressStar_finrank_eq_degree_sub_deletionRankDrop G p hp v] at h

end
end Papers.Rigidity.BarJoint

end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined04/block_0001/Consolidated/RigidityCombined04.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined04/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigidityBodyLoadProjection.lean -/




@[expose] public section

/-!
# Prefix inclusion and the actual vertex-load projection

The compatible loads at a smaller induced vertex set are embedded by
literal zero extension.  Vanishing of all copies at one vertex has
exactly the deleted-prefix space as kernel.  Combining this fact with
the full body-load rank identity gives the actual projection dimension
`3 t_v - δ(v)` used in Section 6.

The projection retains every actual maximal-body label.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def includeBodyFamily (G : SimpleGraph V) (p : Placement V 3)
    (T U : Finset V) (hTU : T ⊆ U) :
    BodyBalancedFamily G p T →ₗ[ℝ] BodyBalancedFamily G p U where
  toFun F C := ⟨(F C).val, (F C).property.1, by
    intro v hv
    apply (F C).property.2 v
    intro h
    exact hv (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
      hTU (Finset.mem_inter.mp h).2⟩)⟩
  map_add' F H := by funext C; apply Subtype.ext; rfl
  map_smul' c F := by funext C; apply Subtype.ext; rfl

@[simp] theorem totalBodyLoad_include
    (G : SimpleGraph V) (p : Placement V 3) (T U : Finset V) (hTU : T ⊆ U)
    (F : BodyBalancedFamily G p T) :
    totalBodyLoad G p U (includeBodyFamily G p T U hTU F) = totalBodyLoad G p T F := by
  rw [totalBodyLoad_apply, totalBodyLoad_apply]
  apply Finset.sum_congr rfl
  intro C _
  rfl

def includeCompatibleLoads (G : SimpleGraph V) (p : Placement V 3)
    (T U : Finset V) (hTU : T ⊆ U) :
    compatibleBodyLoads G p T →ₗ[ℝ] compatibleBodyLoads G p U where
  toFun F := ⟨includeBodyFamily G p T U hTU F.val, by
    rw [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_include]
    exact LinearMap.mem_ker.mp F.property⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

theorem includeCompatibleLoads_injective
    (G : SimpleGraph V) (p : Placement V 3) (T U : Finset V) (hTU : T ⊆ U) :
    Function.Injective (includeCompatibleLoads G p T U hTU) := by
  intro F H h
  apply Subtype.ext
  funext C
  apply Subtype.ext
  exact congrArg (fun L : compatibleBodyLoads G p U => (L.val C).val) h

/-- Actual load copies at one vertex, retaining every maximal-body label. -/
def vertexLoadProjection (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    compatibleBodyLoads G p Finset.univ →ₗ[ℝ] (Body G → Vec3) where
  toFun F C := (F.val C).val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vertexLoadProjectionKernelEquiv
    (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    (vertexLoadProjection G p v).ker ≃ₗ[ℝ]
      compatibleBodyLoads G p (Finset.univ.erase v) where
  toFun F := ⟨fun C => ⟨(F.val.val C).val, (F.val.val C).property.1, by
    intro w hw
    by_cases hwv : w = v
    · subst w
      exact congrFun (LinearMap.mem_ker.mp F.property) C
    · apply (F.val.val C).property.2 w
      intro h
      apply hw
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
        Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ _⟩⟩⟩, by
    rw [mem_compatibleBodyLoads_iff]
    exact (mem_compatibleBodyLoads_iff G p Finset.univ F.val.val).mp F.val.property⟩
  invFun F := ⟨includeCompatibleLoads G p (Finset.univ.erase v) Finset.univ
      (Finset.subset_univ _) F, by
    rw [LinearMap.mem_ker]
    funext C
    apply (F.val C).property.2 v
    simp⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl
  right_inv F := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl
  map_add' F H := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    rfl

def bodyMultiplicity (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun C : Body G => v ∈ C.val).card

theorem complete_body_deletion_rank
    (G : SimpleGraph V) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (C : Body G) (v : V) :
    rigidityRank (cliqueOn (C.val ∩ Finset.univ)) p =
      rigidityRank (cliqueOn (C.val ∩ Finset.univ.erase v)) p +
        if v ∈ C.val then 3 else 0 := by
  have hinter : C.val ∩ Finset.univ.erase v = C.val.erase v := by
    ext w
    simp [and_comm]
  change ∀ H : SimpleGraph V, rigidityRank H p = genericRigidityRank H 3 at hgen
  simp only [Finset.inter_univ, hinter, hgen]
  by_cases hv : v ∈ C.val
  · rw [if_pos hv]
    have hcard := C.property.1
    have hC : genericRigidityRank (cliqueOn C.val) 3 + 6 = 3 * C.val.card := by
      rw [cliqueOn_eq_liftComplete, genericRigidityRank_liftGraph]
      simpa only [Fintype.card_coe] using
        (genericCompleteRank_add_six (V := C.val) (by simpa using (show 3 ≤ C.val.card by omega)))
    have hD : genericRigidityRank (cliqueOn (C.val.erase v)) 3 + 6 =
        3 * (C.val.erase v).card := by
      rw [cliqueOn_eq_liftComplete, genericRigidityRank_liftGraph]
      simpa only [Fintype.card_coe] using
        (genericCompleteRank_add_six (V := C.val.erase v) (by
          simp only [Fintype.card_coe, Finset.card_erase_of_mem hv]
          omega))
    rw [Finset.card_erase_of_mem hv] at hD
    omega
  · rw [if_neg hv, Finset.erase_eq_of_notMem hv, add_zero]

/-- The last assertion of Proposition 6.2, in subtraction-free form.
It holds for every maximum-rank, geometrically general placement. -/
theorem vertexLoadProjection_rank_add_deletionRankDrop
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) (v : V) :
    Module.finrank ℝ (vertexLoadProjection G p v).range + deletionRankDrop G v =
      3 * bodyMultiplicity G v := by
  have hfull := body_load_rank_identity G hG p hp Finset.univ
  have hdeleted := body_load_rank_identity G hG p hp (Finset.univ.erase v)
  have hproject := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := compatibleBodyLoads G p Finset.univ)
    (V₂ := Body G → Vec3) (vertexLoadProjection G p v)
  rw [(vertexLoadProjectionKernelEquiv G p v).finrank_eq] at hproject
  have hsum := Finset.sum_congr rfl (fun C (_ : C ∈ (Finset.univ : Finset (Body G))) =>
    complete_body_deletion_rank G p hgen C v)
  have hcount : (∑ C : Body G, if v ∈ C.val then 3 else 0) =
      3 * bodyMultiplicity G v := by
    simp only [← Finset.sum_filter, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, bodyMultiplicity, mul_comm]
  rw [Finset.sum_add_distrib, hcount] at hsum
  have hwhole : maskedGraph G Finset.univ = G := by ext a b; simp [maskedGraph]
  have haway : maskedGraph G (Finset.univ.erase v) = isolateVertex G v := by
    ext a b
    simp [maskedGraph, isolateVertex]
  have hdgen := generic_deletedPlacement p hgen v
  rw [hwhole, hgen] at hfull
  rw [haway, rigidityRank_isolateVertex, hdgen] at hdeleted
  have hle : genericRigidityRank (deletedGraph G v) 3 ≤ genericRigidityRank G 3 := by
    have hmono := rigidityRank_mono (isolateVertex_le G v) p
    rwa [rigidityRank_isolateVertex, hgen, hdgen] at hmono
  unfold deletionRankDrop
  omega

theorem vertexLoadProjection_rank_eq
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) (v : V) :
    Module.finrank ℝ (vertexLoadProjection G p v).range =
      3 * bodyMultiplicity G v - deletionRankDrop G v := by
  have h := vertexLoadProjection_rank_add_deletionRankDrop G hG p hgen hp v
  omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0002

section BundleSource0003
/- Source: Papers/RigidityTwoBodyLoads.lean -/



@[expose] public section

/-!
# Loads at a vertex belonging to exactly two bodies

The two bodies below are the actual maximal cliques of the graph. Their
load projection is evaluation on the ordinary compatible body-load
space, with its literal force and moment equations.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The two distinct maximal bodies containing an actual graph vertex. -/
structure TwoBodyPin (G : SimpleGraph V) (v : V) where
  left : Body G
  right : Body G
  distinct : left ≠ right
  left_mem : v ∈ left.val
  right_mem : v ∈ right.val
  exhaustive : ∀ C : Body G, v ∈ C.val → C = left ∨ C = right

theorem TwoBodyPin.bodyMultiplicity_eq_two
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) :
    bodyMultiplicity G v = 2 := by
  have heq : (Finset.univ.filter fun C : Body G => v ∈ C.val) =
      {Q.left, Q.right} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact Q.exhaustive C
    · rintro (rfl | rfl)
      · exact Q.left_mem
      · exact Q.right_mem
  rw [bodyMultiplicity, heq, Finset.card_pair Q.distinct]

theorem compatible_load_zero_outside_body
    (G : SimpleGraph V) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ) (C : Body G)
    (v : V) (hv : v ∉ C.val) : (F.val C).val v = 0 := by
  apply (F.val C).property.2 v
  simpa only [Finset.inter_univ] using hv

/-- The load on the first of the two incident bodies. -/
def TwoBodyPin.loadProjection
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (p : Placement V 3) :
    compatibleBodyLoads G p Finset.univ →ₗ[ℝ] Vec3 where
  toFun F := (F.val Q.left).val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem TwoBodyPin.load_sum_eq_pair
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ) :
    (∑ C : Body G, (F.val C).val v) =
      (F.val Q.left).val v + (F.val Q.right).val v := by
  have hsum : (∑ C ∈ ({Q.left, Q.right} : Finset (Body G)), (F.val C).val v) =
      ∑ C : Body G, (F.val C).val v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro C _ hC
    apply compatible_load_zero_outside_body G p F C v
    intro hv
    rcases Q.exhaustive C hv with h | h
    · exact hC (by simp [h])
    · exact hC (by simp [h])
  simpa [Q.distinct] using hsum.symm

theorem TwoBodyPin.load_right_eq_neg_left
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (p : Placement V 3)
    (F : compatibleBodyLoads G p Finset.univ) :
    (F.val Q.right).val v = -(Q.loadProjection p F) := by
  apply add_eq_zero_iff_eq_neg.mp
  have hsum := (mem_compatibleBodyLoads_iff G p Finset.univ F.val).mp F.property v
  rw [Q.load_sum_eq_pair p F] at hsum
  change (F.val Q.right).val v + (F.val Q.left).val v = 0
  simpa only [add_comm] using hsum

/-- Cancellation and the exact two-body incidence make one body's
vanishing equivalent to vanishing of every body load at this vertex. -/
theorem TwoBodyPin.ker_loadProjection
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (p : Placement V 3) :
    (Q.loadProjection p).ker = (vertexLoadProjection G p v).ker := by
  ext F
  constructor
  · intro hF
    have hleft : (F.val Q.left).val v = 0 := LinearMap.mem_ker.mp hF
    have hsum := (mem_compatibleBodyLoads_iff G p Finset.univ F.val).mp F.property v
    have hright : (F.val Q.right).val v = 0 := by
      rw [Finset.sum_eq_single Q.right] at hsum
      · exact hsum
      · intro C _ hC
        by_cases hv : v ∈ C.val
        · rcases Q.exhaustive C hv with rfl | h
          · exact hleft
          · exact False.elim (hC h)
        · exact compatible_load_zero_outside_body G p F C v hv
      · simp
    rw [LinearMap.mem_ker]
    funext C
    by_cases hv : v ∈ C.val
    · rcases Q.exhaustive C hv with rfl | rfl
      · exact hleft
      · exact hright
    · exact compatible_load_zero_outside_body G p F C v hv
  · intro hF
    exact congrFun (LinearMap.mem_ker.mp hF) Q.left

theorem TwoBodyPin.loadProjection_rank_eq_vertex_rank
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (p : Placement V 3) :
    Module.finrank ℝ (Q.loadProjection p).range =
      Module.finrank ℝ (vertexLoadProjection G p v).range := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := compatibleBodyLoads G p Finset.univ)
    (V₂ := Vec3) (Q.loadProjection p)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := compatibleBodyLoads G p Finset.univ)
    (V₂ := Body G → Vec3) (vertexLoadProjection G p v)
  rw [Q.ker_loadProjection p] at h₁
  omega

/-- The precise dimension relation before natural-number subtraction. -/
theorem TwoBodyPin.loadProjection_rank_add_drop
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v)
    (hG : K4Covered G) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) :
    Module.finrank ℝ (Q.loadProjection p).range + deletionRankDrop G v = 6 := by
  rw [Q.loadProjection_rank_eq_vertex_rank p,
    vertexLoadProjection_rank_add_deletionRankDrop G hG p hgen hp v,
    Q.bodyMultiplicity_eq_two]

/-- A two-body pin of the minimal counterexample transmits at most one
independent force. This is an actual load-space result. -/
theorem TwoBodyPin.loadProjection_rank_le_one
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    Module.finrank ℝ (Q.loadProjection p).range ≤ 1 := by
  have h := Q.loadProjection_rank_add_drop M.covered p hgen hp
  have hδ := M.five_le_deletionRankDrop v
  omega

/-- At every nonsoft two-body pin the actual body force vanishes. -/
theorem TwoBodyPin.loadProjection_eq_zero_of_drop_ne_five
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : deletionRankDrop M.graph v ≠ 5) : Q.loadProjection p = 0 := by
  have h := Q.loadProjection_rank_add_drop M.covered p hgen hp
  have hlow := M.five_le_deletionRankDrop v
  have hrank : Module.finrank ℝ (Q.loadProjection p).range = 0 := by omega
  exact LinearMap.range_eq_bot.mp ((Submodule.finrank_eq_zero).mp hrank)

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0003

section BundleSource0004
/- Source: Papers/RigidityFiberSum.lean -/





@[expose] public section

/-!
# Literal duplicate coefficients in a finite incidence map

The map adds coefficients of occurrences with the same underlying
index. Its kernel is exactly the span of opposite coefficients on two
occurrences of one index. Thus the duplicate-edge subspace below will
have its ordinary meaning, rather than being defined by the desired
stress quotient.

The construction applies to arbitrary finite incidence fibers.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open scoped Classical BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def fiberSum (f : I → J) : (I → K) →ₗ[K] (J → K) where
  toFun a := ∑ i, a i • Pi.single (f i) 1
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem fiberSum_apply (f : I → J) (a : I → K) :
    fiberSum f a = ∑ i, a i • Pi.single (f i) 1 := rfl

@[simp] theorem fiberSum_single (f : I → J) (i : I) (c : K) :
    fiberSum f (Pi.single i c) = Pi.single (f i) c := by
  rw [fiberSum_apply, Finset.sum_eq_single i]
  · simp [← Pi.single_smul]
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

theorem fiberSum_coordinate (f : I → J) (a : I → K) (j : J) :
    fiberSum f a j = ∑ i, if f i = j then a i else 0 := by
  simp only [fiberSum_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = j
  · subst j
    simp
  · simp [Pi.single_eq_of_ne (Ne.symm h), h]

theorem sum_coordinate_units (a : I → K) :
    (∑ i, a i • Pi.single i 1) = a := by
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single a

theorem fiberSum_comp {L : Type*} [Fintype L] (f : I → J) (g : J → L)
    (a : I → K) : fiberSum g (fiberSum f a) = fiberSum (g ∘ f) a := by
  rw [fiberSum_apply f, map_sum, fiberSum_apply (g ∘ f)]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, fiberSum_single g (f i) (1 : K)]
  rfl

theorem fiberSum_surjective (f : I → J) (hf : Function.Surjective f) :
    Function.Surjective (fiberSum (K := K) f) := by
  let r : J → I := fun j => Classical.choose (hf j)
  have hr : ∀ j, f (r j) = j := fun j => Classical.choose_spec (hf j)
  intro a
  refine ⟨fiberSum r a, ?_⟩
  rw [fiberSum_comp, fiberSum_apply]
  simpa only [Function.comp_apply, hr] using sum_coordinate_units a

def duplicateCoefficientSpan (f : I → J) : Submodule K (I → K) :=
  Submodule.span K {a | ∃ i k, f i = f k ∧ a = Pi.single i 1 - Pi.single k 1}

/-- Opposite coefficients on two copies generate every cancellation
among actual occurrences. No restriction on fibre multiplicities is
needed, and empty finite index sets are included. -/
theorem ker_fiberSum_eq_duplicateSpan (f : I → J) (hf : Function.Surjective f) :
    (fiberSum (K := K) f).ker = duplicateCoefficientSpan f := by
  let D : Submodule K (I → K) := duplicateCoefficientSpan f
  have hD : D ≤ (fiberSum f).ker := by
    apply Submodule.span_le.mpr
    rintro a ⟨i,k,hik,rfl⟩
    change fiberSum (K := K) f (Pi.single i 1 - Pi.single k 1) = 0
    rw [map_sub, fiberSum_single f i (1 : K), fiberSum_single f k (1 : K), hik, sub_self]
  apply le_antisymm ?_ hD
  intro a ha
  let r : J → I := fun j => Classical.choose (hf j)
  have hr : ∀ j, f (r j) = j := fun j => Classical.choose_spec (hf j)
  have hunit (i : I) : D.mkQ (Pi.single i 1) = D.mkQ (Pi.single (r (f i)) 1) := by
    apply (Submodule.Quotient.eq D).mpr
    exact Submodule.subset_span ⟨i, r (f i), (hr (f i)).symm, rfl⟩
  have hq : D.mkQ a = D.mkQ (fiberSum r (fiberSum f a)) := by
    conv_lhs => rw [← sum_coordinate_units a]
    rw [map_sum, fiberSum_apply f, map_sum, map_sum]
    simp only [map_smul, fiberSum_single]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => a i • x) (hunit i))
  have ha0 : fiberSum f a = 0 := LinearMap.mem_ker.mp ha
  rw [ha0, map_zero, map_zero] at hq
  exact (Submodule.Quotient.mk_eq_zero D).mp hq

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0004

section BundleSource0005
/- Source: Papers/RigidityCopiedCoefficients.lean -/




@[expose] public section

/-!
# Actual copied bar coefficients and their two surjections

There is one coordinate for each occurrence of an unordered edge in a
complete body fragment.  One map adds occurrences of the same graph
edge; the other takes their ordinary forces separately in every body.
Their force-balance square commutes literally.  Restricting to aggregate
stresses gives surjections onto both the ordinary prefix stress space
and the compatible body-load space.

Both maps retain every occurrence of every actual fragment edge.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

abbrev BodyEdgeOccurrence (G : SimpleGraph V) (T : Finset V) :=
  Σ C : Body G, Edge (cliqueOn (C.val ∩ T))

def underlyingCopiedEdge (G : SimpleGraph V) (T : Finset V)
    (i : BodyEdgeOccurrence G T) : Edge (maskedGraph G T) :=
  edgeInclusion (fragment_le_masked G T i.1) i.2

theorem underlyingCopiedEdge_surjective
    (G : SimpleGraph V) (hG : K4Covered G) (T : Finset V) :
    Function.Surjective (underlyingCopiedEdge G T) := by
  intro e
  have he : (maskedGraph G T).Adj e.val.out.1 e.val.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.val.out_eq]
    exact e.property
  obtain ⟨S, hS, hv, hw⟩ := hG.edge_in_body he.1
  let C : Body G := ⟨S,hS⟩
  let d : Edge (cliqueOn (C.val ∩ T)) :=
    ⟨s(e.val.out.1,e.val.out.2), he.1.ne,
      Finset.mem_inter.mpr ⟨hv,he.2.1⟩,
      Finset.mem_inter.mpr ⟨hw,he.2.2⟩⟩
  exact ⟨⟨C,d⟩, Subtype.ext e.val.out_eq⟩

def copyAggregate (G : SimpleGraph V) (T : Finset V) :
    (BodyEdgeOccurrence G T → ℝ) →ₗ[ℝ] (Edge (maskedGraph G T) → ℝ) :=
  fiberSum (underlyingCopiedEdge G T)

def bodyCopyRestriction (G : SimpleGraph V) (T : Finset V) (C : Body G) :
    (BodyEdgeOccurrence G T → ℝ) →ₗ[ℝ] (Edge (cliqueOn (C.val ∩ T)) → ℝ) :=
  LinearMap.pi fun e => LinearMap.proj ⟨C,e⟩

@[simp] theorem bodyCopyRestriction_apply
    (G : SimpleGraph V) (T : Finset V) (C : Body G)
    (a : BodyEdgeOccurrence G T → ℝ) (e : Edge (cliqueOn (C.val ∩ T))) :
    bodyCopyRestriction G T C a e = a ⟨C,e⟩ := rfl

theorem fiberSum_edgeInclusion {H G : SimpleGraph V} (h : H ≤ G)
    (a : Edge H → ℝ) : fiberSum (edgeInclusion h) a = extendEdgeCoefficients h a := by
  ext e
  rw [fiberSum_coordinate]
  by_cases he : e.val ∈ H.edgeSet
  · let d : Edge H := ⟨e.val,he⟩
    have hed : e = edgeInclusion h d := rfl
    rw [hed, extendEdgeCoefficients_inside]
    simp only [(edgeInclusion h).injective.eq_iff]
    simp
  · rw [extendEdgeCoefficients_outside h a e he]
    apply Finset.sum_eq_zero
    intro d _
    rw [if_neg]
    intro hd
    exact he (congrArg Subtype.val hd ▸ d.property)

theorem copyAggregate_eq_sum_extensions
    (G : SimpleGraph V) (T : Finset V) (a : BodyEdgeOccurrence G T → ℝ) :
    copyAggregate G T a = ∑ C : Body G,
      extendEdgeCoefficients (fragment_le_masked G T C) (bodyCopyRestriction G T C a) := by
  unfold copyAggregate
  rw [fiberSum_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  exact fiberSum_edgeInclusion (fragment_le_masked G T C) (bodyCopyRestriction G T C a)

theorem forceOperator_extendEdgeCoefficients {H G : SimpleGraph V}
    (h : H ≤ G) (p : Placement V 3) (a : Edge H → ℝ) :
    forceOperator G p (extendEdgeCoefficients h a) = forceOperator H p a := by
  apply loadWorkEquiv.injective
  rw [loadWork_forceOperator, loadWork_forceOperator, stressOperator_extendEdgeCoefficients]

/-- Take the actual bar loads separately in every body occurrence. -/
def bodyCopyForces (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (BodyEdgeOccurrence G T → ℝ) →ₗ[ℝ] BodyBalancedFamily G p T :=
  LinearMap.pi fun C =>
    ((forceOperator (cliqueOn (C.val ∩ T)) p).codRestrict
      (balancedLoadsOn p (C.val ∩ T)) (fun a =>
        ⟨forceOperator_balanced _ p a, clique_force_zero_outside p (C.val ∩ T) a⟩)).comp
      (bodyCopyRestriction G T C)

@[simp] theorem bodyCopyForces_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) (C : Body G) :
    (bodyCopyForces G p T a C).val =
      forceOperator (cliqueOn (C.val ∩ T)) p (bodyCopyRestriction G T C a) := rfl

theorem bodyCopyForces_surjective
    (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Function.Surjective (bodyCopyForces G p T) := by
  intro F
  have hex (C : Body G) : ∃ a,
      forceOperator (cliqueOn (C.val ∩ T)) p a = (F C).val := by
    have hm : (F C).val ∈ (forceOperator (cliqueOn (C.val ∩ T)) p).range :=
      (range_clique_forceOperator p hp (C.val ∩ T)).ge (F C).property
    exact hm
  let a : BodyEdgeOccurrence G T → ℝ := fun i => Classical.choose (hex i.1) i.2
  refine ⟨a, ?_⟩
  funext C
  apply Subtype.ext
  exact Classical.choose_spec (hex C)

/-- Literal commutation of the bar-force square, before any quotient. -/
theorem totalBodyLoad_bodyCopyForces
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) :
    totalBodyLoad G p T (bodyCopyForces G p T a) =
      forceOperator (maskedGraph G T) p (copyAggregate G T a) := by
  rw [totalBodyLoad_apply, copyAggregate_eq_sum_extensions, map_sum]
  exact Finset.sum_congr rfl (fun C _ =>
    (forceOperator_extendEdgeCoefficients (fragment_le_masked G T C) p
      (bodyCopyRestriction G T C a)).symm)

def compatibleCopiedCoefficients (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (BodyEdgeOccurrence G T → ℝ) :=
  (StressSpace (maskedGraph G T) p).comap (copyAggregate G T)

theorem mem_compatibleCopiedCoefficients_iff
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) :
    a ∈ compatibleCopiedCoefficients G p T ↔
      bodyCopyForces G p T a ∈ compatibleBodyLoads G p T := by
  rw [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_bodyCopyForces,
    forceOperator_eq_zero_iff]
  rfl

def copiedToStress (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    compatibleCopiedCoefficients G p T →ₗ[ℝ] StressSpace (maskedGraph G T) p :=
  ((copyAggregate G T).comp (compatibleCopiedCoefficients G p T).subtype).codRestrict
    (StressSpace (maskedGraph G T) p) (fun a => a.property)

def copiedToLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    compatibleCopiedCoefficients G p T →ₗ[ℝ] compatibleBodyLoads G p T :=
  ((bodyCopyForces G p T).comp (compatibleCopiedCoefficients G p T).subtype).codRestrict
    (compatibleBodyLoads G p T) (fun a =>
      (mem_compatibleCopiedCoefficients_iff G p T a.val).mp a.property)

@[simp] theorem copiedToStress_val
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : compatibleCopiedCoefficients G p T) :
    (copiedToStress G p T a).val = copyAggregate G T a.val := rfl

@[simp] theorem copiedToLoads_val
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : compatibleCopiedCoefficients G p T) :
    (copiedToLoads G p T a).val = bodyCopyForces G p T a.val := rfl

theorem copiedToStress_surjective
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V) :
    Function.Surjective (copiedToStress G p T) := by
  intro s
  obtain ⟨a,ha⟩ := fiberSum_surjective (underlyingCopiedEdge G T)
    (underlyingCopiedEdge_surjective G hG T) s.val
  have hm : a ∈ compatibleCopiedCoefficients G p T := by
    change copyAggregate G T a ∈ StressSpace (maskedGraph G T) p
    rw [show copyAggregate G T a = s.val from ha]
    exact s.property
  exact ⟨⟨a,hm⟩, Subtype.ext ha⟩

theorem copiedToLoads_surjective
    (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Function.Surjective (copiedToLoads G p T) := by
  intro F
  obtain ⟨a,ha⟩ := bodyCopyForces_surjective G p hp T F.val
  have hm : a ∈ compatibleCopiedCoefficients G p T :=
    (mem_compatibleCopiedCoefficients_iff G p T a).mpr (ha.symm ▸ F.property)
  exact ⟨⟨a,hm⟩, Subtype.ext ha⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0005

section BundleSource0006
/- Source: Papers/RigidityTwoQuotients.lean -/



@[expose] public section

/-!
# The two exact sequences of the body-load construction

If the same coefficient space maps onto a stress space and a load
space, quotienting either image by the image of the other kernel gives
the same vector space.  This is the ordinary first isomorphism theorem
applied twice.  The proof retains both actual maps; equality of
dimensions is not used as a substitute for the induced equivalence.

The induced quotient map is identified on every source coefficient.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

variable {K E F H : Type*} [Field K]
  [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
  [AddCommGroup H] [Module K H]

/-- The common source modulo the sum of the two kernels is the quotient
of the first image by the second kernel's image. -/
def commonKernelQuotientEquiv
    (f : E →ₗ[K] F) (g : E →ₗ[K] H) (hf : Function.Surjective f) :
    (E ⧸ (f.ker ⊔ g.ker)) ≃ₗ[K] (F ⧸ g.ker.map f) := by
  let q : E →ₗ[K] (F ⧸ g.ker.map f) := (g.ker.map f).mkQ.comp f
  have hq : Function.Surjective q := (g.ker.map f).mkQ_surjective.comp hf
  have hk : q.ker = f.ker ⊔ g.ker := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, sup_comm]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)

@[simp] theorem commonKernelQuotientEquiv_mk
    (f : E →ₗ[K] F) (g : E →ₗ[K] H) (hf : Function.Surjective f) (x : E) :
    commonKernelQuotientEquiv f g hf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := by
  simp [commonKernelQuotientEquiv]

/-- The quotient equivalence obtained from two genuine surjections out
of a common source.  In Proposition 6.2 the source is the copied bar
coefficients whose aggregate is an ordinary stress. -/
def twoSurjectionsQuotientEquiv
    (f : E →ₗ[K] F) (g : E →ₗ[K] H)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (F ⧸ g.ker.map f) ≃ₗ[K] (H ⧸ f.ker.map g) :=
  (commonKernelQuotientEquiv f g hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm f.ker g.ker)).trans
      (commonKernelQuotientEquiv g f hg))

@[simp] theorem twoSurjectionsQuotientEquiv_mk
    (f : E →ₗ[K] F) (g : E →ₗ[K] H)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (x : E) :
    twoSurjectionsQuotientEquiv f g hf hg (Submodule.Quotient.mk (f x)) =
      Submodule.Quotient.mk (g x) := by
  rw [← commonKernelQuotientEquiv_mk f g hf x]
  simp only [twoSurjectionsQuotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, Submodule.quotEquivOfEq_mk]
  exact commonKernelQuotientEquiv_mk g f hg x

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined04/block_0006/Consolidated/RigidityCombined04.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined04/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityBodyLoadQuotient.lean -/




@[expose] public section

/-!
# The actual stress / compatible-load quotient

The denominator on the stress side is the image of the ordinary local
complete-fragment stress spaces.  The denominator on the load side is
the span of loads induced by opposite coefficients on two copies of
one actual edge.  The common copied-coefficient construction identifies
these literal spaces by the two first isomorphism theorems.

The result includes every induced prefix and all fragment sizes.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

abbrev BodyFragmentStresses (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :=
  ∀ C : Body G, StressSpace (cliqueOn (C.val ∩ T)) p

def bodyStressCoefficients (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyFragmentStresses G p T →ₗ[ℝ] (BodyEdgeOccurrence G T → ℝ) where
  toFun a i := (a i.1).val i.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bodyCopyForces_bodyStressCoefficients
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyFragmentStresses G p T) :
    bodyCopyForces G p T (bodyStressCoefficients G p T a) = 0 := by
  funext C
  apply Subtype.ext
  exact (forceOperator_eq_zero_iff _ p (a C).val).mpr (a C).property

def bodyStressCompatible (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyFragmentStresses G p T →ₗ[ℝ] compatibleCopiedCoefficients G p T :=
  (bodyStressCoefficients G p T).codRestrict (compatibleCopiedCoefficients G p T) (by
    intro a
    rw [mem_compatibleCopiedCoefficients_iff, bodyCopyForces_bodyStressCoefficients]
    exact Submodule.zero_mem _)

/-- Sum actual complete-fragment stresses in the ordinary prefix graph. -/
def localPrefixStressSum (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyFragmentStresses G p T →ₗ[ℝ] StressSpace (maskedGraph G T) p :=
  (copiedToStress G p T).comp (bodyStressCompatible G p T)

theorem localPrefixStressSum_val
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyFragmentStresses G p T) :
    (localPrefixStressSum G p T a).val = ∑ C : Body G,
      extendEdgeCoefficients (fragment_le_masked G T C) (a C).val := by
  change copyAggregate G T (bodyStressCoefficients G p T a) = _
  exact copyAggregate_eq_sum_extensions G T (bodyStressCoefficients G p T a)

def localPrefixStresses (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (StressSpace (maskedGraph G T) p) :=
  (localPrefixStressSum G p T).range

theorem kernel_loads_image_eq_local
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (copiedToLoads G p T).ker.map (copiedToStress G p T) = localPrefixStresses G p T := by
  ext s
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hF : bodyCopyForces G p T a.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    let b : BodyFragmentStresses G p T := fun C =>
      ⟨bodyCopyRestriction G T C a.val, (forceOperator_eq_zero_iff _ p _).mp
        (congrArg (fun F : BodyBalancedFamily G p T => (F C).val) hF)⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨a,rfl⟩
    refine ⟨bodyStressCompatible G p T a, ?_, rfl⟩
    change copiedToLoads G p T (bodyStressCompatible G p T a) = 0
    apply Subtype.ext
    exact bodyCopyForces_bodyStressCoefficients G p T a

/-- The actual body-load image of all cancelling copied coefficients. -/
def duplicateBodyLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (BodyBalancedFamily G p T) :=
  (copyAggregate G T).ker.map (bodyCopyForces G p T)

/-- These are precisely the spans of ordinary opposite-copy edge modes,
as in the paper's definition of D(T). -/
theorem duplicateBodyLoads_eq_span_opposite_copies
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V) :
    duplicateBodyLoads G p T = Submodule.span ℝ
      {F | ∃ i k : BodyEdgeOccurrence G T,
        underlyingCopiedEdge G T i = underlyingCopiedEdge G T k ∧
          F = bodyCopyForces G p T (Pi.single i 1 - Pi.single k 1)} := by
  unfold duplicateBodyLoads copyAggregate
  rw [ker_fiberSum_eq_duplicateSpan _ (underlyingCopiedEdge_surjective G hG T),
    duplicateCoefficientSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨a,⟨i,k,hik,rfl⟩,rfl⟩
    refine ⟨i,k,hik,?_⟩
    apply congrArg (bodyCopyForces G p T)
    funext e
    by_cases hei : e = i <;> by_cases hek : e = k <;>
      simp [Pi.single_apply, hei, hek]
  · rintro ⟨i,k,hik,rfl⟩
    refine ⟨(Pi.single i (1 : ℝ) - Pi.single k 1 : BodyEdgeOccurrence G T → ℝ),
      ⟨i,k,hik,?_⟩, ?_⟩
    · funext e
      by_cases hei : e = i <;> by_cases hek : e = k <;>
        simp [Pi.single_apply, hei, hek]
    · rfl

theorem duplicateBodyLoads_le_compatible
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    duplicateBodyLoads G p T ≤ compatibleBodyLoads G p T := by
  rintro F ⟨a,ha,rfl⟩
  rw [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_bodyCopyForces,
    LinearMap.mem_ker.mp ha, map_zero]

/-- D(T) as a subspace of the literal compatible-load space C(T). -/
def duplicateCompatibleLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (compatibleBodyLoads G p T) :=
  (duplicateBodyLoads G p T).comap (compatibleBodyLoads G p T).subtype

theorem kernel_stress_image_eq_duplicates
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (copiedToStress G p T).ker.map (copiedToLoads G p T) =
      duplicateCompatibleLoads G p T := by
  ext F
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a.val, ?_, rfl⟩
    exact congrArg Subtype.val (LinearMap.mem_ker.mp ha)
  · rintro ⟨a,ha,hF⟩
    have hm : a ∈ compatibleCopiedCoefficients G p T := by
      change copyAggregate G T a ∈ StressSpace (maskedGraph G T) p
      rw [LinearMap.mem_ker.mp ha]
      exact Submodule.zero_mem _
    refine ⟨⟨a,hm⟩, ?_, Subtype.ext hF⟩
    change copiedToStress G p T ⟨a,hm⟩ = 0
    exact Subtype.ext (LinearMap.mem_ker.mp ha)

/-- The ordinary real-module quotient instance, with its ambient space explicit. -/
local instance compatibleBodyLoadsHasQuotient
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    HasQuotient (compatibleBodyLoads G p T)
      (Submodule ℝ (compatibleBodyLoads G p T)) :=
  Submodule.hasQuotient (R := ℝ) (M := compatibleBodyLoads G p T)

set_option diagnostics true in
/-- Equation (2) of Proposition 6.2, with actual ordinary stresses on
the induced prefix and actual opposite-copy load modes. -/
def prefixStressQuotientEquivBodyLoads
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    (StressSpace (maskedGraph G T) p ⧸ localPrefixStresses G p T) ≃ₗ[ℝ]
      (compatibleBodyLoads G p T ⧸ duplicateCompatibleLoads G p T) := by
  let f : compatibleCopiedCoefficients G p T →ₗ[ℝ]
      StressSpace (maskedGraph G T) p := copiedToStress G p T
  let g : compatibleCopiedCoefficients G p T →ₗ[ℝ]
      compatibleBodyLoads G p T := copiedToLoads G p T
  let first : (StressSpace (maskedGraph G T) p ⧸ localPrefixStresses G p T) ≃ₗ[ℝ]
      (StressSpace (maskedGraph G T) p ⧸ g.ker.map f) :=
    Submodule.quotEquivOfEq (R := ℝ) (M := StressSpace (maskedGraph G T) p)
      (localPrefixStresses G p T) (g.ker.map f)
      (kernel_loads_image_eq_local G p T).symm
  let middle :=
    @twoSurjectionsQuotientEquiv
      ℝ
      (compatibleCopiedCoefficients G p T)
      (StressSpace (maskedGraph G T) p)
      (compatibleBodyLoads G p T)
      (inferInstance : Field ℝ)
      (inferInstance : AddCommGroup (compatibleCopiedCoefficients G p T))
      (inferInstance : Module ℝ (compatibleCopiedCoefficients G p T))
      (inferInstance : AddCommGroup (StressSpace (maskedGraph G T) p))
      (inferInstance : Module ℝ (StressSpace (maskedGraph G T) p))
      (inferInstance : AddCommGroup (compatibleBodyLoads G p T))
      (inferInstance : Module ℝ (compatibleBodyLoads G p T))
      f g
      (copiedToStress_surjective G hG p T)
      (copiedToLoads_surjective G p hp T)
  let last :=
    @Submodule.quotEquivOfEq
      ℝ (compatibleBodyLoads G p T)
      (inferInstance : Ring ℝ)
      (inferInstance : AddCommGroup (compatibleBodyLoads G p T))
      (inferInstance : Module ℝ (compatibleBodyLoads G p T))
      (f.ker.map g) (duplicateCompatibleLoads G p T)
      (kernel_stress_image_eq_duplicates G p T)
  exact first.trans (middle.trans last)

theorem prefixStressQuotientEquivBodyLoads_copied
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : compatibleCopiedCoefficients G p T) :
    prefixStressQuotientEquivBodyLoads G hG p hp T
      (Submodule.Quotient.mk (copiedToStress G p T a)) =
        Submodule.Quotient.mk (copiedToLoads G p T a) := by
  simp [prefixStressQuotientEquivBodyLoads]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0007

section BundleSource0008
/- Source: Papers/RigidityHingeLoads.lean -/




@[expose] public section

/-!
# The actual duplicate-edge mode at a two-body hinge

An ordinary edge shared by two bodies has two copied coefficients. Give
them the coefficients `1` and `-1`. They cancel in the graph, while their
body loads transmit the line force along that edge. The rank formula
then shows that every load at a two-body hinge is a multiple of this
literal duplicate-edge mode.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin Matrix
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The ordinary pair of opposite axial forces exerted by one bar. -/
def barLoad (p : Placement V 3) (v w : V) : Velocity V 3 :=
  Pi.single v (p v - p w) - Pi.single w (p v - p w)

theorem barLoad_work (p u : Placement V 3) (v w : V) :
    loadWorkEquiv (barLoad p v w) u = edgeConstraint p u v w := by
  rw [loadWorkEquiv_apply]
  simp only [barLoad, Pi.sub_apply, sub_dotProduct, Finset.sum_sub_distrib]
  have hsingle (x : V) (z : Vec3) :
      (∑ y : V, (Pi.single x z : V → Vec3) y ⬝ᵥ u y) = z ⬝ᵥ u x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Pi.single_apply, hy, Ne.symm hy]
    · simp
  rw [hsingle, hsingle, ← dotProduct_sub]
  rfl

theorem forceOperator_single_bar
    (G : SimpleGraph V) (p : Placement V 3) (v w : V) (hvw : G.Adj v w) :
    forceOperator G p (Pi.single (⟨s(v,w),hvw⟩ : Edge G) 1) = barLoad p v w := by
  apply loadWorkEquiv.injective
  apply LinearMap.ext
  intro u
  rw [loadWork_forceOperator, stressOperator_single, unorderedFunctional_mk, barLoad_work]

@[simp] theorem barLoad_left (p : Placement V 3) {v w : V} (hvw : v ≠ w) :
    barLoad p v w v = p v - p w := by
  simp [barLoad, hvw]

@[simp] theorem barLoad_right (p : Placement V 3) {v w : V} (hvw : v ≠ w) :
    barLoad p v w w = -(p v - p w) := by
  simp [barLoad, hvw.symm]

theorem barLoad_outside (p : Placement V 3) {v w z : V}
    (hzv : z ≠ v) (hzw : z ≠ w) : barLoad p v w z = 0 := by
  simp [barLoad, hzv, hzw]

theorem bodyCopyRestriction_single_same
    (G : SimpleGraph V) (T : Finset V) (C : Body G)
    (e : Edge (cliqueOn (C.val ∩ T))) (c : ℝ) :
    bodyCopyRestriction G T C (Pi.single (⟨C,e⟩ : BodyEdgeOccurrence G T) c) =
      Pi.single e c := by
  ext f
  by_cases hfe : f = e <;>
    simp [bodyCopyRestriction_apply, Pi.single_apply, hfe]

theorem bodyCopyRestriction_single_other
    (G : SimpleGraph V) (T : Finset V) (C D : Body G) (hCD : C ≠ D)
    (e : Edge (cliqueOn (D.val ∩ T))) (c : ℝ) :
    bodyCopyRestriction G T C (Pi.single (⟨D,e⟩ : BodyEdgeOccurrence G T) c) = 0 := by
  ext f
  have hne : (⟨C,f⟩ : BodyEdgeOccurrence G T) ≠ ⟨D,e⟩ := by
    intro h
    exact hCD (congrArg Sigma.fst h)
  simp [bodyCopyRestriction_apply, Pi.single_eq_of_ne hne]

variable {G : SimpleGraph V} {v : V}

/-- A second common vertex of the two actual incident bodies. -/
structure TwoBodyPin.Hinge (Q : TwoBodyPin G v) where
  partner : V
  distinct : v ≠ partner
  left_mem : partner ∈ Q.left.val
  right_mem : partner ∈ Q.right.val

def TwoBodyPin.Hinge.leftEdge {Q : TwoBodyPin G v} (H : Q.Hinge) :
    Edge (cliqueOn (Q.left.val ∩ Finset.univ)) :=
  ⟨s(v,H.partner), H.distinct,
    Finset.mem_inter.mpr ⟨Q.left_mem, Finset.mem_univ _⟩,
    Finset.mem_inter.mpr ⟨H.left_mem, Finset.mem_univ _⟩⟩

def TwoBodyPin.Hinge.rightEdge {Q : TwoBodyPin G v} (H : Q.Hinge) :
    Edge (cliqueOn (Q.right.val ∩ Finset.univ)) :=
  ⟨s(v,H.partner), H.distinct,
    Finset.mem_inter.mpr ⟨Q.right_mem, Finset.mem_univ _⟩,
    Finset.mem_inter.mpr ⟨H.right_mem, Finset.mem_univ _⟩⟩

def TwoBodyPin.Hinge.coefficients {Q : TwoBodyPin G v} (H : Q.Hinge) :
    BodyEdgeOccurrence G Finset.univ → ℝ :=
  Pi.single ⟨Q.left,H.leftEdge⟩ 1 - Pi.single ⟨Q.right,H.rightEdge⟩ 1

theorem TwoBodyPin.Hinge.coefficients_cancel {Q : TwoBodyPin G v} (H : Q.Hinge) :
    H.coefficients ∈ (copyAggregate G Finset.univ).ker := by
  rw [LinearMap.mem_ker]
  dsimp only [copyAggregate, fiberSum]
  have heq : underlyingCopiedEdge G Finset.univ ⟨Q.left,H.leftEdge⟩ =
      underlyingCopiedEdge G Finset.univ ⟨Q.right,H.rightEdge⟩ := Subtype.ext rfl
  simp only [TwoBodyPin.Hinge.coefficients, Pi.sub_apply, sub_smul,
    Finset.sum_sub_distrib]
  simp [Pi.single_apply, sub_smul, Finset.sum_sub_distrib, heq]

/-- The load mode induced by the actual opposite copied edge coefficients. -/
def TwoBodyPin.Hinge.mode {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3) :
    compatibleBodyLoads G p Finset.univ :=
  ⟨bodyCopyForces G p Finset.univ H.coefficients,
    duplicateBodyLoads_le_compatible G p Finset.univ
      ⟨H.coefficients, H.coefficients_cancel, rfl⟩⟩

theorem TwoBodyPin.Hinge.mode_mem_duplicates
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3) :
    H.mode p ∈ duplicateCompatibleLoads G p Finset.univ :=
  ⟨H.coefficients, H.coefficients_cancel, rfl⟩

theorem TwoBodyPin.Hinge.mode_left
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3) :
    ((H.mode p).val Q.left).val = barLoad p v H.partner := by
  change forceOperator _ p (bodyCopyRestriction G Finset.univ Q.left H.coefficients) = _
  rw [TwoBodyPin.Hinge.coefficients, map_sub, bodyCopyRestriction_single_same,
    bodyCopyRestriction_single_other G Finset.univ Q.left Q.right Q.distinct,
    sub_zero]
  exact forceOperator_single_bar _ p v H.partner H.leftEdge.property

theorem TwoBodyPin.Hinge.mode_right
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3) :
    ((H.mode p).val Q.right).val = -barLoad p v H.partner := by
  change forceOperator _ p (bodyCopyRestriction G Finset.univ Q.right H.coefficients) = _
  rw [TwoBodyPin.Hinge.coefficients, map_sub,
    bodyCopyRestriction_single_other G Finset.univ Q.right Q.left Q.distinct.symm,
    bodyCopyRestriction_single_same, zero_sub, map_neg]
  exact congrArg Neg.neg (forceOperator_single_bar _ p v H.partner H.rightEdge.property)

theorem TwoBodyPin.Hinge.mode_other
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3)
    (C : Body G) (hCl : C ≠ Q.left) (hCr : C ≠ Q.right) :
    ((H.mode p).val C).val = 0 := by
  change forceOperator _ p (bodyCopyRestriction G Finset.univ C H.coefficients) = 0
  rw [TwoBodyPin.Hinge.coefficients, map_sub,
    bodyCopyRestriction_single_other G Finset.univ C Q.left hCl,
    bodyCopyRestriction_single_other G Finset.univ C Q.right hCr,
    sub_self, map_zero]

theorem TwoBodyPin.Hinge.mode_outside
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3)
    (z : V) (hzv : z ≠ v) (hzw : z ≠ H.partner) (C : Body G) :
    ((H.mode p).val C).val z = 0 := by
  by_cases hCl : C = Q.left
  · subst C
    rw [H.mode_left p, barLoad_outside p hzv hzw]
  · by_cases hCr : C = Q.right
    · subst C
      rw [H.mode_right p]
      simp only [Pi.neg_apply, barLoad_outside p hzv hzw, neg_zero]
    · rw [H.mode_other p C hCl hCr]
      rfl

theorem TwoBodyPin.Hinge.loadProjection_mode
    {Q : TwoBodyPin G v} (H : Q.Hinge) (p : Placement V 3) :
    Q.loadProjection p (H.mode p) = p v - p H.partner := by
  change ((H.mode p).val Q.left).val v = _
  rw [H.mode_left p, barLoad_left p H.distinct]

/-- A hinge is necessarily soft in deletion rank, and its complete
one-dimensional load image is the ordinary line along the shared edge. -/
theorem TwoBodyPin.Hinge.rank_and_range
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (H : Q.Hinge) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    deletionRankDrop M.graph v = 5 ∧
      (Q.loadProjection p).range = ℝ ∙ (p v - p H.partner) := by
  have hnonzero : p v - p H.partner ≠ 0 := by
    intro hz
    exact H.distinct (GeneralPosition.InGeneralPosition.injective p hp (sub_eq_zero.mp hz))
  have hmem : p v - p H.partner ∈ (Q.loadProjection p).range :=
    ⟨H.mode p, H.loadProjection_mode p⟩
  have hrle := Q.loadProjection_rank_le_one M p hgen hp
  have hrpos : 0 < Module.finrank ℝ (Q.loadProjection p).range := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨p v - p H.partner, hmem⟩, ?_⟩
    intro hz
    exact hnonzero (congrArg Subtype.val hz)
  have hrank : Module.finrank ℝ (Q.loadProjection p).range = 1 := by omega
  constructor
  · have h := Q.loadProjection_rank_add_drop M.covered p hgen hp
    omega
  · exact eq_span_singleton_of_mem_of_finrank_eq_one hrank hmem hnonzero

/-- Subtracting a genuine duplicate-edge load kills every body copy at
the selected two-body hinge. Every other vertex outside the edge keeps
exactly its original body loads. -/
theorem TwoBodyPin.Hinge.eliminate_load
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (H : Q.Hinge) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads M.graph p Finset.univ) :
    ∃ c : ℝ,
      vertexLoadProjection M.graph p v (F - c • H.mode p) = 0 ∧
      ∀ z, z ≠ v → z ≠ H.partner → ∀ C : Body M.graph,
        ((F - c • H.mode p).val C).val z = (F.val C).val z := by
  have hmem : Q.loadProjection p F ∈ ℝ ∙ (p v - p H.partner) := by
    rw [← (H.rank_and_range M p hgen hp).2]
    exact ⟨F,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_, ?_⟩
  · apply LinearMap.mem_ker.mp
    rw [← Q.ker_loadProjection p, LinearMap.mem_ker,
      map_sub (Q.loadProjection p) F (c • H.mode p),
      map_smul (Q.loadProjection p) c (H.mode p),
      H.loadProjection_mode p, ← hc, sub_self]
  · intro z hzv hzw C
    change (F.val C).val z - c • ((H.mode p).val C).val z = (F.val C).val z
    rw [H.mode_outside p z hzv hzw C, smul_zero, sub_zero]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0008

section BundleSource0009
/- Source: Papers/RigidityPointStressForces.lean -/



@[expose] public section

/-!
# Canonical point-pin forces on the actual graph stress space

A point pin has no duplicated incident edge. Consequently the load on
one of its two bodies is independent of how an ordinary graph stress is
lifted to copied edge coefficients. This file constructs that descended
linear map and proves that a soft point pin gives a nonzero scalar
functional on the ordinary stress space.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin Matrix
open scoped Classical BigOperators

variable {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}

/-- The two incident bodies meet only at the indicated point. -/
def TwoBodyPin.IsPoint (Q : TwoBodyPin G v) : Prop :=
  Q.left.val ∩ Q.right.val = {v}

theorem copied_edge_endpoint_mem_body
    (G : SimpleGraph V) (T : Finset V) (i : BodyEdgeOccurrence G T)
    {x : V} (hx : x ∈ i.2.val) : x ∈ i.1.val := by
  obtain ⟨y,he⟩ := Sym2.mem_iff_exists.mp hx
  have hadj : (cliqueOn (i.1.val ∩ T)).Adj x y := by
    rw [← SimpleGraph.mem_edgeSet, ← he]
    exact i.2.property
  exact (Finset.mem_inter.mp hadj.2.1).1

/-- At a point pin each ordinary incident edge occurs in just one body. -/
theorem TwoBodyPin.IsPoint.occurrence_unique
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint)
    (i k : BodyEdgeOccurrence G Finset.univ)
    (hik : underlyingCopiedEdge G Finset.univ i = underlyingCopiedEdge G Finset.univ k)
    (hv : v ∈ i.2.val) : i = k := by
  have he : i.2.val = k.2.val := congrArg Subtype.val hik
  have hvi : v ∈ i.1.val := copied_edge_endpoint_mem_body G Finset.univ i hv
  have hvk : v ∈ k.1.val := copied_edge_endpoint_mem_body G Finset.univ k (he ▸ hv)
  have hbody : i.1 = k.1 := by
    by_contra hne
    have hinter : i.1.val ∩ k.1.val = {v} := by
      rcases Q.exhaustive i.1 hvi with hi | hi <;>
        rcases Q.exhaustive k.1 hvk with hk | hk
      · exact False.elim (hne (hi.trans hk.symm))
      · simpa only [TwoBodyPin.IsPoint, hi, hk] using hQ
      · simpa only [TwoBodyPin.IsPoint, hi, hk, Finset.inter_comm] using hQ
      · exact False.elim (hne (hi.trans hk.symm))
    obtain ⟨w,hw⟩ := Sym2.mem_iff_exists.mp hv
    have hwi : w ∈ i.2.val := hw.symm ▸ Sym2.mem_mk_right v w
    have hwk : w ∈ k.2.val := he ▸ hwi
    have hwm : w ∈ i.1.val ∩ k.1.val := Finset.mem_inter.mpr
      ⟨copied_edge_endpoint_mem_body G Finset.univ i hwi,
        copied_edge_endpoint_mem_body G Finset.univ k hwk⟩
    rw [hinter, Finset.mem_singleton] at hwm
    have hadj : (cliqueOn (i.1.val ∩ Finset.univ)).Adj v w := by
      rw [← SimpleGraph.mem_edgeSet, ← hw]
      exact i.2.property
    exact hadj.1 hwm.symm
  cases i with
  | mk C e =>
    cases k with
    | mk D f =>
      dsimp only at hbody he
      cases hbody
      congr 1
      exact Subtype.ext he

theorem forceOperator_single_zero_outside
    (G : SimpleGraph V) (p : Placement V 3) (e : Edge G) (v : V)
    (hv : v ∉ e.val) : forceOperator G p (Pi.single e 1) v = 0 := by
  rw [forceOperator_vertex]
  apply Finset.sum_eq_zero
  intro f _
  have hfe : f.val ≠ e := by
    intro h
    exact hv (h ▸ f.property)
  simp only [Pi.single_eq_of_ne hfe, zero_smul]

theorem bodyCopyForces_single_zero_outside
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (i : BodyEdgeOccurrence G T) (v : V) (hv : v ∉ i.2.val) (C : Body G) :
    (bodyCopyForces G p T (Pi.single i 1) C).val v = 0 := by
  cases i with
  | mk D e =>
    by_cases hCD : C = D
    · subst C
      rw [bodyCopyForces_apply, bodyCopyRestriction_single_same]
      exact forceOperator_single_zero_outside _ p e v hv
    · rw [bodyCopyForces_apply, bodyCopyRestriction_single_other G T C D hCD, map_zero]
      rfl

/-- Duplicate loads vanish at a point pin; this is a statement about
the actual opposite-copy span D, not a chosen representative. -/
theorem TwoBodyPin.IsPoint.duplicates_zero
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint) (hG : K4Covered G)
    (p : Placement V 3) (F : BodyBalancedFamily G p Finset.univ)
    (hF : F ∈ duplicateBodyLoads G p Finset.univ) :
    ∀ C : Body G, (F C).val v = 0 := by
  rw [duplicateBodyLoads_eq_span_opposite_copies G hG p Finset.univ] at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨i,k,hik,rfl⟩ := hF
      by_cases heq : i = k
      · subst k
        simp
      · have hvi : v ∉ i.2.val := fun hv => heq (hQ.occurrence_unique i k hik hv)
        have he : i.2.val = k.2.val := congrArg Subtype.val hik
        have hvk : v ∉ k.2.val := by simpa only [he] using hvi
        intro C
        rw [map_sub]
        change (bodyCopyForces G p Finset.univ (Pi.single i 1) C).val v -
          (bodyCopyForces G p Finset.univ (Pi.single k 1) C).val v = 0
        rw [bodyCopyForces_single_zero_outside G p Finset.univ i v hvi C,
          bodyCopyForces_single_zero_outside G p Finset.univ k v hvk C, sub_self]
  | zero => simp
  | add F H hF hH ihF ihH =>
      intro C
      change (F C).val v + (H C).val v = 0
      rw [ihF C, ihH C, add_zero]
  | smul c F hF ih =>
      intro C
      change c • (F C).val v = 0
      rw [ih C, smul_zero]

theorem TwoBodyPin.IsPoint.copied_stress_kernel_le_load_kernel
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3) :
    (copiedToStress G p Finset.univ).ker ≤
      ((Q.loadProjection p).comp (copiedToLoads G p Finset.univ)).ker := by
  intro a ha
  have hd : copiedToLoads G p Finset.univ a ∈
      duplicateCompatibleLoads G p Finset.univ := by
    rw [← kernel_stress_image_eq_duplicates]
    exact ⟨a,ha,rfl⟩
  exact hQ.duplicates_zero hG p _ hd Q.left

/-- The canonical force on the first body, on the ordinary whole-prefix
stress space. `liftOfSurjective` enforces independence from every lift. -/
def TwoBodyPin.pointForceOnWholePrefix
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3) :
    StressSpace (maskedGraph G Finset.univ) p →ₗ[ℝ] Vec3 :=
  (copiedToStress G p Finset.univ).liftOfSurjective
    (copiedToStress_surjective G hG p Finset.univ)
    ⟨(Q.loadProjection p).comp (copiedToLoads G p Finset.univ),
      hQ.copied_stress_kernel_le_load_kernel hG p⟩

@[simp] theorem TwoBodyPin.pointForceOnWholePrefix_copied
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3)
    (a : compatibleCopiedCoefficients G p Finset.univ) :
    Q.pointForceOnWholePrefix hQ hG p (copiedToStress G p Finset.univ a) =
      Q.loadProjection p (copiedToLoads G p Finset.univ a) := by
  exact LinearMap.equivOfSurjective_apply _ _

def wholePrefixStressEquiv (G : SimpleGraph V) (p : Placement V 3) :
    StressSpace (maskedGraph G Finset.univ) p ≃ₗ[ℝ] StressSpace G p := by
  have hG : maskedGraph G Finset.univ = G := by
    ext a b
    simp [maskedGraph]
  rw [hG]

/-- The actual body force of an ordinary graph stress at a point pin. -/
def TwoBodyPin.pointForce
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3) :
    StressSpace G p →ₗ[ℝ] Vec3 :=
  (Q.pointForceOnWholePrefix hQ hG p).comp (wholePrefixStressEquiv G p).symm.toLinearMap

theorem TwoBodyPin.pointForceOnWholePrefix_range
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) :
    (Q.pointForceOnWholePrefix hQ hG p).range = (Q.loadProjection p).range := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    obtain ⟨a,rfl⟩ := copiedToStress_surjective G hG p Finset.univ s
    exact ⟨copiedToLoads G p Finset.univ a, (Q.pointForceOnWholePrefix_copied hQ hG p a).symm⟩
  · rintro ⟨F,rfl⟩
    obtain ⟨a,rfl⟩ := copiedToLoads_surjective G p hp Finset.univ F
    exact ⟨copiedToStress G p Finset.univ a, Q.pointForceOnWholePrefix_copied hQ hG p a⟩

theorem TwoBodyPin.pointForce_range
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) :
    (Q.pointForce hQ hG p).range = (Q.loadProjection p).range := by
  rw [TwoBodyPin.pointForce, LinearMap.range_comp_of_range_eq_top _
    (wholePrefixStressEquiv G p).symm.range, Q.pointForceOnWholePrefix_range hQ hG p hp]

theorem TwoBodyPin.soft_pointForce_rank
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hQ : Q.IsPoint) (hδ : deletionRankDrop M.graph v = 5)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    Module.finrank ℝ (Q.pointForce hQ M.covered p).range = 1 := by
  rw [Q.pointForce_range hQ M.covered p hp]
  have h := Q.loadProjection_rank_add_drop M.covered p hgen hp
  omega

/-- A scalar coordinate for a literal rank-one linear force map. -/
theorem scalar_coordinate_of_rank_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ₗ[ℝ] Vec3) (hrank : Module.finrank ℝ F.range = 1) :
    ∃ (a : Vec3) (lam : E →ₗ[ℝ] ℝ),
      a ≠ 0 ∧ lam ≠ 0 ∧ ∀ x, F x = lam x • a := by
  obtain ⟨a,ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (by omega : 0 < Module.finrank ℝ F.range)
  have ha0 : a.val ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨i,hi⟩ : ∃ i : Fin 3, a.val i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha0 (funext h)
  let lam : E →ₗ[ℝ] ℝ :=
    { toFun x := F x i / a.val i
      map_add' x y := by simp [map_add, add_div]
      map_smul' c x := by simp [map_smul, mul_div_assoc] }
  have hspan : F.range = ℝ ∙ a.val :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrank a.property ha0
  have hlam (x : E) : F x = lam x • a.val := by
    have hx : F x ∈ ℝ ∙ a.val := by rw [← hspan]; exact ⟨x,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
    have hclam : lam x = c := by
      change F x i / a.val i = c
      rw [← hc]
      simp [hi]
    rw [hclam]
    exact hc.symm
  refine ⟨a.val, lam, ha0, ?_, hlam⟩
  intro hz
  obtain ⟨x,hx⟩ := a.property
  have h := hlam x
  rw [hz, LinearMap.zero_apply, zero_smul, hx] at h
  exact ha0 h

/-- Every soft point pin supplies a nonzero scalar on the actual
ordinary stress space, with the corresponding literal force direction. -/
theorem TwoBodyPin.exists_soft_stress_scalar
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hQ : Q.IsPoint) (hδ : deletionRankDrop M.graph v = 5)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    ∃ (a : Vec3) (lam : Module.Dual ℝ (StressSpace M.graph p)),
      a ≠ 0 ∧ lam ≠ 0 ∧ ∀ s, Q.pointForce hQ M.covered p s = lam s • a :=
  scalar_coordinate_of_rank_one _ (Q.soft_pointForce_rank M hQ hδ p hgen hp)

/-- The same scalar construction on the literally equal whole-prefix
stress coordinates used by the copied-edge quotient. -/
theorem TwoBodyPin.exists_soft_wholePrefix_scalar
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hQ : Q.IsPoint) (hδ : deletionRankDrop M.graph v = 5)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    ∃ (a : Vec3)
      (lam : Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)),
      a ≠ 0 ∧ lam ≠ 0 ∧ ∀ s,
        Q.pointForceOnWholePrefix hQ M.covered p s = lam s • a := by
  apply scalar_coordinate_of_rank_one
  rw [Q.pointForceOnWholePrefix_range hQ M.covered p hp]
  have h := Q.loadProjection_rank_add_drop M.covered p hgen hp
  omega

/-- Two distinct bodies through a point pin cannot contain any other
common actual vertex. -/
theorem TwoBodyPin.IsPoint.no_shared_edge
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint)
    (C D : Body G) (hCD : C ≠ D) (hvC : v ∈ C.val) (hvD : v ∈ D.val)
    (w : V) (hwC : w ∈ C.val) (hwD : w ∈ D.val) : w = v := by
  have hinter : C.val ∩ D.val = {v} := by
    rcases Q.exhaustive C hvC with hC | hC <;>
      rcases Q.exhaustive D hvD with hD | hD
    · exact False.elim (hCD (hC.trans hD.symm))
    · simpa only [TwoBodyPin.IsPoint,hC,hD] using hQ
    · simpa only [TwoBodyPin.IsPoint,hC,hD,Finset.inter_comm] using hQ
    · exact False.elim (hCD (hC.trans hD.symm))
  have hw : w ∈ C.val ∩ D.val := Finset.mem_inter.mpr ⟨hwC,hwD⟩
  simpa only [hinter,Finset.mem_singleton] using hw

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0009

section BundleSource0010
/- Source: Papers/RigidityTetrahedronScalars.lean -/



@[expose] public section

/-!
# Scalar transmission on tetrahedron edges

The force at a point pin in a tetrahedral body determines its three
ordinary incident edge coefficients. The statement is proved using
generic independence of three star directions, not by imposing scalar
relations as part of a code definition.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

theorem balanced_star_eq_zero_of_support_three
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (a : V → ℝ) (hav : a v = 0)
    (hbalance : ∑ w, a w • (p v - p w) = 0)
    (hcard : (support a).card ≤ 3) : a = 0 := by
  by_contra ha
  have h := balanced_star_support_four p hp v a hav hbalance ha
  omega

theorem clique_star_zero_of_zero_force
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (S : Finset V) (hS : S.card ≤ 4) (v : V) (hv : v ∈ S)
    (a : Edge (cliqueOn S) → ℝ) (hF : forceOperator (cliqueOn S) p a v = 0) :
    starCoordinates (cliqueOn S) v a = 0 := by
  apply balanced_star_eq_zero_of_support_three p hp v _
    (starCoordinates_self (cliqueOn S) v a)
  · rw [sum_starCoordinates_eq_incident, ← forceOperator_vertex]
    exact hF
  · have hsub : support (starCoordinates (cliqueOn S) v a) ⊆ S.erase v := by
      intro w hw
      have hn := (mem_support _ w).mp hw
      by_cases hadj : (cliqueOn S).Adj v w
      · exact Finset.mem_erase.mpr ⟨hadj.1.symm, hadj.2.2⟩
      · exact False.elim (hn (starCoordinates_of_not_adj _ _ _ _ hadj))
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv] at hle
    omega

variable {G : SimpleGraph V} {v : V}
variable {p : Placement V 3}

theorem TwoBodyPin.IsPoint.copyAggregate_incident
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ)
    (i : BodyEdgeOccurrence G Finset.univ) (hv : v ∈ i.2.val) :
    copyAggregate G Finset.univ a (underlyingCopiedEdge G Finset.univ i) = a i := by
  rw [copyAggregate, fiberSum_coordinate, Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [if_neg]
    intro h
    have he : k.2.val = i.2.val := congrArg Subtype.val h
    exact hki (hQ.occurrence_unique k i h (he.symm ▸ hv))
  · simp

/-- At a point pin, the copied tetrahedral star has precisely the
ordinary graph's edge coefficients. -/
theorem TwoBodyPin.IsPoint.copied_left_star
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint)
    (a : compatibleCopiedCoefficients G p Finset.univ)
    (w : V) (hw : w ∈ Q.left.val) (hvw : v ≠ w) :
    starCoordinates (maskedGraph G Finset.univ) v
      (copiedToStress G p Finset.univ a).val w =
    starCoordinates (cliqueOn (Q.left.val ∩ Finset.univ)) v
      (bodyCopyRestriction G Finset.univ Q.left a.val) w := by
  let e : Edge (cliqueOn (Q.left.val ∩ Finset.univ)) :=
    ⟨s(v,w), hvw, Finset.mem_inter.mpr ⟨Q.left_mem,Finset.mem_univ _⟩,
      Finset.mem_inter.mpr ⟨hw,Finset.mem_univ _⟩⟩
  have hadj := fragment_le_masked G Finset.univ Q.left e.property
  rw [starCoordinates_of_adj _ _ _ _ hadj,
    starCoordinates_of_adj _ _ _ _ e.property]
  change copyAggregate G Finset.univ a.val (underlyingCopiedEdge G Finset.univ ⟨Q.left,e⟩) =
    a.val ⟨Q.left,e⟩
  exact hQ.copyAggregate_incident a.val ⟨Q.left,e⟩ (Sym2.mem_mk_left v w)

/-- Zero body force forces every actual incident edge coefficient to
vanish on a tetrahedral side of a point pin. -/
theorem TwoBodyPin.pointForce_zero_tetrahedron_star
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G)
    (hC : Q.left.val.card = 4) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (s : StressSpace (maskedGraph G Finset.univ) p)
    (hs : Q.pointForceOnWholePrefix hQ hG p s = 0) :
    ∀ w ∈ Q.left.val,
      starCoordinates (maskedGraph G Finset.univ) v s.val w = 0 := by
  obtain ⟨a,rfl⟩ := copiedToStress_surjective G hG p Finset.univ s
  rw [Q.pointForceOnWholePrefix_copied hQ hG p a] at hs
  have hforce : forceOperator (cliqueOn (Q.left.val ∩ Finset.univ)) p
      (bodyCopyRestriction G Finset.univ Q.left a.val) v = 0 := hs
  have hstar := clique_star_zero_of_zero_force p hp (Q.left.val ∩ Finset.univ)
    (by simp [hC]) v
    (by simpa only [Finset.inter_univ] using Q.left_mem) _ hforce
  intro w hw
  by_cases hvw : v = w
  · subst w
    exact starCoordinates_self _ _ _
  · rw [hQ.copied_left_star a w hw hvw]
    exact congrFun hstar w

/-- The descended force is literally the sum of the actual graph's
axial edge forces on this body's star. -/
theorem TwoBodyPin.pointForceOnWholePrefix_eq_star_sum
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G)
    (p : Placement V 3) (s : StressSpace (maskedGraph G Finset.univ) p) :
    Q.pointForceOnWholePrefix hQ hG p s =
      ∑ w ∈ Q.left.val,
        starCoordinates (maskedGraph G Finset.univ) v s.val w • (p v - p w) := by
  obtain ⟨a,rfl⟩ := copiedToStress_surjective G hG p Finset.univ s
  rw [Q.pointForceOnWholePrefix_copied hQ hG p a]
  change forceOperator (cliqueOn (Q.left.val ∩ Finset.univ)) p
    (bodyCopyRestriction G Finset.univ Q.left a.val) v = _
  rw [forceOperator_vertex, ← sum_starCoordinates_eq_incident]
  calc
    (∑ w : V, starCoordinates (cliqueOn (Q.left.val ∩ Finset.univ)) v
        (bodyCopyRestriction G Finset.univ Q.left a.val) w • (p v - p w)) =
      ∑ w ∈ Q.left.val, starCoordinates (cliqueOn (Q.left.val ∩ Finset.univ)) v
        (bodyCopyRestriction G Finset.univ Q.left a.val) w • (p v - p w) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      have hnot : ¬ (cliqueOn (Q.left.val ∩ Finset.univ)).Adj v w := by
        intro h
        exact hw (Finset.mem_inter.mp h.2.2).1
      rw [starCoordinates_of_not_adj _ _ _ _ hnot, zero_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hvw : v = w
      · subst w
        simp only [sub_self, smul_zero]
      · rw [hQ.copied_left_star a w hw hvw]

/-- A tetrahedral point-force axis which is not an actual neighbor
direction uses at least two nonzero ordinary edge coefficients. -/
theorem TwoBodyPin.star_support_at_least_two
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G)
    (p : Placement V 3) (s : StressSpace (maskedGraph G Finset.univ) p)
    (hforce : Q.pointForceOnWholePrefix hQ hG p s ≠ 0)
    (haxis : ∀ w ∈ Q.left.val, w ≠ v →
      Q.pointForceOnWholePrefix hQ hG p s ∉ ℝ ∙ (p v - p w)) :
    2 ≤ (Q.left.val.filter fun w =>
      starCoordinates (maskedGraph G Finset.univ) v s.val w ≠ 0).card := by
  let a := starCoordinates (maskedGraph G Finset.univ) v s.val
  let A := Q.left.val.filter fun w => a w ≠ 0
  have hsum : Q.pointForceOnWholePrefix hQ hG p s =
      ∑ w ∈ A, a w • (p v - p w) := by
    rw [Q.pointForceOnWholePrefix_eq_star_sum hQ hG p s]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hwA
    have hz : a w = 0 := by
      simpa only [A, Finset.mem_filter, hw, true_and, not_not] using hwA
    rw [hz, zero_smul]
  change 2 ≤ A.card
  by_contra hsmall
  have hcases : A.card = 0 ∨ A.card = 1 := by omega
  rcases hcases with hz | hone
  · rw [Finset.card_eq_zero.mp hz, Finset.sum_empty] at hsum
    exact hforce hsum
  · obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hone
    have hwA : w ∈ A := by simp [hw]
    have hwC : w ∈ Q.left.val := (Finset.mem_filter.mp hwA).1
    have haw : a w ≠ 0 := (Finset.mem_filter.mp hwA).2
    have hwv : w ≠ v := by
      intro heq
      exact haw (by simpa only [heq, a] using starCoordinates_self _ _ _)
    rw [hw, Finset.sum_singleton] at hsum
    apply haxis w hwC hwv
    exact Submodule.mem_span_singleton.mpr ⟨a w,hsum.symm⟩

/-- A nonzero scalar functional admits a stress normalized to one. -/
theorem exists_normalized_linear_functional
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam : E →ₗ[ℝ] ℝ) (hlam : lam ≠ 0) : ∃ x, lam x = 1 := by
  obtain ⟨x,hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hlam (LinearMap.ext h)
  refine ⟨(lam x)⁻¹ • x, ?_⟩
  simp [map_smul, hx]

/-- The tetrahedral edge coefficients are fixed multiples of the
actual point-force scalar. The normalized witness is a real graph
stress, so the coefficients are not introduced independently. -/
theorem TwoBodyPin.tetrahedron_scalar_transmission
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G)
    (hC : Q.left.val.card = 4) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (lam : Module.Dual ℝ (StressSpace (maskedGraph G Finset.univ) p))
    (axis : Vec3) (hlam : lam ≠ 0)
    (hforce : ∀ s, Q.pointForceOnWholePrefix hQ hG p s = lam s • axis) :
    ∃ s₀ : StressSpace (maskedGraph G Finset.univ) p,
      lam s₀ = 1 ∧ ∀ s w, w ∈ Q.left.val →
        starCoordinates (maskedGraph G Finset.univ) v s.val w =
          lam s * starCoordinates (maskedGraph G Finset.univ) v s₀.val w := by
  obtain ⟨s₀,hs₀⟩ := exists_normalized_linear_functional lam hlam
  refine ⟨s₀,hs₀,?_⟩
  intro s w hw
  have hzero : Q.pointForceOnWholePrefix hQ hG p (s - lam s • s₀) = 0 := by
    rw [map_sub, map_smul, hforce, hforce, hs₀, one_smul, sub_self]
  have hcoeff := Q.pointForce_zero_tetrahedron_star hQ hG hC p hp
    (s - lam s • s₀) hzero w hw
  change starCoordinates (maskedGraph G Finset.univ) v
    (s.val - lam s • s₀.val) w = 0 at hcoeff
  rw [map_sub, map_smul] at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- The copied/ordinary coefficient identity holds on either incident
body, without imposing an orientation on the point pin. -/
theorem TwoBodyPin.IsPoint.copied_body_star
    {Q : TwoBodyPin G v} (hQ : Q.IsPoint)
    (a : compatibleCopiedCoefficients G p Finset.univ)
    (C : Body G) (hvC : v ∈ C.val)
    (w : V) (hw : w ∈ C.val) (hvw : v ≠ w) :
    starCoordinates (maskedGraph G Finset.univ) v
      (copiedToStress G p Finset.univ a).val w =
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
      (bodyCopyRestriction G Finset.univ C a.val) w := by
  let e : Edge (cliqueOn (C.val ∩ Finset.univ)) :=
    ⟨s(v,w), hvw, Finset.mem_inter.mpr ⟨hvC,Finset.mem_univ _⟩,
      Finset.mem_inter.mpr ⟨hw,Finset.mem_univ _⟩⟩
  have hadj := fragment_le_masked G Finset.univ C e.property
  rw [starCoordinates_of_adj _ _ _ _ hadj,
    starCoordinates_of_adj _ _ _ _ e.property]
  change copyAggregate G Finset.univ a.val (underlyingCopiedEdge G Finset.univ ⟨C,e⟩) =
    a.val ⟨C,e⟩
  exact hQ.copyAggregate_incident a.val ⟨C,e⟩ (Sym2.mem_mk_left v w)

/-- A zero point-pin force kills the tetrahedral star on either side. -/
theorem TwoBodyPin.pointForce_zero_incident_tetrahedron_star
    (Q : TwoBodyPin G v) (hQ : Q.IsPoint) (hG : K4Covered G)
    (C : Body G) (hvC : v ∈ C.val) (hC : C.val.card = 4)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (s : StressSpace (maskedGraph G Finset.univ) p)
    (hs : Q.pointForceOnWholePrefix hQ hG p s = 0) :
    ∀ w ∈ C.val,
      starCoordinates (maskedGraph G Finset.univ) v s.val w = 0 := by
  obtain ⟨a,rfl⟩ := copiedToStress_surjective G hG p Finset.univ s
  rw [Q.pointForceOnWholePrefix_copied hQ hG p a] at hs
  have hker : copiedToLoads G p Finset.univ a ∈ (Q.loadProjection p).ker := hs
  rw [Q.ker_loadProjection p] at hker
  have hforce : forceOperator (cliqueOn (C.val ∩ Finset.univ)) p
      (bodyCopyRestriction G Finset.univ C a.val) v = 0 :=
    congrFun (LinearMap.mem_ker.mp hker) C
  have hstar := clique_star_zero_of_zero_force p hp (C.val ∩ Finset.univ)
    (by simp only [Finset.inter_univ,hC]; omega) v
    (by simpa only [Finset.inter_univ] using hvC) _ hforce
  intro w hw
  by_cases hvw : v = w
  · subst w
    exact starCoordinates_self _ _ _
  · rw [hQ.copied_body_star a C hvC w hw hvw]
    exact congrFun hstar w

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0010

section BundleSource0011
/- Source: Papers/RigidityBodyLoadCut.lean -/



@[expose] public section

/-!
# Restricting actual bar loads across a zero coefficient boundary

If every bar coefficient crossing a vertex cut is zero, restricting
its force assignment to one side is still balanced. The proof retains
the coefficients of the actual internal edges and identifies their
force vector. This applies directly to a tetrahedral body in a scalar
component and keeps all original maximal bodies in the pair-pin graph.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Keep precisely the actual edges whose two endpoints lie in S. -/
def internalCoefficients (G : SimpleGraph V) (S : Finset V) :
    (Edge G → ℝ) →ₗ[ℝ] (Edge G → ℝ) where
  toFun a e := if ∀ v, v ∈ e.val → v ∈ S then a e else 0
  map_add' a b := by
    funext e
    split_ifs with he
    · simp only [Pi.add_apply, if_pos he]
    · simp only [Pi.add_apply, if_neg he, add_zero]
  map_smul' c a := by
    funext e
    split_ifs with he
    · simp only [Pi.smul_apply, RingHom.id_apply, if_pos he]
    · simp only [Pi.smul_apply, RingHom.id_apply, if_neg he, smul_zero]

@[simp] theorem internalCoefficients_apply
    (G : SimpleGraph V) (S : Finset V) (a : Edge G → ℝ) (e : Edge G) :
    internalCoefficients G S a e =
      if ∀ v, v ∈ e.val → v ∈ S then a e else 0 := rfl

theorem starCoordinates_symm (G : SimpleGraph V) (a : Edge G → ℝ) (v w : V) :
    starCoordinates G v a w = starCoordinates G w a v := by
  by_cases hvw : G.Adj v w
  · rw [starCoordinates_of_adj G v w a hvw,
      starCoordinates_of_adj G w v a hvw.symm]
    congr 1
    exact Subtype.ext (Sym2.eq_swap)
  · rw [starCoordinates_of_not_adj G v w a hvw,
      starCoordinates_of_not_adj G w v a (fun h => hvw h.symm)]

theorem internalCoefficients_star
    (G : SimpleGraph V) (S : Finset V) (a : Edge G → ℝ) (v w : V) :
    starCoordinates G v (internalCoefficients G S a) w =
      if v ∈ S ∧ w ∈ S then starCoordinates G v a w else 0 := by
  by_cases hvw : G.Adj v w
  · rw [starCoordinates_of_adj G v w _ hvw,
      starCoordinates_of_adj G v w a hvw, internalCoefficients_apply]
    simp only [Sym2.forall_mem_pair]
  · rw [starCoordinates_of_not_adj G v w _ hvw,
      starCoordinates_of_not_adj G v w a hvw]
    simp

/-- A zero coefficient boundary makes the retained bar force exactly
ordinary restriction of the original force to S. -/
theorem force_internalCoefficients
    (G : SimpleGraph V) (p : Placement V 3) (S : Finset V)
    (a : Edge G → ℝ)
    (hcross : ∀ v ∈ S, ∀ w, w ∉ S → starCoordinates G v a w = 0) :
    forceOperator G p (internalCoefficients G S a) =
      fun v => if v ∈ S then forceOperator G p a v else 0 := by
  funext v
  rw [forceOperator_vertex, ← sum_starCoordinates_eq_incident]
  by_cases hv : v ∈ S
  · rw [if_pos hv, forceOperator_vertex, ← sum_starCoordinates_eq_incident]
    apply Finset.sum_congr rfl
    intro w _
    rw [internalCoefficients_star]
    by_cases hw : w ∈ S
    · rw [if_pos ⟨hv,hw⟩]
    · rw [if_neg (fun h => hw h.2), hcross v hv w hw]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro w _
    rw [internalCoefficients_star, if_neg (fun h => hv h.1), zero_smul]

/-- Actual force and moment balance survive a zero coefficient cut. -/
theorem restricted_force_balanced
    (G : SimpleGraph V) (p : Placement V 3) (S : Finset V)
    (a : Edge G → ℝ)
    (hcross : ∀ v ∈ S, ∀ w, w ∉ S → starCoordinates G v a w = 0) :
    (fun v => if v ∈ S then forceOperator G p a v else 0) ∈ balancedLoads p := by
  rw [← force_internalCoefficients G p S a hcross]
  exact forceOperator_balanced G p (internalCoefficients G S a)

/-- At an ordinary vertex of a tetrahedron, a force parallel to one
incident bar has zero coefficients on both other bars. -/
theorem clique_star_zero_away_axis
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (C : Finset V) (hC : C.card ≤ 4) (v u : V)
    (hv : v ∈ C) (hu : u ∈ C) (hvu : v ≠ u)
    (a : Edge (cliqueOn C) → ℝ)
    (haxis : forceOperator (cliqueOn C) p a v ∈ ℝ ∙ (p v - p u)) :
    ∀ w, w ≠ u → starCoordinates (cliqueOn C) v a w = 0 := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp haxis
  let e : Edge (cliqueOn C) := ⟨s(v,u),hvu,hv,hu⟩
  have hbar : forceOperator (cliqueOn C) p (Pi.single e 1) v = p v - p u := by
    rw [forceOperator_single_bar _ p v u e.property, barLoad_left p hvu]
  have hzero : forceOperator (cliqueOn C) p (a - c • Pi.single e 1) v = 0 := by
    rw [map_sub, map_smul]
    change forceOperator (cliqueOn C) p a v -
      c • forceOperator (cliqueOn C) p (Pi.single e 1) v = 0
    rw [hbar, hc, sub_self]
  have hstar := clique_star_zero_of_zero_force p hp C hC v hv _ hzero
  intro w hwu
  have hone : starCoordinates (cliqueOn C) v (Pi.single e 1) w = 0 := by
    by_cases hvw : (cliqueOn C).Adj v w
    · rw [starCoordinates_of_adj _ _ _ _ hvw]
      apply Pi.single_eq_of_ne
      intro he
      apply hwu
      exact Sym2.congr_right.mp (congrArg Subtype.val he)
    · exact starCoordinates_of_not_adj _ _ _ _ hvw
  have hz := congrFun hstar w
  rw [map_sub, map_smul] at hz
  change starCoordinates (cliqueOn C) v a w -
    c * starCoordinates (cliqueOn C) v (Pi.single e 1) w = 0 at hz
  simpa only [hone, mul_zero, sub_zero] using hz

/-- Hinge forces in every incident body are along their actual shared
edge; the chosen left/right orientation is immaterial. -/
theorem TwoBodyPin.Hinge.all_loads_mem_axis
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (H : Q.Hinge) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads M.graph p Finset.univ) (C : Body M.graph) :
    (F.val C).val v ∈ ℝ ∙ (p v - p H.partner) := by
  have hleft : Q.loadProjection p F ∈ ℝ ∙ (p v - p H.partner) := by
    rw [← (H.rank_and_range M p hgen hp).2]
    exact ⟨F,rfl⟩
  by_cases hvC : v ∈ C.val
  · rcases Q.exhaustive C hvC with rfl | rfl
    · exact hleft
    · rw [Q.load_right_eq_neg_left p F]
      exact Submodule.neg_mem _ hleft
  · rw [compatible_load_zero_outside_body M.graph p F C v hvC]
    exact Submodule.zero_mem _

/-- A nonsoft two-body vertex has zero force on every body copy. -/
theorem TwoBodyPin.all_loads_zero_of_drop_ne_five
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : deletionRankDrop M.graph v ≠ 5)
    (F : compatibleBodyLoads M.graph p Finset.univ) (C : Body M.graph) :
    (F.val C).val v = 0 := by
  have hleft : F ∈ (Q.loadProjection p).ker := by
    rw [LinearMap.mem_ker, Q.loadProjection_eq_zero_of_drop_ne_five M p hgen hp hδ]
    rfl
  rw [Q.ker_loadProjection p] at hleft
  exact congrFun (LinearMap.mem_ker.mp hleft) C

/-- A copied tetrahedral coefficient at a nonsoft two-body vertex
vanishes, regardless of which compatible coefficient lift was used. -/
theorem tetrahedron_star_zero_at_nonsoft
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ)
    (C : Body M.graph) (hC : C.val.card = 4)
    (v : V) (Q : TwoBodyPin M.graph v) (hv : v ∈ C.val)
    (hδ : deletionRankDrop M.graph v ≠ 5) :
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ C a.val) = 0 := by
  apply clique_star_zero_of_zero_force p hp (C.val ∩ Finset.univ)
    (by simp only [Finset.inter_univ,hC]; omega) v
    (by simpa only [Finset.inter_univ] using hv)
  exact Q.all_loads_zero_of_drop_ne_five M p hgen hp hδ
    (copiedToLoads M.graph p Finset.univ a) C

/-- On a tetrahedral body at a hinge, every copied edge coefficient
except the actual shared edge is zero. -/
theorem tetrahedron_star_zero_at_hinge
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ)
    (C : Body M.graph) (hC : C.val.card = 4)
    (v : V) (Q : TwoBodyPin M.graph v) (H : Q.Hinge) (hv : v ∈ C.val) :
    ∀ w, w ≠ H.partner →
      starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
        (bodyCopyRestriction M.graph Finset.univ C a.val) w = 0 := by
  have hu : H.partner ∈ C.val := by
    rcases Q.exhaustive C hv with rfl | rfl
    · exact H.left_mem
    · exact H.right_mem
  exact clique_star_zero_away_axis p hp (C.val ∩ Finset.univ)
    (by simp only [Finset.inter_univ,hC]; omega) v H.partner
    (by simpa only [Finset.inter_univ] using hv)
    (by simpa only [Finset.inter_univ] using hu) H.distinct _
    (H.all_loads_mem_axis M p hgen hp (copiedToLoads M.graph p Finset.univ a) C)

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined04/block_0011/Consolidated/RigidityCombined04.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined04/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigidityLevelChart.lean -/






@[expose] public section

/-!
# Genuine local smooth charts of regular length fibers

The chart below is built from Mathlib's proved inverse function theorem.
Its parametrization has the actual derivative kernel as its parameter
space; both inverse identities and the level-set equation are stated as
neighborhood identities.  No manifold or tangent-space existence is
assumed by a definition of a framework.
-/

namespace Papers.Rigidity.Calculus

noncomputable section

open Filter
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A chart of the actual level set, including both local inverse
identities and its exact tangent map. -/
structure SmoothLevelChart (f : E → F) (a : E) (T : Submodule ℝ E) where
  parametrization : T → E
  parameter : E → T
  parametrization_zero : parametrization 0 = a
  parameter_self : parameter a = 0
  smooth_parametrization : ContDiffAt ℝ 2 parametrization 0
  smooth_parameter : ContDiffAt ℝ 2 parameter a
  tangent : HasStrictFDerivAt parametrization T.subtypeL 0
  level : ∀ᶠ u in 𝓝 (0 : T), f (parametrization u) = f a
  left_inverse : ∀ᶠ u in 𝓝 (0 : T), parameter (parametrization u) = u
  fiber_iff : ∀ᶠ x in 𝓝 a, f x = f a ↔ parametrization (parameter x) = x

/-- Every `C²` map with surjective derivative has the displayed actual
smooth level chart.  The proof uses the ordinary implicit-function
construction and verifies all its geometric interpretation fields. -/
def submersionLevelChart (f : E → F) (a : E) (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 2 f a) (hL : HasStrictFDerivAt f L a)
    (hsurj : L.range = ⊤) : SmoothLevelChart f a L.ker := by
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let hker := L.ker_closedComplemented_of_finiteDimensional_range
  -- The standard complemented-kernel data, with all ten fields justified.
  let φ : ImplicitFunctionData ℝ E F L.ker :=
    { leftFun := f
      leftDeriv := L
      rightFun := fun x => Classical.choose hker (x - a)
      rightDeriv := Classical.choose hker
      pt := a
      hasStrictFDerivAt_leftFun := hL
      hasStrictFDerivAt_rightFun :=
        (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  have hpt : φ.pt = a := rfl
  have hleftFun : φ.leftFun = f := rfl
  have hrightFun : φ.rightFun = fun x => Classical.choose hker (x - a) := rfl
  have hleftDeriv : φ.leftDeriv = L := rfl
  have hrightDeriv : φ.rightDeriv = Classical.choose hker := rfl
  have hright : ContDiffAt ℝ 2 φ.rightFun a := by
    rw [hrightFun]
    exact (Classical.choose hker).contDiff.contDiffAt.comp a
      (contDiffAt_id.sub contDiffAt_const)
  have hrighta : φ.rightFun a = 0 := by
    rw [hrightFun]
    simp
  have hpoint : φ.prodFun φ.pt = (f a, (0 : L.ker)) := by
    rw [ImplicitFunctionData.prodFun_apply, hpt, hleftFun, hrighta]
  have hsmooth := φ.contDiffAt_implicitFunction (n := 2)
    (by rw [hleftFun, hpt]; exact hf)
    (by rw [hpt]; exact hright) (by norm_num)
  rw [hpoint] at hsmooth
  have hpair : Tendsto (fun u : L.ker => (f a, u)) (𝓝 0) (𝓝 (f a, (0 : L.ker))) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hlevel : ∀ᶠ u in 𝓝 (0 : L.ker),
      f (φ.implicitFunction (f a) u) = f a := by
    have h := φ.leftFun_implicitFunction
    rw [hpoint, hleftFun] at h
    exact hpair.eventually h
  have hleft : ∀ᶠ u in 𝓝 (0 : L.ker),
      φ.rightFun (φ.implicitFunction (f a) u) = u := by
    have h := φ.rightFun_implicitFunction
    rw [hpoint] at h
    exact hpair.eventually h
  refine
    { parametrization := φ.implicitFunction (f a)
      parameter := φ.rightFun
      parametrization_zero := ?_
      parameter_self := hrighta
      smooth_parametrization := ?_
      smooth_parameter := hright
      tangent := ?_
      level := hlevel
      left_inverse := hleft
      fiber_iff := by
        simpa only [hpt, hleftFun] using φ.leftFun_eq_iff_implicitFunction }
  · have hz := φ.implicitFunction_apply_image.self_of_nhds
    simpa only [hpt, hleftFun, hrighta] using hz
  · exact hsmooth.comp (0 : L.ker) (contDiffAt_const.prodMk contDiffAt_id)
  · have hproj : φ.rightDeriv.comp L.ker.subtypeL = ContinuousLinearMap.id ℝ L.ker := by
      rw [hrightDeriv]
      apply ContinuousLinearMap.ext
      intro x
      simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
        Submodule.coe_subtype, ContinuousLinearMap.id_apply] using Classical.choose_spec hker x
    have hzero : φ.leftDeriv.comp L.ker.subtypeL = 0 := by
      rw [hleftDeriv]
      apply ContinuousLinearMap.ext
      intro x
      simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
        Submodule.coe_subtype, ContinuousLinearMap.zero_apply] using
        (show L x = 0 from x.property)
    simpa only [hpt, hleftFun, hrighta] using
      φ.hasStrictFDerivAt_implicitFunction L.ker.subtypeL hproj hzero

end

end Papers.Rigidity.Calculus

end
end BundleSource0012

section BundleSource0013
/- Source: Papers/RigidityRegularFiber.lean -/





@[expose] public section

/-!
# Redundant equations at a maximum-rank point

A projection onto the derivative range removes only redundant equations.
Near a maximum-rank point, the projected derivative has the same kernel
as the full derivative.  The local fiber chart is then transferred back
to the original map by proving that every omitted equation is constant
on the chart.  This is the regular-fiber step needed for actual Euclidean
configuration spaces.
-/

namespace Papers.Rigidity.Calculus

noncomputable section

open Filter
open scoped Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

def derivativeRangeProjection (L : E →L[ℝ] F) : F →L[ℝ] L.range :=
  LinearMap.toContinuousLinearMap L.range.subtype.leftInverse

theorem derivativeRangeProjection_apply (L : E →L[ℝ] F) (y : L.range) :
    derivativeRangeProjection L y.val = y := by
  exact LinearMap.congr_fun
    (L.range.subtype.leftInverse_comp_of_inj
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)) y

theorem derivativeRangeProjection_comp_surjective (L : E →L[ℝ] F) :
    Function.Surjective ((derivativeRangeProjection L).comp L) := by
  intro y
  obtain ⟨x, hx⟩ := y.property
  change L x = y.val at hx
  refine ⟨x, ?_⟩
  change derivativeRangeProjection L (L x) = y
  rw [hx, derivativeRangeProjection_apply]

theorem ker_comp_eq_of_surjective_of_rank_le
    (P : F →L[ℝ] G) (A : E →L[ℝ] F)
    (hP : Function.Surjective (P.comp A))
    (hA : Module.finrank ℝ A.range ≤ Module.finrank ℝ G) :
    (P.comp A).ker = A.ker := by
  have hle : A.ker ≤ (P.comp A).ker := by
    intro x hx
    change P (A x) = 0
    rw [show A x = 0 from hx, map_zero]
  have hR : Module.finrank ℝ (P.comp A).range = Module.finrank ℝ G := by
    rw [LinearMap.range_eq_top.mpr hP]
    simp
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := F) A.toLinearMap
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := G) (P.comp A).toLinearMap
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

/-- The frozen derivative-range projection has exactly the same
derivative kernel on a neighborhood of a local maximum-rank point. -/
theorem projected_derivative_kernel_eventually (f : E → F) (a : E)
    (hf : ContDiffAt ℝ 2 f a)
    (hmax : ∀ᶠ x in 𝓝 a,
      Module.finrank ℝ (fderiv ℝ f x).range ≤ Module.finrank ℝ (fderiv ℝ f a).range) :
    ∀ᶠ x in 𝓝 a,
      ((derivativeRangeProjection (fderiv ℝ f a)).comp (fderiv ℝ f x)).ker =
        (fderiv ℝ f x).ker := by
  let L := fderiv ℝ f a
  let P := derivativeRangeProjection L
  let r := Module.finrank ℝ L.range
  have hsurj := derivativeRangeProjection_comp_surjective L
  have hR : Module.finrank ℝ (P.comp L).range = r := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [r]
  have hcont : ContinuousAt (fun x => P.comp (fderiv ℝ f x)) a :=
    continuousAt_const.clm_comp
      (hf.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hopen := isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := E) (F := L.range) r
  have hmem : P.comp (fderiv ℝ f a) ∈
      {A : E →L[ℝ] L.range | (r : Cardinal) ≤ A.toLinearMap.rank} := by
    change (r : Cardinal) ≤ Module.rank ℝ (P.comp L).range
    rw [← Module.finrank_eq_rank, hR]
  have hlower := hcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hlower, hmax] with x hx hmaxx
  have hx' : r ≤ Module.finrank ℝ (P.comp (fderiv ℝ f x)).range := by
    change (r : Cardinal) ≤ Module.rank ℝ (P.comp (fderiv ℝ f x)).range at hx
    rw [← Module.finrank_eq_rank] at hx
    exact_mod_cast hx
  have hPx : Function.Surjective (P.comp (fderiv ℝ f x)) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) hx'
  exact ker_comp_eq_of_surjective_of_rank_le P (fderiv ℝ f x) hPx hmaxx

/-- Every omitted equation is constant on the actual projected fiber.
The proof differentiates the already constructed chart and uses a small
convex parameter ball; constancy is not supplied as a rank hypothesis. -/
theorem SmoothLevelChart.level_of_projection
    (f : E → F) (P : F →L[ℝ] G) (a : E) (T : Submodule ℝ E)
    (C : SmoothLevelChart (fun x => P (f x)) a T)
    (hf : ContDiffAt ℝ 2 f a)
    (hker : ∀ᶠ x in 𝓝 a,
      (P.comp (fderiv ℝ f x)).ker ≤ (fderiv ℝ f x).ker) :
    ∀ᶠ u in 𝓝 (0 : T), f (C.parametrization u) = f a := by
  have hψ : Tendsto C.parametrization (𝓝 (0 : T)) (𝓝 a) := by
    simpa only [C.parametrization_zero] using C.smooth_parametrization.continuousAt.tendsto
  have hnear : ∀ᶠ u in 𝓝 (0 : T),
      DifferentiableAt ℝ (fun z => f (C.parametrization z)) u ∧
        fderiv ℝ (fun z => f (C.parametrization z)) u = 0 := by
    filter_upwards [C.smooth_parametrization.eventually (by norm_num),
      hψ.eventually (hf.eventually (by norm_num)), hψ.eventually hker,
      C.level.eventually_nhds] with u hψu hfu hkeru heq
    have hψdiff := hψu.differentiableAt (by norm_num)
    have hfdiff := hfu.differentiableAt (by norm_num)
    have hgdiff : DifferentiableAt ℝ (fun x => P (f x)) (C.parametrization u) :=
      P.differentiableAt.comp _ hfdiff
    have hzero : fderiv ℝ (fun z => P (f (C.parametrization z))) u = 0 :=
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq).trans (fderiv_const_apply (𝕜 := ℝ) (x := u) (P (f a)))
    rw [fderiv_fun_comp u hgdiff hψdiff,
      fderiv_fun_comp (C.parametrization u) P.differentiableAt hfdiff, P.fderiv] at hzero
    refine ⟨hfdiff.comp u hψdiff, ?_⟩
    rw [fderiv_fun_comp u hfdiff hψdiff]
    ext z
    have hz : fderiv ℝ C.parametrization u z ∈
        (P.comp (fderiv ℝ f (C.parametrization u))).ker := by
      exact congrArg (fun A : T →L[ℝ] G => A z) hzero
    exact hkeru hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hdiffOn : DifferentiableOn ℝ (fun z => f (C.parametrization z))
      (Metric.ball (0 : T) ε) :=
    fun u hu => (hball hu).1.differentiableWithinAt
  have hzeroOn : (Metric.ball (0 : T) ε).EqOn
      (fderiv ℝ (fun z => f (C.parametrization z))) 0 := fun u hu => (hball hu).2
  filter_upwards [Metric.ball_mem_nhds (0 : T) hε] with u hu
  have hconst := Metric.isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball (0 : T) ε).isPreconnected hdiffOn hzeroOn hu (Metric.mem_ball_self hε)
  simpa only [C.parametrization_zero] using hconst

/-- Transfer a genuine projected-equation chart to all original
equations, retaining both inverse identities and the exact tangent map. -/
def SmoothLevelChart.of_projection
    (f : E → F) (P : F →L[ℝ] G) (a : E) (T : Submodule ℝ E)
    (C : SmoothLevelChart (fun x => P (f x)) a T)
    (hf : ContDiffAt ℝ 2 f a)
    (hker : ∀ᶠ x in 𝓝 a,
      (P.comp (fderiv ℝ f x)).ker ≤ (fderiv ℝ f x).ker) :
    SmoothLevelChart f a T := by
  have hlevel := C.level_of_projection f P a T hf hker
  have hparam : Tendsto C.parameter (𝓝 a) (𝓝 (0 : T)) := by
    simpa only [C.parameter_self] using C.smooth_parameter.continuousAt.tendsto
  refine
    { parametrization := C.parametrization
      parameter := C.parameter
      parametrization_zero := C.parametrization_zero
      parameter_self := C.parameter_self
      smooth_parametrization := C.smooth_parametrization
      smooth_parameter := C.smooth_parameter
      tangent := C.tangent
      level := hlevel
      left_inverse := C.left_inverse
      fiber_iff := ?_ }
  filter_upwards [C.fiber_iff, hparam.eventually hlevel] with x hx hlevelx
  constructor
  · intro hfx
    exact hx.mp (congrArg P hfx)
  · intro hpx
    simpa only [hpx] using hlevelx

/-- The actual full level set of a `C²` map at any local maximum-rank
point has a smooth chart whose tangent space is exactly its derivative
kernel.  No independent-row or regular-fiber assumption remains. -/
def maximumRankLevelChart (f : E → F) (a : E)
    (hf : ContDiffAt ℝ 2 f a)
    (hmax : ∀ᶠ x in 𝓝 a,
      Module.finrank ℝ (fderiv ℝ f x).range ≤ Module.finrank ℝ (fderiv ℝ f a).range) :
    SmoothLevelChart f a (fderiv ℝ f a).ker := by
  let L := fderiv ℝ f a
  let P := derivativeRangeProjection L
  let g : E → L.range := fun x => P (f x)
  let A := P.comp L
  have hg : ContDiffAt ℝ 2 g a := P.contDiff.contDiffAt.comp a hf
  have hA : HasStrictFDerivAt g A a :=
    P.hasStrictFDerivAt.comp a (hf.hasStrictFDerivAt (by norm_num))
  have hsurj : Function.Surjective A := derivativeRangeProjection_comp_surjective L
  have hker : A.ker = L.ker :=
    ker_comp_eq_of_surjective_of_rank_le P L hsurj le_rfl
  let C := submersionLevelChart g a A hg hA (LinearMap.range_eq_top.mpr hsurj)
  have hnear : ∀ᶠ x in 𝓝 a,
      (P.comp (fderiv ℝ f x)).ker ≤ (fderiv ℝ f x).ker :=
    (projected_derivative_kernel_eventually f a hf hmax).mono fun _ hx => hx.le
  rw [show (fderiv ℝ f a).ker = A.ker from hker.symm]
  exact C.of_projection f P a A.ker hf hnear

end

end Papers.Rigidity.Calculus

end
end BundleSource0013

section BundleSource0014
/- Source: Papers/RigidityLengthFiber.lean -/







@[expose] public section

/-!
# The actual Euclidean bar-length fiber

The squared-length map is defined from the given real vertex coordinates.
Its derivative is twice the previously defined rigidity operator.  At a
maximum-rank placement the ordinary inverse-function theorem therefore
constructs a `C²` chart of the full bar-length fiber with precisely the
actual infinitesimal-motion kernel as its parameter and tangent space.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open Filter
open scoped Topology BigOperators Classical

variable {V : Type} [Fintype V] {d : ℕ}

def squaredDistance (p : Placement V d) (v w : V) : ℝ :=
  ∑ i : Fin d, (p v i - p w i) ^ 2

def squaredLengthMap (G : SimpleGraph V) (p : Placement V d) : V × V → ℝ :=
  fun e => if G.Adj e.1 e.2 then squaredDistance p e.1 e.2 else 0

def coordinateDifference (v w : V) (i : Fin d) : Placement V d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => Fin d → ℝ) v -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => Fin d → ℝ) w)

@[simp] theorem coordinateDifference_apply (v w : V) (i : Fin d) (p : Placement V d) :
    coordinateDifference v w i p = p v i - p w i := rfl

theorem squaredDistance_hasFDerivAt (p : Placement V d) (v w : V) :
    HasFDerivAt (fun q => squaredDistance q v w)
      (LinearMap.toContinuousLinearMap ((2 : ℝ) • edgeFunctional p v w)) p := by
  have hsum : HasFDerivAt
      (fun q : Placement V d => ∑ i : Fin d, (q v i - q w i)^2)
      (∑ i : Fin d, ((2 : ℝ) * (p v i - p w i)) • coordinateDifference v w i) p := by
    apply HasFDerivAt.fun_sum
    intro i _
    simpa [coordinateDifference_apply, pow_one, nsmul_eq_mul] using
      (coordinateDifference v w i).hasFDerivAt.pow 2
  exact hsum.congr_fderiv (by
    ext u
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      coordinateDifference_apply, LinearMap.coe_toContinuousLinearMap',
      LinearMap.smul_apply, edgeFunctional_apply, edgeConstraint, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring)

theorem squaredLengthMap_contDiff (G : SimpleGraph V) :
    ContDiff ℝ 2 (squaredLengthMap G : Placement V d → V × V → ℝ) := by
  apply contDiff_pi.mpr
  intro e
  by_cases he : G.Adj e.1 e.2
  · simp only [squaredLengthMap, he, if_true, squaredDistance]
    fun_prop
  · simpa only [squaredLengthMap, he, if_false] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : Placement V d => (0 : ℝ)))

theorem squaredLengthMap_hasFDerivAt (G : SimpleGraph V) (p : Placement V d) :
    HasFDerivAt (squaredLengthMap G)
      (LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator G p)) p := by
  apply hasFDerivAt_pi'.mpr
  intro e
  by_cases he : G.Adj e.1 e.2
  · have hD : (ContinuousLinearMap.proj e).comp
        (LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator G p)) =
        LinearMap.toContinuousLinearMap ((2 : ℝ) • edgeFunctional p e.1 e.2) := by
      ext u
      simp [LinearMap.coe_toContinuousLinearMap', rigidityOperator, he]
    rw [hD]
    simpa only [squaredLengthMap, he, if_true] using
      squaredDistance_hasFDerivAt p e.1 e.2
  · have hD : (ContinuousLinearMap.proj e).comp
        (LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator G p)) = 0 := by
      ext u
      simp [LinearMap.coe_toContinuousLinearMap', rigidityOperator, he]
    rw [hD]
    simpa [squaredLengthMap, he] using
      (hasFDerivAt_const (x := p) (0 : ℝ))

theorem fderiv_squaredLengthMap (G : SimpleGraph V) (p : Placement V d) :
    fderiv ℝ (squaredLengthMap G) p =
      LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator G p) :=
  (squaredLengthMap_hasFDerivAt G p).fderiv

theorem ker_fderiv_squaredLengthMap (G : SimpleGraph V) (p : Placement V d) :
    (fderiv ℝ (squaredLengthMap G) p).ker = (rigidityOperator G p).ker := by
  rw [fderiv_squaredLengthMap]
  ext u
  change ((2 : ℝ) • rigidityOperator G p u = 0) ↔ rigidityOperator G p u = 0
  simp

theorem rank_fderiv_squaredLengthMap (G : SimpleGraph V) (p : Placement V d) :
    Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) p).range = rigidityRank G p := by
  rw [fderiv_squaredLengthMap]
  change Module.finrank ℝ (((2 : ℝ) • rigidityOperator G p).range) =
    Module.finrank ℝ (rigidityOperator G p).range
  rw [LinearMap.range_smul (rigidityOperator G p) (2 : ℝ) (by norm_num)]

/-- A genuine smooth chart of the whole length fiber at any placement
attaining the actual generic rank.  This proves the regularity assertion
used in the paper; it does not assume a configuration manifold. -/
def maximumRankLengthFiberChart (G : SimpleGraph V) (p : Placement V d)
    (hp : rigidityRank G p = genericRigidityRank G d) :
    Calculus.SmoothLevelChart (squaredLengthMap G) p (rigidityOperator G p).ker := by
  have hmax : ∀ᶠ q in 𝓝 p,
      Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) q).range ≤
        Module.finrank ℝ (fderiv ℝ (squaredLengthMap G) p).range := by
    apply Filter.Eventually.of_forall
    intro q
    rw [rank_fderiv_squaredLengthMap, rank_fderiv_squaredLengthMap, hp]
    exact rigidityRank_le_genericRigidityRank G d q
  have C := Calculus.maximumRankLevelChart (squaredLengthMap G) p
    (squaredLengthMap_contDiff G).contDiffAt hmax
  rw [ker_fderiv_squaredLengthMap] at C
  exact C

end

end Papers.Rigidity.BarJoint

end
end BundleSource0014

section BundleSource0015
/- Source: Papers/RigidityTriangleFrame.lean -/








@[expose] public section

/-!
# Actual rigid-body coordinates from a surviving triangle

The oriented frame consists of the two triangle differences and their
cross product.  Its inverse is taken only at the fixed noncollinear
reference triangle.  Thus the resulting body rotation and translation
depend smoothly on the moving triangle coordinates.  Equality of its
three bar lengths proves orthogonality and proves that the body map
really carries each of the three original vertices to its moving copy.
-/

namespace Papers.Rigidity.TriangleFrame

noncomputable section

open Matrix BarJoint
open scoped Matrix Classical BigOperators

def orientedFrame (u v : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (![u, v, u ⨯₃ v] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ

def frame (p : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  orientedFrame (p 1 - p 0) (p 2 - p 0)

@[simp] theorem orientedFrame_apply (u v : Vec3) (i j : Fin 3) :
    orientedFrame u v i j = (![u, v, u ⨯₃ v] : Fin 3 → Vec3) j i := rfl

theorem orientedFrame_det (u v : Vec3) :
    (orientedFrame u v).det = (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
  simp [Matrix.det_fin_three, orientedFrame_apply, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem frame_det_pos (p : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    0 < (frame p).det := by
  rw [frame, orientedFrame_det]
  have hn : (p 1 - p 0) ⨯₃ (p 2 - p 0) ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hp
  have hnonneg : 0 ≤ ((p 1 - p 0) ⨯₃ (p 2 - p 0)) ⬝ᵥ
      ((p 1 - p 0) ⨯₃ (p 2 - p 0)) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _
  exact lt_of_le_of_ne hnonneg (Ne.symm (fun hz => hn (dotProduct_self_eq_zero.mp hz)))

theorem orientedFrame_gram (u v : Vec3) :
    (orientedFrame u v)ᵀ * orientedFrame u v =
      ![![u ⬝ᵥ u, u ⬝ᵥ v, 0],
        ![u ⬝ᵥ v, v ⬝ᵥ v, 0],
        ![0, 0, (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v)^2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientedFrame_apply, Matrix.transpose_apply, Matrix.mul_apply, cross_apply, dotProduct,
      Fin.sum_univ_three] <;>
    ring

theorem squaredDistance_eq_dot (p : Fin 3 → Vec3) (i j : Fin 3) :
    squaredDistance p i j = (p i - p j) ⬝ᵥ (p i - p j) := by
  simp only [squaredDistance, dotProduct, Pi.sub_apply, pow_two]

theorem displacement_gram_of_lengths (p q : Fin 3 → Vec3)
    (hlen : ∀ i j, squaredDistance q i j = squaredDistance p i j) :
    (q 1 - q 0) ⬝ᵥ (q 1 - q 0) = (p 1 - p 0) ⬝ᵥ (p 1 - p 0) ∧
    (q 2 - q 0) ⬝ᵥ (q 2 - q 0) = (p 2 - p 0) ⬝ᵥ (p 2 - p 0) ∧
    (q 1 - q 0) ⬝ᵥ (q 2 - q 0) = (p 1 - p 0) ⬝ᵥ (p 2 - p 0) := by
  have h₁ := hlen 1 0
  have h₂ := hlen 2 0
  have h₃ := hlen 1 2
  simp only [squaredDistance_eq_dot] at h₁ h₂ h₃
  refine ⟨h₁, h₂, ?_⟩
  have hq : (q 1 - q 2) ⬝ᵥ (q 1 - q 2) =
      (q 1 - q 0) ⬝ᵥ (q 1 - q 0) +
      (q 2 - q 0) ⬝ᵥ (q 2 - q 0) -
      2 * ((q 1 - q 0) ⬝ᵥ (q 2 - q 0)) := by
    simp [dotProduct, Fin.sum_univ_three]
    ring
  have hp : (p 1 - p 2) ⬝ᵥ (p 1 - p 2) =
      (p 1 - p 0) ⬝ᵥ (p 1 - p 0) +
      (p 2 - p 0) ⬝ᵥ (p 2 - p 0) -
      2 * ((p 1 - p 0) ⬝ᵥ (p 2 - p 0)) := by
    simp [dotProduct, Fin.sum_univ_three]
    ring
  linarith

theorem frame_gram_of_lengths (p q : Fin 3 → Vec3)
    (hlen : ∀ i j, squaredDistance q i j = squaredDistance p i j) :
    (frame q)ᵀ * frame q = (frame p)ᵀ * frame p := by
  obtain ⟨h₁, h₂, h₃⟩ := displacement_gram_of_lengths p q hlen
  simp only [frame, orientedFrame_gram, h₁, h₂, h₃]
  rfl

def rotation (p q : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  frame q * (frame p)⁻¹

def translation (p q : Fin 3 → Vec3) : Vec3 :=
  q 0 - rotation p q *ᵥ p 0

theorem rotation_mul_frame (p q : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    rotation p q * frame p = frame q := by
  rw [rotation, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (frame p) (isUnit_iff_ne_zero.mpr (ne_of_gt (frame_det_pos p hp))),
    Matrix.mul_one]

/-- Orthogonality follows from the actual preserved triangle lengths. -/
theorem rotation_orthogonal (p q : Fin 3 → Vec3) (hp : NoncollinearTriangle p)
    (hlen : ∀ i j, squaredDistance q i j = squaredDistance p i j) :
    (rotation p q)ᵀ * rotation p q = 1 := by
  have hP := Matrix.mul_nonsing_inv (frame p)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (frame_det_pos p hp)))
  calc
    (rotation p q)ᵀ * rotation p q =
        ((frame p)⁻¹)ᵀ * ((frame q)ᵀ * frame q) * (frame p)⁻¹ := by
      simp only [rotation, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((frame p)⁻¹)ᵀ * ((frame p)ᵀ * frame p) * (frame p)⁻¹ := by
      rw [frame_gram_of_lengths p q hlen]
    _ = (frame p * (frame p)⁻¹)ᵀ * (frame p * (frame p)⁻¹) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hP, Matrix.transpose_one, Matrix.one_mul]

theorem rotation_displacement_one (p q : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    rotation p q *ᵥ (p 1 - p 0) = q 1 - q 0 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
    A *ᵥ Pi.single (0 : Fin 3) 1) (rotation_mul_frame p q hp)
  rw [← Matrix.mulVec_mulVec] at h
  have hcol (r : Fin 3 → Vec3) : (frame r).col (0 : Fin 3) = r 1 - r 0 := rfl
  simpa only [Matrix.mulVec_single_one, hcol p, hcol q] using h

theorem rotation_displacement_two (p q : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    rotation p q *ᵥ (p 2 - p 0) = q 2 - q 0 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
    A *ᵥ Pi.single (1 : Fin 3) 1) (rotation_mul_frame p q hp)
  rw [← Matrix.mulVec_mulVec] at h
  have hcol (r : Fin 3 → Vec3) : (frame r).col (1 : Fin 3) = r 2 - r 0 := rfl
  simpa only [Matrix.mulVec_single_one, hcol p, hcol q] using h

/-- The constructed body map matches every point of the reference triangle. -/
theorem bodyMap_at_triangle (p q : Fin 3 → Vec3) (hp : NoncollinearTriangle p) (i : Fin 3) :
    rotation p q *ᵥ p i + translation p q = q i := by
  have h₁ := rotation_displacement_one p q hp
  have h₂ := rotation_displacement_two p q hp
  rw [Matrix.mulVec_sub] at h₁ h₂
  fin_cases i
  · simp [translation]
  · rw [translation]
    change rotation p q *ᵥ p 1 + (q 0 - rotation p q *ᵥ p 0) = q 1
    calc
      _ = (rotation p q *ᵥ p 1 - rotation p q *ᵥ p 0) + q 0 := by abel
      _ = q 1 := by rw [h₁, sub_add_cancel]
  · rw [translation]
    change rotation p q *ᵥ p 2 + (q 0 - rotation p q *ᵥ p 0) = q 2
    calc
      _ = (rotation p q *ᵥ p 2 - rotation p q *ᵥ p 0) + q 0 := by abel
      _ = q 2 := by rw [h₂, sub_add_cancel]

theorem rotation_self (p : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    rotation p p = 1 :=
  Matrix.mul_nonsing_inv (frame p)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (frame_det_pos p hp)))

theorem translation_self (p : Fin 3 → Vec3) (hp : NoncollinearTriangle p) :
    translation p p = 0 := by
  simp [translation, rotation_self p hp]

/-- Use the ordinary entrywise Pi norm on the finite matrix space. -/
local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) :=
  inferInstanceAs (NormedAddCommGroup (m → n → ℝ))

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) :=
  inferInstanceAs (NormedSpace ℝ (m → n → ℝ))

theorem rotation_contDiff (p : Fin 3 → Vec3) : ContDiff ℝ 2 (rotation p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [rotation, Matrix.mul_apply, frame, orientedFrame_apply]
  fin_cases i <;> fin_cases j <;> simp [cross_apply, Fin.sum_univ_three] <;> fun_prop

theorem translation_contDiff (p : Fin 3 → Vec3) : ContDiff ℝ 2 (translation p) := by
  apply contDiff_pi.mpr
  intro i
  have hR (j : Fin 3) : ContDiff ℝ 2 (fun q => rotation p q i j) :=
    contDiff_pi.mp (contDiff_pi.mp (rotation_contDiff p) i) j
  simp only [translation, Pi.sub_apply, Matrix.mulVec, dotProduct]
  fun_prop

end

end Papers.Rigidity.TriangleFrame

end
end BundleSource0015

section BundleSource0016
/- Source: Papers/RigidityLieCoordinates.lean -/



@[expose] public section

/-!
# Euclidean twists as homogeneous affine Lie matrices

This matrix has zero last row. It differs from the alternating matrix used
for the Pfaffian geometry of pins. Its commutator is the spatial Euclidean
Lie bracket, which is the bracket occurring in Maurer–Cartan.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- The spatial Euclidean Lie bracket, in angular/translation coordinates. -/
def twistBracket (X Y : Twist) : Twist :=
  (X.1 ⨯₃ Y.1, X.1 ⨯₃ Y.2 - Y.1 ⨯₃ X.2)

theorem twistBracket_smul_smul (a b : ℝ) (X Y : Twist) :
    twistBracket (a • X) (b • Y) = (a * b) • twistBracket X Y := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [twistBracket, cross_apply] <;> ring

def twistLieMatrix (X : Twist) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -X.1 2, X.1 1, X.2 0;
     X.1 2, 0, -X.1 0, X.2 1;
     -X.1 1, X.1 0, 0, X.2 2;
     0, 0, 0, 0]

def twistLieLinear : Twist →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun := twistLieMatrix
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twistLieMatrix, add_comm]
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twistLieMatrix]

theorem twistLieMatrix_injective : Function.Injective twistLieMatrix := by
  intro X Y h
  have hω0 := congrFun (congrFun h 2) 1
  have hω1 := congrFun (congrFun h 0) 2
  have hω2 := congrFun (congrFun h 1) 0
  have ht0 := congrFun (congrFun h 0) 3
  have ht1 := congrFun (congrFun h 1) 3
  have ht2 := congrFun (congrFun h 2) 3
  simp [twistLieMatrix] at hω0 hω1 hω2 ht0 ht1 ht2
  apply Prod.ext
  · ext i
    fin_cases i <;> assumption
  · ext i
    fin_cases i <;> assumption

/-- The affine Lie matrix acts on a finite homogeneous point by its actual
Euclidean infinitesimal velocity. -/
theorem twistLieMatrix_mulVec (X : Twist) (p : Vec3) :
    twistLieMatrix X *ᵥ ![p 0, p 1, p 2, 1] =
      ![evaluateTwist p X 0, evaluateTwist p X 1, evaluateTwist p X 2, 0] := by
  ext i
  fin_cases i <;>
    simp [twistLieMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      evaluateTwist, cross_apply] <;> ring

/-- This is the required bridge from the actual matrix Maurer–Cartan
commutator to the six-coordinate twist bracket. -/
theorem twistLieMatrix_commutator (X Y : Twist) :
    twistLieMatrix (twistBracket X Y) =
      twistLieMatrix X * twistLieMatrix Y - twistLieMatrix Y * twistLieMatrix X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistLieMatrix, twistBracket, Matrix.mul_apply,
      Fin.sum_univ_succ, cross_apply] <;> ring

end Papers.Rigidity

end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined04/block_0016/Consolidated/RigidityCombined04.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined04/checkpoint_0016.json"
