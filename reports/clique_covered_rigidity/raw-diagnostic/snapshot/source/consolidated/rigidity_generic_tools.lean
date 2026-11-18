module
import verification.internal.checkpoint
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section GenericToolsPart01
/- Source: Papers/RigidityLinearCover.lean -/






@[expose] public section

/-!
# The linear covering inequality used in Proposition 6.6

The coordinates of a linear code are vectors in its dual space.  If each
coordinate has at least `k` observers, the sum of the observer ranks is at
least `k` times the rank of all coordinates.  The coordinates may satisfy
arbitrary linear relations.  The proof chooses a basis from the full
coordinate family and counts incidences of that basis with the observers.

This supplies the linear inequality itself.  Constructing the observers
from the actual bar stresses remains a separate mathematical obligation.
-/

namespace Papers.Rigidity.LinearCover

noncomputable section

open scoped BigOperators
open scoped Classical

variable {K M I A : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
  [Module.Finite K M] [Fintype I] [Fintype A]

/-- The rank of the coordinate forms visible to an observer. -/
def observerRank (v : I → M) (S : Finset I) : ℕ :=
  Module.finrank K (Submodule.span K (v '' (S : Set I)))

/-- Linear Shearer's inequality for an arbitrary finite coordinate cover.

Each coordinate is counted with its actual vector value; duplicate or zero
coordinate forms cause no special assumption.  In particular, the result
is a rank inequality and does not count dependent coordinates as independent.
-/
theorem rank_cover (v : I → M) (S : A → Finset I) (k : ℕ)
    (hcover : ∀ i : I, k ≤ (Finset.univ.filter fun a => i ∈ S a).card) :
    k * Module.finrank K (Submodule.span K (Set.range v)) ≤
      ∑ a : A, observerRank (K := K) v (S a) := by
  classical
  obtain ⟨b, hbmem, _, hbind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  choose index hindex using hbmem
  let T (a : A) : Finset (Fin (Module.finrank K (Submodule.span K (Set.range v)))) :=
    Finset.univ.filter fun j => index j ∈ S a
  have hlocal (a : A) : (T a).card ≤ observerRank (K := K) v (S a) := by
    let N : Submodule K M := Submodule.span K (v '' (S a : Set I))
    have hmem (j : T a) : b j.val ∈ N := by
      apply Submodule.subset_span
      refine ⟨index j.val, ?_, hindex j.val⟩
      exact (Finset.mem_filter.mp j.property).2
    have hi : LinearIndependent K (fun j : T a => b j.val) :=
      hbind.comp (fun j : T a => j.val) Subtype.val_injective
    let bN : T a → N := fun j => ⟨b j.val,hmem j⟩
    have hiN : LinearIndependent K bN := LinearIndependent.of_comp N.subtype hi
    have hc := hiN.fintype_card_le_finrank
    simpa only [Fintype.card_coe, observerRank, N] using hc
  have hcount : (∑ a : A, (T a).card) =
      ∑ j : Fin (Module.finrank K (Submodule.span K (Set.range v))),
        (Finset.univ.filter fun a => index j ∈ S a).card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  calc
    k * Module.finrank K (Submodule.span K (Set.range v)) =
        ∑ _j : Fin (Module.finrank K (Submodule.span K (Set.range v))), k := by
      simp [Nat.mul_comm]
    _ ≤ ∑ j : Fin (Module.finrank K (Submodule.span K (Set.range v))),
        (Finset.univ.filter fun a => index j ∈ S a).card := by
      exact Finset.sum_le_sum fun j _ => hcover (index j)
    _ = ∑ a : A, (T a).card := hcount.symm
    _ ≤ ∑ a : A, observerRank (K := K) v (S a) :=
      Finset.sum_le_sum fun a _ => hlocal a

/-- The two-cover form appearing in Proposition 6.6. -/
theorem rank_twoCover (v : I → M) (S : A → Finset I)
    (hcover : ∀ i : I, 2 ≤ (Finset.univ.filter fun a => i ∈ S a).card) :
    2 * Module.finrank K (Submodule.span K (Set.range v)) ≤
      ∑ a : A, observerRank (K := K) v (S a) :=
  rank_cover v S 2 hcover

end

end Papers.Rigidity.LinearCover

end
end GenericToolsPart01

#checked_checkpoint ".lake/checkpoints/generic_tools/block_001/Consolidated/RigidityGenericTools.olean" record ".lake/reports/audit/generic_tools/checkpoint_001.json"

