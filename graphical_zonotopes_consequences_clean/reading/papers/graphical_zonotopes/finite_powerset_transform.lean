module

public import Papers.GraphicalZonotopes.Mobius
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem delta_zeta_reduced {u v : V} (huv : u≠v) {S : Finset V}
    (hu : u∉S) (hv : v∉S) (y : SetFunction V) :
    delta (zeta y) u v S=∑ T∈S.powerset,y (insert u (insert v T)) := by
  have huvS : u∉insert v S:=by simp only [mem_insert,not_or]; exact ⟨huv,hu⟩
  simp only [delta,zeta,sum_powerset_insert huvS,sum_powerset_insert hu,
    sum_powerset_insert hv]
  ring

namespace PowersetTransform

abbrev SubsetIndex (B : Finset V) := ↥B.powerset

/-- The full lower-set sum on the powerset of a fixed ambient finite set.
The domain is exactly all its subsets; no extension or truncation is used. -/
def lowerSum (B : Finset V) :
    (SubsetIndex B → ℝ) →ₗ[ℝ] (SubsetIndex B → ℝ) where
  toFun y S := ∑ T : SubsetIndex B,if T.1⊆S.1 then y T else 0
  map_add' y z := by
    funext S
    simp only [Pi.add_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp
  map_smul' a y := by
    funext S
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp

theorem lowerSum_eq_zero_iff (B : Finset V) (y : SubsetIndex B → ℝ) :
    lowerSum B y=0 ↔ y=0 := by
  constructor
  · intro hz
    have hzero : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩=0 := by
      intro S
      refine Finset.strongInductionOn S ?_
      intro S ih hS
      let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
      have hs:=congrFun hz s
      change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=0 at hs
      rw [sum_eq_single s] at hs
      · simpa only [s,Subset.rfl,ite_true] using hs
      · intro T hT hne
        by_cases hTS : T.1⊆S
        · rw [if_pos hTS]
          have hne' : T.1≠S := by
            intro he
            apply hne
            exact Subtype.ext he
          exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne'⟩)
            (mem_powerset.mp T.2)
        · rw [if_neg hTS]
      · simp
    funext S
    exact hzero S.1 (mem_powerset.mp S.2)
  · rintro rfl
    exact (lowerSum B).map_zero

theorem lowerSum_injective (B : Finset V) : Function.Injective (lowerSum B) := by
  intro y z he
  have hz : lowerSum B (y-z)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp ((lowerSum_eq_zero_iff B (y-z)).mp hz)

def lowerEquiv (B : Finset V) :
    (SubsetIndex B → ℝ) ≃ₗ[ℝ] (SubsetIndex B → ℝ) :=
  LinearEquiv.ofInjectiveEndo (lowerSum B) (lowerSum_injective B)

theorem lowerSum_restriction (B : Finset V) (y : SetFunction V) (S : SubsetIndex B) :
    lowerSum B (fun T => y T.1) S=∑ T∈S.1.powerset,y T := by
  change (∑ T : SubsetIndex B,if T.1⊆S.1 then y T.1 else 0)=_
  rw [← sum_filter]
  apply sum_bij (fun T _ => T.1)
  · intro T hT
    exact mem_powerset.mpr (mem_filter.mp hT).2
  · intro T hT U hU he
    exact Subtype.ext he
  · intro T hT
    let t : SubsetIndex B:=⟨T,mem_powerset.mpr
      ((mem_powerset.mp hT).trans (mem_powerset.mp S.2))⟩
    exact ⟨t,mem_filter.mpr ⟨mem_univ t,mem_powerset.mp hT⟩,rfl⟩
  · intro T hT
    rfl

/-- Triangular inversion preserves every coefficient subring, in particular
the integer lattice. This is proved from the inverse equations themselves. -/
theorem lowerEquiv_symm_mem_subring (B : Finset V) (K : Subring ℝ)
    (x : SubsetIndex B → ℝ) (hx : ∀ S,x S∈K) :
    ∀ S,(lowerEquiv B).symm x S∈K := by
  let y:=(lowerEquiv B).symm x
  have he : lowerSum B y=x:=(lowerEquiv B).apply_symm_apply x
  have hmem : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩∈K := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
    have hs:=congrFun he s
    change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=x s at hs
    rw [← sum_erase_add _ _ (mem_univ s)] at hs
    have hlast : (if s.1⊆S then y s else 0)=y s:=if_pos Subset.rfl
    rw [hlast] at hs
    have hsum : (∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0)∈K := by
      apply K.sum_mem
      intro T hT
      by_cases hTS : T.1⊆S
      · rw [if_pos hTS]
        have hne : T.1≠S := by
          intro he
          exact (ne_of_mem_erase hT) (Subtype.ext he)
        exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne⟩) (mem_powerset.mp T.2)
      · rw [if_neg hTS]
        exact K.zero_mem
    have hy : y s=x s-(∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0) := by linarith
    rw [hy]
    exact K.sub_mem (hx s) hsum
  intro S
  exact hmem S.1 (mem_powerset.mp S.2)

end PowersetTransform
end GraphicalZonotopes
