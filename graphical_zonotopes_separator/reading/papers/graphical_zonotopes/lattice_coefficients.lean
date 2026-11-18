module

public import Papers.GraphicalZonotopes.LatticeSupport
public import Papers.GraphicalZonotopes.MobiusFour

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Möbius inversion preserves the full integer lattice of set functions.
The proof uses the triangular inverse equations over all subsets, without a
rationality or denominator assumption on the inverse linear equivalence. -/
theorem IntegerValued.mobius {z : SetFunction V} (hz : IntegerValued z) :
    IntegerValued (GraphicalZonotopes.mobius z) := by
  classical
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih
  let k : Finset V → ℤ := fun C =>
    if h : C⊂S then Classical.choose (ih C h) else 0
  have hk : ∀ C∈S.powerset.erase S,(k C : ℝ)=GraphicalZonotopes.mobius z C := by
    intro C hC
    have hp : C⊂S := Finset.ssubset_iff_subset_ne.mpr
      ⟨mem_powerset.mp (mem_of_mem_erase hC),ne_of_mem_erase hC⟩
    simpa only [k,dif_pos hp] using (Classical.choose_spec (ih C hp)).symm
  obtain ⟨a,ha⟩ := hz S
  have he := congrFun (zeta_mobius z) S
  change ∑ C∈S.powerset,GraphicalZonotopes.mobius z C=z S at he
  rw [← sum_erase_add _ _ (mem_powerset.mpr Subset.rfl),ha] at he
  refine ⟨a-∑ C∈S.powerset.erase S,k C,?_⟩
  push_cast
  have hs : (∑ C∈S.powerset.erase S,(k C : ℝ))=
      ∑ C∈S.powerset.erase S,GraphicalZonotopes.mobius z C := sum_congr rfl hk
  rw [hs]
  linarith

/-- All tetrahedral coefficients are invariant under an arbitrary real
translation, not merely an integer translation. -/
theorem mobius_four_normalize {z : SetFunction V} {C : Finset V}
    (hC : C.card=4) : mobius (normalize z) C=GraphicalZonotopes.mobius z C := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hC
  rw [mobius_four_eq _ hab hac had hbc hbd hcd,
    mobius_four_eq _ hab hac had hbc hbd hcd,
    delta_normalize z hab (by simp [hac,had]) (by simp [hbc,hbd]),
    delta_normalize z hab (by simp [hac]) (by simp [hbc]),
    delta_normalize z hab (by simp [had]) (by simp [hbd]),
    delta_normalize z hab (by simp) (by simp)]

end GraphicalZonotopes
