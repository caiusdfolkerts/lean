module

public import Papers.GraphicalZonotopes.PairRelabelling
public import Papers.GraphicalZonotopes.MobiusFour
public import Papers.GraphicalZonotopes.LocalSlopes

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integerData_of_clique {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    integerData C=(C.card.choose 2 : ℤ)+∑ v∈C,firstWeight v := by
  have he : firstSet C∩secondSet C=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases mem_inter.mp hi with ⟨h0,h1⟩
    exact hC ((mem_firstSet _ _).mp h0) ((mem_secondSet _ _).mp h1) (by simp) rfl
  have h := integerData_count_identity C
  rw [he,card_empty,Int.natCast_zero,add_zero,← firstWeight_sum] at h
  exact h

def fourRoundedCoefficient (a b c d : ℤ) : ℤ :=
  (6+a+b+c+d)/2-(3+a+b+c)/2-(3+a+b+d)/2-(3+a+c+d)/2-(3+b+c+d)/2+
    (1+a+b)/2+(1+a+c)/2+(1+a+d)/2+(1+b+c)/2+(1+b+d)/2+(1+c+d)/2

/-- The only bounded calculation is a universal four-bit algebra identity;
its application below quantifies over every four-clique in every graph size. -/
theorem fourRoundedCoefficient_sign (a b c d : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) (hc : c=0 ∨ c=1) (hd : d=0 ∨ d=1) :
    fourRoundedCoefficient a b c d=1 ∨ fourRoundedCoefficient a b c d= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    norm_num [fourRoundedCoefficient]

theorem mobius_setFunction_four (a b c d : I×Fin 2)
    (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hC : (graph I).IsClique ({a,b,c,d} : Finset (I×Fin 2))) :
    mobius setFunction {a,b,c,d}=
      (fourRoundedCoefficient (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d) : ℝ) := by
  have hform (T : Finset (I×Fin 2)) (hT : T⊆{a,b,c,d}) :
      integerData T=(T.card.choose 2 : ℤ)+∑ v∈T,firstWeight v := by
    apply integerData_of_clique
    intro x hx y hy hxy
    exact hC (hT hx) (hT hy) hxy
  rw [mobius_four_normalized setFunction setFunction_translationNormalized hab hac had hbc hbd hcd]
  norm_num [setFunction,hform,hab,hac,had,hbc,hbd,hcd,fourRoundedCoefficient,
    Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.choose]
  <;> ring

/-- Every tetrahedral coefficient is nonzero, in every number of doubled
parts, for every choice of the four selected endpoint sides. -/
theorem mobius_setFunction_four_sign {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) :
    mobius setFunction C=1 ∨ mobius setFunction C= -1 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_setFunction_four a b c d hab hac had hbc hbd hcd hC]
  rcases fourRoundedCoefficient_sign (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d)
      (firstWeight_isBit a) (firstWeight_isBit b) (firstWeight_isBit c) (firstWeight_isBit d) with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

theorem mobius_setFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius setFunction C≠0 := by
  rcases mobius_setFunction_four_sign hcard hC with h | h <;> rw [h] <;> norm_num

theorem mobius_graphFunction_four_zero {C : Finset (I×Fin 2)} (hcard : C.card=4) :
    mobius (graphFunction (graph I)) C=0 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_four_eq _ hab hac had hbc hbd hcd]
  rw [graphFunction_delta _ hab (by simp [hac,had]) (by simp [hbc,hbd]),
    graphFunction_delta _ hab (by simp [hac]) (by simp [hbc]),
    graphFunction_delta _ hab (by simp [had]) (by simp [hbd]),
    graphFunction_delta _ hab (by simp) (by simp)]
  ring

theorem mobius_complementFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius complementFunction C≠0 := by
  rw [complementFunction,mobius_sub]
  change mobius (graphFunction (graph I)) C-mobius setFunction C≠0
  rw [mobius_graphFunction_four_zero hcard,zero_sub]
  exact neg_ne_zero.mpr (mobius_setFunction_four_ne_zero hcard hC)

end DoubledParts
end GraphicalZonotopes
