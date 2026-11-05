module

public import Papers.GraphicalZonotopes.OneSingleton
public import Papers.GraphicalZonotopes.BooleanPair

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem complementFunction_boolean {u v : I×Fin 2} (huv : u≠v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta complementFunction u v S=0 ∨ delta complementFunction u v S=1 := by
  have h := complementPolytope_booleanElemental (I := I)
  rw [BooleanElemental,complementPolytope,
    lowerSupport_basePolytope complementFunction_translationNormalized.1 complementFunction_supermodular] at h
  exact h u v huv S hu hv

def doubledPairData (hI : 4≤Fintype.card I) : BooleanPairData (graph I) where
  left := setFunction
  right := complementFunction
  left_extreme := setFunction_extreme hI
  right_extreme := complementFunction_extreme hI
  left_integer := setFunction_integerValued
  right_integer := complementFunction_integerValued
  pair_sum := by unfold complementFunction; abel
  left_boolean := fun _ _ huv _ hu hv => setFunction_boolean huv hu hv
  right_boolean := fun _ _ huv _ hu hv => complementFunction_boolean huv hu hv
  left_direction := fun _ _ h => setFunction_nonzero_slack (by omega) h
  right_direction := fun _ _ h => complementFunction_nonzero_slack (by omega) h

def singletonPairData (hI : 4≤Fintype.card I) (a : I) : BooleanPairData (singletonGraph a) where
  left := singletonFunction a setFunction
  right := singletonFunction a complementFunction
  left_extreme := singleton_extreme hI a setFunction_translationNormalized setFunction_supermodular
    setFunction_graphical setFunction_completeQuadraticRows
    (fun _ hc hC => mobius_setFunction_four_ne_zero hc hC)
  right_extreme := singleton_extreme hI a complementFunction_translationNormalized complementFunction_supermodular
    complementFunction_graphical complementFunction_completeQuadraticRows
    (fun _ hc hC => mobius_complementFunction_four_ne_zero hc hC)
  left_integer := SetFunctionEmbedding.integerValued_restrict _ setFunction_integerValued
  right_integer := SetFunctionEmbedding.integerValued_restrict _ complementFunction_integerValued
  pair_sum := by
    rw [singletonFunction,singletonFunction,← SetFunctionEmbedding.restrict_add]
    rw [show setFunction+complementFunction=graphFunction (graph I) by unfold complementFunction; abel]
    exact SetFunctionEmbedding.graphFunction_restrict (VertexDeletion.embedding (a,(1 : Fin 2))) (graph I)
  left_boolean := by
    intro u v huv S hu hv
    rw [singletonFunction,SetFunctionEmbedding.delta_restrict]
    exact setFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  right_boolean := by
    intro u v huv S hu hv
    rw [singletonFunction,SetFunctionEmbedding.delta_restrict]
    exact complementFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  left_direction := fun _ _ h => singleton_nonzero_slack hI a setFunction_completeQuadraticRows h
  right_direction := fun _ _ h => singleton_nonzero_slack hI a complementFunction_completeQuadraticRows h

end DoubledParts
end GraphicalZonotopes
