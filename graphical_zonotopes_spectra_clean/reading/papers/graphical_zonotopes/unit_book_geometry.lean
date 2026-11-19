module

public import Papers.GraphicalZonotopes.IntegralBooleanResponse
public import Papers.GraphicalZonotopes.ConeCorrespondence

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Actual finite-dimensional lattice geometry for a circuit of unit-weight
Boolean columns. The normalized central lift is derived integrally from the
actual elemental response equations. -/
theorem lattice_book_of_unit_modules {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ i,IsMonotoneBoolean (F i))
    (hess : ∀ i a,Essential (F i) a)
    (hrel : ∃ z : SetFunction (Fin s),TranslationNormalized z ∧ Compatible z F (fun _ => 1))
    (huniq : UniqueIntegrableRelation F (fun _ => 1)) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  letI : Nonempty (Fin s):=⟨⟨0,hs⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F _).mpr hrel
  obtain ⟨z,hzn,hzi,hcInt⟩:=integral_compatible_lift F hF (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hkrel)
  have hc : Compatible z F (fun _ => 1):=by simpa only [Int.cast_one] using hcInt
  let f:=assembled z F (fun _ => 1)
  have hn : TranslationNormalized f:=assembled_normalized hzn F hF (fun _ => 1)
  have hi : IntegerValued f := by
    simpa only [Int.cast_one] using assembled_integerValued hzi F hF (fun _ => (1 : ℤ))
  have he : ExtremeSupermodular f:=positive_circuit_extreme hzn hF
    (fun _ => zero_le_one) ⟨⟨0,hk⟩,one_ne_zero⟩ hc huniq
  have hd : FullDimension (basePolytope f):=assembled_fullDimension hzn hF
    (fun _ => zero_lt_one) hc (essentialSpokeGraph_connected F hess)
  obtain ⟨hl,R,hR,hnR,hQR⟩:=assembled_lattice_complement hzn hzi hF
    (fun _ => (1 : ℤ)) (fun _ => zero_le_one) hcInt
  refine ⟨f,hn,hi,he,assembled_graphical z F (fun _ => 1),hd,
    he.minkowskiIndecomposable,?_,R,hR,hnR,?_⟩
  · simpa only [Int.cast_one] using hl
  · simpa only [Int.cast_one,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hQR

end BooleanModule
end GraphicalZonotopes
