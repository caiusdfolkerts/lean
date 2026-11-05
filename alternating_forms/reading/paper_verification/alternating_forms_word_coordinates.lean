module

public import PaperVerification.AlternatingFormsPrefixWeights
public import PaperVerification.WeightedInitialLinear
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exterior word coordinates with an arbitrary suffix

The coordinate map is extended by the actual homogeneous projection of the
exterior algebra. This lets the prefix relation be transported as a literal
linear identity without changing any word order or identifying different
homogeneous degrees. The weight of a list word is the sum of all its vertex
weights, including the complete suffix.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber
open scoped BigOperators

variable {K : Type*} [Field K] {s n t m : ℕ}

/-- The actual degree projection followed by the proved exterior coordinate map. -/
def totalExteriorPluckerCoordinates (s n : ℕ) :
    ExteriorAlgebra K (Fin n → K) →ₗ[K] MvPolynomial (PluckerIndex s n) K :=
  (exteriorPluckerCoordinates s n).comp
    ((DFinsupp.lapply s).comp
      (DirectSum.decomposeLinearEquiv (fun d : ℕ => ⋀[K]^d (Fin n → K))).toLinearMap)

@[simp] theorem totalExteriorPluckerCoordinates_coe
    (x : ⋀[K]^s (Fin n → K)) :
    totalExteriorPluckerCoordinates (K := K) s n (x : ExteriorAlgebra K (Fin n → K)) =
      exteriorPluckerCoordinates s n x := by
  change exteriorPluckerCoordinates s n
    (DirectSum.decompose (fun d : ℕ => ⋀[K]^d (Fin n → K)) (x : ExteriorAlgebra K (Fin n → K)) s) = _
  have hx : DirectSum.decompose (fun d : ℕ => ⋀[K]^d (Fin n → K))
      (x : ExteriorAlgebra K (Fin n → K)) s = x := by
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same _ x.property
  rw [hx]

def indexExteriorWord (L : List (Fin n)) : ExteriorAlgebra K (Fin n → K) :=
  (L.map (fun i => ExteriorAlgebra.ι K (Pi.basisFun K (Fin n) i))).prod

@[simp] theorem indexExteriorWord_append (L M : List (Fin n)) :
    indexExteriorWord (K := K) (L++M)=indexExteriorWord L*indexExteriorWord M := by
  simp only [indexExteriorWord,List.map_append,List.prod_append]

theorem indexExteriorWord_eq_iota (L : List (Fin n)) :
    indexExteriorWord (K := K) L =
      (exteriorPower.ιMulti K L.length
        (fun i => Pi.basisFun K (Fin n) (L.get i)) : ExteriorAlgebra K (Fin n → K)) := by
  simp only [indexExteriorWord,exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_apply,
    List.ofFn_comp',List.ofFn_get,List.map_map,Function.comp_def]

theorem totalExteriorPluckerCoordinates_word (L : List (Fin n)) :
    totalExteriorPluckerCoordinates (K := K) L.length n (indexExteriorWord L) =
      orderedPluckerCoordinate L.get := by
  rw [indexExteriorWord_eq_iota,totalExteriorPluckerCoordinates_coe,
    exteriorPluckerCoordinates_word]

/-- An arbitrary ordered word has its actual sum of vertex weights.
Repeated vertices are allowed and make its coordinate image zero. -/
theorem totalExteriorPluckerCoordinates_word_weight (w : Fin n → ℕ)
    (L : List (Fin n)) (hs : L.length=s) :
    (totalExteriorPluckerCoordinates (K := K) s n (indexExteriorWord L)).IsWeightedHomogeneous (pluckerVertexWeight w) (L.map w).sum := by
  subst s
  rw [totalExteriorPluckerCoordinates_word]
  have h := orderedPluckerCoordinate_isWeightedHomogeneous (K := K) w L.get
  have he : (L.map w).sum = ∑ i : Fin L.length,w (L.get i) := by
    calc
      (L.map w).sum = (List.ofFn (fun i : Fin L.length => w (L.get i))).sum := by
        rw [List.ofFn_comp',List.ofFn_get]
      _ = _ := List.sum_ofFn
  rwa [←he] at h

theorem totalExteriorPluckerCoordinates_word_lower (w : Fin n → ℕ)
    (L : List (Fin n)) (hs : L.length=s) (d : ℕ) (hd : (L.map w).sum<d) :
    totalExteriorPluckerCoordinates (K := K) s n (indexExteriorWord L) ∈
      lowerWeightSpace (pluckerVertexWeight w) d :=
  lowerWeightSpace_mem_of_homogeneous _ _ _ _
    (totalExteriorPluckerCoordinates_word_weight w L hs) hd

/-- The coordinate image of multiplication by any of the given actual
two-forms is a member of the literal isotropic Plücker ideal. -/
theorem totalExteriorPluckerCoordinates_wedge_mem
    (forms : Fin m → StrictPairs n → K) (l : Fin m)
    (x : ExteriorAlgebra K (Fin n → K)) (hx : x∈⋀[K]^t (Fin n → K)) :
    totalExteriorPluckerCoordinates (K := K) (t+2) n
      ((twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K))*x) ∈ isotropicPluckerIdeal (t := t) forms := by
  change totalExteriorPluckerCoordinates (K := K) (t+2) n
    (coefficientWedge (forms l) (⟨x,hx⟩ : ⋀[K]^t (Fin n → K))) ∈ _
  rw [totalExteriorPluckerCoordinates_coe]
  apply Submodule.mem_sup_right
  apply Ideal.span_mono ?_ (exteriorPluckerCoordinates_wedge_mem (forms l) ⟨x,hx⟩)
  rintro _ ⟨J,rfl⟩
  exact ⟨(l,J),rfl⟩

/-- Linear transport of the complete supported prefix inverse: proving a
lower-weight bound on every actual support state suffices for the full inverse.
The support is supplied by the proved inverse theorem, not an assumed choice. -/
theorem supported_prefix_transport_lower
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (u v : ι → (Fin n → K)) (A B : Finset ι)
    (f : ExteriorAlgebra K (Fin n → K) →ₗ[K] MvPolynomial (PluckerIndex s n) K)
    (w : Fin n → ℕ) (d : ℕ)
    (hstates : ∀ T, f (prefixInverseState u v A B T)∈lowerWeightSpace (pluckerVertexWeight w) d)
    (η : ExteriorAlgebra K (Fin n → K)) (hη : η∈prefixInverseSpace u v A B) :
    f η∈lowerWeightSpace (pluckerVertexWeight w) d := by
  have hle : prefixInverseSpace u v A B ≤
      (lowerWeightSpace (pluckerVertexWeight w) d).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T,rfl⟩
    exact hstates T
  exact hle hη

end PaperVerification.AlternatingForms
