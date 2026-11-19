module

public import Continuation.Runtime.RegularClosure
public import Recovery.Unimodular.RegularMatroid.StandardRepresentations
public import Recovery.Unimodular.RegularMatroid.ModularTUCriterion
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatroid
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic
public import Recovery.Unimodular.PriorExtensions.SignedSumsPivot
public import Recovery.Unimodular.PriorExtensions.SignedSumsRegular
public import Recovery.Unimodular.ProductVectorMatroid

/-! # All-fields regularity and totally unimodular representations

The four named sections below retain the exact reviewed proof sources.
The common rational and regular representation infrastructure is imported
from its native consolidated modules. No theorem hypothesis is changed.
-/

set_option debug.skipKernelTC false
set_option maxHeartbeats 0


/-! Field invariance, the modular criterion, and standard representations
are supplied by the imported unique owners. Their exact public declarations
and all observations remain available; the following equivalence is retained. -/

section Exact_Continuation_RegularMatroid_RegularityEquivalence


/-!
# Equivalence of the two regular-matroid conventions

Representability over every field and existence of a rational totally
unimodular matrix define the same class of finite ordinary matroids. The
proof uses the actual binary and ternary representations and does not
invoke Seymour decomposition or an excluded-minor theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matroid

namespace Unimodular.RegularRepresentation

/-- The all-fields and rational-TU definitions coincide on every actual
finite ground set, including loops, parallel elements and rank zero. -/
theorem regularOnGround_iff_rationalTU {E : Type*} (M : Matroid E) [M.Finite] :
    RegularOnGround M ↔ RepresentationBridge.RegularOnGround M := by
  classical
  letI : Fintype M.E := M.ground_finite.fintype
  constructor
  · intro hM
    obtain ⟨B, A, hA, hrep⟩ := exists_tu_of_binary_ternary
      (M.restrictSubtype M.E) (hM (ZMod 2)) (hM (ZMod 3))
    exact RepresentationBridge.RegularOnGround.of_rationalTU M
      (fun i e => (A i e : ℚ))
      (RepresentationBridge.integer_totallyUnimodular_ratCast A hA) hrep
  · intro hM K _
    obtain ⟨n, A, hA, hrep⟩ :=
      (RepresentationBridge.regularOnGround_iff_integer M).mp hM
    change RepresentationBridge.HasFiniteRepresentation K (M.restrictSubtype M.E)
    rw [tu_representation_all_fields (K := K) (M.restrictSubtype M.E) A hA hrep]
    exact RepresentationBridge.hasFiniteRepresentation_ofFamily _

/-- A rational TU representation gives representations over fields in any
universe, not merely the small fields appearing in the definition. -/
theorem rationalTU_representable {E : Type*} {M : Matroid E} [M.Finite]
    (hM : RepresentationBridge.RegularOnGround M) (K : Type*) [Field K] :
    RepresentationBridge.RepresentableOnGround K M :=
  ((regularOnGround_iff_rationalTU M).mpr hM).representable K

end Unimodular.RegularRepresentation

end
end
end Exact_Continuation_RegularMatroid_RegularityEquivalence

#print axioms Unimodular.SignedSums.tu_matroid_field_invariant
#print axioms Unimodular.ModularTU.isTotallyUnimodular_iff_modularAgreement
#print axioms Unimodular.RegularRepresentation.exists_tu_of_binary_ternary
#print axioms Unimodular.RegularRepresentation.regularOnGround_iff_binary_ternary
#print axioms Unimodular.RegularRepresentation.RegularOnGround.representable
#print axioms Unimodular.RegularRepresentation.regularOnGround_iff_rationalTU
#print axioms Unimodular.RegularRepresentation.rationalTU_representable
