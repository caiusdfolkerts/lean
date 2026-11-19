module

public import PaperVerification.AlternatingFormsTorusFixedPlanes
public import PaperVerification.OddPathIndependent
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!+# Counting the actual fixed isotropic subspaces

The objects counted here are submodules of the original vector space. Their
defining properties are their actual finite dimension, vanishing of both
alternating forms on every pair of vectors, and equality under every torus
map. The coordinate classification and an explicit finite-set equivalence
identify these objects with the independent subsets of a path.

No geometric cell decomposition or cohomological dimension is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open OddPathIndependent

variable (K : Type*) [Field K] [CharZero K]

/-- The fixed points described by their intrinsic subspace properties. -/
abbrev TorusFixedIsotropicPlanes (k s : ℕ) :=
  {U : Submodule K (ChainSpace K k) //
    Module.finrank K U = s ∧ IsCommonIsotropic k U ∧
      ∀ t : Kˣ, U.map (torusMap k t) = U}

/-- A coordinate vector belongs to a coordinate span exactly when its
index belongs to the indexing set. -/
theorem single_mem_coordinateSubspace_iff (k : ℕ)
    (S : Set (Fin (2 * k + 1))) (i : Fin (2 * k + 1)) :
    Pi.single i (1 : K) ∈ Pi.spanSubset K S ↔ i ∈ S := by
  classical
  constructor
  · intro h
    by_contra hi
    have hz := Pi.mem_spanSubset_iff.mp h i hi
    simpa using hz
  · intro hi
    rw [Pi.mem_spanSubset_iff]
    intro j hj
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [Pi.single_apply, hne]

/-- Distinct coordinate subsets give distinct actual subspaces. -/
theorem coordinateSubspace_injective (k : ℕ) :
    Function.Injective (fun S : Set (Fin (2 * k + 1)) => Pi.spanSubset K S) := by
  intro S T h
  change Pi.spanSubset K S = Pi.spanSubset K T at h
  ext i
  rw [← single_mem_coordinateSubspace_iff K k S i,
    ← single_mem_coordinateSubspace_iff K k T i, h]

/-- An independent coordinate subset gives a fixed common isotropic plane
of precisely its original cardinality. -/
def coordinateFixedPlane (k s : ℕ) (I : CoordinateSubsets k s) :
    TorusFixedIsotropicPlanes K k s :=
  ⟨Pi.spanSubset K (I.val : Set (Fin (2 * k + 1))), by
    refine ⟨?_, ?_, coordinateSubspace_map_torus k _⟩
    · simpa only [Pi.dim_spanSubset, Set.ncard_coe_finset] using I.property.1
    · exact (coordinateSubspace_isotropic_iff k _).mpr I.property.2⟩

theorem coordinateFixedPlane_injective (k s : ℕ) :
    Function.Injective (coordinateFixedPlane K k s) := by
  intro I J h
  apply Subtype.ext
  apply Finset.coe_injective
  apply coordinateSubspace_injective K k
  exact congrArg Subtype.val h

theorem coordinateFixedPlane_surjective (k s : ℕ) :
    Function.Surjective (coordinateFixedPlane K k s) := by
  classical
  intro U
  obtain ⟨S, hS⟩ := (torus_fixed_iff_coordinateSubspace k U.val).mp U.property.2.2
  have hdim : S.toFinset.card = s := by
    have h := U.property.1
    rw [hS, Pi.dim_spanSubset] at h
    simpa only [Set.ncard_eq_toFinset_card'] using h
  have hiso : ChainIndependent k S.toFinset := by
    have h := U.property.2.1
    rw [hS, coordinateSubspace_isotropic_iff] at h
    simpa only [ChainIndependent, IsIndependentCoordinateSet, Set.mem_toFinset] using h
  refine ⟨⟨S.toFinset, hdim, hiso⟩, ?_⟩
  apply Subtype.ext
  change Pi.spanSubset K (↑S.toFinset : Set (Fin (2 * k + 1))) = U.val
  rw [Set.coe_toFinset, ← hS]

/-- The classification is a genuine bijection, not merely an upper bound
on the number of fixed points. -/
def coordinateFixedPlaneEquiv (k s : ℕ) :
    CoordinateSubsets k s ≃ TorusFixedIsotropicPlanes K k s :=
  Equiv.ofBijective (coordinateFixedPlane K k s)
    ⟨coordinateFixedPlane_injective K k s, coordinateFixedPlane_surjective K k s⟩

instance finiteTorusFixedIsotropicPlanes (k s : ℕ) :
    Finite (TorusFixedIsotropicPlanes K k s) :=
  Finite.of_equiv (CoordinateSubsets k s) (coordinateFixedPlaneEquiv K k s)

/-- The exact cardinality of all actual torus-fixed common isotropic
`s`-planes, over every characteristic-zero field and throughout the full range. -/
theorem card_torusFixedIsotropicPlanes (k s : ℕ) (hs : s ≤ k + 1) :
    Nat.card (TorusFixedIsotropicPlanes K k s) = (2 * k + 2 - s).choose s := by
  rw [← Nat.card_congr (coordinateFixedPlaneEquiv K k s)]
  exact card_coordinateSubsets k s hs

end PaperVerification.AlternatingForms.CanonicalUnipotent
