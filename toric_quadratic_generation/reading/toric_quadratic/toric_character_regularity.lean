module

public import PaperVerification.ToricCharacterMultiplication
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

@[expose] public section

/-!
# Semigroup chart rings and character shifts inside the actual group algebra

The chart ring is the image of its genuine semigroup-algebra homomorphism
into k[M]. Its underlying module is proved to consist exactly of the
Laurent polynomials with support in the semigroup. Multiplication by a
Cartier character is an actual linear automorphism and translates the
exponent set. Arbitrary intersections preserve this exact support meaning.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Pointwise

variable (k : Type*) [CommSemiring k]
variable {M : Type*} [AddCommMonoid M]

def monoidChartMap (S : AddSubmonoid M) :
    AddMonoidAlgebra k S →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k S.subtype

@[simp] theorem monoidChartMap_single (S : AddSubmonoid M) (m : S) (r : k) :
    monoidChartMap k S (single m r) = single (m : M) r := by
  simp [monoidChartMap]

theorem monoidChartMap_injective (S : AddSubmonoid M) :
    Function.Injective (monoidChartMap k S) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- This is a genuine subalgebra of the group algebra, obtained as an
algebra-homomorphism image, rather than an assumed affine-chart model. -/
def monoidChartAlgebra (S : AddSubmonoid M) : Subalgebra k (AddMonoidAlgebra k M) :=
  (monoidChartMap k S).range

def monoidChartAlgebraEquiv (S : AddSubmonoid M) :
    AddMonoidAlgebra k S ≃ₐ[k] monoidChartAlgebra k S :=
  AlgEquiv.ofInjective (monoidChartMap k S) (monoidChartMap_injective k S)

theorem range_monoidChartMap (S : AddSubmonoid M) :
    LinearMap.range (monoidChartMap k S).toLinearMap = characterModule k (S : Set M) := by
  rw [← Submodule.map_top, ← (AddMonoidAlgebra.basis S k).span_eq,
    Submodule.map_span, characterModule_eq_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨m, rfl⟩, rfl⟩
    exact ⟨(m : M), m.property, by simp⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨AddMonoidAlgebra.basis S k ⟨m, hm⟩,
      Set.mem_range_self _, by simp⟩

theorem monoidChartAlgebra_toSubmodule (S : AddSubmonoid M) :
    (monoidChartAlgebra k S).toSubmodule = characterModule k (S : Set M) :=
  range_monoidChartMap k S

theorem mem_monoidChartAlgebra (S : AddSubmonoid M) (f : AddMonoidAlgebra k M) :
    f ∈ monoidChartAlgebra k S ↔ (f.coeff.support : Set M) ⊆ S := by
  change f ∈ (monoidChartAlgebra k S).toSubmodule ↔ _
  rw [monoidChartAlgebra_toSubmodule, mem_characterModule_iff]

theorem characterModule_iInter {ι : Sort*} (S : ι → Set M) :
    characterModule k (⋂ i, S i) = ⨅ i, characterModule k (S i) := by
  ext f
  simp only [Submodule.mem_iInf, mem_characterModule_iff, Set.subset_iInter_iff]

section Translation

variable {G : Type*} [AddCommGroup G]

/-- Multiplication by χ^v, with the genuine inverse multiplication by
χ^(-v). It acts on the full Laurent-character algebra. -/
def characterTranslation (v : G) : AddMonoidAlgebra k G ≃ₗ[k] AddMonoidAlgebra k G where
  toFun f := single v (1 : k) * f
  invFun f := single (-v) (1 : k) * f
  left_inv f := by simp [← mul_assoc, ← AddMonoidAlgebra.one_def]
  right_inv f := by simp [← mul_assoc, ← AddMonoidAlgebra.one_def]
  map_add' f g := mul_add _ _ _
  map_smul' r f := mul_smul_comm _ _ _

@[simp] theorem characterTranslation_apply (v : G) (f : AddMonoidAlgebra k G) :
    characterTranslation k v f = single v (1 : k) * f := rfl

@[simp] theorem characterTranslation_single (v m : G) (r : k) :
    characterTranslation k v (single m r) = single (v + m) r := by
  simp [characterTranslation]

@[simp] theorem characterTranslation_neg (v : G) :
    (characterTranslation k v).symm = characterTranslation k (-v) := by
  ext f
  rfl

/-- An actual principal character shift translates exactly the support
set, without a convexity, lattice-basis, or finite-generation assumption. -/
theorem map_characterTranslation (v : G) (S : Set G) :
    (characterModule k S).map (characterTranslation k v).toLinearMap =
      characterModule k ((fun m => v + m) '' S) := by
  rw [characterModule_eq_span, Submodule.map_span, characterModule_eq_span]
  congr 1
  simp only [Set.image_image, LinearEquiv.coe_coe, Function.comp_def,
    characterTranslation_single]

theorem mem_characterTranslation_image (v : G) (S : Set G) (f : AddMonoidAlgebra k G) :
    (∃ g ∈ characterModule k S, single v (1 : k) * g = f) ↔
      (f.coeff.support : Set G) ⊆ (fun m => v + m) '' S := by
  change f ∈ (characterModule k S).map (characterTranslation k v).toLinearMap ↔ _
  rw [map_characterTranslation, mem_characterModule_iff]

/-- The intersection of the actual principal chart modules has precisely
the intersection of their allowed exponent sets as its support condition. -/
theorem intersection_principal_character_modules {ι : Sort*}
    (S : ι → AddSubmonoid G) (v : ι → G) :
    (⨅ i, ((monoidChartAlgebra k (S i)).toSubmodule).map
      (characterTranslation k (v i)).toLinearMap) =
      characterModule k (⋂ i, (fun m => v i + m) '' (S i : Set G)) := by
  simp only [monoidChartAlgebra_toSubmodule, map_characterTranslation,
    characterModule_iInter]

end Translation

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monoidChartAlgebra_toSubmodule
#print axioms PaperVerification.ToricCharacters.intersection_principal_character_modules
