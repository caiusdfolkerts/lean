module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import paper_verification.toric005
public import paper_verification.toric010
public import paper_verification.toric017
public import paper_verification.toric018
public import paper_verification.toric029

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricCartierRationalSections
section Source_ToricCartierRationalSections

-- original header: module

-- original header: public import PaperVerification.ToricDominantCartierPullback

-- original header: @[expose] public section

/-! # Actual section membership under dominant pullback -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

theorem mem_sectionValueRange_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈C.openSet i →
        r/(C.generator i : X.functionField)∈regularAtSubring X x := by
  constructor
  · rintro ⟨s,rfl⟩ i x hx hi
    change rationalValue X U s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact (congrArg (fun v : X.functionField =>
      v / (C.generator i : X.functionField) ∈ regularAtSubring X x)
        (rationalValueAt_eq X U ⟨x,hx⟩
          (show Γ(rationalFunctions X,U) from s.val))).mp
            (s.property i ⟨x,hx⟩ hi)
  · intro h
    let s := (rationalValue X U).symm r
    have hs : C.IsSection U s := by
      intro i x hi
      simpa only [rationalValueAt_eq,s,AddEquiv.apply_symm_apply] using
        h i x.val x.property hi
    exact ⟨⟨s,hs⟩,(rationalValue X U).apply_symm_apply r⟩

/-- Pullback of an actual section is a section of the genuinely
constructed Cartier pullback; the proof uses actual stalk maps. -/
theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈C.toCartierData.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (C.dominantPullback f).toCartierData.sectionValueRange (f ⁻¹ᵁ U) := by
  apply ((C.dominantPullback f).mem_sectionValueRange_iff_stalkwise
    (f ⁻¹ᵁ U) _).mpr
  intro i y hy hi
  have h := (C.mem_sectionValueRange_iff_stalkwise U r).mp hr i (f y) hy hi
  change dominantFunctionFieldMap f r /
    dominantFunctionFieldMap f (C.generator i : X.functionField) ∈ regularAtSubring Y y
  simpa only [map_div₀] using
    dominantFunctionFieldMap_mem_regularAt f y
      (r/(C.generator i : X.functionField)) h

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

theorem mem_sectionValueRange_iff_localStalks (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r∈D.sectionValueRange U ↔
      ∀ i (x : X), x∈U → x∈D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈regularAtSubring X x := by
  rw [D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]
  exact D.localCocycle.mem_sectionValueRange_iff_stalkwise U r

theorem dominantPullback_mem_sectionValueRange
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (r : X.functionField)
    (hr : r∈D.sectionValueRange U) :
    dominantFunctionFieldMap f r∈
      (D.dominantPullback f).sectionValueRange (f ⁻¹ᵁ U) := by
  apply D.localCocycle.dominantPullback_mem_sectionValueRange f U r
  rwa [← D.equivalent_sectionValueRange D.localCocycle.toCartierData
    D.equivalent_localCocycle U]

/-- Local affine neighborhoods suffice for the true global-section
condition. Affineness is not an assumption on the covering cocycle. -/
theorem mem_globalSectionValueRange_of_affine_ratios
    (r : X.functionField)
    (h : ∀ i (U : X.Opens) [Nonempty U], IsAffineOpen U →
      U≤D.localCocycle.openSet i →
        r/(D.localCocycle.generator i : X.functionField)∈
          (X.germToFunctionField U).hom.range) :
    r∈D.sectionValueRange ⊤ := by
  apply (D.mem_sectionValueRange_iff_localStalks ⊤ r).mpr
  intro i x hx hi
  obtain ⟨U,hU,hxU,hUi⟩ := exists_isAffineOpen_mem_and_subset hi
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  obtain ⟨a,ha⟩ := h i U hU hUi
  rw [← ha]
  exact regular_germ_mem_regularAt X U a x hxU

end CartierData

end PaperVerification.ToricSchemes
end
end Source_ToricCartierRationalSections
-- END ORIGINAL PaperVerification.ToricCartierRationalSections


-- BEGIN ORIGINAL PaperVerification.ToricCharacterMultiplication
section Source_ToricCharacterMultiplication

-- original header: module

-- original header: public import Mathlib.Algebra.Algebra.Bilinear
-- original header: public import Mathlib.Algebra.MonoidAlgebra.Basic
-- original header: public import Mathlib.Algebra.MonoidAlgebra.Module
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Map

-- original header: @[expose] public section

/-!
# Multiplication of genuine Laurent-character submodules

For an arbitrary exponent set S, the module V(S) consists of the elements
of the actual additive monoid algebra whose finite support is contained
in S. The tensor-product multiplication map has image exactly V(S+T).
This algebraic statement imposes no finiteness on the exponent sets and
does not assume an identification with global sections of a line bundle.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Pointwise TensorProduct

variable (k : Type*) [CommSemiring k]
variable {M : Type*} [AddCommMonoid M]

/-- The ordinary submodule of the monoid algebra with support in S. -/
abbrev characterModule (S : Set M) : Submodule k (AddMonoidAlgebra k M) :=
  AddMonoidAlgebra.supported k k S

theorem mem_characterModule_iff (S : Set M) (f : AddMonoidAlgebra k M) :
    f ∈ characterModule k S ↔ (f.coeff.support : Set M) ⊆ S :=
  AddMonoidAlgebra.mem_supported

theorem characterModule_eq_span (S : Set M) :
    characterModule k S = Submodule.span k ((fun m : M => single m (1 : k)) '' S) :=
  AddMonoidAlgebra.supported_eq_span_single k S

theorem characterModule_mono {S T : Set M} (h : S ⊆ T) :
    characterModule k S ≤ characterModule k T :=
  AddMonoidAlgebra.supported_mono h

theorem single_mem_characterModule [Nontrivial k] (S : Set M) (m : M) :
    single m (1 : k) ∈ characterModule k S ↔ m ∈ S := by
  rw [characterModule_eq_span]
  exact AddMonoidAlgebra.single_mem_span_single

/-- Multiplication on the actual monoid algebra, restricted on its two
tensor factors but initially retaining the full algebra as codomain. -/
def characterMultiplicationAmbient (S T : Set M) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] AddMonoidAlgebra k M :=
  (LinearMap.mul' k (AddMonoidAlgebra k M)).comp
    (TensorProduct.mapIncl (characterModule k S) (characterModule k T))

@[simp] theorem characterMultiplicationAmbient_tmul (S T : Set M)
    (f : characterModule k S) (g : characterModule k T) :
    characterMultiplicationAmbient k S T (f ⊗ₜ[k] g) =
      (f : AddMonoidAlgebra k M) * (g : AddMonoidAlgebra k M) := rfl

theorem character_product_set (S T : Set M) :
    Set.image2 (fun f g : AddMonoidAlgebra k M => f * g)
      ((fun m : M => single m (1 : k)) '' S)
      ((fun m : M => single m (1 : k)) '' T) =
        (fun m : M => single m (1 : k)) '' (S + T) := by
  ext f
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, Set.add_mem_add hx hy, by simp⟩
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨single x 1, ⟨x, hx, rfl⟩,
      single y 1, ⟨y, hy, rfl⟩, by simp⟩

/-- The image is exactly the span of all products of the original
characters; cancellation of coefficients introduces no new exponents. -/
theorem range_characterMultiplicationAmbient (S T : Set M) :
    LinearMap.range (characterMultiplicationAmbient k S T) =
      characterModule k (S + T) := by
  change LinearMap.range (TensorProduct.lift (LinearMap.mul k (AddMonoidAlgebra k M)) ∘ₗ
    TensorProduct.mapIncl (characterModule k S) (characterModule k T)) = _
  rw [← TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  rw [characterModule_eq_span, characterModule_eq_span,
    Submodule.map₂_span_span, characterModule_eq_span]
  congr 1
  exact character_product_set k S T

/-- Multiplication with codomain restricted to any genuine support
module containing the pointwise sum of the two exponent sets. -/
def characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] characterModule k U :=
  (characterMultiplicationAmbient k S T).codRestrict (characterModule k U) (by
    intro x
    apply characterModule_mono k hST
    rw [← range_characterMultiplicationAmbient k S T]
    exact ⟨x, rfl⟩)

@[simp] theorem characterMultiplication_coe (S T U : Set M) (hST : S + T ⊆ U)
    (x : characterModule k S ⊗[k] characterModule k T) :
    ((characterMultiplication k S T U hST x : characterModule k U) :
      AddMonoidAlgebra k M) = characterMultiplicationAmbient k S T x := rfl

@[simp] theorem characterMultiplication_tmul (S T U : Set M) (hST : S + T ⊆ U)
    (f : characterModule k S) (g : characterModule k T) :
    ((characterMultiplication k S T U hST (f ⊗ₜ[k] g) : characterModule k U) :
      AddMonoidAlgebra k M) = (f : AddMonoidAlgebra k M) * g := rfl

theorem range_characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    LinearMap.range (characterMultiplication k S T U hST) =
      (characterModule k (S + T)).comap (characterModule k U).subtype := by
  rw [characterMultiplication, LinearMap.range_codRestrict,
    range_characterMultiplicationAmbient]

/-- Surjectivity is exactly the full lattice-point sum assertion. The
nonzero coefficient hypothesis is necessary to recover an exponent from
its character; it holds over every field, in every characteristic. -/
theorem characterMultiplication_surjective_iff [Nontrivial k]
    (S T U : Set M) (hST : S + T ⊆ U) :
    Function.Surjective (characterMultiplication k S T U hST) ↔ U = S + T := by
  constructor
  · intro hsurj
    apply Set.Subset.antisymm _ hST
    intro m hm
    let χ : characterModule k U :=
      ⟨single m (1 : k), (single_mem_characterModule k U m).mpr hm⟩
    obtain ⟨x, hx⟩ := hsurj χ
    have hχ : single m (1 : k) ∈ LinearMap.range
        (characterMultiplicationAmbient k S T) := by
      refine ⟨x, ?_⟩
      exact congrArg (fun y : characterModule k U => (y : AddMonoidAlgebra k M)) hx
    rw [range_characterMultiplicationAmbient] at hχ
    exact (single_mem_characterModule k (S + T) m).mp hχ
  · intro hU f
    have hf : (f : AddMonoidAlgebra k M) ∈ characterModule k (S + T) := by
      rw [← hU]
      exact f.property
    rw [← range_characterMultiplicationAmbient k S T] at hf
    obtain ⟨x, hx⟩ := hf
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.range_characterMultiplicationAmbient
#print axioms PaperVerification.ToricCharacters.characterMultiplication_surjective_iff
end
end Source_ToricCharacterMultiplication
-- END ORIGINAL PaperVerification.ToricCharacterMultiplication


-- BEGIN ORIGINAL PaperVerification.ToricCharacterRegularity
section Source_ToricCharacterRegularity

-- original header: module

-- original header: public import PaperVerification.ToricCharacterMultiplication
-- original header: public import Mathlib.Algebra.MonoidAlgebra.Support
-- original header: public import Mathlib.Algebra.Algebra.Subalgebra.Basic

-- original header: @[expose] public section

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
end
end Source_ToricCharacterRegularity
-- END ORIGINAL PaperVerification.ToricCharacterRegularity


-- BEGIN ORIGINAL PaperVerification.ToricSmoothChartAlgebra
section Source_ToricSmoothChartAlgebra

-- original header: module

-- original header: public import PaperVerification.ToricCharacterRegularity
-- original header: public import Mathlib.Algebra.MvPolynomial.Basic
-- original header: public import Mathlib.LinearAlgebra.Finsupp.Pi
-- original header: public import Mathlib.LinearAlgebra.Basis.Basic

-- original header: @[expose] public section

/-!
# Actual polynomial and Laurent coordinates on a smooth semigroup chart

The nonnegative coordinates of a subset of an integral basis form the
actual dual-cone semigroup. The remaining coordinates are unrestricted
integers. An explicit additive equivalence identifies this semigroup with
N^I × Z^(I-complement), and hence identifies its semigroup algebra with a
polynomial ring over the corresponding Laurent-character algebra.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℤ E]

abbrev FreeCoordinate (I : Finset ι) := {i : ι // i ∉ I}

def coordinateConeMonoid (b : Module.Basis ι ℤ E) (I : Finset ι) : AddSubmonoid E where
  carrier := {x | ∀ i ∈ I, 0 ≤ b.repr x i}
  zero_mem' := by intro i hi; simp
  add_mem' := by
    intro x y hx hy i hi
    simpa only [map_add, Finsupp.add_apply] using add_nonneg (hx i hi) (hy i hi)

def assembleConeCoordinates (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) : E :=
  b.equivFun.symm (fun i => if hi : i ∈ I then (x.1 ⟨i, hi⟩ : ℤ) else x.2 ⟨i, hi⟩)

theorem assembleConeCoordinates_repr (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) (i : ι) :
    b.repr (assembleConeCoordinates b I x) i =
      if hi : i ∈ I then (x.1 ⟨i, hi⟩ : ℤ) else x.2 ⟨i, hi⟩ := by
  change b.equivFun (b.equivFun.symm _) i = _
  rw [b.equivFun.apply_symm_apply]

theorem assembleConeCoordinates_mem (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) :
    assembleConeCoordinates b I x ∈ coordinateConeMonoid b I := by
  intro i hi
  rw [assembleConeCoordinates_repr, dif_pos hi]
  exact Int.natCast_nonneg _

/-- The semigroup equivalence is integral and explicit in both directions. -/
def coordinateConeEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    coordinateConeMonoid b I ≃+ (I → ℕ) × (FreeCoordinate I → ℤ) where
  toFun x := (fun i => (b.repr (x : E) i).toNat, fun i => b.repr (x : E) i)
  invFun x := ⟨assembleConeCoordinates b I x, assembleConeCoordinates_mem b I x⟩
  left_inv x := by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rw [Module.Basis.equivFun_apply, assembleConeCoordinates_repr,
      Module.Basis.equivFun_apply]
    split_ifs with hi
    · exact Int.toNat_of_nonneg (x.property i hi)
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      change (b.repr (assembleConeCoordinates b I x) i).toNat = x.1 i
      rw [assembleConeCoordinates_repr, dif_pos i.property]
      exact Int.toNat_natCast _
    · funext i
      change b.repr (assembleConeCoordinates b I x) i = x.2 i
      rw [assembleConeCoordinates_repr, dif_neg i.property]
  map_add' x y := by
    apply Prod.ext
    · funext i
      change (b.repr ((x : E) + (y : E)) i).toNat =
        (b.repr (x : E) i).toNat + (b.repr (y : E) i).toNat
      rw [map_add, Finsupp.add_apply,
        Int.toNat_add (x.property i i.property) (y.property i i.property)]
    · funext i
      exact congrArg (fun z : ι →₀ ℤ => z i) (b.repr.map_add (x : E) (y : E))

def naturalFunctionFinsuppEquiv (J : Type*) [Finite J] : (J → ℕ) ≃+ (J →₀ ℕ) :=
  (Finsupp.linearEquivFunOnFinite ℕ ℕ J).symm.toAddEquiv

def polynomialConeEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    coordinateConeMonoid b I ≃+ (I →₀ ℕ) × (FreeCoordinate I → ℤ) :=
  (coordinateConeEquiv b I).trans
    ((naturalFunctionFinsuppEquiv I).prodCongr (AddEquiv.refl (FreeCoordinate I → ℤ)))

variable (k : Type*) [CommSemiring k]

/-- The intrinsic semigroup chart algebra is a polynomial ring over a
Laurent-character algebra. This includes the zero cone and full cones. -/
def smoothSemigroupAlgebraEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    AddMonoidAlgebra k (coordinateConeMonoid b I) ≃ₐ[k]
      MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ)) :=
  (AddMonoidAlgebra.domCongr k k (polynomialConeEquiv b I)).trans
    (AddMonoidAlgebra.curryAlgEquiv k)

/-- The same algebra equivalence for the actual subalgebra of k[E]
used by a chart. The inclusion into k[E] was proved injective separately. -/
def smoothChartAlgebraEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    monoidChartAlgebra k (coordinateConeMonoid b I) ≃ₐ[k]
      MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ)) :=
  (monoidChartAlgebraEquiv k (coordinateConeMonoid b I)).symm.trans
    (smoothSemigroupAlgebraEquiv k b I)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smoothChartAlgebraEquiv
end
end Source_ToricSmoothChartAlgebra
-- END ORIGINAL PaperVerification.ToricSmoothChartAlgebra


-- BEGIN ORIGINAL PaperVerification.ToricCartierCharacterModules
section Source_ToricCartierCharacterModules

-- original header: module

-- original header: public import PaperVerification.ToricSmoothChartAlgebra
-- original header: public import PaperVerification.ToricFanPolytopeConstruction
-- original header: public import PaperVerification.ToricAdjointSupport

-- original header: @[expose] public section

/-!
# Exact intersection of the actual principal character modules

Each affine semigroup chart is a genuine subalgebra of the Laurent
algebra. Its Cartier module is its image under multiplication by the
actual Cartier character. Their intersection is proved to be exactly
the module supported on all integral points of the support polytope.
No global-section or scheme dictionary is assumed by this statement.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

def integerPairing {n : ℕ} (u m : Lattice n) : ℤ := ∑ j, u j * m j

theorem integerPairing_add {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m + p) = integerPairing u m + integerPairing u p := by
  simp only [integerPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem integerPairing_sub {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m - p) = integerPairing u m - integerPairing u p := by
  simp only [integerPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

def dualConeMonoid {n : ℕ} (s : Finset (Lattice n)) : AddSubmonoid (Lattice n) where
  carrier := {m | ∀ u ∈ s, 0 ≤ integerPairing u m}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [integerPairing_add]
    exact add_nonneg (hm u hu) (hp u hu)

/-- Smoothness gives the actual free semigroup coordinates of the
dual cone, including its unrestricted Laurent directions. -/
theorem dualConeMonoid_basis_eq {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    dualConeMonoid (I.image b) = coordinateConeMonoid (integralDualBasis b) I := by
  ext m
  change (∀ u ∈ I.image b, 0 ≤ integerPairing u m) ↔
    ∀ i ∈ I, 0 ≤ (integralDualBasis b).repr m i
  constructor
  · intro h i hi
    have hh := h (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using hh
  · intro h u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using h i hi

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierLatticePoint_pairing (a : Lattice n → ℤ) (s : «Σ».fullCones)
    (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
    integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
  have h := «Σ».cartierPoint_support_eq_of_mem (fun v => (a v : ℝ)) s hu
  rw [← «Σ».embed_cartierLatticePoint a s, normalRay_pairing_lattice] at h
  exact_mod_cast h

theorem cartier_translate_dualCone (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    (fun m => «Σ».cartierLatticePoint a s + m) ''
      (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) =
        {m | ∀ u ∈ (s : Finset (Lattice n)), -a u ≤ integerPairing u m} := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩ u hu
    rw [integerPairing_add, «Σ».cartierLatticePoint_pairing a s u hu]
    exact le_add_of_nonneg_right (hw u hu)
  · intro hm
    refine ⟨m - «Σ».cartierLatticePoint a s, ?_, by abel⟩
    intro u hu
    rw [integerPairing_sub, «Σ».cartierLatticePoint_pairing a s u hu]
    exact sub_nonneg.mpr (hm u hu)

def fanIntegralExponents (a : Lattice n → ℤ) : Set (Lattice n) :=
  {m | embed n m ∈ «Σ».fanPolytope (fun u => (a u : ℝ))}

theorem integral_exponents_eq_chart_intersection (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) :
    «Σ».fanIntegralExponents a =
      ⋂ s : «Σ».fullCones, (fun m => «Σ».cartierLatticePoint a s + m) ''
        (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) := by
  ext m
  simp only [Set.mem_iInter, «Σ».cartier_translate_dualCone, Set.mem_setOf_eq]
  constructor
  · intro hm s u hu
    have h := hm u («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu)
    rw [normalRay_pairing_lattice] at h
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ) at h
    exact_mod_cast h
  · intro hm u hu
    obtain ⟨t, ht, hut⟩ := («Σ».mem_rays_iff u).mp hu
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    have h := hm s' u (hts hut)
    rw [normalRay_pairing_lattice]
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ)
    exact_mod_cast h

variable (k : Type*) [CommSemiring k]

/-- The local principal module, defined by actual multiplication in the
Laurent algebra of the actual semigroup chart ring. -/
def cartierChartCharacterModule (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    Submodule k (AddMonoidAlgebra k (Lattice n)) :=
  ((monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))).toSubmodule).map
    (characterTranslation k («Σ».cartierLatticePoint a s)).toLinearMap

/-- Exact global compatibility at the character-module level. This is
the algebraic computation needed after identifying a toric line bundle's
actual global sections with these local principal modules. -/
theorem iInf_cartierChartCharacterModule (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    (⨅ s : «Σ».fullCones, «Σ».cartierChartCharacterModule k a s) =
      characterModule k («Σ».fanIntegralExponents a) := by
  rw [«Σ».integral_exponents_eq_chart_intersection hpure a]
  exact intersection_principal_character_modules k
    (fun s : «Σ».fullCones => dualConeMonoid (s : Finset (Lattice n)))
    («Σ».cartierLatticePoint a)

/-- Every genuine smooth cone has the proved polynomial/Laurent chart
algebra, with its actual ray set and a chosen integral basis extension. -/
theorem smooth_chart_algebra (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      s = I.image b ∧ Nonempty
        (monoidChartAlgebra k (dualConeMonoid s) ≃ₐ[k]
          MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ))) := by
  obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
  refine ⟨b, I, hI, ?_⟩
  rw [hI, dualConeMonoid_basis_eq]
  exact ⟨smoothChartAlgebraEquiv k (integralDualBasis b) I⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.iInf_cartierChartCharacterModule
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.smooth_chart_algebra
end
end Source_ToricCartierCharacterModules
-- END ORIGINAL PaperVerification.ToricCartierCharacterModules


-- BEGIN ORIGINAL PaperVerification.ToricFanIntegralCoefficients
section Source_ToricFanIntegralCoefficients

-- original header: module

-- original header: public import PaperVerification.ToricCartierCharacterModules

-- original header: @[expose] public section

/-! # Recovering integral support coefficients from compatible chart characters -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)

include hpure in
theorem exists_fullCone_of_ray (u : «Σ».rays) :
    ∃ s : «Σ».fullCones,u.val∈s.val := by
  obtain ⟨t,ht,hut⟩ := («Σ».mem_rays_iff u.val).mp u.property
  obtain ⟨s,hs,hts,hcard⟩ := hpure t ht
  exact ⟨⟨s,Finset.mem_filter.mpr ⟨hs,hcard⟩⟩,hts hut⟩

def rayFullCone (u : «Σ».rays) : «Σ».fullCones :=
  («Σ».exists_fullCone_of_ray hpure u).choose

theorem mem_rayFullCone (u : «Σ».rays) : u.val∈(«Σ».rayFullCone hpure u).val :=
  («Σ».exists_fullCone_of_ray hpure u).choose_spec

/-- Only actual rays carry coefficients; the extension away from the
finite ray set is fixed to zero and has no geometric effect. -/
def coefficientsOfCharacters (m : «Σ».fullCones→Lattice n) (u : Lattice n) : ℤ :=
  if hu : u∈«Σ».rays then -integerPairing u (m («Σ».rayFullCone hpure ⟨u,hu⟩)) else 0

theorem coefficientsOfCharacters_pairing (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t))
    (s : «Σ».fullCones) (u : Lattice n) (hu : u∈s.val) :
    integerPairing u (m s) = -«Σ».coefficientsOfCharacters hpure m u := by
  have hray : u∈«Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu
  rw [coefficientsOfCharacters,dif_pos hray,neg_neg]
  exact hcompat s («Σ».rayFullCone hpure ⟨u,hray⟩) u hu
    («Σ».mem_rayFullCone hpure ⟨u,hray⟩)

/-- A full smooth cone determines the lattice character uniquely from
its actual pairings with the primitive ray basis. -/
theorem eq_cartierLatticePoint_of_pairings (a : Lattice n→ℤ)
    (s : «Σ».fullCones) (m : Lattice n)
    (hm : ∀ u∈s.val,integerPairing u m = -a u) :
    m=«Σ».cartierLatticePoint a s := by
  apply (integralDualBasis («Σ».fullConeBasis s)).repr.injective
  ext i
  have hi : «Σ».fullConeBasis s i∈s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have h := (hm _ hi).trans («Σ».cartierLatticePoint_pairing a s _ hi).symm
  simpa only [integerPairing,integralDualBasis_repr,mul_comm] using h

/-- Compatibility on common rays reconstructs one honest integral
coefficient function whose ordinary Cartier points are the given characters. -/
theorem characters_eq_cartierLatticePoint (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t)) (s : «Σ».fullCones) :
    m s=«Σ».cartierLatticePoint («Σ».coefficientsOfCharacters hpure m) s :=
  «Σ».eq_cartierLatticePoint_of_pairings _ s (m s)
    («Σ».coefficientsOfCharacters_pairing hpure m hcompat s)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.characters_eq_cartierLatticePoint
end
end Source_ToricFanIntegralCoefficients
-- END ORIGINAL PaperVerification.ToricFanIntegralCoefficients


-- BEGIN ORIGINAL PaperVerification.ToricLaurentPicard
section Source_ToricLaurentPicard

-- original header: module

-- original header: public import Mathlib.Algebra.MonoidAlgebra.Basic
-- original header: public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
-- original header: public import Mathlib.Algebra.Polynomial.Laurent
-- original header: public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
-- original header: public import Mathlib.RingTheory.Polynomial.UniqueFactorization
-- original header: public import Mathlib.RingTheory.PicardGroup

-- original header: @[expose] public section

/-!
# The actual split-torus coordinate ring has trivial Picard group

The group algebra of Z^n is identified, recursively and explicitly, with
an iterated Laurent polynomial ring. Polynomial unique factorization and
localization preserve unique factorization. Mathlib's class-group/Picard
equivalence then trivializes every actual invertible module over this ring.
The passage from invertible sheaves on its spectrum to modules is separate.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped Polynomial nonZeroDivisors

def latticeSuccCoordinates (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  map_add' _ _ := rfl

abbrev torusCoordinateRing (k : Type*) [CommRing k] (n : ℕ) :=
  AddMonoidAlgebra k (Fin n → ℤ)

variable (k : Type*) [Field k]

/-- Separating the first character coordinate gives an actual algebra
equivalence with a one-variable Laurent extension of the smaller torus. -/
def torusCoordinateRingSucc (n : ℕ) :
    torusCoordinateRing k (n + 1) ≃ₐ[k]
      AddMonoidAlgebra (torusCoordinateRing k n) ℤ :=
  (AddMonoidAlgebra.domCongr k k (latticeSuccCoordinates n)).trans
    (AddMonoidAlgebra.curryAlgEquiv k)

theorem torusCoordinateRing_isDomain (n : ℕ) : IsDomain (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact MulEquiv.isDomain k
        (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).toMulEquiv
  | succ n ih =>
      letI := ih
      exact MulEquiv.isDomain (AddMonoidAlgebra (torusCoordinateRing k n) ℤ)
        (torusCoordinateRingSucc k n).toMulEquiv

/-- Laurent extension preserves unique factorization by its literal
localization presentation at powers of the polynomial variable. -/
theorem laurent_uniqueFactorization (A : Type*) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] : UniqueFactorizationMonoid (AddMonoidAlgebra A ℤ) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial A)) (AddMonoidAlgebra A ℤ)

theorem torusCoordinateRing_uniqueFactorization (n : ℕ) :
    UniqueFactorizationMonoid (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact ((AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).symm.toMulEquiv).uniqueFactorizationMonoid
        inferInstance
  | succ n ih =>
      letI := ih
      letI := torusCoordinateRing_isDomain k n
      letI := laurent_uniqueFactorization (torusCoordinateRing k n)
      exact ((torusCoordinateRingSucc k n).symm.toMulEquiv).uniqueFactorizationMonoid inferInstance

/-- The Picard group here is Mathlib's actual group of invertible
modules under tensor product, not a fan-defined substitute. -/
theorem torusPic_subsingleton (n : ℕ) :
    Subsingleton (CommRing.Pic (torusCoordinateRing k n)) := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  infer_instance

/-- Every invertible module over the actual split-torus coordinate
ring admits a global rank-one trivialization. -/
def torusInvertibleModuleEquiv (n : ℕ) (V : Type*)
    [AddCommGroup V] [Module (torusCoordinateRing k n) V]
    [Module.Invertible (torusCoordinateRing k n) V] :
    V ≃ₗ[torusCoordinateRing k n] torusCoordinateRing k n := by
  letI := torusPic_subsingleton k n
  exact Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)

theorem torusFractionalIdeal_principal (n : ℕ)
    (I : FractionalIdeal (torusCoordinateRing k n)⁰
      (FractionRing (torusCoordinateRing k n))) (hI : IsUnit I) :
    (I : Submodule (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))).IsPrincipal := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  exact ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.torusCoordinateRing_uniqueFactorization
#print axioms PaperVerification.ToricCharacters.torusInvertibleModuleEquiv
end
end Source_ToricLaurentPicard
-- END ORIGINAL PaperVerification.ToricLaurentPicard


-- BEGIN ORIGINAL PaperVerification.ToricLocallyInvertible
section Source_ToricLocallyInvertible

-- original header: module

-- original header: public import Mathlib.RingTheory.PicardGroup
-- original header: public import Mathlib.RingTheory.LocalProperties.FinitePresentation
-- original header: public import Mathlib.RingTheory.LocalProperties.Exactness
-- original header: public import Mathlib.RingTheory.Localization.BaseChange

-- original header: @[expose] public section

/-!
# Actual rank-one local frames imply module invertibility

Local rank-one trivializations first imply finite presentation. Localization
then commutes with the dual and tensor product, carrying the canonical
evaluation pairing to its local counterpart. Its local bijectivity proves
global bijectivity. Neither finite generation nor projectivity nor a
global trivialization is an extra input.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open Module TensorProduct
open scoped TensorProduct

section OneLocalization

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] [Module A N] [IsScalarTower R A N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f]

/-- Localization of actual linear functionals, with scalars extended
to the localized ring. -/
def localizedDual : Dual R M →ₗ[R] Dual A N :=
  IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R A) A

@[simp] theorem localizedDual_apply (φ : Dual R M) (m : M) :
    localizedDual S A f φ (f m) = algebraMap R A (φ m) := by
  exact IsLocalizedModule.map_apply S f (Algebra.linearMap R A) φ m

instance localizedDual_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedDual S A f) := by
  dsimp only [localizedDual]
  infer_instance

/-- The actual localization map on the domain of the evaluation
pairing. The tensor product in the codomain is over the localized ring. -/
def localizedEvaluationDomainMap :
    Dual R M ⊗[R] M →ₗ[R] Dual A N ⊗[A] N :=
  ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map (localizedDual S A f) f)

@[simp] theorem localizedEvaluationDomainMap_tmul (φ : Dual R M) (m : M) :
    localizedEvaluationDomainMap S A f (φ ⊗ₜ[R] m) =
      localizedDual S A f φ ⊗ₜ[A] f m := rfl

instance localizedEvaluationDomainMap_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedEvaluationDomainMap S A f) := by
  exact IsLocalizedModule.of_linearEquiv S
    (TensorProduct.map (localizedDual S A f) f)
    ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R)

/-- The evaluation pairing commutes with the genuine localization maps. -/
theorem contractLeft_localization [Module.FinitePresentation R M] :
    IsLocalizedModule.map S (localizedEvaluationDomainMap S A f)
        (Algebra.linearMap R A) (contractLeft R M) =
      (contractLeft A N).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext S (localizedEvaluationDomainMap S A f)
    (Algebra.linearMap R A)
  apply TensorProduct.ext'
  intro φ m
  simpa only [LinearMap.comp_apply, contractLeft_apply, Algebra.linearMap_apply,
    LinearMap.restrictScalars_apply, localizedEvaluationDomainMap_tmul, localizedDual_apply] using
    IsLocalizedModule.map_apply S (localizedEvaluationDomainMap S A f)
      (Algebra.linearMap R A) (contractLeft R M) (φ ⊗ₜ[R] m)

end OneLocalization

section PrincipalCover

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (s : Set R) (hs : Ideal.span s = ⊤)
  (A : s → Type*) [∀ r, CommRing (A r)] [∀ r, Algebra R (A r)]
  [∀ r : s, IsLocalization.Away r.val (A r)]
  (N : s → Type*) [∀ r, AddCommGroup (N r)] [∀ r, Module R (N r)]
  [∀ r, Module (A r) (N r)] [∀ r, IsScalarTower R (A r) (N r)]
  (f : ∀ r, M →ₗ[R] N r) [∀ r : s, IsLocalizedModule.Away r.val (f r)]

include hs f in
/-- A module with actual rank-one frames on a principal-open cover is
invertible in the tensor-product sense used by Mathlib's Picard group.
The cover need not be presented as finite: finite presentation is derived
from the unit-ideal cover by the local-property theorem. -/
theorem invertible_of_principalCover_rankOne
    (hframe : ∀ r : s, Nonempty (N r ≃ₗ[A r] A r)) :
    Module.Invertible R M := by
  classical
  let e (r : s) : N r ≃ₗ[A r] A r := Classical.choice (hframe r)
  letI (r : s) : Module.FinitePresentation (A r) (N r) :=
    Module.FinitePresentation.of_equiv (e r).symm
  letI : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' (Rₚ := A) s hs f (fun r => inferInstance)
  letI (r : s) : Module.Invertible (A r) (N r) :=
    Module.Invertible.congr (e r).symm
  refine ⟨?_⟩
  apply bijective_of_isLocalized_span s hs
    (fun r => Dual (A r) (N r) ⊗[A r] N r)
    (fun r => localizedEvaluationDomainMap (Submonoid.powers r.val) (A r) (f r))
    A (fun r => Algebra.linearMap R (A r)) (contractLeft R M)
  intro r
  rw [contractLeft_localization]
  exact Module.Invertible.bijective

include hs in
/-- Specialization to the canonical localized ring and module, without
requiring any identifications as extra structure. -/
theorem invertible_of_localizationCover_rankOne
    (hframe : ∀ r : s, Nonempty
      (LocalizedModule.Away r.val M ≃ₗ[Localization.Away r.val] Localization.Away r.val)) :
    Module.Invertible R M :=
  invertible_of_principalCover_rankOne s hs
    (fun r => Localization.Away r.val) (fun r => LocalizedModule.Away r.val M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.val) M) hframe

end PrincipalCover

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertible_of_principalCover_rankOne
end
end Source_ToricLocallyInvertible
-- END ORIGINAL PaperVerification.ToricLocallyInvertible


-- BEGIN ORIGINAL PaperVerification.ToricAffinePicard
section Source_ToricAffinePicard

-- original header: module

-- original header: public import PaperVerification.ToricInvertibleAffine
-- original header: public import PaperVerification.ToricLocallyInvertible
-- original header: public import PaperVerification.ToricLaurentPicard

-- original header: @[expose] public section

/-!
# Invertible sheaves on an affine scheme and triviality on the split torus

Actual local frames make the section module locally rank one. The literal
principal-open restriction maps are module localizations by quasi-coherence.
The local algebra criterion therefore makes the global section module
invertible, and the tilde equivalence transports a module trivialization
back to an actual sheaf trivialization. Applied to the Laurent coordinate
ring, this proves that every actual invertible sheaf on the split torus is
trivial, with no affine Picard correspondence assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- Principal opens subordinate to one of the actual local frames. -/
def framedPrincipalSet (hM : IsInvertibleModule M) : Set R :=
  {f | ∃ x : Spec R,PrimeSpectrum.basicOpen f≤ invertibleOpen hM x}

theorem framedPrincipalSet_span (hM : IsInvertibleModule M) :
    Ideal.span (framedPrincipalSet M hM)=⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply le_antisymm le_top
  intro x hx
  obtain ⟨f,hxf,hf⟩ := exists_basicOpen_frame M hM x
  exact Opens.mem_iSup.mpr ⟨f,Opens.mem_iSup.mpr ⟨⟨x,hf⟩,hxf⟩⟩

set_option maxHeartbeats 2000000 in
/-- The global section module of an actual invertible sheaf is invertible in
Mathlib's tensor-product sense. All finiteness is derived from local frames. -/
theorem invertibleModule_globalSections (hM : IsInvertibleModule M) :
    Module.Invertible R Γ(M,⊤) := by
  classical
  let G : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  change Module.Invertible R G
  let s := framedPrincipalSet M hM
  let U (f : s) : (Spec R).Opens := PrimeSpectrum.basicOpen f.val
  let A (f : s) : Type u := Γ(Spec R,U f)
  let N (f : s) : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op (U f))
  letI (f : s) : Algebra R (A f) := StructureSheaf.openAlgebra R (op (U f))
  letI (f : s) : IsLocalization.Away f.val (A f) :=
    StructureSheaf.IsLocalization.to_basicOpen R f.val
  letI (f : s) : Module (A f) (N f) := (M.val.obj (op (U f))).isModule
  letI (f : s) : IsScalarTower R (A f) (N f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ (f : s) : G →ₗ[R] N f :=
    ((modulesSpecToSheaf.obj M).obj.map
      (homOfLE (show U f ≤ (⊤ : (Spec R).Opens) from le_top)).op).hom
  letI (f : s) : IsLocalizedModule.Away f.val (ρ f) :=
    invertibleAffine_isLocalizing M hM f.val
  apply invertible_of_principalCover_rankOne s (framedPrincipalSet_span M hM)
    A (fun f => (N f : Type u)) ρ
  intro f
  obtain ⟨x,hx⟩ := f.property
  exact ⟨invertibleFrameCoordinates hM x (U f) hx⟩

/-- Triviality of the actual ring Picard group trivializes actual invertible
sheaves on its spectrum. This is derived through the affine equivalence. -/
def affineInvertibleSheafIso [Subsingleton (CommRing.Pic R)]
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit (Spec R).ringCatSheaf := by
  letI := invertibleModule_globalSections M hM
  let e : Γ(M,⊤) ≃ₗ[R] R :=
    Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)
  exact (invertibleAffineTildeIso M hM).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf

section Torus

variable (k : Type u) [Field k] (n : ℕ)

/-- Every actual invertible sheaf on the split torus is globally rank one. -/
def torusInvertibleSheafIso
    (M : (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).ringCatSheaf := by
  letI := ToricCharacters.torusPic_subsingleton k n
  exact affineInvertibleSheafIso M hM

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertibleModule_globalSections
#print axioms PaperVerification.ToricSchemes.torusInvertibleSheafIso
end
end Source_ToricAffinePicard
-- END ORIGINAL PaperVerification.ToricAffinePicard


-- BEGIN ORIGINAL PaperVerification.ToricCartierScaleCocycle
section Source_ToricCartierScaleCocycle

-- original header: module

-- original header: public import PaperVerification.ToricCartierDescent

-- original header: @[expose] public section

/-!
# Principal translations preserve intrinsic ampleness

The actual sheaf isomorphism multiplies rational values by the specified
factor. Its local regular coefficients are unchanged after the local
generators are multiplied by that same factor. Hence the actual
nonvanishing opens, including those of every positive tensor power, are
unchanged. This proves invariance of intrinsic ampleness under the principal
translation used to normalize a divisor on the torus.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X) (q : X.functionFieldˣ)

def scale : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := q*C.generator i
  transition i j x hi hj := by
    have he : ((q : X.functionField)*(C.generator i : X.functionField))/
        ((q : X.functionField)*(C.generator j : X.functionField)) =
        (C.generator i : X.functionField)/(C.generator j : X.functionField) := by
      field_simp [Units.ne_zero]
    simpa only [Units.val_mul,he] using C.transition i j x hi hj

theorem isSection_scale_iff (U : X.Opens) (s : Γ(rationalFunctions X,U)) :
    C.IsSection U s ↔ (C.scale q).IsSection U (rationalScaleEquiv q U s) := by
  have he (i : C.index) (x : U) :
      rationalValueAt X U x (rationalScaleEquiv q U s) /
        ((C.scale q).generator i : X.functionField) =
      rationalValueAt X U x s/(C.generator i : X.functionField) := by
    letI : Nonempty U := ⟨x⟩
    rw [rationalValueAt_eq,rationalScaleEquiv_value,rationalValueAt_eq]
    change ((q : X.functionField)*rationalValue X U s)/
      ((q : X.functionField)*(C.generator i : X.functionField)) = _
    field_simp [Units.ne_zero]
  constructor <;> intro h i x hx
  · exact (he (show C.index from i) x).symm ▸ h i x hx
  · exact he i x ▸ h i x hx

def scaleSectionEquiv (U : X.Opens) :
    Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ((C.scale q).sheaf,U) where
  toFun s := ⟨rationalScaleEquiv q U s.val,(C.isSection_scale_iff q U s.val).mp s.property⟩
  invFun s :=
    ⟨(rationalScaleEquiv q U).symm s.val,
      (C.isSection_scale_iff q U ((rationalScaleEquiv q U).symm s.val)).mpr
        (Eq.mpr (congrArg ((C.scale q).IsSection U)
          ((rationalScaleEquiv q U).apply_symm_apply s.val)) s.property)⟩
  left_inv s := Subtype.ext ((rationalScaleEquiv q U).symm_apply_apply s.val)
  right_inv s := Subtype.ext ((rationalScaleEquiv q U).apply_symm_apply s.val)
  map_add' s t := Subtype.ext ((rationalScaleEquiv q U).map_add s.val t.val)
  map_smul' a s := Subtype.ext ((rationalScaleEquiv q U).map_smul a s.val)

def scaleSheafIso : C.sheaf ≅ (C.scale q).sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U=>(C.scaleSectionEquiv q U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        apply Subtype.ext
        change rationalScaleEquiv q V.unop
            ((rationalFunctions X).presheaf.map f s.val) =
          (rationalFunctions X).presheaf.map f (rationalScaleEquiv q U.unop s.val)
        exact rationalScaleEquiv_restrict q f.unop s.val)

/-- The explicit generator scaling agrees with postcomposing the actual
fractional embedding by rational multiplication. -/
theorem scale_toCartierData_equivalent :
    (C.toCartierData.scale q).Equivalent (C.scale q).toCartierData := by
  refine ⟨C.scaleSheafIso q,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

@[simp] theorem scaleSheafIso_value (U : X.Opens) [Nonempty U]
    (s : Γ(C.sheaf,U)) :
    (C.scale q).toCartierData.sectionValue U ((C.scaleSheafIso q).hom.app U s) =
      (q : X.functionField)*C.toCartierData.sectionValue U s :=
  rationalScaleEquiv_value q U s.val

theorem scale_localCoefficient (i : C.index) (s : Γ(C.sheaf,⊤)) :
    (C.scale q).localCoefficient i ((C.scaleSheafIso q).hom.app ⊤ s) =
      C.localCoefficient i s := by
  classical
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    let j : (C.scale q).index := i
    letI : Nonempty ((C.scale q).openSet j) := hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.scale q).toCartierData.sectionValue ⊤
            ((C.scaleSheafIso q).hom.app ⊤ s) /
          ((C.scale q).generator j : X.functionField) :=
        (C.scale q).localCoefficient_value j _
      _ = C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField) := by
        rw [C.scaleSheafIso_value]
        change ((q : X.functionField)*C.toCartierData.sectionValue ⊤ s)/
          ((q : X.functionField)*(C.generator i : X.functionField)) = _
        field_simp [Units.ne_zero]
      _ = _ := (C.localCoefficient_value i s).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

theorem scale_nonvanishingOpen (s : Γ(C.sheaf,⊤)) :
    (C.scale q).nonvanishingOpen ((C.scaleSheafIso q).hom.app ⊤ s) =
      C.nonvanishingOpen s := by
  apply iSup_congr
  intro i
  exact congrArg (fun a : Γ(X,C.openSet i) => X.basicOpen a)
    (C.scale_localCoefficient q (show C.index from i) s)

theorem scale_nonvanishingOpen_inv (s : Γ((C.scale q).sheaf,⊤)) :
    C.nonvanishingOpen ((C.scaleSheafIso q).inv.app ⊤ s) =
      (C.scale q).nonvanishingOpen s := by
  have h := C.scale_nonvanishingOpen q ((C.scaleSheafIso q).inv.app ⊤ s)
  have he : (C.scaleSheafIso q).hom.app ⊤ ((C.scaleSheafIso q).inv.app ⊤ s)=s := by
    simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using
      congrArg (fun f=>f.app ⊤ s) (C.scaleSheafIso q).inv_hom_id
  rw [he] at h
  exact h.symm

@[simp] theorem pow_scale (n : ℕ) : (C.scale q).pow n = (C.pow n).scale (q^n) := by
  cases C
  simp [scale,pow,mul_pow]

theorem mul_scale (D : RationalCartierCocycle X) (r : X.functionFieldˣ) :
    (C.scale q).mul (D.scale r)=(C.mul D).scale (q*r) := by
  cases C
  cases D
  simp [scale,mul,mul_assoc,mul_left_comm,mul_comm]

/-- Principal translation preserves the standard, intrinsic notion of
ampleness, because it preserves all actual nonvanishing opens. -/
theorem isAmple_scale_iff : (C.scale q).IsAmple ↔ C.IsAmple := by
  have hpow (n : ℕ) (x : X) :
      (∃ s : Γ(((C.scale q).pow n).sheaf,⊤),
        x ∈ ((C.scale q).pow n).nonvanishingOpen s ∧
          IsAffineOpen (((C.scale q).pow n).nonvanishingOpen s)) =
      (∃ s : Γ(((C.pow n).scale (q^n)).sheaf,⊤),
        x ∈ ((C.pow n).scale (q^n)).nonvanishingOpen s ∧
          IsAffineOpen (((C.pow n).scale (q^n)).nonvanishingOpen s)) :=
    congrArg (fun B : RationalCartierCocycle X =>
      ∃ s : Γ(B.sheaf,⊤), x ∈ B.nonvanishingOpen s ∧ IsAffineOpen (B.nonvanishingOpen s))
        (C.pow_scale q n)
  constructor
  · rintro ⟨hcompact,hcover⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨n,hn,s,hx,ha⟩ := hcover x
    obtain ⟨t,ht,hAt⟩ := Eq.mp (hpow n x) ⟨s,hx,ha⟩
    refine ⟨n,hn,((C.pow n).scaleSheafIso (q^n)).inv.app ⊤ t,?_,?_⟩
    · simpa only [(C.pow n).scale_nonvanishingOpen_inv (q^n) t] using ht
    · simpa only [(C.pow n).scale_nonvanishingOpen_inv (q^n) t] using hAt
  · rintro ⟨hcompact,hcover⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨n,hn,s,hx,ha⟩ := hcover x
    refine ⟨n,hn,Eq.mpr (hpow n x) ?_⟩
    refine ⟨((C.pow n).scaleSheafIso (q^n)).hom.app ⊤ s,?_,?_⟩
    · simpa only [(C.pow n).scale_nonvanishingOpen (q^n) s] using hx
    · simpa only [(C.pow n).scale_nonvanishingOpen (q^n) s] using ha

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X) (q : X.functionFieldˣ)

theorem scale_localCocycle :
    (D.scale q).localCocycle=D.localCocycle.scale q := by
  unfold localCocycle RationalCartierCocycle.scale
  congr 1
  funext x
  apply Units.ext
  letI : Nonempty (invertibleOpen D.locallyFree x) :=
    ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
  exact D.scale_frameRationalGenerator q (invertibleFrame D.locallyFree x)

theorem isAmple_scale_iff : (D.scale q).IsAmple ↔ D.IsAmple := by
  change (D.scale q).localCocycle.IsAmple ↔ D.localCocycle.IsAmple
  rw [D.scale_localCocycle]
  exact D.localCocycle.isAmple_scale_iff q

theorem scale_add_equivalent (E : CartierData X) (r : X.functionFieldˣ) :
    ((D.scale q).add (E.scale r)).Equivalent ((D.add E).scale (q*r)) := by
  have h := (D.localCocycle.mul E.localCocycle).scale_toCartierData_equivalent (q*r)
  have heq : (D.scale q).add (E.scale r) =
      ((D.localCocycle.mul E.localCocycle).scale (q*r)).toCartierData := by
    unfold add
    rw [D.scale_localCocycle,E.scale_localCocycle,
      D.localCocycle.mul_scale q E.localCocycle r]
  rw [heq]
  exact CartierData.equivalent_symm _ _ h

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.scale_nonvanishingOpen
#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_scale_iff
end
end Source_ToricCartierScaleCocycle
-- END ORIGINAL PaperVerification.ToricCartierScaleCocycle


-- BEGIN ORIGINAL PaperVerification.ToricCharacterSubrepresentations
section Source_ToricCharacterSubrepresentations

-- original header: module

-- original header: public import PaperVerification.ToricCharacterMultiplication
-- original header: public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
-- original header: public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- original header: public import Mathlib.Algebra.Module.Submodule.Equiv

-- original header: @[expose] public section

/-!
# Character bases of algebraic torus subrepresentations

Stability here is under the actual coalgebra comultiplication, with values
in the tensor product containing the submodule. It is not stability under
the action of rational points. Thus the argument works over finite fields
as well. Taking one coefficient in the first tensor factor isolates one
character in the second; this proves the character basis assertion.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct

variable (k : Type*) [Field k]
variable {M : Type*} [AddCommGroup M]

/-- Extract the coefficient of one character from the first tensor
factor, retaining the actual second module. -/
def characterCoefficient {V : Type*} [AddCommGroup V] [Module k V] (m : M) :
    AddMonoidAlgebra k M ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (((AddMonoidAlgebra.basis M k).coord m).rTensor V)

@[simp] theorem characterCoefficient_tmul {V : Type*}
    [AddCommGroup V] [Module k V]
    (m : M) (f : AddMonoidAlgebra k M) (v : V) :
    characterCoefficient k m (f ⊗ₜ[k] v) = f.coeff m • v := by
  simp only [characterCoefficient, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rfl

/-- Comultiplication followed by one coefficient projection is exactly
the corresponding individual character term. -/
theorem characterCoefficient_comul (m : M) (f : AddMonoidAlgebra k M) :
    characterCoefficient k m (Coalgebra.comul (R := k) f) = single m (f.coeff m) := by
  have h : (characterCoefficient k m).comp
        (Coalgebra.comul (R := k) (A := AddMonoidAlgebra k M)) =
      (AddMonoidAlgebra.lsingle (R := k) m).comp
        ((AddMonoidAlgebra.basis M k).coord m) := by
    apply (AddMonoidAlgebra.basis M k).ext
    intro i
    change characterCoefficient k m
        (Coalgebra.comul (R := k) (AddMonoidAlgebra.single i (1 : k))) =
      AddMonoidAlgebra.single m ((AddMonoidAlgebra.single i (1 : k)).coeff m)
    by_cases hi : i = m
    · subst i
      simp [AddMonoidAlgebra.comul_single]
    · simp [AddMonoidAlgebra.comul_single, hi, Ne.symm hi]
  exact congrArg (fun g => g f) h

/-- Algebraic stability of a Laurent-polynomial submodule under the
split torus: the genuine coaction factors through `k[M] ⊗ S`. -/
def IsCharacterStable (S : Submodule k (AddMonoidAlgebra k M)) : Prop :=
  ∀ f ∈ S, Coalgebra.comul (R := k) f ∈ LinearMap.range
    (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
      S.subtype)

theorem characterCoefficient_map_subtype
    (S : Submodule k (AddMonoidAlgebra k M)) (m : M)
    (z : AddMonoidAlgebra k M ⊗[k] S) :
    characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        S.subtype z) ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply, characterCoefficient_tmul] using
        S.smul_mem (f.coeff m) g.property
  | add z w hz hw => simpa only [map_add] using S.add_mem hz hw

/-- Algebraic coaction stability is equivalent to closure under the
literal Laurent character components. The reverse implication builds
the required tensor preimage from the finite support of the element. -/
theorem isCharacterStable_iff_components
    (S : Submodule k (AddMonoidAlgebra k M)) :
    IsCharacterStable k S ↔
      ∀ f∈S,∀ m : M,single m (f.coeff m)∈S := by
  constructor
  · intro hS f hf m
    obtain ⟨z,hz⟩ := hS f hf
    have h := characterCoefficient_map_subtype k S m z
    rw [hz,characterCoefficient_comul] at h
    exact h
  · intro hS f hf
    classical
    let z : AddMonoidAlgebra k M ⊗[k] S :=
      ∑ m∈f.coeff.support,
        (single m 1) ⊗ₜ[k] (⟨single m (f.coeff m),hS f hf m⟩ : S)
    refine ⟨z,?_⟩
    have hsum : (∑ m∈f.coeff.support,single m (f.coeff m))=f :=
      AddMonoidAlgebra.sum_coeff_single f
    conv_rhs => rw [← hsum]
    simp only [z,map_sum,TensorProduct.map_tmul,LinearMap.id_apply,
      Submodule.subtype_apply,AddMonoidAlgebra.comul_single,
      CommSemiring.comul_apply,AddMonoidAlgebra.lsingle_apply]

/-- Each nonzero coefficient of a stable element supplies its entire
one-dimensional character line in the same submodule. -/
theorem single_mem_of_stable (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) (f : AddMonoidAlgebra k M) (hf : f ∈ S)
    (m : M) (hm : f.coeff m ≠ 0) : single m (1 : k) ∈ S := by
  obtain ⟨z, hz⟩ := hS f hf
  have hterm := characterCoefficient_map_subtype k S m z
  rw [hz, characterCoefficient_comul] at hterm
  have hmul := S.smul_mem (f.coeff m)⁻¹ hterm
  simpa only [smul_single, smul_eq_mul, inv_mul_cancel₀ hm] using hmul

/-- The exponent set of the characters actually contained in the
submodule, without a chosen spanning family or a weight decomposition. -/
def characterExponents (S : Submodule k (AddMonoidAlgebra k M)) : Set M :=
  {m | single m (1 : k) ∈ S}

/-- A subrepresentation of the regular representation of a split torus
has precisely its contained characters as a basis. This equality first
states the spanning assertion at the level of actual submodules. -/
theorem stable_eq_characterModule (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    S = characterModule k (characterExponents k S) := by
  apply le_antisymm
  · intro f hf
    rw [mem_characterModule_iff]
    intro m hm
    exact single_mem_of_stable k S hS f hf m
      (Finsupp.mem_support_iff.mp hm)
  · rw [characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact hm

/-- The actual coordinate equivalence of a stable module with finitely
supported functions on its character exponents. -/
def stableCharacterCoordinates (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) : S ≃ₗ[k] characterExponents k S →₀ k :=
  (LinearEquiv.ofEq S (characterModule k (characterExponents k S))
    (stable_eq_characterModule k S hS)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        (characterExponents k S))

def stableCharacterBasis (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    Module.Basis (characterExponents k S) k S where
  repr := stableCharacterCoordinates k S hS

/-- Finite-dimensionality supplies a finite exponent set, with no
assumption on the cardinality or characteristic of the ground field. -/
theorem finite_characterExponents
    (S : Submodule k (AddMonoidAlgebra k M)) [FiniteDimensional k S]
    (hS : IsCharacterStable k S) : (characterExponents k S).Finite := by
  letI := FiniteDimensional.fintypeBasisIndex (stableCharacterBasis k S hS)
  exact Set.toFinite _

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.stable_eq_characterModule
#print axioms PaperVerification.ToricCharacters.finite_characterExponents
end
end Source_ToricCharacterSubrepresentations
-- END ORIGINAL PaperVerification.ToricCharacterSubrepresentations


-- BEGIN ORIGINAL PaperVerification.ToricTorusAction
section Source_ToricTorusAction

-- original header: module

-- original header: public import Mathlib.AlgebraicGeometry.Group.Affine
-- original header: public import Mathlib.CategoryTheory.Monoidal.Mod
-- original header: public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
-- original header: public import Mathlib.Algebra.Group.Units.Hom
-- original header: public import Mathlib.Data.Int.Cast.Lemmas
-- original header: public import PaperVerification.ToricCharacterSubrepresentations

-- original header: @[expose] public section

/-!
# The actual split torus and its action on semigroup charts

The torus is the spectrum of the genuine group Hopf algebra. A semigroup
chart is already a monoid scheme. Restriction of its regular monoid action
along the actual torus-to-chart morphism supplies the group action, with
unit and associativity proved in the category of schemes over the field.
Its actual comorphism is the character coaction, over arbitrary fields.
-/

noncomputable section

universe u v w

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open scoped TensorProduct

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The actual spectrum of the group algebra, with its canonical Hopf
algebra group structure. For a rank-n free group this is the split n-torus. -/
def splitTorus : Scheme.{max u v} := Spec (CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_isOver : (splitTorus k M).Over (Spec (CommRingCat.of k)) := by
  dsimp only [splitTorus]
  infer_instance

abbrev splitTorusOver : Over (Spec (CommRingCat.of k)) :=
  (splitTorus k M).asOver (Spec (CommRingCat.of k))

instance splitTorus_monObj : MonObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.instMonObjSpecAsOverSpec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_grpObj : GrpObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.instGrpObjSpecAsOverSpec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_commGrpObj : CommGrpObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  infer_instance

/-- The bundled actual group scheme, not an action of rational points. -/
def splitTorusGroup : Grp (Over (Spec (CommRingCat.of k))) :=
  Grp.mk (splitTorusOver k M)

instance splitTorusGroup_isCommMonObj : IsCommMonObj (splitTorusGroup.{u, v} k M).X := by
  change IsCommMonObj (splitTorusOver k M)
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.isCommMonObj_spec_asOver_spec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

/-- Algebra maps from the torus coordinate ring are exactly characters
of the lattice valued in units of the test algebra. This statement is
valid for every test algebra, including nonreduced algebras. -/
def torusCharacterPointsEquiv (A : Type (max u v)) [CommRing A] [Algebra k A] :
    (AddMonoidAlgebra k M →ₐ[k] A) ≃ (Multiplicative M →* Aˣ) :=
  (AddMonoidAlgebra.lift k A M).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

@[simp] theorem torusCharacterPointsEquiv_apply (A : Type (max u v))
    [CommRing A] [Algebra k A] (f : AddMonoidAlgebra k M →ₐ[k] A) (m : M) :
    ((torusCharacterPointsEquiv k M A f (Multiplicative.ofAdd m) : Aˣ) : A) =
      f (AddMonoidAlgebra.single m 1) := rfl

variable {M} (S : AddSubmonoid M)

/-- The actual affine semigroup chart. -/
def semigroupChart : Scheme.{max u v} :=
  Spec (CommRingCat.of (AddMonoidAlgebra k S))

instance semigroupChart_isOver : (semigroupChart k S).Over (Spec (CommRingCat.of k)) := by
  dsimp only [semigroupChart]
  infer_instance

abbrev semigroupChartOver : Over (Spec (CommRingCat.of k)) :=
  (semigroupChart k S).asOver (Spec (CommRingCat.of k))

instance semigroupChart_monObj : MonObj (semigroupChartOver k S) := by
  dsimp only [semigroupChartOver, semigroupChart]
  infer_instance

/-- The actual morphism induced by inclusion of exponents S→M. Openness
and dominance require the appropriate saturated generating semigroup and
are proved separately from this group-action construction. -/
def torusToSemigroupChart : splitTorus k M ⟶ semigroupChart k S :=
  Spec.map (CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom.toRingHom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance torusToSemigroupChart_isOver :
    (torusToSemigroupChart k S).IsOver (Spec (CommRingCat.of k)) := by
  dsimp only [torusToSemigroupChart, splitTorus, semigroupChart]
  infer_instance

abbrev torusToSemigroupChartOver :
    splitTorusOver k M ⟶ semigroupChartOver k S :=
  (torusToSemigroupChart k S).asOver (Spec (CommRingCat.of k))

instance torusToSemigroupChart_isMonHom :
    IsMonHom (torusToSemigroupChartOver k S) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k S.subtype)).op).hom)
  infer_instance

/-- The genuine torus action, obtained by restriction of the regular
monoid-scheme action. -/
instance semigroupChart_torusAction :
    ModObj (splitTorusOver k M) (semigroupChartOver k S) := by
  letI : ModObj (semigroupChartOver k S) (semigroupChartOver k S) :=
    ModObj.regular (semigroupChartOver k S)
  exact Mod.scalarRestriction (torusToSemigroupChartOver k S) (semigroupChartOver k S)

/-- This action really extends multiplication on the embedded torus. -/
theorem semigroupChart_action_extends_torus :
    (𝟙 (splitTorusOver k M) ⊗ₘ torusToSemigroupChartOver k S) ≫
      γ[splitTorusOver k M, semigroupChartOver k S] =
      μ[splitTorusOver k M] ≫ torusToSemigroupChartOver k S := by
  change ((splitTorusOver k M) ◁ torusToSemigroupChartOver k S) ≫
      (torusToSemigroupChartOver k S ▷ semigroupChartOver k S) ≫
        μ[semigroupChartOver k S] = _
  rw [← Category.assoc, ← tensorHom_def']
  exact (IsMonHom.mul_hom (f := torusToSemigroupChartOver k S)).symm

/-- The coaction on the actual coordinate algebra. -/
def semigroupChartCoaction : AddMonoidAlgebra k S →ₐ[k]
    AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k S :=
  (Algebra.TensorProduct.map
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom
    (AlgHom.id k (AddMonoidAlgebra k S))).comp
      (Bialgebra.comulAlgHom k (AddMonoidAlgebra k S))

@[simp] theorem semigroupChartCoaction_single (s : S) (c : k) :
    semigroupChartCoaction k S (AddMonoidAlgebra.single s c) =
      AddMonoidAlgebra.single (s : M) 1 ⊗ₜ[k] AddMonoidAlgebra.single s c := by
  simp only [semigroupChartCoaction, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, BialgHom.coe_toAlgHom,
    AddMonoidAlgebra.mapDomainBialgHom_single]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The action's actual scheme comorphism is exactly the displayed
character coaction. The tensor-to-fiber-product isomorphism is Mathlib's
proved affine-scheme tensor-product identification. -/
theorem semigroupChart_action_spec :
    (γ[splitTorusOver k M, semigroupChartOver k S]).left =
      (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (AddMonoidAlgebra k M))
        (CommRingCat.of (AddMonoidAlgebra k S))).hom ≫
      Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom) := by
  let F := algSpec (CommRingCat.of k)
  letI : F.LaxMonoidal :=
    (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal
  let T : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k M))
  let C : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k S))
  let i : T ⟶ C := (CommAlgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom).op
  have hnatural := Functor.LaxMonoidal.μ_natural_left F i C
  have haction : γ[splitTorusOver k M, semigroupChartOver k S] =
      Functor.LaxMonoidal.μ F T C ≫ F.map ((i ▷ C) ≫ μ[C]) := by
    change (F.map i ▷ F.obj C) ≫
      (Functor.LaxMonoidal.μ F C C ≫ F.map μ[C]) = _
    rw [← Category.assoc, hnatural, Category.assoc, ← F.map_comp]
  rw [haction]
  rfl

/-- The chart inclusion is equivariant at the genuine coaction level. -/
theorem semigroupChartCoaction_inclusion (f : AddMonoidAlgebra k S) :
    Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M))
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom
      (semigroupChartCoaction k S f) =
    Coalgebra.comul (R := k)
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single s c =>
      simp only [semigroupChartCoaction_single, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, BialgHom.coe_toAlgHom, AddMonoidAlgebra.mapDomainBialgHom_single,
        AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]
      rfl

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open WithConv

section GroupHom

variable (k : Type (max u v w)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The fully faithful affine Hopf correspondence identifies actual
group-scheme morphisms of split tori with their actual bialgebra
comorphisms. In particular, this is not a test on rational points. -/
def torusBialgHomGroupHomEquiv (N : Type w) [AddCommGroup N] :
    (AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) ≃
      (splitTorusGroup.{max u v w, v} k M ⟶
        splitTorusGroup.{max u v w, w} k N) := by
  let e : (AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) ≃
      (op (CommHopfAlgCat.of k (AddMonoidAlgebra k M)) ⟶
        op (CommHopfAlgCat.of k (AddMonoidAlgebra k N))) :=
    { toFun := fun f => (CommHopfAlgCat.ofHom f).op
      invFun := fun f => f.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun f => Quiver.Hom.unop_inj (CommHopfAlgCat.ofHom_hom f.unop) }
  exact e.trans (hopfSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv

@[simp] theorem torusBialgHomGroupHomEquiv_hom (N : Type w) [AddCommGroup N]
    (f : AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) :
    (torusBialgHomGroupHomEquiv.{u, v, w} k M N f).hom.hom =
      (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
        (Spec (CommRingCat.of k)) := rfl

end GroupHom

section Characters

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The target `Spec k[ℤ]` is the ordinary multiplicative group scheme:
its actual scheme-valued points over every test algebra are the units
of that algebra. Nonreduced test algebras are included. -/
def multiplicativeGroupSchemePointsEquiv (A : Type (max u v))
    [CommRing A] [Algebra k A] :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) ⟶
      splitTorusOver k ℤ) ≃ Aˣ :=
  Spec.mapMulEquiv.toEquiv.symm.trans <|
    (WithConv.equiv _).trans <|
      (torusCharacterPointsEquiv k ℤ A).trans (zpowersHom Aˣ).symm

variable [IsDomain k]

/-- The lattice is exactly the group of genuine scheme characters
`T_M → G_m`. Mathlib's group-like-element classification and fully
faithful `hopfSpec` prove exhaustion, over every domain. -/
def torusCharacterEquiv :
    M ≃ (splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :=
  (zmultiplesHom M).trans <|
    (AddMonoidAlgebra.mapDomainBialgHomEquiv (R := k)).trans
      (torusBialgHomGroupHomEquiv.{u, v, 0} k M ℤ)

@[simp] theorem torusCharacterEquiv_hom (m : M) :
    (torusCharacterEquiv k M m).hom.hom =
      (Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m)).toAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of k)) := rfl

/-- The comorphism of the character indexed by `m` literally sends
the Laurent monomial `t^z` to the lattice monomial `χ^(z • m)`. -/
@[simp] theorem torusCharacter_comorphism_single (m : M) (z : ℤ) (c : k) :
    (AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m))
      (AddMonoidAlgebra.single z c) = AddMonoidAlgebra.single (z • m) c := by
  simp only [AddMonoidAlgebra.mapDomainBialgHom_single, zmultiplesHom_apply]

set_option synthInstance.maxHeartbeats 200000 in
/-- Addition in the lattice is the ordinary product of actual
group-scheme characters. -/
theorem torusCharacterEquiv_add (m m' : M) :
    torusCharacterEquiv k M (m + m') =
      torusCharacterEquiv k M m * torusCharacterEquiv k M m' := by
  let f := AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m)
  let g := AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m')
  have hsum : AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M (m + m')) =
      (toConv f * toConv g).ofConv := by
    rw [show zmultiplesHom M (m + m') =
      zmultiplesHom M m + zmultiplesHom M m' from (zmultiplesAddHom M).map_add m m']
    exact AddMonoidAlgebra.mapDomainBialgHom_add _ _
  have hconv := congrArg (fun φ : AddMonoidAlgebra k ℤ →ₐc[k] AddMonoidAlgebra k M =>
    toConv φ.toAlgHom) hsum
  rw [BialgHom.toAlgHom_convMul] at hconv
  apply Grp.hom_ext
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul, torusCharacterEquiv_hom]
  change Spec.mapMulEquiv
      (toConv (AddMonoidAlgebra.mapDomainBialgHom k
        (zmultiplesHom M (m + m'))).toAlgHom) =
    Spec.mapMulEquiv (toConv f.toAlgHom) * Spec.mapMulEquiv (toConv g.toAlgHom)
  rw [hconv, map_mul]

def additiveEquivOfMultiplicativeLaw
    {A B : Type*} [Add A] [Mul B] (e : A ≃ B)
    (h : ∀ x y, e (x + y) = e x * e y) : A ≃+ Additive B where
  toEquiv := e.trans Additive.ofMul
  map_add' x y := congrArg Additive.ofMul (h x y)

set_option synthInstance.maxHeartbeats 200000 in
/-- The character lattice equivalence also preserves the full abelian
group structure, rather than only enumerating its underlying set. -/
def torusCharacterAddEquiv :
    M ≃+ Additive
      (splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :=
  additiveEquivOfMultiplicativeLaw (torusCharacterEquiv.{u, v} k M)
    (torusCharacterEquiv_add.{u, v} k M)

theorem torusCharacter_existsUnique
    (f : splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :
    ∃! m : M, torusCharacterEquiv k M m = f := by
  let e := torusCharacterEquiv k M
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro m hm
  exact e.injective (hm.trans (e.apply_symm_apply f).symm)

end Characters

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusCharacterAddEquiv
#print axioms PaperVerification.ToricSchemes.torusCharacter_existsUnique
end
end Source_ToricTorusAction
-- END ORIGINAL PaperVerification.ToricTorusAction


-- BEGIN ORIGINAL PaperVerification.ToricDenseTorusFunctionField
section Source_ToricDenseTorusFunctionField

-- original header: module

-- original header: public import PaperVerification.ToricFunctionFieldBridge
-- original header: public import PaperVerification.ToricTorusAction
-- original header: public import PaperVerification.ToricLaurentPicard

-- original header: @[expose] public section

/-!
# The function field of a scheme containing the actual split torus

The coordinate ring is the ordinary group algebra of the integral
character lattice. Its domain property is proved from the iterated
Laurent presentation, so no additional domain hypothesis is attached to
the torus statement.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n → ℤ) ⟶ X) [hj : IsOpenImmersion j]

/-- Restriction along the actual open torus identifies rational
functions with the fraction field of its character algebra. -/
def torusOpenFunctionFieldEquiv :
    X.functionField ≃+* FractionRing (torusCoordinateRing k n) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv
    (CommRingCat.of (torusCoordinateRing k n)) j

/-- On global regular functions this is the literal restriction to the
torus, followed by the canonical fraction-field embedding. -/
@[simp] theorem torusOpenFunctionFieldEquiv_germ_top (a : Γ(X,⊤)) :
    torusOpenFunctionFieldEquiv k n X j (X.germToFunctionField ⊤ a) =
      algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
          (j.appTop a)) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv_germ_top
    (CommRingCat.of (torusCoordinateRing k n)) j a

/-- Equality of rational functions can be checked on the actual open
torus. This is injectivity of a constructed equivalence, not a hypothesis. -/
theorem rationalFunction_eq_iff_on_torus (f g : X.functionField) :
    f=g ↔ torusOpenFunctionFieldEquiv k n X j f =
      torusOpenFunctionFieldEquiv k n X j g :=
  (torusOpenFunctionFieldEquiv k n X j).injective.eq_iff.symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusOpenFunctionFieldEquiv
end
end Source_ToricDenseTorusFunctionField
-- END ORIGINAL PaperVerification.ToricDenseTorusFunctionField


-- BEGIN ORIGINAL PaperVerification.ToricInvertibleRestriction
section Source_ToricInvertibleRestriction

-- original header: module

-- original header: public import PaperVerification.ToricInvertibleAffine
-- original header: public import PaperVerification.ToricFunctionFieldBridge

-- original header: @[expose] public section

/-!
# Restriction of actual rank-one sheaves

An open immersion transports actual local frames through its actual
isomorphisms on sections. The proof constructs the linear maps on every
smaller open and checks their restriction compatibility.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : IsInvertibleModule M)

theorem invertibleFrameCoordinates_restrict (x : X)
    {U V : X.Opens} (i : V ⟶ U)
    (hU : U≤ invertibleOpen hM x) (hV : V≤ invertibleOpen hM x)
    (s : Γ(M,U)) :
    invertibleFrameCoordinates hM x V hV (M.presheaf.map i.op s) =
      X.presheaf.map i.op (invertibleFrameCoordinates hM x U hU s) := by
  let f : Over.mk (homOfLE hV) ⟶ Over.mk (homOfLE hU) :=
    Over.homMk i (by subsingleton)
  exact PresheafOfModules.naturality_apply (invertibleFrame hM x).hom.val f.op s

/-- Local frame coordinates transported along the actual section
isomorphism of an open immersion. -/
def restrictFrameCoordinates (x : X) (U : Y.Opens)
    (hU : j ''ᵁ U≤ invertibleOpen hM x) :
    Γ(M.restrict j,U) ≃ₗ[Γ(Y,U)] Γ(Y,U) := by
  let eM := (M.restrictAppIso j U).addCommGroupIsoToAddEquiv
  let eX := invertibleFrameCoordinates hM x (j ''ᵁ U) hU
  let eR := (j.appIso U).commRingCatIsoToRingEquiv
  refine
    { toFun := fun s=>eR (eX (eM s))
      invFun := fun a=>eM.symm (eX.symm (eR.symm a))
      left_inv := by intro s; simp
      right_inv := by intro a; simp
      map_add' := by intro s t; simp
      map_smul' := ?_ }
  intro a s
  change eR (eX (eR.symm a • eM s)) = a * eR (eX (eM s))
  rw [eX.map_smul]
  change eR (eR.symm a * eX (eM s)) = _
  rw [map_mul,RingEquiv.apply_symm_apply]

theorem restrictFrameCoordinates_restrict (x : X)
    {U V : Y.Opens} (i : V ⟶ U)
    (hU : j ''ᵁ U≤ invertibleOpen hM x)
    (hV : j ''ᵁ V≤ invertibleOpen hM x) (s : Γ(M.restrict j,U)) :
    restrictFrameCoordinates j hM x V hV ((M.restrict j).presheaf.map i.op s) =
      Y.presheaf.map i.op (restrictFrameCoordinates j hM x U hU s) := by
  let i' : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_mono i.le)
  let t : Γ(M,j ''ᵁ U) := (M.restrictAppIso j U).hom s
  change (j.appIso V).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ V) hV (M.presheaf.map i'.op t)) =
    Y.presheaf.map i.op ((j.appIso U).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t))
  have hn : X.presheaf.map i'.op ≫ (j.appIso V).hom =
      (j.appIso U).hom ≫ Y.presheaf.map i.op := by
    simp [Scheme.Hom.appIso_hom']
  calc
    _ = (j.appIso V).hom (X.presheaf.map i'.op
        (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) :=
      congrArg (fun a : Γ(X,j ''ᵁ V) => (j.appIso V).hom a)
        (invertibleFrameCoordinates_restrict hM x i' hU hV t)
    _ = _ := congrArg (fun f : Γ(X,j ''ᵁ U) ⟶ Γ(Y,V) =>
      f (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) hn

include hM in
/-- Restriction along an actual open immersion preserves local rank one. -/
theorem isInvertibleModule_restrict : IsInvertibleModule (M.restrict j) := by
  intro y
  let U : Y.Opens := j ⁻¹ᵁ invertibleOpen hM (j y)
  have hy : y∈U := mem_invertibleOpen hM (j y)
  refine ⟨U,hy,⟨?_⟩⟩
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V=>?_) ?_
  · have hV : j ''ᵁ V.unop.left≤ invertibleOpen hM (j y) := by
      rintro z ⟨v,hv,rfl⟩
      exact V.unop.hom.le hv
    exact (restrictFrameCoordinates j hM (j y) V.unop.left hV).toModuleIso
  · intro V W f
    ext s
    exact restrictFrameCoordinates_restrict j hM (j y) f.unop.left _ _ s

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_restrict
end
end Source_ToricInvertibleRestriction
-- END ORIGINAL PaperVerification.ToricInvertibleRestriction


-- BEGIN ORIGINAL PaperVerification.ToricTorusCartierRepresentative
section Source_ToricTorusCartierRepresentative

-- original header: module

-- original header: public import PaperVerification.ToricAffinePicard
-- original header: public import PaperVerification.ToricCartierTranslate
-- original header: public import PaperVerification.ToricCartierScaleCocycle
-- original header: public import PaperVerification.ToricInvertibleRestriction
-- original header: public import PaperVerification.ToricDenseTorusFunctionField

-- original header: @[expose] public section

/-!
# A linearly equivalent Cartier representative trivial on the dense torus

The actual torus Picard trivialization supplies a nonzero rational generator.
Multiplying the fractional embedding by its inverse gives a linearly
equivalent Cartier divisor. On every open of the torus, the new actual
fractional module is precisely the actual regular-function module. The
explicit rational factor is retained; equality of divisors is not confused
with linear equivalence.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j]

namespace CartierData

variable (D : CartierData X)

/-- The actual rational value of a section on a nonempty open chart. -/
def alongSectionValue (V : Y.Opens) [Nonempty V] :
    Γ(D.sheaf.restrict j,V) →+ X.functionField := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue (j ''ᵁ V)).toAddMonoidHom.comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.toAddMonoidHom

theorem alongSectionValue_injective (V : Y.Opens) [Nonempty V] :
    Function.Injective (D.alongSectionValue j V) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue_injective (j ''ᵁ V)).comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.injective

theorem alongSectionValue_smul (V : Y.Opens) [Nonempty V]
    (a : Γ(Y,V)) (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V (a • s) =
      openImmersionRegularToFunctionField j V a * D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  change D.sectionValue (j ''ᵁ V)
      ((j.appIso V).inv a • (D.sheaf.restrictAppIso j V).hom s) = _
  rw [D.sectionValue_smul,openImmersionRegularToFunctionField_eq_germ_image]
  rfl

theorem alongSectionValue_restrict {U V : Y.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (s : Γ(D.sheaf.restrict j,U)) :
    D.alongSectionValue j V ((D.sheaf.restrict j).presheaf.map i.op s) =
      D.alongSectionValue j U s := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.sectionValue_restrict (homOfLE (j.image_mono i.le)) s

/-- Evaluation of an actual global trivialization on any open of the chart. -/
def chartFrameCoordinates
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens) :
    Γ(D.sheaf.restrict j,V) ≃ₗ[Γ(Y,V)] Γ(Y,V) :=
  ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (op V)).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

/-- The nonzero rational generator supplied by an actual chart trivialization. -/
def chartFrameRationalGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) : X.functionField :=
  D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤)))

theorem chartFrameRationalGenerator_ne_zero
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    D.chartFrameRationalGenerator j e ≠ 0 := by
  intro hzero
  have hz : e.inv.app ⊤ (1 : Γ(Y,⊤))=0 :=
    D.alongSectionValue_injective j ⊤ (hzero.trans (map_zero _).symm)
  have h1 : (1 : Γ(Y,⊤))=0 := by
    let L := D.chartFrameCoordinates j e ⊤
    calc
      (1 : Γ(Y,⊤)) = L (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
        (L.apply_symm_apply (1 : Γ(Y,⊤))).symm
      _ = L 0 := congrArg L hz
      _ = 0 := map_zero L
  apply (one_ne_zero : (1 : Y.functionField) ≠ 0)
  calc
    (1 : Y.functionField) = Y.germToFunctionField ⊤ (1 : Γ(Y,⊤)) :=
      (map_one (Y.germToFunctionField ⊤).hom).symm
    _ = Y.germToFunctionField ⊤ (0 : Γ(Y,⊤)) := congrArg (Y.germToFunctionField ⊤) h1
    _ = 0 := map_zero (Y.germToFunctionField ⊤).hom

theorem alongSectionValue_frameGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] :
    D.alongSectionValue j V (e.inv.app V (1 : Γ(Y,V)))=D.chartFrameRationalGenerator j e := by
  have hg : e.inv.app V (1 : Γ(Y,V)) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op (e.inv.app ⊤ (1 : Γ(Y,⊤))) := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op
      (1 : Γ(Y,⊤))
    change e.inv.app V
        ((Y.presheaf.map (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op).hom
          (1 : Γ(Y,⊤))) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
        (e.inv.app ⊤ (1 : Γ(Y,⊤))) at hn
    simpa only [map_one] using hn
  calc
    _ = D.alongSectionValue j V
        ((D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
          (e.inv.app ⊤ (1 : Γ(Y,⊤)))) := congrArg (D.alongSectionValue j V) hg
    _ = D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
      D.alongSectionValue_restrict j (homOfLE (show V≤(⊤ : Y.Opens) from le_top)) _
    _ = _ := rfl

/-- The actual chart coordinate describes the rational value of every
section, not only the distinguished generator. -/
theorem alongSectionValue_frame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V s =
      openImmersionRegularToFunctionField j V (e.hom.app V s) *
        D.chartFrameRationalGenerator j e := by
  let a : Γ(Y,V) := e.hom.app V s
  let t : Γ(D.sheaf.restrict j,V) := e.inv.app V (1 : Γ(Y,V))
  have hs : s=a • t := by
    apply (D.chartFrameCoordinates j e V).injective
    change D.chartFrameCoordinates j e V s =
      D.chartFrameCoordinates j e V
        (D.chartFrameCoordinates j e V s • (D.chartFrameCoordinates j e V).symm 1)
    simp
  calc
    _ = D.alongSectionValue j V (a • t) := congrArg (D.alongSectionValue j V) hs
    _ = openImmersionRegularToFunctionField j V a * D.alongSectionValue j V t :=
      D.alongSectionValue_smul j V a t
    _ = _ := congrArg (fun z : X.functionField => openImmersionRegularToFunctionField j V a * z)
      (D.alongSectionValue_frameGenerator j e V)

theorem scale_alongSectionValue (q : X.functionFieldˣ)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    (D.scale q).alongSectionValue j V s =
      (q : X.functionField)*D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.scale_sectionValue q (j ''ᵁ V) s

end CartierData

section Torus

open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    (D : CartierData X)

local instance torusScheme_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- The actual Picard trivialization of the restriction to the split torus. -/
def torusCartierFrame :
    D.sheaf.restrict j ≅ SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf := by
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact torusInvertibleSheafIso k n (D.sheaf.restrict j)
    (isInvertibleModule_restrict j D.locallyFree)

/-- The explicit ambient rational generator supplied by this trivialization. -/
def torusCartierGenerator : X.functionFieldˣ := by
  letI := torusCoordinateRing_isDomain k n
  exact Units.mk0 (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))
    (D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D))

/-- A linearly equivalent representative, normalized to O_T on the actual
dense open torus. The rational translation factor remains explicit. -/
def torusNormalizedCartier : CartierData X :=
  D.scale (torusCartierGenerator k n X j D)⁻¹

theorem torusNormalizedCartier_linearlyEquivalent :
    (torusNormalizedCartier k n X j D).LinearlyEquivalent D :=
  D.scale_linearlyEquivalent _

theorem torusNormalizedCartier_isAmple_iff :
    (torusNormalizedCartier k n X j D).IsAmple ↔ D.IsAmple :=
  D.isAmple_scale_iff _

def torusNormalizedCartierSheafIso :
    (torusNormalizedCartier k n X j D).sheaf.restrict j ≅
      SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf :=
  torusCartierFrame k n X j D

/-- On every nonempty torus open, the normalized actual fractional embedding
agrees with the ordinary embedding of regular functions into K(X). -/
theorem torusNormalizedCartier_value
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V]
    (s : Γ((torusNormalizedCartier k n X j D).sheaf.restrict j,V)) :
    (torusNormalizedCartier k n X j D).alongSectionValue j V s =
      openImmersionRegularToFunctionField j V
        ((torusNormalizedCartierSheafIso k n X j D).hom.app V s) := by
  letI := torusCoordinateRing_isDomain k n
  calc
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        D.alongSectionValue j V s := D.scale_alongSectionValue j _ V s
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        (openImmersionRegularToFunctionField j V
          ((torusCartierFrame k n X j D).hom.app V s) *
            D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) :=
      congrArg (fun z : X.functionField =>
        (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) * z)
        (D.alongSectionValue_frame j (torusCartierFrame k n X j D) V s)
    _ = _ := by
      change (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))⁻¹ *
          (openImmersionRegularToFunctionField j V
            ((torusCartierFrame k n X j D).hom.app V s) *
              D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) = _
      field_simp [D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D)]
      rfl

/-- Equality of the actual fractional module with the regular-function
module on each torus open. No boundary or invariant-divisor dictionary is
included as an assumption. -/
theorem torusNormalizedCartier_range
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V] :
    Set.range ((torusNormalizedCartier k n X j D).alongSectionValue j V) =
      Set.range (openImmersionRegularToFunctionField j V) := by
  letI := torusCoordinateRing_isDomain k n
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(torusNormalizedCartierSheafIso k n X j D).hom.app V s,
      (torusNormalizedCartier_value k n X j D V s).symm⟩
  · rintro ⟨a,rfl⟩
    let E := torusNormalizedCartierSheafIso k n X j D
    let C := torusNormalizedCartier k n X j D
    let s := E.inv.app V a
    refine ⟨s,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V (E.hom.app V s) :=
        torusNormalizedCartier_value k n X j D V s
      _ = _ := congrArg (openImmersionRegularToFunctionField j V)
        ((C.chartFrameCoordinates j E V).apply_symm_apply a)

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_value
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_range
end
end Source_ToricTorusCartierRepresentative
-- END ORIGINAL PaperVerification.ToricTorusCartierRepresentative


-- BEGIN ORIGINAL PaperVerification.ToricCartierChartValues
section Source_ToricCartierChartValues

-- original header: module

-- original header: public import PaperVerification.ToricTorusCartierRepresentative
-- original header: public import PaperVerification.ToricCartierDescent

-- original header: @[expose] public section

/-!
# Fractional values on genuine open charts

A global frame on an open chart gives a principal fractional module on
every smaller ambient open. This statement is derived from restriction of
the actual sheaf. It also proves the regularity of the ratio of two chart
generators on the actual scheme overlap.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (D : CartierData X) (j : Y ⟶ X) [IsOpenImmersion j]

theorem alongSectionValue_range (V : Y.Opens) [Nonempty V] :
    Set.range (D.alongSectionValue j V) =
      Set.range (@sectionValue X inferInstance D (j ''ᵁ V)
        (openImmersion_image_nonempty j V)) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(D.sheaf.restrictAppIso j V).hom s,rfl⟩
  · rintro ⟨s,rfl⟩
    refine ⟨(D.sheaf.restrictAppIso j V).inv s,?_⟩
    change D.sectionValue (j ''ᵁ V)
      ((D.sheaf.restrictAppIso j V).hom ((D.sheaf.restrictAppIso j V).inv s)) = _
    simp

/-- The exact fractional-principal description on the image of a chart
open, with the ordinary ambient regular-function embedding. -/
theorem mem_sectionValueRange_image_iff
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] [Nonempty (j ''ᵁ V)] (r : X.functionField) :
    r ∈ D.sectionValueRange (j ''ᵁ V) ↔
      ∃ a : Γ(X,j ''ᵁ V), X.germToFunctionField (j ''ᵁ V) a *
        D.chartFrameRationalGenerator j e = r := by
  change r ∈ Set.range (D.sectionValue (j ''ᵁ V)) ↔ _
  rw [← D.alongSectionValue_range j V]
  constructor
  · rintro ⟨s,rfl⟩
    let a : Γ(Y,V) := e.hom.app V s
    refine ⟨(j.appIso V).inv a,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V a * D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V a).symm
      _ = _ := (D.alongSectionValue_frame j e V s).symm
  · rintro ⟨a,ha⟩
    let t : Γ(D.sheaf.restrict j,V) := e.inv.app V ((j.appIso V).hom a)
    refine ⟨t,?_⟩
    have he : (show Γ(Y,V) from e.hom.app V t) = (j.appIso V).hom a :=
      (D.chartFrameCoordinates j e V).apply_symm_apply ((j.appIso V).hom a)
    calc
      _ = openImmersionRegularToFunctionField j V (e.hom.app V t) *
          D.chartFrameRationalGenerator j e := D.alongSectionValue_frame j e V t
      _ = openImmersionRegularToFunctionField j V ((j.appIso V).hom a) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(Y,V) => openImmersionRegularToFunctionField j V r *
          D.chartFrameRationalGenerator j e) he
      _ = X.germToFunctionField (j ''ᵁ V) ((j.appIso V).inv ((j.appIso V).hom a)) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V ((j.appIso V).hom a))
      _ = X.germToFunctionField (j ''ᵁ V) a * D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(X,j ''ᵁ V) => X.germToFunctionField (j ''ᵁ V) r *
          D.chartFrameRationalGenerator j e) (CommRingCat.inv_hom_apply (j.appIso V) a)
      _ = r := ha

/-- The chart-frame formula holds on every smaller ambient open, not only
on opens presented as images in the statement. -/
theorem mem_sectionValueRange_iff_chartFrame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) (r : X.functionField) :
    r ∈ D.sectionValueRange W ↔
      ∃ a : Γ(X,W), X.germToFunctionField W a *
        D.chartFrameRationalGenerator j e = r := by
  let V := j ⁻¹ᵁ W
  letI : Nonempty V := openImmersion_preimage_nonempty j W
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  have himage : j ''ᵁ V=W := by
    rw [show V=j ⁻¹ᵁ W from rfl,j.image_preimage_eq_opensRange_inf,inf_eq_right.mpr hW]
  let P (U : X.Opens) : Prop := ∀ (hU : Nonempty U),
    letI : Nonempty U := hU
    r ∈ D.sectionValueRange U ↔
      ∃ a : Γ(X,U), X.germToFunctionField U a *
        D.chartFrameRationalGenerator j e = r
  have hP : P (j ''ᵁ V) := by
    intro hU
    letI := hU
    exact D.mem_sectionValueRange_image_iff j e V r
  have hQ : P W := Eq.mp (congrArg P himage) hP
  exact hQ inferInstance

theorem chartFrameRationalGenerator_mem_sectionValueRange
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) :
    D.chartFrameRationalGenerator j e ∈ D.sectionValueRange W := by
  apply (D.mem_sectionValueRange_iff_chartFrame j e W hW _).mpr
  exact ⟨1,by simp⟩

/-- A chart generator divided by another is an actual regular unit on
every nonempty open in their overlap. -/
theorem exists_chartFrameTransitionUnit (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hWj : W≤j.opensRange) (hWg : W≤g.opensRange) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f := by
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff_chartFrame g f W hWg _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange j e W hWj)
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hWj _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange g f W hWg)
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.chartFrameRationalGenerator_ne_zero j e)
    rw [mul_assoc,hb,ha,one_mul]
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,
    (eq_div_iff (D.chartFrameRationalGenerator_ne_zero g f)).mpr ha⟩

theorem chartFrameRatio_regularAt (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (x : X) (hxj : x∈j.opensRange) (hxg : x∈g.opensRange) :
    D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f ∈
      regularAtSubring X x := by
  let W := j.opensRange⊓g.opensRange
  letI : Nonempty W := ⟨⟨x,hxj,hxg⟩⟩
  obtain ⟨a,ha⟩ := D.exists_chartFrameTransitionUnit j g e f W inf_le_left inf_le_right
  rw [← ha]
  exact regular_germ_mem_regularAt X W a x ⟨hxj,hxg⟩

/-- A chosen generator of a chart frame is a unit on an open where the
actual fractional module equals the regular-function module. -/
theorem chartFrameGenerator_isUnit_of_range
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange)
    (hregular : (D.sectionValueRange W : Set X.functionField)=
      Set.range (X.germToFunctionField W)) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e := by
  have hq := D.chartFrameRationalGenerator_mem_sectionValueRange j e W hW
  change D.chartFrameRationalGenerator j e ∈ (D.sectionValueRange W : Set X.functionField) at hq
  rw [hregular] at hq
  obtain ⟨a,ha⟩ := hq
  have h1 : (1 : X.functionField)∈D.sectionValueRange W := by
    change (1 : X.functionField)∈(D.sectionValueRange W : Set X.functionField)
    rw [hregular]
    exact ⟨1,map_one _⟩
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hW 1).mp h1
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one,ha,mul_comm]
    exact hb
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

end PaperVerification.ToricSchemes.CartierData

#print axioms PaperVerification.ToricSchemes.CartierData.mem_sectionValueRange_iff_chartFrame
#print axioms PaperVerification.ToricSchemes.CartierData.exists_chartFrameTransitionUnit
#print axioms PaperVerification.ToricSchemes.CartierData.chartFrameGenerator_isUnit_of_range
end
end Source_ToricCartierChartValues
-- END ORIGINAL PaperVerification.ToricCartierChartValues


-- BEGIN ORIGINAL PaperVerification.ToricChartFactorization
section Source_ToricChartFactorization

-- original header: module

-- original header: public import PaperVerification.ToricLaurentPicard
-- original header: public import PaperVerification.ToricCartierCharacterModules

-- original header: @[expose] public section

/-! # Unique factorization on every actual smooth affine chart -/

noncomputable section

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

def finiteLatticeCoordinates (J : Type*) [Fintype J] :
    (J → ℤ) ≃+ (Fin (Fintype.card J) → ℤ) where
  toFun x i := x ((Fintype.equivFin J).symm i)
  invFun x j := x (Fintype.equivFin J j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

def finiteCharacterRingEquiv (J : Type*) [Fintype J] :
    AddMonoidAlgebra k (J → ℤ) ≃ₐ[k] torusCoordinateRing k (Fintype.card J) :=
  AddMonoidAlgebra.domCongr k k (finiteLatticeCoordinates J)

theorem finiteCharacterRing_isDomain (J : Type*) [Fintype J] :
    IsDomain (AddMonoidAlgebra k (J → ℤ)) := by
  letI := torusCoordinateRing_isDomain k (Fintype.card J)
  exact MulEquiv.isDomain _ (finiteCharacterRingEquiv k J).toMulEquiv

theorem finiteCharacterRing_uniqueFactorization (J : Type*) [Fintype J] :
    UniqueFactorizationMonoid (AddMonoidAlgebra k (J → ℤ)) :=
  (finiteCharacterRingEquiv k J).symm.toMulEquiv.uniqueFactorizationMonoid
    (torusCoordinateRing_uniqueFactorization k (Fintype.card J))

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartRing_isDomain (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    IsDomain (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  exact MulEquiv.isDomain _ e.toMulEquiv

/-- Factoriality is proved from the actual chart algebra equivalence;
it is not an extra hypothesis on a smooth fan. -/
theorem chartRing_uniqueFactorization (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    UniqueFactorizationMonoid (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  letI := finiteCharacterRing_uniqueFactorization k (FreeCoordinate I)
  exact e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartRing_uniqueFactorization
end
end Source_ToricChartFactorization
-- END ORIGINAL PaperVerification.ToricChartFactorization


-- BEGIN ORIGINAL PaperVerification.ToricChartPicard
section Source_ToricChartPicard

-- original header: module

-- original header: public import PaperVerification.ToricChartFactorization
-- original header: public import PaperVerification.ToricAffinePicard

-- original header: @[expose] public section

/-! # Triviality of the actual Picard group on every smooth fan chart -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AlgebraicGeometry CategoryTheory

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartPic_subsingleton (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    Subsingleton (CommRing.Pic (monoidChartAlgebra k (dualConeMonoid s))) := by
  letI := «Σ».chartRing_isDomain k s hs
  letI := «Σ».chartRing_uniqueFactorization k s hs
  infer_instance

/-- Every actual invertible sheaf on a smooth cone chart is trivial.
The assertion is for the genuine structure sheaf, not a character module. -/
def chartInvertibleSheafIso (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones)
    (M : (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).ringCatSheaf := by
  letI := «Σ».chartPic_subsingleton k s hs
  exact affineInvertibleSheafIso M hM

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartInvertibleSheafIso
end
end Source_ToricChartPicard
-- END ORIGINAL PaperVerification.ToricChartPicard


-- BEGIN ORIGINAL PaperVerification.ToricPrincipalChartModules
section Source_ToricPrincipalChartModules

-- original header: module

-- original header: public import PaperVerification.ToricCartierCharacterModules
-- original header: public import Mathlib.Algebra.Module.Submodule.Equiv
-- original header: public import Mathlib.Algebra.Module.Submodule.RestrictScalars

-- original header: @[expose] public section

/-!
# Rank-one principal chart modules and the actual transition units

The local module is a module over its genuine semigroup chart algebra.
Multiplication by its Laurent character gives an explicit linear
equivalence with that chart algebra. On overlaps, agreeing Cartier
pairings give an actual unit and its explicit inverse.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

def principalChartGeneratorMap (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S →ₗ[monoidChartAlgebra k S] AddMonoidAlgebra k G :=
  (LinearMap.mul (monoidChartAlgebra k S) (AddMonoidAlgebra k G)
    (single v (1 : k))).comp
      (Algebra.linearMap (monoidChartAlgebra k S) (AddMonoidAlgebra k G))

@[simp] theorem principalChartGeneratorMap_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    principalChartGeneratorMap k S v f = single v (1 : k) * (f : AddMonoidAlgebra k G) := rfl

theorem principalChartGeneratorMap_injective (S : AddSubmonoid G) (v : G) :
    Function.Injective (principalChartGeneratorMap k S v) :=
  (characterTranslation k v).injective.comp Subtype.val_injective

def principalChartModule (S : AddSubmonoid G) (v : G) :
    Submodule (monoidChartAlgebra k S) (AddMonoidAlgebra k G) :=
  LinearMap.range (principalChartGeneratorMap k S v)

/-- Actual rank-one local triviality, over the chart algebra itself. -/
def principalChartTrivialization (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S ≃ₗ[monoidChartAlgebra k S] principalChartModule k S v :=
  LinearEquiv.ofInjective (principalChartGeneratorMap k S v)
    (principalChartGeneratorMap_injective k S v)

@[simp] theorem principalChartTrivialization_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    ((principalChartTrivialization k S v f : principalChartModule k S v) :
      AddMonoidAlgebra k G) = single v (1 : k) * f := rfl

theorem principalChartModule_restrictScalars (S : AddSubmonoid G) (v : G) :
    (principalChartModule k S v).restrictScalars k =
      (characterModule k (S : Set G)).map (characterTranslation k v).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨(g : AddMonoidAlgebra k G), ?_, rfl⟩
    rw [← monoidChartAlgebra_toSubmodule k S]
    exact g.property
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ monoidChartAlgebra k S := by
      change g ∈ (monoidChartAlgebra k S).toSubmodule
      rw [monoidChartAlgebra_toSubmodule]
      exact hg
    exact ⟨⟨g, hg'⟩, rfl⟩

/-- A character and its inverse both in the semigroup give an actual
unit of the chart algebra, not merely a unit in the ambient function field. -/
def chartCharacterUnit (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) : (monoidChartAlgebra k S)ˣ where
  val := ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩
  inv := ⟨single (-v) (1 : k), ⟨single ⟨-v, hneg⟩ (1 : k), by simp⟩⟩
  val_inv := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]
  inv_val := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]

@[simp] theorem chartCharacterUnit_val (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) :
    (((chartCharacterUnit k S v hv hneg : (monoidChartAlgebra k S)ˣ) :
      monoidChartAlgebra k S) : AddMonoidAlgebra k G) = single v (1 : k) := rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (k : Type*) [CommSemiring k]

/-- The difference of two actual Cartier characters pairs to zero on
the intersection cone, so it and its negative are both regular there. -/
theorem cartier_difference_mem_overlap (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    «Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) ∧
    -(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) := by
  have hz (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n)) ∩ t) :
      integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) = 0 := by
    rw [integerPairing_sub,
      «Σ».cartierLatticePoint_pairing a s u (Finset.mem_inter.mp hu).1,
      «Σ».cartierLatticePoint_pairing a t u (Finset.mem_inter.mp hu).2, sub_self]
  constructor
  · intro u hu
    rw [hz u hu]
  · intro u hu
    have he : integerPairing u (-(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)) =
        -integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) := by
      simp only [integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [he, hz u hu, neg_zero]

def cartierTransitionUnit (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ :=
  chartCharacterUnit k _ («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)
    («Σ».cartier_difference_mem_overlap a s t).1
    («Σ».cartier_difference_mem_overlap a s t).2

theorem cartierTransitionUnit_character (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (((«Σ».cartierTransitionUnit k a s t :
      (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ) :
      monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t))) :
      AddMonoidAlgebra k (Lattice n)) =
        single («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) (1 : k) := rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricCharacters.principalChartTrivialization
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierTransitionUnit
end
end Source_ToricPrincipalChartModules
-- END ORIGINAL PaperVerification.ToricPrincipalChartModules


-- BEGIN ORIGINAL PaperVerification.ToricChartLocalization
section Source_ToricChartLocalization

-- original header: module

-- original header: public import PaperVerification.ToricPrincipalChartModules
-- original header: public import Mathlib.RingTheory.Localization.Away.Basic
-- original header: public import Mathlib.Data.Finset.Lattice.Fold

-- original header: @[expose] public section

/-!
# Localization of actual semigroup chart subalgebras

All maps below are the literal inclusions of subalgebras of k[M]. A
finite Laurent polynomial has one common character denominator whenever
each of its finitely many exponents does. This proves the localization
property, without replacing the inclusion by an abstract ring isomorphism.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped BigOperators Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

theorem monoidChartAlgebra_mono {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S ≤ monoidChartAlgebra k T := by
  intro f hf
  rw [mem_monoidChartAlgebra] at hf ⊢
  exact fun m hm => hST (hf hm)

def monoidChartInclusion {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S →ₐ[k] monoidChartAlgebra k T :=
  Subalgebra.inclusion (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_coe {S T : AddSubmonoid G} (hST : S ≤ T)
    (f : monoidChartAlgebra k S) :
    ((monoidChartInclusion k hST f : monoidChartAlgebra k T) : AddMonoidAlgebra k G) = f := rfl

theorem monoidChartInclusion_injective {S T : AddSubmonoid G} (hST : S ≤ T) :
    Function.Injective (monoidChartInclusion k hST) :=
  Subalgebra.inclusion_injective (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (monoidChartInclusion k hTU).comp (monoidChartInclusion k hST) =
      monoidChartInclusion k (hST.trans hTU) := by
  ext f
  rfl

@[simp] theorem monoidChartInclusion_self (S : AddSubmonoid G) :
    monoidChartInclusion k (le_refl S) = AlgHom.id k (monoidChartAlgebra k S) := by
  ext f
  rfl

def chartCharacter (S : AddSubmonoid G) (v : G) (hv : v ∈ S) : monoidChartAlgebra k S :=
  ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩

@[simp] theorem chartCharacter_coe (S : AddSubmonoid G) (v : G) (hv : v ∈ S) :
    ((chartCharacter k S v hv : monoidChartAlgebra k S) : AddMonoidAlgebra k G) =
      single v (1 : k) := rfl

@[simp] theorem monoidChartInclusion_character {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) :
    monoidChartInclusion k hST (chartCharacter k S v hv) =
      chartCharacter k T v (hST hv) := rfl

theorem finite_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (F : Finset G) (hF : ∀ m ∈ F, m ∈ T) :
    ∃ N : ℕ, ∀ m ∈ F, m + N • v ∈ S := by
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro hF
      exact ⟨0, by simp⟩
  | @insert m F hm ih =>
      intro hF
      obtain ⟨N, hN⟩ := ih (fun z hz => hF z (Finset.mem_insert_of_mem hz))
      obtain ⟨L, hL⟩ := hclear m (hF m (Finset.mem_insert_self m F))
      refine ⟨L + N, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [add_nsmul, add_assoc] using S.add_mem hL (S.nsmul_mem hv N)
      · have hh := S.add_mem (hN z hz) (S.nsmul_mem hv L)
        simpa only [add_nsmul, add_assoc, add_comm, add_left_comm] using hh

/-- One common monomial clears every denominator of the actual finite
Laurent polynomial, not only of each monomial separately. -/
theorem polynomial_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (f : monoidChartAlgebra k T) :
    ∃ N : ℕ, (f : AddMonoidAlgebra k G) * single (N • v) (1 : k) ∈
      monoidChartAlgebra k S := by
  have hf : ∀ m ∈ (f : AddMonoidAlgebra k G).coeff.support, m ∈ T :=
    (mem_monoidChartAlgebra k T f).mp f.property
  obtain ⟨N, hN⟩ := finite_character_denominator v hv hclear
    (f : AddMonoidAlgebra k G).coeff.support hf
  refine ⟨N, (mem_monoidChartAlgebra k S _).mpr ?_⟩
  intro z hz
  have hsupport := AddMonoidAlgebra.support_coeff_mul_single_subset
    (f : AddMonoidAlgebra k G) (1 : k) (N • v)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (hsupport hz)
  exact hN m hm

/-- The literal inclusion is a localization map at the specified
character. The kernel condition follows from actual injectivity. -/
theorem monoidChartInclusion_isLocalizationMap {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) (hneg : -v ∈ T)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S) :
    (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST) := by
  have hunit : IsUnit (monoidChartInclusion k hST (chartCharacter k S v hv)) := by
    exact (chartCharacterUnit k T v (hST hv) hneg).isUnit
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff _ _).mp y.property
    rw [← hN, map_pow]
    exact hunit.pow N
  · intro f
    obtain ⟨N, hN⟩ := polynomial_character_denominator k v hv hclear f
    let g : monoidChartAlgebra k S :=
      ⟨(f : AddMonoidAlgebra k G) * single (N • v) (1 : k), hN⟩
    let y : Submonoid.powers (chartCharacter k S v hv) :=
      ⟨(chartCharacter k S v hv) ^ N, (Submonoid.mem_powers_iff _ _).mpr ⟨N, rfl⟩⟩
    refine ⟨(g, y), ?_⟩
    apply Subtype.ext
    change (f : AddMonoidAlgebra k G) * (single v (1 : k)) ^ N =
      (f : AddMonoidAlgebra k G) * single (N • v) (1 : k)
    simp only [AddMonoidAlgebra.single_pow, one_pow]
  · intro x y hxy
    have heq := monoidChartInclusion_injective k hST hxy
    subst y
    exact ⟨1, rfl⟩

end PaperVerification.ToricCharacters
end
end Source_ToricChartLocalization
-- END ORIGINAL PaperVerification.ToricChartLocalization


-- BEGIN ORIGINAL PaperVerification.ToricChartFaceLocalization
section Source_ToricChartFaceLocalization

-- original header: module

-- original header: public import PaperVerification.ToricChartLocalization
-- original header: public import PaperVerification.ToricFanConstruction

-- original header: @[expose] public section

/-!
# The denominator of a smooth cone face

Removing coordinate inequalities is exactly localization by the product
of the removed coordinate characters. The exponent is their sum in the
actual dual integral basis. This applies to every actual smooth fan cone
and every face ray subset.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]

theorem coordinateConeMonoid_antitone (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    coordinateConeMonoid b J ≤ coordinateConeMonoid b I :=
  fun x hx i hi => hx i (hIJ hi)

def faceDenominatorExponent (b : Module.Basis ι ℤ E) (I J : Finset ι) : E :=
  ∑ j ∈ J \ I, b j

theorem faceDenominatorExponent_repr (b : Module.Basis ι ℤ E)
    (I J : Finset ι) (i : ι) :
    b.repr (faceDenominatorExponent b I J) i = if i ∈ J \ I then 1 else 0 := by
  simp [faceDenominatorExponent, map_sum, Finsupp.finsetSum_apply,
    Module.Basis.repr_self_apply, Finsupp.single_apply, eq_comm]

theorem faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  intro i hi
  rw [faceDenominatorExponent_repr]
  split_ifs <;> norm_num

theorem neg_faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    -faceDenominatorExponent b I J ∈ coordinateConeMonoid b I := by
  intro i hi
  rw [map_neg, Finsupp.neg_apply, faceDenominatorExponent_repr,
    if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hi), neg_zero]

theorem faceDenominatorExponent_clears (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b I) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  let N := (J \ I).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiJ
  have hrepr : b.repr (x + N • faceDenominatorExponent b I J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ I then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiI : i ∈ I
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiI), mul_zero, add_zero]
    exact hx i hiI
  · have hi : i ∈ J \ I := Finset.mem_sdiff.mpr ⟨hiJ, hiI⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat) hi
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

/-- After restricting to another face, the original denominator removes
exactly the inequalities not shared by the two faces. Coordinates already
invertible on the restricted chart cause no additional condition. -/
theorem faceDenominatorExponent_clears_intersection (b : Module.Basis ι ℤ E)
    {I K J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b (I ∩ K)) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b K J ∈ coordinateConeMonoid b I := by
  let N := (I \ K).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiI
  have hrepr : b.repr (x + N • faceDenominatorExponent b K J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ K then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiK : i ∈ K
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiK), mul_zero, add_zero]
    exact hx i (Finset.mem_inter.mpr ⟨hiI, hiK⟩)
  · have hi : i ∈ J \ K := Finset.mem_sdiff.mpr ⟨hIJ hiI, hiK⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat)
        (Finset.mem_sdiff.mpr ⟨hiI, hiK⟩)
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

variable (k : Type*) [CommSemiring k]

theorem coordinateChartInclusion_isLocalizationMap
    (b : Module.Basis ι ℤ E) {I J : Finset ι} (hIJ : I ⊆ J) :
    (Submonoid.powers (chartCharacter k (coordinateConeMonoid b J)
      (faceDenominatorExponent b I J) (faceDenominatorExponent_mem b I J))).IsLocalizationMap
        (monoidChartInclusion k (coordinateConeMonoid_antitone b hIJ)) :=
  monoidChartInclusion_isLocalizationMap k (coordinateConeMonoid_antitone b hIJ)
    _ (faceDenominatorExponent_mem b I J) (neg_faceDenominatorExponent_mem b I J)
    (faceDenominatorExponent_clears b hIJ)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

theorem dualConeMonoid_antitone {n : ℕ} {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    dualConeMonoid s ≤ dualConeMonoid t := fun m hm u hu => hm u (hts hu)

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every actual smooth cone face has a single integral character whose
inversion removes precisely the discarded inequalities. -/
theorem exists_face_character_denominator
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ v : Lattice n, v ∈ dualConeMonoid s ∧ -v ∈ dualConeMonoid t ∧
      ∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid s := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b = t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := by
    intro i hi
    have hbi : b i ∈ t := hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  refine ⟨faceDenominatorExponent (integralDualBasis b) I J, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro m hm
    rw [← hI, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩

theorem chart_face_isLocalizationMap (k : Type*) [CommSemiring k]
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) v hv)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) := by
  obtain ⟨v, hv, hneg, hclear⟩ := «Σ».exists_face_character_denominator s t hs hts
  exact ⟨v, hv, monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hneg hclear⟩

/-- The same character localizes both a cone chart to one face and another
face chart to their actual intersection. -/
theorem exists_intersection_character_denominator
    (q s t : Finset (Lattice n)) (hq : q ∈ «Σ».cones)
    (hs : s ⊆ q) (ht : t ⊆ q) :
    ∃ v : Lattice n, v ∈ dualConeMonoid q ∧ -v ∈ dualConeMonoid t ∧
      (∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid q) ∧
      (∀ m ∈ dualConeMonoid (s ∩ t), ∃ N : ℕ, m + N • v ∈ dualConeMonoid s) := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth q hq
  let I := basisRayIndices b s
  let K := basisRayIndices b t
  have hI : I.image b = s := image_basisRayIndices b s
    (hs.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hK : K.image b = t := image_basisRayIndices b t
    (ht.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hI.symm ▸ hs)
  have hKJ : K ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hK.symm ▸ ht)
  have hIK : (I ∩ K).image b = s ∩ t := by
    rw [Finset.image_inter I K b.injective, hI, hK]
  let v := faceDenominatorExponent (integralDualBasis b) K J
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) K J
  · rw [← hK, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) K J
  · intro m hm
    rw [← hK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hKJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩
  · intro m hm
    rw [← hIK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears_intersection
      (integralDualBasis b) hIJ m hm
    refine ⟨N, ?_⟩
    rw [← hI, dualConeMonoid_basis_eq]
    exact hN

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricChartFaceLocalization
-- END ORIGINAL PaperVerification.ToricChartFaceLocalization


-- BEGIN ORIGINAL PaperVerification.ToricChartOpenImmersions
section Source_ToricChartOpenImmersions

-- original header: module

-- original header: public import PaperVerification.ToricChartFaceLocalization
-- original header: public import Mathlib.AlgebraicGeometry.OpenImmersion

-- original header: @[expose] public section

/-!
# Actual affine chart maps and their open images

The schemes are spectra of the semigroup subalgebras inside the character
ring. Every morphism is induced by their literal inclusion. Localization
therefore gives an actual open immersion, with its specified principal
open image. The final lemma is the categorical pullback statement for
two localizations with the same character denominator.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable (k : Type*) [CommRing k]
variable {G : Type*} [AddCommGroup G]

def monoidChartScheme (S : AddSubmonoid G) : Scheme :=
  Spec (CommRingCat.of (monoidChartAlgebra k S))

def monoidChartSpecMap {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartScheme k T ⟶ monoidChartScheme k S :=
  Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom)

@[simp] theorem monoidChartSpecMap_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    monoidChartSpecMap k hTU ≫ monoidChartSpecMap k hST =
      monoidChartSpecMap k (hST.trans hTU) := by
  dsimp only [monoidChartSpecMap, monoidChartScheme]
  rw [← Spec.map_comp]
  congr 1

@[simp] theorem monoidChartSpecMap_self (S : AddSubmonoid G) :
    monoidChartSpecMap k (le_refl S) = 𝟙 (monoidChartScheme k S) := by
  have heq : CommRingCat.ofHom (monoidChartInclusion k (le_refl S)).toRingHom =
      𝟙 (CommRingCat.of (monoidChartAlgebra k S)) := by
    ext f
    rfl
  exact (congrArg Spec.map heq).trans (Spec.map_id _)

theorem monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST)) :
    IsOpenImmersion (monoidChartSpecMap k hST) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact IsOpenImmersion.of_isLocalization (chartCharacter k S v hv)

theorem monoidChartSpecMap_opensRange_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST))
    [IsOpenImmersion (monoidChartSpecMap k hST)] :
    (monoidChartSpecMap k hST).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact SetLike.coe_injective
    (PrimeSpectrum.localization_away_comap_range (monoidChartAlgebra k T)
      (chartCharacter k S v hv))

/-- An actual square of chart inclusions is a pullback when its two
vertical arrows invert the same character before and after restriction.
No abstract replacement of any chart algebra is used. -/
theorem monoidChartSquare_isPullback
    {S T U V : AddSubmonoid G}
    (hST : S ≤ T) (hSU : S ≤ U) (hTV : T ≤ V) (hUV : U ≤ V)
    (v : G) (hv : v ∈ S)
    (hlocSU : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hSU))
    (hlocTV : (Submonoid.powers (chartCharacter k T v (hST hv))).IsLocalizationMap
      (monoidChartInclusion k hTV)) :
    IsPullback (monoidChartSpecMap k hUV) (monoidChartSpecMap k hTV)
      (monoidChartSpecMap k hSU) (monoidChartSpecMap k hST) := by
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hSU v hv hlocSU
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hTV v (hST hv) hlocTV
  apply IsOpenImmersion.isPullback
  · simp only [monoidChartSpecMap_comp]
  · rw [monoidChartSpecMap_opensRange_of_isLocalizationMap k hSU v hv hlocSU,
      monoidChartSpecMap_opensRange_of_isLocalizationMap k hTV v (hST hv) hlocTV]
    change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) =
        PrimeSpectrum.basicOpen (chartCharacter k T v (hST hv))
    rw [SpecMap_preimage_basicOpen]
    rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory

variable (k : Type*) [CommRing k] {n : ℕ}

def coneChart (s : Finset (Lattice n)) : Scheme :=
  monoidChartScheme k (dualConeMonoid s)

def coneChartFaceMap {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    coneChart k t ⟶ coneChart k s :=
  monoidChartSpecMap k (dualConeMonoid_antitone hts)

@[simp] theorem coneChartFaceMap_comp {s t u : Finset (Lattice n)}
    (hts : t ⊆ s) (hut : u ⊆ t) :
    coneChartFaceMap k hut ≫ coneChartFaceMap k hts =
      coneChartFaceMap k (hut.trans hts) :=
  monoidChartSpecMap_comp k (dualConeMonoid_antitone hts) (dualConeMonoid_antitone hut)

@[simp] theorem coneChartFaceMap_self (s : Finset (Lattice n)) :
    coneChartFaceMap k (Finset.Subset.refl s) = 𝟙 (coneChart k s) :=
  monoidChartSpecMap_self k (dualConeMonoid s)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem coneChartFaceMap_isOpenImmersion (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    IsOpenImmersion (coneChartFaceMap k hts) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  exact monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc

theorem coneChartFaceMap_principal_open (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s)
    [IsOpenImmersion (coneChartFaceMap k hts)] :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  exact ⟨v, hv, monoidChartSpecMap_opensRange_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc⟩

/-- The affine chart of the actual common face is the scheme-theoretic
overlap of two face charts inside the original chart. -/
theorem coneChart_faces_isPullback (q s t : Finset (Lattice n))
    (hq : q ∈ «Σ».cones) (hs : s ⊆ q) (ht : t ⊆ q) :
    CategoryTheory.IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s ∩ t ⊆ t))
      (coneChartFaceMap k (Finset.inter_subset_left : s ∩ t ⊆ s))
      (coneChartFaceMap k ht) (coneChartFaceMap k hs) := by
  obtain ⟨v, hv, hneg, hclear, hclearInter⟩ :=
    «Σ».exists_intersection_character_denominator q s t hq hs ht
  apply monoidChartSquare_isPullback k
    (dualConeMonoid_antitone hs) (dualConeMonoid_antitone ht)
    (dualConeMonoid_antitone Finset.inter_subset_left)
    (dualConeMonoid_antitone Finset.inter_subset_right) v hv
  · exact monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone ht)
      v hv hneg hclear
  · exact monoidChartInclusion_isLocalizationMap k
      (dualConeMonoid_antitone Finset.inter_subset_left)
      v (dualConeMonoid_antitone hs hv)
      (dualConeMonoid_antitone Finset.inter_subset_right hneg) hclearInter

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricChartOpenImmersions
-- END ORIGINAL PaperVerification.ToricChartOpenImmersions


-- BEGIN ORIGINAL PaperVerification.ToricFanScheme
section Source_ToricFanScheme

-- original header: module

-- original header: public import PaperVerification.ToricChartOpenImmersions
-- original header: public import Mathlib.AlgebraicGeometry.Gluing
-- original header: public import Mathlib.CategoryTheory.Category.Preorder

-- original header: @[expose] public section

/-!
# The actual scheme obtained by gluing a smooth fan

Every cone supplies its actual affine semigroup chart. Face inclusions are
the previously proved open immersions. Their actual intersections prove
local directedness, so Mathlib's scheme gluing construction applies. The
result is a scheme with an actual affine open cover, not a structure whose
fields assume a toric dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

abbrev ConeIndex := {s : Finset (Lattice n) // s ∈ «Σ».cones}

def coneDiagram : «Σ».ConeIndex ⥤ Scheme.{u} where
  obj s := coneChart k s.val
  map f := coneChartFaceMap k (leOfHom f)
  map_id s := coneChartFaceMap_self k s.val
  map_comp f g := (coneChartFaceMap_comp k (leOfHom g) (leOfHom f)).symm

instance coneDiagram_map_isOpenImmersion {s t : «Σ».ConeIndex} (f : s ⟶ t) :
    IsOpenImmersion ((«Σ».coneDiagram k).map f) :=
  «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom f)

/-- The local directedness condition is proved from the actual common-face
pullback, including the underlying point lifting. -/
instance coneDiagram_isLocallyDirected :
    («Σ».coneDiagram k ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro i j q fi fj xi xj h
    let l : «Σ».ConeIndex :=
      ⟨i.val ∩ j.val, «Σ».downward i.val i.property _ Finset.inter_subset_left⟩
    let fli : l ⟶ i := homOfLE Finset.inter_subset_left
    let flj : l ⟶ j := homOfLE Finset.inter_subset_right
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val i.val q.property (leOfHom fi)
    letI := «Σ».coneChartFaceMap_isOpenImmersion k q.val j.val q.property (leOfHom fj)
    have H := «Σ».coneChart_faces_isPullback k q.val i.val j.val
      q.property (leOfHom fi) (leOfHom fj)
    change coneChartFaceMap k (leOfHom fi) xi =
      coneChartFaceMap k (leOfHom fj) xj at h
    have hx : xi ∈ Set.range (pullback.snd
        (coneChartFaceMap k (leOfHom fj)) (coneChartFaceMap k (leOfHom fi))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨xj, h.symm⟩
    obtain ⟨z, hz⟩ := hx
    let x := H.isoPullback.inv z
    have hxi : coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x =
        xi := by
      exact (congrArg (fun f => f z) H.isoPullback_inv_snd).trans hz
    have hxj : coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x =
        xj := by
      apply (coneChartFaceMap k (leOfHom fj)).isOpenEmbedding.injective
      calc
        coneChartFaceMap k (leOfHom fj)
            (coneChartFaceMap k (Finset.inter_subset_right : i.val ∩ j.val ⊆ j.val) x) =
          coneChartFaceMap k (leOfHom fi)
            (coneChartFaceMap k (Finset.inter_subset_left : i.val ∩ j.val ⊆ i.val) x) :=
          congrArg (fun f => f x) H.w
        _ = coneChartFaceMap k (leOfHom fi) xi := by rw [hxi]
        _ = coneChartFaceMap k (leOfHom fj) xj := h
    exact ⟨l, fli, flj, x, hxi, hxj⟩

/-- Genuine Mathlib gluing data, with all its cocycle obligations derived
by locally directed scheme gluing. -/
def fanGlueData : Scheme.GlueData.{u} :=
  Scheme.IsLocallyDirected.glueData («Σ».coneDiagram k)

/-- The actual colimit scheme of the affine charts. -/
def fanScheme : Scheme.{u} := colimit («Σ».coneDiagram k)

def fanChartMap (s : «Σ».ConeIndex) : coneChart k s.val ⟶ «Σ».fanScheme k :=
  colimit.ι («Σ».coneDiagram k) s

instance fanChartMap_isOpenImmersion (s : «Σ».ConeIndex) :
    IsOpenImmersion («Σ».fanChartMap k s) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι («Σ».coneDiagram k) s))

def fanSchemeOpenCover : («Σ».fanScheme k).OpenCover :=
  Scheme.IsLocallyDirected.openCover («Σ».coneDiagram k)

@[reassoc (attr := simp)] theorem fanChartMap_naturality
    {s t : «Σ».ConeIndex} (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst ≫ «Σ».fanChartMap k t = «Σ».fanChartMap k s :=
  colimit.w («Σ».coneDiagram k) (homOfLE hst)

theorem fanChartMap_jointly_surjective (x : «Σ».fanScheme k) :
    ∃ (s : «Σ».ConeIndex) (y : coneChart k s.val), «Σ».fanChartMap k s y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective («Σ».coneDiagram k) x

/-- Equality of two points in the glued scheme is witnessed in the actual
intersection cone chart. No larger relation is imposed by the gluing. -/
theorem fanChartMap_eq_iff (s t : «Σ».ConeIndex)
    (x : coneChart k s.val) (y : coneChart k t.val) :
    «Σ».fanChartMap k s x = «Σ».fanChartMap k t y ↔
      ∃ z : coneChart k (s.val ∩ t.val),
        coneChartFaceMap k Finset.inter_subset_left z = x ∧
        coneChartFaceMap k Finset.inter_subset_right z = y := by
  constructor
  · intro h
    obtain ⟨l, fls, flt, z, hzs, hzt⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff («Σ».coneDiagram k)).mp h
    have hl : l.val ⊆ s.val ∩ t.val :=
      Finset.subset_inter (leOfHom fls) (leOfHom flt)
    let z' : coneChart k l.val := z
    have hzs' : coneChartFaceMap k (leOfHom fls) z' = x := hzs
    have hzt' : coneChartFaceMap k (leOfHom flt) z' = y := hzt
    refine ⟨coneChartFaceMap k hl z', ?_, ?_⟩
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k s.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val) hl)).trans hzs'
    · exact (congrArg (fun f : coneChart k l.val ⟶ coneChart k t.val => f z')
        (coneChartFaceMap_comp k
          (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val) hl)).trans hzt'
  · rintro ⟨z, rfl, rfl⟩
    let l : «Σ».ConeIndex :=
      ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
    change (coneChartFaceMap k (show l.val ⊆ s.val from Finset.inter_subset_left) ≫
      «Σ».fanChartMap k s) z =
      (coneChartFaceMap k (show l.val ⊆ t.val from Finset.inter_subset_right) ≫
        «Σ».fanChartMap k t) z
    rw [«Σ».fanChartMap_naturality, «Σ».fanChartMap_naturality]

/-- The affine overlap in the glued scheme is the common-face chart as
a scheme-theoretic pullback, not merely as a set of points. -/
theorem fanChart_inter_isPullback (s t : «Σ».ConeIndex) :
    IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))
      («Σ».fanChartMap k t) («Σ».fanChartMap k s) := by
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val s.property _ Finset.inter_subset_left⟩
  letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val l.val s.property Finset.inter_subset_left
  apply IsOpenImmersion.isPullback
  · exact («Σ».fanChartMap_naturality k (s := l) (t := s)
      Finset.inter_subset_left).trans
        («Σ».fanChartMap_naturality k (s := l) (t := t)
          Finset.inter_subset_right).symm
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := («Σ».fanChartMap_eq_iff k s t x y).mp hy.symm
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      refine ⟨coneChartFaceMap k Finset.inter_subset_right z, ?_⟩
      exact («Σ».fanChartMap_eq_iff k s t _ _).mpr ⟨z, rfl, rfl⟩ |>.symm

/-- The zero cone is the actual open torus chart. -/
def zeroConeIndex : «Σ».ConeIndex := ⟨∅, «Σ».empty_mem⟩

def torusOpenMap : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k :=
  «Σ».fanChartMap k «Σ».zeroConeIndex

instance torusOpenMap_isOpenImmersion : IsOpenImmersion («Σ».torusOpenMap k) :=
  inferInstanceAs (IsOpenImmersion («Σ».fanChartMap k «Σ».zeroConeIndex))

set_option maxHeartbeats 1000000 in
@[reassoc (attr := simp)] theorem torusOpenMap_chart (s : «Σ».ConeIndex) :
    coneChartFaceMap k (Finset.empty_subset s.val) ≫ «Σ».fanChartMap k s =
      «Σ».torusOpenMap k :=
  «Σ».fanChartMap_naturality k (s := «Σ».zeroConeIndex) (t := s)
    (Finset.empty_subset s.val)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricFanScheme
-- END ORIGINAL PaperVerification.ToricFanScheme


-- BEGIN ORIGINAL PaperVerification.ToricFanSchemeIntegral
section Source_ToricFanSchemeIntegral

-- original header: module

-- original header: public import PaperVerification.ToricFanScheme
-- original header: public import PaperVerification.ToricChartFactorization
-- original header: public import Mathlib.AlgebraicGeometry.Properties

-- original header: @[expose] public section

/-!
# Integrality and the dense torus of the glued fan scheme

The actual affine chart rings are domains. Their zero prime ideals agree
under all face restrictions, and yield a generic point of the glued
scheme. Reducedness is local on the proved affine open cover. Together
these prove integrality and density of the actual zero-cone chart.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_isIntegral (s : «Σ».ConeIndex) : IsIntegral (coneChart k s.val) := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact inferInstanceAs
    (IsIntegral (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))))

def fanChartGenericPoint (s : «Σ».ConeIndex) : coneChart k s.val := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  exact ⟨⊥, inferInstance⟩

theorem fanChartGenericPoint_isGenericPoint (s : «Σ».ConeIndex) :
    IsGenericPoint («Σ».fanChartGenericPoint k s) Set.univ := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  change closure ({(⟨⊥, inferInstance⟩ :
    PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))} :
    Set (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))) = Set.univ
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

@[simp] theorem fanChartGenericPoint_faceMap {s t : «Σ».ConeIndex}
    (hst : s.val ⊆ t.val) :
    coneChartFaceMap k hst («Σ».fanChartGenericPoint k s) = «Σ».fanChartGenericPoint k t := by
  apply PrimeSpectrum.ext
  change Ideal.comap (monoidChartInclusion k (dualConeMonoid_antitone hst)).toRingHom ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    (monoidChartInclusion_injective k (dualConeMonoid_antitone hst))

def fanGenericPoint : «Σ».fanScheme k :=
  «Σ».torusOpenMap k («Σ».fanChartGenericPoint k «Σ».zeroConeIndex)

@[simp] theorem fanChartMap_genericPoint (s : «Σ».ConeIndex) :
    «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) = «Σ».fanGenericPoint k := by
  have hface := «Σ».fanChartGenericPoint_faceMap k
    (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)
  have h := congrArg
    (fun f : coneChart k (∅ : Finset (Lattice n)) ⟶ «Σ».fanScheme k =>
      f («Σ».fanChartGenericPoint k «Σ».zeroConeIndex))
    («Σ».torusOpenMap_chart k s)
  exact (congrArg (fun z : coneChart k s.val => «Σ».fanChartMap k s z) hface).symm.trans h

theorem fanGenericPoint_isGenericPoint : IsGenericPoint («Σ».fanGenericPoint k) Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x hx
  obtain ⟨s, y, rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  have hclosed : IsClosed ((«Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k}) :=
    isClosed_closure.preimage («Σ».fanChartMap k s).continuous
  have hmem : «Σ».fanChartGenericPoint k s ∈
      («Σ».fanChartMap k s) ⁻¹' closure {«Σ».fanGenericPoint k} := by
    change «Σ».fanChartMap k s («Σ».fanChartGenericPoint k s) ∈ closure {«Σ».fanGenericPoint k}
    rw [«Σ».fanChartMap_genericPoint]
    exact subset_closure (Set.mem_singleton _)
  exact ((«Σ».fanChartGenericPoint_isGenericPoint k s).mem_closed_set_iff hclosed).mp hmem
    (Set.mem_univ y)

instance fanScheme_irreducibleSpace : IrreducibleSpace («Σ».fanScheme k) :=
  (irreducibleSpace_def _).mpr («Σ».fanGenericPoint_isGenericPoint k).isIrreducible

instance fanScheme_isReduced : IsReduced («Σ».fanScheme k) := by
  letI (i : («Σ».fanSchemeOpenCover k).I₀) :
      IsReduced ((«Σ».fanSchemeOpenCover k).X i) := by
    let s : «Σ».ConeIndex := i
    change IsReduced (coneChart k s.val)
    letI := «Σ».coneChart_isIntegral k s
    infer_instance
  exact IsReduced.of_openCover («Σ».fanScheme k) («Σ».fanSchemeOpenCover k)

instance fanScheme_isIntegral : IsIntegral («Σ».fanScheme k) :=
  isIntegral_of_irreducibleSpace_of_isReduced («Σ».fanScheme k)

/-- The actual open zero-cone chart is dense in the actual glued scheme. -/
theorem torusOpenMap_denseRange : DenseRange («Σ».torusOpenMap k) := by
  intro x
  have hsub : ({«Σ».fanGenericPoint k} : Set («Σ».fanScheme k)) ⊆
      Set.range («Σ».torusOpenMap k) := by
    rintro y rfl
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex, rfl⟩
  have hcl := closure_mono hsub
  rw [(«Σ».fanGenericPoint_isGenericPoint k).def] at hcl
  exact hcl (Set.mem_univ x)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricFanSchemeIntegral
-- END ORIGINAL PaperVerification.ToricFanSchemeIntegral


