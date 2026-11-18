module
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import sunlet.main_dimension
public import sunlet.verified_cyclic_field
public import sunlet.verified_normalized_model

@[expose] public section
set_option Elab.async false

#check "SUNLET_VERIFIEDCYCLICPAPER_IMPORTS_READY"

section Stage_RationalCoordinateProjection


/-!
# Rational coordinate projection and its dense open inverse

Equality of coordinate-generated fields is converted here into actual
rational formulas with coefficients in the original ground field. Their
identities hold in the original affine coordinate ring. A single nonzero
polynomial gives a nonempty dense open set on which the coordinate
projection has the displayed inverse.
-/

noncomputable section
open scoped BigOperators

namespace PolynomialImage

variable {k E I J S : Type*} [Field k] [Field E] [Algebra k E]

/-- Membership in a generated field gives a quotient whose denominator
is genuinely nonzero, including when the element itself is zero. -/
theorem rational_form_of_mem (q : J → E) (x : E)
    (hx : x ∈ IntermediateField.adjoin k (Set.range q)) :
    ∃ N D : MvPolynomial J k,
      MvPolynomial.aeval q D ≠ 0 ∧ x * MvPolynomial.aeval q D = MvPolynomial.aeval q N := by
  by_cases hx0 : x=0
  · exact ⟨0,1,by simp,by simp [hx0]⟩
  · obtain ⟨N,D,h⟩ := (IntermediateField.mem_adjoin_range_iff k q x).mp hx
    have hD : MvPolynomial.aeval q D ≠ 0 := by
      intro hz
      exact hx0 (by simpa only [hz,div_zero] using h)
    exact ⟨N,D,hD,(eq_div_iff hD).mp h⟩

/-- Concrete rational reconstruction identities in the original model
coordinate ring; no generic parameters occur in this structure. -/
structure RationalCoordinateInverse (P : I → MvPolynomial S k) (ρ : J → I) where
  numerator : I → MvPolynomial J k
  denominator : I → MvPolynomial J k
  denominator_not_mem : ∀ i, MvPolynomial.rename ρ (denominator i) ∉ definingIdeal P
  relation_mem : ∀ i,
    MvPolynomial.X i * MvPolynomial.rename ρ (denominator i) -
      MvPolynomial.rename ρ (numerator i) ∈ definingIdeal P

/-- A faithful realization of the model function field transports exact
field-generation equality to rational reconstruction over k itself. -/
def rationalCoordinateInverseOfFieldEquality
    (P : I → MvPolynomial S k) (q : I → E) (ρ : J → I)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P)
    (hfield : IntermediateField.adjoin k (Set.range (q ∘ ρ)) =
      IntermediateField.adjoin k (Set.range q)) : RationalCoordinateInverse P ρ := by
  have hq (i : I) : q i ∈ IntermediateField.adjoin k (Set.range (q ∘ ρ)) := by
    rw [hfield]
    exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
  choose N D hD hND using fun i => rational_form_of_mem (q ∘ ρ) (q i) (hq i)
  refine ⟨N,D,?_,?_⟩
  · intro i hi
    apply hD i
    simpa only [MvPolynomial.aeval_rename] using (hkernel _).mpr hi
  · intro i
    apply (hkernel _).mp
    simp only [map_sub,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_rename]
    exact sub_eq_zero.mpr (hND i)

/-- The original substitution ideal is prime, without an assumed
irreducibility hypothesis. -/
instance definingIdeal_isPrime (P : I → MvPolynomial S k) : (definingIdeal P).IsPrime :=
  RingHom.ker_isPrime (comorphism P)

abbrev OriginalCoordinateRing (P : I → MvPolynomial S k) :=
  MvPolynomial I k ⧸ definingIdeal P

instance originalCoordinateRing_isDomain (P : I → MvPolynomial S k) :
    IsDomain (OriginalCoordinateRing P) := Ideal.Quotient.isDomain _

abbrev OriginalFunctionField (P : I → MvPolynomial S k) :=
  FractionRing (OriginalCoordinateRing P)

def originalCoordinateClass (P : I → MvPolynomial S k) (i : I) : OriginalFunctionField P :=
  algebraMap (OriginalCoordinateRing P) (OriginalFunctionField P)
    (Ideal.Quotient.mk (definingIdeal P) (MvPolynomial.X i))

def genericCoordinateRingEquiv (P : I → MvPolynomial S k) (q : I → E)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P) :
    OriginalCoordinateRing P ≃ₐ[k] Algebra.adjoin k (Set.range q) :=
  (Ideal.quotientEquivAlgOfEq k (by ext f; exact (hkernel f).symm)).trans
    ((Ideal.quotientKerEquivRange (MvPolynomial.aeval q)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval k q).symm))

open scoped IntermediateField.algebraAdjoinAdjoin

def genericFunctionFieldEquiv (P : I → MvPolynomial S k) (q : I → E)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P) :
    OriginalFunctionField P ≃ₐ[k] IntermediateField.adjoin k (Set.range q) :=
  IsFractionRing.algEquivOfAlgEquiv (genericCoordinateRingEquiv P q hkernel)

@[simp] theorem genericFunctionFieldEquiv_coordinate
    (P : I → MvPolynomial S k) (q : I → E)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P) (i : I) :
    (genericFunctionFieldEquiv P q hkernel (originalCoordinateClass P i) : E)=q i := by
  rw [genericFunctionFieldEquiv,originalCoordinateClass,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [genericCoordinateRingEquiv,Ideal.quotientKerEquivRange]

theorem projection_generic_equation_iff
    (P : I → MvPolynomial S k) (q : I → E) (ρ : J → I)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P) (f : MvPolynomial J k) :
    MvPolynomial.aeval (q ∘ ρ) f=0 ↔ f ∈ definingIdeal (P ∘ ρ) := by
  simpa only [definingIdeal,RingHom.mem_ker,comorphism,MvPolynomial.aeval_rename]
    using hkernel (MvPolynomial.rename ρ f)

/-- The natural pullback on function fields of the coordinate projection
is an isomorphism, expressed between the two actual substitution quotients. -/
def projectionFunctionFieldEquiv
    (P : I → MvPolynomial S k) (q : I → E) (ρ : J → I)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P)
    (hfield : IntermediateField.adjoin k (Set.range (q ∘ ρ)) =
      IntermediateField.adjoin k (Set.range q)) :
    OriginalFunctionField (P ∘ ρ) ≃ₐ[k] OriginalFunctionField P :=
  (genericFunctionFieldEquiv (P ∘ ρ) (q ∘ ρ)
    (projection_generic_equation_iff P q ρ hkernel)).trans
      ((IntermediateField.equivOfEq hfield).trans (genericFunctionFieldEquiv P q hkernel).symm)

/-- Compatibility with every observed coordinate identifies this field
isomorphism as the pullback of the displayed coordinate projection. -/
theorem projectionFunctionFieldEquiv_coordinate
    (P : I → MvPolynomial S k) (q : I → E) (ρ : J → I)
    (hkernel : ∀ f : MvPolynomial I k,
      MvPolynomial.aeval q f=0 ↔ f ∈ definingIdeal P)
    (hfield : IntermediateField.adjoin k (Set.range (q ∘ ρ)) =
      IntermediateField.adjoin k (Set.range q)) (j : J) :
    projectionFunctionFieldEquiv P q ρ hkernel hfield
      (originalCoordinateClass (P ∘ ρ) j) = originalCoordinateClass P (ρ j) := by
  apply (genericFunctionFieldEquiv P q hkernel).injective
  apply Subtype.ext
  simp only [projectionFunctionFieldEquiv,AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply,genericFunctionFieldEquiv_coordinate]
  change (genericFunctionFieldEquiv (P ∘ ρ) (q ∘ ρ)
    (projection_generic_equation_iff P q ρ hkernel)
      (originalCoordinateClass (P ∘ ρ) j) : E) = q (ρ j)
  exact genericFunctionFieldEquiv_coordinate (P ∘ ρ) (q ∘ ρ)
    (projection_generic_equation_iff P q ρ hkernel) j

namespace RationalCoordinateInverse

variable {P : I → MvPolynomial S k} {ρ : J → I} (R : RationalCoordinateInverse P ρ)

/-- The actual rational inverse as a vector of quotients. -/
def inverse (y : J → k) : I → k :=
  fun i => MvPolynomial.aeval y (R.numerator i) / MvPolynomial.aeval y (R.denominator i)

theorem inverse_projection (x : I → k) (hx : x ∈ closure P)
    (hden : ∀ i, MvPolynomial.aeval (x ∘ ρ) (R.denominator i) ≠ 0) :
    R.inverse (x ∘ ρ) = x := by
  funext i
  apply (div_eq_iff (hden i)).mpr
  have h := hx _ (R.relation_mem i)
  simp only [map_sub,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_rename] at h
  exact (sub_eq_zero.mp h).symm

section Finite

variable [Fintype I]

def commonDenominator : MvPolynomial J k := ∏ i, R.denominator i

theorem commonDenominator_not_mem :
    MvPolynomial.rename ρ R.commonDenominator ∉ definingIdeal P := by
  intro h
  have hzero : comorphism P (MvPolynomial.rename ρ R.commonDenominator)=0 := h
  have hne : comorphism P (MvPolynomial.rename ρ R.commonDenominator) ≠ 0 := by
    unfold commonDenominator
    simp only [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => R.denominator_not_mem i
  exact hne hzero

/-- A principal open subset of the literal affine model. -/
def inverseOpen : Set (I → k) :=
  {x | x ∈ closure P ∧ MvPolynomial.aeval (x ∘ ρ) R.commonDenominator ≠ 0}

theorem inverse_projection_on_open (x : I → k) (hx : x ∈ R.inverseOpen) :
    R.inverse (x ∘ ρ) = x := by
  apply R.inverse_projection x hx.1
  intro i
  have h := hx.2
  simp only [commonDenominator,map_prod] at h
  exact (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)

theorem projection_injective_on_open :
    Set.InjOn (fun x : I → k => x ∘ ρ) R.inverseOpen := by
  intro x hx y hy h
  calc
    x = R.inverse (x ∘ ρ) := (R.inverse_projection_on_open x hx).symm
    _ = R.inverse (y ∘ ρ) := congrArg R.inverse h
    _ = y := R.inverse_projection_on_open y hy

variable [Infinite k]

/-- Algebraic density, stated as equality of the full vanishing ideals. -/
theorem inverseOpen_vanishingIdeal :
    MvPolynomial.vanishingIdeal k R.inverseOpen = definingIdeal P := by
  apply le_antisymm
  · intro f hf
    have hprod : f * MvPolynomial.rename ρ R.commonDenominator ∈ definingIdeal P := by
      rw [← vanishingIdeal_imageClosure P]
      intro x hx
      rw [map_mul,MvPolynomial.aeval_rename]
      by_cases hD : MvPolynomial.aeval (x ∘ ρ) R.commonDenominator=0
      · rw [hD,mul_zero]
      · rw [hf x ⟨hx,hD⟩,zero_mul]
    exact ((RingHom.ker_isPrime (comorphism P)).mem_or_mem hprod).resolve_right
      R.commonDenominator_not_mem
  · intro f hf x hx
    exact hx.1 f hf

/-- Equivalently, the Zariski closure of the inverse's domain is the
entire original affine image closure. -/
theorem inverseOpen_dense :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k R.inverseOpen) = closure P := by
  rw [R.inverseOpen_vanishingIdeal]
  rfl

theorem inverseOpen_nonempty : R.inverseOpen.Nonempty := by
  by_contra he
  have hempty : R.inverseOpen=∅ := Set.not_nonempty_iff_eq_empty.mp he
  have htop : definingIdeal P=⊤ := by
    rw [← R.inverseOpen_vanishingIdeal,hempty,MvPolynomial.vanishingIdeal_empty]
  exact (RingHom.ker_isPrime (comorphism P)).ne_top htop

end Finite
end RationalCoordinateInverse
end PolynomialImage
end
end Stage_RationalCoordinateProjection
#check "SUNLET_VERIFIEDCYCLICPAPER_RationalCoordinateProjection_DONE"

section Stage_CyclicNormalizedRecovery


/-!
# The complete cyclic coordinate projection

This restores all diagonal coordinates, transfers the off-diagonal field
reconstruction to the original model, and supplies a rational inverse on
a nonempty dense principal open set. Every rational formula is defined
over the given characteristic-zero field, in particular over ℚ.
-/

noncomputable section

namespace Sunlet.CyclicSelectedField

open ToricPairAlgebra

set_option backward.isDefEq.respectTransparency false

variable {k : Type*} [Field k] [hchar : CharZero k] (m : ℕ) [NeZero m]

abbrev cyclicLatin : NormalizedLatinSystem (ZMod m) (ZMod m) :=
  GroupCoordinates.translationLatinSystem

/-- The literal iterated rational field, definitionally equal to the normalized source. -/
abbrev NormalizedFullField :=
  RationalBaseChange.ExtendedField (E := FullField (k := k) m) (J := ZMod m)

theorem normalizedFullField_eq :
    NormalizedFullField (k := k) m =
      (cyclicLatin m).NormalizedSourceField (k := k) (0 : ZMod m) := rfl

def normalizedCoordinates : ZMod m × ZMod m → NormalizedFullField (k := k) m :=
  Normalization.parameterMap (cyclicLatin m).perm
    ((cyclicLatin m).genericNormalizedParameters (k := k) 0)

def observedNormalizedCoordinates (hm : 6 ≤ m) :
    FullObserved m hm → NormalizedFullField (k := k) m :=
  normalizedCoordinates m ∘ fullObservationIndex m hm

abbrev ObservedNormalizedField (hm : 6 ≤ m) :=
  IntermediateField.adjoin k (Set.range (observedNormalizedCoordinates (k := k) m hm))

theorem cyclic_nonidentityPerm :
    (cyclicLatin m).nonidentityPerm = permutation m := by
  funext a
  ext x
  rfl

@[simp] theorem normalized_coordinate_zero (x : ZMod m) :
    normalizedCoordinates (k := k) m (0,x) =
      RationalBaseChange.diagonal (E := FullField (k := k) m) x := by
  have h := congrFun ((cyclicLatin m).generic_normalized_coordinates (k := k) 0) (Sum.inl x)
  exact h

@[simp] theorem normalized_coordinate_nonzero (a : Color m) (x : ZMod m) :
    normalizedCoordinates (k := k) m (a.val,x) =
      RationalBaseChange.diagonal (E := FullField (k := k) m) (a.val+x) *
        algebraMap (FullField (k := k) m) (NormalizedFullField (k := k) m)
          (genericCoordinates (k := k) 0 (permutation m) (a,x)) := by
  have h := congrFun ((cyclicLatin m).generic_normalized_coordinates (k := k) 0) (Sum.inr (a,x))
  simp only [Function.comp_apply,NormalizedLatinSystem.normalizedCoordinateIndex,
    Equiv.coe_fn_mk,RationalBaseChange.coordinates,cyclic_nonidentityPerm,
    permutation,Equiv.coe_addLeft] at h
  convert h using 1 <;> rfl

theorem diagonal_mem_observedNormalized (hm : 6 ≤ m) (x : ZMod m) :
    RationalBaseChange.diagonal (E := FullField (k := k) m) x ∈
      ObservedNormalizedField (k := k) m hm := by
  rw [← normalized_coordinate_zero (k := k) m x]
  exact IntermediateField.subset_adjoin k _ ⟨Sum.inl x,rfl⟩

theorem observed_coordinate_mem_observedNormalized (hm : 6 ≤ m) (ax : Observed m hm) :
    algebraMap (FullField (k := k) m) (NormalizedFullField (k := k) m)
      (observedCoordinates (k := k) m hm ax) ∈ ObservedNormalizedField (k := k) m hm := by
  have h := (ObservedNormalizedField (k := k) m hm).div_mem
    (IntermediateField.subset_adjoin k _
      (show observedNormalizedCoordinates (k := k) m hm (.inr ax) ∈
        Set.range (observedNormalizedCoordinates (k := k) m hm) from ⟨.inr ax,rfl⟩))
    (diagonal_mem_observedNormalized (k := k) m hm (ax.val.1.val+ax.val.2))
  simpa only [observedNormalizedCoordinates,Function.comp_apply,fullObservationIndex,
    normalized_coordinate_nonzero,observedCoordinates,
    mul_div_cancel_left₀ _ (RationalBaseChange.diagonal_ne_zero
      (E := FullField (k := k) m) (ax.val.1.val+ax.val.2)),Prod.eta] using h

theorem observed_field_mem_observedNormalized (hm : 6 ≤ m)
    (x : ObservedField (k := k) m hm) :
    algebraMap (FullField (k := k) m) (NormalizedFullField (k := k) m) x.val ∈
      ObservedNormalizedField (k := k) m hm := by
  refine IntermediateField.adjoin_induction k
    (motive := fun x _ => algebraMap (FullField (k := k) m)
      (NormalizedFullField (k := k) m) x ∈ ObservedNormalizedField (k := k) m hm)
    ?_ ?_ ?_ ?_ ?_ x.property
  · rintro _ ⟨i,rfl⟩
    exact observed_coordinate_mem_observedNormalized m hm i
  · intro c
    rw [← IsScalarTower.algebraMap_apply k (FullField (k := k) m) (NormalizedFullField (k := k) m)]
    exact (ObservedNormalizedField (k := k) m hm).algebraMap_mem c
  · intro a b _ _ ha hb
    simpa only [map_add] using (ObservedNormalizedField (k := k) m hm).add_mem ha hb
  · intro a _ ha
    simpa only [map_inv₀] using (ObservedNormalizedField (k := k) m hm).inv_mem ha
  · intro a b _ _ ha hb
    simpa only [map_mul] using (ObservedNormalizedField (k := k) m hm).mul_mem ha hb

/-- Every literal normalized coordinate, including the zero row, belongs
to the field generated by precisely the paper's retained coordinates. -/
theorem normalized_coordinate_mem_observed (hm : 6 ≤ m) (ab : ZMod m × ZMod m) :
    normalizedCoordinates (k := k) m ab ∈ ObservedNormalizedField (k := k) m hm := by
  rcases ab with ⟨a,b⟩
  by_cases ha : a=0
  · subst a
    rw [normalized_coordinate_zero]
    exact diagonal_mem_observedNormalized m hm b
  · rw [normalized_coordinate_nonzero m ⟨a,ha⟩ b]
    exact (ObservedNormalizedField (k := k) m hm).mul_mem
      (diagonal_mem_observedNormalized m hm (a+b))
      (observed_field_mem_observedNormalized m hm
        ⟨genericCoordinates (k := k) 0 (permutation m) (⟨a,ha⟩,b),
          full_coordinate_mem_observed m hm (⟨a,ha⟩,b)⟩)

theorem observedNormalizedField_eq_modelImageField (hm : 6 ≤ m) :
    ObservedNormalizedField (k := k) m hm =
      (cyclicLatin m).NormalizedImageField (k := k) 0 := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ax,rfl⟩
    exact IntermediateField.subset_adjoin k _ ⟨fullObservationIndex m hm ax,rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ab,rfl⟩
    exact normalized_coordinate_mem_observed m hm ab

/-- The coordinate projection induces an isomorphism of the actual
function fields, obtained from the two original substitution quotients. -/
def originalProjectionFieldEquiv (hm : 6 ≤ m) :
    PolynomialImage.OriginalFunctionField
      (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)) ∘
        fullObservationIndex m hm) ≃ₐ[k]
      PolynomialImage.OriginalFunctionField
        (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m))) :=
  PolynomialImage.projectionFunctionFieldEquiv
    (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)))
    (normalizedCoordinates (k := k) m) (fullObservationIndex m hm)
    (fun f => (cyclicLatin m).generic_normalized_equation_iff (k := k) 0 f)
    (observedNormalizedField_eq_modelImageField (k := k) m hm)

@[simp] theorem originalProjectionFieldEquiv_coordinate (hm : 6 ≤ m)
    (j : FullObserved m hm) :
    originalProjectionFieldEquiv (k := k) m hm
      (PolynomialImage.originalCoordinateClass
        (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)) ∘
          fullObservationIndex m hm) j) =
      PolynomialImage.originalCoordinateClass
        (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)))
        (fullObservationIndex m hm j) :=
  PolynomialImage.projectionFunctionFieldEquiv_coordinate _ _ _ _ _ j

/-- A rational inverse over the ground field for the original, unnormalized
polynomial model and the exact coordinate projection in Theorem 6.1. -/
def originalModelRationalInverse (hm : 6 ≤ m) :
    PolynomialImage.RationalCoordinateInverse
      (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)))
      (fullObservationIndex m hm) :=
  PolynomialImage.rationalCoordinateInverseOfFieldEquality
    (Sunlet.coordinatePolynomial (K := k) (addTranslationPerm (G := ZMod m)))
    (normalizedCoordinates (k := k) m) (fullObservationIndex m hm)
    (fun f => (cyclicLatin m).generic_normalized_equation_iff (k := k) 0 f)
    (observedNormalizedField_eq_modelImageField (k := k) m hm)

include hchar in
/-- The complete birational coordinate-projection claim: the coordinates
are exactly the displayed ones, there are 8m−12 distinct observations,
and rational reconstruction holds on a nonempty dense open of the full
original six-family model. The density and inverse identities are
expressed explicitly, without an assumed generic-identifiability axiom. -/
theorem paper_theorem_6_1 (hm : 6 ≤ m) :
    Fintype.card (FullObserved m hm) = 8*m-12 ∧
    Function.Injective (fullObservationIndex m hm) ∧
    Set.range (fullObservationIndex m hm) = {ab | LiteralRetained m ab} ∧
    let R := originalModelRationalInverse (k := k) m hm
    R.inverseOpen.Nonempty ∧
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k R.inverseOpen) =
      GroupCoordinates.imageClosure (K := k) (G := ZMod m) ∧
    ∀ x ∈ R.inverseOpen, R.inverse (x ∘ fullObservationIndex m hm) = x := by
  refine ⟨fullObserved_card m hm,fullObservationIndex_injective m hm,
    fullObservationIndex_range m hm,?_,?_,?_⟩
  · exact (originalModelRationalInverse (k := k) m hm).inverseOpen_nonempty
  · rw [(originalModelRationalInverse (k := k) m hm).inverseOpen_dense,
      GroupCoordinates.imageClosure_eq_fiveFamily]
    rfl
  · exact (originalModelRationalInverse (k := k) m hm).inverse_projection_on_open

/-- The retained indices in the manuscript's constrained triple notation. -/
def fullObservationFlowIndex (hm : 6 ≤ m) :
    FullObserved m hm → GroupCoordinates.FlowIndex (ZMod m) :=
  GroupCoordinates.flowIndexEquiv.symm ∘ fullObservationIndex m hm

theorem fullObservationFlowIndex_injective (hm : 6 ≤ m) :
    Function.Injective (fullObservationFlowIndex m hm) :=
  GroupCoordinates.flowIndexEquiv.symm.injective.comp (fullObservationIndex_injective m hm)

theorem fullObservationFlowIndex_range (hm : 6 ≤ m) :
    Set.range (fullObservationFlowIndex m hm) =
      {abc | LiteralRetained m (GroupCoordinates.flowIndexEquiv abc)} := by
  ext abc
  constructor
  · rintro ⟨j,rfl⟩
    have h : fullObservationIndex m hm j ∈ Set.range (fullObservationIndex m hm) := ⟨j,rfl⟩
    rw [fullObservationIndex_range m hm] at h
    change LiteralRetained m (GroupCoordinates.flowIndexEquiv
      (fullObservationFlowIndex m hm j))
    change LiteralRetained m (fullObservationIndex m hm j) at h
    simpa only [fullObservationFlowIndex,Function.comp_apply,Equiv.apply_symm_apply] using h
  · intro h
    have hr : GroupCoordinates.flowIndexEquiv abc ∈ Set.range (fullObservationIndex m hm) := by
      rw [fullObservationIndex_range m hm]
      exact h
    obtain ⟨j,hj⟩ := hr
    refine ⟨j,?_⟩
    simp only [fullObservationFlowIndex,Function.comp_apply,hj,Equiv.symm_apply_apply]

/-- Exact agreement with all six original Fourier edge families, before
passing to closures or excluding any parameter values. -/
theorem observed_original_triples (hm : 6 ≤ m)
    (w : GroupCoordinates.Parameters (K := k) (G := ZMod m)) :
    GroupCoordinates.tripleParameterMap w ∘ fullObservationFlowIndex m hm =
      GroupCoordinates.parameterMap w ∘ fullObservationIndex m hm := by
  funext j
  rw [GroupCoordinates.tripleParameterMap_eq]
  simp only [fullObservationFlowIndex,Function.comp_apply,Equiv.apply_symm_apply]

/-- The same rational reconstruction in constrained triple coordinates. -/
theorem original_flow_reconstruction (hm : 6 ≤ m)
    (q : GroupCoordinates.FlowIndex (ZMod m) → k)
    (hq : q ∘ GroupCoordinates.flowIndexEquiv.symm ∈
      (originalModelRationalInverse (k := k) m hm).inverseOpen) :
    (originalModelRationalInverse (k := k) m hm).inverse
      (q ∘ fullObservationFlowIndex m hm) ∘ GroupCoordinates.flowIndexEquiv = q := by
  have h := (originalModelRationalInverse (k := k) m hm).inverse_projection_on_open
    (q ∘ GroupCoordinates.flowIndexEquiv.symm) hq
  funext abc
  have he := congrFun h (GroupCoordinates.flowIndexEquiv abc)
  simpa only [fullObservationFlowIndex,Function.comp_assoc,Function.comp_apply,
    Equiv.symm_apply_apply] using he

end Sunlet.CyclicSelectedField
end
end Stage_CyclicNormalizedRecovery
#check "SUNLET_VERIFIEDCYCLICPAPER_CyclicNormalizedRecovery_DONE"

section Stage_CyclicPaperTheorem


/-!
# Theorem 6.1 with exactly the manuscript's numerical hypothesis

The auxiliary ZMod instance asserting m ≠ 0 is derived from m ≥ 6 here.
The function-field isomorphism is over ℚ and preserves every observed
coordinate. The dense-open reconstruction statement uses the original
six-family image closure.
-/

noncomputable section

namespace Sunlet.CyclicSelectedField

/-- The coordinate projection of Theorem 6.1 is birational over ℚ,
with no nonzero-modulus hypothesis beyond the displayed bound m ≥ 6. -/
def paper_projectionFunctionFieldEquiv (m : ℕ) (hm : 6 ≤ m) :
    letI : NeZero m := ⟨by omega⟩
    PolynomialImage.OriginalFunctionField
      (Sunlet.coordinatePolynomial (K := ℚ) (addTranslationPerm (G := ZMod m)) ∘
        fullObservationIndex m hm) ≃ₐ[ℚ]
      PolynomialImage.OriginalFunctionField
        (Sunlet.coordinatePolynomial (K := ℚ) (addTranslationPerm (G := ZMod m))) := by
  letI : NeZero m := ⟨by omega⟩
  exact originalProjectionFieldEquiv (k := ℚ) m hm

/-- All orders m ≥ 6, precisely the literal observations, and rational
reconstruction on a nonempty dense open of the original full model. -/
theorem paper_theorem_6_1_all_orders {k : Type*} [Field k] [CharZero k]
    (m : ℕ) (hm : 6 ≤ m) :
    letI : NeZero m := ⟨by omega⟩
    Fintype.card (FullObserved m hm) = 8*m-12 ∧
    Function.Injective (fullObservationIndex m hm) ∧
    Set.range (fullObservationIndex m hm) = {ab | LiteralRetained m ab} ∧
    let R := originalModelRationalInverse (k := k) m hm
    R.inverseOpen.Nonempty ∧
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k R.inverseOpen) =
      GroupCoordinates.imageClosure (K := k) (G := ZMod m) ∧
    ∀ x ∈ R.inverseOpen, R.inverse (x ∘ fullObservationIndex m hm) = x := by
  letI : NeZero m := ⟨by omega⟩
  exact paper_theorem_6_1 (k := k) m hm

end Sunlet.CyclicSelectedField
end
end Stage_CyclicPaperTheorem
#check "SUNLET_VERIFIEDCYCLICPAPER_CyclicPaperTheorem_DONE"

#check Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv
#print axioms Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv

#check Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders
#print axioms Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders

#check Sunlet.CyclicSelectedField.observed_original_triples
#print axioms Sunlet.CyclicSelectedField.observed_original_triples

#check Sunlet.CyclicSelectedField.original_flow_reconstruction
#print axioms Sunlet.CyclicSelectedField.original_flow_reconstruction
