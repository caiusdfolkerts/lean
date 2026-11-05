module

public import Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.HasLimits

public import Continuation.Runtime.ToricOpenRestriction
public import Continuation.Runtime.UnrestrictedAffineCharacters
public import Continuation.Runtime.DominantRegularSectionNaturality

/-!
# The actual coordinate algebra of an invariant affine chart

The subalgebra consists literally of Laurent polynomials whose original
rational functions are regular on the given open.  The actual coordinate
ring is proved isomorphic to this subalgebra.  Full group-scheme invariance
and the already checked torus-product regularity theorem imply stability
under every individual character component, over arbitrary fields.

Consequently the affine chart is its actual finitely generated saturated
character-semigroup algebra, and that semigroup generates the entire
original character lattice as a group.  Invertible characters are retained;
pointedness and a full-dimensional cone are not assumed.

This is an uncompiled source candidate.  Cone reconstruction and the
identification of actual overlaps remain separate obligations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [IsNoetherian X.left] [Smooth X.hom]
    [X.left.IsSeparated]
    (T : SplitToricEmbedding k n X)
    (U : X.left.Opens) [Nonempty U]

local instance invariantAffineBaseSmooth : Smooth (X.left ↘ Spec (CommRingCat.of k)) :=
  inferInstanceAs (Smooth X.hom)

/-- Every nonempty invariant open contains the whole original torus. -/
theorem torusOpen_le_of_invariant
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) : T.torusOpen ≤ U := by
  have h := T.torusOpen_subset_saturation U
  have he : GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) = U :=
    GroupAction.saturation_eq_of_invariant _ _ _ (congrArg SetLike.coe hInv)
  rwa [he] at h

/-- The actual Laurent polynomials regular on the original open. -/
def invariantAffineCharacterAlgebra : Subalgebra k (torusCoordinateRing k n) :=
  (BaseSections.regularValueAlgHom k U).range.comap
    (openTorusRationalAlgHom k n X.left T.torus.left)

theorem mem_invariantAffineCharacterAlgebra (f : torusCoordinateRing k n) :
    f ∈ T.invariantAffineCharacterAlgebra U ↔
      ∃ r : Γ(X.left,U), X.left.germToFunctionField U r =
        openTorusRationalAlgHom k n X.left T.torus.left f := Iff.rfl

/-- Restriction from an open containing the torus gives a Laurent
polynomial, with its original rational function unchanged. -/
theorem regularValue_mem_torus_range (hT : T.torusOpen ≤ U)
    (r : Γ(X.left,U)) :
    BaseSections.regularValueAlgHom k U r ∈
      (openTorusRationalAlgHom k n X.left T.torus.left).range := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  letI : Nonempty T.torusOpen :=
    ⟨⟨T.torus.left (genericPoint (splitTorus k (Fin n → ℤ))),⟨_,rfl⟩⟩⟩
  have hrange : Set.range (openTorusRationalAlgHom k n X.left T.torus.left) =
      Set.range (X.left.germToFunctionField T.torusOpen) := by
    change Set.range (affineOpenCoordinateMap R T.torus.left) = _
    have h := affineOpenCoordinate_range R T.torus.left
    have hRange {V W : X.left.Opens} [Nonempty V] [Nonempty W] (e : V = W) :
        Set.range (X.left.germToFunctionField V) = Set.range (X.left.germToFunctionField W) := by
      subst W
      rfl
    letI : Nonempty (T.torus.left ''ᵁ (⊤ : (splitTorusOver k (Fin n → ℤ)).left.Opens)) := openImmersion_image_nonempty T.torus.left ⊤
    exact h.trans (hRange (Scheme.Hom.image_top_eq_opensRange _))
  change X.left.germToFunctionField U r ∈
    Set.range (openTorusRationalAlgHom k n X.left T.torus.left)
  rw [hrange]
  exact ⟨X.left.presheaf.map (homOfLE hT).op r,
    germToFunctionField_restrict X.left (homOfLE hT) r⟩

/-- The actual restriction homomorphism to Laurent coordinates, obtained
by inverting the proved injective coordinate embedding on its range. -/
def invariantAffineLaurentHom (hT : T.torusOpen ≤ U) :
    Γ(X.left,U) →ₐ[k] torusCoordinateRing k n :=
  (AlgEquiv.ofInjective (openTorusRationalAlgHom k n X.left T.torus.left)
    (openTorusRationalAlgHom_injective k n X.left T.torus.left)).symm.toAlgHom.comp
      ((BaseSections.regularValueAlgHom k U).codRestrict _
        (T.regularValue_mem_torus_range U hT))

theorem invariantAffineLaurentHom_value (hT : T.torusOpen ≤ U)
    (r : Γ(X.left,U)) :
    openTorusRationalAlgHom k n X.left T.torus.left
        (T.invariantAffineLaurentHom U hT r) = X.left.germToFunctionField U r := by
  let e := AlgEquiv.ofInjective (openTorusRationalAlgHom k n X.left T.torus.left)
    (openTorusRationalAlgHom_injective k n X.left T.torus.left)
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨BaseSections.regularValueAlgHom k U r,T.regularValue_mem_torus_range U hT r⟩)

theorem invariantAffineLaurentHom_injective (hT : T.torusOpen ≤ U) :
    Function.Injective (T.invariantAffineLaurentHom U hT) := by
  intro r s hrs
  apply X.left.germToFunctionField_injective U
  rw [← T.invariantAffineLaurentHom_value U hT r,
    ← T.invariantAffineLaurentHom_value U hT s,hrs]

/-- The whole coordinate ring, not a chosen subring of its functions,
is isomorphic to the actual Laurent character subalgebra. -/
def invariantAffineCoordinateEquiv (hT : T.torusOpen ≤ U) :
    Γ(X.left,U) ≃ₐ[k] T.invariantAffineCharacterAlgebra U :=
  AlgEquiv.ofBijective
    ((T.invariantAffineLaurentHom U hT).codRestrict _ (fun r =>
      ⟨r,(T.invariantAffineLaurentHom_value U hT r).symm⟩))
    ⟨fun r s h => T.invariantAffineLaurentHom_injective U hT (congrArg Subtype.val h),by
      rintro ⟨f,r,hr⟩
      refine ⟨r,Subtype.ext ?_⟩
      apply openTorusRationalAlgHom_injective k n X.left T.torus.left
      exact (T.invariantAffineLaurentHom_value U hT r).trans hr⟩

theorem invariantAffineCoordinateEquiv_value (hT : T.torusOpen ≤ U)
    (r : Γ(X.left,U)) :
    openTorusRationalAlgHom k n X.left T.torus.left
        (T.invariantAffineCoordinateEquiv U hT r).val = X.left.germToFunctionField U r :=
  T.invariantAffineLaurentHom_value U hT r

/-- Every Laurent component is regular on the same actual invariant
affine open.  The proof uses coefficient extraction on the actual product
scheme, including over finite fields. -/
theorem invariantAffineCharacterAlgebra_component
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U)
    (f : torusCoordinateRing k n) (hf : f ∈ T.invariantAffineCharacterAlgebra U)
    (m : Fin n → ℤ) :
    AddMonoidAlgebra.single m (f.coeff m) ∈ T.invariantAffineCharacterAlgebra U := by
  let G := splitTorusOver k (Fin n → ℤ)
  let A := torusCoordinateRing k n
  let p := (snd G X).left
  let a := (γ[G,X]).left
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  let w : A ⊗[k] X.left.functionField :=
    Algebra.TensorProduct.map (AlgHom.id k A) value (Coalgebra.comul (R := k) f)
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  obtain ⟨r,hr⟩ := hf
  have hregular : torusProductRationalMap k n X w ∈
      Set.range ((G ⊗ X).left.germToFunctionField (p ⁻¹ᵁ U)) := by
    refine ⟨a.appLE U (p ⁻¹ᵁ U) hInv.ge r,?_⟩
    erw [dominantFunctionFieldMap_appLE_value,hr]
    exact T.action_pullback_laurent f
  have hw := (torusProductRationalMap_mem_regularAffine_iff k n X U hU w).mp hregular
  have hc := characterCoefficient_mem_range k
    (BaseSections.regularValueAlgHom k U).toLinearMap m w hw
  have he : characterCoefficient k m w =
      value (AddMonoidAlgebra.single m (f.coeff m)) := by
    change characterCoefficient k m
      (TensorProduct.map (LinearMap.id : A →ₗ[k] A) value.toLinearMap
        (Coalgebra.comul (R := k) f)) = _
    rw [characterCoefficient_map,characterCoefficient_comul]
    rfl
  rw [he] at hc
  exact hc

theorem invariantAffineCharacterAlgebra_stable
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) :
    IsCharacterStable k (T.invariantAffineCharacterAlgebra U).toSubmodule :=
  (isCharacterStable_iff_components k _).mpr
    (T.invariantAffineCharacterAlgebra_component U hU hInv)

/-- The original full character lattice is retained as the ambient
group, including all characters which are units on this chart. -/
def invariantAffineExponentMonoid : AddSubmonoid (Fin n → ℤ) :=
  affineExponentMonoid k (T.invariantAffineCharacterAlgebra U)

theorem invariantAffineExponentMonoid_fg
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) :
    (T.invariantAffineExponentMonoid U).FG := by
  letI : Algebra.FiniteType k Γ(X.left,U) :=
    RingHom.finiteType_algebraMap.mp (BaseSections.scalarMap_finiteType k U hU)
  let e := T.invariantAffineCoordinateEquiv U (T.torusOpen_le_of_invariant U hInv)
  letI : Algebra.FiniteType k (T.invariantAffineCharacterAlgebra U) :=
    Algebra.FiniteType.equiv inferInstance e
  exact affineExponentMonoid_finitelyGenerated k _
    (T.invariantAffineCharacterAlgebra_stable U hU hInv)

/-- Saturation and generation of the full lattice are consequences of
the original smooth affine ring and its actual function field. -/
theorem invariantAffineExponentMonoid_saturated_and_groupClosure
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) :
    (∀ (m : Fin n → ℤ) (N : ℕ), 0 < N → N • m ∈ T.invariantAffineExponentMonoid U →
      m ∈ T.invariantAffineExponentMonoid U) ∧
    AddSubgroup.closure (T.invariantAffineExponentMonoid U : Set (Fin n → ℤ)) = ⊤ := by
  let A := T.invariantAffineCharacterAlgebra U
  let R := torusCoordinateRing k n
  let K := X.left.functionField
  let hT := T.torusOpen_le_of_invariant U hInv
  let e : Γ(X.left,U) ≃ₐ[k] A := T.invariantAffineCoordinateEquiv U hT
  let value : R →ₐ[k] K := openTorusRationalAlgHom k n X.left T.torus.left
  letI : Algebra R K := value.toRingHom.toAlgebra
  letI : Algebra A K := (value.comp A.val).toRingHom.toAlgebra
  letI : SMul A K := (inferInstance : Algebra A K).toSMul
  letI : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsFractionRing Γ(X.left,U) K :=
    functionField_isFractionRing_of_isAffineOpen X.left U hU
  letI : IsFractionRing A K := IsFractionRing.of_ringEquiv_left e.symm.toRingEquiv (by
    intro b
    have hb := T.invariantAffineCoordinateEquiv_value U hT (e.symm b)
    change value (e (e.symm b)) = _ at hb
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb)
  letI : IsIntegrallyClosed Γ(X.left,U) := smooth_affineOpen_isIntegrallyClosed X.hom U hU
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have hinj : Function.Injective (algebraMap R K) :=
    openTorusRationalAlgHom_injective k n X.left T.torus.left
  have hstable : IsCharacterStable k A.toSubmodule :=
    T.invariantAffineCharacterAlgebra_stable U hU hInv
  refine ⟨?_,affineExponentMonoid_groupClosure k A hstable K hinj⟩
  intro m N hN hm
  exact affineExponentMonoid_saturated k A K hinj m hN hm

/-- The actual affine chart is the spectrum of its recovered character
semigroup algebra.  The algebra maps used in this isomorphism are the
literal regular-function and original Laurent embeddings above. -/
def invariantAffineMonoidSchemeIso
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) :
    U.toScheme ≅ Spec (CommRingCat.of
      (AddMonoidAlgebra k (T.invariantAffineExponentMonoid U))) :=
  hU.isoSpec ≪≫ Scheme.Spec.mapIso
    (((invariantAffineSemigroupEquiv k (T.invariantAffineCharacterAlgebra U)
      (T.invariantAffineCharacterAlgebra_stable U hU hInv)).trans
        (T.invariantAffineCoordinateEquiv U (T.torusOpen_le_of_invariant U hInv)).symm).toRingEquiv.toCommRingCatIso.op)


/-- Ordinary smoothness of the original scheme is smoothness of the
literal coordinate algebra with its actual base-field map. -/
theorem invariantAffineCharacterAlgebra_smooth
    (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U) :
    Algebra.Smooth k (T.invariantAffineCharacterAlgebra U) := by
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left,U)))) := by
    change Smooth (Spec.map (CommRingCat.ofHom (BaseSections.scalarMap k X.left U)))
    rw [← affineOpen_fromSpec_toBase k X.left U hU]
    infer_instance
  letI : Algebra.Smooth k Γ(X.left,U) :=
    RingHom.smooth_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k Γ(X.left,U)))).mp inferInstance)
  exact Algebra.Smooth.of_equiv (T.invariantAffineCoordinateEquiv U hT)

/-- An actual invariant affine open of the original smooth toric scheme
is a coordinate-cone character algebra in the original lattice. This
allows every possible rank of torus factor. -/
theorem invariantAffineCharacterAlgebra_coordinateCone
    (hU : IsAffineOpen U)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      T.invariantAffineCharacterAlgebra U =
        monoidChartAlgebra k (coordinateConeMonoid b I) := by
  let A := T.invariantAffineCharacterAlgebra U
  let R := torusCoordinateRing k n
  let K := X.left.functionField
  let hT := T.torusOpen_le_of_invariant U hInv
  let e : Γ(X.left,U) ≃ₐ[k] A := T.invariantAffineCoordinateEquiv U hT
  let value : R →ₐ[k] K := openTorusRationalAlgHom k n X.left T.torus.left
  letI : Algebra R K := value.toRingHom.toAlgebra
  letI : Algebra A K := (value.comp A.val).toRingHom.toAlgebra
  letI : SMul A K := (inferInstance : Algebra A K).toSMul
  letI : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq
    (fun c => (value.commutes c).symm)
  letI : IsFractionRing R K :=
    affineOpenCoordinate_isFractionRing (CommRingCat.of R) T.torus.left
  letI : IsFractionRing Γ(X.left,U) K :=
    functionField_isFractionRing_of_isAffineOpen X.left U hU
  letI : IsFractionRing A K := IsFractionRing.of_ringEquiv_left e.symm.toRingEquiv (by
    intro a
    have ha := T.invariantAffineCoordinateEquiv_value U hT (e.symm a)
    change value (e (e.symm a)) = _ at ha
    rw [AlgEquiv.apply_symm_apply] at ha
    exact ha)
  letI : IsIntegrallyClosed Γ(X.left,U) :=
    smooth_affineOpen_isIntegrallyClosed X.hom U hU
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI : Algebra.Smooth k A := T.invariantAffineCharacterAlgebra_smooth U hU hT
  exact smooth_invariant_affineAlgebra_eq_coordinateCone_unrestricted k A
    (T.invariantAffineCharacterAlgebra_stable U hU hInv) K

end PaperVerification.ToricSchemes.SplitToricEmbedding
end

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantAffineCharacterAlgebra_stable
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantAffineExponentMonoid_fg
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantAffineExponentMonoid_saturated_and_groupClosure
#check PaperVerification.ToricSchemes.SplitToricEmbedding.invariantAffineMonoidSchemeIso

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantAffineCharacterAlgebra_coordinateCone
