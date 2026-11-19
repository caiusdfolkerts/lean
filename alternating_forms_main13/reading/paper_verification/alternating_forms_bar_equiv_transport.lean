module

public import PaperVerification.AlternatingFormsBarTensor
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Actual Tor under an isomorphism of augmented algebras

The basis on the second algebra is the image of the first actual basis.
Its multiplication coefficients are equal to the original coefficients,
so the normalized reduced bar complexes have an explicit identity-on-words
isomorphism.  The ordinary Tor comparison on both sides then gives an
isomorphism of the actual derived functor objects.

The comparison preserves every subcomplex of words, in particular those
defined by the sum of the original homogeneous degrees.  This is a proved
comparison of actual complexes and actual Tor, not an invariance assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarEquivTransport

open CategoryTheory HomologicalComplex
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A D I : Type u} [CommRing K] [CommRing A] [CommRing D]
  [Algebra K A] [Algebra K D]
  (e : A ≃ₐ[K] D) (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)

/-- The actual original augmentation composed with the inverse algebra
isomorphism. -/
def augmentation : D →ₐ[K] K := ε.comp e.symm.toAlgHom

/-- The actual positive algebra basis, with the same indexing set. -/
def basis : Module.Basis (Option I) K D := B.map e.toLinearEquiv

@[simp] theorem basis_apply (i : Option I) : basis e B i=e (B i) := rfl

@[simp] theorem augmentation_image (x : A) : augmentation e ε (e x)=ε x := by
  change ε (e.symm (e x))=ε x
  rw [e.symm_apply_apply]

theorem basis_unit (hunit : B none=1) : basis e B none=1 := by
  rw [basis_apply,hunit,map_one]

theorem augmentation_positive (hε : ∀ i,ε (B (some i))=0) (i : I) :
    augmentation e ε (basis e B (some i))=0 := by
  rw [basis_apply,augmentation_image,hε]

@[simp] theorem basis_repr_image (x : A) :
    (basis e B).repr (e x)=B.repr x := by
  change B.repr (e.symm (e x))=B.repr x
  rw [e.symm_apply_apply]

/-- Actual multiplication has exactly the same positive-basis
coefficients after transport. -/
theorem productCoefficients_eq (i j : I) :
    productCoefficients (basis e B) i j=productCoefficients B i j := by
  apply Finsupp.ext
  intro a
  change (basis e B).repr (basis e B (some i)*basis e B (some j)) (some a)=
    B.repr (B (some i)*B (some j)) (some a)
  rw [basis_apply,basis_apply,←map_mul,basis_repr_image]

theorem mergeBasis_eq (i : I) (L : List I) :
    PaperVerification.ReducedBarBasis.mergeBasis (basis e B) i L=
      PaperVerification.ReducedBarBasis.mergeBasis B i L := by
  cases L with
  | nil => rfl
  | cons j L =>
      change PaperVerification.ReducedBarBasis.appendTail L
          (productCoefficients (basis e B) i j)=
        PaperVerification.ReducedBarBasis.appendTail L (productCoefficients B i j)
      rw [productCoefficients_eq]

theorem merge_eq (i : I) :
    PaperVerification.ReducedBarBasis.merge (basis e B) i=
      PaperVerification.ReducedBarBasis.merge B i := by
  unfold PaperVerification.ReducedBarBasis.merge
  congr 1
  funext L
  exact mergeBasis_eq e B i L

theorem differentialBasis_eq (L : List I) :
    PaperVerification.ReducedBarBasis.differentialBasis (basis e B) L=
      PaperVerification.ReducedBarBasis.differentialBasis B L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      change PaperVerification.ReducedBarBasis.merge (basis e B) i (Finsupp.single L 1)-
          PaperVerification.ReducedBarBasis.prepend i
            (PaperVerification.ReducedBarBasis.differentialBasis (basis e B) L)=
        PaperVerification.ReducedBarBasis.merge B i (Finsupp.single L 1)-
          PaperVerification.ReducedBarBasis.prepend i
            (PaperVerification.ReducedBarBasis.differentialBasis B L)
      rw [merge_eq,ih]

theorem differential_eq :
    PaperVerification.ReducedBarBasis.differential (basis e B)=
      PaperVerification.ReducedBarBasis.differential B := by
  unfold PaperVerification.ReducedBarBasis.differential
  congr 1
  funext L
  exact differentialBasis_eq e B L

theorem reducedDegreeDifferential_eq (r : ℕ) :
    BarFree.reducedDegreeDifferential (basis e B) r=
      BarFree.reducedDegreeDifferential B r := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change PaperVerification.ReducedBarBasis.differential (basis e B) z.val=
    PaperVerification.ReducedBarBasis.differential B z.val
  rw [differential_eq]

theorem negativeReducedDegreeDifferential_eq (r : ℕ) :
    BarFree.negativeReducedDegreeDifferential (basis e B) r=
      BarFree.negativeReducedDegreeDifferential B r := by
  apply LinearMap.ext
  intro z
  change -(BarFree.reducedDegreeDifferential (basis e B) r z)=
    -(BarFree.reducedDegreeDifferential B r z)
  rw [reducedDegreeDifferential_eq]

variable (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine normalized bar complexes are isomorphic by the identity
on every coefficient word.  No chain-map identity is assumed. -/
def reducedComplexIso :
    BarFree.reducedComplex ε B hunit hε ≅
      BarFree.reducedComplex (augmentation e ε) (basis e B)
        (basis_unit e B hunit) (augmentation_positive e ε B hε) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ Iso.refl (ModuleCat.of K (BarFree.lengthPiece I K r))) (by
    intro i j hij
    change j+1=i at hij
    subst i
    rw [BarFree.reducedComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change BarFree.negativeReducedDegreeDifferential (basis e B) j z=
      BarFree.negativeReducedDegreeDifferential B j z
    rw [negativeReducedDegreeDifferential_eq])

@[simp] theorem reducedComplexIso_hom_f_apply (r : ℕ)
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).hom.f r) z=z := rfl

@[simp] theorem reducedComplexIso_inv_f_apply (r : ℕ)
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).inv.f r) z=z := rfl

/-- Every degree condition on the actual coefficient words is preserved
in both directions, because the comparison keeps those words literally. -/
theorem reducedComplexIso_mem_iff (r : ℕ)
    (P : Submodule K (BarFree.lengthPiece I K r))
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).hom.f r) z∈P ↔ z∈P := Iff.rfl

/-- Ordinary derived Tor for the actual two augmented algebras, compared
through their explicit normalized free bar resolutions. -/
def torIso (r : ℕ) :
    BarFree.TorOverCoefficients ε r ≅
      BarFree.TorOverCoefficients (augmentation e ε) r :=
  BarFree.reducedBarTorIso ε B hunit hε r ≪≫
    HomologicalComplex.homologyMapIso (reducedComplexIso e ε B hunit hε) r ≪≫
    (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
      (basis_unit e B hunit) (augmentation_positive e ε B hε) r).symm

/-- The actual Tor comparison is induced by the identity-on-words bar
map, after applying the actual source and target Tor comparisons. -/
theorem sourceComparison_inv_comp_torIso (r : ℕ) :
    (BarFree.reducedBarTorIso ε B hunit hε r).inv ≫
        (torIso e ε B hunit hε r).hom=
      HomologicalComplex.homologyMap (reducedComplexIso e ε B hunit hε).hom r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv := by
  simp only [torIso,Iso.trans_hom,Category.assoc,Iso.inv_hom_id_assoc,
    HomologicalComplex.homologyMapIso_hom,Iso.symm_hom]

theorem map_diagonal_submodule {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N)
    (P : Submodule K M) (i j : ℕ) (hP : P=if i=j then ⊤ else ⊥) :
    P.map f.toLinearMap=if i=j then ⊤ else ⊥ := by
  rw [hP]
  split_ifs
  · rw [Submodule.map_top,LinearEquiv.range]
  · exact Submodule.map_bot _

/-- Internal Tor pieces defined by actual bar subcomplexes are carried
to their actual images in the transported bar resolution. -/
theorem subcomplex_homology_image (r : ℕ)
    (C : ChainComplex (ModuleCat K) ℕ)
    (ι : C ⟶ BarFree.reducedComplex ε B hunit hε) :
    LinearMap.range
      ((HomologicalComplex.homologyMap
          (ι ≫ (reducedComplexIso e ε B hunit hε).hom) r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv).hom)=
      (LinearMap.range
        ((HomologicalComplex.homologyMap ι r ≫
          (BarFree.reducedBarTorIso ε B hunit hε r).inv).hom)).map
            (torIso e ε B hunit hε r).toLinearEquiv.toLinearMap := by
  rw [←LinearMap.range_comp]
  congr 1
  change (HomologicalComplex.homologyMap
      (ι ≫ (reducedComplexIso e ε B hunit hε).hom) r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv).hom=
    ((HomologicalComplex.homologyMap ι r ≫
      (BarFree.reducedBarTorIso ε B hunit hε r).inv) ≫
        (torIso e ε B hunit hε r).hom).hom
  apply congrArg (fun f : C.homology r ⟶
    BarFree.TorOverCoefficients (augmentation e ε) r ↦ f.hom)
  simp only [HomologicalComplex.homologyMap_comp,Category.assoc,
    sourceComparison_inv_comp_torIso]

end PaperVerification.AlternatingForms.BarEquivTransport
