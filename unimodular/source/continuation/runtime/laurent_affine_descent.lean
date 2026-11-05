module

public import Continuation.Runtime.AffineFlatDescent
public import Continuation.Runtime.LaurentFaithfullyFlat
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Affineness from a Laurent principal open

Consider the base change of an actual map `X → Spec R` along the Laurent
extension of `R`. If the inverse image of a principal open with one unit
coefficient is affine, then `X` is affine. The affine base change is
faithfully flat by coefficient reduction, and affineness descends through
the actual cartesian square.

This is the descent step for invariant character nonvanishing opens. It
uses neither rational torus points nor a projectivity hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace PaperVerification.ToricSchemes

/-- A Laurent principal open with a unit coefficient detects affineness
through an actual base-change square over an affine scheme.  Taking
`R = Γ(X, ⊤)` and `i = X.toSpecΓ` gives the affinization application. -/
theorem isAffine_of_affine_laurent_principal_preimage
    (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {M : Type} [AddCommMonoid M] [UniqueSums M]
    (i : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X)
    (q : Y ⟶ Spec (CommRingCat.of (AddMonoidAlgebra R M)))
    (H : IsPullback q g
      (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M)))) i)
    (f : AddMonoidAlgebra R M) (m : M) (hm : IsUnit (f.coeff m))
    (hD : IsAffineOpen (q ⁻¹ᵁ (PrimeSpectrum.basicOpen f :
      (Spec (CommRingCat.of (AddMonoidAlgebra R M))).Opens))) : IsAffine X := by
  let A := AddMonoidAlgebra R M
  let B := Localization.Away f
  let σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let D : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen f
  let j : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hjfaith : (algebraMap R B).FaithfullyFlat :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := R) (S := B)).mpr
      (laurentAway_faithfullyFlat_of_isUnit_coeff f m hm)
  have hj : Flat j ∧ Surjective j :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R B))).mpr hjfaith
  letI : Flat j := hj.1
  letI : Surjective j := hj.2
  have hjcomp : j = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σ := by
    have hring : CommRingCat.ofHom (algebraMap R B) =
        CommRingCat.ofHom (algebraMap R A) ≫
          CommRingCat.ofHom (algebraMap A B) :=
      congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq R A B)
    exact (congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of B => Spec.map h) hring).trans
      (Spec.map_comp (CommRingCat.ofHom (algebraMap R A))
        (CommRingCat.ofHom (algebraMap A B)))
  have hDbase : D.ι ≫ σ = (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom ≫ j := by
    calc
      D.ι ≫ σ = ((basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ σ :=
        congrArg (fun h => h ≫ σ) (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) f).symm
      _ = (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σ) :=
        Category.assoc _ _ _
      _ = (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom ≫ j :=
        congrArg (fun h => (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom ≫ h) hjcomp.symm
  letI : Flat (D.ι ≫ σ) := by rw [hDbase]; infer_instance
  letI : Surjective (D.ι ≫ σ) := by rw [hDbase]; infer_instance
  letI : IsAffine D.toScheme := IsAffine.of_isIso (basicOpenIsoSpecAway (R := CommRingCat.of A) f).hom
  letI : IsAffine (q ⁻¹ᵁ D).toScheme := hD
  have H' := ((isPullback_morphismRestrict q D).paste_vert H).flip
  exact isAffine_of_affine_flat_baseChange
    (X := X) (Y := (q ⁻¹ᵁ D).toScheme)
    (S := Spec (CommRingCat.of R)) (T := D.toScheme)
    (f := D.ι ≫ σ) (g := (q ⁻¹ᵁ D).ι ≫ g)
    (iX := i) (iY := q ∣_ D) H'

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isAffine_of_affine_laurent_principal_preimage
