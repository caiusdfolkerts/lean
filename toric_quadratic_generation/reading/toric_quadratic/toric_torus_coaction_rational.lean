module

public import PaperVerification.ToricIntrinsicSectionCharacters
public import PaperVerification.ToricDominantAffineCoordinates

@[expose] public section

/-! # The actual torus multiplication and its rational character coaction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)

local instance torusCoordinate_domain : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

theorem openTorusRationalAlgHom_pullback
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    dominantFunctionFieldMap j (openTorusRationalAlgHom k n X j f) =
      openTorusRationalAlgHom k n (splitTorus k (Fin n→ℤ)) (𝟙 _) f := by
  have hd : IsDominant j := inferInstance
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  letI : IsDominant
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hd
  exact dominantFunctionFieldMap_affineCoordinate
    (CommRingCat.of (torusCoordinateRing k n))
    (CommRingCat.of (torusCoordinateRing k n)) j (𝟙 _) j (𝟙 _)
    (by simp) f

theorem torus_mul_spec :
    μ[splitTorusOver k (Fin n→ℤ)].left =
      (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (torusCoordinateRing k n))
        (CommRingCat.of (torusCoordinateRing k n))).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom k (torusCoordinateRing k n)).toRingHom) :=
  mul_spec_asOver_spec_left

instance torus_mul_surjective : Surjective μ[splitTorusOver k (Fin n→ℤ)].left := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : ModObj G G := ModObj.regular G
  exact torusAction_surjective k n G

namespace SplitToricEmbedding

variable {k n} {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

include T in
theorem torus_locallyNoetherian : IsLocallyNoetherian (splitTorus k (Fin n→ℤ)) := by
  change IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).left
  letI : Smooth (splitTorusOver k (Fin n→ℤ)).hom := T.torus_smooth
  exact LocallyOfFiniteType.isLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).hom

include T in
theorem doubleTorus_integral :
    IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ splitTorusOver k (Fin n→ℤ)).left := by
  letI : IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).left :=
    T.torus_locallyNoetherian
  exact torusProduct_integral k n (splitTorusOver k (Fin n→ℤ))

include T in
/-- The proved double-torus integrality at the literal affine pullback type. -/
theorem doubleTorus_affinePullback_integral :
    IsIntegral (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))) :=
  T.doubleTorus_integral

include T in
/-- The actual affine tensor-product chart of the double torus is a
domain, derived from geometric integrality rather than postulated. -/
theorem doubleTorusTensor_isDomain :
    IsDomain (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n) := by
  letI := T.doubleTorus_affinePullback_integral
  let e := pullbackSpecIso (CommRingCat.of k)
    (CommRingCat.of (torusCoordinateRing k n))
    (CommRingCat.of (torusCoordinateRing k n))
  exact (affine_isIntegral_iff _).mp (IsIntegral.of_isIso e.hom)

/-- Multiplication pulls a genuine torus rational function back through
the genuine Hopf comultiplication on its affine coordinate algebra. -/
theorem torus_mul_rational (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    letI := T.doubleTorus_integral
    letI := T.doubleTorus_affinePullback_integral
    letI := T.doubleTorusTensor_isDomain
    dominantFunctionFieldMap μ[splitTorusOver k (Fin n→ℤ)].left
      (openTorusRationalAlgHom k n (splitTorus k (Fin n→ℤ)) (𝟙 _) f) =
      affineOpenCoordinateMap
        (CommRingCat.of (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n))
        (pullbackSpecIso (CommRingCat.of k)
          (CommRingCat.of (torusCoordinateRing k n))
          (CommRingCat.of (torusCoordinateRing k n))).inv
        (Coalgebra.comul (R:=k) f) := by
  letI := T.doubleTorus_integral
  letI := T.doubleTorus_affinePullback_integral
  letI := T.doubleTorusTensor_isDomain
  let R := CommRingCat.of (torusCoordinateRing k n)
  let S := CommRingCat.of (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n)
  let e := pullbackSpecIso (CommRingCat.of k) R R
  let mul : pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n)))) ⟶ Spec R :=
    μ[splitTorusOver k (Fin n→ℤ)].left
  letI : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  letI : IsDominant mul :=
    inferInstanceAs (IsDominant μ[splitTorusOver k (Fin n→ℤ)].left)
  let φ : R ⟶ S :=
    CommRingCat.ofHom (Bialgebra.comulAlgHom k (torusCoordinateRing k n)).toRingHom
  have hcomm : e.inv ≫ mul = Spec.map φ ≫ 𝟙 (Spec R) := by
    calc
      e.inv ≫ mul = e.inv ≫ (e.hom ≫ Spec.map φ) :=
        congrArg (fun h => e.inv ≫ h) (torus_mul_spec k n)
      _ = Spec.map φ := e.inv_hom_id_assoc _
      _ = Spec.map φ ≫ 𝟙 (Spec R) := (Category.comp_id _).symm
  exact dominantFunctionFieldMap_affineCoordinate R S (𝟙 (Spec R)) e.inv mul φ hcomm f

/-- The open double-torus map used to test actual rational identities. -/
def doubleTorusMap :
    (splitTorusOver k (Fin n→ℤ) ⊗ splitTorusOver k (Fin n→ℤ)).left ⟶
      (splitTorusOver k (Fin n→ℤ) ⊗ X).left :=
  (splitTorusOver k (Fin n→ℤ) ◁ T.torus).left

instance doubleTorusMap_isOpenImmersion : IsOpenImmersion T.doubleTorusMap := by
  rw [doubleTorusMap,Over.whiskerLeft_left]
  infer_instance

theorem doubleTorusMap_comp_action :
    T.doubleTorusMap ≫ (γ[splitTorusOver k (Fin n→ℤ),X]).left =
      μ[splitTorusOver k (Fin n→ℤ)].left ≫ T.torus.left := by
  exact (congrArg (fun f=>f.left) T.equivariant).symm

end SplitToricEmbedding

end PaperVerification.ToricSchemes
