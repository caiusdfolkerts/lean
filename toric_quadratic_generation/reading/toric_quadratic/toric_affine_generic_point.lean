module

public import PaperVerification.ToricFunctionFieldBridge
public import PaperVerification.ToricSectionProjectiveMap

@[expose] public section

/-! # The actual generic morphism in affine coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : CommRingCat.{u}) [IsDomain R]

theorem affine_genericPointMap :
    Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField))=
      (Spec R).fromSpecStalk (genericPoint (Spec R)) := by
  calc
    Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) =
        Spec.map ((Scheme.ΓSpecIso R).inv≫(Spec R).germToFunctionField ⊤) := rfl
    _ = Spec.map ((Spec R).germToFunctionField ⊤)≫Spec.map (Scheme.ΓSpecIso R).inv :=
      Spec.map_comp _ _
    _ = (Spec R).fromSpecStalk (genericPoint (Spec R))≫(Spec R).toSpecΓ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by
      exact congrArg (fun f => f ≫ Spec.map (Scheme.ΓSpecIso R).inv)
        (Scheme.fromSpecStalk_toSpecΓ (Spec R) (genericPoint (Spec R))).symm
    _ = _ := by
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv,Category.comp_id]

variable {X : Scheme.{u}} [IsIntegral X]
    (j : Spec R⟶X) [IsOpenImmersion j]

theorem affineOpenCoordinateMap_genericPoint :
    Spec.map (CommRingCat.ofHom (affineOpenCoordinateMap R j))≫j=
      X.fromSpecStalk (genericPoint X) := by
  let e := openImmersionFunctionFieldIso j
  have he : Spec.map e.hom≫X.fromSpecStalk (genericPoint X)=
      (Spec R).fromSpecStalk (genericPoint (Spec R))≫j := by
    simp only [e,openImmersionFunctionFieldIso,Iso.trans_hom,Spec.map_comp,
      TopCat.Presheaf.stalkCongr_hom,asIso_hom,Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hcoord : CommRingCat.ofHom (affineOpenCoordinateMap R j)=
      CommRingCat.ofHom (algebraMap R (Spec R).functionField)≫e.inv := rfl
  rw [hcoord,Spec.map_comp,Category.assoc,affine_genericPointMap R,← he,
    ← Category.assoc,← Spec.map_comp,Iso.hom_inv_id,Spec.map_id]
  exact Category.id_comp _

theorem affineOpenCoordinateMap_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (affineOpenCoordinateMap R j))) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  have hinj : Function.Injective (affineOpenCoordinateMap R j) :=
    (openImmersionGlobalToFunctionField_injective j).comp
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective
  change RingHom.ker (affineOpenCoordinateMap R j) ≤ nilradical R
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveMap_generic_of_value_ne_zero
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    (hi : C.toCartierData.sectionValue ⊤ (s i)≠0) :
    X.fromSpecStalk (genericPoint X)≫C.sectionProjectiveMap k s hcover=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_X'] using hi) := by
  have hη : genericPoint X∈C.nonvanishingOpen (s i) := by
    obtain ⟨j,hj⟩ := C.covers (genericPoint X)
    rw [C.nonvanishing_iff_value j (s i) (genericPoint X) hj]
    refine ⟨hi,?_⟩
    refine ⟨(C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ (s i),?_⟩
    simp only [RingHom.algebraMap_toAlgebra,TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.id_apply]
  letI : Nonempty (C.nonvanishingOpen (s i)) := ⟨⟨genericPoint X,hη⟩⟩
  rw [← (C.nonvanishingOpen (s i)).fromSpecStalkOfMem_ι
    (genericPoint X) hη,Category.assoc,C.sectionProjectiveMap_chart k s hcover i]
  exact C.sectionProjectiveChart_generic k s i hη

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpenCoordinateMap_genericPoint
