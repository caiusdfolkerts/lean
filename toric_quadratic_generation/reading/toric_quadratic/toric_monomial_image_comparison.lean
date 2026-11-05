module

public import PaperVerification.ToricMonomialProjectiveEmbedding
public import PaperVerification.ToricAffineGenericPoint
public import PaperVerification.ToricIntrinsicSectionCharacters
public import PaperVerification.ToricSectionProjectiveEmbedding

@[expose] public section

/-!
# Equality with the genuine closed monomial image

Two closed immersions receiving the same schematically dense torus have
the same kernel ideal sheaf. The universal property of closed immersions
therefore gives an actual scheme isomorphism. Character-valued genuine
sections give precisely the same projective torus morphism, as checked
in the actual generic stalk.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical BaseSections

theorem closedImmersion_ker_eq_of_dense_composite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    (h : j≫f=q≫g) : f.ker=g.ker := by
  have H := congrArg Scheme.Hom.ker h
  simpa only [Scheme.Hom.ker_comp,Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using H

def closedImageIsoOfDenseComposite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : j≫f=q≫g) : X≅Y := by
  let H := (closedImmersion_ker_eq_of_dense_composite j q f g h).symm
  letI := IsClosedImmersion.isIso_lift g f H
  exact asIso (IsClosedImmersion.lift g f H.le)

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_embedding
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    (closedImageIsoOfDenseComposite j q f g h).hom≫g=f := by
  exact IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_torus
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    j≫(closedImageIsoOfDenseComposite j q f g h).hom=q := by
  apply (cancel_mono g).mp
  rw [Category.assoc,closedImageIsoOfDenseComposite_embedding]
  exact h

namespace RationalCartierCocycle

variable (k : Type u) [Field k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ)⟶X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u}
    (a : ι→(Fin n→ℤ)) (s : ι→Γ(C.sheaf,⊤))
    (hvalue : ∀ i,C.toCartierData.sectionValue ⊤ (s i)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single (a i) (1:k)))

local instance : IsDomain (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusCoordinateRing_isDomain k n

include hvalue in
theorem character_sectionProjectiveFieldMap :
    C.sectionProjectiveFieldMap k s=
      ((openTorusRationalAlgHom k n X j).toRingHom.comp
        (homogeneousExponentAlgHom a k).toRingHom).comp
        (homogeneousMonomialGradedMap a k).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, BaseSections.germ_scalarMap]
    change algebraMap k X.functionField c =
      openTorusRationalAlgHom k n X j
        (homogeneousExponentAlgHom a k
          (homogeneousMonomialMap a k (algebraMap k (MvPolynomial ι k) c)))
    exact ((congrArg
      (fun x => openTorusRationalAlgHom k n X j (homogeneousExponentAlgHom a k x))
      ((homogeneousMonomialMap a k).commutes c)).trans
      ((congrArg (openTorusRationalAlgHom k n X j)
        ((homogeneousExponentAlgHom a k).commutes c)).trans
        ((openTorusRationalAlgHom k n X j).commutes c))).symm
  · intro i
    simpa [sectionProjectiveFieldMap,homogeneousMonomialGradedMap,
      homogeneousMonomialMap,homogeneousWeightCharacter,homogeneousWeight] using hvalue i

include hvalue in
/-- The actual section embedding has the literal projective monomial
map on the actual open torus. -/
theorem character_sectionProjectiveMap_torus
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι) :
    j≫C.sectionProjectiveMap k s hcover=
      monomialTorusChart a k i≫monomialProjectiveEmbedding a k := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let jR : Spec R ⟶ X := j
  letI : IsOpenImmersion jR := inferInstanceAs (IsOpenImmersion j)
  let ρ := openTorusRationalAlgHom k n X j
  let η := Spec.map (CommRingCat.ofHom ρ.toRingHom)
  letI : IsDominant η := affineOpenCoordinateMap_isDominant R jR
  apply ext_of_isDominant η
  have hi : C.toCartierData.sectionValue ⊤ (s i)≠0 := by
    rw [hvalue i]
    simpa only [map_zero] using (openTorusRationalAlgHom_injective k n X j).ne
      (show AddMonoidAlgebra.single (a i) (1:k)≠0 by simp)
  have hη : η≫j=X.fromSpecStalk (genericPoint X) :=
    affineOpenCoordinateMap_genericPoint R jR
  have hleft := ((Category.assoc η jR (C.sectionProjectiveMap k s hcover)).symm.trans
    (congrArg (fun q => q ≫ C.sectionProjectiveMap k s hcover) hη)).trans
      (C.sectionProjectiveMap_generic_of_value_ne_zero k s hcover i hi)
  have hmonomial := monomialProjectiveEmbedding_torus_fieldMap a k ρ.toRingHom
    (openTorusRationalAlgHom_injective k n X j) i
  have hfield : C.sectionProjectiveFieldMap k s =
      (ρ.toRingHom.comp (homogeneousExponentAlgHom a k).toRingHom).comp
        (homogeneousMonomialGradedMap a k).toRingHom :=
    C.character_sectionProjectiveFieldMap k j a s hvalue
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule ι k) :=
    MvPolynomial.gradedAlgebra
  have hcharts (φ ψ : MvPolynomial ι k →+* X.functionField)
      (h : φ = ψ) (hφ : φ (MvPolynomial.X i) ≠ 0)
      (hψ : ψ (MvPolynomial.X i) ≠ 0) :
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k) φ (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (MvPolynomial.isHomogeneous_X k i)) (by decide) hφ =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k) ψ (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (MvPolynomial.isHomogeneous_X k i)) (by decide) hψ := by
    subst ψ
    rfl
  have hφ : C.sectionProjectiveFieldMap k s (MvPolynomial.X i) ≠ 0 := by
    simpa only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_X'] using hi
  have hψ : ((ρ.toRingHom.comp (homogeneousExponentAlgHom a k).toRingHom).comp
      (homogeneousMonomialGradedMap a k).toRingHom) (MvPolynomial.X i) ≠ 0 :=
    hfield ▸ hφ
  exact hleft.trans ((hcharts _ _ hfield hφ hψ).trans hmonomial.symm)

def characterMonomialImageIso
    (hj : DenseRange j)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [IsClosedImmersion (C.sectionProjectiveMap k s hcover)] :
    X≅monomialProjectiveScheme a k := by
  letI : IsDominant j := ⟨hj⟩
  letI : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let q : splitTorus k (Fin n → ℤ) ⟶ monomialProjectiveScheme a k :=
    monomialTorusChart a k i
  letI : IsSchemeTheoreticallyDominant q :=
    monomialTorusChart_isSchemeTheoreticallyDominant a k i
  exact closedImageIsoOfDenseComposite j q
    (C.sectionProjectiveMap k s hcover) (monomialProjectiveEmbedding a k)
    (C.character_sectionProjectiveMap_torus k j a s hvalue hcover i)

theorem characterMonomialImageIso_torus
    (hj : DenseRange j)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [IsClosedImmersion (C.sectionProjectiveMap k s hcover)] :
    j≫(C.characterMonomialImageIso k j a s hvalue hj hcover i).hom=
      monomialTorusChart a k i := by
  letI : IsDominant j := ⟨hj⟩
  letI : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let q : splitTorus k (Fin n → ℤ) ⟶ monomialProjectiveScheme a k :=
    monomialTorusChart a k i
  letI : IsSchemeTheoreticallyDominant q :=
    monomialTorusChart_isSchemeTheoreticallyDominant a k i
  exact closedImageIsoOfDenseComposite_torus j q
    (C.sectionProjectiveMap k s hcover) (monomialProjectiveEmbedding a k)
    (C.character_sectionProjectiveMap_torus k j a s hvalue hcover i)

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.characterMonomialImageIso
