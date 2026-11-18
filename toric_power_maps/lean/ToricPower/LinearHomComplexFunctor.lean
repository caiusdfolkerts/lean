module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Actual linear Hom complexes out of a K-projective complex

This module packages Mathlib's literal signed Hom cochains as a functor
in the second complex.  Its actual homology map is described through
cocycles and coboundaries.  For a K-projective source, the proved
localization bijection shows that this functor preserves every
quasi-isomorphism, including between unbounded target complexes.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower

universe u v r

variable (R : Type r) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  (K : CochainComplex A ℤ)

/-- Actual postcomposition of the degree-`n` Hom cochains. -/
def homCochainPostcomp {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    Cochain K X n →ₗ[R] Cochain K Y n where
  toFun z := z.comp (Cochain.ofHom f) (add_zero n)
  map_add' z w := by simp
  map_smul' r z := by simp

@[simp]
theorem homCochainPostcomp_v {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : Cochain K X n) (p q : ℤ) (h : p+n=q) :
    (homCochainPostcomp R K f n z).v p q h = z.v p q h ≫ f.f q := by
  change (z.comp (Cochain.ofHom f) (add_zero n)).v p q h = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

/-- The actual postcomposition chain map of signed linear Hom complexes. -/
def linearHomComplexMap {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    linearHomComplex R K X ⟶ linearHomComplex R K Y where
  f n := ModuleCat.ofHom (homCochainPostcomp R K f n)
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z f m

/-- Mathlib's actual linear Hom complex, functorial in its target. -/
def linearHomComplexFunctor : CochainComplex A ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj X := linearHomComplex R K X
  map f := linearHomComplexMap R K f
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change z.comp (Cochain.ofHom (𝟙 X)) (add_zero n) = z
    exact Cochain.comp_id z
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change z.comp (Cochain.ofHom (f ≫ g)) (add_zero n) =
      (z.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc_of_second_is_zero_cochain z
      (Cochain.ofHom f) (Cochain.ofHom g) (add_zero n)).symm

/-- Postcomposition preserves actual cocycles, with the same signed
differential as the Hom-complex chain map. -/
def homCocyclePostcomp {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    Cocycle K X n →ₗ[R] Cocycle K Y n where
  toFun z := z.postcomp f
  map_add' z w := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_add, Cochain.add_comp]
  map_smul' r z := by
    apply Cocycle.ext
    simp only [Cocycle.postcomp, Cocycle.mk_coe, Cocycle.coe_smul, Cochain.smul_comp,
      RingHom.id_apply]

/-- The actual postcomposition map on cohomology classes. Coboundaries
are preserved by the proved differential--composition identity. -/
def homClassPostcompAdd {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    CohomologyClass K X n →+ CohomologyClass K Y n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K Y n).comp
      (homCocyclePostcomp R K f n).toAddMonoidHom) (by
    intro z hz
    change CohomologyClass.mk (z.postcomp f) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    obtain ⟨m, hm, b, hb⟩ := hz
    refine ⟨m, hm, b.comp (Cochain.ofHom f) (add_zero m), ?_⟩
    simpa only [δ_comp_ofHom, hb, Cocycle.postcomp_coe])

@[simp]
theorem homClassPostcompAdd_mk {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : Cocycle K X n) :
    homClassPostcompAdd R K f n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp f) := rfl

/-- The quotient map is genuinely linear, since its cocycle map is linear. -/
def homClassPostcomp {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    CohomologyClass K X n →ₗ[R] CohomologyClass K Y n where
  toAddHom := homClassPostcompAdd R K f n
  map_smul' r z := by
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
    change homClassPostcompAdd R K f n (r • CohomologyClass.mk z) =
      r • homClassPostcompAdd R K f n (CohomologyClass.mk z)
    rw [← CohomologyClass.mk_smul, homClassPostcompAdd_mk, homClassPostcompAdd_mk]
    change CohomologyClass.mk (homCocyclePostcomp R K f n (r • z)) =
      r • CohomologyClass.mk (homCocyclePostcomp R K f n z)
    rw [map_smul, CohomologyClass.mk_smul]

@[simp]
theorem homClassPostcomp_mk {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : Cocycle K X n) :
    homClassPostcomp R K f n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp f) := rfl

/-- This data identifies the actual homology map of the actual chain
map, rather than introducing a separate surrogate cohomology map. -/
def linearHomComplexMapHomologyData {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map
        (linearHomComplexMap R K f))
      (HomComplex.linearLeftHomologyData R K X n)
      (HomComplex.linearLeftHomologyData R K Y n) where
  φK := ModuleCat.ofHom (homCocyclePostcomp R K f n)
  φH := ModuleCat.ofHom (homClassPostcomp R K f n)
  commi := by ext z; rfl
  commf' := by
    let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map
      (linearHomComplexMap R K f)
    have hi : ModuleCat.ofHom (homCocyclePostcomp R K f n) ≫
        (HomComplex.linearLeftHomologyData R K Y n).i =
      (HomComplex.linearLeftHomologyData R K X n).i ≫
        φ.τ₂ := by
      ext z
      rfl
    apply (cancel_mono (HomComplex.linearLeftHomologyData R K Y n).i).1
    simp only [Category.assoc, hi,
      ShortComplex.LeftHomologyData.f'_i_assoc,
      ShortComplex.LeftHomologyData.f'_i]
    exact φ.comm₁₂.symm
  commπ := by ext z; rfl

variable [HasDerivedCategory A]

/-- Cohomology of the actual Hom complex computes derived maps out of
the actual K-projective source, in every integer degree. -/
def homClassDerivedEquiv [K.IsKProjective] (X : CochainComplex A ℤ) (n : ℤ) :
    CohomologyClass K X n ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (X⟦n⟧)) :=
  (CohomologyClass.homAddEquiv (K := K) (L := X) (n := n)).toEquiv.trans
    ((Equiv.ofBijective DerivedCategory.Qh.map
      (CochainComplex.IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient A (.up ℤ)).obj (X⟦n⟧)))).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app K)
        ((DerivedCategory.quotientCompQhIso A).app (X⟦n⟧))))

@[simp]
theorem homClassDerivedEquiv_mk [K.IsKProjective] (X : CochainComplex A ℤ) (n : ℤ)
    (z : Cocycle K X n) :
    homClassDerivedEquiv K X n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) := by
  change (DerivedCategory.quotientCompQhIso A).inv.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map
        (Cocycle.equivHomShift.symm z)) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app (X⟦n⟧) = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Naturality is proved on literal cocycles and then on their quotient. -/
theorem homClassDerivedEquiv_postcomp [K.IsKProjective]
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    (z : CohomologyClass K X n) :
    homClassDerivedEquiv K Y n (homClassPostcomp R K f n z) =
      homClassDerivedEquiv K X n z ≫ DerivedCategory.Q.map (f⟦n⟧') := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  simp only [homClassPostcomp_mk, homClassDerivedEquiv_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

/-- A quasi-isomorphism of target complexes induces a bijection on
the actual Hom-complex cohomology classes in every integer degree. -/
theorem homClassPostcomp_bijective [K.IsKProjective]
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [QuasiIso f] (n : ℤ) :
    Function.Bijective (homClassPostcomp R K f n) := by
  constructor
  · intro x y h
    apply (homClassDerivedEquiv K X n).injective
    apply (cancel_mono (DerivedCategory.Q.map (f⟦n⟧'))).1
    rw [← homClassDerivedEquiv_postcomp R K f n x,
      ← homClassDerivedEquiv_postcomp R K f n y, h]
  · intro y
    let z := (homClassDerivedEquiv K X n).symm
      (homClassDerivedEquiv K Y n y ≫ inv (DerivedCategory.Q.map (f⟦n⟧')))
    refine ⟨z, (homClassDerivedEquiv K Y n).injective ?_⟩
    rw [homClassDerivedEquiv_postcomp R K f n z]
    simp only [z, Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The actual Hom-complex functor preserves all quasi-isomorphisms
when its source is K-projective. Neither target is assumed bounded. -/
theorem linearHomComplexMap_quasiIso [K.IsKProjective]
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso (linearHomComplexMap R K f) := by
  constructor
  intro n
  rw [quasiIsoAt_iff]
  apply (linearHomComplexMapHomologyData R K f n).quasiIso_iff.mpr
  rw [ConcreteCategory.isIso_iff_bijective]
  exact homClassPostcomp_bijective R K f n

variable [HasDerivedCategory (ModuleCat.{v} R)]

/-- The literal quasi-isomorphism class is inverted by the computed
Hom complex followed by its target localization. -/
theorem linearHomComplexInverts [K.IsKProjective] :
    (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (linearHomComplexFunctor R K ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  letI : QuasiIso f := hf
  letI := linearHomComplexMap_quasiIso R K f
  exact (inferInstance : IsIso (DerivedCategory.Q.map (linearHomComplexMap R K f)))

/-- The resulting actual functor on the full unbounded derived category.
Its cohomology represents the actual shifted derived Hom groups above. -/
def derivedLinearHom [K.IsKProjective] : DerivedCategory A ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Localization.lift (linearHomComplexFunctor R K ⋙ DerivedCategory.Q)
    (linearHomComplexInverts R K)
    DerivedCategory.Q

/-- The actual localization factorization. -/
def derivedLinearHomFactors [K.IsKProjective] :
    DerivedCategory.Q ⋙ derivedLinearHom R K ≅
      linearHomComplexFunctor R K ⋙ DerivedCategory.Q :=
  Localization.fac _ (linearHomComplexInverts R K) DerivedCategory.Q

end ToricPower

end
