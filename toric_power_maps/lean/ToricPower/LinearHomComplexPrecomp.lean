module

public import ToricPower.LinearHomComplexFunctor
public import ToricPower.RelativeConeOrthogonality

/-!
# Actual precomposition of signed linear Hom complexes

This is the contravariant partner of `LinearHomComplexFunctor`. Its
homology map is identified with literal precomposition of homotopy
classes. This keeps the augmentation comparison a genuine chain map
and retains naturality in the coefficient complex.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L) (X : CochainComplex A ℤ)

/-- Literal precomposition of the signed Hom cochains. -/
def homCochainPrecomp (n : ℤ) : Cochain L X n →ₗ[R] Cochain K X n where
  toFun z := (Cochain.ofHom f).comp z (zero_add n)
  map_add' z w := by simp
  map_smul' r z := by simp

@[simp]
theorem homCochainPrecomp_v (n : ℤ) (z : Cochain L X n)
    (p q : ℤ) (h : p+n=q) :
    (homCochainPrecomp R f X n z).v p q h = f.f p ≫ z.v p q h := by
  change ((Cochain.ofHom f).comp z (zero_add n)).v p q h = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

/-- The actual scalar-linear chain map induced by the source arrow. -/
def linearHomComplexPrecomp : linearHomComplex R L X ⟶ linearHomComplex R K X where
  f n := ModuleCat.ofHom (homCochainPrecomp R f X n)
  comm' n m _ := by
    ext z
    exact δ_ofHom_comp f z m

/-- Source precomposition is natural in every actual coefficient chain map. -/
theorem linearHomComplexPrecomp_naturality {X Y : CochainComplex A ℤ} (g : X ⟶ Y) :
    linearHomComplexMap R L g ≫ linearHomComplexPrecomp R f Y =
      linearHomComplexPrecomp R f X ≫ linearHomComplexMap R K g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change homCochainPrecomp R f Y n (homCochainPostcomp R L g n z) =
    homCochainPostcomp R K g n (homCochainPrecomp R f X n z)
  ext p q hpq
  simp only [homCochainPrecomp_v, homCochainPostcomp_v, Category.assoc]

/-- The whole source-precomposition transformation, before localization. -/
def linearHomComplexPrecompNatTrans :
    linearHomComplexFunctor R L ⟶ linearHomComplexFunctor R K where
  app X := linearHomComplexPrecomp R f X
  naturality {_X _Y} g := linearHomComplexPrecomp_naturality R f g

/-- The same map on actual cocycles. -/
def homCocyclePrecomp (n : ℤ) : Cocycle L X n →ₗ[R] Cocycle K X n where
  toFun z := z.precomp f
  map_add' z w := by
    apply Cocycle.ext
    simp only [Cocycle.precomp, Cocycle.mk_coe, Cocycle.coe_add, Cochain.comp_add]
  map_smul' r z := by
    apply Cocycle.ext
    simp only [Cocycle.precomp, Cocycle.mk_coe, Cocycle.coe_smul, Cochain.comp_smul,
      RingHom.id_apply]

/-- The induced additive map on actual cohomology classes. -/
def homClassPrecompAdd (n : ℤ) : CohomologyClass L X n →+ CohomologyClass K X n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K X n).comp
      (homCocyclePrecomp R f X n).toAddMonoidHom) (by
    intro z hz
    change CohomologyClass.mk (z.precomp f) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    obtain ⟨m, hm, b, hb⟩ := hz
    refine ⟨m, hm, (Cochain.ofHom f).comp b (zero_add m), ?_⟩
    simp only [δ_ofHom_comp, hb, Cocycle.precomp_coe])

@[simp]
theorem homClassPrecompAdd_mk (n : ℤ) (z : Cocycle L X n) :
    homClassPrecompAdd R f X n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

/-- Precomposition is linear on the actual quotient of cocycles. -/
def homClassPrecomp (n : ℤ) : CohomologyClass L X n →ₗ[R] CohomologyClass K X n where
  toAddHom := homClassPrecompAdd R f X n
  map_smul' r z := by
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
    change homClassPrecompAdd R f X n (r • CohomologyClass.mk z) =
      r • homClassPrecompAdd R f X n (CohomologyClass.mk z)
    rw [← CohomologyClass.mk_smul, homClassPrecompAdd_mk, homClassPrecompAdd_mk]
    change CohomologyClass.mk (homCocyclePrecomp R f X n (r • z)) =
      r • CohomologyClass.mk (homCocyclePrecomp R f X n z)
    rw [map_smul, CohomologyClass.mk_smul]

@[simp]
theorem homClassPrecomp_mk (n : ℤ) (z : Cocycle L X n) :
    homClassPrecomp R f X n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

/-- Actual cohomology and actual homotopy precomposition agree. -/
theorem homClassPrecomp_toHom (n : ℤ) (z : CohomologyClass L X n) :
    CohomologyClass.toHom (homClassPrecomp R f X n z) =
      (HomotopyCategory.quotient A (.up ℤ)).map f ≫ CohomologyClass.toHom z := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
  rw [homClassPrecomp_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, CategoryTheory.Functor.map_comp]

/-- This data computes the homology map of the literal chain map. -/
def linearHomComplexPrecompHomologyData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map
        (linearHomComplexPrecomp R f X))
      (HomComplex.linearLeftHomologyData R L X n)
      (HomComplex.linearLeftHomologyData R K X n) where
  φK := ModuleCat.ofHom (homCocyclePrecomp R f X n)
  φH := ModuleCat.ofHom (homClassPrecomp R f X n)
  commi := by ext z; rfl
  commf' := by
    let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map
      (linearHomComplexPrecomp R f X)
    have hi : ModuleCat.ofHom (homCocyclePrecomp R f X n) ≫
        (HomComplex.linearLeftHomologyData R K X n).i =
      (HomComplex.linearLeftHomologyData R L X n).i ≫ φ.τ₂ := by ext z; rfl
    apply (cancel_mono (HomComplex.linearLeftHomologyData R K X n).i).mp
    simp only [Category.assoc, hi,
      ShortComplex.LeftHomologyData.f'_i_assoc, ShortComplex.LeftHomologyData.f'_i]
    exact φ.comm₁₂.symm
  commπ := by ext z; rfl

/-- A homotopy-class bijection in every degree proves a quasi-isomorphism
of the literal signed Hom complexes. -/
theorem linearHomComplexPrecomp_quasiIso_of_homotopy_bijective
    (h : ∀ n : ℤ, Function.Bijective (fun g :
      (HomotopyCategory.quotient A (.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (X⟦n⟧) =>
      (HomotopyCategory.quotient A (.up ℤ)).map f ≫ g)) :
    QuasiIso (linearHomComplexPrecomp R f X) := by
  constructor
  intro n
  rw [quasiIsoAt_iff]
  apply (linearHomComplexPrecompHomologyData R f X n).quasiIso_iff.mpr
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (homClassPrecomp R f X n)
  constructor
  · intro a b hab
    apply (CohomologyClass.homAddEquiv (K := L) (L := X) (n := n)).injective
    apply (h n).injective
    change (HomotopyCategory.quotient A (.up ℤ)).map f ≫ CohomologyClass.toHom a =
      (HomotopyCategory.quotient A (.up ℤ)).map f ≫ CohomologyClass.toHom b
    rw [← homClassPrecomp_toHom R f X n a, ← homClassPrecomp_toHom R f X n b, hab]
  · intro a
    obtain ⟨b, hb⟩ := (h n).surjective (CohomologyClass.toHom a)
    obtain ⟨z, rfl⟩ := (CohomologyClass.homAddEquiv (K := L) (L := X) (n := n)).surjective b
    refine ⟨z, (CohomologyClass.homAddEquiv (K := K) (L := X) (n := n)).injective ?_⟩
    exact (homClassPrecomp_toHom R f X n z).trans hb

end ToricPower
