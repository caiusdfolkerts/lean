module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Scalar-linear homology of unrestricted direct sums

The literal dependent finitely supported module is the categorical
coproduct. Its exactness follows from the proved AB4 property of module
categories. The resulting comparison retains the coefficient ring and
every character; it is not an additive-only dimension argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (R : Type) [CommRing R] {I : Type}

/-- The literal unrestricted algebraic direct-sum functor. -/
def sumFunctor : (Discrete I ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R where
  obj F := ModuleCat.of R (Π₀ i : I, F.obj ⟨i⟩)
  map α := ModuleCat.ofHom (DFinsupp.mapRange.linearMap (fun i : I => (α.app ⟨i⟩).hom))
  map_id F := by
    apply ModuleCat.hom_ext
    exact DFinsupp.mapRange.linearMap_id
  map_comp α β := by
    apply ModuleCat.hom_ext
    exact DFinsupp.mapRange.linearMap_comp _ _

def sumCocone (F : Discrete I ⥤ ModuleCat.{0} R) : Cocone F where
  pt := (sumFunctor R).obj F
  ι := Discrete.natTrans (fun i => ModuleCat.ofHom
    (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(F.obj ⟨j⟩)) i.as))

/-- The direct sum satisfies the actual universal property, including
its canonical inclusions. -/
def sumCoconeIsColimit (F : Discrete I ⥤ ModuleCat.{0} R) :
    IsColimit (sumCocone R F) where
  desc s := ModuleCat.ofHom (DFinsupp.lsum R (fun i : I => (s.ι.app ⟨i⟩).hom))
  fac s i := by
    rcases i with ⟨i⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFinsupp.sumAddHom_single
      (β := fun j : I => ↑(F.obj ⟨j⟩)) (γ := ↑s.pt)
      (fun j => (s.ι.app ⟨j⟩).hom.toAddMonoidHom) i x
  uniq s f compatible := by
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    exact (ConcreteCategory.congr_hom (compatible ⟨i⟩) x).trans
      (DFinsupp.sumAddHom_single
        (β := fun j : I => ↑(F.obj ⟨j⟩)) (γ := ↑s.pt)
        (fun j => (s.ι.app ⟨j⟩).hom.toAddMonoidHom) i x).symm

def sumColimitIso (F : Discrete I ⥤ ModuleCat.{0} R) :
    (sumFunctor R).obj F ≅ colimit F :=
  (sumCoconeIsColimit R F).coconePointUniqueUpToIso (colimit.isColimit F)

@[reassoc]
theorem sumColimitIso_inclusion (F : Discrete I ⥤ ModuleCat.{0} R) (i : I) :
    ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(F.obj ⟨j⟩)) i) ≫
      (sumColimitIso R F).hom = colimit.ι F ⟨i⟩ :=
  (sumCoconeIsColimit R F).fac (colimit.cocone F) ⟨i⟩

@[reassoc]
theorem sumFunctor_map_inclusion {F G : Discrete I ⥤ ModuleCat.{0} R}
    (α : F ⟶ G) (i : I) :
    ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(F.obj ⟨j⟩)) i) ≫
        (sumFunctor R).map α =
      α.app ⟨i⟩ ≫ ModuleCat.ofHom
        (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(G.obj ⟨j⟩)) i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change DFinsupp.mapRange.linearMap (fun j : I => (α.app ⟨j⟩).hom)
    (DFinsupp.single i x) = DFinsupp.single i ((α.app ⟨i⟩) x)
  simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]

def sumFunctorIsoColim : sumFunctor R (I := I) ≅ colim :=
  NatIso.ofComponents (sumColimitIso R) (by
    intro F G α
    apply (sumCoconeIsColimit R F).hom_ext
    intro i
    change ModuleCat.ofHom
        (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(F.obj ⟨j⟩)) i.as) ≫
        (sumFunctor R).map α ≫ (sumColimitIso R G).hom =
      ModuleCat.ofHom
        (DFinsupp.lsingle (R := R) (M := fun j : I => ↑(F.obj ⟨j⟩)) i.as) ≫
        (sumColimitIso R F).hom ≫ colim.map α
    rw [← Category.assoc, sumFunctor_map_inclusion, Category.assoc,
      sumColimitIso_inclusion, ← Category.assoc, sumColimitIso_inclusion, colimit.ι_map])

instance sumFunctorAdditive : (sumFunctor R (I := I)).Additive :=
  Functor.additive_of_iso (sumFunctorIsoColim R).symm

instance sumFunctorPreservesFiniteLimits : PreservesFiniteLimits (sumFunctor R (I := I)) :=
  preservesFiniteLimits_of_natIso (sumFunctorIsoColim R).symm

instance sumFunctorPreservesFiniteColimits : PreservesFiniteColimits (sumFunctor R (I := I)) :=
  preservesFiniteColimits_of_natIso (sumFunctorIsoColim R).symm

instance sumFunctorPreservesHomology : (sumFunctor R (I := I)).PreservesHomology := inferInstance

/-- A literal family of complexes, before applying the actual direct sum. -/
def familyComplex (K : I → CochainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (Discrete I ⥤ ModuleCat.{0} R) ℕ where
  X q := Discrete.functor (fun i => (K i).X q)
  d q r := Discrete.natTrans (fun i => (K i.as).d q r)
  shape q r unrelated := by
    ext i x
    exact ConcreteCategory.congr_hom ((K i.as).shape q r unrelated) x
  d_comp_d' q r t _ _ := by
    ext i x
    exact ConcreteCategory.congr_hom ((K i.as).d_comp_d q r t) x

def familyEvaluationIso (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (i : I) :
    ((((evaluation (Discrete I) (ModuleCat R)).obj ⟨i⟩).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (familyComplex R K)) ≅ K i :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun _ _ _ => by simp [familyComplex])

def familyHomologyIso (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ) :
    (familyComplex R K).homology q ≅ Discrete.functor (fun i => (K i).homology q) :=
  Discrete.natIso (fun i =>
    (((familyComplex R K).sc q).mapHomologyIso
      ((evaluation (Discrete I) (ModuleCat R)).obj i)).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso
        (familyEvaluationIso R K i.as))

/-- The actual direct-sum complex, with its full scalar module structure. -/
def complex (K : I → CochainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((sumFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj (familyComplex R K)

/-- Homology of the actual unrestricted direct sum is the actual
direct sum of homologies, as an isomorphism of modules over the same ring. -/
def homologyIso (K : I → CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ) :
    (complex R K).homology q ≅ ModuleCat.of R (Π₀ i : I, (K i).homology q) :=
  ((familyComplex R K).sc q).mapHomologyIso (sumFunctor R) ≪≫
    (sumFunctor R).mapIso (familyHomologyIso R K q)

end ToricPower.ModuleDirectSum
