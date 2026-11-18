module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor

/-!
# Homology of a literal direct sum of complexes

The direct-sum functor is identified with the genuine categorical coproduct.
Exactness is then inherited from the proved AB4 property of abelian groups.
No exactness or cohomology comparison is added as a hypothesis.

The generic proof body is ported from BondalThomsen commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb,
Toric/Cohomology/CechWeightHomologyDirectSum.lean, lines 20–146.
Candidate source, pending pinned compilation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open scoped Classical DirectSum

namespace ToricPower.CechDirectSumHomology

noncomputable section

variable {Index : Type}

/-- A direct sum vanishes exactly when every actual summand vanishes.
The index set is unrestricted, so this applies to the full character lattice. -/
theorem directSum_subsingleton_iff (family : Index → AddCommGrpCat.{0}) :
    Subsingleton (DirectSum Index (fun index => ↑(family index))) ↔
      ∀ index, Subsingleton (family index) := by
  constructor
  · intro trivial index
    refine ⟨fun first second => ?_⟩
    exact DirectSum.of_injective (β := fun index => ↑(family index)) index
      (trivial.elim _ _)
  · intro trivial
    refine ⟨fun first second => ?_⟩
    ext index
    exact (trivial index).elim _ _

/-- Nonvanishing of an all-character direct sum is witnessed by one character. -/
theorem directSum_nontrivial_iff (family : Index → AddCommGrpCat.{0}) :
    Nontrivial (DirectSum Index (fun index => ↑(family index))) ↔
      ∃ index, Nontrivial (family index) := by
  classical
  simpa only [not_subsingleton_iff_nontrivial, not_forall] using
    not_congr (directSum_subsingleton_iff family)

def directSumFunctor : (Discrete Index ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0} where
  obj family := AddCommGrpCat.of (DirectSum Index (fun index => ↑(family.obj ⟨index⟩)))
  map transformation := AddCommGrpCat.ofHom (DirectSum.map
    (fun index => (transformation.app ⟨index⟩).hom))
  map_id family := by
    apply AddCommGrpCat.hom_ext
    exact DirectSum.map_id
  map_comp first second := by
    apply AddCommGrpCat.hom_ext
    exact DirectSum.map_comp _ _

/-- A specified family of genuine additive isomorphisms induces an
isomorphism on the literal direct sums. The two coefficient functors are
explicit, so no equality of unrelated group presentations is inferred. -/
def directSumIso (first second : Index → AddCommGrpCat.{0})
    (equivalence : ∀ index, first index ≅ second index) :
    AddCommGrpCat.of (DirectSum Index (fun index => ↑(first index))) ≅
      AddCommGrpCat.of (DirectSum Index (fun index => ↑(second index))) :=
  directSumFunctor.mapIso
    (Discrete.natIso (F := Discrete.functor first) (G := Discrete.functor second)
      (fun index => equivalence index.as))

def directSumCocone (family : Discrete Index ⥤ AddCommGrpCat.{0}) : Cocone family where
  pt := directSumFunctor.obj family
  ι := Discrete.natTrans (fun index =>
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(family.obj ⟨index⟩)) index.as))

def directSumCoconeIsColimit (family : Discrete Index ⥤ AddCommGrpCat.{0}) :
    IsColimit (directSumCocone family) where
  desc cocone := AddCommGrpCat.ofHom (DirectSum.toAddMonoid
    (β := fun index => ↑(family.obj ⟨index⟩)) (fun index => (cocone.ι.app ⟨index⟩).hom))
  fac cocone index := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro element
    exact DirectSum.toAddMonoid_of (β := fun index => ↑(family.obj ⟨index⟩)) (γ := ↑cocone.pt)
      (fun index => (cocone.ι.app ⟨index⟩).hom) index.as element
  uniq cocone morphism compatible := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro index element
    exact (ConcreteCategory.congr_hom (compatible ⟨index⟩) element).trans
      (DirectSum.toAddMonoid_of (β := fun index => ↑(family.obj ⟨index⟩)) (γ := ↑cocone.pt)
        (fun index => (cocone.ι.app ⟨index⟩).hom) index element).symm

def directSumColimitIso (family : Discrete Index ⥤ AddCommGrpCat.{0}) :
    directSumFunctor.obj family ≅ colimit family :=
    (directSumCoconeIsColimit family).coconePointUniqueUpToIso
      (colimit.isColimit family)

theorem directSumColimitIso_inclusion (family : Discrete Index ⥤ AddCommGrpCat.{0}) (index : Index) :
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(family.obj ⟨index⟩)) index) ≫
      (directSumColimitIso family).hom = colimit.ι family ⟨index⟩ := by
  exact (directSumCoconeIsColimit family).fac (colimit.cocone family) ⟨index⟩

theorem directSumFunctor_map_of {source target : Discrete Index ⥤ AddCommGrpCat.{0}}
    (transformation : source ⟶ target) (index : Index) :
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(source.obj ⟨index⟩)) index) ≫
      directSumFunctor.map transformation = transformation.app ⟨index⟩ ≫
        AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(target.obj ⟨index⟩)) index) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro element
  exact DirectSum.map_of _ _ _

def directSumFunctorIsoColim :
    directSumFunctor (Index := Index) ≅ colim :=
  NatIso.ofComponents directSumColimitIso (by
    intro source target transformation
    apply (directSumCoconeIsColimit source).hom_ext
    intro index
    change AddCommGrpCat.ofHom (DirectSum.of _ index.as) ≫
        directSumFunctor.map transformation ≫ (directSumColimitIso target).hom =
      AddCommGrpCat.ofHom (DirectSum.of _ index.as) ≫
        (directSumColimitIso source).hom ≫ colim.map transformation
    rw [← Category.assoc, directSumFunctor_map_of, Category.assoc,
      directSumColimitIso_inclusion, ← Category.assoc,
      directSumColimitIso_inclusion, colimit.ι_map])

instance directSumFunctorAdditive : (directSumFunctor (Index := Index)).Additive :=
  Functor.additive_of_iso directSumFunctorIsoColim.symm

instance directSumFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (directSumFunctor (Index := Index)) :=
  preservesFiniteLimits_of_natIso directSumFunctorIsoColim.symm

instance directSumFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (directSumFunctor (Index := Index)) :=
  preservesFiniteColimits_of_natIso directSumFunctorIsoColim.symm

instance directSumFunctorPreservesHomology :
    (directSumFunctor (Index := Index)).PreservesHomology := inferInstance

def familyComplex (family : Index → CochainComplex AddCommGrpCat.{0} ℕ) :
    CochainComplex (Discrete Index ⥤ AddCommGrpCat.{0}) ℕ where
  X degree := Discrete.functor (fun index => (family index).X degree)
  d degree next := Discrete.natTrans (fun index => (family index.as).d degree next)
  shape degree next unrelated := by
    ext index element
    exact ConcreteCategory.congr_hom ((family index.as).shape degree next unrelated) element
  d_comp_d' first second third relatedFirst relatedSecond := by
    ext index element
    exact ConcreteCategory.congr_hom ((family index.as).d_comp_d first second third) element

def familyComplexEvaluationIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (index : Index) :
    (((evaluation (Discrete Index) AddCommGrpCat).obj ⟨index⟩).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (familyComplex family) ≅ family index :=
  HomologicalComplex.Hom.isoOfComponents (fun degree => Iso.refl _)
    (fun degree next related => by simp [familyComplex])

def familyComplexHomologyIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) :
    (familyComplex family).homology degree ≅
      Discrete.functor (fun index => (family index).homology degree) :=
  Discrete.natIso (fun index =>
    (((familyComplex family).sc degree).mapHomologyIso
      ((evaluation (Discrete Index) AddCommGrpCat).obj index)).symm ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
          (familyComplexEvaluationIso family index.as))

def directSumFamilyComplexHomologyIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) :
    ((directSumFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (familyComplex family)).homology degree ≅
        AddCommGrpCat.of (DirectSum Index (fun index => ↑((family index).homology degree))) :=
  ((familyComplex family).sc degree).mapHomologyIso directSumFunctor ≪≫
    directSumFunctor.mapIso (familyComplexHomologyIso family degree)

end

end ToricPower.CechDirectSumHomology
