module

public import ToricPower.ComplexCoconeShortExact
public import ToricPower.MappingConeAcyclicCriterion
public import ToricPower.ModuleComplexFreeVanishing
public import ToricPower.NaturalComplexCoproductComparison
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# A bounded exact natural comparison is determined on the free rank-one module

The comparison here is the given natural transformation. Coproducts
first give its quasi-isomorphism on every unrestricted free module.
The actual mapping cone is exact in the coefficient module and has a
uniform upper degree bound. Free-cover dimension shifting therefore
annihilates it on every module. No finite resolution or cardinality
restriction is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower

variable (R k : Type) [CommRing R] [CommRing k]
  {ι : Type*} {shape : ComplexShape ι}
  {F G : ModuleCat.{0} R ⥤ HomologicalComplex (ModuleCat.{0} k) shape}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

/-- The original comparison on a free module of any cardinality. -/
theorem naturalComparison_free_quasiIso
    (preservesF : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) F)
    (preservesG : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) G)
    (rankOne : QuasiIso (τ.app (ModuleCat.of R R))) (I : Type) :
    QuasiIso (τ.app (ModuleCat.of R (I →₀ R))) := by
  letI := preservesF I
  letI := preservesG I
  letI := rankOne
  let family : I → ModuleCat.{0} R := fun _ => ModuleCat.of R R
  haveI : QuasiIso (τ.app (∐ family)) := naturalComparison_coproduct_quasiIso τ family
  let e : (∐ family) ≅ ModuleCat.of R (I →₀ R) :=
    colimit.isoColimitCocone ⟨ModuleCat.finsuppCocone R R I,
      ModuleCat.finsuppCoconeIsColimit R R I⟩
  haveI : QuasiIso (F.map e.hom ≫ τ.app (ModuleCat.of R (I →₀ R))) := by
    rw [τ.naturality]
    infer_instance
  exact quasiIso_of_comp_left (F.map e.hom) _

section IntegerComplexes

variable {F G : ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} k) ℤ}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

/-- Exactness and a common upper term bound extend the free-module result
to every coefficient module through its actual, possibly infinite, free covers. -/
theorem naturalComparison_quasiIso_of_bounded_exact_free
    (exactF : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map F).ShortExact)
    (exactG : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map G).ShortExact)
    (bound : ℤ)
    (aboveF : ∀ (M : ModuleCat.{0} R) (q : ℤ), bound < q → IsZero ((F.obj M).X q))
    (aboveG : ∀ (M : ModuleCat.{0} R) (q : ℤ), bound < q → IsZero ((G.obj M).X q))
    (free : ∀ I : Type, QuasiIso (τ.app (ModuleCat.of R (I →₀ R)))) (M : ModuleCat.{0} R) :
    QuasiIso (τ.app M) := by
  apply (quasiIso_iff_mappingCone_acyclic (τ.app M)).mpr
  apply moduleComplexFunctor_acyclic_of_boundedTerms_free R k
    (ComplexCone.coneFunctor τ) _ bound _ _ M
  · intro S exact
    exact ComplexCone.coneFunctor_map_shortExact τ S (exactF S exact) (exactG S exact)
  · intro N q high
    exact (mappingCone.isZero_X_iff (τ.app N) q).mpr
      ⟨aboveF N (q+1) (by omega), aboveG N q high⟩
  · intro I
    exact (quasiIso_iff_mappingCone_acyclic _).mp (free I)

/-- The single rank-one calculation, with exactness, coproducts and
a uniform degree bound, determines the given comparison on all modules. -/
theorem naturalComparison_quasiIso_of_bounded_exact_rankOne
    (exactF : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map F).ShortExact)
    (exactG : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map G).ShortExact)
    (preservesF : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) F)
    (preservesG : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) G)
    (bound : ℤ)
    (aboveF : ∀ (M : ModuleCat.{0} R) (q : ℤ), bound < q → IsZero ((F.obj M).X q))
    (aboveG : ∀ (M : ModuleCat.{0} R) (q : ℤ), bound < q → IsZero ((G.obj M).X q))
    (rankOne : QuasiIso (τ.app (ModuleCat.of R R))) (M : ModuleCat.{0} R) :
    QuasiIso (τ.app M) :=
  naturalComparison_quasiIso_of_bounded_exact_free R k τ exactF exactG bound
    aboveF aboveG (naturalComparison_free_quasiIso R k τ preservesF preservesG rankOne) M

end IntegerComplexes

end ToricPower
end
