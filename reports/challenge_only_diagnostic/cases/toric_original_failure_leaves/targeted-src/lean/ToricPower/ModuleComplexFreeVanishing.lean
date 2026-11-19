module

public import ToricPower.BoundedExactFreeVanishing

/-! # The module-category interface for exact free-cover dimension shifting

Fixing the target abelian category here keeps its inherited zero and
preadditive structures uniform when large geometric functors specialize
the general dimension-shifting theorem.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

theorem moduleComplexFunctor_acyclic_of_bounded_free
    (R k : Type u) [Ring R] [Ring k]
    (F : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} k) ℤ)
    [F.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{u} R),
      S.ShortExact → (S.map F).ShortExact)
    (bound : ℤ)
    (above : ∀ (M : ModuleCat.{u} R) (q : ℤ), bound < q →
      IsZero ((F.obj M).homology q))
    (free : ∀ I : Type u, (F.obj (ModuleCat.of R (I →₀ R))).Acyclic)
    (M : ModuleCat.{u} R) : (F.obj M).Acyclic :=
  exactComplexFunctor_acyclic_of_bounded_free R F exact bound above free M

/-- A literal upper bound on the terms supplies the homology bound. -/
theorem moduleComplexFunctor_acyclic_of_boundedTerms_free
    (R k : Type u) [Ring R] [Ring k]
    (F : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} k) ℤ)
    [F.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{u} R),
      S.ShortExact → (S.map F).ShortExact)
    (bound : ℤ)
    (above : ∀ (M : ModuleCat.{u} R) (q : ℤ), bound < q →
      IsZero ((F.obj M).X q))
    (free : ∀ I : Type u, (F.obj (ModuleCat.of R (I →₀ R))).Acyclic)
    (M : ModuleCat.{u} R) : (F.obj M).Acyclic := by
  apply moduleComplexFunctor_acyclic_of_bounded_free R k F exact bound _ free M
  intro N q high
  exact ShortComplex.isZero_homology_of_isZero_X₂ ((F.obj N).sc q) (above N q high)

end ToricPower

end
