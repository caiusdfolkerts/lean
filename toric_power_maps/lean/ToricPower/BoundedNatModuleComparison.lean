module

public import ToricPower.BoundedModuleComparison
public import ToricPower.FiniteCochainSourceBounds
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Rank-one comparison for bounded nonnegative coefficient complexes

Extension by zero preserves the original short exact coefficient
sequences and the actual comparison map. It transports the finite
horizontal bound to integer degrees, where the mapping-cone
dimension-shifting argument applies.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

theorem natCochain_extend_shortExact
    {B : Type*} [Category* B] [Abelian B]
    (S : ShortComplex (CochainComplex B ℕ)) (exact : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor B)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro q
  by_cases nonnegative : 0 ≤ q
  · have equality : ComplexShape.embeddingUpNat.f q.toNat = q :=
      Int.toNat_of_nonneg nonnegative
    let e := ComplexShape.embeddingUpNat.extendFunctorCompEvalIso B equality
    exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso e)).mpr
      (exact.map_of_exact (HomologicalComplex.eval B (.up ℕ) q.toNat))
  · have outside : ∀ a : ℕ, ComplexShape.embeddingUpNat.f a ≠ q := by
      intro a equality
      change (a : ℤ) = q at equality
      omega
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _
          (S.X₂.isZero_extend_X ComplexShape.embeddingUpNat q outside)
        mono_f := (S.X₁.isZero_extend_X ComplexShape.embeddingUpNat q outside).mono _
        epi_g := (S.X₃.isZero_extend_X ComplexShape.embeddingUpNat q outside).epi _ }

variable (R k : Type) [CommRing R] [CommRing k]
  {F G : ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} k) ℕ}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

/-- The original natural transformation is a quasi-isomorphism on every
module, given its actual rank-one calculation and the stated exactness,
coproduct and uniform term-bound properties. -/
theorem naturalComparison_nat_quasiIso_of_bounded_exact_rankOne
    (exactF : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map F).ShortExact)
    (exactG : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map G).ShortExact)
    (preservesF : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) F)
    (preservesG : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) G)
    (bound : ℕ)
    (aboveF : ∀ (M : ModuleCat.{0} R) (q : ℕ), bound < q → IsZero ((F.obj M).X q))
    (aboveG : ∀ (M : ModuleCat.{0} R) (q : ℕ), bound < q → IsZero ((G.obj M).X q))
    (rankOne : QuasiIso (τ.app (ModuleCat.of R R))) (M : ModuleCat.{0} R) :
    QuasiIso (τ.app M) := by
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} k)
  apply (quasiIso_extendMap_iff (τ.app M) ComplexShape.embeddingUpNat).mp
  apply naturalComparison_quasiIso_of_bounded_exact_free R k (Functor.whiskerRight τ E)
    (fun S h => natCochain_extend_shortExact (S.map F) (exactF S h))
    (fun S h => natCochain_extend_shortExact (S.map G) (exactG S h)) (bound : ℤ)
  · intro N q high
    exact finiteCochain_extend_isZero_outside (F.obj N) (bound+1)
      (fun a ha => aboveF N a (by omega)) q (by omega)
  · intro N q high
    exact finiteCochain_extend_isZero_outside (G.obj N) (bound+1)
      (fun a ha => aboveG N a (by omega)) q (by omega)
  · intro I
    exact (quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).mpr
      (naturalComparison_free_quasiIso R k τ preservesF preservesG rankOne I)

end ToricPower
end
