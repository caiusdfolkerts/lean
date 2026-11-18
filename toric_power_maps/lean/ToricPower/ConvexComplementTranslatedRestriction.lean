module

public import ToricPower.ConvexComplementTranslation

/-!
# The ambient top class under translated support restriction

The map is the literal ambient translation followed by restriction of
relative supports. Its action on the fixed ambient top class is one.
This combines the two previously checked naturality statements, without
choosing a separate orientation on any translated convex region.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- Any actual pair map given by a translation preserves the fixed top
class whenever the target support is contained in the translated source. -/
theorem convexComplementTopClassIso_translatedRestriction (M : C) {n : ℕ}
    (S T : Set (Fin n → ℝ)) (z : Fin n → ℝ)
    (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (nonemptyT : T.Nonempty)
    (boundedS : Bornology.IsBounded S) (boundedT : Bornology.IsBounded T)
    (target : T ⊆ translatedRegion S z)
    (f : TopPair.ofSubset (Sᶜ : Set (TopCat.of (Fin n → ℝ))) ⟶
      TopPair.ofSubset (Tᶜ : Set (TopCat.of (Fin n → ℝ))))
    (ambient : TopPair.Hom.fst f =
      TopCat.ofHom ⟨fun p => p + z, by fun_prop⟩) :
    TopPair.singularHomologyMap f M n ≫
        (convexComplementTopClassIso M T convexT nonemptyT boundedT).hom =
      (convexComplementTopClassIso M S convexS nonemptyS boundedS).hom := by
  have equality : f = complementTranslation S z ≫ complementRestriction target := by
    apply TopPair.hom_ext_of_fst
    rw [TopPair.Hom.fst_comp]
    unfold complementTranslation complementRestriction
    erw [TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst, Category.comp_id]
    exact ambient
  rw [equality, TopPair.singularHomologyMap_comp, Category.assoc,
    convexComplementTopClassIso_natural M target convexT
      (translatedRegion_convex convexS z) nonemptyT (nonemptyS.image _)
      boundedT (translatedRegion_bounded boundedS z)]
  exact convexComplementTopClassIso_translation_to M S (translatedRegion S z) z
    convexS (translatedRegion_convex convexS z) nonemptyS (nonemptyS.image _)
    boundedS (translatedRegion_bounded boundedS z) rfl (complementTranslation S z)
    (TopPair.ofSubsetMap_fst _ _)

end ToricPower
