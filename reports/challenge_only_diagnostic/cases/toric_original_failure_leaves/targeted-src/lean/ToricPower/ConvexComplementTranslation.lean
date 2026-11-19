module

public import ToricPower.ConvexComplementTopClass
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Translation preserves the chosen local top classes

For a region `S` and its translate `S + z`, use the common convex region
`conv(S ∪ (S + z))`. The straight translation homotopy carries the
complement of this common region into the complement of `S + z` at every
time. It compares the two actual relative homology maps. Naturality under
restriction then proves that the previously chosen top classes commute
with translation; no independent orientation choices are made per cell.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower

universe w v u

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]

/-- The actual translated subset of the ambient vector space. -/
def translatedRegion (S : Set E) (z : E) : Set E := (fun x => x + z) '' S

theorem translatedRegion_convex {S : Set E} (convexS : Convex ℝ S) (z : E) :
    Convex ℝ (translatedRegion S z) := by
  simpa only [translatedRegion, add_comm] using convexS.translate z

theorem translatedRegion_bounded {S : Set E} (boundedS : Bornology.IsBounded S) (z : E) :
    Bornology.IsBounded (translatedRegion S z) :=
  (isometry_add_right z).lipschitzWith.isBounded_image boundedS

/-- Translation as a map of the actual complementary pairs. -/
def complementTranslation (S : Set E) (z : E) :
    TopPair.ofSubset (Sᶜ : Set (TopCat.of E)) ⟶
      TopPair.ofSubset ((translatedRegion S z)ᶜ : Set (TopCat.of E)) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨fun x => x + z, by fun_prop⟩) (by
    rintro x hx ⟨y, hy, h⟩
    exact hx ((add_right_cancel h) ▸ hy))

/-- A common convex region for the whole straight translation homotopy. -/
def translationHull (S : Set E) (z : E) : Set E :=
  convexHull ℝ (S ∪ translatedRegion S z)

theorem subset_translationHull (S : Set E) (z : E) : S ⊆ translationHull S z :=
  subset_union_left.trans (subset_convexHull ℝ _)

theorem translatedRegion_subset_translationHull (S : Set E) (z : E) :
    translatedRegion S z ⊆ translationHull S z :=
  subset_union_right.trans (subset_convexHull ℝ _)

theorem translationHull_bounded {S : Set E} (boundedS : Bornology.IsBounded S) (z : E) :
    Bornology.IsBounded (translationHull S z) :=
  isBounded_convexHull.mpr (boundedS.union (translatedRegion_bounded boundedS z))

/-- The two maps from the common convex region agree on relative homology,
because the literal straight translation is a homotopy of pairs. -/
theorem complementTranslation_restriction (M : A) (S : Set E) (z : E) (q : ℕ) :
    TopPair.singularHomologyMap
        (complementRestriction (translatedRegion_subset_translationHull S z)) M q =
      TopPair.singularHomologyMap (complementRestriction (subset_translationHull S z)) M q ≫
        TopPair.singularHomologyMap (complementTranslation S z) M q := by
  let g : TopCat.of E ⟶ TopCat.of E := TopCat.ofHom ⟨fun x => x + z, by fun_prop⟩
  let identity : TopCat.of E ⟶ TopCat.of E := 𝟙 _
  let F : identity.hom.Homotopy g.hom :=
    { toFun p := p.2 + (p.1 : ℝ) • z
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp [identity]
      map_one_left := by intro x; simp [g] }
  have hF : ∀ (t : unitInterval) (x : TopCat.of E),
      x ∈ (translationHull S z)ᶜ → F (t, x) ∈ (translatedRegion S z)ᶜ := by
    intro t x hx translated
    obtain ⟨y, hy, equality⟩ := translated
    change y + z = x + (t : ℝ) • z at equality
    apply hx
    have hx' : x = y + (1 - (t : ℝ)) • z := by
      calc
        x = (x + (t : ℝ) • z) - (t : ℝ) • z := (add_sub_cancel_right _ _).symm
        _ = (y + z) - (t : ℝ) • z := by rw [← equality]
        _ = y + (1 - (t : ℝ)) • z := by rw [sub_smul, one_smul]; abel
    rw [hx']
    apply (convex_convexHull ℝ (S ∪ translatedRegion S z)).add_smul_mem
      (subset_translationHull S z hy)
      (translatedRegion_subset_translationHull S z ⟨y, hy, rfl⟩)
    constructor <;> linarith [t.property.1, t.property.2]
  rw [← TopPair.singularHomologyMap_comp]
  convert (TopPair.ofSubsetHomotopy F hF).congr_singularHomologyMap M q using 1
  · congr 1
  · congr 1
    apply TopPair.hom_ext_of_fst
    rw [show TopPair.Hom.fst (complementRestriction (subset_translationHull S z) ≫
        complementTranslation S z) =
        TopPair.Hom.fst (complementRestriction (subset_translationHull S z)) ≫
          TopPair.Hom.fst (complementTranslation S z) from TopPair.proj₁.map_comp _ _]
    unfold complementRestriction complementTranslation
    erw [TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst,
      Category.id_comp]

/-- Translation commutes with the coherent origin-based homology
identification in every degree. -/
theorem convexComplementHomologyIso_translation (M : A) (S : Set E) (z : E)
    (convexS : Convex ℝ S) (nonemptyS : S.Nonempty)
    (boundedS : Bornology.IsBounded S) (q : ℕ) :
    TopPair.singularHomologyMap (complementTranslation S z) M q ≫
        (convexComplementHomologyIso M (translatedRegion S z)
          (translatedRegion_convex convexS z) (nonemptyS.image _)
          (translatedRegion_bounded boundedS z) q).hom =
      (convexComplementHomologyIso M S convexS nonemptyS boundedS q).hom := by
  let W := translationHull S z
  have convexW : Convex ℝ W := convex_convexHull ℝ _
  have nonemptyW : W.Nonempty := nonemptyS.mono (subset_translationHull S z)
  have boundedW : Bornology.IsBounded W := translationHull_bounded boundedS z
  let a := TopPair.singularHomologyMap (complementRestriction (subset_translationHull S z)) M q
  letI : IsIso a := complementRestriction_isIso M (subset_translationHull S z)
    convexS convexW nonemptyS boundedS boundedW q
  apply (cancel_epi a).mp
  rw [← Category.assoc]
  change (TopPair.singularHomologyMap (complementRestriction (subset_translationHull S z)) M q ≫
      TopPair.singularHomologyMap (complementTranslation S z) M q) ≫ _ = _
  rw [← complementTranslation_restriction]
  rw [convexComplementHomologyIso_natural M
      (translatedRegion_subset_translationHull S z)
      (translatedRegion_convex convexS z) convexW (nonemptyS.image _) nonemptyW
      (translatedRegion_bounded boundedS z) boundedW q]
  exact (convexComplementHomologyIso_natural M (subset_translationHull S z)
    convexS convexW nonemptyS nonemptyW boundedS boundedW q).symm

/-- The same natural top-class statement for a separately named target
region and an actual pair map whose ambient component is translation. -/
theorem convexComplementTopClassIso_translation_to [HasCoproducts.{0} A] (M : A) {n : ℕ}
    (S T : Set (Fin n → ℝ)) (z : Fin n → ℝ)
    (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (nonemptyT : T.Nonempty)
    (boundedS : Bornology.IsBounded S) (boundedT : Bornology.IsBounded T)
    (target : translatedRegion S z = T)
    (f : TopPair.ofSubset (Sᶜ : Set (TopCat.of (Fin n → ℝ))) ⟶
      TopPair.ofSubset (Tᶜ : Set (TopCat.of (Fin n → ℝ))))
    (ambient : TopPair.Hom.fst f =
      TopCat.ofHom ⟨fun p => p + z, by fun_prop⟩) :
    TopPair.singularHomologyMap f M n ≫
        (convexComplementTopClassIso M T convexT nonemptyT boundedT).hom =
      (convexComplementTopClassIso M S convexS nonemptyS boundedS).hom := by
  subst T
  have equality : f = complementTranslation S z := by
    apply TopPair.hom_ext_of_fst
    exact ambient.trans (TopPair.ofSubsetMap_fst _ _).symm
  rw [equality]
  simp only [convexComplementTopClassIso, Iso.trans_hom, ← Category.assoc]
  rw [convexComplementHomologyIso_translation]

end ToricPower
