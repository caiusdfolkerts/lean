module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Natural local homology of bounded convex regions

The pair associated with a region `U` is `(E,E \ U)`. For nested nonempty
bounded convex regions, the actual restriction on relative singular homology
is an isomorphism: compare both regions with any point in the smaller one.

To choose these isomorphisms coherently, place `U` and the origin in the
common convex hull `conv(U ∪ {0})`. The two restriction maps identify its
homology with that of `U` and with the fixed local homology at the origin.
The resulting identification is proved natural under all inclusions. Thus
the top classes are not independently chosen rank-one identifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower

universe w v u

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]

/-- Restriction of relative support, on the actual ambient space. -/
def complementRestriction {S T : Set E} (h : S ⊆ T) :
    TopPair.ofSubset (Tᶜ : Set (TopCat.of E)) ⟶
      TopPair.ofSubset (Sᶜ : Set (TopCat.of E)) :=
  TopPair.ofSubsetMap (𝟙 (TopCat.of E)) (Set.compl_subset_compl.mpr h)

@[simp]
theorem complementRestriction_comp {S T U : Set E} (hST : S ⊆ T) (hTU : T ⊆ U) :
    complementRestriction hTU ≫ complementRestriction hST =
      complementRestriction (hST.trans hTU) := by
  simpa only [complementRestriction, Category.id_comp] using
    (TopPair.ofSubsetMap_comp (𝟙 (TopCat.of E)) (𝟙 (TopCat.of E))
      (B := Uᶜ) (B' := Tᶜ) (B'' := Sᶜ)
      (Set.compl_subset_compl.mpr hTU) (Set.compl_subset_compl.mpr hST)
      (by
        intro x hx
        simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
          (Set.compl_subset_compl.mpr (hST.trans hTU) hx))).symm

/-- Nonempty nested bounded convex regions have the same relative
homology, by their actual restriction map in every degree. -/
theorem complementRestriction_isIso (M : A) {S T : Set E}
    (hST : S ⊆ T) (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S)
    (boundedT : Bornology.IsBounded T) (q : ℕ) :
    IsIso (TopPair.singularHomologyMap (complementRestriction hST) M q) := by
  obtain ⟨x, hx⟩ := nonemptyS
  let hxS : {x} ⊆ S := singleton_subset_iff.mpr hx
  let hxT : {x} ⊆ T := singleton_subset_iff.mpr (hST hx)
  letI : IsIso (TopPair.singularHomologyMap (complementRestriction hxS) M q) :=
    TauCeti.isIso_singularHomologyMap_compl_of_starConvex M
      (convexS.starConvex hx) hx boundedS q
  have localT : IsIso (TopPair.singularHomologyMap
      (complementRestriction (hxS.trans hST)) M q) :=
    TauCeti.isIso_singularHomologyMap_compl_of_starConvex M
      (convexT.starConvex (hST hx)) (hST hx) boundedT q
  have composite : IsIso (TopPair.singularHomologyMap (complementRestriction hST) M q ≫
      TopPair.singularHomologyMap (complementRestriction hxS) M q) := by
    rw [← TopPair.singularHomologyMap_comp, complementRestriction_comp]
    exact localT
  exact IsIso.of_isIso_comp_right _
    (TopPair.singularHomologyMap (complementRestriction hxS) M q)

/-- A functorial common convex region containing the given region and
the fixed reference point. -/
def originHull (S : Set E) : Set E := convexHull ℝ (insert 0 S)

theorem subset_originHull (S : Set E) : S ⊆ originHull S :=
  (subset_insert 0 S).trans (subset_convexHull ℝ _)

theorem zero_mem_originHull (S : Set E) : (0 : E) ∈ originHull S :=
  subset_convexHull ℝ _ (mem_insert 0 S)

theorem originHull_mono {S T : Set E} (h : S ⊆ T) : originHull S ⊆ originHull T :=
  convexHull_mono (insert_subset_insert h)

theorem originHull_convex (S : Set E) : Convex ℝ (originHull S) :=
  convex_convexHull ℝ _

theorem originHull_bounded {S : Set E} (h : Bornology.IsBounded S) :
    Bornology.IsBounded (originHull S) :=
  isBounded_convexHull.mpr (h.insert 0)

/-- The chosen local-homology identification with the origin is built
from actual restriction maps through one common convex region. -/
def convexComplementHomologyIso (M : A) (S : Set E) (convexS : Convex ℝ S)
    (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S) (q : ℕ) :
    (TopPair.ofSubset (Sᶜ : Set (TopCat.of E))).singularHomology M q ≅
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomology M q := by
  letI := complementRestriction_isIso M (subset_originHull S) convexS
    (originHull_convex S) nonemptyS boundedS (originHull_bounded boundedS) q
  let zero_subset : {(0 : E)} ⊆ originHull S := singleton_subset_iff.mpr (zero_mem_originHull S)
  letI := complementRestriction_isIso M zero_subset (convex_singleton 0)
    (originHull_convex S) (singleton_nonempty 0) (Bornology.isBounded_singleton)
    (originHull_bounded boundedS) q
  exact (asIso (TopPair.singularHomologyMap (complementRestriction (subset_originHull S)) M q)).symm ≪≫
    asIso (TopPair.singularHomologyMap (complementRestriction zero_subset) M q)

/-- The chosen identifications commute with every inclusion of nonempty
bounded convex regions. This fixes the top-class naturality needed in
the cellular costalk calculation. -/
theorem convexComplementHomologyIso_natural (M : A) {S T : Set E}
    (hST : S ⊆ T) (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (nonemptyT : T.Nonempty)
    (boundedS : Bornology.IsBounded S) (boundedT : Bornology.IsBounded T) (q : ℕ) :
    TopPair.singularHomologyMap (complementRestriction hST) M q ≫
        (convexComplementHomologyIso M S convexS nonemptyS boundedS q).hom =
      (convexComplementHomologyIso M T convexT nonemptyT boundedT q).hom := by
  let aS := TopPair.singularHomologyMap (complementRestriction (subset_originHull S)) M q
  let aT := TopPair.singularHomologyMap (complementRestriction (subset_originHull T)) M q
  let c := TopPair.singularHomologyMap (complementRestriction (originHull_mono hST)) M q
  let bS := TopPair.singularHomologyMap
    (complementRestriction (singleton_subset_iff.mpr (zero_mem_originHull S))) M q
  let bT := TopPair.singularHomologyMap
    (complementRestriction (singleton_subset_iff.mpr (zero_mem_originHull T))) M q
  let r := TopPair.singularHomologyMap (complementRestriction hST) M q
  letI : IsIso aS := complementRestriction_isIso M (subset_originHull S) convexS
    (originHull_convex S) nonemptyS boundedS (originHull_bounded boundedS) q
  letI : IsIso aT := complementRestriction_isIso M (subset_originHull T) convexT
    (originHull_convex T) nonemptyT boundedT (originHull_bounded boundedT) q
  have square : aT ≫ r = c ≫ aS := by
    dsimp only [aT, r, c, aS]
    rw [← TopPair.singularHomologyMap_comp, complementRestriction_comp,
      ← TopPair.singularHomologyMap_comp, complementRestriction_comp]
  have atOrigin : c ≫ bS = bT := by
    dsimp only [c, bS, bT]
    rw [← TopPair.singularHomologyMap_comp, complementRestriction_comp]
  change r ≫ (inv aS ≫ bS) = inv aT ≫ bT
  apply (cancel_epi aT).mp
  calc
    aT ≫ (r ≫ (inv aS ≫ bS)) = (aT ≫ r) ≫ inv aS ≫ bS := by simp only [Category.assoc]
    _ = (c ≫ aS) ≫ inv aS ≫ bS := by rw [square]
    _ = c ≫ bS := by simp
    _ = bT := atOrigin
    _ = aT ≫ (inv aT ≫ bT) := by simp

end ToricPower
