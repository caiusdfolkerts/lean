module

public import ToricPower.ConvexComplementHomology

/-! # Coherent top classes in the actual intrinsic vector space

The ambient space may be a proper linear subspace of the character
space. Its intrinsic dimension determines the degree. The orientation
is fixed once at its origin, and every bounded convex-support comparison
is the actual relative singular homology restriction map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower

universe w v u
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]

def intrinsicOriginTopClassIso (M : A) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomology M
      (Module.finrank ℝ E) ≅ M := by
  generalize dimension : Module.finrank ℝ E = n
  cases n with
  | zero =>
      exact TauCeti.singularHomologyComplSingletonIsoOfFinrankEqZero (E := E) M
        (OpenPartialHomeomorph.refl E) (by trivial) dimension
  | succ n =>
      exact TauCeti.singularHomologyComplSingletonIsoOfFinrankEq (E := E) M
        (OpenPartialHomeomorph.refl E) (by trivial) dimension

def intrinsicConvexTopClassIso (M : A) (S : Set E)
    (convexS : Convex ℝ S) (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S) :
    (TopPair.ofSubset (Sᶜ : Set (TopCat.of E))).singularHomology M
      (Module.finrank ℝ E) ≅ M :=
  convexComplementHomologyIso M S convexS nonemptyS boundedS (Module.finrank ℝ E) ≪≫
    intrinsicOriginTopClassIso M

theorem intrinsicConvexHomology_isZero (M : A) (S : Set E)
    (convexS : Convex ℝ S) (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S)
    (q : ℕ) (different : q ≠ Module.finrank ℝ E) :
    IsZero ((TopPair.ofSubset (Sᶜ : Set (TopCat.of E))).singularHomology M q) :=
  (TauCeti.isZero_singularHomology_complSingleton_of_ne M
    (OpenPartialHomeomorph.refl E) (x := 0) (by trivial) rfl different).of_iso
      (convexComplementHomologyIso M S convexS nonemptyS boundedS q)

theorem intrinsicConvexTopClassIso_natural (M : A) {S T : Set E}
    (included : S ⊆ T) (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (nonemptyT : T.Nonempty)
    (boundedS : Bornology.IsBounded S) (boundedT : Bornology.IsBounded T) :
    TopPair.singularHomologyMap (complementRestriction included) M (Module.finrank ℝ E) ≫
      (intrinsicConvexTopClassIso M S convexS nonemptyS boundedS).hom =
        (intrinsicConvexTopClassIso M T convexT nonemptyT boundedT).hom := by
  simp only [intrinsicConvexTopClassIso,Iso.trans_hom,← Category.assoc]
  rw [convexComplementHomologyIso_natural]

end ToricPower

end
