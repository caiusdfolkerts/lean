module

public import ToricPower.ConvexComplementHomology
public import ToricPower.ArrangementCostalkGeometry

/-!
# The natural top class of an actual convex costalk region

Relative singular homology of `(ℝⁿ,ℝⁿ \ U)` is concentrated in degree `n`
for a nonempty bounded convex region `U`. Its top-degree copy of the
coefficient object uses the fixed local homology at the origin, so it
commutes with all support restriction maps. The final declarations apply
this calculation to the literal bounded arrangement costalk regions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower

universe v u

variable {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A]

/-- Fix the orientation once, in the local homology of the origin. The
zero-dimensional case uses its canonical augmentation. -/
def euclideanOriginLocalHomologyIso (M : A) (n : ℕ) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (Fin n → ℝ)))).singularHomology M n ≅ M := by
  cases n with
  | zero =>
      exact TauCeti.singularHomologyComplSingletonIsoOfFinrankEqZero M
        (OpenPartialHomeomorph.refl (Fin 0 → ℝ)) (by trivial) (by simp)
  | succ n =>
      exact TauCeti.singularHomologyComplSingletonIsoOfFinrankEq M
        (OpenPartialHomeomorph.refl (Fin (n + 1) → ℝ)) (by trivial) (by simp)

/-- The actual top-degree relative singular homology is one copy of the
coefficient object, with a coherent choice of that identification. -/
def convexComplementTopClassIso (M : A) {n : ℕ} (S : Set (Fin n → ℝ))
    (convexS : Convex ℝ S) (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S) :
    (TopPair.ofSubset (Sᶜ : Set (TopCat.of (Fin n → ℝ)))).singularHomology M n ≅ M :=
  convexComplementHomologyIso M S convexS nonemptyS boundedS n ≪≫
    euclideanOriginLocalHomologyIso M n

/-- All other degrees vanish, including degree zero when `n > 0`. -/
theorem convexComplementHomology_isZero (M : A) {n : ℕ} (S : Set (Fin n → ℝ))
    (convexS : Convex ℝ S) (nonemptyS : S.Nonempty) (boundedS : Bornology.IsBounded S)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((TopPair.ofSubset (Sᶜ : Set (TopCat.of (Fin n → ℝ)))).singularHomology M q) := by
  have atOrigin := TauCeti.isZero_singularHomology_complSingleton_of_ne M
    (OpenPartialHomeomorph.refl (Fin n → ℝ)) (x := 0) (by trivial)
    (by simp : Module.finrank ℝ (Fin n → ℝ) = n) different
  exact atOrigin.of_iso (convexComplementHomologyIso M S convexS nonemptyS boundedS q)

/-- Inclusion of supports sends the chosen top class to the same chosen
top class; this is equality of the actual homology maps. -/
theorem convexComplementTopClassIso_natural (M : A) {n : ℕ}
    {S T : Set (Fin n → ℝ)} (hST : S ⊆ T)
    (convexS : Convex ℝ S) (convexT : Convex ℝ T)
    (nonemptyS : S.Nonempty) (nonemptyT : T.Nonempty)
    (boundedS : Bornology.IsBounded S) (boundedT : Bornology.IsBounded T) :
    TopPair.singularHomologyMap (complementRestriction hST) M n ≫
        (convexComplementTopClassIso M S convexS nonemptyS boundedS).hom =
      (convexComplementTopClassIso M T convexT nonemptyT boundedT).hom := by
  simp only [convexComplementTopClassIso, Iso.trans_hom, ← Category.assoc]
  rw [convexComplementHomologyIso_natural]

namespace IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) (x : Fin n → ℝ)

theorem augmentedCostalkRegion_bounded :
    Bornology.IsBounded (costalkRegion (augmentedForms matrix) selected weight x) :=
  (augmented_localStar_bounded matrix x).subset Set.inter_subset_left

/-- The exact top-degree homology of the literal arrangement costalk
pair, over any coefficient object in the stated abelian category. -/
def augmentedCostalkSingularHomologyIso (M : A)
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty) :
    (TopPair.ofSubset ((costalkRegion (augmentedForms matrix) selected weight x)ᶜ :
      Set (TopCat.of (Fin n → ℝ)))).singularHomology M n ≅ M :=
  convexComplementTopClassIso M _
    (costalkRegion_convex (augmentedForms matrix) selected weight x) nonempty
    (augmentedCostalkRegion_bounded matrix selected weight x)

theorem augmentedCostalkSingularHomology_isZero (M : A)
    (nonempty : (costalkRegion (augmentedForms matrix) selected weight x).Nonempty)
    (q : ℕ) (different : q ≠ n) :
    IsZero ((TopPair.ofSubset ((costalkRegion (augmentedForms matrix) selected weight x)ᶜ :
      Set (TopCat.of (Fin n → ℝ)))).singularHomology M q) :=
  convexComplementHomology_isZero M _
    (costalkRegion_convex (augmentedForms matrix) selected weight x) nonempty
    (augmentedCostalkRegion_bounded matrix selected weight x) q different

end IntegralArrangement
end ToricPower
