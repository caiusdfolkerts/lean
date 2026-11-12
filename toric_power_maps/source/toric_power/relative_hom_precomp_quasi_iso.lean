module

public import ToricPower.LinearHomComplexPrecomp
public import ToricPower.ProjectiveAugmentationRows
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Bounded-below Čech assembly as an actual quasi-isomorphism

The augmentation of a projective resolution induces a quasi-isomorphism
on complete signed Hom complexes whenever its augmented coefficient
rows are exact and the target complex is bounded below. The proof uses
the literal cone, its explicit relative null homotopies, and the exact
Hom sequence of its distinguished triangle. It proves the actual
precomposition map, not just an abstract equality of homology groups.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open CochainComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The constructed null homotopies kill every actual homotopy-category map. -/
theorem homotopyHom_eq_zero_of_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [L.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q))
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) : f = 0 := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
  exact (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
    (nonempty_homotopy_zero_of_rightHomExact K L d hrow f)

/-- The same vanishing with a genuinely shifted source, transported by
the actual shift adjunction and quotient shift isomorphism. -/
theorem shiftedHomotopyHom_eq_zero_of_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [L.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) (n : ℤ)
    (f : ((HomotopyCategory.quotient C (.up ℤ)).obj K)⟦n⟧ ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) : f = 0 := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  letI : (shiftEquiv (HomotopyCategory C (.up ℤ)) n).functor.Additive :=
    inferInstanceAs (CategoryTheory.Functor.Additive
      (CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) n))
  let adj := (shiftEquiv (HomotopyCategory C (.up ℤ)) n).toAdjunction
  let e := (Q.commShiftIso (-n)).app L
  have : (L⟦-n⟧).IsStrictlyGE (d+n) := L.isStrictlyGE_shift d (-n) (d+n) (by omega)
  have eq := homotopyHom_eq_zero_of_rightHomExact K (L⟦-n⟧) (d+n)
    (fun q => hrow (q + -n)) (adj.homEquiv _ _ f ≫ e.inv)
  apply (adj.homEquiv _ _).injective
  rw [adj.homAddEquiv_zero]
  apply (cancel_mono e.inv).mp
  simpa only [zero_comp] using eq

/-- Exact rows of the actual augmentation cone make precomposition
bijective into every bounded-below target in the homotopy category. -/
theorem cone_rowExact_precomp_bijective
    {K L : CochainComplex C ℤ} (ε : K ⟶ L)
    (X : CochainComplex C ℤ) (d : ℤ) [X.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact (mappingCone ε) (X.X q)) :
    Function.Bijective (fun f : (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj X =>
      (HomotopyCategory.quotient C (.up ℤ)).map ε ≫ f) := by
  let T := mappingCone.triangleh ε
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished ε
  constructor
  · intro a b hab
    change T.mor₁ ≫ a = T.mor₁ ≫ b at hab
    have closed : T.mor₁ ≫ (a-b) = 0 := by
      simpa only [comp_sub, sub_eq_zero] using hab
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT (a-b) closed
    have gz := homotopyHom_eq_zero_of_rightHomExact (mappingCone ε) X d hrow g
    apply sub_eq_zero.mp
    rw [hg, gz, comp_zero]
  · intro a
    have closed : T.invRotate.mor₁ ≫ a = 0 :=
      shiftedHomotopyHom_eq_zero_of_rightHomExact (mappingCone ε) X d hrow (-1) _
    obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a closed
    exact ⟨g, hg.symm⟩

/-- The actual source precomposition is a quasi-isomorphism in every
integer degree; the bounded-below condition is only on the target. -/
theorem augmentation_linearHomPrecomp_quasiIso
    (R : Type r) [CommRing R] [Linear R C]
    (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (Z : C)
    (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj Z) [Epi (ε.f 0)]
    (X : CochainComplex C ℤ) (d : ℤ) [X.IsStrictlyGE d]
    (h : ∀ q, AugmentationHomExact K Z (X.X q) ε) :
    QuasiIso (linearHomComplexPrecomp R ε X) := by
  apply linearHomComplexPrecomp_quasiIso_of_homotopy_bijective
  intro n
  have : (X⟦n⟧).IsStrictlyGE (d-n) := X.isStrictlyGE_shift d n (d-n) (by omega)
  apply cone_rowExact_precomp_bijective ε (X⟦n⟧) (d-n)
  intro q
  exact rightHomExact_cone_of_single_precomp ε (X.X (q+n))
    (augmentation_single_precomp_bijective K Z (X.X (q+n)) ε (h (q+n)))

/-- Positive exactness of the ordinary projective coefficient rows
discharges the full actual bounded-below augmentation comparison. -/
theorem projective_linearHomPrecomp_quasiIso
    (R : Type r) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z)
    (X : CochainComplex C ℤ) (d : ℤ) [X.IsStrictlyGE d]
    (h : ∀ q (n : ℕ), (projectiveCoefficientComplex R P (X.X q)).ExactAt (n+1)) :
    QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P) X) :=
  augmentation_linearHomPrecomp_quasiIso R (projectiveCochain P) Z
    (projectiveCochainAugmentation P) X d
    (fun q => projectiveCochain_augmentationHomExact R P (X.X q) (h q))

end ToricPower
