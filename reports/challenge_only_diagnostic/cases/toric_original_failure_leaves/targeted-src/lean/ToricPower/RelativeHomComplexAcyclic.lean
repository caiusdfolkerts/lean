module

public import ToricPower.RelativeBoundedBelowHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Row exactness and actual Hom-complex acyclicity

The row condition used by the bounded-below homotopy construction is
exactness of the ordinary scalar-linear dual complex. It is also detected
by null homotopies of maps to single complexes. Degreewise row exactness
then makes the entire signed Hom complex acyclic in every integer degree.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Null homotopies into the actual single complexes give the precise
factorization property required in each row. -/
theorem rightHomExact_of_single_homotopy (K : CochainComplex C ℤ) (Y : C)
    (h : ∀ (q : ℤ) (f : K ⟶ (CochainComplex.singleFunctor C q).obj Y),
      Nonempty (Homotopy f 0)) : RightHomExact K Y := by
  intro n u hu
  have closed : ∀ p, (ComplexShape.up ℤ).Rel p (n+1) → K.d p (n+1) ≫ u = 0 := by
    intro p hp
    have : p = n := by simpa using hp
    subst p
    exact hu
  let f := HomologicalComplex.mkHomToSingle u closed
  obtain ⟨homotopy⟩ := h (n+1) f
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n+1) Y
  refine ⟨homotopy.hom (n+2) (n+1) ≫ e.hom, ?_⟩
  have eq := homotopy.comm (n+1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n+1) (n+2) by simp; omega),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel n (n+1) by simp),
    HomologicalComplex.single_obj_d, comp_zero, HomologicalComplex.zero_f,
    add_zero, add_zero] at eq
  have value := congrArg (fun t => t ≫ e.hom) eq
  simpa only [f, e, HomologicalComplex.mkHomToSingle_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using value.symm

/-- The ordinary contravariant Hom row, indexed in the original source degrees. -/
def rightHomRow (R : Type r) [CommRing R] [Linear R C]
    (K : CochainComplex C ℤ) (Y : C) : ChainComplex (ModuleCat.{v} R) ℤ :=
  (((linearYoneda R C).obj Y).mapHomologicalComplex (.down ℤ)).obj K.op

/-- Exactness of the literal scalar-linear row is exactly the factorization
condition, not a surrogate notion of acyclicity. -/
theorem rightHomExact_of_row_acyclic (R : Type r) [CommRing R] [Linear R C]
    (K : CochainComplex C ℤ) (Y : C) (h : (rightHomRow R K Y).Acyclic) :
    RightHomExact K Y := by
  intro n f hf
  have hex := h (n+1)
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp; omega) (by simp)] at hex
  exact (ShortComplex.moduleCat_exact_iff _).mp hex f hf

/-- Every actual cohomology class of the signed Hom complex vanishes
under degreewise row exactness and a genuine lower bound on the target. -/
theorem homClass_eq_zero_of_rightHomExact (K L : CochainComplex C ℤ)
    (d : ℤ) [L.IsStrictlyGE d] (hrow : ∀ q, RightHomExact K (L.X q))
    (n : ℤ) (x : CohomologyClass K L n) : x = 0 := by
  apply (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).injective
  rw [map_zero]
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
    ((CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)) x)
  rw [← hf]
  haveI : (L⟦n⟧).IsStrictlyGE (d-n) := L.isStrictlyGE_shift d n (d-n) (by omega)
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
  exact nonempty_homotopy_zero_of_rightHomExact K (L⟦n⟧) (d-n)
    (fun q => hrow (q+n)) f

/-- Bounded-below relative acyclic assembly for the complete actual
linear Hom complex, in all integer degrees. -/
theorem linearHomComplex_acyclic_of_rightHomExact
    (R : Type r) [CommRing R] [Linear R C]
    (K L : CochainComplex C ℤ) (d : ℤ) [L.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) :
    (linearHomComplex R K L).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  haveI : Subsingleton (CohomologyClass K L n) :=
    ⟨fun x y => (homClass_eq_zero_of_rightHomExact K L d hrow n x).trans
      (homClass_eq_zero_of_rightHomExact K L d hrow n y).symm⟩
  haveI : Subsingleton ((linearHomComplex R K L).homology n) :=
    (HomComplex.homologyLinearEquiv R K L n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end ToricPower
