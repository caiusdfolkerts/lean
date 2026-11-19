module

public import ToricPower.CoherentFoundations

/-!
# Generation depends on the set of summand isomorphism classes

The intrinsic statement uses Mathlib's actual closure under isomorphisms.
The second form accepts a parameter class map together with proved sheaf
isomorphisms for equal parameter classes. It is designed for the quotient
of toric divisor coefficients by principal character coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

section IsomorphismClasses

variable {C : Type*} [Category* C] {I J A Q : Type*}

/-- Equality of the sets of summand isomorphism classes is exactly the
existence of matching summands in both directions. Multiplicities do not
appear in this statement. -/
theorem isoClosure_ofObj_eq_iff (X : I → C) (Y : J → C) :
    (ObjectProperty.ofObj X).isoClosure = (ObjectProperty.ofObj Y).isoClosure ↔
      (∀ i, ∃ j, Nonempty (X i ≅ Y j)) ∧
        (∀ j, ∃ i, Nonempty (Y j ≅ X i)) := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := (ObjectProperty.ofObj X).le_isoClosure _ (ObjectProperty.ofObj_apply X i)
      rw [h] at hi
      obtain ⟨Z, hZ, e⟩ := hi
      obtain ⟨j⟩ := hZ
      exact ⟨j, e⟩
    · intro j
      have hj := (ObjectProperty.ofObj Y).le_isoClosure _ (ObjectProperty.ofObj_apply Y j)
      rw [← h] at hj
      obtain ⟨Z, hZ, e⟩ := hj
      obtain ⟨i⟩ := hZ
      exact ⟨i, e⟩
  · rintro ⟨hXY, hYX⟩
    ext Z
    constructor
    · rintro ⟨T, hT, ⟨e⟩⟩
      obtain ⟨i⟩ := hT
      obtain ⟨j, ⟨f⟩⟩ := hXY i
      exact ⟨Y j, ObjectProperty.ofObj_apply Y j, ⟨e ≪≫ f⟩⟩
    · rintro ⟨T, hT, ⟨e⟩⟩
      obtain ⟨j⟩ := hT
      obtain ⟨i, ⟨f⟩⟩ := hYX j
      exact ⟨X i, ObjectProperty.ofObj_apply X i, ⟨e ≪≫ f⟩⟩

/-- A proved isomorphism for equal parameter classes turns equality of
class ranges into equality of the actual summand isomorphism classes. -/
theorem isoClosure_ofObj_eq_of_class_range_eq
    (L : A → C) (q : A → Q)
    (hq : ∀ a b, q a = q b → Nonempty (L a ≅ L b))
    (a : I → A) (b : J → A)
    (h : Set.range (q ∘ a) = Set.range (q ∘ b)) :
    (ObjectProperty.ofObj (L ∘ a)).isoClosure =
      (ObjectProperty.ofObj (L ∘ b)).isoClosure := by
  apply (isoClosure_ofObj_eq_iff (L ∘ a) (L ∘ b)).2
  constructor
  · intro i
    have hi : q (a i) ∈ Set.range (q ∘ b) := by
      rw [← h]
      exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, hq (a i) (b j) hj.symm⟩
  · intro j
    have hj : q (b j) ∈ Set.range (q ∘ a) := by
      rw [h]
      exact ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hj
    exact ⟨i, hq (b j) (a i) hi.symm⟩

end IsomorphismClasses

section Coherent

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- An actual module-sheaf isomorphism between coherent objects lifts
through their fully faithful inclusion. -/
def coherentIsoOfUnderlying {M N : Coh X} (e : M.obj ≅ N.obj) : M ≅ N :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).fullyFaithfulι.preimageIso e

/-- An actual finite splitting of the underlying module sheaf gives the
corresponding splitting in the coherent category. The standard biproduct
comparison is included explicitly. -/
def coherentBiproductIsoOfUnderlying
    {I : Type*} [Finite I] (L : I → Coh X) {M : Coh X}
    (e : M.obj ≅ ⨁ (fun i => (L i).obj)) : M ≅ ⨁ L := by
  let F := (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).fullyFaithfulι.preimageIso
    (e ≪≫ (F.mapBiproduct L).symm)

/-- Actual finite coherent sums generate simultaneously whenever their
sets of actual summand isomorphism classes agree. -/
theorem coherentSameIsoClasses_generates_iff
    {I J : Type*} [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    (A : I → Coh X) (B : J → Coh X) {M N : Coh X}
    (eM : M ≅ ⨁ A) (eN : N ≅ ⨁ B)
    (h : (ObjectProperty.ofObj A).isoClosure = (ObjectProperty.ofObj B).isoClosure) :
    generatesDbCoh (coherentSingle X M) ↔ generatesDbCoh (coherentSingle X N) := by
  obtain ⟨hAB, hBA⟩ := (isoClosure_ofObj_eq_iff A B).1 h
  exact coherentSameSummands_generates_iff A B eM eN hAB hBA

/-- The class-range form used with the actual toric divisor coefficient
quotient. Equality of classes must be justified by an actual coherent
sheaf isomorphism; no injectivity or Krull--Schmidt theorem is assumed. -/
theorem coherentSameClassRanges_generates_iff
    {A Q I J : Type*} [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    (L : A → Coh X) (q : A → Q)
    (hq : ∀ a b, q a = q b → Nonempty (L a ≅ L b))
    (a : I → A) (b : J → A) {M N : Coh X}
    (eM : M ≅ ⨁ (L ∘ a)) (eN : N ≅ ⨁ (L ∘ b))
    (h : Set.range (q ∘ a) = Set.range (q ∘ b)) :
    generatesDbCoh (coherentSingle X M) ↔ generatesDbCoh (coherentSingle X N) :=
  coherentSameIsoClasses_generates_iff (L ∘ a) (L ∘ b) eM eN
    (isoClosure_ofObj_eq_of_class_range_eq L q hq a b h)

end Coherent

end ToricPower

end
