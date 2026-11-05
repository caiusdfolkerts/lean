module

public import PaperVerification.ToricCartierCharacterModules
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

/-!
# Actual closed orbit charts

A face of an additive semigroup gives a genuine quotient of its semigroup
algebra: characters outside the face map to zero, and characters on the face
remain their actual basis characters. The quotient map has an explicit right
inverse as a linear map (indeed an algebra map), so it induces an actual
closed immersion of affine schemes. Applied to a cone, the face consists
of characters vanishing on the specified cone rays.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {M : Type*} [AddCommMonoid M]

/-- The intrinsic additive face condition. -/
def IsAdditiveFace (F : AddSubmonoid M) : Prop :=
  ∀ m p : M, m+p∈F → m∈F ∧ p∈F

theorem additiveFace_add_iff (F : AddSubmonoid M) (hF : IsAdditiveFace F)
    (m p : M) : m+p∈F ↔ m∈F ∧ p∈F :=
  ⟨hF m p,fun h => F.add_mem h.1 h.2⟩

variable (k : Type*) [CommRing k]

def additiveFaceCharacter (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    Multiplicative M →* AddMonoidAlgebra k F where
  toFun m := if hm : m.toAdd∈F then single ⟨m.toAdd,hm⟩ 1 else 0
  map_one' := by simp only [toAdd_one,dif_pos F.zero_mem]; rfl
  map_mul' m p := by
    change (if h : m.toAdd+p.toAdd∈F then single (⟨m.toAdd+p.toAdd,h⟩ : F) (1 : k) else 0) = _
    by_cases hm : m.toAdd∈F <;> by_cases hp : p.toAdd∈F
    · rw [dif_pos (F.add_mem hm hp),dif_pos hm,dif_pos hp,single_mul_single,one_mul]
      rfl
    · rw [dif_neg (fun h => hp (hF _ _ h).2),dif_pos hm,dif_neg hp,mul_zero]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_pos hp,zero_mul]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_neg hp,zero_mul]

/-- The literal quotient map on semigroup algebras. -/
def additiveFaceRetraction (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    AddMonoidAlgebra k M →ₐ[k] AddMonoidAlgebra k F :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k F) M (additiveFaceCharacter k F hF)

@[simp] theorem additiveFaceRetraction_single_of_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∈F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = single ⟨m,hm⟩ a := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm,smul_single]

@[simp] theorem additiveFaceRetraction_single_of_not_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∉F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = 0 := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm]

theorem additiveFaceRetraction_surjective (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) : Function.Surjective (additiveFaceRetraction k F hF) := by
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
      refine ⟨single m.val 1,?_⟩
      exact additiveFaceRetraction_single_of_mem k F hF m.val m.property 1
  | add f g hf hg =>
      obtain ⟨f',hf'⟩ := hf
      obtain ⟨g',hg'⟩ := hg
      exact ⟨f'+g',by rw [map_add,hf',hg']⟩
  | smul a f hf =>
      obtain ⟨f',hf'⟩ := hf
      exact ⟨a • f',by rw [map_smul,hf']⟩

/-- An actual closed immersion, obtained from a surjective ring map. -/
theorem additiveFace_isClosedImmersion (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (additiveFaceRetraction k F hF).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (additiveFaceRetraction_surjective k F hF)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ}

/-- The actual semigroup face cut out by vanishing on a subcone. It is
defined inside the original dual semigroup, so every other ray pairing
retains its nonnegativity condition. -/
def orbitCharacterFace (s t : Finset (Lattice n)) : AddSubmonoid (dualConeMonoid s) where
  carrier := {m | ∀ u∈t,integerPairing u m.val=0}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [show ((m+p : dualConeMonoid s) : Lattice n)=m.val+p.val from rfl,
      integerPairing_add,hm u hu,hp u hu,zero_add]

theorem orbitCharacterFace_isAdditiveFace (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsAdditiveFace (orbitCharacterFace s t) := by
  intro m p h
  constructor
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega

variable (k : Type*) [CommRing k]

/-- The orbit-closure chart as the spectrum of its actual semigroup face. -/
def orbitClosureChart (s t : Finset (Lattice n)) : Scheme :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (orbitCharacterFace s t)))

/-- Quotienting the actual chart ring by the characters positive on the
subcone. This is a morphism of actual affine schemes. -/
def orbitClosureChartMap (s t : Finset (Lattice n)) (hts : t⊆s) :
    orbitClosureChart k s t ⟶
      Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s))) :=
  Spec.map (CommRingCat.ofHom
    ((additiveFaceRetraction k (orbitCharacterFace s t)
      (orbitCharacterFace_isAdditiveFace s t hts)).comp
        (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom).toRingHom)

instance orbitClosureChartMap_isClosedImmersion (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsClosedImmersion (orbitClosureChartMap k s t hts) := by
  apply IsClosedImmersion.spec_of_surjective
  exact (additiveFaceRetraction_surjective k (orbitCharacterFace s t)
    (orbitCharacterFace_isAdditiveFace s t hts)).comp
      (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricCharacters.additiveFaceRetraction_surjective
#print axioms PaperVerification.ToricGeometry.orbitClosureChartMap_isClosedImmersion
