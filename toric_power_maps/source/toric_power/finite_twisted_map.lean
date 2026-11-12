module

public import ToricPower.FiniteTwistedTotal

/-! # Actual chain maps between finite signed totals -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.FiniteTotal

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {width : ℕ} (first second : Fin width → CochainComplex C ℤ)
  (firstOff : ∀ a : ℤ, term first a ⟶ term first (a+1))
  (secondOff : ∀ a : ℤ, term second a ⟶ term second (a+1))
  (firstCoherent : Coherent first firstOff) (secondCoherent : Coherent second secondOff)
  (f : ∀ q : Fin width, first q ⟶ second q)

def mapTerm (a : ℤ) : term first a ⟶ term second a :=
  biproduct.map (fun q => (f q).f a)

theorem mapTerm_diagonal (a : ℤ) :
    mapTerm first second f a ≫ diagonal second a =
      diagonal first a ≫ mapTerm first second f (a+1) := by
  apply biproduct.hom_ext
  intro q
  simp only [mapTerm,diagonal,Category.assoc,biproduct.map_π,biproduct.map_π_assoc]
  rw [(f q).comm]

variable (offComm : ∀ a : ℤ,
  mapTerm first second f a ≫ secondOff a = firstOff a ≫ mapTerm first second f (a+1))

/-- The genuine morphism of total complexes, including its horizontal
commutation, with no choice of a derived representative. -/
def map : complex first firstOff firstCoherent ⟶ complex second secondOff secondCoherent :=
  CochainComplex.ofHom (mapTerm first second f) (by
    intro a
    change mapTerm first second f a ≫
      CochainComplex.of.d (term second) (differential second secondOff) a (a+1) =
        CochainComplex.of.d (term first) (differential first firstOff) a (a+1) ≫
          mapTerm first second f (a+1)
    simp only [CochainComplex.of_d,differential,comp_add,add_comp,
      mapTerm_diagonal,offComm])

@[simp]
theorem map_f (a : ℤ) :
    (map first second firstOff secondOff firstCoherent secondCoherent f offComm).f a =
      biproduct.map (fun q => (f q).f a) := rfl

end ToricPower.FiniteTotal

end
