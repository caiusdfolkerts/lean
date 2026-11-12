module

public import ToricPower.ArrangementNormalizedMorseModel
public import ToricPower.ArrangementNormalizedMorseSupport
public import ToricPower.MaximalSupportFanNormal
public import ToricPower.ArrangementNormalizedSupport
public import ToricPower.ArrangementMorsePeriodicPresentation
public import ToricPower.ArrangementFanMorsePresentation

/-! # Genuine fan Morse support on every normalized derived image

The named complex is chosen together with a proved actual representative
of the unbounded derived object and its affine-model equality. Its localization is identified with the
normalized right adjoint, and the precise normal-cover Morse property
is proved on its literal universal periodic pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

local instance actualDerivedMorseQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance actualDerivedMorseCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- Every actual normalized derived image has a representative obtained
from the genuine shifted affine complex model. The existence proof
unpacks localization before choosing the output representative. -/
theorem exists_normalizedDerivedMorseModel
    (M : DerivedCategory (QCoh fan.algebraicRealization)) :
    ∃ L : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ,
      Nonempty ((arrangementNormalizedDerivedHom fan regular basis rays).obj M ≅
        DerivedCategory.Q.obj L) ∧
      HasFanLocalMorseSupport fan regular basis rays (universalPeriodicComplex A ℂ L) ∧
      ∃ K : CochainComplex (QCoh fan.algebraicRealization) ℤ,
        Nonempty (DerivedCategory.Q.obj K ≅ M) ∧
        L = (normalizedAffineMorseModel fan nonempty regular basis rays).obj K := by
  obtain ⟨K,⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (DerivedCategory.Q : CochainComplex (QCoh fan.algebraicRealization) ℤ ⥤
      DerivedCategory (QCoh fan.algebraicRealization)) M
  refine ⟨(normalizedAffineMorseModel fan nonempty regular basis rays).obj K,
    ⟨(arrangementNormalizedDerivedHom fan regular basis rays).mapIso e.symm ≪≫
      normalizedAffineMorseModelIso fan nonempty regular basis rays K⟩, ?_,
    K, ⟨e⟩, rfl⟩
  exact normalizedAffineMorseModel_hasFanLocalMorseSupport fan nonempty regular basis rays K

/-- A fixed actual representative, chosen together with its proved
localization comparison and fan-local Morse property. -/
def normalizedDerivedMorseModel (M : DerivedCategory (QCoh fan.algebraicRealization)) :
    CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ :=
  Classical.choose (exists_normalizedDerivedMorseModel fan regular basis rays M)

/-- The chosen representative models the original normalized right adjoint. -/
def normalizedDerivedMorseModelIso (M : DerivedCategory (QCoh fan.algebraicRealization)) :
    (arrangementNormalizedDerivedHom fan regular basis rays).obj M ≅
      DerivedCategory.Q.obj (normalizedDerivedMorseModel fan regular basis rays M) :=
  Classical.choice (Classical.choose_spec
    (exists_normalizedDerivedMorseModel fan regular basis rays M)).1

/-- The exact normal-cover Morse support on every unbounded derived image. -/
theorem normalizedDerivedMorseModel_hasFanLocalMorseSupport
    (M : DerivedCategory (QCoh fan.algebraicRealization)) :
    HasFanLocalMorseSupport fan regular basis rays
      (universalPeriodicComplex A ℂ (normalizedDerivedMorseModel fan regular basis rays M)) :=
  (Classical.choose_spec (exists_normalizedDerivedMorseModel fan regular basis rays M)).2.1

/-- The representative really comes from the original whole affine
model of a genuine localization preimage; this is part of its proved data. -/
theorem normalizedDerivedMorseModel_isActualAffineModel
    (M : DerivedCategory (QCoh fan.algebraicRealization)) :
    ∃ K : CochainComplex (QCoh fan.algebraicRealization) ℤ,
      Nonempty (DerivedCategory.Q.obj K ≅ M) ∧
      normalizedDerivedMorseModel fan regular basis rays M =
        (normalizedAffineMorseModel fan nonempty regular basis rays).obj K :=
  (Classical.choose_spec (exists_normalizedDerivedMorseModel fan regular basis rays M)).2.2

end ToricPower
end
