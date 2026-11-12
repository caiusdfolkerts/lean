module

public import ToricPower.QuasicoherentCechSequences

/-!
# A natural all-degree comparison of actual sheaf and Čech cohomology

The two cohomology theories agree canonically in degree zero. Applying
their genuine connecting maps to a chosen injective cokernel sequence in
`QCoh` constructs the higher comparisons. The middle sheaf is actually
flasque, so the required connecting maps are epic, and positive ones are
isomorphisms. Comparison maps between the chosen sequences prove
naturality in every coefficient map and every degree.

The final object is a natural isomorphism of the actual functors on
quasicoherent sheaves, rather than a family of unrelated group isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDegreeOneComparison

namespace ToricPower.CechNaturality
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {Index : Type u} [Finite Index]
  (opens : Index → X.Opens) (cover : iSup opens = ⊤)
  (affine : ∀ index, IsAffineOpen (opens index))

/-- The actual degree-one comparison applied to a chosen quasicoherent
injective embedding and its actual cokernel. -/
def quasicoherentOneIso (M : QCoh X) :
    AddCommGrpCat.of (Cohomology M.obj 1) ≅ (schemeCechComplex opens M.obj).homology 1 :=
  cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine
    (quasicoherentUnderlyingInjectiveSequence_shortExact M)

/-- The all-degree comparison built from actual quasicoherent injectives.
The choices are not asserted functorial; naturality is proved below. -/
def quasicoherentCechIso (M : QCoh X) (degree : ℕ) :
    AddCommGrpCat.of (Cohomology M.obj degree) ≅
      (schemeCechComplex opens M.obj).homology degree :=
  Nat.twoStepInduction
    (motive := fun degree => ∀ M : QCoh X,
      AddCommGrpCat.of (Cohomology M.obj degree) ≅
        (schemeCechComplex opens M.obj).homology degree)
    (fun M => zeroIso opens cover M.obj)
    (fun M => quasicoherentOneIso opens cover affine M)
    (fun degree _ previous M => higherStep opens affine
      (quasicoherentUnderlyingInjectiveSequence_shortExact M) degree
      (previous (TauCeti.injectiveCokernelSequence M).X₃)) degree M

@[simp]
theorem quasicoherentCechIso_zero (M : QCoh X) :
    quasicoherentCechIso opens cover affine M 0 = zeroIso opens cover M.obj := rfl

@[simp]
theorem quasicoherentCechIso_one (M : QCoh X) :
    quasicoherentCechIso opens cover affine M 1 =
      quasicoherentOneIso opens cover affine M := rfl

/-- The defining dimension-shift equation, kept opaque for subsequent
naturality proofs to avoid repeatedly unfolding the chosen injectives. -/
theorem quasicoherentCechIso_succ_succ (M : QCoh X) (degree : ℕ) :
    quasicoherentCechIso opens cover affine M (degree + 2) =
      higherStep opens affine (quasicoherentUnderlyingInjectiveSequence_shortExact M) degree
        (quasicoherentCechIso opens cover affine
          (TauCeti.injectiveCokernelSequence M).X₃ (degree + 1)) := by
  exact congrFun (Nat.twoStepInduction.eq_3
    (motive := fun degree => ∀ M : QCoh X,
      AddCommGrpCat.of (Cohomology M.obj degree) ≅
        (schemeCechComplex opens M.obj).homology degree)
    (fun M => zeroIso opens cover M.obj)
    (fun M => quasicoherentOneIso opens cover affine M)
    (fun degree _ previous M => higherStep opens affine
      (quasicoherentUnderlyingInjectiveSequence_shortExact M) degree
      (previous (TauCeti.injectiveCokernelSequence M).X₃)) degree) M

/-- Degree one is natural under every actual quasicoherent coefficient map. -/
@[reassoc]
theorem quasicoherentOneIso_naturality {M N : QCoh X} (mapping : M ⟶ N) :
    (cohomologyFunctor X 1).map mapping.hom ≫ (quasicoherentOneIso opens cover affine N).hom =
      (quasicoherentOneIso opens cover affine M).hom ≫
        (cechHomologyFunctor opens 1).map mapping.hom :=
  oneIso_naturality opens cover affine
    (quasicoherentUnderlyingInjectiveSequence_shortExact M)
    (quasicoherentUnderlyingInjectiveSequence_shortExact N)
    (quasicoherentUnderlyingInjectiveComparison mapping)

/-- Naturality of the all-degree comparison for every actual coefficient map. -/
@[reassoc]
theorem quasicoherentCechIso_naturality (degree : ℕ) {M N : QCoh X} (mapping : M ⟶ N) :
    (cohomologyFunctor X degree).map mapping.hom ≫
        (quasicoherentCechIso opens cover affine N degree).hom =
      (quasicoherentCechIso opens cover affine M degree).hom ≫
        (cechHomologyFunctor opens degree).map mapping.hom := by
  induction degree using Nat.twoStepInduction generalizing M N with
  | zero => exact zeroIso_naturality opens cover mapping.hom
  | one => exact quasicoherentOneIso_naturality opens cover affine mapping
  | more degree _ previous =>
    rw [quasicoherentCechIso_succ_succ, quasicoherentCechIso_succ_succ]
    exact higherStep_naturality opens affine
      (quasicoherentUnderlyingInjectiveSequence_shortExact M)
      (quasicoherentUnderlyingInjectiveSequence_shortExact N)
      (quasicoherentUnderlyingInjectiveComparison mapping) degree _ _
      (previous (injectiveCokernelComparison mapping).τ₃)

/-- Ordinary Zariski sheaf cohomology and the actual finite-affine Čech
cohomology are naturally isomorphic on the actual quasicoherent category. -/
def quasicoherentCechNatIso (degree : ℕ) :
    quasicoherentInclusion X ⋙ cohomologyFunctor X degree ≅
      quasicoherentInclusion X ⋙ cechHomologyFunctor opens degree :=
  NatIso.ofComponents (fun M => quasicoherentCechIso opens cover affine M degree)
    (fun mapping => quasicoherentCechIso_naturality opens cover affine degree mapping)

end ToricPower.CechNaturality
