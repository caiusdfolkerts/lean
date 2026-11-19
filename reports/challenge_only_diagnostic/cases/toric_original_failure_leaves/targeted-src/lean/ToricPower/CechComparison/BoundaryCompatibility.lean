module

public import ToricPower.CechComparison.ConnectingNaturality

/-!
# The Čech comparison carries actual connecting maps to one another

The degree-one comparison is the canonical comparison of two actual
cokernels. The positive-degree step is the composite of the two actual
connecting isomorphisms. Their boundary identities make naturality a
consequence of the corresponding long exact sequence squares.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDegreeOneComparison
open BondalThomsen.FiniteAffineCechAllDegreeComparison
open BondalThomsen.FiniteAffineCechFlasqueAcyclicity
open BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity
open BondalThomsen.Ports.LeanPool

namespace ToricPower.CechNaturality
universe u

private theorem cokernelUniqueIso_π {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex C} (exact : S.Exact) [Epi S.g] :
    cokernel.π S.f ≫ (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel S.f) exact.gIsCokernel).hom = S.g :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel S.f) exact.gIsCokernel WalkingParallelPair.one

variable {X : Scheme.{u}} {Index : Type u}

@[reassoc]
theorem ordinaryCokernelIso_π {S : ShortComplex X.Modules} (exact : S.ShortExact)
    (middleZero : Subsingleton (Cohomology S.X₂ 1)) :
    cokernel.π (S.g.app ⊤) ≫ (schemeCohomologyOneCokernelIso exact middleZero).hom =
      schemeSectionsConnecting exact := by
  letI := schemeSectionsConnecting_epi exact middleZero
  exact cokernelUniqueIso_π (schemeSectionsConnecting_exact exact)

@[reassoc]
theorem cechCokernelIso_π
    {S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)} (exact : S.ShortExact)
    (middleZero : IsZero (S.X₂.homology 1)) :
    cokernel.π (HomologicalComplex.homologyMap S.g 0) ≫
      (cechOneHomologyCokernelIso exact middleZero).hom = exact.δ 0 1 rfl := by
  letI := exact.epi_δ 0 1 rfl middleZero
  exact cokernelUniqueIso_π (exact.homology_exact₃ 0 1 rfl)

@[reassoc]
theorem cohomologyBoundary_zero_eq_sections {S : ShortComplex X.Modules}
    (exact : S.ShortExact) :
    cohomologyBoundary exact 0 =
      (cohomologyZeroEquiv S.X₃).toAddCommGrpIso.hom ≫ schemeSectionsConnecting exact := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  change cohomologyδ exact 0 1 rfl value =
    cohomologyδ exact 0 1 rfl
      ((cohomologyZeroEquiv S.X₃).symm (cohomologyZeroEquiv S.X₃ value))
  rw [AddEquiv.symm_apply_apply]

variable [X.IsSeparated] [Finite Index]
  (opens : Index → X.Opens) (cover : iSup opens = ⊤)
  (affine : ∀ index, IsAffineOpen (opens index))
  {S : ShortComplex X.Modules}
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
  [S.X₂.presheaf.IsFlasque]

/-- The canonical cokernel comparison sends the boundary of an actual
global section to the actual Čech boundary of that section. -/
@[reassoc]
theorem oneIso_sections (exact : S.ShortExact) :
    schemeSectionsConnecting exact ≫
      (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine exact).hom =
    (cechZeroGlobalSectionsIso opens cover S.X₃).hom ≫
      schemeCechBoundary opens affine exact 0 := by
  let middleZero := AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque
    S.X₂ 0
  have ordinary := ordinaryCokernelIso_π exact middleZero
  have cech := cechCokernelIso_π (schemeCechComplex_shortExact opens affine exact)
    (standardCech_homology_one_isZero opens S.X₂)
  simp only [cechOneSchemeCohomologyIso_of_flasque_extension, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← ordinary, Category.assoc, Iso.hom_inv_id_assoc,
    cokernel.mapIso_hom, ← Category.assoc, cokernel.π_desc, Category.assoc]
  exact congrArg (fun morphism : (schemeCechComplex opens S.X₃).homology 0 ⟶
      (schemeCechComplex opens S.X₁).homology 1 =>
    (cechZeroGlobalSectionsIso opens cover S.X₃).hom ≫ morphism) cech

/-- Degree one carries the actual ordinary cohomology boundary to the
actual Čech boundary under the canonical degree-zero comparison. -/
@[reassoc]
theorem oneIso_boundary (exact : S.ShortExact) :
    cohomologyBoundary exact 0 ≫
      (cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine exact).hom =
    (zeroIso opens cover S.X₃).hom ≫ schemeCechBoundary opens affine exact 0 := by
  rw [cohomologyBoundary_zero_eq_sections, Category.assoc, oneIso_sections]
  rfl

/-- A positive-degree comparison step from the two genuine connecting
isomorphisms of a flasque-middle short exact sequence. -/
def higherStep (exact : S.ShortExact) (degree : ℕ)
    (previous : AddCommGrpCat.of (Cohomology S.X₃ (degree + 1)) ≅
      (schemeCechComplex opens S.X₃).homology (degree + 1)) :
    AddCommGrpCat.of (Cohomology S.X₁ (degree + 2)) ≅
      (schemeCechComplex opens S.X₁).homology (degree + 2) :=
  (schemeCohomologyPositiveBoundaryIso exact degree).symm ≪≫ previous ≪≫
    schemeCechBoundaryIso opens affine exact (degree + 1)
      (standardCech_homology_positive_isZero opens S.X₂ degree)
      (standardCech_homology_positive_isZero opens S.X₂ (degree + 1))

omit cover in
/-- The positive comparison step also carries the actual boundaries to
one another, for any given lower-degree comparison. -/
@[reassoc]
theorem higherStep_boundary (exact : S.ShortExact) (degree : ℕ)
    (previous : AddCommGrpCat.of (Cohomology S.X₃ (degree + 1)) ≅
      (schemeCechComplex opens S.X₃).homology (degree + 1)) :
    cohomologyBoundary exact (degree + 1) ≫ (higherStep opens affine exact degree previous).hom =
      previous.hom ≫ schemeCechBoundary opens affine exact (degree + 1) := by
  exact Iso.hom_inv_id_assoc (schemeCohomologyPositiveBoundaryIso exact degree)
    (previous.hom ≫ (schemeCechBoundaryIso opens affine exact (degree + 1)
      (standardCech_homology_positive_isZero opens S.X₂ degree)
      (standardCech_homology_positive_isZero opens S.X₂ (degree + 1))).hom)

end ToricPower.CechNaturality
