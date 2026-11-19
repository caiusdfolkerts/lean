module

public import ToricPower.ToricSubspaceTorusCohomology
public import ToricPower.LinearSubspaceNeighbourhoodComparison

/-!
# Actual cohomology on the open neighbourhood and on the linear subvariety

For every actual line bundle, its restriction to the same-lattice open
subfan has nonzero cohomology in a degree exactly when its restriction to
the saturated-trace toric subvariety does. The original linear inclusion
factors through this actual open subscheme; the comparison uses ordinary
pullback composition and the proved exact equality of the restricted fans.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The neighbourhood contains the zero cone whenever the original fan
is nonempty. -/
theorem linearAmbientFan_cones_nonempty (fan : Fan i) (nonempty : Nonempty fan.cones)
    (W : Submodule ℝ V) : Nonempty (linearAmbientFan fan W).cones := by
  obtain ⟨cone⟩ := nonempty
  exact ⟨⟨⊥, ⟨fan.bot_mem cone.property, bot_le⟩⟩⟩

/-- Actual pullback along an open immersion preserves an invertible sheaf. -/
theorem invertible_open_pullback {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y F] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X ((Scheme.Modules.pullback j).obj F) :=
  (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F)
    (InvertibleRestriction.invertible_restrict j F)

/-- The ordinary cohomology of the actual open pullback. -/
abbrev toricOpenNeighbourhoodCohomology (fan : Fan i) (F : fan.algebraicRealization.Modules)
    (W : Submodule ℝ V) (degree : ℕ) :=
  Cohomology ((Scheme.Modules.pullback (linearAmbientOpenInclusion fan W)).obj F) degree

/-- Every degree of the actual open pullback vanishes precisely when that
degree of the actual original-sheaf linear restriction vanishes. -/
theorem toricOpenNeighbourhood_nontrivial_iff_subspace (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) (degree : ℕ) :
    Nontrivial (toricOpenNeighbourhoodCohomology fan F W degree) ↔
      Nontrivial (toricSubspacePullbackCohomology fan F W rational degree) := by
  let ambient := linearAmbientFan fan W
  let j := linearAmbientOpenInclusion fan W
  let inclusion := restrictedFanInclusion ambient W rational
  letI : IsOpenImmersion j := linearAmbientOpenInclusion_isOpenImmersion fan W
  letI := invertible_open_pullback j F
  have first := toricLineBundleCohomology_nontrivial_iff_subspace_of_cones_le
    ambient (linearAmbientFan_cones_nonempty fan nonempty W)
    (linearAmbientFan_isRegular fan regular W) ((Scheme.Modules.pullback j).obj F)
    W rational (fun cone => cone.property.2) degree
  have factorization : inclusion.algebraicMap ≫ j =
      (linearAmbientRestrictedComposite fan W rational).algebraicMap :=
    (FanHom.algebraicMap_comp
      (subfanFanHom ambient fan (fun _ h => h.1)) inclusion).symm
  let comparison := (Scheme.Modules.pullbackComp inclusion.algebraicMap j).app F ≪≫
    (Scheme.Modules.pullbackCongr factorization).app F
  let cohomologyComparison := (cohomologyFunctor
    (restrictedFan ambient W rational).algebraicRealization degree).mapIso comparison
  exact first.trans (cohomologyComparison.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.trans
    (linearAmbientRestrictedComposite_predicate fan W rational
      (fun source mapping => Nontrivial
        (Cohomology ((Scheme.Modules.pullback mapping.algebraicMap).obj F) degree))))

/-- The all-degree nonvanishing form of the actual open comparison. -/
theorem toricOpenNeighbourhood_nonzero_iff_subspace (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) :
    (∃ degree, Nontrivial (toricOpenNeighbourhoodCohomology fan F W degree)) ↔
      ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W rational degree) := by
  apply exists_congr
  exact toricOpenNeighbourhood_nontrivial_iff_subspace fan nonempty regular F W rational

/-- Vanishing on the linear subvariety is exactly vanishing on its actual
same-lattice open neighbourhood, for every actual line bundle. -/
theorem toricOpenNeighbourhood_subsingleton_iff_subspace (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) :
    (∀ degree, Subsingleton (toricOpenNeighbourhoodCohomology fan F W degree)) ↔
      ∀ degree, Subsingleton (toricSubspacePullbackCohomology fan F W rational degree) := by
  apply forall_congr'
  intro degree
  rw [← not_nontrivial_iff_subsingleton, ← not_nontrivial_iff_subsingleton]
  exact not_congr (toricOpenNeighbourhood_nontrivial_iff_subspace
    fan nonempty regular F W rational degree)

end ToricPower
