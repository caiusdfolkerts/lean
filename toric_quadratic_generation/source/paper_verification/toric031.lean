module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import paper_verification.toric037

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalDifferentialCocycle
section Source_ToricCanonicalDifferentialCocycle

-- original header: module

-- original header: public import PaperVerification.ToricFanDifferentials
-- original header: public import Mathlib.AlgebraicGeometry.Modules.Tilde

-- original header: @[expose] public section

/-!
# Gluing the actual top differential modules

The rational local generators here are the coefficients of the actual
top Kähler forms, defined through their images in the generic differential
module. Their regular-unit transition property is proved from the
differential calculation. Thus the resulting invertible fractional sheaf
is obtained from genuine differential modules. Its identification with
the fan coefficient function -1 is a theorem.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- Equal actual subsheaves give equivalent fractional presentations,
with the rational embeddings preserved. -/
theorem cartierCocycles_equivalent_of_submodule_eq
    (C D : RationalCartierCocycle X) (h : C.sheafSubmodule = D.sheafSubmodule) :
    C.toCartierData.Equivalent D.toCartierData := by
  have aux {A B : (rationalFunctions X).Submodule} (hAB : A = B) :
      ∃ e : A.toSheafOfModules ≅ B.toSheafOfModules, e.hom ≫ B.ι = A.ι := by
    subst B
    exact ⟨Iso.refl _, Category.id_comp _⟩
  exact aux h

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AddMonoidAlgebra KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- The nonzero rational coefficient of a genuine regular coordinate
volume. Its definition refers to the actual Kähler map, not a divisor
coefficient or a prescribed character. -/
def differentialVolumeUnit (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ((«Σ».fanScheme k).functionField)ˣ :=
  Units.mk0
    («Σ».actualChartTopCoefficient k b₀ s
      (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
        («Σ».actualFullChartDifferentialBasis k s))) (by
      rw [«Σ».actualChartTopCoefficient_basis]
      exact Units.ne_zero _)

theorem differentialVolumeUnit_eq (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) :
    «Σ».differentialVolumeUnit k b₀ s = «Σ».chartVolumeCoefficient k b₀ s := by
  apply Units.ext
  exact «Σ».actualChartTopCoefficient_basis k b₀ s

def differentialDetUnit (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ℤˣ :=
  (b₀.isUnit_det («Σ».fullCharacterBasis s)).unit

theorem differentialVolumeUnit_character
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    «Σ».differentialVolumeUnit k b₀ s =
      «Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) *
        Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
          («Σ».differentialDetUnit b₀ s) := by
  rw [«Σ».differentialVolumeUnit_eq, «Σ».canonical_cartierLatticePoint]
  rfl

theorem differentialVolume_transition_regular
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s t : «Σ».fullCones)
    (x : «Σ».fanScheme k) (hxs : x ∈ «Σ».fullChartOpen k s)
    (hxt : x ∈ «Σ».fullChartOpen k t) :
    ((«Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) /
      («Σ».differentialVolumeUnit k b₀ t : («Σ».fanScheme k).functionField)) ∈
        regularAtSubring («Σ».fanScheme k) x := by
  have hc := «Σ».cartier_rational_transition_regular k (fun _ => -1) s t x hxs hxt
  have hd : (((«Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t : ℤˣ) : ℤ) :
      («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have he :
      («Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) /
          («Σ».differentialVolumeUnit k b₀ t : («Σ».fanScheme k).functionField) =
        ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) :
            («Σ».fanScheme k).functionField) /
          («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) t) :
            («Σ».fanScheme k).functionField)) *
          (((«Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t : ℤˣ) : ℤ) :
            («Σ».fanScheme k).functionField) := by
    rw [«Σ».differentialVolumeUnit_character, «Σ».differentialVolumeUnit_character]
    let ψ : ℤˣ →* ((«Σ».fanScheme k).functionField)ˣ :=
      Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
    change
      ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) *
          ψ («Σ».differentialDetUnit b₀ s) : ((«Σ».fanScheme k).functionField)ˣ) :
          («Σ».fanScheme k).functionField) /
        ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) t) *
          ψ («Σ».differentialDetUnit b₀ t) : ((«Σ».fanScheme k).functionField)ˣ) :
          («Σ».fanScheme k).functionField) =
        _ * ((ψ («Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t) :
          ((«Σ».fanScheme k).functionField)ˣ) : («Σ».fanScheme k).functionField)
    rw [map_div]
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    exact mul_div_mul_comm _ _ _ _
  rw [he]
  exact (regularAtSubring («Σ».fanScheme k) x).mul_mem hc hd

/-- The actual differential-volume gluing data. The cover is the genuine
full affine cover, and the generators come from its actual top Ω modules. -/
def differentialVolumeCocycle (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    RationalCartierCocycle («Σ».fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure x
    exact ⟨⟨s⟩, hs⟩
  generator i := «Σ».differentialVolumeUnit k b₀ i.down
  transition i j x hi hj := «Σ».differentialVolume_transition_regular k b₀ i.down j.down x hi hj

/-- The invertible fractional sheaf obtained by gluing the actual local
top differential modules through their generic differential images. -/
def differentialVolumeData (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    CartierData («Σ».fanScheme k) :=
  («Σ».differentialVolumeCocycle k hpure b₀).toCartierData

theorem differential_division_regular_iff
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (x : «Σ».fanScheme k) (z : («Σ».fanScheme k).functionField) :
    z / («Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x ↔
      z / («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) :
        («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x := by
  let d := «Σ».differentialDetUnit b₀ s
  have hd : ((d : ℤ) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have hdi : (((d⁻¹ : ℤˣ) : ℤ) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have hdinv : (((d⁻¹ : ℤˣ) : ℤ) : («Σ».fanScheme k).functionField) =
      (((d : ℤ) : («Σ».fanScheme k).functionField))⁻¹ := by
    exact Units.val_inv_eq_inv_val
      (Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom d)
  have hd0 : ((d : ℤ) : («Σ».fanScheme k).functionField) ≠ 0 :=
    Units.ne_zero (Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom d)
  rw [«Σ».differentialVolumeUnit_character, Units.val_mul]
  change z / (_ * ((d : ℤ) : («Σ».fanScheme k).functionField)) ∈ _ ↔ _
  constructor
  · intro h
    have hm := (regularAtSubring («Σ».fanScheme k) x).mul_mem h hd
    convert hm using 1
    field_simp [Units.ne_zero, hd0]
  · intro h
    have hm := (regularAtSubring («Σ».fanScheme k) x).mul_mem h hdi
    rw [hdinv] at hm
    convert hm using 1
    field_simp [Units.ne_zero, hd0]

theorem differentialVolume_subsheaf_eq (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeCocycle k hpure b₀).sheafSubmodule =
      («Σ».fanCartierCocycle k hpure (fun _ => -1)).sheafSubmodule := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro U
  apply Submodule.ext
  intro z
  change (∀ i : ULift.{u} «Σ».fullCones, ∀ x : U.unop,
      x.val ∈ «Σ».fullChartOpen k i.down →
        rationalValueAt («Σ».fanScheme k) U.unop x z /
          («Σ».differentialVolumeUnit k b₀ i.down : («Σ».fanScheme k).functionField) ∈
            regularAtSubring («Σ».fanScheme k) x.val) ↔
    (∀ i : ULift.{u} «Σ».fullCones, ∀ x : U.unop,
      x.val ∈ «Σ».fullChartOpen k i.down →
        rationalValueAt («Σ».fanScheme k) U.unop x z /
          («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) i.down) :
            («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x.val)
  exact forall_congr' fun i => forall_congr' fun x => imp_congr_right fun _ =>
    «Σ».differential_division_regular_iff k b₀ i.down x.val _

/-- The toric canonical coefficient formula, obtained from the actual
top Kähler gluing and preserving its embedding in rational functions. -/
theorem differentialVolumeData_equivalent_canonical (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeData k hpure b₀).Equivalent
      («Σ».fanCartierData k hpure (fun _ => -1)) :=
  cartierCocycles_equivalent_of_submodule_eq _ _
    («Σ».differentialVolume_subsheaf_eq k hpure b₀)

/-- The actual affine sheaf associated to the full chart's top Kähler
module. This is independent of the Cartier coefficient formula. -/
def fullChartTopDifferentialSheaf (s : «Σ».fullCones) : (coneChart k s.val).Modules :=
  tilde (ModuleCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]))

/-- Its local freeness follows from the actual polynomial Ω basis. -/
def fullChartTopDifferentialFrame (s : «Σ».fullCones) :
    «Σ».fullChartTopDifferentialSheaf k s ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  (tilde.functor (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))).mapIso
      (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s)).toModuleIso ≪≫ tildeSelf

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.differentialVolumeData_equivalent_canonical

end
end Source_ToricCanonicalDifferentialCocycle
-- END ORIGINAL PaperVerification.ToricCanonicalDifferentialCocycle


