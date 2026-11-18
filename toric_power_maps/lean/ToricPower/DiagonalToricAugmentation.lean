module

public import ToricPower.DiagonalToricWeights

/-!
# The local cellular complex resolves the actual intersection-chart module

The target is the coordinate ring of `U_(σ∩τ)`, with scalars restricted
along the literal multiplication-of-characters map from the product chart.
The supported-weight bijection is upgraded to an actual isomorphism of
modules over that ring.  Consequently the genuine augmented cellular
complex is a quasi-isomorphism to this actual toric module in degree zero.

The ring map sends `(χ^a,χ^b)` to `χ^(a+b)` after the displayed full-lattice
coordinate change.  No homology object is renamed as the diagonal module.
The scheme-level affine product and sheafification comparisons remain
separate from this literal ring-and-module identification.

Candidate until its full dependency closure passes the pinned compiler.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "B" => affineCoordinateRing fan.lattice (σ.val ⊓ τ.val)

/-- The actual character sum on the intersection cone. -/
def diagonalPairCharacter :
    (rayCharacterMonoid A S × rayCharacterMonoid A T) →+
      dualSemigroup fan.lattice (σ.val ⊓ τ.val) where
  toFun p := ⟨basis.equivFun.symm (p.1.val+p.2.val),by
    rw [map_add]
    exact add_mem
      (dualSemigroup_anti fan.lattice inf_le_left
        ((fanRayCharacterMonoidEquiv fan basis rays σ) p.1).property)
      (dualSemigroup_anti fan.lattice inf_le_right
        ((fanRayCharacterMonoidEquiv fan basis rays τ) p.2).property)⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' p q := by
    apply Subtype.ext
    change basis.equivFun.symm ((p.1.val+q.1.val)+(p.2.val+q.2.val)) =
      basis.equivFun.symm (p.1.val+p.2.val) + basis.equivFun.symm (q.1.val+q.2.val)
    rw [← map_add]
    congr 1
    abel

/-- The genuine coordinate-ring map whose restriction of scalars is
the diagonal chart module. -/
def diagonalChartToIntersection : R →+* B :=
  (MonoidAlgebra.mapDomainRingHom ℂ
    (diagonalPairCharacter fan basis rays σ τ).toMultiplicative).comp
      (AddMonoidAlgebra.toMultiplicative ℂ _).toRingHom

@[simp]
theorem diagonalChartToIntersection_single
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : ℂ) :
    diagonalChartToIntersection fan basis rays σ τ (AddMonoidAlgebra.single p r) =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (diagonalPairCharacter fan basis rays σ τ p)) r := by
  simp [diagonalChartToIntersection]

/-- The actual intersection coordinate ring, regarded as a module over
the product-chart ring through the displayed ring homomorphism. -/
def diagonalIntersectionModule : ModuleCat R :=
  (ModuleCat.restrictScalars (diagonalChartToIntersection fan basis rays σ τ)).obj
    (ModuleCat.of B B)

def diagonalSupportedMonomialEquiv :
    DiagonalSupportedWeight A S T ≃ Multiplicative (dualSemigroup fan.lattice (σ.val ⊓ τ.val)) where
  toFun u := Multiplicative.ofAdd (diagonalSupportedWeightEquiv fan basis rays σ τ u)
  invFun m := (diagonalSupportedWeightEquiv fan basis rays σ τ).symm m.toAdd
  left_inv u := (diagonalSupportedWeightEquiv fan basis rays σ τ).symm_apply_apply u
  right_inv m := congrArg Multiplicative.ofAdd
    ((diagonalSupportedWeightEquiv fan basis rays σ τ).apply_symm_apply m.toAdd)

/-- The full finite-support coefficient bijection with the actual
intersection coordinate ring. -/
def diagonalIntersectionCoefficientEquiv : DiagonalChartHZero ℂ A S T ≃ₗ[ℂ] B :=
  (Finsupp.domLCongr (diagonalSupportedMonomialEquiv fan basis rays σ τ)).trans
    (MonoidAlgebra.coeffLinearEquiv ℂ).symm

@[simp]
theorem diagonalIntersectionCoefficientEquiv_single (u : DiagonalSupportedWeight A S T)
    (r : ℂ) :
    diagonalIntersectionCoefficientEquiv fan basis rays σ τ (Finsupp.single u r) =
      MonoidAlgebra.single (diagonalSupportedMonomialEquiv fan basis rays σ τ u) r := by
  simp [diagonalIntersectionCoefficientEquiv,Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply,Finsupp.equivMapDomain_single]

theorem diagonalSupportedWeightEquiv_translate
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DiagonalSupportedWeight A S T) :
    diagonalSupportedWeightEquiv fan basis rays σ τ
        (diagonalSupportedWeightTranslate A S T p u) =
      diagonalPairCharacter fan basis rays σ τ p +
        diagonalSupportedWeightEquiv fan basis rays σ τ u := by
  apply Subtype.ext
  change basis.equivFun.symm (u.val+p.1.val+p.2.val) =
    basis.equivFun.symm (p.1.val+p.2.val) + basis.equivFun.symm u.val
  simp only [map_add]
  abel

theorem diagonalIntersectionCoefficientEquiv_monomial_single
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (a r : ℂ) (u : DiagonalSupportedWeight A S T) :
    diagonalIntersectionCoefficientEquiv fan basis rays σ τ
        (AddMonoidAlgebra.single p a •
          (Finsupp.single u r : DiagonalChartHZero ℂ A S T)) =
      diagonalChartToIntersection fan basis rays σ τ (AddMonoidAlgebra.single p a) *
        diagonalIntersectionCoefficientEquiv fan basis rays σ τ (Finsupp.single u r) := by
  rw [diagonalChartHZero_single_smul,Finsupp.mapDomain_single,Finsupp.smul_single]
  simp only [smul_eq_mul,diagonalIntersectionCoefficientEquiv_single,
    diagonalChartToIntersection_single,MonoidAlgebra.single_mul_single]
  congr 1
  exact congrArg Multiplicative.ofAdd
    (diagonalSupportedWeightEquiv_translate fan basis rays σ τ p u)

theorem diagonalIntersectionCoefficientEquiv_monomial
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (a : ℂ)
    (v : DiagonalChartHZero ℂ A S T) :
    diagonalIntersectionCoefficientEquiv fan basis rays σ τ
        (AddMonoidAlgebra.single p a • v) =
      diagonalChartToIntersection fan basis rays σ τ (AddMonoidAlgebra.single p a) *
        diagonalIntersectionCoefficientEquiv fan basis rays σ τ v := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add u r v _ _ ih =>
      rw [smul_add,map_add,map_add,mul_add,ih,
        diagonalIntersectionCoefficientEquiv_monomial_single]

theorem diagonalIntersectionCoefficientEquiv_smul (r : R)
    (v : DiagonalChartHZero ℂ A S T) :
    diagonalIntersectionCoefficientEquiv fan basis rays σ τ (r • v) =
      diagonalChartToIntersection fan basis rays σ τ r *
        diagonalIntersectionCoefficientEquiv fan basis rays σ τ v := by
  induction r using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p a r _ _ ih =>
      rw [add_smul,map_add,map_add,add_mul,ih,
        diagonalIntersectionCoefficientEquiv_monomial]

/-- The actual target-module isomorphism respects every product-chart
scalar, as proved from the literal monomial action. -/
def diagonalIntersectionLinearEquiv :
    DiagonalChartHZero ℂ A S T ≃ₗ[R] diagonalIntersectionModule fan basis rays σ τ where
  toAddEquiv := (diagonalIntersectionCoefficientEquiv fan basis rays σ τ).toAddEquiv
  map_smul' r v := diagonalIntersectionCoefficientEquiv_smul fan basis rays σ τ r v

def diagonalIntersectionModuleIso :
    ModuleCat.of R (DiagonalChartHZero ℂ A S T) ≅
      diagonalIntersectionModule fan basis rays σ τ :=
  (diagonalIntersectionLinearEquiv fan basis rays σ τ).toModuleIso

/-- The actual chart cellular complex, augmented to the actual toric
intersection module rather than to an abstractly isomorphic object. -/
def diagonalToricChartAugmentation :
    diagonalChartComplex ℂ A S T ⟶
      (ChainComplex.single₀ (ModuleCat R)).obj
        (diagonalIntersectionModule fan basis rays σ τ) :=
  diagonalChartAugmentation ℂ A S T ≫
    (ChainComplex.single₀ (ModuleCat R)).map
      (diagonalIntersectionModuleIso fan basis rays σ τ).hom

/-- A complete local quasi-isomorphism to the literal intersection-chart
module, with all character weights and the intended scalar action. -/
theorem diagonalToricChartAugmentation_quasiIso :
    QuasiIso (diagonalToricChartAugmentation fan basis rays σ τ) := by
  letI := diagonalChartAugmentation_quasiIso ℂ A S T
  unfold diagonalToricChartAugmentation
  infer_instance

end ToricPower
