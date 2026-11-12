module

public import ToricPower.DivisorWeightAlgebra

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeightRestriction -/

/-!
# Chart restrictions and compatibility of the splitting

Deleting ray inequalities gives the literal inclusion of Laurent-supported
divisor modules.  The maps are semilinear for the induced chart-ring map, and
the residue splitting commutes with every such restriction.
-/



namespace ToricPower

open MonoidAlgebra
open scoped BigOperators

variable {ι ι' κ : Type*} [Fintype κ]

def rayWeightMonoidRestrict (f : ι' → ι) (A : ι → κ → ℤ) :
    rayWeightMonoid A →+ rayWeightMonoid (fun i => A (f i)) where
  toFun s := ⟨s.1, fun i => s.2 (f i)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def rayChartRestrictionHom (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) :
    RayChartRing R A →+* RayChartRing R (fun i => A (f i)) :=
  mapDomainRingHom R (rayWeightMonoidRestrict f A).toMultiplicative

@[simp] theorem rayChartPowerMonoidHom_restrict (f : ι' → ι)
    (A : ι → κ → ℤ) (ell : ℕ) :
    (rayChartPowerMonoidHom (fun i => A (f i)) ell).comp
      (rayWeightMonoidRestrict f A).toMultiplicative =
      rayChartPowerMonoidHom A ell := by
  ext s
  rfl

theorem rayChartPower_map_restrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (ell : ℕ) (a : RayChartRing R A) :
    mapDomain (rayChartPowerMonoidHom (fun i => A (f i)) ell)
      (rayChartRestrictionHom R f A a) =
      mapDomain (rayChartPowerMonoidHom A ell) a := by
  have h := congrArg (fun g : RayChartRing R A →+*
      MonoidAlgebra R (Multiplicative (κ → ℤ)) => g a)
    (mapDomainRingHom_comp (R := R) (rayChartPowerMonoidHom (fun i => A (f i)) ell)
      (rayWeightMonoidRestrict f A).toMultiplicative)
  simpa only [rayChartPowerMonoidHom_restrict, RingHom.comp_apply,
    mapDomainRingHom_apply, rayChartRestrictionHom] using h.symm

/-- Restriction of divisor sections is the actual inclusion of Laurent
polynomials, semilinear over the chart-ring restriction map. -/
def divisorSectionRestrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    DivisorSectionModule R A b ell →ₛₗ[rayChartRestrictionHom R f A]
      DivisorSectionModule R (fun i => A (f i)) (fun i => b (f i)) ell where
  toFun x := ⟨rayPowerLaurentOfValue R (fun i => A (f i)) ell
      (rayPowerLaurentValue R A ell x.1), by
    change rayPowerLaurentValue R A ell x.1 ∈
      supported R R {m | DivisorWeightAllowed (fun i => A (f i))
        (fun i => b (f i)) (Multiplicative.toAdd m)}
    apply mem_supported.mpr
    intro m hm i
    exact (mem_supported.mp x.2) hm (f i)⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R (fun i => A (f i)) ell
    change mapDomain (rayChartPowerMonoidHom A ell) a * rayPowerLaurentValue R A ell x.1 =
      mapDomain (rayChartPowerMonoidHom (fun i => A (f i)) ell)
        (rayChartRestrictionHom R f A a) * rayPowerLaurentValue R A ell x.1
    rw [rayChartPower_map_restrict]

@[simp] theorem divisorSectionRestrict_val (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (x : DivisorSectionModule R A b ell) :
    (divisorSectionRestrict R f A b ell x).1 = x.1 := rfl

theorem divisorResidueSummand_restrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell)
    (x : DivisorSectionModule R A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :
    divisorSectionRestrict R f A b ell (divisorResidueSummand R A b ell hell u x) =
      divisorResidueSummand R (fun i => A (f i)) (fun i => b (f i)) ell hell u
        (divisorSectionRestrict R f A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1 x) := by
  apply Subtype.ext
  rfl

/-- The complete affine splitting agrees on every common face chart. -/
theorem divisorResidueSum_restrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (x : ∀ u : LatticeResidues κ ell,
      DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :
    divisorSectionRestrict R f A b ell (divisorResidueSum R A b ell hell x) =
      divisorResidueSum R (fun i => A (f i)) (fun i => b (f i)) ell hell
        (fun u => divisorSectionRestrict R f A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1 (x u)) := by
  classical
  simp only [divisorResidueSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  congr 1

/-- The face module viewed over the original chart ring.  Its scalar action is
the same ambient Laurent multiplication as on the source chart. -/
def DivisorFaceSectionModule (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    Submodule (RayChartRing R A) (RayPowerLaurent R A ell) where
  carrier := {x | rayPowerLaurentValue R A ell x ∈
    supported R R {m | DivisorWeightAllowed (fun i => A (f i))
      (fun i => b (f i)) (Multiplicative.toAdd m)}}
  zero_mem' := (supported R R _).zero_mem
  add_mem' := (supported R R _).add_mem
  smul_mem' a x hx := by
    change rayPowerLaurentValue R A ell (a • x) ∈
      supported R R {m | DivisorWeightAllowed (fun i => A (f i))
        (fun i => b (f i)) (Multiplicative.toAdd m)}
    rw [rayPowerLaurentValue_smul, ← rayChartPower_map_restrict R f A ell a]
    exact divisor_support_chart_mul R (fun i => A (f i)) (fun i => b (f i)) ell
      (rayChartRestrictionHom R f A a) (rayPowerLaurentValue R A ell x) hx

def divisorSectionFaceRestriction (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    DivisorSectionModule R A b ell →ₗ[RayChartRing R A]
      DivisorFaceSectionModule R f A b ell where
  toFun x := ⟨x.1, (divisorSectionRestrict R f A b ell x).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem divisorSectionFaceRestriction_injective (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    Function.Injective (divisorSectionFaceRestriction R f A b ell) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : DivisorFaceSectionModule R f A b ell => z.val) h

end ToricPower

