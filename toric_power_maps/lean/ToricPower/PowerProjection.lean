module

public import ToricPower.GeometricCore

/-! # The canonical monomial projection for a toric power map

This construction uses coefficient extraction, rather than an independently
chosen basis on each affine chart. Consequently its compatibility with cone
inclusions is an equality of the actual coordinate-ring maps. The module is a
development candidate until its ordinary compiler record reports success.
-/

@[expose] public noncomputable section

open MonoidAlgebra

namespace ToricPower

section GroupAlgebra

variable {R M N : Type*} [Semiring R] [Group M] [Group N]

/-- Extraction of coefficients in the image of an injective group homomorphism
is linear for restriction of scalars along the corresponding group-ring map. -/
theorem comapDomain_mapDomain_mul (p : M →* N) (hp : Function.Injective p)
    (a : R[M]) (b : R[N]) :
    comapDomain p hp (mapDomain p a * b) = a * comapDomain p hp b := by
  induction a using induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ =>
      simp only [mapDomain_add, add_mul, comapDomain_add, h₁, h₂]
  | single m r =>
      ext x
      simp only [mapDomain_single, coeff_comapDomain, Finsupp.comapDomain_apply,
        coeff_single_mul_apply, map_mul, map_inv]

/-- The genuine linear retraction of the group-ring inclusion. -/
def groupPowerProjection (p : M →* N) (hp : Function.Injective p) :
    letI := (mapDomainRingHom R p).toModule
    R[N] →ₗ[R[M]] R[M] := by
  letI := (mapDomainRingHom R p).toModule
  exact
    { comapDomainAddMonoidHom p hp with
      map_smul' := fun a b => by
        change comapDomain p hp (mapDomain p a * b) = a * comapDomain p hp b
        exact comapDomain_mapDomain_mul p hp a b }

theorem groupPowerProjection_retract (p : M →* N) (hp : Function.Injective p)
    (a : R[M]) :
    comapDomain p hp (mapDomain p a) = a := by
  ext x
  exact Finsupp.mapDomain_apply_of_injective hp a.coeff x

end GroupAlgebra

section SaturatedMonoid

variable {R M : Type*} [Semiring R] [Group M]

/-- Restrict a group endomorphism to a submonoid that it preserves. -/
def restrictedMonoidPower (p : M →* M) (S : Submonoid M)
    (hS : ∀ m, p m ∈ S ↔ m ∈ S) : S →* S where
  toFun m := ⟨p m, (hS m).mpr m.property⟩
  map_one' := Subtype.ext (map_one p)
  map_mul' a b := Subtype.ext (map_mul p (a : M) (b : M))

theorem restrictedMonoidPower_injective (p : M →* M)
    (hp : Function.Injective p) (S : Submonoid M)
    (hS : ∀ m, p m ∈ S ↔ m ∈ S) :
    Function.Injective (restrictedMonoidPower p S hS) := by
  intro a b hab
  exact Subtype.ext (hp (congrArg Subtype.val hab))

/-- Coefficient extraction commutes with the embedding of a saturated monoid
algebra into its ambient group algebra. This is the gluing compatibility. -/
theorem submonoidProjection_ambient (p : M →* M) (hp : Function.Injective p)
    (S : Submonoid M) (hS : ∀ m, p m ∈ S ↔ m ∈ S) (a : R[S]) :
    mapDomain S.subtype
        (comapDomain (restrictedMonoidPower p S hS)
          (restrictedMonoidPower_injective p hp S hS) a) =
      comapDomain p hp (mapDomain S.subtype a) := by
  classical
  ext m
  by_cases hm : m ∈ S
  · let s : S := ⟨m, hm⟩
    change (Finsupp.mapDomain S.subtype
        (a.coeff.comapDomain (restrictedMonoidPower p S hS)
          (restrictedMonoidPower_injective p hp S hS).injOn)) (S.subtype s) =
      (Finsupp.mapDomain S.subtype a.coeff) (p (S.subtype s))
    rw [Finsupp.mapDomain_apply_of_injective
      (show Function.Injective S.subtype from fun _ _ h => Subtype.ext h)]
    change a.coeff (restrictedMonoidPower p S hS s) =
      (Finsupp.mapDomain S.subtype a.coeff)
        (S.subtype (restrictedMonoidPower p S hS s))
    rw [Finsupp.mapDomain_apply_of_injective
      (show Function.Injective S.subtype from fun _ _ h => Subtype.ext h)]
  · have hm' : m ∉ Set.range S.subtype := by
      rintro ⟨s, rfl⟩
      exact hm s.property
    have hpm : p m ∉ Set.range S.subtype := by
      rintro ⟨s, hs⟩
      exact hm ((hS m).mp (hs ▸ s.property))
    change (Finsupp.mapDomain S.subtype
        (a.coeff.comapDomain (restrictedMonoidPower p S hS)
          (restrictedMonoidPower_injective p hp S hS).injOn)) m =
      (Finsupp.mapDomain S.subtype a.coeff) (p m)
    rw [Finsupp.mapDomain_of_notMem_range _ _ hm',
      Finsupp.mapDomain_of_notMem_range _ _ hpm]

theorem monoid_power_square (p : M →* M) (S : Submonoid M)
    (hS : ∀ m, p m ∈ S ↔ m ∈ S) (a : R[S]) :
    mapDomain S.subtype (mapDomain (restrictedMonoidPower p S hS) a) =
      mapDomain p (mapDomain S.subtype a) := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp only [mapDomain_add, ha, hb]
  | single m r => simp only [mapDomain_single]; rfl

/-- The ambient projection restricts to a genuine linear projection on every
saturated affine semigroup ring. -/
theorem restrictedProjection_mapDomain_mul (p : M →* M) (hp : Function.Injective p)
    (S : Submonoid M) (hS : ∀ m, p m ∈ S ↔ m ∈ S) (a b : R[S]) :
    comapDomain (restrictedMonoidPower p S hS)
        (restrictedMonoidPower_injective p hp S hS)
        (mapDomain (restrictedMonoidPower p S hS) a * b) =
      a * comapDomain (restrictedMonoidPower p S hS)
        (restrictedMonoidPower_injective p hp S hS) b := by
  apply mapDomain_injective (R := R) (f := S.subtype)
    (fun _ _ h => Subtype.ext h)
  rw [submonoidProjection_ambient p hp S hS, mapDomain_mul, monoid_power_square,
    comapDomain_mapDomain_mul p hp, mapDomain_mul, submonoidProjection_ambient p hp S hS]

def saturatedPowerProjection (p : M →* M) (hp : Function.Injective p)
    (S : Submonoid M) (hS : ∀ m, p m ∈ S ↔ m ∈ S) :
    @LinearMap R[S] R[S] _ _ (RingHom.id _) R[S] R[S] _ _
      (mapDomainRingHom R (restrictedMonoidPower p S hS)).toModule
      Semiring.toModule := by
  refine @LinearMap.mk R[S] R[S] _ _ (RingHom.id _) R[S] R[S] _ _
    (mapDomainRingHom R (restrictedMonoidPower p S hS)).toModule Semiring.toModule
    { toFun := comapDomain (restrictedMonoidPower p S hS)
        (restrictedMonoidPower_injective p hp S hS)
      map_add' := fun a b => comapDomain_add _ _ a b } ?_
  intro a b
  change comapDomain (restrictedMonoidPower p S hS)
    (restrictedMonoidPower_injective p hp S hS)
    (mapDomain (restrictedMonoidPower p S hS) a * b) =
      a * comapDomain (restrictedMonoidPower p S hS)
        (restrictedMonoidPower_injective p hp S hS) b
  exact restrictedProjection_mapDomain_mul p hp S hS a b

theorem saturatedPowerProjection_retract (p : M →* M) (hp : Function.Injective p)
    (S : Submonoid M) (hS : ∀ m, p m ∈ S ↔ m ∈ S) (a : R[S]) :
    comapDomain (restrictedMonoidPower p S hS)
        (restrictedMonoidPower_injective p hp S hS)
        (mapDomain (restrictedMonoidPower p S hS) a) = a := by
  ext m
  exact Finsupp.mapDomain_apply_of_injective
    (restrictedMonoidPower_injective p hp S hS) a.coeff m

/-- The canonical affine projections agree on inclusions of saturated
semigroups; in particular they agree on every toric face overlap. -/
theorem saturatedPowerProjection_natural (p : M →* M) (hp : Function.Injective p)
    (S T : Submonoid M) (hST : S ≤ T)
    (hS : ∀ m, p m ∈ S ↔ m ∈ S) (hT : ∀ m, p m ∈ T ↔ m ∈ T)
    (a : R[S]) :
    mapDomain (Submonoid.inclusion hST)
        (comapDomain (restrictedMonoidPower p S hS)
          (restrictedMonoidPower_injective p hp S hS) a) =
      comapDomain (restrictedMonoidPower p T hT)
        (restrictedMonoidPower_injective p hp T hT)
        (mapDomain (Submonoid.inclusion hST) a) := by
  have hcomp (a : R[S]) :
      mapDomain T.subtype (mapDomain (Submonoid.inclusion hST) a) =
        mapDomain S.subtype a := by
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mapDomain_add, ha, hb]
    | single m r => simp only [mapDomain_single]; rfl
  apply mapDomain_injective (R := R) (f := T.subtype)
    (fun _ _ h => Subtype.ext h)
  rw [hcomp, submonoidProjection_ambient p hp S hS,
    submonoidProjection_ambient p hp T hT, hcomp]

end SaturatedMonoid

section ToricSemigroup

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Multiplication by a positive integer is injective on the actual integral
character group. No choice of a lattice basis is needed. -/
theorem characterPower_injective (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (exponentPower ell (N →+ ℤ)) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  ext n
  have hn := congrArg (fun m : Multiplicative (N →+ ℤ) => m.toAdd n) hab
  change (ell • a.toAdd) n = (ell • b.toAdd) n at hn
  simp only [AddMonoidHom.smul_apply, nsmul_eq_mul] at hn
  exact mul_left_cancel₀ (show (ell : ℤ) ≠ 0 by exact_mod_cast hell.ne') hn

/-- The actual dual semigroup of every real cone is saturated under positive
integral dilation. This does not require smoothness of the cone. -/
theorem dualSemigroup_power_mem (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (ell : ℕ) (hell : 0 < ell) (m : N →+ ℤ) :
    ell • m ∈ dualSemigroup hi σ ↔ m ∈ dualSemigroup hi σ := by
  have helr : (0 : ℝ) < ell := by exact_mod_cast hell
  simp only [mem_dualSemigroup, map_nsmul, LinearMap.smul_apply]
  constructor
  · intro h x hx
    have hh := h hx
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul] at hh
    exact nonneg_of_mul_nonneg_right hh helr
  · intro h x hx
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul]
    exact mul_nonneg helr.le (h hx)

/-- The same saturation property on the literal multiplicative semigroup
used by the coordinate-ring construction. -/
theorem dualSubmonoid_power_mem (hi : IsIntegralLattice i) (σ : PointedCone ℝ V)
    (ell : ℕ) (hell : 0 < ell) (m : Multiplicative (N →+ ℤ)) :
    exponentPower ell (N →+ ℤ) m ∈ (dualSemigroup hi σ).toSubmonoid ↔
      m ∈ (dualSemigroup hi σ).toSubmonoid :=
  dualSemigroup_power_mem hi σ ell hell m.toAdd

/-- A type-tag equivalence only: both sides are the same actual semigroup of
integral characters nonnegative on the cone. -/
def dualSemigroupMultiplicativeEquiv (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    Multiplicative (dualSemigroup hi σ) ≃* (dualSemigroup hi σ).toSubmonoid where
  toFun m := ⟨Multiplicative.ofAdd m.toAdd.val, m.toAdd.property⟩
  invFun m := Multiplicative.ofAdd ⟨m.val.toAdd, m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end ToricSemigroup

end ToricPower

