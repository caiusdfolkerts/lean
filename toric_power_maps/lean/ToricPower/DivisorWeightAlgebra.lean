module

public import ToricPower.Core
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Divisor modules and the complete affine toric power-map splitting

This file constructs the actual Laurent-supported modules and their unique
residue splitting. Chart restrictions, Cartier frames and face localization
are continued in `DivisorWeightRestrictionAlgebra`. The coefficient definitions
are imported from the unchanged arithmetic foundation `ToricPower.Core`.

The sections below preserve the full generality of the individual construction:
all finite lattice ranks, arbitrary divisor coefficients, every positive power,
and charts that may have smaller dimension than the ambient lattice.
-/

set_option maxHeartbeats 2000000
-- Development diagnostics only; remove before the final audited build.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeights -/

/-!
# Divisor sections and residue decomposition on toric affine charts

An exponent is allowed for a divisor precisely when its pairing with each ray,
plus the divisor coefficient, is nonnegative.  This file uses that literal
inequality, rather than postulating a splitting.  Regrouping monomials by their
residues modulo a positive integer gives the floor coefficients of the paper.
-/



namespace ToricPower

variable {ι κ : Type*} [Fintype κ]

/-- The exponents of regular sections of the divisor with ray coefficients `b`.
The convention is `div(χ^m) + D ≥ 0`. -/
def DivisorWeightAllowed (A : ι → κ → ℤ) (b : ι → ℤ) (m : κ → ℤ) : Prop :=
  ∀ i, 0 ≤ b i + rayMap A m i

/-- The actual admissible character exponents, with no quotient of the lattice. -/
abbrev DivisorWeight (A : ι → κ → ℤ) (b : ι → ℤ) :=
  {m : κ → ℤ // DivisorWeightAllowed A b m}

/-- The standard complete set of representatives for `M / ℓM`. -/
abbrev LatticeResidues (κ : Type*) (ell : ℕ) := κ → Fin ell

instance latticeResiduesFintype (ell : ℕ) : Fintype (LatticeResidues κ ell) := by
  classical
  exact inferInstanceAs (Fintype (κ → Fin ell))

@[simp] theorem latticeResidues_card (ell : ℕ) :
    Fintype.card (LatticeResidues κ ell) = ell ^ Fintype.card κ := by
  classical
  simp [LatticeResidues]

def latticeResidueRepresentative {ell : ℕ} (u : LatticeResidues κ ell) : κ → ℤ :=
  fun j => (u j : ℤ)

def coordinateResidueEquiv (ell : ℕ) (hell : 0 < ell) : Fin ell × ℤ ≃ ℤ where
  toFun p := (p.1 : ℤ) + (ell : ℤ) * p.2
  invFun m :=
    (⟨(m % (ell : ℤ)).toNat, by
      have h0 : 0 ≤ m % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
      have hlt : m % (ell : ℤ) < (ell : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast hell)
      omega⟩, m / (ell : ℤ))
  left_inv p := by
    have h0 : (0 : ℤ) ≤ (p.1 : ℕ) := Int.natCast_nonneg _
    have hlt : ((p.1 : ℕ) : ℤ) < (ell : ℤ) := by exact_mod_cast p.1.isLt
    have hz : (ell : ℤ) ≠ 0 := by exact_mod_cast hell.ne'
    apply Prod.ext
    · apply Fin.ext
      simp [Int.emod_eq_of_lt h0 hlt]
    · simp [Int.add_mul_ediv_left _ _ hz, Int.ediv_eq_zero_of_lt h0 hlt]
  right_inv m := by
    have h0 : 0 ≤ m % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
    simp only [Int.toNat_of_nonneg h0]
    exact Int.emod_add_mul_ediv m ell

/-- Coordinatewise Euclidean division, including negative lattice coordinates. -/
def latticeResidueEquiv (ell : ℕ) (hell : 0 < ell) :
    LatticeResidues κ ell × (κ → ℤ) ≃ (κ → ℤ) :=
  (Equiv.arrowProdEquivProdArrow κ (fun _ => Fin ell) (fun _ => ℤ)).symm.trans
    (Equiv.piCongrRight fun _ => coordinateResidueEquiv ell hell)

@[simp] theorem latticeResidueEquiv_apply (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell) (m : κ → ℤ) :
    latticeResidueEquiv ell hell (u, m) =
      latticeResidueRepresentative u + (ell : ℤ) • m := rfl

/-- The elementary inequality that produces the floor divisor in the splitting. -/
theorem divisorWeightAllowed_power_iff (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) (u m : κ → ℤ) :
    DivisorWeightAllowed A (powerCoefficient A b ell u) m ↔
      DivisorWeightAllowed A b (u + ell • m) := by
  apply forall_congr'
  intro i
  have h := congrFun (powerCoefficient_translate A b ell hell.ne' u m) i
  change (b i + rayMap A (u + ell • m) i) / ell =
    powerCoefficient A b ell u i + rayMap A m i at h
  change (0 ≤ powerCoefficient A b ell u i + rayMap A m i) ↔ _
  rw [← h]
  exact Int.ediv_nonneg_iff_of_pos hell

/-- The full residue decomposition of the admissible exponents.  In particular,
each summand uses the literal floor coefficient vector, not merely its class. -/
def divisorWeightResidueEquiv (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℕ) (hell : 0 < ell) :
    (Σ u : LatticeResidues κ ell,
      DivisorWeight A (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) ≃
      DivisorWeight A b :=
  (Equiv.subtypeProdEquivSigmaSubtype (fun (u : LatticeResidues κ ell) (m : κ → ℤ) =>
    DivisorWeightAllowed A (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) m)).symm.trans
    ((latticeResidueEquiv ell hell).subtypeEquiv (fun p => by
      change DivisorWeightAllowed A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative p.1)) p.2 ↔
        DivisorWeightAllowed A b (latticeResidueRepresentative p.1 + (ell : ℤ) • p.2)
      exact divisorWeightAllowed_power_iff A b ell (by exact_mod_cast hell) _ _))

@[simp] theorem divisorWeightResidueEquiv_apply_val (A : ι → κ → ℤ)
    (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) (u : LatticeResidues κ ell)
    (m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) :
    (divisorWeightResidueEquiv A b ell hell ⟨u, m⟩).1 =
      latticeResidueRepresentative u + (ell : ℤ) • m.1 := rfl

/-- Coefficients of the actual monomials in a divisor-section module. -/
abbrev DivisorCoefficients (R : Type*) [Zero R]
    (A : ι → κ → ℤ) (b : ι → ℤ) := DivisorWeight A b →₀ R

/-- The coefficient-level direct-sum decomposition.  Its finiteness comes from
the finite lattice basis; all exponents and all divisor coefficients are allowed. -/
def divisorCoefficientsResidueEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (∀ u : LatticeResidues κ ell,
      DivisorCoefficients R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) ≃ₗ[R]
      DivisorCoefficients R A b :=
  (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm.trans
    (Finsupp.domLCongr (divisorWeightResidueEquiv A b ell hell))

section Restriction

variable {ι' : Type*}

/-- Removing ray inequalities is the restriction map on allowed characters.
For a fan face, `f` is the inclusion of its rays in the rays of the chart. -/
def divisorWeightRestrict (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ) :
    DivisorWeight A b → DivisorWeight (fun i => A (f i)) (fun i => b (f i)) :=
  fun m => ⟨m.1, fun i => m.2 (f i)⟩

theorem divisorWeightRestrict_injective (f : ι' → ι)
    (A : ι → κ → ℤ) (b : ι → ℤ) :
    Function.Injective (divisorWeightRestrict f A b) := by
  intro m n h
  apply Subtype.ext
  exact congrArg
    (fun z : DivisorWeight (fun i => A (f i)) (fun i => b (f i)) => z.1) h

/-- Floor coefficients commute literally with restriction to the rays of a face. -/
@[simp] theorem powerCoefficient_restrict (f : ι' → ι)
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ) (u : κ → ℤ) :
    powerCoefficient (fun i => A (f i)) (fun i => b (f i)) ell u =
      fun i => powerCoefficient A b ell u (f i) := rfl

/-- The residue monomial map is independent of which chart contains it. -/
theorem divisorWeightResidueEquiv_restrict (f : ι' → ι)
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell)
    (m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) :
    divisorWeightRestrict f A b (divisorWeightResidueEquiv A b ell hell ⟨u, m⟩) =
      divisorWeightResidueEquiv (fun i => A (f i)) (fun i => b (f i)) ell hell
        ⟨u, divisorWeightRestrict f A _ m⟩ := rfl

end Restriction

end ToricPower

/-! ## Source section: DivisorWeightModules -/

/-!
# Laurent-supported modules of divisor sections

The modules below are submodules of the Laurent group algebra.  The parameter
`ell` records restriction of scalars through the actual monomial power map.
Thus `ell = 1` gives the usual chart module and general positive `ell` gives
its direct image module on an affine chart.
-/



namespace ToricPower

open MonoidAlgebra

variable {ι κ : Type*} [Fintype κ]

/-- The semigroup of characters nonnegative on the given rays. -/
def rayWeightMonoid (A : ι → κ → ℤ) : AddSubmonoid (κ → ℤ) where
  carrier := {m | ∀ i, 0 ≤ rayMap A m i}
  zero_mem' := by simp
  add_mem' := by
    intro m n hm hn i
    simpa only [map_add, Pi.add_apply] using add_nonneg (hm i) (hn i)

abbrev RayChartRing (R : Type*) [Semiring R] (A : ι → κ → ℤ) :=
  MonoidAlgebra R (Multiplicative (rayWeightMonoid A))

/-- The chart monoid embeds in the character lattice, followed by multiplication
of exponents by `ell`. -/
def rayChartPowerMonoidHom (A : ι → κ → ℤ) (ell : ℕ) :
    Multiplicative (rayWeightMonoid A) →* Multiplicative (κ → ℤ) :=
  (ell • (rayWeightMonoid A).subtype).toMultiplicative

@[simp] theorem rayChartPowerMonoidHom_toAdd (A : ι → κ → ℤ) (ell : ℕ)
    (m : Multiplicative (rayWeightMonoid A)) :
    Multiplicative.toAdd (rayChartPowerMonoidHom A ell m) =
      ell • (Multiplicative.toAdd m).1 := rfl

/-- A tagged Laurent algebra; the tag records its chart scalar action. -/
def RayPowerLaurent (R : Type*) [Semiring R] (A : ι → κ → ℤ) (_ell : ℕ) :=
  MonoidAlgebra R (Multiplicative (κ → ℤ))

instance (R : Type*) [Semiring R] (A : ι → κ → ℤ) (ell : ℕ) :
    Semiring (RayPowerLaurent R A ell) :=
  inferInstanceAs (Semiring (MonoidAlgebra R (Multiplicative (κ → ℤ))))

instance (R : Type*) [CommRing R] (A : ι → κ → ℤ) (ell : ℕ) :
    CommRing (RayPowerLaurent R A ell) :=
  inferInstanceAs (CommRing (MonoidAlgebra R (Multiplicative (κ → ℤ))))

def rayChartPowerRingHom (R : Type*) [Semiring R] (A : ι → κ → ℤ) (ell : ℕ) :
    RayChartRing R A →+* RayPowerLaurent R A ell :=
  mapDomainRingHom R (rayChartPowerMonoidHom A ell)

instance (R : Type*) [Semiring R] (A : ι → κ → ℤ) (ell : ℕ) :
    Module (RayChartRing R A) (RayPowerLaurent R A ell) :=
  (rayChartPowerRingHom R A ell).toModule

/-- Explicitly forget the scalar-action tag without changing a Laurent polynomial. -/
def rayPowerLaurentValue (R : Type*) [Semiring R] (A : ι → κ → ℤ) (ell : ℕ)
    (x : RayPowerLaurent R A ell) : MonoidAlgebra R (Multiplicative (κ → ℤ)) := x

/-- Put the selected scalar-action tag on an actual Laurent polynomial. -/
def rayPowerLaurentOfValue (R : Type*) [Semiring R] (A : ι → κ → ℤ) (ell : ℕ)
    (x : MonoidAlgebra R (Multiplicative (κ → ℤ))) : RayPowerLaurent R A ell := x

@[simp] theorem rayPowerLaurentValue_ofValue (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (x : MonoidAlgebra R (Multiplicative (κ → ℤ))) :
    rayPowerLaurentValue R A ell (rayPowerLaurentOfValue R A ell x) = x := rfl

@[simp] theorem rayPowerLaurentOfValue_value (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (x : RayPowerLaurent R A ell) :
    rayPowerLaurentOfValue R A ell (rayPowerLaurentValue R A ell x) = x := rfl

theorem rayPowerLaurentValue_injective (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) : Function.Injective (rayPowerLaurentValue R A ell) :=
  fun _ _ h => h

@[simp] theorem rayPowerLaurentValue_zero (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) : rayPowerLaurentValue R A ell 0 = 0 := rfl

@[simp] theorem rayPowerLaurentValue_add (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (x y : RayPowerLaurent R A ell) :
    rayPowerLaurentValue R A ell (x+y) =
      rayPowerLaurentValue R A ell x + rayPowerLaurentValue R A ell y := rfl

/-- The tag uses exactly restriction of scalars through the monomial power map. -/
@[simp] theorem rayPowerLaurentValue_smul (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (a : RayChartRing R A) (x : RayPowerLaurent R A ell) :
    rayPowerLaurentValue R A ell (a • x) =
      mapDomain (rayChartPowerMonoidHom A ell) a * rayPowerLaurentValue R A ell x := rfl

/-- Adding a regular chart character preserves the divisor inequalities. -/
theorem divisorWeightAllowed_add_nonnegative (A : ι → κ → ℤ) (b : ι → ℤ)
    {m n : κ → ℤ} (hm : DivisorWeightAllowed A b m)
    (hn : ∀ i, 0 ≤ rayMap A n i) : DivisorWeightAllowed A b (n + m) := by
  intro i
  simp only [map_add, Pi.add_apply]
  have := hm i
  have := hn i
  omega

/-- Scalar multiplication by every chart Laurent polynomial preserves the
allowed support, also after restriction through a power map. -/
theorem divisor_support_chart_mul (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (a : RayChartRing R A)
    (x : MonoidAlgebra R (Multiplicative (κ → ℤ)))
    (hx : x ∈ supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}) :
    mapDomain (rayChartPowerMonoidHom A ell) a * x ∈
      supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)} := by
  induction a using induction_linear with
  | zero => simpa using (supported R R
      {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}).zero_mem
  | add a a' ha ha' =>
    simpa only [mapDomain_add, add_mul] using
      (supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}).add_mem ha ha'
  | single s r =>
    rw [mapDomain_single]
    apply mem_supported'.mpr
    intro m hm
    rw [coeff_single_mul_apply]
    have hbad : ¬ DivisorWeightAllowed A b
        (Multiplicative.toAdd ((rayChartPowerMonoidHom A ell s)⁻¹ * m)) := by
      intro hv
      apply hm
      have hpos : ∀ i, 0 ≤ rayMap A (ell • (Multiplicative.toAdd s).1) i := by
        intro i
        simpa only [map_nsmul, Pi.smul_apply] using
          nsmul_nonneg ((Multiplicative.toAdd s).2 i) ell
      have hsum : ell • (Multiplicative.toAdd s).1 +
          Multiplicative.toAdd ((rayChartPowerMonoidHom A ell s)⁻¹ * m) =
          Multiplicative.toAdd m := by
        change Multiplicative.toAdd (rayChartPowerMonoidHom A ell s) +
          (-(Multiplicative.toAdd (rayChartPowerMonoidHom A ell s)) +
            Multiplicative.toAdd m) = Multiplicative.toAdd m
        abel
      change DivisorWeightAllowed A b (Multiplicative.toAdd m)
      rw [← hsum]
      exact divisorWeightAllowed_add_nonnegative A b hv hpos
    rw [(mem_supported'.mp hx) _ hbad, mul_zero]

/-- The divisor module inside the Laurent algebra with the specified chart
scalar action.  Its support condition is independent of the power-map tag. -/
def DivisorSectionModule (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    Submodule (RayChartRing R A) (RayPowerLaurent R A ell) where
  carrier := {x | rayPowerLaurentValue R A ell x ∈
    supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}}
  zero_mem' := (supported R R _).zero_mem
  add_mem' := (supported R R _).add_mem
  smul_mem' a x hx := by
    change rayPowerLaurentValue R A ell (a • x) ∈
      supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}
    rw [rayPowerLaurentValue_smul]
    exact divisor_support_chart_mul R A b ell a (rayPowerLaurentValue R A ell x) hx

/-- Removing the type tag gives exactly the usual supported Laurent polynomial
space; this equivalence introduces no mathematical assumptions. -/
def divisorSectionSupportedAddEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    DivisorSectionModule R A b ell ≃+
      supported R R {m : Multiplicative (κ → ℤ) |
        DivisorWeightAllowed A b (Multiplicative.toAdd m)} where
  toFun x := ⟨rayPowerLaurentValue R A ell x.1, x.2⟩
  invFun x := ⟨rayPowerLaurentOfValue R A ell x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def divisorWeightMultiplicativeEquiv (A : ι → κ → ℤ) (b : ι → ℤ) :
    DivisorWeight A b ≃ {m : Multiplicative (κ → ℤ) |
      DivisorWeightAllowed A b (Multiplicative.toAdd m)} where
  toFun m := ⟨Multiplicative.ofAdd m.1, m.2⟩
  invFun m := ⟨Multiplicative.toAdd m.1, m.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coefficients identify the chart divisor module with finitely supported
functions on its admissible exponents. -/
def divisorSectionCoefficientsAddEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    DivisorSectionModule R A b ell ≃+ DivisorCoefficients R A b :=
  (divisorSectionSupportedAddEquiv R A b ell).trans
    ((supportedEquivFinsupp _).toAddEquiv.trans
      (Finsupp.domCongr (divisorWeightMultiplicativeEquiv A b).symm))

@[simp] theorem divisorSectionCoefficientsAddEquiv_apply
    (R : Type*) [Semiring R] (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (x : DivisorSectionModule R A b ell) (m : DivisorWeight A b) :
    divisorSectionCoefficientsAddEquiv R A b ell x m =
      (rayPowerLaurentValue R A ell x.1).coeff
        (Multiplicative.ofAdd m.1) := rfl

/-- A monomial section, carrying its actual admissibility proof. -/
def divisorSectionSingle (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (m : DivisorWeight A b) (r : R) :
    DivisorSectionModule R A b ell :=
  ⟨rayPowerLaurentOfValue R A ell (single (Multiplicative.ofAdd m.1) r), by
    classical
    change (single (Multiplicative.ofAdd m.1) r : MonoidAlgebra R (Multiplicative (κ → ℤ))) ∈
      supported R R {g | DivisorWeightAllowed A b (Multiplicative.toAdd g)}
    apply mem_supported'.mpr
    intro g hg
    have hne : Multiplicative.ofAdd m.1 ≠ g := by
      intro h
      apply hg
      subst g
      change DivisorWeightAllowed A b m.val
      exact m.property
    simp [hne]⟩

@[simp] theorem divisorSectionCoefficientsAddEquiv_single
    (R : Type*) [Semiring R] (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (m : DivisorWeight A b) (r : R) :
    divisorSectionCoefficientsAddEquiv R A b ell (divisorSectionSingle R A b ell m r) =
      Finsupp.single m r := by
  classical
  ext n
  simp only [divisorSectionCoefficientsAddEquiv_apply, divisorSectionSingle,
    rayPowerLaurentValue_ofValue, coeff_single, Finsupp.single_apply]
  have hmn : Multiplicative.ofAdd m.1 = Multiplicative.ofAdd n.1 ↔ m = n := by
    constructor
    · intro h
      exact Subtype.ext (Multiplicative.ofAdd.injective h)
    · intro h
      exact congrArg (fun z : DivisorWeight A b => Multiplicative.ofAdd z.1) h
  by_cases h : m = n
  · subst n
    simp
  · have h' : Multiplicative.ofAdd m.1 ≠ Multiplicative.ofAdd n.1 :=
      fun e => h (hmn.mp e)
    simp [h, h']

@[simp] theorem divisorSectionCoefficientsAddEquiv_symm_single
    (R : Type*) [Semiring R] (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (m : DivisorWeight A b) (r : R) :
    (divisorSectionCoefficientsAddEquiv R A b ell).symm (Finsupp.single m r) =
      divisorSectionSingle R A b ell m r := by
  apply (divisorSectionCoefficientsAddEquiv R A b ell).injective
  simp

/-- The additive residue isomorphism on the actual Laurent-supported modules.
The scalar compatibility is established separately using the power ring map. -/
def divisorSectionResidueAddEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (∀ u : LatticeResidues κ ell,
      DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) ≃+
      DivisorSectionModule R A b ell :=
  (AddEquiv.piCongrRight fun u => divisorSectionCoefficientsAddEquiv R A _ 1).trans
    ((divisorCoefficientsResidueEquiv R A b ell hell).toAddEquiv.trans
      (divisorSectionCoefficientsAddEquiv R A b ell).symm)

end ToricPower

/-! ## Source section: DivisorWeightSplitting -/

/-!
# Chart-linear monomial splitting

The maps in this file send `χ^m` in the residue-`u` summand to
`χ^(u + ℓm)`.  Their linearity is over the chart coordinate ring, where the
target scalar action is restriction through the monomial power map.
-/



namespace ToricPower

open MonoidAlgebra
open scoped BigOperators

variable {ι κ : Type*} [Fintype κ]

def latticePowerMonoidHom (ell : ℕ) :
    Multiplicative (κ → ℤ) →* Multiplicative (κ → ℤ) :=
  (ell • AddMonoidHom.id (κ → ℤ)).toMultiplicative

@[simp] theorem latticePowerMonoidHom_chart (A : ι → κ → ℤ) (ell : ℕ) :
    (latticePowerMonoidHom ell).comp (rayChartPowerMonoidHom A 1) =
      rayChartPowerMonoidHom A ell := by
  apply MonoidHom.ext
  intro m
  apply Multiplicative.toAdd.injective
  change ell • (1 • (Multiplicative.toAdd m).1) = ell • (Multiplicative.toAdd m).1
  rw [one_smul]

@[simp] theorem latticePowerMonoidHom_mul_representative (ell : ℕ)
    (u m : κ → ℤ) :
    latticePowerMonoidHom ell (Multiplicative.ofAdd m) * Multiplicative.ofAdd u =
      Multiplicative.ofAdd (u + (ell : ℤ) • m) := by
  change ell • m + u = u + (ell : ℤ) • m
  rw [natCast_zsmul, add_comm]

/-- The monomial residue map on the ambient Laurent algebras is linear for
the actual source and power-restricted target chart actions. -/
def divisorResidueAmbientLinearMap (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (u : κ → ℤ) :
    RayPowerLaurent R A 1 →ₗ[RayChartRing R A] RayPowerLaurent R A ell where
  toFun x := rayPowerLaurentOfValue R A ell
    (mapDomain (latticePowerMonoidHom ell) (rayPowerLaurentValue R A 1 x) *
      single (Multiplicative.ofAdd u) 1)
  map_add' x y := by
    apply rayPowerLaurentValue_injective R A ell
    simp only [rayPowerLaurentValue_ofValue, rayPowerLaurentValue_add,
      mapDomain_add, add_mul]
  map_smul' a x := by
    apply rayPowerLaurentValue_injective R A ell
    simp only [rayPowerLaurentValue_ofValue, rayPowerLaurentValue_smul,
      RingHom.id_apply]
    rw [mapDomain_mul, ← mul_assoc]
    congr 2
    have h := congrArg (fun f : RayChartRing R A →+*
        MonoidAlgebra R (Multiplicative (κ → ℤ)) => f a)
      (mapDomainRingHom_comp (R := R) (latticePowerMonoidHom ell) (rayChartPowerMonoidHom A 1))
    simpa only [latticePowerMonoidHom_chart, RingHom.comp_apply,
      mapDomainRingHom_apply] using h.symm

@[simp] theorem divisorResidueAmbientLinearMap_single (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (u m : κ → ℤ) (r : R) :
    divisorResidueAmbientLinearMap R A ell u (single (Multiplicative.ofAdd m) r) =
      single (Multiplicative.ofAdd (u + (ell : ℤ) • m)) r := by
  apply rayPowerLaurentValue_injective R A ell
  change (mapDomain (latticePowerMonoidHom ell)
      (single (Multiplicative.ofAdd m) r) * single (Multiplicative.ofAdd u) 1 :
        MonoidAlgebra R (Multiplicative (κ → ℤ))) = single (Multiplicative.ofAdd (u + (ell : ℤ) • m)) r
  rw [mapDomain_single, single_mul_single, latticePowerMonoidHom_mul_representative,
    mul_one]

/-- The divisor inequalities ensure that the monomial residue map lands in the
correct target divisor module. -/
theorem divisorResidueAmbientLinearMap_mem (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) (u : κ → ℤ)
    (x : DivisorSectionModule R A (powerCoefficient A b (ell : ℤ) u) 1) :
    divisorResidueAmbientLinearMap R A ell u x.1 ∈ DivisorSectionModule R A b ell := by
  classical
  change mapDomain (latticePowerMonoidHom ell) (rayPowerLaurentValue R A 1 x.1) *
    single (Multiplicative.ofAdd u) 1 ∈
    supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}
  rw [mem_supported]
  intro g hg
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp
    (support_coeff_mul_single_subset
      (mapDomain (latticePowerMonoidHom ell) (rayPowerLaurentValue R A 1 x.1))
        (1 : R) (Multiplicative.ofAdd u) hg)
  have hv' : v ∈ (rayPowerLaurentValue R A 1 x.1).coeff.support.image
      (latticePowerMonoidHom ell) :=
    Finsupp.mapDomain_support hv
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv'
  change DivisorWeightAllowed A b (ell • Multiplicative.toAdd m + u)
  simpa only [natCast_zsmul, add_comm] using
    (divisorWeightAllowed_power_iff A b ell (by exact_mod_cast hell) u
      (Multiplicative.toAdd m)).mp ((mem_supported.mp x.2) hm)

/-- One summand in the affine-chart Frobenius decomposition. -/
def divisorResidueSummand (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell) :
    DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1 →ₗ[RayChartRing R A]
      DivisorSectionModule R A b ell :=
  LinearMap.codRestrict _
    ((divisorResidueAmbientLinearMap R A ell (latticeResidueRepresentative u)).comp
      (DivisorSectionModule R A _ 1).subtype)
    (divisorResidueAmbientLinearMap_mem R A b ell hell (latticeResidueRepresentative u))

@[simp] theorem divisorResidueSummand_single (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell)
    (m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) (r : R) :
    divisorResidueSummand R A b ell hell u (divisorSectionSingle R A _ 1 m r) =
      divisorSectionSingle R A b ell (divisorWeightResidueEquiv A b ell hell ⟨u, m⟩) r := by
  apply Subtype.ext
  exact divisorResidueAmbientLinearMap_single R A ell (latticeResidueRepresentative u) m.1 r

/-- Sum the monomial residue inclusions.  There are exactly `ell ^ rank M`
indices, even when several summands have the same divisor class. -/
def divisorResidueSum (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (∀ u : LatticeResidues κ ell,
      DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) →ₗ[RayChartRing R A]
      DivisorSectionModule R A b ell :=
  ∑ u, (divisorResidueSummand R A b ell hell u).comp (LinearMap.proj u)

@[simp] theorem divisorResidueSum_single (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell)
    (m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) (r : R) :
    divisorResidueSum R A b ell hell (Pi.single u (divisorSectionSingle R A _ 1 m r)) =
      divisorSectionSingle R A b ell (divisorWeightResidueEquiv A b ell hell ⟨u, m⟩) r := by
  classical
  simp only [divisorResidueSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single u]
  · rw [Pi.single_eq_same, divisorResidueSummand_single]
  · intro v _ h
    rw [Pi.single_eq_of_ne h, map_zero]
  · intro h
    exact (h (Finset.mem_univ u)).elim

/-- An auxiliary coefficient parametrization used only to prove bijectivity of
the chart-linear map. -/
def divisorResidueSourceCoefficients (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) :
    ((Σ u : LatticeResidues κ ell,
      DivisorWeight A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) →₀ R) ≃+
      (∀ u : LatticeResidues κ ell,
        DivisorSectionModule R A
          (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :=
  (Finsupp.sigmaFinsuppLEquivPiFinsupp R).toAddEquiv.trans
    (AddEquiv.piCongrRight fun u =>
      (divisorSectionCoefficientsAddEquiv R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1).symm)

@[simp] theorem divisorResidueSourceCoefficients_single (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ)
    (u : LatticeResidues κ ell)
    (m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) (r : R) :
    divisorResidueSourceCoefficients R A b ell (Finsupp.single ⟨u, m⟩ r) =
      Pi.single u (divisorSectionSingle R A _ 1 m r) := by
  classical
  funext v
  apply (divisorSectionCoefficientsAddEquiv R A _ 1).injective
  by_cases h : u = v
  · subst v
    ext n
    simp [divisorResidueSourceCoefficients, Finsupp.single_apply, Sigma.mk.inj_iff]
  · ext n
    simp [divisorResidueSourceCoefficients, Pi.single_apply, h, Ne.symm h,
      Finsupp.single_apply]

set_option maxHeartbeats 200000 in
/-- The explicit chart-linear sum is exactly the regrouping of all admissible
Laurent coefficients by their unique residues. -/
theorem divisorResidueSum_sourceCoefficients (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (z : (Σ u : LatticeResidues κ ell,
      DivisorWeight A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) →₀ R) :
    divisorResidueSum R A b ell hell (divisorResidueSourceCoefficients R A b ell z) =
      (divisorSectionCoefficientsAddEquiv R A b ell).symm
        (Finsupp.domLCongr (R := R) (divisorWeightResidueEquiv A b ell hell) z) := by
  let Source := (Σ u : LatticeResidues κ ell,
    DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u))) →₀ R
  let Target := DivisorCoefficients R A b
  let coefficients := divisorSectionCoefficientsAddEquiv R A b ell
  let source : Source ≃+ (∀ u : LatticeResidues κ ell,
      DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) :=
    divisorResidueSourceCoefficients R A b ell
  let sourceMap : Source →+ Target := coefficients.toAddMonoidHom.comp
    ((divisorResidueSum R A b ell hell).toAddMonoidHom.comp source.toAddMonoidHom)
  let targetMap : Source →+ Target :=
    (Finsupp.domCongr (divisorWeightResidueEquiv A b ell hell)).toAddMonoidHom
  have maps_equal : sourceMap = targetMap := by
    apply Finsupp.addHom_ext
    rintro ⟨u, m⟩ r
    change divisorSectionCoefficientsAddEquiv R A b ell
        (divisorResidueSum R A b ell hell
          (divisorResidueSourceCoefficients R A b ell (Finsupp.single ⟨u, m⟩ r))) =
      Finsupp.equivMapDomain (divisorWeightResidueEquiv A b ell hell)
        (Finsupp.single ⟨u, m⟩ r)
    exact (congrArg
        (fun sections => divisorSectionCoefficientsAddEquiv R A b ell
          (divisorResidueSum R A b ell hell sections))
        (divisorResidueSourceCoefficients_single R A b ell u m r)).trans
      ((congrArg (divisorSectionCoefficientsAddEquiv R A b ell)
        (divisorResidueSum_single R A b ell hell u m r)).trans
        ((divisorSectionCoefficientsAddEquiv_single R A b ell
          (divisorWeightResidueEquiv A b ell hell ⟨u, m⟩) r).trans
          (Finsupp.equivMapDomain_single (divisorWeightResidueEquiv A b ell hell)
            ⟨u, m⟩ r).symm))
  apply coefficients.injective
  rw [AddEquiv.apply_symm_apply]
  change sourceMap z = targetMap z
  exact DFunLike.congr_fun maps_equal z


theorem divisorResidueSum_bijective (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    Function.Bijective (divisorResidueSum R A b ell hell) := by
  let S := divisorResidueSourceCoefficients R A b ell
  let T := (Finsupp.domLCongr
      (divisorWeightResidueEquiv A b ell hell) : _ ≃ₗ[R] _).toAddEquiv.trans
    (divisorSectionCoefficientsAddEquiv R A b ell).symm
  have h (z) : divisorResidueSum R A b ell hell (S z) = T z :=
    divisorResidueSum_sourceCoefficients R A b ell hell z
  constructor
  · intro x y hxy
    obtain ⟨z, rfl⟩ := S.surjective x
    obtain ⟨w, rfl⟩ := S.surjective y
    apply congrArg S
    apply T.injective
    simpa only [← h z, ← h w] using hxy
  · intro y
    obtain ⟨z, hz⟩ := T.surjective y
    exact ⟨S z, (h z).trans hz⟩

/-- The full affine-chart splitting for an arbitrary integer ray matrix and
every divisor coefficient vector.  The target is the literal divisor module
with scalar action through the power map.  No regularity, characteristic, or
completeness assumption is required for this affine module identity. -/
def divisorSectionResidueLinearEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell) :
    (∀ u : LatticeResidues κ ell,
      DivisorSectionModule R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) 1) ≃ₗ[RayChartRing R A]
      DivisorSectionModule R A b ell :=
  LinearEquiv.ofBijective (divisorResidueSum R A b ell hell)
    (divisorResidueSum_bijective R A b ell hell)

end ToricPower
