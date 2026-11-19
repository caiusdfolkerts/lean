module
public import resolution_existence.part008
public import mixed_results.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.RegularSubstitutionFineResolution -/
section

/-! # The complete finite free resolution clause of Corollary 5.8

The source resolution is constructed from the actual fine Koszul homology.
Its finite bases carry the exponent-vector shifts. Evaluation at a positive
homogeneous regular sequence yields an actual finite free minimal resolution
of the literal substituted ideal, with these same bases and weighted shifts.
No source resolution or exactness assertion is supplied as a hypothesis.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Sublattice
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → MvPolynomial Y K) (w : V → ℕ) (hhom : ∀ v,(f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v,0<w v)
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)]
  [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (hvars : ∀ v,algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v) (B : Family V)

def monomialResolution :
    ProjectiveResolution (ModuleCat.of R
      ((monomialIdeal K B).map (MvPolynomial.aeval f).toRingHom)) :=
  idealResolution f w hhom hreg hw hvars (monomialIdeal K B)
    (MonomialFineResolution.resolution (K := K) B)

def monomialResolutionBasis (p : ℕ) :
    Module.Basis (MonomialFineResolution.ResolutionIndex (K := K) B p) R
      ((monomialResolution f w hhom hreg hw hvars B).complex.X p) :=
  baseChangedResolutionBasis f w hhom hreg hw hvars
    (MonomialFineResolution.resolution (K := K) B) (MonomialFineResolution.resolutionBasis (K := K) B) p

instance monomialResolution_free (p : ℕ) :
    Module.Free R ((monomialResolution f w hhom hreg hw hvars B).complex.X p) :=
  Module.Free.of_basis (monomialResolutionBasis f w hhom hreg hw hvars B p)

instance monomialResolution_finite (p : ℕ) :
    Module.Finite R ((monomialResolution f w hhom hreg hw hvars B).complex.X p) :=
  Module.Finite.of_basis (monomialResolutionBasis f w hhom hreg hw hvars B p)

/-- The specialized complex has the same finite length. -/
theorem monomialResolution_zero_above (p : ℕ) (hp : Fintype.card V<p) :
    Subsingleton ((monomialResolution f w hhom hreg hw hvars B).complex.X p) := by
  have he : IsEmpty (MonomialFineResolution.ResolutionIndex (K := K) B p) :=
    ⟨fun a => Nat.not_lt_of_ge
      (a.property ▸ MonomialFineResolution.homologyIndex_homological_le (K := K) B a.val) hp⟩
  letI := he
  refine ⟨fun x y => (monomialResolutionBasis f w hhom hreg hw hvars B p).repr.injective ?_⟩
  ext i
  exact isEmptyElim i

theorem monomialResolution_minimal (p : ℕ)
    (i : MonomialFineResolution.ResolutionIndex (K := K) B (p+1))
    (j : MonomialFineResolution.ResolutionIndex (K := K) B p) :
    (monomialResolutionBasis f w hhom hreg hw hvars B p).repr
      ((monomialResolution f w hhom hreg hw hvars B).complex.d (p+1) p
        (monomialResolutionBasis f w hhom hreg hw hvars B (p+1) i)) j∈
          MvPolynomial.idealOfVars Y K :=
  baseChangedResolution_minimal f w hhom hreg hw hvars
    (MonomialFineResolution.resolution (K := K) B) (MonomialFineResolution.resolutionBasis (K := K) B)
    (MonomialFineResolution.resolution_minimal (K := K) B) p i j

/-- The matrix degree is exactly the difference of the regraded shifts. -/
theorem monomialResolution_regraded (p : ℕ)
    (i : MonomialFineResolution.ResolutionIndex (K := K) B (p+1))
    (j : MonomialFineResolution.ResolutionIndex (K := K) B p) :
    ((monomialResolutionBasis f w hhom hreg hw hvars B p).repr
      ((monomialResolution f w hhom hreg hw hvars B).complex.d (p+1) p
        (monomialResolutionBasis f w hhom hreg hw hvars B (p+1) i)) j).IsHomogeneous
          (Finsupp.weight w i.val.1-Finsupp.weight w j.val.1) :=
  baseChangedResolution_regraded_entry f w hhom hreg hw hvars
    (MonomialFineResolution.resolution (K := K) B) (MonomialFineResolution.resolutionBasis (K := K) B)
    p _ i j (MonomialFineResolution.resolution_weighted_entry (K := K) B w p i j)

/-- Every actual matrix entry is the literal evaluation of its fine
homogeneous source entry at the given regular sequence. -/
theorem monomialResolution_entry (p : ℕ)
    (i : MonomialFineResolution.ResolutionIndex (K := K) B (p+1))
    (j : MonomialFineResolution.ResolutionIndex (K := K) B p) :
    (monomialResolutionBasis f w hhom hreg hw hvars B p).repr
      ((monomialResolution f w hhom hreg hw hvars B).complex.d (p+1) p
        (monomialResolutionBasis f w hhom hreg hw hvars B (p+1) i)) j=
      MvPolynomial.aeval f
        ((MonomialFineResolution.resolutionBasis (K := K) B p).repr
          ((MonomialFineResolution.resolution (K := K) B).complex.d (p+1) p
            (MonomialFineResolution.resolutionBasis (K := K) B (p+1) i)) j) :=
  baseChange_entry f hvars (MonomialFineResolution.resolutionBasis (K := K) B (p+1))
    (MonomialFineResolution.resolutionBasis (K := K) B p)
    ((MonomialFineResolution.resolution (K := K) B).complex.d (p+1) p).hom i j

theorem monomialResolution_entry_zero_of_not_le (p : ℕ)
    (i : MonomialFineResolution.ResolutionIndex (K := K) B (p+1))
    (j : MonomialFineResolution.ResolutionIndex (K := K) B p)
    (hij : ¬j.val.1 ≤ i.val.1) :
    (monomialResolutionBasis f w hhom hreg hw hvars B p).repr
      ((monomialResolution f w hhom hreg hw hvars B).complex.d (p+1) p
        (monomialResolutionBasis f w hhom hreg hw hvars B (p+1) i)) j = 0 := by
  rw [monomialResolution_entry,
    MonomialFineResolution.resolution_entry_zero_of_not_le (K := K) B p i j hij, map_zero]

/-- A nonzero coefficient in a homogeneous polynomial satisfies the
additive shift equation whenever incomparable fine shifts give zero. -/
theorem fineShift_degree_of_homogeneous_coefficient
    {q : R} {α β : V →₀ ℕ} (hzero : ¬ β ≤ α → q = 0)
    (hq : q.IsHomogeneous (Finsupp.weight w α - Finsupp.weight w β))
    (a : Y →₀ ℕ) (ha : q.coeff a ≠ 0) :
    a.degree + Finsupp.weight w β = Finsupp.weight w α := by
  have hβα : β ≤ α := by
    by_contra h
    exact ha ((congrArg (fun x : R => x.coeff a) (hzero h)).trans rfl)
  have he := congrArg (Finsupp.weight w) (tsub_add_cancel_of_le hβα)
  rw [map_add] at he
  have hwle : Finsupp.weight w β ≤ Finsupp.weight w α := by omega
  have hd : Finsupp.weight (fun _ : Y => (1 : ℕ)) a =
      Finsupp.weight w α - Finsupp.weight w β := hq ha
  rw [← Finsupp.degree_eq_weight_one] at hd
  rw [hd, Nat.sub_add_cancel hwle]

/-- The additive degree equation states the exact graded-map property
without using truncated subtraction for a potentially negative difference. -/
theorem monomialResolution_regraded_degree (p : ℕ)
    (i : MonomialFineResolution.ResolutionIndex (K := K) B (p+1))
    (j : MonomialFineResolution.ResolutionIndex (K := K) B p)
    (a : Y →₀ ℕ)
    (ha : ((monomialResolutionBasis f w hhom hreg hw hvars B p).repr
      ((monomialResolution f w hhom hreg hw hvars B).complex.d (p+1) p
        (monomialResolutionBasis f w hhom hreg hw hvars B (p+1) i)) j).coeff a ≠ 0) :
    a.degree + Finsupp.weight w j.val.1 = Finsupp.weight w i.val.1 :=
  fineShift_degree_of_homogeneous_coefficient w
    (monomialResolution_entry_zero_of_not_le f w hhom hreg hw hvars B p i j)
    (monomialResolution_regraded f w hhom hreg hw hvars B p i j) a ha

/-- The actual ideal augmentation applied to a scalar-extended basis vector.
This formula is proved before specializing the underlying resolution, so
normalizing a chosen fine homology basis is unnecessary. -/
theorem idealResolution_augmentation_baseChangedBasis (I : Ideal S)
    (P : ProjectiveResolution (ModuleCat.of S I)) {ι : ℕ → Type u}
    (b : ∀ p, Module.Basis (ι p) S (P.complex.X p)) (i : ι 0) :
    ((idealResolution f w hhom hreg hw hvars I P).π.f 0
      (baseChangedResolutionBasis f w hhom hreg hw hvars P b 0 i)).val =
      MvPolynomial.aeval f (P.π.f 0 (b 0 i)).val := by
  change ((idealResolution f w hhom hreg hw hvars I P).π.f 0
    ((b 0).baseChange R i)).val = _
  rw [Module.Basis.baseChange_apply, idealResolution_augmentation_tmul, one_mul]

theorem monomialResolution_augmentation_entry
    (i : MonomialFineResolution.ResolutionIndex (K := K) B 0) :
    ((monomialResolution f w hhom hreg hw hvars B).π.f 0
      (monomialResolutionBasis f w hhom hreg hw hvars B 0 i)).val =
      MvPolynomial.aeval f
        ((MonomialFineResolution.resolution (K := K) B).π.f 0
          (MonomialFineResolution.resolutionBasis (K := K) B 0 i)).val :=
  idealResolution_augmentation_baseChangedBasis f w hhom hreg hw hvars (monomialIdeal K B)
    (MonomialFineResolution.resolution (K := K) B)
    (MonomialFineResolution.resolutionBasis (K := K) B) i

/-- The actual augmentation preserves the same weighted shifts as the
differential, so the specialized resolution is graded all the way to its ideal. -/
theorem monomialResolution_augmentation_regraded
    (i : MonomialFineResolution.ResolutionIndex (K := K) B 0) :
    (((monomialResolution f w hhom hreg hw hvars B).π.f 0
      (monomialResolutionBasis f w hhom hreg hw hvars B 0 i)).val).IsHomogeneous
        (Finsupp.weight w i.val.1) := by
  exact (congrArg (fun x : R => x.IsHomogeneous (Finsupp.weight w i.val.1))
    (monomialResolution_augmentation_entry f w hhom hreg hw hvars B i)).mpr
    (aeval_weightedHomogeneous f w hhom _ _
      (MonomialFineResolution.resolution_augmentation_weighted (K := K) B w i))

end FourPapers.PolynomialRegularSubstitution

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg.Polymatroid
universe u
variable {K Y : Type u} [Field K] {d : ℕ} {n : Fin d → ℕ}
  (f : FiniteVariable.{u} n → MvPolynomial Y K)
  (w : FiniteVariable.{u} n → ℕ) (hhom : ∀ v,(f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v,0<w v)

/-- Every substituted power has the explicitly constructed actual finite
free minimal resolution. The remaining basis and matrix theorems above retain
its fine shifts and the exact weighted regrading. -/
def corollary58_powerFreeResolution (E : Finset (FiniteTuple n)) (m : ℕ) :
    ProjectiveResolution (ModuleCat.of (MvPolynomial Y K)
      ↥(substitutedSublatticeIdeal f E ^ m)) := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  let B := exponentPowerFamily (finiteRowFamily n E) m
  let Q := PolynomialRegularSubstitution.monomialResolution f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) B
  have hI : (monomialIdeal K B).map (MvPolynomial.aeval f).toRingHom=
      substitutedSublatticeIdeal f E ^ m := by
    rw [show monomialIdeal K B=finiteSublatticeIdeal n (k := K) E ^ m from
      finitePowerFamily_ideal n E m,substitutedSublatticeIdeal_pow]
  let e := (LinearEquiv.ofEq _ _ hI).toModuleIso
  exact
    { complex := Q.complex
      projective := Q.projective
      π := Q.π ≫ (ChainComplex.single₀ (ModuleCat (MvPolynomial Y K))).map e.hom
      quasiIso := by infer_instance }

abbrev SubstitutedPowerResolutionIndex (E : Finset (FiniteTuple n)) (m p : ℕ) :=
  MonomialFineResolution.ResolutionIndex (K := K)
    (exponentPowerFamily (finiteRowFamily n E) m) p

def substitutedPowerResolutionBasis (E : Finset (FiniteTuple n)) (m p : ℕ) :
    Module.Basis (SubstitutedPowerResolutionIndex (K := K) E m p) (MvPolynomial Y K)
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.X p) := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolutionBasis f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) (exponentPowerFamily (finiteRowFamily n E) m) p

instance substitutedPowerResolution_free (E : Finset (FiniteTuple n)) (m p : ℕ) :
    Module.Free (MvPolynomial Y K)
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.X p) :=
  Module.Free.of_basis (substitutedPowerResolutionBasis f w hhom hreg hw E m p)

instance substitutedPowerResolution_finite (E : Finset (FiniteTuple n)) (m p : ℕ) :
    Module.Finite (MvPolynomial Y K)
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.X p) :=
  Module.Finite.of_basis (substitutedPowerResolutionBasis f w hhom hreg hw E m p)

theorem corollary58_powerFreeResolution_minimal (E : Finset (FiniteTuple n)) (m p : ℕ)
    (i : SubstitutedPowerResolutionIndex (K := K) E m (p+1))
    (j : SubstitutedPowerResolutionIndex (K := K) E m p) :
    (substitutedPowerResolutionBasis f w hhom hreg hw E m p).repr
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.d (p+1) p
        (substitutedPowerResolutionBasis f w hhom hreg hw E m (p+1) i)) j∈
          MvPolynomial.idealOfVars Y K := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolution_minimal f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) (exponentPowerFamily (finiteRowFamily n E) m) p i j

theorem corollary58_powerFreeResolution_regraded (E : Finset (FiniteTuple n)) (m p : ℕ)
    (i : SubstitutedPowerResolutionIndex (K := K) E m (p+1))
    (j : SubstitutedPowerResolutionIndex (K := K) E m p) :
    ((substitutedPowerResolutionBasis f w hhom hreg hw E m p).repr
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.d (p+1) p
        (substitutedPowerResolutionBasis f w hhom hreg hw E m (p+1) i)) j).IsHomogeneous
          (Finsupp.weight w i.val.1-Finsupp.weight w j.val.1) := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolution_regraded f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) (exponentPowerFamily (finiteRowFamily n E) m) p i j

/-- Every nonzero polynomial coefficient has exactly the additive degree
required by the source and target shifts, including when their numerical
difference would be negative. -/
theorem corollary58_powerFreeResolution_degree (E : Finset (FiniteTuple n)) (m p : ℕ)
    (i : SubstitutedPowerResolutionIndex (K := K) E m (p+1))
    (j : SubstitutedPowerResolutionIndex (K := K) E m p) (a : Y →₀ ℕ)
    (ha : ((substitutedPowerResolutionBasis f w hhom hreg hw E m p).repr
      ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.d (p+1) p
        (substitutedPowerResolutionBasis f w hhom hreg hw E m (p+1) i)) j).coeff a ≠ 0) :
    a.degree + Finsupp.weight w j.val.1 = Finsupp.weight w i.val.1 := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolution_regraded_degree f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) (exponentPowerFamily (finiteRowFamily n E) m) p i j a ha

theorem corollary58_powerFreeResolution_bounded (E : Finset (FiniteTuple n)) (m p : ℕ)
    (hp : Fintype.card (FiniteVariable.{u} n)<p) :
    Subsingleton ((corollary58_powerFreeResolution f w hhom hreg hw E m).complex.X p) := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolution_zero_above f w hhom hreg hw
    (fun v => MvPolynomial.aeval_X f v) (exponentPowerFamily (finiteRowFamily n E) m) p hp

/-- The augmentation of the literal substituted-power resolution has
exactly the weighted fine degree assigned to its degree-zero generator. -/
theorem corollary58_powerFreeResolution_augmentation_regraded
    (E : Finset (FiniteTuple n)) (m : ℕ)
    (i : SubstitutedPowerResolutionIndex (K := K) E m 0) :
    (((corollary58_powerFreeResolution f w hhom hreg hw E m).π.f 0
      (substitutedPowerResolutionBasis f w hhom hreg hw E m 0 i)).val).IsHomogeneous
        (Finsupp.weight w i.val.1) := by
  letI := PolynomialRegularSubstitution.substitutionAlgebra f
  letI : IsScalarTower K (MvPolynomial (FiniteVariable.{u} n) K) (MvPolynomial Y K) :=
    IsScalarTower.of_algHom (MvPolynomial.aeval f)
  exact PolynomialRegularSubstitution.monomialResolution_augmentation_regraded
    f w hhom hreg hw (fun v => MvPolynomial.aeval_X f v)
    (exponentPowerFamily (finiteRowFamily n E) m) i

/-- The fine shifts in the base-changed minimal resolution have the
multiplicities of the original actual fine Tor, for every power. -/
theorem corollary58_powerFreeResolution_shift_multiplicity
    (E : Finset (FiniteTuple n)) (m p : ℕ) (α : CommAlg.Polymatroid.Exponent (FiniteVariable.{u} n)) :
    Nat.card {i : SubstitutedPowerResolutionIndex (K := K) E m p // i.val.1=α}=
      CommAlg.Koszul.bettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) α p :=
  MonomialFineResolution.resolution_shift_multiplicity (K := K)
    (exponentPowerFamily (finiteRowFamily n E) m) α p

end FourPapers.Sublattice

end
end
end

end
