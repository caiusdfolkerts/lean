module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.Finset.SDiff
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

/-! Exact recovered ordinary invariant-curve degree proofs. See adjacent source manifest. -/

section Source_ToricFanNoetherian




/-!
# Noetherianity of the actual fan scheme

The coordinate rings are actual polynomial rings over iterated Laurent
extensions, up to the previously constructed algebra equivalences. Hilbert's
basis theorem and localization prove that they are Noetherian. The actual
finite affine open cover then proves that the glued scheme is Noetherian.
-/


namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

theorem laurent_isNoetherianRing (A : Type*) [CommRing A]
    [IsNoetherianRing A] : IsNoetherianRing (AddMonoidAlgebra A ℤ) :=
  IsLocalization.isNoetherianRing
    (Submonoid.powers (Polynomial.X : Polynomial A))
    (AddMonoidAlgebra A ℤ) inferInstance

theorem torusCoordinateRing_isNoetherianRing (n : ℕ) :
    IsNoetherianRing (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_ringEquiv k
        (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).symm.toRingEquiv
  | succ n ih =>
      letI := ih
      letI := laurent_isNoetherianRing (torusCoordinateRing k n)
      exact isNoetherianRing_of_ringEquiv
        (AddMonoidAlgebra (torusCoordinateRing k n) ℤ)
        (torusCoordinateRingSucc k n).symm.toRingEquiv

theorem finiteCharacterRing_isNoetherianRing (J : Type*) [Fintype J] :
    IsNoetherianRing (AddMonoidAlgebra k (J → ℤ)) := by
  letI := torusCoordinateRing_isNoetherianRing k (Fintype.card J)
  exact isNoetherianRing_of_ringEquiv _ (finiteCharacterRingEquiv k J).symm.toRingEquiv

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartRing_isNoetherianRing (s : Finset (Lattice n)) (hs : s∈«Σ».cones) :
    IsNoetherianRing (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b,I,hI,⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isNoetherianRing k (FreeCoordinate I)
  exact isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv

instance fanScheme_isLocallyNoetherian : IsLocallyNoetherian («Σ».fanScheme k) := by
  apply (isLocallyNoetherian_iff_openCover («Σ».fanSchemeOpenCover k)).mpr
  intro s
  letI := «Σ».chartRing_isNoetherianRing k s.val s.property
  change IsLocallyNoetherian (Spec (CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid s.val))))
  infer_instance

instance fanScheme_isNoetherian : IsNoetherian («Σ».fanScheme k) where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := by
    letI : Finite («Σ».fanSchemeOpenCover k).I₀ :=
      inferInstanceAs (Finite «Σ».ConeIndex)
    letI : ∀ s : («Σ».fanSchemeOpenCover k).I₀,
        CompactSpace ((«Σ».fanSchemeOpenCover k).X s) := fun s => by
      change CompactSpace (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val))))
      infer_instance
    exact Scheme.OpenCover.compactSpace («Σ».fanSchemeOpenCover k)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_isNoetherian
end Source_ToricFanNoetherian

section Source_ToricProjectiveLineFan




/-!
# The actual two-chart projective line

The complete rank-one fan has the primitive rays `1` and `-1`. Its scheme
is the actual gluing of the two affine polynomial charts along their common
Laurent chart. The algebra equivalences below identify the coordinate on
each affine chart with the corresponding primitive character.
-/


namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

def projectiveLineRay (negative : Bool) : Lattice 1 :=
  fun _ => if negative then -1 else 1

def projectiveLineBasis (negative : Bool) : Module.Basis (Fin 1) ℤ (Lattice 1) :=
  if negative then (Pi.basisFun ℤ (Fin 1)).map (LinearEquiv.neg ℤ)
  else Pi.basisFun ℤ (Fin 1)

theorem projectiveLineBasis_apply (negative : Bool) (i : Fin 1) :
    projectiveLineBasis negative i = projectiveLineRay negative := by
  cases negative <;> ext j <;>
    simp [projectiveLineBasis,projectiveLineRay,Pi.basisFun_apply,
      Subsingleton.elim i j]

theorem projectiveLineBasis_rays (negative : Bool) :
    Finset.univ.image (projectiveLineBasis negative) = {projectiveLineRay negative} := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    exact projectiveLineBasis_apply negative i
  · rintro rfl
    exact ⟨0,projectiveLineBasis_apply negative 0⟩

theorem projectiveLineRay_ne : projectiveLineRay false ≠ projectiveLineRay true := by
  intro h
  have hh := congrFun h (0 : Fin 1)
  norm_num [projectiveLineRay] at hh

theorem mem_finiteRayCone_singleton_iff {E : Type*} [AddCommGroup E]
    [Module ℝ E] (v x : E) :
    x∈finiteRayCone {v} ↔ ∃ a : ℝ, 0≤a ∧ a • v=x := by
  constructor
  · rintro ⟨c,hc,hx⟩
    exact ⟨c v,hc v (Finset.mem_singleton_self v),by simpa only [Finset.sum_singleton] using hx⟩
  · rintro ⟨a,ha,hx⟩
    exact ⟨fun _ => a,fun _ _ => ha,by simpa only [Finset.sum_singleton] using hx⟩

theorem mem_projectiveLineCone (negative : Bool) (x : Ambient 1) :
    x∈latticeRayCone {projectiveLineRay negative} ↔
      0≤(if negative then -x 0 else x 0) := by
  rw [latticeRayCone,Finset.image_singleton,mem_finiteRayCone_singleton_iff]
  cases negative
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      have ha0 : a=x 0 := by simpa [embed,projectiveLineRay] using h
      simpa only [ha0, Bool.false_eq_true, ite_false] using ha
    · intro hx
      refine ⟨x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      simp [embed,projectiveLineRay] at h
      change 0≤-x 0
      linarith
    · intro hx
      refine ⟨-x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]

theorem projectiveLineCone_inter :
    latticeRayCone {projectiveLineRay false} ⊓
      latticeRayCone {projectiveLineRay true} = ⊥ := by
  ext x
  simp only [Submodule.mem_inf,mem_projectiveLineCone,Bool.false_eq_true,
    if_false,if_true,Submodule.mem_bot]
  constructor
  · intro h
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simp only [hi,Pi.zero_apply]
    linarith [h.1,h.2]
  · rintro rfl
    simp

theorem projectiveLineBasis_inter (a b : Bool) :
    latticeRayCone (Finset.univ.image (projectiveLineBasis a)) ⊓
      latticeRayCone (Finset.univ.image (projectiveLineBasis b)) =
        latticeRayCone ((Finset.univ.image (projectiveLineBasis a)) ∩
          (Finset.univ.image (projectiveLineBasis b))) := by
  rw [projectiveLineBasis_rays,projectiveLineBasis_rays]
  cases a <;> cases b
  · simp
  · have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · rw [inf_comm,Finset.inter_comm]
    have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · simp

theorem projectiveLineBasis_cover (x : Ambient 1) :
    ∃ negative : Bool,
      x∈latticeRayCone (Finset.univ.image (projectiveLineBasis negative)) := by
  by_cases hx : 0≤x 0
  · exact ⟨false,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      Bool.false_eq_true,ite_false] using hx⟩
  · exact ⟨true,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      ite_true] using
      neg_nonneg.mpr (le_of_not_ge hx)⟩

/-- The fan is proved smooth and complete by its actual real cones. -/
def projectiveLineFan : SmoothCompleteFan 1 :=
  fanOfBasisFamily projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineFan_isPure : projectiveLineFan.IsPure :=
  fanOfBasisFamily_isPure projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineRayCone_mem (negative : Bool) :
    {projectiveLineRay negative} ∈ projectiveLineFan.cones := by
  apply (mem_basisFamilyCones projectiveLineBasis _).mpr
  exact ⟨negative,by simpa only [projectiveLineBasis_rays] using
    (Finset.Subset.refl {projectiveLineRay negative})⟩

theorem mem_projectiveLineFan_cones (s : Finset (Lattice 1)) :
    s∈projectiveLineFan.cones ↔
      s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  rw [show projectiveLineFan.cones=basisFamilyCones projectiveLineBasis from rfl,
    mem_basisFamilyCones]
  simp only [projectiveLineBasis_rays,Finset.subset_singleton_iff]
  constructor
  · rintro ⟨b,h⟩
    rcases h with h|h
    · exact Or.inl h
    · cases b
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (h|h|h)
    · exact ⟨false,Or.inl h⟩
    · exact ⟨false,Or.inr h⟩
    · exact ⟨true,Or.inr h⟩

theorem mem_projectiveLineDualCone (negative : Bool) (m : Lattice 1) :
    m∈dualConeMonoid {projectiveLineRay negative} ↔
      0≤(if negative then -m 0 else m 0) := by
  change (∀ u∈({projectiveLineRay negative} : Finset (Lattice 1)),
    0≤ integerPairing u m) ↔ _
  cases negative <;> simp [integerPairing,projectiveLineRay]

/-- Exact natural-number coordinates on the actual dual semigroup. -/
def projectiveLineSemigroupEquiv (negative : Bool) :
    dualConeMonoid {projectiveLineRay negative} ≃+ ℕ where
  toFun m := (if negative then -m.val 0 else m.val 0).toNat
  invFun a := ⟨fun _ => if negative then -(a : ℤ) else a,by
    rw [mem_projectiveLineDualCone]
    cases negative <;> simp⟩
  left_inv m := by
    apply Subtype.ext
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp only [hi,if_false,if_true] at hm ⊢
    · exact Int.toNat_of_nonneg hm
    · rw [Int.toNat_of_nonneg hm,neg_neg]
  right_inv a := by cases negative <;> simp
  map_add' m p := by
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    have hp := (mem_projectiveLineDualCone negative p.val).mp p.property
    cases negative
    · exact Int.toNat_add hm hp
    · change (-(m.val 0 + p.val 0)).toNat = (-m.val 0).toNat + (-p.val 0).toNat
      rw [neg_add]
      exact Int.toNat_add (by simpa using hm) (by simpa using hp)

variable (k : Type*) [Field k]

/-- Each affine chart is the actual affine line. -/
def projectiveLineChartRingEquiv (negative : Bool) :
    monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative}) ≃ₐ[k]
      Polynomial k :=
  (monoidChartAlgebraEquiv k _).symm.trans
    ((AddMonoidAlgebra.domCongr k k (projectiveLineSemigroupEquiv negative)).trans
      (Polynomial.toFinsuppIsoAlg k).symm)

/-- The usual two affine lines with inverted transition coordinate, as an
actual scheme obtained by the already verified common-face gluing. -/
abbrev projectiveLineScheme : Scheme := projectiveLineFan.fanScheme k

def projectiveLineChart (negative : Bool) :
    coneChart k {projectiveLineRay negative} ⟶ projectiveLineScheme k :=
  projectiveLineFan.fanChartMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLineChart k negative) :=
  projectiveLineFan.fanChartMap_isOpenImmersion k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineScheme_isIntegral : IsIntegral (projectiveLineScheme k) :=
  inferInstanceAs (IsIntegral (projectiveLineFan.fanScheme k))

instance projectiveLineScheme_isNoetherian : IsNoetherian (projectiveLineScheme k) :=
  inferInstanceAs (IsNoetherian (projectiveLineFan.fanScheme k))

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineBasis_inter
#print axioms PaperVerification.ToricGeometry.projectiveLineChartRingEquiv
end Source_ToricProjectiveLineFan

section Source_ToricCoordinateOrders




/-!
# Actual orders along coordinate boundary primes

The local ring is the literal localization at the principal coordinate
prime. Its DVR structure, its uniformizer, and the units in the other
coordinate directions are proved. The order is Mathlib's order of
vanishing defined from module length and its fraction-field extension,
rather than a newly defined exponent function.
-/


namespace PaperVerification.ToricSchemes

open IsLocalRing
open scoped BigOperators Classical nonZeroDivisors

section PrincipalPrime

variable (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] [IsLocalRing S] [IsDomain S]

theorem maximalIdeal_eq_span_of_principalPrime (p : R) (hP : P = Ideal.span {p}) :
    maximalIdeal S = Ideal.span {algebraMap R S p} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, hP,
    Ideal.map_span, Set.image_singleton]

/-- A Noetherian domain localized at a nonzero principal prime is a DVR.
The conclusion is proved from the actual principal maximal ideal. -/
theorem principalPrimeLocalization_isDiscreteValuationRing
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    IsDiscreteValuationRing S := by
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hp' : algebraMap R S p ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hp
  have hmax := maximalIdeal_eq_span_of_principalPrime R S P p hP
  have hnot : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [hmax, Ideal.span_singleton_eq_bot]
    exact hp'
  have hprincipal : (maximalIdeal S).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE S hnot).out 5 1).mp hprincipal

theorem principalPrimeLocalization_generator_irreducible
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    Irreducible (algebraMap R S p) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact (map_ne_zero_iff _
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).mpr hp
  · exact maximalIdeal_eq_span_of_principalPrime R S P p hP

end PrincipalPrime

variable (k : Type*) [Field k] {n : ℕ}

/-- The actual prime ideal defining the i-th coordinate boundary. -/
def coordinatePrime (i : Fin n) : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {MvPolynomial.X i}

instance coordinatePrime_isPrime (i : Fin n) : (coordinatePrime k i).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (MvPolynomial.X_prime (R := k) (i := i))

abbrev coordinateBoundaryLocalRing (i : Fin n) :=
  Localization.AtPrime (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDomain (i : Fin n) :
    IsDomain (coordinateBoundaryLocalRing k i) :=
  IsLocalization.isDomain_of_atPrime _ (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDiscreteValuationRing (i : Fin n) :
    IsDiscreteValuationRing (coordinateBoundaryLocalRing k i) :=
  principalPrimeLocalization_isDiscreteValuationRing
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

def coordinateBoundaryParameter (i j : Fin n) : coordinateBoundaryLocalRing k i :=
  algebraMap (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i) (MvPolynomial.X j)

theorem coordinateBoundaryParameter_irreducible (i : Fin n) :
    Irreducible (coordinateBoundaryParameter k i i) :=
  principalPrimeLocalization_generator_irreducible
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

theorem coordinateBoundaryParameter_isUnit (i j : Fin n) (hij : i ≠ j) :
    IsUnit (coordinateBoundaryParameter k i j) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (S := coordinateBoundaryLocalRing k i) (I := coordinatePrime k i)
      (MvPolynomial.X j)).mpr
  change MvPolynomial.X j ∉ Ideal.span {MvPolynomial.X i}
  rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X]
  exact hij

variable (i : Fin n) (K : Type*) [Field K]
    [Algebra (coordinateBoundaryLocalRing k i) K]
    [IsFractionRing (coordinateBoundaryLocalRing k i) K]

/-- The literal order of the coordinate defining the boundary is one. -/
theorem ordFrac_X_i :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i i)) = WithZero.exp (1 : ℤ) :=
  Ring.ordFrac_irreducible (coordinateBoundaryParameter_irreducible k i)

theorem ordFrac_X_other (j : Fin n) (hij : i ≠ j) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = 1 :=
  Ring.ordFrac_of_isUnit (coordinateBoundaryParameter_isUnit k i j hij)

theorem ordFrac_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = WithZero.exp (1 : ℤ) := by
  rw [map_prod]
  rw [Finset.prod_eq_single i]
  · exact ordFrac_X_i k i K
  · intro j hj hji
    exact ordFrac_X_other k i K j hji.symm
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coefficient of a logarithmic volume relative to a regular
coordinate volume has the genuine order -1 at every boundary prime. -/
theorem ordFrac_inverse_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      ((∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j))⁻¹) = WithZero.exp (-1 : ℤ) := by
  rw [map_inv₀, ordFrac_coordinate_product, WithZero.inv_exp]

/-- The familiar exponent formula is a consequence of actual DVR order,
and holds for all integral character exponents. -/
theorem ordFrac_coordinate_character (m : Fin n → ℤ) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) ^ m j) = WithZero.exp (m i) := by
  rw [map_prod]
  simp_rw [map_zpow₀]
  rw [Finset.prod_eq_single i]
  · rw [ordFrac_X_i, ← WithZero.exp_zsmul]
    simp
  · intro j hj hji
    rw [ordFrac_X_other k i K j hji.symm, one_zpow]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.principalPrimeLocalization_isDiscreteValuationRing
#print axioms PaperVerification.ToricSchemes.ordFrac_inverse_coordinate_product

end Source_ToricCoordinateOrders

section Source_ToricAffineBoundaryOrders




/-!
# From an actual affine boundary prime to scheme order

The stalk equivalence below is composed from the actual affine stalk
localization and the actual open-immersion stalk map. Its compatibility
with the coordinate-ring embedding in the generic stalk is proved.
Principal prime uniformizers therefore compute the scheme's ordinary
order function at the corresponding actual point.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical nonZeroDivisors

variable (R : CommRingCat.{u}) [IsDomain R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec R ⟶ X) [IsOpenImmersion j]

local instance affineOpenStalkMap_isIso (p : PrimeSpectrum R) : IsIso (j.stalkMap p) :=
  (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j)).2
    (show Spec R from p)

/-- The genuine affine localization isomorphism followed by the inverse
of the genuine open-immersion map on local rings. -/
def affineOpenStalkEquiv (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk (j p) :=
  ((Spec.stalkIso R p).symm ≪≫ (asIso (j.stalkMap p)).symm).commRingCatIsoToRingEquiv

@[simp] theorem affineOpenStalkEquiv_stalkMap (p : PrimeSpectrum R)
    (r : Localization.AtPrime p.asIdeal) :
    j.stalkMap p (affineOpenStalkEquiv R j p r) = (Spec.stalkIso R p).inv r := by
  change (asIso (j.stalkMap p)).hom
    ((asIso (j.stalkMap p)).inv ((Spec.stalkIso R p).inv r)) =
      (Spec.stalkIso R p).inv r
  exact Iso.inv_hom_id_apply (asIso (j.stalkMap p)) _

theorem affineOpenStalkEquiv_algebraMap (p : PrimeSpectrum R) (r : R) :
    affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p, trivial, rfl⟩
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)) := by
  apply (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv.injective
  change j.stalkMap p
      (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
    j.stalkMap p (X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p,trivial,rfl⟩
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)))
  erw [affineOpenStalkEquiv_stalkMap, j.germ_stalkMap_apply]
  have hsec := congrArg (fun f => f ((Scheme.ΓSpecIso R).inv r)) (j.appIso_inv_app ⊤)
  erw [hsec]
  erw [(Spec R).presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j ⊤))]
  exact congrArg (fun f => f r) (Spec.algebraMap_stalkIso_inv (R := R) (x := p))

/-- The two routes to the actual generic stalk agree exactly. -/
theorem affineOpenStalkEquiv_functionField (p : PrimeSpectrum R) (r : R) :
    algebraMap (X.presheaf.stalk (j p)) X.functionField
        (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
      affineOpenCoordinateMap R j r := by
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
  rw [affineOpenStalkEquiv_algebraMap]
  exact (X.algebraMap_germ_eq_germToFunctionField
    (U := j ''ᵁ (⊤ : (Spec R).Opens)) (x := j p) ⟨p,trivial,rfl⟩
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))).trans
    (openImmersionRegularToFunctionField_eq_germ_image j ⊤
      ((Scheme.ΓSpecIso R).inv r)).symm

theorem affineOpenCoordinateMap_injective : Function.Injective (affineOpenCoordinateMap R j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

/-- A DVR on the literal affine localization transports to the actual
scheme stalk; no regularity axiom is added to that stalk. -/
theorem affineOpen_stalk_isDiscreteValuationRing (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    IsDiscreteValuationRing (X.presheaf.stalk (j p)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (affineOpenStalkEquiv R j p)

theorem affineOpen_coheight_eq_one (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    Order.coheight (j p) = 1 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk (j p))
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_eq_coe.mp h

variable [IsNoetherianRing R] [IsLocallyNoetherian X]

/-- Exact scheme order of a nonzero principal prime generator on an
actual affine open chart. -/
theorem affineOpen_order_principalPrime (p : PrimeSpectrum R)
    (r : R) (hr : r ≠ 0) (hp : p.asIdeal = Ideal.span {r}) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 1 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    principalPrimeLocalization_isDiscreteValuationRing R
      (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (1 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  apply Ring.ordFrac_irreducible
  exact (principalPrimeLocalization_generator_irreducible R
    (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp).map
      (affineOpenStalkEquiv R j p).toMulEquiv

/-- An element outside the actual affine prime is a local unit, so its
scheme order is zero at the corresponding point. -/
theorem affineOpen_order_of_not_mem (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (0 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  have hu' : IsUnit ((affineOpenStalkEquiv R j p)
      (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
    hu.map (affineOpenStalkEquiv R j p).toRingHom
  simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpen_order_principalPrime

end Source_ToricAffineBoundaryOrders

section Source_ToricCartierOrders




/-!
# Orders and degrees of actual Cartier divisors

The coefficient is computed using Mathlib's order in the actual local ring.
Since our local generators generate `O(D)`, their orders have the opposite
sign from the coefficients of `D`. Independence of the chosen frame follows
from its regular-unit transition function. The construction descends through
the equivalence of embedded fractional sheaves.

The cycle constructor below requires a proof of local finiteness. Thus the
definition of degree cannot silently replace an infinite divisor by a finite
sum or treat a nonproper curve as a proper curve. In the applications the
support and the actual residue degrees are computed on the invariant curve.
-/


universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem rationalOrder_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x,trivial⟩⟩
  simpa only [map_one] using
    X.ord_of_isUnit (U := ⊤) (f := (1 : Γ(X,⊤))) isUnit_one
      (x := x) (show x ∈ (⊤ : X.Opens) from trivial)

theorem rationalOrder_inv {r : X.functionField} (hr : r ≠ 0) (x : X) :
    X.ord r⁻¹ x = - X.ord r x := by
  have h := X.ord_mul (x := x) hr (inv_ne_zero hr)
  rw [mul_inv_cancel₀ hr,rationalOrder_one] at h
  omega

theorem rationalOrder_div {r s : X.functionField}
    (hr : r ≠ 0) (hs : s ≠ 0) (x : X) :
    X.ord (r/s) x = X.ord r x - X.ord s x := by
  rw [div_eq_mul_inv,X.ord_mul hr (inv_ne_zero hs),rationalOrder_inv hs]
  rfl

theorem rationalOrder_pow {r : X.functionField} (hr : r ≠ 0)
    (n : ℕ) (x : X) : X.ord (r^n) x = (n : ℤ) * X.ord r x := by
  induction n with
  | zero => simp [rationalOrder_one]
  | succ n ih =>
      rw [pow_succ,X.ord_mul (pow_ne_zero n hr) hr,ih]
      push_cast
      ring

theorem rationalOrder_zpow {r : X.functionField} (hr : r ≠ 0)
    (n : ℤ) (x : X) : X.ord (r^n) x = n * X.ord r x := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using rationalOrder_pow hr n x
  | negSucc n =>
      rw [zpow_negSucc,rationalOrder_inv (pow_ne_zero _ hr),rationalOrder_pow hr,
        Int.negSucc_eq]
      push_cast
      ring

namespace CartierData

variable (D E : CartierData X)

/-- The order of an actual rational frame is independent of the frame at
every point in the overlap. -/
theorem frameOrder_eq {U W : X.Opens} [Nonempty U] [Nonempty W]
    (e : D.Frame U) (f : D.Frame W) {x : X} (hxU : x∈U) (hxW : x∈W) :
    X.ord (D.frameRationalGenerator e) x =
      X.ord (D.frameRationalGenerator f) x := by
  let V : X.Opens := U⊓W
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  obtain ⟨a,ha⟩ := D.exists_frameTransitionUnit e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (D.frameRationalGenerator_ne_zero f)] at h
  omega

/-- The actual Weil coefficient of a Cartier divisor. At noncodimension-one
points the value is zero, as in Mathlib's order function. -/
def weilCoefficient (x : X) : ℤ :=
  - X.ord (D.localCocycle.generator x : X.functionField) x

/-- Any actual local frame computes the coefficient, not only the selected
frame used in the definition. -/
theorem weilCoefficient_eq_neg_frameOrder {U : X.Opens} [Nonempty U]
    (e : D.Frame U) {x : X} (hxU : x∈U) :
    D.weilCoefficient x = -X.ord (D.frameRationalGenerator e) x := by
  let W := invertibleOpen D.locallyFree x
  letI : Nonempty W := ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
  change -X.ord (D.frameRationalGenerator (invertibleFrame D.locallyFree x)) x = _
  rw [D.frameOrder_eq (invertibleFrame D.locallyFree x) e
    (mem_invertibleOpen D.locallyFree x) hxU]

@[simp] theorem weilCoefficient_eq_zero_of_coheight_ne_one {x : X}
    (hx : Order.coheight x ≠ 1) : D.weilCoefficient x = 0 := by
  simp [weilCoefficient,Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Frames of equivalent embedded fractional sheaves differ by an actual
regular unit. This conclusion uses the embedding-preserving equivalence,
not merely an isomorphism of the underlying line bundles. -/
theorem exists_equivalentFrameTransitionUnit (hDE : D.Equivalent E)
    {U W V : X.Opens} [Nonempty U] [Nonempty W] [Nonempty V]
    (e : D.Frame U) (f : E.Frame W) (hVU : V≤U) (hVW : V≤W) :
    ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
      D.frameRationalGenerator e / E.frameRationalGenerator f := by
  have hD : D.frameRationalGenerator e ∈ E.sectionValueRange V := by
    rw [← D.equivalent_sectionValueRange E hDE V]
    exact ⟨D.frameGenerator e V hVU,D.sectionValue_frameGenerator e hVU⟩
  have hE : E.frameRationalGenerator f ∈ D.sectionValueRange V := by
    rw [D.equivalent_sectionValueRange E hDE V]
    exact ⟨E.frameGenerator f V hVW,E.sectionValue_frameGenerator f hVW⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff f hVW _).mp hD
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff e hVU _).mp hE
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective V
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.frameRationalGenerator_ne_zero e)
    rw [mul_assoc,hb,ha,one_mul]
  let aUnit : Γ(X,V)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  exact ⟨aUnit,(eq_div_iff (E.frameRationalGenerator_ne_zero f)).mpr ha⟩

theorem equivalent_weilCoefficient (hDE : D.Equivalent E) :
    D.weilCoefficient = E.weilCoefficient := by
  funext x
  let U := invertibleOpen D.locallyFree x
  let W := invertibleOpen E.locallyFree x
  let V : X.Opens := U⊓W
  have hxU : x∈U := mem_invertibleOpen D.locallyFree x
  have hxW : x∈W := mem_invertibleOpen E.locallyFree x
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : Nonempty W := ⟨⟨x,hxW⟩⟩
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  let e := invertibleFrame D.locallyFree x
  let f := invertibleFrame E.locallyFree x
  obtain ⟨a,ha⟩ := D.exists_equivalentFrameTransitionUnit E hDE e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (E.frameRationalGenerator_ne_zero f)] at h
  rw [D.weilCoefficient_eq_neg_frameOrder e hxU,
    E.weilCoefficient_eq_neg_frameOrder f hxW]
  omega

/-- The actual Weil cycle, provided its coefficients have locally finite
support. The coefficients are already fixed by the actual local orders. -/
def weilCycle (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle X ℤ where
  toFun := D.weilCoefficient
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := h x

@[simp] theorem weilCycle_apply
    (h : LocallyFiniteSupport D.weilCoefficient) (x : X) :
    D.weilCycle h x = D.weilCoefficient x := rfl

theorem weilCycle_isWeilDivisor
    (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle.IsWeilDivisor (D.weilCycle h) := by
  intro x hx
  by_contra hcodim
  exact hx (D.weilCoefficient_eq_zero_of_coheight_ne_one hcodim)

/-- Finite support is sufficient, without a separatedness or a T1-space
assumption. This is useful for an explicitly computed invariant curve. -/
theorem locallyFiniteSupport_weilCoefficient_of_finite
    (h : (Function.support D.weilCoefficient).Finite) :
    LocallyFiniteSupport D.weilCoefficient := by
  intro x
  exact ⟨Set.univ,Filter.univ_mem,by simpa only [Set.univ_inter] using h⟩

/-- Degree uses the actual residue degrees of the structure morphism. -/
def degree {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) : ℤ :=
  AlgebraicCycle.degree f (D.weilCycle h)

theorem degree_eq_finsum {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) :
    D.degree f h = ∑ᶠ x, f.residueDegree x • D.weilCoefficient x := rfl

theorem degree_eq_sum_of_support_subset {Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] (h : LocallyFiniteSupport D.weilCoefficient)
    (s : Finset X) (hs : Function.support D.weilCoefficient ⊆ s) :
    D.degree f h = ∑ x ∈ s, f.residueDegree x • D.weilCoefficient x := by
  rw [degree_eq_finsum]
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  apply hs
  intro hz
  exact hx (by simp [hz])

theorem equivalent_degree (hDE : D.Equivalent E) {Y : Scheme.{u}}
    (f : X ⟶ Y) [CompactSpace X]
    (hD : LocallyFiniteSupport D.weilCoefficient)
    (hE : LocallyFiniteSupport E.weilCoefficient) :
    D.degree f hD = E.degree f hE := by
  rw [degree_eq_finsum,degree_eq_finsum,D.equivalent_weilCoefficient E hDE]

end CartierData

namespace CartierDivisor

/-- Weil coefficients are independent of the presentation of a Cartier
divisor as an invertible embedded fractional sheaf. -/
def weilCoefficient : CartierDivisor X → X → ℤ :=
  Quotient.lift CartierData.weilCoefficient
    (fun _ _ h => CartierData.equivalent_weilCoefficient _ _ h)

@[simp] theorem weilCoefficient_ofData (D : CartierData X) :
    weilCoefficient (ofData D) = D.weilCoefficient := rfl

end CartierDivisor

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_weilCoefficient
#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_degree
end Source_ToricCartierOrders

section Source_ToricRationalPointDegrees




/-!
# Residue degree at an actual rational point

A section of a scheme morphism induces inverse maps on residue fields
at its image. The proof uses the actual maps on local residue fields.
In particular, the two coordinate boundary points of an invariant
projective line contribute residue degree one over the ground field.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme.{u}}

/-- A section is an isomorphism on the residue field at every point of
its image, regardless of whether the base field is algebraically closed. -/
theorem residueFieldMap_bijective_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    Function.Bijective (f.residueFieldMap (s y)) := by
  have hpoint : f (s y)=y := congrArg (fun g : Y ⟶ Y => g y) hs
  have hcomp : f.residueFieldMap (s y) ≫ s.residueFieldMap y =
      (Y.residueFieldCongr hpoint).hom := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr hs,
      Scheme.residueFieldMap_id]
    exact Category.comp_id ((Y.residueFieldCongr hpoint).hom)
  refine ⟨(f.residueFieldMap (s y)).hom.injective,?_⟩
  intro z
  obtain ⟨a,ha⟩ := (Y.residueFieldCongr hpoint).commRingCatIsoToRingEquiv.surjective
    (s.residueFieldMap y z)
  refine ⟨a,(s.residueFieldMap y).hom.injective ?_⟩
  exact (congrArg (fun g => g a) hcomp).trans ha

/-- Degree one is computed from Mathlib's literal residue extension. -/
theorem residueDegree_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    f.residueDegree (s y) = 1 := by
  letI := (f.residueFieldMap (s y)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (residueFieldMap_bijective_of_section f s hs y)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.residueDegree_of_section
end Source_ToricRationalPointDegrees

section Source_ToricPolynomialBoundary




/-!
# Boundary orders on an actual affine-line chart

The origin is the prime defined by evaluation at zero. Its ideal is
literally `(X)`, and its local ring is the actual DVR at that prime.
The coordinate has order one there and zero at every other point of
the affine chart. Arbitrary integral powers are treated without a
positivity restriction on the exponent.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

variable (k : Type u) [Field k]

def polynomialOrigin : PrimeSpectrum (Polynomial k) :=
  ⟨RingHom.ker (Polynomial.evalRingHom (0 : k)),RingHom.ker_isPrime _⟩

theorem polynomialOrigin_ideal :
    (polynomialOrigin k).asIdeal = Ideal.span {Polynomial.X} := by
  change RingHom.ker (Polynomial.evalRingHom (0 : k)) = _
  simpa using Polynomial.ker_evalRingHom (0 : k)

instance polynomialOrigin_isMaximal : (polynomialOrigin k).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (0 : k))
    (fun a => ⟨Polynomial.C a,by simp⟩)

theorem polynomial_X_mem_iff (p : PrimeSpectrum (Polynomial k)) :
    Polynomial.X ∈ p.asIdeal ↔ p = polynomialOrigin k := by
  constructor
  · intro h
    apply PrimeSpectrum.ext
    symm
    apply (polynomialOrigin_isMaximal k).eq_of_le p.isPrime.ne_top
    rw [polynomialOrigin_ideal]
    apply Ideal.span_le.mpr
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact h
  · rintro rfl
    rw [polynomialOrigin_ideal]
    exact Ideal.subset_span (Set.mem_singleton _)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A regular germ outside the affine prime is a unit even if no DVR
structure is specified. At other codimensions the order is zero by its
ordinary definition. -/
theorem affineOpen_order_zero_of_not_mem (R : CommRingCat.{u})
    [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  by_cases hc : Order.coheight (j p) = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk (j p)) :=
      krullDimLE_of_coheight_le hc.le
    have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
    have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
    have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
      (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
    rw [X.ord_eq_iff hc hr']
    change Ring.ordFrac (X.presheaf.stalk (j p))
      (affineOpenCoordinateMap R j r) = WithZero.exp (0 : ℤ)
    rw [← affineOpenStalkEquiv_functionField R j p r]
    have hu' : IsUnit ((affineOpenStalkEquiv R j p)
        (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
      hu.map (affineOpenStalkEquiv R j p).toRingHom
    simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'
  · exact X.ord_eq_zero_of_coheight_neq_one hc _

variable (j : Spec (.of (Polynomial k)) ⟶ X) [IsOpenImmersion j]

/-- The order of the literal affine coordinate is supported precisely
at the actual origin of that chart. -/
theorem affineLine_coordinate_order (p : PrimeSpectrum (Polynomial k)) :
    X.ord (affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X) (j p) =
      if p = polynomialOrigin k then 1 else 0 := by
  by_cases hp : p=polynomialOrigin k
  · subst p
    rw [if_pos rfl]
    exact affineOpen_order_principalPrime (.of (Polynomial k)) j
      (polynomialOrigin k) Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
  · rw [if_neg hp]
    exact affineOpen_order_zero_of_not_mem (.of (Polynomial k)) j p Polynomial.X
      (fun h => hp ((polynomial_X_mem_iff k p).mp h))

theorem affineLine_coordinate_zpow_order (m : ℤ)
    (p : PrimeSpectrum (Polynomial k)) :
    X.ord ((affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X)^m) (j p) =
      if p=polynomialOrigin k then m else 0 := by
  have hX : affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective _ j)).mpr Polynomial.X_ne_zero
  rw [rationalOrder_zpow hX,affineLine_coordinate_order]
  split_ifs <;> simp

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineLine_coordinate_zpow_order
end Source_ToricPolynomialBoundary

section Source_ToricOrbitChartQuotient




/-!
# Actual closed orbit charts

A face of an additive semigroup gives a genuine quotient of its semigroup
algebra: characters outside the face map to zero, and characters on the face
remain their actual basis characters. The quotient map has an explicit right
inverse as a linear map (indeed an algebra map), so it induces an actual
closed immersion of affine schemes. Applied to a cone, the face consists
of characters vanishing on the specified cone rays.
-/


namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {M : Type*} [AddCommMonoid M]

/-- The intrinsic additive face condition. -/
def IsAdditiveFace (F : AddSubmonoid M) : Prop :=
  ∀ m p : M, m+p∈F → m∈F ∧ p∈F

theorem additiveFace_add_iff (F : AddSubmonoid M) (hF : IsAdditiveFace F)
    (m p : M) : m+p∈F ↔ m∈F ∧ p∈F :=
  ⟨hF m p,fun h => F.add_mem h.1 h.2⟩

variable (k : Type*) [CommRing k]

def additiveFaceCharacter (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    Multiplicative M →* AddMonoidAlgebra k F where
  toFun m := if hm : m.toAdd∈F then single ⟨m.toAdd,hm⟩ 1 else 0
  map_one' := by simp only [toAdd_one,dif_pos F.zero_mem]; rfl
  map_mul' m p := by
    change (if h : m.toAdd+p.toAdd∈F then single (⟨m.toAdd+p.toAdd,h⟩ : F) (1 : k) else 0) = _
    by_cases hm : m.toAdd∈F <;> by_cases hp : p.toAdd∈F
    · rw [dif_pos (F.add_mem hm hp),dif_pos hm,dif_pos hp,single_mul_single,one_mul]
      rfl
    · rw [dif_neg (fun h => hp (hF _ _ h).2),dif_pos hm,dif_neg hp,mul_zero]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_pos hp,zero_mul]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_neg hp,zero_mul]

/-- The literal quotient map on semigroup algebras. -/
def additiveFaceRetraction (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    AddMonoidAlgebra k M →ₐ[k] AddMonoidAlgebra k F :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k F) M (additiveFaceCharacter k F hF)

@[simp] theorem additiveFaceRetraction_single_of_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∈F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = single ⟨m,hm⟩ a := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm,smul_single]

@[simp] theorem additiveFaceRetraction_single_of_not_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∉F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = 0 := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm]

theorem additiveFaceRetraction_surjective (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) : Function.Surjective (additiveFaceRetraction k F hF) := by
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
      refine ⟨single m.val 1,?_⟩
      exact additiveFaceRetraction_single_of_mem k F hF m.val m.property 1
  | add f g hf hg =>
      obtain ⟨f',hf'⟩ := hf
      obtain ⟨g',hg'⟩ := hg
      exact ⟨f'+g',by rw [map_add,hf',hg']⟩
  | smul a f hf =>
      obtain ⟨f',hf'⟩ := hf
      exact ⟨a • f',by rw [map_smul,hf']⟩

/-- An actual closed immersion, obtained from a surjective ring map. -/
theorem additiveFace_isClosedImmersion (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (additiveFaceRetraction k F hF).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (additiveFaceRetraction_surjective k F hF)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ}

/-- The actual semigroup face cut out by vanishing on a subcone. It is
defined inside the original dual semigroup, so every other ray pairing
retains its nonnegativity condition. -/
def orbitCharacterFace (s t : Finset (Lattice n)) : AddSubmonoid (dualConeMonoid s) where
  carrier := {m | ∀ u∈t,integerPairing u m.val=0}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [show ((m+p : dualConeMonoid s) : Lattice n)=m.val+p.val from rfl,
      integerPairing_add,hm u hu,hp u hu,zero_add]

theorem orbitCharacterFace_isAdditiveFace (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsAdditiveFace (orbitCharacterFace s t) := by
  intro m p h
  constructor
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega

variable (k : Type*) [CommRing k]

/-- The orbit-closure chart as the spectrum of its actual semigroup face. -/
def orbitClosureChart (s t : Finset (Lattice n)) : Scheme :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (orbitCharacterFace s t)))

/-- Quotienting the actual chart ring by the characters positive on the
subcone. This is a morphism of actual affine schemes. -/
def orbitClosureChartMap (s t : Finset (Lattice n)) (hts : t⊆s) :
    orbitClosureChart k s t ⟶
      Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s))) :=
  Spec.map (CommRingCat.ofHom
    ((additiveFaceRetraction k (orbitCharacterFace s t)
      (orbitCharacterFace_isAdditiveFace s t hts)).comp
        (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom).toRingHom)

instance orbitClosureChartMap_isClosedImmersion (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsClosedImmersion (orbitClosureChartMap k s t hts) := by
  apply IsClosedImmersion.spec_of_surjective
  exact (additiveFaceRetraction_surjective k (orbitCharacterFace s t)
    (orbitCharacterFace_isAdditiveFace s t hts)).comp
      (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricCharacters.additiveFaceRetraction_surjective
#print axioms PaperVerification.ToricGeometry.orbitClosureChartMap_isClosedImmersion
end Source_ToricOrbitChartQuotient

section Source_ToricContractionCones

/-!
# Cone consequences of the actual contraction replacement condition

The hypotheses below are the explicit cone replacement condition in
Casagrande's theorem. In particular no geometric contraction, dimension
bound, or maximal-cone ray count is built into them.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A full-dimensional cone containing the negative focus of a contractible
primitive relation contains exactly `r` positive rays. This is the old-fan
part of Lemma 5.1(iii), with actual finite ray sets throughout. -/
theorem positive_count_in_full_cone (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    (R.positive ∩ s).card = R.fiberDimension := by
  let ν := s \ (R.positive ∪ R.negative)
  have hνs : ν ⊆ s := Finset.sdiff_subset
  have hνcone : ν ∈ «Σ».cones := «Σ».downward s hs ν hνs
  have hνdisjoint : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hrest
    exact (Finset.mem_sdiff.mp hv).2 hrest
  have hnegativeν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward s hs _ (Finset.union_subset hnegative hνs)
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have hexpanded := hR ν hνcone hνdisjoint hnegativeν x hx
  have hdim := «Σ».card_cone_le hexpanded
  have hposneg : Disjoint (R.positive.erase x) R.negative :=
    R.disjoint.mono_left (Finset.erase_subset x R.positive)
  have hcoreν : Disjoint (R.positive.erase x ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hv)
    · exact Finset.mem_union_right _ hv
  rw [Finset.card_union_of_disjoint hcoreν,
    Finset.card_union_of_disjoint hposneg,
    Finset.card_erase_of_mem hx] at hdim
  have hpartition : (R.positive ∩ s) ∪ R.negative ∪ ν = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).2
        · exact hnegative hv
      · exact hνs hv
    · intro hv
      by_cases hvP : v ∈ R.positive
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvP, hv⟩))
      · by_cases hvT : v ∈ R.negative
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvT)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, by
            simpa only [Finset.mem_union, not_or] using And.intro hvP hvT⟩)
  have hPT : Disjoint (R.positive ∩ s) R.negative :=
    R.disjoint.mono_left Finset.inter_subset_left
  have hPTν : Disjoint ((R.positive ∩ s) ∪ R.negative) ν := by
    apply Finset.disjoint_left.mpr
    intro v hv hvν
    apply (Finset.mem_sdiff.mp hvν).2
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).1
    · exact Finset.mem_union_right _ hv
  have hcounts : (R.positive ∩ s).card + R.negative.card + ν.card = n := by
    rw [← Finset.card_union_of_disjoint hPT,
      ← Finset.card_union_of_disjoint hPTν, hpartition, hcard]
  have hupper := R.positive_rays_in_cone_bound hs
  unfold fiberDimension at hupper ⊢
  omega

/-- There is a unique positive ray missing from every full cone over the
focus. The assertion is about the full ray set, not merely its cardinality. -/
theorem exists_unique_omitted_positive (hR : R.IsCombinatoriallyContractible)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hcard : s.card = n)
    (hnegative : R.negative ⊆ s) :
    ∃ x ∈ R.positive, R.positive \ s = {x} := by
  have hcount := R.positive_count_in_full_cone hR hs hcard hnegative
  have hsize := («Σ».primitiveCollection_card_bounds R.primitive).1
  have herase : (R.positive \ s).card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter R.positive s
    unfold fiberDimension at hcount
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
  refine ⟨x, ?_, hx⟩
  exact (Finset.mem_sdiff.mp (hx.symm ▸ Finset.mem_singleton_self x)).1

/-- The dimension of the negative focus is bounded by the complementary
fiber dimension, directly from the smooth cone supplied by replacement. -/
theorem focus_card_le_codimension (hR : R.IsCombinatoriallyContractible) :
    R.negative.card ≤ n - R.fiberDimension := by
  have h := R.contractible_dimension_bound hR
  omega

/-- A contraction with fiber dimension equal to the whole ambient dimension
has zero-dimensional focus; this is the numerical first step of the simplex
base case. No projective-space identification is claimed by this lemma. -/
theorem negative_eq_empty_of_fiberDimension_eq (hR : R.IsCombinatoriallyContractible)
    (hr : R.fiberDimension = n) : R.negative = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := R.contractible_dimension_bound hR
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end Source_ToricContractionCones

section Source_ToricPrimitiveOverlap




/-!
# Primitive collections meeting a contraction focus

The replacement condition forbids a different primitive collection from
containing the entire focus and also a positive ray of the contraction.
This is a finite-cone argument, independent of scheme contractions.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- Every cone over the focus can be filled with all positive rays except
one ray which it already omits. -/
theorem fill_cone_with_positive_except (hR : R.IsCombinatoriallyContractible)
    {C : Finset (Lattice n)} (hC : C ∈ «Σ».cones) (hNC : R.negative ⊆ C)
    {u : Lattice n} (hu : u ∈ R.positive) (huC : u ∉ C) :
    R.positive.erase u ∪ C ∈ «Σ».cones := by
  let ν := C \ (R.positive ∪ R.negative)
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν Finset.sdiff_subset
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC Finset.sdiff_subset)
  have hreplace := hR ν hν hdisj hNν u hu
  apply «Σ».downward _ hreplace _
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · by_cases hvP : v ∈ R.positive
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨fun he => huC (he ▸ hv), hvP⟩))
    · by_cases hvN : v ∈ R.negative
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hv, by simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

theorem positive_disjoint_of_focus_subset_primitive
    (hR : R.IsCombinatoriallyContractible)
    {Q : Finset (Lattice n)} (hQ : «Σ».IsPrimitiveCollection Q)
    (hNQ : R.negative ⊆ Q) (hneq : R.positive ≠ Q) :
    Disjoint R.positive Q := by
  have hnot : ¬ R.positive ⊆ Q := by
    intro hsubset
    exact R.primitive.2.1 (hQ.2.2 R.positive
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩))
  obtain ⟨u, hu, huQ⟩ := Finset.not_subset.mp hnot
  apply Finset.disjoint_left.mpr
  intro x hxP hxQ
  let C := Q.erase x
  have hC : C ∈ «Σ».cones := hQ.2.2 C (Finset.erase_ssubset hxQ)
  have hNC : R.negative ⊆ C := by
    intro v hv
    have hvx : v ≠ x := by
      intro he
      exact Finset.disjoint_left.mp R.disjoint hxP (he ▸ hv)
    exact Finset.mem_erase.mpr ⟨hvx, hNQ hv⟩
  let ν := C \ (R.positive ∪ R.negative)
  have hνC : ν ⊆ C := Finset.sdiff_subset
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν hνC
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC hνC)
  have hreplace := hR ν hν hdisj hNν u hu
  apply hQ.2.1
  apply «Σ».downward _ hreplace Q
  intro v hv
  by_cases hvP : v ∈ R.positive
  · have hvu : v ≠ u := fun he => huQ (he ▸ hv)
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvu, hvP⟩))
  · by_cases hvN : v ∈ R.negative
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
    · have hvx : v ≠ x := fun he => hvP (he.symm ▸ hxP)
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hvx, hv⟩, by
          simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end Source_ToricPrimitiveOverlap

section Source_ToricBundleFanCoordinates




/-!
# Saturated quotient coordinates for a smooth cone

Deleting coordinates of an integral basis gives the actual free quotient by
the lattice generated by a smooth cone.  All maps here are explicit linear
maps, with an integral section.  Changing the basis containing that cone
gives an integral equivalence of the resulting quotients.  This supplies the
lattice, rather than only real-vector-space, part of the bundle construction.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section Coordinates

variable {ι E R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [AddCommGroup E] [Module R E]

/-- The coordinates complementary to a specified basis subset. -/
abbrev ComplementaryIndex (I : Finset ι) := {i : ι // i ∉ I}

/-- Restriction of basis coordinates to the complementary indices. -/
def basisProjection (b : Module.Basis ι R E) (I : Finset ι) :
    E →ₗ[R] (ComplementaryIndex I → R) where
  toFun x j := b.repr x j
  map_add' x y := by ext j; simp
  map_smul' a x := by ext j; simp

def complementaryExtension (I : Finset ι) :
    (ComplementaryIndex I → R) →ₗ[R] (ι → R) where
  toFun x i := if hi : i ∈ I then 0 else x ⟨i, hi⟩
  map_add' x y := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi]
  map_smul' a x := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi]

/-- The section sets all deleted coordinates to zero. -/
def basisSection (b : Module.Basis ι R E) (I : Finset ι) :
    (ComplementaryIndex I → R) →ₗ[R] E :=
  b.equivFun.symm.toLinearMap.comp (complementaryExtension I)

@[simp] theorem basisProjection_apply (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) (j : ComplementaryIndex I) :
    basisProjection b I x j = b.repr x j := rfl

@[simp] theorem basisSection_repr (b : Module.Basis ι R E)
    (I : Finset ι) (x : ComplementaryIndex I → R) (i : ι) :
    b.repr (basisSection b I x) i = if hi : i ∈ I then 0 else x ⟨i, hi⟩ := by
  change b.equivFun (b.equivFun.symm (complementaryExtension I x)) i = _
  rw [b.equivFun.apply_symm_apply]
  rfl

@[simp] theorem basisProjection_section (b : Module.Basis ι R E)
    (I : Finset ι) (x : ComplementaryIndex I → R) :
    basisProjection b I (basisSection b I x) = x := by
  ext j
  simp only [basisProjection_apply, basisSection_repr, dif_neg j.property]

theorem basisProjection_surjective (b : Module.Basis ι R E) (I : Finset ι) :
    Function.Surjective (basisProjection b I) :=
  fun x => ⟨basisSection b I x, basisProjection_section b I x⟩

theorem basisProjection_basis_mem (b : Module.Basis ι R E) (I : Finset ι)
    {i : ι} (hi : i ∈ I) : basisProjection b I (b i) = 0 := by
  ext j
  have hij : i ≠ j := fun he => j.property (he ▸ hi)
  simp [Module.Basis.repr_self_apply, hij]

theorem basisProjection_basis_not_mem (b : Module.Basis ι R E)
    (I : Finset ι) (j : ComplementaryIndex I) :
    basisProjection b I (b j) = Pi.single j 1 := by
  ext k
  simp [Module.Basis.repr_self_apply, Finsupp.single_apply,
    Pi.single_apply, Subtype.ext_iff, eq_comm]

@[simp] theorem basisSection_single (b : Module.Basis ι R E)
    (I : Finset ι) (j : ComplementaryIndex I) :
    basisSection b I (Pi.single j 1) = b j := by
  apply b.equivFun.injective
  funext i
  rw [Module.Basis.equivFun_apply, basisSection_repr,
    Module.Basis.equivFun_apply, Module.Basis.repr_self_apply]
  by_cases hi : i ∈ I
  · have hji : (j : ι) ≠ i := fun he => j.property (he.symm ▸ hi)
    simp [hi, hji]
  · simp [hi, Pi.single_apply, Subtype.ext_iff, eq_comm]

/-- The omitted part is exactly a linear combination of the deleted basis
vectors; there is no finite-index discrepancy. -/
theorem basisSection_projection_decomposition (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) :
    basisSection b I (basisProjection b I x) +
      ∑ i ∈ I, b.repr x i • b i = x := by
  apply b.equivFun.injective
  funext i
  simp only [map_add, Module.Basis.equivFun_apply, basisSection_repr,
    Finsupp.add_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hi : i ∈ I <;> simp [Finsupp.single_apply, hi]

theorem basisProjection_eq_zero_iff (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) :
    basisProjection b I x = 0 ↔ ∀ i ∉ I, b.repr x i = 0 := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    ext j
    exact h j j.property

theorem map_basisSection_projection {F : Type*} [AddCommGroup F] [Module R F]
    (b : Module.Basis ι R E) (I : Finset ι) (q : E →ₗ[R] F)
    (hq : ∀ i ∈ I, q (b i) = 0) (x : E) :
    q (basisSection b I (basisProjection b I x)) = q x := by
  have h := congrArg q (basisSection_projection_decomposition b I x)
  simp only [map_add, map_sum, map_smul] at h
  have hz : (∑ i ∈ I, b.repr x i • q (b i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hq i hi, smul_zero]
  simpa only [hz, add_zero] using h

theorem basisProjection_of_mem_image (b : Module.Basis ι R E)
    (I : Finset ι) {v : E} (hv : v ∈ I.image b) :
    basisProjection b I v = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact basisProjection_basis_mem b I hi

/-- Changing the full basis containing the same deleted ray set changes
quotient coordinates by a unimodular transformation. -/
def basisQuotientTransition (b c : Module.Basis ι R E) (I J : Finset ι)
    (hIJ : I.image b = J.image c) :
    (ComplementaryIndex I → R) ≃ₗ[R] (ComplementaryIndex J → R) where
  toFun x := basisProjection c J (basisSection b I x)
  invFun y := basisProjection b I (basisSection c J y)
  left_inv x := by
    change basisProjection b I
      (basisSection c J (basisProjection c J (basisSection b I x))) = x
    rw [map_basisSection_projection c J (basisProjection b I) ?_]
    · exact basisProjection_section b I x
    · intro j hj
      apply basisProjection_of_mem_image b I
      rw [hIJ]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  right_inv y := by
    change basisProjection c J
      (basisSection b I (basisProjection b I (basisSection c J y))) = y
    rw [map_basisSection_projection b I (basisProjection c J) ?_]
    · exact basisProjection_section c J y
    · intro i hi
      apply basisProjection_of_mem_image c J
      rw [← hIJ]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  map_add' x y := by simp only [map_add]
  map_smul' a x := by simp only [map_smul, RingHom.id_apply]

theorem basisQuotientTransition_projection (b c : Module.Basis ι R E)
    (I J : Finset ι) (hIJ : I.image b = J.image c) (x : E) :
    basisQuotientTransition b c I J hIJ (basisProjection b I x) =
      basisProjection c J x := by
  apply map_basisSection_projection b I (basisProjection c J)
  intro i hi
  apply basisProjection_of_mem_image c J
  rw [← hIJ]
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- The projections of complementary vectors of any integral basis
containing the same cone form a basis of the free quotient lattice. -/
def descendedQuotientBasis (b c : Module.Basis ι R E) (I J : Finset ι)
    (hIJ : I.image b = J.image c) :
    Module.Basis (ComplementaryIndex J) R (ComplementaryIndex I → R) :=
  (Pi.basisFun R (ComplementaryIndex J)).map
    (basisQuotientTransition b c I J hIJ).symm

@[simp] theorem descendedQuotientBasis_apply (b c : Module.Basis ι R E)
    (I J : Finset ι) (hIJ : I.image b = J.image c) (j : ComplementaryIndex J) :
    descendedQuotientBasis b c I J hIJ j = basisProjection b I (c j) := by
  simp only [descendedQuotientBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    basisQuotientTransition]
  change basisProjection b I (basisSection c J (Pi.single j 1)) = _
  rw [basisSection_single]

end Coordinates

section IntegralCoordinates

variable {n : ℕ}

/-- The quotient index has exactly the codimension of the deleted cone. -/
theorem complementaryIndex_card (I : Finset (Fin n)) :
    Fintype.card (ComplementaryIndex I) = n - I.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

def quotientIndexEquivFin (I : Finset (Fin n)) :
    ComplementaryIndex I ≃ Fin (n - I.card) :=
  Fintype.equivFinOfCardEq (complementaryIndex_card I)

def quotientCoordinateFinEquiv (R : Type*) [CommRing R]
    (I : Finset (Fin n)) :
    (ComplementaryIndex I → R) ≃ₗ[R] (Fin (n - I.card) → R) where
  toFun x j := x ((quotientIndexEquivFin I).symm j)
  invFun y i := y (quotientIndexEquivFin I i)
  left_inv x := by ext i; simp
  right_inv y := by ext i; simp
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Explicit integral quotient map onto the standard coordinate lattice. -/
def coneQuotientLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice n →ₗ[ℤ] Lattice (n - I.card) :=
  (quotientCoordinateFinEquiv ℤ I).toLinearMap.comp (basisProjection b I)

/-- Its real extension uses the same integral basis coordinates. -/
def coneQuotientReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient n →ₗ[ℝ] Ambient (n - I.card) :=
  (quotientCoordinateFinEquiv ℝ I).toLinearMap.comp
    (basisProjection (integralBasisReal b) I)

def coneQuotientSectionLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice (n - I.card) →ₗ[ℤ] Lattice n :=
  (basisSection b I).comp (quotientCoordinateFinEquiv ℤ I).symm.toLinearMap

def coneQuotientSectionReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient (n - I.card) →ₗ[ℝ] Ambient n :=
  (basisSection (integralBasisReal b) I).comp
    (quotientCoordinateFinEquiv ℝ I).symm.toLinearMap

@[simp] theorem coneQuotient_section_lattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice (n - I.card)) :
    coneQuotientLattice b I (coneQuotientSectionLattice b I z) = z := by
  simp [coneQuotientLattice, coneQuotientSectionLattice, basisProjection_section]

@[simp] theorem coneQuotient_section_real (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient (n - I.card)) :
    coneQuotientReal b I (coneQuotientSectionReal b I x) = x := by
  simp [coneQuotientReal, coneQuotientSectionReal, basisProjection_section]

theorem coneQuotient_decomposition (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient n) :
    coneQuotientSectionReal b I (coneQuotientReal b I x) +
      ∑ i ∈ I, (integralBasisReal b).repr x i • integralBasisReal b i = x := by
  change basisSection (integralBasisReal b) I
      ((quotientCoordinateFinEquiv ℝ I).symm
        ((quotientCoordinateFinEquiv ℝ I)
          (basisProjection (integralBasisReal b) I x))) +
      ∑ i ∈ I, (integralBasisReal b).repr x i • integralBasisReal b i = x
  rw [LinearEquiv.symm_apply_apply]
  exact basisSection_projection_decomposition (integralBasisReal b) I x

@[simp] theorem coneQuotient_compatible (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice n) :
    coneQuotientReal b I (embed n z) =
      embed (n - I.card) (coneQuotientLattice b I z) := by
  funext j
  exact integralBasisReal_repr b z ((quotientIndexEquivFin I).symm j)

@[simp] theorem coneQuotientSection_compatible
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n - I.card)) :
    coneQuotientSectionReal b I (embed (n - I.card) z) =
      embed n (coneQuotientSectionLattice b I z) := by
  apply (integralBasisReal b).repr.injective
  ext i
  rw [integralBasisReal_repr]
  simp only [coneQuotientSectionReal, coneQuotientSectionLattice,
    LinearMap.comp_apply, basisSection_repr]
  by_cases hi : i ∈ I <;>
    simp [hi, quotientCoordinateFinEquiv, embed]

theorem coneQuotientLattice_of_mem (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {v : Lattice n} (hv : v ∈ I.image b) :
    coneQuotientLattice b I v = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  change quotientCoordinateFinEquiv ℤ I (basisProjection b I (b i)) = 0
  rw [basisProjection_basis_mem b I hi, map_zero]

theorem coneQuotientReal_of_mem (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {v : Lattice n} (hv : v ∈ I.image b) :
    coneQuotientReal b I (embed n v) = 0 := by
  rw [coneQuotient_compatible, coneQuotientLattice_of_mem b I hv, map_zero]

/-- The deleted lattice is saturated: a real zero quotient of an integer
vector is already zero in the integral quotient. -/
theorem coneQuotient_zero_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice n) :
    coneQuotientReal b I (embed n z) = 0 ↔ coneQuotientLattice b I z = 0 := by
  rw [coneQuotient_compatible]
  constructor
  · intro h
    apply embed_injective (n - I.card)
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

end IntegralCoordinates

end PaperVerification.ToricGeometry
end Source_ToricBundleFanCoordinates

section Source_ToricBundleFanQuotient




/-!
# Actual cones in a saturated quotient

The fan intersection property descends through a smooth cone.  The proof
lifts two equal quotient vectors and adds nonnegative combinations of the
common cone rays to make the lifts equal.  Smoothness descends through the
explicit integral quotient basis from `ToricBundleFanCoordinates`.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem finiteRayCone_image_linear {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (s : Finset E) (f : E →ₗ[ℝ] F) :
    finiteRayCone (s.image f) = (finiteRayCone s).map f := by
  rw [finiteRayCone_eq_hull, finiteRayCone_eq_hull]
  change Submodule.span (Nonneg ℝ) ((s.image f : Finset F) : Set F) =
    Submodule.map (f : E →ₗ[Nonneg ℝ] F) (Submodule.span (Nonneg ℝ) (s : Set E))
  rw [Finset.coe_image]
  exact Submodule.span_image (f : E →ₗ[Nonneg ℝ] F)

variable {n : ℕ}

theorem latticeRayCone_image_quotient
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone (s.image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  unfold latticeRayCone
  rw [← finiteRayCone_image_linear]
  congr 1
  simp only [Finset.image_image]
  ext x
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, coneQuotient_compatible b I v⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (coneQuotient_compatible b I v).symm⟩

theorem coneQuotient_zero_on_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x : Ambient n} (hx : x ∈ latticeRayCone (I.image b)) :
    coneQuotientReal b I x = 0 := by
  have hcoord := (mem_latticeRayCone_basis_iff b I x).mp hx
  change quotientCoordinateFinEquiv ℝ I
    (basisProjection (integralBasisReal b) I x) = 0
  rw [(basisProjection_eq_zero_iff (integralBasisReal b) I x).mpr hcoord.2, map_zero]

/-- Two lifts of one quotient vector become identical after adding vectors
in the same actual cone on the deleted basis rays. -/
theorem coneQuotient_common_lift
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x y : Ambient n} (hxy : coneQuotientReal b I x = coneQuotientReal b I y) :
    ∃ a ∈ latticeRayCone (I.image b), ∃ c ∈ latticeRayCone (I.image b),
      x + a = y + c := by
  let β := integralBasisReal b
  let d : Fin n → ℝ := fun i => β.repr (y - x) i
  have hproj : basisProjection β I (y - x) = 0 := by
    apply (quotientCoordinateFinEquiv ℝ I).injective
    change coneQuotientReal b I (y - x) = quotientCoordinateFinEquiv ℝ I 0
    rw [map_sub, hxy, sub_self, map_zero]
  have hsum : (∑ i ∈ I, d i • β i) = y - x := by
    have h := basisSection_projection_decomposition β I (y - x)
    rw [hproj, map_zero, zero_add] at h
    exact h
  let a := ∑ i ∈ I, max (d i) 0 • β i
  let c := ∑ i ∈ I, (max (d i) 0 - d i) • β i
  have ha : a ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (le_max_right _ _) (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hc : c ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (sub_nonneg.mpr (le_max_left _ _))
      (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hac : a - c = y - x := by
    change (∑ i ∈ I, max (d i) 0 • β i) -
      (∑ i ∈ I, (max (d i) 0 - d i) • β i) = _
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul, sub_sub_cancel]
    exact hsum
  refine ⟨a, ha, c, hc, ?_⟩
  calc
    x + a = x + (a - c) + c := by abel
    _ = x + (y - x) + c := by rw [hac]
    _ = y + c := by abel

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Projecting genuine cones containing a common smooth cone preserves
their genuine geometric intersections. -/
theorem coneQuotient_intersection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t) :
    (latticeRayCone s).map (coneQuotientReal b I) ⊓
      (latticeRayCone t).map (coneQuotientReal b I) =
        (latticeRayCone (s ∩ t)).map (coneQuotientReal b I) := by
  apply le_antisymm
  · rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    obtain ⟨a, ha, c, hc, he⟩ := coneQuotient_common_lift b I (hxz.trans hyz.symm)
    have has : a ∈ latticeRayCone s := latticeRayCone_mono hIs ha
    have hct : c ∈ latticeRayCone t := latticeRayCone_mono hIt hc
    have hboth : x + a ∈ latticeRayCone (s ∩ t) := by
      rw [← «Σ».intersection s hs t ht]
      refine ⟨Submodule.add_mem _ hx has, ?_⟩
      rw [he]
      exact Submodule.add_mem _ hy hct
    refine ⟨x + a, hboth, ?_⟩
    change coneQuotientReal b I x = z at hxz
    change coneQuotientReal b I (x + a) = z
    rw [map_add, coneQuotient_zero_on_cone b I ha, add_zero, hxz]
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, latticeRayCone_mono Finset.inter_subset_left hx, rfl⟩,
      ⟨x, latticeRayCone_mono Finset.inter_subset_right hx, rfl⟩⟩

end SmoothCompleteFan

/-- Removing the rays killed by the quotient does not change the image cone. -/
theorem latticeRayCone_quotient_sdiff
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone ((s \ I.image b).image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  rw [← latticeRayCone_image_quotient]
  apply le_antisymm
  · exact latticeRayCone_mono (Finset.image_subset_image Finset.sdiff_subset)
  · rw [latticeRayCone, finiteRayCone_eq_hull]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    by_cases hwI : w ∈ I.image b
    · rw [coneQuotientLattice_of_mem b I hwI, map_zero]
      exact Submodule.zero_mem _
    · exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwI⟩, rfl⟩)

theorem basis_image_card_eq {b c : Module.Basis (Fin n) ℤ (Lattice n)}
    {I J : Finset (Fin n)} (hIJ : I.image b = J.image c) : I.card = J.card := by
  have h := congrArg Finset.card hIJ
  simpa only [Finset.card_image_of_injective _ b.injective,
    Finset.card_image_of_injective _ c.injective] using h

/-- A full integral basis of the quotient, constructed from any full basis
containing the deleted rays. -/
def coneQuotientBasis (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c) :
    Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)) :=
  ((descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ)).map
    (quotientCoordinateFinEquiv ℤ I)).reindex
    (Fintype.equivFinOfCardEq (by
      rw [complementaryIndex_card, basis_image_card_eq hIJ]))

theorem coneQuotientBasis_range (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c)
    (j : ComplementaryIndex J) :
    coneQuotientLattice b I (c j) ∈
      (Finset.univ : Finset (Fin (n - I.card))).image (coneQuotientBasis b c I J hIJ) := by
  let e : ComplementaryIndex J ≃ Fin (n - I.card) :=
    Fintype.equivFinOfCardEq (by rw [complementaryIndex_card, basis_image_card_eq hIJ])
  refine Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, ?_⟩
  simp only [coneQuotientBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  change quotientCoordinateFinEquiv ℤ I
    (descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ) (e.symm (e j))) = _
  rw [e.symm_apply_apply, descendedQuotientBasis_apply]
  rfl

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Smoothness survives in the saturated quotient, with an actual integral
basis of the target lattice. -/
theorem coneQuotient_smooth
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s) :
    ∃ (β : Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)))
      (K : Finset (Fin (n - I.card))),
      (s \ I.image b).image (coneQuotientLattice b I) = K.image β := by
  obtain ⟨c, L, hL⟩ := «Σ».smooth s hs
  let J := basisRayIndices c (I.image b)
  have hJ : J.image c = I.image b := image_basisRayIndices c _ (by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hIs hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let β := coneQuotientBasis b c I J hJ.symm
  let T := (s \ I.image b).image (coneQuotientLattice b I)
  have hT : T ⊆ Finset.univ.image β := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwS, hwF⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hwS)
    have hiJ : i ∉ J := by
      intro hij
      exact hwF (hJ ▸ Finset.mem_image.mpr ⟨i, hij, rfl⟩)
    exact coneQuotientBasis_range b c I J hJ.symm ⟨i, hiJ⟩
  exact ⟨β, basisRayIndices β T, (image_basisRayIndices β T hT).symm⟩

theorem coneQuotient_nonzero_ray
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) : coneQuotientLattice b I v ≠ 0 := by
  obtain ⟨β, K, hK⟩ := «Σ».coneQuotient_smooth b I hs hIs
  have hmem : coneQuotientLattice b I v ∈ K.image β :=
    hK ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hmem
  rw [← he]
  exact β.ne_zero j

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricBundleFanQuotient

section Source_ToricBundleFanStar




/-!
# The fan of projected cones over a smooth cone

The only input to completeness in this construction is the literal covering
of quotient vectors by projected cones.  Smoothness, finiteness, intersections,
faces, purity, and uniqueness of ray lifts are proved from the original fan.
The empty-focus bundle case proves this covering in `ToricBundleFan`.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem coneQuotient_injective_star_rays
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t)
    {v w : Lattice n} (hv : v ∈ s \ I.image b) (hw : w ∈ t \ I.image b)
    (he : coneQuotientLattice b I v = coneQuotientLattice b I w) : v = w := by
  by_contra hvw
  let F := I.image b
  let S := insert v F
  let T := insert w F
  have hS : S ∈ «Σ».cones := «Σ».downward s hs S (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hv).1
    · exact hIs ha)
  have hT : T ∈ «Σ».cones := «Σ».downward t ht T (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hw).1
    · exact hIt ha)
  have hST : S ∩ T = F := by
    ext a
    constructor
    · intro ha
      obtain ⟨haS, haT⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haS with rfl | haF
      · rcases Finset.mem_insert.mp haT with heq | haF
        · exact (hvw heq).elim
        · exact haF
      · exact haF
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem ha⟩
  have hm : embed (n - I.card) (coneQuotientLattice b I v) ∈
      (latticeRayCone S).map (coneQuotientReal b I) ⊓
        (latticeRayCone T).map (coneQuotientReal b I) := by
    refine ⟨⟨embed n v, latticeRayCone_generator S (Finset.mem_insert_self v F),
      coneQuotient_compatible b I v⟩, ?_⟩
    refine ⟨embed n w, latticeRayCone_generator T (Finset.mem_insert_self w F), ?_⟩
    change coneQuotientReal b I (embed n w) =
      embed (n - I.card) (coneQuotientLattice b I v)
    rw [coneQuotient_compatible, he]
  rw [«Σ».coneQuotient_intersection b I hS hT
    (Finset.subset_insert v F) (Finset.subset_insert w F), hST] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  change coneQuotientReal b I x =
    embed (n - I.card) (coneQuotientLattice b I v) at hxe
  have hz : coneQuotientLattice b I v = 0 := by
    apply embed_injective (n - I.card)
    rw [← hxe, coneQuotient_zero_on_cone b I hx, map_zero]
  exact «Σ».coneQuotient_nonzero_ray b I hs hIs hv hz

/-- Literal finite family of all quotient cones over the deleted cone. -/
def quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Finset (Finset (Lattice (n - I.card))) :=
  («Σ».cones.filter (fun s => I.image b ⊆ s)).image
    (fun s => (s \ I.image b).image (coneQuotientLattice b I))

theorem mem_quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (t : Finset (Lattice (n - I.card))) :
    t ∈ «Σ».quotientStarCones b I ↔
      ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
        t = (s \ I.image b).image (coneQuotientLattice b I) := by
  simp only [quotientStarCones, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hIs⟩, he⟩
    exact ⟨s, hs, hIs, he.symm⟩
  · rintro ⟨s, hs, hIs, he⟩
    exact ⟨s, ⟨hs, hIs⟩, he.symm⟩

theorem quotientStarCones_downward (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (hts : t ⊆ s) :
    t ∈ «Σ».quotientStarCones b I := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  let D := S.filter (fun v => v ∉ I.image b ∧ coneQuotientLattice b I v ∈ t)
  have hD : I.image b ∪ D ⊆ S := Finset.union_subset hIS (Finset.filter_subset _ _)
  refine («Σ».mem_quotientStarCones b I t).mpr
    ⟨I.image b ∪ D, «Σ».downward S hS _ hD, Finset.subset_union_left, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hts hv)
    obtain ⟨hwS, hwI⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_image.mpr ⟨w,
      Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hwS, hwI, hv⟩), hwI⟩, rfl⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwU, hwI⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp hwU with hwF | hwD
    · exact (hwI hwF).elim
    · exact (Finset.mem_filter.mp hwD).2.2

theorem quotientStarCones_intersection (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (ht : t ∈ «Σ».quotientStarCones b I) :
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t) := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hIT, rfl⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  apply le_antisymm
  · rw [latticeRayCone_quotient_sdiff, latticeRayCone_quotient_sdiff,
      «Σ».coneQuotient_intersection b I hS hT hIS hIT,
      ← latticeRayCone_quotient_sdiff]
    apply latticeRayCone_mono
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwST, hwI⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwS, hwT⟩ := Finset.mem_inter.mp hwST
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwS, hwI⟩, rfl⟩,
        Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwT, hwI⟩, rfl⟩⟩
  · exact le_inf (latticeRayCone_mono Finset.inter_subset_left)
      (latticeRayCone_mono Finset.inter_subset_right)

/-- The actual smooth complete fan in the saturated quotient.  Its covering
input is an ordinary statement about real images of actual cones. -/
def quotientStarFan (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    SmoothCompleteFan (n - I.card) where
  cones := «Σ».quotientStarCones b I
  smooth := by
    intro s hs
    obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
    exact «Σ».coneQuotient_smooth b I hS hIS
  downward := by
    intro s hs t hts
    exact «Σ».quotientStarCones_downward b I hs hts
  intersection := by
    intro s hs t ht
    exact «Σ».quotientStarCones_intersection b I hs ht
  complete := by
    intro y
    obtain ⟨S, hS, hIS, hy⟩ := hcover y
    refine ⟨(S \ I.image b).image (coneQuotientLattice b I),
      («Σ».mem_quotientStarCones b I _).mpr ⟨S, hS, hIS, rfl⟩, ?_⟩
    rw [latticeRayCone_quotient_sdiff]
    exact hy

theorem quotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    («Σ».quotientStarFan b I hcover).IsPure := by
  intro s hs
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hST, hcard⟩ := hpure S hS
  have hIT : I.image b ⊆ T := hIS.trans hST
  refine ⟨(T \ I.image b).image (coneQuotientLattice b I),
    («Σ».mem_quotientStarCones b I _).mpr ⟨T, hT, hIT, rfl⟩, ?_, ?_⟩
  · exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hST)
  · rw [Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hIT,
      Finset.card_image_of_injective I b.injective, hcard]
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hT hT hIT hIT hv hw he

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricBundleFanStar

section Source_ToricQuotientStarCovering




/-!
# Completeness of the actual quotient star

The sum of the deleted cone's primitive rays lies in no cone which fails
to contain that cone. A finite union of closed basis cones stays away from
that point. Small perturbations in any quotient direction therefore lie
in cones containing the deleted cone, and projection followed by positive
rescaling proves completeness in the saturated quotient.
-/


namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

theorem isClosed_finiteRayCone_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (I : Finset (Fin n)) :
    IsClosed (finiteRayCone (I.image b) : Set (Ambient n)) := by
  have he : (finiteRayCone (I.image b) : Set (Ambient n)) =
      (⋂ i, {x : Ambient n | 0 ≤ b.coord i x}) ∩
      (⋂ i, ⋂ (_ : i ∉ I), {x : Ambient n | b.coord i x = 0}) := by
    have hI : I.image b =
        @Finset.image (Fin n) (Ambient n)
          (fun (x y : Ambient n) => Classical.propDecidable (x = y)) b I := by
      ext y
      simp only [Finset.mem_image]
    ext x
    change (x ∈ finiteRayCone (I.image b)) ↔ _
    rw [hI]
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Module.Basis.coord_apply] using (mem_finiteRayCone_basis_iff b I x)
  rw [he]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (b.coord i).continuous_of_finiteDimensional
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro hi
    exact isClosed_eq (b.coord i).continuous_of_finiteDimensional continuous_const

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem isClosed_latticeRayCone {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    IsClosed (latticeRayCone s : Set (Ambient n)) := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [latticeRayCone_basis]
  exact isClosed_finiteRayCone_basis (integralBasisReal b) I

/-- Every real direction admits a positive small perturbation of the ray
sum inside an actual cone containing the original cone. -/
theorem exists_small_perturbation_in_containing_cone
    {F : Finset (Lattice n)} (hF : F ∈ «Σ».cones) (x : Ambient n) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s ∈ «Σ».cones, F ⊆ s ∧
      (∑ u ∈ F, embed n u) + ε • x ∈ latticeRayCone s := by
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    exact (Finset.mem_filter.mp hs).2
      («Σ».sum_mem_cone_implies_subset hF (Finset.mem_filter.mp hs).1 hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • x
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • x ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  exact ⟨ε, hε, s, hs, hFs, hφs⟩

/-- The literal projected-cover statement required by `quotientStarFan`,
proved for every actual smooth cone, including the empty cone. -/
theorem coneQuotient_projected_cover
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) :
    ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I) := by
  intro y
  let F := I.image b
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    have hscone := (Finset.mem_filter.mp hs).1
    have hnsub := (Finset.mem_filter.mp hs).2
    exact hnsub («Σ».sum_mem_cone_implies_subset hF hscone hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • coneQuotientSectionReal b I y
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • coneQuotientSectionReal b I y ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  have hwcone : w ∈ latticeRayCone (I.image b) := by
    apply Submodule.sum_mem
    intro u hu
    exact latticeRayCone_generator _ hu
  have hproj : coneQuotientReal b I (φ ε) = ε • y := by
    change coneQuotientReal b I (w + ε • coneQuotientSectionReal b I y) = ε • y
    rw [map_add, coneQuotient_zero_on_cone b I hwcone,
      map_smul, coneQuotient_section_real, zero_add]
  have hmem : ε • y ∈ (latticeRayCone s).map (coneQuotientReal b I) :=
    ⟨φ ε, hφs, hproj⟩
  have hscaled := PointedCone.smul_mem
    ((latticeRayCone s).map (coneQuotientReal b I)) (inv_nonneg.mpr hε.le) hmem
  refine ⟨s, hs, hFs, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] using hscaled

/-- The actual saturated quotient star of any cone of a smooth complete
fan is a smooth complete fan, with no completeness premise left over. -/
def completeQuotientStarFan
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : SmoothCompleteFan (n - I.card) :=
  «Σ».quotientStarFan b I («Σ».coneQuotient_projected_cover b I hF)

theorem completeQuotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : («Σ».completeQuotientStarFan b I hF).IsPure :=
  «Σ».quotientStarFan_isPure hpure b I («Σ».coneQuotient_projected_cover b I hF)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricQuotientStarCovering

section Source_ToricFanFaceHulls




/-!
# Exact nef face hulls over an actual fan cone

Even when nef support collapses some edges, the face cut out by a cone is
the convex hull of Cartier points of full cones containing it. Small
perturbations of the cone's interior normal prove the minimizing property,
so no assumption that the nef polytope retains the original normal fan is
needed.
-/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ u ∈ F,
    (dotProductEquiv ℝ (Fin n) (embed n u)) x = -a u}

def fullConesOver (F : Finset (Lattice n)) : Finset «Σ».fullCones :=
  Finset.univ.filter (fun s => F ⊆ (s : Finset (Lattice n)))

theorem cartierPoint_support_eq (a : Lattice n → ℝ) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ (s : Finset (Lattice n))) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) = -a u := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hu)
  exact «Σ».cartierPoint_active a s i

theorem convex_supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) :
    Convex ℝ («Σ».supportFace a F) := by
  intro x hx y hy r t hr ht hrt
  refine ⟨«Σ».convex_fanPolytope a hx.1 hy.1 hr ht hrt, ?_⟩
  intro u hu
  rw [map_add, map_smul, map_smul, hx.2 u hu, hy.2 u hu]
  change r * -a u + t * -a u = -a u
  rw [← add_mul, hrt, one_mul]

/-- Equality in genuine supporting primitive halfspaces cuts out an
actual extreme face of the original halfspace polytope. -/
theorem supportFace_isExtreme (a : Lattice n → ℝ)
    (F : Finset (Lattice n)) (hF : F ⊆ «Σ».rays) :
    IsExtreme ℝ («Σ».fanPolytope a) («Σ».supportFace a F) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, t, hr, ht, hrt, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro u hu
  have hxu := hx u (hF hu)
  have hyu := hy u (hF hu)
  have hzu := hz.2 u hu
  have hlin := congrArg (dotProductEquiv ℝ (Fin n) (embed n u) : Ambient n → ℝ) he
  simp only [map_add, map_smul, smul_eq_mul] at hlin
  have hxnon := mul_nonneg hr.le (sub_nonneg.mpr hxu)
  have hynon := mul_nonneg ht.le (sub_nonneg.mpr hyu)
  have htotal :
      r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y + a u) = 0 := by
    calc
      _ = (r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y)) + (r + t) * a u := by ring
      _ = 0 := by rw [hlin, hzu, hrt]; ring
  have hzero : r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) = 0 := by
    nlinarith only [hxnon, hynon, htotal]
  have hz := (mul_eq_zero.mp hzero).resolve_left hr.ne'
  linarith

theorem cartierPoint_mem_supportFace {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (s : «Σ».fullConesOver F) :
    «Σ».cartierPoint a s ∈ «Σ».supportFace a F := by
  refine ⟨«Σ».cartierPoint_mem_of_nef ha s, ?_⟩
  intro u hu
  exact «Σ».cartierPoint_support_eq a s ((Finset.mem_filter.mp s.property).2 hu)

/-- A normal in a full fan cone is minimized at that cone's actual
Cartier point on the whole nef polytope. -/
theorem cartierPoint_minimizes_normal (a : Lattice n → ℝ) (s : «Σ».fullCones)
    (u : Ambient n) (hu : u ∈ latticeRayCone (s : Finset (Lattice n)))
    (x : Ambient n) (hx : x ∈ «Σ».fanPolytope a) :
    (dotProductEquiv ℝ (Fin n) u) («Σ».cartierPoint a s) ≤
      (dotProductEquiv ℝ (Fin n) u) x := by
  let d := «Σ».fullConeBasis s
  let B := «Σ».cartierBasis s
  rw [«Σ».fullConeBasis_ray_set s] at hu
  have hcoords := ((mem_latticeRayCone_basis_iff d Finset.univ u).mp hu).1
  apply linear_le_of_basis_coordinates B (dotProductEquiv ℝ (Fin n) u)
    («Σ».cartierPoint a s) x
  · intro i
    have hp := integralDualBasis_real_repr (integralDualBasis d) u i
    rw [integralDualBasis_involutive] at hp
    have hi := hcoords i
    rw [hp] at hi
    exact hi
  · intro i
    rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
    exact sub_nonneg.mpr (hx («Σ».activeRay s i) («Σ».activeRay s i).property)

/-- Equation (1) restricted to the face indexed by any actual cone. This
also applies at nef endpoints and to lower-dimensional restriction polytopes. -/
theorem supportFace_eq_convexHull_cartier (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (hF : F ∈ «Σ».cones) :
    «Σ».supportFace a F = convexHull ℝ
      (Set.range (fun s : «Σ».fullConesOver F => «Σ».cartierPoint a s)) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support
    intro f
    obtain ⟨ε, hε, t, ht, hFt, hut⟩ :=
      «Σ».exists_small_perturbation_in_containing_cone hF (dualVector f)
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    let s'' : «Σ».fullConesOver F :=
      ⟨s', Finset.mem_filter.mpr ⟨Finset.mem_univ s', hFt.trans hts⟩⟩
    let w : Ambient n := ∑ u ∈ F, embed n u
    have hnormal : w + ε • dualVector f ∈ latticeRayCone s :=
      latticeRayCone_mono hts hut
    have hmin := «Σ».cartierPoint_minimizes_normal a s' (w + ε • dualVector f)
      hnormal x hx.1
    have hcface := «Σ».cartierPoint_mem_supportFace ha F s''
    let q : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) w
    have hwvalue (y : Ambient n) (hy : y ∈ «Σ».supportFace a F) :
        q y = -∑ u ∈ F, a u := by
      change (dotProductEquiv ℝ (Fin n) (∑ u ∈ F, embed n u)) y = _
      calc
        _ = ∑ u ∈ F, (dotProductEquiv ℝ (Fin n) (embed n u)) y := by
          rw [map_sum, LinearMap.sum_apply]
        _ = ∑ u ∈ F, -a u := Finset.sum_congr rfl (fun u hu => hy.2 u hu)
        _ = _ := Finset.sum_neg_distrib a
    have hpair (y : Ambient n) :
        (dotProductEquiv ℝ (Fin n) (w + ε • dualVector f)) y = q y + ε * f y := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      have hf : (dotProductEquiv ℝ (Fin n) (dualVector f)) y = f y := by
        change (∑ i, dualVector f i * y i) = f y
        simpa only [Pi.zero_apply, sub_zero] using
          dualVector_pairing f (0 : Ambient n) y
      rw [hf]
      rfl
    rw [hpair, hpair, hwvalue x hx, hwvalue _ hcface] at hmin
    refine ⟨s'', ?_⟩
    nlinarith
  · exact convexHull_min
      (by rintro _ ⟨s, rfl⟩; exact «Σ».cartierPoint_mem_supportFace ha F s)
      («Σ».convex_supportFace a F)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end Source_ToricFanFaceHulls

section Source_ToricIntegralAffine

/-!
# Saturated integral affine coordinate embeddings

These data encode an ordinary injective integral affine map whose linear image
is saturated in the ambient lattice. The saturation clause is about all actual
lattice vectors in that real subspace; no decomposition property is assumed.
-/


namespace PaperVerification.ToricGeometry

open PaperVerification.ToricExchange

/-- An integral affine coordinate embedding with exactly the induced lattice
on its real image. -/
structure IntegralAffineEmbedding (d n : ℕ) where
  origin : Lattice n
  linear : Lattice d →+ Lattice n
  realLinear : Ambient d →ₗ[ℝ] Ambient n
  injective : Function.Injective realLinear
  compatible : ∀ z, embed n (linear z) = realLinear (embed d z)
  saturated : ∀ z : Lattice n, embed n z ∈ Set.range realLinear → ∃ w, linear w = z

/-- Coordinate content of an integer vector, equal to its lattice segment length. -/
def latticeContent {n : ℕ} (z : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i => (z i).natAbs)

/-- Coordinate gcd divisibility is exactly divisibility of the whole lattice vector. -/
theorem dvd_latticeContent_iff {n : ℕ} (k : ℕ) (z : Lattice n) :
    k ∣ latticeContent z ↔ ∃ w : Lattice n, z = (k : ℤ) • w := by
  classical
  constructor
  · intro hk
    have hd (i : Fin n) : (k : ℤ) ∣ z i :=
      Int.natCast_dvd.mpr (hk.trans (Finset.gcd_dvd (Finset.mem_univ i)))
    choose w hw using hd
    exact ⟨w, by funext i; exact hw i⟩
  · rintro ⟨w, rfl⟩
    apply Finset.dvd_gcd
    intro i hi
    apply Int.natCast_dvd.mp
    exact ⟨w i, rfl⟩

/-- Injective affine maps preserve ordinary extreme subsets. -/
theorem affine_isExtreme_image {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P F : Set V} (hF : IsExtreme ℝ P F) :
    IsExtreme ℝ (f '' P) (f '' F) := by
  refine ⟨Set.image_mono hF.subset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f x y] at hseg
  obtain ⟨w, hw, he⟩ := hseg
  have hwz := hf he
  subst w
  exact ⟨x, hF.left_mem_of_mem_openSegment hx hy hz hw, rfl⟩

/-- Extremeness of an affine image is equivalent to extremeness in the source. -/
theorem affine_isExtreme_image_iff {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P F : Set V) :
    IsExtreme ℝ (f '' P) (f '' F) ↔ IsExtreme ℝ P F := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, he⟩ := hF.subset ⟨x, hx, rfl⟩
      have hyx := hf he
      simpa only [hyx] using hy
    · intro x hx y hy z hz hseg
      have hseg' : f z ∈ openSegment ℝ (f x) (f y) := by
        rw [← image_openSegment ℝ f x y]
        exact ⟨z, hseg, rfl⟩
      obtain ⟨w, hw, he⟩ := hF.left_mem_of_mem_openSegment
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hseg'
      have hwx := hf he
      simpa only [hwx] using hw
  · exact affine_isExtreme_image f hf

namespace IntegralAffineEmbedding

variable {d n : ℕ} (e : IntegralAffineEmbedding d n)

theorem linear_injective : Function.Injective e.linear := by
  intro x y h
  apply embed_injective d
  apply e.injective
  simpa only [e.compatible] using congrArg (embed n) h

/-- Saturation preserves divisibility of lattice vectors by every natural
number, including zero. -/
theorem linear_exists_smul_iff (k : ℕ) (z : Lattice d) :
    (∃ w : Lattice n, e.linear z = (k : ℤ) • w) ↔
      ∃ w : Lattice d, z = (k : ℤ) • w := by
  constructor
  · rintro ⟨w, hw⟩
    by_cases hk : k = 0
    · subst k
      refine ⟨0, ?_⟩
      apply e.linear_injective
      simpa using hw
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have he : e.realLinear (embed d z) = (k : ℝ) • embed n w := by
        rw [← e.compatible, hw, embed_int_smul, Int.cast_natCast]
      have hwrange : embed n w ∈ Set.range e.realLinear := by
        refine ⟨(k : ℝ)⁻¹ • embed d z, ?_⟩
        rw [map_smul, he, smul_smul, inv_mul_cancel₀ hkR, one_smul]
      obtain ⟨v, hv⟩ := e.saturated w hwrange
      refine ⟨v, ?_⟩
      apply e.linear_injective
      rw [map_zsmul, hv]
      exact hw
  · rintro ⟨w, rfl⟩
    exact ⟨e.linear w, map_zsmul e.linear _ _⟩

/-- Saturated integral embeddings preserve the exact coordinate gcd. -/
theorem latticeContent_linear (z : Lattice d) :
    latticeContent (e.linear z) = latticeContent z := by
  apply Nat.dvd_antisymm
  · apply (dvd_latticeContent_iff _ z).mpr
    apply (e.linear_exists_smul_iff _ z).mp
    exact (dvd_latticeContent_iff _ (e.linear z)).mp dvd_rfl
  · apply (dvd_latticeContent_iff _ (e.linear z)).mpr
    apply (e.linear_exists_smul_iff _ z).mpr
    exact (dvd_latticeContent_iff _ z).mp dvd_rfl

/-- The actual real affine map, including its integral translation. -/
def realMap : Ambient d →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ (Ambient d) (embed n e.origin) + e.realLinear.toAffineMap

/-- The corresponding map on actual integer coordinates. -/
def latticeMap (z : Lattice d) : Lattice n := e.origin + e.linear z

@[simp] theorem realMap_apply (x : Ambient d) :
    e.realMap x = embed n e.origin + e.realLinear x := rfl

@[simp] theorem embed_latticeMap (z : Lattice d) :
    embed n (e.latticeMap z) = e.realMap (embed d z) := by
  simp [latticeMap, realMap_apply, e.compatible]

theorem realMap_injective : Function.Injective e.realMap := by
  intro x y h
  apply e.injective
  exact add_left_cancel h

theorem latticeMap_injective : Function.Injective e.latticeMap := by
  intro x y h
  apply embed_injective d
  apply e.realMap_injective
  simpa only [embed_latticeMap] using congrArg (embed n) h

/-- The usual lattice length is unchanged by a saturated integral affine chart. -/
theorem latticeLength_latticeMap (x y : Lattice d) :
    LatticePolytope.latticeLength (e.latticeMap x) (e.latticeMap y) =
      LatticePolytope.latticeLength x y := by
  change latticeContent (e.latticeMap y - e.latticeMap x) = latticeContent (y - x)
  have he : e.latticeMap y - e.latticeMap x = e.linear (y - x) := by
    simp only [latticeMap, map_sub]
    abel
  rw [he, e.latticeContent_linear]

/-- Every ambient lattice point in the affine image has unique integral
coordinates. Thus the coordinate lattice is the saturated face lattice. -/
theorem exists_latticeMap_of_mem_range (z : Lattice n)
    (hz : embed n z ∈ Set.range e.realMap) :
    ∃ w : Lattice d, e.latticeMap w = z := by
  obtain ⟨x, hx⟩ := hz
  have hrange : embed n (z - e.origin) ∈ Set.range e.realLinear := by
    refine ⟨x, ?_⟩
    rw [map_sub, ← hx, realMap_apply, add_sub_cancel_left]
  obtain ⟨w, hw⟩ := e.saturated (z - e.origin) hrange
  refine ⟨w, ?_⟩
  simp only [latticeMap, hw]
  abel

/-- Lattice-point membership in an affine image is exactly membership of the
unique integral preimage. -/
theorem lattice_image_membership (P : Set (Ambient d)) (z : Lattice n) :
    embed n z ∈ e.realMap '' P ↔
      ∃ w : Lattice d, embed d w ∈ P ∧ e.latticeMap w = z := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨w, hw⟩ := e.exists_latticeMap_of_mem_range z ⟨x, he⟩
    refine ⟨w, ?_, hw⟩
    have hcoord : embed d w = x := by
      apply e.realMap_injective
      rw [← e.embed_latticeMap, hw, he]
    simpa only [hcoord] using hx
  · rintro ⟨w, hw, rfl⟩
    exact ⟨embed d w, hw, (e.embed_latticeMap w).symm⟩

/-- The induced map on points of a convex set uses the actual affine image. -/
def mapLatticePoint (P : Set (Ambient d)) :
    latticePoints (embed d) P → latticePoints (embed n) (e.realMap '' P) :=
  fun z => ⟨e.latticeMap z, (e.lattice_image_membership P _).mpr ⟨z, z.property, rfl⟩⟩

/-- Summing affine images adds one copy of the origin per summand. -/
theorem total_mapLatticePoint (P : Set (Ambient d))
    (s : Multiset (latticePoints (embed d) P)) :
    total (latticePoints (embed n) (e.realMap '' P)) (s.map (e.mapLatticePoint P)) =
      s.card • e.origin + e.linear (total (latticePoints (embed d) P) s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, total_cons, ih, Multiset.card_cons, map_add,
      add_nsmul, one_nsmul]
    change e.origin + e.linear (a : Lattice d) +
      (s.card • e.origin + e.linear (total (latticePoints (embed d) P) s)) = _
    abel

/-- Full integer decomposition transfers through a saturated integral affine
embedding in every degree, with the translation multiplicity handled exactly. -/
theorem integerDecompositionProperty_image (P : Set (Ambient d))
    (hP : IntegerDecompositionProperty (embed d) P) :
    IntegerDecompositionProperty (embed n) (e.realMap '' P) := by
  intro k hk z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hz
  have hdiff : embed n (z - (k : ℤ) • e.origin) = e.realLinear ((k : ℝ) • x) := by
    rw [map_sub, embed_int_smul, hz, realMap_apply, smul_add, map_smul]
    simp only [Int.cast_natCast]
    abel
  obtain ⟨u, hu⟩ := e.saturated (z - (k : ℤ) • e.origin) ⟨(k : ℝ) • x, hdiff.symm⟩
  have huR : embed d u = (k : ℝ) • x := by
    apply e.injective
    rw [← e.compatible, hu, hdiff]
  obtain ⟨s, hcard, htotal⟩ := hP k hk u ⟨x, hx, huR⟩
  refine ⟨s.map (e.mapLatticePoint P), ?_, ?_⟩
  · simpa only [Multiset.card_map] using hcard
  · rw [e.total_mapLatticePoint, hcard, htotal, hu, natCast_zsmul]
    abel

/-- The affine range of a full-dimensional coordinate polytope equals the
actual affine span of its image. -/
theorem realMap_range_eq_affineSpan (P : LatticePolytope d) :
    Set.range e.realMap = (affineSpan ℝ (e.realMap '' P.carrier) : Set (Ambient n)) := by
  rw [← AffineSubspace.map_span]
  change Set.range e.realMap = e.realMap '' (affineSpan ℝ P.carrier : Set (Ambient d))
  rw [show affineSpan ℝ P.carrier = ⊤ from P.fullDimensional]
  simp

/-- Two full-dimensional charts of the same actual set have equal affine ranges. -/
theorem realMap_range_eq_of_image_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n) (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier) :
    Set.range e.realMap = Set.range f.realMap := by
  rw [e.realMap_range_eq_affineSpan P, f.realMap_range_eq_affineSpan Q, h]

/-- Edges in a chart are exactly the actual nondegenerate segment faces of
its affine image. -/
theorem edge_iff_ambient (P : LatticePolytope d) (x y : Ambient d) :
    P.IsEdge x y ↔ e.realMap x ≠ e.realMap y ∧
      IsExtreme ℝ (e.realMap '' P.carrier) (segment ℝ (e.realMap x) (e.realMap y)) := by
  rw [LatticePolytope.IsEdge, ← image_segment ℝ e.realMap,
    affine_isExtreme_image_iff e.realMap e.realMap_injective]
  constructor
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (e.realMap_injective he), hface⟩
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (congrArg e.realMap he), hface⟩

/-- Actual edges transfer between any two injective affine charts of the same set. -/
theorem edge_transfer_iff {k : ℕ} (f : IntegralAffineEmbedding k n)
    (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier)
    (x y : Ambient d) (u v : Ambient k)
    (hx : e.realMap x = f.realMap u) (hy : e.realMap y = f.realMap v) :
    P.IsEdge x y ↔ Q.IsEdge u v := by
  rw [e.edge_iff_ambient P, f.edge_iff_ambient Q, h, hx, hy]

/-- Equal affine coordinate ranges have equal linear direction ranges, even
when the two integral origins differ. -/
theorem linear_range_eq_of_affine_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realMap = Set.range f.realMap) :
    Set.range e.realLinear = Set.range f.realLinear := by
  have hincl {d k : ℕ} (e : IntegralAffineEmbedding d n) (f : IntegralAffineEmbedding k n)
      (h : Set.range e.realMap = Set.range f.realMap) :
      Set.range e.realLinear ⊆ Set.range f.realLinear := by
    rintro z ⟨x, rfl⟩
    have hx : e.realMap x ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self x
    have hzero : e.realMap 0 ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self 0
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y0, hy0⟩ := hzero
    refine ⟨y - y0, ?_⟩
    rw [map_sub]
    have he := congrArg₂ (fun a b : Ambient n => a - b) hy hy0
    simpa only [realMap_apply, map_zero, add_zero, add_sub_add_left_eq_sub,
      add_sub_cancel_left] using he
  exact Set.Subset.antisymm (hincl e f h) (hincl f e h.symm)

/-- Saturation supplies an integral coordinate preimage for every vector
expressed in another chart of the same real direction subspace. -/
theorem exists_linear_preimage_of_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    ∃ w : Lattice d, e.linear w = f.linear z := by
  apply e.saturated
  rw [h, f.compatible]
  exact Set.mem_range_self (embed k z)

/-- The integral linear map changing between two saturated coordinate charts. -/
def changeLinearMap {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k →ₗ[ℤ] Lattice d where
  toFun z := Classical.choose (e.exists_linear_preimage_of_range_eq f h z)
  map_add' x y := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (x + y))) =
      e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h x) +
        Classical.choose (e.exists_linear_preimage_of_range_eq f h y))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (x + y))]
    simp only [map_add,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x),
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h y)]
  map_smul' r x := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (r • x))) =
      e.linear (r • Classical.choose (e.exists_linear_preimage_of_range_eq f h x))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (r • x))]
    simp only [map_zsmul,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x)]

@[simp] theorem changeLinearMap_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinearMap f h z) = f.linear z :=
  Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h z)

/-- The change of saturated lattice coordinates is an actual integral linear
equivalence, in arbitrary source dimensions. -/
def changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k ≃ₗ[ℤ] Lattice d :=
  LinearEquiv.ofBijective (e.changeLinearMap f h) ⟨by
    intro x y hxy
    apply f.linear_injective
    simpa only [e.changeLinearMap_apply] using congrArg e.linear hxy, by
    intro y
    obtain ⟨x, hx⟩ := f.exists_linear_preimage_of_range_eq e h.symm y
    refine ⟨x, e.linear_injective ?_⟩
    rw [e.changeLinearMap_apply]
    exact hx⟩

@[simp] theorem changeLinear_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinear f h z) = f.linear z :=
  e.changeLinearMap_apply f h z

/-- Changing a saturated coordinate chart translates the origin once and
then uses the exact integral linear change of coordinates. -/
theorem latticeMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.latticeMap (z0 + e.changeLinear f h z) = f.latticeMap z := by
  change e.origin + e.linear (z0 + e.changeLinear f h z) = f.origin + f.linear z
  rw [map_add, e.changeLinear_apply, ← add_assoc]
  exact congrArg (fun x => x + f.linear z) hz0

/-- The real images of integer-coordinate changes agree exactly. -/
theorem realMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.realMap (embed d (z0 + e.changeLinear f h z)) = f.realMap (embed k z) := by
  rw [← e.embed_latticeMap, e.latticeMap_changeLinear f h z0 hz0 z, f.embed_latticeMap]

/-- Applying an affine lattice chart preserves the prescribed parity class
of a difference. This is the forward direction used for face parity. -/
theorem sameParity_latticeMap {x y : Lattice d} (h : SameParity x y) :
    SameParity (e.latticeMap x) (e.latticeMap y) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨e.linear w, ?_⟩
  change (e.origin + e.linear x) - (e.origin + e.linear y) = _
  rw [add_sub_add_left_eq_sub, ← map_sub, hw, map_add]

end IntegralAffineEmbedding

end PaperVerification.ToricGeometry
end Source_ToricIntegralAffine

section Source_ToricFaceCoordinates

/-!
# Saturated coordinates on a subset of an integral basis

Selecting any subset of a genuine integral basis gives an injective integral
affine coordinate map whose real image has exactly the induced lattice.
These maps will be used as actual coordinates on faces of smooth polytopes.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators

section BasisSelection

variable {R E ι κ : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [Fintype κ]

def selectedBasisMap (b : Module.Basis ι R E) (a : κ ↪ ι) : (κ → R) →ₗ[R] E :=
  Fintype.linearCombination R (fun i => b (a i))

@[simp] theorem selectedBasisMap_apply (b : Module.Basis ι R E) (a : κ ↪ ι) (x : κ → R) :
    selectedBasisMap b a x = ∑ i, x i • b (a i) := rfl

@[simp] theorem selectedBasisMap_coordinate (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (i : κ) :
    b.repr (selectedBasisMap b a x) (a i) = x i := by
  classical
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply,
    a.injective.eq_iff, smul_eq_mul]

theorem selectedBasisMap_coordinate_eq_zero (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (j : ι) (hj : j ∉ Set.range a) :
    b.repr (selectedBasisMap b a x) j = 0 := by
  classical
  have hne (i : κ) : a i ≠ j := fun hi => hj ⟨i, hi⟩
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, hne, smul_eq_mul]

theorem selectedBasisMap_injective (b : Module.Basis ι R E) (a : κ ↪ ι) :
    Function.Injective (selectedBasisMap b a) := by
  intro x y hxy
  funext i
  have h := congrArg (fun z => b.repr z (a i)) hxy
  simpa only [selectedBasisMap_coordinate] using h

/-- A selected-basis subspace is exactly the locus where all omitted basis
coordinates vanish. -/
theorem mem_range_selectedBasisMap_iff (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E) :
    x ∈ Set.range (selectedBasisMap b a) ↔
      ∀ j ∉ Set.range a, b.repr x j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ j hj
    exact selectedBasisMap_coordinate_eq_zero b a t j hj
  · intro hx
    refine ⟨fun i => b.repr x (a i), ?_⟩
    apply b.ext_elem
    intro j
    by_cases hj : j ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hj
      exact selectedBasisMap_coordinate b a (fun i => b.repr x (a i)) i
    · rw [selectedBasisMap_coordinate_eq_zero b a _ j hj, hx j hj]

theorem selectedBasisMap_repr_restrict (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E)
    (hx : ∀ j ∉ Set.range a, b.repr x j = 0) :
    selectedBasisMap b a (fun i => b.repr x (a i)) = x := by
  obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a x).mpr hx
  have hcoord : w = fun i => b.repr x (a i) := by
    funext i
    rw [← hw, selectedBasisMap_coordinate]
  rw [← hcoord]
  exact hw

@[simp] theorem selectedBasisMap_single (b : Module.Basis ι R E) (a : κ ↪ ι)
    [DecidableEq κ] (i : κ) (r : R) :
    selectedBasisMap b a (Pi.single i r) = r • b (a i) :=
  Fintype.linearCombination_apply_single R (fun k => b (a k)) i r

end BasisSelection

/-- An integral selected-basis combination embeds as the identical real combination. -/
theorem embed_selectedBasisMap {d n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (z : Lattice d) :
    embed n (selectedBasisMap b a z) =
      selectedBasisMap (integralBasisReal b) a (embed d z) := by
  ext j
  simp [selectedBasisMap_apply, map_sum, integralBasisReal_apply, embed,
    Finset.sum_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]

/-- Selecting an integral basis subset and an integral origin defines an actual
saturated integral affine coordinate embedding. -/
def selectedBasisChart {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) :
    IntegralAffineEmbedding d n where
  origin := v
  linear := (selectedBasisMap b a).toAddMonoidHom
  realLinear := selectedBasisMap (integralBasisReal b) a
  injective := selectedBasisMap_injective _ _
  compatible := embed_selectedBasisMap b a
  saturated := by
    intro z hz
    have hzero := (mem_range_selectedBasisMap_iff (integralBasisReal b) a (embed n z)).mp hz
    have hzeroZ (j : Fin n) (hj : j ∉ Set.range a) : b.repr z j = 0 := by
      have h := hzero j hj
      rw [integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a z).mpr hzeroZ
    exact ⟨w, hw⟩

@[simp] theorem selectedBasisChart_realMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Ambient d) :
    (selectedBasisChart v b a).realMap x =
      embed n v + ∑ i, x i • integralBasisReal b (a i) := rfl

@[simp] theorem selectedBasisChart_latticeMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Lattice d) :
    (selectedBasisChart v b a).latticeMap x = v + ∑ i, x i • b (a i) := rfl

end PaperVerification.ToricGeometry
end Source_ToricFaceCoordinates

section Source_ToricQuotientFaceCoordinates




/-!
# Actual saturated affine coordinates on a support face

The normal quotient and the tangent embedding are dual under the ordinary
coordinate pairing. The origin solves precisely the active support
equalities. At integral support values this is an actual saturated integral
affine chart, so all lattice and parity coordinates retain their meaning.
-/


namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

def complementaryEmbedding (I : Finset (Fin n)) : Fin (n - I.card) ↪ Fin n where
  toFun j := ((quotientIndexEquivFin I).symm j : Fin n)
  inj' := Subtype.val_injective.comp (quotientIndexEquivFin I).symm.injective

theorem mem_range_complementaryEmbedding_iff (I : Finset (Fin n)) (i : Fin n) :
    i ∈ Set.range (complementaryEmbedding I) ↔ i ∉ I := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ((quotientIndexEquivFin I).symm j).property
  · intro hi
    refine ⟨quotientIndexEquivFin I ⟨i, hi⟩, ?_⟩
    simp only [complementaryEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply]

def faceTangentReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient (n - I.card) →ₗ[ℝ] Ambient n :=
  selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)

def faceTangentLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice (n - I.card) →ₗ[ℤ] Lattice n :=
  selectedBasisMap (integralDualBasis b) (complementaryEmbedding I)

/-- The tangent embedding is literally dual to the saturated normal
quotient, not merely isomorphic after tensoring with the reals. -/
theorem faceTangentReal_pairing (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (u : Ambient n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) u) (faceTangentReal b I x) =
      (dotProductEquiv ℝ (Fin (n - I.card)) (coneQuotientReal b I u)) x := by
  have hp (j : Fin (n - I.card)) :
      (dotProductEquiv ℝ (Fin n) u)
        (integralBasisReal (integralDualBasis b) (complementaryEmbedding I j)) =
      (integralBasisReal b).repr u (complementaryEmbedding I j) := by
    rw [integralBasisReal_apply]
    change (∑ k, u k * embed n (integralDualBasis b (complementaryEmbedding I j)) k) = _
    simpa only [mul_comm] using
      integralDualBasis_real_pairing b (complementaryEmbedding I j) u
  simp only [faceTangentReal, selectedBasisMap_apply, map_sum, map_smul, hp, smul_eq_mul]
  change (∑ j, x j * (integralBasisReal b).repr u (complementaryEmbedding I j)) =
    ∑ j, (coneQuotientReal b I u) j * x j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

def quotientFaceOrigin (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Ambient n :=
  -∑ i ∈ I, a (b i) • integralBasisReal (integralDualBasis b) i

def quotientFaceOriginLattice (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Lattice n :=
  -∑ i ∈ I, a (b i) • integralDualBasis b i

theorem embed_quotientFaceOrigin (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    embed n (quotientFaceOriginLattice a b I) =
      quotientFaceOrigin (fun u => (a u : ℝ)) b I := by
  simp only [quotientFaceOriginLattice, quotientFaceOrigin, map_neg, map_sum,
    embed_int_smul, integralBasisReal_apply]

theorem quotientFaceOrigin_coordinate (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr (quotientFaceOrigin a b I) i =
      if i ∈ I then -a (b i) else 0 := by
  by_cases hi : i ∈ I <;>
    simp [quotientFaceOrigin, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul, hi]

def quotientFaceMap (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Ambient (n - I.card) →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ _ (quotientFaceOrigin a b I) + (faceTangentReal b I).toAffineMap

@[simp] theorem quotientFaceMap_apply (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) :
    quotientFaceMap a b I x = quotientFaceOrigin a b I + faceTangentReal b I x := rfl

theorem quotientFaceMap_injective (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Function.Injective (quotientFaceMap a b I) := by
  intro x y h
  apply selectedBasisMap_injective (integralBasisReal (integralDualBasis b))
    (complementaryEmbedding I)
  exact add_left_cancel h

theorem normal_pairing_eq_dual_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) x =
      (integralBasisReal (integralDualBasis b)).repr x i := by
  change (∑ j, embed n (b i) j * x j) = _
  simpa only [integralDualBasis_involutive] using
    integralDualBasis_real_pairing (integralDualBasis b) i x

theorem quotientFaceMap_active (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) (i : Fin n) (hi : i ∈ I) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceMap a b I x) = -a (b i) := by
  rw [normal_pairing_eq_dual_coordinate, quotientFaceMap_apply,
    map_add, Finsupp.add_apply, quotientFaceOrigin_coordinate, if_pos hi]
  have hnot : i ∉ Set.range (complementaryEmbedding I) := by
    rw [mem_range_complementaryEmbedding_iff]
    exact not_not.mpr hi
  rw [show faceTangentReal b I x = selectedBasisMap
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) x from rfl,
    selectedBasisMap_coordinate_eq_zero _ _ _ _ hnot, add_zero]

/-- The affine chart covers exactly the genuine active hyperplanes, with
no unproved saturation or affine-span premise. -/
theorem mem_range_quotientFaceMap_iff (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (x : Ambient n) :
    x ∈ Set.range (quotientFaceMap a b I) ↔ ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact quotientFaceMap_active a b I y i hi
  · intro hx
    have hzero : ∀ i ∉ Set.range (complementaryEmbedding I),
        (integralBasisReal (integralDualBasis b)).repr
          (x - quotientFaceOrigin a b I) i = 0 := by
      intro i hi
      have hiI : i ∈ I := by
        simpa only [mem_range_complementaryEmbedding_iff, not_not] using hi
      rw [map_sub, Finsupp.sub_apply, quotientFaceOrigin_coordinate, if_pos hiI,
        ← normal_pairing_eq_dual_coordinate, hx i hiI, sub_self]
    obtain ⟨y, hy⟩ := (mem_range_selectedBasisMap_iff
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)
      (x - quotientFaceOrigin a b I)).mpr hzero
    refine ⟨y, ?_⟩
    change quotientFaceOrigin a b I +
      selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) y = x
    rw [hy]
    abel

/-- Integral support gives the actual saturated affine lattice chart. -/
def quotientFaceIntegralChart (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    IntegralAffineEmbedding (n - I.card) n :=
  selectedBasisChart (quotientFaceOriginLattice a b I)
    (integralDualBasis b) (complementaryEmbedding I)

theorem quotientFaceIntegralChart_realMap (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    (quotientFaceIntegralChart a b I).realMap =
      quotientFaceMap (fun u => (a u : ℝ)) b I := by
  ext x
  simp only [quotientFaceIntegralChart, IntegralAffineEmbedding.realMap_apply,
    selectedBasisChart, embed_quotientFaceOrigin, quotientFaceMap_apply,
    faceTangentReal]

/-- A linear form vanishing on the deleted normals factors through the
explicit saturated quotient, with the actual chosen section. -/
theorem linear_face_factorization
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i ∈ I, ℓ (integralBasisReal b i) = 0) (u : Ambient n) :
    ℓ (coneQuotientSectionReal b I (coneQuotientReal b I u)) = ℓ u := by
  change ℓ (basisSection (integralBasisReal b) I
    ((quotientCoordinateFinEquiv ℝ I).symm
      (quotientCoordinateFinEquiv ℝ I (basisProjection (integralBasisReal b) I u)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact map_basisSection_projection (integralBasisReal b) I ℓ hℓ u

end PaperVerification.ToricGeometry
end Source_ToricQuotientFaceCoordinates

section Source_ToricOrbitQuotientCoordinates




/-!
# The orbit chart is the actual chart of the quotient star

Vanishing on a smooth cone gives the saturated character lattice dual to
the quotient of the normal lattice. The coordinate maps are integral, and
the pairing identity identifies the two actual nonnegative semigroups.
Consequently the orbit quotient is a surjective map of the literal chart
algebras, rather than an assumed description of an orbit closure.
-/


namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

theorem integerPairing_basis_eq_dualCoordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (m : Lattice n) :
    integerPairing (b i) m = (integralDualBasis b).repr m i := by
  simp only [integerPairing,integralDualBasis_repr,mul_comm]

theorem embed_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    embed n (faceTangentLattice b I z) =
      faceTangentReal b I (embed (n-I.card) z) := by
  simp only [faceTangentLattice,faceTangentReal,selectedBasisMap_apply,
    map_sum,embed_int_smul,integralBasisReal_apply]
  rfl

theorem integerPairing_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (z : Lattice (n-I.card)) :
    integerPairing u (faceTangentLattice b I z) =
      integerPairing (coneQuotientLattice b I u) z := by
  have h := faceTangentReal_pairing b I (embed n u) (embed (n-I.card) z)
  rw [← embed_faceTangentLattice,coneQuotient_compatible,
    SmoothCompleteFan.normalRay_pairing_lattice,
    SmoothCompleteFan.normalRay_pairing_lattice] at h
  exact_mod_cast h

def faceCharacterProjection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Lattice n →ₗ[ℤ] Lattice (n-I.card) where
  toFun m j := (integralDualBasis b).repr m (complementaryEmbedding I j)
  map_add' m p := by ext j; simp
  map_smul' a m := by
    ext j
    exact congrArg (fun z : Fin n →₀ ℤ => z (complementaryEmbedding I j))
      ((integralDualBasis b).repr.map_smul a m)

@[simp] theorem faceCharacterProjection_tangent
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    faceCharacterProjection b I (faceTangentLattice b I z) = z := by
  ext j
  exact selectedBasisMap_coordinate (integralDualBasis b) (complementaryEmbedding I) z j

theorem faceTangentLattice_annihilates
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) (u : Lattice n) (hu : u∈I.image b) :
    integerPairing u (faceTangentLattice b I z)=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  rw [integerPairing_basis_eq_dualCoordinate]
  apply selectedBasisMap_coordinate_eq_zero
  simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi

theorem faceTangentLattice_projection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (m : Lattice n) (hm : ∀ u∈I.image b,integerPairing u m=0) :
    faceTangentLattice b I (faceCharacterProjection b I m)=m := by
  apply selectedBasisMap_repr_restrict
  intro i hi
  have hiI : i∈I := by
    simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi
  rw [← integerPairing_basis_eq_dualCoordinate]
  exact hm (b i) (Finset.mem_image.mpr ⟨i,hiI,rfl⟩)

def orbitQuotientCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) : Finset (Lattice (n-I.card)) :=
  (s \ I.image b).image (coneQuotientLattice b I)

theorem faceCharacterProjection_mem_quotientDualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n))
    (m : orbitCharacterFace s (I.image b)) :
    faceCharacterProjection b I m.val.val ∈ dualConeMonoid (orbitQuotientCone b I s) := by
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I m.val.val m.property]
  exact m.val.property u (Finset.mem_sdiff.mp hu).1

theorem faceTangentLattice_mem_dualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (z : dualConeMonoid (orbitQuotientCone b I s)) :
    faceTangentLattice b I z.val ∈ dualConeMonoid s := by
  intro u hu
  by_cases huI : u∈I.image b
  · rw [faceTangentLattice_annihilates b I z.val u huI]
  · rw [integerPairing_faceTangentLattice]
    exact z.property _ (Finset.mem_image.mpr
      ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)

/-- The actual saturated semigroup equivalence. It uses no fan
classification, geometry, or positivity hypothesis beyond the semigroups. -/
def orbitQuotientSemigroupEquiv
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    orbitCharacterFace s (I.image b) ≃+ dualConeMonoid (orbitQuotientCone b I s) where
  toFun m := ⟨faceCharacterProjection b I m.val.val,
    faceCharacterProjection_mem_quotientDualCone b I s m⟩
  invFun z := ⟨⟨faceTangentLattice b I z.val,faceTangentLattice_mem_dualCone b I s z⟩,
    faceTangentLattice_annihilates b I z.val⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    exact faceTangentLattice_projection b I m.val.val m.property
  right_inv z := Subtype.ext (faceCharacterProjection_tangent b I z.val)
  map_add' m p := Subtype.ext ((faceCharacterProjection b I).map_add m.val.val p.val.val)

variable (k : Type*) [CommRing k]

def orbitQuotientAlgebraMap
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
      monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s)) :=
  (monoidChartAlgebraEquiv k _).toAlgHom.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).toAlgHom.comp
      ((additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom))

theorem orbitQuotientAlgebraMap_surjective
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    Function.Surjective (orbitQuotientAlgebraMap k b I s hIs) :=
  (monoidChartAlgebraEquiv k _).surjective.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).surjective.comp
      ((additiveFaceRetraction_surjective k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective))

theorem orbitQuotientChartMap_isClosedImmersion
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (orbitQuotientAlgebraMap k b I s hIs).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (orbitQuotientAlgebraMap_surjective k b I s hIs)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientSemigroupEquiv
#print axioms PaperVerification.ToricGeometry.orbitQuotientChartMap_isClosedImmersion
end Source_ToricOrbitQuotientCoordinates

section Source_ToricOrbitStarIndex




/-! # The actual cone index of an orbit closure and its quotient fan -/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

abbrev OrbitConeIndex :=
  {s : Finset (Lattice n) // s∈«Σ».cones ∧ I.image b⊆s}

def orbitConeQuotientIndex (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).ConeIndex :=
  ⟨orbitQuotientCone b I s.val,(«Σ».mem_quotientStarCones b I _).mpr
    ⟨s.val,s.property.1,s.property.2,rfl⟩⟩

theorem orbitQuotientCone_subset_iff (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I s.val ⊆ orbitQuotientCone b I t.val ↔ s.val⊆t.val := by
  constructor
  · intro h u hu
    by_cases huI : u∈I.image b
    · exact t.property.2 huI
    · have hup : coneQuotientLattice b I u∈orbitQuotientCone b I t.val :=
        h (Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hup
      have huv := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
        s.property.2 t.property.2 (Finset.mem_sdiff.mpr ⟨hu,huI⟩) hv hvu.symm
      exact huv.symm ▸ (Finset.mem_sdiff.mp hv).1
  · intro h
    exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) h)

theorem orbitConeQuotientIndex_injective :
    Function.Injective («Σ».orbitConeQuotientIndex b I hF) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  apply Finset.Subset.antisymm
  · apply («Σ».orbitQuotientCone_subset_iff b I s t).mp
    exact he.le
  · apply («Σ».orbitQuotientCone_subset_iff b I t s).mp
    exact he.symm.le

theorem orbitConeQuotientIndex_surjective :
    Function.Surjective («Σ».orbitConeQuotientIndex b I hF) := by
  intro t
  obtain ⟨s,hs,hIs,ht⟩ := («Σ».mem_quotientStarCones b I t.val).mp t.property
  exact ⟨⟨s,hs,hIs⟩,Subtype.ext ht.symm⟩

/-- This is an order isomorphism of the actual cone sets. In particular it
records all face inclusions, not merely a bijection of maximal cones. -/
def orbitConeOrderIso :
    «Σ».OrbitConeIndex b I ≃o («Σ».completeQuotientStarFan b I hF).ConeIndex where
  toEquiv := Equiv.ofBijective («Σ».orbitConeQuotientIndex b I hF)
    ⟨«Σ».orbitConeQuotientIndex_injective b I hF,
      «Σ».orbitConeQuotientIndex_surjective b I hF⟩
  map_rel_iff' := by
    intro s t
    exact «Σ».orbitQuotientCone_subset_iff b I s t

@[simp] theorem orbitConeOrderIso_apply (s : «Σ».OrbitConeIndex b I) :
    («Σ».orbitConeOrderIso b I hF s).val = orbitQuotientCone b I s.val := rfl

variable (k : Type*) [CommRing k]

/-- The quotient fan's actual affine chart diagram, indexed instead by
the original cones containing the orbit cone. -/
def orbitChartDiagram : «Σ».OrbitConeIndex b I ⥤ Scheme :=
  («Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
    («Σ».completeQuotientStarFan b I hF).coneDiagram k

instance orbitChartDiagram_hasColimit : HasColimit («Σ».orbitChartDiagram b I hF k) := by
  exact inferInstanceAs (HasColimit
    ((«Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
      («Σ».completeQuotientStarFan b I hF).coneDiagram k))

def orbitChartColimit : Scheme := colimit («Σ».orbitChartDiagram b I hF k)

/-- Reindexing changes no glued scheme. The isomorphism follows from the
actual categorical colimit and an equivalence of its indexing categories. -/
def orbitChartColimitIsoFan :
    «Σ».orbitChartColimit b I hF k ≅ («Σ».completeQuotientStarFan b I hF).fanScheme k :=
  Functor.Final.colimitIso («Σ».orbitConeOrderIso b I hF).equivalence.functor
    ((«Σ».completeQuotientStarFan b I hF).coneDiagram k)

@[reassoc (attr := simp)] theorem orbitChartColimitIsoFan_ι
    (s : «Σ».OrbitConeIndex b I) :
    colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom =
        («Σ».completeQuotientStarFan b I hF).fanChartMap k
          («Σ».orbitConeQuotientIndex b I hF s) :=
  Functor.Final.ι_colimitIso_hom _ _ s

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitConeOrderIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitChartColimitIsoFan
end Source_ToricOrbitStarIndex

section Source_ToricOrbitChartMaps




/-! # Naturality and gluing of actual orbit chart quotient morphisms -/


namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M]

@[simp] theorem monoidChartAlgebraEquiv_single_character
    (S : AddSubmonoid M) (m : S) :
    monoidChartAlgebraEquiv k S (single m 1) = chartCharacter k S m.val m.property :=
  Subtype.ext (monoidChartMap_single k S m 1)

@[simp] theorem monoidChartAlgebraEquiv_symm_character
    (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    (monoidChartAlgebraEquiv k S).symm (chartCharacter k S m hm) = single ⟨m,hm⟩ 1 := by
  apply (monoidChartAlgebraEquiv k S).injective
  simp only [AlgEquiv.apply_symm_apply,monoidChartAlgebraEquiv_single_character]

theorem chartAlgHom_ext_characters (S : AddSubmonoid M)
    {A : Type*} [Semiring A] [Algebra k A]
    (F G : monoidChartAlgebra k S →ₐ[k] A)
    (h : ∀ m (hm : m∈S),F (chartCharacter k S m hm)=G (chartCharacter k S m hm)) :
    F=G := by
  ext f
  obtain ⟨g,rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  induction g using AddMonoidAlgebra.induction_on with
  | of m =>
      simpa only [AddMonoidAlgebra.of_apply,toAdd_ofAdd,monoidChartAlgebraEquiv_single_character] using
        h m.val m.property
  | add f g hf hg => simp only [map_add,hf,hg]
  | smul a f hf => simp only [map_smul,hf]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem orbitQuotientAlgebraMap_character
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) (m : Lattice n)
    (hm : m∈dualConeMonoid s) :
    ((orbitQuotientAlgebraMap k b I s hIs (chartCharacter k (dualConeMonoid s) m hm) :
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      if h : ∀ u∈I.image b,integerPairing u m=0
      then single (faceCharacterProjection b I m) 1 else 0 := by
  simp only [orbitQuotientAlgebraMap,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character]
  by_cases h : ∀ u∈I.image b,integerPairing u m=0
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∈orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_mem k _ _ _ hmem,
      AddMonoidAlgebra.domCongr_single,dif_pos h]
    exact monoidChartMap_single k _ _ 1
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∉orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_not_mem k _ _ _ hmem,map_zero,map_zero,dif_neg h]
    rfl

theorem orbitQuotientCone_mono {s t : Finset (Lattice n)} (hts : t⊆s) :
    orbitQuotientCone b I t ⊆ orbitQuotientCone b I s :=
  Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hts)

/-- Restriction along an actual cone face commutes with killing the
characters positive on the orbit cone. -/
theorem orbitQuotientAlgebraMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    (orbitQuotientAlgebraMap k b I t hIt).comp
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) =
      (monoidChartInclusion k (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).comp
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)) := by
  apply chartAlgHom_ext_characters
  intro m hm
  apply Subtype.ext
  simp only [AlgHom.comp_apply,monoidChartInclusion_character,
    monoidChartInclusion_coe,orbitQuotientAlgebraMap_character]

def orbitQuotientChartMap (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    coneChart k (orbitQuotientCone b I s) ⟶ coneChart k s :=
  Spec.map (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s hIs).toRingHom)

instance orbitQuotientChartMap_closed (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (orbitQuotientChartMap k b I s hIs) :=
  orbitQuotientChartMap_isClosedImmersion k b I s hIs

set_option maxHeartbeats 2000000 in
@[reassoc] theorem orbitQuotientChartMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    coneChartFaceMap k (orbitQuotientCone_mono b I hts) ≫
        orbitQuotientChartMap k b I s (hIt.trans hts) =
      orbitQuotientChartMap k b I t hIt ≫ coneChartFaceMap k hts := by
  exact (Spec.map_comp
    (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s (hIt.trans hts)).toRingHom)
    (CommRingCat.ofHom (monoidChartInclusion k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).toRingHom)).symm.trans
    ((congrArg (fun f : monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I t)) =>
          Spec.map (CommRingCat.ofHom f.toRingHom))
      (orbitQuotientAlgebraMap_naturality k b I hts hIt).symm).trans
      (Spec.map_comp
        (CommRingCat.ofHom (monoidChartInclusion k (dualConeMonoid_antitone hts)).toRingHom)
        (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I t hIt).toRingHom)))

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

/-- The actual quotient charts map compatibly into the actual fan scheme. -/
def orbitClosureCocone : Cocone («Σ».orbitChartDiagram b I hF k) where
  pt := «Σ».fanScheme k
  ι :=
    { app s := orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩
      naturality := by
        intro s t f
        change coneChartFaceMap k (orbitQuotientCone_mono b I (leOfHom f)) ≫
          (orbitQuotientChartMap k b I t.val t.property.2 ≫
            «Σ».fanChartMap k ⟨t.val,t.property.1⟩) =
          (orbitQuotientChartMap k b I s.val s.property.2 ≫
            «Σ».fanChartMap k ⟨s.val,s.property.1⟩) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc,
          orbitQuotientChartMap_naturality k b I (leOfHom f) s.property.2,
          Category.assoc]
        exact congrArg
          (fun q => orbitQuotientChartMap k b I s.val s.property.2 ≫ q)
          («Σ».fanChartMap_naturality k
            (s := ⟨s.val, s.property.1⟩) (t := ⟨t.val, t.property.1⟩)
            (leOfHom f)) }

/-- The global morphism from the actual quotient-star scheme. Closedness
and its identification with the invariant orbit closure are proved using
the actual local quotient squares; they are not included in this definition. -/
def orbitClosureMap :
    («Σ».completeQuotientStarFan b I hF).fanScheme k ⟶ «Σ».fanScheme k :=
  («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
    colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF)

@[reassoc (attr := simp)] theorem orbitClosureMap_chart
    (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) ≫ «Σ».orbitClosureMap k b I hF =
      orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩ := by
  rw [← «Σ».orbitChartColimitIsoFan_ι b I hF k s]
  change (colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom) ≫
    («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
      colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫ q)
      (Iso.hom_inv_id_assoc («Σ».orbitChartColimitIsoFan b I hF k)
        (colimit.desc («Σ».orbitChartDiagram b I hF k)
          («Σ».orbitClosureCocone k b I hF)))).trans
      (colimit.ι_desc («Σ».orbitClosureCocone k b I hF) s))

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientAlgebraMap_naturality
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_chart
end Source_ToricOrbitChartMaps

section Source_ToricProjectiveLineOrders




/-!
# Character orders on the actual two-chart projective line

Each smooth rank-one chart is identified with `Spec k[X]`, and its
primitive character is identified with the literal coordinate `X`.
Orders are consequently computed in the actual scheme local rings.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]

/-- Actual affine coordinate maps commute with restriction along a
specified affine open morphism. -/
theorem affineOpenCoordinateMap_comp (r : R) :
    affineOpenCoordinateMap S (Spec.map φ ≫ j) (φ r) =
      affineOpenCoordinateMap R j r := by
  have hsec : (Scheme.ΓSpecIso S).inv (φ r) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) :=
    congrArg (fun g => g r) (Scheme.ΓSpecIso_inv_naturality φ)
  change openImmersionGlobalToFunctionField (Spec.map φ ≫ j)
      ((Scheme.ΓSpecIso S).inv (φ r)) =
    openImmersionGlobalToFunctionField j ((Scheme.ΓSpecIso R).inv r)
  rw [hsec]
  exact openImmersionGlobalToFunctionField_restrict
    (Spec.map φ) j ((Scheme.ΓSpecIso R).inv r)

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

variable (k : Type u) [Field k]

/-- The actual affine-line chart map, including the algebra equivalence
which determines its coordinate. -/
def projectiveLinePolynomialChart (negative : Bool) :
    Spec (.of (Polynomial k)) ⟶ projectiveLineScheme k :=
  Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom ≫
    projectiveLineChart k negative

instance projectiveLinePolynomialChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLinePolynomialChart k negative) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  change IsOpenImmersion (Spec.map φ ≫ j)
  exact IsOpenImmersion.comp (Spec.map φ) j

def projectiveLineBoundaryPoint (negative : Bool) : projectiveLineScheme k :=
  projectiveLinePolynomialChart k negative (polynomialOrigin k)

/-- The primitive character of either one-dimensional cone is its
ordinary polynomial coordinate. -/
theorem projectiveLineChartRingEquiv_primitive (negative : Bool) :
    projectiveLineChartRingEquiv k negative
      (chartCharacter k (dualConeMonoid {projectiveLineRay negative})
        (projectiveLineRay negative) (by
          rw [mem_projectiveLineDualCone]
          cases negative <;> norm_num [projectiveLineRay])) = Polynomial.X := by
  apply (Polynomial.toFinsuppIsoAlg k).injective
  simp only [projectiveLineChartRingEquiv,AlgEquiv.trans_apply,
    monoidChartAlgebraEquiv_symm_character,AlgEquiv.apply_symm_apply,
    AddMonoidAlgebra.domCongr_single]
  cases negative <;>
    simp [projectiveLineSemigroupEquiv,projectiveLineRay,
      Polynomial.toFinsuppIsoAlg, Polynomial.toFinsuppIso_apply, Polynomial.X_eq_single]

theorem projectiveLine_coordinate_rationalCharacter (negative : Bool) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) Polynomial.X =
        (projectiveLineFan.rationalCharacter k (projectiveLineRay negative) :
          (projectiveLineScheme k).functionField) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  have hm : projectiveLineRay negative∈dualConeMonoid s.val := by
    rw [mem_projectiveLineDualCone]
    cases negative <;> norm_num [projectiveLineRay]
  let r := chartCharacter k (dualConeMonoid s.val) (projectiveLineRay negative) hm
  rw [← projectiveLineChartRingEquiv_primitive k negative]
  exact (affineOpenCoordinateMap_comp R S j φ r).trans
      (projectiveLineFan.chartRationalMap_character k s
        (projectiveLineRay negative) hm)

theorem projectiveLine_character_as_power (negative : Bool) (m : Lattice 1) :
    projectiveLineFan.rationalCharacter k m =
      (projectiveLineFan.rationalCharacter k (projectiveLineRay negative)) ^
        (if negative then -m 0 else m 0) := by
  have hm : m = (if negative then -m 0 else m 0) • projectiveLineRay negative := by
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp [projectiveLineRay,hi]
  nth_rw 1 [hm]
  exact (projectiveLineFan.rationalCharacterHom k).map_zpow
    (Multiplicative.ofAdd (projectiveLineRay negative)) _

/-- All character orders on each actual affine chart, for every integer
character and every actual scheme point. -/
theorem projectiveLine_character_order (negative : Bool) (m : Lattice 1)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) =
      if p=polynomialOrigin k then (if negative then -m 0 else m 0) else 0 := by
  rw [projectiveLine_character_as_power k negative m,Units.val_zpow_eq_zpow_val,
    ← projectiveLine_coordinate_rationalCharacter k negative]
  exact affineLine_coordinate_zpow_order k
    (projectiveLinePolynomialChart k negative) _ p

theorem projectiveLine_character_order_boundary (negative : Bool) (m : Lattice 1) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLineBoundaryPoint k negative) = if negative then -m 0 else m 0 := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_character_order k negative m (polynomialOrigin k)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_character_order
end Source_ToricProjectiveLineOrders

section Source_ToricCocycleOrders




/-!
# The local equations compute actual Cartier orders

The fractional sheaf reconstructed from a rational Cartier cocycle has
the specified local rational generators. This connects its intrinsic
Weil coefficients to the input equations through the actual sheaf frames.
-/


universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem localFrame_frameLinearEquiv (i : C.index) (V : X.Opens)
    (hV : V≤C.openSet i) :
    C.toCartierData.frameLinearEquiv (C.localFrame i) V hV =
      C.localCoordinates i V hV := rfl

/-- The sheaf construction recovers the literal rational generator,
including its multiplicative scalar. -/
theorem localFrame_rationalGenerator (i : C.index) [Nonempty (C.openSet i)] :
    C.toCartierData.frameRationalGenerator (C.localFrame i) =
      (C.generator i : X.functionField) := by
  let U := C.openSet i
  let s := C.toCartierData.frameGenerator (C.localFrame i) U le_rfl
  have hs : C.localCoordinates i U le_rfl s = 1 := by
    rw [← C.localFrame_frameLinearEquiv]
    exact LinearEquiv.apply_symm_apply _ _
  have h := C.localCoordinates_value i U le_rfl s
  rw [hs,map_one] at h
  change rationalValue X U s.val = (C.generator i : X.functionField)
  exact (div_eq_one_iff_eq (Units.ne_zero _)).mp h.symm

variable [IsLocallyNoetherian X]

/-- The sign is fixed by taking local generators of `O(D)`, rather than
local equations of `D`. -/
theorem weilCoefficient_eq (i : C.index) {x : X} (hx : x∈C.openSet i) :
    C.toCartierData.weilCoefficient x = -X.ord (C.generator i : X.functionField) x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hx⟩⟩
  rw [C.toCartierData.weilCoefficient_eq_neg_frameOrder (C.localFrame i) hx,
    C.localFrame_rationalGenerator]

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.weilCoefficient_eq
end Source_ToricCocycleOrders

section Source_ToricProjectiveLineDegree




/-!
# The actual divisor degree on the rank-one fan

For a Cartier divisor specified by integral coefficients at the two rays,
the actual Weil cycle is supported at the two actual rational boundary
points. Its coefficients are the two specified integers. Both residue
degrees are proved to be one, so Mathlib's cycle degree is their sum.
-/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

def projectiveLineFullCone (negative : Bool) : projectiveLineFan.fullCones :=
  ⟨{projectiveLineRay negative},Finset.mem_filter.mpr
    ⟨projectiveLineRayCone_mem negative,Finset.card_singleton _⟩⟩

theorem projectiveLineFullCone_surjective :
    Function.Surjective projectiveLineFullCone := by
  intro s
  rcases (mem_projectiveLineFan_cones s.val).mp (projectiveLineFan.fullCones_mem s)
    with h|h|h
  · have hc := projectiveLineFan.fullCones_card s
    simp only [h,Finset.card_empty] at hc
    omega
  · exact ⟨false,Subtype.ext h.symm⟩
  · exact ⟨true,Subtype.ext h.symm⟩

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_jointly_surjective (x : projectiveLineScheme k) :
    ∃ (negative : Bool) (p : PrimeSpectrum (Polynomial k)),
      projectiveLinePolynomialChart k negative p=x := by
  obtain ⟨s,y,hy⟩ := projectiveLineFan.fullChartOpen_cover k
    projectiveLineFan_isPure x
  obtain ⟨negative,rfl⟩ := projectiveLineFullCone_surjective s
  obtain ⟨p,hp⟩ :=
    (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective y
  refine ⟨negative,p,?_⟩
  have hy' : projectiveLineChart k negative y = x := hy
  change projectiveLineChart k negative
    ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
  exact (congrArg (projectiveLineChart k negative) hp).trans hy'

theorem projectiveLineBoundaryPoint_ne :
    projectiveLineBoundaryPoint k false ≠ projectiveLineBoundaryPoint k true := by
  intro h
  have hh := congrArg (fun x => (projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k (projectiveLineRay false) :
      (projectiveLineScheme k).functionField) x) h
  rw [projectiveLine_character_order_boundary,projectiveLine_character_order_boundary] at hh
  norm_num [projectiveLineRay] at hh

/-- Each boundary point is an actual rational point over the field. -/
def projectiveLineBoundarySection (negative : Bool) :
    Spec (.of k) ⟶ projectiveLineScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    projectiveLinePolynomialChart k negative

theorem projectiveLineBoundarySection_isSection (negative : Bool) :
    projectiveLineBoundarySection k negative ≫
      projectiveLineFan.fanSchemeStructureMap k = 𝟙 (Spec (.of k)) := by
  let s := projectiveLineFan.fullConeIndex (projectiveLineFullCone negative)
  have hj : projectiveLineFan.fanChartMap k s ≫
      projectiveLineFan.fanSchemeStructureMap k =
        Spec.map (CommRingCat.ofHom (algebraMap k
          (monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})))) :=
    comp_over (projectiveLineFan.fanChartMap k s) (Spec (.of k))
  unfold projectiveLineBoundarySection projectiveLinePolynomialChart projectiveLineChart
  erw [Category.assoc,Category.assoc,hj,← Spec.map_comp,← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  change Polynomial.eval 0
    (projectiveLineChartRingEquiv k negative (algebraMap k _ a)) = a
  rw [AlgEquiv.commutes]
  simp

theorem projectiveLineBoundarySection_apply (negative : Bool) :
    projectiveLineBoundarySection k negative (⊥ : PrimeSpectrum k) =
      projectiveLineBoundaryPoint k negative := by
  change projectiveLinePolynomialChart k negative
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (⊥ : PrimeSpectrum k)) = _
  congr 1

theorem projectiveLineBoundaryPoint_residueDegree (negative : Bool) :
    (projectiveLineFan.fanSchemeStructureMap k).residueDegree
      (projectiveLineBoundaryPoint k negative) = 1 := by
  rw [← projectiveLineBoundarySection_apply k negative]
  exact residueDegree_of_section (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLineBoundarySection k negative)
    (projectiveLineBoundarySection_isSection k negative) (⊥ : PrimeSpectrum k)

def projectiveLineCartierData (a : Lattice 1→ℤ) : CartierData (projectiveLineScheme k) :=
  projectiveLineFan.fanCartierData k projectiveLineFan_isPure a

theorem projectiveLine_weilCoefficient_chart (a : Lattice 1→ℤ) (negative : Bool)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineCartierData k a).weilCoefficient
      (projectiveLinePolynomialChart k negative p) =
        if p=polynomialOrigin k then a (projectiveLineRay negative) else 0 := by
  let C := projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a
  let s := projectiveLineFullCone negative
  have hx : projectiveLinePolynomialChart k negative p∈C.openSet ⟨s⟩ :=
    ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,rfl⟩
  change C.toCartierData.weilCoefficient (projectiveLinePolynomialChart k negative p) = _
  erw [C.weilCoefficient_eq ⟨s⟩ hx]
  change -(projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k
      (projectiveLineFan.cartierLatticePoint a s) : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) = _
  rw [projectiveLine_character_order]
  have hp := projectiveLineFan.cartierLatticePoint_pairing a s
    (projectiveLineRay negative) (Finset.mem_singleton_self _)
  have hv : (if negative then -(projectiveLineFan.cartierLatticePoint a s) 0
      else (projectiveLineFan.cartierLatticePoint a s) 0) =
        -a (projectiveLineRay negative) := by
    cases negative <;> simpa only [integerPairing,Fin.sum_univ_one,
      projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] using hp
  rw [hv]
  split_ifs <;> simp

theorem projectiveLine_weilCoefficient_boundary (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).weilCoefficient (projectiveLineBoundaryPoint k negative) =
      a (projectiveLineRay negative) := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_weilCoefficient_chart k a negative (polynomialOrigin k)

theorem projectiveLine_weilCoefficient_support (a : Lattice 1→ℤ) :
    Function.support (projectiveLineCartierData k a).weilCoefficient ⊆
      ({projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true} :
        Finset (projectiveLineScheme k)) := by
  intro x hx
  obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
  have hp : p=polynomialOrigin k := by
    by_contra hp
    exact hx (by rw [projectiveLine_weilCoefficient_chart,if_neg hp])
  subst p
  cases negative <;> simp [projectiveLineBoundaryPoint]

theorem projectiveLine_weilCoefficient_locallyFinite (a : Lattice 1→ℤ) :
    LocallyFiniteSupport (projectiveLineCartierData k a).weilCoefficient :=
  (projectiveLineCartierData k a).locallyFiniteSupport_weilCoefficient_of_finite
    ((Finset.finite_toSet _).subset (projectiveLine_weilCoefficient_support k a))

/-- The actual divisor degree, computed using actual local orders and
actual residue-field extensions. -/
theorem projectiveLineCartier_degree (a : Lattice 1→ℤ) :
    (projectiveLineCartierData k a).degree
      (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
        a (projectiveLineRay false)+a (projectiveLineRay true) := by
  rw [(projectiveLineCartierData k a).degree_eq_sum_of_support_subset
    (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLine_weilCoefficient_locallyFinite k a)
    {projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true}
    (projectiveLine_weilCoefficient_support k a)]
  simp [projectiveLineBoundaryPoint_ne,projectiveLineBoundaryPoint_residueDegree,
    projectiveLine_weilCoefficient_boundary]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_degree
end Source_ToricProjectiveLineDegree

section Source_ToricRankOneFans




/-!
# Every smooth complete rank-one fan is the two-ray fan

A basis of the rank-one integral lattice has generator `1` or `-1`.
Smoothness restricts each cone to one of these rays or the zero cone,
and completeness forces both rays. The result is an equality of the
actual fans and hence an isomorphism of their actual glued schemes.
-/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

theorem rankOneBasis_generator (b : Module.Basis (Fin 1) ℤ (Lattice 1)) :
    b 0=projectiveLineRay false ∨ b 0=projectiveLineRay true := by
  have hsum := b.sum_repr (projectiveLineRay false)
  have hmul : b 0 0 * b.repr (projectiveLineRay false) 0=1 := by
    have h := congrFun hsum (0 : Fin 1)
    simpa [Fin.sum_univ_one,projectiveLineRay,mul_comm] using h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h|h
  · left
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h
  · right
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h

namespace SmoothCompleteFan

theorem eq_of_cones_eq {d : ℕ} {«Σ» Γ : SmoothCompleteFan d}
    (h : «Σ».cones=Γ.cones) : «Σ»=Γ := by
  cases «Σ»
  cases Γ
  cases h
  rfl

variable («Σ» : SmoothCompleteFan 1)

theorem rankOne_cone_cases {s : Finset (Lattice 1)} (hs : s∈«Σ».cones) :
    s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  obtain ⟨b,I,rfl⟩ := «Σ».smooth s hs
  have hI : I⊆{(0 : Fin 1)} := by
    intro i hi
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  rcases Finset.subset_singleton_iff.mp hI with h|h
  · exact Or.inl (by rw [h,Finset.image_empty])
  · rw [h,Finset.image_singleton]
    rcases rankOneBasis_generator b with hb|hb
    · exact Or.inr (Or.inl (congrArg singleton hb))
    · exact Or.inr (Or.inr (congrArg singleton hb))

theorem rankOne_ray_mem (negative : Bool) :
    {projectiveLineRay negative}∈«Σ».cones := by
  obtain ⟨s,hs,hx⟩ := «Σ».complete (embed 1 (projectiveLineRay negative))
  rcases «Σ».rankOne_cone_cases hs with h|h|h
  · rw [h,latticeRayCone_empty] at hx
    have hz : embed 1 (projectiveLineRay negative)=0 := hx
    have h0 := congrFun hz (0 : Fin 1)
    cases negative <;> norm_num [embed,projectiveLineRay] at h0
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · simpa only [h] using hs
    · norm_num [embed,projectiveLineRay] at hx
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · norm_num [embed,projectiveLineRay] at hx
    · simpa only [h] using hs

/-- There is no extra classification hypothesis in dimension one. -/
theorem rankOne_eq_projectiveLine : «Σ»=projectiveLineFan := by
  apply eq_of_cones_eq
  ext s
  rw [mem_projectiveLineFan_cones]
  constructor
  · exact «Σ».rankOne_cone_cases
  · rintro (rfl|rfl|rfl)
    · exact «Σ».empty_mem
    · exact «Σ».rankOne_ray_mem false
    · exact «Σ».rankOne_ray_mem true

variable (k : Type u) [Field k]

def rankOneSchemeIso : «Σ».fanScheme k ≅ projectiveLineScheme k :=
  eqToIso (congrArg (fun Γ : SmoothCompleteFan 1 => Γ.fanScheme k)
    «Σ».rankOne_eq_projectiveLine)

end SmoothCompleteFan

/-- The rank condition is an equality of ordinary lattice dimensions,
not a replacement definition of a curve. -/
def oneDimensionalFanSchemeIso {d : ℕ} («Σ» : SmoothCompleteFan d)
    (hd : d=1) (k : Type u) [Field k] :
    «Σ».fanScheme k ≅ projectiveLineScheme k := by
  subst d
  exact «Σ».rankOneSchemeIso k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rankOne_eq_projectiveLine
end Source_ToricRankOneFans

section Source_ToricProjectiveLineDimension




/-! # The actual Krull dimension of the two-chart projective line -/


namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes

variable (k : Type*) [Field k]

theorem projectiveLine_orderKrullDim : Order.krullDim (projectiveLineScheme k) = 1 := by
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
    let R := CommRingCat.of (Polynomial k)
    let q : Spec R := p
    have hc : Order.coheight ((projectiveLinePolynomialChart k negative) q) =
        p.asIdeal.height :=
      (coheight_eq_of_isOpenImmersion (x := q)
        (projectiveLinePolynomialChart k negative)).trans
          (idealHeight_eq_coheight R q).symm
    have h := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
    have hp : (p.asIdeal.height : WithBot ENat) ≤ 1 := by
      simpa only [Polynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field,zero_add] using h
    exact (congrArg (fun d : ENat => (d : WithBot ENat)) hc).trans_le hp
  · let p := polynomialOrigin k
    letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
      principalPrimeLocalization_isDiscreteValuationRing
        (Polynomial k) (Localization.AtPrime p.asIdeal) p.asIdeal
        Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
    have hc := affineOpen_coheight_eq_one (.of (Polynomial k))
      (projectiveLinePolynomialChart k false) p
    have h := Order.coheight_le_krullDim
      (projectiveLinePolynomialChart k false p)
    simpa only [hc,WithBot.coe_one] using h

/-- The dimension is the usual dimension by chains of irreducible closed
subsets of the actual underlying topological space. -/
theorem projectiveLine_topologicalKrullDim :
    topologicalKrullDim (projectiveLineScheme k) = 1 := by
  change Order.krullDim (IrreducibleCloseds (projectiveLineScheme k)) = 1
  rw [Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := projectiveLineScheme k))]
  exact projectiveLine_orderKrullDim k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_topologicalKrullDim
end Source_ToricProjectiveLineDimension

section Source_ToricChartCoaction




/-! # Actual affine coactions and their genuine scheme-morphism equations -/


universe u v w

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct

section Categorical

variable {C : Type u} {D : Type v} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {T Q A B : C}

/-- Naturality of the tensorator turns an actual algebra coaction
identity into the corresponding action identity after a monoidal functor. -/
theorem map_coaction_intertwining (r : T ⟶ Q) (f : B ⟶ A)
    (a : T ⊗ A ⟶ A) (b : Q ⊗ B ⟶ B)
    (h : T ◁ f ≫ a = r ▷ B ≫ b ≫ f) :
    F.obj T ◁ F.map f ≫ (Functor.LaxMonoidal.μ F T A ≫ F.map a) =
      F.map r ▷ F.obj B ≫ (Functor.LaxMonoidal.μ F Q B ≫ F.map b) ≫ F.map f := by
  rw [← Category.assoc,Functor.LaxMonoidal.μ_natural_right,Category.assoc,
    ← F.map_comp,h,F.map_comp,F.map_comp]
  rw [← Category.assoc,← Functor.LaxMonoidal.μ_natural_left,Category.assoc,Category.assoc]

end Categorical

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

section AffineMorphism

variable (k : Type u) [CommRing k]

/-- The actual morphism of affine schemes associated to a coaction. -/
def affineCoactionMorphism {T A : Type u} [CommRing T] [CommRing A]
    [Algebra k T] [Algebra k A] (d : A →ₐ[k] T ⊗[k] A) :
    ((Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k))) ⊗
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))) ⟶
        (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) :=
  Functor.LaxMonoidal.μ (algSpec (CommRingCat.of k))
      (op (CommAlgCat.of k T)) (op (CommAlgCat.of k A)) ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom d).op

end AffineMorphism

section Characters

variable (k : Type (max u v)) [CommRing k] {M : Type v} [AddCommGroup M]

/-- The coaction on the literal chart subalgebra, transported through its
proved semigroup-algebra equivalence. -/
def monoidChartCoaction (S : AddSubmonoid M) :
    monoidChartAlgebra k S →ₐ[k]
      AddMonoidAlgebra k M ⊗[k] monoidChartAlgebra k S :=
  (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M))
    (monoidChartAlgebraEquiv k S).toAlgHom).comp
      ((semigroupChartCoaction k S).comp (monoidChartAlgebraEquiv k S).symm.toAlgHom)

@[simp] theorem monoidChartCoaction_character (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    monoidChartCoaction k S (chartCharacter k S m hm) =
      AddMonoidAlgebra.single m 1 ⊗ₜ[k] chartCharacter k S m hm := by
  simp only [monoidChartCoaction,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character,semigroupChartCoaction_single,
    Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
    monoidChartAlgebraEquiv_single_character]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semigroupChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,semigroupChartOver k S] =
      affineCoactionMorphism k (semigroupChartCoaction k S) := by
  apply Over.OverMorphism.ext
  exact semigroupChart_action_spec k S

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported chart action really is the spectrum of the displayed
coaction on its actual coordinate subalgebra. -/
theorem monoidChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,monoidChartSchemeOver k S] =
      affineCoactionMorphism k (monoidChartCoaction k S) := by
  let F := algSpec (CommRingCat.of k)
  letI : F.LaxMonoidal :=
    (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal
  let T : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k M))
  let A : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (monoidChartAlgebra k S))
  let B : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k S))
  let e : A ⟶ B := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).toAlgHom).op
  let e' : B ⟶ A := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).symm.toAlgHom).op
  change (F.obj T ◁ F.map e) ≫
    γ[splitTorusOver k M,semigroupChartOver k S] ≫ F.map e' = _
  rw [semigroupChart_action_coaction]
  change (F.obj T ◁ F.map e) ≫
    (Functor.LaxMonoidal.μ F T B ≫ F.map
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op) ≫ F.map e' =
    Functor.LaxMonoidal.μ F T A ≫ F.map (CommAlgCat.ofHom (monoidChartCoaction k S)).op
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc F T e,
    ← F.map_comp,← F.map_comp]
  rfl

end Characters

section AffineIntertwining

variable (k : Type u) [CommRing k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A literal coaction equation gives a literal affine action equation. -/
theorem affineCoaction_intertwining
    {T Q A B : Type u} [CommRing T] [CommRing Q] [CommRing A] [CommRing B]
    [Algebra k T] [Algebra k Q] [Algebra k A] [Algebra k B]
    (r : Q →ₐ[k] T) (f : A →ₐ[k] B)
    (a : A →ₐ[k] T ⊗[k] A) (b : B →ₐ[k] Q ⊗[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k T) f).comp a =
      (Algebra.TensorProduct.map r (AlgHom.id k B)).comp (b.comp f)) :
    (Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k)) ◁
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ affineCoactionMorphism k a =
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom r).op ▷
        (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k))) ≫
      affineCoactionMorphism k b ≫
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op := by
  unfold affineCoactionMorphism
  apply map_coaction_intertwining (algSpec (CommRingCat.of k))
    (CommAlgCat.ofHom r).op (CommAlgCat.ofHom f).op
    (CommAlgCat.ofHom a).op (CommAlgCat.ofHom b).op
  exact congrArg (fun z => (CommAlgCat.ofHom z).op) h

end AffineIntertwining

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.monoidChart_action_coaction
end Source_ToricChartCoaction

section Source_ToricOrbitFacePullbacks




/-!
# Actual pullback squares for orbit charts

The denominator removing a smooth cone face has pairing zero on the
retained rays and pairing one on the removed rays. If the orbit cone is
retained, the denominator descends to precisely the quotient-star face
denominator. If an orbit ray is removed, that denominator is killed by
the orbit quotient, so the preimage of the face chart is empty.
-/


namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

variable {n : ℕ}

theorem integerPairing_neg (u m : Lattice n) :
    integerPairing u (-m) = -integerPairing u m := by
  simp [integerPairing]

theorem integerPairing_nsmul (u m : Lattice n) (N : ℕ) :
    integerPairing u (N • m) = (N : ℤ) * integerPairing u m := by
  simp only [integerPairing,Pi.smul_apply,nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem exists_face_character_denominator_exact
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (hts : t⊆s) :
    ∃ v : Lattice n, v∈dualConeMonoid s ∧ -v∈dualConeMonoid t ∧
      (∀ u∈s,integerPairing u v=if u∈t then 0 else 1) ∧
      (∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) := by
  obtain ⟨b,J,rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b=t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I⊆J := by
    intro i hi
    have hbi : b i∈t := hI ▸ Finset.mem_image.mpr ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  let v := faceDenominatorExponent (integralDualBasis b) I J
  refine ⟨v,?_,?_,?_,?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI,dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,faceDenominatorExponent_repr]
    have hbit : b i∈t ↔ i∈I := by simp [I,basisRayIndices]
    by_cases hiI : i∈I
    · simp [hiI,hbit.mpr hiI]
    · have hnot : b i∉t := fun h => hiI (hbit.mp h)
      simp [hi,hiI,hnot]
  · intro m hm
    rw [← hI,dualConeMonoid_basis_eq] at hm
    obtain ⟨N,hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N,(dualConeMonoid_basis_eq b J).symm ▸ hN⟩

end SmoothCompleteFan

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem projected_face_denominator
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t)
    (v : Lattice n) (hv : v∈dualConeMonoid s) (hnv : -v∈dualConeMonoid t)
    (hzero : ∀ u∈I.image b,integerPairing u v=0)
    (hclear : ∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) :
    faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) ∧
      -faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I t) ∧
      ∀ m∈dualConeMonoid (orbitQuotientCone b I t),∃ N : ℕ,
        m+N • faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) := by
  refine ⟨faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨v,hv⟩,hzero⟩,?_,?_⟩
  · have hzneg : ∀ u∈I.image b,integerPairing u (-v)=0 := by
      intro u hu
      rw [integerPairing_neg,hzero u hu,neg_zero]
    simpa only [map_neg] using
      faceCharacterProjection_mem_quotientDualCone b I t ⟨⟨-v,hnv⟩,hzneg⟩
  · intro m hm
    have hlift := faceTangentLattice_mem_dualCone b I t ⟨m,hm⟩
    obtain ⟨N,hN⟩ := hclear (faceTangentLattice b I m) hlift
    have hz : ∀ u∈I.image b,
        integerPairing u (faceTangentLattice b I m+N • v)=0 := by
      intro u hu
      rw [integerPairing_add,faceTangentLattice_annihilates b I m u hu,
        integerPairing_nsmul,hzero u hu,mul_zero,zero_add]
    have hproj := faceCharacterProjection_mem_quotientDualCone b I s
      ⟨⟨faceTangentLattice b I m+N • v,hN⟩,hz⟩
    exact ⟨N,by simpa only [map_add,map_nsmul,faceCharacterProjection_tangent] using hproj⟩

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]

theorem orbitQuotientChart_face_isPullback
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIt : I.image b⊆t) :
    IsPullback (orbitQuotientChartMap k b I t hIt)
      (coneChartFaceMap k (orbitQuotientCone_mono b I hts))
      (coneChartFaceMap k hts)
      (orbitQuotientChartMap k b I s (hIt.trans hts)) := by
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hzero : ∀ u∈I.image b,integerPairing u v=0 := by
    intro u hu
    rw [hpair u (hts (hIt hu)),if_pos (hIt hu)]
  obtain ⟨hp,hnp,hpclear⟩ := projected_face_denominator b I hts hIt v hv hnv hzero hclear
  let hloc := monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone hts)
    v hv hnv hclear
  let hploc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hnp hpclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hploc
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc
  letI : IsOpenImmersion (coneChartFaceMap k (orbitQuotientCone_mono b I hts)) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
      (faceCharacterProjection b I v) hp hploc
  apply IsOpenImmersion.isPullback
  · exact orbitQuotientChartMap_naturality k b I hts hIt
  · rw [show (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone hts) v hv hloc]
    rw [show (coneChartFaceMap k (orbitQuotientCone_mono b I hts)).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k
          (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
        (faceCharacterProjection b I v) hp hploc]
    change PrimeSpectrum.basicOpen
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)
          (chartCharacter k (dualConeMonoid s) v hv)) =
      PrimeSpectrum.basicOpen (chartCharacter k
        (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp)
    apply congrArg PrimeSpectrum.basicOpen
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_pos hzero]
    rfl

/-- A cone face omitting an orbit ray has empty preimage in the orbit
chart. This is proved by the literal denominator being mapped to zero. -/
theorem orbitQuotientChart_preimage_face_empty
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIs : I.image b⊆s) (hnot : ¬I.image b⊆t) :
    (orbitQuotientChartMap k b I s hIs) ⁻¹ᵁ
      ((coneChartFaceMap k hts).opensRange
        (H := «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts)) = ⊥ := by
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hnonzero : ¬∀ u∈I.image b,integerPairing u v=0 := by
    intro h
    apply hnot
    intro u hu
    by_contra hut
    have he := hpair u (hIs hu)
    rw [if_neg hut,h u hu] at he
    norm_num at he
  let hloc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hnv hclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  rw [show (coneChartFaceMap k hts).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
    monoidChartSpecMap_opensRange_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc]
  change PrimeSpectrum.basicOpen (orbitQuotientAlgebraMap k b I s hIs
    (chartCharacter k (dualConeMonoid s) v hv)) = ⊥
  have hmap : orbitQuotientAlgebraMap k b I s hIs
      (chartCharacter k (dualConeMonoid s) v hv)=0 := by
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_neg hnonzero]
    rfl
  rw [hmap,PrimeSpectrum.basicOpen_zero]

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_face_isPullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_preimage_face_empty
end Source_ToricOrbitFacePullbacks

section Source_ToricOrbitClosedImmersion




/-!
# The quotient-star scheme is an actual closed subscheme

The global map constructed from the actual semigroup quotient maps is a
closed immersion. Its pullback over a cone containing the orbit cone is
exactly the corresponding quotient chart, as a scheme-theoretic pullback.
Its preimage over every other cone is empty. These facts are proved from
the real fan intersection identity and the explicit localizations.
-/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbitChart_jointly_surjective
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k) :
    ∃ (s : «Σ».OrbitConeIndex b I) (y : coneChart k (orbitQuotientCone b I s.val)),
      («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) y=x := by
  obtain ⟨t,y,hy⟩ := («Σ».completeQuotientStarFan b I hF).fanChartMap_jointly_surjective k x
  obtain ⟨s,hs⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  subst t
  exact ⟨s,y,hy⟩

theorem orbitClosureMap_preimage_chart_empty (t : «Σ».ConeIndex)
    (hnot : ¬I.image b⊆t.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ («Σ».fanChartMap k t).opensRange = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
  obtain ⟨z,hz⟩ := hx
  have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
        (orbitQuotientChartMap k b I s.val s.property.2 y) = «Σ».fanChartMap k t z := by
    rw [← Scheme.Hom.comp_apply]
    rw [← «Σ».orbitClosureMap_chart k b I hF s]
    exact hz.symm
  obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
    ⟨s.val,s.property.1⟩ t _ z).mp heq
  letI : IsOpenImmersion
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val)) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s.val (s.val ∩ t.val)
      s.property.1 Finset.inter_subset_left
  have hface : orbitQuotientChartMap k b I s.val s.property.2 y∈
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange :=
    ⟨w,hws⟩
  have hnotInter : ¬I.image b⊆s.val∩t.val := fun h => hnot
    (h.trans Finset.inter_subset_right)
  have hempty := «Σ».orbitQuotientChart_preimage_face_empty b I k s.property.1
    (Finset.inter_subset_left : s.val∩t.val⊆s.val) s.property.2 hnotInter
  have hy : y∈(orbitQuotientChartMap k b I s.val s.property.2) ⁻¹ᵁ
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange := hface
  rw [hempty] at hy
  exact hy

theorem orbitClosureMap_preimage_chart (t : «Σ».OrbitConeIndex b I) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
        («Σ».fanChartMap k ⟨t.val,t.property.1⟩).opensRange =
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t)).opensRange := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  ext x
  constructor
  · intro hx
    obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
    obtain ⟨z,hz⟩ := hx
    have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
          (orbitQuotientChartMap k b I s.val s.property.2 y) =
        «Σ».fanChartMap k ⟨t.val,t.property.1⟩ z := by
      rw [← Scheme.Hom.comp_apply,← «Σ».orbitClosureMap_chart k b I hF s]
      exact hz.symm
    obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
      ⟨s.val,s.property.1⟩ ⟨t.val,t.property.1⟩ _ z).mp heq
    let u : «Σ».OrbitConeIndex b I :=
      ⟨s.val∩t.val,«Σ».downward s.val s.property.1 _ Finset.inter_subset_left,
        Finset.subset_inter s.property.2 t.property.2⟩
    have H := «Σ».orbitQuotientChart_face_isPullback b I k s.property.1
      (Finset.inter_subset_left : u.val⊆s.val) u.property.2
    letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val u.val
      s.property.1 Finset.inter_subset_left
    have hy : y∈Set.range (pullback.snd
        (coneChartFaceMap k (Finset.inter_subset_left : u.val⊆s.val))
        (orbitQuotientChartMap k b I s.val s.property.2)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨w,hws⟩
    obtain ⟨p,hp⟩ := hy
    let r := H.isoPullback.inv p
    have hr : coneChartFaceMap k
        (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val⊆s.val)) r = y :=
      (congrArg (fun f => f p) H.isoPullback_inv_snd).trans hp
    refine ⟨coneChartFaceMap k
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val⊆t.val)) r,?_⟩
    have htmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF t)
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val ⊆ t.val))
    have hsmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF s)
      (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val ⊆ s.val))
    exact (congrArg (fun f => f r) htmap).trans
      ((congrArg (fun f => f r) hsmap).symm.trans
        (congrArg (Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF s)) hr))
  · rintro ⟨y,rfl⟩
    refine ⟨orbitQuotientChartMap k b I t.val t.property.2 y,?_⟩
    exact (congrArg (fun f => f y) («Σ».orbitClosureMap_chart k b I hF t)).symm

/-- The quotient chart is the actual scheme-theoretic pullback of the
corresponding ambient chart. -/
theorem orbitClosureMap_chart_isPullback (t : «Σ».OrbitConeIndex b I) :
    IsPullback (orbitQuotientChartMap k b I t.val t.property.2)
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t))
      («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF) := by
  exact @IsOpenImmersion.isPullback
    (coneChart k (orbitQuotientCone b I t.val)) (coneChart k t.val)
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k) («Σ».fanScheme k)
    (orbitQuotientChartMap k b I t.val t.property.2)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap_isOpenImmersion k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap_isOpenImmersion k ⟨t.val,t.property.1⟩)
    («Σ».orbitClosureMap_chart k b I hF t)
    («Σ».orbitClosureMap_preimage_chart k b I hF t)

/-- Closedness is checked on the actual ambient affine open cover. -/
instance orbitClosureMap_isClosedImmersion :
    IsClosedImmersion («Σ».orbitClosureMap k b I hF) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    («Σ».fanSchemeOpenCover k)]
  intro t
  let t₀ : «Σ».ConeIndex := t
  letI : IsOpenImmersion («Σ».fanChartMap k t₀) :=
    «Σ».fanChartMap_isOpenImmersion k t₀
  change IsClosedImmersion
    (pullback.snd («Σ».orbitClosureMap k b I hF) («Σ».fanChartMap k t₀))
  by_cases hIt : I.image b ⊆ t₀.val
  · let t' : «Σ».OrbitConeIndex b I := ⟨t₀.val, t₀.property, hIt⟩
    have H := «Σ».orbitClosureMap_chart_isPullback k b I hF t'
    have hc : IsClosedImmersion
        (H.flip.isoPullback.inv ≫ orbitQuotientChartMap k b I t'.val t'.property.2) :=
      inferInstance
    exact Eq.mp (congrArg (fun f => IsClosedImmersion f) H.flip.isoPullback_inv_snd) hc
  · letI : IsEmpty ↥(pullback («Σ».orbitClosureMap k b I hF)
        («Σ».fanChartMap k t₀) : Scheme) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro x ⟨y,rfl⟩ hx
      have hy : y∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
          («Σ».fanChartMap k t₀).opensRange := hx
      rw [«Σ».orbitClosureMap_preimage_chart_empty k b I hF t₀ hIt] at hy
      exact hy
    infer_instance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_isClosedImmersion
end Source_ToricOrbitClosedImmersion

section Source_ToricOrbitActions




/-!
# Genuine torus invariance of the actual orbit closed immersion

The quotient torus is acted on through the homomorphism induced by the
saturated inclusion of its character lattice. The chart quotient kills
exactly the characters positive on the orbit cone. Its displayed coaction
identity is transported to actual affine schemes and then glued along the
actual open cover. The resulting equivariance is an equality of morphisms
over Spec(k), including arbitrary test schemes.
-/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped TensorProduct

variable {n : ℕ} (k : Type u) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

/-- The actual pullback of characters along the quotient-torus map. -/
def orbitTorusCharacterMap :
    AddMonoidAlgebra k (Lattice (n-I.card)) →ₐ[k] AddMonoidAlgebra k (Lattice n) :=
  (AddMonoidAlgebra.mapDomainBialgHom k
    (faceTangentLattice b I).toAddMonoidHom).toAlgHom

@[simp] theorem orbitTorusCharacterMap_single (m : Lattice (n-I.card)) (a : k) :
    orbitTorusCharacterMap k b I (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single (faceTangentLattice b I m) a :=
  AddMonoidAlgebra.mapDomainBialgHom_single (R := k) _ m a

/-- The quotient map of actual split group schemes. -/
def orbitTorusMapOver :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      ToricSchemes.splitTorusOver k (Lattice (n-I.card)) :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitTorusCharacterMap k b I)).op

instance orbitTorusMapOver_isMonHom : IsMonHom (orbitTorusMapOver k b I) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (faceTangentLattice b I).toAddMonoidHom)).op).hom)
  infer_instance

/-- The quotient of a chart commutes with the genuine character
coactions, including the characters sent to zero. -/
theorem orbitQuotientAlgebraMap_coaction
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (Algebra.TensorProduct.map
        (AlgHom.id k (AddMonoidAlgebra k (Lattice n)))
        (orbitQuotientAlgebraMap k b I s hIs)).comp
      (monoidChartCoaction k (dualConeMonoid s)) =
    (Algebra.TensorProduct.map (orbitTorusCharacterMap k b I)
        (AlgHom.id k (monoidChartAlgebra k
          (dualConeMonoid (orbitQuotientCone b I s))))).comp
      ((monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))).comp
        (orbitQuotientAlgebraMap k b I s hIs)) := by
  classical
  apply chartAlgHom_ext_characters
  intro m hm
  by_cases hann : ∀ u∈I.image b,integerPairing u m=0
  · have hproj : faceCharacterProjection b I m∈
        dualConeMonoid (orbitQuotientCone b I s) :=
      faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨m,hm⟩,hann⟩
    have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) =
          chartCharacter k (dualConeMonoid (orbitQuotientCone b I s))
            (faceCharacterProjection b I m) hproj := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_pos hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,
      orbitTorusCharacterMap_single,faceTangentLattice_projection b I m hann]
  · have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) = 0 := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_neg hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,map_zero,
      TensorProduct.tmul_zero]

instance orbitQuotientChartMap_isOver
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (orbitQuotientChartMap k b I s hIs).IsOver (Spec (CommRingCat.of k)) := by
  exact ⟨((algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op).w⟩

/-- The actual affine orbit chart map intertwines the two group-scheme
actions through the actual quotient-torus homomorphism. -/
theorem orbitQuotientChartMap_action
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        (coneChart k s).asOver (Spec (CommRingCat.of k))] =
    orbitTorusMapOver k b I ▷
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k))] ≫
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) := by
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let U := monoidChartSchemeOver k (dualConeMonoid (orbitQuotientCone b I s))
  let V := monoidChartSchemeOver k (dualConeMonoid s)
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let q : U ⟶ V := (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op
  change G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q
  have h₁ : G ◁ q ≫ γ[G,V] = G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) :=
    congrArg (fun h : G ⊗ V ⟶ V => G ◁ q ≫ h)
      (monoidChart_action_coaction k (dualConeMonoid s))
  have h₂ : G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) =
      ρ ▷ U ≫ affineCoactionMorphism k
        (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q :=
    affineCoaction_intertwining k (orbitTorusCharacterMap k b I)
      (orbitQuotientAlgebraMap k b I s hIs)
      (monoidChartCoaction k (dualConeMonoid s))
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s)))
      (orbitQuotientAlgebraMap_coaction k b I s hIs)
  have h₃ : ρ ▷ U ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q =
      ρ ▷ U ≫ γ[Q,U] ≫ q :=
    congrArg (fun h : Q ⊗ U ⟶ U => ρ ▷ U ≫ h ≫ q)
      (monoidChart_action_coaction k
        (dualConeMonoid (orbitQuotientCone b I s))).symm
  exact h₁.trans (h₂.trans h₃)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

instance orbitClosureMap_isOver :
    («Σ».orbitClosureMap k b I hF).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    apply ((«Σ».completeQuotientStarFan b I hF).fanSchemeOpenCover k).hom_ext
    intro t
    obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
    let U := coneChart k (orbitQuotientCone b I s.val)
    let V := coneChart k s.val
    let Z := («Σ».completeQuotientStarFan b I hF).fanScheme k
    let j : U ⟶ Z := («Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF s)
    let i : V ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨s.val,s.property.1⟩
    let q : U ⟶ V := orbitQuotientChartMap k b I s.val s.property.2
    let f : Z ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
    have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart k b I hF s
    have hjbase : j ≫ (Z ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)) (Spec (CommRingCat.of k))
    have hibase : i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) =
        (V ↘ Spec (CommRingCat.of k)) :=
      comp_over («Σ».fanChartMap k ⟨s.val,s.property.1⟩) (Spec (CommRingCat.of k))
    have hqbase : q ≫ (V ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over (orbitQuotientChartMap k b I s.val s.property.2) (Spec (CommRingCat.of k))
    change j ≫ (f ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) =
      j ≫ (Z ↘ Spec (CommRingCat.of k))
    calc
      _ = (j ≫ f) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        (Category.assoc _ _ _).symm
      _ = (q ≫ i) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : U ⟶ «Σ».fanScheme k =>
          h ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) hj
      _ = q ≫ (i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) :=
        Category.assoc _ _ _
      _ = q ≫ (V ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : V ⟶ Spec (CommRingCat.of k) => q ≫ h) hibase
      _ = (U ↘ Spec (CommRingCat.of k)) := hqbase
      _ = _ := hjbase.symm

@[reassoc] theorem orbitClosureMap_chart_over (s : «Σ».OrbitConeIndex b I) :
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) =
    (orbitQuotientChartMap k b I s.val s.property.2).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver (Spec (CommRingCat.of k)) := by
  apply Over.OverMorphism.ext
  exact «Σ».orbitClosureMap_chart k b I hF s

/-- The actual orbit closed immersion is equivariant. This statement
holds as an equality over Spec(k), not only on rational points. -/
theorem orbitClosureMap_action :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] =
    orbitTorusMapOver k b I ▷
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k] ≫
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let X := Γ.fanSchemeOver k
  let Y := «Σ».fanSchemeOver k
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let f : X ⟶ Y := («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))
  apply tensorCover_hom_ext (Γ.fanSchemeOpenCover k) G Y
  intro t
  obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  let U := monoidChartSchemeOver k
    (dualConeMonoid (orbitQuotientCone b I s.val))
  let V := monoidChartSchemeOver k (dualConeMonoid s.val)
  let j : U ⟶ X := (Γ.fanChartMap k
    («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k))
  let i : V ⟶ Y := («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver
    (Spec (CommRingCat.of k))
  let q : U ⟶ V := (orbitQuotientChartMap k b I s.val s.property.2).asOver
    (Spec (CommRingCat.of k))
  letI : IsModHom G i := «Σ».fanChartMap_isModHom k ⟨s.val,s.property.1⟩
  letI : IsModHom Q j := Γ.fanChartMap_isModHom k
    («Σ».orbitConeQuotientIndex b I hF s)
  have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart_over k b I hF s
  have hi_action : γ[G,V] ≫ i = G ◁ i ≫ γ[G,Y] :=
    IsModHom.smul_hom (A := G) (f := i)
  have hj_action : γ[Q,U] ≫ j = Q ◁ j ≫ γ[Q,X] :=
    IsModHom.smul_hom (A := Q) (f := j)
  have hq_action : G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q :=
    orbitQuotientChartMap_action k b I s.val s.property.2
  change G ◁ j ≫ (G ◁ f ≫ γ[G,Y]) =
    G ◁ j ≫ (ρ ▷ X ≫ γ[Q,X] ≫ f)
  calc
    _ = (G ◁ j ≫ G ◁ f) ≫ γ[G,Y] := (Category.assoc _ _ _).symm
    _ = G ◁ (j ≫ f) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G j f).symm
    _ = G ◁ (q ≫ i) ≫ γ[G,Y] :=
      congrArg (fun h : U ⟶ Y => G ◁ h ≫ γ[G,Y]) hj
    _ = (G ◁ q ≫ G ◁ i) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G q i)
    _ = G ◁ q ≫ (G ◁ i ≫ γ[G,Y]) := Category.assoc _ _ _
    _ = G ◁ q ≫ (γ[G,V] ≫ i) :=
      congrArg (fun h : G ⊗ V ⟶ Y => G ◁ q ≫ h) hi_action.symm
    _ = (G ◁ q ≫ γ[G,V]) ≫ i := (Category.assoc _ _ _).symm
    _ = (ρ ▷ U ≫ γ[Q,U] ≫ q) ≫ i :=
      congrArg (fun h : G ⊗ U ⟶ V => h ≫ i) hq_action
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (q ≫ i) := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (j ≫ f) :=
      congrArg (fun h : U ⟶ Y => ρ ▷ U ≫ γ[Q,U] ≫ h) hj.symm
    _ = ρ ▷ U ≫ (γ[Q,U] ≫ j) ≫ f := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ (Q ◁ j ≫ γ[Q,X]) ≫ f :=
      congrArg (fun h : Q ⊗ U ⟶ X => ρ ▷ U ≫ h ≫ f) hj_action
    _ = (ρ ▷ U ≫ Q ◁ j) ≫ γ[Q,X] ≫ f := by simp only [Category.assoc]
    _ = (G ◁ j ≫ ρ ▷ X) ≫ γ[Q,X] ≫ f :=
      congrArg (fun h : G ⊗ U ⟶ Q ⊗ X => h ≫ γ[Q,X] ≫ f)
        (whisker_exchange ρ j).symm
    _ = _ := by simp only [Category.assoc]

/-- The original torus acts on the quotient-star scheme through its
actual quotient homomorphism. Kept explicit to avoid competing instances
for the quotient torus's own action. -/
def orbitClosureSourceAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k) :=
  Mod.scalarRestriction (orbitTorusMapOver k b I)
    ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k)

/-- The already-proved closed immersion identifies an invariant closed
subscheme, with invariance witnessed by an actual group-scheme action. -/
theorem orbitClosureMap_equivariant :
    letI := «Σ».orbitClosureSourceAction k b I hF
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))) := by
  letI := «Σ».orbitClosureSourceAction k b I hF
  constructor
  exact («Σ».orbitClosureMap_action k b I hF).symm

end SmoothCompleteFan
end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_action
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_equivariant
end Source_ToricOrbitActions

section Source_ToricQuotientFaceSupport




/-!
# Support functions on the actual saturated quotient star

Every projected star ray has one actual primitive lift. Restriction support
is the original coefficient plus the value of the chosen affine origin on
that lift. The linear support functions factor through the saturated
quotient, proving both nefness and strict support on the actual quotient
fan. The affine image of its polytope is proved to be the original face.
-/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem exists_starRayLift
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ v : Lattice n, ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      v ∈ s \ I.image b ∧ coneQuotientLattice b I v = u := by
  obtain ⟨t, ht, hut⟩ := ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff u).mp u.property
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  rw [hts] at hut
  obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hut
  exact ⟨v, s, hs, hFs, hv, hvu⟩

def starRayLift (u : («Σ».completeQuotientStarFan b I hF).rays) : Lattice n :=
  Classical.choose («Σ».exists_starRayLift b I hF u)

theorem starRayLift_spec (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      «Σ».starRayLift b I hF u ∈ s \ I.image b ∧
      coneQuotientLattice b I («Σ».starRayLift b I hF u) = u :=
  Classical.choose_spec («Σ».exists_starRayLift b I hF u)

theorem projected_starRay_mem {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    coneQuotientLattice b I v ∈ («Σ».completeQuotientStarFan b I hF).rays := by
  apply ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff _).mpr
  refine ⟨(s \ I.image b).image (coneQuotientLattice b I), ?_,
    Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  exact («Σ».mem_quotientStarCones b I _).mpr ⟨s, hs, hFs, rfl⟩

theorem starRayLift_projected {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».starRayLift b I hF ⟨coneQuotientLattice b I v,
      «Σ».projected_starRay_mem b I hF hs hFs hv⟩ = v := by
  obtain ⟨t, ht, hFt, hwt, hwp⟩ := «Σ».starRayLift_spec b I hF
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  exact «Σ».coneQuotient_injective_star_rays b I ht hs hFt hFs hwt hv hwp

/-- The actual restriction coefficient on each quotient primitive ray.
Values outside the ray set are irrelevant and are fixed to zero. -/
def faceSupport (a : Lattice n → ℝ) : Lattice (n - I.card) → ℝ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF ⟨u, hu⟩)))
        (quotientFaceOrigin a b I)
  else 0

theorem faceSupport_lift (a : Lattice n → ℝ)
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    «Σ».faceSupport b I hF a u = a («Σ».starRayLift b I hF u) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF u)))
        (quotientFaceOrigin a b I) := by
  simp only [faceSupport, dif_pos u.property]

theorem faceSupport_projected (a : Lattice n → ℝ)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hFs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».faceSupport b I hF a (coneQuotientLattice b I v) =
      a v + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
  have h := «Σ».faceSupport_lift b I hF a
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  rw [«Σ».starRayLift_projected b I hF hs hFs hv] at h
  exact h

theorem quotientFaceMap_pairing (a : Lattice n → ℝ)
    (u : Lattice n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) =
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceOrigin a b I) +
      (dotProductEquiv ℝ (Fin (n - I.card)) (embed (n - I.card)
        (coneQuotientLattice b I u))) x := by
  rw [quotientFaceMap_apply, map_add, faceTangentReal_pairing, coneQuotient_compatible]

/-- Original linear support, shifted by the affine origin, factors through
the normal quotient. -/
theorem face_linear_support_factors (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ i ∈ I, ℓ (embed n (b i)) = a (b i)) :
    ∀ u : Ambient n,
      ((ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)).comp
        (coneQuotientSectionReal b I)) (coneQuotientReal b I u) =
      ℓ u + (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) u := by
  intro u
  apply linear_face_factorization b I
    (ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) ?_ u
  intro i hi
  simp only [LinearMap.add_apply, integralBasisReal_apply, he i hi]
  have hp : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
      -a (b i) := by
    have hcomm : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceOrigin a b I) := by
      change quotientFaceOrigin a b I ⬝ᵥ embed n (b i) =
        embed n (b i) ⬝ᵥ quotientFaceOrigin a b I
      exact dotProduct_comm _ _
    rw [hcomm, normal_pairing_eq_dual_coordinate,
      quotientFaceOrigin_coordinate, if_pos hi]
  rw [hp, add_neg_cancel]

/-- Nefness restricts to the genuine saturated quotient-star fan. -/
theorem faceSupport_isNef (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    («Σ».completeQuotientStarFan b I hF).IsNef («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hbound := hle («Σ».starRayLift b I hF u') hvray
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_le ((add_le_add hbound le_rfl).trans_eq hsupp.symm)

/-- Strict support restricts as well: no extra quotient-ray coincidence is
assumed, since uniqueness of actual primitive lifts was proved above. -/
theorem faceSupport_isStrictSupport (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) :
    («Σ».completeQuotientStarFan b I hF).IsStrictSupport («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu hut
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hvnot : «Σ».starRayLift b I hF u' ∉ s := by
      intro hvs
      apply hut
      rw [hts]
      exact Finset.mem_image.mpr ⟨«Σ».starRayLift b I hF u',
        Finset.mem_sdiff.mpr ⟨hvs, (Finset.mem_sdiff.mp hv).2⟩, hproj⟩
    have hbound := hlt («Σ».starRayLift b I hF u') hvray hvnot
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_lt ((add_lt_add_of_lt_of_le hbound le_rfl).trans_eq hsupp.symm)

/-- A full cone of the quotient star is the projection of a full original
cone containing the deleted cone. The dimension assertion is a consequence
of the already proved injectivity of primitive ray projection. -/
theorem exists_fullCone_lift
    (t : («Σ».completeQuotientStarFan b I hF).fullCones) :
    ∃ s : «Σ».fullCones, I.image b ⊆ (s : Finset (Lattice n)) ∧
      (t : Finset (Lattice (n - I.card))) =
        ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I) := by
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp
    ((«Σ».completeQuotientStarFan b I hF).fullCones_mem t)
  have hcard := («Σ».completeQuotientStarFan b I hF).fullCones_card t
  have himage : ((s \ I.image b).image (coneQuotientLattice b I)).card =
      (s \ I.image b).card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hs hs hFs hFs hv hw he
  have hIcard : (I.image b).card = I.card := Finset.card_image_of_injective I b.injective
  have hIs : I.card ≤ s.card := by
    rw [← hIcard]
    exact Finset.card_le_card hFs
  have hIn : I.card ≤ n := hIs.trans («Σ».card_cone_le hs)
  rw [hts, himage, Finset.card_sdiff_of_subset hFs, hIcard] at hcard
  have hsn : s.card = n := by omega
  exact ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hsn⟩⟩, hFs, hts⟩

/-- The quotient Cartier point maps to the original Cartier point in every
full lifted chart. This is an equality of actual vectors. -/
theorem quotientFaceMap_cartierPoint (a : Lattice n → ℝ)
    (t : («Σ».completeQuotientStarFan b I hF).fullCones)
    (s : «Σ».fullCones) (hFs : I.image b ⊆ (s : Finset (Lattice n)))
    (hts : (t : Finset (Lattice (n - I.card))) =
      ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I)) :
    quotientFaceMap a b I
        ((«Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t) =
      «Σ».cartierPoint a s := by
  let x := («Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t
  have hactive (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) = -a u := by
    by_cases huF : u ∈ I.image b
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huF
      exact quotientFaceMap_active a b I x i hi
    · have hut : coneQuotientLattice b I u ∈ (t : Finset (Lattice (n - I.card))) := by
        rw [hts]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huF⟩, rfl⟩
      have hq := («Σ».completeQuotientStarFan b I hF).cartierPoint_support_eq
        («Σ».faceSupport b I hF a) t hut
      rw [«Σ».faceSupport_projected b I hF a («Σ».fullCones_mem s) hFs
        (Finset.mem_sdiff.mpr ⟨hu, huF⟩)] at hq
      rw [quotientFaceMap_pairing]
      change _ + (dotProductEquiv ℝ (Fin (n - I.card))
        (embed (n - I.card) (coneQuotientLattice b I u))) x = _
      rw [hq]
      ring
  apply (integralBasisReal (integralDualBasis («Σ».fullConeBasis s))).ext_elem
  intro i
  rw [← normal_pairing_eq_dual_coordinate, ← normal_pairing_eq_dual_coordinate]
  have hi : «Σ».fullConeBasis s i ∈ (s : Finset (Lattice n)) := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [hactive _ hi, «Σ».cartierPoint_support_eq a s hi]

/-- The exact saturated face dictionary, including nef degenerate faces.
No extra inequality is discarded: containment in the original polytope is
proved first on all quotient Cartier points and then on their convex hull. -/
theorem quotientFaceMap_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    quotientFaceMap a b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope («Σ».faceSupport b I hF a) =
      «Σ».supportFace a (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hΨnef : Ψ.IsNef («Σ».faceSupport b I hF a) :=
    «Σ».faceSupport_isNef b I hF a ha
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hcontain : Ψ.fanPolytope («Σ».faceSupport b I hF a) ⊆
        quotientFaceMap a b I ⁻¹' «Σ».supportFace a (I.image b) := by
      rw [Ψ.fanPolytope_eq_convexHull_cartier hΨpure _ hΨnef]
      apply convexHull_min
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hFs, hts⟩ := «Σ».exists_fullCone_lift b I hF t
        change quotientFaceMap a b I
          (Ψ.cartierPoint («Σ».faceSupport b I hF a) t) ∈ «Σ».supportFace a (I.image b)
        rw [«Σ».quotientFaceMap_cartierPoint b I hF a t s hFs hts]
        exact ⟨«Σ».cartierPoint_mem_of_nef ha s,
          fun u hu => «Σ».cartierPoint_support_eq a s (hFs hu)⟩
      · exact Convex.affine_preimage _ («Σ».convex_supportFace a (I.image b))
    exact hcontain hy
  · intro x hx
    have hactive : ∀ i ∈ I,
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) :=
      fun i hi => hx.2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨y, rfl⟩ := (mem_range_quotientFaceMap_iff a b I x).mpr hactive
    refine ⟨y, ?_, rfl⟩
    intro u hu
    let u' : Ψ.rays := ⟨u, hu⟩
    obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
    have hbound := hx.1 («Σ».starRayLift b I hF u') hvray
    rw [quotientFaceMap_pairing, hproj] at hbound
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    change -«Σ».faceSupport b I hF a u ≤ _
    rw [hsupp]
    linarith

/-- Integral restriction coefficients use the actual integral affine
origin and the actual primitive lifts. -/
def faceSupportLattice (a : Lattice n → ℤ) : Lattice (n - I.card) → ℤ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      ∑ i, («Σ».starRayLift b I hF ⟨u, hu⟩) i * quotientFaceOriginLattice a b I i
  else 0

theorem faceSupportLattice_cast (a : Lattice n → ℤ) :
    (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».faceSupport b I hF (fun u => (a u : ℝ)) := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupportLattice, faceSupport, dif_pos hu, Int.cast_add]
    rw [← embed_quotientFaceOrigin, normalRay_pairing_lattice]
  · simp only [faceSupportLattice, faceSupport, dif_neg hu, Int.cast_zero]

theorem quotientFaceIntegralChart_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsNef (fun u => (a u : ℝ))) :
    (quotientFaceIntegralChart a b I).realMap ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  rw [quotientFaceIntegralChart_realMap, «Σ».faceSupportLattice_cast]
  exact «Σ».quotientFaceMap_image_fanPolytope b I hF hpure _ ha

end PaperVerification.ToricGeometry.SmoothCompleteFan
end Source_ToricQuotientFaceSupport

section Source_ToricOrbitCartierCoefficients




/-!
# Cartier equations on an actual quotient-star orbit closure

A common integral character is used to normalize all local generators
along the orbit cone. The normalized characters lie in its actual
annihilator lattice. Their projections are proved to be the Cartier
characters of the quotient fan, and actual transition units are mapped
by the previously constructed surjective chart homomorphisms.
-/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

def orbitRestrictionCoefficients (a : Lattice n→ℤ) (m₀ : Lattice n) :
    Lattice (n-I.card)→ℤ := fun u =>
  if hu : u∈(«Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u,hu⟩)+
      integerPairing («Σ».starRayLift b I hF ⟨u,hu⟩) m₀
  else 0

theorem orbitRestrictionCoefficients_projected (a : Lattice n→ℤ) (m₀ : Lattice n)
    {s : Finset (Lattice n)} (hs : s∈«Σ».cones) (hIs : I.image b⊆s)
    {u : Lattice n} (hu : u∈s\I.image b) :
    «Σ».orbitRestrictionCoefficients b I hF a m₀ (coneQuotientLattice b I u) =
      a u+integerPairing u m₀ := by
  have hp := «Σ».projected_starRay_mem b I hF hs hIs hu
  simp only [orbitRestrictionCoefficients,dif_pos hp]
  rw [«Σ».starRayLift_projected b I hF hs hIs hu]

def orbitFullConeIndex (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».completeQuotientStarFan b I hF).fullCones :=
  ⟨orbitQuotientCone b I s.val,Finset.mem_filter.mpr ⟨
    («Σ».mem_quotientStarCones b I _).mpr ⟨s.val,«Σ».fullCones_mem s,hIs,rfl⟩,by
      have himage : (orbitQuotientCone b I s.val).card=(s.val\I.image b).card := by
        apply Finset.card_image_of_injOn
        intro v hv w hw he
        exact «Σ».coneQuotient_injective_star_rays b I
          («Σ».fullCones_mem s) («Σ».fullCones_mem s) hIs hIs hv hw he
      rw [himage,Finset.card_sdiff_of_subset hIs,
        Finset.card_image_of_injective I b.injective,«Σ».fullCones_card]⟩⟩

theorem orbit_normalized_character_annihilates (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    ∀ u∈I.image b,integerPairing u («Σ».cartierLatticePoint a s-m₀)=0 := by
  intro u hu
  rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),hm₀ u hu,sub_self]

/-- Projected local equations are uniquely the actual Cartier equations
of the quotient fan. -/
theorem orbit_cartierLatticePoint (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-m₀) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀)
        («Σ».orbitFullConeIndex b I hF s hIs) := by
  apply («Σ».completeQuotientStarFan b I hF).eq_cartierLatticePoint_of_pairings
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I _
      («Σ».orbit_normalized_character_annihilates b I a m₀ hm₀ s hIs),
    integerPairing_sub,
    «Σ».cartierLatticePoint_pairing a s u (Finset.mem_sdiff.mp hu).1,
    «Σ».orbitRestrictionCoefficients_projected b I hF a m₀ («Σ».fullCones_mem s) hIs hu]
  ring

theorem orbit_cartier_difference (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF s hIs) -
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF t hIt) := by
  rw [← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ s hIs,
    ← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ t hIt,← map_sub]
  congr 1
  abel

theorem orbitQuotientCone_inter (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I (s.val∩t.val) =
      orbitQuotientCone b I s.val∩orbitQuotientCone b I t.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_sdiff.mp hu with ⟨hut,huI⟩
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).1,huI⟩,rfl⟩,
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).2,huI⟩,rfl⟩⟩
  · intro hv
    obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
    have huw := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
      s.property.2 t.property.2 hu hw (huv.trans hwv.symm)
    subst w
    exact Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1,(Finset.mem_sdiff.mp hw).1⟩,
        (Finset.mem_sdiff.mp hu).2⟩,huv⟩

variable (k : Type*) [CommRing k]

/-- The exact regular transition character is sent to its projected
character by the actual closed-immersion chart algebra homomorphism. -/
theorem orbit_cartierTransition_character (a : Lattice n→ℤ)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
      («Σ».cartierTransitionUnit k a s t :
        monoidChartAlgebra k (dualConeMonoid (s.val∩t.val)))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      AddMonoidAlgebra.single
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) 1 := by
  have hz : ∀ u∈I.image b,
      integerPairing u («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)=0 := by
    intro u hu
    rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),
      «Σ».cartierLatticePoint_pairing a t u (hIt hu),sub_self]
  change ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
    (chartCharacter k (dualConeMonoid (s.val∩t.val))
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1)) :
        AddMonoidAlgebra k (Lattice (n-I.card))) = _
  rw [orbitQuotientAlgebraMap_character,dif_pos hz]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierLatticePoint
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierTransition_character
end Source_ToricOrbitCartierCoefficients

section Source_ToricWallCurves




/-!
# Actual invariant curves associated to fan walls

Deleting one primitive generator from a full smooth cone gives an
actual quotient-star scheme. Its map into the fan scheme is the
previously constructed closed immersion. The quotient has rank one,
so its scheme is isomorphic to the actual two-chart projective line
and has ordinary topological Krull dimension one.
-/


universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open MonoidalCategory MonObj
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

def wallIndices (_s : «Σ».fullCones) (j : Fin n) : Finset (Fin n) := Finset.univ.erase j

theorem wallIndices_codimension : n-(«Σ».wallIndices s j).card=1 := by
  simp only [wallIndices,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_fin]
  have hn := j.isLt
  omega

theorem wallCone_mem :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)∈«Σ».cones := by
  apply «Σ».downward s.val («Σ».fullCones_mem s)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

def wallCurveFan : SmoothCompleteFan (n-(«Σ».wallIndices s j).card) :=
  «Σ».completeQuotientStarFan («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

variable (k : Type u) [Field k]

def wallCurve : Scheme.{u} := («Σ».wallCurveFan s j).fanScheme k

def wallCurveInclusion : «Σ».wallCurve s j k ⟶ «Σ».fanScheme k :=
  «Σ».orbitClosureMap k («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurveInclusion_isClosedImmersion :
    IsClosedImmersion («Σ».wallCurveInclusion s j k) := by
  exact «Σ».orbitClosureMap_isClosedImmersion k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurve_isIntegral : IsIntegral («Σ».wallCurve s j k) :=
  inferInstanceAs (IsIntegral ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isNoetherian : IsNoetherian («Σ».wallCurve s j k) :=
  inferInstanceAs (IsNoetherian ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isOver : («Σ».wallCurve s j k).Over (Spec (.of k)) :=
  inferInstanceAs (((«Σ».wallCurveFan s j).fanScheme k).Over (Spec (.of k)))

instance wallCurveInclusion_isOver :
    («Σ».wallCurveInclusion s j k).IsOver (Spec (.of k)) :=
  inferInstanceAs ((«Σ».orbitClosureMap k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)).IsOver (Spec (.of k)))

def wallCurveProjectiveLineIso : «Σ».wallCurve s j k ≅ projectiveLineScheme k :=
  oneDimensionalFanSchemeIso («Σ».wallCurveFan s j) («Σ».wallIndices_codimension s j) k

theorem wallCurve_dimension : topologicalKrullDim («Σ».wallCurve s j k)=1 := by
  have h := IsHomeomorph.topologicalKrullDim_eq
    (fun x => («Σ».wallCurveProjectiveLineIso s j k).hom x)
    («Σ».wallCurveProjectiveLineIso s j k).hom.homeomorph.isHomeomorph
  exact h.trans (projectiveLine_topologicalKrullDim k)

/-- The actual group-scheme equivariance identity is inherited from the
closed orbit immersion; it is stronger than invariance of rational points. -/
theorem wallCurve_equivariant :
    letI : ModObj (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
        ((«Σ».wallCurve s j k).asOver (Spec (.of k))) :=
      «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
        («Σ».wallIndices s j) («Σ».wallCone_mem s j)
    IsModHom (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».wallCurveInclusion s j k).asOver (Spec (.of k))) :=
  «Σ».orbitClosureMap_equivariant k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_dimension
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_equivariant
end Source_ToricWallCurves

section Source_ToricAffinePullbackSections




/-!
# Pulling regular functions through an actual affine chart square

This argument does not require dominance. A function which is regular
on an ambient affine chart pulls back through its actual coordinate-ring
homomorphism. The conclusion is expressed in the function field of the
source only after pulling back the regular section.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l]

/-- The actual regular function on the image of an affine chart. -/
def affineChartSection (r : R) : Γ(X,j ''ᵁ (⊤ : (Spec R).Opens)) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)

theorem affineChartSection_germ
    [Nonempty (j ''ᵁ (⊤ : (Spec R).Opens))] (r : R) :
    X.germToFunctionField (j ''ᵁ (⊤ : (Spec R).Opens))
      (affineChartSection R j r) = affineOpenCoordinateMap R j r :=
  (openImmersionRegularToFunctionField_eq_germ_image j ⊤
    ((Scheme.ΓSpecIso R).inv r)).symm

variable (f : Y ⟶ X) (φ : R ⟶ S)
    (hcomm : l ≫ f = Spec.map φ ≫ j)

include hcomm in
theorem affineChartSquare_image_le :
    l ''ᵁ (⊤ : (Spec S).Opens) ≤ f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) := by
  rintro y ⟨q,hq,rfl⟩
  exact ⟨Spec.map φ q,trivial,
    (congrArg (fun g : Spec S ⟶ X=>g q) hcomm).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem affineChartSquare_sections :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
        (affineChartSquare_image_le R S j l f φ hcomm) ≫ (l.appIso ⊤).hom =
      (j.appIso ⊤).hom ≫ (Spec.map φ).appTop := by
  rw [l.appIso_hom',j.appIso_hom']
  change f.appLE _ _ _ ≫ l.appLE _ ⊤ _ =
    j.appLE _ ⊤ _ ≫ (Spec.map φ).appLE ⊤ ⊤ le_top
  rw [Scheme.Hom.appLE_comp_appLE,Scheme.Hom.appLE_comp_appLE]
  have hc {a b : Spec S ⟶ X} (hab : a = b)
      (ha : (⊤ : (Spec S).Opens) ≤ a ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)))
      (hb : (⊤ : (Spec S).Opens) ≤ b ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))) :
      a.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ ha =
        b.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ hb := by
    cases hab
    rfl
  have ha : (⊤ : (Spec S).Opens) ≤ (l ≫ f) ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) :=
    (l.preimage_image_eq ⊤).ge.trans
      (l.preimage_mono (affineChartSquare_image_le R S j l f φ hcomm))
  exact hc hcomm ha (hcomm ▸ ha)

/-- Equality of genuine regular sections on the source chart image. -/
theorem affineChartSection_pullback (r : R) :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
      (affineChartSquare_image_le R S j l f φ hcomm)
      (affineChartSection R j r) = affineChartSection S l (φ r) := by
  apply (l.appIso ⊤).commRingCatIsoToRingEquiv.injective
  calc
    (l.appIso ⊤).hom
        (f.appLE _ _ (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j r)) =
      (Spec.map φ).appTop ((j.appIso ⊤).hom (affineChartSection R j r)) :=
        congrArg (fun g=>g (affineChartSection R j r))
          (affineChartSquare_sections R S j l f φ hcomm)
    _ = (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]
    _ = (Scheme.ΓSpecIso S).inv (φ r) :=
      (congrArg (fun g=>g r) (Scheme.ΓSpecIso_inv_naturality φ)).symm
    _ = (l.appIso ⊤).hom (affineChartSection S l (φ r)) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]

include hcomm in
/-- On any smaller open, a regular function with the specified affine
coordinate value pulls back to the value of the actual affine ring map.
Only the regular section is pulled through `f`; no map `K(X) → K(Y)` is
used or assumed. -/
theorem affineChartSection_pullback_value
    (hpre : f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) =
      l ''ᵁ (⊤ : (Spec S).Opens))
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hU : U≤j ''ᵁ (⊤ : (Spec R).Opens))
    (r : Γ(X,U)) (a : R)
    (hr : X.germToFunctionField U r=affineOpenCoordinateMap R j a) :
    Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) =
      affineOpenCoordinateMap S l (φ a) := by
  let V := j ''ᵁ (⊤ : (Spec R).Opens)
  let W := l ''ᵁ (⊤ : (Spec S).Opens)
  letI : Nonempty V := openImmersion_image_nonempty j ⊤
  letI : Nonempty W := openImmersion_image_nonempty l ⊤
  have hW : f ⁻¹ᵁ U≤W := by
    change f ⁻¹ᵁ U ≤ l ''ᵁ (⊤ : (Spec S).Opens)
    rw [← hpre]
    exact f.preimage_mono hU
  have heq : r = X.presheaf.map (homOfLE hU).op (affineChartSection R j a) := by
    apply X.germToFunctionField_injective U
    rw [germToFunctionField_restrict,affineChartSection_germ,hr]
  rw [heq]
  have hs : f.app U
      (X.presheaf.map (homOfLE hU).op (affineChartSection R j a)) =
      Y.presheaf.map (homOfLE hW).op
        (f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j a)) := by
    have hm : X.presheaf.map (homOfLE hU).op ≫ f.app U =
        f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm) ≫
          Y.presheaf.map (homOfLE hW).op := by
      rw [f.app_eq_appLE,f.map_appLE,f.appLE_map]
    exact congrArg
      (fun g : Γ(X,V) ⟶ Γ(Y,f ⁻¹ᵁ U) => g.hom (affineChartSection R j a)) hm
  rw [hs,affineChartSection_pullback R S j l f φ hcomm,germToFunctionField_restrict,
    affineChartSection_germ]

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineChartSection_pullback_value
end Source_ToricAffinePullbackSections

section Source_ToricProjectiveLineUnits




/-!
# Units on the actual affine-line charts

Every regular unit on either affine-line chart is an actual nonzero
constant, by the polynomial-unit theorem. Its rational value therefore
has zero order at every point of the complete curve, including the point
outside that chart. This is the key input for degree invariance under
an arbitrary isomorphism of line bundles.
-/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_image (negative : Bool) :
    (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens) =
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative) := by
  ext x
  change (∃ p : PrimeSpectrum (Polynomial k),p∈(⊤ : (Spec (.of (Polynomial k))).Opens) ∧
    projectiveLinePolynomialChart k negative p=x) ↔
      ∃ q,projectiveLineChart k negative q=x
  constructor
  · rintro ⟨p,hp,hpx⟩
    exact ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,hpx⟩
  · rintro ⟨q,hq⟩
    obtain ⟨p,hp⟩ :=
      (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective q
    refine ⟨p,trivial,?_⟩
    change projectiveLineChart k negative
      ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
    exact (congrArg (projectiveLineChart k negative) hp).trans hq

theorem projectiveLine_constant_coordinate (negative : Bool) (c : k) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) (Polynomial.C c) =
        projectiveLineFan.rationalScalar k c := by
  let R := monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})
  let j : Spec (.of R) ⟶ projectiveLineScheme k := projectiveLineChart k negative
  letI : IsOpenImmersion j := projectiveLineChart_isOpenImmersion k negative
  have h : affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative)
      (projectiveLineChartRingEquiv k negative (algebraMap k R c)) =
      affineOpenCoordinateMap (.of R) j (algebraMap k R c) :=
    affineOpenCoordinateMap_comp (.of R) (.of (Polynomial k)) j
      (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom _
  rw [(projectiveLineChartRingEquiv k negative).commutes] at h
  exact h.trans (projectiveLineFan.chartRationalMap_eq_torusRationalMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩ _)

theorem projectiveLine_rationalScalar_order (c : kˣ) (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord (projectiveLineFan.rationalScalar k (c : k)) x=0 := by
  have hc : projectiveLineFan.rationalScalar k (c : k)≠0 :=
    Units.ne_zero (projectiveLineFan.rationalScalarUnit k c)
  obtain ⟨a,ha⟩ := (regular_unit_iff_stalkwise (projectiveLineScheme k) ⊤
    (projectiveLineFan.rationalScalar k (c : k)) hc).mpr (by
      constructor
      · intro y hy
        exact projectiveLineFan.rationalScalar_mem_regularAt k (c : k) y
      · intro y hy
        exact (map_inv₀ (projectiveLineFan.rationalScalar k) (c : k)) ▸
          projectiveLineFan.rationalScalar_mem_regularAt k ((c : k)⁻¹) y)
  rw [← ha]
  exact (projectiveLineScheme k).ord_of_isUnit a.isUnit (show x∈(⊤ : (projectiveLineScheme k).Opens) from trivial)

theorem projectiveLine_polynomialChartUnit_scalar (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    ∃ c : kˣ,(projectiveLineScheme k).germToFunctionField
      ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_)) =
        projectiveLineFan.rationalScalar k (c : k) := by
  let j := projectiveLinePolynomialChart k negative
  let R := CommRingCat.of (Polynomial k)
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let e : Γ(projectiveLineScheme k,U) ≃+* Polynomial k :=
    ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have he : IsUnit (e (u : Γ(projectiveLineScheme k,U))) := u.isUnit.map e
  obtain ⟨r,hr,hp⟩ := Polynomial.isUnit_iff.mp he
  obtain ⟨c,hc⟩ := hr
  refine ⟨c,?_⟩
  have hu : (u : Γ(projectiveLineScheme k,U)) =
      affineChartSection R j (e (u : Γ(projectiveLineScheme k,U))) := by
    change (u : Γ(projectiveLineScheme k,U)) = e.symm (e (u : Γ(projectiveLineScheme k,U)))
    exact (e.symm_apply_apply _).symm
  rw [hu,affineChartSection_germ,← hp,← hc]
  exact projectiveLine_constant_coordinate k negative (c : k)

theorem projectiveLine_polynomialChartUnit_order (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ)
    (x : projectiveLineScheme k) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_))) x=0 := by
  letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
  obtain ⟨c,hc⟩ := projectiveLine_polynomialChartUnit_scalar k negative u
  rw [hc]
  exact projectiveLine_rationalScalar_order k c x

theorem projectiveLine_fullChartUnit_order (negative : Bool)
    [Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))]
    (u : Γ(projectiveLineScheme k,
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))ˣ)
    (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))
        (u : Γ(projectiveLineScheme k,_))) x=0 := by
  let j := projectiveLinePolynomialChart k negative
  let U := j ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let φ := (projectiveLineScheme k).presheaf.map
    (eqToHom (projectiveLinePolynomialChart_image k negative)).op
  have h := projectiveLine_polynomialChartUnit_order k negative (Units.map φ.hom u) x
  change (projectiveLineScheme k).ord
    ((projectiveLineScheme k).germToFunctionField U
      ((projectiveLineScheme k).presheaf.map
        (eqToHom (projectiveLinePolynomialChart_image k negative)).op
          (u : Γ(projectiveLineScheme k,_)))) x = 0 at h
  have hr := germToFunctionField_restrict (projectiveLineScheme k)
    (eqToHom (projectiveLinePolynomialChart_image k negative))
      (u : Γ(projectiveLineScheme k,_))
  exact (congrArg (fun r => (projectiveLineScheme k).ord r x) hr).symm.trans h

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_fullChartUnit_order
end Source_ToricProjectiveLineUnits

section Source_ToricCartierFrameIsomorphisms




/-!
# Local Cartier frames under an actual line-bundle isomorphism

An isomorphism of the underlying module sheaves need not preserve their
fractional embeddings. It does, however, preserve the regular change of
coordinates between two transported frames. This distinction is used
when proving that degree depends only on the actual line bundle.
-/


universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes

namespace ModuleFrame

variable {X : Scheme.{u}} {M N : X.Modules} (F : M ≅ N)
    {U : X.Opens} (e : ModuleFrame N U)

def precompose : ModuleFrame M U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso F ≪≫ e

@[simp] theorem precompose_coordinates (V : X.Opens) (hV : V≤U)
    (s : Γ(M,V)) :
    (e.precompose F).coordinates V hV s = e.coordinates V hV (F.hom.app V s) := rfl

@[simp] theorem precompose_generator (V : X.Opens) (hV : V≤U) :
    F.hom.app V ((e.precompose F).generator V hV) = e.generator V hV := by
  apply (e.coordinates V hV).injective
  rw [← precompose_coordinates,coordinates_generator,coordinates_generator]

end ModuleFrame

namespace CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)
    (F : D.sheaf ≅ E.sheaf)

/-- Ratios of transported rational generators agree, even though the
individual generators need not have the same rational value. -/
theorem precompose_frameRatio {U V : X.Opens} [Nonempty U] [Nonempty V]
    (e : E.Frame U) (q : E.Frame V) :
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
      D.frameRationalGenerator (ModuleFrame.precompose F q) =
        E.frameRationalGenerator e / E.frameRationalGenerator q := by
  let W := U⊓V
  letI : Nonempty W := ⟨⟨genericPoint X,genericPoint_mem_open X U,
    genericPoint_mem_open X V⟩⟩
  let c := (ModuleFrame.precompose F q).coordinates W inf_le_right
    ((ModuleFrame.precompose F e).generator W inf_le_left)
  have hD : (ModuleFrame.precompose F e).generator W inf_le_left =
      c • (ModuleFrame.precompose F q).generator W inf_le_right :=
    (ModuleFrame.precompose F q).section_eq W inf_le_right _
  have hE := congrArg (F.hom.app W) hD
  rw [ModuleFrame.precompose_generator,Scheme.Modules.Hom.app_smul,
    ModuleFrame.precompose_generator] at hE
  have hDv := congrArg (D.sectionValue W) hD
  have hEv := congrArg (E.sectionValue W) hE
  change D.sectionValue W (D.frameGenerator (ModuleFrame.precompose F e) W inf_le_left) =
    D.sectionValue W (c • D.frameGenerator (ModuleFrame.precompose F q) W inf_le_right) at hDv
  change E.sectionValue W (E.frameGenerator e W inf_le_left) =
    E.sectionValue W (c • E.frameGenerator q W inf_le_right) at hEv
  rw [D.sectionValue_frameGenerator,D.sectionValue_smul,D.sectionValue_frameGenerator] at hDv
  rw [E.sectionValue_frameGenerator,E.sectionValue_smul,E.sectionValue_frameGenerator] at hEv
  calc
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
        D.frameRationalGenerator (ModuleFrame.precompose F q) = X.germToFunctionField W c := by
      rw [hDv,mul_div_cancel_right₀ _ (D.frameRationalGenerator_ne_zero _)]
    _ = E.frameRationalGenerator e / E.frameRationalGenerator q := by
      rw [hEv,mul_div_cancel_right₀ _ (E.frameRationalGenerator_ne_zero _)]

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.precompose_frameRatio
end Source_ToricCartierFrameIsomorphisms

section Source_ToricProjectiveLinePicardDegree




/-!
# Degree of the actual line bundle on the rank-one fan

An arbitrary isomorphism of the two Cartier sheaves preserves the sum of
their ray coefficients. The proof compares their genuine local frames:
the changes on the two affine-line charts are polynomial units, and the
remaining transition ratio is measured by actual local order. Thus the
degree is a property of the actual line bundle, not of a chosen fractional
embedding. Every Cartier sheaf has such a fan presentation by the proved
arbitrary-Cartier classification.
-/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLine_cartierPoint_coordinate (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) 0 =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  have h := projectiveLineFan.cartierLatticePoint_pairing a
    (projectiveLineFullCone negative) (projectiveLineRay negative)
      (Finset.mem_singleton_self _)
  cases negative <;> simp only [integerPairing,Fin.sum_univ_one,
    projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] at h ⊢ <;> omega

instance projectiveLine_fullChart_nonempty (negative : Bool) :
    Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) := by
  rw [← projectiveLinePolynomialChart_image k negative]
  exact openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤

def projectiveLineCartierFrame (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).Frame
      (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) :=
  (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_generator (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).frameRationalGenerator
      (projectiveLineCartierFrame k a negative) =
        (projectiveLineFan.rationalCharacter k
          (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) :
            (projectiveLineScheme k).functionField) := by
  letI : Nonempty ((projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).openSet
      ⟨projectiveLineFullCone negative⟩) := projectiveLine_fullChart_nonempty k negative
  exact (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame_rationalGenerator
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_order (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineScheme k).ord
      ((projectiveLineCartierData k a).frameRationalGenerator
        (projectiveLineCartierFrame k a negative)) (projectiveLineBoundaryPoint k false) =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  rw [projectiveLineCartierFrame_generator,projectiveLine_character_order_boundary]
  exact projectiveLine_cartierPoint_coordinate a negative

/-- Degree invariance is proved for every genuine sheaf isomorphism,
without requiring compatibility with the rational embeddings. -/
theorem projectiveLine_coefficientSum_eq_of_sheafIso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    a (projectiveLineRay false)+a (projectiveLineRay true) =
      b (projectiveLineRay false)+b (projectiveLineRay true) := by
  let X := projectiveLineScheme k
  let D := projectiveLineCartierData k a
  let E := projectiveLineCartierData k b
  let x := projectiveLineBoundaryPoint k false
  let e (negative : Bool) := projectiveLineCartierFrame k a negative
  let q (negative : Bool) := projectiveLineCartierFrame k b negative
  have hsame (negative : Bool) :
      X.ord (D.frameRationalGenerator (e negative)) x =
        X.ord (D.frameRationalGenerator (ModuleFrame.precompose F (q negative))) x := by
    obtain ⟨u,hu⟩ := D.exists_frameTransitionUnit
      (e negative) (ModuleFrame.precompose F (q negative)) le_rfl le_rfl
    have hzero := projectiveLine_fullChartUnit_order k negative u x
    rw [hu,rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _)] at hzero
    omega
  have hratio := D.precompose_frameRatio E F (q false) (q true)
  have hord := congrArg (fun r : X.functionField=>X.ord r x) hratio
  rw [rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _),
    rationalOrder_div (E.frameRationalGenerator_ne_zero _)
      (E.frameRationalGenerator_ne_zero _),← hsame false,← hsame true] at hord
  change X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a false)) x -
      X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a true)) x =
    X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b false)) x -
      X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b true)) x at hord
  rw [projectiveLineCartierFrame_order,projectiveLineCartierFrame_order,
    projectiveLineCartierFrame_order,projectiveLineCartierFrame_order] at hord
  simp only [Bool.false_eq_true,if_false,if_true] at hord
  omega

theorem projectiveLineCartier_degree_iso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    (projectiveLineCartierData k a).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
    (projectiveLineCartierData k b).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k b) := by
  rw [projectiveLineCartier_degree,projectiveLineCartier_degree]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b F

/-- Degree via the actual integral fan Cartier presentations. Existence
for arbitrary Cartier sheaves and uniqueness are proved below. Each such
presentation has exactly this Mathlib Weil-cycle degree. -/
def ProjectiveLineHasDegree (M : (projectiveLineScheme k).Modules) (d : ℤ) : Prop :=
  ∃ a : Lattice 1→ℤ, Nonempty (M ≅ (projectiveLineCartierData k a).sheaf) ∧
    a (projectiveLineRay false)+a (projectiveLineRay true)=d

theorem projectiveLineHasDegree_unique {M : (projectiveLineScheme k).Modules}
    {d e : ℤ} (hd : ProjectiveLineHasDegree k M d) (he : ProjectiveLineHasDegree k M e) : d=e := by
  obtain ⟨a,⟨Fa⟩,ha⟩ := hd
  obtain ⟨b,⟨Fb⟩,hb⟩ := he
  rw [← ha,← hb]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b (Fa.symm ≪≫ Fb)

theorem projectiveLineHasDegree_iso {M N : (projectiveLineScheme k).Modules}
    (F : M ≅ N) (d : ℤ) : ProjectiveLineHasDegree k M d ↔ ProjectiveLineHasDegree k N d := by
  constructor
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F.symm ≪≫ G⟩,ha⟩
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F ≪≫ G⟩,ha⟩

theorem projectiveLineCartier_hasDegree (a : Lattice 1→ℤ) :
    ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
      (a (projectiveLineRay false)+a (projectiveLineRay true)) :=
  ⟨a,⟨Iso.refl _⟩,rfl⟩

/-- Every arbitrary actual Cartier sheaf has a unique degree; no
character presentation or equivariance is assumed of the input. -/
theorem projectiveLineCartier_existsUnique_degree (D : CartierData (projectiveLineScheme k)) :
    ∃! d : ℤ,ProjectiveLineHasDegree k D.sheaf d := by
  let a := projectiveLineFan.cartierCoefficients k projectiveLineFan_isPure D
  let d := a (projectiveLineRay false)+a (projectiveLineRay true)
  have hd : ProjectiveLineHasDegree k D.sheaf d :=
    ⟨a,projectiveLineFan.cartierData_linearlyEquivalent_fanCartier k projectiveLineFan_isPure D,rfl⟩
  exact ⟨d,hd,fun e he=>projectiveLineHasDegree_unique k he hd⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_coefficientSum_eq_of_sheafIso
#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_existsUnique_degree
end Source_ToricProjectiveLinePicardDegree

section Source_ToricRankOneDegree




/-! # Actual line-bundle degrees on arbitrary rank-one complete fans -/


universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

theorem projectiveLineFan_rays :
    projectiveLineFan.rays={projectiveLineRay false,projectiveLineRay true} := by
  ext u
  rw [projectiveLineFan.mem_rays_iff]
  constructor
  · rintro ⟨s,hs,hu⟩
    rcases (mem_projectiveLineFan_cones s).mp hs with h|h|h
    · rw [h] at hu
      exact (Finset.notMem_empty u hu).elim
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
  · intro hu
    rcases Finset.mem_insert.mp hu with h|h
    · subst u
      exact ⟨{projectiveLineRay false},projectiveLineRayCone_mem false,
        Finset.mem_singleton_self _⟩
    · have h' := Finset.mem_singleton.mp h
      subst u
      exact ⟨{projectiveLineRay true},projectiveLineRayCone_mem true,
        Finset.mem_singleton_self _⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

include hd in
theorem oneDimensional_rays :
    Γ.rays={(fun _=>1 : Lattice d),(fun _=>-1 : Lattice d)} := by
  subst d
  rw [Γ.rankOne_eq_projectiveLine,projectiveLineFan_rays]
  rfl

variable (k : Type u) [Field k]

/-- Transport through the constructed actual scheme isomorphism to the
two-chart line, using the actual module-sheaf pullback functor. -/
def OneDimensionalHasDegree (M : (Γ.fanScheme k).Modules) (degree : ℤ) : Prop :=
  ProjectiveLineHasDegree k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).obj M) degree

theorem oneDimensionalHasDegree_unique {M : (Γ.fanScheme k).Modules}
    {r s : ℤ} (hr : Γ.OneDimensionalHasDegree hd k M r)
    (hs : Γ.OneDimensionalHasDegree hd k M s) : r=s :=
  projectiveLineHasDegree_unique k hr hs

theorem oneDimensionalHasDegree_iso {M N : (Γ.fanScheme k).Modules}
    (F : M ≅ N) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ Γ.OneDimensionalHasDegree hd k N r :=
  projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).mapIso F) r

/-- The degree of the actual fan Cartier sheaf is the sum over its actual
two primitive rays. This is derived from local orders and residue degrees. -/
theorem oneDimensionalFanCartier_hasDegree (hpure : Γ.IsPure) (a : Lattice d→ℤ) :
    Γ.OneDimensionalHasDegree hd k (Γ.fanCartierData k hpure a).sheaf
      (∑ v∈Γ.rays,a v) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  have hiso : oneDimensionalFanSchemeIso projectiveLineFan rfl k=
      Iso.refl (projectiveLineScheme k) := by
    rfl
  unfold OneDimensionalHasDegree
  rw [hiso]
  apply (projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullbackId (projectiveLineScheme k)).app
      (projectiveLineCartierData k a).sheaf) _).mpr
  change ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
    (∑ v∈projectiveLineFan.rays,a v)
  have h := projectiveLineCartier_hasDegree k a
  simpa only [projectiveLineFan_rays,Finset.sum_pair projectiveLineRay_ne] using h

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.oneDimensionalFanCartier_hasDegree
end Source_ToricRankOneDegree

section Source_ToricCartierPullbackFrames




/-!
# Identification of the actual sheaf pullback by local frames

The target is identified with Mathlib's ordinary module-sheaf pullback by
its adjunction universal property. Compatible transition maps are used to
construct a genuine sheaf morphism; no pullback or section-space dictionary
is a field of a structure or an additional axiom. The statement applies to
closed immersions as well as dominant morphisms.
-/


universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (e : ∀ i,ModuleFrame M (U i))
    (q : ∀ i,ModuleFrame N (f ⁻¹ᵁ U i))

include hcover in
theorem pullback_frameCover : ∀ y : Y,∃ i,y∈f ⁻¹ᵁ U i := fun y=>hcover (f y)

theorem pushforward_frameGenerator_res {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι)
    (V : X.Opens) (hV : V≤U i) :
    moduleRes F (f.preimage_mono hV)
        (β.app (U i) ((e i).generator (U i) le_rfl)) =
      β.app V ((e i).generator V hV) := by
  have h := PresheafOfModules.naturality_apply β.val (homOfLE hV).op
    ((e i).generator (U i) le_rfl)
  change β.app V (moduleRes M hV ((e i).generator (U i) le_rfl)) =
    moduleRes F (f.preimage_mono hV)
      (β.app (U i) ((e i).generator (U i) le_rfl)) at h
  exact h.symm.trans (congrArg (β.app V)
    ((e i).generator_res (V := U i) le_rfl hV))

variable (β₀ : M ⟶ (pushforward f).obj N)
    (hβ₀ : ∀ i,β₀.app (U i) ((e i).generator (U i) le_rfl) =
      (q i).generator (f ⁻¹ᵁ U i) le_rfl)

include β₀ hβ₀ in
/-- Any genuine morphism from the original sheaf supplies compatible
images of the comparison target's local generators. -/
theorem comparison_frameImages_compatible {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    ModuleFrameGluing.Compatible (fun i=>f ⁻¹ᵁ U i) q
      (fun i=>β.app (U i) ((e i).generator (U i) le_rfl)) := by
  intro i j W hWi hWj
  let V := U i⊓U j
  let c : Γ(X,V) := (e j).coordinates V inf_le_right ((e i).generator V inf_le_left)
  have hW : W≤f ⁻¹ᵁ V := by
    intro y hy
    exact ⟨hWi hy,hWj hy⟩
  have hgen : (e i).generator V inf_le_left =
      c • (e j).generator V inf_le_right :=
    (e j).section_eq V inf_le_right ((e i).generator V inf_le_left)
  have hβ (F : Y.Modules) (β : M ⟶ (pushforward f).obj F) :
      moduleRes F (f.preimage_mono (show V≤U i from inf_le_left))
          (β.app (U i) ((e i).generator (U i) le_rfl)) =
        f.app V c • moduleRes F (f.preimage_mono (show V≤U j from inf_le_right))
          (β.app (U j) ((e j).generator (U j) le_rfl)) := by
    rw [pushforward_frameGenerator_res f U e β i V inf_le_left,
      pushforward_frameGenerator_res f U e β j V inf_le_right,hgen,
      Scheme.Modules.Hom.app_smul]
    rfl
  have hN := hβ N β₀
  rw [hβ₀ i,hβ₀ j,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN
  have hN' := congrArg (moduleRes N hW) hN
  rw [moduleRes_smul,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN'
  have hc : (q j).coordinates W hWj ((q i).generator W hWi) =
      regularRes hW (f.app V c) := by
    rw [hN',_root_.map_smul,ModuleFrame.coordinates_generator,smul_eq_mul,mul_one]
  rw [hc]
  let hi : f ⁻¹ᵁ V≤f ⁻¹ᵁ U i := f.preimage_mono (show V≤U i from inf_le_left)
  let hj : f ⁻¹ᵁ V≤f ⁻¹ᵁ U j := f.preimage_mono (show V≤U j from inf_le_right)
  calc
    _ = moduleRes F hW (moduleRes F hi
        (β.app (U i) ((e i).generator (U i) le_rfl))) :=
      (moduleRes_trans F hi hW _).symm
    _ = moduleRes F hW (f.app V c • moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      congrArg (moduleRes F hW) (hβ F β)
    _ = regularRes hW (f.app V c) • moduleRes F hW (moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      moduleRes_smul F hW _ _
    _ = _ := congrArg (fun z=>regularRes hW (f.app V c) • z)
      (moduleRes_trans F hj hW _)

/-- The unique candidate supplied by the actual gluing of local frame
images. Its codomain is an arbitrary genuine module sheaf. -/
def comparisonLift {F : Y.Modules} (β : M ⟶ (pushforward f).obj F) : N ⟶ F :=
  ModuleFrameGluing.hom (fun i=>f ⁻¹ᵁ U i) (pullback_frameCover f U hcover) q
    (fun i=>β.app (U i) ((e i).generator (U i) le_rfl))
    (comparison_frameImages_compatible f U e q β₀ hβ₀ β)

theorem comparisonLift_generator {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι) :
    (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
        ((q i).generator (f ⁻¹ᵁ U i) le_rfl) =
      β.app (U i) ((e i).generator (U i) le_rfl) :=
  ModuleFrameGluing.hom_generator _ _ _ _ _ i

theorem comparison_comp_lift {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    β₀ ≫ (pushforward f).map (comparisonLift f U hcover e q β₀ hβ₀ β) = β := by
  apply ModuleFrameGluing.hom_ext U hcover e
  intro i
  change (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
    (β₀.app (U i) ((e i).generator (U i) le_rfl)) = _
  rw [hβ₀ i,comparisonLift_generator]

include hcover e q hβ₀ in
theorem comparison_postcompose_bijective (F : Y.Modules) :
    Function.Bijective (fun h : N ⟶ F=>β₀ ≫ (pushforward f).map h) := by
  constructor
  · intro h l heq
    apply ModuleFrameGluing.hom_ext (fun i=>f ⁻¹ᵁ U i)
      (pullback_frameCover f U hcover) q
    intro i
    have hEval := congrArg (fun a : M ⟶ (pushforward f).obj F =>
      a.app (U i) ((e i).generator (U i) le_rfl)) heq
    change h.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) =
      l.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) at hEval
    simpa only [hβ₀ i] using hEval
  · intro β
    exact ⟨comparisonLift f U hcover e q β₀ hβ₀ β,
      comparison_comp_lift f U hcover e q β₀ hβ₀ β⟩

include hcover e q hβ₀ in
/-- The actual adjoint morphism is an isomorphism because it has the
genuine universal property of the module-sheaf pullback. -/
theorem pullback_comparison_isIso :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀) := by
  let α := ((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  change Function.Bijective (fun h : N ⟶ F=>α ≫ h)
  let E := (pullbackPushforwardAdjunction f).homEquiv M F
  have hcomp (h : N ⟶ F) : E (α ≫ h)=β₀ ≫ (pushforward f).map h := by
    rw [Adjunction.homEquiv_naturality_right,Equiv.apply_symm_apply]
  have hb := comparison_postcompose_bijective f U hcover e q β₀ hβ₀ F
  constructor
  · intro h l heq
    apply hb.injective
    exact (hcomp h).symm.trans ((congrArg E heq).trans (hcomp l))
  · intro γ
    obtain ⟨h,hh⟩ := hb.surjective (E γ)
    refine ⟨h,E.injective ?_⟩
    exact (hcomp h).trans hh

/-- A shared criterion for arbitrary scheme morphisms: an actual map
sending one local basis to the other identifies the actual pullback. -/
def pullbackIso_of_frameComparison : (pullback f).obj M ≅ N := by
  letI := pullback_comparison_isIso f U hcover e q β₀ hβ₀
  exact asIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀)

section CompatibleTransitions

variable
    (htrans : ModuleFrameGluing.Compatible (N := (pushforward f).obj N) U e
      (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl))

/-- Mapped regular transition functions construct the comparison itself;
the existence of this sheaf map is not assumed. -/
def framePullbackComparison : M ⟶ (pushforward f).obj N :=
  ModuleFrameGluing.hom U hcover e
    (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl) htrans

/-- Local frames with genuinely mapped transition functions identify the
ordinary sheaf pullback, also along a closed boundary immersion. -/
def pullbackIso_of_compatible_frames : (pullback f).obj M ≅ N :=
  pullbackIso_of_frameComparison f U hcover e q
    (framePullbackComparison f U hcover e q htrans)
    (ModuleFrameGluing.hom_generator U hcover e _ htrans)

end CompatibleTransitions

end PaperVerification.ToricSchemes
end Source_ToricCartierPullbackFrames

section Source_ToricDominantCartierPullback




/-!
# Actual Cartier pullback along a dominant morphism

The rational equations are pulled through the genuine map of generic
stalks. Their regularity comes from the actual maps on local rings. The
resulting invertible fractional sheaf is identified with the ordinary
module-sheaf pullback by the independent local-frame theorem.
-/


universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def dominantPullback : RationalCartierCocycle Y where
  index := C.index
  openSet i := f ⁻¹ᵁ C.openSet i
  covers y := C.covers (f y)
  generator i := Units.map (dominantFunctionFieldMap f).toMonoidHom (C.generator i)
  transition i j y hi hj := by
    have h := dominantFunctionFieldMap_mem_regularAt f y
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j (f y) hi hj)
    change dominantFunctionFieldMap f (C.generator i : X.functionField) /
      dominantFunctionFieldMap f (C.generator j : X.functionField) ∈ regularAtSubring Y y
    simpa only [map_div₀] using h

@[simp] theorem dominantPullback_generator (i : C.index) :
    ((C.dominantPullback f).generator i : Y.functionField) =
      dominantFunctionFieldMap f (C.generator i : X.functionField) := rfl

@[simp] theorem localFrame_coordinates (i : C.index)
    (V : X.Opens) (hV : V≤C.openSet i) :
    ModuleFrame.coordinates (C.localFrame i) V hV = C.localCoordinates i V hV := rfl

theorem localFrame_generator_value (i : C.index) (V : X.Opens) [Nonempty V]
    (hV : V≤C.openSet i) :
    C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hV) =
      (C.generator i : X.functionField) := by
  have h := C.localCoordinates_value i V hV (ModuleFrame.generator (C.localFrame i) V hV)
  rw [← localFrame_coordinates,ModuleFrame.coordinates_generator,map_one] at h
  change 1 = C.toCartierData.sectionValue V
    (ModuleFrame.generator (C.localFrame i) V hV)/(C.generator i : X.functionField) at h
  field_simp [Units.ne_zero] at h
  exact h.symm

/-- The pullback local frames have exactly the mapped regular transition
functions of the original frames. This is proved inside actual local
section rings and actual function fields. -/
theorem dominantPullback_frames_compatible :
    ModuleFrameGluing.Compatible
      (N := (Scheme.Modules.pushforward f).obj (C.dominantPullback f).sheaf)
      C.openSet C.localFrame
      (fun i=>ModuleFrame.generator ((C.dominantPullback f).localFrame i)
        (f ⁻¹ᵁ C.openSet i) le_rfl) := by
  intro i j V hi hj
  let B := C.dominantPullback f
  let W := f ⁻¹ᵁ V
  by_cases hW : Nonempty W
  · letI := hW
    let bi : B.index := i
    let bj : B.index := j
    have hWi : W≤B.openSet bi := f.preimage_mono hi
    have hWj : W≤B.openSet bj := f.preimage_mono hj
    letI : Nonempty V := ⟨⟨f (Classical.choice hW).val,(Classical.choice hW).property⟩⟩
    letI : Nonempty (f ⁻¹ᵁ C.openSet i) :=
      ⟨⟨(Classical.choice hW).val,hi (Classical.choice hW).property⟩⟩
    letI : Nonempty (f ⁻¹ᵁ C.openSet j) :=
      ⟨⟨(Classical.choice hW).val,hj (Classical.choice hW).property⟩⟩
    let a : Γ(X,V) := ModuleFrame.coordinates (C.localFrame j) V hj
      (ModuleFrame.generator (C.localFrame i) V hi)
    let b : Γ(Y,W) := f.app V a
    have ha : X.germToFunctionField V a =
        (C.generator i : X.functionField) / (C.generator j : X.functionField) := by
      calc
        _ = rationalValue X V (ModuleFrame.generator (C.localFrame i) V hi).val /
            (C.generator j : X.functionField) :=
          C.localCoordinates_value j V hj (ModuleFrame.generator (C.localFrame i) V hi)
        _ = C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hi) /
            (C.generator j : X.functionField) :=
          congrArg (fun z : X.functionField => z / (C.generator j : X.functionField))
            (C.toCartierData_sectionValue V (ModuleFrame.generator (C.localFrame i) V hi)).symm
        _ = _ := congrArg (fun z : X.functionField => z / (C.generator j : X.functionField))
          (C.localFrame_generator_value i V hi)
    have hb : Y.germToFunctionField W b =
        (B.generator bi : Y.functionField) / (B.generator bj : Y.functionField) := by
      calc
        _ = dominantFunctionFieldMap f (X.germToFunctionField V a) :=
          (dominantFunctionFieldMap_germ f V a).symm
        _ = dominantFunctionFieldMap f
            ((C.generator i : X.functionField) / (C.generator j : X.functionField)) :=
          congrArg (dominantFunctionFieldMap f) ha
        _ = dominantFunctionFieldMap f (C.generator i : X.functionField) /
            dominantFunctionFieldMap f (C.generator j : X.functionField) :=
          map_div₀ (dominantFunctionFieldMap f) _ _
        _ = _ := rfl
    apply B.toCartierData.sectionValue_injective W
    change B.toCartierData.sectionValue W
        (moduleRes B.sheaf hWi
          (ModuleFrame.generator (B.localFrame bi) (B.openSet bi) le_rfl)) =
      B.toCartierData.sectionValue W
        (b • moduleRes B.sheaf hWj
          (ModuleFrame.generator (B.localFrame bj) (B.openSet bj) le_rfl))
    calc
      _ = B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bi) W hWi) :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W s)
          (ModuleFrame.generator_res (B.localFrame bi) le_rfl hWi)
      _ = (B.generator bi : Y.functionField) := B.localFrame_generator_value bi W hWi
      _ = ((B.generator bi : Y.functionField) / (B.generator bj : Y.functionField)) *
          (B.generator bj : Y.functionField) :=
        (div_mul_cancel₀ (B.generator bi : Y.functionField) (B.generator bj).ne_zero).symm
      _ = Y.germToFunctionField W b * (B.generator bj : Y.functionField) :=
        congrArg (fun z : Y.functionField => z * (B.generator bj : Y.functionField)) hb.symm
      _ = Y.germToFunctionField W b *
          B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bj) W hWj) :=
        congrArg (fun z : Y.functionField => Y.germToFunctionField W b * z)
          (B.localFrame_generator_value bj W hWj).symm
      _ = B.toCartierData.sectionValue W
          (b • ModuleFrame.generator (B.localFrame bj) W hWj) :=
        (B.toCartierData.sectionValue_smul W b
          (ModuleFrame.generator (B.localFrame bj) W hWj)).symm
      _ = _ :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W (b • s))
          (ModuleFrame.generator_res (B.localFrame bj) le_rfl hWj).symm
  · have hbot : W=⊥ := by
      apply le_antisymm ?_ bot_le
      intro y hy
      exact (hW ⟨⟨y,hy⟩⟩).elim
    letI := moduleSections_subsingleton_of_empty B.sheaf W hbot
    change (_ : Γ(B.sheaf,W)) = _
    exact Subsingleton.elim _ _

/-- The independent sheaf-pullback theorem identifies the fractional
construction with Mathlib's genuine module-sheaf pullback. -/
def dominantPullbackSheafIso :
    (Scheme.Modules.pullback f).obj C.sheaf ≅ (C.dominantPullback f).sheaf :=
  pullbackIso_of_compatible_frames f C.openSet C.covers C.localFrame
    (C.dominantPullback f).localFrame (C.dominantPullback_frames_compatible f)

theorem GeneratorRatioRegular.dominantPullback
    (D : RationalCartierCocycle X) (h : C.GeneratorRatioRegular D) :
    (C.dominantPullback f).GeneratorRatioRegular (D.dominantPullback f) := by
  intro i j y hi hj
  have hv := dominantFunctionFieldMap_mem_regularAt f y
    ((C.generator i : X.functionField)/(D.generator j : X.functionField))
    (h i j (f y) hi hj)
  change dominantFunctionFieldMap f (C.generator i : X.functionField) /
    dominantFunctionFieldMap f (D.generator j : X.functionField) ∈ regularAtSubring Y y
  simpa only [map_div₀] using hv

theorem dominantPullback_equivalent_of_equivalent
    (D : RationalCartierCocycle X) (h : C.toCartierData.Equivalent D.toCartierData) :
    (C.dominantPullback f).toCartierData.Equivalent
      (D.dominantPullback f).toCartierData :=
  (C.dominantPullback f).equivalent_of_generatorRatios (D.dominantPullback f)
    (GeneratorRatioRegular.dominantPullback f C D
      (C.generatorRatios_of_equivalent D h))
    (GeneratorRatioRegular.dominantPullback f D C
      (D.generatorRatios_of_equivalent C
        (C.toCartierData.equivalent_symm D.toCartierData h)))

/-- Composition is equality of actual Cartier divisors, proved using
generic-stalk functoriality and the original regular transition ratios. -/
theorem dominantPullback_comp_equivalent {Z : Scheme.{u}} [IsIntegral Z]
    (g : Z ⟶ Y) [IsDominant g] :
    ((C.dominantPullback f).dominantPullback g).toCartierData.Equivalent
      (C.dominantPullback (g≫f)).toCartierData := by
  apply RationalCartierCocycle.equivalent_of_generatorRatios
  · intro i j z hi hj
    have h := dominantFunctionFieldMap_mem_regularAt (g≫f) z
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j ((g≫f) z) hi hj)
    change dominantFunctionFieldMap g (dominantFunctionFieldMap f
        (C.generator i : X.functionField)) /
      dominantFunctionFieldMap (g≫f) (C.generator j : X.functionField) ∈ regularAtSubring Z z
    simpa only [dominantFunctionFieldMap_comp,RingHom.comp_apply,map_div₀] using h
  · intro i j z hi hj
    have h := dominantFunctionFieldMap_mem_regularAt (g≫f) z
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j ((g≫f) z) hi hj)
    change dominantFunctionFieldMap (g≫f) (C.generator i : X.functionField) /
      dominantFunctionFieldMap g (dominantFunctionFieldMap f
        (C.generator j : X.functionField)) ∈ regularAtSubring Z z
    simpa only [dominantFunctionFieldMap_comp,RingHom.comp_apply,map_div₀] using h

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- Pullback of an arbitrary actual Cartier divisor through a dominant
morphism, defined from its proved local rational presentation. -/
def dominantPullback : CartierData Y :=
  (D.localCocycle.dominantPullback f).toCartierData

def dominantPullbackSheafIso :
    (Scheme.Modules.pullback f).obj D.sheaf ≅ (D.dominantPullback f).sheaf :=
  (Scheme.Modules.pullback f).mapIso D.equivalent_localCocycle.choose ≪≫
    D.localCocycle.dominantPullbackSheafIso f

theorem dominantPullback_equivalent (h : D.Equivalent E) :
    (D.dominantPullback f).Equivalent (E.dominantPullback f) := by
  have hC : D.localCocycle.toCartierData.Equivalent E.localCocycle.toCartierData :=
    D.localCocycle.toCartierData.equivalent_trans D E.localCocycle.toCartierData
      (D.equivalent_symm D.localCocycle.toCartierData D.equivalent_localCocycle)
      (D.equivalent_trans E E.localCocycle.toCartierData h E.equivalent_localCocycle)
  exact D.localCocycle.dominantPullback_equivalent_of_equivalent f E.localCocycle hC

end CartierData

end PaperVerification.ToricSchemes
end Source_ToricDominantCartierPullback

section Source_ToricOrbitCartierRestriction





/-!
# Actual restriction of a Cartier sheaf to an orbit closure

The normalized local characters define an actual fractional sheaf on the
quotient-star scheme. The original transition functions are regular on
their overlaps and are pulled through the actual affine quotient maps.
The independent local-frame universal property then identifies this
fractional sheaf with Mathlib's ordinary module-sheaf pullback.
-/


universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fanChartMap_inter_opensRange (s t : «Σ».ConeIndex) :
    («Σ».fanChartMap k
      ⟨s.val∩t.val,«Σ».downward s.val s.property _ Finset.inter_subset_left⟩).opensRange =
      («Σ».fanChartMap k s).opensRange⊓(«Σ».fanChartMap k t).opensRange := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    constructor
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
  · rintro ⟨⟨ys,hys⟩,⟨yt,hyt⟩⟩
    obtain ⟨z,hzs,hzt⟩ := («Σ».fanChartMap_eq_iff k s t ys yt).mp (hys.trans hyt.symm)
    refine ⟨z,?_⟩
    rw [← «Σ».fanChartMap_naturality k Finset.inter_subset_left]
    change «Σ».fanChartMap k s (coneChartFaceMap k Finset.inter_subset_left z)=x
    rw [hzs,hys]

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbit_preimage_fullChart_forces (s : «Σ».fullCones)
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k)
    (hx : x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s) :
    I.image b⊆s.val := by
  by_contra hn
  have he := «Σ».orbitClosureMap_preimage_chart_empty k b I hF («Σ».fullConeIndex s) hn
  change x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
    («Σ».fanChartMap k («Σ».fullConeIndex s)).opensRange at hx
  rw [he] at hx
  exact hx

theorem orbit_preimage_fullChart (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s =
      («Σ».completeQuotientStarFan b I hF).fullChartOpen k
        («Σ».orbitFullConeIndex b I hF s hIs) :=
  «Σ».orbitClosureMap_preimage_chart k b I hF
    ⟨s.val,«Σ».fullCones_mem s,hIs⟩

variable (hpure : «Σ».IsPure) (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)

/-- Empty preimages cause no problem: arbitrary generators there have
no effect on the actual sheaf. On every nonempty preimage the generator
is the projected normalized ambient character. -/
def orbitRestrictionCocycle :
    RationalCartierCocycle ((«Σ».completeQuotientStarFan b I hF).fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure («Σ».orbitClosureMap k b I hF x)
    exact ⟨⟨s⟩,hs⟩
  generator i := («Σ».completeQuotientStarFan b I hF).rationalCharacter k
    (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀))
  transition i j x hi hj := by
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi,
      «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply («Σ».completeQuotientStarFan b I hF).cartier_rational_transition_regular k
      («Σ».orbitRestrictionCoefficients b I hF a m₀)
      («Σ».orbitFullConeIndex b I hF i.down hIi)
      («Σ».orbitFullConeIndex b I hF j.down hIj) x
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

theorem orbitRestrictionCocycle_equivalent :
    («Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀).toCartierData.Equivalent
      ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
        («Σ».completeQuotientStarFan_isPure hpure b I hF)
        («Σ».orbitRestrictionCoefficients b I hF a m₀)) := by
  let C := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let E := Γ.fanCartierCocycle k («Σ».completeQuotientStarFan_isPure hpure b I hF)
    («Σ».orbitRestrictionCoefficients b I hF a m₀)
  apply C.equivalent_of_generatorRatios E
  · intro i j x hi hj
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    change ((Γ.rationalCharacter k
      (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k (Γ.cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) j.down) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi]
    apply Γ.cartier_rational_transition_regular k _ _ _ x _ hj
    rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
  · intro i j x hi hj
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    change ((Γ.rationalCharacter k (Γ.cartierLatticePoint
      («Σ».orbitRestrictionCoefficients b I hF a m₀) i.down) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply Γ.cartier_rational_transition_regular k _ _ _ x hi
    rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

/-- The actual pullback of any regular representative of an ambient
transition function has exactly the projected transition character. -/
theorem orbit_regularTransition_pullback
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val)
    (V : («Σ».fanScheme k).Opens) [Nonempty V]
    [Nonempty ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V)]
    (hVs : V≤«Σ».fullChartOpen k s) (hVt : V≤«Σ».fullChartOpen k t)
    (c : Γ(«Σ».fanScheme k,V))
    (hc : («Σ».fanScheme k).germToFunctionField V c =
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) :
        («Σ».fanScheme k).functionField)) :
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k).germToFunctionField
      ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V) ((«Σ».orbitClosureMap k b I hF).app V c) =
      ((«Σ».completeQuotientStarFan b I hF).rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) :
          ((«Σ».completeQuotientStarFan b I hF).fanScheme k).functionField) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let q : «Σ».OrbitConeIndex b I :=
    ⟨s.val∩t.val,«Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left,
      Finset.subset_inter hIs hIt⟩
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid q.val))
  let S := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I q.val)))
  let j : Spec R ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨q.val,q.property.1⟩
  let l : Spec S ⟶ Γ.fanScheme k := Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF q)
  letI : IsOpenImmersion j := «Σ».fanChartMap_isOpenImmersion k ⟨q.val,q.property.1⟩
  letI : IsOpenImmersion l := Γ.fanChartMap_isOpenImmersion k
    («Σ».orbitConeQuotientIndex b I hF q)
  let φ : R ⟶ S := CommRingCat.ofHom
    (orbitQuotientAlgebraMap k b I q.val q.property.2).toRingHom
  let d : R := «Σ».cartierTransitionUnit k a s t
  have hpre : («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ (j ''ᵁ ⊤)=l ''ᵁ ⊤ := by
    rw [j.image_top_eq_opensRange,l.image_top_eq_opensRange]
    exact «Σ».orbitClosureMap_preimage_chart k b I hF q
  have hV : V≤j ''ᵁ ⊤ := by
    have h := «Σ».fanChartMap_inter_opensRange k («Σ».fullConeIndex s) («Σ».fullConeIndex t)
    change j.opensRange = «Σ».fullChartOpen k s ⊓ «Σ».fullChartOpen k t at h
    rw [Scheme.Hom.image_top_eq_opensRange,h]
    exact le_inf hVs hVt
  have hd : («Σ».fanScheme k).germToFunctionField V c=affineOpenCoordinateMap R j d := by
    rw [hc]
    exact («Σ».chartRationalMap_character k ⟨q.val,q.property.1⟩
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1).symm
  rw [affineChartSection_pullback_value R S j l («Σ».orbitClosureMap k b I hF) φ
    («Σ».orbitClosureMap_chart k b I hF q) hpre V hV c d hd]
  have hm : faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)∈
      dualConeMonoid (orbitQuotientCone b I q.val) := by
    have h := (φ d).property
    rw [mem_monoidChartAlgebra] at h
    apply h
    change faceCharacterProjection b I
        («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) ∈
      ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
        («Σ».cartierTransitionUnit k a s t) : AddMonoidAlgebra k (Lattice (n-I.card)))).coeff.support
    rw [«Σ».orbit_cartierTransition_character b I k a s t hIs hIt]
    simp
  have hd' : φ d=chartCharacter k (dualConeMonoid (orbitQuotientCone b I q.val))
      (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) hm := by
    apply Subtype.ext
    exact «Σ».orbit_cartierTransition_character b I k a s t hIs hIt
  rw [hd']
  exact Γ.chartRationalMap_character k («Σ».orbitConeQuotientIndex b I hF q) _ hm

theorem orbitRestriction_frames_compatible :
    let C := «Σ».fanCartierCocycle k hpure a
    let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
    ModuleFrameGluing.Compatible
      (N := (Scheme.Modules.pushforward («Σ».orbitClosureMap k b I hF)).obj B.sheaf)
      C.openSet C.localFrame
      (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let f := «Σ».orbitClosureMap k b I hF
  change ModuleFrameGluing.Compatible
    (N := (Scheme.Modules.pushforward f).obj B.sheaf)
    C.openSet C.localFrame
    (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl)
  intro i j V hi hj
  let W := f ⁻¹ᵁ V
  by_cases hW : Nonempty W
  · letI := hW
    let bi : B.index := i
    let bj : B.index := j
    have hWi : W≤B.openSet bi := f.preimage_mono hi
    have hWj : W≤B.openSet bj := f.preimage_mono hj
    let y : W := Classical.choice hW
    letI : Nonempty V := ⟨⟨f y.val,y.property⟩⟩
    letI : Nonempty (B.openSet bi) := ⟨⟨y.val,hi y.property⟩⟩
    letI : Nonempty (B.openSet bj) := ⟨⟨y.val,hj y.property⟩⟩
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down y.val (hi y.property)
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down y.val (hj y.property)
    let c : Γ(«Σ».fanScheme k,V) := ModuleFrame.coordinates (C.localFrame j) V hj
      (ModuleFrame.generator (C.localFrame i) V hi)
    let d : Γ(Γ.fanScheme k,W) := f.app V c
    have hc₀ : («Σ».fanScheme k).germToFunctionField V c =
        (C.generator i : («Σ».fanScheme k).functionField) /
          (C.generator j : («Σ».fanScheme k).functionField) := by
      calc
        _ = rationalValue («Σ».fanScheme k) V
            (ModuleFrame.generator (C.localFrame i) V hi).val /
              (C.generator j : («Σ».fanScheme k).functionField) :=
          C.localCoordinates_value j V hj (ModuleFrame.generator (C.localFrame i) V hi)
        _ = C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hi) /
            (C.generator j : («Σ».fanScheme k).functionField) :=
          congrArg (fun z : («Σ».fanScheme k).functionField =>
            z / (C.generator j : («Σ».fanScheme k).functionField))
            (C.toCartierData_sectionValue V (ModuleFrame.generator (C.localFrame i) V hi)).symm
        _ = _ := congrArg (fun z : («Σ».fanScheme k).functionField =>
          z / (C.generator j : («Σ».fanScheme k).functionField))
          (C.localFrame_generator_value i V hi)
    have hc : («Σ».fanScheme k).germToFunctionField V c =
        («Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down) : («Σ».fanScheme k).functionField) := by
      simpa only [C,fanCartierCocycle,«Σ».rationalCharacter_sub k,
        Units.val_div_eq_div_val] using hc₀
    have hpc := «Σ».orbit_regularTransition_pullback k b I hF a
      i.down j.down hIi hIj V hi hj c hc
    have hmul : (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := by
      change (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W (f.app V c) * _
      rw [hpc]
      change (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
          (Γ.fanScheme k).functionField) =
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down)) : (Γ.fanScheme k).functionField) *
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField)
      rw [← Units.val_mul,← Γ.rationalCharacter_add k,← map_add (faceCharacterProjection b I)]
      congr 3
      abel
    apply B.toCartierData.sectionValue_injective W
    change B.toCartierData.sectionValue W
      (moduleRes B.sheaf hWi
        (ModuleFrame.generator (B.localFrame bi) (B.openSet bi) le_rfl)) =
      B.toCartierData.sectionValue W (d • moduleRes B.sheaf hWj
        (ModuleFrame.generator (B.localFrame bj) (B.openSet bj) le_rfl))
    calc
      _ = B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bi) W hWi) :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W s)
          (ModuleFrame.generator_res (B.localFrame bi) le_rfl hWi)
      _ = (B.generator bi : (Γ.fanScheme k).functionField) :=
        B.localFrame_generator_value bi W hWi
      _ = (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := hmul
      _ = (Γ.fanScheme k).germToFunctionField W d *
          B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bj) W hWj) :=
        congrArg (fun z : (Γ.fanScheme k).functionField =>
          (Γ.fanScheme k).germToFunctionField W d * z)
          (B.localFrame_generator_value bj W hWj).symm
      _ = B.toCartierData.sectionValue W
          (d • ModuleFrame.generator (B.localFrame bj) W hWj) :=
        (B.toCartierData.sectionValue_smul W d
          (ModuleFrame.generator (B.localFrame bj) W hWj)).symm
      _ = _ := congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W (d • s))
        (ModuleFrame.generator_res (B.localFrame bj) le_rfl hWj).symm
  · have hb : W=⊥ := by
      apply le_antisymm
      · intro y hy
        exact False.elim (hW ⟨⟨y,hy⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty B.sheaf W hb
    change (_ : Γ(B.sheaf,W)) = _
    exact Subsingleton.elim _ _

/-- The actual ambient line bundle restricts to the actual fan Cartier
sheaf with the computed quotient-ray coefficients. -/
def orbitCartierPullbackIso :
    (Scheme.Modules.pullback («Σ».orbitClosureMap k b I hF)).obj
      («Σ».fanCartierData k hpure a).sheaf ≅
        ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
          («Σ».completeQuotientStarFan_isPure hpure b I hF)
          («Σ».orbitRestrictionCoefficients b I hF a m₀)).sheaf := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  exact pullbackIso_of_compatible_frames («Σ».orbitClosureMap k b I hF)
    C.openSet C.covers C.localFrame B.localFrame
    («Σ».orbitRestriction_frames_compatible k b I hF hpure a m₀ hm₀) ≪≫
      («Σ».orbitRestrictionCocycle_equivalent k b I hF hpure a m₀ hm₀).choose

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitRestrictionCocycle_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_regularTransition_pullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitCartierPullbackIso
end Source_ToricOrbitCartierRestriction

section Source_ToricStarConeCovering

/-!
# The actual support of a finite star subdivision

These lemmas work with ordinary finite nonnegative spans. In particular, the
new ray is the actual sum of the old focus rays, and preservation of support
is proved by subtracting a minimum coefficient.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Intersecting a finitely generated subcone with an actual face keeps
exactly the generators belonging to that face. -/
theorem finiteRayCone_inf_face (C F : PointedCone ℝ E) (hF : F.IsFaceOf C)
    (s : Finset E) (hs : ∀ v ∈ s, v ∈ C) :
    finiteRayCone s ⊓ F = finiteRayCone (s.filter (fun v => v ∈ F)) := by
  apply le_antisymm
  · rintro x ⟨⟨c, hc, hsum⟩, hxF⟩
    have hzero (v : E) (hv : v ∈ s) (hvF : v ∉ F) : c v = 0 := by
      by_contra hne
      have hpos : 0 < c v := lt_of_le_of_ne (hc v hv) (Ne.symm hne)
      apply hvF
      apply hF.mem_of_smul_add_mem (hs v hv)
        (Submodule.sum_mem _ (fun w hw => PointedCone.smul_mem _
          (hc w (Finset.mem_of_mem_erase hw)) (hs w (Finset.mem_of_mem_erase hw)))) hpos
      rw [Finset.add_sum_erase s (fun w => c w • w) hv, hsum]
      exact hxF
    refine ⟨c, fun v hv => hc v ((Finset.mem_filter.mp hv).1), ?_⟩
    calc
      (∑ v ∈ s.filter (fun v => v ∈ F), c v • v) = ∑ v ∈ s, c v • v := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro v hv hvfilter
        have hvF : v ∉ F := fun h => hvfilter (Finset.mem_filter.mpr ⟨hv, h⟩)
        rw [hzero v hv hvF, zero_smul]
      _ = x := hsum
  · rintro x ⟨c, hc, hsum⟩
    refine ⟨finiteRayCone_mono (Finset.filter_subset _ _) ⟨c, hc, hsum⟩, ?_⟩
    rw [← hsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv) (Finset.mem_filter.mp hv).2)

/-- The actual ray set of one cone in the star subdivision of `s` along
the nonempty subset `t`, omitting the selected old ray `v`. -/
def starRaySet (s t : Finset E) (v : E) : Finset E :=
  insert (∑ w ∈ t, w) (s.erase v)

omit [Module ℝ E] in
/-- Membership in the actual star ray set, independent of the implementation
of decidable equality used by its finite-set operations. -/
theorem mem_starRaySet (s t : Finset E) (v w : E) :
    w ∈ starRaySet s t v ↔ w = (∑ z ∈ t, z) ∨ (w ≠ v ∧ w ∈ s) := by
  simp only [starRaySet, Finset.mem_insert, Finset.mem_erase]

/-- Every new cone is contained in its old parent cone. -/
theorem finiteRayCone_starRaySet_le {s t : Finset E} (hts : t ⊆ s) (v : E) :
    finiteRayCone (starRaySet s t v) ≤ finiteRayCone s := by
  rw [finiteRayCone_eq_hull]
  apply Submodule.span_le.mpr
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Submodule.sum_mem _ (fun w hw => finiteRayCone_generator s (hts hw))
  · exact finiteRayCone_generator s (Finset.mem_of_mem_erase hw)

/-- A cone is covered by the actual cones obtained by replacing one focus
ray with the sum of all focus rays. No smoothness or linear independence is
needed for this support assertion. -/
theorem finiteRayCone_star_cover {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) {x : E} (hx : x ∈ finiteRayCone s) :
    ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v) := by
  obtain ⟨c, hc, hsum⟩ := hx
  obtain ⟨v, hv, hmin⟩ := t.exists_min_image c ht
  have hvs : v ∈ s := hts hv
  let d : E → ℝ := fun w => c w - if w ∈ t then c v else 0
  have hd (w : E) (hw : w ∈ s) : 0 ≤ d w := by
    by_cases hwt : w ∈ t
    · simp only [d, if_pos hwt]
      exact sub_nonneg.mpr (hmin w hwt)
    · simp only [d, if_neg hwt, sub_zero]
      exact hc w hw
  have hdv : d v = 0 := by simp [d, hv]
  have hcond : (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
      c v • ∑ w ∈ t, w := by
    calc
      (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
          ∑ w ∈ t, (if w ∈ t then c v else 0) • w := by
        symm
        apply Finset.sum_subset hts
        intro w _ hw
        simp only [if_neg hw, zero_smul]
      _ = ∑ w ∈ t, c v • w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [if_pos hw]
      _ = c v • ∑ w ∈ t, w := Finset.smul_sum.symm
  have hfull : (∑ w ∈ s, d w • w) = x - c v • ∑ w ∈ t, w := by
    simp only [d, sub_smul, Finset.sum_sub_distrib, hcond, hsum]
  have herase : (∑ w ∈ s.erase v, d w • w) = x - c v • ∑ w ∈ t, w := by
    rw [← Finset.sum_erase_add s (fun w => d w • w) hvs, hdv, zero_smul,
      add_zero] at hfull
    exact hfull
  refine ⟨v, hv, ?_⟩
  have hfirst : c v • (∑ w ∈ t, w) ∈ finiteRayCone (starRaySet s t v) :=
    PointedCone.smul_mem _ (hc v hvs)
      (finiteRayCone_generator _ (Finset.mem_insert_self _ _))
  have hsecond : (∑ w ∈ s.erase v, d w • w) ∈
      finiteRayCone (starRaySet s t v) := by
    apply Submodule.sum_mem
    intro w hw
    exact PointedCone.smul_mem _ (hd w (Finset.mem_of_mem_erase hw))
      (finiteRayCone_generator _ (Finset.mem_insert_of_mem hw))
  have hnew := (finiteRayCone (starRaySet s t v)).add_mem hfirst hsecond
  rw [herase] at hnew
  have hcancel : c v • (∑ w ∈ t, w) +
      (x - c v • (∑ w ∈ t, w)) = x := by abel
  rw [hcancel] at hnew
  exact hnew

/-- Equality of the old cone with the finite union of the new actual cones. -/
theorem finiteRayCone_eq_union_star {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) :
    (finiteRayCone s : Set E) =
      {x | ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v)} := by
  ext x
  constructor
  · exact finiteRayCone_star_cover hts ht
  · rintro ⟨v, hv, hx⟩
    exact finiteRayCone_starRaySet_le hts v hx

end PaperVerification.ToricGeometry
end Source_ToricStarConeCovering

section Source_ToricStarConeIntersections

/-!
# Actual intersections of the cones in a smooth star chart

The intersection of two newly subdivided cones is proved to be their
common-ray cone. The key equality is that both chosen pivot coordinates
must be minima, hence equal; the corresponding new coefficient vanishes.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section RaySets

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The actual inserted-sum ray set is exactly the indicated subset of the
unimodular replacement basis. -/
theorem starRaySet_basis (b : Module.Basis ι R E)
    (I J : Finset ι) (hJI : J ⊆ I) (j : ι) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    letI : Subsingleton E := Module.subsingleton R E
    ext x
    constructor
    · intro _
      exact Finset.mem_image.mpr ⟨j, hJI hj, Subsingleton.elim _ _⟩
    · intro _
      exact (mem_starRaySet _ _ _ _).mpr (Or.inl (Subsingleton.elim _ _))
  · letI := hR
    have hjI : j ∈ I := hJI hj
    have hsum : (∑ v ∈ J.image b, v) = ∑ i ∈ J, b i := by
      rw [Finset.sum_image]
      exact fun i _ k _ hik => b.injective hik
    have hrest : (I.erase j).image (starRayBasis b J j) = (I.erase j).image b := by
      apply Finset.image_congr
      intro i hi
      exact starRayBasis_other b J j i (Finset.mem_erase.mp hi).1
    calc
      starRaySet (I.image b) (J.image b) (b j) =
          insert (∑ i ∈ J, b i) ((I.erase j).image b) := by
        rw [starRaySet, hsum, ← Finset.image_erase b.injective]
      _ = insert (starRayBasis b J j j) ((I.erase j).image (starRayBasis b J j)) := by
        rw [starRayBasis_pivot b J j hj, hrest]
      _ = I.image (starRayBasis b J j) := by
        rw [← Finset.image_insert, Finset.insert_erase hjI]

end RaySets

section OneBasis

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] [DecidableEq ι]

/-- Two charts of a subdivision of one smooth cone meet in exactly the cone
on their common rays. This uses the actual sheared bases, not an asserted
fan-intersection property. -/
theorem starRayBasis_cone_inter (b : Module.Basis ι ℝ E)
    (I J : Finset ι) (hJI : J ⊆ I) (p q : ι) (hp : p ∈ J) (hq : q ∈ J) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓
        finiteRayCone (I.image (starRayBasis b J q)) =
      finiteRayCone ((I.image (starRayBasis b J p)) ∩
        (I.image (starRayBasis b J q))) := by
  by_cases hpq : p = q
  · subst q
    simp
  let bp := starRayBasis b J p
  let bq := starRayBasis b J q
  have hpI : p ∈ I := hJI hp
  have hqI : q ∈ I := hJI hq
  have hF : (I.erase q).image bp ⊆ (I.image bp) ∩ (I.image bq) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiI := Finset.mem_of_mem_erase hi
    have hiq := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, hiI, rfl⟩, ?_⟩
    by_cases hip : i = p
    · subst i
      refine Finset.mem_image.mpr ⟨q, hqI, ?_⟩
      exact (starRayBasis_pivot b J q hq).trans (starRayBasis_pivot b J p hp).symm
    · refine Finset.mem_image.mpr ⟨i, hiI, ?_⟩
      rw [starRayBasis_other b J q i hiq, starRayBasis_other b J p i hip]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ :=
      (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ :=
      (mem_finiteRayCone_basis_iff bq I x).mp hx.2
    have hqp : q ∈ J.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
    have hpq' : p ∈ J.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
    have hxq : 0 ≤ b.coord q x - b.coord p x := by
      have h := hxpos q
      change 0 ≤ bp.coord q x at h
      simpa only [bp, starRayBasis_coord, if_pos hqp] using h
    have hyp : 0 ≤ b.coord p x - b.coord q x := by
      have h := hypos p
      change 0 ≤ bq.coord p x at h
      simpa only [bq, starRayBasis_coord, if_pos hpq'] using h
    have hzeroq : bp.repr x q = 0 := by
      change bp.coord q x = 0
      rw [starRayBasis_coord, if_pos hqp]
      linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff bp (I.erase q) x).mpr
    refine ⟨hxpos, ?_⟩
    intro i hi
    by_cases hiq : i = q
    · simpa only [hiq] using hzeroq
    · exact hxzero i (fun hiI => hi (Finset.mem_erase.mpr ⟨hiq, hiI⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

/-- If an old coordinate face omits a focus direction, its intersection
with a new cone has no exceptional-ray coefficient. -/
theorem starRayBasis_cone_inter_old_face (b : Module.Basis ι ℝ E)
    (I J K : Finset ι) (hJI : J ⊆ I) (hKI : K ⊆ I)
    (p : ι) (hp : p ∈ J) (hJK : ¬ J ⊆ K) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓ finiteRayCone (K.image b) =
      finiteRayCone (((I.image (starRayBasis b J p))) ∩ (K.image b)) := by
  let bp := starRayBasis b J p
  have hF : (K.erase p).image b ⊆ (I.image bp) ∩ (K.image b) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiK := Finset.mem_of_mem_erase hi
    have hip := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_image.mpr ⟨i, hiK, rfl⟩⟩
    exact Finset.mem_image.mpr ⟨i, hKI hiK, starRayBasis_other b J p i hip⟩
  obtain ⟨q, hqJ, hqK⟩ := Finset.not_subset.mp hJK
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ := (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ := (mem_finiteRayCone_basis_iff b K x).mp hx.2
    have hqzero : b.coord q x = 0 := hyzero q hqK
    have hpzero : b.coord p x = 0 := by
      by_cases hqp : q = p
      · simpa only [hqp] using hqzero
      · have hqerase : q ∈ J.erase p := Finset.mem_erase.mpr ⟨hqp, hqJ⟩
        have hqnonneg := hxpos q
        change 0 ≤ bp.coord q x at hqnonneg
        rw [starRayBasis_coord, if_pos hqerase, hqzero, zero_sub] at hqnonneg
        have hpnonneg := hypos p
        change 0 ≤ b.coord p x at hpnonneg
        linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff b (K.erase p) x).mpr
    refine ⟨hypos, ?_⟩
    intro i hi
    by_cases hip : i = p
    · subst i
      change b.coord p x = 0
      exact hpzero
    · exact hyzero i (fun hiK => hi (Finset.mem_erase.mpr ⟨hip, hiK⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

end OneBasis

end PaperVerification.ToricGeometry
end Source_ToricStarConeIntersections

section Source_ToricStarFanFaces

/-!
# Restriction of star cones to old fan faces

All ray sets are finite subsets of the actual integer lattice. The exceptional
ray is their sum, and its incidence with an old face is proved from the fan's
actual geometric intersection property.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem image_embed_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) :
    (I.image b).image (embed n) = I.image (integralBasisReal b) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact (integralBasisReal_apply b i).symm

/-- The generic basis identity with finite images in the literal lattice. -/
theorem lattice_starRaySet_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hJI : J ⊆ I) (j : Fin n) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  have hImage (f : Fin n → Lattice n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Lattice n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have h := starRaySet_basis b I J hJI j hj
  rw [hImage b I, hImage b J, hImage (starRayBasis b J j) I] at h
  exact h

theorem embed_starRaySet {n : ℕ} (s t : Finset (Lattice n)) (v : Lattice n) :
    (starRaySet s t v).image (embed n) =
      starRaySet (s.image (embed n)) (t.image (embed n)) (embed n v) := by
  have hsum : embed n (∑ w ∈ t, w) = ∑ w ∈ t.image (embed n), w := by
    rw [map_sum, Finset.sum_image]
    exact fun a _ b _ hab => embed_injective n hab
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_starRaySet _ _ _ _).mpr
    rcases (mem_starRaySet _ _ _ _).mp hz with hsumz | ⟨hzv, hzs⟩
    · exact Or.inl (congrArg (embed n) hsumz |>.trans hsum)
    · exact Or.inr ⟨fun h => hzv (embed_injective n h),
        Finset.mem_image.mpr ⟨z, hzs, rfl⟩⟩
  · intro hx
    rcases (mem_starRaySet _ _ _ _).mp hx with hxsum | ⟨hxv, hxs⟩
    · refine Finset.mem_image.mpr ⟨∑ w ∈ t, w,
        (mem_starRaySet _ _ _ _).mpr (Or.inl rfl), ?_⟩
      exact hsum.trans hxsum.symm
    · obtain ⟨z, hzs, rfl⟩ := Finset.mem_image.mp hxs
      exact Finset.mem_image.mpr ⟨z,
        (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun h => hxv (congrArg (embed n) h), hzs⟩), rfl⟩

theorem latticeRayCone_starRaySet_le {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ≤ latticeRayCone s := by
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact finiteRayCone_starRaySet_le (Finset.image_subset_image hts) (embed n v)

theorem latticeRayCone_star_cover {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (ht : t.Nonempty) {x : Ambient n} (hx : x ∈ latticeRayCone s) :
    ∃ v ∈ t, x ∈ latticeRayCone (starRaySet s t v) := by
  obtain ⟨v, hv, hxv⟩ := finiteRayCone_star_cover
    (Finset.image_subset_image hts) (ht.image (embed n)) hx
  obtain ⟨vZ, hvZ, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨vZ, hvZ, ?_⟩
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact hxv

theorem latticeRayCone_inf_face {n : ℕ} (C F : PointedCone ℝ (Ambient n))
    (hF : F.IsFaceOf C) (s : Finset (Lattice n))
    (hs : ∀ v ∈ s, embed n v ∈ C) :
    latticeRayCone s ⊓ F = latticeRayCone (s.filter (fun v => embed n v ∈ F)) := by
  unfold latticeRayCone
  rw [finiteRayCone_inf_face C F hF _ (by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hs v hv)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hxF⟩, rfl⟩
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hv, hvF⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hvF⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An actual subcone is a subset of the same integral basis as its parent. -/
theorem adapted_basis_for_subcone {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I J : Finset (Fin n)),
      s = I.image b ∧ t = J.image b ∧ J ⊆ I := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  let J := I.filter (fun i => b i ∈ t)
  refine ⟨b, I, J, rfl, ?_, Finset.filter_subset _ _⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2

/-- Every new ray set is literally part of a genuine integral basis. -/
theorem starRaySet_smooth {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      starRaySet s t v = I.image b := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨starRayBasis b J j, I, ?_⟩
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj]

/-- The local star-chart intersection theorem transferred to actual integer
ray sets, with an integral basis adapted to the original cone. -/
theorem star_cones_same_parent_inter {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet s t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet s t w) := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv hw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI p hp,
    lattice_starRaySet_basis b I J hJI q hq]
  unfold latticeRayCone
  rw [Finset.image_inter _ _ (embed_injective n)]
  simp only [image_embed_basis, integralBasisReal_starRayBasis]
  have hImage (f : Fin n → Ambient n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Ambient n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have hInter (S T : Finset (Ambient n)) :
      (letI : DecidableEq (Ambient n) := fun a b => Classical.propDecidable (a = b)
       S ∩ T) = S ∩ T := by
    ext x
    simp only [Finset.mem_inter]
  have h := starRayBasis_cone_inter (integralBasisReal b) I J hJI p q hp hq
  rw [hImage (starRayBasis (integralBasisReal b) J p) I,
    hImage (starRayBasis (integralBasisReal b) J q) I, hInter] at h
  exact h

/-- The sum of all focus rays lies in an old cone exactly when that cone
contains every focus ray. -/
theorem sum_rays_mem_cone_iff {t u : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones) :
    embed n (∑ v ∈ t, v) ∈ latticeRayCone u ↔ t ⊆ u := by
  rw [map_sum]
  constructor
  · exact «Σ».sum_mem_cone_implies_subset ht hu
  · intro htu
    exact Submodule.sum_mem _ (fun v hv => latticeRayCone_generator u (htu hv))

/-- A focus of dimension at least two produces a new ray, distinct from
every original ray of the complete smooth fan. -/
theorem sum_rays_not_mem_rays {t : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hcard : 2 ≤ t.card) : (∑ v ∈ t, v) ∉ «Σ».rays := by
  intro hmem
  have hsingle := «Σ».singleton_mem_of_mem_rays hmem
  have hsub : t ⊆ {∑ v ∈ t, v} := («Σ».sum_rays_mem_cone_iff ht hsingle).mp
    (latticeRayCone_generator _ (Finset.mem_singleton_self _))
  have h := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at h
  omega

/-- Filtering one new ray set by incidence with an old face is explicit:
the exceptional ray survives precisely when the entire focus does. -/
theorem filter_starRaySet_by_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hus : u ⊆ s) (v : Lattice n) :
    (starRaySet s t v).filter (fun w => embed n w ∈ latticeRayCone u) =
      if t ⊆ u then starRaySet u t v else u.erase v := by
  ext w
  have hcone (hws : w ∈ s) : embed n w ∈ latticeRayCone u ↔ w ∈ u := by
    exact «Σ».ray_mem_cone_iff hu ((«Σ».mem_rays_iff w).mpr ⟨s, hs, hws⟩)
  by_cases htu : t ⊆ u
  · simp only [Finset.mem_filter, mem_starRaySet, if_pos htu]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · exact Or.inl hsum
      · exact Or.inr ⟨hwv, (hcone hws).mp hwcone⟩
    · intro hstar
      rcases hstar with hsum | ⟨hwv, hwu⟩
      · refine ⟨Or.inl hsum, ?_⟩
        rw [hsum]
        exact («Σ».sum_rays_mem_cone_iff ht hu).mpr htu
      · exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩
  · simp only [Finset.mem_filter, mem_starRaySet, if_neg htu, Finset.mem_erase]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · rw [hsum] at hwcone
        exact False.elim (htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp hwcone))
      · exact ⟨hwv, (hcone hws).mp hwcone⟩
    · rintro ⟨hwv, hwu⟩
      exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩

/-- Restriction of a new cone to an actual old face is either the
corresponding star cone in that face or its unchanged old rays. -/
theorem star_cone_inter_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (hus : u ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ u then latticeRayCone (starRaySet u t v) else latticeRayCone (u.erase v) := by
  rw [latticeRayCone_inf_face (latticeRayCone s) (latticeRayCone u)
    («Σ».cone_subset_isFaceOf hs hus) _ (by
      intro w hw
      exact latticeRayCone_starRaySet_le hts v (latticeRayCone_generator _ hw)),
    «Σ».filter_starRaySet_by_face hs ht hu hus v]
  split_ifs <;> rfl

/-- The same restriction formula against any old fan cone, using the
actual common face of its old parent. -/
theorem star_cone_inter_old_cone {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ s ∩ u then latticeRayCone (starRaySet (s ∩ u) t v)
      else latticeRayCone ((s ∩ u).erase v) := by
  have hle := latticeRayCone_starRaySet_le hts v
  have heq : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (s ∩ u) := by
    rw [← «Σ».intersection s hs u hu]
    ext x
    exact ⟨fun h => ⟨h.1, hle h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [heq]
  exact «Σ».star_cone_inter_face hs ht
    («Σ».downward s hs _ Finset.inter_subset_left) hts Finset.inter_subset_left v

/-- A new cone and an unchanged old cone have precisely their common-ray
intersection. The focus is not contained in an unchanged old cone. -/
theorem star_cone_inter_unchanged {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : ¬ t ⊆ u) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v ∩ u) := by
  have hnot : ¬ t ⊆ s ∩ u := fun h => htu (h.trans Finset.inter_subset_right)
  rw [«Σ».star_cone_inter_old_cone hs ht hu hts v, if_neg hnot]
  have he : (∑ w ∈ t, w) ∉ u := by
    intro heu
    exact htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp (latticeRayCone_generator u heu))
  congr 1
  ext z
  by_cases hze : z = ∑ w ∈ t, w
  · subst z
    simp [starRaySet, he]
  · simp [starRaySet, hze, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

/-- New cones over any two old cones meet in their exact common-ray cone.
Restriction to the old common face reduces this to the same-parent theorem. -/
theorem star_cones_inter {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : t ⊆ u) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet u t w) := by
  let F := s ∩ u
  have hF : F ∈ «Σ».cones := «Σ».downward s hs F Finset.inter_subset_left
  have htF : t ⊆ F := Finset.subset_inter hts htu
  have hleft := «Σ».star_cone_inter_face hs ht hF hts Finset.inter_subset_left v
  have hright := «Σ».star_cone_inter_face hu ht hF htu Finset.inter_subset_right w
  rw [if_pos htF] at hleft hright
  have hmeet : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      (latticeRayCone (starRaySet s t v) ⊓ latticeRayCone F) ⊓
      (latticeRayCone (starRaySet u t w) ⊓ latticeRayCone F) := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ latticeRayCone F := by
        rw [← «Σ».intersection s hs u hu]
        exact ⟨latticeRayCone_starRaySet_le hts v hx.1,
          latticeRayCone_starRaySet_le htu w hx.2⟩
      exact ⟨⟨hx.1, hxF⟩, ⟨hx.2, hxF⟩⟩
    · exact fun hx => ⟨hx.1.1, hx.2.1⟩
  rw [hmeet, hleft, hright, «Σ».star_cones_same_parent_inter hF htF hv hw]
  congr 1
  ext z
  by_cases hze : z = ∑ y ∈ t, y
  · subst z
    simp [starRaySet]
  · simp [starRaySet, hze, F, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricStarFanFaces

section Source_ToricFiniteConeFamily

/-!
# A finite smooth cone cover and all its faces

The generating cones need not be full dimensional. Each is assumed only to
have a genuine integral-basis ray set; coverage and the actual intersection
identity then propagate to all their subsets.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n))) :
    Finset (Finset (Lattice n)) := C.biUnion Finset.powerset

theorem mem_finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n)))
    (s : Finset (Lattice n)) :
    s ∈ finiteConeFamilyClosure C ↔ ∃ u ∈ C, s ⊆ u := by
  simp [finiteConeFamilyClosure]

/-- Closing a finite smooth cone cover under ray subsets produces an actual
smooth complete fan if the original cone intersections are the common-ray
cones. None of these geometric properties is discarded in the closure. -/
def fanOfFiniteSmoothCones {n : ℕ} (C : Finset (Finset (Lattice n)))
    (hsmooth : ∀ s ∈ C, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b)
    (hinter : ∀ s ∈ C, ∀ t ∈ C,
      latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t))
    (hcover : ∀ x : Ambient n, ∃ s ∈ C, x ∈ latticeRayCone s) :
    SmoothCompleteFan n where
  cones := finiteConeFamilyClosure C
  smooth := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨b, hb⟩ := hsmooth u hu
    exact ⟨b, basisRayIndices b s, (image_basisRayIndices b s (hsu.trans hb)).symm⟩
  downward := by
    intro s hs t hts
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    exact (mem_finiteConeFamilyClosure C t).mpr ⟨u, hu, hts.trans hsu⟩
  intersection := by
    intro s hs t ht
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨v, hv, htv⟩ := (mem_finiteConeFamilyClosure C t).mp ht
    obtain ⟨bu, hbu⟩ := hsmooth u hu
    obtain ⟨bv, hbv⟩ := hsmooth v hv
    have hsets : (s ∩ (u ∩ v)) ∩ t = s ∩ t := by
      ext w
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hws, hwu, hwv⟩, hwt⟩
        exact ⟨hws, hwt⟩
      · rintro ⟨hws, hwt⟩
        exact ⟨⟨hws, hsu hws, htv hwt⟩, hwt⟩
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      have hxuv : x ∈ latticeRayCone (u ∩ v) := by
        rw [← hinter u hu v hv]
        exact ⟨latticeRayCone_mono hsu hxs, latticeRayCone_mono htv hxt⟩
      have hxmid : x ∈ latticeRayCone (s ∩ (u ∩ v)) := by
        rw [← latticeRayCone_inter_of_subsets_basis bu s (u ∩ v)
          (hsu.trans hbu) (Finset.inter_subset_left.trans hbu)]
        exact ⟨hxs, hxuv⟩
      have hmidv : s ∩ (u ∩ v) ⊆ v :=
        Finset.inter_subset_right.trans Finset.inter_subset_right
      have hxfin : x ∈ latticeRayCone ((s ∩ (u ∩ v)) ∩ t) := by
        rw [← latticeRayCone_inter_of_subsets_basis bv (s ∩ (u ∩ v)) t
          (hmidv.trans hbv) (htv.trans hbv)]
        exact ⟨hxmid, hxt⟩
      simpa only [hsets] using hxfin
    · intro hx
      exact ⟨latticeRayCone_mono Finset.inter_subset_left hx,
        latticeRayCone_mono Finset.inter_subset_right hx⟩
  complete := by
    intro x
    obtain ⟨s, hs, hx⟩ := hcover x
    exact ⟨s, (mem_finiteConeFamilyClosure C s).mpr ⟨s, hs, Finset.Subset.refl _⟩, hx⟩

end PaperVerification.ToricGeometry
end Source_ToricFiniteConeFamily

section Source_ToricStarSubdivision

/-!
# Smooth star subdivision of an actual complete fan

The subdivision is constructed from actual finite ray sets and their actual
nonnegative spans. Smoothness follows from an integral transvection,
completeness from the minimum-coefficient covering, and the fan intersection
condition from the proved old-face restrictions and local chart calculation.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The generating cones of the star subdivision: retain cones not containing
the focus and subdivide each remaining cone at every focus ray. -/
def starCandidates (t : Finset (Lattice n)) : Finset (Finset (Lattice n)) :=
  «Σ».cones.biUnion (fun s => if t ⊆ s then t.image (starRaySet s t) else {s})

theorem mem_starCandidates (t s : Finset (Lattice n)) :
    s ∈ «Σ».starCandidates t ↔
      (s ∈ «Σ».cones ∧ ¬ t ⊆ s) ∨
      ∃ u ∈ «Σ».cones, ∃ v ∈ t, t ⊆ u ∧ s = starRaySet u t v := by
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := Finset.mem_biUnion.mp hs
    by_cases htu : t ⊆ u
    · rw [if_pos htu] at hsu
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hsu
      exact Or.inr ⟨u, hu, v, hv, htu, he.symm⟩
    · rw [if_neg htu] at hsu
      have hsu := Finset.mem_singleton.mp hsu
      subst s
      exact Or.inl ⟨hu, htu⟩
  · rintro (⟨hs, hts⟩ | ⟨u, hu, v, hv, htu, rfl⟩)
    · apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, by rw [if_neg hts]; exact Finset.mem_singleton_self s⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, ?_⟩
      rw [if_pos htu]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem starCandidates_smooth (t : Finset (Lattice n)) :
    ∀ s ∈ «Σ».starCandidates t, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b := by
  intro s hs
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨u, hu, v, hv, htu, rfl⟩
  · obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
    exact ⟨b, Finset.image_subset_image (Finset.subset_univ I)⟩
  · obtain ⟨b, I, he⟩ := «Σ».starRaySet_smooth hu htu hv
    refine ⟨b, ?_⟩
    rw [he]
    exact Finset.image_subset_image (Finset.subset_univ I)

theorem starCandidates_intersection (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) :
    ∀ s ∈ «Σ».starCandidates t, ∀ u ∈ «Σ».starCandidates t,
      latticeRayCone s ⊓ latticeRayCone u = latticeRayCone (s ∩ u) := by
  intro s hs u hu
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨s', hs', v, hv, hts', rfl⟩
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».intersection s hs u hu
    · rw [inf_comm, Finset.inter_comm]
      exact «Σ».star_cone_inter_unchanged hu' ht hs htu' hts w
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».star_cone_inter_unchanged hs' ht hu hts' htu v
    · exact «Σ».star_cones_inter hs' ht hu' hts' htu' hv hw

theorem starCandidates_cover (t : Finset (Lattice n)) (ht : t.Nonempty) :
    ∀ x : Ambient n, ∃ s ∈ «Σ».starCandidates t, x ∈ latticeRayCone s := by
  intro x
  obtain ⟨s, hs, hx⟩ := «Σ».complete x
  by_cases hts : t ⊆ s
  · obtain ⟨v, hv, hxv⟩ := latticeRayCone_star_cover hts ht hx
    refine ⟨starRaySet s t v, ?_, hxv⟩
    exact («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩)
  · exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), hx⟩

/-- The smooth complete star-subdivided fan, with every defining geometric
property proved from the original fan and the nonempty focus cone. -/
def starSubdivision (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    SmoothCompleteFan n :=
  fanOfFiniteSmoothCones («Σ».starCandidates t)
    («Σ».starCandidates_smooth t) («Σ».starCandidates_intersection t ht)
    («Σ».starCandidates_cover t hne)

/-- An unchanged old cone is literally a cone of the new fan. -/
theorem mem_starSubdivision_of_unchanged (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : ¬ t ⊆ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mpr
  exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), Finset.Subset.refl s⟩

/-- Every explicitly subdivided cone is literally a cone of the new fan. -/
theorem starRaySet_mem_starSubdivision (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    starRaySet s t v ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) _).mpr
  exact ⟨starRaySet s t v,
    («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩),
    Finset.Subset.refl _⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricStarSubdivision

section Source_ToricStarPurity




/-!
# Full cone extensions survive star subdivision

Purity is derived from the original fan's full-cone extensions and the
explicit ray-set replacement. No general purity theorem is assumed.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem starRaySet_mono {n : ℕ} {s u : Finset (Lattice n)}
    (hsu : s ⊆ u) (t : Finset (Lattice n)) (p : Lattice n) :
    starRaySet s t p ⊆ starRaySet u t p := by
  intro v hv
  apply (mem_starRaySet _ _ _ _).mpr
  rcases (mem_starRaySet _ _ _ _).mp hv with hsum | ⟨hvp, hvs⟩
  · exact Or.inl hsum
  · exact Or.inr ⟨hvp, hsu hvs⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem starRaySet_card {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {p : Lattice n} (hp : p ∈ t) :
    (starRaySet s t p).card = s.card := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (htJ ▸ hp)
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj,
    Finset.card_image_of_injective I (starRayBasis b J j).injective,
    Finset.card_image_of_injective I b.injective]

/-- Every cone of the actual subdivided fan extends to a full cone whenever
that property holds for the original fan. -/
theorem isPure_starSubdivision (hpure : «Σ».IsPure)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    («Σ».starSubdivision t ht hne).IsPure := by
  intro c hc
  obtain ⟨u, hu, hcu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) c).mp hc
  rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
    ⟨u', hu', p, hp, htu', rfl⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u hu
    by_cases hts : t ⊆ s
    · obtain ⟨p, hp, hpu⟩ := Finset.not_subset.mp htu
      refine ⟨starRaySet s t p,
        «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp, ?_, ?_⟩
      · intro v hv
        exact (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun hvp => hpu (hvp ▸ hcu hv), hus (hcu hv)⟩)
      · rw [«Σ».starRaySet_card hs hts hp, hscard]
    · exact ⟨s, «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts, hcu.trans hus, hscard⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u' hu'
    have hts := htu'.trans hus
    exact ⟨starRaySet s t p,
      «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp,
      hcu.trans (starRaySet_mono hus t p),
      («Σ».starRaySet_card hs hts hp).trans hscard⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricStarPurity

section Source_ToricWallUniqueness




/-!
# Uniqueness of the opposite smooth cone at a wall

Two prospective opposite rays with the same negative normal coordinate
produce a common point by adding nonnegative wall coordinates. The fan's
actual common-ray intersection forces the rays to coincide.
-/


namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An integral wall in a genuine basis has at most one adjacent fan ray
whose missing coordinate is strictly negative. The two coefficients are
scaled to the same height before applying the genuine fan intersection. -/
theorem opposite_wall_ray_unique_of_negative (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j < 0) (hjz : b.repr z j < 0) : w = z := by
  let W := (Finset.univ.erase j).image b
  let B := integralBasisReal b
  let α : ℝ := -(b.repr z j : ℝ)
  let β : ℝ := -(b.repr w j : ℝ)
  have hα : 0 < α := neg_pos.mpr (by exact_mod_cast hjz)
  have hβ : 0 < β := neg_pos.mpr (by exact_mod_cast hjw)
  let d : Fin n → ℝ := fun i => B.repr (β • embed n z - α • embed n w) i
  let u : Fin n → ℝ := fun i => |d i| + d i
  let v : Fin n → ℝ := fun i => |d i|
  have hdj : d j = 0 := by
    simp only [d, B, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      integralBasisReal_repr, smul_eq_mul, α, β]
    ring
  have hu (i : Fin n) : 0 ≤ u i := by
    have h := neg_abs_le (d i)
    dsimp only [u]
    linarith
  have hv (i : Fin n) : 0 ≤ v i := abs_nonneg _
  have huj : u j = 0 := by simp [u, hdj]
  have hvj : v j = 0 := by simp [v, hdj]
  have hwall (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (haj : a j = 0)
      (y : Lattice n) : (∑ i, a i • B i) ∈ latticeRayCone (insert y W) := by
    apply Submodule.sum_mem
    intro i hi
    by_cases hij : i = j
    · subst i
      simp only [haj, zero_smul]
      exact Submodule.zero_mem _
    · rw [integralBasisReal_apply]
      apply PointedCone.smul_mem _ (ha i)
      apply latticeRayCone_generator
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, rfl⟩)
  have hsum : (∑ i, u i • B i) =
      (∑ i, v i • B i) + (β • embed n z - α • embed n w) := by
    simp only [u, add_smul, Finset.sum_add_distrib, v, d, Module.Basis.sum_repr]
  have hbalance : α • embed n w + (∑ i, u i • B i) =
      β • embed n z + (∑ i, v i • B i) := by
    rw [hsum]
    abel
  have hxw : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert w W) :=
    (latticeRayCone (insert w W)).add_mem
      (PointedCone.smul_mem _ hα.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall u hu huj w)
  have hxz : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert z W) := by
    rw [hbalance]
    exact (latticeRayCone (insert z W)).add_mem
      (PointedCone.smul_mem _ hβ.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall v hv hvj z)
  have hxmeet : α • embed n w + (∑ i, u i • B i) ∈
      latticeRayCone ((insert w W) ∩ (insert z W)) := by
    rw [← «Σ».intersection _ hw _ hz]
    exact ⟨hxw, hxz⟩
  have hface := «Σ».cone_subset_isFaceOf hw
    (Finset.inter_subset_left : insert w W ∩ insert z W ⊆ insert w W)
  have hwmeet : embed n w ∈ latticeRayCone ((insert w W) ∩ (insert z W)) :=
    hface.mem_of_smul_add_mem
      (latticeRayCone_generator _ (Finset.mem_insert_self _ _)) (hwall u hu huj w) hα hxmeet
  have hwrays : w ∈ «Σ».rays := («Σ».mem_rays_iff w).mpr
    ⟨insert w W, hw, Finset.mem_insert_self _ _⟩
  have hwz : w ∈ insert z W := («Σ».ray_mem_cone_iff hz hwrays).mp
    (latticeRayCone_mono Finset.inter_subset_right hwmeet)
  rcases Finset.mem_insert.mp hwz with hwz | hwW
  · exact hwz
  · obtain ⟨i, hi, hwi⟩ := Finset.mem_image.mp hwW
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [← hwi] at hjw
    simp only [Module.Basis.repr_self_apply, if_neg hij] at hjw
    norm_num at hjw

/-- The normalized smooth-wall form used by primitive contraction relations. -/
theorem opposite_wall_ray_unique (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j = -1) (hjz : b.repr z j = -1) : w = z :=
  «Σ».opposite_wall_ray_unique_of_negative b j w z hw hz (by omega) (by omega)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end Source_ToricWallUniqueness

section Source_ToricCompleteWalls




/-!
# Genuine opposite full cones in a complete smooth fan

Completeness is used through a small negative transverse perturbation of
the sum of the wall rays. Purity extends the resulting cone. The integral
basis condition then forces the opposite ray's transverse coordinate to
be exactly minus one.
-/


namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem basis_wall_card (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) :
    ((Finset.univ.erase j).image b).card=n-1 := by
  rw [Finset.card_image_of_injective _ b.injective,Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp

theorem basis_wall_coord_zero (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (v : Lattice n) (hv : v∈(Finset.univ.erase j).image b) : b.repr v j=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  simp only [Module.Basis.repr_self_apply,if_neg (Finset.mem_erase.mp hi).1]

/-- Smoothness makes the opposite transverse coefficient a unit in Z;
its sign therefore determines it exactly. -/
theorem opposite_wall_coord_eq_neg_one
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (w : Lattice n)
    (hwcone : insert w ((Finset.univ.erase j).image b)∈«Σ».cones)
    (hwneg : b.repr w j<0) : b.repr w j = -1 := by
  let F := (Finset.univ.erase j).image b
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hn : 0<n := by have h := j.isLt; omega
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    omega
  obtain ⟨c,hc⟩ := «Σ».full_cone_basis hwcone hcard
  obtain ⟨l,hl,hcl⟩ := Finset.mem_image.mp (hc ▸ Finset.mem_insert_self w F)
  have hzero (i : Fin n) (hil : i≠l) : b.repr (c i) j=0 := by
    have hci : c i∈insert w F := hc.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    rcases Finset.mem_insert.mp hci with hiw | hiF
    · exact (hil (c.injective (hiw.trans hcl.symm))).elim
    · exact basis_wall_coord_zero b j (c i) hiF
  have hprod : b.repr w j * c.repr (b j) l = 1 := by
    calc
      b.repr w j * c.repr (b j) l = ∑ i, c.repr (b j) i * b.repr (c i) j := by
        rw [Finset.sum_eq_single l]
        · rw [hcl,mul_comm]
        · intro i hi hil
          rw [hzero i hil,mul_zero]
        · intro hl
          exact (hl (Finset.mem_univ l)).elim
      _ = b.repr (∑ i,c.repr (b j) i • c i) j := by
        simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
      _ = 1 := by rw [c.sum_repr]; simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h
  · omega
  · exact h

/-- A negative coordinate of a cone vector must occur in one of the
actual generating rays. -/
theorem exists_ray_negative_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (s : Finset (Lattice n)) (x : Ambient n) (hx : x∈latticeRayCone s)
    (hxneg : (integralBasisReal b).repr x j<0) :
    ∃ w∈s,b.repr w j<0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨c,hc,hcx⟩ := hx
  have hsum : 0≤∑ v∈s.image (embed n),c v * (integralBasisReal b).repr v j := by
    apply Finset.sum_nonneg
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact mul_nonneg (hc _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
      (by rw [integralBasisReal_repr]; exact_mod_cast hn w hw)
  have he := congrArg (fun y=>(integralBasisReal b).repr y j) hcx
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul] at he
  rw [he] at hsum
  exact (not_lt_of_ge hsum) hxneg

/-- An actual opposite full cone exists across every facet of every full
cone; all ray sets and the transverse integral coordinate are explicit. -/
theorem exists_full_opposite_wall (hpure : «Σ».IsPure) (s : «Σ».fullCones) (j : Fin n) :
    ∃ t : «Σ».fullCones, ∃ w : Lattice n,
      t.val=insert w ((Finset.univ.erase j).image («Σ».fullConeBasis s)) ∧
      («Σ».fullConeBasis s).repr w j = -1 ∧
      s.val∩t.val=(Finset.univ.erase j).image («Σ».fullConeBasis s) ∧
      w∈t.val ∧ w∉s.val := by
  let b := «Σ».fullConeBasis s
  let F := (Finset.univ.erase j).image b
  have hFs : F⊆s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.image_subset_image (Finset.erase_subset j _)
  have hF : F∈«Σ».cones := «Σ».downward s.val («Σ».fullCones_mem s) F hFs
  obtain ⟨ε,hε,q,hq,hFq,hx⟩ := «Σ».exists_small_perturbation_in_containing_cone hF
    (-embed n (b j))
  obtain ⟨t,ht,hqt,htcard⟩ := hpure q hq
  let t' : «Σ».fullCones := ⟨t,Finset.mem_filter.mpr ⟨ht,htcard⟩⟩
  have hFt : F⊆t := hFq.trans hqt
  have hx' : (∑ u∈F,embed n u)+ε • (-embed n (b j))∈latticeRayCone t :=
    latticeRayCone_mono hqt hx
  have hneg : (integralBasisReal b).repr
      ((∑ u∈F,embed n u)+ε • (-embed n (b j))) j<0 := by
    have hz : (integralBasisReal b).repr (∑ u∈F,embed n u) j=0 := by
      rw [map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro u hu
      rw [integralBasisReal_repr,basis_wall_coord_zero b j u hu,Int.cast_zero]
    simp only [map_add,map_smul,map_neg,Finsupp.add_apply,Finsupp.smul_apply,
      Finsupp.neg_apply,integralBasisReal_repr,Module.Basis.repr_self_apply,
      if_true,Int.cast_one,smul_eq_mul,hz,zero_add,mul_neg,mul_one]
    exact neg_neg_of_pos hε
  obtain ⟨w,hwt,hwneg⟩ := exists_ray_negative_coordinate b j t _ hx' hneg
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hins : insert w F⊆t := Finset.insert_subset hwt hFt
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    have hn := j.isLt
    omega
  have htF : t=insert w F :=
    (Finset.eq_of_subset_of_card_le hins (by rw [hcard,htcard])).symm
  have hwcone : insert w F∈«Σ».cones := htF ▸ ht
  have hwj : b.repr w j = -1 := «Σ».opposite_wall_coord_eq_neg_one b j w hwcone hwneg
  have hws : w∉s.val := by
    intro hws
    obtain ⟨i,hi,hwi⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hws)
    rw [← hwi,Module.Basis.repr_self_apply] at hwneg
    split_ifs at hwneg <;> omega
  have hmeet : s.val∩t=F := by
    rw [htF]
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hvs,rfl|hvF⟩
      · exact (hws hvs).elim
      · exact hvF
    · intro hvF
      exact ⟨hFs hvF,Or.inr hvF⟩
  exact ⟨t',w,htF,hwj,hmeet,hwt,hws⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.opposite_wall_coord_eq_neg_one
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_full_opposite_wall
end Source_ToricCompleteWalls

section Source_ToricWallPolytopeBounds

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan
variable {n : ℕ} («Σ» : SmoothCompleteFan n)
def integerWallSlack (a : Lattice n→ℤ) (s : «Σ».fullCones) (u : Lattice n) : ℤ :=
  a u+integerPairing u («Σ».cartierLatticePoint a s)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end Source_ToricWallPolytopeBounds

section Source_ToricWallCurveDegrees




/-!
# Actual invariant-curve degree equals integral wall slack

The orbit cone is the wall obtained by deleting one basis ray. The
quotient lattice has one coordinate. The original ray projects to `1`
and the opposite ray to `-1`; normalization at the original full cone
makes the first restricted coefficient zero and the second exactly the
integral wall slack. The genuine pullback-sheaf isomorphism and the
proved degree formula on the actual curve give the equality.
-/


universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

theorem wall_complementaryEmbedding
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    complementaryEmbedding («Σ».wallIndices s j) q=j := by
  have hnot : complementaryEmbedding («Σ».wallIndices s j) q∉«Σ».wallIndices s j :=
    (mem_range_complementaryEmbedding_iff _ _).mp ⟨q,rfl⟩
  by_contra hne
  exact hnot (Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩)

theorem wall_quotient_coordinate (v : Lattice n)
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) v q =
      («Σ».fullConeBasis s).repr v j := by
  change («Σ».fullConeBasis s).repr v (complementaryEmbedding («Σ».wallIndices s j) q)=_
  rw [«Σ».wall_complementaryEmbedding]

theorem wallCone_subset_full :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆s.val := by
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

theorem fullConeBasis_mem_sdiff_wall :
    «Σ».fullConeBasis s j∈s.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  · intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hij := («Σ».fullConeBasis s).injective he
    exact (Finset.mem_erase.mp hi).1 hij

theorem wall_quotient_positive :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».fullConeBasis s j) = (fun _=>1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate]
  simp

theorem wall_quotient_negative (w : Lattice n)
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) w = (fun _=>-1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate,hw]

theorem wall_positive_ne_negative :
    (fun _=>1 : Lattice (n-(«Σ».wallIndices s j).card))≠(fun _=>-1) := by
  intro h
  let q : Fin (n-(«Σ».wallIndices s j).card) :=
    ⟨0,by rw [«Σ».wallIndices_codimension]; omega⟩
  have hq := congrFun h q
  norm_num at hq

def wallRestrictionCoefficients (a : Lattice n→ℤ) :
    Lattice (n-(«Σ».wallIndices s j).card)→ℤ :=
  «Σ».orbitRestrictionCoefficients («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)

theorem wallRestriction_positive (a : Lattice n→ℤ) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>1)=0 := by
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_positive s j,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s) («Σ».fullCones_mem s)
      («Σ».wallCone_subset_full s j) («Σ».fullConeBasis_mem_sdiff_wall s j),
    «Σ».cartierLatticePoint_pairing a s («Σ».fullConeBasis s j)
      (Finset.mem_sdiff.mp («Σ».fullConeBasis_mem_sdiff_wall s j)).1]
  ring

theorem wallRestriction_negative (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>-1)=«Σ».integerWallSlack a s w := by
  have hwF : w∉(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    intro hw
    have hzero := basis_wall_coord_zero («Σ».fullConeBasis s) j w hw
    omega
  have hFt : («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆t.val := by
    rw [ht]
    exact Finset.subset_insert _ _
  have hwt : w∈t.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    rw [ht]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,hwF⟩
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_negative s j w hwj,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)
      («Σ».fullCones_mem t) hFt hwt]
  rfl

theorem wallRestriction_sum (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    (∑ u∈(«Σ».wallCurveFan s j).rays,«Σ».wallRestrictionCoefficients s j a u) =
      «Σ».integerWallSlack a s w := by
  rw [(«Σ».wallCurveFan s j).oneDimensional_rays («Σ».wallIndices_codimension s j),
    Finset.sum_pair («Σ».wall_positive_ne_negative s j),
    «Σ».wallRestriction_positive s j a,«Σ».wallRestriction_negative s j a t w ht hwj,zero_add]

variable (k : Type u) [Field k] (hpure : «Σ».IsPure)

/-- The bound in the paper is applied to the genuine restricted line
bundle on the actual invariant curve. Its degree is the wall slack. -/
theorem wallCurve_fanCartier_hasDegree (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj
        («Σ».fanCartierData k hpure a).sheaf) («Σ».integerWallSlack a s w) := by
  have hm : ∀ u∈(«Σ».wallIndices s j).image («Σ».fullConeBasis s),
      integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
    intro u hu
    exact «Σ».cartierLatticePoint_pairing a s u («Σ».wallCone_subset_full s j hu)
  let F := «Σ».orbitCartierPullbackIso k («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) hpure a («Σ».cartierLatticePoint a s) hm
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k F _).mpr
  have h := («Σ».wallCurveFan s j).oneDimensionalFanCartier_hasDegree
    («Σ».wallIndices_codimension s j) k
    («Σ».completeQuotientStarFan_isPure hpure («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j)) («Σ».wallRestrictionCoefficients s j a)
  rwa [«Σ».wallRestriction_sum s j a t w ht hwj] at h

/-- An arbitrary Cartier sheaf is handled through its proved actual
isomorphism to the recovered invariant presentation. -/
theorem wallCurve_cartier_hasDegree (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) := by
  let F := («Σ».cartierData_linearlyEquivalent_fanCartier k hpure D).some
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) _).mpr
  exact «Σ».wallCurve_fanCartier_hasDegree s j k hpure _ t w ht hwj

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_fanCartier_hasDegree
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_cartier_hasDegree
end Source_ToricWallCurveDegrees

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_fanCartier_hasDegree
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_cartier_hasDegree
