module

public import PaperVerification.SegreTwistingRestrictions
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Full Laurent coefficient coordinates on all Čech terms

The whole degree component of every coordinate localization is identified
with its allowed Laurent coefficients. The finite product over chart tuples
commutes with finite-support Laurent coefficients. These equivalences retain
all monomials and all chart tuples, including repeated indices.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PaperVerification.Segre.CoordinateLocalization

open CechMonomials
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- Laurent exponents of fixed degree allowed on a coordinate intersection. -/
def allowedDegreeExponents (S : Finset I) (t : ℤ) : Set (DegreeExponent I t) :=
  {a | ∀ i, i ∉ S → 0≤a.val i}

abbrev coefficientSpace (S : Finset I) (t : ℤ) :
    Submodule K (DegreeExponent I t →₀ K) :=
  Finsupp.supported K K (allowedDegreeExponents S t)

/-- Exchanging the order of the degree and denominator conditions. -/
def allowedDegreeEquiv (S : Finset I) (t : ℤ) :
    {a : allowedExponents S // totalDegree S a=t} ≃ allowedDegreeExponents S t where
  toFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  invFun a := ⟨⟨a.val.val,a.property⟩,a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Passing to coefficients preserves exactly the entire homogeneous submodule. -/
def homogeneousCoefficients (S : Finset I) (t : ℤ) :
    localDegree (K := K) S t ≃ₗ[K]
      Finsupp.supported K K {a : allowedExponents S | totalDegree S a=t} where
  toFun z := ⟨z.val.coeff,z.property⟩
  invFun z := ⟨AddMonoidAlgebra.ofCoeff z.val,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every Laurent coefficient on the intersection, with no truncation. -/
def localCoefficientEquiv (S : Finset I) (t : ℤ) :
    localDegree (K := K) S t ≃ₗ[K] coefficientSpace (K := K) S t :=
  (homogeneousCoefficients (K := K) S t).trans
    ((Finsupp.supportedEquivFinsupp (R := K) {a : allowedExponents S | totalDegree S a=t}).trans
      ((Finsupp.domLCongr (allowedDegreeEquiv S t)).trans
        (Finsupp.supportedEquivFinsupp (R := K) (allowedDegreeExponents S t)).symm))

/-- The equivalence reads the literal coefficient whenever the exponent is allowed. -/
theorem localCoefficientEquiv_apply (S : Finset I) (t : ℤ)
    (z : localDegree (K := K) S t) (a : DegreeExponent I t)
    (ha : a ∈ allowedDegreeExponents S t) :
    (localCoefficientEquiv S t z).val a=z.val.coeff ⟨a.val,ha⟩ := by
  classical
  simp [localCoefficientEquiv,homogeneousCoefficients,allowedDegreeEquiv,
    Finsupp.supportedEquivFinsupp_symm_apply_coe,Finsupp.extendDomain_apply,ha]; rfl

theorem localCoefficientEquiv_apply_of_not_allowed (S : Finset I) (t : ℤ)
    (z : localDegree (K := K) S t) (a : DegreeExponent I t)
    (ha : a ∉ allowedDegreeExponents S t) : (localCoefficientEquiv S t z).val a=0 :=
  ((Finsupp.mem_supported' K _).mp (localCoefficientEquiv S t z).property) a ha

/-- The coefficient inclusion on a smaller chart is literally extension by zero. -/
def coefficientRestriction {S T : Finset I} (h : S ⊆ T) (t : ℤ) :
    coefficientSpace (K := K) S t →ₗ[K] coefficientSpace (K := K) T t :=
  Submodule.inclusion (Finsupp.supported_mono (fun a ha i hi => ha i (fun hs => hi (h hs))))

@[simp] theorem coefficientRestriction_apply {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : coefficientSpace (K := K) S t) (a : DegreeExponent I t) :
    (coefficientRestriction h t z).val a = z.val a := rfl

/-- Actual coordinate restriction leaves every Laurent coefficient unchanged. -/
theorem localCoefficientEquiv_restriction {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : localDegree (K := K) S t) :
    localCoefficientEquiv T t (degreeRestriction h t z)=
      coefficientRestriction h t (localCoefficientEquiv S t z) := by
  classical
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ allowedDegreeExponents S t
  · have haT : a ∈ allowedDegreeExponents T t := fun i hi => ha i (fun hs => hi (h hs))
    rw [localCoefficientEquiv_apply T t _ a haT]
    change (localRestriction h z.val).coeff ⟨a.val,haT⟩=
      (localCoefficientEquiv S t z).val a
    rw [localCoefficientEquiv_apply S t z a ha]
    exact localRestriction_coeff h z.val ⟨a.val,ha⟩
  · rw [show (coefficientRestriction h t (localCoefficientEquiv S t z)).val a=0 from
      localCoefficientEquiv_apply_of_not_allowed S t z a ha]
    by_cases haT : a ∈ allowedDegreeExponents T t
    · rw [localCoefficientEquiv_apply T t _ a haT]
      change Finsupp.mapDomain (exponentInclusion h) z.val.coeff ⟨a.val,haT⟩=0
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨b,hb⟩
      apply ha
      have hv : b.val=a.val := congrArg Subtype.val hb
      change ∀ i, i ∉ S → 0 ≤ a.val i
      have hb : ∀ i, i ∉ S → 0 ≤ b.val i := b.property
      simpa only [hv] using hb
    · exact localCoefficientEquiv_apply_of_not_allowed T t _ a haT

end PaperVerification.Segre.CoordinateLocalization

namespace PaperVerification.Segre.CechMonomials

open CoordinateLocalization
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- All distinct chart indices appearing in a tuple. -/
def tupleCoordinates {q : ℕ} (a : Fin q → I) : Finset I := Finset.univ.image a

@[simp] theorem mem_tupleCoordinates {q : ℕ} (a : Fin q → I) (i : I) :
    i ∈ tupleCoordinates a ↔ i ∈ Set.range a := by
  simp [tupleCoordinates,Set.mem_range]

theorem tupleCoordinates_nonempty {q : ℕ} (a : Fin (q+1) → I) :
    (tupleCoordinates a).Nonempty := ⟨a 0,by simp⟩

theorem allowedDegreeExponents_iff {q : ℕ} (t : ℤ) (a : Fin q → I)
    (v : DegreeExponent I t) :
    v ∈ allowedDegreeExponents (tupleCoordinates a) t ↔ negativeSupport v.val ⊆ Set.range a := by
  constructor
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge (h i (by simpa using hn))) hi
  · intro h i hi
    by_contra hn
    exact hi ((mem_tupleCoordinates a i).mpr (h (lt_of_not_ge hn)))

section FiniteExchange

variable {A B : Type*} [Fintype B]

/-- Finite products commute with arbitrary finite-support coefficient expansions. -/
def finitePiExchange : (A →₀ B → K) ≃ₗ[K] B → A →₀ K where
  toFun f b := Finsupp.mapRange (fun g : B → K => g b) rfl f
  invFun f := by
    classical
    exact Finsupp.onFinset (Finset.univ.biUnion (fun b => (f b).support))
      (fun a b => f b a) (by
        intro a ha
        by_contra hn
        apply ha
        funext b
        have hb : a ∉ (f b).support := by
          intro hm
          exact hn (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ b,hm⟩)
        exact Finsupp.notMem_support_iff.mp hb)
  left_inv f := by ext a b; rfl
  right_inv f := by ext b a; rfl
  map_add' f g := by ext b a; rfl
  map_smul' c f := by ext b a; rfl

@[simp] theorem finitePiExchange_apply (f : A →₀ B → K) (b : B) (a : A) :
    (finitePiExchange (K := K) (A := A) (B := B)) f b a=f a b := rfl

@[simp] theorem finitePiExchange_symm_apply (f : B → A →₀ K) (a : A) (b : B) :
    (finitePiExchange (K := K) (A := A) (B := B)).symm f a b=f b a := rfl

end FiniteExchange

/-- The Laurent support condition is exactly the allowed denominator condition on each tuple. -/
def laurentCoefficientEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t q ≃ₗ[K]
      ((a : Fin q → I) → coefficientSpace (K := K) (tupleCoordinates a) t) where
  toFun f a := ⟨(finitePiExchange (K := K) (A := DegreeExponent I t) (B := Fin q → I)) f.val a,by
    intro v hv
    rw [allowedDegreeExponents_iff]
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hv) (f.property v a hn)⟩
  invFun f := ⟨(finitePiExchange (K := K) (A := DegreeExponent I t) (B := Fin q → I)).symm (fun a => (f a).val),by
    intro v a hn
    apply ((Finsupp.mem_supported' K _).mp (f a).property) v
    rwa [allowedDegreeExponents_iff]⟩
  left_inv f := by apply Subtype.ext; ext v a; rfl
  right_inv f := by funext a; apply Subtype.ext; ext v; rfl
  map_add' f g := by funext a; apply Subtype.ext; ext v; rfl
  map_smul' c f := by funext a; apply Subtype.ext; ext v; rfl

@[simp] theorem laurentCoefficientEquiv_apply (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin q → I)
    (v : DegreeExponent I t) :
    (laurentCoefficientEquiv t q f a).val v=f.val v a := rfl

/-- The whole tuple product of homogeneous localization components is the Laurent Čech term. -/
def laurentLocalEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t q ≃ₗ[K]
      ((a : Fin q → I) → localDegree (K := K) (tupleCoordinates a) t) :=
  (laurentCoefficientEquiv t q).trans
    (LinearEquiv.piCongrRight (fun a => (localCoefficientEquiv (tupleCoordinates a) t).symm))

theorem laurentLocalEquiv_coeff (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin q → I)
    (v : DegreeExponent I t) :
    (localCoefficientEquiv (tupleCoordinates a) t (laurentLocalEquiv t q f a)).val v=f.val v a := by
  simp only [laurentLocalEquiv,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply,
    LinearEquiv.apply_symm_apply,laurentCoefficientEquiv_apply]

end PaperVerification.Segre.CechMonomials
