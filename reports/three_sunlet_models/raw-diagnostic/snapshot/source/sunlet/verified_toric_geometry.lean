module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import sunlet.verified_generic_conclusions

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_TORIC_GEOMETRY_IMPORTS_READY"

section Stage_LaurentMonomials



/-!
# Faithful Laurent monomials in the polynomial fraction field

Integer exponents are retained literally. The group algebra is proved to be
the localization of the polynomial algebra at the product of its variables;
the resulting map into the ordinary polynomial fraction field is injective.
The localization proof is the additive version of the checked TauCeti lemma
`MonoidAlgebra.isLocalization_away_mapDomainRingHom`, at revision
6b896c7c411221eb78639e4be8ead6e479a62893 (Apache 2.0).
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.LaurentMonomials

section Localization

variable (R : Type*) [CommSemiring R] {M N : Type*}
  [AddCommMonoid M] [AddCommMonoid N]

theorem additive_monomial_localization (f : M →+ N)
    (hf : Function.Injective f) (x : M)
    (hx : IsUnit (AddMonoidAlgebra.single (f x) (1 : R)))
    (hsurj : ∀ y : N, ∃ n : ℕ,y+n • f x ∈ Set.range f) :
    letI := (AddMonoidAlgebra.mapDomainRingHom R f).toAlgebra
    IsLocalization.Away (AddMonoidAlgebra.single x (1 : R))
      (AddMonoidAlgebra R N) := by
  letI := (AddMonoidAlgebra.mapDomainRingHom R f).toAlgebra
  have halg : ∀ a : AddMonoidAlgebra R M,
      algebraMap (AddMonoidAlgebra R M) (AddMonoidAlgebra R N) a =
        AddMonoidAlgebra.mapDomain f a := fun a => by
    rw [RingHom.algebraMap_toAlgebra,AddMonoidAlgebra.mapDomainRingHom_apply]
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [halg,AddMonoidAlgebra.mapDomain_single]
    exact hx
  · intro s
    induction s using AddMonoidAlgebra.induction_on with
    | of y =>
        obtain ⟨n,z,hz⟩ := hsurj y
        refine ⟨n,AddMonoidAlgebra.single z 1,?_⟩
        simp [halg,hz,AddMonoidAlgebra.single_pow]
    | add s t hs ht =>
        obtain ⟨n,a,ha⟩ := hs
        obtain ⟨k,b,hb⟩ := ht
        refine ⟨n+k,a*AddMonoidAlgebra.single x 1^k+
          b*AddMonoidAlgebra.single x 1^n,?_⟩
        simp only [map_add,map_mul,map_pow]
        rw [← ha,← hb]
        ring
    | smul r s hs =>
        obtain ⟨n,a,ha⟩ := hs
        refine ⟨n,algebraMap R (AddMonoidAlgebra R M) r*a,?_⟩
        have ha' : s*AddMonoidAlgebra.mapDomain f
            (AddMonoidAlgebra.single x 1)^n=AddMonoidAlgebra.mapDomain f a := by
          simpa only [halg] using ha
        simp only [Algebra.smul_def,halg]
        rw [mul_assoc,ha',AddMonoidAlgebra.mapDomain_mul]
        congr 1
        exact ((AddMonoidAlgebra.mapDomainAlgHom R R f).commutes r).symm
  · intro a b hab
    exact ⟨0,by rw [AddMonoidAlgebra.mapDomain_injective hf hab]⟩

end Localization

variable {k J : Type*} [Field k] [Fintype J] [DecidableEq J]

abbrev Exponent (J : Type*) := J →₀ ℤ
abbrev LaurentRing (k J : Type*) [Field k] := AddMonoidAlgebra k (Exponent J)
abbrev PolynomialRing (k J : Type*) [Field k] := MvPolynomial J k
abbrev FunctionField (k J : Type*) [Field k] := FractionRing (PolynomialRing k J)

def castExponent : (J →₀ ℕ) →+ Exponent J :=
  Finsupp.mapRange.addMonoidHom Int.ofNatHom.toAddMonoidHom

omit [Fintype J] [DecidableEq J] in
@[simp] theorem castExponent_apply (d : J →₀ ℕ) (j : J) :
    castExponent d j = (d j : ℤ) := rfl

omit [Fintype J] [DecidableEq J] in
theorem castExponent_injective : Function.Injective (castExponent (J := J)) := by
  intro d e h
  ext j
  exact Int.ofNat_inj.mp (congrArg (fun z : Exponent J => z j) h)

def allOnes : J →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem allOnes_apply (j : J) : allOnes (J := J) j=1 := rfl

theorem clear_negative_exponents (d : Exponent J) :
    ∃ n : ℕ,d+n • castExponent (allOnes (J := J)) ∈ Set.range castExponent := by
  let n : ℕ := ∑ j : J,(-d j).toNat
  have hn (j : J) : 0≤d j+(n : ℤ) := by
    have hle : (-d j).toNat≤n :=
      Finset.single_le_sum (f := fun j => (-d j).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hle' : ((-d j).toNat : ℤ)≤n := by exact_mod_cast hle
    have ht := Int.self_le_toNat (-d j)
    omega
  let e : J →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (d j+n).toNat)
  refine ⟨n,e,?_⟩
  ext j
  simp only [castExponent_apply,Finsupp.add_apply,Finsupp.smul_apply,allOnes_apply,
    nsmul_eq_mul,mul_one]
  change ((d j+(n : ℤ)).toNat : ℤ)=d j+(n : ℤ)*1
  simpa using Int.toNat_of_nonneg (hn j)

def polynomialMap : PolynomialRing k J →ₐ[k] LaurentRing k J :=
  AddMonoidAlgebra.mapDomainAlgHom k k castExponent

instance polynomialAlgebra : Algebra (PolynomialRing k J) (LaurentRing k J) :=
  (polynomialMap (k := k) (J := J)).toRingHom.toAlgebra

instance polynomialTower : IsScalarTower k (PolynomialRing k J) (LaurentRing k J) :=
  IsScalarTower.of_algHom (polynomialMap (k := k) (J := J))

@[simp] theorem polynomialMap_monomial (d : J →₀ ℕ) (c : k) :
    polynomialMap (MvPolynomial.monomial d c) =
      AddMonoidAlgebra.single (castExponent d) c := by
  exact AddMonoidAlgebra.mapDomain_single

theorem polynomialMap_injective :
    Function.Injective (polynomialMap (k := k) (J := J)) :=
  AddMonoidAlgebra.mapDomain_injective castExponent_injective

def variableProduct : PolynomialRing k J := MvPolynomial.monomial allOnes 1

theorem variableProduct_ne_zero : variableProduct (k := k) (J := J)≠0 := by
  simp [variableProduct]

instance laurentLocalization :
    IsLocalization.Away (variableProduct (k := k) (J := J)) (LaurentRing k J) := by
  apply additive_monomial_localization k castExponent castExponent_injective allOnes
  · refine ⟨⟨AddMonoidAlgebra.single (castExponent allOnes) 1,
        AddMonoidAlgebra.single (-castExponent allOnes) 1,?_,?_⟩,rfl⟩ <;>
      simp <;> rfl
  · exact clear_negative_exponents

def evaluate : LaurentRing k J →ₐ[k] FunctionField k J :=
  IsLocalization.Away.liftAlgHom (variableProduct (k := k) (J := J))
    (f := IsScalarTower.toAlgHom k (PolynomialRing k J) (FunctionField k J))
    (isUnit_iff_ne_zero.mpr (fun h => variableProduct_ne_zero
      (IsFractionRing.injective (PolynomialRing k J) (FunctionField k J)
        (by simpa using h))))

@[simp] theorem evaluate_polynomialMap (p : PolynomialRing k J) :
    evaluate (polynomialMap p) = algebraMap (PolynomialRing k J) (FunctionField k J) p := by
  change evaluate (algebraMap (PolynomialRing k J) (LaurentRing k J) p)=_
  simp [evaluate]

/-- The Laurent algebra is embedded faithfully in the literal rational
function field. No algebraic independence is assumed here. -/
theorem evaluate_injective : Function.Injective (evaluate (k := k) (J := J)) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (variableProduct (k := k) (J := J)))
    (evaluate (k := k) (J := J)).toRingHom).mpr
  intro p q
  constructor
  · intro h
    exact congrArg evaluate h
  · intro h
    have hpq : p=q := by
      apply IsFractionRing.injective (PolynomialRing k J) (FunctionField k J)
      change evaluate (polynomialMap p)=evaluate (polynomialMap q) at h
      simpa only [evaluate_polynomialMap] using h
    exact congrArg (algebraMap (PolynomialRing k J) (LaurentRing k J)) hpq

def monomial (d : Exponent J) : FunctionField k J :=
  evaluate (AddMonoidAlgebra.single d 1)

@[simp] theorem monomial_zero : monomial (k := k) (0 : Exponent J)=1 := by
  change evaluate 1=1
  exact map_one evaluate

theorem monomial_add (d e : Exponent J) :
    monomial (k := k) (d+e)=monomial d*monomial e := by
  simp [monomial,← map_mul]

theorem monomial_ne_zero (d : Exponent J) : monomial (k := k) d≠0 := by
  intro h
  have hh := monomial_add (k := k) d (-d)
  simpa [h] using hh

theorem monomial_neg (d : Exponent J) : monomial (k := k) (-d)=(monomial d)⁻¹ := by
  apply (mul_right_cancel₀ (monomial_ne_zero (k := k) d))
  rw [← monomial_add,neg_add_cancel,monomial_zero,
    inv_mul_cancel₀ (monomial_ne_zero d)]

theorem monomial_zsmul (n : ℤ) (d : Exponent J) :
    monomial (k := k) (n • d)=monomial d^n := by
  let f : Multiplicative (Exponent J) →* FunctionField k J :=
    { toFun := fun e => monomial e.toAdd,
      map_one' := monomial_zero,
      map_mul' := fun e e' => monomial_add e.toAdd e'.toAdd }
  exact map_zpow f (Multiplicative.ofAdd d) n

@[simp] theorem monomial_single (j : J) :
    monomial (k := k) (Finsupp.single j 1)=
      algebraMap (PolynomialRing k J) (FunctionField k J) (MvPolynomial.X j) := by
  have he : castExponent (Finsupp.single j 1)=Finsupp.single j 1 := by
    ext i
    by_cases hi : i=j <;> simp [hi]
  rw [monomial,← he,← polynomialMap_monomial,evaluate_polynomialMap]
  rfl

end Sunlet.LaurentMonomials
end
end Stage_LaurentMonomials

#check "SUNLET_LaurentMonomials_READY"

section Stage_MonomialRationality



/-!
# Rationality of the actual integral monomial field

The exponent module is the integral span of the displayed monomials, with no
saturation. A basis of that module gives algebraically independent Laurent
monomials generating exactly the same intermediate field.
-/

noncomputable section
open scoped BigOperators
open Module

namespace Sunlet.LaurentMonomials

variable {k J I O : Type*} [Field k] [Fintype J] [DecidableEq J]

def exponentMap (b : I → Exponent J) : (I →₀ ℕ) →+ Exponent J :=
  (Finsupp.linearCombination ℤ b).toAddMonoidHom.comp castExponent

@[simp] theorem castExponent_single (i : I) (n : ℕ) :
    castExponent (Finsupp.single i n)=Finsupp.single i (n : ℤ) := by
  classical
  ext j
  by_cases h : j=i <;> simp [h]

@[simp] theorem exponentMap_single (b : I → Exponent J) (i : I) :
    exponentMap b (Finsupp.single i 1)=b i := by
  simp [exponentMap]

theorem exponentMap_injective (b : I → Exponent J) (hb : LinearIndependent ℤ b) :
    Function.Injective (exponentMap b) :=
  (linearIndependent_iff_injective_finsuppLinearCombination.mp hb).comp castExponent_injective

theorem monomial_algebraicIndependent (b : I → Exponent J)
    (hb : LinearIndependent ℤ b) : AlgebraicIndependent k (fun i => monomial (k := k) (b i)) := by
  let f : MvPolynomial I k →ₐ[k] LaurentRing k J :=
    AddMonoidAlgebra.mapDomainAlgHom k k (exponentMap b)
  have hf : Function.Injective f :=
    AddMonoidAlgebra.mapDomain_injective (exponentMap_injective b hb)
  have he : evaluate.comp f=MvPolynomial.aeval (fun i => monomial (k := k) (b i)) := by
    ext i
    simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]
    simp [f,MvPolynomial.X,← MvPolynomial.single_eq_monomial,monomial]
  rw [algebraicIndependent_iff_injective_aeval,← he]
  exact evaluate_injective.comp hf

abbrev monomialField (D : O → Exponent J) : IntermediateField k (FunctionField k J) :=
  IntermediateField.adjoin k (Set.range (fun a => monomial (k := k) (D a)))

/-- Integer linear combinations give products and inverse products in the
actual displayed-coordinate field. -/
theorem monomial_mem_span (D : O → Exponent J) {d : Exponent J}
    (hd : d ∈ Submodule.span ℤ (Set.range D)) : monomial (k := k) d ∈ monomialField D := by
  induction hd using Submodule.span_induction with
  | mem d hd =>
      obtain ⟨a,rfl⟩ := hd
      exact IntermediateField.subset_adjoin k _ ⟨a,rfl⟩
  | zero => simp [monomial_zero]
  | add d e _ _ hd he =>
      rw [monomial_add]
      exact (monomialField D).mul_mem hd he
  | smul n d _ hd =>
      rw [monomial_zsmul]
      exact zpow_mem hd n

theorem basis_span_eq (L : Submodule ℤ (Exponent J)) {n : ℕ} (b : Basis (Fin n) ℤ L) :
    Submodule.span ℤ (Set.range (fun i => (b i : Exponent J)))=L := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (b i).property
  · intro d hd
    have hh := congrArg (fun z : L => (z : Exponent J)) (b.sum_repr ⟨d,hd⟩)
    simp only [Submodule.coe_sum,Submodule.coe_smul] at hh
    rw [← hh]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem basis_monomialField_eq (D : O → Exponent J) {n : ℕ}
    (b : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range D))) :
    monomialField (k := k) D=
      monomialField (fun i => (b i : Exponent J)) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨a,rfl⟩
    apply monomial_mem_span
    rw [basis_span_eq]
    exact Submodule.subset_span ⟨a,rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact monomial_mem_span D (b i).property

/-- Every finite-dimensional toric monomial field is purely transcendental,
with an explicit algebraic-independence and exact field-generation witness. -/
theorem exists_rational_parameters (D : O → Exponent J) :
    ∃ n : ℕ,∃ b : Fin n → FunctionField k J,
      AlgebraicIndependent k b ∧
      monomialField (k := k) D=IntermediateField.adjoin k (Set.range b) := by
  let L := Submodule.span ℤ (Set.range D)
  let B := Submodule.basisOfPid (Finsupp.basisSingleOne : Basis J ℤ (Exponent J)) L
  let b : Fin B.1 → Exponent J := fun i => (B.2 i : Exponent J)
  have hb : LinearIndependent ℤ b :=
    B.2.linearIndependent.map' L.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨B.1,fun i => monomial (b i),monomial_algebraicIndependent b hb,?_⟩
  exact basis_monomialField_eq D B.2

/-- A literal rational-function-field isomorphism, not only an equality
of transcendence degrees. -/
theorem exists_rational_field_equiv (D : O → Exponent J) :
    ∃ n : ℕ,Nonempty (FractionRing (MvPolynomial (Fin n) k) ≃ₐ[k]
      monomialField (k := k) D) := by
  obtain ⟨n,b,hb,he⟩ := exists_rational_parameters (k := k) D
  exact ⟨n,⟨hb.aevalEquivField.trans (IntermediateField.equivOfEq he.symm)⟩⟩

end Sunlet.LaurentMonomials
end
end Stage_MonomialRationality

#check "SUNLET_MonomialRationality_READY"

section Stage_RationalityDevelopment



/-! Exact rationality source-body aggregation. The companion source map
records its fragments; a build is required before any proof claim. -/

noncomputable section

section RationalitySource_SymmetricSquareRationality

open scoped BigOperators IntermediateField.algebraAdjoinAdjoin

namespace Sunlet.SymmetricSquare

variable {k E I : Type*} [Field k] [Field E] [Algebra k E]
  [DecidableEq I]

def invariant (v : Bool × I → E) (o : I) (j : Bool × I) : E :=
  if j.2=o then
    if j.1 then v (false,o)*v (true,o) else v (false,o)+v (true,o)
  else if j.1 then
    (v (false,o)*v (true,j.2)-v (true,o)*v (false,j.2)) /
      (v (false,o)-v (true,o))
  else (v (false,j.2)-v (true,j.2))/(v (false,o)-v (true,o))

abbrev invariantField (v : Bool × I → E) (o : I) : IntermediateField k E :=
  IntermediateField.adjoin k (Set.range (invariant v o))

def fixedField (σ : E ≃ₐ[k] E) : IntermediateField k E where
  carrier := {x | σ x=x}
  zero_mem' := map_zero σ
  one_mem' := map_one σ
  add_mem' hx hy := by simp only [Set.mem_setOf_eq] at *; simp [hx,hy]
  mul_mem' hx hy := by simp only [Set.mem_setOf_eq] at *; simp [hx,hy]
  inv_mem' x hx := by simp only [Set.mem_setOf_eq] at *; simp [hx]
  algebraMap_mem' := σ.commutes

@[simp] theorem mem_fixedField (σ : E ≃ₐ[k] E) (x : E) :
    x∈fixedField σ ↔ σ x=x := Iff.rfl

/-- Restrict an ambient automorphism to a subfield and identify its fixed
field with a given intermediate field by equality of actual elements. -/
def fixedFieldEquiv (F K : IntermediateField k E) (hFK : F ≤ K)
    (σ : E ≃ₐ[k] E) (τ : K ≃ₐ[k] K)
    (hτ : ∀ z : K,(τ z : E)=σ (z : E))
    (hfixed : ∀ z : E,z∈K → (σ z=z ↔ z∈F)) :
    fixedField τ ≃ₐ[k] F where
  toFun z := ⟨(z.val : E),(hfixed _ z.val.property).mp (by
    rw [← hτ]
    exact congrArg (fun t : K => (t : E)) z.property)⟩
  invFun z := ⟨⟨z.val,hFK z.property⟩,by
    apply Subtype.ext
    rw [hτ]
    exact (hfixed _ (hFK z.property)).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem invariant_mem (v : Bool × I → E) (o : I) (j : Bool × I) :
    invariant v o j∈invariantField (k := k) v o :=
  IntermediateField.subset_adjoin k _ ⟨j,rfl⟩

theorem base_difference_ne_zero (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v) : v (false,o)-v (true,o)≠0 := by
  apply sub_ne_zero.mpr
  intro h
  have hh := hv.injective h
  exact Bool.false_ne_true (congrArg Prod.fst hh)

theorem reconstruct_left (v : Bool × I → E) (o i : I) (hi : i≠o)
    (hd : v (false,o)-v (true,o)≠0) :
    v (false,i)=invariant v o (false,i)*v (false,o)+invariant v o (true,i) := by
  simp only [invariant,hi,ite_false,ite_true,Bool.false_eq_true]
  field_simp [hd]
  <;> ring

theorem reconstruct_right (v : Bool × I → E) (o i : I) (hi : i≠o)
    (hd : v (false,o)-v (true,o)≠0) :
    v (true,i)=invariant v o (false,i)*v (true,o)+invariant v o (true,i) := by
  simp only [invariant,hi,ite_false,ite_true,Bool.false_eq_true]
  field_simp [hd]
  <;> ring

def baseSum (v : Bool × I → E) (o : I) : invariantField (k := k) v o :=
  ⟨invariant v o (false,o),invariant_mem v o (false,o)⟩

def baseProduct (v : Bool × I → E) (o : I) : invariantField (k := k) v o :=
  ⟨invariant v o (true,o),invariant_mem v o (true,o)⟩

@[simp] theorem baseSum_val (v : Bool × I → E) (o : I) :
    (baseSum (k := k) v o : E)=v (false,o)+v (true,o) := by
  simp [baseSum,invariant]

@[simp] theorem baseProduct_val (v : Bool × I → E) (o : I) :
    (baseProduct (k := k) v o : E)=v (false,o)*v (true,o) := by
  simp [baseProduct,invariant]

/-- The quadratic degree calculation uses only the elementary polynomial API. -/
theorem elementary_quadratic_natDegree {F : Type*} [Field F] (a b : F) :
    (Polynomial.X^2-Polynomial.C a*Polynomial.X+Polynomial.C b : Polynomial F).natDegree=2 := by
  rw [Polynomial.natDegree_add_C]
  have hlt : (Polynomial.C a * Polynomial.X : Polynomial F).natDegree <
      (Polynomial.X^2 : Polynomial F).natDegree :=
    (Polynomial.natDegree_C_mul_le a Polynomial.X).trans_lt (by simp)
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt,Polynomial.natDegree_X_pow]

theorem elementary_quadratic_monic {F : Type*} [Field F] (a b : F) :
    (Polynomial.X^2-Polynomial.C a*Polynomial.X+Polynomial.C b : Polynomial F).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2
  · exact (elementary_quadratic_natDegree a b).le
  · simp

def quadratic (v : Bool × I → E) (o : I) : Polynomial (invariantField (k := k) v o) :=
  Polynomial.X^2-Polynomial.C (baseSum v o)*Polynomial.X+Polynomial.C (baseProduct v o)

theorem quadratic_monic (v : Bool × I → E) (o : I) :
    (quadratic (k := k) v o).Monic :=
  elementary_quadratic_monic _ _

theorem quadratic_natDegree (v : Bool × I → E) (o : I) :
    (quadratic (k := k) v o).natDegree=2 :=
  elementary_quadratic_natDegree _ _

theorem quadratic_aeval (v : Bool × I → E) (o : I) :
    Polynomial.aeval (v (false,o)) (quadratic (k := k) v o)=0 := by
  simp [quadratic,baseSum,baseProduct,invariant]
  ring

theorem base_integral (v : Bool × I → E) (o : I) :
    IsIntegral (invariantField (k := k) v o) (v (false,o)) :=
  ⟨quadratic v o,quadratic_monic v o,quadratic_aeval v o⟩

theorem adjoin_base_eq_top (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤) :
    IntermediateField.adjoin (invariantField (k := k) v o) {v (false,o)}=⊤ := by
  let M := IntermediateField.adjoin (invariantField (k := k) v o) {v (false,o)}
  have hb (z : E) (hz : z∈invariantField (k := k) v o) : z∈M :=
    M.algebraMap_mem ⟨z,hz⟩
  have hx : v (false,o)∈M := IntermediateField.mem_adjoin_simple_self _ _
  have hy : v (true,o)∈M := by
    have hh := M.sub_mem (hb _ (invariant_mem v o (false,o))) hx
    simpa [invariant] using hh
  have hall (c : Bool) (i : I) : v (c,i)∈M := by
    by_cases hi : i=o
    · subst i
      cases c
      · exact hx
      · exact hy
    · cases c
      · rw [reconstruct_left v o i hi (base_difference_ne_zero v o hv)]
        exact M.add_mem (M.mul_mem (hb _ (invariant_mem v o (false,i))) hx)
          (hb _ (invariant_mem v o (true,i)))
      · rw [reconstruct_right v o i hi (base_difference_ne_zero v o hv)]
        exact M.add_mem (M.mul_mem (hb _ (invariant_mem v o (false,i))) hy)
          (hb _ (invariant_mem v o (true,i)))
  have hle : IntermediateField.adjoin k (Set.range v)≤M.restrictScalars k := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨c,i⟩,rfl⟩
    exact hall c i
  apply IntermediateField.restrictScalars_injective k
  apply top_unique
  simpa only [hgen,IntermediateField.restrictScalars_top] using hle

def powerBasis (v : Bool × I → E) (o : I) (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤) :
    PowerBasis (invariantField (k := k) v o) E :=
  PowerBasis.ofAdjoinSimpleEqTop (base_integral v o) (adjoin_base_eq_top v o hv hgen)

theorem powerBasis_dim_le_two (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤) :
    (powerBasis v o hv hgen).dim≤2 := by
  rw [powerBasis,PowerBasis.ofAdjoinSimpleEqTop_dim]
  exact (Polynomial.natDegree_le_natDegree
    (minpoly.min _ _ (quadratic_monic v o) (quadratic_aeval v o))).trans_eq
      (quadratic_natDegree v o)

theorem linear_representation (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤) (z : E) :
    ∃ a b : invariantField (k := k) v o,z=(a : E)+(b : E)*v (false,o) := by
  let B := powerBasis v o hv hgen
  have hdim : B.dim≤2 := powerBasis_dim_le_two v o hv hgen
  have hspan : Submodule.span (invariantField (k := k) v o)
      ({1,v (false,o)} : Set E)=⊤ := by
    apply top_unique
    rw [← B.basis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [B.basis_eq_pow]
    have hgenB : B.gen=v (false,o) := by simp [B,powerBasis]
    rw [hgenB]
    have hi : i.val=0 ∨ i.val=1 := by omega
    rcases hi with hi|hi
    · simp only [hi,pow_zero]
      exact Submodule.subset_span (by simp)
    · simp only [hi,pow_one]
      exact Submodule.subset_span (by simp)
  have hz : z∈Submodule.span (invariantField (k := k) v o) ({1,v (false,o)} : Set E) := by
    rw [hspan]; trivial
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hz
  exact ⟨a,b,by simpa only [Algebra.smul_def,IntermediateField.algebraMap_apply,mul_one] using hab.symm⟩

theorem invariant_fixed (v : Bool × I → E) (o : I) (σ : E ≃ₐ[k] E)
    (hσ : ∀ c i,σ (v (c,i))=v (!c,i)) (j : Bool × I) :
    σ (invariant v o j)=invariant v o j := by
  rcases j with ⟨c,i⟩
  by_cases hi : i=o
  · subst i
    cases c <;> simp [invariant,hσ,add_comm,mul_comm]
  · cases c <;> simp only [invariant,hi,ite_false,Bool.false_eq_true,
      Bool.true_eq_false,ite_true,map_div₀,map_sub,map_mul,hσ,Bool.not_false,Bool.not_true]
    · rw [show v (true,i)-v (false,i)=-(v (false,i)-v (true,i)) by ring,
        show v (true,o)-v (false,o)=-(v (false,o)-v (true,o)) by ring,
        neg_div_neg_eq]
    · rw [show v (true,o)*v (false,i)-v (false,o)*v (true,i)=
          -(v (false,o)*v (true,i)-v (true,o)*v (false,i)) by ring,
        show v (true,o)-v (false,o)=-(v (false,o)-v (true,o)) by ring,
        neg_div_neg_eq]

theorem invariantField_le_fixedField (v : Bool × I → E) (o : I)
    (σ : E ≃ₐ[k] E) (hσ : ∀ c i,σ (v (c,i))=v (!c,i)) :
    invariantField (k := k) v o≤fixedField σ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨j,rfl⟩
  exact invariant_fixed v o σ hσ j

/-- Every fixed rational function is a rational function of the displayed
sum, product, slopes and intercepts. -/
theorem invariantField_eq_fixedField (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤)
    (σ : E ≃ₐ[k] E) (hσ : ∀ c i,σ (v (c,i))=v (!c,i)) :
    invariantField (k := k) v o=fixedField σ := by
  apply le_antisymm (invariantField_le_fixedField v o σ hσ)
  intro z hz
  obtain ⟨a,b,hzab⟩ := linear_representation v o hv hgen z
  have ha : σ (a : E)=(a : E) :=
    invariantField_le_fixedField v o σ hσ a.property
  have hb : σ (b : E)=(b : E) :=
    invariantField_le_fixedField v o σ hσ b.property
  have hh : (b : E)*(v (false,o)-v (true,o))=0 := by
    have hh : σ z=z := hz
    rw [hzab,map_add,map_mul,ha,hb,hσ] at hh
    simp only [Bool.not_false] at hh
    linear_combination -hh
  have hb0 : (b : E)=0 := (mul_eq_zero.mp hh).resolve_right (base_difference_ne_zero v o hv)
  rw [hzab,hb0,zero_mul,add_zero]
  exact a.property

theorem invariants_algebraicIndependent [Finite I] (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤) :
    AlgebraicIndependent k (invariant v o) := by
  let F := invariantField (k := k) v o
  let A := Algebra.adjoin k (Set.range (invariant v o))
  letI : Module.Finite F E := (powerBasis v o hv hgen).finite
  letI : Algebra.IsAlgebraic A E := Algebra.IsAlgebraic.trans A F E
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
    k (invariant v o) hv.lift_cardinalMk_le_trdeg).1

/-- A literal rational function field isomorphism for the entire fixed
subfield. All coordinates and the involution retain their ordinary meaning. -/
theorem rational_fixedField [Finite I] (v : Bool × I → E) (o : I)
    (hv : AlgebraicIndependent k v)
    (hgen : IntermediateField.adjoin k (Set.range v)=⊤)
    (σ : E ≃ₐ[k] E) (hσ : ∀ c i,σ (v (c,i))=v (!c,i)) :
    Nonempty (FractionRing (MvPolynomial (Bool × I) k) ≃ₐ[k] fixedField σ) :=
  ⟨(invariants_algebraicIndependent v o hv hgen).aevalEquivField.trans
    (IntermediateField.equivOfEq (invariantField_eq_fixedField v o hv hgen σ hσ))⟩

end Sunlet.SymmetricSquare

end RationalitySource_SymmetricSquareRationality

section RationalitySource_PairedMonomialRationality

open scoped BigOperators
open Module

namespace Sunlet.LaurentMonomials

variable {k J O : Type*} [Field k] [Fintype J] [DecidableEq J]

def copyExponent (c : Bool) : Exponent J →ₗ[ℤ] Exponent (Bool × J) where
  toFun d := Finsupp.equivFunOnFinite.symm (fun p => if p.1=c then d p.2 else 0)
  map_add' d e := by ext ⟨b,j⟩; by_cases h : b=c <;> simp [h]
  map_smul' n d := by ext ⟨b,j⟩; by_cases h : b=c <;> simp [h]

@[simp] theorem copyExponent_apply (c b : Bool) (d : Exponent J) (j : J) :
    copyExponent c d (b,j)=if b=c then d j else 0 := rfl

@[simp] theorem copyExponent_single (c : Bool) (j : J) (n : ℤ) :
    copyExponent c (Finsupp.single j n)=Finsupp.single (c,j) n := by
  ext ⟨b,i⟩
  by_cases hbc : b=c <;> by_cases hij : i=j <;> simp [hbc,hij]

def pairedExponents (D : O → Exponent J) : Bool × O → Exponent (Bool × J) :=
  fun p => copyExponent p.1 (D p.2)

theorem copy_mem_span (D : O → Exponent J) (c : Bool) {d : Exponent J}
    (hd : d∈Submodule.span ℤ (Set.range D)) :
    copyExponent c d∈Submodule.span ℤ (Set.range (pairedExponents D)) := by
  induction hd using Submodule.span_induction with
  | mem d hd =>
      obtain ⟨a,rfl⟩ := hd
      exact Submodule.subset_span ⟨(c,a),rfl⟩
  | zero => simp
  | add d e _ _ hd he =>
      rw [map_add]
      exact Submodule.add_mem _ hd he
  | smul n d _ hd =>
      rw [map_smul]
      exact Submodule.smul_mem _ n hd

theorem paired_linearIndependent {n : ℕ} (b : Fin n → Exponent J)
    (hb : LinearIndependent ℤ b) : LinearIndependent ℤ (pairedExponents b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg ci
  rcases ci with ⟨c,i⟩
  apply Fintype.linearIndependent_iff.mp hb (fun i => g (c,i)) _ i
  ext j
  have hh := congrArg (fun d : Exponent (Bool × J) => d (c,j)) hg
  cases c <;>
    simpa [pairedExponents,Fintype.sum_prod_type,Finsupp.sum_apply,
      Finsupp.smul_apply,Finsupp.finsetSum_apply,Fintype.sum_bool,copyExponent_apply] using hh

theorem paired_basis_monomialField_eq (D : O → Exponent J) {n : ℕ}
    (b : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range D))) :
    monomialField (k := k) (pairedExponents D)=
      monomialField (pairedExponents (fun i => (b i : Exponent J))) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨c,a⟩,rfl⟩
    apply monomial_mem_span
    apply copy_mem_span
    rw [basis_span_eq]
    exact Submodule.subset_span ⟨a,rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨c,i⟩,rfl⟩
    apply monomial_mem_span
    exact copy_mem_span D c (b i).property

theorem exists_paired_rational_parameters (D : O → Exponent J) :
    ∃ n : ℕ,∃ b : Fin n → Exponent J,
      LinearIndependent ℤ b ∧
      AlgebraicIndependent k (fun p => monomial (k := k) (pairedExponents b p)) ∧
      monomialField (k := k) (pairedExponents D)=
        IntermediateField.adjoin k (Set.range
          (fun p => monomial (k := k) (pairedExponents b p))) := by
  let L := Submodule.span ℤ (Set.range D)
  let B := Submodule.basisOfPid (Finsupp.basisSingleOne : Basis J ℤ (Exponent J)) L
  let b : Fin B.1 → Exponent J := fun i => (B.2 i : Exponent J)
  have hb : LinearIndependent ℤ b :=
    B.2.linearIndependent.map' L.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact ⟨B.1,b,hb,monomial_algebraicIndependent _ (paired_linearIndependent b hb),
    paired_basis_monomialField_eq D B.2⟩

/-- A nonzero displayed exponent ensures that the rational coordinate
system has a distinguished coordinate, as required for the explicit
symmetric-square construction. -/
theorem exists_nonempty_paired_rational_parameters (D : O → Exponent J)
    (hD : ∃ a,D a≠0) :
    ∃ n : ℕ,0<n ∧ ∃ b : Fin n → Exponent J,
      LinearIndependent ℤ b ∧
      AlgebraicIndependent k (fun p => monomial (k := k) (pairedExponents b p)) ∧
      monomialField (k := k) (pairedExponents D)=
        IntermediateField.adjoin k (Set.range
          (fun p => monomial (k := k) (pairedExponents b p))) := by
  let L := Submodule.span ℤ (Set.range D)
  let B := Submodule.basisOfPid (Finsupp.basisSingleOne : Basis J ℤ (Exponent J)) L
  let b : Fin B.1 → Exponent J := fun i => (B.2 i : Exponent J)
  have hb : LinearIndependent ℤ b :=
    B.2.linearIndependent.map' L.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hn : 0<B.1 := by
    by_contra hn
    have hn0 : B.1=0 := by omega
    obtain ⟨a,ha⟩ := hD
    have he := basis_span_eq L B.2
    have hempty : Set.range (fun i => (B.2 i : Exponent J))=∅ := by
      ext d
      simp only [Set.mem_range,Set.mem_empty_iff_false,iff_false]
      rintro ⟨i,_⟩
      have := i.isLt
      omega
    rw [hempty,Submodule.span_empty] at he
    have hDa : D a∈L := Submodule.subset_span ⟨a,rfl⟩
    rw [← he] at hDa
    exact ha hDa
  exact ⟨B.1,hn,b,hb,monomial_algebraicIndependent _ (paired_linearIndependent b hb),
    paired_basis_monomialField_eq D B.2⟩

end Sunlet.LaurentMonomials

end RationalitySource_PairedMonomialRationality

section RationalitySource_MonomialSwapRationality

namespace Sunlet.LaurentMonomials

variable {k J O : Type*} [Field k] [Fintype J] [DecidableEq J]

theorem monomial_single_int (j : J) (n : ℤ) :
    monomial (k := k) (Finsupp.single j n)=
      (algebraMap (PolynomialRing k J) (FunctionField k J) (MvPolynomial.X j))^n := by
  rw [← Finsupp.smul_single_one,monomial_zsmul,monomial_single]

theorem copy_monomial_swap
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1)) (c : Bool) (d : Exponent J) :
    σ (monomial (copyExponent c d))=monomial (copyExponent (!c) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add,monomial_add,map_mul,hd,he]
  | single j n =>
      rw [copyExponent_single,copyExponent_single]
      rw [← Finsupp.smul_single_one (c,j) n,← Finsupp.smul_single_one (!c,j) n,
        monomial_zsmul,monomial_zsmul,map_zpow₀,hσ]

theorem pairedField_map_swap (D : O → Exponent J)
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1)) :
    (monomialField (k := k) (pairedExponents D)).map σ.toAlgHom=
      monomialField (pairedExponents D) := by
  rw [monomialField,IntermediateField.adjoin_map,← Set.range_comp]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨c,a⟩,rfl⟩
    exact ⟨(!c,a),(copy_monomial_swap σ hσ c (D a)).symm⟩
  · rintro ⟨⟨c,a⟩,rfl⟩
    refine ⟨(!c,a),?_⟩
    simpa only [Function.comp_apply,AlgEquiv.coe_toAlgHom,pairedExponents,Bool.not_not]
      using copy_monomial_swap σ hσ (!c) (D a)

def pairedFieldSwap (D : O → Exponent J)
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1)) :
    monomialField (k := k) (pairedExponents D) ≃ₐ[k]
      monomialField (k := k) (pairedExponents D) :=
  (IntermediateField.equivMap (monomialField (k := k) (pairedExponents D)) σ.toAlgHom).trans
    (IntermediateField.equivOfEq (pairedField_map_swap (k := k) D σ hσ))

@[simp] theorem pairedFieldSwap_val (D : O → Exponent J)
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1))
    (z : monomialField (k := k) (pairedExponents D)) :
    (pairedFieldSwap D σ hσ z : FunctionField k (Bool × J))=σ z := rfl

def pairedRationalParameter (D : O → Exponent J) {n : ℕ} (b : Fin n → Exponent J)
    (hfield : monomialField (k := k) (pairedExponents D)=
      monomialField (pairedExponents b)) (p : Bool × Fin n) :
    monomialField (k := k) (pairedExponents D) :=
  ⟨monomial (pairedExponents b p),by
    rw [hfield]
    exact IntermediateField.subset_adjoin k _ ⟨p,rfl⟩⟩

theorem pairedRationalParameter_independent (D : O → Exponent J) {n : ℕ}
    (b : Fin n → Exponent J) (hb : LinearIndependent ℤ b)
    (hfield : monomialField (k := k) (pairedExponents D)=
      monomialField (pairedExponents b)) :
    AlgebraicIndependent k (pairedRationalParameter D b hfield) := by
  apply AlgebraicIndependent.of_comp (monomialField (k := k) (pairedExponents D)).val
  exact monomial_algebraicIndependent _ (paired_linearIndependent b hb)

theorem pairedRationalParameter_generates (D : O → Exponent J) {n : ℕ}
    (b : Fin n → Exponent J)
    (hfield : monomialField (k := k) (pairedExponents D)=
      monomialField (pairedExponents b)) :
    IntermediateField.adjoin k (Set.range (pairedRationalParameter D b hfield))=⊤ := by
  apply IntermediateField.map_injective (monomialField (k := k) (pairedExponents D)).val
  rw [IntermediateField.adjoin_map,← Set.range_comp]
  change monomialField (k := k) (pairedExponents b)=_
  rw [← hfield]
  ext z
  simp

theorem pairedRationalParameter_swap (D : O → Exponent J) {n : ℕ}
    (b : Fin n → Exponent J)
    (hfield : monomialField (k := k) (pairedExponents D)=
      monomialField (pairedExponents b))
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1)) (c : Bool) (i : Fin n) :
    pairedFieldSwap D σ hσ (pairedRationalParameter D b hfield (c,i))=
      pairedRationalParameter D b hfield (!c,i) := by
  apply Subtype.ext
  exact copy_monomial_swap σ hσ c (b i)

/-- Pure transcendence of the literal fixed field, compatible with the
interchange action inherited from the original independent parameters. -/
theorem paired_fixedField_rational (D : O → Exponent J) (hD : ∃ a,D a≠0)
    (σ : FunctionField k (Bool × J) ≃ₐ[k] FunctionField k (Bool × J))
    (hσ : ∀ c j,σ (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1)) :
    ∃ n : ℕ,0<n ∧ Nonempty (FractionRing (MvPolynomial (Bool × Fin n) k) ≃ₐ[k]
      SymmetricSquare.fixedField (pairedFieldSwap D σ hσ)) := by
  obtain ⟨n,hn,b,hb,_,hfield⟩ := exists_nonempty_paired_rational_parameters (k := k) D hD
  exact ⟨n,hn,SymmetricSquare.rational_fixedField
    (pairedRationalParameter D b hfield) ⟨0,hn⟩
    (pairedRationalParameter_independent D b hb hfield)
    (pairedRationalParameter_generates D b hfield) (pairedFieldSwap D σ hσ)
    (pairedRationalParameter_swap D b hfield σ hσ)⟩

end Sunlet.LaurentMonomials

end RationalitySource_MonomialSwapRationality

section RationalitySource_ToricMonomialRationality

namespace Sunlet.ToricMonomialRationality

open LaurentMonomials

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

def torusExponent (o : Ω) (x : Ω) : Exponent (NormalizedVariations.Index ι Ω o) :=
  if hx : x=o then 0 else Finsupp.single (.inr ⟨x,hx⟩) 1

def pointExponent (o : Ω) (π : ι → Equiv.Perm Ω) (ax : ι × Ω) :
    Exponent (NormalizedVariations.Index ι Ω o) :=
  Finsupp.single (.inl ax.1) 1+torusExponent o ax.2-torusExponent o (π ax.1 ax.2)

@[simp] theorem torusExponent_coefficient (o x : Ω) (a : ι) :
    torusExponent (ι := ι) o x (.inl a)=0 := by
  by_cases hx : x=o <;> simp [torusExponent,hx]

@[simp] theorem pointExponent_coefficient (o : Ω) (π : ι → Equiv.Perm Ω)
    (a : ι) (x : Ω) : pointExponent o π (a,x) (.inl a)=1 := by
  simp [pointExponent]

theorem pointExponent_ne_zero (o : Ω) (π : ι → Equiv.Perm Ω)
    (a : ι) (x : Ω) : pointExponent o π (a,x)≠0 := by
  intro h
  have hh := congrArg (fun d => d (Sum.inl a)) h
  simpa using hh

theorem monomial_copy_coefficient (o : Ω) (b : Bool) (a : ι) :
    monomial (k := k) (copyExponent b
      (Finsupp.single (.inl a : NormalizedVariations.Index ι Ω o) 1))=
        ToricPairAlgebra.genericCoefficient o b a := by
  rw [copyExponent_single,monomial_single]
  rfl

theorem monomial_copy_torus (o : Ω) (b : Bool) (x : Ω) :
    monomial (k := k) (copyExponent b (torusExponent (ι := ι) o x))=
      (ToricPairAlgebra.genericTorus (k := k) (ι := ι) o b x).val := by
  by_cases hx : x=o
  · subst x
    simp [torusExponent]
  · simp only [torusExponent,dif_neg hx,copyExponent_single,monomial_single,
      ToricPairAlgebra.genericTorus,Units.val_mk0]
    rfl

/-- Equality with the literal toric point, not merely its exponent support. -/
theorem monomial_pointExponent (o : Ω) (π : ι → Equiv.Perm Ω)
    (b : Bool) (ax : ι × Ω) :
    monomial (k := k) (copyExponent b (pointExponent o π ax))=
      ToricPairAlgebra.genericPoint o π b ax := by
  simp only [pointExponent,map_sub,map_add,sub_eq_add_neg,map_neg,monomial_add,monomial_neg,
    monomial_copy_coefficient,monomial_copy_torus,ToricPairAlgebra.genericPoint,
    ToricDifferential.coordinate,ToricDifferential.ratio,div_eq_mul_inv,mul_assoc]

abbrev pointField (o : Ω) (π : ι → Equiv.Perm Ω) :
    IntermediateField k (ToricPairAlgebra.FunctionField (k := k) (ι := ι) o) :=
  IntermediateField.adjoin k (Set.range
    (fun p : Bool × (ι × Ω) => ToricPairAlgebra.genericPoint o π p.1 p.2))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem pointField_eq_monomialField (o : Ω) (π : ι → Equiv.Perm Ω) :
    pointField (k := k) o π=
      monomialField (k := k) (pairedExponents (pointExponent o π)) := by
  have h :
      (fun p : Bool × (ι × Ω) => ToricPairAlgebra.genericPoint (k := k) o π p.1 p.2) =
        (fun p => monomial (k := k) (pairedExponents (pointExponent o π) p)) := by
    funext p
    exact (monomial_pointExponent o π p.1 p.2).symm
  exact congrArg (fun f : Bool × (ι × Ω) →
    ToricPairAlgebra.FunctionField (k := k) (ι := ι) o =>
      IntermediateField.adjoin k (Set.range f)) h

theorem loop_swap_single (L : LoopData Ω) (c : Bool)
    (j : NormalizedVariations.Index ι Ω L.identity) :
    L.permutationAutomorphism (k := k) (ι := ι) (Equiv.swap false true)
        (monomial (Finsupp.single (c,j) 1))=
      monomial (Finsupp.single (!c,j) 1) := by
  rw [monomial_single,monomial_single]
  change L.permutationAutomorphism (k := k) (ι := ι) (Equiv.swap false true)
      (ToricPairAlgebra.genericVariable L.identity (c,j))=
    ToricPairAlgebra.genericVariable L.identity (!c,j)
  rw [LoopData.permutationAutomorphism_variable]
  cases c <;> simp

theorem rational_pair_fixedField [Nonempty ι] (L : LoopData Ω)
    (π : ι → Equiv.Perm Ω) :
    ∃ n : ℕ,0<n ∧ Nonempty (FractionRing (MvPolynomial (Bool × Fin n) k) ≃ₐ[k]
      SymmetricSquare.fixedField
        (pairedFieldSwap (pointExponent L.identity π)
          (L.permutationAutomorphism (k := k) (ι := ι) (Equiv.swap false true))
          (loop_swap_single L))) := by
  apply paired_fixedField_rational
  obtain ⟨a⟩ := ‹Nonempty ι›
  exact ⟨(a,L.identity),pointExponent_ne_zero L.identity π a L.identity⟩

end Sunlet.ToricMonomialRationality

end RationalitySource_ToricMonomialRationality

end
end Stage_RationalityDevelopment

#check "SUNLET_RationalityDevelopment_READY"

section Stage_LatinRationality



/-!
# Rationality over the original ground field

This combines the literal paired monomial field, its simultaneous-swap
invariant field, and the elementwise descent proved for the secant map.
No algebraic closure assumption or assumed descent theorem occurs here.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra LaurentMonomials ToricMonomialRationality

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- The off-diagonal secant coordinate field is a rational function field
over the given ground field, in particular over ℚ. -/
theorem offDiagonal_rational (hm : 5 ≤ Fintype.card Ω) :
    ∃ n : ℕ,0<n ∧ Nonempty (FractionRing (MvPolynomial (Bool × Fin n) k) ≃ₐ[k]
      JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm)) := by
  letI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hx⟩ := exists_ne o
  letI : Nonempty L.NonidentityColor := ⟨(L.loopColorEquiv o) ⟨x,hx⟩⟩
  let E := FunctionField (k := k) (ι := L.NonidentityColor) o
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm)
  let D := pointExponent o L.nonidentityPerm
  let K := monomialField (k := k) (pairedExponents D)
  let σ := (L.loopAt o).permutationAutomorphism (k := k)
    (ι := L.NonidentityColor) (Equiv.swap false true)
  let τ := pairedFieldSwap D σ (loop_swap_single (L.loopAt o))
  have hK : K=pairPointField (k := k) o L.nonidentityPerm :=
    (pointField_eq_monomialField o L.nonidentityPerm).symm
  have hFK : F≤K := by
    rw [hK]
    exact sumField_le_pairPointField o L.nonidentityPerm
  have hτ : ∀ z : K,(τ z : E)=σ (z : E) := fun _ => rfl
  have hfix : ∀ z : E,z∈K → (σ z=z ↔ z∈F) := by
    intro z hz
    apply L.pairField_fixed_iff o hm z
    rwa [hK] at hz
  let e := SymmetricSquare.fixedFieldEquiv F K hFK σ τ hτ hfix
  obtain ⟨n,hn,⟨er⟩⟩ := rational_pair_fixedField (k := k) (L.loopAt o) L.nonidentityPerm
  exact ⟨n,hn,⟨er.trans e⟩⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_LatinRationality

#check "SUNLET_LatinRationality_READY"

section Stage_TorusCharacterExtension



/-! Extension of integral torus characters over an algebraically closed
field. The integral subgroup is not replaced by its saturation. -/

noncomputable section

namespace Sunlet.TorusCharacterExtension

variable {k : Type*} [Field k] [IsAlgClosed k]

local instance unitsNatDivisible : DivisibleBy (Additive kˣ) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq u.toMul.val (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      exact u.toMul.ne_zero (by simpa [h,hn] using hz.symm)
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    simpa only [toMul_nsmul,toMul_ofMul,Units.val_pow_eq_pow_val,
      Units.val_mk0] using hz

local instance unitsIntDivisible : DivisibleBy (Additive kˣ) ℤ :=
  AddGroup.divisibleByIntOfDivisibleByNat _

/-- Every character on an actual subgroup of an integral lattice extends
to the ambient lattice. Roots are supplied by algebraic closedness. -/
theorem exists_extension {M : Type*} [AddCommGroup M]
    (H : AddSubgroup M) (χ : H →+ Additive kˣ) :
    ∃ ψ : M →+ Additive kˣ, ψ.comp H.subtype = χ :=
  (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    H.subtype Subtype.val_injective χ

/-- The same result for the exact integral span used in the monomial
parametrization, retaining its possible finite index. -/
theorem exists_span_extension {J O : Type*} (D : O → J →₀ ℤ)
    (χ : Submodule.span ℤ (Set.range D) →+ Additive kˣ) :
    ∃ ψ : (J →₀ ℤ) →+ Additive kˣ,
      ∀ d : Submodule.span ℤ (Set.range D), ψ d.val = χ d := by
  obtain ⟨ψ,hψ⟩ := exists_extension
    (Submodule.span ℤ (Set.range D)).toAddSubgroup χ
  exact ⟨ψ, fun d => DFunLike.congr_fun hψ d⟩

end Sunlet.TorusCharacterExtension
end
end Stage_TorusCharacterExtension

#check "SUNLET_TorusCharacterExtension_READY"

section Stage_ToricNonzeroLifting



/-!
# Nonzero points of an actual monomial closure lift to the torus

The argument retains the integral exponent lattice, including its finite
index in the ambient lattice. Polynomial binomial relations descend a
character to the image lattice, and divisibility of the units of an
algebraically closed field extends that character to all source exponents.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.ToricNonzeroLifting

open LaurentMonomials

variable {k J O : Type*} [Field k]
  [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

/-- Evaluation of an integral exponent as a unit, written additively so
that the exact lattice maps are ordinary additive homomorphisms. -/
def character (t : J → kˣ) : Exponent J →+ Additive kˣ :=
  (Finsupp.linearCombination ℤ (fun j => Additive.ofMul (t j))).toAddMonoidHom

@[simp] theorem character_single (t : J → kˣ) (j : J) (n : ℤ) :
    character t (Finsupp.single j n) = n • Additive.ofMul (t j) := by
  simp [character]

/-- The literal monomial parametrization, with every source variable a
unit. No quotient or identifiability relation is built into this map. -/
def point (D : O → Exponent J) (t : J → kˣ) : O → k :=
  fun a => ((character t (D a)).toMul).val

theorem character_comp (D : O → Exponent J) (t : J → kˣ) :
    character (fun a => (character t (D a)).toMul) =
      (character t).comp (Finsupp.linearCombination ℤ D).toAddMonoidHom := by
  apply Finsupp.addHom_ext
  intro a n
  simp [character]

@[simp] theorem castExponent_support (n : O →₀ ℕ) :
    (castExponent n).support = n.support := by
  ext a
  simp [Finsupp.mem_support_iff]

theorem aeval_monomial_character (t : O → kˣ) (n : O →₀ ℕ) :
    MvPolynomial.aeval (fun a => (t a).val) (MvPolynomial.monomial n (1 : k)) =
      ((character t (castExponent n)).toMul).val := by
  simp only [MvPolynomial.aeval_monomial, map_one, one_mul,
    character, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,
    Finsupp.sum, Finsupp.prod, toMul_sum, Units.coe_prod,
    castExponent_support, castExponent_apply, toMul_zsmul,
    toMul_ofMul, zpow_natCast, Units.val_pow_eq_pow_val]

theorem aeval_point_monomial (D : O → Exponent J) (t : J → kˣ)
    (n : O →₀ ℕ) :
    MvPolynomial.aeval (point D t) (MvPolynomial.monomial n (1 : k)) =
      ((character t (exponentMap D n)).toMul).val := by
  change MvPolynomial.aeval (fun a => ((character t (D a)).toMul).val)
    (MvPolynomial.monomial n (1 : k)) = _
  rw [aeval_monomial_character, character_comp]
  rfl

theorem aeval_generic_monomial (D : O → Exponent J) (n : O →₀ ℕ) :
    MvPolynomial.aeval (fun a => monomial (k := k) (D a))
      (MvPolynomial.monomial n (1 : k)) = monomial (exponentMap D n) := by
  let f : MvPolynomial O k →ₐ[k] LaurentRing k J :=
    AddMonoidAlgebra.mapDomainAlgHom k k (exponentMap D)
  have he : evaluate.comp f =
      MvPolynomial.aeval (fun a => monomial (k := k) (D a)) := by
    ext a
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    simp [f, MvPolynomial.X, ← MvPolynomial.single_eq_monomial, monomial]
  rw [← he, AlgHom.comp_apply]
  have hf : f (MvPolynomial.monomial n (1 : k)) =
      AddMonoidAlgebra.single (exponentMap D n) 1 :=
    AddMonoidAlgebra.mapDomain_single
  rw [hf]
  rfl

section Lifting

variable [IsAlgClosed k]

/-- Binomial relations are sufficient for a nonzero point to lie in the
actual torus image. The relations range over all integral lattice
dependencies, expressed as equalities between two nonnegative exponents. -/
theorem exists_lift_of_relations (D : O → Exponent J) (z : O → k)
    (hz0 : ∀ a, z a ≠ 0)
    (hrelations : ∀ n m : O →₀ ℕ, exponentMap D n = exponentMap D m →
      MvPolynomial.aeval z (MvPolynomial.monomial n (1 : k)) =
        MvPolynomial.aeval z (MvPolynomial.monomial m (1 : k))) :
    ∃ t : J → kˣ, point D t = z := by
  let u : O → kˣ := fun a => Units.mk0 (z a) (hz0 a)
  let C : Exponent O →+ Additive kˣ := character u
  let E : Exponent O →+ Exponent J := (Finsupp.linearCombination ℤ D).toAddMonoidHom
  have hker : ∀ d, E d = 0 → C d = 0 := by
    intro d hd
    obtain ⟨n, e, he⟩ := clear_negative_exponents d
    let f : O →₀ ℕ := n • allOnes
    have he' : castExponent e = d + castExponent f := by
      simpa only [f, map_nsmul] using he
    have hD : exponentMap D e = exponentMap D f := by
      change E (castExponent e) = E (castExponent f)
      rw [he', map_add, hd, zero_add]
    have hv := hrelations e f hD
    have hv' : ((C (castExponent e)).toMul).val =
        ((C (castExponent f)).toMul).val := by
      simpa only [C, ← aeval_monomial_character, u, Units.val_mk0] using hv
    have hc : C (castExponent e) = C (castExponent f) :=
      Additive.toMul.injective (Units.ext hv')
    rw [he', map_add] at hc
    exact add_eq_right.mp hc
  have hcongr {a b : Exponent O} (h : E a = E b) : C a = C b := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hker
    rw [map_sub, h, sub_self]
  let H : AddSubgroup (Exponent J) := E.range
  let χ : H →+ Additive kˣ :=
    { toFun := fun y => C y.property.choose
      map_zero' := by
        have hh : E ((0 : H).property.choose) = E 0 := by
          simpa only [map_zero, AddSubgroup.coe_zero] using (0 : H).property.choose_spec
        exact (hcongr hh).trans C.map_zero
      map_add' := by
        intro a b
        have hh : E ((a + b).property.choose) =
            E (a.property.choose + b.property.choose) := by
          rw [map_add, a.property.choose_spec, b.property.choose_spec,
            (a + b).property.choose_spec]
          rfl
        exact (hcongr hh).trans (C.map_add _ _) }
  have hχ (d : Exponent O) : χ ⟨E d, ⟨d, rfl⟩⟩ = C d := by
    exact hcongr (show E (⟨E d, ⟨d, rfl⟩⟩ : H).property.choose = E d from
      (⟨E d, ⟨d, rfl⟩⟩ : H).property.choose_spec)
  obtain ⟨ψ, hψ⟩ := TorusCharacterExtension.exists_extension H χ
  have hψE (d : Exponent O) : ψ (E d) = C d := by
    exact (DFunLike.congr_fun hψ (⟨E d, ⟨d, rfl⟩⟩ : H)).trans (hχ d)
  let t : J → kˣ := fun j => (ψ (Finsupp.single j 1)).toMul
  have ht : character t = ψ := by
    apply Finsupp.addHom_ext
    intro j n
    rw [character_single]
    change n • ψ (Finsupp.single j 1) = ψ (Finsupp.single j n)
    calc
      n • ψ (Finsupp.single j 1) = ψ (n • Finsupp.single j (1 : ℤ)) := by
        rw [map_zsmul]
      _ = ψ (Finsupp.single j n) := by rw [Finsupp.smul_single_one]
  refine ⟨t, funext fun a => ?_⟩
  have ha : ψ (D a) = Additive.ofMul (u a) := by
    simpa only [E, C, LinearMap.toAddMonoidHom_coe,
      Finsupp.linearCombination_single, one_smul, character_single] using
      hψE (Finsupp.single a 1)
  change ((character t (D a)).toMul).val = z a
  rw [ht, ha]
  rfl

/-- The common zero set of every polynomial vanishing on the literal
monomial torus image. -/
def closure (D : O → Exponent J) : Set (O → k) :=
  {z | ∀ P : MvPolynomial O k,
    (∀ t : J → kˣ, MvPolynomial.aeval (point D t) P = 0) →
      MvPolynomial.aeval z P = 0}

/-- Every all-nonzero point of the actual monomial closure is in its
torus image, with no assumption that the exponent lattice is saturated. -/
theorem exists_lift_of_closure (D : O → Exponent J) (z : O → k)
    (hz : z ∈ closure D) (hz0 : ∀ a, z a ≠ 0) :
    ∃ t : J → kˣ, point D t = z := by
  apply exists_lift_of_relations D z hz0
  intro n m hnm
  have hP := hz (MvPolynomial.monomial n 1 - MvPolynomial.monomial m 1)
    (fun t => by
      rw [map_sub, aeval_point_monomial, aeval_point_monomial, hnm, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hP)

/-- The form convenient for a toric variety already identified with
the zero locus of its generic monomial-coordinate equations. -/
theorem exists_lift_of_generic_equations (D : O → Exponent J) (z : O → k)
    (hz0 : ∀ a, z a ≠ 0)
    (hz : ∀ P : MvPolynomial O k,
      MvPolynomial.aeval (fun a => monomial (k := k) (D a)) P = 0 →
        MvPolynomial.aeval z P = 0) :
    ∃ t : J → kˣ, point D t = z := by
  apply exists_lift_of_relations D z hz0
  intro n m hnm
  have hP := hz (MvPolynomial.monomial n 1 - MvPolynomial.monomial m 1)
    (by rw [map_sub, aeval_generic_monomial, aeval_generic_monomial, hnm, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hP)

end Lifting

end Sunlet.ToricNonzeroLifting
end
end Stage_ToricNonzeroLifting

#check "SUNLET_ToricNonzeroLifting_READY"

section Stage_ToricOpenConditions



/-!
# A principal open with distinct, nonzero toric summands

The additional numerators are explicit polynomials in the sum coordinates.
Their identities hold on the full product of toric closures, so the open set
also excludes decompositions involving any toric boundary coordinate.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  {o : Ω} {π : ι → Equiv.Perm Ω} {p : ι × Ω}

/-- Each displayed sum coordinate is a nonzero rational function. Thus
one may also require any finite collection of output coordinates to be
nonzero without losing the generic open set. -/
theorem genericCoordinates_coordinate_ne_zero (o : Ω) (π : ι → Equiv.Perm Ω)
    (i : ι × Ω) : genericCoordinates (k := k) o π i ≠ 0 := by
  intro he
  have hh := congrArg (euler (k := k) (ι := ι) o) he
  have hf := congrFun (euler_genericPoint (k := k) o π false) i
  have ht := congrFun (euler_genericPoint (k := k) o π true) i
  change euler o (genericPoint (k := k) o π false i) = genericPoint (k := k) o π false i at hf
  change euler o (genericPoint (k := k) o π true i) = 0 at ht
  change euler o (genericPoint (k := k) o π false i + genericPoint (k := k) o π true i) =
    euler o 0 at hh
  rw [map_add, map_zero, hf, ht, add_zero] at hh
  exact genericPoint_coordinate_ne_zero o π false i hh

namespace PivotRecovery

variable (D : PivotRecovery (k := k) o π p)

/-- A cleared numerator of the product of the two coordinates in row `i`.
Only the already proved pivot reconstruction relations enter its definition. -/
def coordinateProductNumerator (i : ι × Ω) : MvPolynomial (ι × Ω) k :=
  MvPolynomial.X i ^ 2 * D.numerator p * D.denominator i ^ 2 -
    D.numerator i ^ 2 * D.denominator p

theorem coordinateProductNumerator_generic (i : ι × Ω) :
    MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.coordinateProductNumerator i) =
      4 * genericPoint (k := k) o π false i * genericPoint (k := k) o π true i *
        MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.numerator p) *
        MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.denominator i) ^ 2 := by
  simp only [coordinateProductNumerator, map_sub, map_mul, map_pow, MvPolynomial.aeval_X]
  rw [← D.relation p, ← D.relation i]
  rw [show genericCoordinates (k := k) o π i =
    genericPoint o π false i + genericPoint o π true i from rfl]
  unfold genericDifference
  ring

theorem coordinateProductNumerator_generic_ne (i : ι × Ω) :
    MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.coordinateProductNumerator i) ≠ 0 := by
  rw [D.coordinateProductNumerator_generic]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (genericPoint_coordinate_ne_zero o π false i))
        (genericPoint_coordinate_ne_zero o π true i))
      D.numerator_pivot_ne)
    (pow_ne_zero _ (D.denominator_ne i))

theorem coordinateProductNumerator_on_closure (x y : ι × Ω → k)
    (hx : x ∈ toricClosure (k := k) o π) (hy : y ∈ toricClosure (k := k) o π)
    (i : ι × Ω) :
    MvPolynomial.aeval (x + y) (D.coordinateProductNumerator i) =
      4 * x i * y i * MvPolynomial.aeval (x + y) (D.numerator p) *
        MvPolynomial.aeval (x + y) (D.denominator i) ^ 2 := by
  simp only [coordinateProductNumerator, map_sub, map_mul, map_pow, MvPolynomial.aeval_X,
    Pi.add_apply]
  rw [← D.relation_on_closure x y hx hy p, ← D.relation_on_closure x y hx hy i]
  ring

def torusOpenPolynomial : MvPolynomial (ι × Ω) k :=
  D.openPolynomial * ∏ i, D.coordinateProductNumerator i

theorem torusOpenPolynomial_generic_ne :
    MvPolynomial.aeval (genericCoordinates (k := k) o π) D.torusOpenPolynomial ≠ 0 := by
  simp only [torusOpenPolynomial, map_mul, map_prod]
  exact mul_ne_zero D.openPolynomial_generic_ne
    (Finset.prod_ne_zero_iff.mpr (fun i _ => D.coordinateProductNumerator_generic_ne i))

theorem torusOpen_factors (z : ι × Ω → k)
    (hz : MvPolynomial.aeval z D.torusOpenPolynomial ≠ 0) :
    MvPolynomial.aeval z D.openPolynomial ≠ 0 ∧
      ∀ i, MvPolynomial.aeval z (D.coordinateProductNumerator i) ≠ 0 := by
  simp only [torusOpenPolynomial, map_mul, map_prod, mul_ne_zero_iff] at hz
  exact ⟨hz.1, fun i => (Finset.prod_ne_zero_iff.mp hz.2) i (Finset.mem_univ i)⟩

theorem summands_nonzero_distinct (z x y : ι × Ω → k)
    (hz : MvPolynomial.aeval z D.torusOpenPolynomial ≠ 0)
    (hx : x ∈ toricClosure (k := k) o π) (hy : y ∈ toricClosure (k := k) o π)
    (hs : x + y = z) :
    (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ x ≠ y := by
  have hfactor := D.torusOpen_factors z hz
  have hn (i : ι × Ω) : x i ≠ 0 ∧ y i ≠ 0 := by
    have hrel := D.coordinateProductNumerator_on_closure x y hx hy i
    rw [hs] at hrel
    constructor
    · intro hi
      exact hfactor.2 i (by simpa only [hi, mul_zero, zero_mul] using hrel)
    · intro hi
      exact hfactor.2 i (by simpa only [hi, mul_zero, zero_mul] using hrel)
  refine ⟨fun i => (hn i).1, fun i => (hn i).2, ?_⟩
  intro he
  have hp := D.product_at z x y hfactor.1 hx hy hs p
  rw [he, sub_self, zero_mul] at hp
  exact (div_ne_zero (D.open_factors z hfactor.1).1
    ((D.open_factors z hfactor.1).2 p)) hp.symm

end PivotRecovery

/-- A nonzero polynomial at the generic sum is nonzero at a genuine
parameterized sum. This proves nonemptiness without an implicit generic
point or an assumed dominance theorem. -/
theorem exists_parameters_nonvanishing (o : Ω) (π : ι → Equiv.Perm Ω)
    (P : MvPolynomial (ι × Ω) k)
    (hP : MvPolynomial.aeval (genericCoordinates (k := k) o π) P ≠ 0) :
    ∃ (U : Bool → ι → k) (h : Bool → Ω → kˣ), (∀ b, h b o = 1) ∧
      MvPolynomial.aeval (toricPoint π (U false) (h false) +
        toricPoint π (U true) (h true)) P ≠ 0 := by
  by_contra hn
  push_neg at hn
  let f : LaurentRing (k := k) (ι := ι) o :=
    MvPolynomial.aeval (fun i => laurentPoint (k := k) o π false i +
      laurentPoint (k := k) o π true i) P
  have hf : f = 0 := by
    apply laurent_separated_by_points o
    intro U h hb
    dsimp only [f]
    rw [MvPolynomial.comp_aeval_apply]
    simp only [map_add, evaluate_laurentPoint o π U h hb]
    exact hn U h hb
  have hg := congrArg (generic (k := k) (ι := ι) o) hf
  dsimp only [f] at hg
  rw [map_zero, MvPolynomial.comp_aeval_apply] at hg
  simp only [map_add, generic_laurentPoint] at hg
  exact hP hg

theorem principalOpen_nonempty (o : Ω) (π : ι → Equiv.Perm Ω)
    (P : MvPolynomial (ι × Ω) k)
    (hP : MvPolynomial.aeval (genericCoordinates (k := k) o π) P ≠ 0) :
    (principalOpen (k := k) o π P).Nonempty := by
  obtain ⟨U, h, hb, hnonzero⟩ := exists_parameters_nonvanishing o π P hP
  let x := toricPoint π (U false) (h false)
  let y := toricPoint π (U true) (h true)
  have hx : x ∈ toricClosure (k := k) o π :=
    parameterImage_subset_toricClosure o π ⟨U false, h false, hb false, rfl⟩
  have hy : y ∈ toricClosure (k := k) o π :=
    parameterImage_subset_toricClosure o π ⟨U true, h true, hb true, rfl⟩
  refine ⟨x + y, ?_, hnonzero⟩
  intro Q hQ
  exact hQ (x + y) ⟨x, hx, y, hy, rfl⟩

end Sunlet.ToricPairAlgebra

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω) (hm : 5 ≤ Fintype.card Ω)

include hm in
/-- A dense nonempty principal open with a unique unordered pair of
distinct summands, all of whose coordinates are nonzero. Every alternative
decomposition in the full toric closure is included in the quantifiers. -/
theorem generic_unique_nonzero_decomposition :
    ∃ P : MvPolynomial (L.NonidentityColor × Ω) k,
      MvPolynomial.aeval (genericCoordinates (k := k) o L.nonidentityPerm) P ≠ 0 ∧
      (principalOpen (k := k) o L.nonidentityPerm P).Nonempty ∧
      PolynomialClosureProduct.closure (principalOpen (k := k) o L.nonidentityPerm P) =
        secantClosure (k := k) o L.nonidentityPerm ∧
      ∀ z ∈ principalOpen (k := k) o L.nonidentityPerm P,
        ∃ x ∈ toricClosure (k := k) o L.nonidentityPerm,
          ∃ y ∈ toricClosure (k := k) o L.nonidentityPerm,
            x + y = z ∧ (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ x ≠ y ∧
            ∀ x' ∈ toricClosure (k := k) o L.nonidentityPerm,
              ∀ y' ∈ toricClosure (k := k) o L.nonidentityPerm,
                x' + y' = z → (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  let W := L.genericWitness (k := k) o hm
  obtain ⟨a, _, _, _, _⟩ := W.Atwo
  let p : L.NonidentityColor × Ω := (a, o)
  obtain ⟨D⟩ := exists_pivotRecovery_of_witness (k := k) o L.nonidentityPerm W
    (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm) p
  refine ⟨D.torusOpenPolynomial, D.torusOpenPolynomial_generic_ne,
    principalOpen_nonempty o L.nonidentityPerm _ D.torusOpenPolynomial_generic_ne,
    closure_principalOpen o L.nonidentityPerm _ D.torusOpenPolynomial_generic_ne, ?_⟩
  intro z hz
  have hbase := (D.torusOpen_factors z hz.2).1
  have hnot : genericDifference (k := k) o L.nonidentityPerm p ∉
      JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm) :=
    (L.loopAt o).difference_not_mem_coordinateField (k := k)
      (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p
  obtain ⟨x, hx, y, hy, hs⟩ := D.exists_pair_on_open hnot z hz.1 hbase
  obtain ⟨hxn, hyn, hxy⟩ := D.summands_nonzero_distinct z x y hz.2 hx hy hs
  refine ⟨x, hx, y, hy, hs, hxn, hyn, hxy, ?_⟩
  intro x' hx' y' hy' hs'
  exact D.unique_unordered_on_open z x y x' y' hbase hx hy hx' hy' hs hs'

end Sunlet.NormalizedLatinSystem
end
end Stage_ToricOpenConditions

#check "SUNLET_ToricOpenConditions_READY"

section Stage_LatinToricOpen



/-!
# A generic open with actual normalized torus representatives

The closure-to-torus bridge and the explicit nonvanishing numerators remove
all auxiliary assumptions from the point-fiber calculation: every output
in one dense nonempty principal open has two distinct toric summands, both
with actual unit torus parameters and nonzero coefficient families.
-/

noncomputable section

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)

/-- An all-nonzero point of the actual toric closure has a literal
normalized torus representation with nonzero coefficients. -/
theorem exists_toric_parameters_of_nonzero (x : ι × Ω → k)
    (hx : x ∈ toricClosure (k := k) o π) (hxn : ∀ i, x i ≠ 0) :
    ∃ (U : ι → k) (h : Ω → kˣ), h o = 1 ∧ (∀ a, U a ≠ 0) ∧ toricPoint π U h = x := by
  let D : ι × Ω → LaurentMonomials.Exponent (Bool × NormalizedVariations.Index ι Ω o) :=
    fun ax => LaurentMonomials.copyExponent false (ToricMonomialRationality.pointExponent o π ax)
  have hD : (fun ax => LaurentMonomials.monomial (k := k) (D ax)) =
      genericPoint (k := k) o π false := by
    funext ax
    exact ToricMonomialRationality.monomial_pointExponent o π false ax
  obtain ⟨t, ht⟩ := ToricNonzeroLifting.exists_lift_of_generic_equations D x hxn (by
    intro P hP
    rw [hD] at hP
    exact hx P ((generic_point_equation_iff o π false P).mp hP))
  let U : ι → k := fun a => (t (false, .inl a)).val
  let h : Ω → kˣ := fun b => if hb : b = o then 1 else t (false, .inr ⟨b, hb⟩)
  have htorus (b : Ω) :
      ToricNonzeroLifting.character t
        (LaurentMonomials.copyExponent false (ToricMonomialRationality.torusExponent (ι := ι) o b)) =
          Additive.ofMul (h b) := by
    by_cases hb : b = o <;> simp [ToricMonomialRationality.torusExponent, h, hb]
  have hpoint : ToricNonzeroLifting.point D t = toricPoint π U h := by
    funext ⟨a, b⟩
    change ((ToricNonzeroLifting.character t
      (LaurentMonomials.copyExponent false
        (ToricMonomialRationality.pointExponent o π (a, b)))).toMul).val =
          U a * ((h b).val / (h (π a b)).val)
    simp only [ToricMonomialRationality.pointExponent, sub_eq_add_neg, map_add, map_neg,
      LaurentMonomials.copyExponent_single, ToricNonzeroLifting.character_single,
      one_smul, htorus, toMul_add, toMul_neg, toMul_ofMul,
      Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [U, div_eq_mul_inv, mul_assoc]
  exact ⟨U, h, by simp [h], fun a => (t (false, .inl a)).ne_zero, hpoint.symm.trans ht⟩

end Sunlet.ToricPairAlgebra

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω) (hm : 5 ≤ Fintype.card Ω)

include hm in
/-- The generic decomposition theorem in the exact form needed for
geometric fibers. Both component representatives exist on the same dense
nonempty principal open; every alternative closure decomposition is
included, and the coefficient families are proved nonzero. -/
theorem generic_unique_torus_decomposition :
    ∃ P : MvPolynomial (L.NonidentityColor × Ω) k,
      MvPolynomial.aeval (genericCoordinates (k := k) o L.nonidentityPerm) P ≠ 0 ∧
      (principalOpen (k := k) o L.nonidentityPerm P).Nonempty ∧
      PolynomialClosureProduct.closure (principalOpen (k := k) o L.nonidentityPerm P) =
        secantClosure (k := k) o L.nonidentityPerm ∧
      ∀ z ∈ principalOpen (k := k) o L.nonidentityPerm P,
        ∃ (U V : L.NonidentityColor → k) (h g : Ω → kˣ),
          h o = 1 ∧ g o = 1 ∧ (∀ a, U a ≠ 0) ∧ (∀ a, V a ≠ 0) ∧
          toricPoint L.nonidentityPerm U h + toricPoint L.nonidentityPerm V g = z ∧
          toricPoint L.nonidentityPerm U h ≠ toricPoint L.nonidentityPerm V g ∧
          ∀ x' ∈ toricClosure (k := k) o L.nonidentityPerm,
            ∀ y' ∈ toricClosure (k := k) o L.nonidentityPerm,
              x' + y' = z →
                (toricPoint L.nonidentityPerm U h = x' ∧ toricPoint L.nonidentityPerm V g = y') ∨
                (toricPoint L.nonidentityPerm U h = y' ∧ toricPoint L.nonidentityPerm V g = x') := by
  obtain ⟨P, hP, hnonempty, hdense, hdecomp⟩ :=
    L.generic_unique_nonzero_decomposition (k := k) o hm
  refine ⟨P, hP, hnonempty, hdense, ?_⟩
  intro z hz
  obtain ⟨x, hx, y, hy, hs, hxn, hyn, hxy, huniq⟩ := hdecomp z hz
  obtain ⟨U, h, hb, hU, he⟩ := exists_toric_parameters_of_nonzero o L.nonidentityPerm x hx hxn
  obtain ⟨V, g, gb, hV, hf⟩ := exists_toric_parameters_of_nonzero o L.nonidentityPerm y hy hyn
  refine ⟨U, V, h, g, hb, gb, hU, hV, ?_, ?_, ?_⟩
  · simpa only [he, hf] using hs
  · simpa only [he, hf] using hxy
  · simpa only [he, hf] using huniq

end Sunlet.NormalizedLatinSystem
end
end Stage_LatinToricOpen

#check "SUNLET_LatinToricOpen_READY"

#check @Sunlet.NormalizedLatinSystem.offDiagonal_rational
#print axioms Sunlet.NormalizedLatinSystem.offDiagonal_rational
#check @Sunlet.NormalizedLatinSystem.generic_unique_nonzero_decomposition
#print axioms Sunlet.NormalizedLatinSystem.generic_unique_nonzero_decomposition
#check @Sunlet.ToricPairAlgebra.exists_toric_parameters_of_nonzero
#print axioms Sunlet.ToricPairAlgebra.exists_toric_parameters_of_nonzero
#check @Sunlet.NormalizedLatinSystem.generic_unique_torus_decomposition
#print axioms Sunlet.NormalizedLatinSystem.generic_unique_torus_decomposition
