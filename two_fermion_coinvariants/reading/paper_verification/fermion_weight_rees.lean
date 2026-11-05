module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# The actual Laurent Rees algebra of a finite weighted basis

The family is a subalgebra of the Laurent polynomial algebra of the original
algebra. Its specified generators are t^(-w_i)b_i. Closure is derived from
the actual multiplication coefficients. Laurent coefficient extraction
proves that these generators are linearly independent over K[t]; thus the
family is finite free and flat, with no flatness premise.

The relation between the basis-tail filtration and the actual quotient
filtration is supplied separately by `BlockInitial.TriangularPresentation.actual_descending_filtration_iff`.
The special-fiber identifications are separate obligations, not definitions
of this subalgebra.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.WeightRees

open scoped Classical BigOperators LaurentPolynomial

variable (K A : Type*) [CommRing K] [Ring A] [Algebra K A]

def parameterMap : Polynomial K →+* LaurentPolynomial A :=
  Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap K A))

@[simp] theorem parameterMap_C (c : K) :
    parameterMap K A (Polynomial.C c)=algebraMap K (LaurentPolynomial A) c := by
  simp only [parameterMap,RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.toLaurent_C,LaurentPolynomial.algebraMap_apply]

@[simp] theorem parameterMap_X :
    parameterMap K A Polynomial.X=LaurentPolynomial.T 1 := by
  simp only [parameterMap,RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_X,
    Polynomial.toLaurent_X]

@[simp] theorem parameterMap_monomial (r : ℕ) (c : K) :
    parameterMap K A (Polynomial.monomial r c)=
      AddMonoidAlgebra.single (r : ℤ) (algebraMap K A c) := by
  simp only [parameterMap,RingHom.comp_apply,Polynomial.coe_mapRingHom,
    Polynomial.map_monomial,Polynomial.toLaurent_C_mul_T,
    ←LaurentPolynomial.single_eq_C_mul_T]

theorem parameterMap_central (p : Polynomial K) (z : LaurentPolynomial A) :
    parameterMap K A p*z=z*parameterMap K A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,add_mul,mul_add,hp,hq]
  | monomial r c =>
      rw [parameterMap_monomial,LaurentPolynomial.single_eq_C_mul_T]
      have hc : LaurentPolynomial.C (algebraMap K A c)*z=
          z*LaurentPolynomial.C (algebraMap K A c) := Algebra.commutes c z
      calc
        (LaurentPolynomial.C (algebraMap K A c)*LaurentPolynomial.T (r : ℤ))*z=
            LaurentPolynomial.C (algebraMap K A c)*(LaurentPolynomial.T (r : ℤ)*z) := mul_assoc _ _ _
        _=LaurentPolynomial.C (algebraMap K A c)*(z*LaurentPolynomial.T (r : ℤ)) := by
          rw [LaurentPolynomial.T_mul]
        _=(LaurentPolynomial.C (algebraMap K A c)*z)*LaurentPolynomial.T (r : ℤ) :=
          (mul_assoc _ _ _).symm
        _=(z*LaurentPolynomial.C (algebraMap K A c))*LaurentPolynomial.T (r : ℤ) := by rw [hc]
        _=z*(LaurentPolynomial.C (algebraMap K A c)*LaurentPolynomial.T (r : ℤ)) := mul_assoc _ _ _

/-- The parameter acts by the central Laurent variable, not by an evaluation
of that variable inside the original coefficient algebra. -/
scoped instance parameterAlgebra : Algebra (Polynomial K) (LaurentPolynomial A) :=
  (parameterMap K A).toAlgebra' (parameterMap_central K A)

open scoped PaperVerification.Fermion.WeightRees

scoped instance parameterTower : IsScalarTower K (Polynomial K) (LaurentPolynomial A) :=
  IsScalarTower.of_algebraMap_eq (fun c ↦ (parameterMap_C K A c).symm)

variable {K A}

def laurentCoefficient (e : ℤ) : LaurentPolynomial A →ₗ[K] A where
  toFun z := z.coeff e
  map_add' z t := by simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  map_smul' c z := by simp only [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,RingHom.id_apply]

variable {I : Type*} [Fintype I] (b : Module.Basis I K A) (weight : I → ℕ)

def shiftedBasisVector (i : I) : LaurentPolynomial A :=
  AddMonoidAlgebra.single (-(weight i : ℤ)) (b i)

theorem monomial_smul_shifted (r : ℕ) (c : K) (i : I) :
    (Polynomial.monomial r c) • shiftedBasisVector b weight i=
      AddMonoidAlgebra.single ((r : ℤ)-(weight i : ℤ)) (c • b i) := by
  change parameterMap K A (Polynomial.monomial r c)*
    AddMonoidAlgebra.single (-(weight i : ℤ)) (b i)=_
  rw [parameterMap_monomial,AddMonoidAlgebra.single_mul_single]
  simp only [sub_eq_add_neg,Algebra.smul_def]

def coefficientExtract (i : I) (r : ℕ) : LaurentPolynomial A →ₗ[K] K :=
  (b.coord i).comp (laurentCoefficient ((r : ℤ)-(weight i : ℤ)))

theorem coefficientExtract_monomial (i j : I) (r s : ℕ) (c : K) :
    coefficientExtract b weight i r ((Polynomial.monomial s c) • shiftedBasisVector b weight j)=
      if i=j then (Polynomial.monomial s c).coeff r else 0 := by
  classical
  rw [monomial_smul_shifted]
  change b.repr
    ((AddMonoidAlgebra.single ((s : ℤ)-(weight j : ℤ)) (c • b j)).coeff
      ((r : ℤ)-(weight i : ℤ))) i=_
  rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases hij : i=j
  · subst j
    have he : (s : ℤ)-(weight i : ℤ)=(r : ℤ)-(weight i : ℤ) ↔ s=r := by omega
    simp only [he,if_pos rfl,Polynomial.coeff_monomial,Finsupp.single_apply]
    split_ifs <;> simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_same,smul_eq_mul,mul_one,map_zero,Finsupp.zero_apply]
  · rw [if_neg hij]
    split_ifs <;> simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hij,smul_zero,map_zero,Finsupp.zero_apply]

theorem coefficientExtract_smul_shifted (i j : I) (r : ℕ) (p : Polynomial K) :
    coefficientExtract b weight i r (p • shiftedBasisVector b weight j)=
      if i=j then p.coeff r else 0 := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_smul,map_add,hp,hq,Polynomial.coeff_add]
      split_ifs <;> simp only [add_zero]
  | monomial s c => exact coefficientExtract_monomial b weight i j r s c

theorem shiftedBasisVector_linearIndependent :
    LinearIndependent (Polynomial K) (shiftedBasisVector b weight) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  ext r
  have hh := congrArg (coefficientExtract b weight i r) hc
  simp only [map_sum,coefficientExtract_smul_shifted,map_zero] at hh
  simpa only [Finset.sum_ite_eq,Finset.mem_univ,if_true,Polynomial.coeff_zero] using hh

def span : Submodule (Polynomial K) (LaurentPolynomial A) :=
  Submodule.span (Polynomial K) (Set.range (shiftedBasisVector b weight))

/-- The coefficient condition is precisely preservation of the descending
filtration by multiplication in the original algebra. -/
def Multiplicative : Prop :=
  ∀ i j k,b.repr (b i*b j) k≠0 → weight i+weight j≤weight k

def multiplicationPolynomial (i j k : I) : Polynomial K :=
  Polynomial.monomial (weight k-(weight i+weight j)) (b.repr (b i*b j) k)

theorem shiftedBasisVector_mul (hmul : Multiplicative b weight) (i j : I) :
    shiftedBasisVector b weight i*shiftedBasisVector b weight j=
      ∑ k,multiplicationPolynomial b weight i j k • shiftedBasisVector b weight k := by
  classical
  rw [shiftedBasisVector,shiftedBasisVector,AddMonoidAlgebra.single_mul_single]
  change (AddMonoidAlgebra.lsingle (R := K) (-(weight i : ℤ)+(-(weight j : ℤ))))
    (b i*b j)=_
  rw [←b.sum_repr (b i*b j),map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AddMonoidAlgebra.single (-(weight i : ℤ)+(-(weight j : ℤ)))
    ((b.repr (b i*b j) k) • b k)=_
  rw [multiplicationPolynomial,monomial_smul_shifted]
  by_cases hc : b.repr (b i*b j) k=0
  · simp only [hc,zero_smul,AddMonoidAlgebra.single_zero]
  · have hw := hmul i j k hc
    have he : ((weight k-(weight i+weight j) : ℕ) : ℤ)-(weight k : ℤ)=
        -(weight i : ℤ)+(-(weight j : ℤ)) := by omega
    rw [he]

theorem shifted_unit_expansion :
    (1 : LaurentPolynomial A)=
      ∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)) • shiftedBasisVector b weight i := by
  change (AddMonoidAlgebra.lsingle (R := K) (0 : ℤ)) (1 : A)=_
  conv_lhs => rw [←b.sum_repr (1 : A),map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change AddMonoidAlgebra.single 0 ((b.repr 1 i) • b i)=_
  rw [monomial_smul_shifted,sub_self]

theorem one_mem_span : (1 : LaurentPolynomial A)∈span b weight := by
  rw [shifted_unit_expansion b weight]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem span_mul_mem (hmul : Multiplicative b weight)
    (x y : LaurentPolynomial A) (hx : x∈span b weight) (hy : y∈span b weight) :
    x*y∈span b weight := by
  have hgen (i j : I) : shiftedBasisVector b weight i*shiftedBasisVector b weight j∈span b weight := by
    rw [shiftedBasisVector_mul b weight hmul]
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)
  have hright (i : I) : shiftedBasisVector b weight i*y∈span b weight := by
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨j,rfl⟩ := hz; exact hgen i j
    | zero => simpa only [mul_zero] using (span b weight).zero_mem
    | add z t hz ht ihz iht =>
        simpa only [mul_add] using (span b weight).add_mem ihz iht
    | smul c z hz ih =>
        simpa only [mul_smul_comm] using (span b weight).smul_mem c ih
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i,rfl⟩ := hz; exact hright i
  | zero => simpa only [zero_mul] using (span b weight).zero_mem
  | add z t hz ht ihz iht => simpa only [add_mul] using (span b weight).add_mem ihz iht
  | smul c z hz ih => simpa only [smul_mul_assoc] using (span b weight).smul_mem c ih

/-- The Rees algebra is a genuine subalgebra of Laurent polynomials over
the original, potentially noncommutative algebra. -/
def algebra (hmul : Multiplicative b weight) :
    Subalgebra (Polynomial K) (LaurentPolynomial A) where
  carrier := span b weight
  zero_mem' := (span b weight).zero_mem
  add_mem' := (span b weight).add_mem
  one_mem' := one_mem_span b weight
  mul_mem' := fun hx hy ↦ span_mul_mem b weight hmul _ _ hx hy
  algebraMap_mem' c := by
    change algebraMap (Polynomial K) (LaurentPolynomial A) c∈span b weight
    rw [Algebra.algebraMap_eq_smul_one]
    exact (span b weight).smul_mem c (one_mem_span b weight)

/-- Canonical structure constructors, with the ambient ring and parameter
algebra fixed before specializing to a concrete quotient. -/
def algebraRing (hmul : Multiplicative b weight) : Ring (algebra b weight hmul) :=
  (algebra b weight hmul).toRing

def algebraPolynomialAlgebra (hmul : Multiplicative b weight) :
    Algebra (Polynomial K) (algebra b weight hmul) :=
  (algebra b weight hmul).algebra

def algebraBaseAlgebra (hmul : Multiplicative b weight) :
    Algebra K (algebra b weight hmul) :=
  (algebra b weight hmul).algebra'

def algebraScalarTower (hmul : Multiplicative b weight) :
    IsScalarTower K (Polynomial K) (algebra b weight hmul) :=
  inferInstance

def spanEquivAlgebra (hmul : Multiplicative b weight) :
    span b weight ≃ₗ[Polynomial K] algebra b weight hmul where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def basis (hmul : Multiplicative b weight) :
    Module.Basis I (Polynomial K) (algebra b weight hmul) :=
  (Module.Basis.span (shiftedBasisVector_linearIndependent b weight)).map
    (spanEquivAlgebra b weight hmul)

@[simp] theorem basis_coe (hmul : Multiplicative b weight) (i : I) :
    (basis b weight hmul i : LaurentPolynomial A)=shiftedBasisVector b weight i := by
  exact (congrArg (fun x : algebra b weight hmul ↦ (x : LaurentPolynomial A))
    (Module.Basis.map_apply
      (Module.Basis.span (shiftedBasisVector_linearIndependent b weight))
      (spanEquivAlgebra b weight hmul) i)).trans
        (Module.Basis.coe_span_apply (shiftedBasisVector_linearIndependent b weight) i)

theorem basis_mul (hmul : Multiplicative b weight) (i j : I) :
    basis b weight hmul i*basis b weight hmul j=
      ∑ k,multiplicationPolynomial b weight i j k • basis b weight hmul k := by
  apply Subtype.ext
  change (basis b weight hmul i : LaurentPolynomial A)*
    (basis b weight hmul j : LaurentPolynomial A)=
      (algebra b weight hmul).val (∑ k,multiplicationPolynomial b weight i j k • basis b weight hmul k)
  rw [map_sum]
  simp only [map_smul,Subalgebra.val_apply,basis_coe]
  exact shiftedBasisVector_mul b weight hmul i j

theorem basis_unit_expansion (hmul : Multiplicative b weight) :
    (1 : algebra b weight hmul)=
      ∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)) • basis b weight hmul i := by
  apply Subtype.ext
  change (1 : LaurentPolynomial A)=
    (algebra b weight hmul).val (∑ i,(Polynomial.monomial (weight i) (b.repr 1 i)) • basis b weight hmul i)
  rw [map_sum]
  simp only [map_smul,Subalgebra.val_apply,basis_coe]
  exact shifted_unit_expansion b weight

theorem finite_free (hmul : Multiplicative b weight) :
    Module.Finite (Polynomial K) (algebra b weight hmul) ∧
      Module.Free (Polynomial K) (algebra b weight hmul) :=
  ⟨Module.Finite.of_basis (basis b weight hmul),Module.Free.of_basis (basis b weight hmul)⟩

theorem flat (hmul : Multiplicative b weight) :
    Module.Flat (Polynomial K) (algebra b weight hmul) := by
  letI := (finite_free b weight hmul).2
  infer_instance

end PaperVerification.Fermion.WeightRees
