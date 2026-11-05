module

public import PaperVerification.AlternatingFormsExteriorCoordinates
public import PaperVerification.AlternatingFormsDuality
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Scalar change on the actual finite exterior powers

The maps are the universal exterior-algebra maps induced by coefficient
change.  Increasing exterior words give their literal coordinate formula.
In particular a surjective coefficient map is surjective on every exterior
power, and reduction modulo an ideal has precisely the expected kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R]

def powerBasis (s n : ℕ) :
    Module.Basis (PluckerIndex s n) R (⋀[R]^s (Fin n → R)) :=
  ((Pi.basisFun R (Fin n)).exteriorPower s).reindex (pluckerSubsetEquiv s n).symm

theorem powerBasis_apply {s n : ℕ} (I : PluckerIndex s n) :
    powerBasis R s n I =
      exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I.val i)) := by
  simp only [powerBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    pluckerSubsetEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

def firstForm (k : ℕ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathFirstLeft i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i)]

def secondForm (k : ℕ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathSecondRight i)]

abbrev quotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree (firstForm R k) (secondForm R k) s

variable (S : Type*) [CommRing S] [Algebra R S]

def vectorMap (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → S) :=
  (Pi.basisFun R (Fin n)).constr R (Pi.basisFun S (Fin n))

@[simp] theorem vectorMap_basis (n : ℕ) (i : Fin n) :
    vectorMap R S n (Pi.basisFun R (Fin n) i) = Pi.basisFun S (Fin n) i :=
  Module.Basis.constr_basis _ _ _ _

def exteriorMap (n : ℕ) :
    ExteriorAlgebra R (Fin n → R) →ₐ[R] ExteriorAlgebra S (Fin n → S) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S).restrictScalars R).comp (vectorMap R S n),
      fun x => ExteriorAlgebra.ι_sq_zero (R := S) (vectorMap R S n x)⟩

@[simp] theorem exteriorMap_ι_basis (n : ℕ) (i : Fin n) :
    exteriorMap R S n (ExteriorAlgebra.ι R (Pi.basisFun R (Fin n) i)) =
      ExteriorAlgebra.ι S (Pi.basisFun S (Fin n) i) := by
  erw [exteriorMap, ExteriorAlgebra.lift_ι_apply]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, vectorMap_basis]

theorem exteriorMap_word {s n : ℕ} (I : Fin s → Fin n) :
    exteriorMap R S n
      (ExteriorAlgebra.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I i))) =
      ExteriorAlgebra.ιMulti S s (fun i => Pi.basisFun S (Fin n) (I i)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_map, List.map_ofFn,
    Function.comp_def, exteriorMap_ι_basis]

def powerMap (s n : ℕ) : (⋀[R]^s (Fin n → R)) →ₗ[R] (⋀[S]^s (Fin n → S)) :=
  (powerBasis R s n).constr R (powerBasis S s n)

@[simp] theorem powerMap_basis {s n : ℕ} (I : PluckerIndex s n) :
    powerMap R S s n (powerBasis R s n I) = powerBasis S s n I :=
  Module.Basis.constr_basis _ _ _ _

theorem powerMap_coe {s n : ℕ} (x : ⋀[R]^s (Fin n → R)) :
    (powerMap R S s n x : ExteriorAlgebra S (Fin n → S)) =
      exteriorMap R S n x := by
  have h : ((Submodule.subtype (⋀[S]^s (Fin n → S))).restrictScalars R).comp
      (powerMap R S s n) =
      (exteriorMap R S n).toLinearMap.comp (Submodule.subtype (⋀[R]^s (Fin n → R))) := by
    apply (powerBasis R s n).ext
    intro I
    change (powerMap R S s n (powerBasis R s n I) :
      ExteriorAlgebra S (Fin n → S)) = exteriorMap R S n (powerBasis R s n I)
    rw [powerMap_basis]
    simpa only [powerBasis_apply, exteriorPower.ιMulti_apply_coe] using
      (exteriorMap_word R S I.val).symm
  exact congrArg (fun L : (⋀[R]^s (Fin n → R)) →ₗ[R]
    ExteriorAlgebra S (Fin n → S) => L x) h

theorem powerMap_repr {s n : ℕ} (x : ⋀[R]^s (Fin n → R)) (I : PluckerIndex s n) :
    (powerBasis S s n).repr (powerMap R S s n x) I =
      algebraMap R S ((powerBasis R s n).repr x I) := by
  classical
  conv_lhs => rw [← (powerBasis R s n).sum_repr x, map_sum]
  simp only [map_smul, powerMap_basis]
  simp_rw [← IsScalarTower.algebraMap_smul (R := R) S]
  simp only [map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem powerMap_injective (h : Function.Injective (algebraMap R S)) (s n : ℕ) :
    Function.Injective (powerMap R S s n) := by
  intro x y hxy
  apply (powerBasis R s n).repr.injective
  ext I
  apply h
  rw [← powerMap_repr R S x I, ← powerMap_repr R S y I, hxy]

theorem powerMap_surjective (h : Function.Surjective (algebraMap R S)) (s n : ℕ) :
    Function.Surjective (powerMap R S s n) := by
  classical
  intro y
  choose c hc using fun I : PluckerIndex s n => h ((powerBasis S s n).repr y I)
  refine ⟨(powerBasis R s n).equivFun.symm c, ?_⟩
  apply (powerBasis S s n).repr.injective
  ext I
  rw [powerMap_repr]
  change algebraMap R S ((powerBasis R s n).coord I
    ((powerBasis R s n).equivFun.symm c)) = _
  rw [Module.Basis.coord_equivFun_symm]
  exact hc I

theorem powerMap_word {s n : ℕ} (I : Fin s → Fin n) :
    powerMap R S s n
      (exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin n) (I i))) =
      exteriorPower.ιMulti S s (fun i => Pi.basisFun S (Fin n) (I i)) := by
  apply Subtype.ext
  rw [powerMap_coe]
  exact exteriorMap_word R S I

theorem powerMap_pair {n : ℕ} (u v : Fin n) :
    powerMap R S 2 n
      (exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin n) u, Pi.basisFun R (Fin n) v]) =
      exteriorPower.ιMulti S 2 ![Pi.basisFun S (Fin n) u, Pi.basisFun S (Fin n) v] := by
  apply Subtype.ext
  rw [powerMap_coe]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, mul_one, map_mul, exteriorMap_ι_basis]

@[simp] theorem powerMap_firstForm (k : ℕ) :
    powerMap R S 2 (2*k+1) (firstForm R k) = firstForm S k := by
  simp only [firstForm, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact powerMap_pair R S (oddPathFirstLeft i) (oddPathMiddle i)

@[simp] theorem powerMap_secondForm (k : ℕ) :
    powerMap R S 2 (2*k+1) (secondForm R k) = secondForm S k := by
  simp only [secondForm, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact powerMap_pair R S (oddPathMiddle i) (oddPathSecondRight i)

theorem powerMap_wedge {n a b : ℕ}
    (x : ⋀[R]^a (Fin n → R)) (y : ⋀[R]^b (Fin n → R)) :
    powerMap R S (a+b) n (exteriorPower.wedge R _ a b x y) =
      exteriorPower.wedge S _ a b (powerMap R S a n x) (powerMap R S b n y) := by
  apply Subtype.ext
  rw [powerMap_coe]
  simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    map_mul, ← powerMap_coe]

theorem powerMap_relations_mem {k s : ℕ}
    (x : ⋀[R]^s (Fin (2*k+1) → R))
    (hx : x∈exteriorDegreeRelations (firstForm R k) (secondForm R k) s) :
    powerMap R S s (2*k+1) x∈
      exteriorDegreeRelations (firstForm S k) (secondForm S k) s := by
  change (x : ExteriorAlgebra R (Fin (2*k+1) → R))∈exteriorRelationIdeal _ _ at hx
  change (powerMap R S s (2*k+1) x : ExteriorAlgebra S (Fin (2*k+1) → S))∈
    exteriorRelationIdeal _ _
  obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hx
  apply Ideal.mem_span_pair.mpr
  refine ⟨exteriorMap R S _ a, exteriorMap R S _ b, ?_⟩
  have hf := congrArg Subtype.val (powerMap_firstForm R S k)
  have hg := congrArg Subtype.val (powerMap_secondForm R S k)
  rw [powerMap_coe] at hf hg
  rw [powerMap_coe, ← hab, map_add, map_mul, map_mul, hf, hg]

def quotientMap (k s : ℕ) : quotientDegree R k s →ₗ[R] quotientDegree S k s :=
  (Submodule.Quotient.restrictScalarsEquiv R
    (exteriorDegreeRelations (firstForm S k) (secondForm S k) s)).toLinearMap.comp
      ((exteriorDegreeRelations (firstForm R k) (secondForm R k) s).mapQ
        ((exteriorDegreeRelations (firstForm S k) (secondForm S k) s).restrictScalars R)
        (powerMap R S s (2*k+1)) (fun x hx => powerMap_relations_mem R S x hx))

@[simp] theorem quotientMap_mk {k s : ℕ} (x : ⋀[R]^s (Fin (2*k+1) → R)) :
    quotientMap R S k s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (powerMap R S s (2*k+1) x) := rfl

theorem powerMap_relations_surjective
    (h : Function.Surjective (algebraMap R S)) (k s : ℕ) :
    (exteriorDegreeRelations (firstForm R k) (secondForm R k) s).map
        (powerMap R S s (2*k+1)) =
      (exteriorDegreeRelations (firstForm S k) (secondForm S k) s).restrictScalars R := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact powerMap_relations_mem R S y hy
  · intro x hx
    by_cases hs : s<2
    · rw [exteriorDegreeRelations_eq_bot _ _ hs] at hx
      have hz : x=0 := hx
      rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hs)
      change x∈exteriorDegreeRelations (firstForm S k) (secondForm S k) (2+q) at hx
      rw [exteriorDegreeRelations_eq_images] at hx
      obtain ⟨a,⟨y,rfl⟩,b,⟨z,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨y',hy'⟩ := powerMap_surjective R S h q (2*k+1) y
      obtain ⟨z',hz'⟩ := powerMap_surjective R S h q (2*k+1) z
      refine ⟨exteriorPower.wedge R _ 2 q (firstForm R k) y' +
        exteriorPower.wedge R _ 2 q (secondForm R k) z', ?_, ?_⟩
      · rw [exteriorDegreeRelations_eq_images]
        exact Submodule.mem_sup.mpr
          ⟨_,LinearMap.mem_range_self _ y',_,LinearMap.mem_range_self _ z',rfl⟩
      · rw [map_add, powerMap_wedge, powerMap_wedge,
          powerMap_firstForm, powerMap_secondForm, hy', hz']

theorem quotientMap_surjective
    (h : Function.Surjective (algebraMap R S)) (k s : ℕ) :
    Function.Surjective (quotientMap R S k s) := by
  intro y
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (exteriorDegreeRelations (firstForm S k) (secondForm S k) s) y
  obtain ⟨x',hx'⟩ := powerMap_surjective R S h s (2*k+1) x
  refine ⟨Submodule.Quotient.mk x', ?_⟩
  rw [quotientMap_mk, hx']
  rfl

variable {S}

theorem powerMap_quotient_ker (J : Ideal R) (s n : ℕ) :
    (powerMap R (R⧸J) s n).ker = J • (⊤ : Submodule R (⋀[R]^s (Fin n → R))) := by
  classical
  apply le_antisymm
  · intro x hx
    have hz : powerMap R (R⧸J) s n x=0 := hx
    have hc (I : PluckerIndex s n) : (powerBasis R s n).repr x I∈J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change algebraMap R (R⧸J) ((powerBasis R s n).repr x I)=0
      rw [← powerMap_repr, hz, map_zero, Finsupp.zero_apply]
    rw [← (powerBasis R s n).sum_repr x]
    exact Submodule.sum_mem _ fun I hI => Submodule.smul_mem_smul (hc I) (Submodule.mem_top)
  · apply Submodule.smul_le.mpr
    intro r hr x hx
    change powerMap R (R⧸J) s n (r • x)=0
    rw [map_smul, ← IsScalarTower.algebraMap_smul (R⧸J),
      show algebraMap R (R⧸J) r=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_smul]

theorem quotientMap_quotient_ker (J : Ideal R) (k s : ℕ) :
    (quotientMap R (R⧸J) k s).ker =
      J • (⊤ : Submodule R (quotientDegree R k s)) := by
  classical
  let N := exteriorDegreeRelations (firstForm R k) (secondForm R k) s
  let π : (⋀[R]^s (Fin (2*k+1) → R)) →ₗ[R] quotientDegree R k s := N.mkQ
  have hred : Function.Surjective (algebraMap R (R⧸J)) := Ideal.Quotient.mk_surjective
  apply le_antisymm
  · intro z hz
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective N z
    have hx : powerMap R (R⧸J) s (2*k+1) x ∈
        exteriorDegreeRelations (firstForm (R⧸J) k) (secondForm (R⧸J) k) s := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact hz
    have hm := powerMap_relations_surjective R (R⧸J) hred k s
    change powerMap R (R⧸J) s (2*k+1) x ∈
      (exteriorDegreeRelations (firstForm (R⧸J) k)
        (secondForm (R⧸J) k) s).restrictScalars R at hx
    rw [← hm] at hx
    obtain ⟨y,hy,hyx⟩ := hx
    have hxy : x-y∈J • (⊤ : Submodule R (⋀[R]^s (Fin (2*k+1) → R))) := by
      rw [← powerMap_quotient_ker R J s (2*k+1)]
      change powerMap R (R⧸J) s (2*k+1) (x-y)=0
      rw [map_sub, hyx, sub_self]
    have hmap : π (x-y)∈
        (J • (⊤ : Submodule R (⋀[R]^s (Fin (2*k+1) → R)))).map π :=
      Submodule.mem_map_of_mem hxy
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
      (Submodule.mkQ_surjective N)] at hmap
    simpa only [π, map_sub, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hy, sub_zero] using hmap
  · apply Submodule.smul_le.mpr
    intro r hr x hx
    change quotientMap R (R⧸J) k s (r • x)=0
    rw [map_smul, ← IsScalarTower.algebraMap_smul (R⧸J),
      show algebraMap R (R⧸J) r=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_smul]

end PaperVerification.AlternatingForms.IntegralOdd
