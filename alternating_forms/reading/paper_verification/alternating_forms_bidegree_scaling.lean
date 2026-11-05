module

public import PaperVerification.AlternatingFormsOddPencilRelations
public import PaperVerification.AlternatingFormsDuality
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Basic

/-!
# The actual diagonal action distinguishing the two exterior degrees

In the path order `b₀,a₁,b₁,…,aₖ,bₖ`, scale the odd positions by a scalar
and fix the even positions.  Both actual canonical quadratic relations are
scaled by that same scalar.  Hence the action descends to the genuine
exterior quotient in every total degree.  On an exterior word its eigenvalue
is the scalar raised to the number of `a`-letters.  No grading or dimension
formula for the quotient is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.Bidegree

section Diagonal

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A literal diagonal linear map in the specified original vector basis. -/
def basisScaling (B : Module.Basis I K M) (δ : I → ℕ) (c : K) : M →ₗ[K] M :=
  B.constr K (fun i => c ^ δ i • B i)

@[simp] theorem basisScaling_basis (B : Module.Basis I K M) (δ : I → ℕ)
    (c : K) (i : I) : basisScaling B δ c (B i)=c ^ δ i • B i :=
  Module.Basis.constr_basis _ _ _ _

/-- Scaling on an actual alternating word multiplies the diagonal weights. -/
theorem basisScaling_word (B : Module.Basis I K M) (δ : I → ℕ)
    (c : K) (s : ℕ) (a : Fin s → I) :
    exteriorPower.map s (basisScaling B δ c)
        (exteriorPower.ιMulti K s (fun j => B (a j)))=
      c ^ (∑ j,δ (a j)) • exteriorPower.ιMulti K s (fun j => B (a j)) := by
  rw [exteriorPower.map_apply_ιMulti]
  have he : basisScaling B δ c ∘ (fun j => B (a j))=
      fun j => c ^ δ (a j) • B (a j) := by
    funext j
    exact basisScaling_basis B δ c (a j)
  rw [he,AlternatingMap.map_smul_univ,Finset.prod_pow_eq_pow_sum]

end Diagonal

section Relations

variable {K M J : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype J] [DecidableEq J]

/-- Functoriality of the actual matching quadratic, with both endpoint weights. -/
theorem map_matchingQuadratic (L : M →ₗ[K] M) (u v : J → M) (c d : K)
    (hu : ∀ i,L (u i)=c • u i) (hv : ∀ i,L (v i)=d • v i) :
    exteriorPower.map 2 L (matchingQuadratic u v)=(c*d) • matchingQuadratic u v := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map,matchingQuadratic_coe,Submodule.coe_smul,
    map_sum,map_mul,ExteriorAlgebra.map_apply_ι,hu,hv,map_smul,
    smul_mul_assoc,mul_smul_comm,smul_smul,Finset.smul_sum,mul_comm]

/-- The generated relation ideal is carried into itself whenever both
of its actual generators are eigenvectors. -/
theorem relationIdeal_map_mem (L : M →ₗ[K] M) (f g : ⋀[K]^2 M) (c d : K)
    (hf : exteriorPower.map 2 L f=c • f) (hg : exteriorPower.map 2 L g=d • g)
    (x : ExteriorAlgebra K M) (hx : x∈exteriorRelationIdeal f g) :
    ExteriorAlgebra.map L x∈exteriorRelationIdeal f g := by
  have hf' : ExteriorAlgebra.map L (f : ExteriorAlgebra K M)=c • (f : ExteriorAlgebra K M) := by
    simpa only [exteriorPower.coe_map,Submodule.coe_smul] using congrArg Subtype.val hf
  have hg' : ExteriorAlgebra.map L (g : ExteriorAlgebra K M)=d • (g : ExteriorAlgebra K M) := by
    simpa only [exteriorPower.coe_map,Submodule.coe_smul] using congrArg Subtype.val hg
  obtain ⟨a,b,rfl⟩ := Ideal.mem_span_pair.mp hx
  apply Ideal.mem_span_pair.mpr
  refine ⟨c • ExteriorAlgebra.map L a,d • ExteriorAlgebra.map L b,?_⟩
  simp only [map_add,map_mul,hf',hg',smul_mul_assoc,mul_smul_comm]

/-- The quotient action is justified on the complete homogeneous relation
space, including coefficients of every possible exterior degree. -/
theorem degreeRelations_map_le (L : M →ₗ[K] M) (f g : ⋀[K]^2 M) (c d : K)
    (hf : exteriorPower.map 2 L f=c • f) (hg : exteriorPower.map 2 L g=d • g)
    (s : ℕ) :
    exteriorDegreeRelations f g s≤
      (exteriorDegreeRelations f g s).comap (exteriorPower.map s L) := by
  intro x hx
  change ((exteriorPower.map s L x : ⋀[K]^s M) : ExteriorAlgebra K M)∈
    exteriorRelationIdeal f g
  rw [exteriorPower.coe_map]
  exact relationIdeal_map_mem L f g c d hf hg x hx

end Relations

section OddPath

variable {K : Type*} [Field K]

/-- Zero-based odd path positions are the `a`-variables. -/
def aIndexDegree {k : ℕ} (i : Fin (2*k+1)) : ℕ := if i.val%2=1 then 1 else 0

def aWordDegree {k s : ℕ} (a : Fin s → Fin (2*k+1)) : ℕ :=
  ∑ j,aIndexDegree (a j)

/-- The original vector-space action; in particular no quotient basis is
used to define this endomorphism. -/
def oddScaling (k : ℕ) (c : K) : (Fin (2*k+1) → K) →ₗ[K] (Fin (2*k+1) → K) :=
  basisScaling (Pi.basisFun K (Fin (2*k+1))) aIndexDegree c

@[simp] theorem aIndexDegree_firstLeft {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathFirstLeft i)=0 := by
  have h : (2*i.val)%2≠1 := by omega
  change (if (2*i.val)%2=1 then 1 else 0)=0
  exact if_neg h

@[simp] theorem aIndexDegree_middle {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathMiddle i)=1 := by
  have h : (2*i.val+1)%2=1 := by omega
  change (if (2*i.val+1)%2=1 then 1 else 0)=1
  exact if_pos h

@[simp] theorem aIndexDegree_secondRight {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathSecondRight i)=0 := by
  have h : (2*i.val+2)%2≠1 := by omega
  change (if (2*i.val+2)%2=1 then 1 else 0)=0
  exact if_neg h

@[simp] theorem oddScaling_first (k : ℕ) (c : K) :
    exteriorPower.map 2 (oddScaling k c)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))=
      c • oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) := by
  unfold oddPathFirstQuadratic
  simpa only [one_mul] using
    (map_matchingQuadratic (oddScaling k c)
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathFirstLeft i))
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathMiddle i)) 1 c
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_firstLeft,pow_zero,one_smul])
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_middle,pow_one]))

@[simp] theorem oddScaling_second (k : ℕ) (c : K) :
    exteriorPower.map 2 (oddScaling k c)
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))=
      c • oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) := by
  unfold oddPathSecondQuadratic
  simpa only [mul_one] using
    (map_matchingQuadratic (oddScaling k c)
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathMiddle i))
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathSecondRight i)) c 1
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_middle,pow_one])
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_secondRight,pow_zero,one_smul]))

/-- The induced endomorphism of the paper's actual homogeneous exterior
quotient.  Ideal preservation is a theorem used in the construction. -/
def quotientScaling (k s : ℕ) (c : K) :
    Module.End K (ExteriorQuotientDegree (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s) :=
  (exteriorDegreeRelations (K := K)
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s).mapQ
    (exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s)
    (exteriorPower.map s (oddScaling k c))
    (degreeRelations_map_le (oddScaling k c) _ _ c c
      (oddScaling_first k c) (oddScaling_second k c) s)

@[simp] theorem quotientScaling_word (k s : ℕ) (c : K)
    (a : Fin s → Fin (2*k+1)) :
    quotientScaling k s c (Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j))))=
      c ^ aWordDegree a • Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j))) := by
  rw [quotientScaling,Submodule.mapQ_apply]
  rw [show exteriorPower.map s (oddScaling k c)
      (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)))=
      c ^ aWordDegree a • exteriorPower.ιMulti K s
        (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)) from
    basisScaling_word _ _ _ _ _]
  exact Submodule.Quotient.mk_smul (R := K) (S := K)
    (p := exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s)
    (c ^ aWordDegree a)
    (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)))

/-- Distinct `a`-degrees have distinct eigenvalues in every characteristic-zero
coefficient field; no order on that field is required. -/
theorem two_pow_injective [CharZero K] : Function.Injective (fun p : ℕ => (2 : K)^p) := by
  intro p q h
  apply Nat.pow_right_injective (by decide : 2≤(2 : ℕ))
  apply (Nat.cast_injective (R := K))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

end OddPath
end PaperVerification.AlternatingForms.Bidegree
