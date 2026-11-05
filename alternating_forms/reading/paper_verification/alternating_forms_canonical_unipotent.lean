module

public import PaperVerification.NilpotentExponentialInvariant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The canonical odd pencil and its unique unipotent fixed plane

Coordinates are ordered along the chain
`b₀,b₁,...,bₖ,aₖ,aₖ₋₁,...,a₁`. In these coordinates the nilpotent operator of
Section 4.1 is a weighted lowering shift. Its coefficient at the single bridge
from `aₖ` to `bₖ` is one; every other coefficient is the coordinate index minus
`k`. This includes `k=0` without an exceptional definition.

The two forms below are actual bilinear forms and their mixed basis values
are precisely the two incidence pairings from the paper. The unique-fixed-plane
statement concerns actual subspaces, their dimensions, and the genuine finite
exponential linear action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open RegularNilpotentFlag NilpotentExponentialInvariant

variable {K : Type*} [Field K] [CharZero K]

abbrev ChainSpace (K : Type*) (k : ℕ) := Fin (2*k+1) → K

/-- Nonzero arrow coefficients in the paper's single Jordan chain. -/
def chainCoefficient (k : ℕ) (i : Fin (2*k+1)) : K :=
  if i.val=k then 1 else (i.val : K)-(k : K)

theorem chainCoefficient_ne_zero (k : ℕ) (i : Fin (2*k+1)) :
    chainCoefficient (K := K) k i ≠ 0 := by
  unfold chainCoefficient
  split_ifs with h
  · exact one_ne_zero
  · apply sub_ne_zero.mpr
    exact_mod_cast h

/-- The actual nilpotent endomorphism in chain coordinates. -/
def generator (k : ℕ) : Module.End K (ChainSpace K k) :=
  weightedShift (chainCoefficient k)

theorem generator_nilpotent (k : ℕ) : IsNilpotent (generator (K := K) k) :=
  weightedShift_nilpotent _

/-- The actual additive one-parameter family, using Mathlib's finite exponential. -/
def gaMap (k : ℕ) (u : K) : Module.End K (ChainSpace K k) :=
  IsNilpotent.exp (u • generator k)

@[simp] theorem gaMap_zero (k : ℕ) : gaMap (K := K) k 0 = 1 := by
  simp [gaMap]

theorem gaMap_add (k : ℕ) (u v : K) : gaMap k (u+v) = gaMap k u * gaMap k v :=
  exponential_add _ (generator_nilpotent k) u v

theorem gaMap_isUnit (k : ℕ) (u : K) : IsUnit (gaMap k u) :=
  IsNilpotent.isUnit_exp ((generator_nilpotent k).smul u)

/-- The actual span of the first `s` vectors of the Jordan chain. -/
abbrev fixedPlane (k s : ℕ) : Submodule K (ChainSpace K k) :=
  Pi.spanSubset K {i : Fin (2*k+1) | i.val < s}

theorem fixedPlane_finrank (k s : ℕ) (hs : s ≤ 2*k+1) :
    Module.finrank K (fixedPlane (K := K) k s) = s := finrank_prefix s hs

theorem fixedPlane_invariant (k s : ℕ) :
    ∀ u : K, (fixedPlane (K := K) k s).map (gaMap k u) = fixedPlane k s := by
  unfold gaMap
  apply (exponential_map_eq_iff (K:=K) (V:=ChainSpace K k)
    (generator k) (generator_nilpotent k) _).mpr
  apply exponential_invariant_of_invariant (K:=K) _ (generator_nilpotent k)
  exact weightedShift_prefix_invariant (chainCoefficient k) s

/-- The exponential subgroup fixes exactly one plane of each dimension. -/
theorem fixedPlane_unique (k s : ℕ) (hs : s ≤ 2*k+1)
    (U : Submodule K (ChainSpace K k)) (hdim : Module.finrank K U=s)
    (hfixed : ∀ u : K, U.map (gaMap k u)=U) : U=fixedPlane k s := by
  unfold gaMap at hfixed
  have hstable := (exponential_map_eq_iff (K:=K) (V:=ChainSpace K k)
    (generator k) (generator_nilpotent k) U).mp hfixed
  have hgen := invariant_of_exponential_invariant (K:=K)
    (generator k) (generator_nilpotent k) U hstable
  exact weightedShift_invariant_subspace_unique (chainCoefficient k)
    (fun i _ => chainCoefficient_ne_zero k i) s hs U hgen hdim

/-- A skew anti-diagonal matrix, with the orientation of `aᵢ∧bⱼ`. -/
def skewAntiDiagonal (k r : ℕ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) K :=
  fun i j => if i.val+j.val=r then
    (if i.val < j.val then -1 else if j.val < i.val then 1 else 0) else 0

theorem skewAntiDiagonal_swap (k r : ℕ) (i j : Fin (2*k+1)) :
    skewAntiDiagonal (K := K) k r i j = -skewAntiDiagonal k r j i := by
  unfold skewAntiDiagonal
  by_cases h : i.val+j.val=r
  · have h' : j.val+i.val=r := by omega
    simp only [if_pos h,if_pos h']
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · simp [hij,show ¬ j.val < i.val by omega]
    · simp [hij]
    · simp [hij,show ¬ i.val < j.val by omega]
  · have h' : ¬ j.val+i.val=r := by omega
    simp only [if_neg h,if_neg h',neg_zero]

theorem skewAntiDiagonal_isAlt (k r : ℕ) :
    ((skewAntiDiagonal (K := K) k r).toBilin').IsAlt := by
  apply LinearMap.isAlt_iff_eq_neg_flip.mpr
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro i
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro j
  simp only [Pi.basisFun_apply,LinearMap.neg_apply,LinearMap.flip_apply,
    Matrix.toBilin'_single]
  exact skewAntiDiagonal_swap k r i j

/-- The two canonical pairings in chain coordinates. -/
def firstForm (k : ℕ) : LinearMap.BilinForm K (ChainSpace K k) :=
  (skewAntiDiagonal k (2*k+1)).toBilin'

def secondForm (k : ℕ) : LinearMap.BilinForm K (ChainSpace K k) :=
  (skewAntiDiagonal k (2*k)).toBilin'

theorem firstForm_isAlt (k : ℕ) : (firstForm (K:=K) k).IsAlt :=
  skewAntiDiagonal_isAlt k (2*k+1)

theorem secondForm_isAlt (k : ℕ) : (secondForm (K:=K) k).IsAlt :=
  skewAntiDiagonal_isAlt k (2*k)

/-- Position of `aᵢ₊₁` in the chain basis. -/
def aIndex (k : ℕ) (i : Fin k) : Fin (2*k+1) := ⟨2*k-i.val,by omega⟩

/-- Position of `bⱼ` in the chain basis. -/
def bIndex (k : ℕ) (j : Fin (k+1)) : Fin (2*k+1) := ⟨j.val,by omega⟩

/-- This is exactly the first incidence pairing of Section 4. -/
theorem firstForm_a_b (k : ℕ) (i : Fin k) (j : Fin (k+1)) :
    firstForm (K := K) k (Pi.single (aIndex k i) 1) (Pi.single (bIndex k j) 1) =
      if j.val=i.val+1 then 1 else 0 := by
  rw [firstForm,Matrix.toBilin'_single]
  change (if 2*k-i.val+j.val=2*k+1 then
    (if 2*k-i.val < j.val then -1 else if j.val < 2*k-i.val then 1 else 0) else 0) = _
  have hi := i.isLt
  have hj := j.isLt
  have hlt : j.val < 2*k-i.val := by omega
  have he : (2*k-i.val+j.val=2*k+1) ↔ j.val=i.val+1 := by omega
  simp only [not_lt_of_gt hlt,if_false,if_pos hlt,he]

/-- This is exactly the second incidence pairing of Section 4. -/
theorem secondForm_a_b (k : ℕ) (i : Fin k) (j : Fin (k+1)) :
    secondForm (K := K) k (Pi.single (aIndex k i) 1) (Pi.single (bIndex k j) 1) =
      if j.val=i.val then 1 else 0 := by
  rw [secondForm,Matrix.toBilin'_single]
  change (if 2*k-i.val+j.val=2*k then
    (if 2*k-i.val < j.val then -1 else if j.val < 2*k-i.val then 1 else 0) else 0) = _
  have hi := i.isLt
  have hj := j.isLt
  have hlt : j.val < 2*k-i.val := by omega
  have he : (2*k-i.val+j.val=2*k) ↔ j.val=i.val := by omega
  simp only [not_lt_of_gt hlt,if_false,if_pos hlt,he]

theorem skewAntiDiagonal_low_zero (k r : ℕ) (hr : r=2*k ∨ r=2*k+1)
    (i j : Fin (2*k+1)) (hi : i.val ≤ k) (hj : j.val ≤ k) :
    skewAntiDiagonal (K := K) k r i j = 0 := by
  unfold skewAntiDiagonal
  rcases hr with rfl|rfl <;> split_ifs <;> (first | rfl | omega)

/-- Common isotropy refers to the actual two bilinear forms. -/
def IsCommonIsotropic (k : ℕ) (U : Submodule K (ChainSpace K k)) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, firstForm k u v=0 ∧ secondForm k u v=0

/-- The unique invariant plane lies in the common isotropic locus throughout
exactly the range used in Section 4. -/
theorem fixedPlane_common_isotropic (k s : ℕ) (hs : s ≤ k+1) :
    IsCommonIsotropic k (fixedPlane (K := K) k s) := by
  intro u hu v hv
  rw [Pi.mem_spanSubset_iff] at hu hv
  have hform (r : ℕ) (hr : r=2*k ∨ r=2*k+1) :
      (skewAntiDiagonal (K := K) k r).toBilin' u v=0 := by
    rw [Matrix.toBilin'_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hi : i.val < s
    · by_cases hj : j.val < s
      · rw [skewAntiDiagonal_low_zero k r hr i j (by omega) (by omega)]
        simp
      · rw [hv j hj,mul_zero]
    · rw [hu i hi,zero_mul,zero_mul]
  exact ⟨hform _ (Or.inr rfl),hform _ (Or.inl rfl)⟩

/-- The canonical common isotropic locus has a unique unipotent-fixed `s`-plane.
This is a statement about all actual subspaces, not a selected coordinate list. -/
theorem existsUnique_fixed_common_isotropic_plane (k s : ℕ) (hs : s ≤ k+1) :
    ∃! U : Submodule K (ChainSpace K k),
      Module.finrank K U=s ∧ IsCommonIsotropic k U ∧
        ∀ u : K, U.map (gaMap k u)=U := by
  refine ⟨fixedPlane k s,⟨fixedPlane_finrank k s (by omega),
    fixedPlane_common_isotropic k s hs,fixedPlane_invariant k s⟩,?_⟩
  intro U hU
  exact fixedPlane_unique k s (by omega) U hU.1 hU.2.2

end PaperVerification.AlternatingForms.CanonicalUnipotent
