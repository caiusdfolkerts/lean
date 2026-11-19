module

public import PaperVerification.FermionSl2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NoncommRing

/-!
# Creation, annihilation, and the exterior number operator

These are the literal exterior-algebra operations used in Section 3. This file
connects their algebraic identities with the homogeneous exterior grading.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion
namespace Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

local notation "E" => ExteriorAlgebra R V

/-- Left exterior multiplication, viewed linearly as a function of its vector. -/
def creation : V →ₗ[R] Module.End R E :=
  (LinearMap.mul R E).comp (ExteriorAlgebra.ι R)

@[simp] theorem creation_apply (v : V) (w : E) :
    creation v w = ExteriorAlgebra.ι R v * w := rfl

/-- Left contraction by a linear functional. -/
def annihilation (l : Module.Dual R V) : Module.End R E :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) l

@[simp] theorem annihilation_one (l : Module.Dual R V) :
    annihilation l (1 : E) = 0 := CliffordAlgebra.contractLeft_one (0 : QuadraticForm R V) l

@[simp] theorem annihilation_algebraMap (l : Module.Dual R V) (r : R) :
    annihilation l (algebraMap R E r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap (0 : QuadraticForm R V) l r

/-- The creation-annihilation anticommutation relation, with its actual evaluation scalar. -/
theorem annihilation_creation (l : Module.Dual R V) (v : V) :
    annihilation l * creation v + creation v * annihilation l = (l v) • 1 := by
  apply LinearMap.ext
  intro w
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, creation_apply, annihilation]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp

theorem creation_anticomm (v w : V) :
    creation (R := R) v * creation w + creation w * creation v = 0 := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply, creation_apply]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem creation_anticomm_eq (v w : V) :
    creation (R := R) v * creation w = -(creation w * creation v) :=
  eq_neg_of_add_eq_zero_left (creation_anticomm v w)

theorem annihilation_anticomm_eq (l m : Module.Dual R V) :
    annihilation l * annihilation m = -(annihilation m * annihilation l) := by
  apply LinearMap.ext
  intro w
  simpa only [annihilation, Module.End.mul_apply, LinearMap.neg_apply] using
    CliffordAlgebra.contractLeft_comm l m w

theorem annihilation_square (l : Module.Dual R V) :
    annihilation l * annihilation l = 0 := by
  apply LinearMap.ext
  intro w
  exact CliffordAlgebra.contractLeft_contractLeft l w

theorem creation_square (v : V) : creation (R := R) v * creation v = 0 := by
  apply LinearMap.ext
  intro w
  simp only [Module.End.mul_apply, LinearMap.zero_apply, creation_apply]
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R V)

/-- The sum of the coordinate occupation operators. -/
noncomputable def number : Module.End R E :=
  ∑ i, creation (b i) * annihilation (b.coord i)

@[simp] theorem number_algebraMap (r : R) : number b (algebraMap R E r) = 0 := by
  simp [number, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_coord_creation (v : V) :
    (∑ i, (b.coord i v) • creation (R := R) (b i)) = creation v := by
  simp only [Module.Basis.coord_apply, ← map_smul, ← map_sum, b.sum_repr]

/-- Each creation increases the number operator by one. -/
theorem number_creation (v : V) :
    number b * creation v = creation v + creation v * number b := by
  have hterm (i : ι) :
      (creation (b i) * annihilation (b.coord i)) * creation v =
        (b.coord i v) • creation (b i) +
          creation v * (creation (b i) * annihilation (b.coord i)) := by
    have hcar : annihilation (b.coord i) * creation v =
        (b.coord i v) • 1 - creation v * annihilation (b.coord i) :=
      eq_sub_of_add_eq (annihilation_creation (b.coord i) v)
    rw [mul_assoc, hcar, mul_sub, mul_smul_comm, mul_one,
      ← mul_assoc, creation_anticomm_eq]
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.add_apply, LinearMap.smul_apply, sub_neg_eq_add]
  calc
    number b * creation v = ∑ i, (creation (b i) * annihilation (b.coord i)) * creation v := by
      rw [number, Finset.sum_mul]
    _ = ∑ i, ((b.coord i v) • creation (b i) +
        creation v * (creation (b i) * annihilation (b.coord i))) :=
      Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = creation v + creation v * number b := by
      rw [Finset.sum_add_distrib, sum_coord_creation, ← Finset.mul_sum, number]

theorem number_creation_apply (v : V) (w : E) :
    number b (ExteriorAlgebra.ι R v * w) =
      ExteriorAlgebra.ι R v * w + ExteriorAlgebra.ι R v * number b w := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply, creation_apply] using
    congrArg (fun a : Module.End R E ↦ a w) (number_creation b v)

theorem sum_dual_annihilation (l : Module.Dual R V) :
    (∑ i, l (b i) • annihilation (b.coord i)) = annihilation l := by
  unfold annihilation
  simp_rw [← map_smul]
  rw [← map_sum, b.sum_dual_apply_smul_coord]

/-- Each contraction decreases the number operator by one. -/
theorem number_annihilation (l : Module.Dual R V) :
    number b * annihilation l = annihilation l * number b - annihilation l := by
  have hterm (i : ι) :
      (creation (b i) * annihilation (b.coord i)) * annihilation l =
        annihilation l * (creation (b i) * annihilation (b.coord i)) -
          l (b i) • annihilation (b.coord i) := by
    have hcar : creation (b i) * annihilation l =
        l (b i) • 1 - annihilation l * creation (b i) :=
      eq_sub_of_add_eq (by simpa only [add_comm] using annihilation_creation l (b i))
    calc
      _ = creation (b i) * (annihilation (b.coord i) * annihilation l) := by rw [mul_assoc]
      _ = creation (b i) * (-(annihilation l * annihilation (b.coord i))) := by
        rw [annihilation_anticomm_eq]
      _ = -((creation (b i) * annihilation l) * annihilation (b.coord i)) := by
        apply LinearMap.ext
        intro w
        simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      _ = -((l (b i) • 1 - annihilation l * creation (b i)) * annihilation (b.coord i)) := by
        rw [hcar]
      _ = _ := by rw [sub_mul, smul_mul_assoc, one_mul, neg_sub, mul_assoc]
  calc
    number b * annihilation l =
        ∑ i, (creation (b i) * annihilation (b.coord i)) * annihilation l := by
      rw [number, Finset.sum_mul]
    _ = ∑ i, (annihilation l * (creation (b i) * annihilation (b.coord i)) -
        l (b i) • annihilation (b.coord i)) := Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_dual_annihilation, number]

/-- The occupation-number operator has eigenvalue `k` on the actual `k`th exterior power. -/
theorem number_homogeneous (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V) :
    number b w = (k : R) • w := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y k hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | mem_mul v hv k w hw ih =>
    obtain ⟨v, rfl⟩ := hv
    rw [number_creation_apply, ih, mul_smul_comm]
    simp only [Nat.cast_succ, add_smul, one_smul]
    exact add_comm _ _

include b in
/-- Exterior degrees larger than the number of basis vectors vanish over any coefficient ring. -/
theorem homogeneous_eq_zero_of_card_lt
    (k : ℕ) (hk : Fintype.card ι < k) (w : E) (hw : w ∈ ⋀[R]^k V) : w = 0 := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : IsEmpty (Set.powersetCard ι k) := ⟨fun s ↦ by
    have hcard := Finset.card_le_univ s.val
    have hs : s.val.card = k := s.prop
    omega⟩
  have hz : (⟨w, hw⟩ : ⋀[R]^k V) = 0 := by
    apply (b.exteriorPower k).repr.injective
    ext s
    exact isEmptyElim s
  exact congrArg Subtype.val hz

end Exterior

section OperatorIdentities

variable {A : Type*} [Ring A]

/-- The two-mode commutator, proved from four elementary anticommutation identities. -/
theorem pair_operator_commutator (a b c d : A)
    (hac : a * c + c * a = 1) (hbd : b * d + d * b = 1)
    (had : a * d + d * a = 0) (hbc : b * c + c * b = 0) :
    (b * a) * (c * d) = (c * d) * (b * a) + (1 - c * a - d * b) := by
  have hac' : a * c = 1 - c * a := eq_sub_of_add_eq hac
  have hbd' : b * d = 1 - d * b := eq_sub_of_add_eq hbd
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  have hbc' : b * c = -(c * b) := eq_neg_of_add_eq_zero_left hbc
  calc
    (b * a) * (c * d) = b * (a * c) * d := by noncomm_ring
    _ = b * (1 - c * a) * d := by rw [hac']
    _ = b * d - (b * c) * (a * d) := by noncomm_ring
    _ = (1 - d * b) - (-(c * b)) * (-(d * a)) := by rw [hbd', hbc', had']
    _ = 1 - d * b - c * (b * d) * a := by noncomm_ring
    _ = 1 - d * b - c * (1 - d * b) * a := by rw [hbd']
    _ = (c * d) * (b * a) + (1 - c * a - d * b) := by noncomm_ring

/-- Quadratic even operators on disjoint modes commute. -/
theorem disjoint_pair_operators_commute (a b c d : A)
    (hac : a * c + c * a = 0) (hbd : b * d + d * b = 0)
    (had : a * d + d * a = 0) (hbc : b * c + c * b = 0) :
    (b * a) * (c * d) = (c * d) * (b * a) := by
  have hac' : a * c = -(c * a) := eq_neg_of_add_eq_zero_left hac
  have hbd' : b * d = -(d * b) := eq_neg_of_add_eq_zero_left hbd
  have had' : a * d = -(d * a) := eq_neg_of_add_eq_zero_left had
  have hbc' : b * c = -(c * b) := eq_neg_of_add_eq_zero_left hbc
  calc
    (b * a) * (c * d) = b * (a * c) * d := by noncomm_ring
    _ = b * (-(c * a)) * d := by rw [hac']
    _ = -(b * c) * (a * d) := by noncomm_ring
    _ = (-(-(c * b))) * (-(d * a)) := by rw [hbc', had']
    _ = -c * (b * d) * a := by noncomm_ring
    _ = -c * (-(d * b)) * a := by rw [hbd']
    _ = (c * d) * (b * a) := by noncomm_ring

end OperatorIdentities

namespace Exterior

open scoped BigOperators

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [Fintype ι] [DecidableEq ι]

local notation "E" => ExteriorAlgebra R V

/- An ordered pairing of the `2d` exterior modes. -/
variable (b : Module.Basis (ι ⊕ ι) R V)

def pairLower (i : ι) : Module.End R E :=
  annihilation (b.coord (.inr i)) * annihilation (b.coord (.inl i))

def pairRaise (i : ι) : Module.End R E :=
  creation (b (.inl i)) * creation (b (.inr i))

/-- Contraction by the standard symplectic form. -/
def lowering : Module.End R E := ∑ i, pairLower b i

/-- Exterior multiplication by the sum of the paired two-forms. -/
def raising : Module.End R E := ∑ i, pairRaise b i

def weight : Module.End R E := (Fintype.card ι : R) • 1 - number b

theorem pair_commutator (i j : ι) :
    pairLower b i * pairRaise b j - pairRaise b j * pairLower b i =
      if i = j then
        1 - creation (b (.inl i)) * annihilation (b.coord (.inl i)) -
          creation (b (.inr i)) * annihilation (b.coord (.inr i))
      else 0 := by
  have hself (a : ι ⊕ ι) :
      annihilation (b.coord a) * creation (b a) +
        creation (b a) * annihilation (b.coord a) = (1 : Module.End R E) := by
    rw [annihilation_creation, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, one_smul]
  have hne (a c : ι ⊕ ι) (hac : a ≠ c) :
      annihilation (b.coord a) * creation (b c) +
        creation (b c) * annihilation (b.coord a) = (0 : Module.End R E) := by
    rw [annihilation_creation, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hac, zero_smul]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, sub_eq_iff_eq_add']
    unfold pairLower pairRaise
    exact pair_operator_commutator (A := Module.End R E)
      (annihilation (b.coord (.inl i))) (annihilation (b.coord (.inr i)))
      (creation (b (.inl i))) (creation (b (.inr i)))
      (hself (.inl i)) (hself (.inr i))
      (hne (.inl i) (.inr i) Sum.inl_ne_inr)
      (hne (.inr i) (.inl i) Sum.inr_ne_inl)
  · rw [if_neg hij, sub_eq_zero]
    unfold pairLower pairRaise
    exact disjoint_pair_operators_commute (A := Module.End R E)
      (annihilation (b.coord (.inl i))) (annihilation (b.coord (.inr i)))
      (creation (b (.inl j))) (creation (b (.inr j)))
      (hne (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h)))
      (hne (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h)))
      (hne (.inl i) (.inr j) Sum.inl_ne_inr)
      (hne (.inr i) (.inl j) Sum.inr_ne_inl)

theorem lower_raise : lowering b * raising b = raising b * lowering b + weight b := by
  apply sub_eq_iff_eq_add'.mp
  calc
    lowering b * raising b - raising b * lowering b =
        ∑ i, ∑ j, (pairLower b i * pairRaise b j - pairRaise b j * pairLower b i) := by
      simp only [lowering, raising, Finset.sum_sub_distrib]
      rw [← Fintype.sum_mul_sum, Finset.sum_comm, ← Fintype.sum_mul_sum]
    _ = ∑ i, (1 - creation (b (.inl i)) * annihilation (b.coord (.inl i)) -
        creation (b (.inr i)) * annihilation (b.coord (.inr i))) := by
      simp_rw [pair_commutator]
      simp
    _ = weight b := by
      simp only [weight, number, Fintype.sum_sum_type, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      abel

theorem number_pairRaise (i : ι) :
    number b * pairRaise b i = (2 : R) • pairRaise b i + pairRaise b i * number b := by
  unfold pairRaise
  rw [← mul_assoc, number_creation, add_mul, mul_assoc, number_creation, mul_add]
  simp only [← mul_assoc]
  simp only [two_smul]
  abel

theorem number_raising :
    number b * raising b = (2 : R) • raising b + raising b * number b := by
  simp only [raising, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    number_pairRaise, Finset.sum_add_distrib]

theorem weight_raise :
    weight b * raising b = raising b * weight b - (2 : R) • raising b := by
  simp only [weight, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [number_raising]
  abel

theorem number_pairLower (i : ι) :
    number b * pairLower b i = pairLower b i * number b - (2 : R) • pairLower b i := by
  unfold pairLower
  rw [← mul_assoc, number_annihilation, sub_mul, mul_assoc, number_annihilation, mul_sub]
  simp only [← mul_assoc, two_smul]
  abel

theorem number_lowering :
    number b * lowering b = lowering b * number b - (2 : R) • lowering b := by
  simp only [lowering, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    number_pairLower, Finset.sum_sub_distrib]

theorem weight_lower :
    weight b * lowering b = lowering b * weight b + (2 : R) • lowering b := by
  simp only [weight, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [number_lowering]
  abel

theorem raisingLowering : RaisingLowering (lowering b) (raising b) (weight b) :=
  ⟨lower_raise b, weight_raise b⟩

/-- The reversed orientation, useful for wedge injectivity below middle degree. -/
theorem loweringRaising : RaisingLowering (raising b) (lowering b) (-weight b) := by
  constructor
  · rw [← sub_eq_add_neg]
    exact eq_sub_of_add_eq (lower_raise b).symm
  · calc
      -weight b * lowering b = -(weight b * lowering b) := by
        apply LinearMap.ext
        intro w
        rfl
      _ = -(lowering b * weight b + (2 : R) • lowering b) :=
        congrArg Neg.neg (weight_lower b)
      _ = lowering b * -weight b - (2 : R) • lowering b := by
        apply LinearMap.ext
        intro w
        simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.smul_apply, map_neg]
        abel

theorem weight_homogeneous (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V) :
    weight b w = ((Fintype.card ι : R) - (k : R)) • w := by
  simp only [weight, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    number_homogeneous b k w hw, sub_smul]

theorem creation_mem_succ (v : V) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    creation v w ∈ ⋀[R]^(k + 1) V := by
  change ExteriorAlgebra.ι R v * w ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ (k + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) hw

theorem raising_mem_add_two {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    raising b w ∈ ⋀[R]^(k + 2) V := by
  rw [raising, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  exact creation_mem_succ _ (creation_mem_succ _ hw)

theorem raising_pow_mem {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) (j : ℕ) :
    (raising b ^ j) w ∈ ⋀[R]^(k + 2 * j) V := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert raising_mem_add_two b ih using 1 <;> congr 1 <;> omega

/-- The primitive bound of Lemma 3.1 for the literal exterior-algebra operators.

It holds over every commutative coefficient ring in which `d!` is a unit,
and uses the exterior grading, not a postulated nilpotence condition.
-/
theorem primitive_degree_bound
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hdegree : Fintype.card ι < k) : w = 0 := by
  apply primitive_eq_zero_of_degree_gt (lowering b) (raising b) (weight b)
    (raisingLowering b) (Fintype.card ι) k hfac hdegree w he (weight_homogeneous b k w hw)
  intro j hj
  apply homogeneous_eq_zero_of_card_lt b (k + 2 * j) _ _ (raising_pow_mem b hw j)
  simpa only [Fintype.card_sum, two_mul] using hj

/-- The precise Lefschetz truncation needed in the polynomial part of Lemma 3.1.
It is deduced from the actual exterior grading and the checked commutators. -/
theorem primitive_raising_pow_eq_zero
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hk : k ≤ Fintype.card ι) :
    (raising b ^ (Fintype.card ι - k + 1)) w = 0 := by
  let c := Fintype.card ι - k
  have hcast : (Fintype.card ι : R) - (k : R) = (c : R) := (Nat.cast_sub hk).symm
  have hh : weight b w = (c : R) • w := by
    rw [weight_homogeneous b k w hw, hcast]
  have hprimitive : lowering b ((raising b ^ (c + 1)) w) = 0 := by
    have h := (raisingLowering b).lower_pow_apply (c : R) w he hh c
    simpa only [sub_self, mul_zero, zero_smul] using h
  apply primitive_degree_bound b hfac (k + 2 * (c + 1)) _
    (raising_pow_mem b hw (c + 1)) hprimitive
  dsimp [c]
  omega

/-- Every stage through degree `d-k` of a nonzero primitive string is nonzero. -/
theorem primitive_raising_pow_ne_zero
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    (k : ℕ) (w : E) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hk : k ≤ Fintype.card ι) (hne : w ≠ 0)
    (j : ℕ) (hj : j ≤ Fintype.card ι - k) : (raising b ^ j) w ≠ 0 := by
  apply mt (primitive_raising_power_eq_zero_iff (lowering b) (raising b) (weight b)
    (raisingLowering b) (Fintype.card ι) (Fintype.card ι - k) hfac (Nat.sub_le _ _)
    w he (by rw [weight_homogeneous b k w hw, Nat.cast_sub hk]) j hj).mp hne

end Exterior

end PaperVerification.Fermion
