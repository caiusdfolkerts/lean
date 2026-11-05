module

public import PaperVerification.VectorEulerBasic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The actual integer target grading and its exceptional Hilbert function

The basis vector in coordinate `a` has degree `-h a`. Thus a target vector
of degree `e : ℤ` has its `a`-th polynomial coordinate in degree `e+h a`.
Negative target degrees are retained. Weighted Euler induces an endomorphism
of the actual hit quotient; its distinct integer eigenvalues prove separation
of the homogeneous quotient pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.VectorEuler

variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P

def integerWeights (w : ι → ℕ) : ι → ℤ := fun i => (w i : ℤ)

theorem weight_integerWeights (w : ι → ℕ) (a : ι →₀ ℕ) :
    Finsupp.weight (integerWeights w) a = (Finsupp.weight w a : ℤ) := by
  simp only [Finsupp.weight_eq_sum, integerWeights, nsmul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_id]

theorem homogeneous_nat_iff_integer (w : ι → ℕ) (p : P) (d : ℕ) :
    p.IsWeightedHomogeneous w d ↔
      p.IsWeightedHomogeneous (integerWeights w) (d : ℤ) := by
  constructor
  · intro hp a ha
    rw [weight_integerWeights, hp ha]
  · intro hp a ha
    exact Nat.cast_injective ((weight_integerWeights w a).symm.trans (hp ha))

theorem integer_homogeneous_nonneg (w : ι → ℕ) (p : P) (e : ℤ)
    (hp : p.IsWeightedHomogeneous (integerWeights w) e) (hne : p ≠ 0) : 0 ≤ e := by
  obtain ⟨a, ha⟩ := MvPolynomial.exists_coeff_ne_zero hne
  rw [← hp ha, weight_integerWeights]
  exact Int.natCast_nonneg _

theorem integer_piece_eq (w : ι → ℕ) (e : ℤ) :
    weightedHomogeneousSubmodule K (integerWeights w) e =
      if 0 ≤ e then weightedHomogeneousSubmodule K w e.toNat else ⊥ := by
  split_ifs with he
  · ext p
    change p.IsWeightedHomogeneous (integerWeights w) e ↔
      p.IsWeightedHomogeneous w e.toNat
    rw [homogeneous_nat_iff_integer, Int.toNat_of_nonneg he]
  · apply eq_bot_iff.mpr
    intro p hp
    by_contra hp0
    exact he (integer_homogeneous_nonneg w p e hp hp0)

theorem weightedEuler_integer_homogeneous (w : ι → ℕ) (p : P) (e : ℤ)
    (hp : p.IsWeightedHomogeneous (integerWeights w) e) :
    JacobianDivergence.weightedEuler w p = (e : K) • p := by
  by_cases hzero : p = 0
  · simp only [hzero, map_zero, smul_zero]
  · have he := integer_homogeneous_nonneg w p e hp hzero
    have hp' : p.IsWeightedHomogeneous w e.toNat := by
      apply (homogeneous_nat_iff_integer w p e.toNat).mpr
      simpa only [Int.toNat_of_nonneg he] using hp
    rw [JacobianDivergence.weightedEuler_homogeneous w p e.toNat hp']
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg he]

/-- This is the paper's literal target grading, including negative degrees. -/
def targetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) : Submodule K M :=
  Submodule.pi Set.univ fun a =>
    weightedHomogeneousSubmodule K (integerWeights w) (e + (h a : ℤ))

@[simp] theorem mem_targetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (v : M) :
    v ∈ targetPiece (K := K) w h e ↔
      ∀ a, (v a).IsWeightedHomogeneous (integerWeights w) (e + (h a : ℤ)) := by
  simp only [targetPiece, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  rfl

def targetEuler (w : ι → ℕ) (h : κ → ℕ) : M →ₗ[K] M where
  toFun v a := JacobianDivergence.weightedEuler w (v a) - (h a : K) • v a
  map_add' v u := by
    funext a
    simp only [Pi.add_apply, map_add, smul_add]
    abel
  map_smul' c v := by
    funext a
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_comm c]

theorem targetEuler_of_mem_piece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (v : M)
    (hv : v ∈ targetPiece (K := K) w h e) : targetEuler w h v = (e : K) • v := by
  funext a
  change JacobianDivergence.weightedEuler w (v a) - (h a : K) • v a = (e : K) • v a
  rw [weightedEuler_integer_homogeneous w (v a) _ ((mem_targetPiece w h e v).mp hv a)]
  simp only [Int.cast_add, Int.cast_natCast, add_smul, add_sub_cancel_right]

/-- The genuine coordinatewise projection for the shifted target grading. -/
def targetComponent (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) : M →ₗ[K] M :=
  LinearMap.pi fun a =>
    (weightedHomogeneousComponent (integerWeights w) (e + (h a : ℤ))).comp (LinearMap.proj a)

theorem targetComponent_mem_piece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (v : M) :
    targetComponent w h e v ∈ targetPiece (K := K) w h e := by
  rw [mem_targetPiece]
  intro a
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem targetComponent_of_mem (w : ι → ℕ) (h : κ → ℕ) (e f : ℤ) (v : M)
    (hv : v ∈ targetPiece (K := K) w h f) :
    targetComponent w h e v = if e = f then v else 0 := by
  funext a
  change weightedHomogeneousComponent (integerWeights w) (e + (h a : ℤ)) (v a) = _
  rw [weightedHomogeneousComponent_of_mem ((mem_targetPiece w h f v).mp hv a)]
  by_cases hef : e = f
  · simp only [hef, if_true]
  · simp only [add_left_inj, if_neg hef, Pi.zero_apply]

theorem targetComponent_finite_support [Fintype κ]
    (w : ι → ℕ) (h : κ → ℕ) (v : M) :
    (fun e : ℤ => targetComponent w h e v).HasFiniteSupport := by
  have ha (a : κ) :
      (fun e : ℤ => weightedHomogeneousComponent (integerWeights w)
        (e + (h a : ℤ)) (v a)).HasFiniteSupport :=
    Function.HasFiniteSupport.fun_comp_of_injective
      (f := fun j : ℤ => weightedHomogeneousComponent (integerWeights w) j (v a))
      (g := fun e : ℤ => e + (h a : ℤ))
      (fun x y hxy => add_right_cancel hxy)
      (weightedHomogeneousComponent_finsupp (w := integerWeights w) (v a))
  apply (Set.finite_iUnion ha).subset
  intro e he
  by_contra hnone
  apply he
  funext a
  change weightedHomogeneousComponent (integerWeights w) (e + (h a : ℤ)) (v a) = 0
  by_contra hz
  exact hnone (Set.mem_iUnion.mpr ⟨a, hz⟩)

/-- Every target vector is the finite sum of its actual shifted components. -/
theorem sum_targetComponent [Fintype κ]
    (w : ι → ℕ) (h : κ → ℕ) (v : M) :
    (∑ᶠ e : ℤ, targetComponent w h e v) = v := by
  funext a
  rw [finsum_apply (targetComponent_finite_support w h v)]
  change (∑ᶠ e : ℤ, weightedHomogeneousComponent (integerWeights w)
    (e + (h a : ℤ)) (v a)) = v a
  rw [finsum_comp (g := fun j : ℤ => weightedHomogeneousComponent (integerWeights w) j (v a))
    (fun e : ℤ => e + (h a : ℤ))
    ⟨fun x y hxy => add_right_cancel hxy, fun j => ⟨j - h a, sub_add_cancel _ _⟩⟩]
  exact sum_weightedHomogeneousComponent (integerWeights w) (v a)

/-- Stability under the actual shifted Euler operator implies stability
under every actual homogeneous projection. The argument uses the entire finite
component expansion and distinct integer eigenvalues, not pairwise disjointness. -/
theorem targetComponent_mem_of_eulerStable [Fintype κ]
    (w : ι → ℕ) (h : κ → ℕ) (U : Submodule K M)
    (hU : ∀ v ∈ U, targetEuler w h v ∈ U) (v : M) (hv : v ∈ U) (e : ℤ) :
    targetComponent w h e v ∈ U := by
  classical
  let f : ℤ → M := fun j => targetComponent w h j v
  have hf := targetComponent_finite_support w h v
  let s : Finset ℤ := hf.toFinset
  have hsum : ∑ j ∈ s, f j = v := by
    rw [← sum_targetComponent w h v, finsum_eq_sum _ hf]
  have heig (j : ℤ) : targetEuler w h (f j) = (j : K) • f j :=
    targetEuler_of_mem_piece w h j _ (targetComponent_mem_piece w h j v)
  by_cases he : e ∈ s
  · exact Eigencomponents.mem_of_sum_mem (targetEuler w h) U hU
      (fun j : ℤ => (j : K)) Int.cast_injective s f (fun j _ => heig j)
      (hsum.symm ▸ hv) e he
  · have hz : f e = 0 := by
      apply Function.notMem_support.mp
      intro hm
      exact he (hf.mem_toFinset.mpr hm)
    change f e ∈ U
    rw [hz]
    exact U.zero_mem

theorem targetEuler_coefficient (F : κ → P) (h : κ → ℕ) (w : ι → ℕ)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (g : ι → P) :
    targetEuler w h (VectorJacobian.normalizedJacobianMap F h g) =
      VectorJacobian.normalizedJacobianMap F h (JacobianDivergence.eulerShift w g) := by
  funext a
  have hc (g' : ι → P) : VectorJacobian.jacobianMap F g' a =
      KoszulSyzygies.coefficient (JacobianDivergence.gradient (F a)) g' := by
    simp only [VectorJacobian.jacobianMap_apply, KoszulSyzygies.coefficient_apply,
      JacobianDivergence.gradient, mul_comm]
  change JacobianDivergence.weightedEuler w
      ((h a : K)⁻¹ • VectorJacobian.jacobianMap F g a) -
        (h a : K) • ((h a : K)⁻¹ • VectorJacobian.jacobianMap F g a) =
      (h a : K)⁻¹ • VectorJacobian.jacobianMap F (JacobianDivergence.eulerShift w g) a
  simp only [map_smul, hc]
  rw [JacobianDivergence.coefficient_eulerShift (F a) w (h a) (hF a)]
  simp only [smul_sub, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_comm]

theorem targetEuler_potential (F : κ → P) (h : κ → ℕ) (w : ι → ℕ)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (p : P) :
    targetEuler w h (potential F p) = potential F (JacobianDivergence.weightedEuler w p) := by
  funext a
  change JacobianDivergence.weightedEuler w (F a * p) - (h a : K) • (F a * p) = _
  rw [JacobianDivergence.weightedEuler_mul,
    JacobianDivergence.weightedEuler_homogeneous w (F a) (h a) (hF a), smul_mul_assoc]
  exact add_sub_cancel_left _ _

theorem targetEuler_aggregate (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (g : ι → P) :
    targetEuler w h (aggregate F h t g) =
      aggregate F h t (JacobianDivergence.eulerShift w g) := by
  simp only [aggregate, EulerReduction.perturbed_apply, map_add, map_smul,
    targetEuler_coefficient F h w hF, targetEuler_potential F h w hF,
    JacobianDivergence.divergence_eulerShift]

theorem targetEuler_mem_hit (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (v : M) (hv : v ∈ hit F h t) :
    targetEuler w h v ∈ hit F h t := by
  obtain ⟨g, rfl⟩ := hv
  exact ⟨JacobianDivergence.eulerShift w g, (targetEuler_aggregate F h w t hF g).symm⟩

/-- The actual hit subspace is homogeneous for the full shifted grading. -/
theorem targetComponent_mem_hit [Fintype κ]
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (v : M) (hv : v ∈ hit F h t) (e : ℤ) :
    targetComponent w h e v ∈ hit F h t :=
  targetComponent_mem_of_eulerStable w h (hit F h t)
    (targetEuler_mem_hit F h w t hF) v hv e

/-- The coefficient subspace is homogeneous for the same actual grading. -/
theorem targetComponent_mem_coefficient [Fintype κ]
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (v : M) (hv : v ∈ coefficientSpace F h) (e : ℤ) :
    targetComponent w h e v ∈ coefficientSpace F h := by
  apply targetComponent_mem_of_eulerStable w h (coefficientSpace F h) _ v hv e
  rintro u ⟨g, rfl⟩
  exact ⟨JacobianDivergence.eulerShift w g, (targetEuler_coefficient F h w hF g).symm⟩

def quotientTargetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (U : Submodule K M) :
    Submodule K (M ⧸ U) := (targetPiece w h e).map U.mkQ

def quotientTargetComponent (w : ι → ℕ) (h : κ → ℕ) (U : Submodule K M)
    (hU : ∀ e v, v ∈ U → targetComponent w h e v ∈ U) (e : ℤ) :
    (M ⧸ U) →ₗ[K] (M ⧸ U) :=
  U.mapQ U (targetComponent w h e) (fun v hv => hU e v hv)

theorem quotientTargetComponent_of_mem (w : ι → ℕ) (h : κ → ℕ) (U : Submodule K M)
    (hU : ∀ e v, v ∈ U → targetComponent w h e v ∈ U)
    (e f : ℤ) (x : M ⧸ U) (hx : x ∈ quotientTargetPiece w h f U) :
    quotientTargetComponent w h U hU e x = if e = f then x else 0 := by
  obtain ⟨v, hv, rfl⟩ := hx
  change U.mkQ (targetComponent w h e v) = _
  rw [targetComponent_of_mem w h e f v hv]
  split_ifs <;> simp only [map_zero]

/-- Full independence of every finite family of quotient components. This
is stronger than pairwise disjointness and supplies uniqueness of grading. -/
theorem quotientTargetPieces_finite_independent
    (w : ι → ℕ) (h : κ → ℕ) (U : Submodule K M)
    (hU : ∀ e v, v ∈ U → targetComponent w h e v ∈ U)
    (s : Finset ℤ) (v : ℤ → M ⧸ U)
    (hv : ∀ e ∈ s, v e ∈ quotientTargetPiece w h e U)
    (hs : ∑ e ∈ s, v e = 0) : ∀ e ∈ s, v e = 0 := by
  classical
  intro e he
  have hp := congrArg (quotientTargetComponent w h U hU e) hs
  rw [map_sum, map_zero] at hp
  have hterms : ∑ j ∈ s, quotientTargetComponent w h U hU e (v j) = v e := by
    calc
      _ = ∑ j ∈ s, if e = j then v j else 0 :=
        Finset.sum_congr rfl fun j hj => quotientTargetComponent_of_mem w h U hU e j (v j) (hv j hj)
      _ = v e := by simp [he, eq_comm]
  exact hterms.symm.trans hp

/-- Every quotient class is a finite sum of actual homogeneous quotient
classes. Together with the preceding independence theorem this is the entire
direct-sum assertion, with no unproved grading premise. -/
theorem quotientTargetPieces_span [Fintype κ]
    (w : ι → ℕ) (h : κ → ℕ) (U : Submodule K M) (x : M ⧸ U) :
    ∃ (s : Finset ℤ) (v : ℤ → M ⧸ U),
      (∀ e, v e ∈ quotientTargetPiece w h e U) ∧ ∑ e ∈ s, v e = x := by
  classical
  obtain ⟨p, rfl⟩ := U.mkQ_surjective x
  have hf := targetComponent_finite_support w h p
  refine ⟨hf.toFinset, fun e => U.mkQ (targetComponent w h e p),
    fun e => ⟨targetComponent w h e p, targetComponent_mem_piece w h e p, rfl⟩, ?_⟩
  rw [← map_sum]
  congr 1
  exact (finsum_eq_sum (fun e => targetComponent w h e p) hf).symm.trans
    (sum_targetComponent w h p)

theorem quotientTargetPiece_disjoint (w : ι → ℕ) (h : κ → ℕ)
    (U : Submodule K M) (hU : ∀ v ∈ U, targetEuler w h v ∈ U)
    (e f : ℤ) (hef : e ≠ f) :
    Disjoint (quotientTargetPiece w h e U) (quotientTargetPiece w h f U) := by
  let T : (M ⧸ U) →ₗ[K] (M ⧸ U) := U.mapQ U (targetEuler w h) hU
  have heig (j : ℤ) (x : M ⧸ U) (hx : x ∈ quotientTargetPiece w h j U) :
      T x = (j : K) • x := by
    obtain ⟨v, hv, rfl⟩ := hx
    change U.mkQ (targetEuler w h v) = _
    rw [targetEuler_of_mem_piece w h j v hv, map_smul]
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro x hx
  have hzero : ((e : K) - (f : K)) • x = 0 := by
    rw [sub_smul, ← heig e x hx.1, ← heig f x hx.2, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left
    (sub_ne_zero.mpr (fun heq => hef (Int.cast_injective heq)))

theorem targetPiece_finite [Fintype κ] (w : ι → ℕ) (h : κ → ℕ) (e : ℤ)
    (hw : ∀ i, 0 < w i) : Module.Finite K (targetPiece (K := K) w h e) := by
  have hfin (j : ℤ) : Module.Finite K (weightedHomogeneousSubmodule K (integerWeights w) j) := by
    apply Module.Finite.of_fg
    rw [integer_piece_eq]
    split_ifs
    · exact weightedHomogeneousSubmodule_fg K w (fun i => (hw i).ne') _
    · exact Submodule.fg_bot
  letI (a : κ) : Module.Finite K
    (weightedHomogeneousSubmodule K (integerWeights w) (e + (h a : ℤ))) := hfin _
  let f : targetPiece (K := K) w h e →ₗ[K]
      (a : κ) → weightedHomogeneousSubmodule K (integerWeights w) (e + (h a : ℤ)) :=
    { toFun v a := ⟨v.val a, (mem_targetPiece w h e v.val).mp v.property a⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact Module.Finite.of_injective f (fun x y hxy =>
    Subtype.ext (funext fun a => congrArg Subtype.val (congrFun hxy a)))

theorem quotientTargetPiece_finite [Fintype κ] (w : ι → ℕ) (h : κ → ℕ) (e : ℤ)
    (U : Submodule K M) (hw : ∀ i, 0 < w i) :
    Module.Finite K (quotientTargetPiece w h e U) := by
  letI := targetPiece_finite (K := K) w h e hw
  unfold quotientTargetPiece
  infer_instance

theorem potential_mem_targetPiece (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (d : ℕ)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (p : P)
    (hp : p.IsWeightedHomogeneous w d) :
    potential F p ∈ targetPiece (K := K) w h (d : ℤ) := by
  rw [mem_targetPiece]
  intro a
  have hp' := (homogeneous_nat_iff_integer w (F a * p) (h a + d)).mp ((hF a).mul hp)
  simpa only [potential_apply, Nat.cast_add, add_comm] using hp'

theorem exceptional_defect_concentrated
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    defectImage F h t ≤ quotientTargetPiece w h (d : ℤ) (hit F h t) := by
  rw [← potentialToQuotient_range F h w t hh hF]
  rintro _ ⟨p, rfl⟩
  rw [potentialToQuotient_eq_component F h w t d hh hF hC hres p]
  refine ⟨potential F (weightedHomogeneousComponent w d p), ?_, rfl⟩
  exact potential_mem_targetPiece F h w d hF _
    (weightedHomogeneousComponent_isWeightedHomogeneous d p)

theorem exceptional_defect_other_degree
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ) (e : ℤ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) (he : (d : ℤ) ≠ e) :
    defectImage F h t ⊓ quotientTargetPiece w h e (hit F h t) = ⊥ := by
  apply eq_bot_iff.mpr
  exact (inf_le_inf_right _ (exceptional_defect_concentrated F h w t d hh hF hC hres)).trans
    (quotientTargetPiece_disjoint w h (hit F h t)
      (targetEuler_mem_hit F h w t hF) (d : ℤ) e he).eq_bot.le

theorem quotientTargetPiece_finrank_add [Fintype κ]
    (w : ι → ℕ) (h : κ → ℕ) (e : ℤ)
    (U V : Submodule K M) (hUV : U ≤ V) (hw : ∀ i, 0 < w i) :
    Module.finrank K (quotientTargetPiece w h e U) =
      Module.finrank K (quotientTargetPiece w h e V) +
      Module.finrank K ↥(V.map U.mkQ ⊓ quotientTargetPiece w h e U : Submodule K (M ⧸ U)) := by
  let S := quotientTargetPiece w h e U
  let f := (Submodule.factor hUV).domRestrict S
  letI : Module.Finite K S := quotientTargetPiece_finite w h e U hw
  have hrange : LinearMap.range f = quotientTargetPiece w h e V := by
    dsimp only [f, LinearMap.domRestrict]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    dsimp only [S, quotientTargetPiece]
    rw [← Submodule.map_comp, Submodule.factor_comp_mk]
  have hfactor : LinearMap.ker (Submodule.factor hUV) = V.map U.mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  have hkernel : (LinearMap.ker f).map S.subtype = V.map U.mkQ ⊓ S := by
    dsimp only [f, LinearMap.domRestrict]
    rw [LinearMap.ker_comp, hfactor, Submodule.map_comap_subtype, inf_comm]
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq S (LinearMap.ker f), hkernel] at hdim
  exact hdim.symm

/-- The Hilbert-series identity coefficient by coefficient for every integer
target degree. This includes every negative baseline degree. -/
theorem exceptional_hilbert_function [Fintype κ]
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ) (e : ℤ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    Module.finrank K (quotientTargetPiece w h e (hit F h t)) =
      Module.finrank K (quotientTargetPiece w h e (coefficientSpace F h)) +
        if e = (d : ℤ) then Module.finrank K (weightedHomogeneousSubmodule K w d) else 0 := by
  have hdim := quotientTargetPiece_finrank_add w h e (hit F h t) (coefficientSpace F h)
    (hit_le_coefficient F h w t hh hF) hw
  change _ = _ + Module.finrank K
    ↥(defectImage F h t ⊓ quotientTargetPiece w h e (hit F h t)) at hdim
  by_cases he : e = (d : ℤ)
  · subst e
    rw [inf_eq_left.mpr (exceptional_defect_concentrated F h w t d hh hF hC hres)] at hdim
    rw [if_pos rfl]
    exact hdim.trans (congrArg (_ + ·)
      (homogeneousDefectEquiv F h w t d hh hF hC hres).finrank_eq.symm)
  · rw [exceptional_defect_other_degree F h w t d e hh hF hC hres (Ne.symm he),
      finrank_bot, add_zero] at hdim
    simpa only [if_neg he, add_zero] using hdim

end PaperVerification.VectorEuler
