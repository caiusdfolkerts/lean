module
import verification.internal.checkpoint
import verification.internal.extract
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
public import consolidated.pair_pin_progress02
import all consolidated.pair_pin_progress02
public import consolidated.rigidity_combined02
import all consolidated.rigidity_combined02
public import consolidated.rigidity_combined03
import all consolidated.rigidity_combined03
public import consolidated.rigidity_combined04
import all consolidated.rigidity_combined04
public import consolidated.rigidity_combined05
import all consolidated.rigidity_combined05
public import consolidated.rigidity_combined06
import all consolidated.rigidity_combined06
public import consolidated.rigidity_combined07
import all consolidated.rigidity_combined07
public import consolidated.rigidity_combined_prepared
import all consolidated.rigidity_combined_prepared
public import consolidated.rigidity_foundations01
import all consolidated.rigidity_foundations01
public import consolidated.rigidity_foundations02
import all consolidated.rigidity_foundations02
public import consolidated.rigidity_generic_tools
import all consolidated.rigidity_generic_tools
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import papers.rigidity_mode_splitting
import all papers.rigidity_mode_splitting

set_option Elab.async false

section BundleSource0001
/- Source: Papers/RigidityProjectiveCenters.lean -/




@[expose] public section

/-!
# Alternating forms and projective virtual centers

The six twist coordinates are identified explicitly with all alternating
four-by-four real matrices. A nonzero homogeneous point is unique up to a
nonzero scalar, so finite centers and centers at infinity are both retained.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

/-- Classification with uniqueness of the homogeneous center up to nonzero
scalar, i.e. uniqueness of the projective point asserted in Lemma 3.4. -/
theorem singularPinSpace_unique_projective_center
    (W : Submodule ℝ Twist) (hW : SingularPinSpace W)
    (hdim : 3 ≤ Module.finrank ℝ W) :
    ∃ q : HomogeneousPoint, q ≠ 0 ∧ W = homogeneousCenterSpace q ∧
      ∀ r : HomogeneousPoint, r ≠ 0 → W = homogeneousCenterSpace r →
        ∃ c : ℝ, c ≠ 0 ∧ c • q = r := by
  rcases singularPinSpace_classification W hW hdim with hf | ⟨d, hd, hWd⟩
  · obtain ⟨a, hWa, _⟩ := hf
    refine ⟨(a, 1), by simp, hWa.trans (homogeneousCenterSpace_finite a).symm, ?_⟩
    intro r hr hWr
    have hs : r.2 ≠ 0 := by
      intro hzero
      have hrd : r.1 ≠ 0 := fun h => hr (Prod.ext h hzero)
      have he : homogeneousCenterSpace r = infiniteCenterSpace r.1 := by
        have hpair : r = (r.1, 0) := Prod.ext rfl hzero
        rw [hpair, homogeneousCenterSpace_infinite]
      exact finiteCenterSpace_ne_infiniteCenterSpace a r.1 hrd
        (hWa.symm.trans (hWr.trans he))
    have ha : a = r.2⁻¹ • r.1 := finiteCenterSpace_injective
      (hWa.symm.trans (hWr.trans (homogeneousCenterSpace_normalize r hs)))
    refine ⟨r.2, hs, ?_⟩
    apply Prod.ext
    · simp [ha, smul_smul, hs]
    · simp
  · refine ⟨(d, 0), by simpa using hd,
      hWd.trans (homogeneousCenterSpace_infinite d).symm, ?_⟩
    intro r hr hWr
    have hs : r.2 = 0 := by
      by_contra hn
      exact finiteCenterSpace_ne_infiniteCenterSpace (r.2⁻¹ • r.1) d hd
        ((homogeneousCenterSpace_normalize r hn).symm.trans (hWr.symm.trans hWd))
    have hrd : r.1 ≠ 0 := fun h => hr (Prod.ext h hs)
    have he : homogeneousCenterSpace r = infiniteCenterSpace r.1 := by
      have hpair : r = (r.1, 0) := Prod.ext rfl hs
      rw [hpair, homogeneousCenterSpace_infinite]
    obtain ⟨c, hc, hcd⟩ := infiniteCenters_scalar_equivalent r.1 d hrd hd
      (he.symm.trans (hWr.symm.trans hWd))
    refine ⟨c, hc, ?_⟩
    exact Prod.ext hcd (by simpa using hs.symm)

/-- Lemma 3.4 at an algebraically generic point, stated with the literal
four-by-four matrix contraction and uniqueness of its projective center.
The coefficient field is chosen before the new pin coordinates. -/
theorem generic_alternating_pin_space_unique_projective_center
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hdim : 3 ≤ Module.finrank ℝ (coefficientTwistSpan X))
    (hrank : Module.finrank ℝ
      (matrixPinContraction (coefficientTwistSpan X) p).range ≤ 2) :
    ∃ q : HomogeneousPoint, q ≠ 0 ∧
      (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
        twistMatrix Y *ᵥ homogeneousVector q = 0) ∧
      ∀ r : HomogeneousPoint, r ≠ 0 →
        (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
          twistMatrix Y *ᵥ homogeneousVector r = 0) →
        ∃ c : ℝ, c ≠ 0 ∧ c • q = r := by
  rw [matrixPinContraction_rank] at hrank
  obtain ⟨q, hq, hWq, hunique⟩ := singularPinSpace_unique_projective_center
    (coefficientTwistSpan X) (singularPinSpace_of_generic_pin X p hp hrank) hdim
  refine ⟨q, hq, ?_, ?_⟩
  · intro Y
    rw [hWq]
    exact mem_homogeneousCenterSpace_iff_matrix_kernel q Y
  · intro r hr hWr
    apply hunique r hr
    ext Y
    exact (hWr Y).trans (mem_homogeneousCenterSpace_iff_matrix_kernel r Y).symm

/-- The small-dimensional clause of Lemma 3.4 for the actual alternating
contraction: no nonzero form in such a space kills the generic point. -/
theorem generic_alternating_pin_injective_of_finrank_le_two
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K)
    (hdim : Module.finrank ℝ (coefficientTwistSpan X) ≤ 2)
    (p : Vec3) (hp : AlgebraicIndependent K p) :
    Function.Injective (matrixPinContraction (coefficientTwistSpan X) p) := by
  intro A B h
  apply generic_pin_injective_of_finrank_le_two X hdim p hp
  have h₁ := homogeneousVectorLinear_injective h
  rw [homogeneousEvaluation_finite_eq_graph] at h₁
  exact pinVelocityGraph_injective p h₁

/-- The coefficient-field dimension and the generic real contraction
dimension refer to the same twist space, as required when a vertex is
deleted before its algebraically independent coordinates are reintroduced.
This is the principal clause of Lemma 3.4 with its original dimension. -/
theorem generic_alternating_coefficient_space_unique_projective_center
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hdim : 3 ≤ Module.finrank K (Submodule.span K (Set.range X)))
    (hrank : Module.finrank ℝ
      (matrixPinContraction (coefficientTwistSpan X) p).range ≤ 2) :
    ∃ q : HomogeneousPoint, q ≠ 0 ∧
      (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
        twistMatrix Y *ᵥ homogeneousVector q = 0) ∧
      ∀ r : HomogeneousPoint, r ≠ 0 →
        (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
          twistMatrix Y *ᵥ homogeneousVector r = 0) →
        ∃ c : ℝ, c ≠ 0 ∧ c • q = r := by
  apply generic_alternating_pin_space_unique_projective_center X p hp
  · simpa only [finrank_coefficientTwistSpan] using hdim
  · exact hrank

/-- The other clause of Lemma 3.4 with dimension measured over the
pre-existing coefficient field. -/
theorem generic_alternating_coefficient_pin_injective_of_finrank_le_two
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K)
    (hdim : Module.finrank K (Submodule.span K (Set.range X)) ≤ 2)
    (p : Vec3) (hp : AlgebraicIndependent K p) :
    Function.Injective (matrixPinContraction (coefficientTwistSpan X) p) := by
  apply generic_alternating_pin_injective_of_finrank_le_two X _ p hp
  simpa only [finrank_coefficientTwistSpan] using hdim

end Papers.Rigidity

end
end BundleSource0001

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0001/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0001.json"

section BundleSource0002
/- Source: Papers/RigiditySoftPinCenters.lean -/










@[expose] public section

/-!
# Virtual-center forces at actual body pins

The first results identify the annihilator of rotations about a finite
center. The later constructions extract the unique twist of each actual
maximal clique after deletion of a vertex, and use the ordinary balanced
load equations to prove the virtual-work identity.

The early linear-algebra lemmas state their center premise explicitly.
The final graph theorems derive the three-dimensional singular relative
image from actual deletion ranks and then apply the proved projective
classification. Their nonzero force-axis conclusion includes centers
at infinity and requires no choice of affine chart. Ambient rigidity
closure excludes every other actual incident-body vertex from the
axis, avoiding a coefficient-field descent argument.
-/

noncomputable section
namespace Papers.Rigidity

open Matrix BarJoint
open scoped Classical Matrix BigOperators

/-- A force annihilates every rotational velocity about a nonzero axis
vector exactly when it is a scalar multiple of that vector. -/
theorem force_annihilates_rotations_iff
    (d F : Vec3) (hd : d ≠ 0) :
    (∀ ω : Vec3, F ⬝ᵥ (ω ⨯₃ d) = 0) ↔
      F ∈ Submodule.span ℝ {d} := by
  constructor
  · intro h
    rw [← ker_crossProduct_eq_span d hd, LinearMap.mem_ker]
    have hcross : ∀ ω : Vec3, ω ⬝ᵥ (d ⨯₃ F) = 0 := by
      intro ω
      rw [← triple_product_permutation F ω d]
      exact h ω
    exact dotProduct_self_eq_zero.mp (hcross (d ⨯₃ F))
  · intro h ω
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [smul_dotProduct, dot_cross_self, smul_zero]

/-- The force-axis statement of Lemma 3.6 in a finite-center chart. -/
theorem force_annihilates_finiteCenter_iff
    (a p F : Vec3) (hpa : p ≠ a) :
    (∀ X : finiteCenterSpace a, F ⬝ᵥ evaluateTwist p X.val = 0) ↔
      F ∈ Submodule.span ℝ {p - a} := by
  have heval (X : finiteCenterSpace a) :
      evaluateTwist p X.val = X.val.1 ⨯₃ (p - a) := by
    have hfix : X.val.2 + X.val.1 ⨯₃ a = 0 := X.property
    rw [evaluateTwist_apply, map_sub]
    have ht : X.val.2 = -(X.val.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left hfix
    rw [ht]
    abel
  rw [← force_annihilates_rotations_iff (p - a) F (sub_ne_zero.mpr hpa)]
  constructor
  · intro h ω
    let X : finiteCenterSpace a :=
      ⟨(ω, -(ω ⨯₃ a)), by
        change -(ω ⨯₃ a) + ω ⨯₃ a = 0
        exact neg_add_cancel _⟩
    exact (congrArg (fun z : Vec3 => F ⬝ᵥ z) (heval X)).symm.trans (h X)
  · intro h X
    rw [heval]
    exact h X.val.1

/-- A relative twist image equal to the finite-center space has precisely
the same force annihilator; the domain is arbitrary and no surjectivity
is assumed separately from the literal range equality. -/
theorem force_annihilates_range_finiteCenter_iff
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (R : U →ₗ[ℝ] Twist) (a p F : Vec3)
    (hR : R.range = finiteCenterSpace a) (hpa : p ≠ a) :
    (∀ u, F ⬝ᵥ evaluateTwist p (R u) = 0) ↔
      F ∈ Submodule.span ℝ {p - a} := by
  rw [← force_annihilates_finiteCenter_iff a p F hpa]
  constructor
  · intro h X
    have hX : X.val ∈ R.range := by rw [hR]; exact X.property
    obtain ⟨u, hu⟩ := hX
    rw [← hu]
    exact h u
  · intro h u
    exact h ⟨R u, by rw [← hR]; exact ⟨u, rfl⟩⟩

/-- A Euclidean twist fixing two points fixes their whole affine line. -/
theorem evaluateTwist_eq_zero_on_affine_line
    (X : Twist) (a p w : Vec3)
    (ha : evaluateTwist a X = 0) (hp : evaluateTwist p X = 0)
    (hw : w - a ∈ Submodule.span ℝ {p - a}) : evaluateTwist w X = 0 := by
  have he (q : Vec3) : evaluateTwist q X - evaluateTwist a X = X.1 ⨯₃ (q - a) := by
    rw [evaluateTwist_apply, evaluateTwist_apply, map_sub]
    abel
  have hpa : X.1 ⨯₃ (p - a) = 0 := by rw [← he p, hp, ha, sub_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have hwa : X.1 ⨯₃ (w - a) = 0 := by rw [← hc, map_smul, hpa, smul_zero]
  rw [← he w, ha, sub_zero] at hwa
  exact hwa

/-- A homogeneous center determines the force direction without choosing
an affine chart. The vector is nonzero when the pin and the projective
center are distinct. -/
theorem force_annihilates_homogeneousCenter_axis
    (q : HomogeneousPoint) (p F : Vec3) (hd : q.2 • p - q.1 ≠ 0)
    (hF : ∀ X : homogeneousCenterSpace q, F ⬝ᵥ evaluateTwist p X.val = 0) :
    F ∈ Submodule.span ℝ {q.2 • p - q.1} := by
  apply (force_annihilates_rotations_iff (q.2 • p - q.1) F hd).mp
  intro ω
  let X : homogeneousCenterSpace q := ⟨(q.2 • ω, -(ω ⨯₃ q.1)), by
    change homogeneousEvaluation q (q.2 • ω, -(ω ⨯₃ q.1)) = 0
    apply Prod.ext
    · change q.2 • -(ω ⨯₃ q.1) + (q.2 • ω) ⨯₃ q.1 = 0
      rw [smul_neg, map_smul, LinearMap.smul_apply, neg_add_cancel]
    · simp [homogeneousEvaluation_apply]⟩
  have he : evaluateTwist p X.val = ω ⨯₃ (q.2 • p - q.1) := by
    simp only [X, evaluateTwist_apply, map_sub, map_smul, LinearMap.smul_apply]
    abel
  exact (congrArg (fun z : Vec3 => F ⬝ᵥ z) he).symm.trans (hF X)

/-- A twist fixing a finite point and a projective center fixes the
corresponding entire line, including when the center lies at infinity. -/
theorem evaluateTwist_eq_zero_on_homogeneous_axis
    (X : Twist) (q : HomogeneousPoint) (p w : Vec3)
    (hq : X ∈ homogeneousCenterSpace q) (hp : evaluateTwist p X = 0)
    (hw : w - p ∈ Submodule.span ℝ {q.2 • p - q.1}) :
    evaluateTwist w X = 0 := by
  have ht : X.2 = -(X.1 ⨯₃ p) := eq_neg_of_add_eq_zero_left hp
  have hfirst : q.2 • X.2 + X.1 ⨯₃ q.1 = 0 := congrArg Prod.fst hq
  have hd : X.1 ⨯₃ (q.2 • p - q.1) = 0 := by
    rw [map_sub, map_smul]
    rw [ht, smul_neg] at hfirst
    apply sub_eq_zero.mpr
    calc
      q.2 • (X.1 ⨯₃ p) = q.2 • (X.1 ⨯₃ p) +
          (-(q.2 • (X.1 ⨯₃ p)) + X.1 ⨯₃ q.1) := by rw [hfirst, add_zero]
      _ = X.1 ⨯₃ q.1 := by abel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have hwp : X.1 ⨯₃ (w - p) = 0 := by rw [← hc, map_smul, hd, smul_zero]
  have he : evaluateTwist w X - evaluateTwist p X = X.1 ⨯₃ (w - p) := by
    rw [evaluateTwist_apply, evaluateTwist_apply, map_sub]
    abel
  rw [← he, hp, sub_zero] at hwp
  exact hwp

/-- A nonzero vector on one line cannot also lie on a line whose
direction is outside the first line. -/
theorem nonzero_force_not_on_other_line
    (d w F : Vec3) (hF : F ≠ 0) (hFd : F ∈ Submodule.span ℝ {d})
    (hw : w ∉ Submodule.span ℝ {d}) : F ∉ Submodule.span ℝ {w} := by
  intro hFw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hFw
  have hcne : c ≠ 0 := by
    intro hz
    exact hF (by rw [← hc, hz, zero_smul])
  apply hw
  have h := (Submodule.span ℝ {d}).smul_mem c⁻¹ hFd
  simpa only [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul] using h

namespace BodyLoads

variable {V : Type} [Fintype V]

theorem Body.three_le_card_erase {G : SimpleGraph V} (C : Body G) (v : V) :
    3 ≤ (C.val.erase v).card := by
  have hc := C.property.1
  by_cases hv : v ∈ C.val
  · rw [Finset.card_erase_of_mem hv]
    omega
  · rw [Finset.erase_eq_of_notMem hv]
    omega

/-- A surviving maximal clique still contains a triangle and hence every
deleted graph motion restricts to one Euclidean twist on it. -/
theorem exists_deletedBodyTwist
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : VertexPin.DeletedMotions G p v) :
    ∃ X : Twist, ∀ w ∈ C.val, ∀ hw : w ≠ v,
      u.val ⟨w, hw⟩ = evaluateTwist (p w) X := by
  let S := C.val.erase v
  let e : S ↪ V := Function.Embedding.subtype _
  let d : S ↪ VertexPin.DeletedVertex v :=
    ⟨fun w => ⟨w.val, (Finset.mem_erase.mp w.property).1⟩, by
      intro a b h
      exact Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h)⟩
  obtain ⟨f : Fin 3 ↪ S⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 3) (β := ↥S) (by simpa only [Fintype.card_fin, Fintype.card_coe] using C.three_le_card_erase v)
  have hpS := GeneralPosition.InGeneralPosition.comp_embedding p hp e
  have huS : IsInfinitesimalMotion (SimpleGraph.completeGraph S)
      (p ∘ e) (u.val ∘ d) := by
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    apply (isInfinitesimalMotion_iff (VertexPin.deletedGraph G v)
      (VertexPin.deletedPlacement p v) u.val).mp u.property (d a) (d b)
    exact C.property.2.1 (Finset.mem_erase.mp a.property).2
      (Finset.mem_erase.mp b.property).2 (fun h => hab (Subtype.ext h))
  obtain ⟨X, hX⟩ := exists_twist_of_completeMotion (p ∘ e) (u.val ∘ d) hpS f huS
  refine ⟨X, ?_⟩
  intro w hw hne
  exact hX ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩⟩

/-- Three surviving points make the body twist unique. -/
theorem deletedBodyTwist_unique
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (X Y : Twist)
    (hfit : ∀ w ∈ C.val, w ≠ v →
      evaluateTwist (p w) X = evaluateTwist (p w) Y) : X = Y := by
  obtain ⟨f : Fin 3 ↪ V, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := C.val.erase v) (by simpa using C.three_le_card_erase v)
  apply sub_eq_zero.mp
  apply twist_eq_zero_of_fixing_triangle (p ∘ f)
    (GeneralPosition.InGeneralPosition.triangle p hp f) (X - Y)
  intro i
  change evaluateTwist (p (f i)) (X - Y) = 0
  have hi := Finset.mem_erase.mp (hf ⟨i, rfl⟩)
  rw [map_sub, hfit (f i) hi.2 hi.1, sub_self]

def deletedBodyTwistValue
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : VertexPin.DeletedMotions G p v) : Twist :=
  Classical.choose (exists_deletedBodyTwist G v C p hp u)

theorem deletedBodyTwistValue_fit
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : VertexPin.DeletedMotions G p v) (w : V) (hw : w ∈ C.val) (hne : w ≠ v) :
    evaluateTwist (p w) (deletedBodyTwistValue G v C p hp u) = u.val ⟨w, hne⟩ :=
  (Classical.choose_spec (exists_deletedBodyTwist G v C p hp u) w hw hne).symm

/-- The actual linear twist extracted from a maximal body after deletion.
Linearity follows from uniqueness on the surviving triangle. -/
def deletedBodyTwist
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    VertexPin.DeletedMotions G p v →ₗ[ℝ] Twist where
  toFun := deletedBodyTwistValue G v C p hp
  map_add' u z := by
    apply deletedBodyTwist_unique G v C p hp
    intro w hw hne
    rw [map_add, deletedBodyTwistValue_fit G v C p hp (u + z) w hw hne,
      deletedBodyTwistValue_fit G v C p hp u w hw hne,
      deletedBodyTwistValue_fit G v C p hp z w hw hne] <;> rfl
  map_smul' c u := by
    apply deletedBodyTwist_unique G v C p hp
    intro w hw hne
    rw [map_smul, deletedBodyTwistValue_fit G v C p hp (c • u) w hw hne,
      deletedBodyTwistValue_fit G v C p hp u w hw hne] <;> rfl

@[simp] theorem deletedBodyTwist_fit
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : VertexPin.DeletedMotions G p v) (w : V) (hw : w ∈ C.val) (hne : w ≠ v) :
    evaluateTwist (p w) (deletedBodyTwist G v C p hp u) = u.val ⟨w, hne⟩ :=
  deletedBodyTwistValue_fit G v C p hp u w hw hne

/-- Virtual work at the deleted vertex. Every other vertex cancels by
compatibility, and each body's full work is zero by its force/moment
balance. This is proved for the actual compatible body-load space. -/
theorem compatible_load_deleted_virtual_work
    (G : SimpleGraph V) (v : V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads G p Finset.univ)
    (u : VertexPin.DeletedMotions G p v) :
    (∑ C : Body G, (F.val C).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v C p hp u)) = 0 := by
  let u₀ : Placement V 3 := fun w => if hw : w = v then 0 else u.val ⟨w, hw⟩
  have hpoint (C : Body G) :
      (∑ w, (F.val C).val w ⬝ᵥ
        (evaluateTwist (p w) (deletedBodyTwist G v C p hp u) - u₀ w)) =
      (F.val C).val v ⬝ᵥ evaluateTwist (p v) (deletedBodyTwist G v C p hp u) := by
    rw [Finset.sum_eq_single v]
    · simp [u₀]
    · intro w _ hw
      by_cases hC : w ∈ C.val
      · rw [deletedBodyTwist_fit G v C p hp u w hC hw]
        simp [u₀, hw]
      · have hzero : (F.val C).val w = 0 :=
          (F.val C).property.2 w (by simpa using hC)
        rw [hzero, zero_dotProduct]
    · simp
  have hbody (C : Body G) :
      (∑ w, (F.val C).val w ⬝ᵥ
        evaluateTwist (p w) (deletedBodyTwist G v C p hp u)) = 0 := by
    simpa only [loadWorkEquiv_apply, globalTwistOperator_apply] using
      balanced_load_annihilates_twist p (F.val C).val
        (F.val C).property.1 (deletedBodyTwist G v C p hp u)
  have hcancel : (∑ C : Body G, ∑ w, (F.val C).val w ⬝ᵥ u₀ w) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro w _
    rw [← sum_dotProduct,
      (mem_compatibleBodyLoads_iff G p Finset.univ F.val).mp F.property w,
      zero_dotProduct]
  calc
    (∑ C : Body G, (F.val C).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v C p hp u)) =
        ∑ C : Body G, ∑ w, (F.val C).val w ⬝ᵥ
          (evaluateTwist (p w) (deletedBodyTwist G v C p hp u) - u₀ w) := by
            exact Finset.sum_congr rfl (fun C _ => (hpoint C).symm)
    _ = (∑ C : Body G, ∑ w, (F.val C).val w ⬝ᵥ
          evaluateTwist (p w) (deletedBodyTwist G v C p hp u)) -
          ∑ C : Body G, ∑ w, (F.val C).val w ⬝ᵥ u₀ w := by
            simp only [dotProduct_sub, Finset.sum_sub_distrib]
    _ = 0 := by simp only [hbody, Finset.sum_const_zero, hcancel, sub_zero]

/-- The relative twist of the actual two bodies, with the first body
used as reference. No reduced body framework replaces the graph. -/
def TwoBodyPin.relativeTwist
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    VertexPin.DeletedMotions G p v →ₗ[ℝ] Twist :=
  deletedBodyTwist G v Q.right p hp - deletedBodyTwist G v Q.left p hp

theorem TwoBodyPin.load_annihilates_relativeTwist
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (F : compatibleBodyLoads G p Finset.univ)
    (u : VertexPin.DeletedMotions G p v) :
    Q.loadProjection p F ⬝ᵥ evaluateTwist (p v) (Q.relativeTwist p hp u) = 0 := by
  have hwork := compatible_load_deleted_virtual_work G v p hp F u
  have hsum : (∑ C : Body G, (F.val C).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v C p hp u)) =
      (F.val Q.left).val v ⬝ᵥ
        evaluateTwist (p v) (deletedBodyTwist G v Q.left p hp u) +
      (F.val Q.right).val v ⬝ᵥ
        evaluateTwist (p v) (deletedBodyTwist G v Q.right p hp u) := by
    have hsub : (∑ C ∈ ({Q.left, Q.right} : Finset (Body G)), (F.val C).val v ⬝ᵥ
        evaluateTwist (p v) (deletedBodyTwist G v C p hp u)) =
        ∑ C : Body G, (F.val C).val v ⬝ᵥ
          evaluateTwist (p v) (deletedBodyTwist G v C p hp u) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro C _ hC
      have hv : v ∉ C.val := by
        intro hv
        exact hC (by simpa only [Finset.mem_insert, Finset.mem_singleton] using Q.exhaustive C hv)
      rw [compatible_load_zero_outside_body G p F C v hv, zero_dotProduct]
    rw [← hsub, Finset.sum_pair Q.distinct]
  rw [hsum, Q.load_right_eq_neg_left, neg_dotProduct] at hwork
  change (F.val Q.left).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v Q.left p hp u) +
    -((F.val Q.left).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v Q.right p hp u)) = 0 at hwork
  change Q.loadProjection p F ⬝ᵥ
    evaluateTwist (p v)
      (deletedBodyTwist G v Q.right p hp u - deletedBodyTwist G v Q.left p hp u) = 0
  rw [map_sub, dotProduct_sub]
  change (F.val Q.left).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v Q.right p hp u) -
    (F.val Q.left).val v ⬝ᵥ
      evaluateTwist (p v) (deletedBodyTwist G v Q.left p hp u) = 0
  linarith

/-- Once the literal relative image is identified, every actual body
load lies on the virtual-center axis. -/
theorem TwoBodyPin.load_mem_center_axis
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (a : Vec3) (ha : p v ≠ a)
    (hcenter : (Q.relativeTwist p hp).range = finiteCenterSpace a)
    (F : compatibleBodyLoads G p Finset.univ) :
    Q.loadProjection p F ∈ Submodule.span ℝ {p v - a} := by
  apply (force_annihilates_range_finiteCenter_iff
    (Q.relativeTwist p hp) a (p v) (Q.loadProjection p F) hcenter ha).mp
  exact Q.load_annihilates_relativeTwist p hp F

def restrictDeletedMotion
    (G : SimpleGraph V) (v : V) (p : Placement V 3) :
    (rigidityOperator G p).ker →ₗ[ℝ] VertexPin.DeletedMotions G p v where
  toFun u := ⟨fun w => u.val w.val, by
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro a b hab
    exact (isInfinitesimalMotion_iff G p u.val).mp u.property a.val b.val hab⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The twist recovered after deletion agrees with the full body's
twist whenever the deleted motion comes from the full graph. -/
theorem deletedBodyTwist_fullMotion_fit
    (G : SimpleGraph V) (v : V) (C : Body G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (u : (rigidityOperator G p).ker) (w : V) (hw : w ∈ C.val) :
    u.val w = evaluateTwist (p w)
      (deletedBodyTwist G v C p hp (restrictDeletedMotion G v p u)) := by
  obtain ⟨X, hX⟩ := exists_twist_on_clique G p u.val hp u.property C.val
    (by have hc := C.property.1; omega) C.property.2.1
  have heq : deletedBodyTwist G v C p hp (restrictDeletedMotion G v p u) = X := by
    apply deletedBodyTwist_unique G v C p hp
    intro z hz hne
    rw [deletedBodyTwist_fit G v C p hp (restrictDeletedMotion G v p u) z hz hne]
    exact hX z hz
  rw [heq]
  exact hX w hw

/-- If every full graph motion gives a vertex of one body the velocity
of another body, that vertex is already in the latter maximal body. -/
theorem relative_fixed_vertex_mem_body
    (M : MinimalCounterexample V) (v : V) (C D : Body M.graph)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (w : V) (hwC : w ∈ C.val)
    (hfix : ∀ u : (rigidityOperator M.graph p).ker,
      evaluateTwist (p w)
        (deletedBodyTwist M.graph v D p hp (restrictDeletedMotion M.graph v p u) -
          deletedBodyTwist M.graph v C p hp (restrictDeletedMotion M.graph v p u)) = 0) :
    w ∈ D.val := by
  have hcluster : RigidCluster M.graph (insert w D.val) := by
    apply rigidCluster_of_motionRepresentation M.graph (insert w D.val) p hgen
    intro u
    refine ⟨deletedBodyTwist M.graph v D p hp (restrictDeletedMotion M.graph v p u), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      have h := hfix u
      rw [map_sub, sub_eq_zero] at h
      rw [deletedBodyTwist_fullMotion_fit M.graph v C p hp u w hwC]
      exact h.symm
    · exact deletedBodyTwist_fullMotion_fit M.graph v D p hp u z hz
  have hcard : 4 ≤ (insert w D.val).card :=
    D.property.1.trans (Finset.card_le_card (Finset.subset_insert w D.val))
  have hclique := M.rigidCluster_isClique (insert w D.val) hcard hcluster
  exact D.property.2.2 (insert w D.val) (Finset.subset_insert w D.val)
    hclique (Finset.mem_insert_self w D.val)

/-- Uniform projective version of the axis exclusion. An affine chart
is unnecessary: `q.2 • p v - q.1` is the direction of the line through
the pin and its homogeneous virtual center. -/
theorem TwoBodyPin.homogeneous_axis_avoids_other_body_vertices
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (q : HomogeneousPoint)
    (hcenter : (Q.relativeTwist p hp).range = homogeneousCenterSpace q)
    (w : V) (hw : w ∈ Q.left.val ∪ Q.right.val) (hwv : w ≠ v) :
    p w - p v ∉ Submodule.span ℝ {q.2 • p v - q.1} := by
  intro hline
  have hfix (u : (rigidityOperator M.graph p).ker) :
      evaluateTwist (p w)
        (Q.relativeTwist p hp (restrictDeletedMotion M.graph v p u)) = 0 := by
    apply evaluateTwist_eq_zero_on_homogeneous_axis _ q (p v) (p w) _ _ hline
    · rw [← hcenter]
      exact ⟨restrictDeletedMotion M.graph v p u, rfl⟩
    · change evaluateTwist (p v)
        (deletedBodyTwist M.graph v Q.right p hp (restrictDeletedMotion M.graph v p u) -
          deletedBodyTwist M.graph v Q.left p hp (restrictDeletedMotion M.graph v p u)) = 0
      rw [map_sub,
        ← deletedBodyTwist_fullMotion_fit M.graph v Q.right p hp u v Q.right_mem,
        ← deletedBodyTwist_fullMotion_fit M.graph v Q.left p hp u v Q.left_mem,
        sub_self]
  have hboth : w ∈ Q.left.val ∩ Q.right.val := by
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_inter.mpr ⟨hw,
        relative_fixed_vertex_mem_body M v Q.left Q.right p hgen hp w hw hfix⟩
    · refine Finset.mem_inter.mpr ⟨?_, hw⟩
      apply relative_fixed_vertex_mem_body M v Q.right Q.left p hgen hp w hw
      intro u
      have h := hfix u
      change evaluateTwist (p w)
        (deletedBodyTwist M.graph v Q.right p hp (restrictDeletedMotion M.graph v p u) -
          deletedBodyTwist M.graph v Q.left p hp (restrictDeletedMotion M.graph v p u)) = 0 at h
      rw [map_sub, sub_eq_zero] at h
      rw [map_sub, h, sub_self]
  rw [hinter, Finset.mem_singleton] at hboth
  exact hwv hboth

/-- Strong axis exclusion: the rotation axis of a soft point pin
contains no other actual vertex of either incident body. This follows
directly from ambient rigidity closure, without field descent. -/
theorem TwoBodyPin.center_axis_avoids_other_body_vertices
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (a : Vec3)
    (hcenter : (Q.relativeTwist p hp).range = finiteCenterSpace a)
    (w : V) (hw : w ∈ Q.left.val ∪ Q.right.val) (hwv : w ≠ v) :
    p w - a ∉ Submodule.span ℝ {p v - a} := by
  intro hline
  have hfix (u : (rigidityOperator M.graph p).ker) :
      evaluateTwist (p w)
        (Q.relativeTwist p hp (restrictDeletedMotion M.graph v p u)) = 0 := by
    apply evaluateTwist_eq_zero_on_affine_line _ a (p v) (p w) _ _ hline
    · have hm : Q.relativeTwist p hp (restrictDeletedMotion M.graph v p u) ∈
          finiteCenterSpace a := by
        rw [← hcenter]
        exact ⟨restrictDeletedMotion M.graph v p u, rfl⟩
      exact hm
    · change evaluateTwist (p v)
        (deletedBodyTwist M.graph v Q.right p hp (restrictDeletedMotion M.graph v p u) -
          deletedBodyTwist M.graph v Q.left p hp (restrictDeletedMotion M.graph v p u)) = 0
      rw [map_sub,
        ← deletedBodyTwist_fullMotion_fit M.graph v Q.right p hp u v Q.right_mem,
        ← deletedBodyTwist_fullMotion_fit M.graph v Q.left p hp u v Q.left_mem,
        sub_self]
  have hboth : w ∈ Q.left.val ∩ Q.right.val := by
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_inter.mpr ⟨hw,
        relative_fixed_vertex_mem_body M v Q.left Q.right p hgen hp w hw hfix⟩
    · refine Finset.mem_inter.mpr ⟨?_, hw⟩
      apply relative_fixed_vertex_mem_body M v Q.right Q.left p hgen hp w hw
      intro u
      have h := hfix u
      change evaluateTwist (p w)
        (deletedBodyTwist M.graph v Q.right p hp (restrictDeletedMotion M.graph v p u) -
          deletedBodyTwist M.graph v Q.left p hp (restrictDeletedMotion M.graph v p u)) = 0 at h
      rw [map_sub, sub_eq_zero] at h
      rw [map_sub, h, sub_self]
  rw [hinter, Finset.mem_singleton] at hboth
  exact hwv hboth

/-- A common evaluation center of two relative body motions cannot be
a vertex belonging to only one of those bodies. Otherwise the other
body plus that vertex is an actual ambient rigid cluster. -/
theorem relative_center_ne_exclusive_vertex
    (M : MinimalCounterexample V) (v : V) (C D : Body M.graph)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (a : Vec3)
    (hfix : ∀ u : VertexPin.DeletedMotions M.graph p v,
      evaluateTwist a (deletedBodyTwist M.graph v D p hp u -
        deletedBodyTwist M.graph v C p hp u) = 0)
    (w : V) (hwC : w ∈ C.val) (hwD : w ∉ D.val) : a ≠ p w := by
  intro haw
  have hcluster : RigidCluster M.graph (insert w D.val) := by
    apply rigidCluster_of_motionRepresentation M.graph (insert w D.val) p hgen
    intro u
    refine ⟨deletedBodyTwist M.graph v D p hp (restrictDeletedMotion M.graph v p u), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      have h := hfix (restrictDeletedMotion M.graph v p u)
      rw [haw, map_sub, sub_eq_zero] at h
      rw [deletedBodyTwist_fullMotion_fit M.graph v C p hp u w hwC]
      exact h.symm
    · exact deletedBodyTwist_fullMotion_fit M.graph v D p hp u z hz
  have hcard : 4 ≤ (insert w D.val).card :=
    D.property.1.trans (Finset.card_le_card (Finset.subset_insert w D.val))
  have hclique := M.rigidCluster_isClique (insert w D.val) hcard hcluster
  exact hwD (D.property.2.2 (insert w D.val) (Finset.subset_insert w D.val)
    hclique (Finset.mem_insert_self w D.val))

/-- The vertex-exclusion part of Lemma 3.6 for the finite-center branch.
The excluded vertices are exactly the actual vertices of either body
other than the shared point pin. -/
theorem TwoBodyPin.center_ne_other_body_vertex
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (a : Vec3)
    (hcenter : (Q.relativeTwist p hp).range = finiteCenterSpace a)
    (w : V) (hw : w ∈ Q.left.val ∪ Q.right.val) (hwv : w ≠ v) : a ≠ p w := by
  have hfix (u : VertexPin.DeletedMotions M.graph p v) :
      evaluateTwist a (Q.relativeTwist p hp u) = 0 := by
    have hm : Q.relativeTwist p hp u ∈ finiteCenterSpace a := by
      rw [← hcenter]
      exact ⟨u, rfl⟩
    exact hm
  have hnotboth : ¬ (w ∈ Q.left.val ∧ w ∈ Q.right.val) := by
    intro h
    have hm : w ∈ Q.left.val ∩ Q.right.val := Finset.mem_inter.mpr h
    rw [hinter, Finset.mem_singleton] at hm
    exact hwv hm
  rcases Finset.mem_union.mp hw with hw | hw
  · exact relative_center_ne_exclusive_vertex M v Q.left Q.right p hgen hp a
      hfix w hw (fun h => hnotboth ⟨hw, h⟩)
  · apply relative_center_ne_exclusive_vertex M v Q.right Q.left p hgen hp a
      _ w hw (fun h => hnotboth ⟨h, hw⟩)
    intro u
    have h := hfix u
    change evaluateTwist a
      (deletedBodyTwist M.graph v Q.right p hp u -
        deletedBodyTwist M.graph v Q.left p hp u) = 0 at h
    rw [map_sub, sub_eq_zero] at h
    rw [map_sub, h, sub_self]

/-- A chosen triangle in a body after deletion, carrying its genuine
maximal-body owner. -/
def Body.incidentTriangle {G : SimpleGraph V} (C : Body G) (v : V)
    (hv : v ∈ C.val) : VertexPin.OwnedIncidentTriangle G v := by
  let S := C.val.erase v
  let f : Fin 3 ↪ S := Classical.choice
    (Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := ↥S)
      (by simpa only [Fintype.card_fin, Fintype.card_coe] using C.three_le_card_erase v))
  let d : Fin 3 ↪ VertexPin.DeletedVertex v :=
    ⟨fun i => ⟨(f i).val, (Finset.mem_erase.mp (f i).property).1⟩,
      fun i j h => f.injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h))⟩
  exact ⟨(C.val, d), C.property, hv,
    fun i => (Finset.mem_erase.mp (f i).property).2⟩

@[simp] theorem Body.incidentTriangle_owner {G : SimpleGraph V}
    (C : Body G) (v : V) (hv : v ∈ C.val) :
    (C.incidentTriangle v hv).owner = C.val := rfl

theorem owned_bodyTwist_eq_deletedBodyTwist
    {G : SimpleGraph V} {v : V} (hG : K4Covered G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (b : VertexPin.OwnedIncidentTriangle G v)
    (u : VertexPin.DeletedMotions G p v) :
    (VertexPin.ownedIncidentTetrahedra G v hG).bodyTwist p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
        (VertexPin.ownedIncidentTetrahedra G v hG)) b u =
      deletedBodyTwist G v ⟨b.owner, b.property.1⟩ p hp u := by
  apply deletedBodyTwist_unique G v ⟨b.owner, b.property.1⟩ p hp
  intro w hw hne
  rw [deletedBodyTwist_fit G v ⟨b.owner, b.property.1⟩ p hp u w hw hne]
  exact (VertexPin.IncidentTetrahedra.owned_bodyTwist_fit hG p hp b u ⟨w, hne⟩ hw).symm

/-- The full owned-tetrahedron family and the two-body relative map
have the same kernel, even for bodies with arbitrarily many vertices. -/
theorem TwoBodyPin.ker_owned_relativeTwist
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (hG : K4Covered G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    let T := VertexPin.ownedIncidentTetrahedra G v hG
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
    (T.relativeTwistOperator p hn (Q.left.incidentTriangle v Q.left_mem)).ker =
      (Q.relativeTwist p hp).ker := by
  intro T hn
  ext u
  constructor
  · intro hu
    have h := congrFun (LinearMap.mem_ker.mp hu) (Q.right.incidentTriangle v Q.right_mem)
    change T.bodyTwist p hn (Q.right.incidentTriangle v Q.right_mem) u -
      T.bodyTwist p hn (Q.left.incidentTriangle v Q.left_mem) u = 0 at h
    rw [owned_bodyTwist_eq_deletedBodyTwist, owned_bodyTwist_eq_deletedBodyTwist] at h
    exact h
  · intro hu
    have h := LinearMap.mem_ker.mp hu
    rw [LinearMap.mem_ker]
    funext b
    change T.bodyTwist p hn b u -
      T.bodyTwist p hn (Q.left.incidentTriangle v Q.left_mem) u = 0
    rw [owned_bodyTwist_eq_deletedBodyTwist, owned_bodyTwist_eq_deletedBodyTwist]
    rcases Q.exhaustive ⟨b.owner, b.property.1⟩ b.property.2.1 with hb | hb
    · rw [hb]
      exact sub_self _
    · rw [hb]
      exact h

theorem TwoBodyPin.relativeTwist_rank_eq_owned
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (hG : K4Covered G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    let T := VertexPin.ownedIncidentTetrahedra G v hG
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
    Module.finrank ℝ (Q.relativeTwist p hp).range =
      Module.finrank ℝ
        (T.relativeTwistOperator p hn (Q.left.incidentTriangle v Q.left_mem)).range := by
  intro T hn
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := VertexPin.DeletedMotions G p v) (V₂ := Twist)
    (Q.relativeTwist p hp)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := VertexPin.DeletedMotions G p v)
    (V₂ := VertexPin.OwnedIncidentTriangle G v → Twist)
    (T.relativeTwistOperator p hn (Q.left.incidentTriangle v Q.left_mem))
  rw [Q.ker_owned_relativeTwist hG p hp] at h₂
  omega

/-- Every common-pin equation in a two-body family is either zero or
the same relative evaluation. This identifies the actual pin rank. -/
theorem TwoBodyPin.ker_owned_commonPin
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (hG : K4Covered G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (q : Vec3) :
    let T := VertexPin.ownedIncidentTetrahedra G v hG
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
    (T.commonPinAt p hn (Q.left.incidentTriangle v Q.left_mem) q).ker =
      ((evaluateTwist q).comp (Q.relativeTwist p hp)).ker := by
  intro T hn
  ext u
  constructor
  · intro hu
    have h := congrFun (LinearMap.mem_ker.mp hu) (Q.right.incidentTriangle v Q.right_mem)
    change evaluateTwist q
      (T.bodyTwist p hn (Q.right.incidentTriangle v Q.right_mem) u -
        T.bodyTwist p hn (Q.left.incidentTriangle v Q.left_mem) u) = 0 at h
    rw [owned_bodyTwist_eq_deletedBodyTwist hG p hp
      (Q.right.incidentTriangle v Q.right_mem) u,
      owned_bodyTwist_eq_deletedBodyTwist hG p hp
        (Q.left.incidentTriangle v Q.left_mem) u] at h
    exact h
  · intro hu
    have h := LinearMap.mem_ker.mp hu
    rw [LinearMap.mem_ker]
    funext b
    change evaluateTwist q
      (T.bodyTwist p hn b u -
        T.bodyTwist p hn (Q.left.incidentTriangle v Q.left_mem) u) = 0
    rw [owned_bodyTwist_eq_deletedBodyTwist hG p hp b u,
      owned_bodyTwist_eq_deletedBodyTwist hG p hp
        (Q.left.incidentTriangle v Q.left_mem) u]
    change evaluateTwist q
      (deletedBodyTwist G v ⟨b.owner, b.property.1⟩ p hp u -
        deletedBodyTwist G v Q.left p hp u) = 0
    rcases Q.exhaustive ⟨b.owner, b.property.1⟩ b.property.2.1 with hb | hb
    · rw [hb, sub_self, map_zero]
    · rw [hb]
      exact h

theorem TwoBodyPin.evaluation_rank_eq_owned
    {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) (hG : K4Covered G)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (q : Vec3) :
    let T := VertexPin.ownedIncidentTetrahedra G v hG
    let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
    Module.finrank ℝ (restrictEvaluation (Q.relativeTwist p hp).range q).range =
      Module.finrank ℝ
        (T.commonPinAt p hn (Q.left.incidentTriangle v Q.left_mem) q).range := by
  intro T hn
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := VertexPin.DeletedMotions G p v) (V₂ := Vec3)
    ((evaluateTwist q).comp (Q.relativeTwist p hp))
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := VertexPin.DeletedMotions G p v)
    (V₂ := VertexPin.OwnedIncidentTriangle G v → Vec3)
    (T.commonPinAt p hn (Q.left.incidentTriangle v Q.left_mem) q)
  rw [Q.ker_owned_commonPin hG p hp q] at h₂
  have hr : ((evaluateTwist q).comp (Q.relativeTwist p hp)).range =
      (restrictEvaluation (Q.relativeTwist p hp).range q).range := by
    simp [restrictEvaluation, LinearMap.range_comp]
  rw [hr] at h₁
  omega

/-- The deleted relative image of a soft two-body pin has dimension
three, proved from the original graph ranks and Proposition 3.5. -/
theorem TwoBodyPin.relativeTwist_finrank_eq_three
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5) :
    Module.finrank ℝ (Q.relativeTwist p hp).range = 3 := by
  let T := VertexPin.ownedIncidentTetrahedra M.graph v M.covered
  have h := T.minimalCounterexample_relativeTwist_dimension
    M v p hgen hp (Q.left.incidentTriangle v Q.left_mem)
  rw [← Q.relativeTwist_rank_eq_owned M.covered p hp,
    M.flexibility_eq_one, hδ] at h
  omega

theorem TwoBodyPin.relativeTwist_singular
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5) :
    SingularPinSpace (Q.relativeTwist p hp).range := by
  let T := VertexPin.ownedIncidentTetrahedra M.graph v M.covered
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p hp T
  have h := T.commonPin_rank_le_of_deletionDrop p hgen hn ht
    (Q.left.incidentTriangle v Q.left_mem) 2 (by omega)
  intro q
  rw [Q.evaluation_rank_eq_owned M.covered p hp q]
  exact h q

/-- The projective center in Lemma 3.6 is obtained for the literal
deleted graph motions, including the possible center at infinity. -/
theorem TwoBodyPin.relativeTwist_unique_projective_center
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5) :
    ∃ q : HomogeneousPoint, q ≠ 0 ∧
      (Q.relativeTwist p hp).range = homogeneousCenterSpace q ∧
      ∀ r : HomogeneousPoint, r ≠ 0 →
        (Q.relativeTwist p hp).range = homogeneousCenterSpace r →
        ∃ c : ℝ, c ≠ 0 ∧ c • q = r := by
  apply singularPinSpace_unique_projective_center
    (Q.relativeTwist p hp).range (Q.relativeTwist_singular M p hgen hp hδ)
  exact (Q.relativeTwist_finrank_eq_three M p hgen hp hδ).ge

/-- Reintroducing the actual vertex imposes exactly two conditions. -/
theorem TwoBodyPin.evaluation_rank_eq_two
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5) :
    Module.finrank ℝ (restrictEvaluation (Q.relativeTwist p hp).range (p v)).range = 2 := by
  let T := VertexPin.ownedIncidentTetrahedra M.graph v M.covered
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p hp T
  have h := T.rigidityRank_deletion_identity p hn ht
    (Q.left.incidentTriangle v Q.left_mem)
  have hsame : T.commonPinOperator p hn (Q.left.incidentTriangle v Q.left_mem) =
      T.commonPinAt p hn (Q.left.incidentTriangle v Q.left_mem) (p v) := rfl
  rw [hsame, hgen M.graph,
    VertexPin.generic_deletedPlacement p hgen v (VertexPin.deletedGraph M.graph v),
    ← Q.evaluation_rank_eq_owned M.covered p hp (p v)] at h
  unfold VertexPin.deletionRankDrop at hδ
  omega

/-- The finite virtual center cannot be the deleted pin itself. -/
theorem TwoBodyPin.pin_ne_center
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5)
    (a : Vec3) (hcenter : (Q.relativeTwist p hp).range = finiteCenterSpace a) :
    p v ≠ a := by
  intro hpa
  have hzero : restrictEvaluation (Q.relativeTwist p hp).range (p v) = 0 := by
    apply LinearMap.ext
    intro X
    have hm : X.val ∈ finiteCenterSpace a := by rw [← hcenter]; exact X.property
    change evaluateTwist (p v) X.val = 0
    rw [hpa]
    exact hm
  have h := Q.evaluation_rank_eq_two M p hgen hp hδ
  rw [hzero, LinearMap.range_zero, finrank_bot] at h
  norm_num at h

/-- The homogeneous axis vector is nonzero for every soft pin, including
the infinite-center case. Its vanishing would identify the virtual
center with the pin and make the observed pin rank zero. -/
theorem TwoBodyPin.homogeneous_axis_ne_zero
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5)
    (q : HomogeneousPoint) (hq : q ≠ 0)
    (hcenter : (Q.relativeTwist p hp).range = homogeneousCenterSpace q) :
    q.2 • p v - q.1 ≠ 0 := by
  intro hz
  have hqa : q.2 • p v = q.1 := sub_eq_zero.mp hz
  have hc : q.2 ≠ 0 := by
    intro hc
    have ha : q.1 = 0 := by simpa only [hc, zero_smul] using hqa.symm
    exact hq (Prod.ext ha hc)
  have hn : q.2⁻¹ • q.1 = p v := by
    rw [← hqa, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hf : (Q.relativeTwist p hp).range = finiteCenterSpace (p v) := by
    rw [hcenter, homogeneousCenterSpace_normalize q hc, hn]
  exact Q.pin_ne_center M p hgen hp hδ (p v) hf rfl

/-- Actual compatible body forces lie along the homogeneous center axis.
This is the force part of Lemma 3.6 uniformly in all projective charts. -/
theorem TwoBodyPin.load_mem_homogeneous_axis
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5)
    (q : HomogeneousPoint) (hq : q ≠ 0)
    (hcenter : (Q.relativeTwist p hp).range = homogeneousCenterSpace q)
    (F : compatibleBodyLoads M.graph p Finset.univ) :
    Q.loadProjection p F ∈ Submodule.span ℝ {q.2 • p v - q.1} := by
  apply force_annihilates_homogeneousCenter_axis q (p v) (Q.loadProjection p F)
    (Q.homogeneous_axis_ne_zero M p hgen hp hδ q hq hcenter)
  intro X
  have hX : X.val ∈ (Q.relativeTwist p hp).range := by rw [hcenter]; exact X.property
  obtain ⟨u, hu⟩ := hX
  rw [← hu]
  exact Q.load_annihilates_relativeTwist p hp F u

/-- Full projective axis data for a literal soft point pin. The load
direction is nonzero, every compatible load has that direction, and no
other incident-body vertex lies on its line. -/
theorem TwoBodyPin.exists_nonzero_force_axis
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5) :
    ∃ d : Vec3, d ≠ 0 ∧
      (∀ F : compatibleBodyLoads M.graph p Finset.univ,
        Q.loadProjection p F ∈ Submodule.span ℝ {d}) ∧
      ∀ w ∈ Q.left.val ∪ Q.right.val, w ≠ v →
        p w - p v ∉ Submodule.span ℝ {d} := by
  obtain ⟨q, hq, hcenter, _⟩ :=
    Q.relativeTwist_unique_projective_center M p hgen hp hδ
  refine ⟨q.2 • p v - q.1,
    Q.homogeneous_axis_ne_zero M p hgen hp hδ q hq hcenter, ?_, ?_⟩
  · exact Q.load_mem_homogeneous_axis M p hgen hp hδ q hq hcenter
  · exact Q.homogeneous_axis_avoids_other_body_vertices M hinter p hgen hp q hcenter

/-- A nonzero force at a soft point pin cannot lie along any actual
edge of either incident body. This is the geometric input ensuring
that a tetrahedral star uses at least two edge coefficients. -/
theorem TwoBodyPin.nonzero_load_not_neighbor_line
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5)
    (F : compatibleBodyLoads M.graph p Finset.univ)
    (hF : Q.loadProjection p F ≠ 0)
    (w : V) (hw : w ∈ Q.left.val ∪ Q.right.val) (hwv : w ≠ v) :
    Q.loadProjection p F ∉ Submodule.span ℝ {p v - p w} := by
  obtain ⟨d,_,hload,haxis⟩ := Q.exists_nonzero_force_axis M hinter p hgen hp hδ
  apply nonzero_force_not_on_other_line d (p v - p w) (Q.loadProjection p F) hF (hload F)
  intro hwline
  apply haxis w hw hwv
  simpa only [neg_sub] using (Submodule.span ℝ {d}).neg_mem hwline

/-- Both the axis and the exclusion of all actual incident-body
vertices are now consequences of the graph, in the finite chart. -/
theorem TwoBodyPin.finite_center_loads_and_exclusion
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hinter : Q.left.val ∩ Q.right.val = {v})
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hδ : VertexPin.deletionRankDrop M.graph v = 5)
    (a : Vec3) (hcenter : (Q.relativeTwist p hp).range = finiteCenterSpace a) :
    (∀ w ∈ Q.left.val ∪ Q.right.val, a ≠ p w) ∧
      ∀ F : compatibleBodyLoads M.graph p Finset.univ,
        ∃ c : ℝ, c • (p v - a) = Q.loadProjection p F := by
  have hpa := Q.pin_ne_center M p hgen hp hδ a hcenter
  constructor
  · intro w hw
    by_cases hwv : w = v
    · subst w
      exact hpa.symm
    · exact Q.center_ne_other_body_vertex M hinter p hgen hp a hcenter w hw hwv
  · intro F
    exact Submodule.mem_span_singleton.mp (Q.load_mem_center_axis p hp a hpa hcenter F)

end BodyLoads
end Papers.Rigidity

end
end
end BundleSource0002

section BundleSource0003
/- Source: Papers/RigidityBodyScalarRank.lean -/








@[expose] public section

/-!
# Actual scalar rank constraints from body equilibrium

The scalar coordinates are those of the actual stress space. After
hinge normalization, a body with no hypervertices is loaded only at its
soft point pins, so its scalar image lies in the kernel of its literal
force/moment synthesis map. With a sole hypervertex, moments about that
vertex supply a nonzero constraint. These are the rank upper bounds
used for the body budgets in Section 7.3.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin Matrix
open scoped Classical Matrix BigOperators

variable {V : Type} [Fintype V]

/-- A body's actual soft ports, indexed by original vertex labels. -/
abbrev BodySoftPort {G : SimpleGraph V} (C : Body G) :=
  {v : V // v ∈ C.val ∧ IsSoftPointPin G v}

def BodySoftPort.soft {G : SimpleGraph V} {C : Body G} (v : BodySoftPort C) :
    SoftPointPin G := ⟨v.val,v.property.2⟩

theorem card_bodySoftPort {G : SimpleGraph V} (C : Body G) :
    Fintype.card (BodySoftPort C) = (C.val.filter (IsSoftPointPin G)).card := by
  change Fintype.card {v : V // v ∈ C.val ∧ IsSoftPointPin G v} = _
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- Orient each canonical soft axis as the force on this particular
body; the opposite incident body receives the opposite axis. -/
def SoftScalarSystem.bodyAxis (L : SoftScalarSystem M p)
    (C : Body M.graph) (v : BodySoftPort C) : Vec3 :=
  if C = v.soft.pin.left then L.axis v.soft else -L.axis v.soft

theorem SoftScalarSystem.bodyAxis_ne_zero
    (L : SoftScalarSystem M p) (C : Body M.graph) (v : BodySoftPort C) :
    L.bodyAxis C v ≠ 0 := by
  unfold SoftScalarSystem.bodyAxis
  split_ifs
  · exact L.axis_ne_zero v.soft
  · exact neg_ne_zero.mpr (L.axis_ne_zero v.soft)

def SoftScalarSystem.bodyScalarMap (L : SoftScalarSystem M p) (C : Body M.graph) :
    StressSpace (maskedGraph M.graph Finset.univ) p →ₗ[ℝ] (BodySoftPort C → ℝ) :=
  LinearMap.pi fun v => L.scalar v.soft

def SoftScalarSystem.bodyScalarRank (L : SoftScalarSystem M p) (C : Body M.graph) : ℕ :=
  Module.finrank ℝ (L.bodyScalarMap C).range

/-- The body rank is the dimension of the original scalar functionals,
not the number of ports or a replacement independent coordinate set. -/
theorem SoftScalarSystem.bodyScalarRank_eq_span
    (L : SoftScalarSystem M p) (C : Body M.graph) :
    L.bodyScalarRank C =
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : BodySoftPort C => L.scalar v.soft)) := by
  have heq : (L.bodyScalarMap C).dualMap ∘ (Pi.basisFun ℝ (BodySoftPort C)).dualBasis =
      fun v => L.scalar v.soft := by
    funext v
    apply LinearMap.ext
    intro s
    simp [SoftScalarSystem.bodyScalarMap,Module.Basis.dualBasis_apply]
  have hspan := LinearMap.range_dualMap_eq_span_image_dualBasis
    (Pi.basisFun ℝ (BodySoftPort C)) (L.bodyScalarMap C)
  rw [heq] at hspan
  change Module.finrank ℝ (L.bodyScalarMap C).range = _
  rw [← hspan,LinearMap.finrank_range_dualMap_eq_finrank_range]

theorem SoftScalarSystem.largeRank_eq_bodyScalarRank
    (L : SoftScalarSystem M p) (C : LargeBody M.graph) :
    L.largeRank C = L.bodyScalarRank C.val := by
  have hset : L.scalar '' (L.seed (Sum.inr C) : Set (SoftPointPin M.graph)) =
      Set.range (fun v : BodySoftPort C.val => L.scalar v.soft) := by
    ext f
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hvC : v.val ∈ C.val.val := (Finset.mem_filter.mp hv).2
      exact ⟨⟨v.val,hvC,v.property⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact ⟨v.soft,Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.property.1⟩,rfl⟩
  change Module.finrank ℝ
    (Submodule.span ℝ (L.scalar '' (L.seed (Sum.inr C) : Set (SoftPointPin M.graph)))) = _
  exact (congrArg (fun S : Set (Module.Dual ℝ
      (StressSpace (maskedGraph M.graph Finset.univ) p)) =>
        Module.finrank ℝ (Submodule.span ℝ S)) hset).trans
    (L.bodyScalarRank_eq_span C.val).symm

theorem SoftScalarSystem.bodyScalarRank_le_card
    (L : SoftScalarSystem M p) (C : Body M.graph) :
    L.bodyScalarRank C ≤ Fintype.card (BodySoftPort C) := by
  have h := Submodule.finrank_le (L.bodyScalarMap C).range
  simpa only [SoftScalarSystem.bodyScalarRank,Module.finrank_fintype_fun_eq_card] using h

/-- Normalize an actual stress lift while retaining every original
soft scalar. The chosen normalization need not depend linearly on the
stress; the eventual equilibrium identities hold for every stress. -/
theorem SoftScalarSystem.exists_normalized_load
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    ∃ A : compatibleBodyLoads M.graph p Finset.univ,
      (∀ (v : V) (Q : TwoBodyPin M.graph v) (_ : Q.Hinge),
        ∀ C : Body M.graph, (A.val C).val v = 0) ∧
      ∀ v : SoftPointPin M.graph,
        (A.val v.pin.left).val v.val = L.scalar v s • L.axis v := by
  obtain ⟨a,ha⟩ := copiedToStress_surjective M.graph M.covered p Finset.univ s
  obtain ⟨A,_,hhinge,hpoint⟩ := hinge_normalization_preserves_point_loads M p hgen hp
    (copiedToLoads M.graph p Finset.univ a)
  refine ⟨A,hhinge,?_⟩
  intro v
  rw [hpoint v.val v.pin v.isPoint v.pin.left]
  change v.pin.loadProjection p (copiedToLoads M.graph p Finset.univ a) = _
  rw [← v.pin.pointForceOnWholePrefix_copied v.isPoint M.covered p a,ha,L.force_eq]

theorem SoftScalarSystem.normalized_load_at_soft
    (L : SoftScalarSystem M p)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (A : compatibleBodyLoads M.graph p Finset.univ)
    (hsoft : ∀ v : SoftPointPin M.graph,
      (A.val v.pin.left).val v.val = L.scalar v s • L.axis v)
    (C : Body M.graph) (v : BodySoftPort C) :
    (A.val C).val v.val = L.scalar v.soft s • L.bodyAxis C v := by
  rcases v.soft.pin.exhaustive C v.property.1 with hC | hC
  · rw [SoftScalarSystem.bodyAxis,if_pos hC]
    exact (congrArg (fun D : Body M.graph => (A.val D).val v.val) hC).trans (hsoft v.soft)
  · have hne : C ≠ v.soft.pin.left := fun h => v.soft.pin.distinct (h.symm.trans hC)
    rw [SoftScalarSystem.bodyAxis,if_neg hne,smul_neg]
    calc
      (A.val C).val v.val = (A.val v.soft.pin.right).val v.val :=
        congrArg (fun D : Body M.graph => (A.val D).val v.val) hC
      _ = -(A.val v.soft.pin.left).val v.val := v.soft.pin.load_right_eq_neg_left p A
      _ = -(L.scalar v.soft s • L.axis v.soft) := congrArg Neg.neg (hsoft v.soft)

/-- The canonical axis chosen by any actual scalar system also avoids
every other actual vertex in either incident body. -/
theorem SoftScalarSystem.axis_avoids_body_vertex
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (v : SoftPointPin M.graph) (C : Body M.graph) (hv : v.val ∈ C.val)
    (w : V) (hw : w ∈ C.val) (hne : v.val ≠ w) :
    (p v.val - p w) ⨯₃ L.axis v ≠ 0 := by
  obtain ⟨s,hs⟩ := exists_normalized_linear_functional (L.scalar v) (L.scalar_ne_zero v)
  obtain ⟨a,ha⟩ := copiedToStress_surjective M.graph M.covered p Finset.univ s
  let F := copiedToLoads M.graph p Finset.univ a
  have hforce : v.pin.loadProjection p F = L.axis v := by
    rw [← v.pin.pointForceOnWholePrefix_copied v.isPoint M.covered p a,ha,L.force_eq,hs,one_smul]
  have hwunion : w ∈ v.pin.left.val ∪ v.pin.right.val := by
    rcases v.pin.exhaustive C hv with hC | hC
    · exact Finset.mem_union_left _ (hC ▸ hw)
    · exact Finset.mem_union_right _ (hC ▸ hw)
  have hnot := v.pin.nonzero_load_not_neighbor_line M v.isPoint p hgen hp v.drop_eq_five
    F (by rw [hforce]; exact L.axis_ne_zero v) w hwunion hne.symm
  rw [hforce] at hnot
  have hd : p v.val - p w ≠ 0 := by
    intro hz
    exact hne (GeneralPosition.InGeneralPosition.injective p hp (sub_eq_zero.mp hz))
  intro hz
  apply hnot
  rw [← ker_crossProduct_eq_span (p v.val - p w) hd,LinearMap.mem_ker]
  exact hz

theorem SoftScalarSystem.bodyAxis_avoids_body_vertex
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (C : Body M.graph) (v : BodySoftPort C) (w : V) (hw : w ∈ C.val) (hne : v.val ≠ w) :
    (p v.val - p w) ⨯₃ L.bodyAxis C v ≠ 0 := by
  have h := L.axis_avoids_body_vertex hgen hp v.soft C v.property.1 w hw hne
  change (p v.val - p w) ⨯₃ L.axis v.soft ≠ 0 at h
  unfold SoftScalarSystem.bodyAxis
  split_ifs
  · exact h
  · simpa only [map_neg,neg_ne_zero] using h

def SoftScalarSystem.bodyWrenchMap (L : SoftScalarSystem M p) (C : Body M.graph) :
    (BodySoftPort C → ℝ) →ₗ[ℝ] (Vec3 × Vec3) :=
  Fintype.linearCombination ℝ (fun v => WrenchRank.wrench (p v.val) (L.bodyAxis C v))

theorem SoftScalarSystem.bodyWrenchMap_range
    (L : SoftScalarSystem M p) (C : Body M.graph) :
    (L.bodyWrenchMap C).range =
      WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C) := by
  exact Fintype.range_linearCombination ℝ _

/-- The geometric wrench bound is applied to the actual oriented soft
axes. Every hypothesis comes from the original placement and the
ambient-closure axis exclusion. -/
theorem SoftScalarSystem.body_wrench_rank_lower_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph) :
    min (Fintype.card (BodySoftPort C)) 2 +
        (if 4 ≤ Fintype.card (BodySoftPort C) then 1 else 0) ≤
      Module.finrank ℝ
        (WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C)) := by
  apply WrenchRank.wrench_rank_lower_bound
  · intro f
    exact hp (3 : Fin 4) (f.trans ⟨Subtype.val,Subtype.val_injective⟩)
  · exact L.bodyAxis_ne_zero C
  · intro v w hvw
    exact L.bodyAxis_avoids_body_vertex hgen hp C v w.val w.property.1
      (fun h => hvw (Subtype.ext h))

theorem sum_bodySoftPort_eq_of_zero_off
    {G : SimpleGraph V} (C : Body G) {E : Type*} [AddCommMonoid E]
    (f : V → E) (hf : ∀ w, ¬ (w ∈ C.val ∧ IsSoftPointPin G w) → f w = 0) :
    (∑ v : BodySoftPort C, f v.val) = ∑ w : V, f w := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun w => w ∈ C.val ∧ IsSoftPointPin G w) f
  have hz : (∑ w : {w : V // ¬ (w ∈ C.val ∧ IsSoftPointPin G w)}, f w.val) = 0 := by
    exact Finset.sum_eq_zero fun w _ => hf w.val w.property
  rw [hz,add_zero] at h
  exact h

/-- Force and moment equilibrium for the actual scalar values of every
stress, after the proved hinge adjustment. -/
theorem SoftScalarSystem.body_wrench_equilibrium
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (hhyper : ∀ w ∈ C.val, ¬ IsHypervertex M.graph w)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    L.bodyWrenchMap C (L.bodyScalarMap C s) = 0 := by
  obtain ⟨A,hhinge,hsoft⟩ := L.exists_normalized_load hgen hp s
  have hzero (w : V) (hw : ¬ (w ∈ C.val ∧ IsSoftPointPin M.graph w)) :
      (A.val C).val w = 0 := by
    by_cases hwC : w ∈ C.val
    · exact normalized_load_zero_at_nonsoft_nonhyper M p hgen hp A hhinge w
        (fun h => hw ⟨hwC,h⟩) (hhyper w hwC) C
    · exact compatible_load_zero_outside_body M.graph p A C w hwC
  have hb := (mem_balancedLoads_iff p (A.val C).val).mp (A.val C).property.1
  change (∑ v : BodySoftPort C,
    L.scalar v.soft s • WrenchRank.wrench (p v.val) (L.bodyAxis C v)) = 0
  calc
    (∑ v : BodySoftPort C,
        L.scalar v.soft s • WrenchRank.wrench (p v.val) (L.bodyAxis C v)) =
      ∑ v : BodySoftPort C, ((A.val C).val v.val,
        p v.val ⨯₃ (A.val C).val v.val) := by
          apply Finset.sum_congr rfl
          intro v _
          simp only [L.normalized_load_at_soft s A hsoft C v,
            WrenchRank.wrench,Prod.smul_mk,map_smul]
    _ = ∑ w : V, ((A.val C).val w,p w ⨯₃ (A.val C).val w) := by
      apply sum_bodySoftPort_eq_of_zero_off C (E := Vec3 × Vec3)
        (fun w : V => ((A.val C).val w,p w ⨯₃ (A.val C).val w))
      intro w hw
      simp only [hzero w hw,map_zero] <;> rfl
    _ = 0 := by rw [← prod_mk_sum,hb.1,hb.2] <;> rfl

/-- The rank inequality `r_C + k ≤ p` in the case with no hypervertex.
Here `k` is the actual force/moment column rank and `p` is the actual
number of soft ports. -/
theorem SoftScalarSystem.bodyScalarRank_add_wrenchRank_le_card
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (hhyper : ∀ w ∈ C.val, ¬ IsHypervertex M.graph w) :
    L.bodyScalarRank C + Module.finrank ℝ
        (WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C)) ≤
      Fintype.card (BodySoftPort C) := by
  have hker : (L.bodyScalarMap C).range ≤ (L.bodyWrenchMap C).ker := by
    rintro x ⟨s,rfl⟩
    exact L.body_wrench_equilibrium hgen hp C hhyper s
  have hle := Submodule.finrank_mono hker
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := BodySoftPort C → ℝ) (V₂ := Vec3 × Vec3)
    (L.bodyWrenchMap C)
  rw [L.bodyWrenchMap_range,Module.finrank_fintype_fun_eq_card] at hdim
  unfold SoftScalarSystem.bodyScalarRank
  omega

theorem balanced_load_moment_about
    (p : Placement V 3) (F : V → Vec3) (hF : F ∈ balancedLoads p) (a : Vec3) :
    (∑ w : V, (p w - a) ⨯₃ F w) = 0 := by
  obtain ⟨hforce,hmoment⟩ := (mem_balancedLoads_iff p F).mp hF
  calc
    (∑ w : V, (p w - a) ⨯₃ F w) =
      (∑ w : V, p w ⨯₃ F w) - a ⨯₃ (∑ w : V, F w) := by
        simp only [map_sub,LinearMap.sub_apply,Finset.sum_sub_distrib,map_sum]
    _ = 0 := by rw [hforce,hmoment,map_zero,sub_self]

def SoftScalarSystem.bodyMomentMap (L : SoftScalarSystem M p)
    (C : Body M.graph) (h : V) : (BodySoftPort C → ℝ) →ₗ[ℝ] Vec3 :=
  Fintype.linearCombination ℝ (fun v => (p v.val - p h) ⨯₃ L.bodyAxis C v)

/-- Taking moments about the sole hypervertex eliminates its unknown
load and leaves a homogeneous relation on the actual soft scalars. -/
theorem SoftScalarSystem.body_moment_equilibrium
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph) (h : V)
    (honly : ∀ w ∈ C.val, IsHypervertex M.graph w → w = h)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    L.bodyMomentMap C h (L.bodyScalarMap C s) = 0 := by
  obtain ⟨A,hhinge,hsoft⟩ := L.exists_normalized_load hgen hp s
  have hzero (w : V) (hw : ¬ (w ∈ C.val ∧ IsSoftPointPin M.graph w)) :
      (p w - p h) ⨯₃ (A.val C).val w = 0 := by
    by_cases hwC : w ∈ C.val
    · by_cases hwhyper : IsHypervertex M.graph w
      · rw [honly w hwC hwhyper,sub_self]
        simp
      · rw [normalized_load_zero_at_nonsoft_nonhyper M p hgen hp A hhinge w
          (fun h => hw ⟨hwC,h⟩) hwhyper C,map_zero]
    · rw [compatible_load_zero_outside_body M.graph p A C w hwC,map_zero]
  change (∑ v : BodySoftPort C,
    L.scalar v.soft s • ((p v.val - p h) ⨯₃ L.bodyAxis C v)) = 0
  calc
    (∑ v : BodySoftPort C,
        L.scalar v.soft s • ((p v.val - p h) ⨯₃ L.bodyAxis C v)) =
      ∑ v : BodySoftPort C, (p v.val - p h) ⨯₃ (A.val C).val v.val := by
          apply Finset.sum_congr rfl
          intro v _
          rw [L.normalized_load_at_soft s A hsoft C v,map_smul]
    _ = ∑ w : V, (p w - p h) ⨯₃ (A.val C).val w :=
      sum_bodySoftPort_eq_of_zero_off C _ hzero
    _ = 0 := balanced_load_moment_about p (A.val C).val (A.val C).property.1 (p h)

/-- The sole-hypervertex moment constraint is nonzero at every soft
port, by the actual soft-axis exclusion proved from ambient closure. -/
theorem SoftScalarSystem.bodyMomentMap_rank_pos
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (h : V) (hhC : h ∈ C.val) (hh : IsHypervertex M.graph h)
    (hports : 0 < Fintype.card (BodySoftPort C)) :
    0 < Module.finrank ℝ (L.bodyMomentMap C h).range := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hports
  have hvh : v.val ≠ h := by
    intro he
    exact v.soft.not_hypervertex (he.symm ▸ hh)
  have hn := L.bodyAxis_avoids_body_vertex hgen hp C v h hhC hvh
  have hm : (p v.val - p h) ⨯₃ L.bodyAxis C v ∈ (L.bodyMomentMap C h).range := by
    refine ⟨Pi.single v 1,?_⟩
    simp [SoftScalarSystem.bodyMomentMap]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨(p v.val - p h) ⨯₃ L.bodyAxis C v,hm⟩,?_⟩
  intro hz
  exact hn (congrArg Subtype.val hz)

/-- The inequality `r_C ≤ p−1` for a body with exactly one hypervertex
and at least one soft port, stated without truncated subtraction. -/
theorem SoftScalarSystem.bodyScalarRank_add_one_le_card
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (h : V) (hhC : h ∈ C.val) (hh : IsHypervertex M.graph h)
    (honly : ∀ w ∈ C.val, IsHypervertex M.graph w → w = h)
    (hports : 0 < Fintype.card (BodySoftPort C)) :
    L.bodyScalarRank C + 1 ≤ Fintype.card (BodySoftPort C) := by
  have hker : (L.bodyScalarMap C).range ≤ (L.bodyMomentMap C h).ker := by
    rintro x ⟨s,rfl⟩
    exact L.body_moment_equilibrium hgen hp C h honly s
  have hle := Submodule.finrank_mono hker
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := BodySoftPort C → ℝ) (V₂ := Vec3)
    (L.bodyMomentMap C h)
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  have hpos := L.bodyMomentMap_rank_pos hgen hp C h hhC hh hports
  unfold SoftScalarSystem.bodyScalarRank
  omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0003

section BundleSource0004
/- Source: Papers/RigidityCorePorts.lean -/




@[expose] public section

/-!
# Literal K5/K4 hinge ports and their exterior pairs

A core port is an actual two-body hinge, with a five-vertex body on
one side and a tetrahedron on the other. Its two exterior vertices are
actual neighbors of the common hinge partner. Distinct ports in one
core have disjoint exterior pairs, by maximality of the actual bodies.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin NeighborhoodBases
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The precise type-B incidence, with an explicit orientation toward
the K5 core. No rank, support, or counting conclusion is assumed. -/
structure CorePort (M : MinimalCounterexample V) (C : Body M.graph) (h v : V) where
  pin : TwoBodyPin M.graph v
  core_eq : pin.left = C
  core_card : C.val.card = 5
  outer_card : pin.right.val.card = 4
  hinge : pin.Hinge
  partner_eq : hinge.partner = h

variable {M : MinimalCounterexample V} {C : Body M.graph} {h v w : V}

def CorePort.outer (P : CorePort M C h v) : Body M.graph := P.pin.right

theorem CorePort.port_ne_partner (P : CorePort M C h v) : v ≠ h := by
  simpa only [P.partner_eq] using P.hinge.distinct

theorem CorePort.port_mem_core (P : CorePort M C h v) : v ∈ C.val :=
  P.core_eq ▸ P.pin.left_mem

theorem CorePort.partner_mem_core (P : CorePort M C h v) : h ∈ C.val := by
  simpa only [P.partner_eq,P.core_eq] using P.hinge.left_mem

theorem CorePort.port_mem_outer (P : CorePort M C h v) : v ∈ P.outer.val := P.pin.right_mem

theorem CorePort.partner_mem_outer (P : CorePort M C h v) : h ∈ P.outer.val := by
  exact Eq.mp (congrArg (fun w : V => w ∈ P.pin.right.val) P.partner_eq)
    P.hinge.right_mem

theorem CorePort.outer_ne_core (P : CorePort M C h v) : P.outer ≠ C := by
  intro heq
  exact P.pin.distinct (P.core_eq.trans heq.symm)

theorem CorePort.intersection (P : CorePort M C h v) : C.val ∩ P.outer.val = {h,v} := by
  have hsub : ({h,v} : Finset V) ⊆ C.val ∩ P.outer.val := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨P.partner_mem_core,P.partner_mem_outer⟩
    · have hxv := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr ⟨P.port_mem_core,P.port_mem_outer⟩
  have hsmall := M.body_intersection_le_two C.val P.outer.val C.property P.outer.property
    (fun h => P.outer_ne_core (Subtype.ext h.symm))
  have hpair : ({h,v} : Finset V).card = 2 := Finset.card_pair P.port_ne_partner.symm
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- The two literal vertices of the outer tetrahedron outside its core. -/
def CorePort.externalPair (P : CorePort M C h v) : Finset V := P.outer.val \ C.val

theorem CorePort.externalPair_card (P : CorePort M C h v) : P.externalPair.card = 2 := by
  have h := Finset.card_sdiff_add_card_inter P.outer.val C.val
  rw [Finset.inter_comm,P.intersection,Finset.card_pair P.port_ne_partner.symm] at h
  change (P.outer.val \ C.val).card = 2
  have hfour : P.outer.val.card = 4 := P.outer_card
  omega

theorem CorePort.externalPair_subset_neighbors (P : CorePort M C h v) :
    P.externalPair ⊆ M.graph.neighborFinset h := by
  intro x hx
  obtain ⟨hxouter,hxcore⟩ := Finset.mem_sdiff.mp hx
  apply (M.graph.mem_neighborFinset h x).mpr
  exact P.outer.property.2.1 P.partner_mem_outer hxouter
    (fun heq => hxcore (heq ▸ P.partner_mem_core))

/-- Every neighbor of a two-body pin belongs to one of its two actual bodies. -/
theorem TwoBodyPin.closedNeighborhood_eq_union
    {G : SimpleGraph V} {x : V} (Q : TwoBodyPin G x) (hG : K4Covered G) :
    closedNeighborhood G x = Q.left.val ∪ Q.right.val := by
  ext y
  constructor
  · intro hy
    rcases (mem_closedNeighborhood G x y).mp hy with rfl | hy
    · exact Finset.mem_union_left _ Q.left_mem
    · obtain ⟨D,hD,hxD,hyD⟩ := hG.edge_in_body hy
      rcases Q.exhaustive ⟨D,hD⟩ hxD with hd | hd
      · exact Finset.mem_union_left _ (congrArg Subtype.val hd ▸ hyD)
      · exact Finset.mem_union_right _ (congrArg Subtype.val hd ▸ hyD)
  · intro hy
    by_cases hxy : y = x
    · exact (mem_closedNeighborhood G x y).mpr (Or.inl hxy)
    apply (mem_closedNeighborhood G x y).mpr
    apply Or.inr
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Q.left.property.2.1 Q.left_mem hy (Ne.symm hxy)
    · exact Q.right.property.2.1 Q.right_mem hy (Ne.symm hxy)

/-- The displayed K5/K4 hinge incidence has precisely degree six. -/
theorem CorePort.degree_eq_six (P : CorePort M C h v) : M.graph.degree v = 6 := by
  have hsum := Finset.card_union_add_card_inter C.val P.outer.val
  have houter : P.outer.val.card = 4 := P.outer_card
  rw [P.intersection,Finset.card_pair P.port_ne_partner.symm,P.core_card,houter] at hsum
  have hclosed := P.pin.closedNeighborhood_eq_union M.covered
  rw [P.core_eq] at hclosed
  change closedNeighborhood M.graph v = C.val ∪ P.outer.val at hclosed
  have hcard := congrArg Finset.card hclosed
  rw [card_closedNeighborhood] at hcard
  omega

/-- Distinct ports of one core cannot share their outer tetrahedron. -/
theorem CorePort.outer_ne_of_port_ne
    (P : CorePort M C h v) (Q : CorePort M C h w) (hvw : v ≠ w) : P.outer ≠ Q.outer := by
  intro heq
  have hwP : w ∈ P.outer.val := heq.symm ▸ Q.port_mem_outer
  have hwint : w ∈ C.val ∩ P.outer.val := Finset.mem_inter.mpr ⟨Q.port_mem_core,hwP⟩
  rw [P.intersection,Finset.mem_insert,Finset.mem_singleton] at hwint
  rcases hwint with hwh | hwv
  · exact Q.port_ne_partner hwh
  · exact hvw hwv.symm

/-- The key boundary geometry of Section 7.4. A common exterior vertex
would form a literal K4 with h and the two core ports, forcing a forbidden
three-vertex intersection of maximal bodies. -/
theorem CorePort.externalPair_disjoint
    (P : CorePort M C h v) (Q : CorePort M C h w) (hvw : v ≠ w) :
    Disjoint P.externalPair Q.externalPair := by
  apply Finset.disjoint_left.mpr
  intro x hxP hxQ
  obtain ⟨hxPbody,hxC⟩ := Finset.mem_sdiff.mp hxP
  obtain ⟨hxQbody,_⟩ := Finset.mem_sdiff.mp hxQ
  let U : Finset V := insert x {h,v,w}
  -- The three core vertices form a triangle. Add the shared exterior
  -- vertex using its three actual bars, avoiding a Cartesian case split.
  have htriangle : M.graph.IsClique (({h,v,w} : Finset V) : Set V) := by
    refine SimpleGraph.IsClique.subset ?_ C.property.2.1
    intro y hy
    change y ∈ ({h,v,w} : Finset V) at hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact P.partner_mem_core
    · exact P.port_mem_core
    · exact Q.port_mem_core
  have hxadj : ∀ y ∈ (({h,v,w} : Finset V) : Set V), x ≠ y → M.graph.Adj x y := by
    intro y hy hxy
    change y ∈ ({h,v,w} : Finset V) at hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact P.outer.property.2.1 hxPbody P.partner_mem_outer hxy
    · exact P.outer.property.2.1 hxPbody P.port_mem_outer hxy
    · exact Q.outer.property.2.1 hxQbody Q.port_mem_outer hxy
  have hU : M.graph.IsClique (U : Set V) := by
    simpa only [U,Finset.coe_insert] using htriangle.insert hxadj
  have hcommon : 3 ≤ (C.val ∩ U).card := three_common_of_members
    P.partner_mem_core P.port_mem_core Q.port_mem_core
    (by simp [U]) (by simp [U]) (by simp [U])
    P.port_ne_partner.symm Q.port_ne_partner.symm hvw
  have hUC := body_absorbs_clique M C.val U C.property hU hcommon
  exact hxC (hUC (by simp [U]))

/-- Distinct ports contribute exactly two distinct exterior neighbors
each. This is the actual `2b` count in the last cases of Section 7.4. -/
theorem externalPairs_card
    (M : MinimalCounterexample V) (C : Body M.graph) (h : V)
    (P : Finset V) (Q : ∀ v : P, CorePort M C h v.val) :
    (Finset.univ.biUnion (fun v : P => (Q v).externalPair)).card = 2 * P.card := by
  rw [Finset.card_biUnion]
  · simp only [CorePort.externalPair_card,Finset.sum_const,Finset.card_univ,
      Fintype.card_coe,nsmul_eq_mul,Nat.cast_id,mul_comm]
  · intro v _ w _ hvw
    exact (Q v).externalPair_disjoint (Q w)
      (fun h => hvw (Subtype.ext h))

/-- The defining vertex-connectivity condition rules out any smaller
separator whose two surviving sides are explicitly exhibited. -/
theorem separator_card_ge
    {G : SimpleGraph V} {k : ℕ} (hG : VertexConnected G k)
    (A B : Finset V) (hA : A.Nonempty) (hAB : Disjoint A B)
    (houtside : ∃ z, z ∉ A ∪ B)
    (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y ∈ B) : k ≤ B.card := by
  by_contra hsmall
  have hBk : B.card < k := by omega
  obtain ⟨x,hx⟩ := hA
  obtain ⟨z,hz⟩ := houtside
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hx h
  have hzB : z ∉ B := fun h => hz (Finset.mem_union_right _ h)
  let x' : {w : V // w ∉ B} := ⟨x,hxB⟩
  let z' : {w : V // w ∉ B} := ⟨z,hzB⟩
  have hstep (a b : {w : V // w ∉ B}) (ha : a.val ∈ A)
      (hab : (G.induce ((B : Set V)ᶜ)).Adj a b) : b.val ∈ A := by
    rcases hclosed a.val ha b.val hab with h | h
    · exact h
    · exact False.elim (b.property h)
  have hwalk : ∀ {a b : {w : V // w ∉ B}},
      (G.induce ((B : Set V)ᶜ)).Walk a b → a.val ∈ A → b.val ∈ A := by
    intro a b walk
    induction walk with
    | nil => exact id
    | @cons a b c hab walk ih => exact fun ha => ih (hstep a b ha hab)
  obtain ⟨walk⟩ := hG.2 B hBk x' z'
  exact hz (Finset.mem_union_left _ (hwalk walk hx))

/-- In a six-connected flexible graph, the other endpoint of a K5/K4
hinge port is an actual hypervertex. If it had only two bodies, their
five external vertices would separate the hinge edge from another
vertex of the graph. -/
theorem CorePort.partner_isHypervertex (P : CorePort M C h v) : IsHypervertex M.graph h := by
  by_contra hnot
  obtain ⟨Q⟩ := nonempty_twoBodyPin_of_not_hypervertex M h hnot
  have hexhaustive (D : Body M.graph) (hhD : h ∈ D.val) : D = C ∨ D = P.outer := by
    have hC := Q.exhaustive C P.partner_mem_core
    have hO := Q.exhaustive P.outer P.partner_mem_outer
    rcases hC with hC | hC <;> rcases hO with hO | hO
    · exact False.elim (P.outer_ne_core (hO.trans hC.symm))
    · rcases Q.exhaustive D hhD with hD | hD
      · exact Or.inl (hD.trans hC.symm)
      · exact Or.inr (hD.trans hO.symm)
    · rcases Q.exhaustive D hhD with hD | hD
      · exact Or.inr (hD.trans hO.symm)
      · exact Or.inl (hD.trans hC.symm)
    · exact False.elim (P.outer_ne_core (hO.trans hC.symm))
  let U := C.val ∪ P.outer.val
  let A : Finset V := {v,h}
  let B := U \ A
  have hAU : A ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_union_left _ P.port_mem_core
    · have hxh := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_union_left _ P.partner_mem_core
  have hAcard : A.card = 2 := Finset.card_pair P.port_ne_partner
  have hUcard : U.card = 7 := by
    have hsum := Finset.card_union_add_card_inter C.val P.outer.val
    have houter : P.outer.val.card = 4 := P.outer_card
    rw [P.intersection,Finset.card_pair P.port_ne_partner.symm,P.core_card,houter] at hsum
    change (C.val ∪ P.outer.val).card = 7
    omega
  have hBcard : B.card = 5 := by
    change (U \ A).card = 5
    rw [Finset.card_sdiff_of_subset hAU,hUcard,hAcard]
  have hunion : A ∪ B = U := by
    ext x
    simp only [B,Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx,_⟩)
      · exact hAU hx
      · exact hx
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx,hxA⟩
  have houtside : ∃ z, z ∉ A ∪ B := by
    rw [hunion]
    by_contra hnone
    push_neg at hnone
    have hsub : (Finset.univ : Finset V) ⊆ U := fun z _ => hnone z
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ,hUcard] at hcard
    have hlarge := M.eight_le_card
    omega
  have hneighbor (x : V) (hx : x ∈ A) (y : V) (hxy : M.graph.Adj x y) : y ∈ U := by
    rcases Finset.mem_insert.mp hx with hxv | hx
    · subst x
      have hy := (mem_closedNeighborhood M.graph v y).mpr (Or.inr hxy)
      rw [P.pin.closedNeighborhood_eq_union M.covered,P.core_eq] at hy
      exact hy
    · have hxh := Finset.mem_singleton.mp hx
      subst x
      obtain ⟨D,hD,hhD,hyD⟩ := M.covered.edge_in_body hxy
      rcases hexhaustive ⟨D,hD⟩ hhD with heq | heq
      · exact Finset.mem_union_left _ (congrArg Subtype.val heq ▸ hyD)
      · exact Finset.mem_union_right _ (congrArg Subtype.val heq ▸ hyD)
  have hbound := separator_card_ge M.connected A B (by simp [A])
    (Finset.disjoint_left.mpr (fun x hx hxb => (Finset.mem_sdiff.mp hxb).2 hx))
    houtside (by
      intro x hx y hxy
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hneighbor x hx y hxy,hyA⟩))
  omega

/-- A shared-edge port is never a soft point pin. -/
theorem CorePort.not_softPointPin (P : CorePort M C h v) : ¬ IsSoftPointPin M.graph v := by
  rintro ⟨Q,hQ,_⟩
  have hh := hQ.no_shared_edge P.pin.left P.pin.right P.pin.distinct
    P.pin.left_mem P.pin.right_mem h
    (by simpa only [P.partner_eq] using P.hinge.left_mem)
    (by simpa only [P.partner_eq] using P.hinge.right_mem)
  exact P.port_ne_partner hh.symm

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0004

section BundleSource0005
/- Source: Papers/RigidityCoreSelection.lean -/



@[expose] public section

/-!
# Literal body-incidence counts and selected K5 cores

All counts in the final account refer to vertices and maximal bodies of
the original graph. A type-B vertex is witnessed by an actual K5/K4
hinge port, and a selected core contains a soft point pin or such a port.
The four classes used in the body budget form a proved partition.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def bodySoftVertices (M : MinimalCounterexample V) (C : Body M.graph) : Finset V :=
  C.val.filter (IsSoftPointPin M.graph)

def bodyHyperVertices (M : MinimalCounterexample V) (C : Body M.graph) : Finset V :=
  C.val.filter (IsHypervertex M.graph)

def bodyTypeBVertices (M : MinimalCounterexample V) (C : Body M.graph) : Finset V :=
  C.val.filter fun v => ∃ h, Nonempty (CorePort M C h v)

def bodyOtherVertices (M : MinimalCounterexample V) (C : Body M.graph) : Finset V :=
  C.val.filter fun v => ¬ IsSoftPointPin M.graph v ∧
    ¬ (∃ h, Nonempty (CorePort M C h v)) ∧ ¬ IsHypervertex M.graph v

def IsSelectedCore (M : MinimalCounterexample V) (C : Body M.graph) : Prop :=
  C.val.card = 5 ∧ ((bodySoftVertices M C).Nonempty ∨ (bodyTypeBVertices M C).Nonempty)

abbrev SelectedCore (M : MinimalCounterexample V) :=
  {C : Body M.graph // IsSelectedCore M C}

/-- The exact number of selected local K5 modes incident with h. -/
def selectedIncidentCount (M : MinimalCounterexample V) (h : V) : ℕ :=
  (Finset.univ.filter fun C : SelectedCore M => h ∈ C.val.val).card

/-- Cores charged to h in Section 7.4, grouped by their number of
actual type-B ports. The sole hypervertex and absence of soft ports are
literal equalities of vertex sets. -/
def chargedCoreCountAt (M : MinimalCounterexample V) (h : V) (b : ℕ) : ℕ :=
  (Finset.univ.filter fun C : SelectedCore M =>
    bodyHyperVertices M C.val = {h} ∧ bodySoftVertices M C.val = ∅ ∧
      (bodyTypeBVertices M C.val).card = b).card

theorem softPointPin_not_hypervertex (G : SimpleGraph V) (v : V)
    (hv : IsSoftPointPin G v) : ¬ IsHypervertex G v := by
  obtain ⟨Q,hQ,hδ⟩ := hv
  exact Q.not_hypervertex

theorem bodyTypeB_not_soft
    (M : MinimalCounterexample V) (C : Body M.graph) (v : V)
    (hv : ∃ h, Nonempty (CorePort M C h v)) : ¬ IsSoftPointPin M.graph v := by
  obtain ⟨h,⟨P⟩⟩ := hv
  exact P.not_softPointPin

theorem bodyTypeB_not_hyper
    (M : MinimalCounterexample V) (C : Body M.graph) (v : V)
    (hv : ∃ h, Nonempty (CorePort M C h v)) : ¬ IsHypervertex M.graph v := by
  obtain ⟨h,⟨P⟩⟩ := hv
  exact P.pin.not_hypervertex

/-- The four body counts in Section 7.3 add to the original body order. -/
theorem body_vertex_counts_partition
    (M : MinimalCounterexample V) (C : Body M.graph) :
    (bodySoftVertices M C).card + (bodyTypeBVertices M C).card +
      (bodyHyperVertices M C).card + (bodyOtherVertices M C).card = C.val.card := by
  simp only [bodySoftVertices,bodyTypeBVertices,bodyHyperVertices,bodyOtherVertices,
    Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hs : IsSoftPointPin M.graph v
  · have hb : ¬ (∃ h, Nonempty (CorePort M C h v)) :=
      fun h => bodyTypeB_not_soft M C v h hs
    simp [hs,hb,softPointPin_not_hypervertex M.graph v hs]
  · by_cases hb : ∃ h, Nonempty (CorePort M C h v)
    · simp [hs,hb,bodyTypeB_not_hyper M C v hb]
    · by_cases hh : IsHypervertex M.graph v <;> simp [hs,hb,hh]

/-- Every type-B port exposes an actual hypervertex of its core. -/
theorem bodyHyperVertices_nonempty_of_typeB
    (M : MinimalCounterexample V) (C : Body M.graph)
    (hB : (bodyTypeBVertices M C).Nonempty) :
    (bodyHyperVertices M C).Nonempty := by
  obtain ⟨v,hv⟩ := hB
  obtain ⟨h,⟨P⟩⟩ := (Finset.mem_filter.mp hv).2
  exact ⟨h,Finset.mem_filter.mpr ⟨P.partner_mem_core,P.partner_isHypervertex⟩⟩

theorem bodyTypeB_empty_of_no_hypervertices
    (M : MinimalCounterexample V) (C : Body M.graph)
    (hH : (bodyHyperVertices M C).card = 0) : bodyTypeBVertices M C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hpos := Finset.card_pos.mpr
    (bodyHyperVertices_nonempty_of_typeB M C ⟨v,hv⟩)
  omega

theorem bodyTypeB_empty_of_card_ne_five
    (M : MinimalCounterexample V) (C : Body M.graph) (hC : C.val.card ≠ 5) :
    bodyTypeBVertices M C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨h,⟨P⟩⟩ := (Finset.mem_filter.mp hv).2
  exact hC P.core_card

theorem bodyTypeB_port_at_sole_hypervertex
    (M : MinimalCounterexample V) (C : Body M.graph) (h : V)
    (hH : bodyHyperVertices M C = {h}) (v : V) (hv : v ∈ bodyTypeBVertices M C) :
    Nonempty (CorePort M C h v) := by
  obtain ⟨w,⟨P⟩⟩ := (Finset.mem_filter.mp hv).2
  have hw : w ∈ bodyHyperVertices M C :=
    Finset.mem_filter.mpr ⟨P.partner_mem_core,P.partner_isHypervertex⟩
  rw [hH,Finset.mem_singleton] at hw
  subst w
  exact ⟨P⟩

theorem selectedCore_of_soft
    (M : MinimalCounterexample V) (C : Body M.graph) (hC : C.val.card = 5)
    (v : SoftPointPin M.graph) (hv : v.val ∈ C.val) : IsSelectedCore M C :=
  ⟨hC,Or.inl ⟨v.val,Finset.mem_filter.mpr ⟨hv,v.property⟩⟩⟩

theorem selectedCore_of_typeB
    (M : MinimalCounterexample V) (C : Body M.graph) (h v : V)
    (P : CorePort M C h v) : IsSelectedCore M C :=
  ⟨P.core_card,Or.inr ⟨v,Finset.mem_filter.mpr ⟨P.port_mem_core,h,⟨P⟩⟩⟩⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0005

section BundleSource0006
/- Source: Papers/RigidityBudget.lean -/






@[expose] public section

/-!
# Exact arithmetic in the final rigidity count

These are the numerical implications in Sections 3 and 7 of the paper.
Their hypotheses are kept explicit. The graph-theoretic, stress-space and
integrability arguments supplying those hypotheses are separate obligations.
None of these numerical lemmas asserts the principal rigidity theorem.
-/

namespace Papers.Rigidity.Budget

noncomputable def supportedBound (s r : ℝ) : ℝ := r * (r + 1) / (2 * (r + s))

theorem degree_ge_seven_bound (d : ℝ) (hd : 7 ≤ d) :
    3 ≤ d / 2 - supportedBound 4 (d - 5) := by
  have hden : 0 < d - 1 := by linarith
  have hid : d / 2 - supportedBound 4 (d - 5) = 4 - 6 / (d - 1) := by
    unfold supportedBound
    rw [show d - 5 + 4 = d - 1 by ring]
    field_simp [ne_of_gt hden]
    ring
  rw [hid]
  have hfrac : 6 / (d - 1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  linarith

theorem hypervertex_contribution_identity (d δ a g R : ℝ)
    (hR : 0 ≤ R) (hd : d = R + δ + a + g) :
    d / 2 - g / 5 - supportedBound 4 R - 3 =
      a / 2 + 3 * g / 10 + (δ - 3) / 2 - 6 / (R + 4) := by
  have hden : R + 4 ≠ 0 := by linarith
  rw [hd]
  unfold supportedBound
  field_simp [hden]
  ring

/-- Equation (8), including its exact `3/10` core credit. -/
theorem hypervertex_contribution_lower_bound (d δ a g R : ℝ)
    (hR : 0 ≤ R) (hd : d = R + δ + a + g) :
    a / 2 + 3 * g / 10 + (δ - 6) / 2 ≤
      d / 2 - g / 5 - supportedBound 4 R - 3 := by
  rw [hypervertex_contribution_identity d δ a g R hR hd]
  have hden : 0 < R + 4 := by linarith
  have hfrac : 6 / (R + 4) ≤ 3 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  linarith

/-- The nonexceptional K5 cases in Section 7.3, multiplied by twenty.
The integer `k` is the actual wrench-column rank in the application. -/
theorem five_body_budget (p b j z r k : ℕ)
    (hsize : p + b + j + z = 5) (hr : r ≤ p)
    (hone : j = 1 → 0 < p → r + 1 ≤ p)
    (hzero : j = 0 → b = 0 ∧ r + k ≤ p ∧
      min p 2 + (if 4 ≤ p then 1 else 0) ≤ k)
    (hnonexceptional : j ≠ 1 ∨ p ≠ 0) :
    4 * b + 10 * r ≤ 6 * p + z + 6 * j := by
  by_cases hj0 : j = 0
  · obtain ⟨hb, hrk, hk⟩ := hzero hj0
    split_ifs at hk <;> omega
  · by_cases hj1 : j = 1
    · have hp : 0 < p := by omega
      have h := hone hj1 hp
      omega
    · omega

/-- In the exceptional K5 case the uncovered amount is exactly bounded by
`max (0, b/4 - 1/2)`, here expressed without truncated real subtraction and
multiplied by twenty. -/
theorem five_body_exceptional_budget (b z r : ℕ)
    (hsize : b + z = 4) (hr : r = 0) :
    4 * b + 10 * r ≤ z + 6 + (5 * b - 10) := by
  omega

set_option maxHeartbeats 1000000 in
/-- All cases of the final hypervertex account, in exact integer units.

`hdelete` is the first inequality in (10), before replacing `k` by `5a`.
The four boundary hypotheses are precisely the additional neighborhood
counts proved in the last two pages of the paper. The conclusion says that
`(δ-6)/2` pays `a/2 + q₃/4 + q₄/2`.
-/
theorem remaining_hypervertex_charges (a q₂ q₃ q₄ k D δ : ℕ)
    (hbase : 7 ≤ δ) (hk : 5 * a ≤ k)
    (hdelete : k + (2 * q₂ + 3 * q₃ + 4 * q₄) + min 3 D ≤
      δ + a + (q₂ + q₃ + q₄))
    (hzero : a = 0 → 0 < q₂ + q₃ + q₄ → 3 ≤ D)
    (hmixed : a = 1 → q₂ = 1 → q₃ = 1 → q₄ = 0 → 1 ≤ D)
    (hthree : a = 1 → q₂ = 0 → q₃ = 1 → q₄ = 0 → 7 ≤ k + D)
    (hfour : a = 1 → q₂ = 0 → q₃ = 0 → q₄ = 1 → 8 ≤ k + D) :
    12 + 2 * a + q₃ + 2 * q₄ ≤ 2 * δ := by
  have hlower : 4 * a + q₂ + 2 * q₃ + 3 * q₄ + min 3 D ≤ δ := by
    omega
  by_cases ha0 : a = 0
  · by_cases hg : q₂ + q₃ + q₄ = 0
    · omega
    · have hD := hzero ha0 (by omega)
      omega
  · by_cases ha1 : a = 1
    · by_cases hmany : 2 ≤ q₃ + q₄
      · omega
      · by_cases hq3 : q₃ = 1
        · by_cases hq2zero : q₂ = 0
          · have hD := hthree ha1 hq2zero hq3 (by omega)
            omega
          · by_cases hq2one : q₂ = 1
            · have hD := hmixed ha1 hq2one hq3 (by omega)
              omega
            · omega
        · by_cases hq4 : q₄ = 1
          · by_cases hq2 : q₂ = 0
            · have hD := hfour ha1 hq2 (by omega) hq4
              omega
            · omega
          · omega
    · omega

end Papers.Rigidity.Budget

end
end BundleSource0006

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0006/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0006.json"

section BundleSource0007
/- Source: Papers/RigidityBodyBudget.lean -/





@[expose] public section

/-!
# The observer budget of each actual maximal body

The ranks below are dimensions of the actual point-force scalar maps.
The cases with zero or one hypervertex use the force/moment constraints
proved in `RigidityBodyScalarRank`. The only remaining shortfalls are
the literal three-port and four-port cores of Section 7.4.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- The two possible exceptional core deficits, in the original units
of the expected rank contribution. -/
def coreShortfall (b : ℕ) : ℝ :=
  if b = 3 then 1 / 4 else if b = 4 then 1 / 2 else 0

def bodyShortfall (M : MinimalCounterexample V) (C : Body M.graph) : ℝ :=
  if C.val.card = 5 ∧ (bodyHyperVertices M C).card = 1 ∧
      (bodySoftVertices M C).card = 0 then
    coreShortfall (bodyTypeBVertices M C).card else 0

/-- The conservative allocation supplied by the two-body vertices.
For K5 it retains every positive `1/20` ordinary-port contribution. -/
def bodyBaseCredit (M : MinimalCounterexample V) (C : Body M.graph) : ℝ :=
  if C.val.card = 5 then
    3 * ((bodySoftVertices M C).card : ℝ) / 10 - ((bodyTypeBVertices M C).card : ℝ) / 5 +
      ((bodyOtherVertices M C).card : ℝ) / 20
  else if 6 ≤ C.val.card then ((bodySoftVertices M C).card : ℝ) / 2 else 0

/-- Exactly the selected-core credit supplied by the incident
hypervertices; unselected bodies receive no such credit. -/
def bodyHyperCredit (M : MinimalCounterexample V) (C : Body M.graph) : ℝ :=
  if IsSelectedCore M C then 3 * ((bodyHyperVertices M C).card : ℝ) / 10 else 0

theorem coreShortfall_nonneg (b : ℕ) : 0 ≤ coreShortfall b := by
  unfold coreShortfall
  split_ifs <;> norm_num

theorem bodyShortfall_nonneg (M : MinimalCounterexample V) (C : Body M.graph) :
    0 ≤ bodyShortfall M C := by
  unfold bodyShortfall
  split_ifs
  · exact coreShortfall_nonneg _
  · rfl

theorem bodyHyperCredit_nonneg (M : MinimalCounterexample V) (C : Body M.graph) :
    0 ≤ bodyHyperCredit M C := by
  unfold bodyHyperCredit
  split_ifs
  · positivity
  · rfl

theorem SoftScalarSystem.bodyScalarRank_le_softCard
    (L : SoftScalarSystem M p) (C : Body M.graph) :
    L.bodyScalarRank C ≤ (bodySoftVertices M C).card := by
  simpa only [card_bodySoftPort,bodySoftVertices] using L.bodyScalarRank_le_card C

theorem SoftScalarSystem.bodyScalarRank_one_hypervertex_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (hH : (bodyHyperVertices M C).card = 1)
    (hP : 0 < (bodySoftVertices M C).card) :
    L.bodyScalarRank C + 1 ≤ (bodySoftVertices M C).card := by
  obtain ⟨h,hh⟩ := Finset.card_eq_one.mp hH
  have hmem : h ∈ bodyHyperVertices M C := by rw [hh]; simp
  have hmem' := Finset.mem_filter.mp hmem
  have honly (w : V) (hw : w ∈ C.val) (hwhyper : IsHypervertex M.graph w) : w = h := by
    have hm : w ∈ bodyHyperVertices M C := Finset.mem_filter.mpr ⟨hw,hwhyper⟩
    simpa only [hh,Finset.mem_singleton] using hm
  simpa only [card_bodySoftPort,bodySoftVertices] using
    L.bodyScalarRank_add_one_le_card hgen hp C h hmem'.1 hmem'.2 honly
      (by simpa only [card_bodySoftPort,bodySoftVertices] using hP)

/-- The actual zero-hypervertex case supplies every hypothesis of the
integer wrench budget, including absence of type-B ports. -/
theorem SoftScalarSystem.bodyScalarRank_no_hypervertex_bounds
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (hH : (bodyHyperVertices M C).card = 0) :
    (bodyTypeBVertices M C).card = 0 ∧
      L.bodyScalarRank C + Module.finrank ℝ
        (WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C)) ≤
          (bodySoftVertices M C).card ∧
      min (bodySoftVertices M C).card 2 +
        (if 4 ≤ (bodySoftVertices M C).card then 1 else 0) ≤ Module.finrank ℝ
          (WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C)) := by
  have hnone (w : V) (hw : w ∈ C.val) : ¬ IsHypervertex M.graph w := by
    intro hh
    have hm : w ∈ bodyHyperVertices M C := Finset.mem_filter.mpr ⟨hw,hh⟩
    have hpos := Finset.card_pos.mpr ⟨w,hm⟩
    omega
  refine ⟨by rw [bodyTypeB_empty_of_no_hypervertices M C hH]; rfl,?_,?_⟩
  · simpa only [card_bodySoftPort,bodySoftVertices] using
      L.bodyScalarRank_add_wrenchRank_le_card hgen hp C hnone
  · have hcard : Fintype.card (BodySoftPort C) = (bodySoftVertices M C).card := by
      simpa only [bodySoftVertices] using card_bodySoftPort C
    rw [← hcard]
    exact L.body_wrench_rank_lower_bound hgen hp C

/-- The nonexceptional K5 inequalities now have no unproved rank or
geometric premise: every bound comes from the actual graph. -/
theorem SoftScalarSystem.five_body_nonexceptional_budget
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : Body M.graph)
    (hC : C.val.card = 5)
    (hne : (bodyHyperVertices M C).card ≠ 1 ∨ (bodySoftVertices M C).card ≠ 0) :
    4 * (bodyTypeBVertices M C).card + 10 * L.bodyScalarRank C ≤
      6 * (bodySoftVertices M C).card + (bodyOtherVertices M C).card +
        6 * (bodyHyperVertices M C).card := by
  apply Budget.five_body_budget (bodySoftVertices M C).card (bodyTypeBVertices M C).card
    (bodyHyperVertices M C).card (bodyOtherVertices M C).card (L.bodyScalarRank C)
    (Module.finrank ℝ
      (WrenchRank.wrenchSpan (fun v : BodySoftPort C => p v.val) (L.bodyAxis C)))
  · simpa only [hC] using body_vertex_counts_partition M C
  · exact L.bodyScalarRank_le_softCard C
  · exact L.bodyScalarRank_one_hypervertex_bound hgen hp C
  · exact L.bodyScalarRank_no_hypervertex_bounds hgen hp C
  · exact hne

/-- Every selected K5 pays its full scalar-observer cost after the
explicit, separately counted exceptional shortfall is supplied. -/
theorem SoftScalarSystem.selected_five_body_budget
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : SelectedCore M) :
    (L.bodyScalarRank C.val : ℝ) / 2 ≤
      bodyBaseCredit M C.val + bodyHyperCredit M C.val + bodyShortfall M C.val := by
  have hC := C.property.1
  have hselected := C.property
  by_cases he : (bodyHyperVertices M C.val).card = 1 ∧ (bodySoftVertices M C.val).card = 0
  · have hr : L.bodyScalarRank C.val = 0 := by
      have h := L.bodyScalarRank_le_softCard C.val
      omega
    have hsize : (bodyTypeBVertices M C.val).card + (bodyOtherVertices M C.val).card = 4 := by
      have h := body_vertex_counts_partition M C.val
      omega
    have hsizeR : ((bodyTypeBVertices M C.val).card : ℝ) +
        (bodyOtherVertices M C.val).card = 4 := by exact_mod_cast hsize
    have hb : (bodyTypeBVertices M C.val).card ≤ 2 ∨
        (bodyTypeBVertices M C.val).card = 3 ∨ (bodyTypeBVertices M C.val).card = 4 := by omega
    have hshort : bodyShortfall M C.val = coreShortfall (bodyTypeBVertices M C.val).card := by
      rw [bodyShortfall,if_pos ⟨hC,he⟩]
    rw [bodyBaseCredit,if_pos hC,bodyHyperCredit,if_pos hselected,hshort,he.1,he.2,hr]
    norm_num only [Nat.cast_zero,Nat.cast_one,zero_div,mul_zero,mul_one,zero_sub]
    rcases hb with hb | hb | hb
    · have hb3 : (bodyTypeBVertices M C.val).card ≠ 3 := by omega
      have hb4 : (bodyTypeBVertices M C.val).card ≠ 4 := by omega
      have hbR : ((bodyTypeBVertices M C.val).card : ℝ) ≤ 2 := by exact_mod_cast hb
      rw [coreShortfall,if_neg hb3,if_neg hb4]
      linarith
    · rw [coreShortfall,if_pos hb]
      have hbR : ((bodyTypeBVertices M C.val).card : ℝ) = 3 := by exact_mod_cast hb
      linarith
    · have hb3 : (bodyTypeBVertices M C.val).card ≠ 3 := by omega
      rw [coreShortfall,if_neg hb3,if_pos hb]
      have hbR : ((bodyTypeBVertices M C.val).card : ℝ) = 4 := by exact_mod_cast hb
      linarith
  · have hne : (bodyHyperVertices M C.val).card ≠ 1 ∨
        (bodySoftVertices M C.val).card ≠ 0 := by tauto
    have h := L.five_body_nonexceptional_budget hgen hp C.val hC hne
    have hR : 4 * ((bodyTypeBVertices M C.val).card : ℝ) +
        10 * L.bodyScalarRank C.val ≤ 6 * (bodySoftVertices M C.val).card +
          (bodyOtherVertices M C.val).card + 6 * (bodyHyperVertices M C.val).card := by
      exact_mod_cast h
    have hshort : bodyShortfall M C.val = 0 := by
      unfold bodyShortfall
      exact if_neg (fun h => he h.2)
    rw [bodyBaseCredit,if_pos hC,bodyHyperCredit,if_pos hselected,hshort]
    linarith

/-- The body budget for every actual observer, including all orders
above five and unselected K5 bodies. -/
theorem SoftScalarSystem.large_body_budget
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C : LargeBody M.graph) :
    (L.largeRank C : ℝ) / 2 ≤
      bodyBaseCredit M C.val + bodyHyperCredit M C.val + bodyShortfall M C.val := by
  rw [L.largeRank_eq_bodyScalarRank]
  by_cases hC : C.val.val.card = 5
  · by_cases hs : IsSelectedCore M C.val
    · exact L.selected_five_body_budget hgen hp ⟨C.val,hs⟩
    · have hpzero : (bodySoftVertices M C.val).card = 0 := by
        by_contra h
        exact hs ⟨hC,Or.inl (Finset.card_pos.mp (by omega))⟩
      have hbzero : (bodyTypeBVertices M C.val).card = 0 := by
        by_contra h
        exact hs ⟨hC,Or.inr (Finset.card_pos.mp (by omega))⟩
      have hrzero : L.bodyScalarRank C.val = 0 := by
        have h := L.bodyScalarRank_le_softCard C.val
        omega
      rw [bodyBaseCredit,if_pos hC,bodyHyperCredit,if_neg hs,hpzero,hbzero,hrzero]
      have hn := bodyShortfall_nonneg M C.val
      simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,zero_add,add_zero]
      positivity
  · have hlarge : 6 ≤ C.val.val.card := by have := C.property; omega
    have hr := L.bodyScalarRank_le_softCard C.val
    have hrR : (L.bodyScalarRank C.val : ℝ) ≤ (bodySoftVertices M C.val).card := by
      exact_mod_cast hr
    have hh := bodyHyperCredit_nonneg M C.val
    have hd := bodyShortfall_nonneg M C.val
    rw [bodyBaseCredit,if_neg hC,if_pos hlarge]
    linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0007

section BundleSource0008
/- Source: Papers/RigidityStressLedger.lean -/




@[expose] public section

/-!
# The exact global stress ledger

The supported dimensions of an arbitrary fixed subspace telescope in
every vertex order.  Applied to the annihilator of the actual soft-pin
functionals, this gives equation (6) of the paper without a probabilistic
independence assumption or an additional rank identity in the hypotheses.
-/

noncomputable section
open scoped Classical BigOperators

namespace Papers.Rigidity.SupportedCode

variable {K E : Type*} [Field K] [Fintype E]

@[simp] theorem supportedOn_empty (W : Submodule K (E → K)) :
    supportedOn W ∅ = ⊥ := by
  ext w
  constructor
  · intro hw
    rw [Submodule.mem_bot]
    funext e
    exact hw.2 e (by simp)
  · intro hw
    rw [Submodule.mem_bot] at hw
    subst w
    exact (supportedOn W ∅).zero_mem

@[simp] theorem supportedOn_univ (W : Submodule K (E → K)) :
    supportedOn W Set.univ = W := by
  ext w
  simp

/-- The literal common kernel of functionals on a subspace, embedded
back into the original coordinate space. -/
def annihilatorIn (S : Submodule K (E → K))
    (U : Submodule K (Module.Dual K S)) : Submodule K (E → K) :=
  U.dualCoannihilator.map S.subtype

theorem annihilatorIn_le (S : Submodule K (E → K))
    (U : Submodule K (Module.Dual K S)) : annihilatorIn S U ≤ S := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

theorem mem_annihilatorIn (S : Submodule K (E → K))
    (U : Submodule K (Module.Dual K S)) (x : S) :
    x.val ∈ annihilatorIn S U ↔ ∀ φ ∈ U, φ x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h : y = x := Subtype.ext hxy
    subst y
    exact (Submodule.mem_dualCoannihilator x).mp hy
  · intro h
    exact ⟨x, (Submodule.mem_dualCoannihilator x).mpr h, rfl⟩

theorem finrank_annihilatorIn (S : Submodule K (E → K))
    (U : Submodule K (Module.Dual K S)) :
    Module.finrank K U + Module.finrank K (annihilatorIn S U) =
      Module.finrank K S := by
  rw [annihilatorIn, Submodule.finrank_map_subtype_eq]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq U

end Papers.Rigidity.SupportedCode

namespace Papers.Rigidity.BarJoint

open SupportedCode UniformOrders
variable {V : Type} [Fintype V]

/-- Supported subspaces telescope for each actual order, including
graphs with isolated vertices and the empty graph. -/
theorem sum_stressDimensionContribution (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) :
    (∑ v : V, stressDimensionContribution G W v) =
      (Module.finrank ℝ W : ℝ) := by
  have htel (σ : Outcome V) :
      (∑ v : V, ((Module.finrank ℝ (stressThrough G W σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G W σ v))) =
      (Module.finrank ℝ W : ℝ) := by
    let f : ℕ → ℝ := fun k =>
      Module.finrank ℝ (supportedOn W (subgraphEdgeSet G (prefixGraph G σ k)))
    have hb (v : V) :
        (Module.finrank ℝ (stressBefore G W σ v) : ℝ) = f (σ v).val := by
      exact (congrArg (fun A : Set (Edge G) =>
        (Module.finrank ℝ (supportedOn W A) : ℝ))
          (subgraphEdgeSet_prefix_before G σ v)).symm
    have ht (v : V) :
        (Module.finrank ℝ (stressThrough G W σ v) : ℝ) = f ((σ v).val + 1) := by
      exact (congrArg (fun A : Set (Edge G) =>
        (Module.finrank ℝ (supportedOn W A) : ℝ))
          (subgraphEdgeSet_prefix_through G σ v)).symm
    simp_rw [hb, ht]
    have heq := Equiv.sum_comp σ
      (fun k : Fin (Fintype.card V) => f (k.val + 1) - f k.val)
    rw [heq, Fin.sum_univ_eq_sum_range (fun k => f (k + 1) - f k) (Fintype.card V),
      Finset.sum_range_sub f]
    have hzero : subgraphEdgeSet G (⊥ : SimpleGraph V) = ∅ := by
      ext e
      simp [subgraphEdgeSet]
    have hfull : subgraphEdgeSet G G = Set.univ := by
      ext e
      simp only [subgraphEdgeSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact e.property
    dsimp only [f]
    rw [prefixGraph_card, prefixGraph_zero, hzero, hfull]
    rw [supportedOn_univ, supportedOn_empty, finrank_bot, Nat.cast_zero, sub_zero]
  simp only [stressDimensionContribution]
  rw [← mean_sum, mean_congr _ _ htel, mean_const]

/-- The exact identity before the chosen stress subspace is specialized
to the soft-pin annihilator. -/
theorem subspace_rank_ledger (G : SimpleGraph V) (p : Placement V 3)
    (hp : IsGenericPlacement p) (W : Submodule ℝ (Edge G → ℝ)) :
    (∑ v : V, ((G.degree v : ℝ) / 2 - stressDimensionContribution G W v)) =
      (genericRigidityRank G 3 : ℝ) +
        Module.finrank ℝ (StressSpace G p) - Module.finrank ℝ W := by
  have hfull := sum_stressDimensionContribution G (StressSpace G p)
  have hW := sum_stressDimensionContribution G W
  have hrank := sum_rankContribution G
  simp_rw [rankContribution_eq_degree_half_sub_stress G p hp] at hrank
  rw [Finset.sum_sub_distrib] at hrank ⊢
  rw [hfull] at hrank
  rw [hW]
  linarith

/-- Equation (6), with `U` a literal subspace of the dual of the actual
equilibrium-stress space, and `K` its literal annihilator. -/
theorem scalar_annihilator_rank_ledger (G : SimpleGraph V) (p : Placement V 3)
    (hp : IsGenericPlacement p)
    (U : Submodule ℝ (Module.Dual ℝ (StressSpace G p))) :
    (genericRigidityRank G 3 : ℝ) =
      (∑ v : V, ((G.degree v : ℝ) / 2 -
        stressDimensionContribution G (annihilatorIn (StressSpace G p) U) v)) -
      Module.finrank ℝ U := by
  have h := subspace_rank_ledger G p hp (annihilatorIn (StressSpace G p) U)
  have hd := congrArg (fun n : ℕ => (n : ℝ))
    (finrank_annihilatorIn (StressSpace G p) U)
  push_cast at hd
  linarith

end Papers.Rigidity.BarJoint

end
end
end BundleSource0008

section BundleSource0009
/- Source: Papers/RigidityLocalPrefixDimensions.lean -/





@[expose] public section

/-!
# Exact dimensions of the supported local stress sum

The summands below are actual ambient stresses, with both body support
and prefix support. Injectivity and the support identity of Lemma 6.1
identify their sum with the supported part of the full local stress
space. Zero extension then identifies every summand with the stress
space of its complete body fragment, including fragments of size 0–3.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem vertexEdgeSet_inter (G : SimpleGraph V) (S T : Finset V) :
    vertexEdgeSet G (S ∩ T) = vertexEdgeSet G S ∩ vertexEdgeSet G T := by
  ext e
  simp only [vertexEdgeSet,Set.mem_setOf_eq,Set.mem_inter_iff,Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1,fun v hv => (h v hv).2⟩
  · rintro ⟨hS,hT⟩ v hv
    exact ⟨hS v hv,hT v hv⟩

theorem subgraphEdgeSet_cliqueOn (G : SimpleGraph V) (S : Finset V) :
    subgraphEdgeSet G (cliqueOn S) = vertexEdgeSet G S := by
  ext e
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
    have hne : v ≠ w := (show G.Adj v w from he).ne
    change (v ≠ w ∧ v ∈ S ∧ w ∈ S) ↔ ∀ a, a ∈ s(v,w) → a ∈ S
    constructor
    · rintro ⟨_,hv,hw⟩ a ha
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact hv
      · exact hw
    · intro h
      exact ⟨hne,h v (Sym2.mem_mk_left v w),h w (Sym2.mem_mk_right v w)⟩

theorem bodyFragment_le_graph (G : SimpleGraph V) (C : Body G) (T : Finset V) :
    cliqueOn (C.val ∩ T) ≤ G := by
  rintro v w ⟨hne,hv,hw⟩
  exact C.property.2.1 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hw).1 hne

def localBodyPrefixSpace (G : SimpleGraph V) (p : Placement V 3)
    (C : Body G) (T : Finset V) : Submodule ℝ (Edge G → ℝ) :=
  supportedOn (localStressSpace G p C) (vertexEdgeSet G T)

theorem localBodyPrefixSpace_eq (G : SimpleGraph V) (p : Placement V 3)
    (C : Body G) (T : Finset V) :
    localBodyPrefixSpace G p C T =
      supportedOn (StressSpace G p) (subgraphEdgeSet G (cliqueOn (C.val ∩ T))) := by
  rw [subgraphEdgeSet_cliqueOn,vertexEdgeSet_inter]
  ext x
  simp only [localBodyPrefixSpace,localStressSpace,mem_supportedOn,Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hx,hC⟩,hT⟩
    refine ⟨hx,?_⟩
    intro e he
    by_cases hc : e ∈ vertexEdgeSet G C.val
    · exact hT e (fun ht => he ⟨hc,ht⟩)
    · exact hC e hc
  · rintro ⟨hx,h⟩
    exact ⟨⟨hx,fun e he => h e (fun hm => he hm.1)⟩,
      fun e he => h e (fun hm => he hm.2)⟩

theorem localBodyPrefixSpace_finrank (G : SimpleGraph V) (p : Placement V 3)
    (C : Body G) (T : Finset V) :
    Module.finrank ℝ (localBodyPrefixSpace G p C T) =
      Module.finrank ℝ (StressSpace (cliqueOn (C.val ∩ T)) p) := by
  rw [localBodyPrefixSpace_eq]
  exact (subgraphStressEquiv (bodyFragment_le_graph G C T) p).finrank_eq.symm

def localPrefixFamilyInclusion (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (∀ C : Body G, localBodyPrefixSpace G p C T) →ₗ[ℝ]
      (∀ C : Body G, localStressSpace G p C) where
  toFun a C := ⟨(a C).val,(a C).property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localPrefixFamilyInclusion_injective (G : SimpleGraph V)
    (p : Placement V 3) (T : Finset V) :
    Function.Injective (localPrefixFamilyInclusion G p T) := by
  intro a b hab
  funext C
  exact Subtype.ext (congrArg
    (fun x : ∀ D : Body G, localStressSpace G p D => (x C).val) hab)

def localBodyPrefixSum (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (∀ C : Body G, localBodyPrefixSpace G p C T) →ₗ[ℝ] (Edge G → ℝ) :=
  (localStressSum G p).comp (localPrefixFamilyInclusion G p T)

@[simp] theorem localBodyPrefixSum_apply (G : SimpleGraph V) (p : Placement V 3)
    (T : Finset V) (a : ∀ C : Body G, localBodyPrefixSpace G p C T) :
    localBodyPrefixSum G p T a = ∑ C : Body G, (a C).val := by
  simp [localBodyPrefixSum,localPrefixFamilyInclusion]

def fullLocalStressSpace (G : SimpleGraph V) (p : Placement V 3) :
    Submodule ℝ (Edge G → ℝ) := (localStressSum G p).range

theorem fullLocalStressSpace_le_stress (G : SimpleGraph V) (p : Placement V 3) :
    fullLocalStressSpace G p ≤ StressSpace G p := by
  rintro x ⟨a,rfl⟩
  exact localStressSum_mem G p a

theorem localBodyPrefixSum_injective (M : MinimalCounterexample V)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Function.Injective (localBodyPrefixSum M.graph p T) :=
  (localStressSum_injective M p hp).comp
    (localPrefixFamilyInclusion_injective M.graph p T)

theorem localBodyPrefixSum_range (M : MinimalCounterexample V)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    (localBodyPrefixSum M.graph p T).range =
      supportedOn (fullLocalStressSpace M.graph p) (vertexEdgeSet M.graph T) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨⟨localPrefixFamilyInclusion M.graph p T a,rfl⟩,?_⟩
    intro e he
    rw [localBodyPrefixSum_apply,Finset.sum_apply]
    exact Finset.sum_eq_zero (fun C _ => (a C).property.2 e he)
  · rintro ⟨⟨a,rfl⟩,ha⟩
    have hs := (localStressSum_supported_iff M p hp T a).mp ha
    let b : ∀ C : Body M.graph, localBodyPrefixSpace M.graph p C T :=
      fun C => ⟨(a C).val,(a C).property,hs C⟩
    refine ⟨b,?_⟩
    rfl

/-- Exact prefix dimension of the genuine direct sum of local stresses. -/
theorem fullLocalStressSpace_prefix_finrank (M : MinimalCounterexample V)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ
        (supportedOn (fullLocalStressSpace M.graph p) (vertexEdgeSet M.graph T)) =
      ∑ C : Body M.graph, Module.finrank ℝ (StressSpace (cliqueOn (C.val ∩ T)) p) := by
  rw [← localBodyPrefixSum_range M p hp T,
    LinearMap.finrank_range_of_inj (localBodyPrefixSum_injective M p hp T),
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl (fun C _ => localBodyPrefixSpace_finrank M.graph p C T)

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0009

section BundleSource0010
/- Source: Papers/RigidityScalarKernel.lean -/




@[expose] public section

/-!
# The actual scalar annihilator

The residual coefficient space consists of equilibrium stresses whose
soft point-pin forces vanish.  Internal body stresses belong to it by
the copied-force construction, independently of the chosen scalar
normalizations.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- This definition uses the actual normalized point-force functionals.
It is equivalent to their coordinatewise vanishing, as proved below. -/
def SoftScalarSystem.scalarKernel (L : SoftScalarSystem M p) :
    Submodule ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ) :=
  annihilatorIn (StressSpace (maskedGraph M.graph Finset.univ) p)
    (Submodule.span ℝ (Set.range L.scalar))

theorem SoftScalarSystem.scalarKernel_le_stress (L : SoftScalarSystem M p) :
    L.scalarKernel ≤ StressSpace (maskedGraph M.graph Finset.univ) p :=
  annihilatorIn_le _ _

theorem SoftScalarSystem.mem_scalarKernel (L : SoftScalarSystem M p)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    s.val ∈ L.scalarKernel ↔ ∀ v, L.scalar v s = 0 := by
  rw [SoftScalarSystem.scalarKernel, mem_annihilatorIn]
  constructor
  · intro h v
    exact h _ (Submodule.subset_span ⟨v,rfl⟩)
  · intro h
    have hle : Submodule.span ℝ (Set.range L.scalar) ≤
        ((Module.Dual.eval ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)) s).ker := by
      apply Submodule.span_le.mpr
      rintro φ ⟨v,rfl⟩
      exact h v
    intro φ hφ
    exact hle hφ

theorem SoftScalarSystem.point_force_zero_on_kernel (L : SoftScalarSystem M p)
    (v : SoftPointPin M.graph)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : s.val ∈ L.scalarKernel) :
    v.pin.pointForceOnWholePrefix v.isPoint M.covered p s = 0 := by
  rw [L.force_eq, (L.mem_scalarKernel s).mp hs v, zero_smul]

/-- Every actual sum of internal complete-body stresses has zero soft
force coordinates.  There are no hypotheses about its dimension. -/
theorem SoftScalarSystem.localPrefixStresses_le_coannihilator
    (L : SoftScalarSystem M p) :
    localPrefixStresses M.graph p Finset.univ ≤
      (Submodule.span ℝ (Set.range L.scalar)).dualCoannihilator := by
  rintro s ⟨a,rfl⟩
  rw [Submodule.mem_dualCoannihilator]
  have hzero (v : SoftPointPin M.graph) :
      L.scalar v (localPrefixStressSum M.graph p Finset.univ a) = 0 := by
    have hf : v.pin.pointForceOnWholePrefix v.isPoint M.covered p
        (localPrefixStressSum M.graph p Finset.univ a) = 0 := by
      change v.pin.pointForceOnWholePrefix v.isPoint M.covered p
        (copiedToStress M.graph p Finset.univ
          (bodyStressCompatible M.graph p Finset.univ a)) = 0
      rw [TwoBodyPin.pointForceOnWholePrefix_copied]
      change (bodyCopyForces M.graph p Finset.univ
        (bodyStressCoefficients M.graph p Finset.univ a) v.pin.left).val v.val = 0
      rw [bodyCopyForces_bodyStressCoefficients]
      rfl
    rw [L.force_eq] at hf
    exact (smul_eq_zero.mp hf).resolve_right (L.axis_ne_zero v)
  have hmem : (localPrefixStressSum M.graph p Finset.univ a).val ∈ L.scalarKernel :=
    (L.mem_scalarKernel _).mpr hzero
  exact (mem_annihilatorIn _ _ _).mp hmem

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0010

section BundleSource0011
/- Source: Papers/RigidityWholeLocalStress.lean -/





@[expose] public section

/-!
# Identifying the two presentations of the actual local stress sum

The copied-edge construction retains the whole-prefix graph in its
types. This file identifies its internal stresses with the ordinary
ambient local stress space, including their actual coefficients and
every induced-prefix support. The identifications are explicit linear
equivalences and finite-sum reindexings.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

@[simp] theorem maskedGraph_univ (G : SimpleGraph V) :
    maskedGraph G Finset.univ = G := by
  ext v w
  simp [maskedGraph]

def wholeBodyEquiv (G : SimpleGraph V) : Body G ≃ Body (maskedGraph G Finset.univ) where
  toFun C := ⟨C.val,by simpa only [maskedGraph_univ] using C.property⟩
  invFun C := ⟨C.val,by simpa only [maskedGraph_univ] using C.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem wholeBodyEquiv_val (G : SimpleGraph V) (C : Body G) :
    (wholeBodyEquiv G C).val = C.val := rfl

def wholeFragmentLocalEquiv (G : SimpleGraph V) (p : Placement V 3) (C : Body G) :
    StressSpace (cliqueOn (C.val ∩ Finset.univ)) p ≃ₗ[ℝ]
      localStressSpace (maskedGraph G Finset.univ) p (wholeBodyEquiv G C) :=
  (subgraphStressEquiv (fragment_le_masked G Finset.univ C) p).trans
    (LinearEquiv.ofEq
      (supportedOn (StressSpace (maskedGraph G Finset.univ) p)
        (subgraphEdgeSet (maskedGraph G Finset.univ)
          (cliqueOn (C.val ∩ Finset.univ))))
      (localStressSpace (maskedGraph G Finset.univ) p (wholeBodyEquiv G C)) (by
        rw [subgraphEdgeSet_cliqueOn,Finset.inter_univ]
        rfl))

@[simp] theorem wholeFragmentLocalEquiv_val (G : SimpleGraph V)
    (p : Placement V 3) (C : Body G)
    (s : StressSpace (cliqueOn (C.val ∩ Finset.univ)) p) :
    (wholeFragmentLocalEquiv G p C s).val =
      extendEdgeCoefficients (fragment_le_masked G Finset.univ C) s.val := rfl

def wholeLocalFamily (G : SimpleGraph V) (p : Placement V 3)
    (b : BodyFragmentStresses G p Finset.univ) :
    ∀ C : Body (maskedGraph G Finset.univ),
      localStressSpace (maskedGraph G Finset.univ) p C :=
  fun C => wholeFragmentLocalEquiv G p ((wholeBodyEquiv G).symm C)
    (b ((wholeBodyEquiv G).symm C))

theorem localPrefixStressSum_eq_localStressSum (G : SimpleGraph V)
    (p : Placement V 3) (b : BodyFragmentStresses G p Finset.univ) :
    (localPrefixStressSum G p Finset.univ b).val =
      localStressSum (maskedGraph G Finset.univ) p (wholeLocalFamily G p b) := by
  rw [localPrefixStressSum_val,localStressSum_apply]
  have h := Equiv.sum_comp (wholeBodyEquiv G)
    (fun C => (wholeLocalFamily G p b C).val)
  exact h

theorem wholeLocalFamily_surjective (G : SimpleGraph V) (p : Placement V 3) :
    Function.Surjective (wholeLocalFamily G p) := by
  intro a
  let b : BodyFragmentStresses G p Finset.univ := fun C =>
    (wholeFragmentLocalEquiv G p C).symm (a (wholeBodyEquiv G C))
  refine ⟨b,?_⟩
  funext C
  simp only [wholeLocalFamily,b,Equiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rfl

theorem fullLocalStressSpace_eq_wholePrefix (G : SimpleGraph V) (p : Placement V 3) :
    fullLocalStressSpace (maskedGraph G Finset.univ) p =
      (localPrefixStresses G p Finset.univ).map
        (StressSpace (maskedGraph G Finset.univ) p).subtype := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := wholeLocalFamily_surjective G p a
    refine ⟨localPrefixStressSum G p Finset.univ b,⟨b,rfl⟩,?_⟩
    exact localPrefixStressSum_eq_localStressSum G p b
  · rintro ⟨s,⟨b,rfl⟩,rfl⟩
    exact ⟨wholeLocalFamily G p b,(localPrefixStressSum_eq_localStressSum G p b).symm⟩

theorem localPrefixStressSum_supported (G : SimpleGraph V) (p : Placement V 3)
    (T : Finset V) (b : BodyFragmentStresses G p Finset.univ)
    (hb : ∀ C e, (∃ w, w ∈ e.val ∧ w ∉ T) → (b C).val e = 0) :
    ∀ e, e ∉ vertexEdgeSet (maskedGraph G Finset.univ) T →
      (localPrefixStressSum G p Finset.univ b).val e = 0 := by
  intro e he
  rw [localPrefixStressSum_val,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro C _
  by_cases hc : e.val ∈ (cliqueOn (C.val ∩ Finset.univ)).edgeSet
  · let d : Edge (cliqueOn (C.val ∩ Finset.univ)) := ⟨e.val,hc⟩
    have hed : edgeInclusion (fragment_le_masked G Finset.univ C) d = e := rfl
    rw [← hed,extendEdgeCoefficients_inside]
    apply hb C d
    change ¬∀ w, w ∈ e.val → w ∈ T at he
    push_neg at he
    exact he
  · exact extendEdgeCoefficients_outside _ _ _ hc

variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.fullLocalStressSpace_le_kernel (L : SoftScalarSystem M p) :
    fullLocalStressSpace (maskedGraph M.graph Finset.univ) p ≤ L.scalarKernel := by
  rw [fullLocalStressSpace_eq_wholePrefix]
  exact Submodule.map_mono L.localPrefixStresses_le_coannihilator

theorem fullLocalWholePrefix_finrank (M : MinimalCounterexample V)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ (supportedOn
        (fullLocalStressSpace (maskedGraph M.graph Finset.univ) p)
        (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)) =
      ∑ C : Body M.graph, Module.finrank ℝ (StressSpace (cliqueOn (C.val ∩ T)) p) := by
  rw [maskedGraph_univ]
  exact fullLocalStressSpace_prefix_finrank M p hp T

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0011

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0011/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0011.json"

section BundleSource0012
/- Source: Papers/RigiditySupportedCopyLift.lean -/




@[expose] public section

/-!
# Support-preserving lifts to actual body-edge occurrences

Every stress supported on an induced vertex set has a copied coefficient
lift supported on that same set.  This supplies prefix lifts without
assuming that an arbitrary right inverse respects support.
-/

noncomputable section
namespace Papers.Rigidity
open BodyLoads
open scoped Classical BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

theorem fiberSum_supported_lift (f : I → J) (hf : Function.Surjective f)
    (A : Set J) (b : J → K) (hb : ∀ j ∉ A, b j = 0) :
    ∃ a : I → K, fiberSum f a = b ∧ ∀ i, f i ∉ A → a i = 0 := by
  obtain ⟨a,ha⟩ := fiberSum_surjective f hf b
  let c : I → K := fun i => if f i ∈ A then a i else 0
  refine ⟨c, ?_, ?_⟩
  · ext j
    rw [fiberSum_coordinate]
    by_cases hj : j ∈ A
    · rw [← congrFun ha j, fiberSum_coordinate]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : f i = j
      · simp [hij,c,hj]
      · simp [hij]
    · rw [hb j hj]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hij : f i = j
      · simp [hij,c,hj]
      · simp [hij]
  · intro i hi
    simp [c,hi]

namespace BodyLoads
open BarJoint SupportedCode
variable {V : Type} [Fintype V]

def CopiedSupportedOn (G : SimpleGraph V) (T : Finset V)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ) : Prop :=
  ∀ i, (∃ v, v ∈ i.2.val ∧ v ∉ T) → a i = 0

/-- Literal copied coefficients lift the given actual stress and retain
the support of every induced prefix. -/
theorem exists_supported_copied_lift (G : SimpleGraph V) (hG : K4Covered G)
    (p : Placement V 3) (T : Finset V)
    (s : StressSpace (maskedGraph G Finset.univ) p)
    (hs : ∀ e, e ∉ vertexEdgeSet (maskedGraph G Finset.univ) T → s.val e = 0) :
    ∃ a : compatibleCopiedCoefficients G p Finset.univ,
      copiedToStress G p Finset.univ a = s ∧ CopiedSupportedOn G T a.val := by
  obtain ⟨a,ha,hsupp⟩ := fiberSum_supported_lift
    (underlyingCopiedEdge G Finset.univ)
    (underlyingCopiedEdge_surjective G hG Finset.univ)
    (vertexEdgeSet (maskedGraph G Finset.univ) T) s.val hs
  have hm : a ∈ compatibleCopiedCoefficients G p Finset.univ := by
    change copyAggregate G Finset.univ a ∈ StressSpace (maskedGraph G Finset.univ) p
    rw [show copyAggregate G Finset.univ a = s.val from ha]
    exact s.property
  refine ⟨⟨a,hm⟩, Subtype.ext ha, ?_⟩
  intro i hi
  apply hsupp i
  intro he
  obtain ⟨v,hv,hvT⟩ := hi
  exact hvT (he v hv)

theorem supported_copy_force_zero_outside (G : SimpleGraph V) (p : Placement V 3)
    (T : Finset V) (a : BodyEdgeOccurrence G Finset.univ → ℝ)
    (ha : CopiedSupportedOn G T a) (C : Body G) (v : V) (hv : v ∉ T) :
    (bodyCopyForces G p Finset.univ a C).val v = 0 := by
  rw [bodyCopyForces_apply, forceOperator_vertex]
  apply Finset.sum_eq_zero
  intro e _
  rw [bodyCopyRestriction_apply, ha ⟨C,e.val⟩ ⟨v,e.property,hv⟩, zero_smul]

/-- The unchanged loads, regarded on their actual smaller fragments. -/
def supportedCompatibleLoad (G : SimpleGraph V) (p : Placement V 3)
    (T : Finset V) (F : compatibleBodyLoads G p Finset.univ)
    (hF : ∀ C v, v ∉ T → (F.val C).val v = 0) :
    compatibleBodyLoads G p T :=
  ⟨fun C => ⟨(F.val C).val, (F.val C).property.1, by
    intro v hv
    by_cases hvC : v ∈ C.val
    · apply hF C v
      intro hvT
      exact hv (Finset.mem_inter.mpr ⟨hvC,hvT⟩)
    · apply (F.val C).property.2 v
      simp [hvC]⟩, by
    rw [mem_compatibleBodyLoads_iff]
    exact (mem_compatibleBodyLoads_iff G p Finset.univ F.val).mp F.property⟩

end BodyLoads
end Papers.Rigidity

end
end
end BundleSource0012

section BundleSource0013
/- Source: Papers/RigidityPrefixPinNormalization.lean -/





@[expose] public section

/-!
# Killing the two-body force within every actual prefix

The copied lift in this file retains exactly the original graph stress.
At a point pin its force already vanishes on the scalar annihilator.
At a hinge the literal opposite-copy coefficient vector removes it when
the partner is present.  When the partner is absent, the open-variation
argument proves that the original force is zero.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem TwoBodyPin.Hinge.coefficients_supported
    {G : SimpleGraph V} {v : V} {Q : TwoBodyPin G v} (H : Q.Hinge)
    (T : Finset V) (hv : v ∈ T) (hw : H.partner ∈ T) :
    CopiedSupportedOn G T H.coefficients := by
  intro i hi
  have hleft : i ≠ (⟨Q.left,H.leftEdge⟩ : BodyEdgeOccurrence G Finset.univ) := by
    intro heq
    subst i
    obtain ⟨z,hz,hzT⟩ := hi
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hzT hv
    · exact hzT hw
  have hright : i ≠ (⟨Q.right,H.rightEdge⟩ : BodyEdgeOccurrence G Finset.univ) := by
    intro heq
    subst i
    obtain ⟨z,hz,hzT⟩ := hi
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hzT hv
    · exact hzT hw
  simp [TwoBodyPin.Hinge.coefficients, Pi.single_eq_of_ne hleft,
    Pi.single_eq_of_ne hright]

theorem CopiedSupportedOn.sub_smul
    {G : SimpleGraph V} {T : Finset V}
    {a b : BodyEdgeOccurrence G Finset.univ → ℝ}
    (ha : CopiedSupportedOn G T a) (hb : CopiedSupportedOn G T b) (c : ℝ) :
    CopiedSupportedOn G T (a-c•b) := by
  intro i hi
  simp only [Pi.sub_apply, Pi.smul_apply, ha i hi, hb i hi, smul_zero, sub_self]

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- Every prefix-supported residual stress has a prefix-supported copy
lift with zero load at every body copy of the selected two-body vertex.
This is the force normalization needed for Lemma 7.1. -/
theorem SoftScalarSystem.exists_prefix_lift_zero_at_twoBody
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (Q : TwoBodyPin M.graph v) (T : Finset V) (hv : v ∈ T)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hsK : s.val ∈ L.scalarKernel)
    (hsT : ∀ e, e ∉ vertexEdgeSet (maskedGraph M.graph Finset.univ) T → s.val e = 0) :
    ∃ a : compatibleCopiedCoefficients M.graph p Finset.univ,
      copiedToStress M.graph p Finset.univ a = s ∧
      CopiedSupportedOn M.graph T a.val ∧
      ∀ C : Body M.graph, (bodyCopyForces M.graph p Finset.univ a.val C).val v = 0 := by
  obtain ⟨a,ha,hasupp⟩ := exists_supported_copied_lift M.graph M.covered p T s hsT
  let F := copiedToLoads M.graph p Finset.univ a
  rcases Q.point_or_hinge with hQ | hHingeExists
  · refine ⟨a,ha,hasupp,?_⟩
    by_cases hδ : deletionRankDrop M.graph v = 5
    · let u : SoftPointPin M.graph := ⟨v,⟨Q,hQ,hδ⟩⟩
      have hz := L.point_force_zero_on_kernel u s hsK
      rw [← ha,TwoBodyPin.pointForceOnWholePrefix_copied] at hz
      have hk : F ∈ (u.pin.loadProjection p).ker := hz
      rw [u.pin.ker_loadProjection p] at hk
      intro C
      exact congrFun (LinearMap.mem_ker.mp hk) C
    · have hz : Q.loadProjection p F = 0 := by
        rw [Q.loadProjection_eq_zero_of_drop_ne_five M p hgen hp hδ]
        rfl
      have hk : F ∈ (Q.loadProjection p).ker := hz
      rw [Q.ker_loadProjection p] at hk
      intro C
      exact congrFun (LinearMap.mem_ker.mp hk) C
  · let H : Q.Hinge := Classical.choice hHingeExists
    by_cases hw : H.partner ∈ T
    · obtain ⟨c,hzero,haway⟩ := H.eliminate_load M p hgen hp F
      have hcancel : copyAggregate M.graph Finset.univ H.coefficients = 0 :=
        LinearMap.mem_ker.mp H.coefficients_cancel
      have hagg : copyAggregate M.graph Finset.univ (a.val-c•H.coefficients) = s.val := by
        rw [map_sub,map_smul,hcancel,smul_zero,sub_zero]
        exact congrArg Subtype.val ha
      let b : compatibleCopiedCoefficients M.graph p Finset.univ :=
        ⟨a.val-c•H.coefficients,by
          change copyAggregate M.graph Finset.univ (a.val-c•H.coefficients) ∈
            StressSpace (maskedGraph M.graph Finset.univ) p
          rw [hagg]
          exact s.property⟩
      have hload : copiedToLoads M.graph p Finset.univ b = F-c•H.mode p := by
        apply Subtype.ext
        change bodyCopyForces M.graph p Finset.univ (a.val-c•H.coefficients) =
          bodyCopyForces M.graph p Finset.univ a.val -
            c • bodyCopyForces M.graph p Finset.univ H.coefficients
        rw [map_sub,map_smul]
      refine ⟨b,Subtype.ext hagg,hasupp.sub_smul (H.coefficients_supported T hv hw) c,?_⟩
      intro C
      have hc := congrFun hzero C
      rw [← hload] at hc
      exact hc
    · have hF : ∀ C z, z ∉ T → (F.val C).val z = 0 := by
        intro C z hz
        exact supported_copy_force_zero_outside M.graph p T a.val hasupp C z hz
      let A := supportedCompatibleLoad M.graph p T F hF
      have hz := H.prefix_load_zero_of_partner_not_mem M p hgen hp T hw A
      exact ⟨a,ha,hasupp,hz⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0013

section BundleSource0014
/- Source: Papers/RigidityStressCut.lean -/




@[expose] public section

/-!
# Cutting a stress across a one-vertex boundary

The exceptional modes in Lemma 6.5 are actual bar stresses.  This
module proves the equilibrium step used to isolate them: retaining
every edge incident with a vertex set preserves equilibrium whenever
the nonzero boundary ends at just one other vertex.  Equilibrium at
that vertex follows from cancellation of the total bar force.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint

open BodyLoads SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def edgeTouches (G : SimpleGraph V) (S : Finset V) (e : Edge G) : Prop :=
  ∃ v ∈ S, v ∈ e.val

/-- Literal coordinate restriction to the edges touching S. -/
def cutCoefficients (G : SimpleGraph V) (S : Finset V) :
    (Edge G → ℝ) →ₗ[ℝ] (Edge G → ℝ) where
  toFun a e := if edgeTouches G S e then a e else 0
  map_add' a b := by
    funext e
    by_cases h : edgeTouches G S e <;> simp [h]
  map_smul' c a := by
    funext e
    by_cases h : edgeTouches G S e <;> simp [h]

@[simp] theorem cutCoefficients_apply (G : SimpleGraph V) (S : Finset V)
    (a : Edge G → ℝ) (e : Edge G) :
    cutCoefficients G S a e = if edgeTouches G S e then a e else 0 := rfl

theorem cutCoefficients_incident (G : SimpleGraph V) (S : Finset V)
    (a : Edge G → ℝ) (v : V) (hv : v ∈ S) (e : IncidentEdge G v) :
    cutCoefficients G S a e.val = a e.val := by
  exact if_pos ⟨v, hv, e.property⟩

theorem cut_force_at_mem (G : SimpleGraph V) (p : Placement V 3)
    (S : Finset V) (a : Edge G → ℝ) (v : V) (hv : v ∈ S) :
    forceOperator G p (cutCoefficients G S a) v = forceOperator G p a v := by
  rw [forceOperator_vertex, forceOperator_vertex]
  apply Finset.sum_congr rfl
  intro e _
  rw [cutCoefficients_incident G S a v hv e]

/-- Every nonzero edge retained by the cut has both endpoints in S or
at the displayed boundary vertex.  This is a literal support condition. -/
def HasSingleBoundary (G : SimpleGraph V) (S : Finset V) (h : V)
    (a : Edge G → ℝ) : Prop :=
  ∀ e, edgeTouches G S e → a e ≠ 0 → ∀ v, v ∈ e.val → v ∈ S ∨ v = h

theorem cut_coeff_zero_outside (G : SimpleGraph V) (S : Finset V) (h : V)
    (a : Edge G → ℝ) (hboundary : HasSingleBoundary G S h a)
    (v : V) (hv : v ∉ S) (hvh : v ≠ h) (e : IncidentEdge G v) :
    cutCoefficients G S a e.val = 0 := by
  by_cases ht : edgeTouches G S e.val
  · rw [cutCoefficients_apply, if_pos ht]
    by_contra ha
    rcases hboundary e.val ht ha v e.property with hv' | hv'
    · exact hv hv'
    · exact hvh hv'
  · exact if_neg ht

theorem cut_force_zero_outside (G : SimpleGraph V) (p : Placement V 3)
    (S : Finset V) (h : V) (a : Edge G → ℝ)
    (hboundary : HasSingleBoundary G S h a)
    (v : V) (hv : v ∉ S) (hvh : v ≠ h) :
    forceOperator G p (cutCoefficients G S a) v = 0 := by
  rw [forceOperator_vertex]
  apply Finset.sum_eq_zero
  intro e _
  rw [cut_coeff_zero_outside G S h a hboundary v hv hvh e, zero_smul]

/-- The ordinary bar-force cancellation identity, with no equilibrium
assumption on the edge coefficients. -/
theorem sum_forceOperator (G : SimpleGraph V) (p : Placement V 3)
    (a : Edge G → ℝ) : (∑ v, forceOperator G p a v) = 0 :=
  ((mem_balancedLoads_iff p _).mp (forceOperator_balanced G p a)).1

/-- The retained edge coefficients are a genuine equilibrium stress. -/
theorem cut_mem_stress (G : SimpleGraph V) (p : Placement V 3)
    (S : Finset V) (h : V) (a : Edge G → ℝ)
    (ha : a ∈ StressSpace G p) (hboundary : HasSingleBoundary G S h a) :
    cutCoefficients G S a ∈ StressSpace G p := by
  have ha0 := (forceOperator_eq_zero_iff G p a).mpr ha
  have hoff (v : V) (hvh : v ≠ h) :
      forceOperator G p (cutCoefficients G S a) v = 0 := by
    by_cases hv : v ∈ S
    · rw [cut_force_at_mem G p S a v hv, ha0]
      rfl
    · exact cut_force_zero_outside G p S h a hboundary v hv hvh
  have hsum := sum_forceOperator G p (cutCoefficients G S a)
  have hsingle : (∑ v, forceOperator G p (cutCoefficients G S a) v) =
      forceOperator G p (cutCoefficients G S a) h := by
    apply Finset.sum_eq_single h
    · intro v _ hv
      exact hoff v hv
    · simp
  rw [hsingle] at hsum
  apply (forceOperator_eq_zero_iff G p _).mp
  funext v
  by_cases hv : v = h
  · subst v
    exact hsum
  · exact hoff v hv

/-- Its edge support lies in the induced graph on S together with h. -/
theorem cut_supported (G : SimpleGraph V) (S : Finset V) (h : V)
    (a : Edge G → ℝ) (hboundary : HasSingleBoundary G S h a)
    (e : Edge G) (he : ¬ ∀ v, v ∈ e.val → v ∈ insert h S) :
    cutCoefficients G S a e = 0 := by
  by_cases ht : edgeTouches G S e
  · rw [cutCoefficients_apply, if_pos ht]
    by_contra ha
    apply he
    intro v hv
    rcases hboundary e ht ha v hv with hS | hh
    · exact Finset.mem_insert_of_mem hS
    · exact Finset.mem_insert.mpr (Or.inl hh)
  · exact if_neg ht

/-- Subtracting the cut kills every star at a vertex in S. -/
theorem subtract_cut_incident_zero (G : SimpleGraph V) (S : Finset V)
    (a : Edge G → ℝ) (v : V) (hv : v ∈ S) (e : IncidentEdge G v) :
    (a - cutCoefficients G S a) e.val = 0 := by
  simp only [Pi.sub_apply, cutCoefficients_incident G S a v hv e, sub_self]

end Papers.Rigidity.BarJoint

end
end
end BundleSource0014

section BundleSource0015
/- Source: Papers/RigidityBalancedStarExtension.lean -/




@[expose] public section

/-!
# Extending a balanced star inside a complete fragment

This is the local extension step in Lemma 7.1.  A bar-coefficient vector
on a complete fragment whose force at `v` is zero has the same `v`-star
as a genuine stress on that fragment.  The construction first retains
the star, then resolves its opposite load on the complete fragment with
`v` deleted.  It works for every fragment size.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem starCoordinates_extendEdgeCoefficients
    {G H : SimpleGraph V} (h : H ≤ G) (v : V) (a : Edge H → ℝ) :
    starCoordinates G v (extendEdgeCoefficients h a) = starCoordinates H v a := by
  ext w
  by_cases hH : H.Adj v w
  · rw [starCoordinates_of_adj G v w _ (h hH), starCoordinates_of_adj H v w a hH]
    exact extendEdgeCoefficients_inside h a ⟨s(v,w),hH⟩
  · rw [starCoordinates_of_not_adj H v w a hH]
    by_cases hG : G.Adj v w
    · rw [starCoordinates_of_adj G v w _ hG]
      exact extendEdgeCoefficients_outside h a ⟨s(v,w),hG⟩ hH
    · exact starCoordinates_of_not_adj G v w _ hG

theorem starCoordinates_eq_of_incident_eq
    (G : SimpleGraph V) (v : V) (a b : Edge G → ℝ)
    (h : ∀ e : IncidentEdge G v, a e.val = b e.val) :
    starCoordinates G v a = starCoordinates G v b := by
  ext w
  by_cases hG : G.Adj v w
  · rw [starCoordinates_of_adj G v w a hG, starCoordinates_of_adj G v w b hG]
    exact h ⟨⟨s(v,w),hG⟩,Sym2.mem_mk_left v w⟩
  · rw [starCoordinates_of_not_adj G v w a hG, starCoordinates_of_not_adj G v w b hG]

theorem extended_star_eq_of_restricted_star_eq
    {G H : SimpleGraph V} (h : H ≤ G) (v : V)
    (a : Edge G → ℝ) (b : Edge H → ℝ)
    (ha : ∀ e, e.val ∉ H.edgeSet → a e = 0)
    (hb : ∀ e : IncidentEdge H v, b e.val = restrictEdgeCoefficients h a e.val) :
    starCoordinates G v (extendEdgeCoefficients h b) = starCoordinates G v a := by
  apply starCoordinates_eq_of_incident_eq
  intro e
  by_cases he : e.val.val ∈ H.edgeSet
  · let d : Edge H := ⟨e.val.val,he⟩
    have hed : e.val = edgeInclusion h d := rfl
    rw [hed,extendEdgeCoefficients_inside]
    exact hb ⟨d,e.property⟩
  · rw [extendEdgeCoefficients_outside h b e.val he,ha e.val he]

theorem cliqueOn_mono_finset {S T : Finset V} (h : S ⊆ T) :
    cliqueOn S ≤ cliqueOn T := by
  intro v w hvw
  exact ⟨hvw.1, h hvw.2.1, h hvw.2.2⟩

/-- A literal balanced star extends to a local equilibrium stress,
without requiring the rest of the displayed edge vector to equilibrate. -/
theorem exists_localStress_with_same_star
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (S : Finset V) (v : V) (a : Edge (cliqueOn S) → ℝ)
    (hbalance : forceOperator (cliqueOn S) p a v = 0) :
    ∃ s : StressSpace (cliqueOn S) p,
      ∀ e : IncidentEdge (cliqueOn S) v, s.val e.val = a e.val := by
  let b := cutCoefficients (cliqueOn S) {v} a
  have hbv : forceOperator (cliqueOn S) p b v = 0 := by
    rw [cut_force_at_mem (cliqueOn S) p {v} a v (by simp)]
    exact hbalance
  have hb : forceOperator (cliqueOn S) p b ∈ balancedLoadsOn p (S.erase v) := by
    refine ⟨forceOperator_balanced (cliqueOn S) p b, ?_⟩
    intro w hw
    by_cases hwv : w = v
    · subst w
      exact hbv
    · have hwS : w ∉ S := by
        intro hwS
        exact hw (Finset.mem_erase.mpr ⟨hwv, hwS⟩)
      exact clique_force_zero_outside p S b w hwS
  obtain ⟨c, hc⟩ : forceOperator (cliqueOn S) p b ∈
      (forceOperator (cliqueOn (S.erase v)) p).range := by
    rw [range_clique_forceOperator p hp]
    exact hb
  let hle : cliqueOn (S.erase v) ≤ cliqueOn S :=
    cliqueOn_mono_finset (Finset.erase_subset v S)
  let d := extendEdgeCoefficients hle c
  have hstress : b - d ∈ StressSpace (cliqueOn S) p := by
    apply (forceOperator_eq_zero_iff (cliqueOn S) p _).mp
    rw [map_sub, forceOperator_extendEdgeCoefficients, hc, sub_self]
  refine ⟨⟨b-d, hstress⟩, ?_⟩
  intro e
  have hnot : e.val.val ∉ (cliqueOn (S.erase v)).edgeSet := by
    intro he
    rw [← Sym2.other_spec e.property] at he
    change (cliqueOn (S.erase v)).Adj v (incidentOther (cliqueOn S) v e) at he
    exact Finset.notMem_erase v S he.2.1
  change b e.val - extendEdgeCoefficients hle c e.val = a e.val
  rw [extendEdgeCoefficients_outside hle c e.val hnot, sub_zero]
  exact cutCoefficients_incident (cliqueOn S) {v} a v (by simp) e

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0015

section BundleSource0016
/- Source: Papers/RigidityPrefixLocalStars.lean -/




@[expose] public section

/-!
# Local body stresses account for a two-body prefix star

The normalization is converted into actual local stresses.  Every
local summand retains the given induced-prefix support.  The final
star equality is an equality of ordinary graph-edge coefficients.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

def bodyFragmentInclusion (G : SimpleGraph V) (C : Body G) (T : Finset V) :
    cliqueOn (C.val ∩ T) ≤ cliqueOn (C.val ∩ Finset.univ) :=
  cliqueOn_mono_finset (by
    intro w hw
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,Finset.mem_univ _⟩)

theorem supported_copy_restriction_zero_outside
    (G : SimpleGraph V) (T : Finset V)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ) (ha : CopiedSupportedOn G T a)
    (C : Body G) (e : Edge (cliqueOn (C.val ∩ Finset.univ)))
    (he : e.val ∉ (cliqueOn (C.val ∩ T)).edgeSet) :
    bodyCopyRestriction G Finset.univ C a e = 0 := by
  by_contra hne
  have hT (w : V) (hw : w ∈ e.val) : w ∈ T := by
    by_contra hwT
    exact hne (ha ⟨C,e⟩ ⟨w,hw,hwT⟩)
  have hefull : (cliqueOn (C.val ∩ Finset.univ)).Adj e.val.out.1 e.val.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.val.out_eq]
    exact e.property
  apply he
  rw [← e.val.out_eq]
  exact ⟨hefull.1,
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hefull.2.1).1,hT _ (Sym2.out_fst_mem _)⟩,
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hefull.2.2).1,hT _ (Sym2.out_snd_mem _)⟩⟩

/-- One body's zero force at v can be replaced by an internal stress
with precisely the same star and the same prefix support. -/
theorem exists_body_local_stress_with_prefix_star
    (G : SimpleGraph V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ) (ha : CopiedSupportedOn G T a)
    (C : Body G) (v : V)
    (hF : (bodyCopyForces G p Finset.univ a C).val v = 0) :
    ∃ s : StressSpace (cliqueOn (C.val ∩ Finset.univ)) p,
      starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v s.val =
        starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
          (bodyCopyRestriction G Finset.univ C a) ∧
      ∀ e, (∃ w, w ∈ e.val ∧ w ∉ T) → s.val e = 0 := by
  let h := bodyFragmentInclusion G C T
  let b := restrictEdgeCoefficients h (bodyCopyRestriction G Finset.univ C a)
  have hsupport := supported_copy_restriction_zero_outside G T a ha C
  have hext : extendEdgeCoefficients h b = bodyCopyRestriction G Finset.univ C a :=
    extend_restrictEdgeCoefficients h _ hsupport
  have hb : forceOperator (cliqueOn (C.val ∩ T)) p b v = 0 := by
    rw [← forceOperator_extendEdgeCoefficients h p b,hext]
    exact hF
  obtain ⟨s,hs⟩ := exists_localStress_with_same_star p hp (C.val ∩ T) v b hb
  let d := (subgraphStressEquiv h p s)
  refine ⟨⟨d.val,d.property.1⟩, ?_, ?_⟩
  · exact extended_star_eq_of_restricted_star_eq h v _ s.val hsupport hs
  · intro e he
    apply d.property.2 e
    intro hmem
    obtain ⟨w,hw,hwT⟩ := he
    change e.val ∈ (cliqueOn (C.val ∩ T)).edgeSet at hmem
    rw [← Sym2.other_spec hw] at hmem
    change (cliqueOn (C.val ∩ T)).Adj w (Sym2.Mem.other hw) at hmem
    exact hwT (Finset.mem_inter.mp hmem.2.1).2

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- The actual prefix star is the sum of actual local prefix stresses.
No direct-sum or star-surjectivity hypothesis is inserted. -/
theorem SoftScalarSystem.exists_local_prefix_stars
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (Q : TwoBodyPin M.graph v) (T : Finset V) (hv : v ∈ T)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hsK : s.val ∈ L.scalarKernel)
    (hsT : ∀ e, e ∉ vertexEdgeSet (maskedGraph M.graph Finset.univ) T → s.val e = 0) :
    ∃ b : BodyFragmentStresses M.graph p Finset.univ,
      starCoordinates (maskedGraph M.graph Finset.univ) v
        (localPrefixStressSum M.graph p Finset.univ b).val =
      starCoordinates (maskedGraph M.graph Finset.univ) v s.val ∧
      ∀ C e, (∃ w, w ∈ e.val ∧ w ∉ T) → (b C).val e = 0 := by
  obtain ⟨a,ha,hsupp,hzero⟩ :=
    L.exists_prefix_lift_zero_at_twoBody hgen hp v Q T hv s hsK hsT
  have hex (C : Body M.graph) := exists_body_local_stress_with_prefix_star
    M.graph p hp T a.val hsupp C v (hzero C)
  choose b hstar hsupport using hex
  refine ⟨b,?_,hsupport⟩
  rw [localPrefixStressSum_val,← ha,copiedToStress_val,copyAggregate_eq_sum_extensions,
    map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [starCoordinates_extendEdgeCoefficients,starCoordinates_extendEdgeCoefficients]
  exact hstar C

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0016

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0016/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0016.json"

section BundleSource0017
/- Source: Papers/RigidityCliqueContribution.lean -/







@[expose] public section

/-!
# The exact expected rank contribution in a complete body

Permutation symmetry makes the expected contribution identical at every
vertex of a complete body. Isolated labels contribute zero. The exact
sum of contributions and the complete-graph rank then give `3 - 6/m`.
This uses the same uniform order on the full vertex set as the stress
ledger; no separate probability model for a body is assumed.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint
open UniformOrders
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem prefixGraph_relabel_perm (G : SimpleGraph V) (e : Equiv.Perm V)
    (σ : Outcome V) (k : ℕ) :
    (prefixGraph G σ k).comap e.symm =
      prefixGraph (G.comap e.symm) (e.symm.trans σ) k := by
  ext a b
  rfl

theorem rankContribution_relabel_perm (G : SimpleGraph V)
    (e : Equiv.Perm V) (v : V) :
    rankContribution (G.comap e.symm) (e v) = rankContribution G v := by
  let t : Outcome V ≃ Outcome V :=
    { toFun := fun σ => e.symm.trans σ
      invFun := fun σ => e.trans σ
      left_inv := by intro σ; ext w; simp
      right_inv := by intro σ; ext w; simp }
  let f : Outcome V → ℝ := fun σ =>
    (genericRigidityRank (prefixGraph (G.comap e.symm) σ ((σ (e v)).val + 1)) 3 : ℝ) -
      genericRigidityRank (prefixGraph (G.comap e.symm) σ (σ (e v)).val) 3
  have he (σ : Outcome V) : f (t σ) =
      (genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
        genericRigidityRank (prefixGraph G σ (σ v).val) 3 := by
    change (genericRigidityRank
        (prefixGraph (G.comap e.symm) (e.symm.trans σ)
          ((σ (e.symm (e v))).val + 1)) 3 : ℝ) -
      genericRigidityRank
        (prefixGraph (G.comap e.symm) (e.symm.trans σ)
          (σ (e.symm (e v))).val) 3 = _
    simp only [Equiv.symm_apply_apply]
    rw [← prefixGraph_relabel_perm,← prefixGraph_relabel_perm,
      genericRigidityRank_relabel,genericRigidityRank_relabel]
  unfold rankContribution mean
  rw [← Equiv.sum_comp t f]
  simp only [he]

theorem rankContribution_eq_zero_of_isolated (G : SimpleGraph V) (v : V)
    (hv : ∀ w, ¬ G.Adj v w) : rankContribution G v = 0 := by
  have hprefix (σ : Outcome V) :
      prefixGraph G σ ((σ v).val + 1) = prefixGraph G σ (σ v).val := by
    ext a b
    constructor
    · rintro ⟨hab,ha,hb⟩
      have hav : a ≠ v := fun h => hv b (h ▸ hab)
      have hbv : b ≠ v := fun h => hv a (h ▸ hab.symm)
      refine ⟨hab,?_,?_⟩
      · have hne : (σ a).val ≠ (σ v).val :=
          fun h => hav (σ.injective (Fin.ext h))
        omega
      · have hne : (σ b).val ≠ (σ v).val :=
          fun h => hbv (σ.injective (Fin.ext h))
        omega
    · rintro ⟨hab,ha,hb⟩
      exact ⟨hab,by omega,by omega⟩
  simp only [rankContribution,hprefix,sub_self,mean_const]

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity.BodyLoads
open BarJoint UniformOrders
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem cliqueOn_comap_swap (S : Finset V) (v w : V)
    (hv : v ∈ S) (hw : w ∈ S) :
    (cliqueOn S).comap (Equiv.swap v w).symm = cliqueOn S := by
  have hm (a : V) : Equiv.swap v w a ∈ S ↔ a ∈ S := by
    by_cases hav : a = v
    · subst a
      simp [hv,hw]
    by_cases haw : a = w
    · subst a
      simp [hv,hw]
    simp [Equiv.swap_apply_of_ne_of_ne hav haw]
  ext a b
  simp only [SimpleGraph.comap_adj,Equiv.symm_swap,cliqueOn,
    (Equiv.swap v w).injective.ne_iff,hm]

theorem clique_rankContribution_eq (S : Finset V) (v w : V)
    (hv : v ∈ S) (hw : w ∈ S) :
    rankContribution (cliqueOn S) v = rankContribution (cliqueOn S) w := by
  have h := rankContribution_relabel_perm (cliqueOn S) (Equiv.swap v w) v
  rw [cliqueOn_comap_swap S v w hv hw,Equiv.swap_apply_left] at h
  exact h.symm

theorem clique_rankContribution_zero (S : Finset V) (v : V) (hv : v ∉ S) :
    rankContribution (cliqueOn S) v = 0 := by
  apply rankContribution_eq_zero_of_isolated
  intro w h
  exact hv h.2.1

/-- The exact local expectation used in Lemma 7.1, with arbitrary
isolated vertices elsewhere in the ambient order. -/
theorem clique_rankContribution (S : Finset V) (v : V) (hv : v ∈ S)
    (hS : 3 ≤ S.card) :
    rankContribution (cliqueOn S) v = 3 - 6 / (S.card : ℝ) := by
  have hs : (∑ w : V, rankContribution (cliqueOn S) w) =
      (S.card : ℝ) * rankContribution (cliqueOn S) v := by
    calc
      _ = ∑ w ∈ S, rankContribution (cliqueOn S) w := by
        symm
        exact Finset.sum_subset (Finset.subset_univ S)
          (fun w _ hw => clique_rankContribution_zero S w hw)
      _ = ∑ _w ∈ S, rankContribution (cliqueOn S) v := by
        apply Finset.sum_congr rfl
        intro w hw
        exact clique_rankContribution_eq S w v hw hv
      _ = _ := by simp
  have hRank : genericRigidityRank (cliqueOn S) 3 =
      genericRigidityRank (SimpleGraph.completeGraph S) 3 := by
    rw [cliqueOn_eq_liftComplete,genericRigidityRank_liftGraph]
  have hr := sum_rankContribution (cliqueOn S)
  rw [hs,hRank] at hr
  have hc := genericCompleteRank_add_six (V := S) (by simpa using hS)
  have hcR := congrArg (fun n : ℕ => (n : ℝ)) hc
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Fintype.card_coe] at hcR
  have hpos : (S.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : S.card ≠ 0)
  apply (eq_sub_iff_add_eq).mpr
  apply (mul_left_cancel₀ hpos)
  rw [mul_add,hr,mul_div_cancel₀ _ hpos]
  nlinarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0017

section BundleSource0018
/- Source: Papers/RigidityTwoBodyBirth.lean -/





@[expose] public section

/-!
# Exact prefix births at a two-body vertex

Rank-nullity identifies an actual supported-space increment with its
new star image. At a two-body vertex the prefix normalization and local
star extension identify this image with the local body-stress image.
The genuine direct-sum support theorem then supplies the sum of the
complete-fragment births.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint
open SupportedCode UniformOrders
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem stressPrefix_finrank_eq (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V) :
    Module.finrank ℝ (stressThrough G W σ v) =
      Module.finrank ℝ (stressBefore G W σ v) +
        Module.finrank ℝ ((stressThrough G W σ v).map (starRestriction G v)) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := stressThrough G W σ v) (V₂ := IncidentEdge G v → ℝ)
    ((starRestriction G v).domRestrict (stressThrough G W σ v))
  rw [LinearMap.range_domRestrict] at h
  have he := (supportedPrefixKernelEquiv W (edgesBefore G σ v) (edgesThrough G σ v)
    (incidentEdgeEmbedding G v) (edgesBefore_subset_edgesThrough G σ v)
    (incident_not_edgesBefore G σ v) (new_edge_incident G σ v)).finrank_eq
  change Module.finrank ℝ
      ((starRestriction G v).domRestrict (stressThrough G W σ v)).ker =
        Module.finrank ℝ (stressBefore G W σ v) at he
  rw [he] at h
  omega

theorem stressBirth_eq_of_star_image_eq (G : SimpleGraph V)
    (W Z : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V)
    (h : (stressThrough G W σ v).map (starRestriction G v) =
      (stressThrough G Z σ v).map (starRestriction G v)) :
    (Module.finrank ℝ (stressThrough G W σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G W σ v) =
      (Module.finrank ℝ (stressThrough G Z σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G Z σ v) := by
  have hW := stressPrefix_finrank_eq G W σ v
  have hZ := stressPrefix_finrank_eq G Z σ v
  rw [h] at hW
  exact_mod_cast (by omega :
    (Module.finrank ℝ (stressThrough G W σ v) : ℤ) -
        Module.finrank ℝ (stressBefore G W σ v) =
      (Module.finrank ℝ (stressThrough G Z σ v) : ℤ) -
        Module.finrank ℝ (stressBefore G Z σ v))

theorem starRestriction_eq_of_starCoordinates_eq (G : SimpleGraph V) (v : V)
    (a b : Edge G → ℝ) (h : starCoordinates G v a = starCoordinates G v b) :
    starRestriction G v a = starRestriction G v b := by
  ext e
  change a e.val = b e.val
  have he := congrFun h (incidentOther G v e)
  simpa only [starCoordinates_incidentOther] using he

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

def verticesThrough (σ : Outcome V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => σ w ≤ σ v)

def verticesBefore (σ : Outcome V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => σ w < σ v)

@[simp] theorem mem_verticesThrough (σ : Outcome V) (v w : V) :
    w ∈ verticesThrough σ v ↔ σ w ≤ σ v := by simp [verticesThrough]

@[simp] theorem mem_verticesBefore (σ : Outcome V) (v w : V) :
    w ∈ verticesBefore σ v ↔ σ w < σ v := by simp [verticesBefore]

theorem edgesThrough_eq_vertexEdgeSet (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    edgesThrough G σ v = vertexEdgeSet G (verticesThrough σ v) := by
  ext e
  simp only [edgesThrough,vertexEdgeSet,Set.mem_setOf_eq,mem_verticesThrough]

theorem edgesBefore_eq_vertexEdgeSet (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    edgesBefore G σ v = vertexEdgeSet G (verticesBefore σ v) := by
  ext e
  simp only [edgesBefore,vertexEdgeSet,Set.mem_setOf_eq,mem_verticesBefore]

variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.twoBody_prefix_star_image
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) (Q : TwoBodyPin M.graph v)
    (σ : Outcome V) :
    (stressThrough (maskedGraph M.graph Finset.univ) L.scalarKernel σ v).map
        (starRestriction (maskedGraph M.graph Finset.univ) v) =
      (stressThrough (maskedGraph M.graph Finset.univ)
        (fullLocalStressSpace (maskedGraph M.graph Finset.univ) p) σ v).map
          (starRestriction (maskedGraph M.graph Finset.univ) v) := by
  let G := maskedGraph M.graph Finset.univ
  apply le_antisymm
  · rintro x ⟨s,hs,rfl⟩
    let a : StressSpace G p := ⟨s,L.scalarKernel_le_stress hs.1⟩
    obtain ⟨b,hstar,hb⟩ := L.exists_local_prefix_stars hgen hp v Q
      (verticesThrough σ v) (by simp) a hs.1
        (by simpa only [← edgesThrough_eq_vertexEdgeSet] using hs.2)
    refine ⟨(localPrefixStressSum M.graph p Finset.univ b).val,?_,?_⟩
    · constructor
      · rw [fullLocalStressSpace_eq_wholePrefix]
        exact ⟨localPrefixStressSum M.graph p Finset.univ b,⟨b,rfl⟩,rfl⟩
      · simpa only [← edgesThrough_eq_vertexEdgeSet] using
          localPrefixStressSum_supported M.graph p (verticesThrough σ v) b hb
    · exact starRestriction_eq_of_starCoordinates_eq G v _ _ hstar
  · apply Submodule.map_mono
    intro s hs
    exact ⟨L.fullLocalStressSpace_le_kernel hs.1,hs.2⟩

theorem SoftScalarSystem.twoBody_birth_eq_local
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) (Q : TwoBodyPin M.graph v) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      stressDimensionContribution (maskedGraph M.graph Finset.univ)
        (fullLocalStressSpace (maskedGraph M.graph Finset.univ) p) v := by
  apply mean_congr
  intro σ
  exact stressBirth_eq_of_star_image_eq _ _ _ σ v
    (L.twoBody_prefix_star_image hgen hp v Q σ)

theorem clique_fragment_supported_finrank (p : Placement V 3)
    (S T : Finset V) :
    Module.finrank ℝ
        (supportedOn (StressSpace (cliqueOn S) p) (vertexEdgeSet (cliqueOn S) T)) =
      Module.finrank ℝ (StressSpace (cliqueOn (S ∩ T)) p) := by
  have hle : cliqueOn (S ∩ T) ≤ cliqueOn S :=
    cliqueOn_mono_finset Finset.inter_subset_left
  have hset : subgraphEdgeSet (cliqueOn S) (cliqueOn (S ∩ T)) =
      vertexEdgeSet (cliqueOn S) T := by
    rw [subgraphEdgeSet_cliqueOn,vertexEdgeSet_inter]
    ext e
    have heS : e ∈ vertexEdgeSet (cliqueOn S) S := by
      rcases e with ⟨e,he⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
        have h := (show (cliqueOn S).Adj a b from he)
        intro w hw
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact h.2.1
        · exact h.2.2
    simp only [Set.mem_inter_iff,heS,true_and]
  rw [← hset]
  exact (subgraphStressEquiv hle p).finrank_eq.symm

/-- Exact expectation of the actual local direct sum, retaining all
body fragments and all ambient labels. -/
theorem fullLocalStressSpace_contribution (M : MinimalCounterexample V)
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (v : V) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ)
        (fullLocalStressSpace (maskedGraph M.graph Finset.univ) p) v =
      ∑ C : Body M.graph,
        stressDimensionContribution (cliqueOn C.val) (StressSpace (cliqueOn C.val) p) v := by
  unfold stressDimensionContribution
  rw [← mean_sum]
  apply mean_congr
  intro σ
  have ht (H : SimpleGraph V) (W : Submodule ℝ (Edge H → ℝ)) :
      Module.finrank ℝ (stressThrough H W σ v) =
        Module.finrank ℝ (supportedOn W (vertexEdgeSet H (verticesThrough σ v))) :=
    congrArg (fun A : Set (Edge H) => Module.finrank ℝ (supportedOn W A))
      (edgesThrough_eq_vertexEdgeSet H σ v)
  have hb (H : SimpleGraph V) (W : Submodule ℝ (Edge H → ℝ)) :
      Module.finrank ℝ (stressBefore H W σ v) =
        Module.finrank ℝ (supportedOn W (vertexEdgeSet H (verticesBefore σ v))) :=
    congrArg (fun A : Set (Edge H) => Module.finrank ℝ (supportedOn W A))
      (edgesBefore_eq_vertexEdgeSet H σ v)
  simp only [ht,hb,fullLocalWholePrefix_finrank M p hp,clique_fragment_supported_finrank]
  push_cast
  rw [Finset.sum_sub_distrib]

theorem SoftScalarSystem.twoBody_birth_eq_sum_clique
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) (Q : TwoBodyPin M.graph v) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      ∑ C : Body M.graph,
        stressDimensionContribution (cliqueOn C.val) (StressSpace (cliqueOn C.val) p) v := by
  rw [L.twoBody_birth_eq_local hgen hp v Q]
  exact fullLocalStressSpace_contribution M p hp v

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0018

section BundleSource0019
/- Source: Papers/RigidityFiveCliqueStress.lean -/




@[expose] public section

/-!
# The unique K5 stress and its full edge support

The one-dimensional local stress and its ten nonzero coefficients are
derived from ordinary complete-graph rank and generic star equilibrium.
These properties justify the canonical coefficients of Section 7.2.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem cliqueOn_eq_map_complete (S : Finset V) :
    cliqueOn S = (SimpleGraph.completeGraph S).map
      (⟨Subtype.val,Subtype.val_injective⟩ : S ↪ V) := by
  ext v w
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨hne,hv,hw⟩
    exact ⟨⟨v,hv⟩,⟨w,hw⟩,fun h => hne (congrArg Subtype.val h),rfl,rfl⟩
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact ⟨fun h => hab (Subtype.ext h),a.property,b.property⟩

theorem card_clique_edges (S : Finset V) :
    Fintype.card (Edge (cliqueOn S)) = S.card.choose 2 := by
  change Fintype.card (cliqueOn S).edgeSet = S.card.choose 2
  rw [← Nat.card_eq_fintype_card,cliqueOn_eq_map_complete,Nat.card_eq_fintype_card,
    SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_map
      (⟨Subtype.val,Subtype.val_injective⟩ : S ↪ V) (SimpleGraph.completeGraph S)]
  simpa only [SimpleGraph.completeGraph_eq_top,Fintype.card_coe] using
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := S))

theorem clique_degree (S : Finset V) (v : V) (hv : v ∈ S) :
    (cliqueOn S).degree v = S.card-1 := by
  have hn : (cliqueOn S).neighborFinset v = S.erase v := by
    ext w
    rw [(cliqueOn S).mem_neighborFinset v w]
    change (v ≠ w ∧ v ∈ S ∧ w ∈ S) ↔ w ∈ S.erase v
    simp only [Finset.mem_erase,hv,true_and,ne_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_erase_of_mem hv]

theorem stress_clique_le_four_eq_bot
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (S : Finset V) (hS : S.card ≤ 4) : StressSpace (cliqueOn S) p = ⊥ := by
  apply le_antisymm
  · intro a ha
    rw [Submodule.mem_bot]
    funext e
    have hF := (forceOperator_eq_zero_iff (cliqueOn S) p a).mpr ha
    have he : (cliqueOn S).Adj e.val.out.1 e.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.val.out_eq]
      exact e.property
    have hs := clique_star_zero_of_zero_force p hp S hS e.val.out.1 he.2.1 a
      (congrFun hF e.val.out.1)
    have hz := congrFun hs e.val.out.2
    rw [starCoordinates_of_adj _ _ _ _ he] at hz
    simpa only [Pi.zero_apply,show (⟨s(e.val.out.1,e.val.out.2),he⟩ : Edge (cliqueOn S)) = e from
      Subtype.ext e.val.out_eq] using hz
  · exact bot_le

theorem fiveCliqueStress_finrank
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (S : Finset V) (hS : S.card = 5) :
    Module.finrank ℝ (StressSpace (cliqueOn S) p) = 1 := by
  have hr := genericCompleteRank_add_six (V := S) (by simpa [hS])
  have hRank : rigidityRank (cliqueOn S) p =
      genericRigidityRank (SimpleGraph.completeGraph S) 3 := by
    rw [hgen,cliqueOn_eq_liftComplete,genericRigidityRank_liftGraph]
  have h := rigidityRank_add_stress_dimension (cliqueOn S) p
  rw [hRank,card_clique_edges,hS] at h
  simp only [Fintype.card_coe,hS] at hr
  norm_num [Nat.choose] at h hr
  omega

theorem isolate_clique (S : Finset V) (v : V) :
    isolateVertex (cliqueOn S) v = cliqueOn (S.erase v) := by
  ext a b
  simp only [isolateVertex,cliqueOn,Finset.mem_erase]
  tauto

/-- Every one of the ten actual K5 edge coordinates is nonzero in
every nonzero local stress. -/
theorem fiveCliqueStress_edge_ne_zero
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (S : Finset V) (hS : S.card = 5)
    (s : StressSpace (cliqueOn S) p) (hs : s ≠ 0)
    (e : Edge (cliqueOn S)) : s.val e ≠ 0 := by
  intro hz
  let v := e.val.out.1
  have he : (cliqueOn S).Adj v e.val.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.val.out_eq]
    exact e.property
  let i : IncidentEdge (cliqueOn S) v := ⟨e,Sym2.out_fst_mem e.val⟩
  let f := (starRestriction (cliqueOn S) v).domRestrict (StressSpace (cliqueOn S) p)
  have hcard : Fintype.card (IncidentEdge (cliqueOn S) v) = 4 := by
    rw [card_incidentEdge_eq_degree,clique_degree S v he.2.1,hS]
  have hsupport : support (f s) ⊆ Finset.univ.erase i := by
    intro j hj
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro hji
    subst j
    exact (mem_support _ i).mp hj hz
  have hsmall : (support (f s)).card ≤ 3 := by
    have h := Finset.card_le_card hsupport
    simpa [hcard] using h
  have hzero : f s = 0 := by
    by_contra hne
    have hmin := stressStarCode_minimumSupport_four (cliqueOn S) p hp v
      (StressSpace (cliqueOn S) p) le_rfl
    have hm : f s ∈ stressStarCode (cliqueOn S) v (StressSpace (cliqueOn S) p) :=
      ⟨s.val,s.property,rfl⟩
    have hfour := hmin (f s) hm hne
    omega
  have hdeleted : StressSpace (isolateVertex (cliqueOn S) v) p = ⊥ := by
    rw [isolate_clique]
    exact stress_clique_le_four_eq_bot p hp (S.erase v) (by
      rw [Finset.card_erase_of_mem he.2.1,hS])
  have hstar := stressStar_finrank_add_deletedStress (cliqueOn S) p v
  rw [hdeleted,finrank_bot,add_zero] at hstar
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := StressSpace (cliqueOn S) p)
    (V₂ := IncidentEdge (cliqueOn S) v → ℝ) f
  rw [show f.range = stressStarCode (cliqueOn S) v (StressSpace (cliqueOn S) p) from
    LinearMap.range_domRestrict _ _,hstar] at hnull
  have hker : f.ker = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact hs ((LinearMap.ker_eq_bot.mp hker) (by simpa only [map_zero] using hzero))

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0019

section BundleSource0020
/- Source: Papers/RigidityTwoBodyContribution.lean -/




@[expose] public section

/-!
# Lemma 7.1: the exact two-body contribution

The prefix stress birth has already been identified with the sum of
local clique births. The remaining correction counts the common actual
edge of a hinge once. Point pins have no such edge; the maximal-body
intersection theorem excludes larger intersections.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem TwoBodyPin.neighborFinset (G : SimpleGraph V) (hG : K4Covered G)
    (v : V) (Q : TwoBodyPin G v) :
    G.neighborFinset v = (Q.left.val ∪ Q.right.val).erase v := by
  ext w
  constructor
  · intro hw
    have hadj := (G.mem_neighborFinset v w).mp hw
    obtain ⟨S,hS,hvS,hwS⟩ := hG.edge_in_body hadj
    have hC := Q.exhaustive ⟨S,hS⟩ hvS
    refine Finset.mem_erase.mpr ⟨hadj.ne.symm,?_⟩
    rcases hC with hC | hC
    · have heq : S = Q.left.val := congrArg Subtype.val hC
      exact Finset.mem_union_left _ (heq ▸ hwS)
    · have heq : S = Q.right.val := congrArg Subtype.val hC
      exact Finset.mem_union_right _ (heq ▸ hwS)
  · intro hw
    obtain ⟨hwv,hw⟩ := Finset.mem_erase.mp hw
    apply (G.mem_neighborFinset v w).mpr
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Q.left.property.2.1 Q.left_mem hw hwv.symm
    · exact Q.right.property.2.1 Q.right_mem hw hwv.symm

theorem TwoBodyPin.intersection_card (M : MinimalCounterexample V)
    (v : V) (Q : TwoBodyPin M.graph v) :
    (Q.left.val ∩ Q.right.val).card = if Q.IsPoint then 1 else 2 := by
  by_cases hp : Q.IsPoint
  · simp only [hp,ite_true]
    rw [hp,Finset.card_singleton]
  · simp only [hp,ite_false]
    have hupper := M.body_intersection_le_two Q.left.val Q.right.val
      Q.left.property Q.right.property (fun h => Q.distinct (Subtype.ext h))
    obtain h | hHingeExists := Q.point_or_hinge
    · exact False.elim (hp h)
    let H : Q.Hinge := Classical.choice hHingeExists
    have hsub : ({v,H.partner} : Finset V) ⊆ Q.left.val ∩ Q.right.val := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨Q.left_mem,Q.right_mem⟩
      · exact Finset.mem_inter.mpr ⟨H.left_mem,H.right_mem⟩
    have hlow := Finset.card_le_card hsub
    rw [Finset.card_pair H.distinct] at hlow
    omega

theorem TwoBodyPin.degree_add_correction (M : MinimalCounterexample V)
    (v : V) (Q : TwoBodyPin M.graph v) :
    M.graph.degree v + (if Q.IsPoint then 0 else 1) =
      (cliqueOn Q.left.val).degree v + (cliqueOn Q.right.val).degree v := by
  have hu := Finset.card_union_add_card_inter Q.left.val Q.right.val
  have hv : v ∈ Q.left.val ∪ Q.right.val := Finset.mem_union_left _ Q.left_mem
  have hdeg : M.graph.degree v = (Q.left.val ∪ Q.right.val).card-1 := by
    rw [← M.graph.card_neighborFinset_eq_degree v,TwoBodyPin.neighborFinset M.graph M.covered v Q,
      Finset.card_erase_of_mem hv]
  have hl := Q.left.property.1
  have hr := Q.right.property.1
  have hi := TwoBodyPin.intersection_card M v Q
  rw [clique_degree _ _ Q.left_mem,clique_degree _ _ Q.right_mem,hdeg]
  by_cases hp : Q.IsPoint
  · simp only [hp,ite_true] at hi ⊢
    omega
  · simp only [hp,ite_false] at hi ⊢
    omega

theorem clique_stressContribution_zero (p : Placement V 3)
    (hgen : IsGenericPlacement p) (S : Finset V) (v : V) (hv : v ∉ S) :
    stressDimensionContribution (cliqueOn S) (StressSpace (cliqueOn S) p) v = 0 := by
  have hrc := rankContribution_eq_degree_half_sub_stress (cliqueOn S) p hgen v
  have hd : (cliqueOn S).degree v = 0 :=
    (SimpleGraph.degree_eq_zero (cliqueOn S) v).mpr (fun w h => hv h.2.1)
  rw [clique_rankContribution_zero S v hv,hd] at hrc
  norm_num at hrc
  linarith

variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.twoBody_birth_eq_pair
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) (Q : TwoBodyPin M.graph v) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      stressDimensionContribution (cliqueOn Q.left.val)
          (StressSpace (cliqueOn Q.left.val) p) v +
        stressDimensionContribution (cliqueOn Q.right.val)
          (StressSpace (cliqueOn Q.right.val) p) v := by
  rw [L.twoBody_birth_eq_sum_clique hgen hp v Q]
  let f : Body M.graph → ℝ := fun C =>
    stressDimensionContribution (cliqueOn C.val) (StressSpace (cliqueOn C.val) p) v
  have hs : ∑ C ∈ ({Q.left,Q.right} : Finset (Body M.graph)), f C =
      ∑ C : Body M.graph, f C := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro C _ hC
    apply clique_stressContribution_zero p hgen C.val v
    intro hv
    rcases Q.exhaustive C hv with rfl | rfl
    · exact hC (by simp)
    · exact hC (by simp)
  simpa only [Finset.sum_pair Q.distinct,f] using hs.symm

/-- Lemma 7.1, with the point/hinge distinction proved from the actual
maximal bodies and with the literal scalar-annihilator prefix space. -/
theorem SoftScalarSystem.two_body_contribution
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) (Q : TwoBodyPin M.graph v) :
    (M.graph.degree v : ℝ) / 2 -
        stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      (3 - 6 / (Q.left.val.card : ℝ)) +
        (3 - 6 / (Q.right.val.card : ℝ)) - (if Q.IsPoint then 0 else 1 / 2) := by
  rw [L.twoBody_birth_eq_pair hgen hp v Q]
  have hl := rankContribution_eq_degree_half_sub_stress (cliqueOn Q.left.val) p hgen v
  have hr := rankContribution_eq_degree_half_sub_stress (cliqueOn Q.right.val) p hgen v
  rw [clique_rankContribution _ _ Q.left_mem (by have h := Q.left.property.1; omega)] at hl
  rw [clique_rankContribution _ _ Q.right_mem (by have h := Q.right.property.1; omega)] at hr
  have hd := TwoBodyPin.degree_add_correction M v Q
  by_cases hpoint : Q.IsPoint
  · simp only [hpoint,ite_true] at hd ⊢
    have hdR := congrArg (fun n : ℕ => (n : ℝ)) hd
    push_cast at hdR
    linarith
  · simp only [hpoint,ite_false] at hd ⊢
    have hdR := congrArg (fun n : ℕ => (n : ℝ)) hd
    push_cast at hdR
    linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0020

section BundleSource0021
/- Source: Papers/RigidityIncidenceAllocation.lean -/




@[expose] public section

/-!
# Allocating the actual two-body excess to maximal bodies

This file implements the incidence table of Section 7.1. Its sum at a
two-body vertex is exactly the proved expected-rank excess. The body
credits used in Section 7.3 are lower bounds for the sum of these
literal allocations, including the negative K5/K4 hinge incidences.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def TwoBodyPin.swap {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) : TwoBodyPin G v where
  left := Q.right
  right := Q.left
  distinct := Q.distinct.symm
  left_mem := Q.right_mem
  right_mem := Q.left_mem
  exhaustive C hC := (Q.exhaustive C hC).symm

@[simp] theorem TwoBodyPin.swap_left {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) :
    Q.swap.left = Q.right := rfl

@[simp] theorem TwoBodyPin.swap_right {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) :
    Q.swap.right = Q.left := rfl

@[simp] theorem TwoBodyPin.swap_isPoint {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) :
    Q.swap.IsPoint ↔ Q.IsPoint := by
  simp only [TwoBodyPin.IsPoint,TwoBodyPin.swap,Finset.inter_comm]

theorem TwoBodyPin.isPoint_of_soft {G : SimpleGraph V} {v : V}
    (Q : TwoBodyPin G v) (hv : IsSoftPointPin G v) : Q.IsPoint := by
  obtain ⟨R,hR,hδ⟩ := hv
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_inter.mpr ⟨Q.left_mem,Q.right_mem⟩,?_⟩
  intro w hw
  exact hR.no_shared_edge Q.left Q.right Q.distinct Q.left_mem Q.right_mem w
    (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2

/-- The degree-six minimum excludes a two-body hinge between two
tetrahedra; this is the exact exceptional incidence excluded by the table. -/
theorem TwoBodyPin.hinge_not_both_tetrahedra
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hn : ¬ Q.IsPoint) : Q.left.val.card ≠ 4 ∨ Q.right.val.card ≠ 4 := by
  have hi := Q.intersection_card M v
  rw [if_neg hn] at hi
  have hu := Finset.card_union_add_card_inter Q.left.val Q.right.val
  have hc := congrArg Finset.card (Q.closedNeighborhood_eq_union M.covered)
  rw [card_closedNeighborhood] at hc
  have hd := M.connected.degree_ge v
  by_contra h
  push_neg at h
  omega

def bodyOrderExcess (m : ℕ) : ℝ := 3 / 2 - 6 / (m : ℝ)

/-- One row of the incidence table, oriented toward a body of order a. -/
def sideAllocation (a b : ℕ) (point : Prop) : ℝ :=
  if point then bodyOrderExcess a else
    if a = 4 then 0 else if b = 4 then bodyOrderExcess a - 1 / 2
      else bodyOrderExcess a - 1 / 4

theorem sideAllocation_pair (a b : ℕ) (point : Prop)
    (hhinge : ¬ point → a ≠ 4 ∨ b ≠ 4) :
    sideAllocation a b point + sideAllocation b a point =
      bodyOrderExcess a + bodyOrderExcess b - (if point then 0 else 1 / 2) := by
  by_cases hp : point
  · simp [sideAllocation,hp]
  · have hn := hhinge hp
    by_cases ha : a = 4
    · have hb : b ≠ 4 := hn.resolve_left (not_not.mpr ha)
      simp only [sideAllocation,if_neg hp,if_pos ha,if_neg hb,bodyOrderExcess,ha]
      norm_num <;> ring
    · by_cases hb : b = 4
      · simp only [sideAllocation,if_neg hp,if_neg ha,if_pos hb,bodyOrderExcess,hb]
        norm_num <;> ring
      · simp only [sideAllocation,if_neg hp,if_neg ha,if_neg hb]
        ring

theorem bodyOrderExcess_ge_half (m : ℕ) (hm : 6 ≤ m) : 1 / 2 ≤ bodyOrderExcess m := by
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  have hdiv : (6 : ℝ) / m ≤ 1 := (div_le_one hpos).mpr hmR
  unfold bodyOrderExcess
  linarith

def twoBodyPinAt (M : MinimalCounterexample V) (v : V) (hv : ¬ IsHypervertex M.graph v) :
    TwoBodyPin M.graph v := Classical.choice (nonempty_twoBodyPin_of_not_hypervertex M v hv)

/-- The allocation is zero away from the two actual incident bodies,
and zero at hypervertices, which have their separate account. -/
def incidenceAllocation (M : MinimalCounterexample V) (C : Body M.graph) (v : V) : ℝ :=
  if hv : IsHypervertex M.graph v then 0 else
    let Q := twoBodyPinAt M v hv
    (if C = Q.left then sideAllocation Q.left.val.card Q.right.val.card Q.IsPoint else 0) +
    (if C = Q.right then sideAllocation Q.right.val.card Q.left.val.card Q.IsPoint else 0)

theorem sum_incidenceAllocation_at_hypervertex
    (M : MinimalCounterexample V) (v : V) (hv : IsHypervertex M.graph v) :
    (∑ C : Body M.graph, incidenceAllocation M C v) = 0 := by
  simp [incidenceAllocation,hv]

theorem sum_incidenceAllocation_at_twoBody
    (M : MinimalCounterexample V) (v : V) (hv : ¬ IsHypervertex M.graph v) :
    let Q := twoBodyPinAt M v hv
    (∑ C : Body M.graph, incidenceAllocation M C v) =
      bodyOrderExcess Q.left.val.card + bodyOrderExcess Q.right.val.card -
        (if Q.IsPoint then 0 else 1 / 2) := by
  intro Q
  simp only [incidenceAllocation,dif_neg hv]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact sideAllocation_pair _ _ _ (Q.hinge_not_both_tetrahedra M)

/-- The conservative body credit, written one original vertex at a
time so that its total can be compared with the actual incidence table. -/
def bodyVertexCredit (M : MinimalCounterexample V) (C : Body M.graph) (v : V) : ℝ :=
  if v ∈ C.val then
    if C.val.card = 5 then
      if IsSoftPointPin M.graph v then 3 / 10 else
      if ∃ h, Nonempty (CorePort M C h v) then -(1 / 5) else
      if IsHypervertex M.graph v then 0 else 1 / 20
    else if 6 ≤ C.val.card ∧ IsSoftPointPin M.graph v then 1 / 2 else 0
  else 0

/-- A type-B witness forces the opposite body in every orientation to
be its actual outer tetrahedron. -/
theorem TwoBodyPin.other_card_of_typeB
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hB : ∃ h, Nonempty (CorePort M Q.left h v)) :
    Q.right.val.card = 4 ∧ ¬ Q.IsPoint := by
  obtain ⟨h,⟨P⟩⟩ := hB
  have hout : P.outer = Q.right := by
    rcases Q.exhaustive P.outer P.port_mem_outer with heq | heq
    · exact False.elim (P.outer_ne_core heq)
    · exact heq
  refine ⟨by rw [← hout]; exact P.outer_card,?_⟩
  intro hpoint
  have heq := hpoint.no_shared_edge Q.left P.outer P.outer_ne_core.symm
    Q.left_mem P.port_mem_outer h P.partner_mem_core P.partner_mem_outer
  exact P.port_ne_partner heq.symm

theorem bodyVertexCredit_le_sideAllocation
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v) :
    bodyVertexCredit M Q.left v ≤
      sideAllocation Q.left.val.card Q.right.val.card Q.IsPoint := by
  rw [bodyVertexCredit,if_pos Q.left_mem]
  by_cases hC : Q.left.val.card = 5
  · rw [if_pos hC]
    by_cases hs : IsSoftPointPin M.graph v
    · have hpoint := Q.isPoint_of_soft hs
      norm_num [hs,sideAllocation,hpoint,bodyOrderExcess,hC]
    · rw [if_neg hs]
      by_cases hb : ∃ h, Nonempty (CorePort M Q.left h v)
      · obtain ⟨hright,hnpoint⟩ := Q.other_card_of_typeB M hb
        norm_num [hb,sideAllocation,hnpoint,bodyOrderExcess,hC,hright]
      · rw [if_neg hb,if_neg Q.not_hypervertex]
        by_cases hpoint : Q.IsPoint
        · norm_num [sideAllocation,hpoint,bodyOrderExcess,hC]
        · have hright : Q.right.val.card ≠ 4 := by
            intro hr
            let H : Q.Hinge := Classical.choice (Q.point_or_hinge.resolve_left hpoint)
            exact hb ⟨H.partner,⟨⟨Q,rfl,hC,hr,H,rfl⟩⟩⟩
          norm_num [sideAllocation,hpoint,bodyOrderExcess,hC,hright]
  · rw [if_neg hC]
    by_cases hlarge : 6 ≤ Q.left.val.card
    · have hq := bodyOrderExcess_ge_half Q.left.val.card hlarge
      have hfour : Q.left.val.card ≠ 4 := by omega
      by_cases hs : IsSoftPointPin M.graph v
      · have hpoint := Q.isPoint_of_soft hs
        simp only [hlarge,hs,and_self,if_true,sideAllocation,if_pos hpoint]
        exact hq
      · simp only [hs,and_false,if_false]
        unfold sideAllocation
        split_ifs <;> linarith
    · have hfour : Q.left.val.card = 4 := by have := Q.left.property.1; omega
      simp only [hlarge,false_and,if_false,sideAllocation,hfour]
      split_ifs <;> norm_num [bodyOrderExcess] at *

theorem bodyVertexCredit_eq_zero_at_hypervertex
    (M : MinimalCounterexample V) (C : Body M.graph) (v : V)
    (hh : IsHypervertex M.graph v) : bodyVertexCredit M C v = 0 := by
  have hs : ¬ IsSoftPointPin M.graph v := fun h => softPointPin_not_hypervertex _ _ h hh
  have hb : ¬ (∃ h, Nonempty (CorePort M C h v)) := fun h => bodyTypeB_not_hyper _ _ _ h hh
  simp [bodyVertexCredit,hs,hb,hh]

theorem bodyVertexCredit_le_incidenceAllocation
    (M : MinimalCounterexample V) (C : Body M.graph) (v : V) :
    bodyVertexCredit M C v ≤ incidenceAllocation M C v := by
  by_cases hh : IsHypervertex M.graph v
  · simp [incidenceAllocation,hh,bodyVertexCredit_eq_zero_at_hypervertex M C v hh]
  · let Q := twoBodyPinAt M v hh
    have hformula : incidenceAllocation M C v =
        (if C = Q.left then sideAllocation Q.left.val.card Q.right.val.card Q.IsPoint else 0) +
        (if C = Q.right then sideAllocation Q.right.val.card Q.left.val.card Q.IsPoint else 0) := by
      simp only [incidenceAllocation,dif_neg hh,Q]
    rw [hformula]
    by_cases hvC : v ∈ C.val
    · rcases Q.exhaustive C hvC with heq | heq
      · subst C
        rw [if_pos rfl,if_neg Q.distinct,add_zero]
        exact bodyVertexCredit_le_sideAllocation M Q
      · subst C
        rw [if_neg Q.distinct.symm,if_pos rfl,zero_add]
        have h := bodyVertexCredit_le_sideAllocation M Q.swap
        change bodyVertexCredit M Q.right v ≤
          sideAllocation Q.right.val.card Q.left.val.card Q.swap.IsPoint at h
        rw [show Q.swap.IsPoint = Q.IsPoint from propext Q.swap_isPoint] at h
        exact h
    · have hleft : C ≠ Q.left := fun h => hvC (h.symm ▸ Q.left_mem)
      have hright : C ≠ Q.right := fun h => hvC (h.symm ▸ Q.right_mem)
      simp [bodyVertexCredit,hvC,hleft,hright]

theorem sum_indicator_finset (S : Finset V) (c : ℝ) :
    (∑ v : V, if v ∈ S then c else 0) = (S.card : ℝ) * c := by
  rw [← Finset.sum_filter]
  have heq : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
  rw [heq]
  simp

theorem bodyBaseCredit_eq_sum_vertexCredit
    (M : MinimalCounterexample V) (C : Body M.graph) :
    bodyBaseCredit M C = ∑ v : V, bodyVertexCredit M C v := by
  by_cases hC : C.val.card = 5
  · have heq (v : V) : bodyVertexCredit M C v =
        (if v ∈ bodySoftVertices M C then (3 / 10 : ℝ) else 0) -
        (if v ∈ bodyTypeBVertices M C then (1 / 5 : ℝ) else 0) +
        (if v ∈ bodyOtherVertices M C then (1 / 20 : ℝ) else 0) := by
      by_cases hvC : v ∈ C.val
      · by_cases hs : IsSoftPointPin M.graph v
        · have hb : ¬ (∃ h, Nonempty (CorePort M C h v)) :=
            fun h => bodyTypeB_not_soft _ _ _ h hs
          simp [bodyVertexCredit,bodySoftVertices,bodyTypeBVertices,bodyOtherVertices,
            hvC,hC,hs,hb]
        · by_cases hb : ∃ h, Nonempty (CorePort M C h v)
          · simp [bodyVertexCredit,bodySoftVertices,bodyTypeBVertices,bodyOtherVertices,
              hvC,hC,hs,hb]
          · by_cases hh : IsHypervertex M.graph v <;>
              simp [bodyVertexCredit,bodySoftVertices,bodyTypeBVertices,bodyOtherVertices,
                hvC,hC,hs,hb,hh]
      · simp [bodyVertexCredit,bodySoftVertices,bodyTypeBVertices,bodyOtherVertices,hvC]
    simp only [heq,Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_indicator_finset]
    rw [bodyBaseCredit,if_pos hC]
    ring
  · by_cases hlarge : 6 ≤ C.val.card
    · have heq (v : V) : bodyVertexCredit M C v =
          if v ∈ bodySoftVertices M C then (1 / 2 : ℝ) else 0 := by
        by_cases hvC : v ∈ C.val <;> by_cases hs : IsSoftPointPin M.graph v <;>
          simp [bodyVertexCredit,bodySoftVertices,hC,hlarge,hvC,hs]
      simp only [heq,sum_indicator_finset]
      rw [bodyBaseCredit,if_neg hC,if_pos hlarge]
      ring
    · simp [bodyBaseCredit,bodyVertexCredit,hC,hlarge]

theorem bodyBaseCredit_le_sum_incidenceAllocation
    (M : MinimalCounterexample V) (C : Body M.graph) :
    bodyBaseCredit M C ≤ ∑ v : V, incidenceAllocation M C v := by
  rw [bodyBaseCredit_eq_sum_vertexCredit]
  exact Finset.sum_le_sum fun v _ => bodyVertexCredit_le_incidenceAllocation M C v

variable {M : MinimalCounterexample V} {p : Placement V 3}

def SoftScalarSystem.vertexExcess (L : SoftScalarSystem M p) (v : V) : ℝ :=
  (M.graph.degree v : ℝ) / 2 -
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v - 3

/-- Lemma 7.1 is used here as its proved exact identity, not as a
numerical input detached from the graph. -/
theorem SoftScalarSystem.two_body_excess_eq_allocations
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V)
    (hv : ¬ IsHypervertex M.graph v) :
    L.vertexExcess v = ∑ C : Body M.graph, incidenceAllocation M C v := by
  let Q := twoBodyPinAt M v hv
  rw [SoftScalarSystem.vertexExcess,L.two_body_contribution hgen hp v Q,
    sum_incidenceAllocation_at_twoBody M v hv]
  change (3 - 6 / (Q.left.val.card : ℝ)) + (3 - 6 / (Q.right.val.card : ℝ)) -
      (if Q.IsPoint then 0 else 1 / 2) - 3 =
    bodyOrderExcess Q.left.val.card + bodyOrderExcess Q.right.val.card -
      (if Q.IsPoint then 0 else 1 / 2)
  unfold bodyOrderExcess
  ring

/-- Summing the actual two-body vertices pays at least the sum of the
conservative body allocations. All negative core-port allocations are
retained on both sides of this inequality. -/
theorem SoftScalarSystem.two_body_total_excess_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (∑ C : Body M.graph, bodyBaseCredit M C) ≤
      ∑ v : V, if IsHypervertex M.graph v then 0 else L.vertexExcess v := by
  calc
    _ ≤ ∑ C : Body M.graph, ∑ v : V, incidenceAllocation M C v :=
      Finset.sum_le_sum fun C _ => bodyBaseCredit_le_sum_incidenceAllocation M C
    _ = ∑ v : V, ∑ C : Body M.graph, incidenceAllocation M C v := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : IsHypervertex M.graph v
      · simp only [if_pos hv,sum_incidenceAllocation_at_hypervertex M v hv]
      · rw [if_neg hv,← L.two_body_excess_eq_allocations hgen hp v hv]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0021

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0021/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0021.json"

section BundleSource0022
/- Source: Papers/RigidityExceptionalScalarModes.lean -/




@[expose] public section

/-!
# Actual exceptional scalar stress modes

For a component with sole observer h, the coefficient cut is a genuine
stress, retains exactly the component stars, and has rank one. Its
kernel consists precisely of stresses supported away from the whole
component. Thus the scalar mode is an actual direct summand, not merely
a coordinate in an abstract observer code.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Cutting all edges incident with S preserves every star at S. -/
theorem cut_starCoordinates_of_mem
    (G : SimpleGraph V) (S : Finset V) (a : Edge G → ℝ)
    (v : V) (hv : v ∈ S) (w : V) :
    starCoordinates G v (cutCoefficients G S a) w = starCoordinates G v a w := by
  by_cases hadj : G.Adj v w
  · rw [starCoordinates_of_adj _ _ _ _ hadj,
      starCoordinates_of_adj _ _ _ _ hadj,cutCoefficients_apply,
      if_pos ⟨v,hv,Sym2.mem_mk_left v w⟩]
  · rw [starCoordinates_of_not_adj _ _ _ _ hadj,
      starCoordinates_of_not_adj _ _ _ _ hadj]

theorem cut_eq_zero_of_stars_zero
    (G : SimpleGraph V) (S : Finset V) (a : Edge G → ℝ)
    (hstar : ∀ v ∈ S, ∀ w, starCoordinates G v a w = 0) :
    cutCoefficients G S a = 0 := by
  funext e
  by_cases ht : edgeTouches G S e
  · obtain ⟨v,hv,hve⟩ := ht
    obtain ⟨w,he⟩ := Sym2.mem_iff_exists.mp hve
    have hadj : G.Adj v w := by
      rw [← SimpleGraph.mem_edgeSet,← he]
      exact e.property
    have hz := hstar v hv w
    rw [starCoordinates_of_adj G v w a hadj] at hz
    rw [cutCoefficients_apply,if_pos ⟨v,hv,hve⟩]
    have he' : (⟨s(v,w),hadj⟩ : Edge G) = e := Subtype.ext he.symm
    simpa only [he',Pi.zero_apply] using hz
  · rw [cutCoefficients_apply,if_neg ht]
    rfl

/-- A star-coordinate description implies the literal endpoint support
condition used by the stress-cut equilibrium theorem. -/
theorem singleBoundary_of_stars
    (G : SimpleGraph V) (S : Finset V) (h : V) (a : Edge G → ℝ)
    (hstar : ∀ v ∈ S, ∀ w, starCoordinates G v a w ≠ 0 → w ∈ S ∨ w = h) :
    HasSingleBoundary G S h a := by
  rintro e ⟨v,hv,hve⟩ he z hze
  obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp hve
  have hadj : G.Adj v w := by
    rw [← SimpleGraph.mem_edgeSet,← hew]
    exact e.property
  have hcoord : starCoordinates G v a w ≠ 0 := by
    rw [starCoordinates_of_adj _ _ _ _ hadj]
    have he' : (⟨s(v,w),hadj⟩ : Edge G) = e := Subtype.ext hew.symm
    simpa only [he'] using he
  rw [hew,Sym2.mem_iff] at hze
  rcases hze with rfl | rfl
  · exact Or.inl hv
  · exact hstar v hv _ hcoord

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- Vanishing of one component coordinate makes every scalar in that
component vanish, while retaining all linear relations between components. -/
theorem SoftScalarSystem.scalar_zero_of_same_component
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (v w : SoftPointPin M.graph)
    (hvw : L.graph.connectedComponentMk v = L.graph.connectedComponentMk w)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hw : L.scalar w s = 0) :
    L.scalar v s = 0 := by
  have hline := ObserverCover.line_eq_of_reachable L.graph L.scalar
    (L.edge_identifies_scalars hp) (SimpleGraph.ConnectedComponent.exact hvw)
  have hm : L.scalar v ∈ ℝ ∙ L.scalar w := by
    change L.scalar v ∈ ObserverCover.line L.scalar w
    rw [← hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have he := LinearMap.congr_fun hc s
  simpa only [LinearMap.smul_apply,hw,smul_zero] using he.symm

/-- In a solely observed component, every actual stress star is killed
by the vanishing of the chosen component scalar. -/
theorem SoftScalarSystem.sole_component_stars_zero
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v₀ : SoftPointPin M.graph) (hv₀ : L.graph.connectedComponentMk v₀ = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : L.scalar v₀ s = 0) :
    ∀ v ∈ L.vertices c, ∀ w,
      starCoordinates (maskedGraph M.graph Finset.univ) v s.val w = 0 := by
  intro v hv w
  let sv : SoftPointPin M.graph := ⟨v,L.soft_of_mem_vertices c v hv⟩
  have hsv : L.graph.connectedComponentMk sv = c := L.mk_eq_of_mem_vertices c sv hv
  have hlam : L.scalar sv s = 0 :=
    L.scalar_zero_of_same_component hp sv v₀ (hsv.trans hv₀.symm) s hs
  have hF : sv.pin.pointForceOnWholePrefix sv.isPoint M.covered p s = 0 := by
    rw [L.force_eq,hlam,zero_smul]
  by_cases hadj : (maskedGraph M.graph Finset.univ).Adj v w
  · obtain ⟨C,hC,hvC,hwC⟩ := M.covered.edge_in_body hadj.1
    let B : Body M.graph := ⟨C,hC⟩
    have hfour : B.val.card = 4 := L.sole_observer_all_tetrahedra c h hc sv hsv B hvC
    exact sv.pin.pointForce_zero_incident_tetrahedron_star sv.isPoint M.covered
      B hvC hfour p hp s hF w hwC
  · exact starCoordinates_of_not_adj _ _ _ _ hadj

/-- Every nonzero boundary edge of a solely observed component ends at
its unique hypervertex observer. -/
theorem SoftScalarSystem.sole_component_boundary
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    HasSingleBoundary (maskedGraph M.graph Finset.univ) (L.vertices c) h.val s.val := by
  apply singleBoundary_of_stars
  intro v hv w hvw
  have hadj : (maskedGraph M.graph Finset.univ).Adj v w := by
    by_contra hn
    exact hvw (starCoordinates_of_not_adj _ _ _ _ hn)
  let sv : SoftPointPin M.graph := ⟨v,L.soft_of_mem_vertices c v hv⟩
  have hsv : L.graph.connectedComponentMk sv = c := L.mk_eq_of_mem_vertices c sv hv
  obtain ⟨C,hC,hvC,hwC⟩ := M.covered.edge_in_body hadj.1
  let B : Body M.graph := ⟨C,hC⟩
  have hfour : B.val.card = 4 := L.sole_observer_all_tetrahedra c h hc sv hsv B hvC
  obtain ⟨a,rfl⟩ := copiedToStress_surjective M.graph M.covered p Finset.univ s
  have hcopy : starCoordinates (cliqueOn (B.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ B a.val) w ≠ 0 := by
    rw [← sv.isPoint.copied_body_star a B hvC w hwC hadj.1.ne]
    exact hvw
  have he : stressEdgeFunctional M.graph p v w ≠ 0 := by
    intro hz
    exact hvw (LinearMap.congr_fun hz (copiedToStress M.graph p Finset.univ a))
  rcases tetrahedron_active_neighbor_soft_or_hyper M p hgen hp a sv B hfour hvC w hwC hcopy
      with hwsoft | hwhyper
  · let sw : SoftPointPin M.graph := ⟨w,hwsoft⟩
    have hedge : L.graph.Adj sv sw := ⟨B,hfour,hvC,hwC,he⟩
    have hsw : L.graph.connectedComponentMk sw = c :=
      (SimpleGraph.ConnectedComponent.sound hedge.reachable).symm.trans hsv
    exact Or.inl ((L.mem_vertices c w).mpr ⟨hwsoft,hsw⟩)
  · have hseen : Sum.inl (⟨w,hwhyper⟩ : Hypervertex M.graph) ∈ L.observers c :=
      (L.hyper_mem_observers c ⟨w,hwhyper⟩).mpr ⟨sv,hsv,B,hfour,hvC,hwC,he⟩
    rw [hc,Finset.mem_singleton] at hseen
    exact Or.inr (congrArg Subtype.val (Sum.inl.inj hseen))

/-- The actual rank-one stress projection attached to an exceptional
component: keep exactly the ordinary graph edges incident with it. -/
def SoftScalarSystem.exceptionalCut
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h}) :
    StressSpace (maskedGraph M.graph Finset.univ) p →ₗ[ℝ]
      StressSpace (maskedGraph M.graph Finset.univ) p :=
  ((cutCoefficients (maskedGraph M.graph Finset.univ) (L.vertices c)).comp
    (StressSpace (maskedGraph M.graph Finset.univ) p).subtype).codRestrict
    (StressSpace (maskedGraph M.graph Finset.univ) p) (fun s =>
      cut_mem_stress _ p (L.vertices c) h.val s.val s.property
        (L.sole_component_boundary hgen hp c h hc s))

@[simp] theorem SoftScalarSystem.exceptionalCut_val
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    (L.exceptionalCut hgen hp c h hc s).val =
      cutCoefficients (maskedGraph M.graph Finset.univ) (L.vertices c) s.val := rfl

/-- The cut preserves each actual point-force scalar on its component. -/
theorem SoftScalarSystem.exceptionalCut_scalar
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    L.scalar v (L.exceptionalCut hgen hp c h hc s) = L.scalar v s := by
  apply smul_left_injective ℝ (L.axis_ne_zero v)
  change L.scalar v (L.exceptionalCut hgen hp c h hc s) • L.axis v =
    L.scalar v s • L.axis v
  rw [← L.force_eq,← L.force_eq,
    v.pin.pointForceOnWholePrefix_eq_star_sum,
    v.pin.pointForceOnWholePrefix_eq_star_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [L.exceptionalCut_val,cut_starCoordinates_of_mem _ _ _ v.val
    ((L.mem_vertices c v.val).mpr ⟨v.property,hv⟩) w]

/-- Every exceptional cut is determined by one actual scalar. -/
theorem SoftScalarSystem.exceptionalCut_eq_scalar_smul
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (s₀ : StressSpace (maskedGraph M.graph Finset.univ) p) (hs₀ : L.scalar v s₀ = 1) :
    ∀ s, L.exceptionalCut hgen hp c h hc s =
      L.scalar v s • L.exceptionalCut hgen hp c h hc s₀ := by
  intro s
  have hlam : L.scalar v (s - L.scalar v s • s₀) = 0 := by
    rw [map_sub,map_smul,hs₀,smul_eq_mul,mul_one,sub_self]
  have hzero : L.exceptionalCut hgen hp c h hc (s - L.scalar v s • s₀) = 0 := by
    apply Subtype.ext
    exact cut_eq_zero_of_stars_zero _ _ _
      (L.sole_component_stars_zero hp c h hc v hv _ hlam)
  rw [map_sub,map_smul] at hzero
  exact sub_eq_zero.mp hzero

/-- The direct-summand form of Lemma 6.5. The displayed mode is a
nonzero actual stress supported on the component together with h;
subtracting its scalar multiple kills every component star. -/
theorem SoftScalarSystem.exists_exceptional_stress_mode
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c) :
    ∃ s₀ : StressSpace (maskedGraph M.graph Finset.univ) p,
      s₀ ≠ 0 ∧ L.scalar v s₀ = 1 ∧
      (∀ e, (¬ ∀ w, w ∈ e.val → w ∈ insert h.val (L.vertices c)) → s₀.val e = 0) ∧
      (∀ s, ∀ w ∈ L.vertices c, ∀ z,
        starCoordinates (maskedGraph M.graph Finset.univ) w
          (s - L.scalar v s • s₀).val z = 0) := by
  obtain ⟨s,hs⟩ := exists_normalized_linear_functional (L.scalar v) (L.scalar_ne_zero v)
  let s₀ := L.exceptionalCut hgen hp c h hc s
  have hnorm : L.scalar v s₀ = 1 := (L.exceptionalCut_scalar hgen hp c h hc v hv s).trans hs
  refine ⟨s₀,?_,hnorm,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at hnorm
    exact zero_ne_one hnorm
  · intro e he
    exact cut_supported _ (L.vertices c) h.val s.val
      (L.sole_component_boundary hgen hp c h hc s) e he
  · intro t w hw z
    exact L.sole_component_stars_zero hp c h hc v hv _ (by
      rw [map_sub,map_smul,hnorm,smul_eq_mul,mul_one,sub_self]) w hw z

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0022

section BundleSource0023
/- Source: Papers/RigidityFourBars.lean -/



@[expose] public section

/-!
# Four generic bars force rigidity of their old endpoints

This is the linear-algebraic part of the four-neighbor closure theorem
used in Lemma 3.7.  The old motion space is arbitrary.  If adding a new
point with four bars costs only three ranks on an open set of new-point
positions, every old motion preserves all six distances among the four
endpoints.  The proof propagates the affine rank bound and then puts the
new point at the midpoint of each pair of old endpoints.
-/

namespace Papers.Rigidity.FourBars

noncomputable section

open Matrix
open scoped Matrix

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  [FiniteDimensional ℝ M]

def AffinelyIndependent (q : Fin 4 → Vec3) : Prop :=
  LinearIndependent ℝ (fun i : Fin 3 => q i.succ - q 0)

/-- The three velocity coordinates of the newly inserted point. -/
def newPointOperator (q : Fin 4 → Vec3) (p : Vec3) : Vec3 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun i => dotProductBilin ℝ ℝ (q i - p)

@[simp] theorem newPointOperator_apply (q : Fin 4 → Vec3) (p w : Vec3) (i : Fin 4) :
    newPointOperator q p w i = (q i - p) ⬝ᵥ w := rfl

theorem newPointOperator_injective (q : Fin 4 → Vec3)
    (hq : AffinelyIndependent q) (p : Vec3) :
    Function.Injective (newPointOperator q p) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro w hw
    change w = 0
    have hz := LinearMap.mem_ker.mp hw
    let A : Matrix (Fin 3) (Fin 3) ℝ := fun i => q i.succ - q 0
    have hinj : Function.Injective A.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        (Matrix.linearIndependent_row_iff_isUnit.mp hq)
    apply hinj
    have hi (i : Fin 3) : (A *ᵥ w) i = 0 := by
      have h₀ := congrFun hz 0
      have hᵢ := congrFun hz i.succ
      change (q 0 - p) ⬝ᵥ w = 0 at h₀
      change (q i.succ - p) ⬝ᵥ w = 0 at hᵢ
      change (q i.succ - q 0) ⬝ᵥ w = 0
      simp only [dotProduct, Pi.sub_apply, Fin.sum_univ_three] at h₀ hᵢ ⊢
      linear_combination hᵢ - h₀
    rw [Matrix.mulVec_zero]
    exact funext hi
  · exact bot_le

theorem newPointOperator_rank (q : Fin 4 → Vec3)
    (hq : AffinelyIndependent q) (p : Vec3) :
    Module.finrank ℝ (newPointOperator q p).range = 3 := by
  rw [LinearMap.finrank_range_of_inj (newPointOperator_injective q hq p)]
  simp [Vec3]

/-- The four actual bar equations, restricted to the supplied old
motion space and the three new velocity coordinates. -/
def starOperator (q : Fin 4 → Vec3)
    (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3) :
    (M × Vec3) →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun i => (dotProductBilin ℝ ℝ (q i - p)).comp
    (((LinearMap.proj i).comp U).comp (LinearMap.fst ℝ M Vec3) -
      LinearMap.snd ℝ M Vec3)

@[simp] theorem starOperator_apply (q : Fin 4 → Vec3)
    (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3) (z : M × Vec3) (i : Fin 4) :
    starOperator q U p z i = (q i - p) ⬝ᵥ (U z.1 i - z.2) := rfl

def starLinearPart (U : M →ₗ[ℝ] (Fin 4 → Vec3)) :
    Vec3 →ₗ[ℝ] ((M × Vec3) →ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun p := LinearMap.pi fun i => (-(dotProductBilin ℝ ℝ p)).comp
    (((LinearMap.proj i).comp U).comp (LinearMap.fst ℝ M Vec3) -
      LinearMap.snd ℝ M Vec3)
  map_add' p q := by
    apply LinearMap.ext
    intro z
    funext i
    simp [add_dotProduct] <;> ring
  map_smul' c p := by
    apply LinearMap.ext
    intro z
    funext i
    simp <;> ring

theorem starOperator_eq_affineFamily (q : Fin 4 → Vec3)
    (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3) :
    starOperator q U p =
      AffineRank.family (starOperator q U 0) (starLinearPart U) p := by
  apply LinearMap.ext
  intro z
  funext i
  simp [AffineRank.family, starLinearPart, sub_dotProduct] <;> ring

theorem range_newPointOperator_le (q : Fin 4 → Vec3)
    (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3) :
    (newPointOperator q p).range ≤ (starOperator q U p).range := by
  rintro y ⟨w, rfl⟩
  refine ⟨(0, -w), ?_⟩
  ext i
  simp

/-- Rank three is exactly enough to extend every old motion through
the four bars.  Affine independence is used solely to ensure that the
new velocity coordinates themselves already contribute rank three. -/
theorem exists_extension_of_rank_le_three (q : Fin 4 → Vec3)
    (hq : AffinelyIndependent q) (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3)
    (hrank : Module.finrank ℝ (starOperator q U p).range ≤ 3) (u : M) :
    ∃ w : Vec3, ∀ i : Fin 4, (q i - p) ⬝ᵥ (U u i - w) = 0 := by
  have hranges : (newPointOperator q p).range = (starOperator q U p).range :=
    Submodule.eq_of_le_of_finrank_le (range_newPointOperator_le q U p)
      (by simpa [newPointOperator_rank q hq p] using hrank)
  have hy : starOperator q U p (u, 0) ∈ (newPointOperator q p).range := by
    rw [hranges]
    exact ⟨(u, 0), rfl⟩
  obtain ⟨w, hw⟩ := hy
  refine ⟨w, ?_⟩
  intro i
  have hi := congrFun hw i
  change (q i - p) ⬝ᵥ w = (q i - p) ⬝ᵥ (U u i - 0) at hi
  simp only [sub_zero] at hi
  rw [dotProduct_sub, ← hi, sub_self]

theorem rank_le_three_of_extensions (q : Fin 4 → Vec3)
    (U : M →ₗ[ℝ] (Fin 4 → Vec3)) (p : Vec3)
    (hext : ∀ u : M, ∃ w : Vec3, ∀ i : Fin 4,
      (q i - p) ⬝ᵥ (U u i - w) = 0) :
    Module.finrank ℝ (starOperator q U p).range ≤ 3 := by
  have hle : (starOperator q U p).range ≤ (newPointOperator q p).range := by
    rintro y ⟨⟨u, w⟩, rfl⟩
    obtain ⟨w₀, hw₀⟩ := hext u
    refine ⟨w₀ - w, ?_⟩
    ext i
    have hi := hw₀ i
    change (q i - p) ⬝ᵥ (w₀ - w) = (q i - p) ⬝ᵥ (U u i - w)
    rw [dotProduct_sub] at hi
    rw [dotProduct_sub, dotProduct_sub, sub_eq_zero.mp hi]
  exact (Submodule.finrank_mono hle).trans
    (by simpa [Vec3] using LinearMap.finrank_range_le (newPointOperator q p))

/-- The four-endpoint closure conclusion follows from a genuine open
rank condition.  At a midpoint, the two corresponding bar equations
immediately imply the old bar equation between those endpoints. -/
theorem preserves_all_bars_of_rank_le_three_on_open (q : Fin 4 → Vec3)
    (hq : AffinelyIndependent q) (U : M →ₗ[ℝ] (Fin 4 → Vec3))
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hrank : ∀ p ∈ O, Module.finrank ℝ (starOperator q U p).range ≤ 3) :
    ∀ u : M, ∀ i j : Fin 4, (q i - q j) ⬝ᵥ (U u i - U u j) = 0 := by
  have hall := AffineRank.rankAt_le_of_on_open
    (starOperator q U 0) (starLinearPart U) O hO hne 3
    (by
      intro p hp
      unfold AffineRank.rankAt
      rw [← starOperator_eq_affineFamily q U p]
      exact hrank p hp)
  intro u i j
  let p : Vec3 := (1 / 2 : ℝ) • (q i + q j)
  have hp : Module.finrank ℝ (starOperator q U p).range ≤ 3 := by
    have hh := hall p
    unfold AffineRank.rankAt at hh
    rwa [← starOperator_eq_affineFamily q U p] at hh
  obtain ⟨w, hw⟩ := exists_extension_of_rank_le_three q hq U p hp u
  have hi := hw i
  have hj := hw j
  simp only [p, dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, Fin.sum_univ_three] at hi hj ⊢
  linear_combination 2 * hi + 2 * hj

theorem preserves_all_bars_of_extensions_on_open (q : Fin 4 → Vec3)
    (hq : AffinelyIndependent q) (U : M →ₗ[ℝ] (Fin 4 → Vec3))
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty)
    (hext : ∀ p ∈ O, ∀ u : M, ∃ w : Vec3, ∀ i : Fin 4,
      (q i - p) ⬝ᵥ (U u i - w) = 0) :
    ∀ u : M, ∀ i j : Fin 4, (q i - q j) ⬝ᵥ (U u i - U u j) = 0 :=
  preserves_all_bars_of_rank_le_three_on_open q hq U O hO hne
    (fun p hp => rank_le_three_of_extensions q U p (hext p hp))

end

end Papers.Rigidity.FourBars

end
end BundleSource0023

section BundleSource0024
/- Source: Papers/RigidityFourBarExtension.lean -/





@[expose] public section

/-!
# A vertex with four bars and rank increment three

The graph has its literal old edges and exactly four new incident edges.
An explicit kernel isomorphism proves the elimination identity for its
rank.  The four-bar lemma then proves that the four old neighbors belong
to one ambient rigid cluster whenever the generic rank increment is at
most three.  This supplies the content of the external four-neighbor
closure result used by the paper, without assuming that result.
-/

namespace Papers.Rigidity.FourBars

noncomputable section

open BarJoint Matrix
open scoped Classical Matrix

variable {V : Type} [Fintype V]

def extensionGraph (H : SimpleGraph V) (f : Fin 4 ↪ V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some v, some w => H.Adj v w
    | none, some w => w ∈ Set.range f
    | some v, none => v ∈ Set.range f
    | none, none => False
  symm := by
    constructor
    intro a b
    cases a <;> cases b <;> simp only
    · exact id
    · exact id
    · exact id
    · exact H.adj_symm
  loopless := by
    constructor
    intro a
    cases a <;> simp

def extensionPlacement (q : Placement V 3) (p : Vec3) : Placement (Option V) 3 :=
  fun v => Option.elim v p q

@[simp] theorem extensionPlacement_none (q : Placement V 3) (p : Vec3) :
    extensionPlacement q p none = p := rfl

@[simp] theorem extensionPlacement_some (q : Placement V 3) (p : Vec3) (v : V) :
    extensionPlacement q p (some v) = q v := rfl

def oldMotionAtNeighbors (H : SimpleGraph V) (q : Placement V 3) (f : Fin 4 ↪ V) :
    (rigidityOperator H q).ker →ₗ[ℝ] (Fin 4 → Vec3) where
  toFun u i := u.val (f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting a full motion and remembering the new velocity is an
isomorphism onto the kernel of the four actual restricted bar rows. -/
def extensionMotionEquiv (H : SimpleGraph V) (q : Placement V 3)
    (f : Fin 4 ↪ V) (p : Vec3) :
    (rigidityOperator (extensionGraph H f) (extensionPlacement q p)).ker ≃ₗ[ℝ]
      (starOperator (q ∘ f) (oldMotionAtNeighbors H q f) p).ker where
  toFun u := by
    let uold : Velocity V 3 := fun v => u.val (some v)
    have hold : IsInfinitesimalMotion H q uold := by
      rw [isInfinitesimalMotion_iff]
      intro v w hvw
      exact (isInfinitesimalMotion_iff _ _ u.val).mp u.property (some v) (some w) hvw
    refine ⟨(⟨uold, hold⟩, u.val none), ?_⟩
    rw [LinearMap.mem_ker]
    ext i
    have h := (isInfinitesimalMotion_iff _ _ u.val).mp u.property
      (some (f i)) none ⟨i, rfl⟩
    simpa only [starOperator_apply, oldMotionAtNeighbors, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, uold, edgeConstraint,
      extensionPlacement_some, extensionPlacement_none, dotProduct,
      Pi.sub_apply,Pi.zero_apply] using h
  invFun z := by
    let u : Velocity (Option V) 3 := fun v => Option.elim v z.val.2 z.val.1.val
    refine ⟨u, ?_⟩
    change IsInfinitesimalMotion (extensionGraph H f) (extensionPlacement q p) u
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    have hstar := LinearMap.mem_ker.mp z.property
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hab
      | some w =>
        obtain ⟨i, rfl⟩ := hab
        rw [edgeConstraint_comm]
        have hi := congrFun hstar i
        simpa only [starOperator_apply, oldMotionAtNeighbors, LinearMap.coe_mk,
          AddHom.coe_mk, Function.comp_apply, Pi.zero_apply, edgeConstraint,
          extensionPlacement_some, extensionPlacement_none, u, Option.elim,
          dotProduct,Pi.sub_apply] using hi
    | some v =>
      cases b with
      | none =>
        obtain ⟨i, rfl⟩ := hab
        have hi := congrFun hstar i
        simpa only [starOperator_apply, oldMotionAtNeighbors, LinearMap.coe_mk,
          AddHom.coe_mk, Function.comp_apply, Pi.zero_apply, edgeConstraint,
          extensionPlacement_some, extensionPlacement_none, u, Option.elim,
          dotProduct,Pi.sub_apply] using hi
      | some w =>
        exact (isInfinitesimalMotion_iff H q z.val.1.val).mp z.val.1.property v w hab
  left_inv u := by
    apply Subtype.ext
    funext v
    cases v <;> rfl
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  map_add' u w := rfl
  map_smul' c u := rfl

/-- The restricted four-row rank is exactly the rank gained by adding
the new vertex.  No genericity or general-position hypothesis is needed. -/
theorem extension_rank_identity (H : SimpleGraph V) (q : Placement V 3)
    (f : Fin 4 ↪ V) (p : Vec3) :
    rigidityRank (extensionGraph H f) (extensionPlacement q p) =
      rigidityRank H q +
        Module.finrank ℝ (starOperator (q ∘ f) (oldMotionAtNeighbors H q f) p).range := by
  have hker := (extensionMotionEquiv H q f p).finrank_eq
  have hfull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity (Option V) 3) (V₂ := Option V × Option V → ℝ)
    (rigidityOperator (extensionGraph H f) (extensionPlacement q p))
  have hold := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity V 3) (V₂ := V × V → ℝ) (rigidityOperator H q)
  have hstar := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := (rigidityOperator H q).ker × Vec3) (V₂ := Fin 4 → ℝ)
    (starOperator (q ∘ f) (oldMotionAtNeighbors H q f) p)
  have hdold : Module.finrank ℝ (Velocity V 3) = 3 * Fintype.card V := by
    simp [Velocity, Module.finrank_pi_fintype, Nat.mul_comm]
  have hdfull : Module.finrank ℝ (Velocity (Option V) 3) =
      3 * Fintype.card V + 3 := by
    simp [Velocity, Module.finrank_pi_fintype, Nat.mul_add, Nat.add_mul, Nat.mul_comm]
  have hdstar : Module.finrank ℝ ((rigidityOperator H q).ker × Vec3) =
      Module.finrank ℝ (rigidityOperator H q).ker + 3 := by
    simp [Vec3, Module.finrank_prod]
  rw [hdfull] at hfull
  rw [hdold] at hold
  rw [hdstar] at hstar
  unfold rigidityRank
  omega

/-- The four-neighbor closure theorem, for arbitrary finite old graphs.
Its conclusion is the ambient rigidity closure, so the neighbors need
not already induce a rigid subgraph. -/
theorem rigidCluster_of_generic_rank_increment_le_three
    (H : SimpleGraph V) (f : Fin 4 ↪ V)
    (hrank : genericRigidityRank (extensionGraph H f) 3 ≤ genericRigidityRank H 3 + 3) :
    RigidCluster H (Finset.univ.image f) := by
  obtain ⟨q, hqGeneric, hqGeom⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  have hq : AffinelyIndependent (q ∘ f) := hqGeom (3 : Fin 4) f
  have hstar (p : Vec3) :
      Module.finrank ℝ (starOperator (q ∘ f) (oldMotionAtNeighbors H q f) p).range ≤ 3 := by
    have hactual := rigidityRank_le_genericRigidityRank
      (extensionGraph H f) 3 (extensionPlacement q p)
    rw [extension_rank_identity, hqGeneric H] at hactual
    omega
  have hbars := preserves_all_bars_of_rank_le_three_on_open (q ∘ f) hq
    (oldMotionAtNeighbors H q f) Set.univ isOpen_univ Set.univ_nonempty
    (fun p _ => hstar p)
  let S := Finset.univ.image f
  let C := clusterCompletion (fun _ : Unit => S)
  have hker : (rigidityOperator H q).ker ≤ (rigidityOperator (H ⊔ C) q).ker := by
    intro u hu
    change IsInfinitesimalMotion (H ⊔ C) q u
    rw [isInfinitesimalMotion_iff]
    intro v w hvw
    rcases hvw with hold | ⟨_, _, hv, hw⟩
    · exact (isInfinitesimalMotion_iff H q u).mp hu v w hold
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact hbars ⟨u, hu⟩ i j
  have hr := rigidityRank_le_of_ker_le (H ⊔ C) H q hker
  change genericRigidityRank (H ⊔ C) 3 = genericRigidityRank H 3
  exact le_antisymm
    ((hqGeneric (H ⊔ C)).symm.le.trans (hr.trans (hqGeneric H).le))
    (genericRigidityRank_mono le_sup_left)

end

end Papers.Rigidity.FourBars

end
end BundleSource0024

section BundleSource0025
/- Source: Papers/RigidityFourStarClosure.lean -/






@[expose] public section

/-!
# Four supported stress-star edges force a five-vertex rigid cluster

The four-bar closure theorem is applied to the actual subgraph obtained
by keeping all old edges and only the four displayed star edges. A
nonzero stress on this star lowers the generic insertion rank to three.
The conclusion is an ambient rigid cluster, including the central
vertex, so it applies to a stress whose other support is arbitrary.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint

open BodyLoads VertexPin FourBars SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Retain all old edges and only the indicated neighbors of v. -/
def trimStar (G : SimpleGraph V) (v : V) (N : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ (a = v → b ∈ N) ∧ (b = v → a ∈ N)
  symm := by
    constructor
    rintro a b ⟨hab,ha,hb⟩
    exact ⟨hab.symm,hb,ha⟩
  loopless := by
    constructor
    intro a h
    exact G.loopless.irrefl a h.1

theorem trimStar_le (G : SimpleGraph V) (v : V) (N : Finset V) :
    trimStar G v N ≤ G := fun _ _ h => h.1

theorem deleted_trimStar (G : SimpleGraph V) (v : V) (N : Finset V) :
    deletedGraph (trimStar G v N) v = deletedGraph G v := by
  ext a b
  change (G.Adj a.val b.val ∧ (a.val = v → b.val ∈ N) ∧
    (b.val = v → a.val ∈ N)) ↔ G.Adj a.val b.val
  simp only [a.property,b.property,false_implies,and_true]

theorem neighborFinset_trimStar (G : SimpleGraph V) (v : V) (N : Finset V)
    (hN : ∀ w ∈ N, G.Adj v w) : (trimStar G v N).neighborFinset v = N := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · exact fun h => h.2.1 rfl
  · intro hw
    exact ⟨hN w hw,fun _ => hw,fun h => False.elim ((hN w hw).ne h.symm)⟩

theorem restrict_stress_to_trimStar
    (G : SimpleGraph V) (v : V) (N : Finset V) (p : Placement V 3)
    (s : StressSpace G p)
    (hout : ∀ w, w ∉ N → starCoordinates G v s.val w = 0) :
    s.val ∈ supportedOn (StressSpace G p) (subgraphEdgeSet G (trimStar G v N)) := by
  refine ⟨s.property,?_⟩
  intro e he
  by_contra hse
  apply he
  obtain ⟨a,b,heab⟩ : ∃ a b, e.val = s(a,b) :=
    ⟨e.val.out.1,e.val.out.2,e.val.out_eq.symm⟩
  have hab : G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet,← heab]
    exact e.property
  change e.val ∈ (trimStar G v N).edgeSet
  rw [heab,SimpleGraph.mem_edgeSet]
  refine ⟨hab,?_,?_⟩
  · intro hav
    subst a
    by_contra hb
    have hz := hout b hb
    rw [starCoordinates_of_adj _ _ _ _ hab] at hz
    exact hse ((congrArg s.val (Subtype.ext heab)).trans hz)
  · intro hbv
    subst b
    by_contra ha
    have hz := hout a ha
    rw [starCoordinates_of_adj _ _ _ _ hab.symm] at hz
    have heva : e.val = s(v,a) := heab.trans Sym2.eq_swap
    exact hse ((congrArg s.val (Subtype.ext heva)).trans hz)

/-- A nonzero stress on four star edges gives insertion rank at most
three in the literal trimmed subgraph. -/
theorem trimStar_generic_rank_le
    (G : SimpleGraph V) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (v : V) (N : Finset V) (hNcard : N.card = 4)
    (hN : ∀ w ∈ N, G.Adj v w) (s : StressSpace G p)
    (hout : ∀ w, w ∉ N → starCoordinates G v s.val w = 0)
    (hnonzero : ∃ w ∈ N, starCoordinates G v s.val w ≠ 0) :
    genericRigidityRank (trimStar G v N) 3 ≤
      genericRigidityRank (deletedGraph G v) 3 + 3 := by
  let A := trimStar G v N
  let hs := restrict_stress_to_trimStar G v N p s hout
  let t : StressSpace A p := (subgraphStressEquiv (trimStar_le G v N) p).symm ⟨s.val,hs⟩
  have htstar : starRestriction A v t.val ≠ 0 := by
    obtain ⟨w,hw,hws⟩ := hnonzero
    have hadj : A.Adj v w :=
      ⟨hN w hw,fun _ => hw,fun heq => False.elim ((hN w hw).ne heq.symm)⟩
    let e : IncidentEdge A v := ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w⟩
    intro hz
    have hze := congrFun hz e
    change s.val (⟨s(v,w),hN w hw⟩ : Edge G) = 0 at hze
    exact hws ((starCoordinates_of_adj G v w s.val (hN w hw)).trans hze)
  have hpos : 0 < Module.finrank ℝ (stressStarCode A v (StressSpace A p)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨starRestriction A v t.val,⟨t.val,t.property,rfl⟩⟩,?_⟩
    intro hz
    exact htstar (congrArg Subtype.val hz)
  have hdim := stressStar_finrank_add_rank A p v
  have hdegree : A.degree v = 4 := by
    rw [← A.card_neighborFinset_eq_degree,neighborFinset_trimStar G v N hN,hNcard]
  rw [hdegree,hgen A,deleted_trimStar G v N,
    generic_deletedPlacement p hgen v (deletedGraph G v)] at hdim
  change genericRigidityRank A 3 ≤ genericRigidityRank (deletedGraph G v) 3 + 3
  omega

/-- Four nonzero star coefficients in a generic stress force the four
neighbors, together with the central vertex, into one ambient rigid
cluster. This is the exact external four-neighbor result used in 6.5. -/
theorem rigidCluster_of_stress_star_four
    (G : SimpleGraph V) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (N : Finset V) (hNcard : N.card = 4)
    (hN : ∀ w ∈ N, G.Adj v w) (s : StressSpace G p)
    (hout : ∀ w, w ∉ N → starCoordinates G v s.val w = 0)
    (hnonzero : ∃ w ∈ N, starCoordinates G v s.val w ≠ 0) :
    RigidCluster G (insert v N) := by
  have hvN : v ∉ N := fun hv => G.loopless.irrefl v (hN v hv)
  let f₀ : Fin 4 ≃ N := (Finset.equivFinOfCardEq hNcard).symm
  let f : Fin 4 ↪ DeletedVertex v :=
    ⟨fun i => ⟨(f₀ i).val,fun h => hvN (h ▸ (f₀ i).property)⟩,
      fun i j h => f₀.injective (Subtype.ext (congrArg (fun x : {w : V // w ≠ v} => x.val) h))⟩
  have hf (w : DeletedVertex v) : w ∈ Set.range f ↔ w.val ∈ N := by
    constructor
    · rintro ⟨i,rfl⟩
      exact (f₀ i).property
    · intro hw
      refine ⟨f₀.symm ⟨w.val,hw⟩,?_⟩
      apply Subtype.ext
      exact congrArg (fun z : N => z.val) (f₀.apply_symm_apply ⟨w.val,hw⟩)
  let e : Option (DeletedVertex v) ≃ V := Equiv.optionSubtypeNe v
  have hegraph :
      (trimStar G v N).comap e = extensionGraph (deletedGraph G v) f := by
    ext a b
    cases a with
    | none =>
        cases b with
        | none => simp [e,trimStar,extensionGraph]
        | some b =>
            change (G.Adj v b.val ∧ (v = v → b.val ∈ N) ∧ (b.val = v → v ∈ N)) ↔
              b ∈ Set.range f
            rw [hf]
            constructor
            · exact fun h => h.2.1 rfl
            · exact fun h => ⟨hN _ h,fun _ => h,fun heq => False.elim (b.property heq)⟩
    | some a =>
        cases b with
        | none =>
            change (G.Adj a.val v ∧ (a.val = v → v ∈ N) ∧ (v = v → a.val ∈ N)) ↔
              a ∈ Set.range f
            rw [hf]
            constructor
            · exact fun h => h.2.2 rfl
            · exact fun h => ⟨(hN _ h).symm,fun heq => False.elim (a.property heq),fun _ => h⟩
        | some b =>
            change (G.Adj a.val b.val ∧ (a.val = v → b.val ∈ N) ∧
              (b.val = v → a.val ∈ N)) ↔ G.Adj a.val b.val
            simp only [a.property,b.property,false_implies,and_true]
  have hrank : genericRigidityRank (extensionGraph (deletedGraph G v) f) 3 ≤
      genericRigidityRank (deletedGraph G v) 3 + 3 := by
    rw [← hegraph]
    have hrel := genericRigidityRank_relabel e.symm (trimStar G v N) 3
    rw [Equiv.symm_symm] at hrel
    rw [hrel]
    exact trimStar_generic_rank_le G p hgen v N hNcard hN s hout hnonzero
  let q := deletedPlacement p v
  have hqgen : IsGenericPlacement q := generic_deletedPlacement p hgen v
  have hqgeom : GeneralPosition.InGeneralPosition q :=
    GeneralPosition.InGeneralPosition.comp_embedding p hp (Function.Embedding.subtype _)
  have hstar (x : Vec3) :
      Module.finrank ℝ (starOperator (q ∘ f)
        (oldMotionAtNeighbors (deletedGraph G v) q f) x).range ≤ 3 := by
    have hactual := rigidityRank_le_genericRigidityRank
      (extensionGraph (deletedGraph G v) f) 3 (extensionPlacement q x)
    rw [extension_rank_identity,hqgen] at hactual
    omega
  have hbars := preserves_all_bars_of_rank_le_three_on_open (q ∘ f)
    (hqgeom (3 : Fin 4) f) (oldMotionAtNeighbors (deletedGraph G v) q f)
    Set.univ isOpen_univ Set.univ_nonempty (fun x _ => hstar x)
  apply rigidCluster_of_motionRepresentation G (insert v N) p hgen
  intro u
  let uold : (rigidityOperator (deletedGraph G v) q).ker :=
    ⟨fun w => u.val w.val,by
      rw [← IsInfinitesimalMotion,isInfinitesimalMotion_iff]
      intro a b hab
      exact (isInfinitesimalMotion_iff G p u.val).mp u.property a.val b.val hab⟩
  have hpreserve (a b : V) (ha : a ∈ insert v N) (hb : b ∈ insert v N) (hab : a ≠ b) :
      edgeConstraint p u.val a b = 0 := by
    by_cases hav : a = v
    · subst a
      have hbN : b ∈ N := (Finset.mem_insert.mp hb).resolve_left hab.symm
      exact (isInfinitesimalMotion_iff G p u.val).mp u.property v b (hN b hbN)
    by_cases hbv : b = v
    · subst b
      have haN : a ∈ N := (Finset.mem_insert.mp ha).resolve_left hav
      exact (isInfinitesimalMotion_iff G p u.val).mp u.property a v (hN a haN).symm
    have haN : a ∈ N := (Finset.mem_insert.mp ha).resolve_left hav
    have hbN : b ∈ N := (Finset.mem_insert.mp hb).resolve_left hbv
    obtain ⟨i,hi⟩ := (hf ⟨a,hav⟩).mpr haN
    obtain ⟨j,hj⟩ := (hf ⟨b,hbv⟩).mpr hbN
    have h := hbars uold i j
    simpa only [oldMotionAtNeighbors,LinearMap.coe_mk,AddHom.coe_mk,
      Function.comp_apply,hi,hj,q,deletedPlacement,uold,edgeConstraint,dotProduct,
      Pi.sub_apply] using h
  let S := insert v N
  let emb : S ↪ V := Function.Embedding.subtype _
  have hcomplete : IsInfinitesimalMotion (SimpleGraph.completeGraph S)
      (p ∘ emb) (u.val ∘ emb) := by
    rw [isInfinitesimalMotion_iff]
    intro a b hab
    exact hpreserve a.val b.val a.property b.property
      (fun h => hab (Subtype.ext h))
  obtain ⟨X,hX⟩ := exists_twist_of_completeMotion_all (p ∘ emb) (u.val ∘ emb)
    (GeneralPosition.InGeneralPosition.comp_embedding p hp emb) hcomplete
  exact ⟨X,fun w hw => hX ⟨w,hw⟩⟩

end Papers.Rigidity.BarJoint

end
end
end BundleSource0025

section BundleSource0026
/- Source: Papers/RigidityExceptionalStarSupport.lean -/




@[expose] public section

/-!
# Exceptional modes have at least five actual hypervertex star edges

A sole observer really detects a nonzero coefficient of the normalized
mode. Four supported edges would put their neighbors and the observer
in a five-vertex rigid cluster, contradicting the tetrahedral body type
of every component pin. All supports below are ordinary edge supports.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.hypervertex_not_mem_vertices
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (h : Hypervertex M.graph) : h.val ∉ L.vertices c := by
  intro hh
  let v : SoftPointPin M.graph := ⟨h.val,L.soft_of_mem_vertices c h.val hh⟩
  exact v.not_hypervertex h.property

/-- The hypervertex observer detects a nonzero actual star coefficient
whenever the component scalar is nonzero. -/
theorem SoftScalarSystem.sole_observer_star_ne_zero
    (L : SoftScalarSystem M p) (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v₀ : SoftPointPin M.graph) (hv₀ : L.graph.connectedComponentMk v₀ = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : L.scalar v₀ s ≠ 0) :
    starCoordinates (maskedGraph M.graph Finset.univ) h.val s.val ≠ 0 := by
  have hh : Sum.inl h ∈ L.observers c := by rw [hc]; simp
  obtain ⟨v,hv,C,hC,hvC,hhC,he⟩ := (L.hyper_mem_observers c h).mp hh
  have hlam : L.scalar v s ≠ 0 := by
    intro hz
    exact hs (L.scalar_zero_of_same_component hp v₀ v (hv₀.trans hv.symm) s hz)
  have hline := span_eq_of_nonzero_functional_kernel
    (L.scalar v) (stressEdgeFunctional M.graph p v.val h.val)
    (L.scalar_ne_zero v) he
    (L.scalar_kernel_le_edge_kernel hp v C hC hvC h.val hhC)
  have hm : L.scalar v ∈ ℝ ∙ stressEdgeFunctional M.graph p v.val h.val := by
    rw [← hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hm
  intro hstar
  have hezero : stressEdgeFunctional M.graph p v.val h.val s = 0 := by
    change starCoordinates (maskedGraph M.graph Finset.univ) v.val s.val h.val = 0
    rw [starCoordinates_symm]
    exact congrFun hstar v.val
  apply hlam
  have hz := LinearMap.congr_fun ht s
  simpa only [LinearMap.smul_apply,hezero,smul_zero] using hz.symm

/-- Every nonzero h-star edge of the cut joins h to a component pin. -/
theorem SoftScalarSystem.exceptionalCut_neighbor_mem
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (w : V)
    (hw : starCoordinates (maskedGraph M.graph Finset.univ) h.val
      (L.exceptionalCut hgen hp c h hc s).val w ≠ 0) : w ∈ L.vertices c := by
  by_contra hwS
  have hadj : (maskedGraph M.graph Finset.univ).Adj h.val w := by
    by_contra hn
    exact hw (starCoordinates_of_not_adj _ _ _ _ hn)
  let e : Edge (maskedGraph M.graph Finset.univ) := ⟨s(h.val,w),hadj⟩
  have hnot : ¬ edgeTouches (maskedGraph M.graph Finset.univ) (L.vertices c) e := by
    rintro ⟨z,hz,hze⟩
    rcases Sym2.mem_iff.mp hze with rfl | rfl
    · exact L.hypervertex_not_mem_vertices c h hz
    · exact hwS hz
  rw [starCoordinates_of_adj _ _ _ _ hadj,L.exceptionalCut_val,
    cutCoefficients_apply,if_neg hnot] at hw
  exact hw rfl

/-- The final star-support assertion in Lemma 6.5, at full generality
for every exceptional component of the actual minimal counterexample. -/
theorem SoftScalarSystem.exceptionalCut_star_support_ge_five
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : L.scalar v s ≠ 0) :
    5 ≤ (support (starCoordinates (maskedGraph M.graph Finset.univ) h.val
      (L.exceptionalCut hgen hp c h hc s).val)).card := by
  let t := L.exceptionalCut hgen hp c h hc s
  let N := support (starCoordinates (maskedGraph M.graph Finset.univ) h.val t.val)
  have hscalar : L.scalar v t ≠ 0 := by
    rw [L.exceptionalCut_scalar hgen hp c h hc v hv s]
    exact hs
  have hstar := L.sole_observer_star_ne_zero hp c h hc v hv t hscalar
  have hfour : 4 ≤ N.card := balanced_star_support_four p hp h.val _
    (starCoordinates_self _ _ _)
    (stress_starCoordinates_balance _ p t.val t.property h.val) hstar
  change 5 ≤ N.card
  by_contra hsmall
  have hNcard : N.card = 4 := by omega
  have hNadj (w : V) (hw : w ∈ N) : (maskedGraph M.graph Finset.univ).Adj h.val w := by
    have hn : starCoordinates (maskedGraph M.graph Finset.univ) h.val t.val w ≠ 0 :=
      (mem_support _ w).mp hw
    by_contra hadj
    exact hn (starCoordinates_of_not_adj _ _ _ _ hadj)
  have hNmem (w : V) (hw : w ∈ N) : w ∈ L.vertices c :=
    L.exceptionalCut_neighbor_mem hgen hp c h hc s w ((mem_support _ w).mp hw)
  have hout (w : V) (hw : w ∉ N) :
      starCoordinates (maskedGraph M.graph Finset.univ) h.val t.val w = 0 := by
    simpa only [N,mem_support,not_not] using hw
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
  have hcluster := rigidCluster_of_stress_star_four
    (maskedGraph M.graph Finset.univ) p hgen hp h.val N hNcard hNadj t hout
      ⟨w,hw,(mem_support _ w).mp hw⟩
  have hGraph : maskedGraph M.graph Finset.univ = M.graph := by
    ext a b
    simp [maskedGraph]
  rw [hGraph] at hcluster
  have hhN : h.val ∉ N := by
    intro hh
    exact (hNadj h.val hh).ne rfl
  have hsize : (insert h.val N).card = 5 := by
    rw [Finset.card_insert_of_notMem hhN,hNcard]
  have hclique := M.rigidCluster_isClique (insert h.val N) (by omega) hcluster
  obtain ⟨B,hSB,hB⟩ := exists_body_containing M.graph (insert h.val N) (by omega) hclique
  have hBfive : 5 ≤ B.card := by
    simpa only [hsize] using Finset.card_le_card hSB
  let sw : SoftPointPin M.graph := ⟨w,L.soft_of_mem_vertices c w (hNmem w hw)⟩
  have hsw : L.graph.connectedComponentMk sw = c :=
    L.mk_eq_of_mem_vertices c sw (hNmem w hw)
  have hBfour : B.card = 4 := L.sole_observer_all_tetrahedra c h hc sw hsw ⟨B,hB⟩
    (hSB (Finset.mem_insert_of_mem hw))
  omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0026

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0026/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0026.json"

section BundleSource0027
/- Source: Papers/RigidityExceptionalPrefix.lean -/



@[expose] public section

/-!
# Exact prefix support and independence of exceptional modes

The support of a nonzero exceptional cut is exactly its scalar
component together with its sole hypervertex observer. Every omitted
vertex therefore kills its scalar on that prefix. Cuts from different
components have zero stars at one another's pins, which gives actual
biorthogonal stress modes and proves their independence.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The actual vertices incident with a nonzero ordinary coefficient. -/
def coefficientVertexSupport (G : SimpleGraph V) (a : Edge G → ℝ) : Finset V :=
  Finset.univ.filter fun v => ∃ e : Edge G, v ∈ e.val ∧ a e ≠ 0

@[simp] theorem mem_coefficientVertexSupport
    (G : SimpleGraph V) (a : Edge G → ℝ) (v : V) :
    v ∈ coefficientVertexSupport G a ↔ ∃ e : Edge G, v ∈ e.val ∧ a e ≠ 0 := by
  simp only [coefficientVertexSupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem star_ne_zero_iff_mem_vertexSupport
    (G : SimpleGraph V) (a : Edge G → ℝ) (v : V) :
    starCoordinates G v a ≠ 0 ↔ v ∈ coefficientVertexSupport G a := by
  constructor
  · intro hstar
    obtain ⟨w,hw⟩ : ∃ w, starCoordinates G v a w ≠ 0 := by
      by_contra h
      push_neg at h
      exact hstar (funext h)
    have hadj : G.Adj v w := by
      by_contra h
      exact hw (starCoordinates_of_not_adj _ _ _ _ h)
    refine (mem_coefficientVertexSupport G a v).mpr
      ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w,?_⟩
    simpa only [starCoordinates_of_adj G v w a hadj] using hw
  · intro hv
    obtain ⟨e,hve,he⟩ := (mem_coefficientVertexSupport G a v).mp hv
    obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp hve
    have hadj : G.Adj v w := by
      rw [← SimpleGraph.mem_edgeSet,← hew]
      exact e.property
    intro hzero
    have hzw := congrFun hzero w
    rw [starCoordinates_of_adj _ _ _ _ hadj] at hzw
    have heq : (⟨s(v,w),hadj⟩ : Edge G) = e := Subtype.ext hew.symm
    exact he (by simpa only [heq,Pi.zero_apply] using hzw)

/-- Ordinary induced-vertex support, expressed on actual coefficients. -/
def CoefficientsSupportedOn (G : SimpleGraph V) (T : Finset V) (a : Edge G → ℝ) : Prop :=
  ∀ e, a e ≠ 0 → ∀ v, v ∈ e.val → v ∈ T

theorem coefficientsSupportedOn_iff_vertexSupport_subset
    (G : SimpleGraph V) (T : Finset V) (a : Edge G → ℝ) :
    CoefficientsSupportedOn G T a ↔ coefficientVertexSupport G a ⊆ T := by
  constructor
  · intro h v hv
    obtain ⟨e,hve,he⟩ := (mem_coefficientVertexSupport G a v).mp hv
    exact h e he v hve
  · intro h e he v hve
    exact h ((mem_coefficientVertexSupport G a v).mpr ⟨e,hve,he⟩)

theorem cut_preserves_vertex_support
    (G : SimpleGraph V) (S T : Finset V) (a : Edge G → ℝ)
    (ha : CoefficientsSupportedOn G T a) :
    CoefficientsSupportedOn G T (cutCoefficients G S a) := by
  intro e he v hve
  by_cases ht : edgeTouches G S e
  · rw [cutCoefficients_apply,if_pos ht] at he
    exact ha e he v hve
  · exact False.elim (he (if_neg ht))

variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.scalar_zero_of_star_zero
    (L : SoftScalarSystem M p) (v : SoftPointPin M.graph)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : starCoordinates (maskedGraph M.graph Finset.univ) v.val s.val = 0) :
    L.scalar v s = 0 := by
  apply smul_left_injective ℝ (L.axis_ne_zero v)
  change L.scalar v s • L.axis v = (0 : ℝ) • L.axis v
  rw [zero_smul,← L.force_eq,v.pin.pointForceOnWholePrefix_eq_star_sum]
  apply Finset.sum_eq_zero
  intro w hw
  rw [congrFun hs w,Pi.zero_apply,zero_smul]

/-- Different scalar components have disjoint sets of actual pins. -/
theorem SoftScalarSystem.vertices_disjoint
    (L : SoftScalarSystem M p) (c d : L.graph.ConnectedComponent) (hcd : c ≠ d) :
    Disjoint (L.vertices c) (L.vertices d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  obtain ⟨hsoft,hv'⟩ := (L.mem_vertices c v).mp hv
  obtain ⟨hsoft',hc'⟩ := (L.mem_vertices d v).mp hc
  exact hcd (hv'.symm.trans hc')

/-- The cut's support contains every component pin and the observer,
and contains no other actual vertex. -/
theorem SoftScalarSystem.exceptionalCut_vertexSupport
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v₀ : SoftPointPin M.graph) (hv₀ : L.graph.connectedComponentMk v₀ = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : L.scalar v₀ s ≠ 0) :
    coefficientVertexSupport (maskedGraph M.graph Finset.univ)
      (L.exceptionalCut hgen hp c h hc s).val = insert h.val (L.vertices c) := by
  let t := L.exceptionalCut hgen hp c h hc s
  have hlam₀ : L.scalar v₀ t ≠ 0 := by
    rw [L.exceptionalCut_scalar hgen hp c h hc v₀ hv₀ s]
    exact hs
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨e,hwe,he⟩ := (mem_coefficientVertexSupport _ t.val w).mp hw
    by_contra hwT
    have hout : ¬ ∀ z, z ∈ e.val → z ∈ insert h.val (L.vertices c) :=
      fun hh => hwT (hh w hwe)
    exact he (cut_supported _ (L.vertices c) h.val s.val
      (L.sole_component_boundary hgen hp c h hc s) e hout)
  · intro w hw
    rw [← star_ne_zero_iff_mem_vertexSupport]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact L.sole_observer_star_ne_zero hp c h hc v₀ hv₀ t hlam₀
    · let v : SoftPointPin M.graph := ⟨w,L.soft_of_mem_vertices c w hw⟩
      have hv : L.graph.connectedComponentMk v = c := L.mk_eq_of_mem_vertices c v hw
      intro hstar
      have hz := L.scalar_zero_of_star_zero v t hstar
      exact hlam₀ (L.scalar_zero_of_same_component hp v₀ v (hv₀.trans hv.symm) t hz)

/-- On every induced prefix, an exceptional scalar vanishes unless all
vertices of its complete mode support have already appeared. -/
theorem SoftScalarSystem.exceptional_scalar_vanishes_on_incomplete_prefix
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (T : Finset V) (hT : ¬ insert h.val (L.vertices c) ⊆ T)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T s.val) :
    L.scalar v s = 0 := by
  by_contra hnonzero
  have hcut := cut_preserves_vertex_support _ (L.vertices c) T s.val hs
  rw [coefficientsSupportedOn_iff_vertexSupport_subset,
    ← L.exceptionalCut_val hgen hp c h hc s,
    L.exceptionalCut_vertexSupport hgen hp c h hc v hv s hnonzero] at hcut
  exact hT hcut

/-- A normalized exceptional mode is present on a prefix exactly when
its complete support is present. -/
theorem SoftScalarSystem.exceptionalCut_supported_iff
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = c)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : L.scalar v s ≠ 0)
    (T : Finset V) :
    CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T
      (L.exceptionalCut hgen hp c h hc s).val ↔ insert h.val (L.vertices c) ⊆ T := by
  rw [coefficientsSupportedOn_iff_vertexSupport_subset,
    L.exceptionalCut_vertexSupport hgen hp c h hc v hv s hs]

/-- An exceptional cut has zero stars on every other scalar component. -/
theorem SoftScalarSystem.exceptionalCut_other_component_stars_zero
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c d : L.graph.ConnectedComponent) (hcd : c ≠ d)
    (h : Hypervertex M.graph) (hc : L.observers c = {Sum.inl h})
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    ∀ v ∈ L.vertices d, starCoordinates (maskedGraph M.graph Finset.univ) v
      (L.exceptionalCut hgen hp c h hc s).val = 0 := by
  intro v hv
  have hvS : v ∉ L.vertices c := fun hc' =>
    Finset.disjoint_left.mp (L.vertices_disjoint c d hcd) hc' hv
  have hvh : v ≠ h.val := by
    intro heq
    exact L.hypervertex_not_mem_vertices d h (heq ▸ hv)
  have hvT : v ∉ insert h.val (L.vertices c) := by simp [hvh,hvS]
  funext w
  by_cases hadj : (maskedGraph M.graph Finset.univ).Adj v w
  · rw [starCoordinates_of_adj _ _ _ _ hadj]
    exact cut_supported _ (L.vertices c) h.val s.val
      (L.sole_component_boundary hgen hp c h hc s) ⟨s(v,w),hadj⟩
      (fun hall => hvT (hall v (Sym2.mem_mk_left v w)))
  · exact starCoordinates_of_not_adj _ _ _ _ hadj

/-- Scalar evaluations on different exceptional cuts are zero. Together
with the normalization theorem this is actual biorthogonality. -/
theorem SoftScalarSystem.exceptionalCut_other_scalar_zero
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (c d : L.graph.ConnectedComponent) (hcd : c ≠ d)
    (h : Hypervertex M.graph) (hc : L.observers c = {Sum.inl h})
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (v : SoftPointPin M.graph) (hv : L.graph.connectedComponentMk v = d) :
    L.scalar v (L.exceptionalCut hgen hp c h hc s) = 0 := by
  apply L.scalar_zero_of_star_zero
  exact L.exceptionalCut_other_component_stars_zero hgen hp c d hcd h hc s v.val
    ((L.mem_vertices d v.val).mpr ⟨v.property,hv⟩)

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0027

section BundleSource0028
/- Source: Papers/RigiditySelectedCoreModes.lean -/






@[expose] public section

/-!
# Selected K5 modes and their literal coefficient functionals

A selector is either an actual soft point pin of a five-vertex body,
or an actual K5/K4 hinge port.  One selector is enough for each body.
The resulting coordinate is an ordinary bar coefficient divided by
the corresponding nonzero coefficient of an actual local K5 stress.
Its star identity, complete five-vertex prefix requirement, and
biorthogonality are consequences of the actual local stress spaces.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

/-- The two literal kinds of private ports used to select a core mode. -/
inductive PrivateCorePort (M : MinimalCounterexample V) (C : Body M.graph) where
  | point (v : SoftPointPin M.graph) (mem : v.val ∈ C.val)
  | hinge (h v : V) (port : CorePort M C h v)

variable {M : MinimalCounterexample V} {p : Placement V 3} {C D : Body M.graph}

def PrivateCorePort.vertex (P : PrivateCorePort M C) : V :=
  match P with
  | .point v _ => v.val
  | .hinge _ v _ => v

def PrivateCorePort.pin (P : PrivateCorePort M C) : TwoBodyPin M.graph P.vertex :=
  match P with
  | .point v _ => v.pin
  | .hinge _ _ Q => Q.pin

theorem PrivateCorePort.mem_core (P : PrivateCorePort M C) : P.vertex ∈ C.val := by
  cases P with
  | point v hv => exact hv
  | hinge h v Q => exact Q.port_mem_core

theorem PrivateCorePort.not_hypervertex (P : PrivateCorePort M C) :
    ¬ IsHypervertex M.graph P.vertex := P.pin.not_hypervertex

theorem nonempty_privateCorePort_iff :
    Nonempty (PrivateCorePort M C) ↔
      (bodySoftVertices M C).Nonempty ∨ (bodyTypeBVertices M C).Nonempty := by
  constructor
  · rintro ⟨P⟩
    cases P with
    | point v hv => exact Or.inl ⟨v.val,Finset.mem_filter.mpr ⟨hv,v.property⟩⟩
    | hinge h v Q =>
        exact Or.inr ⟨v,Finset.mem_filter.mpr ⟨Q.port_mem_core,h,⟨Q⟩⟩⟩
  · rintro (⟨v,hv⟩ | ⟨v,hv⟩)
    · obtain ⟨hvC,hsoft⟩ := Finset.mem_filter.mp hv
      exact ⟨PrivateCorePort.point ⟨v,hsoft⟩ hvC⟩
    · obtain ⟨hvC,h,⟨Q⟩⟩ := Finset.mem_filter.mp hv
      exact ⟨PrivateCorePort.hinge h v Q⟩

/-- No selected core edge belongs to any other body of order at least
five.  At a point pin this uses the literal one-vertex intersection;
at a hinge port its only other body is the displayed tetrahedron. -/
theorem PrivateCorePort.other_large_not_adj
    (P : PrivateCorePort M C) (D : Body M.graph) (hDC : D ≠ C)
    (hD : 5 ≤ D.val.card) (w : V) (hwC : w ∈ C.val) :
    ¬ (cliqueOn (D.val ∩ Finset.univ)).Adj P.vertex w := by
  intro hadj
  have hvD := (Finset.mem_inter.mp hadj.2.1).1
  have hwD := (Finset.mem_inter.mp hadj.2.2).1
  cases P with
  | point v hv =>
      exact hadj.1 (v.isPoint.no_shared_edge C D hDC.symm hv hvD w hwC hwD).symm
  | hinge h v Q =>
      rcases Q.pin.exhaustive D hvD with heq | heq
      · exact hDC (heq.trans Q.core_eq)
      · have hc : D.val.card = 4 := by simpa only [heq] using Q.outer_card
        omega

/-- Other internal body stresses have zero coefficient on the selected
core star.  The tetrahedral side of a hinge has no internal stress. -/
theorem PrivateCorePort.other_local_star_zero
    (P : PrivateCorePort M C) (hp : GeneralPosition.InGeneralPosition p)
    (D : Body M.graph) (hDC : D ≠ C)
    (s : StressSpace (cliqueOn (D.val ∩ Finset.univ)) p)
    (w : V) (hwC : w ∈ C.val) :
    starCoordinates (cliqueOn (D.val ∩ Finset.univ)) P.vertex s.val w = 0 := by
  by_cases hsmall : D.val.card ≤ 4
  · have hbot := stress_clique_le_four_eq_bot p hp
      (D.val ∩ Finset.univ) (by simpa only [Finset.inter_univ] using hsmall)
    have hs : s.val = 0 := by simpa only [hbot,Submodule.mem_bot] using s.property
    simp only [hs,map_zero,Pi.zero_apply]
  · exact starCoordinates_of_not_adj _ _ _ _
      (P.other_large_not_adj D hDC (by omega) w hwC)

/-- In a sum of actual local stresses, the selected core star is read
from precisely its own local summand. -/
theorem PrivateCorePort.local_sum_core_star
    (P : PrivateCorePort M C) (hp : GeneralPosition.InGeneralPosition p)
    (b : BodyFragmentStresses M.graph p Finset.univ)
    (w : V) (hwC : w ∈ C.val) :
    starCoordinates (maskedGraph M.graph Finset.univ) P.vertex
      (localPrefixStressSum M.graph p Finset.univ b).val w =
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) P.vertex (b C).val w := by
  rw [localPrefixStressSum_val,map_sum,Finset.sum_apply]
  simp only [starCoordinates_extendEdgeCoefficients]
  apply Finset.sum_eq_single C
  · intro D _ hDC
    exact P.other_local_star_zero hp D hDC (b D) w hwC
  · simp

/-- An actual chosen local K5 stress with one actual private port. -/
structure SelectedCoreMode (M : MinimalCounterexample V) (p : Placement V 3)
    (C : Body M.graph) where
  card_eq_five : C.val.card = 5
  port : PrivateCorePort M C
  localStress : StressSpace (cliqueOn (C.val ∩ Finset.univ)) p
  localStress_ne_zero : localStress ≠ 0

theorem exists_selectedCoreMode
    (hgen : IsGenericPlacement p) (C : Body M.graph) (hC : C.val.card = 5)
    (P : PrivateCorePort M C) : Nonempty (SelectedCoreMode M p C) := by
  have hd : Module.finrank ℝ (StressSpace (cliqueOn (C.val ∩ Finset.univ)) p) = 1 :=
    fiveCliqueStress_finrank p hgen _ (by simpa only [Finset.inter_univ] using hC)
  obtain ⟨s,hs⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (R := ℝ) (M := StressSpace (cliqueOn (C.val ∩ Finset.univ)) p)).mp (by omega)
  exact ⟨⟨hC,P,s,hs⟩⟩

theorem selectedCoreMode_nonempty
    (hgen : IsGenericPlacement p) (C : SelectedCore M) :
    Nonempty (SelectedCoreMode M p C.val) := by
  obtain ⟨P⟩ := nonempty_privateCorePort_iff.mpr C.property.2
  exact exists_selectedCoreMode hgen C.val C.property.1 P

/-- A simultaneous selection for all and only the selected cores of
the original graph. The preceding theorem proves that every choice is
an actual nonzero equilibrium stress with an actual private port. -/
def selectedCoreMode (hgen : IsGenericPlacement p) (C : SelectedCore M) :
    SelectedCoreMode M p C.val := Classical.choice (selectedCoreMode_nonempty hgen C)

variable (B : SelectedCoreMode M p C)

def SelectedCoreMode.vertex : V := B.port.vertex

theorem SelectedCoreMode.vertex_mem : B.vertex ∈ C.val := B.port.mem_core

theorem SelectedCoreMode.exists_neighbor : ∃ w ∈ C.val, w ≠ B.vertex :=
  Finset.exists_mem_ne (s := C.val) (by rw [B.card_eq_five]; omega) B.vertex

def SelectedCoreMode.neighbor : V := Classical.choose B.exists_neighbor

theorem SelectedCoreMode.neighbor_mem : B.neighbor ∈ C.val :=
  (Classical.choose_spec B.exists_neighbor).1

theorem SelectedCoreMode.neighbor_ne : B.neighbor ≠ B.vertex :=
  (Classical.choose_spec B.exists_neighbor).2

def SelectedCoreMode.localEdge : Edge (cliqueOn (C.val ∩ Finset.univ)) :=
  ⟨s(B.vertex,B.neighbor),B.neighbor_ne.symm,
    Finset.mem_inter.mpr ⟨B.vertex_mem,Finset.mem_univ _⟩,
    Finset.mem_inter.mpr ⟨B.neighbor_mem,Finset.mem_univ _⟩⟩

def SelectedCoreMode.unitCoefficient : ℝ := B.localStress.val B.localEdge

theorem SelectedCoreMode.unitCoefficient_ne_zero
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) :
    B.unitCoefficient ≠ 0 :=
  fiveCliqueStress_edge_ne_zero p hgen hp _
    (by simpa only [Finset.inter_univ] using B.card_eq_five)
    B.localStress B.localStress_ne_zero B.localEdge

/-- The coefficient is a genuine ordinary graph-bar functional.  It is
defined on the full stress space and used on the scalar kernel. -/
def SelectedCoreMode.coefficient :
    Module.Dual ℝ (StressSpace (maskedGraph M.graph Finset.univ) p) :=
  B.unitCoefficient⁻¹ • stressEdgeFunctional M.graph p B.vertex B.neighbor

@[simp] theorem SelectedCoreMode.coefficient_apply
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    B.coefficient s = B.unitCoefficient⁻¹ *
      starCoordinates (maskedGraph M.graph Finset.univ) B.vertex s.val B.neighbor := rfl

def SelectedCoreMode.fullStress : StressSpace (maskedGraph M.graph Finset.univ) p :=
  localPrefixStressSum M.graph p Finset.univ (Pi.single C B.localStress)

theorem SelectedCoreMode.fullStress_val :
    B.fullStress.val =
      extendEdgeCoefficients (fragment_le_masked M.graph Finset.univ C) B.localStress.val := by
  rw [SelectedCoreMode.fullStress,localPrefixStressSum_val]
  rw [Finset.sum_eq_single C]
  · simp
  · intro D _ hDC
    simp only [Pi.single_eq_of_ne hDC,ZeroMemClass.coe_zero,map_zero]
  · simp

theorem SelectedCoreMode.fullStress_star (v w : V) :
    starCoordinates (maskedGraph M.graph Finset.univ) v B.fullStress.val w =
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v B.localStress.val w := by
  rw [B.fullStress_val,starCoordinates_extendEdgeCoefficients]

theorem SelectedCoreMode.fullStress_mem_kernel (L : SoftScalarSystem M p) :
    B.fullStress.val ∈ L.scalarKernel := by
  have hm := L.localPrefixStresses_le_coannihilator
    (show B.fullStress ∈ localPrefixStresses M.graph p Finset.univ from
      ⟨Pi.single C B.localStress,rfl⟩)
  rw [Submodule.mem_dualCoannihilator] at hm
  exact (L.mem_scalarKernel B.fullStress).mpr fun v =>
    hm _ (Submodule.subset_span ⟨v,rfl⟩)

def SelectedCoreMode.kernelStress (L : SoftScalarSystem M p) : L.scalarKernel :=
  ⟨B.fullStress.val,B.fullStress_mem_kernel L⟩

def SelectedCoreMode.kernelCoefficient (L : SoftScalarSystem M p) :
    Module.Dual ℝ L.scalarKernel :=
  B.coefficient.comp (Submodule.inclusion L.scalarKernel_le_stress)

theorem SelectedCoreMode.coefficient_fullStress
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) :
    B.coefficient B.fullStress = 1 := by
  rw [B.coefficient_apply,B.fullStress_star,
    starCoordinates_of_adj _ _ _ _ B.localEdge.property]
  exact inv_mul_cancel₀ (B.unitCoefficient_ne_zero hgen hp)

theorem SelectedCoreMode.localStress_multiple
    (hgen : IsGenericPlacement p)
    (s : StressSpace (cliqueOn (C.val ∩ Finset.univ)) p) :
    ∃ c : ℝ, s = c • B.localStress := by
  have hd := fiveCliqueStress_finrank p hgen (C.val ∩ Finset.univ)
    (by simpa only [Finset.inter_univ] using B.card_eq_five)
  have hne : B.localStress.val ≠ 0 := fun h => B.localStress_ne_zero (Subtype.ext h)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd
    B.localStress.property hne
  have hs : s.val ∈ ℝ ∙ B.localStress.val := hspan.le s.property
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hs
  exact ⟨c,Subtype.ext hc.symm⟩

/-- Equation (8): on the actual residual stress space, all four core
edges at the chosen port are read by one literal coefficient. -/
theorem SelectedCoreMode.core_star_eq_coefficient
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : s.val ∈ L.scalarKernel) (w : V) (hw : w ∈ C.val) :
    starCoordinates (maskedGraph M.graph Finset.univ) B.vertex s.val w =
      B.coefficient s *
        starCoordinates (cliqueOn (C.val ∩ Finset.univ)) B.vertex B.localStress.val w := by
  obtain ⟨b,hstar,_⟩ := L.exists_local_prefix_stars hgen hp B.vertex B.port.pin
    Finset.univ (Finset.mem_univ _) s hs (by
      intro e he
      exact False.elim (he (fun _ _ => Finset.mem_univ _)))
  obtain ⟨c,hc⟩ := B.localStress_multiple hgen (b C)
  have hread (z : V) (hz : z ∈ C.val) :
      starCoordinates (maskedGraph M.graph Finset.univ) B.vertex s.val z =
      c * starCoordinates (cliqueOn (C.val ∩ Finset.univ)) B.vertex B.localStress.val z := by
    have hlocal :
        starCoordinates (maskedGraph M.graph Finset.univ) B.vertex
          (localPrefixStressSum M.graph p Finset.univ b).val z =
        starCoordinates (cliqueOn (C.val ∩ Finset.univ)) B.vertex (b C).val z :=
      B.port.local_sum_core_star hp b z hz
    rw [← hstar,hlocal,hc]
    simp only [SetLike.val_smul,map_smul,Pi.smul_apply,smul_eq_mul]
  have hcoef : B.coefficient s = c := by
    rw [B.coefficient_apply,hread B.neighbor B.neighbor_mem,
      starCoordinates_of_adj _ _ _ _ B.localEdge.property]
    change B.unitCoefficient⁻¹ * (c * B.unitCoefficient) = c
    field_simp [B.unitCoefficient_ne_zero hgen hp]
  rw [hcoef]
  exact hread w hw

/-- A different selected core mode has zero coefficient at this
selector, even when the bodies share a point pin. -/
theorem SelectedCoreMode.coefficient_other_fullStress
    (A : SelectedCoreMode M p D) (hDC : D ≠ C) :
    B.coefficient A.fullStress = 0 := by
  have hnot : ¬ (cliqueOn (D.val ∩ Finset.univ)).Adj B.vertex B.neighbor :=
    B.port.other_large_not_adj D hDC (by rw [A.card_eq_five]) B.neighbor B.neighbor_mem
  rw [B.coefficient_apply,A.fullStress_star,
    starCoordinates_of_not_adj _ _ _ _ hnot,mul_zero]

/-- Every ordinary coefficient of this local mode is supported on its
literal core, rather than merely on an abstract five-element index. -/
theorem SelectedCoreMode.fullStress_supported :
    CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) C.val B.fullStress.val := by
  intro e he v hve
  have hm : e.val ∈ (cliqueOn (C.val ∩ Finset.univ)).edgeSet := by
    by_contra hn
    exact he (by rw [B.fullStress_val,extendEdgeCoefficients_outside _ _ e hn])
  obtain ⟨w,hew⟩ := Sym2.mem_iff_exists.mp hve
  rw [hew] at hm
  exact (Finset.mem_inter.mp hm.2.1).1

theorem SelectedCoreMode.fullStress_supported_in_prefix
    (T : Finset V) (hCT : C.val ⊆ T) :
    CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T B.fullStress.val := by
  intro e he v hv
  exact hCT (B.fullStress_supported e he v hv)

/-- A nonzero coefficient requires all five vertices of the selected
core, including when the prefix omits the selected port itself. -/
theorem SelectedCoreMode.core_subset_of_coefficient_ne_zero
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (T : Finset V) (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : s.val ∈ L.scalarKernel)
    (hsT : CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T s.val)
    (hcoef : B.coefficient s ≠ 0) : C.val ⊆ T := by
  have hedge (w : V) (hw : w ∈ C.val) (hvw : B.vertex ≠ w) :
      B.vertex ∈ T ∧ w ∈ T := by
    let e : Edge (cliqueOn (C.val ∩ Finset.univ)) :=
      ⟨s(B.vertex,w),hvw,Finset.mem_inter.mpr ⟨B.vertex_mem,Finset.mem_univ _⟩,
        Finset.mem_inter.mpr ⟨hw,Finset.mem_univ _⟩⟩
    let d := edgeInclusion (fragment_le_masked M.graph Finset.univ C) e
    have hne : s.val d ≠ 0 := by
      have hread := B.core_star_eq_coefficient L hgen hp s hs w hw
      rw [starCoordinates_of_adj _ _ _ _ d.property,
        starCoordinates_of_adj _ _ _ _ e.property] at hread
      change s.val d = B.coefficient s * B.localStress.val e at hread
      rw [hread]
      exact mul_ne_zero hcoef (fiveCliqueStress_edge_ne_zero p hgen hp _
        (by simpa only [Finset.inter_univ] using B.card_eq_five)
        B.localStress B.localStress_ne_zero e)
    exact ⟨hsT d hne _ (Sym2.mem_mk_left _ _),hsT d hne _ (Sym2.mem_mk_right _ _)⟩
  intro w hw
  by_cases hwv : w = B.vertex
  · subst w
    exact (hedge B.neighbor B.neighbor_mem B.neighbor_ne.symm).1
  · exact (hedge w hw (Ne.symm hwv)).2

theorem SelectedCoreMode.coefficient_zero_on_incomplete_prefix
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (T : Finset V) (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (hs : s.val ∈ L.scalarKernel)
    (hsT : CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T s.val)
    (hmissing : ¬ C.val ⊆ T) : B.coefficient s = 0 := by
  by_contra hn
  exact hmissing (B.core_subset_of_coefficient_ne_zero L hgen hp T s hs hsT hn)

/-- Every hypervertex of the selected core reads its coordinate on the
literal edge joining it to the chosen private port. -/
theorem SelectedCoreMode.hypervertex_reads_coefficient
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (h : V) (hh : h ∈ C.val) (hhyper : IsHypervertex M.graph h) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ s : StressSpace (maskedGraph M.graph Finset.univ) p,
      s.val ∈ L.scalarKernel →
      starCoordinates (maskedGraph M.graph Finset.univ) h s.val B.vertex = c * B.coefficient s := by
  have hvh : B.vertex ≠ h := by
    intro heq
    have hB : IsHypervertex M.graph B.vertex := heq.symm ▸ hhyper
    exact B.port.not_hypervertex hB
  let e : Edge (cliqueOn (C.val ∩ Finset.univ)) :=
    ⟨s(B.vertex,h),hvh,Finset.mem_inter.mpr ⟨B.vertex_mem,Finset.mem_univ _⟩,
      Finset.mem_inter.mpr ⟨hh,Finset.mem_univ _⟩⟩
  refine ⟨B.localStress.val e,fiveCliqueStress_edge_ne_zero p hgen hp _
    (by simpa only [Finset.inter_univ] using B.card_eq_five)
    B.localStress B.localStress_ne_zero e,?_⟩
  intro s hs
  rw [starCoordinates_symm,B.core_star_eq_coefficient L hgen hp s hs h hh,
    starCoordinates_of_adj _ _ _ _ e.property,mul_comm]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0028

section BundleSource0029
/- Source: Papers/RigidityCoreStarReadout.lean -/




@[expose] public section

/-!
# Full-stress readout at type-B ports

For a K5 core with no soft point pin and at most one hypervertex,
simultaneous hinge normalization makes its complete copied load zero.
Its copied coefficients are therefore one actual local K5 stress.
Every type-B star of that core reads the same local coefficient.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}
variable {C : Body M.graph} {h v : V}

/-- A normalized tetrahedral side contributes no coefficient at its
hinge port, including on the duplicated hinge edge itself. -/
theorem CorePort.normalized_core_star
    (P : CorePort M C h v) (hp : GeneralPosition.InGeneralPosition p)
    (a : compatibleCopiedCoefficients M.graph p Finset.univ)
    (hzero : ∀ D : Body M.graph,
      (bodyCopyForces M.graph p Finset.univ a.val D).val v = 0)
    (w : V) :
    starCoordinates (maskedGraph M.graph Finset.univ) v
      (copiedToStress M.graph p Finset.univ a).val w =
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ C a.val) w := by
  rw [copiedToStress_val,copyAggregate_eq_sum_extensions,map_sum,Finset.sum_apply]
  simp only [starCoordinates_extendEdgeCoefficients]
  apply Finset.sum_eq_single C
  · intro D _ hDC
    by_cases hvD : v ∈ D.val
    · have hD : D = P.pin.right := by
        rcases P.pin.exhaustive D hvD with hd | hd
        · exact False.elim (hDC (hd.trans P.core_eq))
        · exact hd
      have hfour : D.val.card ≤ 4 := by simp only [hD,P.outer_card,Nat.le_refl]
      have hz := clique_star_zero_of_zero_force p hp (D.val ∩ Finset.univ)
        (by simpa only [Finset.inter_univ] using hfour) v
        (Finset.mem_inter.mpr ⟨hvD,Finset.mem_univ _⟩)
        (bodyCopyRestriction M.graph Finset.univ D a.val) (hzero D)
      exact congrFun hz w
    · exact starCoordinates_of_not_adj _ _ _ _
        (fun hadj => hvD (Finset.mem_inter.mp hadj.2.1).1)
  · simp

/-- The normalized actual copied restriction of the core is a genuine
equilibrium stress, not an assumed stress parameter. -/
theorem exists_normalized_core_stress
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (C : Body M.graph) (h : V)
    (hsoft : ∀ v ∈ C.val, ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ v ∈ C.val, IsHypervertex M.graph v → v = h)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    ∃ t : StressSpace (cliqueOn (C.val ∩ Finset.univ)) p,
      ∀ (z v : V) (P : CorePort M C z v) (w : V),
        starCoordinates (maskedGraph M.graph Finset.univ) v s.val w =
        starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v t.val w := by
  obtain ⟨a,ha⟩ := copiedToStress_surjective M.graph M.covered p Finset.univ s
  obtain ⟨b,hb,hzero⟩ := exists_hinge_normalized_copied_coefficients M p hgen hp a
  have hload := normalized_load_zero_on_body_with_at_most_one_hypervertex
    M p hgen hp (copiedToLoads M.graph p Finset.univ b) hzero C h hsoft hhyper
  have ht : bodyCopyRestriction M.graph Finset.univ C b.val ∈
      StressSpace (cliqueOn (C.val ∩ Finset.univ)) p := by
    apply (forceOperator_eq_zero_iff _ p _).mp
    exact hload
  refine ⟨⟨bodyCopyRestriction M.graph Finset.univ C b.val,ht⟩,?_⟩
  intro z v P w
  rw [← ha,← hb]
  exact P.normalized_core_star hp b (hzero v P.pin P.hinge) w

/-- For a core without soft pins, the chosen private port is itself
one of its actual K5/K4 hinge ports. -/
theorem PrivateCorePort.eq_hinge_of_no_soft
    (P : PrivateCorePort M C)
    (hsoft : ∀ v ∈ C.val, ¬ IsSoftPointPin M.graph v) :
    ∃ h v, ∃ Q : CorePort M C h v, P = PrivateCorePort.hinge h v Q := by
  cases P with
  | point v hv => exact False.elim (hsoft v.val hv v.property)
  | hinge h v Q => exact ⟨h,v,Q,rfl⟩

/-- A single coefficient reads all specified type-B stars of a
one-hypervertex core with no soft pin, on the full ordinary stress
space.  No scalar-kernel hypothesis is required here. -/
theorem SelectedCoreMode.typeB_star_eq_coefficient
    (B : SelectedCoreMode M p C)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : V)
    (hsoft : ∀ v ∈ C.val, ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ v ∈ C.val, IsHypervertex M.graph v → v = h)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p)
    (z v : V) (P : CorePort M C z v) (w : V) :
    starCoordinates (maskedGraph M.graph Finset.univ) v s.val w =
      B.coefficient s *
        starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v B.localStress.val w := by
  obtain ⟨t,ht⟩ := exists_normalized_core_stress M p hgen hp C h hsoft hhyper s
  obtain ⟨c,hc⟩ := B.localStress_multiple hgen t
  have hread (z v : V) (Q : CorePort M C z v) (w : V) :
      starCoordinates (maskedGraph M.graph Finset.univ) v s.val w =
      c * starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v B.localStress.val w := by
    rw [ht z v Q w,hc]
    simp only [SetLike.val_smul,map_smul,Pi.smul_apply,smul_eq_mul]
  obtain ⟨z₀,v₀,Q₀,hport⟩ := B.port.eq_hinge_of_no_soft hsoft
  have hv₀ : B.vertex = v₀ := congrArg PrivateCorePort.vertex hport
  have hcoef : B.coefficient s = c := by
    rw [B.coefficient_apply,hv₀,hread z₀ v₀ Q₀ B.neighbor,← hv₀,
      starCoordinates_of_adj _ _ _ _ B.localEdge.property]
    change B.unitCoefficient⁻¹ * (c * B.unitCoefficient) = c
    field_simp [B.unitCoefficient_ne_zero hgen hp]
  rw [hcoef]
  exact hread z v P w

theorem SelectedCoreMode.typeB_hyperstar_zero_of_coefficient_zero
    (B : SelectedCoreMode M p C)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : V)
    (hsoft : ∀ v ∈ C.val, ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ v ∈ C.val, IsHypervertex M.graph v → v = h)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) (hs : B.coefficient s = 0)
    (v : V) (P : CorePort M C h v) :
    starCoordinates (maskedGraph M.graph Finset.univ) h s.val v = 0 := by
  rw [starCoordinates_symm,B.typeB_star_eq_coefficient hgen hp h hsoft hhyper s h v P h,
    hs,zero_mul]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0029

section BundleSource0030
/- Source: Papers/RigidityStarChargeBound.lean -/



@[expose] public section

/-!
# The actual star-rank inequality behind equation (10)

After controlling the rank seen on specified star edges, the residual
star is supported on the remaining edges. Its minimum support is four,
so the proved Singleton bound gives dimension at most `D - 3`. This
supplies the exact `min(3,D)` contribution, including all small D cases.
-/

noncomputable section
namespace Papers.Rigidity.SupportedCode

open scoped Classical

variable {K I : Type*} [Field K] [Fintype I]

def selectedRestriction (C : Submodule K (I → K)) (A : Finset I) :
    C →ₗ[K] (A → K) :=
  (coordinateRestriction (Function.Embedding.subtype (fun i => i ∈ A))).domRestrict C

@[simp] theorem selectedRestriction_apply
    (C : Submodule K (I → K)) (A : Finset I) (x : C) (i : A) :
    selectedRestriction C A x i = x.val i.val := rfl

/-- Exact kernel identification with the ordinary residual supported
code. There is no prescribed residual dimension. -/
def selectedRestrictionKernelEquiv
    (C : Submodule K (I → K)) (A : Finset I) :
    (selectedRestriction C A).ker ≃ₗ[K] supportedOn C {i | i ∉ A} where
  toFun x := ⟨x.val.val,x.val.property,by
    intro i hi
    have hiA : i ∈ A := not_not.mp hi
    exact congrFun (LinearMap.mem_ker.mp x.property) ⟨i,hiA⟩⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,by
    rw [LinearMap.mem_ker]
    funext i
    exact x.property.2 i.val (not_not.mpr i.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The residual minimum-support-four code obeys Singleton even when
there are fewer than four remaining coordinates. -/
theorem residual_finrank_le
    (C : Submodule K (I → K)) (hC : MinimumSupport C 4) (A : Finset I) :
    Module.finrank K (supportedOn C {i | i ∉ A}) ≤
      (Fintype.card I - A.card) - 3 := by
  let R := supportedOn C {i | i ∉ A}
  change Module.finrank K R ≤ (Fintype.card I - A.card) - 3
  by_cases hR : R = ⊥
  · rw [hR,finrank_bot]
    exact Nat.zero_le _
  have hmin : MinimumSupport R 4 := fun x hx hne => hC x hx.1 hne
  have hbound := singleton_bound R 4 (by decide) hmin hR
  have hsub : activeCoordinates R ⊆ Finset.univ \ A := by
    intro i hi
    obtain ⟨x,hx,hxi⟩ := (mem_activeCoordinates R i).mp hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hiA =>
      hxi (hx.2 i (not_not.mpr hiA))⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),Finset.card_univ] at hcard
  change Module.finrank K R ≤ _
  omega

/-- A precise code-dimension bound for an arbitrary specified subset of
coordinates. The observed rank is the actual restriction image rank. -/
theorem selected_rank_ledger
    (C : Submodule K (I → K)) (hC : MinimumSupport C 4) (A : Finset I) :
    Module.finrank K C + A.card + min 3 (Fintype.card I - A.card) ≤
      Fintype.card I + Module.finrank K (selectedRestriction C A).range := by
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (K := K) (V := C) (V₂ := A → K) (selectedRestriction C A)
  rw [(selectedRestrictionKernelEquiv C A).finrank_eq] at hdim
  have hres := residual_finrank_le C hC A
  have hAc : A.card ≤ Fintype.card I := Finset.card_le_univ A
  omega

end Papers.Rigidity.SupportedCode

namespace Papers.Rigidity.BarJoint

open SupportedCode VertexPin
open scoped Classical

variable {V : Type} [Fintype V]

/-- Exact additive form of the stress-star deletion-rank identity. -/
theorem stressStar_finrank_add_deletionRankDrop
    (G : SimpleGraph V) (p : Placement V 3) (hgen : IsGenericPlacement p) (v : V) :
    Module.finrank ℝ (stressStarCode G v (StressSpace G p)) + deletionRankDrop G v =
      G.degree v := by
  have h := stressStar_finrank_add_rank G p v
  have hdeleted := generic_deletedPlacement p hgen v
  have hle : genericRigidityRank (deletedGraph G v) 3 ≤ genericRigidityRank G 3 := by
    have hmono := rigidityRank_mono (isolateVertex_le G v) p
    rwa [rigidityRank_isolateVertex,hgen,hdeleted] at hmono
  rw [hgen,hdeleted] at h
  unfold deletionRankDrop
  omega

/-- Equation (10)'s linear-algebra step, for the literal h-star of the
original stress space. A later choice of exceptional and core edges
only has to bound the rank of its actual selected-coordinate map. -/
theorem selected_star_deletion_bound
    (G : SimpleGraph V) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V)
    (A : Finset (IncidentEdge G v)) (r : ℕ)
    (hr : Module.finrank ℝ (selectedRestriction (stressStarCode G v (StressSpace G p)) A).range ≤ r) :
    A.card + min 3 (G.degree v - A.card) ≤ deletionRankDrop G v + r := by
  have h := selected_rank_ledger (stressStarCode G v (StressSpace G p))
    (stressStarCode_minimumSupport_four G p hp v _ le_rfl) A
  rw [card_incidentEdge_eq_degree] at h
  have hdim := stressStar_finrank_add_deletionRankDrop G p hgen v
  omega

end Papers.Rigidity.BarJoint

end
end
end BundleSource0030

section BundleSource0031
/- Source: Papers/RigidityHypervertexStarRank.lean -/




@[expose] public section

/-!
# The specified-star rank bound in Section 7.4

Every exceptional-component part is killed by its actual soft scalar.
Every counted no-soft core part is killed by its actual K5 coefficient.
Rank-nullity therefore bounds the rank of all specified ordinary star
edges by the number of those literal components and cores.
-/

noncomputable section
namespace Papers.Rigidity.BarJoint
open SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

def selectedStressStar (G : SimpleGraph V) (p : Placement V 3) (v : V)
    (A : Finset (IncidentEdge G v)) :
    StressSpace G p →ₗ[ℝ] (A → ℝ) :=
  LinearMap.pi fun e => (LinearMap.proj e.val.val).comp (StressSpace G p).subtype

@[simp] theorem selectedStressStar_apply
    (G : SimpleGraph V) (p : Placement V 3) (v : V)
    (A : Finset (IncidentEdge G v)) (s : StressSpace G p) (e : A) :
    selectedStressStar G p v A s e = s.val e.val.val := rfl

theorem selectedStressStar_range
    (G : SimpleGraph V) (p : Placement V 3) (v : V)
    (A : Finset (IncidentEdge G v)) :
    (selectedStressStar G p v A).range =
      (selectedRestriction (stressStarCode G v (StressSpace G p)) A).range := by
  ext y
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨⟨starRestriction G v s.val,⟨s.val,s.property,rfl⟩⟩,rfl⟩
  · rintro ⟨s,rfl⟩
    obtain ⟨a,ha,heq⟩ := s.property
    refine ⟨⟨a,ha⟩,?_⟩
    ext e
    exact congrFun heq e.val

/-- A family of actual linear readings that kills every specified bar
also bounds the dimension of the specified actual stress-star image. -/
theorem selectedStar_rank_le_of_joint_kernel
    (G : SimpleGraph V) (p : Placement V 3) (v : V)
    (A : Finset (IncidentEdge G v)) {I : Type*} [Fintype I]
    (ρ : I → Module.Dual ℝ (StressSpace G p))
    (hkill : ∀ s : StressSpace G p, (∀ i, ρ i s = 0) →
      ∀ e ∈ A, s.val e.val = 0) :
    Module.finrank ℝ
      (selectedRestriction (stressStarCode G v (StressSpace G p)) A).range ≤ Fintype.card I := by
  let f : StressSpace G p →ₗ[ℝ] (I → ℝ) := LinearMap.pi ρ
  let g := selectedStressStar G p v A
  have hker : f.ker ≤ g.ker := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    ext e
    exact hkill s (fun i => congrFun hs i) e.val e.property
  have hk := Submodule.finrank_mono hker
  have hf := f.finrank_range_add_finrank_ker
  have hg := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := StressSpace G p) (V₂ := A → ℝ) g
  have hr : Module.finrank ℝ f.range ≤ Fintype.card I := by
    simpa using Submodule.finrank_le f.range
  rw [← selectedStressStar_range G p v A]
  change Module.finrank ℝ g.range ≤ _
  omega

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- The literal exceptional-plus-core selected-star bound `rank ≤ a+g`.
The displayed edge cover is a cover by actual exceptional component
vertices and actual type-B port records of the original graph. -/
theorem SoftScalarSystem.exceptional_core_star_rank_le
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph)
    {I J : Type*} [Fintype I] [Fintype J]
    (component : I → L.graph.ConnectedComponent)
    (sole : ∀ i, L.observers (component i) = {Sum.inl h})
    (representative : I → SoftPointPin M.graph)
    (hrep : ∀ i, L.graph.connectedComponentMk (representative i) = component i)
    (core : J → Body M.graph)
    (mode : ∀ j, SelectedCoreMode M p (core j))
    (hsoft : ∀ j v, v ∈ (core j).val → ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ j v, v ∈ (core j).val → IsHypervertex M.graph v → v = h.val)
    (A : Finset (IncidentEdge (maskedGraph M.graph Finset.univ) h.val))
    (hcover : ∀ e ∈ A,
      (∃ i, incidentOther (maskedGraph M.graph Finset.univ) h.val e ∈ L.vertices (component i)) ∨
      (∃ j, Nonempty (CorePort M (core j) h.val
        (incidentOther (maskedGraph M.graph Finset.univ) h.val e)))) :
    Module.finrank ℝ (selectedRestriction
      (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (StressSpace (maskedGraph M.graph Finset.univ) p)) A).range ≤
      Fintype.card I + Fintype.card J := by
  let ρ : I ⊕ J → Module.Dual ℝ
      (StressSpace (maskedGraph M.graph Finset.univ) p) :=
    Sum.elim (fun i => L.scalar (representative i)) (fun j => (mode j).coefficient)
  have hbound := selectedStar_rank_le_of_joint_kernel
    (maskedGraph M.graph Finset.univ) p h.val A ρ (by
      intro s hs e he
      rw [← starCoordinates_incidentOther (maskedGraph M.graph Finset.univ) h.val s.val e]
      rcases hcover e he with ⟨i,hi⟩ | ⟨j,⟨P⟩⟩
      · rw [starCoordinates_symm]
        exact L.sole_component_stars_zero hp (component i) h (sole i)
          (representative i) (hrep i) s (hs (Sum.inl i)) _ hi h.val
      · exact (mode j).typeB_hyperstar_zero_of_coefficient_zero hgen hp h.val
          (hsoft j) (hhyper j) s (hs (Sum.inr j)) _ P)
  simpa only [Fintype.card_sum] using hbound

/-- Equation (10), after substituting the actual exceptional/core rank
bound.  The only choices are the finite lists of literal components,
cores, and the specified ordinary star edges. -/
theorem SoftScalarSystem.exceptional_core_star_deletion_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph)
    {I J : Type*} [Fintype I] [Fintype J]
    (component : I → L.graph.ConnectedComponent)
    (sole : ∀ i, L.observers (component i) = {Sum.inl h})
    (representative : I → SoftPointPin M.graph)
    (hrep : ∀ i, L.graph.connectedComponentMk (representative i) = component i)
    (core : J → Body M.graph)
    (mode : ∀ j, SelectedCoreMode M p (core j))
    (hsoft : ∀ j v, v ∈ (core j).val → ¬ IsSoftPointPin M.graph v)
    (hhyper : ∀ j v, v ∈ (core j).val → IsHypervertex M.graph v → v = h.val)
    (A : Finset (IncidentEdge (maskedGraph M.graph Finset.univ) h.val))
    (hcover : ∀ e ∈ A,
      (∃ i, incidentOther (maskedGraph M.graph Finset.univ) h.val e ∈ L.vertices (component i)) ∨
      (∃ j, Nonempty (CorePort M (core j) h.val
        (incidentOther (maskedGraph M.graph Finset.univ) h.val e)))) :
    A.card + min 3 (M.graph.degree h.val - A.card) ≤
      deletionRankDrop M.graph h.val + Fintype.card I + Fintype.card J := by
  have hbound := selected_star_deletion_bound
    (maskedGraph M.graph Finset.univ) p hgen hp h.val A
    (Fintype.card I + Fintype.card J)
    (L.exceptional_core_star_rank_le hgen hp h component sole representative hrep
      core mode hsoft hhyper A hcover)
  have hwhole : maskedGraph M.graph Finset.univ = M.graph := by
    ext a b
    simp only [maskedGraph,Finset.mem_univ,and_true]
  have hdegree : (maskedGraph M.graph Finset.univ).degree h.val = M.graph.degree h.val := by
    simp only [← SimpleGraph.ncard_neighborSet]
    rw [hwhole]
  simpa only [hdegree,hwhole,Nat.add_assoc] using hbound

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0031

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0031/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0031.json"

section BundleSource0032
/- Source: Papers/RigidityNeighborhoodBudget.lean -/




@[expose] public section

/-!
# The strict planar neighborhood budget and core-port boundary counts

The neighborhood cannot itself be planar rigid. Consequently the
independent union of bases from any actual incident bodies has at most
`2 d(h) - 4` edges. Applying this to K5 cores and their outer tetrahedra
gives the missing three directions in the zero-exceptional-mode case
of Section 7.4.
-/

noncomputable section
namespace Papers.Rigidity.NeighborhoodBases

open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The independent neighborhood bases satisfy the strict bound,
because equality at the planar rigidity bound would make v simplicial. -/
theorem union_edge_budget
    (M : MinimalCounterexample V) (v : V)
    {ι : Type} [Fintype ι] (T : ι → Finset V) (B : ι → SimpleGraph V)
    (hTinj : Function.Injective T)
    (hT : ∀ i, IsBody M.graph (T i)) (hv : ∀ i, v ∈ T i)
    (hB : ∀ i, (B i).IsSparse 2 3)
    (hedges : ∀ i, (B i).edgeSet ⊆ M.graph.edgesIn ((T i).erase v : Set V)) :
    (∑ i, (B i).edgeSet.ncard) + 4 ≤ 2 * M.graph.degree v := by
  let U : SimpleGraph V := ⨆ i, B i
  let N := M.graph.neighborFinset v
  have hsparse := union_isSparse M v T B hTinj hT hv hB hedges
  have hUG : U ≤ M.graph := by
    intro a b hab
    obtain ⟨i,hi⟩ := SimpleGraph.iSup_adj.mp hab
    exact (hedges i ((SimpleGraph.mem_edgeSet (B i)).mpr hi)).1
  have hinside : U.edgesIn (N : Set V) = U.edgeSet := by
    apply Set.inter_eq_left.mpr
    intro e he
    rw [SimpleGraph.edgeSet_iSup] at he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    apply Set.mem_sym2_iff_subset.mpr
    intro w hw
    have hwT := Finset.mem_erase.mp ((SimpleGraph.mem_edgesIn.mp (hedges i hi)).2 hw)
    exact (M.graph.mem_neighborFinset v w).mpr ((hT i).2.1 (hv i) hwT.2 hwT.1.symm)
  have hNcard : N.card = M.graph.degree v := M.graph.card_neighborFinset_eq_degree v
  have hdegree := M.connected.degree_ge v
  have hbound := hsparse N (by omega)
  change (U.edgesIn (N : Set V)).ncard + 3 ≤ 2 * N.card at hbound
  rw [hinside,hNcard] at hbound
  have hstrict : U.edgeSet.ncard + 4 ≤ 2 * M.graph.degree v := by
    by_contra hnot
    have heq : U.edgeSet.ncard + 3 = 2 * M.graph.degree v := by omega
    have hcardN : Fintype.card (N : Set V) = N.card :=
      @Fintype.card_coe V N (inferInstance : Fintype (N : Set V))
    have hlaman : (U.induce (N : Set V)).IsLaman := by
      refine ⟨hsparse.comap Subtype.val_injective,?_⟩
      rw [← SimpleGraph.ncard_edgesIn_eq_ncard_induce_edgeSet,hinside,
        Nat.card_eq_fintype_card,hcardN,hNcard]
      exact heq
    have hrigid : (M.graph.induce (N : Set V)).IsGenericallyRigid 2 :=
      SimpleGraph.IsGenericallyRigid.mono (fun _ _ h => hUG h)
        hlaman.isGenericallyRigid_two
    have hclique := Coning.planar_neighborhood_cone_isClique M v N
      (Finset.Subset.refl N) (by omega) hrigid
    apply M.not_simplicial v
    intro a ha b hb hab
    exact hclique
      (Finset.mem_insert_of_mem ((M.graph.mem_neighborFinset v a).mpr ha))
      (Finset.mem_insert_of_mem ((M.graph.mem_neighborFinset v b).mpr hb)) hab
  have hsum : U.edgeSet.ncard = ∑ i, (B i).edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_iSup]
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun i => (B i).edgeSet.toFinite)
        (pairwise_disjoint_edges M v T B hTinj hT hv hedges)
  rwa [hsum] at hstrict

/-- The numerical strict neighborhood budget for any chosen actual
incident maximal bodies. Their planar bases are constructed here. -/
theorem incident_body_budget
    (M : MinimalCounterexample V) (v : V) (S : Finset (BodyLoads.Body M.graph))
    (hS : ∀ C ∈ S, v ∈ C.val) :
    (∑ C ∈ S, (2 * C.val.card - 5)) + 4 ≤ 2 * M.graph.degree v := by
  have hex (C : S) : ∃ B : SimpleGraph V,
      B.IsSparse 2 3 ∧ B.edgeSet ⊆ M.graph.edgesIn ((C.val.val).erase v : Set V) ∧
      B.edgeSet.ncard + 3 = 2 * ((C.val.val).erase v).card := by
    apply exists_basis_on_clique M.graph ((C.val.val).erase v)
    · rw [Finset.card_erase_of_mem (hS C.val C.property)]
      have := C.val.property.1
      omega
    · intro a ha b hb hab
      exact C.val.property.2.1 (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hab
  choose B hBsparse hBedges hBcount using hex
  have h := union_edge_budget M v (fun C : S => C.val.val) B
    (fun C D h => Subtype.ext (Subtype.ext h)) (fun C => C.val.property)
    (fun C => hS C.val C.property) hBsparse hBedges
  have hcount (C : S) : (B C).edgeSet.ncard = 2 * C.val.val.card - 5 := by
    have hc := hBcount C
    rw [Finset.card_erase_of_mem (hS C.val C.property)] at hc
    have hcard := C.val.property.1
    omega
  simp only [hcount] at h
  rw [Finset.sum_coe_sort S (fun C : BodyLoads.Body M.graph => 2 * C.val.card - 5)] at h
  exact h

end Papers.Rigidity.NeighborhoodBases

namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin NeighborhoodBases
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- A vertex in a K5/K4 port has exactly one incident body of order at
least five. Thus counted ports cannot belong to another core. -/
theorem CorePort.core_unique
    {M : MinimalCounterexample V} {C : Body M.graph} {h v : V}
    (P : CorePort M C h v) (D : Body M.graph) (hD : 5 ≤ D.val.card)
    (hvD : v ∈ D.val) : D = C := by
  rcases P.pin.exhaustive D hvD with hDC | hDO
  · exact hDC.trans P.core_eq
  · have hcard : D.val.card = 4 := by
      simpa only [hDO] using P.outer_card
    omega

/-- A family of ports on one core exposes two distinct exterior
neighbors per port, in addition to the four core neighbors. -/
theorem core_ports_neighbor_bound
    (M : MinimalCounterexample V) (C : Body M.graph) (h : V)
    (P : Finset V) (Q : ∀ v : P, CorePort M C h v.val) (hP : P.Nonempty) :
    4 + 2 * P.card ≤ M.graph.degree h := by
  obtain ⟨v,hv⟩ := hP
  let port := Q ⟨v,hv⟩
  let X := Finset.univ.biUnion (fun v : P => (Q v).externalPair)
  have hXcard : X.card = 2 * P.card := externalPairs_card M C h P Q
  have hCcard : (C.val.erase h).card = 4 := by
    rw [Finset.card_erase_of_mem port.partner_mem_core,port.core_card]
  have hdisj : Disjoint (C.val.erase h) X := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxX
    obtain ⟨w,_,hwX⟩ := Finset.mem_biUnion.mp hxX
    exact (Finset.mem_sdiff.mp hwX).2 (Finset.mem_erase.mp hxC).2
  have hsub : C.val.erase h ∪ X ⊆ M.graph.neighborFinset h := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxh,hxC⟩ := Finset.mem_erase.mp hx
      exact (M.graph.mem_neighborFinset h x).mpr
        (C.property.2.1 port.partner_mem_core hxC hxh.symm)
    · obtain ⟨w,_,hwX⟩ := Finset.mem_biUnion.mp hx
      exact (Q w).externalPair_subset_neighbors hwX
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,hCcard,hXcard,
    M.graph.card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- The total actual incidence count of selected K5 cores and outer
K4s, before any exceptional coordinates are removed. -/
theorem core_port_family_neighborhood_budget
    (M : MinimalCounterexample V) (h : V) (P : Finset V)
    (core : P → Body M.graph) (Q : ∀ v : P, CorePort M (core v) h v.val) :
    5 * (Finset.univ.image core).card + P.card + 4 ≤ 2 * M.graph.degree h ∧
      P.card ≤ 4 * (Finset.univ.image core).card := by
  let A := Finset.univ.image core
  let B := Finset.univ.image (fun v : P => (Q v).outer)
  have hAcard (C : Body M.graph) (hC : C ∈ A) : C.val.card = 5 := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hC
    exact (Q v).core_card
  have hBcard (C : Body M.graph) (hC : C ∈ B) : C.val.card = 4 := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hC
    exact (Q v).outer_card
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro C hC hC'
    have ha := hAcard C hC
    have hb := hBcard C hC'
    omega
  have hpartner (C : Body M.graph) (hC : C ∈ A ∪ B) : h ∈ C.val := by
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hC
      exact (Q v).partner_mem_core
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hC
      exact (Q v).partner_mem_outer
  have hbudget := incident_body_budget M h (A ∪ B) hpartner
  rw [Finset.sum_union hdisj] at hbudget
  have hsumA : (∑ C ∈ A, (2 * C.val.card - 5)) = 5 * A.card := by
    calc
      _ = ∑ C ∈ A, 5 := Finset.sum_congr rfl (fun C hC => by rw [hAcard C hC])
      _ = _ := by simp [mul_comm]
  have hsumB : (∑ C ∈ B, (2 * C.val.card - 5)) = 3 * B.card := by
    calc
      _ = ∑ C ∈ B, 3 := Finset.sum_congr rfl (fun C hC => by rw [hBcard C hC])
      _ = _ := by simp [mul_comm]
  rw [hsumA,hsumB] at hbudget
  have hPouter : P ⊆ B.biUnion (fun C => C.val.erase h) := by
    intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨(Q ⟨v,hv⟩).outer,Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩,
        Finset.mem_erase.mpr ⟨(Q ⟨v,hv⟩).port_ne_partner,(Q ⟨v,hv⟩).port_mem_outer⟩⟩
  have hPcore : P ⊆ A.biUnion (fun C => C.val.erase h) := by
    intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨core ⟨v,hv⟩,Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩,
        Finset.mem_erase.mpr ⟨(Q ⟨v,hv⟩).port_ne_partner,(Q ⟨v,hv⟩).port_mem_core⟩⟩
  have hPB : P.card ≤ 3 * B.card := by
    calc
      P.card ≤ (B.biUnion (fun C => C.val.erase h)).card := Finset.card_le_card hPouter
      _ ≤ ∑ C ∈ B, (C.val.erase h).card := Finset.card_biUnion_le
      _ = ∑ C ∈ B, 3 := Finset.sum_congr rfl (fun C hC => by
        rw [Finset.card_erase_of_mem (hpartner C (Finset.mem_union_right _ hC)),hBcard C hC])
      _ = 3 * B.card := by simp [mul_comm]
  have hPA : P.card ≤ 4 * A.card := by
    calc
      P.card ≤ (A.biUnion (fun C => C.val.erase h)).card := Finset.card_le_card hPcore
      _ ≤ ∑ C ∈ A, (C.val.erase h).card := Finset.card_biUnion_le
      _ = ∑ C ∈ A, 4 := Finset.sum_congr rfl (fun C hC => by
        rw [Finset.card_erase_of_mem (hpartner C (Finset.mem_union_left _ hC)),hAcard C hC])
      _ = 4 * A.card := by simp [mul_comm]
  exact ⟨by change 5 * A.card + P.card + 4 ≤ _; omega,hPA⟩

/-- When at least one counted core is present, at least three actual
neighbors remain outside its counted type-B port set. This supplies
the zero-exceptional-mode boundary condition in Section 7.4. -/
theorem core_port_family_three_unused_neighbors
    (M : MinimalCounterexample V) (h : V) (P : Finset V) (hP : P.Nonempty)
    (core : P → Body M.graph) (Q : ∀ v : P, CorePort M (core v) h v.val) :
    3 ≤ (M.graph.neighborFinset h \ P).card := by
  have hb := core_port_family_neighborhood_budget M h P core Q
  have hPsub : P ⊆ M.graph.neighborFinset h := by
    intro v hv
    let R := Q ⟨v,hv⟩
    exact (M.graph.mem_neighborFinset h v).mpr
      ((core ⟨v,hv⟩).property.2.1 R.partner_mem_core R.port_mem_core R.port_ne_partner.symm)
  have hgpos : 0 < (Finset.univ.image core).card := by
    obtain ⟨v,hv⟩ := hP
    exact Finset.card_pos.mpr ⟨core ⟨v,hv⟩,
      Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩⟩
  rw [Finset.card_sdiff_of_subset hPsub,M.graph.card_neighborFinset_eq_degree]
  omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0032

section BundleSource0033
/- Source: Papers/RigidityHypervertexBoundary.lean -/




@[expose] public section

/-!
# The remaining neighborhood counts in Section 7.4

These are counts of actual vertex sets. Exterior pairs of ports give
the seven- and eight-neighbor bounds in the single-core cases. An
inactive vertex in a three-port core supplies a remaining neighbor in
the mixed case, because a solely observed scalar component contains no
vertex of any large body.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Membership of a counted port in a large body is exactly equality
of its unique core with that body. -/
theorem core_port_family_inter_card
    (M : MinimalCounterexample V) (h : V) (P : Finset V)
    (core : P → Body M.graph) (Q : ∀ v : P, CorePort M (core v) h v.val)
    (C : Body M.graph) (hC : 5 ≤ C.val.card) :
    (P ∩ C.val).card = (Finset.univ.filter fun v : P => core v = C).card := by
  let A := Finset.univ.filter fun v : P => core v = C
  have heq : A.image (fun v : P => v.val) = P ∩ C.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      have hcore : core w = C := (Finset.mem_filter.mp hw).2
      exact Finset.mem_inter.mpr ⟨w.property,hcore ▸ (Q w).port_mem_core⟩
    · intro hv
      obtain ⟨hvP,hvC⟩ := Finset.mem_inter.mp hv
      have hcore : core ⟨v,hvP⟩ = C := ((Q ⟨v,hvP⟩).core_unique C hC hvC).symm
      exact Finset.mem_image.mpr ⟨⟨v,hvP⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcore⟩,rfl⟩
  rw [← heq,Finset.card_image_of_injective A Subtype.val_injective]

/-- If one core accounts for the selected ports, its remaining ordinary
neighbors satisfy the precise `k+D ≥ 4+b` estimate. -/
theorem core_ports_residual_neighbor_bound
    (M : MinimalCounterexample V) (C : Body M.graph) (h : V)
    (P K : Finset V) (Q : ∀ v : P, CorePort M C h v.val) (hP : P.Nonempty)
    (hK : K ⊆ M.graph.neighborFinset h) (hKP : Disjoint K P) :
    4 + P.card ≤ K.card + (M.graph.neighborFinset h \ (K ∪ P)).card := by
  have hdegree := core_ports_neighbor_bound M C h P Q hP
  have hPsub : P ⊆ M.graph.neighborFinset h := by
    intro v hv
    let R := Q ⟨v,hv⟩
    exact (M.graph.mem_neighborFinset h v).mpr
      (C.property.2.1 R.partner_mem_core R.port_mem_core R.port_ne_partner.symm)
  have hsub : K ∪ P ⊆ M.graph.neighborFinset h := Finset.union_subset hK hPsub
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint hKP,M.graph.card_neighborFinset_eq_degree] at hcard
  omega

variable {M : MinimalCounterexample V} {p : Placement V 3}

/-- A solely observed component is disjoint from every actual large
body, not merely from the displayed observer seed. -/
theorem SoftScalarSystem.sole_component_disjoint_large_body
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (h : Hypervertex M.graph) (hc : L.observers c = {Sum.inl h})
    (C : Body M.graph) (hC : 5 ≤ C.val.card) : Disjoint (L.vertices c) C.val := by
  apply Finset.disjoint_left.mpr
  intro v hv hvC
  let sv : SoftPointPin M.graph := ⟨v,L.soft_of_mem_vertices c v hv⟩
  have hvc := L.mk_eq_of_mem_vertices c sv hv
  have hfour := L.sole_observer_all_tetrahedra c h hc sv hvc C hvC
  omega

/-- An actual exceptional-component star set is disjoint from all
counted type-B ports, even across different cores. -/
theorem SoftScalarSystem.component_disjoint_core_ports
    (L : SoftScalarSystem M p) (c : L.graph.ConnectedComponent)
    (h : V) (P : Finset V) (core : P → Body M.graph)
    (Q : ∀ v : P, CorePort M (core v) h v.val) : Disjoint (L.vertices c) P := by
  apply Finset.disjoint_left.mpr
  intro v hv hvP
  exact (Q ⟨v,hvP⟩).not_softPointPin (L.soft_of_mem_vertices c v hv)

/-- A three-port core has an inactive ordinary neighbor outside the
exceptional component and outside every counted port of every core. -/
theorem SoftScalarSystem.three_port_core_has_residual_neighbor
    (L : SoftScalarSystem M p)
    (c : L.graph.ConnectedComponent) (h : Hypervertex M.graph)
    (hc : L.observers c = {Sum.inl h})
    (P K : Finset V) (core : P → Body M.graph)
    (Q : ∀ v : P, CorePort M (core v) h.val v.val)
    (C : Body M.graph) (hC : C.val.card = 5) (hhC : h.val ∈ C.val)
    (hports : (Finset.univ.filter fun v : P => core v = C).card = 3)
    (hK : K ⊆ L.vertices c) :
    1 ≤ (M.graph.neighborFinset h.val \ (K ∪ P)).card := by
  have hinter : (P ∩ C.val).card = 3 := by
    rw [core_port_family_inter_card M h.val P core Q C (by omega),hports]
  have hCfour : (C.val.erase h.val).card = 4 := by
    rw [Finset.card_erase_of_mem hhC,hC]
  have hinside : ((C.val.erase h.val) ∩ P).card ≤ 3 := by
    have hsub : (C.val.erase h.val) ∩ P ⊆ P ∩ C.val := by
      intro v hv
      obtain ⟨hvC,hvP⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_inter.mpr ⟨hvP,(Finset.mem_erase.mp hvC).2⟩
    simpa only [hinter] using Finset.card_le_card hsub
  have hnonempty : ((C.val.erase h.val) \ P).Nonempty := by
    apply Finset.card_pos.mp
    have hcount := Finset.card_sdiff_add_card_inter (C.val.erase h.val) P
    omega
  obtain ⟨v,hv⟩ := hnonempty
  obtain ⟨hvC,hvP⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hvh,hvC⟩ := Finset.mem_erase.mp hvC
  have hvK : v ∉ K := by
    intro hvK
    exact Finset.disjoint_left.mp (L.sole_component_disjoint_large_body c h hc C (by omega))
      (hK hvK) hvC
  apply Finset.one_le_card.mpr
  refine ⟨v,Finset.mem_sdiff.mpr ⟨?_,?_⟩⟩
  · exact (M.graph.mem_neighborFinset h.val v).mpr (C.property.2.1 hhC hvC hvh.symm)
  · simpa only [Finset.mem_union,not_or] using And.intro hvK hvP

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0033

section BundleSource0034
/- Source: Papers/RigidityHypervertexFamilies.lean -/





@[expose] public section

/-!
# The literal families charged at a hypervertex

The exceptional family consists exactly of scalar components with this
sole observer. The charged core family consists exactly of no-soft K5
cores with this sole hypervertex and two, three, or four type-B ports.
The two specified neighbor sets are disjoint actual vertex sets.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

def exceptionalComponentsAt (L : SoftScalarSystem M p) (h : Hypervertex M.graph) :
    Finset L.graph.ConnectedComponent :=
  Finset.univ.filter fun c => L.observers c = {Sum.inl h}

def exceptionalCountAt (L : SoftScalarSystem M p) (h : Hypervertex M.graph) : ℕ :=
  (exceptionalComponentsAt L h).card

def exceptionalNeighborsAt (L : SoftScalarSystem M p) (h : Hypervertex M.graph) : Finset V :=
  M.graph.neighborFinset h.val ∩
    (exceptionalComponentsAt L h).biUnion L.vertices

def chargedCoresAt (M : MinimalCounterexample V) (h : V) : Finset (SelectedCore M) :=
  Finset.univ.filter fun C => bodyHyperVertices M C.val = {h} ∧
    bodySoftVertices M C.val = ∅ ∧ 2 ≤ (bodyTypeBVertices M C.val).card

def chargedPortsAt (M : MinimalCounterexample V) (h : V) : Finset V :=
  (chargedCoresAt M h).biUnion fun C => bodyTypeBVertices M C.val

@[simp] theorem mem_exceptionalComponentsAt
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph) (c : L.graph.ConnectedComponent) :
    c ∈ exceptionalComponentsAt L h ↔ L.observers c = {Sum.inl h} := by
  simp only [exceptionalComponentsAt,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_chargedCoresAt
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M) :
    C ∈ chargedCoresAt M h ↔ bodyHyperVertices M C.val = {h} ∧
      bodySoftVertices M C.val = ∅ ∧ 2 ≤ (bodyTypeBVertices M C.val).card := by
  simp only [chargedCoresAt,Finset.mem_filter,Finset.mem_univ,true_and]

theorem chargedCore_port_count_le_four
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M)
    (hC : C ∈ chargedCoresAt M h) : (bodyTypeBVertices M C.val).card ≤ 4 := by
  have hH := (mem_chargedCoresAt M h C).mp hC
  have hh : h ∈ C.val.val ∧ IsHypervertex M.graph h := by
    have hm : h ∈ bodyHyperVertices M C.val := by rw [hH.1]; simp
    exact Finset.mem_filter.mp hm
  have hsub : bodyTypeBVertices M C.val ⊆ C.val.val.erase h := by
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hv'.1⟩
    intro heq
    exact bodyTypeB_not_hyper M C.val v hv'.2 (heq.symm ▸ hh.2)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hh.1,C.property.1] at hcard
  exact hcard

theorem chargedCore_no_soft
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M)
    (hC : C ∈ chargedCoresAt M h) :
    ∀ v ∈ C.val.val, ¬ IsSoftPointPin M.graph v := by
  intro v hv hs
  have hm : v ∈ bodySoftVertices M C.val := Finset.mem_filter.mpr ⟨hv,hs⟩
  rw [((mem_chargedCoresAt M h C).mp hC).2.1] at hm
  exact Finset.notMem_empty _ hm

theorem chargedCore_sole_hyper
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M)
    (hC : C ∈ chargedCoresAt M h) :
    ∀ v ∈ C.val.val, IsHypervertex M.graph v → v = h := by
  intro v hv hh
  have hm : v ∈ bodyHyperVertices M C.val := Finset.mem_filter.mpr ⟨hv,hh⟩
  rwa [((mem_chargedCoresAt M h C).mp hC).1,Finset.mem_singleton] at hm

theorem chargedCore_partner_mem
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M)
    (hC : C ∈ chargedCoresAt M h) : h ∈ C.val.val := by
  have hm : h ∈ bodyHyperVertices M C.val := by
    rw [((mem_chargedCoresAt M h C).mp hC).1]
    simp
  exact (Finset.mem_filter.mp hm).1

theorem chargedCore_counts
    (M : MinimalCounterexample V) (h : V) :
    (chargedCoresAt M h).card = chargedCoreCountAt M h 2 +
      chargedCoreCountAt M h 3 + chargedCoreCountAt M h 4 ∧
    (∑ C ∈ chargedCoresAt M h, (bodyTypeBVertices M C.val).card) =
      2 * chargedCoreCountAt M h 2 + 3 * chargedCoreCountAt M h 3 +
      4 * chargedCoreCountAt M h 4 := by
  have hcard (C : SelectedCore M)
      (hH : bodyHyperVertices M C.val = {h}) :
      (bodyTypeBVertices M C.val).card ≤ 4 := by
    by_cases htwo : 2 ≤ (bodyTypeBVertices M C.val).card
    · by_cases hsoft : bodySoftVertices M C.val = ∅
      · exact chargedCore_port_count_le_four M h C
          ((mem_chargedCoresAt M h C).mpr ⟨hH,hsoft,htwo⟩)
      · have hpartition := body_vertex_counts_partition M C.val
        rw [hH,Finset.card_singleton,C.property.1] at hpartition
        omega
    · omega
  constructor
  · simp only [chargedCoresAt,chargedCoreCountAt,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hH : bodyHyperVertices M C.val = {h}
    · have hc := hcard C hH
      by_cases hs : bodySoftVertices M C.val = ∅
      · by_cases h2 : (bodyTypeBVertices M C.val).card = 2
        · simp [hH,hs,h2]
        · by_cases h3 : (bodyTypeBVertices M C.val).card = 3
          · simp [hH,hs,h3]
          · by_cases h4 : (bodyTypeBVertices M C.val).card = 4
            · simp [hH,hs,h4]
            · have hl : ¬ 2 ≤ (bodyTypeBVertices M C.val).card := by omega
              simp [hH,hs,h2,h3,h4,hl]
      · simp [hH,hs]
    · simp [hH]
  · simp only [chargedCoresAt,chargedCoreCountAt,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
      ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hH : bodyHyperVertices M C.val = {h}
    · have hc := hcard C hH
      by_cases hs : bodySoftVertices M C.val = ∅
      · by_cases h2 : (bodyTypeBVertices M C.val).card = 2
        · simp [hH,hs,h2]
        · by_cases h3 : (bodyTypeBVertices M C.val).card = 3
          · simp [hH,hs,h3]
          · by_cases h4 : (bodyTypeBVertices M C.val).card = 4
            · simp [hH,hs,h4]
            · have hl : ¬ 2 ≤ (bodyTypeBVertices M C.val).card := by omega
              simp [hH,hs,h2,h3,h4,hl]
      · simp [hH,hs]
    · simp [hH]

theorem charged_ports_pairwise_disjoint
    (M : MinimalCounterexample V) (h : V)
    (C D : SelectedCore M) (hC : C ∈ chargedCoresAt M h)
    (hD : D ∈ chargedCoresAt M h) (hCD : C ≠ D) :
    Disjoint (bodyTypeBVertices M C.val) (bodyTypeBVertices M D.val) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  obtain ⟨P⟩ := bodyTypeB_port_at_sole_hypervertex M C.val h
    ((mem_chargedCoresAt M h C).mp hC).1 v hvC
  have heq : D.val = C.val := P.core_unique D.val (by rw [D.property.1])
    (Finset.mem_filter.mp hvD).1
  exact hCD (Subtype.ext heq.symm)

theorem chargedPorts_card
    (M : MinimalCounterexample V) (h : V) :
    (chargedPortsAt M h).card =
      2 * chargedCoreCountAt M h 2 + 3 * chargedCoreCountAt M h 3 +
      4 * chargedCoreCountAt M h 4 := by
  rw [chargedPortsAt,Finset.card_biUnion]
  · exact (chargedCore_counts M h).2
  · exact fun C hC D hD hCD => charged_ports_pairwise_disjoint M h C D hC hD hCD

def chargedPortCore (M : MinimalCounterexample V) (h : V)
    (v : chargedPortsAt M h) : SelectedCore M :=
  Classical.choose (Finset.mem_biUnion.mp v.property)

theorem chargedPortCore_mem (M : MinimalCounterexample V) (h : V)
    (v : chargedPortsAt M h) : chargedPortCore M h v ∈ chargedCoresAt M h :=
  (Classical.choose_spec (Finset.mem_biUnion.mp v.property)).1

theorem chargedPortCore_port_mem (M : MinimalCounterexample V) (h : V)
    (v : chargedPortsAt M h) :
    v.val ∈ bodyTypeBVertices M (chargedPortCore M h v).val :=
  (Classical.choose_spec (Finset.mem_biUnion.mp v.property)).2

def chargedPortRecord (M : MinimalCounterexample V) (h : V)
    (v : chargedPortsAt M h) : CorePort M (chargedPortCore M h v).val h v.val :=
  Classical.choice (bodyTypeB_port_at_sole_hypervertex M _ h
    ((mem_chargedCoresAt M h _).mp (chargedPortCore_mem M h v)).1 v.val
    (chargedPortCore_port_mem M h v))

theorem chargedPorts_subset_neighbors
    (M : MinimalCounterexample V) (h : V) : chargedPortsAt M h ⊆ M.graph.neighborFinset h := by
  intro v hv
  let P := chargedPortRecord M h ⟨v,hv⟩
  exact (M.graph.mem_neighborFinset h v).mpr
    (P.pin.left.property.2.1 (by rw [P.core_eq]; exact P.partner_mem_core)
      P.pin.left_mem P.port_ne_partner.symm)

theorem exceptionalNeighbors_subset_neighbors
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph) :
    exceptionalNeighborsAt L h ⊆ M.graph.neighborFinset h.val := Finset.inter_subset_left

theorem exceptional_charged_neighbors_disjoint
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph) :
    Disjoint (exceptionalNeighborsAt L h) (chargedPortsAt M h.val) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvP
  obtain ⟨c,hc,hvc⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).2
  exact (chargedPortRecord M h.val ⟨v,hvP⟩).not_softPointPin (L.soft_of_mem_vertices c v hvc)

theorem exceptionalNeighbors_card_ge
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    5 * exceptionalCountAt L h ≤ (exceptionalNeighborsAt L h).card := by
  let N := M.graph.neighborFinset h.val
  let S := exceptionalComponentsAt L h
  have heq : exceptionalNeighborsAt L h = S.biUnion (fun c => N ∩ L.vertices c) := by
    ext v
    simp only [exceptionalNeighborsAt,Finset.mem_inter,Finset.mem_biUnion]
    constructor
    · rintro ⟨hv,c,hc,hvc⟩
      exact ⟨c,hc,hv,hvc⟩
    · rintro ⟨c,hc,hv,hvc⟩
      exact ⟨hv,c,hc,hvc⟩
  have hdisj : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      Disjoint (N ∩ L.vertices c) (N ∩ L.vertices d) := by
    intro c hc d hd hcd
    exact Finset.disjoint_left.mpr fun v hv hw =>
      Finset.disjoint_left.mp (L.vertices_disjoint c d hcd)
        (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hw).2
  have hfive (c : L.graph.ConnectedComponent) (hc : c ∈ S) :
      5 ≤ (N ∩ L.vertices c).card := by
    have hsole := (mem_exceptionalComponentsAt L h c).mp hc
    obtain ⟨s,hs⟩ := exists_normalized_linear_functional (L.scalar c.out) (L.scalar_ne_zero c.out)
    have hsupport := L.exceptionalCut_star_support_ge_five hgen hp c h hsole
      c.out c.out_eq s (by rw [hs]; exact one_ne_zero)
    apply hsupport.trans
    apply Finset.card_le_card
    intro v hv
    have hn := (mem_support _ v).mp hv
    refine Finset.mem_inter.mpr ⟨?_,L.exceptionalCut_neighbor_mem hgen hp c h hsole s v hn⟩
    apply (M.graph.mem_neighborFinset h.val v).mpr
    by_contra ha
    exact hn (starCoordinates_of_not_adj _ _ _ _ (fun hab => ha hab.1))
  rw [heq,Finset.card_biUnion hdisj]
  calc
    5 * exceptionalCountAt L h = ∑ c ∈ S, 5 := by simp [S,exceptionalCountAt,mul_comm]
    _ ≤ ∑ c ∈ S, (N ∩ L.vertices c).card := Finset.sum_le_sum hfive

theorem exceptionalNeighbors_eq_empty_of_count_zero
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph)
    (ha : exceptionalCountAt L h = 0) : exceptionalNeighborsAt L h = ∅ := by
  have heq : exceptionalComponentsAt L h = ∅ := Finset.card_eq_zero.mp ha
  simp only [exceptionalNeighborsAt,heq,Finset.biUnion_empty,Finset.inter_empty]

theorem exceptionalNeighbors_subset_of_count_one
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph)
    (ha : exceptionalCountAt L h = 1) :
    ∃ c : L.graph.ConnectedComponent, L.observers c = {Sum.inl h} ∧
      exceptionalNeighborsAt L h ⊆ L.vertices c := by
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp ha
  have hm : c ∈ exceptionalComponentsAt L h := by rw [hc]; simp
  refine ⟨c,(mem_exceptionalComponentsAt L h c).mp hm,?_⟩
  simp only [exceptionalNeighborsAt,hc,Finset.singleton_biUnion]
  exact Finset.inter_subset_right

theorem chargedPorts_inter_core
    (M : MinimalCounterexample V) (h : V) (C : SelectedCore M)
    (hC : C ∈ chargedCoresAt M h) :
    chargedPortsAt M h ∩ C.val.val = bodyTypeBVertices M C.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvP,hvC⟩ := Finset.mem_inter.mp hv
    have heq : C.val = (chargedPortCore M h ⟨v,hvP⟩).val :=
      (chargedPortRecord M h ⟨v,hvP⟩).core_unique C.val (by rw [C.property.1]) hvC
    rw [heq]
    exact chargedPortCore_port_mem M h ⟨v,hvP⟩
  · intro hv
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨C,hC,hv⟩,(Finset.mem_filter.mp hv).1⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0034

section BundleSource0035
/- Source: Papers/RigidityRegularBodyPin.lean -/



@[expose] public section

/-!
# Regular pins for an actual four-dimensional body image

The singular-space classification supplies one surjective evaluation;
the determinant rank-locus argument makes such pins dense.  This is
independent of any chosen Cramer chart.
-/

noncomputable section
namespace Papers.Rigidity

theorem dense_surjective_evaluation_of_finrank_four (W : Submodule ℝ Twist)
    (hW : Module.finrank ℝ W = 4) :
    Dense {p : Vec3 | Function.Surjective (restrictEvaluation W p)} := by
  have hlarge : ∃ p : Vec3, 3 ≤ Module.finrank ℝ (restrictEvaluation W p).range := by
    by_contra hn
    have hsingular : SingularPinSpace W := by
      intro p
      by_contra hp
      exact hn ⟨p, by omega⟩
    have hthree := finrank_eq_three_of_singularPinSpace W hsingular (by omega)
    omega
  obtain ⟨p, hp⟩ := hlarge
  have hdense := AffineRank.dense_setOf_le_rankAt (restrictEvaluation W 0)
    (pinEvaluationLinearPart W) 3 ⟨p, by
      unfold AffineRank.rankAt
      rw [← restrictEvaluation_eq_affineFamily W p]
      exact hp⟩
  apply hdense.mono
  intro q hq
  have hlow : 3 ≤ Module.finrank ℝ (restrictEvaluation W q).range := by
    change 3 ≤ Module.finrank ℝ
      (AffineRank.family (restrictEvaluation W 0) (pinEvaluationLinearPart W) q).range at hq
    rwa [← restrictEvaluation_eq_affineFamily W q] at hq
  have hupper := Submodule.finrank_le (restrictEvaluation W q).range
  have hdim : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  omega

theorem dense_surjective_body_evaluation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ] Twist) (hA : Module.finrank ℝ A.range = 4) :
    Dense {p : Vec3 | Function.Surjective ((evaluateTwist p).comp A)} := by
  apply (dense_surjective_evaluation_of_finrank_four A.range hA).mono
  intro p hp y
  obtain ⟨X, hX⟩ := hp y
  obtain ⟨u, hu⟩ := X.property
  refine ⟨u, ?_⟩
  change evaluateTwist p (A u) = y
  rw [hu]
  exact hX

end Papers.Rigidity

end
end
end BundleSource0035

section BundleSource0036
/- Source: Papers/RigidityHypervertexFourRank.lean -/




@[expose] public section

/-!
# No rank-four body projection at a deletion-loss-six hypervertex

Choose a generic new pin at which the immersed first body's evaluation
is surjective.  A distinct nonreference maximal body has a nonzero
surviving relative twist there, by actual ambient-closure separation.
The cofactor and Maurer--Cartan merger then identifies those two owners,
a contradiction.  This works at every generic placement and therefore
also supplies the upper rank bound throughout nearby actual fibers.

These rank bounds support the hypervertex argument in Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_no_injective_bodyForm
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    ¬ Function.Injective
      (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0) := by
  intro hinj
  let T := ownedIncidentTetrahedra M.graph v M.covered
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 4 := by
    have h := M.grounded_incident_finrank v T p hgen hp base
    omega
  let A := ((T.incidentBodyRepresentation p hp base C b).form 0).toLinearMap
  have hA : Module.finrank ℝ A.range = 4 := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact hE
  obtain ⟨c, hcbase, hcb⟩ := hh.exists_other_owned base b
  obtain ⟨O, hO, hpO, hwindow⟩ := exists_open_generic_general_pin_window p v hgen hp
  obtain ⟨q, hqsurj, hqO⟩ :=
    (dense_surjective_body_evaluation A hA).exists_mem_open hO ⟨p v, hpO⟩
  let p' := replacePlacement p v q
  have hqgen := (hwindow q hqO).1
  have hqgeom := (hwindow q hqO).2
  have ht := GeneralPosition.InGeneralPosition.incident_transverse p' hqgeom T
  obtain ⟨u, hu⟩ := Papers.Rigidity.VertexPin.MinimalCounterexample.owned_bodies_not_merged M v p' hqgen hqgeom c base hcbase
  have hsecond : (T.incidentBodyRepresentation p hp base C c).form 0
      (T.groundedFullMotionReplace p hp base q u) ≠ 0 := by
    rw [T.incidentBodyForm_groundedFullMotionReplace]
    exact sub_ne_zero.mpr hu
  have hmotion : ∃ e : T.IncidentGroundedMotions p base,
      evaluateTwist q ((T.incidentBodyRepresentation p hp base C b).form 0 e) = 0 ∧
        (T.incidentBodyRepresentation p hp base C c).form 0 e ≠ 0 :=
    ⟨T.groundedFullMotionReplace p hp base q u,
      T.incidentBodyForm_groundedFullMotionReplace_stationary p hp base C q ht u b,
      hsecond⟩
  have hmerge := T.incidentBody_regular_pin_merges p hp base C hgen (by omega) hE
    b c q hinj hqsurj hmotion
  exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_pin_merger_contradiction M v p hp base C b c (Ne.symm hcb) q hqgen hqgeom
    (fun e he _ => (hmerge e he).symm)

theorem MinimalCounterexample.hypervertex_bodyForm_rank_le_three
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    Module.finrank ℝ
      (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0).toLinearMap.range ≤ 3 := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 4 := by
    have h := M.grounded_incident_finrank v T p hgen hp base
    omega
  by_contra hlarge
  apply M.hypervertex_no_injective_bodyForm v hh hdrop p hgen hp base b C
  apply linearMap_injective_of_finrank_range_ge
  change Module.finrank ℝ (T.IncidentGroundedMotions p base) ≤ _
  omega

/-- The upper bound concerns the original deleted-graph relative
operator at every generic placement, rather than an arbitrary chosen
constant-rank stratum. -/
theorem MinimalCounterexample.hypervertex_relative_rank_le_three
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v) :
    Module.finrank ℝ
      ((ownedIncidentTetrahedra M.graph v M.covered).relativeTwists p
        (GeneralPosition.InGeneralPosition.incident_noncollinear p hp
          (ownedIncidentTetrahedra M.graph v M.covered)) base b).range ≤ 3 := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  let C := groundedLengthFiberChart (deletedGraph M.graph v) (T.triangleEmbedding base)
    (T.clique base) (deletedPlacement p v)
    (generic_deletedPlacement p hgen v (deletedGraph M.graph v)) (hn base)
  have h := M.hypervertex_bodyForm_rank_le_three v hh hdrop p hgen hp base b C
  rwa [T.incidentBodyForm_range_at_zero] at h

end Papers.Rigidity

end
end
end BundleSource0036

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0036/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0036.json"

section BundleSource0037
/- Source: Papers/RigidityFixedCenterSubmersion.lean -/





@[expose] public section

/-!
# Fixed centers with redundant configuration parameters

In the rank-three projection case the whole configuration manifold may
have dimension four. The angular projection is a submersion, not an
isomorphism from that whole tangent space. The mixed-derivative argument
still forces the center derivative to vanish: first restrict to a linear
section of the angular map, then use the same identity in every remaining
tangent direction. No quotient manifold or image-manifold assumption is
needed for this differential conclusion.

This module supplies an alternative implementation of the paper's use
of Lemma 4.2 in Proposition 4.1.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

theorem linearMap_eq_zero_of_surjective_cross_integrability
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A D : E →ₗ[ℝ] Vec3) (hA : Function.Surjective A)
    (h : ∀ v w : E, A v ⨯₃ D w = A w ⨯₃ D v) : D = 0 := by
  obtain ⟨s, hs⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  have hAs (u : Vec3) : A (s u) = u :=
    congrArg (fun L : Vec3 →ₗ[ℝ] Vec3 => L u) hs
  have hDs : D.comp s = 0 := by
    apply linearMap_eq_zero_of_cross_integrability
    intro u v
    simpa only [LinearMap.comp_apply, hAs] using h (s u) (s v)
  have hDs_apply (u : Vec3) : D (s u) = 0 :=
    congrArg (fun L : Vec3 →ₗ[ℝ] Vec3 => L u) hDs
  apply LinearMap.ext
  intro v
  have hcross (u : Vec3) : u ⨯₃ D v = 0 := by
    have he := h (s u) v
    simpa only [hAs, hDs_apply, map_zero] using he
  have h0 := congrFun (hcross ![1, 0, 0]) (2 : Fin 3)
  have h1 := congrFun (hcross ![1, 0, 0]) (1 : Fin 3)
  have h2 := congrFun (hcross ![0, 1, 0]) (2 : Fin 3)
  simp [cross_apply] at h0 h1 h2
  change D v = 0
  funext i
  fin_cases i
  · exact h2
  · exact h0
  · exact h1

namespace Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The body-frame center derivative vanishes on the entire original
configuration tangent space, including the kernel of the angular map. -/
theorem fixed_body_center_derivative_eq_zero_of_angular_surjective
    (R : E → (Vec3 →L[ℝ] Vec3)) (t b : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (hb : DifferentiableAt ℝ b x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u : E,
      fderiv ℝ t y u = -(fderiv ℝ R y u) (b y))
    (A : Vec3 →ₗ[ℝ] Vec3) (ω : E →ₗ[ℝ] Vec3)
    (hω : Function.Surjective ω)
    (hangular : ∀ v q, A ((fderiv ℝ R x v) q) = ω v ⨯₃ q) :
    fderiv ℝ b x = 0 := by
  have hD : (fderiv ℝ b x).toLinearMap = 0 := by
    apply linearMap_eq_zero_of_surjective_cross_integrability ω _ hω
    intro v w
    have he := congrArg A (fixed_center_mixed_relation R t b x hR ht hb hfix v w)
    simpa only [hangular, ContinuousLinearMap.coe_coe] using he
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : E →ₗ[ℝ] Vec3 => L v) hD

/-- The spatial center has zero derivative on the same full tangent
space; the assertion does not silently replace the four-dimensional
manifold by a supplied three-dimensional image chart. -/
theorem fixed_spatial_center_derivative_eq_zero_of_angular_surjective
    (R : E → (Vec3 →L[ℝ] Vec3)) (t b : E → Vec3) (x : E)
    (hR : ContDiffAt ℝ 2 R x) (ht : ContDiffAt ℝ 2 t x)
    (hb : DifferentiableAt ℝ b x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u : E,
      fderiv ℝ t y u = -(fderiv ℝ R y u) (b y))
    (A : Vec3 →ₗ[ℝ] Vec3) (ω : E →ₗ[ℝ] Vec3)
    (hω : Function.Surjective ω)
    (hangular : ∀ v q, A ((fderiv ℝ R x v) q) = ω v ⨯₃ q) :
    fderiv ℝ (fun y => R y (b y) + t y) x = 0 := by
  have hRdiff := hR.differentiableAt (by norm_num)
  have htdiff := ht.differentiableAt (by norm_num)
  have hdb := fixed_body_center_derivative_eq_zero_of_angular_surjective
    R t b x hR ht hb hfix A ω hω hangular
  have hfixx := hfix.self_of_nhds
  rw [fderiv_fun_add (hRdiff.clm_apply hb) htdiff,
    fderiv_clm_apply hRdiff hb, hdb]
  apply ContinuousLinearMap.ext
  intro v
  simp [hfixx]

end Calculus

end

end Papers.Rigidity

end
end BundleSource0037

section BundleSource0038
/- Source: Papers/RigiditySmoothFiniteCenter.lean -/






@[expose] public section

/-!
# A finite center obtained from the actual body form

Surjectivity of the angular projection is an explicit hypothesis in this
local lemma.  The statement does not cover an infinite projective center.
On this open chart the center is recovered by inverting one angular frame
and reading three entries of its translational part.  Consequently its
differentiability is proved, rather than assumed as part of a chosen
three-dimensional image manifold.

This module treats finite centers in the two rank-three projection case
of Proposition 4.1. A projective change of the entire placement, or
a separate infinite-center argument, remains necessary in that branch.
-/

noncomputable section
namespace Papers.Rigidity

open Matrix
open scoped Matrix

theorem exists_finiteCenter_of_singular_angular_surjective
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] Twist) (hA : SingularPinSpace A.range)
    (hω : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp A)) :
    ∃ a : Vec3, A.range = finiteCenterSpace a := by
  have hdim : 3 ≤ Module.finrank ℝ A.range := by
    have hh := Submodule.finrank_map_le (LinearMap.fst ℝ Vec3 Vec3) A.range
    rw [← LinearMap.range_comp, LinearMap.range_eq_top.mpr hω] at hh
    simpa [Vec3] using hh
  rcases singularPinSpace_classification A.range hA hdim with
    ⟨a, ha, _⟩ | ⟨d, hd, hAd⟩
  · exact ⟨a, ha⟩
  · have hcross (ω : Vec3) : ω ⨯₃ d = 0 := by
      obtain ⟨u, hu⟩ := hω ω
      have hm : A u ∈ infiniteCenterSpace d := by
        rw [← hAd]
        exact ⟨u, rfl⟩
      change (A u).1 = ω at hu
      rw [← hu]
      exact hm.1
    have h0 := congrFun (hcross ![1, 0, 0]) (2 : Fin 3)
    have h1 := congrFun (hcross ![1, 0, 0]) (1 : Fin 3)
    have h2 := congrFun (hcross ![0, 1, 0]) (2 : Fin 3)
    simp [cross_apply] at h0 h1 h2
    exact False.elim (hd (by
      funext i
      fin_cases i
      · exact h2
      · exact h0
      · exact h1))

namespace Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def angularForm (θ : E →L[ℝ] Twist) : E →L[ℝ] Vec3 :=
  (ContinuousLinearMap.fst ℝ Vec3 Vec3).comp θ

def translationalForm (θ : E →L[ℝ] Twist) : E →L[ℝ] Vec3 :=
  (ContinuousLinearMap.snd ℝ Vec3 Vec3).comp θ

@[simp] theorem angularForm_apply (θ : E →L[ℝ] Twist) (u : E) :
    angularForm θ u = (θ u).1 := rfl

@[simp] theorem translationalForm_apply (θ : E →L[ℝ] Twist) (u : E) :
    translationalForm θ u = (θ u).2 := rfl

/-- The actual singular body image supplies its differentiable finite
center on an angular frame chart.  No center regularity or image-chart
hypothesis is included in the premises. -/
theorem exists_finite_center_chart
    (θ : E → (E →L[ℝ] Twist)) (x : E)
    (hθ : DifferentiableAt ℝ θ x)
    (hsingular : ∀ᶠ y in 𝓝 x, SingularPinSpace (θ y).toLinearMap.range)
    (hω : Function.Surjective (angularForm (θ x))) :
    ∃ a : E → Vec3, DifferentiableAt ℝ a x ∧
      ∀ᶠ y in 𝓝 x, (DifferentiableAt ℝ θ y → DifferentiableAt ℝ a y) ∧
        (θ y).toLinearMap.range = finiteCenterSpace (a y) := by
  obtain ⟨s₀, hs₀⟩ := (angularForm (θ x)).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hω)
  let s : Vec3 →L[ℝ] E := s₀.toContinuousLinearMap
  let A : E → (Vec3 →L[ℝ] Vec3) := fun y => (angularForm (θ y)).comp s
  let B : E → (Vec3 →L[ℝ] Vec3) := fun y =>
    ((translationalForm (θ y)).comp s).comp (Ring.inverse (A y))
  have hAx : A x = 1 := by
    apply ContinuousLinearMap.ext
    intro ω
    exact congrArg (fun L : Vec3 →ₗ[ℝ] Vec3 => L ω) hs₀
  have hA : DifferentiableAt ℝ A x :=
    ((differentiableAt_const (ContinuousLinearMap.fst ℝ Vec3 Vec3)).clm_comp hθ).clm_comp (differentiableAt_const s)
  have hAxUnit : IsUnit (A x) := by rw [hAx]; exact isUnit_one
  have hAunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.eventually (Units.isOpen.mem_nhds hAxUnit)
  let a : E → Vec3 := fun y =>
    ![(B y ![0, 1, 0]) 2, -(B y ![1, 0, 0]) 2, (B y ![1, 0, 0]) 1]
  have ha_of (y : E) (hθy : DifferentiableAt ℝ θ y) (hAy : IsUnit (A y)) :
      DifferentiableAt ℝ a y := by
    have hA' : DifferentiableAt ℝ A y :=
      ((differentiableAt_const (ContinuousLinearMap.fst ℝ Vec3 Vec3)).clm_comp hθy).clm_comp (differentiableAt_const s)
    have hB : DifferentiableAt ℝ B y :=
      (((differentiableAt_const (ContinuousLinearMap.snd ℝ Vec3 Vec3)).clm_comp hθy).clm_comp (differentiableAt_const s)).clm_comp
        (hA'.inverse hAy)
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact differentiableAt_pi.mp (hB.clm_apply (differentiableAt_const (![0, 1, 0] : Vec3))) 2
    · exact (differentiableAt_pi.mp (hB.clm_apply (differentiableAt_const (![1, 0, 0] : Vec3))) 2).neg
    · exact differentiableAt_pi.mp (hB.clm_apply (differentiableAt_const (![1, 0, 0] : Vec3))) 1
  refine ⟨a, ha_of x hθ hAxUnit, ?_⟩
  filter_upwards [hAunit, hsingular] with y hAy hsy
  refine ⟨fun hθy => ha_of y hθy hAy, ?_⟩
  have hangular (ω : Vec3) : angularForm (θ y) (s (Ring.inverse (A y) ω)) = ω := by
    have h := congrArg (fun L : Vec3 →L[ℝ] Vec3 => L ω)
      (Ring.mul_inverse_cancel (A y) hAy)
    exact h
  have hωy : Function.Surjective (angularForm (θ y)) :=
    fun ω => ⟨s (Ring.inverse (A y) ω), hangular ω⟩
  obtain ⟨c, hc⟩ := exists_finiteCenter_of_singular_angular_surjective
    (θ y).toLinearMap hsy hωy
  have htranslation (ω : Vec3) : B y ω = -(ω ⨯₃ c) := by
    have hm : θ y (s (Ring.inverse (A y) ω)) ∈ finiteCenterSpace c := by
      rw [← hc]
      exact ⟨s (Ring.inverse (A y) ω), rfl⟩
    change (θ y (s (Ring.inverse (A y) ω))).2 +
      (θ y (s (Ring.inverse (A y) ω))).1 ⨯₃ c = 0 at hm
    change B y ω + angularForm (θ y) (s (Ring.inverse (A y) ω)) ⨯₃ c = 0 at hm
    rw [hangular] at hm
    exact eq_neg_of_add_eq_zero_left hm
  have hay : a y = c := by
    ext i
    fin_cases i <;> simp [a, htranslation, cross_apply]
  simpa only [hay] using hc

/-- A pointwise differentiable version of the explicit finite-center
chart. -/
theorem exists_differentiable_finite_center
    (θ : E → (E →L[ℝ] Twist)) (x : E)
    (hθ : DifferentiableAt ℝ θ x)
    (hsingular : ∀ᶠ y in 𝓝 x, SingularPinSpace (θ y).toLinearMap.range)
    (hω : Function.Surjective (angularForm (θ x))) :
    ∃ a : E → Vec3, DifferentiableAt ℝ a x ∧
      ∀ᶠ y in 𝓝 x, (θ y).toLinearMap.range = finiteCenterSpace (a y) := by
  obtain ⟨a, ha, hnear⟩ := exists_finite_center_chart θ x hθ hsingular hω
  exact ⟨a, ha, hnear.mono fun _ h => h.2⟩

/-- When the actual body form is differentiable throughout a
neighborhood, the same single center function is differentiable at every
point of a smaller neighborhood.  This supplies the regularity needed
to apply the moving-center integrability argument at nearby points. -/
theorem exists_differentiable_finite_center_locally
    (θ : E → (E →L[ℝ] Twist)) (x : E)
    (hθ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ θ y)
    (hsingular : ∀ᶠ y in 𝓝 x, SingularPinSpace (θ y).toLinearMap.range)
    (hω : Function.Surjective (angularForm (θ x))) :
    ∃ a : E → Vec3, ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ a y ∧
      (θ y).toLinearMap.range = finiteCenterSpace (a y) := by
  obtain ⟨a, _, hnear⟩ := exists_finite_center_chart θ x hθ.self_of_nhds hsingular hω
  refine ⟨a, ?_⟩
  filter_upwards [hnear, hθ] with y hy hθy
  exact ⟨hy.1 hθy, hy.2⟩

end Calculus
end Papers.Rigidity

end
end
end BundleSource0038

section BundleSource0039
/- Source: Papers/RigidityFixedCenters.lean -/



@[expose] public section

/-!
# The first-order obstruction for two distinct fixed rotation centers

This verifies the algebraic obstruction that can replace the flow calculation
in Lemma 4.5. The differential step deriving the displayed identity from
Maurer–Cartan remains separate; it is not hidden in a definition of rigidity.
-/

namespace Papers.Rigidity

open Matrix
open scoped Matrix

theorem eq_zero_of_mem_span_and_perpendicular (d v : Vec3) (hd : d ≠ 0)
    (hspan : v ∈ Submodule.span ℝ {d}) (hperp : v ⬝ᵥ d = 0) : v = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  have hdd : d ⬝ᵥ d ≠ 0 := fun h => hd (dotProduct_self_eq_zero.mp h)
  have hp : a * (d ⬝ᵥ d) = 0 := by
    rw [← ha] at hperp
    simpa [smul_dotProduct] using hperp
  have ha0 : a = 0 := (mul_eq_zero.mp hp).resolve_right hdd
  simpa [ha0] using ha.symm

/-- A nonzero rotation on its perpendicular plane cannot be a scalar map. -/
theorem no_scaled_cross_identity_on_normalPlane (d : Vec3) (hd : d ≠ 0)
    (c g : ℝ) (hc : c ≠ 0)
    (h : ∀ v : Vec3, v ⬝ᵥ d = 0 → c • (d ⨯₃ v) + g • v = 0) : False := by
  have hplane : normalPlane d ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    rw [finrank_normalPlane d hd]
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hplane
  have hvd : v ⬝ᵥ d = 0 := by
    have h : d ⬝ᵥ v = 0 := hv
    simpa only [dotProduct_comm] using h
  have he := h v hvd
  have hdot := congrArg (fun w : Vec3 => v ⬝ᵥ w) he
  have hvv : v ⬝ᵥ v ≠ 0 := fun h => hv0 (dotProduct_self_eq_zero.mp h)
  have hg : g = 0 := by
    have hm : g * (v ⬝ᵥ v) = 0 := by
      simpa [dotProduct_add, dotProduct_smul] using hdot
    exact (mul_eq_zero.mp hm).resolve_right hvv
  have hcross : d ⨯₃ v = 0 := by
    have hm : c • (d ⨯₃ v) = 0 := by simpa [hg] using he
    exact (smul_eq_zero.mp hm).resolve_left hc
  have hspan : v ∈ Submodule.span ℝ {d} := by
    rw [← ker_crossProduct_eq_span d hd]
    exact hcross
  exact hv0 (eq_zero_of_mem_span_and_perpendicular d v hd hspan hvd)

/-- The four-dimensional angular relation occurring with two distinct centers. -/
def coupledAngularSpace (d : Vec3) (c : ℝ) : Submodule ℝ (Vec3 × Vec3) :=
  (Submodule.span ℝ {d}).comap
    (LinearMap.fst ℝ Vec3 Vec3 + c • LinearMap.snd ℝ Vec3 Vec3)

/-- Differentiating the fixed-center relation and imposing the two genuine
angular Maurer–Cartan equations gives an impossible identity. The conclusion
holds for every derivative functional `α`, so no constancy of `c` is assumed. -/
theorem no_fixed_center_maurer_cartan_identity (d : Vec3) (hd : d ≠ 0)
    (c : ℝ) (hc : c ≠ 0) (α : coupledAngularSpace d c →ₗ[ℝ] ℝ)
    (hMC : ∀ X Y : coupledAngularSpace d c,
      -(X.val.1 ⨯₃ Y.val.1) - c • (X.val.2 ⨯₃ Y.val.2) +
          α X • Y.val.2 - α Y • X.val.2 ∈ Submodule.span ℝ {d}) : False := by
  let X : coupledAngularSpace d c := ⟨(d, 0), by
    change d + c • (0 : Vec3) ∈ Submodule.span ℝ {d}
    simpa using (Submodule.subset_span (Set.mem_singleton d) :
      d ∈ Submodule.span ℝ {d})⟩
  apply no_scaled_cross_identity_on_normalPlane d hd c (α X) hc
  intro v hv
  let Y : coupledAngularSpace d c := ⟨(-(c • v), v), by
    change -(c • v) + c • v ∈ Submodule.span ℝ {d}
    simp⟩
  have hspan : c • (d ⨯₃ v) + α X • v ∈ Submodule.span ℝ {d} := by
    have h := hMC X Y
    simpa [X, Y, map_neg, map_smul] using h
  have hperp : (c • (d ⨯₃ v) + α X • v) ⬝ᵥ d = 0 := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hv]
    simp [dotProduct_comm]
  exact eq_zero_of_mem_span_and_perpendicular d _ hd hspan hperp

end Papers.Rigidity

end
end BundleSource0039

section BundleSource0040
/- Source: Papers/RigidityFixedCenterActual.lean -/




@[expose] public section

/-!
# The actual differential obstruction for two fixed centers

The coupled angular constraint is differentiated as an equality of
ordinary functions. Maurer--Cartan is derived from the two actual body
maps. This supplies the differential step in the fixed-center obstruction
without an assumption about tangency-preserving flows.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix
open scoped Topology Matrix

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem derivative_mem_kernel_of_eventually
    (L : F →L[ℝ] G) (f : E → F) (x v : E)
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ y in 𝓝 x, L (f y) = 0) : L (fderiv ℝ f x v) = 0 := by
  have hd : fderiv ℝ (fun y => L (f y)) x = 0 := by
    exact (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h).trans (fderiv_const_apply (𝕜 := ℝ) (x := x) (0 : G))
  rw [fderiv_fun_comp x L.differentiableAt hf, L.fderiv] at hd
  exact congrArg (fun D : E →L[ℝ] G => D v) hd

theorem derivative_mem_fixed_line (d : Vec3) (hd : d ≠ 0)
    (f : E → Vec3) (x v : E) (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ y in 𝓝 x, f y ∈ Submodule.span ℝ {d}) :
    fderiv ℝ f x v ∈ Submodule.span ℝ {d} := by
  let L : Vec3 →L[ℝ] Vec3 := (crossProduct (R := ℝ) d).toContinuousLinearMap
  rw [← ker_crossProduct_eq_span d hd]
  apply derivative_mem_kernel_of_eventually L f x v hf
  filter_upwards [h] with y hy
  rwa [← ker_crossProduct_eq_span d hd] at hy

theorem LocalTwistRepresentation.angular_maurer_cartan {x : E}
    (A : LocalTwistRepresentation (E := E) x) (v w : E) :
    fderiv ℝ (fun y => (A.form y w).1) x v -
        fderiv ℝ (fun y => (A.form y v).1) x w =
      (A.form x v).1 ⨯₃ (A.form x w).1 := by
  have hpart (u : E) : DifferentiableAt ℝ (fun y => A.form y u) x :=
    A.form_differentiable.clm_apply (differentiableAt_const u)
  rw [fderiv.fst (hpart w), fderiv.fst (hpart v)]
  exact congrArg Prod.fst (A.maurer_cartan v w)

/-- A fixed line containing the coupled angular form also contains its
exterior derivative. The coefficient derivative is retained exactly. -/
theorem coupled_angular_derivative_mem_line
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (d : Vec3) (hd : d ≠ 0) (c : E → ℝ) (hc : DifferentiableAt ℝ c x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      (A₁.form y u).1 + c y • (A₂.form y u).1 ∈ Submodule.span ℝ {d})
    (v w : E) :
    (A₁.form x v).1 ⨯₃ (A₁.form x w).1 +
        c x • ((A₂.form x v).1 ⨯₃ (A₂.form x w).1) +
        fderiv ℝ c x v • (A₂.form x w).1 -
        fderiv ℝ c x w • (A₂.form x v).1 ∈ Submodule.span ℝ {d} := by
  let F (u : E) (y : E) := (A₁.form y u).1 + c y • (A₂.form y u).1
  have hpart₁ (u : E) : DifferentiableAt ℝ (fun y => (A₁.form y u).1) x :=
    (A₁.form_differentiable.clm_apply (differentiableAt_const u)).fst
  have hpart₂ (u : E) : DifferentiableAt ℝ (fun y => (A₂.form y u).1) x :=
    (A₂.form_differentiable.clm_apply (differentiableAt_const u)).fst
  have hF (u : E) : DifferentiableAt ℝ (F u) x := (hpart₁ u).add (hc.smul (hpart₂ u))
  have hdF (u z : E) :
      fderiv ℝ (F u) x z = fderiv ℝ (fun y => (A₁.form y u).1) x z +
        c x • fderiv ℝ (fun y => (A₂.form y u).1) x z +
        fderiv ℝ c x z • (A₂.form x u).1 := by
    have hscaled : DifferentiableAt ℝ (fun y => c y • (A₂.form y u).1) x :=
      hc.smul (hpart₂ u)
    dsimp only [F]
    rw [fderiv_fun_add (hpart₁ u) hscaled,
      fderiv_fun_smul hc (hpart₂ u)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, add_assoc]
  have hline (u z : E) : fderiv ℝ (F u) x z ∈ Submodule.span ℝ {d} :=
    derivative_mem_fixed_line d hd (F u) x z (hF u)
      (hrel.mono fun y hy => hy u)
  have hsub := (Submodule.span ℝ {d}).sub_mem (hline w v) (hline v w)
  have heq : fderiv ℝ (F w) x v - fderiv ℝ (F v) x w =
      (A₁.form x v).1 ⨯₃ (A₁.form x w).1 +
        c x • ((A₂.form x v).1 ⨯₃ (A₂.form x w).1) +
        fderiv ℝ c x v • (A₂.form x w).1 -
        fderiv ℝ c x w • (A₂.form x v).1 := by
    rw [hdF, hdF]
    rw [← A₁.angular_maurer_cartan v w, ← A₂.angular_maurer_cartan v w, smul_sub]
    abel
  rwa [heq] at hsub

/-- No actual pair of body maps has the four-dimensional coupled tangent
spaces forced by two distinct fixed centers and the common-new-pin
condition. The chart-to-angular-space identification is literal. -/
theorem no_actual_coupled_angular_manifold
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (d : Vec3) (hd : d ≠ 0) (c : E → ℝ) (hc : DifferentiableAt ℝ c x)
    (hcne : c x ≠ 0)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      (A₁.form y u).1 + c y • (A₂.form y u).1 ∈ Submodule.span ℝ {d})
    (e : E ≃ₗ[ℝ] coupledAngularSpace d (c x))
    (he : ∀ u, (e u).val = ((A₁.form x u).1, (A₂.form x u).1)) : False := by
  let α : coupledAngularSpace d (c x) →ₗ[ℝ] ℝ :=
    -((fderiv ℝ c x).toLinearMap.comp e.symm.toLinearMap)
  apply no_fixed_center_maurer_cartan_identity d hd (c x) hcne α
  intro X Y
  have hX : ((A₁.form x (e.symm X)).1, (A₂.form x (e.symm X)).1) = X.val := by
    rw [← he, e.apply_symm_apply]
  have hY : ((A₁.form x (e.symm Y)).1, (A₂.form x (e.symm Y)).1) = Y.val := by
    rw [← he, e.apply_symm_apply]
  have h := (Submodule.span ℝ {d}).neg_mem
    (coupled_angular_derivative_mem_line A₁ A₂ d hd c hc hrel (e.symm X) (e.symm Y))
  have h₁ := congrArg Prod.fst hX
  have h₂ := congrArg Prod.snd hX
  have h₃ := congrArg Prod.fst hY
  have h₄ := congrArg Prod.snd hY
  dsimp only at h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄] at h
  convert h using 1 <;>
    simp only [α, LinearMap.neg_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, neg_smul] <;> abel

end Papers.Rigidity.Calculus

end
end
end BundleSource0040

section BundleSource0041
/- Source: Papers/RigidityFiniteCenterIntegrability.lean -/




@[expose] public section

/-!
# The center derivative from the actual Maurer--Cartan equation

This is the finite-center part of Lemma 4.2 on the original configuration
chart, whose dimension may exceed three.  A linear section of the angular
map suffices; no local image manifold or integrable chosen distribution is
assumed.  The finite-center premise is explicit and must not be silently
substituted for the infinite-center alternative in a principal theorem.

The calculation applies to the actual configuration chart.
-/

noncomputable section
namespace Papers.Rigidity

open Matrix
open scoped Matrix

theorem evaluateTwist_bracket (a : Vec3) (X Y : Twist) :
    evaluateTwist a (twistBracket X Y) =
      X.1 ⨯₃ evaluateTwist a Y - Y.1 ⨯₃ evaluateTwist a X := by
  ext i
  fin_cases i <;>
    simp [evaluateTwist_apply, twistBracket, cross_apply,Matrix.vecHead,Matrix.vecTail] <;> ring

namespace Calculus

open Filter
open scoped Topology

def crossContinuous : Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (crossProduct (R := ℝ))).toContinuousLinearMap

@[simp] theorem crossContinuous_apply (u v : Vec3) : crossContinuous u v = u ⨯₃ v := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differentiableAt_cross (f g : E → Vec3) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y ⨯₃ g y) x :=
  (crossContinuous.differentiableAt.comp x hf).clm_apply hg

theorem fderiv_cross (f g : E → Vec3) (x u : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => f y ⨯₃ g y) x u =
      f x ⨯₃ fderiv ℝ g x u + fderiv ℝ f x u ⨯₃ g x := by
  change fderiv ℝ (fun y => crossContinuous (f y) (g y)) x u = _
  have hF : DifferentiableAt ℝ (fun y => crossContinuous (f y)) x :=
    crossContinuous.differentiableAt.comp x hf
  rw [fderiv_clm_apply hF hg,
    fderiv_fun_comp x crossContinuous.differentiableAt hf, crossContinuous.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, crossContinuous_apply]

/-- An actual finite center has zero spatial derivative when the angular
projection is onto.  This holds on the entire tangent space, including
any kernel of the body's rank-three projection. -/
theorem actual_finite_center_derivative_eq_zero
    {x : E} (A : LocalTwistRepresentation (E := E) x)
    (a : E → Vec3) (ha : DifferentiableAt ℝ a x)
    (hfix : ∀ᶠ y in 𝓝 x, ∀ u, evaluateTwist (a y) (A.form y u) = 0)
    (hω : Function.Surjective (fun u => (A.form x u).1)) :
    fderiv ℝ a x = 0 := by
  let ω : E →ₗ[ℝ] Vec3 := (LinearMap.fst ℝ Vec3 Vec3).comp (A.form x).toLinearMap
  have hpart (u : E) : DifferentiableAt ℝ (fun y => A.form y u) x :=
    A.form_differentiable.clm_apply (differentiableAt_const u)
  have hdiff (u z : E) :
      fderiv ℝ (fun y => (A.form y u).2) x z +
        (A.form x u).1 ⨯₃ fderiv ℝ a x z +
        fderiv ℝ (fun y => (A.form y u).1) x z ⨯₃ a x = 0 := by
    have he : (fun y => (A.form y u).2 + (A.form y u).1 ⨯₃ a y) =ᶠ[𝓝 x]
        (fun _ => (0 : Vec3)) := hfix.mono fun y hy => hy u
    have hd := congrArg (fun L : E →L[ℝ] Vec3 => L z) (he.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_fun_add (hpart u).snd
        (differentiableAt_cross (fun y => (A.form y u).1) a x (hpart u).fst ha),
      fderiv_const_apply] at hd
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
      fderiv_cross _ _ _ _ (hpart u).fst ha, add_assoc] using hd
  have hD : (fderiv ℝ a x).toLinearMap = 0 := by
    apply linearMap_eq_zero_of_surjective_cross_integrability ω _ hω
    intro v w
    have hangular := A.angular_maurer_cartan v w
    have htranslation :
        fderiv ℝ (fun y => (A.form y w).2) x v -
          fderiv ℝ (fun y => (A.form y v).2) x w =
        (A.form x v).1 ⨯₃ (A.form x w).2 -
          (A.form x w).1 ⨯₃ (A.form x v).2 := by
      rw [fderiv.snd (hpart w), fderiv.snd (hpart v)]
      exact congrArg Prod.snd (A.maurer_cartan v w)
    have hcombo :
        (fderiv ℝ (fun y => (A.form y w).2) x v -
          fderiv ℝ (fun y => (A.form y v).2) x w) +
        ((A.form x w).1 ⨯₃ fderiv ℝ a x v -
          (A.form x v).1 ⨯₃ fderiv ℝ a x w) +
        (fderiv ℝ (fun y => (A.form y w).1) x v -
          fderiv ℝ (fun y => (A.form y v).1) x w) ⨯₃ a x = 0 := by
      calc
        _ = (fderiv ℝ (fun y => (A.form y w).2) x v +
            (A.form x w).1 ⨯₃ fderiv ℝ a x v +
            fderiv ℝ (fun y => (A.form y w).1) x v ⨯₃ a x) -
          (fderiv ℝ (fun y => (A.form y v).2) x w +
            (A.form x v).1 ⨯₃ fderiv ℝ a x w +
            fderiv ℝ (fun y => (A.form y v).1) x w ⨯₃ a x) := by
              simp only [map_sub, LinearMap.sub_apply]
              abel
        _ = 0 := by rw [hdiff, hdiff, sub_self]
    rw [htranslation, hangular] at hcombo
    have hbracket : evaluateTwist (a x) (twistBracket (A.form x v) (A.form x w)) = 0 := by
      rw [evaluateTwist_bracket, hfix.self_of_nhds v, hfix.self_of_nhds w]
      simp
    have hsum : evaluateTwist (a x) (twistBracket (A.form x v) (A.form x w)) +
        ((A.form x w).1 ⨯₃ fderiv ℝ a x v -
          (A.form x v).1 ⨯₃ fderiv ℝ a x w) = 0 := by
      convert hcombo using 1
      simp only [evaluateTwist_apply, twistBracket]
      abel
    rw [hbracket, zero_add, sub_eq_zero] at hsum
    exact hsum.symm
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun L : E →ₗ[ℝ] Vec3 => L u) hD

end Calculus
end Papers.Rigidity

end
end
end BundleSource0041

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0041/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0041.json"

section BundleSource0042
/- Source: Papers/RigidityCoupledAffine.lean -/



@[expose] public section

/-!
# The two-row affine determinant calculation

The generic-new-pin calculation for two spherical projections reduces to
two surjective linear maps to a two-dimensional quotient. The identity
of their affine determinants forces a constant nonzero scalar multiple
and identifies the line joining distinct centers. The proof uses the
actual linear maps and evaluations; no coprimality assertion is assumed.
-/

noncomputable section
namespace Papers.Rigidity

open scoped Matrix

abbrev Vec2 := Fin 2 → ℝ

def determinantTwo (u v : Vec2) : ℝ := u 0 * v 1 - u 1 * v 0

theorem proportional_of_determinantTwo_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A B : E →ₗ[ℝ] Vec2) (hA : Function.Surjective A)
    (h : ∀ q, determinantTwo (A q) (B q) = 0) :
    ∃ c : ℝ, B = c • A := by
  obtain ⟨u₀, hu₀⟩ := hA ![1, 0]
  obtain ⟨u₁, hu₁⟩ := hA ![0, 1]
  have hb₀ : B u₀ 1 = 0 := by
    have hh := h u₀
    simpa [hu₀, determinantTwo] using hh
  have hb₁ : B u₁ 0 = 0 := by
    have hh := h u₁
    simpa [hu₁, determinantTwo] using hh
  have hdiag : B u₁ 1 = B u₀ 0 := by
    have hh := h (u₀ + u₁)
    simp [map_add, determinantTwo, hu₀, hu₁, hb₀, hb₁] at hh
    linarith
  refine ⟨B u₀ 0, ?_⟩
  ext q i
  have hq := h q
  have hh₀ := h (q + u₀)
  have hh₁ := h (q + u₁)
  simp only [map_add, determinantTwo, Pi.add_apply, hu₀, hu₁,
    Matrix.cons_val_zero, Matrix.cons_val_one, hb₀, hb₁, hdiag] at hh₀ hh₁
  dsimp [determinantTwo] at hq
  fin_cases i
  · change B q 0 = B u₀ 0 * A q 0
    nlinarith
  · change B q 1 = B u₀ 0 * A q 1
    nlinarith

/-- The full affine calculation in Lemma 4.5. The scalar is globally
constant because both maps are linear and both rows are independent. -/
theorem affine_determinantTwo_classification
    (A B : Vec3 →ₗ[ℝ] Vec2) (hA : Function.Surjective A)
    (hB : Function.Surjective B) (a b : Vec3)
    (h : ∀ p, determinantTwo (A (p - a)) (B (p - b)) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ B = c • A ∧ A (b - a) = 0 := by
  have hsplit (q : Vec3) :
      determinantTwo (A q) (B q) = 0 ∧
        determinantTwo (A q) (B (a - b)) = 0 := by
    have hp := h (a + q)
    have hm := h (a - q)
    have hpa : a + q - a = q := by abel
    have hpb : a + q - b = q + (a - b) := by abel
    have hma : a - q - a = -q := by abel
    have hmb : a - q - b = -q + (a - b) := by abel
    rw [hpa, hpb] at hp
    rw [hma, hmb] at hm
    simp only [map_add, map_neg, determinantTwo, Pi.add_apply, Pi.neg_apply] at hp hm ⊢
    constructor <;> nlinarith
  obtain ⟨c, hc⟩ := proportional_of_determinantTwo_eq_zero A B hA
    (fun q => (hsplit q).1)
  have hcne : c ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := hB ![1, 0]
    have hh := congrFun hq 0
    simp [hc, hz] at hh
  have hbzero : B (a - b) = 0 := by
    obtain ⟨u₀, hu₀⟩ := hA ![1, 0]
    obtain ⟨u₁, hu₁⟩ := hA ![0, 1]
    have h₀ := (hsplit u₀).2
    have h₁ := (hsplit u₁).2
    simp only [hu₀, determinantTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, zero_mul, sub_zero] at h₀
    simp only [hu₁, determinantTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, zero_mul, zero_sub, neg_eq_zero] at h₁
    ext i
    fin_cases i
    · exact h₁
    · exact h₀
  have hazero : A (a - b) = 0 := by
    rw [hc, LinearMap.smul_apply] at hbzero
    exact (smul_eq_zero.mp hbzero).resolve_left hcne
  refine ⟨c, hcne, hc, ?_⟩
  have heq : b - a = -(a - b) := by abel
  rw [heq, map_neg, hazero, neg_zero]

/-- Once the two-row affine calculation is known, the literal kernel is
the coupled angular space with the fixed inter-center line. -/
theorem affine_kernel_eq_coupledAngularSpace
    (A B : Vec3 →ₗ[ℝ] Vec2) (hA : Function.Surjective A)
    (hB : Function.Surjective B) (a b : Vec3) (hab : b - a ≠ 0)
    (h : ∀ p, determinantTwo (A (p - a)) (B (p - b)) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      (A.comp (LinearMap.fst ℝ Vec3 Vec3) +
        B.comp (LinearMap.snd ℝ Vec3 Vec3)).ker = coupledAngularSpace (b - a) c := by
  obtain ⟨c, hcne, hBscalar, hdiff⟩ := affine_determinantTwo_classification A B hA hB a b h
  have hrank : Module.finrank ℝ A.range = 2 := by
    rw [LinearMap.range_eq_top.mpr hA]
    simp [Vec2]
  have hkerdim : Module.finrank ℝ A.ker = 1 := by
    have hn := A.finrank_range_add_finrank_ker
    rw [hrank] at hn
    have hd : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    rw [hd] at hn
    omega
  have hker : A.ker = Submodule.span ℝ {b - a} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      change A (b - a) = 0
      exact hdiff
    · rw [finrank_span_singleton hab, hkerdim]
  refine ⟨c, hcne, ?_⟩
  ext X
  change A X.1 + B X.2 = 0 ↔ X.1 + c • X.2 ∈ Submodule.span ℝ {b - a}
  rw [← hker]
  change A X.1 + B X.2 = 0 ↔ A (X.1 + c • X.2) = 0
  simp only [map_add, map_smul, hBscalar, LinearMap.smul_apply]

end Papers.Rigidity

end
end
end BundleSource0042

section BundleSource0043
/- Source: Papers/RigidityCoupledQuotient.lean -/




@[expose] public section

/-!
# The actual two-body quotient supplying the affine equations

A four-dimensional angular motion space with surjective projections has
a two-dimensional ordinary quotient. Its two restrictions are surjective
two-row linear maps. Common pins on a dense set imply their determinant
identity everywhere, and the affine calculation gives the fixed-center
coupled form.
-/

noncomputable section
namespace Papers.Rigidity

theorem four_dimensional_two_body_quotient
    (W : Submodule ℝ (Vec3 × Vec3)) (hW : Module.finrank ℝ W = 4)
    (h₁ : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp W.subtype))
    (h₂ : Function.Surjective ((LinearMap.snd ℝ Vec3 Vec3).comp W.subtype)) :
    ∃ A B : Vec3 →ₗ[ℝ] Vec2,
      Function.Surjective A ∧ Function.Surjective B ∧
        W = (A.comp (LinearMap.fst ℝ Vec3 Vec3) +
          B.comp (LinearMap.snd ℝ Vec3 Vec3)).ker := by
  have hdim : Module.finrank ℝ ((Vec3 × Vec3) ⧸ W) = Module.finrank ℝ Vec2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hW] at hh
    have hv : Module.finrank ℝ (Vec3 × Vec3) = 6 := by simp [Vec3]
    rw [hv] at hh
    have ht : Module.finrank ℝ Vec2 = 2 := by simp [Vec2]
    omega
  let e : ((Vec3 × Vec3) ⧸ W) ≃ₗ[ℝ] Vec2 := LinearEquiv.ofFinrankEq _ _ hdim
  let L : (Vec3 × Vec3) →ₗ[ℝ] Vec2 := e.toLinearMap.comp W.mkQ
  have hLsurj : Function.Surjective L := e.surjective.comp W.mkQ_surjective
  have hLker : L.ker = W := by
    dsimp only [L]
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, W.ker_mkQ]
  let A : Vec3 →ₗ[ℝ] Vec2 := L.comp (LinearMap.inl ℝ Vec3 Vec3)
  let B : Vec3 →ₗ[ℝ] Vec2 := L.comp (LinearMap.inr ℝ Vec3 Vec3)
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨X, hX⟩ := hLsurj y
    obtain ⟨Z, hZ⟩ := h₂ X.2
    have hZsecond : Z.val.2 = X.2 := hZ
    have hLZ : L Z.val = 0 := by
      change Z.val ∈ L.ker
      rw [hLker]
      exact Z.property
    refine ⟨X.1 - Z.val.1, ?_⟩
    change L (X.1 - Z.val.1, 0) = y
    have hsplit : (X.1 - Z.val.1, (0 : Vec3)) = X - Z.val := by
      apply Prod.ext
      · rfl
      · simp [hZsecond]
    rw [hsplit, map_sub, hLZ, sub_zero, hX]
  have hB : Function.Surjective B := by
    intro y
    obtain ⟨X, hX⟩ := hLsurj y
    obtain ⟨Z, hZ⟩ := h₁ X.1
    have hZfirst : Z.val.1 = X.1 := hZ
    have hLZ : L Z.val = 0 := by
      change Z.val ∈ L.ker
      rw [hLker]
      exact Z.property
    refine ⟨X.2 - Z.val.2, ?_⟩
    change L (0, X.2 - Z.val.2) = y
    have hsplit : ((0 : Vec3), X.2 - Z.val.2) = X - Z.val := by
      apply Prod.ext
      · simp [hZfirst]
      · rfl
    rw [hsplit, map_sub, hLZ, sub_zero, hX]
  refine ⟨A, B, hA, hB, ?_⟩
  have hsplit : A.comp (LinearMap.fst ℝ Vec3 Vec3) +
      B.comp (LinearMap.snd ℝ Vec3 Vec3) = L := by
    apply LinearMap.ext
    intro X
    change L (X.1, 0) + L (0, X.2) = L X
    rw [← map_add]
    congr 1
    simp
  rw [hsplit, hLker]

theorem determinantTwo_eq_zero_of_dense_common_pins
    (A B : Vec3 →ₗ[ℝ] Vec2) (a b : Vec3)
    (U : Set Vec3) (hU : Dense U)
    (hpin : ∀ p ∈ U, ∃ s t : ℝ, s ≠ 0 ∧ t ≠ 0 ∧
      A (s • (p - a)) + B (t • (p - b)) = 0) :
    ∀ p, determinantTwo (A (p - a)) (B (p - b)) = 0 := by
  have hlocal : ∀ p ∈ U, determinantTwo (A (p - a)) (B (p - b)) = 0 := by
    intro p hp
    obtain ⟨s, t, hs, ht, he⟩ := hpin p hp
    have h₀ := congrFun he 0
    have h₁ := congrFun he 1
    simp only [map_smul, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h₀ h₁
    have hscaled : t * determinantTwo (A (p - a)) (B (p - b)) = 0 := by
      dsimp [determinantTwo]
      linear_combination (A (p - a) 0) * h₁ - (A (p - a) 1) * h₀
    exact (mul_eq_zero.mp hscaled).resolve_left ht
  have hAc : Continuous (fun p : Vec3 => A (p - a)) :=
    A.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  have hBc : Continuous (fun p : Vec3 => B (p - b)) :=
    B.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  have hf : Continuous (fun p => determinantTwo (A (p - a)) (B (p - b))) := by
    exact (((continuous_apply 0).comp hAc).mul ((continuous_apply 1).comp hBc)).sub
      (((continuous_apply 1).comp hAc).mul ((continuous_apply 0).comp hBc))
  have hclosed : IsClosed {p | determinantTwo (A (p - a)) (B (p - b)) = 0} :=
    isClosed_eq hf continuous_const
  have hcl := closure_minimal hlocal hclosed
  intro p
  exact hcl (by rw [hU.closure_eq]; trivial)

/-- The full four-dimensional angular-space classification for distinct
centers, derived from actual common pins on a dense set. -/
theorem coupledAngularSpace_of_dense_common_pins
    (W : Submodule ℝ (Vec3 × Vec3)) (hW : Module.finrank ℝ W = 4)
    (h₁ : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp W.subtype))
    (h₂ : Function.Surjective ((LinearMap.snd ℝ Vec3 Vec3).comp W.subtype))
    (a b : Vec3) (hab : b - a ≠ 0) (U : Set Vec3) (hU : Dense U)
    (hpin : ∀ p ∈ U, ∃ s t : ℝ, s ≠ 0 ∧ t ≠ 0 ∧
      (s • (p - a), t • (p - b)) ∈ W) :
    ∃ c : ℝ, c ≠ 0 ∧ W = coupledAngularSpace (b - a) c := by
  obtain ⟨A, B, hA, hB, hWker⟩ := four_dimensional_two_body_quotient W hW h₁ h₂
  have hdet : ∀ p, determinantTwo (A (p - a)) (B (p - b)) = 0 := by
    apply determinantTwo_eq_zero_of_dense_common_pins A B a b U hU
    intro p hp
    obtain ⟨s, t, hs, ht, hst⟩ := hpin p hp
    rw [hWker] at hst
    exact ⟨s, t, hs, ht, hst⟩
  obtain ⟨c, hc, hker⟩ := affine_kernel_eq_coupledAngularSpace A B hA hB a b hab hdet
  exact ⟨c, hc, hWker.trans hker⟩

end Papers.Rigidity

end
end
end BundleSource0043

section BundleSource0044
/- Source: Papers/RigidityDenseCommonPins.lean -/





@[expose] public section

/-!
# Nonzero common-pin motions from the actual joint rank

For two rank-three body projections on a four-dimensional tangent space,
injectivity of the combined projection makes their one-dimensional
kernels distinct.  A dense set of pins detects the other body's twist
on either kernel.  The joint pin rank bound then supplies a stationary
motion with both projections nonzero.  Such a family is therefore a
conclusion, not an extra generic-pin premise in the coupled calculation.

The dense-pin calculation supplies the coupled case of Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity

open CofactorKernel CommonPinLowRank CenterKernelFamily
open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem dense_common_pins_of_two_rankThree_projections
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4)
    (hA : Module.finrank ℝ A.range = 3) (hB : Module.finrank ℝ B.range = 3)
    (hinj : Function.Injective (A.prod B))
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ U : Set Vec3, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∃ u : E, A u ≠ 0 ∧ B u ≠ 0 ∧
        evaluateTwist p (A u) = 0 ∧ evaluateTwist p (B u) = 0 := by
  let S₁ := A.ker.map B
  let S₂ := B.ker.map A
  have hkA : Module.finrank ℝ A.ker = 1 := by
    have h := A.finrank_range_add_finrank_ker
    omega
  have hkB : Module.finrank ℝ B.ker = 1 := by
    have h := B.finrank_range_add_finrank_ker
    omega
  have hS₁ : Module.finrank ℝ S₁ ≤ 1 := (Submodule.finrank_map_le B A.ker).trans hkA.le
  have hS₂ : Module.finrank ℝ S₂ ≤ 1 := (Submodule.finrank_map_le A B.ker).trans hkB.le
  let U₁ := {p : Vec3 | Function.Injective (restrictEvaluation S₁ p)}
  let U₂ := {p : Vec3 | Function.Injective (restrictEvaluation S₂ p)}
  have hO₁ : IsOpen U₁ := isOpen_injective_evaluation S₁
  have hO₂ : IsOpen U₂ := isOpen_injective_evaluation S₂
  have hD₁ : Dense U₁ := dense_injective_evaluation_of_finrank_le_one S₁ hS₁
  have hD₂ : Dense U₂ := dense_injective_evaluation_of_finrank_le_one S₂ hS₂
  refine ⟨U₁ ∩ U₂, hO₁.inter hO₂, hD₁.inter_of_isOpen_left hD₂ hO₁, ?_⟩
  intro p hp
  have hk : 0 < Module.finrank ℝ (bodyJointPin A B p).ker := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (K := ℝ) (V := E) (V₂ := Vec3 × Vec3) (bodyJointPin A B p)
    have hb := hrank p
    omega
  obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := (bodyJointPin A B p).ker)).mp hk
  have huval : u.val ≠ 0 := fun h => hu (Subtype.ext h)
  have hfix : evaluateTwist p (A u.val) = 0 ∧ evaluateTwist p (B u.val) = 0 := by
    have hz : bodyJointPin A B p u.val = 0 := u.property
    exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  have hAne : A u.val ≠ 0 := by
    intro hzero
    let Y : S₁ := ⟨B u.val, u.val, hzero, rfl⟩
    have hY : Y = 0 := hp.1 (by
      change evaluateTwist p (B u.val) = evaluateTwist p 0
      simpa only [map_zero] using hfix.2)
    have hBzero : B u.val = 0 := congrArg Subtype.val hY
    exact huval (hinj (by
      change (A u.val, B u.val) = (A 0, B 0)
      simp only [hzero, hBzero, map_zero]))
  have hBne : B u.val ≠ 0 := by
    intro hzero
    let Y : S₂ := ⟨A u.val, u.val, hzero, rfl⟩
    have hY : Y = 0 := hp.2 (by
      change evaluateTwist p (A u.val) = evaluateTwist p 0
      simpa only [map_zero] using hfix.1)
    exact hAne (congrArg Subtype.val hY)
  exact ⟨u.val, hAne, hBne, hfix⟩

def angularPair (A B : E →ₗ[ℝ] Twist) : E →ₗ[ℝ] (Vec3 × Vec3) :=
  ((LinearMap.fst ℝ Vec3 Vec3).comp A).prod ((LinearMap.fst ℝ Vec3 Vec3).comp B)

theorem angularPair_injective_of_finiteCenters
    (A B : E →ₗ[ℝ] Twist) (a b : Vec3)
    (hA : A.range = finiteCenterSpace a) (hB : B.range = finiteCenterSpace b)
    (hinj : Function.Injective (A.prod B)) : Function.Injective (angularPair A B) := by
  intro u v huv
  change ((A u).1, (B u).1) = ((A v).1, (B v).1) at huv
  have hω₁ := congrArg (fun X : Vec3 × Vec3 => X.1) huv
  have hω₂ := congrArg (fun X : Vec3 × Vec3 => X.2) huv
  dsimp only at hω₁ hω₂
  have htranslation (T : E →ₗ[ℝ] Twist) (c : Vec3)
      (hT : T.range = finiteCenterSpace c) (z : E) : (T z).2 = -((T z).1 ⨯₃ c) := by
    have hm : T z ∈ finiteCenterSpace c := by rw [← hT]; exact ⟨z, rfl⟩
    exact eq_neg_of_add_eq_zero_left hm
  apply hinj
  change (A u, B u) = (A v, B v)
  apply Prod.ext
  · exact Prod.ext hω₁ (by rw [htranslation A a hA, htranslation A a hA, hω₁])
  · exact Prod.ext hω₂ (by rw [htranslation B b hB, htranslation B b hB, hω₂])

theorem angular_surjective_of_finiteCenter_range
    (A : E →ₗ[ℝ] Twist) (a : Vec3) (hA : A.range = finiteCenterSpace a) :
    Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp A) := by
  intro ω
  have hm : (finiteCenterRotations a ω).val ∈ A.range := by
    rw [hA]
    exact (finiteCenterRotations a ω).property
  obtain ⟨u, hu⟩ := hm
  exact ⟨u, congrArg Prod.fst hu⟩

theorem exists_dense_finiteCenters_angular_common_pins
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4)
    (a b : Vec3)
    (hA : A.range = finiteCenterSpace a) (hB : B.range = finiteCenterSpace b)
    (hinj : Function.Injective (A.prod B))
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ O : Set Vec3, Dense O ∧ ∀ p ∈ O, ∃ s t : ℝ, s ≠ 0 ∧ t ≠ 0 ∧
      (s • (p - a), t • (p - b)) ∈ (angularPair A B).range := by
  have hArank : Module.finrank ℝ A.range = 3 := by rw [hA, finrank_finiteCenterSpace]
  have hBrank : Module.finrank ℝ B.range = 3 := by rw [hB, finrank_finiteCenterSpace]
  obtain ⟨U, _, hUdense, hU⟩ := dense_common_pins_of_two_rankThree_projections
    A B hdim hArank hBrank hinj hrank
  let O := (U \ {a}) \ {b}
  refine ⟨O, (hUdense.sdiff_singleton a).sdiff_singleton b, ?_⟩
  intro p hp
  obtain ⟨u, hAu, hBu, hpA, hpB⟩ := hU p hp.1.1
  let X : finiteCenterSpace a := ⟨A u, by rw [← hA]; exact ⟨u, rfl⟩⟩
  let Y : finiteCenterSpace b := ⟨B u, by rw [← hB]; exact ⟨u, rfl⟩⟩
  obtain ⟨s, hs⟩ := finiteVector_kernel a p hp.1.2 X hpA
  obtain ⟨t, ht⟩ := finiteVector_kernel b p hp.2 Y hpB
  have hsne : s ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val hs
    exact hAu (by simpa only [hz, zero_smul, Submodule.coe_zero] using hh)
  have htne : t ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val ht
    exact hBu (by simpa only [hz, zero_smul, Submodule.coe_zero] using hh)
  refine ⟨s, t, hsne, htne, u, ?_⟩
  apply Prod.ext
  · exact congrArg (fun Z : finiteCenterSpace a => Z.val.1) hs
  · exact congrArg (fun Z : finiteCenterSpace b => Z.val.1) ht

/-- The literal angular motion space has the coupled fixed-center form
when the two finite centers are distinct.  The nonzero dense stationary
family has been derived from the actual rank-three projections. -/
theorem coupledAngularSpace_of_finiteCenters_joint_rank
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4)
    (a b : Vec3) (hab : b - a ≠ 0)
    (hA : A.range = finiteCenterSpace a) (hB : B.range = finiteCenterSpace b)
    (hinj : Function.Injective (A.prod B))
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ c : ℝ, c ≠ 0 ∧ (angularPair A B).range = coupledAngularSpace (b - a) c := by
  classical
  have hArank : Module.finrank ℝ A.range = 3 := by rw [hA, finrank_finiteCenterSpace]
  have hBrank : Module.finrank ℝ B.range = 3 := by rw [hB, finrank_finiteCenterSpace]
  obtain ⟨U, hUopen, hUdense, hU⟩ := dense_common_pins_of_two_rankThree_projections
    A B hdim hArank hBrank hinj hrank
  let W := (angularPair A B).range
  have hW : Module.finrank ℝ W = 4 := by
    rw [LinearMap.finrank_range_of_inj
      (angularPair_injective_of_finiteCenters A B a b hA hB hinj)]
    exact hdim
  have hsurj₁ : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range A a hA ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  have hsurj₂ : Function.Surjective ((LinearMap.snd ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range B b hB ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  let O := (U \ {a}) \ {b}
  have hOdense : Dense O := (hUdense.sdiff_singleton a).sdiff_singleton b
  apply coupledAngularSpace_of_dense_common_pins W hW hsurj₁ hsurj₂ a b hab O hOdense
  intro p hp
  obtain ⟨u, hAu, hBu, hpA, hpB⟩ := hU p hp.1.1
  have hpane : p ≠ a := hp.1.2
  have hpbne : p ≠ b := hp.2
  let X : finiteCenterSpace a := ⟨A u, by rw [← hA]; exact ⟨u, rfl⟩⟩
  let Y : finiteCenterSpace b := ⟨B u, by rw [← hB]; exact ⟨u, rfl⟩⟩
  obtain ⟨s, hs⟩ := finiteVector_kernel a p hpane X hpA
  obtain ⟨t, ht⟩ := finiteVector_kernel b p hpbne Y hpB
  have hsne : s ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val hs
    exact hAu (by simpa only [hz, zero_smul, Submodule.coe_zero] using hh)
  have htne : t ≠ 0 := by
    intro hz
    have hh := congrArg Subtype.val ht
    exact hBu (by simpa only [hz, zero_smul, Submodule.coe_zero] using hh)
  refine ⟨s, t, hsne, htne, u, ?_⟩
  apply Prod.ext
  · exact congrArg (fun Z : finiteCenterSpace a => Z.val.1) hs
  · exact congrArg (fun Z : finiteCenterSpace b => Z.val.1) ht

end Papers.Rigidity

end
end
end BundleSource0044

section BundleSource0045
/- Source: Papers/RigidityMovingCenterLine.lean -/




@[expose] public section

/-!
# Differentiating the actual coupled center line

The finite centers are recovered as functions of the original chart.
Their derivatives vanish by the actual body Maurer--Cartan equations.
Consequently one can differentiate membership in their moving difference
line without postulating that line to be fixed on a neighborhood.

This supplies the distinct-center case of the four-dimensional,
two-rank-three calculation.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix CofactorKernel
open scoped Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_mem_moving_line_of_derivative_zero
    (d f : E → Vec3) (x v : E) (hd : DifferentiableAt ℝ d x)
    (hf : DifferentiableAt ℝ f x) (hdne : d x ≠ 0) (hDd : fderiv ℝ d x = 0)
    (hline : ∀ᶠ y in 𝓝 x, f y ∈ Submodule.span ℝ {d y}) :
    fderiv ℝ f x v ∈ Submodule.span ℝ {d x} := by
  have he : (fun y => d y ⨯₃ f y) =ᶠ[𝓝 x] (fun _ => (0 : Vec3)) := by
    filter_upwards [hline] with y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    rw [← ha, map_smul, cross_self, smul_zero]
  have hh := congrArg (fun L : E →L[ℝ] Vec3 => L v) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_cross d f x v hd hf, hDd, fderiv_const_apply] at hh
  have hzero : d x ⨯₃ fderiv ℝ f x v = 0 := by simpa using hh
  rw [← ker_crossProduct_eq_span (d x) hdne]
  exact hzero

theorem coupled_angular_derivative_mem_moving_line
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (d : E → Vec3) (hd : DifferentiableAt ℝ d x) (hdne : d x ≠ 0)
    (hDd : fderiv ℝ d x = 0)
    (c : E → ℝ) (hc : DifferentiableAt ℝ c x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      (A₁.form y u).1 + c y • (A₂.form y u).1 ∈ Submodule.span ℝ {d y})
    (v w : E) :
    (A₁.form x v).1 ⨯₃ (A₁.form x w).1 +
        c x • ((A₂.form x v).1 ⨯₃ (A₂.form x w).1) +
        fderiv ℝ c x v • (A₂.form x w).1 -
        fderiv ℝ c x w • (A₂.form x v).1 ∈ Submodule.span ℝ {d x} := by
  let F (u : E) (y : E) := (A₁.form y u).1 + c y • (A₂.form y u).1
  have hpart₁ (u : E) : DifferentiableAt ℝ (fun y => (A₁.form y u).1) x :=
    (A₁.form_differentiable.clm_apply (differentiableAt_const u)).fst
  have hpart₂ (u : E) : DifferentiableAt ℝ (fun y => (A₂.form y u).1) x :=
    (A₂.form_differentiable.clm_apply (differentiableAt_const u)).fst
  have hF (u : E) : DifferentiableAt ℝ (F u) x := (hpart₁ u).add (hc.smul (hpart₂ u))
  have hdF (u z : E) :
      fderiv ℝ (F u) x z = fderiv ℝ (fun y => (A₁.form y u).1) x z +
        c x • fderiv ℝ (fun y => (A₂.form y u).1) x z +
        fderiv ℝ c x z • (A₂.form x u).1 := by
    have hscaled : DifferentiableAt ℝ (fun y => c y • (A₂.form y u).1) x :=
      hc.smul (hpart₂ u)
    dsimp only [F]
    rw [fderiv_fun_add (hpart₁ u) hscaled,
      fderiv_fun_smul hc (hpart₂ u)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, add_assoc]
  have hline (u z : E) : fderiv ℝ (F u) x z ∈ Submodule.span ℝ {d x} :=
    derivative_mem_moving_line_of_derivative_zero d (F u) x z hd (hF u) hdne hDd
      (hrel.mono fun y hy => hy u)
  have hsub := (Submodule.span ℝ {d x}).sub_mem (hline w v) (hline v w)
  have heq : fderiv ℝ (F w) x v - fderiv ℝ (F v) x w =
      (A₁.form x v).1 ⨯₃ (A₁.form x w).1 +
        c x • ((A₂.form x v).1 ⨯₃ (A₂.form x w).1) +
        fderiv ℝ c x v • (A₂.form x w).1 -
        fderiv ℝ c x w • (A₂.form x v).1 := by
    rw [hdF, hdF]
    rw [← A₁.angular_maurer_cartan v w, ← A₂.angular_maurer_cartan v w, smul_sub]
    abel
  rwa [heq] at hsub

theorem no_actual_coupled_angular_manifold_moving_line
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (d : E → Vec3) (hd : DifferentiableAt ℝ d x) (hdne : d x ≠ 0)
    (hDd : fderiv ℝ d x = 0)
    (c : E → ℝ) (hc : DifferentiableAt ℝ c x) (hcne : c x ≠ 0)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ u,
      (A₁.form y u).1 + c y • (A₂.form y u).1 ∈ Submodule.span ℝ {d y})
    (e : E ≃ₗ[ℝ] coupledAngularSpace (d x) (c x))
    (he : ∀ u, (e u).val = ((A₁.form x u).1, (A₂.form x u).1)) : False := by
  let α : coupledAngularSpace (d x) (c x) →ₗ[ℝ] ℝ :=
    -((fderiv ℝ c x).toLinearMap.comp e.symm.toLinearMap)
  apply no_fixed_center_maurer_cartan_identity (d x) hdne (c x) hcne α
  intro X Y
  have hX : ((A₁.form x (e.symm X)).1, (A₂.form x (e.symm X)).1) = X.val := by
    rw [← he, e.apply_symm_apply]
  have hY : ((A₁.form x (e.symm Y)).1, (A₂.form x (e.symm Y)).1) = Y.val := by
    rw [← he, e.apply_symm_apply]
  have h := (Submodule.span ℝ {d x}).neg_mem
    (coupled_angular_derivative_mem_moving_line A₁ A₂ d hd hdne hDd c hc hrel
      (e.symm X) (e.symm Y))
  have h₁ := congrArg Prod.fst hX
  have h₂ := congrArg Prod.snd hX
  have h₃ := congrArg Prod.fst hY
  have h₄ := congrArg Prod.snd hY
  dsimp only at h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄] at h
  convert h using 1 <;>
    simp only [α, LinearMap.neg_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, neg_smul] <;> abel

end Papers.Rigidity.Calculus

end
end
end BundleSource0045

section BundleSource0046
/- Source: Papers/RigidityFinitePairCenters.lean -/



@[expose] public section

/-!
# The actual two finite centers coincide

The pointwise two-row classification supplies a scalar, whose smooth
representative is an explicit coordinate quotient of cross products.
The two center derivatives vanish on the entire original chart.  The
resulting moving-line calculation contradicts distinct centers, with no
flow-invariance assumption and no postulated smooth scalar.

These center calculations support Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix CofactorKernel
open scoped Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_differentiable_coupled_scalar
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (d : E → Vec3) (x : E)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hd : DifferentiableAt ℝ d x) (hdne : d x ≠ 0)
    (hsurj : Function.Surjective (fun u => (θ₂ x u).1))
    (hpoint : ∀ᶠ y in 𝓝 x, ∃ γ : ℝ, γ ≠ 0 ∧
      (angularPair (θ₁ y).toLinearMap (θ₂ y).toLinearMap).range =
        coupledAngularSpace (d y) γ) :
    ∃ c : E → ℝ, DifferentiableAt ℝ c x ∧ c x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x,
        (angularPair (θ₁ y).toLinearMap (θ₂ y).toLinearMap).range =
          coupledAngularSpace (d y) (c y) := by
  have hcross : ∃ ω : Vec3, d x ⨯₃ ω ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h0 := congrFun (hn ![1, 0, 0]) (2 : Fin 3)
    have h1 := congrFun (hn ![1, 0, 0]) (1 : Fin 3)
    have h2 := congrFun (hn ![0, 1, 0]) (2 : Fin 3)
    simp [cross_apply] at h0 h1 h2
    apply hdne
    funext i
    fin_cases i <;> simp_all
  obtain ⟨ω, hω⟩ := hcross
  obtain ⟨u₀, hu₀⟩ := hsurj ω
  change (θ₂ x u₀).1 = ω at hu₀
  have hvalue : d x ⨯₃ (θ₂ x u₀).1 ≠ 0 := by rwa [hu₀]
  obtain ⟨j, hj⟩ := not_forall.mp (fun h => hvalue (funext h))
  let f₁ : E → ℝ := fun y => (d y ⨯₃ (θ₁ y u₀).1) j
  let f₂ : E → ℝ := fun y => (d y ⨯₃ (θ₂ y u₀).1) j
  let c : E → ℝ := fun y => -f₁ y / f₂ y
  have hf₁ : DifferentiableAt ℝ f₁ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₁ y u₀).1) x hd
      (hθ₁.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₂ : DifferentiableAt ℝ f₂ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₂ y u₀).1) x hd
      (hθ₂.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₂ne : f₂ x ≠ 0 := hj
  have hnear : ∀ᶠ y in 𝓝 x, c y ≠ 0 ∧
      (angularPair (θ₁ y).toLinearMap (θ₂ y).toLinearMap).range =
        coupledAngularSpace (d y) (c y) := by
    filter_upwards [hf₂.continuousAt.eventually_ne hf₂ne, hpoint] with y hy hpy
    obtain ⟨γ, hγ, hspace⟩ := hpy
    have hline : (θ₁ y u₀).1 + γ • (θ₂ y u₀).1 ∈ Submodule.span ℝ {d y} := by
      change angularPair (θ₁ y).toLinearMap (θ₂ y).toLinearMap u₀ ∈
        coupledAngularSpace (d y) γ
      rw [← hspace]
      exact ⟨u₀, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hline
    have hzero : d y ⨯₃ ((θ₁ y u₀).1 + γ • (θ₂ y u₀).1) = 0 := by
      rw [← hr, map_smul, cross_self, smul_zero]
    have hcoordinate : f₁ y + γ * f₂ y = 0 := by
      have hh := congrFun hzero j
      simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, smul_eq_mul] using hh
    have hcy : c y = γ := by
      apply (div_eq_iff hy).mpr
      linarith
    exact ⟨by simpa only [hcy] using hγ, by simpa only [hcy] using hspace⟩
  have hprod : DifferentiableAt ℝ (fun y => -f₁ y * (f₂ y)⁻¹) x :=
    hf₁.neg.mul (hf₂.inv hf₂ne)
  have hquot : DifferentiableAt ℝ c x := by
    simpa only [c, div_eq_mul_inv] using hprod
  exact ⟨c, hquot, hnear.self_of_nhds.1, hnear.mono fun _ h => h.2⟩

/-- Lemma 4.5 on the original four-dimensional configuration chart.
The two center functions are permitted to move in the hypotheses; their
derivatives are derived to vanish from the actual body maps. -/
theorem actual_two_finite_centers_equal
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (hdim : Module.finrank ℝ E = 4) (a b : E → Vec3)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hcenters : ∀ᶠ y in 𝓝 x,
      (A₁.form y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (A₂.form y).toLinearMap.range = finiteCenterSpace (b y))
    (hinj : ∀ᶠ y in 𝓝 x,
      Function.Injective ((A₁.form y).toLinearMap.prod (A₂.form y).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (A₁.form y).toLinearMap (A₂.form y).toLinearMap p).range ≤ 3) :
    a x = b x := by
  by_contra hab
  let d : E → Vec3 := fun y => b y - a y
  have hd : DifferentiableAt ℝ d x := hb.sub ha
  have hdne : d x ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hsurj₁ : Function.Surjective (fun u => (A₁.form x u).1) :=
    angular_surjective_of_finiteCenter_range (A₁.form x).toLinearMap (a x)
      hcenters.self_of_nhds.1
  have hsurj₂ : Function.Surjective (fun u => (A₂.form x u).1) :=
    angular_surjective_of_finiteCenter_range (A₂.form x).toLinearMap (b x)
      hcenters.self_of_nhds.2
  have hfix₁ : ∀ᶠ y in 𝓝 x, ∀ u, evaluateTwist (a y) (A₁.form y u) = 0 := by
    filter_upwards [hcenters] with y hy
    intro u
    have hm : A₁.form y u ∈ finiteCenterSpace (a y) := by
      rw [← hy.1]
      exact ⟨u, rfl⟩
    exact hm
  have hfix₂ : ∀ᶠ y in 𝓝 x, ∀ u, evaluateTwist (b y) (A₂.form y u) = 0 := by
    filter_upwards [hcenters] with y hy
    intro u
    have hm : A₂.form y u ∈ finiteCenterSpace (b y) := by
      rw [← hy.2]
      exact ⟨u, rfl⟩
    exact hm
  have hDa := actual_finite_center_derivative_eq_zero A₁ a ha hfix₁ hsurj₁
  have hDb := actual_finite_center_derivative_eq_zero A₂ b hb hfix₂ hsurj₂
  have hDd : fderiv ℝ d x = 0 := by
    rw [fderiv_fun_sub hb ha, hDa, hDb, sub_self]
  have hpoint : ∀ᶠ y in 𝓝 x, ∃ γ : ℝ, γ ≠ 0 ∧
      (angularPair (A₁.form y).toLinearMap (A₂.form y).toLinearMap).range =
        coupledAngularSpace (d y) γ := by
    filter_upwards [hd.continuousAt.eventually_ne hdne, hcenters, hinj, hrank] with y hdy hcy hiy hry
    exact coupledAngularSpace_of_finiteCenters_joint_rank
      (A₁.form y).toLinearMap (A₂.form y).toLinearMap hdim (a y) (b y) hdy hcy.1 hcy.2 hiy hry
  obtain ⟨c, hc, hcne, hspace⟩ := exists_differentiable_coupled_scalar
    A₁.form A₂.form d x A₁.form_differentiable A₂.form_differentiable
    hd hdne hsurj₂ hpoint
  have hangularInj : Function.Injective (angularPair (A₁.form x).toLinearMap (A₂.form x).toLinearMap) :=
    angularPair_injective_of_finiteCenters _ _ (a x) (b x)
      hcenters.self_of_nhds.1 hcenters.self_of_nhds.2 hinj.self_of_nhds
  let e : E ≃ₗ[ℝ] coupledAngularSpace (d x) (c x) :=
    (LinearEquiv.ofInjective
      (angularPair (A₁.form x).toLinearMap (A₂.form x).toLinearMap) hangularInj).trans
        (LinearEquiv.ofEq _ _ hspace.self_of_nhds)
  refine no_actual_coupled_angular_manifold_moving_line A₁ A₂ d hd hdne hDd c hc hcne ?_ e ?_
  · filter_upwards [hspace] with y hy
    intro u
    change angularPair (A₁.form y).toLinearMap (A₂.form y).toLinearMap u ∈
      coupledAngularSpace (d y) (c y)
    rw [← hy]
    exact ⟨u, rfl⟩
  · intro u
    rfl

end Papers.Rigidity.Calculus

end
end
end BundleSource0046

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0046/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0046.json"

section BundleSource0047
/- Source: Papers/RigiditySmoothKernelVector.lean -/



@[expose] public section

/-!
# A differentiable vector in the actual one-dimensional kernel

A fixed right inverse at the base point gives a nearby right inverse by
ordinary inversion of a three-by-three continuous linear map.  Subtracting
the resulting correction from a fixed nonzero kernel vector constructs
the smooth vector used in the final common-center calculation.  Its
nonvanishing follows by continuity, not from a chosen kernel bundle.

The resulting vector lies in the original family of kernels.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_differentiable_kernel_vector
    (A : E → (E →L[ℝ] Vec3)) (x : E)
    (hdim : Module.finrank ℝ E = 4) (hA : DifferentiableAt ℝ A x)
    (hsurj : Function.Surjective (A x)) :
    ∃ v : E → E, DifferentiableAt ℝ v x ∧
      ∀ᶠ y in 𝓝 x, v y ≠ 0 ∧ A y (v y) = 0 := by
  have hk : 0 < Module.finrank ℝ (A x).toLinearMap.ker := by
    have hh := LinearMap.finrank_range_add_finrank_ker
      (K := ℝ) (V := E) (V₂ := Vec3) (A x).toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj] at hh
    have hd₃ : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    rw [finrank_top, hd₃, hdim] at hh
    omega
  obtain ⟨v₀, hv₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := (A x).toLinearMap.ker)).mp hk
  have hv₀val : v₀.val ≠ 0 := fun h => hv₀ (Subtype.ext h)
  have hAv₀ : A x v₀.val = 0 := v₀.property
  obtain ⟨s₀, hs₀⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let s : Vec3 →L[ℝ] E := s₀.toContinuousLinearMap
  let F : E → (Vec3 →L[ℝ] Vec3) := fun y => (A y).comp s
  have hF : DifferentiableAt ℝ F x := hA.clm_comp (differentiableAt_const s)
  have hFx : F x = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun L : Vec3 →ₗ[ℝ] Vec3 => L u) hs₀
  have hFxUnit : IsUnit (F x) := by rw [hFx]; exact isUnit_one
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (F y) :=
    hF.continuousAt.eventually (Units.isOpen.mem_nhds hFxUnit)
  let v : E → E := fun y => v₀.val - s (Ring.inverse (F y) (A y v₀.val))
  have hv : DifferentiableAt ℝ v x := (differentiableAt_const v₀.val).sub
    (s.differentiableAt.comp x ((hF.inverse hFxUnit).clm_apply
      (hA.clm_apply (differentiableAt_const v₀.val))))
  have hvx : v x = v₀.val := by simp only [v, hAv₀, map_zero, sub_zero]
  have hvxne : v x ≠ 0 := by rwa [hvx]
  refine ⟨v, hv, ?_⟩
  filter_upwards [hunit, hv.continuousAt.eventually_ne hvxne] with y hy hyv
  refine ⟨hyv, ?_⟩
  have hright : A y (s (Ring.inverse (F y) (A y v₀.val))) = A y v₀.val := by
    exact congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (A y v₀.val))
      (Ring.mul_inverse_cancel (F y) hy)
  dsimp only [v]
  rw [map_sub, hright, sub_self]

end Papers.Rigidity.Calculus

end
end
end BundleSource0047

section BundleSource0048
/- Source: Papers/RigiditySameCenterDiscrepancy.lean -/



@[expose] public section

/-!
# The actual rank-one discrepancy for a common finite center

The two-row quotient is constructed from the literal four-dimensional
angular image.  Its affine determinant equations force one scalar.
The discrepancy has rank one and its kernel maps onto the full center
space in the first body.  These are exactly the data required by the
already-derived Maurer--Cartan distribution obstruction.

The discrepancy is derived from the actual joint-pin rank bound.
-/

noncomputable section
namespace Papers.Rigidity

open CofactorKernel Matrix
open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem eq_of_angular_eq_mem_finiteCenter (a : Vec3) (X Y : Twist)
    (hX : X ∈ finiteCenterSpace a) (hY : Y ∈ finiteCenterSpace a)
    (hω : X.1 = Y.1) : X = Y := by
  apply Prod.ext hω
  have htx : X.2 = -(X.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left hX
  have hty : Y.2 = -(Y.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left hY
  rw [htx, hty, hω]

/-- No distribution, scalar regularity, or rank-one relation is assumed:
all three are pointwise algebraic consequences of the actual pin bound. -/
theorem sameCenter_scalar_discrepancy
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4) (a : Vec3)
    (hA : A.range = finiteCenterSpace a) (hB : B.range = finiteCenterSpace a)
    (hinj : Function.Injective (A.prod B))
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ lam : ℝ, lam ≠ 0 ∧ B - lam • A ≠ 0 ∧
      Module.finrank ℝ (B - lam • A).range ≤ 1 ∧
      finiteCenterSpace a ≤ (A.comp (B - lam • A).ker.subtype).range := by
  let W := (angularPair A B).range
  have hW : Module.finrank ℝ W = 4 := by
    rw [LinearMap.finrank_range_of_inj
      (angularPair_injective_of_finiteCenters A B a a hA hB hinj)]
    exact hdim
  have hsurj₁ : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range A a hA ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  have hsurj₂ : Function.Surjective ((LinearMap.snd ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range B a hB ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  obtain ⟨Q, R, hQ, hR, hkernel⟩ := four_dimensional_two_body_quotient W hW hsurj₁ hsurj₂
  obtain ⟨O, hOdense, hpin⟩ := exists_dense_finiteCenters_angular_common_pins
    A B hdim a a hA hB hinj hrank
  have hdet : ∀ p, determinantTwo (Q (p - a)) (R (p - a)) = 0 := by
    apply determinantTwo_eq_zero_of_dense_common_pins Q R a a O hOdense
    intro p hp
    obtain ⟨s, t, hs, ht, hst⟩ := hpin p hp
    change (s • (p - a), t • (p - a)) ∈ W at hst
    rw [hkernel] at hst
    exact ⟨s, t, hs, ht, hst⟩
  obtain ⟨γ, hγ, hRγ, _⟩ := affine_determinantTwo_classification Q R hQ hR a a hdet
  let lam : ℝ := -γ⁻¹
  let D : E →ₗ[ℝ] Twist := B - lam • A
  have hlam : lam ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hγ)
  have hγlam : γ * lam = -1 := by simp [lam, hγ]
  have hlamγ : lam * γ = -1 := by simp [lam, hγ]
  have hmemA (u : E) : A u ∈ finiteCenterSpace a := by rw [← hA]; exact ⟨u, rfl⟩
  have hmemB (u : E) : B u ∈ finiteCenterSpace a := by rw [← hB]; exact ⟨u, rfl⟩
  have hmemD (u : E) : D u ∈ finiteCenterSpace a :=
    (finiteCenterSpace a).sub_mem (hmemB u) ((finiteCenterSpace a).smul_mem lam (hmemA u))
  have hconstraint (u : E) : Q (A u).1 + γ • Q (B u).1 = 0 := by
    have hm : angularPair A B u ∈ W := ⟨u, rfl⟩
    rw [hkernel] at hm
    change Q (A u).1 + R (B u).1 = 0 at hm
    rw [hRγ, LinearMap.smul_apply] at hm
    exact hm
  have hQD (u : E) : Q (D u).1 = 0 := by
    have hfirst : Q (A u).1 = -(γ • Q (B u).1) := eq_neg_of_add_eq_zero_left (hconstraint u)
    change Q ((B u).1 - lam • (A u).1) = 0
    rw [map_sub, map_smul, hfirst, smul_neg, smul_smul, hlamγ]
    simp
  have hQker : Module.finrank ℝ Q.ker = 1 := by
    have hn := Q.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hQ] at hn
    have hdim₂ : Module.finrank ℝ Vec2 = 2 := by simp [Vec2]
    have hdim₃ : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    rw [finrank_top, hdim₂, hdim₃] at hn
    omega
  let L : D.range →ₗ[ℝ] Q.ker :=
    ((LinearMap.fst ℝ Vec3 Vec3).comp D.range.subtype).codRestrict Q.ker (by
      rintro ⟨X, u, rfl⟩
      exact hQD u)
  have hLinj : Function.Injective L := by
    intro X Y hXY
    apply Subtype.ext
    obtain ⟨u, hu⟩ := X.property
    obtain ⟨v, hv⟩ := Y.property
    apply eq_of_angular_eq_mem_finiteCenter a X.val Y.val
    · rw [← hu]
      exact hmemD u
    · rw [← hv]
      exact hmemD v
    · exact congrArg Subtype.val hXY
  have hDrank : Module.finrank ℝ D.range ≤ 1 := by
    have hh := LinearMap.finrank_le_finrank_of_injective hLinj
    rwa [hQker] at hh
  have hcenter : finiteCenterSpace a ≤ (A.comp D.ker.subtype).range := by
    intro X hX
    have hpair : (X.1, lam • X.1) ∈ W := by
      rw [hkernel]
      change Q X.1 + R (lam • X.1) = 0
      rw [hRγ, LinearMap.smul_apply, map_smul, smul_smul, hγlam]
      simp
    obtain ⟨u, hu⟩ := hpair
    change ((A u).1, (B u).1) = (X.1, lam • X.1) at hu
    have huA := congrArg (fun Z : Vec3 × Vec3 => Z.1) hu
    have huB := congrArg (fun Z : Vec3 × Vec3 => Z.2) hu
    have hAu : A u = X :=
      eq_of_angular_eq_mem_finiteCenter a (A u) X (hmemA u) hX huA
    have hBu : B u = lam • X :=
      eq_of_angular_eq_mem_finiteCenter a (B u) (lam • X) (hmemB u)
        ((finiteCenterSpace a).smul_mem lam hX) huB
    have hDu : D u = 0 := by simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, hAu, hBu, sub_self]
    exact ⟨⟨u, hDu⟩, hAu⟩
  have hDne : D ≠ 0 := by
    intro hz
    have hArank : Module.finrank ℝ A.range = 3 := by rw [hA, finrank_finiteCenterSpace]
    have hk : 0 < Module.finrank ℝ A.ker := by
      have hh := A.finrank_range_add_finrank_ker
      omega
    obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A.ker)).mp hk
    have hAu : A u.val = 0 := u.property
    have hBu : B u.val = 0 := by
      have hh := congrArg (fun T : E →ₗ[ℝ] Twist => T u.val) hz
      simpa only [D, LinearMap.sub_apply, LinearMap.smul_apply,
        hAu, smul_zero, sub_zero, LinearMap.zero_apply] using hh
    exact hu (Subtype.ext (hinj (by
      change (A u.val, B u.val) = (A 0, B 0)
      simp only [hAu, hBu, map_zero])))
  exact ⟨lam, hlam, hDne, hDrank, hcenter⟩

end Papers.Rigidity

end
end
end BundleSource0048

section BundleSource0049
/- Source: Papers/RigiditySameCenterMerger.lean -/





@[expose] public section

/-!
# The actual merger for two rank-three bodies with a common center

A nonzero vector in the first projection's kernel is constructed smoothly.
The second angular image of that vector gives the actual discrepancy
axis.  A fixed cross-product coordinate then recovers the pointwise
scalar as a differentiable quotient.  The full center-space distribution
obstruction forces that scalar to be one.  Dense pins consequently force
the two actual twists to agree in every surviving common-pin motion.

The same-center merger supplies the remaining coupled case of Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix CofactorKernel CommonPinLowRank
open scoped Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_differentiable_sameCenter_scalar
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (a : E → Vec3) (x : E)
    (hdim : Module.finrank ℝ E = 4)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hcenters : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (a y))
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective ((θ₁ y).toLinearMap.prod (θ₂ y).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ lam : E → ℝ, DifferentiableAt ℝ lam x ∧
      ∀ᶠ y in 𝓝 x, lam y ≠ 0 ∧ θ₂ y - lam y • θ₁ y ≠ 0 ∧
        Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1 ∧
        finiteCenterSpace (a y) ≤
          ((θ₁ y).toLinearMap.comp (θ₂ y - lam y • θ₁ y).toLinearMap.ker.subtype).range := by
  let A : E → (E →L[ℝ] Vec3) := fun y => angularForm (θ₁ y)
  have hA : DifferentiableAt ℝ A x := (differentiableAt_const (ContinuousLinearMap.fst ℝ Vec3 Vec3)).clm_comp hθ₁
  have hsurj : Function.Surjective (A x) :=
    angular_surjective_of_finiteCenter_range (θ₁ x).toLinearMap (a x) hcenters.self_of_nhds.1
  obtain ⟨v, hv, hvker⟩ := exists_differentiable_kernel_vector A x hdim hA hsurj
  have hfirstzero : ∀ᶠ y in 𝓝 x, θ₁ y (v y) = 0 := by
    filter_upwards [hvker, hcenters] with y hy hcy
    apply eq_of_angular_eq_mem_finiteCenter (a y) (θ₁ y (v y)) 0
    · rw [← hcy.1]
      exact ⟨v y, rfl⟩
    · exact (finiteCenterSpace (a y)).zero_mem
    · exact hy.2
  let d : E → Vec3 := fun y => (θ₂ y (v y)).1
  have hd : DifferentiableAt ℝ d x := (hθ₂.clm_apply hv).fst
  have hdne : d x ≠ 0 := by
    intro hz
    have hsecond : θ₂ x (v x) = 0 := by
      apply eq_of_angular_eq_mem_finiteCenter (a x) (θ₂ x (v x)) 0
      · rw [← hcenters.self_of_nhds.2]
        exact ⟨v x, rfl⟩
      · exact (finiteCenterSpace (a x)).zero_mem
      · exact hz
    exact hvker.self_of_nhds.1 (hinj.self_of_nhds (by
      change (θ₁ x (v x), θ₂ x (v x)) = (θ₁ x 0, θ₂ x 0)
      simp only [hfirstzero.self_of_nhds, hsecond, map_zero]))
  have hcross : ∃ ω : Vec3, d x ⨯₃ ω ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h0 := congrFun (hn ![1, 0, 0]) (2 : Fin 3)
    have h1 := congrFun (hn ![1, 0, 0]) (1 : Fin 3)
    have h2 := congrFun (hn ![0, 1, 0]) (2 : Fin 3)
    simp [cross_apply] at h0 h1 h2
    apply hdne
    funext i
    fin_cases i <;> simp_all
  obtain ⟨ω, hω⟩ := hcross
  obtain ⟨u₀, hu₀⟩ := hsurj ω
  have hcrossvalue : d x ⨯₃ (θ₁ x u₀).1 ≠ 0 := by rwa [← hu₀] at hω
  obtain ⟨j, hj⟩ := not_forall.mp (fun h => hcrossvalue (funext h))
  let f₁ : E → ℝ := fun y => (d y ⨯₃ (θ₁ y u₀).1) j
  let f₂ : E → ℝ := fun y => (d y ⨯₃ (θ₂ y u₀).1) j
  let lam : E → ℝ := fun y => f₂ y / f₁ y
  have hf₁ : DifferentiableAt ℝ f₁ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₁ y u₀).1) x hd
      (hθ₁.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₂ : DifferentiableAt ℝ f₂ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₂ y u₀).1) x hd
      (hθ₂.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₁ne : f₁ x ≠ 0 := hj
  have hprod : DifferentiableAt ℝ (fun y => f₂ y * (f₁ y)⁻¹) x :=
    hf₂.mul (hf₁.inv hf₁ne)
  have hquot : DifferentiableAt ℝ lam x := by
    simpa only [lam, div_eq_mul_inv] using hprod
  refine ⟨lam, hquot, ?_⟩
  filter_upwards [hf₁.continuousAt.eventually_ne hf₁ne,
    hd.continuousAt.eventually_ne hdne, hfirstzero, hcenters, hinj, hrank]
      with y hy hdy hAy hcy hiy hry
  obtain ⟨γ, hγ, hDγne, hDγrank, hDγcenter⟩ :=
    sameCenter_scalar_discrepancy (θ₁ y).toLinearMap (θ₂ y).toLinearMap
      hdim (a y) hcy.1 hcy.2 hiy hry
  let D : E →ₗ[ℝ] Twist := (θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap
  have hDv : D (v y) = θ₂ y (v y) := by
    change θ₂ y (v y) - γ • θ₁ y (v y) = θ₂ y (v y)
    rw [hAy, smul_zero, sub_zero]
  have hDvne : D (v y) ≠ 0 := by
    intro hz
    apply hdy
    exact congrArg Prod.fst (hDv.symm.trans hz)
  have hDrank : Module.finrank ℝ D.range = 1 := by
    have hnonbot : D.range ≠ ⊥ := by
      intro hz
      have hm : D (v y) ∈ D.range := ⟨v y, rfl⟩
      rw [hz] at hm
      exact hDvne hm
    have hlow := Submodule.one_le_finrank_iff.mpr hnonbot
    change Module.finrank ℝ D.range ≤ 1 at hDγrank
    omega
  have hDspan : D.range = Submodule.span ℝ {D (v y)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hDrank ⟨v y, rfl⟩ hDvne
  have hcrossD : d y ⨯₃ (D u₀).1 = 0 := by
    have hm : D u₀ ∈ Submodule.span ℝ {D (v y)} := by rw [← hDspan]; exact ⟨u₀, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
    rw [← hr, hDv]
    change d y ⨯₃ (r • d y) = 0
    rw [map_smul, cross_self, smul_zero]
  have hcoordinate : f₂ y - γ * f₁ y = 0 := by
    have hh := congrFun hcrossD j
    change (d y ⨯₃ ((θ₂ y u₀).1 - γ • (θ₁ y u₀).1)) j = 0 at hh
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hh
    exact hh
  have hlamy : lam y = γ := by
    apply (div_eq_iff hy).mpr
    linarith
  rw [hlamy]
  refine ⟨hγ, ?_, ?_, ?_⟩
  · intro hz
    apply hDγne
    have hh := congrArg ContinuousLinearMap.toLinearMap hz
    change (θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap = 0 at hh
    exact hh
  · change Module.finrank ℝ ((θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap).range ≤ 1
    exact hDγrank
  · change finiteCenterSpace (a y) ≤
      ((θ₁ y).toLinearMap.comp ((θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap).ker.subtype).range
    exact hDγcenter

/-- The actual common-center branch gives equality of the two surviving
twists for an open dense set of new pins.  The first body need not be an
immersion of the four-dimensional configuration chart. -/
theorem actual_sameCenter_dense_pin_merger
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (hdim : Module.finrank ℝ E = 4) (a : E → Vec3)
    (hcenters : ∀ᶠ y in 𝓝 x,
      (A₁.form y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (A₂.form y).toLinearMap.range = finiteCenterSpace (a y))
    (hinj : ∀ᶠ y in 𝓝 x,
      Function.Injective ((A₁.form y).toLinearMap.prod (A₂.form y).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (A₁.form y).toLinearMap (A₂.form y).toLinearMap p).range ≤ 3) :
    ∃ U : Set Vec3, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ u : E,
        evaluateTwist p (A₁.form x u) = 0 → evaluateTwist p (A₂.form x u) = 0 →
          A₂.form x u = A₁.form x u := by
  obtain ⟨lam, hlam, hnear⟩ := exists_differentiable_sameCenter_scalar A₁.form A₂.form a x
    hdim A₁.form_differentiable A₂.form_differentiable hcenters hinj hrank
  have hx := hnear.self_of_nhds
  have hone : lam x = 1 :=
    proportional_center_discrepancy_eq_one A₁ A₂ lam hlam hx.1 hx.2.1
      (hnear.mono fun _ h => h.2.2.1) (Or.inl ⟨a x, hx.2.2.2⟩)
  let D := (A₂.form x - A₁.form x).toLinearMap
  have hD : Module.finrank ℝ D.range ≤ 1 := by
    have hh := hx.2.2.1
    rw [hone, one_smul] at hh
    exact hh
  let U := {p : Vec3 | Function.Injective (restrictEvaluation D.range p)}
  refine ⟨U, isOpen_injective_evaluation D.range,
    dense_injective_evaluation_of_finrank_le_one D.range hD, ?_⟩
  intro p hp u hu₁ hu₂
  let X : D.range := ⟨D u, u, rfl⟩
  have hX : X = 0 := hp (by
    change evaluateTwist p (A₂.form x u - A₁.form x u) = evaluateTwist p 0
    simp only [map_sub, hu₁, hu₂, sub_self, map_zero])
  exact sub_eq_zero.mp (congrArg Subtype.val hX)

end Papers.Rigidity.Calculus

end
end
end BundleSource0049

section BundleSource0050
/- Source: Papers/RigidityRankThreePair.lean -/





@[expose] public section

/-!
# The local four-dimensional chart with two rank-three body images

The center functions are recovered from actual angular frames.  Their
differentiability on a neighborhood is proved by the frame formulas.
The two centers then agree on that neighborhood by the moving-center
Maurer--Cartan argument.  Finally the actual common-center discrepancy
forces equality of the two surviving twists at an open dense set of pins.

Angular surjectivity is stated only at the base point; the separate
projective placement transport produces this finite chart, including for
initial centers at infinity.  This lemma does not transport a Euclidean
configuration fiber through a projective map.

The paired rank-three calculation retains both projective center types.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter CofactorKernel
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem eventually_injective_body_pair
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hinj : Function.Injective ((θ₁ x).toLinearMap.prod (θ₂ x).toLinearMap)) :
    ∀ᶠ y in 𝓝 x,
      Function.Injective ((θ₁ y).toLinearMap.prod (θ₂ y).toLinearMap) := by
  let P : E → (E →L[ℝ] (Twist × Twist)) := fun y => (θ₁ y).prod (θ₂ y)
  have hP : ContinuousAt P x :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp
      (hθ₁.continuousAt.prodMk hθ₂.continuousAt)
  exact hP.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)

/-- This local result has no chosen smooth-center, distribution, or
center-equality premise.  It uses the actual body representations and
the literal joint-pin ranks throughout. -/
theorem actual_rankThree_pair_dense_pin_merger
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (hdim : Module.finrank ℝ E = 4)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hsingular : ∀ᶠ y in 𝓝 x,
      SingularPinSpace (θ₁ y).toLinearMap.range ∧
      SingularPinSpace (θ₂ y).toLinearMap.range)
    (hω₁ : Function.Surjective (angularForm (θ₁ x)))
    (hω₂ : Function.Surjective (angularForm (θ₂ x)))
    (hinj : Function.Injective ((θ₁ x).toLinearMap.prod (θ₂ x).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ U : Set Vec3, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ u : E,
        evaluateTwist p (θ₁ x u) = 0 → evaluateTwist p (θ₂ x u) = 0 →
          θ₂ x u = θ₁ x u := by
  have hd₁ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ θ₁ y := by
    filter_upwards [hactual] with y hy
    obtain ⟨A, hA⟩ := hy.1
    simpa only [hA] using A.form_differentiable
  have hd₂ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ θ₂ y := by
    filter_upwards [hactual] with y hy
    obtain ⟨A, hA⟩ := hy.2
    simpa only [hA] using A.form_differentiable
  have hipair := eventually_injective_body_pair θ₁ θ₂ x
    hd₁.self_of_nhds hd₂.self_of_nhds hinj
  obtain ⟨a, ha⟩ := exists_differentiable_finite_center_locally θ₁ x hd₁
    (hsingular.mono fun _ h => h.1) hω₁
  obtain ⟨b, hb⟩ := exists_differentiable_finite_center_locally θ₂ x hd₂
    (hsingular.mono fun _ h => h.2) hω₂
  have hcenters : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (b y) := by
    filter_upwards [ha, hb] with y hay hby
    exact ⟨hay.2, hby.2⟩
  have heq : ∀ᶠ y in 𝓝 x, a y = b y := by
    filter_upwards [hactual, ha, hb, eventually_eventually_nhds.mpr hcenters,
      eventually_eventually_nhds.mpr hipair, eventually_eventually_nhds.mpr hrank]
        with y hy hay hby hcy hiy hry
    obtain ⟨A₁, hA₁⟩ := hy.1
    obtain ⟨A₂, hA₂⟩ := hy.2
    subst θ₁
    subst θ₂
    exact actual_two_finite_centers_equal A₁ A₂ hdim a b hay.1 hby.1 hcy hiy hry
  have hcommon : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (a y) := by
    filter_upwards [hcenters, heq] with y hcy hey
    exact ⟨hcy.1, by simpa only [hey] using hcy.2⟩
  obtain ⟨A₁, hA₁⟩ := hactual.self_of_nhds.1
  obtain ⟨A₂, hA₂⟩ := hactual.self_of_nhds.2
  subst θ₁
  subst θ₂
  obtain ⟨U, hU, hUdense, hmerge⟩ := actual_sameCenter_dense_pin_merger A₁ A₂ hdim a
    hcommon hipair hrank
  exact ⟨U, hU, hUdense, hmerge⟩

end Papers.Rigidity.Calculus

end
end
end BundleSource0050

section BundleSource0051
/- Source: Papers/RigidityOwnedLocalSingular.lean -/




@[expose] public section

/-!
# Actual singular body images throughout the deleted configuration fiber

The derivative of the chart is an actual grounded bar motion at each
nearby configuration.  Its body image is contained in the original
relative-twist image there.  Genericity is open.  The already derived
global exclusion of rank-four projections consequently supplies singular
images throughout a neighborhood, without assuming body-rank constancy
or imposing an additional center hypothesis.

The singularity statement concerns the actual local body forms.
-/

noncomputable section
namespace Papers.Rigidity

theorem SingularPinSpace.mono {W U : Submodule ℝ Twist}
    (hU : SingularPinSpace U) (hWU : W ≤ U) : SingularPinSpace W := by
  intro p
  have hle : (restrictEvaluation W p).range ≤ (restrictEvaluation U p).range := by
    rintro _ ⟨X, rfl⟩
    exact ⟨⟨X.val, hWU X.property⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (hU p)

namespace VertexPin.IncidentTetrahedra

open BarJoint Calculus Calculus.GroundedConfiguration Filter
open scoped Classical Topology

variable {V B : Type} [Fintype V] [Fintype B] {G : SimpleGraph V} {v : V}
variable (T : IncidentTetrahedra G v B) (p : Placement V 3)
  (hp : GeneralPosition.InGeneralPosition p) (base : B)
variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph G v) (T.triangleEmbedding base))
  (deletedPlacement p v) (T.IncidentGroundedMotions p base))

theorem incidentBodyForm_range_le_relative_eventually (hgen : IsGenericPlacement p) :
    ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      let P := restoreDeletedPlacement v (p v) (C.parametrization y)
      ∃ hgen' : IsGenericPlacement P,
        ∃ hgeom' : GeneralPosition.InGeneralPosition P, ∀ b : B,
          ((T.incidentBodyRepresentation p hp base C b).form y).toLinearMap.range ≤
            (T.relativeTwists P
              (GeneralPosition.InGeneralPosition.incident_noncollinear P hgeom' T) base b).range := by
  let P : T.IncidentGroundedMotions p base → Placement V 3 :=
    fun y => restoreDeletedPlacement v (p v) (C.parametrization y)
  have hP : ContinuousAt P 0 :=
    (continuous_restoreDeletedPlacement v (p v)).continuousAt.comp
      C.smooth_parametrization.continuousAt
  have hP0 : P 0 = p := by simp [P, C.parametrization_zero]
  have hgeneric : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base), IsGenericPlacement (P y) := by
    apply hP.eventually
    rw [hP0]
    exact isOpen_isGenericPlacement.mem_nhds hgen
  have hgeometry : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      GeneralPosition.InGeneralPosition (P y) := by
    apply hP.eventually
    rw [hP0]
    exact GeneralPosition.isOpen_generalPosition.mem_nhds hp
  have hvelocity := bodyRepresentation_velocity (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v)
  have hground := bodyRepresentation_grounded (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v) base (T.triangleEmbedding_mem base)
  filter_upwards [hgeneric, hgeometry, hvelocity, hground,
    C.smooth_parametrization.eventually (by simp),
    eventually_eventually_nhds.mpr C.level] with y hgy hpy hvel hzero hsmooth hlevel
  refine ⟨hgy, hpy, ?_⟩
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear (P y) hpy T
  let F : T.IncidentGroundedMotions p base →ₗ[ℝ] DeletedMotions G (P y) v :=
    (fderiv ℝ C.parametrization y).toLinearMap.codRestrict _ (by
      intro u
      have hu := derivative_mem_groundedMotions (deletedGraph G v) (T.triangleEmbedding base)
        (deletedPlacement p v) C.parametrization y u
        (hsmooth.differentiableAt (by norm_num)) hlevel
      change (fderiv ℝ C.parametrization y) u ∈
        (rigidityOperator (deletedGraph G v)
          (deletedPlacement (restoreDeletedPlacement v (p v) (C.parametrization y)) v)).ker
      rw [deletedPlacement_restore]
      exact hu.1)
  have htwist (b : B) (u : T.IncidentGroundedMotions p base) :
      T.bodyTwist (P y) hn b (F u) =
        (T.incidentBodyRepresentation p hp base C b).form y u := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (T.trianglePoints (P y) b) (hn b)
    intro i
    rw [map_sub, sub_eq_zero, T.bodyTwist_fit]
    have hv := hvel u b (T.triangle b i) (T.triangleEmbedding_mem b i)
    simpa only [F, LinearMap.codRestrict_apply, ContinuousLinearMap.coe_coe,
      P, trianglePoints, restoreDeletedPlacement_other, incidentBodyRepresentation] using hv
  intro b X hX
  obtain ⟨u, rfl⟩ := hX
  refine ⟨F u, ?_⟩
  change T.bodyTwist (P y) hn b (F u) - T.bodyTwist (P y) hn base (F u) = _
  rw [htwist, htwist]
  change (T.incidentBodyRepresentation p hp base C b).form y u -
      (T.incidentBodyRepresentation p hp base C base).form y u =
    (T.incidentBodyRepresentation p hp base C b).form y u
  have hbase : (T.incidentBodyRepresentation p hp base C base).form y u = 0 := hzero u
  rw [hbase, sub_zero]

end VertexPin.IncidentTetrahedra

open BarJoint VertexPin Calculus Filter
open scoped Classical Topology

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_owned_body_singular_eventually
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (hne : b.owner ≠ base.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    ∀ᶠ y in 𝓝 (0 : (ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base),
      SingularPinSpace
        (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form y).toLinearMap.range := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  filter_upwards [T.incidentBodyForm_range_le_relative_eventually p hp base C hgen] with y hy
  obtain ⟨hgy, hpy, hle⟩ := hy
  let P := restoreDeletedPlacement v (p v) (C.parametrization y)
  have hlow := Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v P hgy hpy base b hne
  have hhigh := M.hypervertex_relative_rank_le_three v hh hdrop P hgy hpy base b
  have hdim := Nat.le_antisymm hhigh hlow
  exact (Papers.Rigidity.VertexPin.MinimalCounterexample.owned_rankThree_singular M v P hgy hpy base b hne hdim).mono (hle b)

end Papers.Rigidity

end
end
end BundleSource0051

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0051/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0051.json"

section BundleSource0052
/- Source: Papers/RigidityIncidentPairSelection.lean -/



@[expose] public section

/-!
# Selecting the genuine coupled pair from the incident body map

On a four-dimensional tangent space a rank-three projection has a
one-dimensional kernel.  Joint injectivity of all actual incident-body
forms supplies a second projection nonzero on that kernel.  The paired
projection is therefore injective.  Maximal-owner equality is excluded
using the already proved actual twist dictionary.

The selected pair retains its original maximal-body owners.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical

theorem exists_injective_pair_of_rank_three
    {E B : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : B → E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4)
    (hinj : Function.Injective (LinearMap.pi A)) (b : B)
    (hb : Module.finrank ℝ (A b).range = 3) :
    ∃ c : B, ∃ u : E, u ≠ 0 ∧ A b u = 0 ∧ A c u ≠ 0 ∧
      Function.Injective ((A b).prod (A c)) := by
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := Twist) (A b)
  have hkdim : Module.finrank ℝ (A b).ker = 1 := by omega
  have hpositive : 0 < Module.finrank ℝ (A b).ker := by omega
  obtain ⟨u, hu⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := (A b).ker)).mp hpositive
  have hune : (u : E) ≠ 0 := fun hz => hu (Subtype.ext hz)
  have hAu : A b (u : E) = 0 := u.property
  have hex : ∃ c, A c (u : E) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hune
    apply hinj
    funext c
    simpa only [LinearMap.pi_apply, map_zero] using hn c
  obtain ⟨c, hc⟩ := hex
  have hspan : (A b).ker = Submodule.span ℝ {(u : E)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hkdim u.property hune
  refine ⟨c, u, hune, hAu, hc, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    have hz0 := LinearMap.mem_ker.mp hz
    have hbz : A b z = 0 := congrArg Prod.fst hz0
    have hcz : A c z = 0 := congrArg Prod.snd hz0
    have hzm : z ∈ Submodule.span ℝ {(u : E)} := by
      rw [← hspan]
      exact hbz
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hzm
    have hrzero : r = 0 := by
      have h : r • A c (u : E) = 0 := by rw [← map_smul, hr, hcz]
      exact (smul_eq_zero.mp h).resolve_right hc
    change z = 0
    rw [← hr, hrzero, zero_smul]
  · exact bot_le

namespace VertexPin.IncidentTetrahedra

variable {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}

theorem owned_incident_forms_eq_of_owner_eq (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (base b c : OwnedIncidentTriangle G v)
    (hbc : b.owner = c.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph G v)
        ((ownedIncidentTetrahedra G v hG).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra G v hG).IncidentGroundedMotions p base)) :
    ((ownedIncidentTetrahedra G v hG).incidentBodyRepresentation p hp base C b).form 0 =
      ((ownedIncidentTetrahedra G v hG).incidentBodyRepresentation p hp base C c).form 0 := by
  let T := ownedIncidentTetrahedra G v hG
  apply ContinuousLinearMap.ext
  intro u
  rw [T.incidentBodyForm_at_zero, T.incidentBodyForm_at_zero]
  exact owned_bodyTwist_eq_of_owner_eq hG p hp b c hbc (T.groundedDeletedInclusion p base u)

end VertexPin.IncidentTetrahedra

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_select_injective_pair
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (hbbase : b.owner ≠ base.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    ∃ c : OwnedIncidentTriangle M.graph v, c.owner ≠ base.owner ∧ c.owner ≠ b.owner ∧
      Function.Injective
        ((((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0).toLinearMap.prod
          (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0).toLinearMap) := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let A := fun c : OwnedIncidentTriangle M.graph v =>
    ((T.incidentBodyRepresentation p hp base C c).form 0).toLinearMap
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 4 := by
    have h := M.grounded_incident_finrank v T p hgen hp base
    omega
  have hall : Function.Injective (LinearMap.pi A) :=
    T.incidentBodyFormOperator_injective p hp base C hgen
      (M.neighborCompletion_isGenericallyRigid v)
  have hlow : 3 ≤ Module.finrank ℝ (A b).range := by
    rw [show (A b).range = (T.relativeTwists p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) base b).range from
      T.incidentBodyForm_range_at_zero p hp base C b]
    exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v p hgen hp base b hbbase
  have hhigh := M.hypervertex_bodyForm_rank_le_three v hh hdrop p hgen hp base b C
  obtain ⟨c, u, hu, hbu, hcu, hpair⟩ := exists_injective_pair_of_rank_three A hE hall b
    (Nat.le_antisymm hhigh hlow)
  refine ⟨c, ?_, ?_, hpair⟩
  · intro hcbase
    have he := IncidentTetrahedra.owned_incident_forms_eq_of_owner_eq M.covered p hp
      base c base hcbase C
    apply hcu
    change (T.incidentBodyRepresentation p hp base C c).form 0 u = 0
    rw [he, T.incidentBodyForm_at_zero, T.bodyTwist_grounded_base]
  · intro hcb
    have he := IncidentTetrahedra.owned_incident_forms_eq_of_owner_eq M.covered p hp
      base c b hcb C
    apply hcu
    change (T.incidentBodyRepresentation p hp base C c).form 0 u = 0
    rw [he]
    exact hbu

end Papers.Rigidity

end
end
end BundleSource0052

section BundleSource0053
/- Source: Papers/RigidityProjectiveTransport.lean -/




@[expose] public section

/-!
# Actual projective transport of bar velocities and virtual centers

The special projective transformation used here is
`p ↦ p / (1 + c · p)`.  Its velocity transport is not the derivative of
that map: it is the contragredient transport appropriate to the bar
equations.  Every equation is multiplied by an explicit nonzero edge
factor, and the motion-kernel equivalence is constructed in both
directions.  The twist and homogeneous-center maps are genuine linear
equivalences, including for centers at infinity.

This module supplies the change of placement made before choosing a
Euclidean length fiber in Section 4. It does not transport an existing
Euclidean configuration manifold.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open Matrix BarJoint
open scoped Matrix

def denominator (c p : Vec3) : ℝ := 1 + c ⬝ᵥ p

def point (c p : Vec3) : Vec3 := (denominator c p)⁻¹ • p

def velocity (c p : Vec3) : Vec3 →ₗ[ℝ] Vec3 :=
  (denominator c p)⁻¹ •
    ((LinearMap.id : Vec3 →ₗ[ℝ] Vec3) + (dotProductBilin ℝ ℝ p).smulRight c)

@[simp] theorem velocity_apply (c p u : Vec3) :
    velocity c p u = (denominator c p)⁻¹ • (u + (p ⬝ᵥ u) • c) := rfl

theorem denominator_inverse (c p : Vec3) (hp : denominator c p ≠ 0) :
    denominator (-c) (point c p) = (denominator c p)⁻¹ := by
  simp only [denominator, point, neg_dotProduct, dotProduct_smul, smul_eq_mul] at *
  field_simp
  ring

theorem denominator_inverse_ne_zero (c p : Vec3) (hp : denominator c p ≠ 0) :
    denominator (-c) (point c p) ≠ 0 := by
  rw [denominator_inverse c p hp]
  exact inv_ne_zero hp

theorem point_inverse (c p : Vec3) (hp : denominator c p ≠ 0) :
    point (-c) (point c p) = p := by
  rw [point, denominator_inverse c p hp, inv_inv, point, smul_smul,
    mul_inv_cancel₀ hp, one_smul]

theorem velocity_inverse (c p u : Vec3) (hp : denominator c p ≠ 0) :
    velocity (-c) (point c p) (velocity c p u) = u := by
  rw [velocity_apply, denominator_inverse c p hp, inv_inv, velocity_apply]
  ext i
  simp only [point, Pi.smul_apply, Pi.add_apply, Pi.neg_apply,
    smul_eq_mul, dotProduct, Fin.sum_univ_succ]
  dsimp [denominator] at hp ⊢
  field_simp
  norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

/-- Each pointwise velocity map is invertible on its actual affine chart. -/
def velocityEquiv (c p : Vec3) (hp : denominator c p ≠ 0) : Vec3 ≃ₗ[ℝ] Vec3 where
  toLinearMap := velocity c p
  invFun := velocity (-c) (point c p)
  left_inv := fun u => velocity_inverse c p u hp
  right_inv := by
    intro u
    have hh := velocity_inverse (-c) (point c p) u (denominator_inverse_ne_zero c p hp)
    rw [neg_neg, point_inverse c p hp] at hh
    exact hh

/-- The literal transported twist; this is the alternating-matrix
congruence in the special projective chart. -/
def twistEquiv (c : Vec3) : Twist ≃ₗ[ℝ] Twist where
  toFun X := (X.1 + X.2 ⨯₃ c, X.2)
  invFun X := (X.1 - X.2 ⨯₃ c, X.2)
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    · rfl
  map_smul' a X := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    · rfl

def centerEquiv (c : Vec3) : HomogeneousPoint ≃ₗ[ℝ] HomogeneousPoint where
  toFun q := (q.1, q.2 + c ⬝ᵥ q.1)
  invFun q := (q.1, q.2 - c ⬝ᵥ q.1)
  left_inv q := by simp
  right_inv q := by simp
  map_add' q r := by simp [dotProduct_add, add_assoc, add_left_comm, add_comm]
  map_smul' a q := by simp [dotProduct_smul, smul_add] <;> ring

def covectorEquiv (c : Vec3) : HomogeneousPoint ≃ₗ[ℝ] HomogeneousPoint where
  toFun q := (q.1 - q.2 • c, q.2)
  invFun q := (q.1 + q.2 • c, q.2)
  left_inv q := by simp
  right_inv q := by simp
  map_add' q r := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · rfl
  map_smul' a q := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_smul,
        RingHom.id_apply, smul_eq_mul]
    · rfl

/-- The fourth contraction coordinate is retained.  It is exactly the
orthogonality equation needed to transport a center at infinity. -/
theorem homogeneousEvaluation_transport (c : Vec3) (q : HomogeneousPoint) (X : Twist) :
    homogeneousEvaluation (centerEquiv c q) (twistEquiv c X) =
      covectorEquiv c (homogeneousEvaluation q X) := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [homogeneousEvaluation_apply, centerEquiv, twistEquiv, covectorEquiv,
        cross_apply, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ] <;> ring
  · simp [homogeneousEvaluation_apply, centerEquiv, twistEquiv, covectorEquiv]

theorem homogeneousEvaluation_transport_eq_zero_iff
    (c : Vec3) (q : HomogeneousPoint) (X : Twist) :
    homogeneousEvaluation (centerEquiv c q) (twistEquiv c X) = 0 ↔
      homogeneousEvaluation q X = 0 := by
  rw [homogeneousEvaluation_transport]
  exact (covectorEquiv c).map_eq_zero_iff

theorem centerSpace_map (c : Vec3) (q : HomogeneousPoint) :
    (homogeneousCenterSpace q).map (twistEquiv c).toLinearMap =
      homogeneousCenterSpace (centerEquiv c q) := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (homogeneousEvaluation_transport_eq_zero_iff c q X).mpr hX
  · intro hY
    refine ⟨(twistEquiv c).symm Y, ?_, by simp⟩
    apply (homogeneousEvaluation_transport_eq_zero_iff c q ((twistEquiv c).symm Y)).mp
    rw [LinearEquiv.apply_symm_apply]
    exact hY

/-- A transported body twist evaluates to the transported bar velocity. -/
theorem evaluateTwist_transport (c p : Vec3) (hp : denominator c p ≠ 0) (X : Twist) :
    evaluateTwist (point c p) (twistEquiv c X) = velocity c p (evaluateTwist p X) := by
  ext i
  fin_cases i <;>
    simp [evaluateTwist_apply, twistEquiv, point, velocity_apply, cross_apply,
      Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ] <;>
    dsimp [denominator] at hp ⊢ <;> field_simp <;>
    norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

/-- Exact scaling of an arbitrary bar equation, before any graph or rank
condition is imposed. -/
theorem bar_constraint_transport (c p q u v : Vec3)
    (hp : denominator c p ≠ 0) (hq : denominator c q ≠ 0) :
    (point c p - point c q) ⬝ᵥ (velocity c p u - velocity c q v) =
      (denominator c p * denominator c q)⁻¹ * ((p - q) ⬝ᵥ (u - v)) := by
  simp only [point, velocity_apply, dotProduct, Fin.sum_univ_succ,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [denominator] at hp hq ⊢
  field_simp
  norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

variable {V : Type}

def placement (c : Vec3) (p : Placement V 3) : Placement V 3 := fun v => point c (p v)

def placementVelocity (c : Vec3) (p : Placement V 3) :
    Velocity V 3 →ₗ[ℝ] Velocity V 3 :=
  LinearMap.pi fun v => (velocity c (p v)).comp (LinearMap.proj v)

@[simp] theorem placementVelocity_apply (c : Vec3) (p : Placement V 3)
    (u : Velocity V 3) (v : V) : placementVelocity c p u v = velocity c (p v) (u v) := rfl

theorem edgeConstraint_transport (c : Vec3) (p : Placement V 3) (u : Velocity V 3)
    (hp : ∀ v, denominator c (p v) ≠ 0) (v w : V) :
    edgeConstraint (placement c p) (placementVelocity c p u) v w =
      (denominator c (p v) * denominator c (p w))⁻¹ * edgeConstraint p u v w :=
  bar_constraint_transport c (p v) (p w) (u v) (u w) (hp v) (hp w)

theorem isInfinitesimalMotion_transport_iff (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0) (u : Velocity V 3) :
    IsInfinitesimalMotion G (placement c p) (placementVelocity c p u) ↔
      IsInfinitesimalMotion G p u := by
  rw [isInfinitesimalMotion_iff, isInfinitesimalMotion_iff]
  simp only [edgeConstraint_transport c p u hp,
    mul_eq_zero, inv_eq_zero, mul_eq_zero, hp, false_or]

def motionKernelEquiv (G : SimpleGraph V) (c : Vec3) (p : Placement V 3)
    (hp : ∀ v, denominator c (p v) ≠ 0) :
    (rigidityOperator G p).ker ≃ₗ[ℝ] (rigidityOperator G (placement c p)).ker where
  toFun u := ⟨placementVelocity c p u.val,
    (isInfinitesimalMotion_transport_iff G c p hp u.val).mpr u.property⟩
  invFun u := ⟨placementVelocity (-c) (placement c p) u.val, by
    have hh := (isInfinitesimalMotion_transport_iff G (-c) (placement c p)
      (fun v => denominator_inverse_ne_zero c (p v) (hp v)) u.val).mpr u.property
    have hpoint : placement (-c) (placement c p) = p := by
      funext v
      exact point_inverse c (p v) (hp v)
    rw [hpoint] at hh
    exact hh⟩
  left_inv u := by
    apply Subtype.ext
    funext v
    exact velocity_inverse c (p v) (u.val v) (hp v)
  right_inv u := by
    apply Subtype.ext
    funext v
    have hh := velocity_inverse (-c) (point c (p v)) (u.val v)
      (denominator_inverse_ne_zero c (p v) (hp v))
    rw [neg_neg, point_inverse c (p v) (hp v)] at hh
    exact hh
  map_add' u w := Subtype.ext (map_add _ _ _)
  map_smul' a u := Subtype.ext (map_smul _ _ _)

/-- Projective transport preserves the actual rank of every graph on
the given vertex set, with no genericity hypothesis. -/
theorem rigidityRank_transport [Fintype V] (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0) :
    rigidityRank G (placement c p) = rigidityRank G p := by
  have hk := (motionKernelEquiv G c p hp).finrank_eq
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity V 3) (V₂ := V × V → ℝ) (rigidityOperator G p)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity V 3) (V₂ := V × V → ℝ)
    (rigidityOperator G (placement c p))
  change Module.finrank ℝ (rigidityOperator G (placement c p)).range =
    Module.finrank ℝ (rigidityOperator G p).range
  omega

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0053

section BundleSource0054
/- Source: Papers/RigidityFiniteProjectiveChart.lean -/




@[expose] public section

/-!
# A finite chart for finitely many actual virtual centers

The allowed special projective transformations contain arbitrarily small
parameters making any finite family of nonzero homogeneous centers finite.
All actual vertices remain finite as well.  The construction uses an open
dense intersection of genuine affine rank conditions; it assumes no
genericity of the virtual centers themselves.

Together with the exact rank transport, this permits choosing a new
placement before constructing its own Euclidean length fiber.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open Matrix BarJoint Filter
open scoped Matrix Topology

def heightConstant (q : HomogeneousPoint) : ℝ →ₗ[ℝ] ℝ :=
  q.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

def heightLinear (q : HomogeneousPoint) : Vec3 →ₗ[ℝ] (ℝ →ₗ[ℝ] ℝ) :=
  (dotProductBilin ℝ ℝ q.1).smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

theorem heightFamily_apply (q : HomogeneousPoint) (c : Vec3) (r : ℝ) :
    AffineRank.family (heightConstant q) (heightLinear q) c r =
      (centerEquiv c q).2 * r := by
  change q.2 * r + (q.1 ⬝ᵥ c) * r = (q.2 + c ⬝ᵥ q.1) * r
  rw [dotProduct_comm q.1 c]
  ring

theorem height_rank_iff (q : HomogeneousPoint) (c : Vec3) :
    1 ≤ AffineRank.rankAt (heightConstant q) (heightLinear q) c ↔
      (centerEquiv c q).2 ≠ 0 := by
  by_cases h : (centerEquiv c q).2 = 0
  · have hzero : AffineRank.family (heightConstant q) (heightLinear q) c = 0 := by
      ext r
      simp only [heightFamily_apply, h, zero_mul, LinearMap.zero_apply]
    simp [AffineRank.rankAt, hzero, h]
  · have hinj : Function.Injective (AffineRank.family (heightConstant q) (heightLinear q) c) := by
      intro r s hrs
      rw [heightFamily_apply, heightFamily_apply] at hrs
      exact mul_left_cancel₀ h hrs
    have hrank : AffineRank.rankAt (heightConstant q) (heightLinear q) c = 1 := by
      rw [AffineRank.rankAt, LinearMap.finrank_range_of_inj hinj]
      simp
    simp [hrank, h]

theorem exists_nonzero_center_height (q : HomogeneousPoint) (hq : q ≠ 0) :
    ∃ c : Vec3, (centerEquiv c q).2 ≠ 0 := by
  by_cases hs : q.2 = 0
  · have ha : q.1 ≠ 0 := fun h => hq (Prod.ext h hs)
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => ha (funext h))
    refine ⟨Pi.single i 1, ?_⟩
    change q.2 + Pi.single i 1 ⬝ᵥ q.1 ≠ 0
    rw [hs, zero_add, single_one_dotProduct]
    exact hi
  · exact ⟨0, by simpa [centerEquiv] using hs⟩

theorem isOpen_nonzero_center_height (q : HomogeneousPoint) :
    IsOpen {c : Vec3 | (centerEquiv c q).2 ≠ 0} := by
  have h := AffineRank.isOpen_setOf_le_rankAt (heightConstant q) (heightLinear q) 1
  simpa only [height_rank_iff] using h

theorem dense_nonzero_center_height (q : HomogeneousPoint) (hq : q ≠ 0) :
    Dense {c : Vec3 | (centerEquiv c q).2 ≠ 0} := by
  have hw : ∃ c, 1 ≤ AffineRank.rankAt (heightConstant q) (heightLinear q) c := by
    obtain ⟨c, hc⟩ := exists_nonzero_center_height q hq
    exact ⟨c, (height_rank_iff q c).mpr hc⟩
  have h := AffineRank.dense_setOf_le_rankAt (heightConstant q) (heightLinear q) 1 hw
  simpa only [height_rank_iff] using h

/-- Every nonempty open set of chart parameters contains one making the
whole finite family of nonzero homogeneous points finite. -/
theorem exists_finite_chart_in_open
    {I : Type*} [Finite I] (q : I → HomogeneousPoint) (hq : ∀ i, q i ≠ 0)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ c ∈ O, ∀ i, (centerEquiv c (q i)).2 ≠ 0 := by
  have hdense : Dense (⋂ i : I, {c : Vec3 | (centerEquiv c (q i)).2 ≠ 0}) :=
    dense_iInter_of_isOpen (fun i => isOpen_nonzero_center_height (q i))
      (fun i => dense_nonzero_center_height (q i) (hq i))
  obtain ⟨c, hc, hcO⟩ := hdense.exists_mem_open hO hne
  exact ⟨c, hcO, Set.mem_iInter.mp hc⟩

theorem point_continuousAt_zero (p : Vec3) :
    ContinuousAt (fun c : Vec3 => point c p) 0 := by
  have hden : Continuous (fun c : Vec3 => denominator c p) := by
    exact continuous_const.add ((dotProductBilin ℝ ℝ p).continuous_of_finiteDimensional.congr
      (fun c => dotProduct_comm p c))
  have hnonzero : denominator 0 p ≠ 0 := by simp [denominator]
  exact (hden.continuousAt.inv₀ hnonzero).smul continuousAt_const

theorem placement_continuousAt_zero {V : Type} (p : Placement V 3) :
    ContinuousAt (fun c : Vec3 => placement c p) 0 :=
  continuousAt_pi.mpr fun v => point_continuousAt_zero (p v)

@[simp] theorem placement_zero {V : Type} (p : Placement V 3) : placement 0 p = p := by
  funext v
  simp [placement, point, denominator]

/-- Actual vertices and finitely many virtual centers are simultaneously
finite after a transformation arbitrarily close to the original placement.
The open neighborhood can encode every required general-position condition. -/
theorem exists_finite_chart_preserving_neighborhood
    {V I : Type} [Finite V] [Finite I]
    (p : Placement V 3) (q : I → HomogeneousPoint) (hq : ∀ i, q i ≠ 0)
    (U : Set (Placement V 3)) (hU : U ∈ 𝓝 p) :
    ∃ c : Vec3, placement c p ∈ U ∧
      (∀ v, denominator c (p v) ≠ 0) ∧
      ∀ i, (centerEquiv c (q i)).2 ≠ 0 := by
  let r : V ⊕ I → HomogeneousPoint := Sum.elim (fun v => (p v, 1)) q
  have hr : ∀ j, r j ≠ 0 := by
    intro j
    cases j with
    | inl v => simp [r]
    | inr i => exact hq i
  have hpre : (fun c : Vec3 => placement c p) ⁻¹' U ∈ 𝓝 (0 : Vec3) := by
    apply (placement_continuousAt_zero p).preimage_mem_nhds
    simpa only [placement_zero] using hU
  obtain ⟨O, hOsub, hOopen, hzero⟩ := mem_nhds_iff.mp hpre
  obtain ⟨c, hcO, hc⟩ := exists_finite_chart_in_open r hr O hOopen ⟨0, hzero⟩
  refine ⟨c, hOsub hcO, ?_, ?_⟩
  · intro v
    exact hc (Sum.inl v)
  · intro i
    exact hc (Sum.inr i)

/-- Every maximal-rank condition is preserved by the same actual
transport. This conclusion holds for each graph on the vertex set. -/
theorem genericRank_preserved {V : Type} [Fintype V] (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0)
    (hgeneric : rigidityRank G p = genericRigidityRank G 3) :
    rigidityRank G (placement c p) = genericRigidityRank G 3 := by
  rw [rigidityRank_transport G c p hp]
  exact hgeneric

/-- The simultaneous genericity used in the graph proof is preserved for
all graphs, rather than only for the particular graph currently studied. -/
theorem genericPlacement_preserved {V : Type} [Fintype V] (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0)
    (hgeneric : IsGenericPlacement p) : IsGenericPlacement (placement c p) := by
  intro G
  exact genericRank_preserved G c p hp (hgeneric G)

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0054

section BundleSource0055
/- Source: Papers/RigidityProjectiveBodies.lean -/




@[expose] public section

/-!
# Projective transport of the graph's actual extracted body twists

The triangle extraction maps come from the deleted graph's bar motions.
Their transport is proved by uniqueness on the same three actual body
vertices.  Hence relative-twist images, their projective centers, and
equality of bodies transport through literal linear equivalences.

The two noncollinearity hypotheses are retained explicitly here.  In the
chart-selection application they are provided by the open neighborhood
of the original general-position placement.  No body-motion space is
postulated independently of the graph.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open BarJoint VertexPin

variable {V B : Type} [Fintype V] [Fintype B]
variable {G : SimpleGraph V} {v : V}

def deletedMotionEquiv (G : SimpleGraph V) (v : V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0) :
    DeletedMotions G p v ≃ₗ[ℝ] DeletedMotions G (placement c p) v :=
  motionKernelEquiv (deletedGraph G v) c (deletedPlacement p v) (fun w => hp w.val)

@[simp] theorem deletedMotionEquiv_apply (c : Vec3) (p : Placement V 3)
    (hp : ∀ w, denominator c (p w) ≠ 0) (u : DeletedMotions G p v)
    (w : DeletedVertex v) :
    (deletedMotionEquiv G v c p hp u).val w = velocity c (p w.val) (u.val w) := rfl

theorem bodyTwist_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (b : B) (u : DeletedMotions G p v) :
    T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u) =
      twistEquiv c (T.bodyTwist p hn b u) := by
  apply triangleTwistOperator_injective (T.trianglePoints (placement c p) b) (hn' b)
  funext ij
  change evaluateTwist (T.trianglePoints (placement c p) b ij.1)
      (T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u)) ij.2 =
    evaluateTwist (point c (T.trianglePoints p b ij.1))
      (twistEquiv c (T.bodyTwist p hn b u)) ij.2
  rw [T.bodyTwist_fit,
    evaluateTwist_transport c (T.trianglePoints p b ij.1) (hp (T.triangle b ij.1).val),
    T.bodyTwist_fit]
  rfl

theorem relativeTwists_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) (u : DeletedMotions G p v) :
    T.relativeTwists (placement c p) hn' base b (deletedMotionEquiv G v c p hp u) =
      twistEquiv c (T.relativeTwists p hn base b u) := by
  change T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u) -
      T.bodyTwist (placement c p) hn' base (deletedMotionEquiv G v c p hp u) =
    twistEquiv c (T.bodyTwist p hn b u - T.bodyTwist p hn base u)
  rw [bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', map_sub]

/-- The whole relative-twist image transforms, including motions in the
kernel of individual body projections. -/
theorem relativeTwists_range_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) :
    (T.relativeTwists (placement c p) hn' base b).range =
      (T.relativeTwists p hn base b).range.map (twistEquiv c).toLinearMap := by
  ext X
  constructor
  · rintro ⟨u, rfl⟩
    let u₀ := (deletedMotionEquiv G v c p hp).symm u
    refine ⟨T.relativeTwists p hn base b u₀, ⟨u₀, rfl⟩, ?_⟩
    change twistEquiv c (T.relativeTwists p hn base b u₀) =
      T.relativeTwists (placement c p) hn' base b u
    rw [← relativeTwists_transport T c p hp hn hn']
    simp only [u₀, LinearEquiv.apply_symm_apply]
  · rintro ⟨Y, ⟨u, rfl⟩, rfl⟩
    refine ⟨deletedMotionEquiv G v c p hp u, ?_⟩
    exact relativeTwists_transport T c p hp hn hn' base b u

theorem relative_center_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) (q : HomogeneousPoint)
    (hq : (T.relativeTwists p hn base b).range = homogeneousCenterSpace q) :
    (T.relativeTwists (placement c p) hn' base b).range =
      homogeneousCenterSpace (centerEquiv c q) := by
  rw [relativeTwists_range_transport T c p hp hn hn', hq, centerSpace_map]

/-- Equality or inequality of two body projections in all deleted
motions is retained; the transport introduces no merger assumption. -/
theorem body_agreement_transport_iff (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (b₁ b₂ : B) :
    (∀ u : DeletedMotions G (placement c p) v,
      T.bodyTwist (placement c p) hn' b₁ u = T.bodyTwist (placement c p) hn' b₂ u) ↔
    (∀ u : DeletedMotions G p v, T.bodyTwist p hn b₁ u = T.bodyTwist p hn b₂ u) := by
  constructor
  · intro h u
    apply (twistEquiv c).injective
    rw [← bodyTwist_transport T c p hp hn hn', ← bodyTwist_transport T c p hp hn hn']
    exact h _
  · intro h u
    obtain ⟨u₀, rfl⟩ := (deletedMotionEquiv G v c p hp).surjective u
    rw [bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', h]

theorem restrictFullMotion_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (u : (rigidityOperator G p).ker) :
    T.restrictFullMotion (placement c p) (motionKernelEquiv G c p hp u) =
      deletedMotionEquiv G v c p hp (T.restrictFullMotion p u) := by
  apply Subtype.ext
  rfl

/-- The no-merger condition used for the surviving flex of the original
graph transports through the full graph kernel, not just its deletion. -/
theorem body_agreement_on_full_motions_transport_iff
    (T : IncidentTetrahedra G v B) (c : Vec3) (p : Placement V 3)
    (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p)) (b₁ b₂ : B) :
    (∀ u : (rigidityOperator G (placement c p)).ker,
      T.bodyTwist (placement c p) hn' b₁ (T.restrictFullMotion (placement c p) u) =
        T.bodyTwist (placement c p) hn' b₂ (T.restrictFullMotion (placement c p) u)) ↔
    (∀ u : (rigidityOperator G p).ker,
      T.bodyTwist p hn b₁ (T.restrictFullMotion p u) =
        T.bodyTwist p hn b₂ (T.restrictFullMotion p u)) := by
  constructor
  · intro h u
    have hh := h (motionKernelEquiv G c p hp u)
    rw [restrictFullMotion_transport T c p hp,
      bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn'] at hh
    exact (twistEquiv c).injective hh
  · intro h u
    obtain ⟨u₀, rfl⟩ := (motionKernelEquiv G c p hp).surjective u
    rw [restrictFullMotion_transport T c p hp,
      bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', h]

/-- The finite-center reduction for any finite family of the graph's
actual singular relative-body images.  Infinite centers are included in
the input classification and are made finite by the constructed change
of placement.  Genericity and general position refer to the new placement
on which its own length fiber may subsequently be built. -/
theorem exists_generic_placement_with_finite_relative_centers
    {I : Type} [Finite I] (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hgeneric : IsGenericPlacement p)
    (hgeom : GeneralPosition.InGeneralPosition p) (base : B) (b : I → B)
    (hsingular : ∀ i, SingularPinSpace
      (T.relativeTwists p (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T)
        base (b i)).range)
    (hdim : ∀ i, 3 ≤ Module.finrank ℝ
      (T.relativeTwists p (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T)
        base (b i)).range) :
    ∃ c : Vec3, (∀ w, denominator c (p w) ≠ 0) ∧
      IsGenericPlacement (placement c p) ∧
      ∃ hgeom' : GeneralPosition.InGeneralPosition (placement c p),
        ∀ i, ∃ a : Vec3,
          (T.relativeTwists (placement c p)
            (GeneralPosition.InGeneralPosition.incident_noncollinear (placement c p) hgeom' T)
            base (b i)).range = finiteCenterSpace a := by
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T
  have hex (i : I) : ∃ q : HomogeneousPoint, q ≠ 0 ∧
      (T.relativeTwists p hn base (b i)).range = homogeneousCenterSpace q := by
    obtain ⟨q, hq, hWq, _⟩ := singularPinSpace_unique_projective_center
      (T.relativeTwists p hn base (b i)).range (hsingular i) (hdim i)
    exact ⟨q, hq, hWq⟩
  choose q hq hWq using hex
  obtain ⟨c, hgeom', hc, hfinite⟩ := exists_finite_chart_preserving_neighborhood
    p q hq {p' | GeneralPosition.InGeneralPosition p'}
      (GeneralPosition.isOpen_generalPosition.mem_nhds hgeom)
  refine ⟨c, hc, genericPlacement_preserved c p hc hgeneric, hgeom', ?_⟩
  intro i
  refine ⟨(centerEquiv c (q i)).2⁻¹ • (centerEquiv c (q i)).1, ?_⟩
  rw [relative_center_transport T c p hc hn
    (GeneralPosition.InGeneralPosition.incident_noncollinear (placement c p) hgeom' T)
      base (b i) (q i) (hWq i)]
  exact homogeneousCenterSpace_normalize _ (hfinite i)

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0055

section BundleSource0056
/- Source: Papers/RigidityHypervertexDeletion.lean -/




@[expose] public section

/-!
# The complete intended hypervertex deletion bound

This assembles the actual graph and differential arguments for
Proposition 4.1.  In the four-dimensional case rank-four projections
have already been excluded at every generic placement.  Every remaining
nonreference maximal body has a three-dimensional singular image.  One
fixed projective placement change makes all finitely many such centers
finite.  The transformed placement's own Euclidean fiber is then built.
Neighbor-completion rigidity selects a genuinely injective pair, and
the two-center Maurer--Cartan argument forces an impossible merger.

The proof retains centers at infinity before the actual chart change.
No covariance of Euclidean length fibers or Maurer--Cartan forms is
assumed. The assembly combines the actual body forms and chart transport.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical Topology

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_deletionRankDrop_ne_six
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v) :
    deletionRankDrop M.graph v ≠ 6 := by
  intro hdrop
  obtain ⟨b, hb⟩ := hh.exists_three_owned
  obtain ⟨p, hgen, hp⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let base := b 0
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  let I := {c : OwnedIncidentTriangle M.graph v // c.owner ≠ base.owner}
  have hthree (i : I) : Module.finrank ℝ (T.relativeTwists p hn base i.val).range = 3 := by
    exact Nat.le_antisymm
      (M.hypervertex_relative_rank_le_three v hh hdrop p hgen hp base i.val)
      (Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v p hgen hp base i.val i.property)
  have hsingular (i : I) : SingularPinSpace (T.relativeTwists p hn base i.val).range :=
    Papers.Rigidity.VertexPin.MinimalCounterexample.owned_rankThree_singular M v p hgen hp base i.val i.property (hthree i)
  obtain ⟨c, hc, hgq, hq, hfinite⟩ :=
    ProjectiveTransport.exists_generic_placement_with_finite_relative_centers
      T p hgen hp base (fun i : I => i.val) hsingular (fun i => (hthree i).ge)
  let q := ProjectiveTransport.placement c p
  let hnq := GeneralPosition.InGeneralPosition.incident_noncollinear q hq T
  let C := groundedLengthFiberChart (deletedGraph M.graph v) (T.triangleEmbedding base)
    (T.clique base) (deletedPlacement q v)
    (generic_deletedPlacement q hgq v (deletedGraph M.graph v)) (hnq base)
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions q base) = 4 := by
    have h := M.grounded_incident_finrank v T q hgq hq base
    omega
  let b₁ := b 1
  have hb₁ : b₁.owner ≠ base.owner := hb.ne (by decide)
  obtain ⟨b₂, hb₂, hb₂₁, hpair⟩ :=
    M.hypervertex_select_injective_pair v hh hdrop q hgq hq base b₁ hb₁ C
  let θ₁ := (T.incidentBodyRepresentation q hq base C b₁).form
  let θ₂ := (T.incidentBodyRepresentation q hq base C b₂).form
  have hω₁ : Function.Surjective (angularForm (θ₁ 0)) := by
    obtain ⟨a, ha⟩ := hfinite (⟨b₁, hb₁⟩ : I)
    apply angular_surjective_of_finiteCenter_range (θ₁ 0).toLinearMap a
    rw [show (θ₁ 0).toLinearMap.range = (T.relativeTwists q hnq base b₁).range from
      T.incidentBodyForm_range_at_zero q hq base C b₁]
    exact ha
  have hω₂ : Function.Surjective (angularForm (θ₂ 0)) := by
    obtain ⟨a, ha⟩ := hfinite (⟨b₂, hb₂⟩ : I)
    apply angular_surjective_of_finiteCenter_range (θ₂ 0).toLinearMap a
    rw [show (θ₂ 0).toLinearMap.range = (T.relativeTwists q hnq base b₂).range from
      T.incidentBodyForm_range_at_zero q hq base C b₂]
    exact ha
  have hactual : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions q base),
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y :=
    (T.incidentBodyRepresentation_locallyRepresented q hq base C).mono
      (fun _ hy => ⟨hy b₁, hy b₂⟩)
  have hsnear : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions q base),
      SingularPinSpace (θ₁ y).toLinearMap.range ∧ SingularPinSpace (θ₂ y).toLinearMap.range := by
    filter_upwards [M.hypervertex_owned_body_singular_eventually v hh hdrop q hgq hq base b₁ hb₁ C,
      M.hypervertex_owned_body_singular_eventually v hh hdrop q hgq hq base b₂ hb₂ C]
        with y hy₁ hy₂
    exact ⟨hy₁, hy₂⟩
  have hrank := T.incidentBody_joint_rank_le_three q hq base C hgq (by omega) b₁ b₂
  obtain ⟨U, hU, hUdense, hmerge⟩ := actual_rankThree_pair_dense_pin_merger θ₁ θ₂ 0 hE
    hactual hsnear hω₁ hω₂ hpair hrank
  exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_dense_pin_merger_contradiction M v q hq base C hgq b₂ b₁ hb₂₁ U hUdense
    (fun pin hpin u h₂ h₁ => hmerge pin hpin u h₁ h₂)

/-- Proposition 4.1 with the literal maximal-body incidence definition
and the actual generic graph-rank deletion loss. -/
theorem MinimalCounterexample.hypervertex_deletionRankDrop_ge_seven
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v) :
    7 ≤ deletionRankDrop M.graph v := by
  have hlow := M.five_le_deletionRankDrop v
  have hfive := M.hypervertex_deletionRankDrop_ne_five v hh
  have hsix := M.hypervertex_deletionRankDrop_ne_six v hh
  omega

end Papers.Rigidity

end
end
end BundleSource0056

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0056/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0056.json"

section BundleSource0057
/- Source: Papers/RigidityHypervertexCharges.lean -/





@[expose] public section

/-!
# The final actual hypervertex charge

The integer inequality here is the concluding account of Section 7.4.
Its exceptional-component and core counts are the literal counts from
the original graph. The proof constructs the specified ordinary star
edges and verifies all geometric side conditions of the arithmetic
lemma, including its small boundary cases.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

def neighborIncidentSet (G : SimpleGraph V) (v : V) (S : Finset V) :
    Finset (IncidentEdge G v) :=
  Finset.univ.filter fun e => incidentOther G v e ∈ S

theorem neighborIncidentSet_card
    (G : SimpleGraph V) (v : V) (S : Finset V)
    (hS : S ⊆ G.neighborFinset v) : (neighborIncidentSet G v S).card = S.card := by
  apply Finset.card_bij (fun e _ => incidentOther G v e)
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he f hf hef
    exact incidentOther_injective G v hef
  · intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp (hS hw)
    let e : IncidentEdge G v := ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w⟩
    have heq : incidentOther G v e = w :=
      Sym2.congr_right.mp (Sym2.other_spec e.property)
    exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq.symm ▸ hw⟩,heq⟩

theorem charged_core_single_residual_bound
    (M : MinimalCounterexample V) (h : V)
    (hcount : (chargedCoresAt M h).card = 1)
    (K : Finset V) (hK : K ⊆ M.graph.neighborFinset h)
    (hKP : Disjoint K (chargedPortsAt M h)) :
    4 + (chargedPortsAt M h).card ≤
      K.card + (M.graph.neighborFinset h \ (K ∪ chargedPortsAt M h)).card := by
  obtain ⟨C,hC⟩ := Finset.card_eq_one.mp hcount
  have hCm : C ∈ chargedCoresAt M h := by rw [hC]; simp
  have heq (v : chargedPortsAt M h) : chargedPortCore M h v = C := by
    have hm := chargedPortCore_mem M h v
    rwa [hC,Finset.mem_singleton] at hm
  let Q : ∀ v : chargedPortsAt M h, CorePort M C.val h v.val := fun v =>
    (heq v) ▸ chargedPortRecord M h v
  have hP : (chargedPortsAt M h).Nonempty := by
    have htwo := ((mem_chargedCoresAt M h C).mp hCm).2.2
    have hcard : (chargedPortsAt M h).card = (bodyTypeBVertices M C.val).card := by
      simp only [chargedPortsAt,hC,Finset.singleton_biUnion]
    exact Finset.card_pos.mp (by omega)
  exact core_ports_residual_neighbor_bound M C.val h (chargedPortsAt M h) K Q hP hK hKP

theorem exists_charged_three_port_core
    (M : MinimalCounterexample V) (h : V) (hpos : 0 < chargedCoreCountAt M h 3) :
    ∃ C : SelectedCore M, C ∈ chargedCoresAt M h ∧
      (bodyTypeBVertices M C.val).card = 3 := by
  obtain ⟨C,hC⟩ := Finset.card_pos.mp hpos
  have hm : bodyHyperVertices M C.val = {h} ∧ bodySoftVertices M C.val = ∅ ∧
      (bodyTypeBVertices M C.val).card = 3 := (Finset.mem_filter.mp hC).2
  exact ⟨C,(mem_chargedCoresAt M h C).mpr ⟨hm.1,hm.2.1,by omega⟩,hm.2.2⟩

theorem exceptional_and_three_port_residual_nonempty
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph)
    (ha : exceptionalCountAt L h = 1) (hq3 : 0 < chargedCoreCountAt M h.val 3) :
    1 ≤ (M.graph.neighborFinset h.val \
      (exceptionalNeighborsAt L h ∪ chargedPortsAt M h.val)).card := by
  obtain ⟨c,hc,hK⟩ := exceptionalNeighbors_subset_of_count_one L h ha
  obtain ⟨C,hC,hthree⟩ := exists_charged_three_port_core M h.val hq3
  have hfiber : (Finset.univ.filter fun v : chargedPortsAt M h.val =>
      (chargedPortCore M h.val v).val = C.val).card = 3 := by
    rw [← core_port_family_inter_card M h.val (chargedPortsAt M h.val)
      (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
      C.val (by rw [C.property.1]),chargedPorts_inter_core M h.val C hC,hthree]
  exact L.three_port_core_has_residual_neighbor c h hc
    (chargedPortsAt M h.val) (exceptionalNeighborsAt L h)
    (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
    C.val C.property.1 (chargedCore_partner_mem M h.val C hC) hfiber hK

/-- The actual specified star consists of all exceptional-component
neighbors and all charged type-B ports. The included zero coordinates
cause no problem: the proved joint-kernel rank bound applies to them
as well. -/
theorem exceptional_charged_star_deletion_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (exceptionalNeighborsAt L h).card + (chargedPortsAt M h.val).card +
      min 3 (M.graph.neighborFinset h.val \
        (exceptionalNeighborsAt L h ∪ chargedPortsAt M h.val)).card ≤
      deletionRankDrop M.graph h.val + exceptionalCountAt L h + (chargedCoresAt M h.val).card := by
  let K := exceptionalNeighborsAt L h
  let P := chargedPortsAt M h.val
  let G := maskedGraph M.graph Finset.univ
  let A := neighborIncidentSet G h.val (K ∪ P)
  have hG : G = M.graph := by ext v w; simp [G,maskedGraph]
  have hKP : Disjoint K P := exceptional_charged_neighbors_disjoint L h
  have hsub : K ∪ P ⊆ M.graph.neighborFinset h.val :=
    Finset.union_subset (exceptionalNeighbors_subset_neighbors L h)
      (chargedPorts_subset_neighbors M h.val)
  have hsubG : K ∪ P ⊆ G.neighborFinset h.val := by
    intro w hw
    apply (G.mem_neighborFinset h.val w).mpr
    rw [hG]
    exact (M.graph.mem_neighborFinset h.val w).mp (hsub hw)
  have hAcard : A.card = K.card + P.card := by
    rw [neighborIncidentSet_card G h.val (K ∪ P) hsubG,
      Finset.card_union_of_disjoint hKP]
  have hD : M.graph.degree h.val - A.card =
      (M.graph.neighborFinset h.val \ (K ∪ P)).card := by
    rw [Finset.card_sdiff_of_subset hsub,Finset.card_union_of_disjoint hKP,
      M.graph.card_neighborFinset_eq_degree,hAcard]
  have hb := L.exceptional_core_star_deletion_bound hgen hp h
    (fun c : exceptionalComponentsAt L h => c.val)
    (fun c => (mem_exceptionalComponentsAt L h c.val).mp c.property)
    (fun c => c.val.out) (fun c => c.val.out_eq)
    (fun C : chargedCoresAt M h.val => C.val.val)
    (fun C => selectedCoreMode hgen C.val)
    (fun C => chargedCore_no_soft M h.val C.val C.property)
    (fun C => chargedCore_sole_hyper M h.val C.val C.property)
    A (by
      intro e he
      have hmem : incidentOther G h.val e ∈ K ∪ P := (Finset.mem_filter.mp he).2
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · obtain ⟨c,hc,hvc⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hmem).2
        exact Or.inl ⟨⟨c,hc⟩,hvc⟩
      · let v : P := ⟨incidentOther G h.val e,hmem⟩
        exact Or.inr ⟨⟨chargedPortCore M h.val v,chargedPortCore_mem M h.val v⟩,
          ⟨chargedPortRecord M h.val v⟩⟩)
  rw [hD, hAcard] at hb
  simp only [Fintype.card_coe] at hb
  exact hb

/-- The concluding inequality of Section 7.4, in exact integer units.
Every count refers to a proved actual graph family. -/
theorem SoftScalarSystem.remaining_hypervertex_charges
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    12 + 2 * exceptionalCountAt L h + chargedCoreCountAt M h.val 3 +
      2 * chargedCoreCountAt M h.val 4 ≤ 2 * deletionRankDrop M.graph h.val := by
  let a := exceptionalCountAt L h
  let q2 := chargedCoreCountAt M h.val 2
  let q3 := chargedCoreCountAt M h.val 3
  let q4 := chargedCoreCountAt M h.val 4
  let K := exceptionalNeighborsAt L h
  let P := chargedPortsAt M h.val
  let D := (M.graph.neighborFinset h.val \ (K ∪ P)).card
  have hPcard : P.card = 2*q2 + 3*q3 + 4*q4 := chargedPorts_card M h.val
  have hCcard : (chargedCoresAt M h.val).card = q2+q3+q4 := (chargedCore_counts M h.val).1
  have hKsub : K ⊆ M.graph.neighborFinset h.val := exceptionalNeighbors_subset_neighbors L h
  have hKP : Disjoint K P := exceptional_charged_neighbors_disjoint L h
  apply Budget.remaining_hypervertex_charges a q2 q3 q4 K.card D
    (deletionRankDrop M.graph h.val)
  · exact M.hypervertex_deletionRankDrop_ge_seven h.val h.property
  · exact exceptionalNeighbors_card_ge L hgen hp h
  · have hb := exceptional_charged_star_deletion_bound L hgen hp h
    rw [hPcard,hCcard] at hb
    exact hb
  · intro ha hg
    have hKempty : K = ∅ := exceptionalNeighbors_eq_empty_of_count_zero L h ha
    have hPnonempty : P.Nonempty := Finset.card_pos.mp (by omega)
    have hb := core_port_family_three_unused_neighbors M h.val P hPnonempty
      (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
    simpa only [D,hKempty,Finset.empty_union] using hb
  · intro ha h2 h3 h4
    exact exceptional_and_three_port_residual_nonempty L h ha (by omega)
  · intro ha h2 h3 h4
    have hc : (chargedCoresAt M h.val).card = 1 := by omega
    have hb := charged_core_single_residual_bound M h.val hc K hKsub hKP
    have hp3 : P.card = 3 := by omega
    change 7 ≤ K.card + D
    change 4 + P.card ≤ K.card + D at hb
    omega
  · intro ha h2 h3 h4
    have hc : (chargedCoresAt M h.val).card = 1 := by omega
    have hb := charged_core_single_residual_bound M h.val hc K hKsub hKP
    have hp4 : P.card = 4 := by omega
    change 8 ≤ K.card + D
    change 4 + P.card ≤ K.card + D at hb
    omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0057

section BundleSource0058
/- Source: Papers/RigidityLastInSubset.lean -/



@[expose] public section

/-!
# Birth of a locally supported mode

A fixed vertex is last in a nonempty finite support with probability
the reciprocal of its cardinality.  The probability is computed in the
same literal finite space of global orders used for rank contributions.
It applies to every support and does not introduce independent priorities
or assume a law for an induced order.
-/

namespace Papers.Rigidity.UniformOrders
noncomputable section
open scoped Classical BigOperators
variable {V I : Type*} [Fintype V] [Fintype I]

theorem mean_indicator_position (i : I) (q : Fin (Fintype.card I)) :
    mean (fun σ : Outcome I => if σ i = q then (1 : ℝ) else 0) =
      1 / Fintype.card I := by
  let F : I → Outcome I → ℝ := fun j σ => if σ j = q then 1 else 0
  have hsame (j : I) : mean (F j) = mean (F i) := by
    let swap : Outcome I ≃ Outcome I :=
      { toFun := fun σ => (Equiv.swap i j).trans σ
        invFun := fun σ => (Equiv.swap i j).trans σ
        left_inv := by intro σ; ext a; simp
        right_inv := by intro σ; ext a; simp }
    have hsum := Equiv.sum_comp swap (F i)
    simpa [mean, F, swap] using congrArg
      (fun x : ℝ => x / Fintype.card (Outcome I)) hsum
  have hone (σ : Outcome I) : (∑ j : I, F j σ) = 1 := by
    have h := Equiv.sum_comp σ (fun r => if r = q then (1 : ℝ) else 0)
    simpa [F] using h
  have htotal : (Fintype.card I : ℝ) * mean (F i) = 1 := by
    calc
      _ = ∑ j : I, mean (F j) := by simp [hsame]
      _ = mean (fun σ => ∑ j : I, F j σ) := (mean_sum F).symm
      _ = 1 := by rw [mean_congr _ _ hone, mean_const]
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  apply (eq_div_iff hcard).mpr
  simpa [F, mul_comm] using htotal

theorem mean_indicator_last (i : I) :
    mean (fun σ : Outcome I =>
      if ∀ j : I, σ j ≤ σ i then (1 : ℝ) else 0) =
      1 / Fintype.card I := by
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  let q : Fin (Fintype.card I) := ⟨Fintype.card I - 1, by omega⟩
  have hmax (σ : Outcome I) : (∀ j : I, σ j ≤ σ i) ↔ σ i = q := by
    constructor
    · intro h
      have hi := h (σ.symm q)
      have hi' : q.val ≤ (σ i).val := by simpa using hi
      apply Fin.ext
      have hil := (σ i).isLt
      change (σ i).val = Fintype.card I - 1
      change Fintype.card I - 1 ≤ (σ i).val at hi'
      omega
    · intro h j
      rw [h]
      change (σ j).val ≤ Fintype.card I - 1
      have hj := (σ j).isLt
      omega
  simp_rw [hmax]
  exact mean_indicator_position i q

theorem restrict_le_iff (e : I ↪ V) (σ : Outcome V) (i j : I) :
    restrict e σ i ≤ restrict e σ j ↔ σ (e i) ≤ σ (e j) := by
  rw [← not_lt, restrict_lt_iff, not_lt]

/-- Exact probability that a specified vertex completes a given finite
vertex support in the actual uniformly random global order. -/
theorem mean_indicator_last_in_finset (S : Finset V) (v : V) (hv : v ∈ S) :
    mean (fun σ : Outcome V =>
      if ∀ w ∈ S, σ w ≤ σ v then (1 : ℝ) else 0) = 1 / S.card := by
  let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let i : S := ⟨v, hv⟩
  let F : Outcome S → ℝ := fun τ => if ∀ j : S, τ j ≤ τ i then 1 else 0
  have hpoint (σ : Outcome V) :
      (if ∀ w ∈ S, σ w ≤ σ v then (1 : ℝ) else 0) = F (restrict e σ) := by
    have h : (∀ j : S, restrict e σ j ≤ restrict e σ i) ↔
        ∀ w ∈ S, σ w ≤ σ v := by
      simp only [restrict_le_iff, e, i, Function.Embedding.coeFn_mk]
      constructor
      · intro h w hw
        exact h ⟨w, hw⟩
      · intro h j
        exact h j.val j.property
    simp only [F, h]
  rw [mean_congr _ _ hpoint, mean_restrict]
  simpa [F, i] using mean_indicator_last i

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0058

section BundleSource0059
/- Source: Papers/RigiditySelectedCoreBirth.lean -/






@[expose] public section

/-!
# Exact prefix splitting and the one-fifth core contribution

The coordinate functionals below act on the ordinary ambient edge
coefficient space.  They cut the actual scalar kernel into the selected
local K5 modes and its actual common-kernel remainder.  Every induced
prefix sees exactly the modes whose five actual vertices are present.
The same finite uniform order space as the stress ledger then gives
one fifth at each incident vertex, with no independence assumption.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders ModeSplitting
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

def SoftScalarSystem.coreCoefficient (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (C : SelectedCore M) :
    Module.Dual ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ) :=
  let B := selectedCoreMode hgen C
  B.unitCoefficient⁻¹ •
    ((LinearMap.proj B.neighbor).comp (starCoordinates (maskedGraph M.graph Finset.univ) B.vertex))

@[simp] theorem SoftScalarSystem.coreCoefficient_on_stress
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p) (C : SelectedCore M)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    L.coreCoefficient hgen C s.val = (selectedCoreMode hgen C).coefficient s := rfl

def SoftScalarSystem.coreResidual (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) :
    Submodule ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ) :=
  L.scalarKernel ⊓ nullModes (L.coreCoefficient hgen)

theorem SoftScalarSystem.coreResidual_le_kernel (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) : L.coreResidual hgen ≤ L.scalarKernel := inf_le_left

def availableSelectedCores (M : MinimalCounterexample V) (T : Finset V) :
    Finset (SelectedCore M) := Finset.univ.filter fun C => C.val.val ⊆ T

@[simp] theorem mem_availableSelectedCores
    (M : MinimalCounterexample V) (T : Finset V) (C : SelectedCore M) :
    C ∈ availableSelectedCores M T ↔ C.val.val ⊆ T := by
  simp only [availableSelectedCores,Finset.mem_filter,Finset.mem_univ,true_and]

theorem SoftScalarSystem.core_modes_biorthogonal
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C D : SelectedCore M) :
    L.coreCoefficient hgen C (selectedCoreMode hgen D).fullStress.val =
      if C = D then 1 else 0 := by
  rw [L.coreCoefficient_on_stress]
  by_cases hCD : C = D
  · subst D
    rw [if_pos rfl]
    exact (selectedCoreMode hgen C).coefficient_fullStress hgen hp
  · rw [if_neg hCD]
    exact (selectedCoreMode hgen C).coefficient_other_fullStress
      (selectedCoreMode hgen D) (fun h => hCD (Subtype.ext h.symm))

/-- Exact equality of the original scalar-kernel prefix dimension with
the available local-mode count and the literal residual prefix. -/
theorem SoftScalarSystem.selectedCore_prefix_finrank
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ (supportedOn L.scalarKernel
      (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)) =
      (availableSelectedCores M T).card +
      Module.finrank ℝ (supportedOn (L.coreResidual hgen)
        (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)) := by
  let P := supportedOn L.scalarKernel (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)
  have hmem (C : SelectedCore M) (hC : C ∈ availableSelectedCores M T) :
      (selectedCoreMode hgen C).fullStress.val ∈ P := by
    refine ⟨(selectedCoreMode hgen C).fullStress_mem_kernel L,?_⟩
    intro e he
    by_contra hn
    exact he ((selectedCoreMode hgen C).fullStress_supported_in_prefix T
      ((mem_availableSelectedCores M T C).mp hC) e hn)
  have habsent (x : Edge (maskedGraph M.graph Finset.univ) → ℝ) (hx : x ∈ P)
      (C : SelectedCore M) (hC : C ∉ availableSelectedCores M T) :
      L.coreCoefficient hgen C x = 0 := by
    let s : StressSpace (maskedGraph M.graph Finset.univ) p :=
      ⟨x,L.scalarKernel_le_stress hx.1⟩
    have hsupport : CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T x := by
      intro e he v hv
      by_contra hvT
      exact he (hx.2 e (fun heT => hvT (heT v hv)))
    exact (selectedCoreMode hgen C).coefficient_zero_on_incomplete_prefix L hgen hp T
      s hx.1 hsupport (fun h => hC ((mem_availableSelectedCores M T C).mpr h))
  have h := prefix_finrank P (L.coreCoefficient hgen)
    (fun C => (selectedCoreMode hgen C).fullStress.val) (availableSelectedCores M T)
    (by
      intro C D
      have hh := L.core_modes_biorthogonal hgen hp C D
      by_cases hCD : C = D
      · rw [if_pos hCD] at hh ⊢
        exact hh
      · rw [if_neg hCD] at hh ⊢
        exact hh) hmem habsent
  have heq : (P ⊓ nullModes (L.coreCoefficient hgen) :
      Submodule ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ)) =
      supportedOn (L.coreResidual hgen) (vertexEdgeSet (maskedGraph M.graph Finset.univ) T) := by
    ext x
    change ((x ∈ L.scalarKernel ∧ _) ∧ _) ↔ ((x ∈ L.scalarKernel ∧ _) ∧ _)
    tauto
  rw [heq] at h
  exact h

theorem selectedCore_indicator_birth
    (C : SelectedCore M) (σ : Outcome V) (v : V) :
    (if C.val.val ⊆ verticesThrough σ v then (1 : ℝ) else 0) -
      (if C.val.val ⊆ verticesBefore σ v then (1 : ℝ) else 0) =
      if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0 := by
  have hthrough : C.val.val ⊆ verticesThrough σ v ↔ ∀ w ∈ C.val.val, σ w ≤ σ v := by
    simp only [Finset.subset_iff,mem_verticesThrough]
  have hbefore : C.val.val ⊆ verticesBefore σ v ↔ ∀ w ∈ C.val.val, σ w < σ v := by
    simp only [Finset.subset_iff,mem_verticesBefore]
  by_cases hv : v ∈ C.val.val
  · have hn : ¬ C.val.val ⊆ verticesBefore σ v := by
      intro hs
      exact (lt_irrefl (σ v)) ((hbefore.mp hs) v hv)
    simp only [hv,if_pos,hn,if_false,hthrough,sub_zero]
  · have heq : (∀ w ∈ C.val.val, σ w ≤ σ v) ↔ ∀ w ∈ C.val.val, σ w < σ v := by
      constructor
      · intro hs w hw
        exact lt_of_le_of_ne (hs w hw) (fun he => hv (σ.injective he ▸ hw))
      · intro hs w hw
        exact (hs w hw).le
    simp only [hv,if_false,hthrough,hbefore,heq,sub_self]

theorem selectedCore_count_birth
    (M : MinimalCounterexample V) (σ : Outcome V) (v : V) :
    ((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
      (availableSelectedCores M (verticesBefore σ v)).card =
      ∑ C : SelectedCore M, if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0 := by
  simp only [availableSelectedCores,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun C _ => selectedCore_indicator_birth C σ v

theorem mean_selectedCore_count_birth
    (M : MinimalCounterexample V) (v : V) :
    mean (fun σ : Outcome V =>
      ((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
        (availableSelectedCores M (verticesBefore σ v)).card) =
      (selectedIncidentCount M v : ℝ) / 5 := by
  rw [mean_congr _ _ (fun σ => selectedCore_count_birth M σ v),mean_sum]
  have hterm (C : SelectedCore M) :
      mean (fun σ : Outcome V => if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0) =
      if v ∈ C.val.val then (1 : ℝ)/5 else 0 := by
    by_cases hv : v ∈ C.val.val
    · simp only [hv,if_pos]
      rw [mean_indicator_last_in_finset C.val.val v hv,C.property.1]
      norm_num
    · simp only [hv,if_false,mean_const]
  simp only [hterm]
  simp only [selectedIncidentCount,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs <;> norm_num

/-- Equation (7), including the exact one-fifth contribution for every
incident selected core in the original uniformly random vertex order. -/
theorem SoftScalarSystem.selectedCore_stressDimensionContribution
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      (selectedIncidentCount M v : ℝ) / 5 +
      stressDimensionContribution (maskedGraph M.graph Finset.univ) (L.coreResidual hgen) v := by
  let G := maskedGraph M.graph Finset.univ
  have hpoint (σ : Outcome V) :
      (Module.finrank ℝ (stressThrough G L.scalarKernel σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G L.scalarKernel σ v) =
      (((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
        (availableSelectedCores M (verticesBefore σ v)).card) +
      ((Module.finrank ℝ (stressThrough G (L.coreResidual hgen) σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G (L.coreResidual hgen) σ v)) := by
    have ht (W : Submodule ℝ (Edge G → ℝ)) :
        Module.finrank ℝ (stressThrough G W σ v) =
          Module.finrank ℝ (supportedOn W (vertexEdgeSet G (verticesThrough σ v))) :=
      congrArg (fun A : Set (Edge G) => Module.finrank ℝ (supportedOn W A))
        (edgesThrough_eq_vertexEdgeSet G σ v)
    have hb (W : Submodule ℝ (Edge G → ℝ)) :
        Module.finrank ℝ (stressBefore G W σ v) =
          Module.finrank ℝ (supportedOn W (vertexEdgeSet G (verticesBefore σ v))) :=
      congrArg (fun A : Set (Edge G) => Module.finrank ℝ (supportedOn W A))
        (edgesBefore_eq_vertexEdgeSet G σ v)
    have hprefix (T : Finset V) :
        Module.finrank ℝ (supportedOn L.scalarKernel (vertexEdgeSet G T)) =
          (availableSelectedCores M T).card +
          Module.finrank ℝ (supportedOn (L.coreResidual hgen) (vertexEdgeSet G T)) :=
      L.selectedCore_prefix_finrank hgen hp T
    have hT := (ht L.scalarKernel).trans (hprefix (verticesThrough σ v))
    have hB := (hb L.scalarKernel).trans (hprefix (verticesBefore σ v))
    rw [hT, hB, ht, hb]
    push_cast
    ring
  unfold stressDimensionContribution
  rw [mean_congr _ _ hpoint,mean_add,mean_selectedCore_count_birth M v]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0059

section BundleSource0060
/- Source: Papers/RigidityScalarStarRank.lean -/






@[expose] public section

/-!
# The star rank after imposing the actual soft scalar equations

Vertex-indexed star coordinates have the same image dimension as the
ordinary incident-edge restriction. Their dual row space is exactly
the span used to define the paper's observer credit. Dual annihilator
rank-nullity therefore proves the first rank loss in equation (8).
-/

noncomputable section
namespace Papers.Rigidity.BarJoint
open SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem starCoordinates_eq_zero_iff (G : SimpleGraph V) (v : V)
    (a : Edge G → ℝ) :
    starCoordinates G v a = 0 ↔ starRestriction G v a = 0 := by
  constructor
  · intro h
    ext e
    have he := congrFun h (incidentOther G v e)
    change a e.val = 0
    simpa only [starCoordinates_incidentOther,Pi.zero_apply] using he
  · intro h
    ext w
    by_cases hadj : G.Adj v w
    · rw [starCoordinates_of_adj _ _ _ _ hadj]
      exact congrFun h ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w⟩
    · exact starCoordinates_of_not_adj G v w a hadj

theorem starCoordinates_range_finrank (G : SimpleGraph V) (v : V)
    (W : Submodule ℝ (Edge G → ℝ)) :
    Module.finrank ℝ ((starCoordinates G v).domRestrict W).range =
      Module.finrank ℝ (stressStarCode G v W) := by
  have hk : ((starCoordinates G v).domRestrict W).ker =
      ((starRestriction G v).domRestrict W).ker := by
    ext a
    exact starCoordinates_eq_zero_iff G v a.val
  have hC := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := V → ℝ) ((starCoordinates G v).domRestrict W)
  have hS := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := IncidentEdge G v → ℝ)
    ((starRestriction G v).domRestrict W)
  rw [hk] at hC
  rw [LinearMap.range_domRestrict] at hS
  change Module.finrank ℝ ((starCoordinates G v).domRestrict W).range =
    Module.finrank ℝ (W.map (starRestriction G v))
  omega

theorem starCoordinates_map_finrank (G : SimpleGraph V) (v : V)
    (W : Submodule ℝ (Edge G → ℝ)) :
    Module.finrank ℝ (W.map (starCoordinates G v)) =
      Module.finrank ℝ (stressStarCode G v W) := by
  rw [← LinearMap.range_domRestrict]
  exact starCoordinates_range_finrank G v W

def stressStarMeasurement (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    StressSpace G p →ₗ[ℝ] (V → ℝ) := (starCoordinates G v).domRestrict (StressSpace G p)

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode AnnihilatorRank VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V] {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.hyperStarSpan_coannihilator (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    (L.hyperStarSpan h).dualCoannihilator =
      (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val).ker := by
  ext s
  rw [Submodule.mem_dualCoannihilator,LinearMap.mem_ker]
  constructor
  · intro hs
    ext w
    exact hs _ (Submodule.subset_span ⟨w,rfl⟩)
  · intro hs
    have hle : L.hyperStarSpan h ≤
        ((Module.Dual.eval ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)) s).ker := by
      apply Submodule.span_le.mpr
      rintro φ ⟨w,rfl⟩
      exact congrFun hs w
    intro φ hφ
    exact hle hφ

theorem SoftScalarSystem.hyperStarSpan_eq_readable (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    L.hyperStarSpan h = readable
      (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val) := by
  rw [readable,← L.hyperStarSpan_coannihilator h,
    Subspace.dualCoannihilator_dualAnnihilator_eq]

theorem SoftScalarSystem.scalarKernel_star_range (L : SoftScalarSystem M p)
    (v : V) :
    ((stressStarMeasurement (maskedGraph M.graph Finset.univ) p v).domRestrict L.scalarSpan.dualCoannihilator).range =
        L.scalarKernel.map (starCoordinates (maskedGraph M.graph Finset.univ) v) := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val.val,⟨x.val,x.property,rfl⟩,rfl⟩
  · rintro ⟨x,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨⟨s,hs⟩,rfl⟩

/-- Imposing the soft point-pin equations removes exactly the readable
scalar dimension from each hypervertex star. -/
theorem SoftScalarSystem.scalarKernel_star_rank (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) + L.hyperCredit h =
      Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (StressSpace (maskedGraph M.graph Finset.univ) p)) := by
  have ha := finrank_restrict_coannihilator
    (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val) L.scalarSpan
  rw [L.scalarKernel_star_range,starCoordinates_map_finrank,
    ← L.hyperStarSpan_eq_readable] at ha
  change _ + L.hyperCredit h =
    Module.finrank ℝ ((starCoordinates (maskedGraph M.graph Finset.univ) h.val).domRestrict (StressSpace (maskedGraph M.graph Finset.univ) p)).range at ha
  rw [starCoordinates_range_finrank] at ha
  exact ha

theorem SoftScalarSystem.scalarKernel_star_rank_add_drop (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) + L.hyperCredit h + deletionRankDrop M.graph h.val =
      M.graph.degree h.val := by
  rw [L.scalarKernel_star_rank,maskedGraph_univ]
  exact stressStar_finrank_add_deletionRankDrop M.graph p hgen h.val

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0060

section BundleSource0061
/- Source: Papers/RigidityHypervertexContribution.lean -/






@[expose] public section

/-!
# Equation (8): the actual hypervertex contribution

The selected core coordinates are readable on exactly their incident
hypervertex stars. Biorthogonal actual modes remove precisely that many
dimensions. Combined with the scalar-annihilator rank identity, the
one-fifth prefix birth formula, and Corollary 2.2, this gives all credits
in the paper's hypervertex estimate.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders ModeSplitting VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V] {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.coreResidual_star_rank (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (L.coreResidual hgen)) + selectedIncidentCount M h.val =
      Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) := by
  let G := maskedGraph M.graph Finset.univ
  let f : L.scalarKernel →ₗ[ℝ] (V → ℝ) :=
    (starCoordinates G h.val).domRestrict L.scalarKernel
  let ρ : SelectedCore M → L.scalarKernel →ₗ[ℝ] ℝ := fun C =>
    (L.coreCoefficient hgen C).comp L.scalarKernel.subtype
  let s : SelectedCore M → L.scalarKernel := fun C =>
    ⟨(selectedCoreMode hgen C).fullStress.val,
      (selectedCoreMode hgen C).fullStress_mem_kernel L⟩
  let A : Finset (SelectedCore M) := Finset.univ.filter fun C => h.val ∈ C.val.val
  have hdual (C D : SelectedCore M) : ρ C (s D) = if C = D then 1 else 0 :=
    L.core_modes_biorthogonal hgen hp C D
  have hread (C : SelectedCore M) (hC : C ∈ A) (x : L.scalarKernel)
      (hx : f x = 0) : ρ C x = 0 := by
    have hhC : h.val ∈ C.val.val := (Finset.mem_filter.mp hC).2
    let B := selectedCoreMode hgen C
    obtain ⟨c,hc,hread⟩ := B.hypervertex_reads_coefficient L hgen hp h.val hhC h.property
    let a : StressSpace G p := ⟨x.val,L.scalarKernel_le_stress x.property⟩
    have he := hread a x.property
    have hz := congrFun hx B.vertex
    change starCoordinates G h.val x.val B.vertex = 0 at hz
    rw [hz] at he
    have hco : B.coefficient a = 0 := (mul_eq_zero.mp he.symm).resolve_left hc
    exact hco
  have hinvisible (C : SelectedCore M) (hC : C ∉ A) : f (s C) = 0 := by
    have hhC : h.val ∉ C.val.val := by simpa only [A,Finset.mem_filter,Finset.mem_univ,
      true_and] using hC
    let B := selectedCoreMode hgen C
    change starCoordinates G h.val B.fullStress.val = 0
    ext w
    rw [B.fullStress_star]
    apply starCoordinates_of_not_adj
    intro hadj
    exact hhC (Finset.mem_inter.mp hadj.2.1).1
  have hd := measured_nullModes_finrank f ρ s A (by
    intro C D
    have hh := hdual C D
    by_cases hCD : C = D
    · rw [if_pos hCD] at hh ⊢
      exact hh
    · rw [if_neg hCD] at hh ⊢
      exact hh) hread hinvisible
  have himage : (f.domRestrict (nullModes ρ)).range =
      (L.coreResidual hgen).map (starCoordinates G h.val) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val.val,⟨x.val.property,x.property⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨⟨x,hx.1⟩,hx.2⟩,rfl⟩
  rw [himage,starCoordinates_map_finrank] at hd
  change _ + A.card =
    Module.finrank ℝ ((starCoordinates G h.val).domRestrict L.scalarKernel).range at hd
  rw [starCoordinates_range_finrank] at hd
  exact hd

/-- The rank parameter R in equation (8) is the actual residual star
image dimension, and its additive identity has no truncated subtraction. -/
theorem SoftScalarSystem.coreResidual_star_rank_add_drop (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (L.coreResidual hgen)) + selectedIncidentCount M h.val + L.hyperCredit h +
        deletionRankDrop M.graph h.val = M.graph.degree h.val := by
  rw [L.coreResidual_star_rank hgen hp]
  exact L.scalarKernel_star_rank_add_drop hgen h

/-- Equation (8), for every actual hypervertex of the original minimal
counterexample and the literal fixed scalar-annihilator stress space. -/
theorem SoftScalarSystem.hypervertex_contribution_bound (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    (L.hyperCredit h : ℝ) / 2 + 3 * (selectedIncidentCount M h.val : ℝ) / 10 +
        ((deletionRankDrop M.graph h.val : ℝ) - 6) / 2 ≤
      (M.graph.degree h.val : ℝ) / 2 -
        stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel h.val - 3 := by
  let R := Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
    (L.coreResidual hgen))
  have hstar := L.coreResidual_star_rank_add_drop hgen hp h
  have hstarR := congrArg (fun n : ℕ => (n : ℝ)) hstar
  push_cast at hstarR
  have hdim : (M.graph.degree h.val : ℝ) = (R : ℝ) +
      deletionRankDrop M.graph h.val + L.hyperCredit h + selectedIncidentCount M h.val := by
    dsimp [R]
    linarith
  have hb := Budget.hypervertex_contribution_lower_bound
    (M.graph.degree h.val) (deletionRankDrop M.graph h.val)
    (L.hyperCredit h) (selectedIncidentCount M h.val) R (Nat.cast_nonneg _) hdim
  have hexp := corollary_two_two_subspace (maskedGraph M.graph Finset.univ) p hp h.val
    (L.coreResidual hgen) ((L.coreResidual_le_kernel hgen).trans L.scalarKernel_le_stress)
  have hbound : bound 4 R = Budget.supportedBound 4 R := by
    simp only [bound,Budget.supportedBound,Nat.cast_ofNat]
  change _ ≤ bound 4 R at hexp
  rw [hbound] at hexp
  rw [L.selectedCore_stressDimensionContribution hgen hp h.val]
  linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0061

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0061/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0061.json"

section BundleSource0062
/- Source: Papers/RigidityGlobalBudget.lean -/





@[expose] public section

/-!
# The final global rigidity account

Every summand here is attached to the original graph: actual scalar
observers, actual maximal bodies, actual selected cores, and actual
exceptional scalar components. The double counts identify the local
credits exactly. The final contradiction uses the proved local bounds
and the exact scalar-annihilator rank ledger.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem sum_subtype_as_indicator {I A : Type*} [Fintype I] [AddCommMonoid A]
    (P : I → Prop) (f : I → A) :
    (∑ x : {x : I // P x}, f x.val) = ∑ x : I, if P x then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

theorem sum_indicator_predicate {I : Type*} [Fintype I] (P : I → Prop) (c : ℝ) :
    (∑ x : I, if P x then c else 0) =
      ((Finset.univ.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp

theorem sum_largeBodies_eq_sum (f : Body M.graph → ℝ)
    (hzero : ∀ C, ¬ 5 ≤ C.val.card → f C = 0) :
    (∑ C : LargeBody M.graph, f C.val) = ∑ C : Body M.graph, f C := by
  trans ∑ C : Body M.graph, if 5 ≤ C.val.card then f C else 0
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun C : Body M.graph => 5 ≤ C.val.card)) (by simp) f).symm
  · apply Finset.sum_congr rfl
    intro C _
    by_cases hC : 5 ≤ C.val.card
    · rw [if_pos hC]
    · rw [if_neg hC,hzero C hC]

theorem sum_selectedCores_eq_sum (f : Body M.graph → ℝ)
    (hzero : ∀ C, ¬ IsSelectedCore M C → f C = 0) :
    (∑ C : SelectedCore M, f C.val) = ∑ C : Body M.graph, f C := by
  trans ∑ C : Body M.graph, if IsSelectedCore M C then f C else 0
  · exact sum_subtype_as_indicator (IsSelectedCore M) f
  · apply Finset.sum_congr rfl
    intro C _
    by_cases hC : IsSelectedCore M C
    · rw [if_pos hC]
    · rw [if_neg hC,hzero C hC]

/-- Each exceptional scalar component has exactly one hypervertex
observer, so the sum of the local exceptional counts is its actual
global count in Proposition 6.6. -/
theorem SoftScalarSystem.sum_exceptionalCountAt
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    (∑ h : Hypervertex M.graph, exceptionalCountAt L h) =
      ObserverCover.exceptionalCount L.graph L.seed := by
  have hone (c : L.graph.ConnectedComponent) :
      (∑ h : Hypervertex M.graph, if L.observers c = {Sum.inl h} then 1 else 0) =
        if (L.observers c).card = 1 then 1 else 0 := by
    by_cases hc : (L.observers c).card = 1
    · obtain ⟨h,hh⟩ := L.sole_observer_is_hypervertex hgen hp hpin c hc
      simp [hc,hh,Finset.singleton_inj]
    · have hnone (h : Hypervertex M.graph) : L.observers c ≠ {Sum.inl h} := by
        intro heq
        exact hc (by rw [heq]; simp)
      simp [hc,hnone]
  calc
    _ = ∑ c : L.graph.ConnectedComponent, ∑ h : Hypervertex M.graph,
        if L.observers c = {Sum.inl h} then 1 else 0 := by
          simp only [exceptionalCountAt,exceptionalComponentsAt,
            Finset.card_eq_sum_ones,Finset.sum_filter]
          exact Finset.sum_comm
    _ = ∑ c : L.graph.ConnectedComponent, if (L.observers c).card = 1 then 1 else 0 :=
      Finset.sum_congr rfl (fun c _ => hone c)
    _ = ObserverCover.exceptionalCount L.graph L.seed := by
      change (∑ c : L.graph.ConnectedComponent,
        if (ObserverCover.observers L.graph L.seed c).card = 1 then (1 : ℕ) else 0) =
        Nat.card {c : L.graph.ConnectedComponent //
          (ObserverCover.observers L.graph L.seed c).card = 1}
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact Finset.sum_boole
        (fun c : L.graph.ConnectedComponent =>
          (ObserverCover.observers L.graph L.seed c).card = 1) Finset.univ

/-- Count selected-core/hypervertex incidences in either order. -/
theorem sum_selectedIncidentCount (M : MinimalCounterexample V) :
    (∑ h : Hypervertex M.graph, selectedIncidentCount M h.val) =
      ∑ C : SelectedCore M, (bodyHyperVertices M C.val).card := by
  have hbody (C : SelectedCore M) :
      (∑ h : Hypervertex M.graph, if h.val ∈ C.val.val then 1 else 0) =
        (bodyHyperVertices M C.val).card := by
    have hsum : (∑ h : Hypervertex M.graph, if h.val ∈ C.val.val then (1 : ℕ) else 0) =
        ∑ v : V, if IsHypervertex M.graph v then (if v ∈ C.val.val then 1 else 0) else 0 :=
      sum_subtype_as_indicator (IsHypervertex M.graph)
        (fun v : V => if v ∈ C.val.val then (1 : ℕ) else 0)
    rw [hsum]
    have heq (v : V) :
        (if IsHypervertex M.graph v then (if v ∈ C.val.val then 1 else 0) else 0) =
          if v ∈ bodyHyperVertices M C.val then 1 else 0 := by
      by_cases hh : IsHypervertex M.graph v <;> by_cases hv : v ∈ C.val.val <;>
        simp [bodyHyperVertices,hh,hv]
    calc
      _ = ∑ v : V, if v ∈ bodyHyperVertices M C.val then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl (fun v _ => heq v)
      _ = (Finset.univ.filter (fun v : V => v ∈ bodyHyperVertices M C.val)).card :=
        Finset.sum_boole _ _
      _ = _ := by rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    _ = ∑ C : SelectedCore M, ∑ h : Hypervertex M.graph,
        if h.val ∈ C.val.val then 1 else 0 := by
          simp only [selectedIncidentCount,Finset.card_eq_sum_ones,Finset.sum_filter]
          exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun C _ => hbody C)

theorem sum_bodyHyperCredit (M : MinimalCounterexample V) :
    (∑ C : Body M.graph, bodyHyperCredit M C) =
      ∑ h : Hypervertex M.graph, 3 * (selectedIncidentCount M h.val : ℝ) / 10 := by
  have hcount : (∑ h : Hypervertex M.graph, (selectedIncidentCount M h.val : ℝ)) =
      ∑ C : SelectedCore M, ((bodyHyperVertices M C.val).card : ℝ) := by
    exact_mod_cast sum_selectedIncidentCount M
  calc
    _ = ∑ C : SelectedCore M, 3 * ((bodyHyperVertices M C.val).card : ℝ) / 10 := by
      exact (sum_subtype_as_indicator (IsSelectedCore M)
        (fun C : Body M.graph => 3 * ((bodyHyperVertices M C).card : ℝ) / 10)).symm
    _ = 3 * (∑ C : SelectedCore M, ((bodyHyperVertices M C.val).card : ℝ)) / 10 := by
      rw [← Finset.sum_div,← Finset.mul_sum]
    _ = 3 * (∑ h : Hypervertex M.graph, (selectedIncidentCount M h.val : ℝ)) / 10 :=
      by rw [hcount]
    _ = _ := by rw [Finset.mul_sum,Finset.sum_div]

theorem bodyShortfall_zero_of_not_selected
    (M : MinimalCounterexample V) (C : Body M.graph) (hC : ¬ IsSelectedCore M C) :
    bodyShortfall M C = 0 := by
  unfold bodyShortfall
  split_ifs with he
  · have hb : (bodyTypeBVertices M C).card = 0 := by
      by_contra h
      exact hC ⟨he.1,Or.inr (Finset.card_pos.mp (by omega))⟩
    simp [hb,coreShortfall]
  · rfl

/-- Each positive core shortfall is assigned to its unique actual
hypervertex, with the coefficient prescribed in Section 7.4. -/
theorem selected_bodyShortfall_eq_hyper_sum
    (M : MinimalCounterexample V) (C : SelectedCore M) :
    bodyShortfall M C.val = ∑ h : Hypervertex M.graph,
      ((if bodyHyperVertices M C.val = {h.val} ∧ bodySoftVertices M C.val = ∅ ∧
          (bodyTypeBVertices M C.val).card = 3 then (1 / 4 : ℝ) else 0) +
      (if bodyHyperVertices M C.val = {h.val} ∧ bodySoftVertices M C.val = ∅ ∧
          (bodyTypeBVertices M C.val).card = 4 then (1 / 2 : ℝ) else 0)) := by
  by_cases he : (bodyHyperVertices M C.val).card = 1 ∧ (bodySoftVertices M C.val).card = 0
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp he.1
    have hmem : v ∈ bodyHyperVertices M C.val := by rw [hv]; simp
    have hh := (Finset.mem_filter.mp hmem).2
    let h : Hypervertex M.graph := ⟨v,hh⟩
    have hsoft : bodySoftVertices M C.val = ∅ := Finset.card_eq_zero.mp he.2
    have hiff (k : Hypervertex M.graph) : bodyHyperVertices M C.val = {k.val} ↔ k = h := by
      rw [hv,Finset.singleton_inj]
      constructor
      · intro heq
        exact Subtype.ext heq.symm
      · intro heq
        exact (congrArg Subtype.val heq).symm
    by_cases hb3 : (bodyTypeBVertices M C.val).card = 3
    · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hiff,hsoft]
    · by_cases hb4 : (bodyTypeBVertices M C.val).card = 4
      · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hb4,hiff,hsoft]
      · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hb4,hiff,hsoft]
  · have hzero : bodyShortfall M C.val = 0 := by
      unfold bodyShortfall
      rw [if_neg (fun h => he h.2)]
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro h _
    by_cases hH : bodyHyperVertices M C.val = {h.val}
    · have hS : bodySoftVertices M C.val ≠ ∅ := by
        intro heq
        exact he ⟨by rw [hH]; simp,by rw [heq]; simp⟩
      simp [hH,hS]
    · simp [hH]

theorem sum_bodyShortfall (M : MinimalCounterexample V) :
    (∑ C : Body M.graph, bodyShortfall M C) = ∑ h : Hypervertex M.graph,
      ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2) := by
  rw [← sum_selectedCores_eq_sum (M := M) (bodyShortfall M) (bodyShortfall_zero_of_not_selected M)]
  simp_rw [selected_bodyShortfall_eq_hyper_sum M]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold chargedCoreCountAt
  ring

theorem small_body_credits_zero (M : MinimalCounterexample V) (C : Body M.graph)
    (hsmall : ¬ 5 ≤ C.val.card) :
    bodyBaseCredit M C = 0 ∧ bodyHyperCredit M C = 0 ∧ bodyShortfall M C = 0 := by
  have hfour : C.val.card = 4 := by have := C.property.1; omega
  have hn : ¬ IsSelectedCore M C := fun h => by have := h.1; omega
  simp [bodyBaseCredit,bodyHyperCredit,bodyShortfall,hfour,hn]

/-- Reindexing the per-body inequalities produces exactly the selected
incidence and exceptional-core charges paid by the hypervertex account. -/
theorem SoftScalarSystem.total_body_budget
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (∑ C : LargeBody M.graph, (L.largeRank C : ℝ) / 2) ≤
      (∑ C : Body M.graph, bodyBaseCredit M C) +
      (∑ h : Hypervertex M.graph, 3 * (selectedIncidentCount M h.val : ℝ) / 10) +
      (∑ h : Hypervertex M.graph,
        ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2)) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (LargeBody M.graph)))
    (fun C _ => L.large_body_budget hgen hp C)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  rw [sum_largeBodies_eq_sum (M := M) (bodyBaseCredit M)
      (fun C hc => (small_body_credits_zero M C hc).1),
    sum_largeBodies_eq_sum (M := M) (bodyHyperCredit M)
      (fun C hc => (small_body_credits_zero M C hc).2.1),
    sum_largeBodies_eq_sum (M := M) (bodyShortfall M)
      (fun C hc => (small_body_credits_zero M C hc).2.2),
    sum_bodyHyperCredit,sum_bodyShortfall] at h
  exact h

theorem SoftScalarSystem.remaining_charge_le_residual
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (exceptionalCountAt L h : ℝ) / 2 + (chargedCoreCountAt M h.val 3 : ℝ) / 4 +
      (chargedCoreCountAt M h.val 4 : ℝ) / 2 ≤
        ((deletionRankDrop M.graph h.val : ℝ) - 6) / 2 := by
  have hnat := L.remaining_hypervertex_charges hgen hp h
  have hreal : (12 : ℝ) + 2 * exceptionalCountAt L h + chargedCoreCountAt M h.val 3 +
      2 * chargedCoreCountAt M h.val 4 ≤ 2 * deletionRankDrop M.graph h.val := by
    exact_mod_cast hnat
  linarith

/-- The actual hypervertex contribution pays scalar observation,
selected-core incidences, and every remaining exceptional charge. -/
theorem SoftScalarSystem.hypervertex_excess_pays
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (L.hyperCredit h : ℝ) / 2 + 3 * (selectedIncidentCount M h.val : ℝ) / 10 +
      (exceptionalCountAt L h : ℝ) / 2 +
      ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2) ≤
        L.vertexExcess h.val := by
  have hcontribution := L.hypervertex_contribution_bound hgen hp h
  have hcharge := L.remaining_charge_le_residual hgen hp h
  change _ ≤ (M.graph.degree h.val : ℝ) / 2 -
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel h.val - 3
  linarith

theorem SoftScalarSystem.observer_cost_le_total_excess
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (∑ h : Hypervertex M.graph, (L.hyperCredit h : ℝ) / 2) +
      (∑ C : LargeBody M.graph, (L.largeRank C : ℝ) / 2) +
      (∑ h : Hypervertex M.graph, (exceptionalCountAt L h : ℝ) / 2) ≤
        ∑ v : V, L.vertexExcess v := by
  have hbody := L.total_body_budget hgen hp
  have htwo := L.two_body_total_excess_bound hgen hp
  have hhyper := Finset.sum_le_sum (s := (Finset.univ : Finset (Hypervertex M.graph)))
    (fun h _ => L.hypervertex_excess_pays hgen hp h)
  simp only [Finset.sum_add_distrib] at hbody hhyper
  have hpartition : (∑ v : V, L.vertexExcess v) =
      (∑ v : V, if IsHypervertex M.graph v then 0 else L.vertexExcess v) +
      (∑ h : Hypervertex M.graph, L.vertexExcess h.val) := by
    rw [sum_subtype_as_indicator,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : IsHypervertex M.graph v <;> simp [hv]
  rw [hpartition]
  linarith

/-- Proposition 6.6 closes the global account for the actual scalar
span, with the exceptional components counted exactly once. -/
theorem SoftScalarSystem.scalar_rank_le_total_excess
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    (Module.finrank ℝ L.scalarSpan : ℝ) ≤ ∑ v : V, L.vertexExcess v := by
  have hnat := L.proposition_six_six hgen hp hpin
  have hreal : 2 * (Module.finrank ℝ L.scalarSpan : ℝ) ≤
      (∑ h : Hypervertex M.graph, (L.hyperCredit h : ℝ)) +
      (∑ C : LargeBody M.graph, (L.largeRank C : ℝ)) +
      (ObserverCover.exceptionalCount L.graph L.seed : ℝ) := by exact_mod_cast hnat
  have hcount : (ObserverCover.exceptionalCount L.graph L.seed : ℝ) =
      ∑ h : Hypervertex M.graph, (exceptionalCountAt L h : ℝ) := by
    exact_mod_cast (L.sum_exceptionalCountAt hgen hp hpin).symm
  rw [hcount] at hreal
  apply le_trans _ (L.observer_cost_le_total_excess hgen hp)
  rw [← Finset.sum_div,← Finset.sum_div,← Finset.sum_div]
  linarith

theorem SoftScalarSystem.total_excess_ledger
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p) :
    (genericRigidityRank M.graph 3 : ℝ) + Module.finrank ℝ L.scalarSpan =
      3 * (Fintype.card V : ℝ) + ∑ v : V, L.vertexExcess v := by
  have hwhole : maskedGraph M.graph Finset.univ = M.graph := by
    ext a b
    simp [maskedGraph]
  have hdegree (v : V) : (maskedGraph M.graph Finset.univ).degree v = M.graph.degree v := by
    rw [hwhole]
  have hrank : genericRigidityRank (maskedGraph M.graph Finset.univ) 3 =
      genericRigidityRank M.graph 3 := by rw [hwhole]
  have h := scalar_annihilator_rank_ledger (maskedGraph M.graph Finset.univ) p hgen L.scalarSpan
  change (genericRigidityRank (maskedGraph M.graph Finset.univ) 3 : ℝ) =
    (∑ v : V, (((maskedGraph M.graph Finset.univ).degree v : ℝ) / 2 -
      stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v)) -
      Module.finrank ℝ L.scalarSpan at h
  simp only [hrank,hdegree,Finset.sum_sub_distrib] at h
  simp only [SoftScalarSystem.vertexExcess,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  linarith

/-- The final contradiction is an actual rigidity-rank contradiction.
There is no numerical budget or geometric conclusion among its premises. -/
theorem SoftScalarSystem.contradiction
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) : False := by
  have hcost := L.scalar_rank_le_total_excess hgen hp hpin
  have hledger := L.total_excess_ledger hgen
  have hcard := M.eight_le_card
  have hcomplete := genericCompleteRank_add_six (V := V) (by omega)
  have hle : genericRigidityRank M.graph 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph V) 3 := genericRigidityRank_mono le_top
  have hcompleteR : (genericRigidityRank (SimpleGraph.completeGraph V) 3 : ℝ) + 6 =
      3 * (Fintype.card V : ℝ) := by exact_mod_cast hcomplete
  have hleR : (genericRigidityRank M.graph 3 : ℝ) ≤
      (genericRigidityRank (SimpleGraph.completeGraph V) 3 : ℝ) := by exact_mod_cast hle
  linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0062

section BundleSource0063
/- Source: Papers/RigidityFinalTheorems.lean -/




@[expose] public section

/-!
# The principal rigidity theorem and its two completion corollaries

These statements retain all finite graphs and the original definitions
of vertex connectivity, K4 coverage, generic rigidity, and ambient
rigid clusters. The proof chooses one placement satisfying all proved
genericity requirements, constructs its actual soft-force coordinates,
and applies the global rank contradiction.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint BodyLoads
open scoped Classical

theorem minimalCounterexample_false {V : Type} [Fintype V]
    (M : MinimalCounterexample V) : False := by
  obtain ⟨p,hgen,hp,hpin⟩ :=
    PairPinGraph.exists_generic_generalPosition_universalPin (V := V) (B := Body M.graph)
  obtain ⟨L⟩ := exists_softScalarSystem M p hgen hp
  exact L.contradiction hgen hp hpin

/-- Theorem 1.1 in precisely the unrestricted form recorded in the
statement module. -/
theorem theorem_one_one : SixConnectedK4RigidityClaim := by
  by_contra hfalse
  obtain ⟨V,hV,⟨M⟩⟩ := exists_minimalCounterexample hfalse
  letI : Fintype V := hV
  exact minimalCounterexample_false M

/-- Theorem 1.1, with the finite graph and hypotheses exposed directly. -/
theorem sixConnected_k4Covered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : K4Covered G) :
    IsGenericallyRigidInR3 G := theorem_one_one V G hconn hcover

/-- Corollary 1.2: actual generically rigid edge-covering subgraphs may
have arbitrary order at least four and may omit edges of the induced graph. -/
theorem corollary_one_two_rigid_subgraph_cover : RigidClusterCoveredRigidityClaim :=
  rigidClusterCoveredRigidity_of_sixConnectedK4Rigidity theorem_one_one

/-- The more general spanning-completion assertion of Corollary 1.2,
with rigidity in the ambient graph rather than an induced-clique assumption. -/
theorem corollary_one_two_rigid_cluster_completion : RigidClusterCompletionRigidityClaim :=
  rigidClusterCompletionRigidity_of_sixConnectedK4Rigidity theorem_one_one

theorem sixConnected_rigidSubgraphCovered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : RigidSubgraphCovered G) :
    IsGenericallyRigidInR3 G := corollary_one_two_rigid_subgraph_cover V G hconn hcover

theorem rigidCluster_completion_sixConnected_rigid
    {V I : Type} [Fintype V] (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6) : IsGenericallyRigidInR3 G :=
  corollary_one_two_rigid_cluster_completion V I G C hC hconn

end Papers.Rigidity

end
end
end BundleSource0063

section BundleSource0064
/- Source: Papers/RigidityLocalRigidity.lean -/



@[expose] public section

/-!
# Local distance rigidity and the actual generic rank

A framework is locally rigid when every sufficiently nearby framework
with the same graph-edge lengths has all the same pairwise distances.
The equivalence below is proved using the genuine length-fiber chart,
not by defining local rigidity in terms of the rigidity matrix.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open Filter
open scoped Topology Classical

variable {V : Type} [Fintype V] {d : ℕ}

/-- Local rigidity stated directly through the real squared distances.
This formulation of congruence includes degenerate finite frameworks. -/
def IsLocallyDistanceRigid (G : SimpleGraph V) (p : Placement V d) : Prop :=
  ∀ᶠ q in 𝓝 p, squaredLengthMap G q = squaredLengthMap G p →
    squaredLengthMap (SimpleGraph.completeGraph V) q =
      squaredLengthMap (SimpleGraph.completeGraph V) p

def lengthMask (G : SimpleGraph V) : (V × V → ℝ) →L[ℝ] (V × V → ℝ) :=
  LinearMap.toContinuousLinearMap <|
    LinearMap.pi fun e => if G.Adj e.1 e.2 then LinearMap.proj e else 0

@[simp] theorem lengthMask_apply (G : SimpleGraph V) (l : V × V → ℝ) (e : V × V) :
    lengthMask G l e = if G.Adj e.1 e.2 then l e else 0 := by
  by_cases h : G.Adj e.1 e.2 <;>
    simp [lengthMask, LinearMap.coe_toContinuousLinearMap', h]

theorem lengthMask_complete (G : SimpleGraph V) (p : Placement V d) :
    lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) p) =
      squaredLengthMap G p := by
  ext e
  by_cases h : G.Adj e.1 e.2
  · simp [lengthMask_apply, squaredLengthMap, h, h.ne]
  · simp [lengthMask_apply, squaredLengthMap, h]

theorem lengthMask_derivative (G : SimpleGraph V) (p : Placement V d) :
    (lengthMask G).comp (fderiv ℝ (squaredLengthMap (SimpleGraph.completeGraph V)) p) =
      fderiv ℝ (squaredLengthMap G) p := by
  have h := (lengthMask G).hasFDerivAt.comp p
    (squaredLengthMap_hasFDerivAt (SimpleGraph.completeGraph V) p)
  rw [← fderiv_squaredLengthMap] at h
  change HasFDerivAt (fun q : Placement V d =>
    lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) q)) _ p at h
  have heq : (fun q : Placement V d =>
      lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) q)) =
      squaredLengthMap G := funext (lengthMask_complete G)
  rw [heq] at h
  exact h.fderiv.symm

/-- At a simultaneous maximum-rank placement, infinitesimal rigidity
forces actual local rigidity of the full Euclidean distance constraints. -/
theorem IsGenericallyRigidInDimension.isLocallyDistanceRigid
    {G : SimpleGraph V} (hG : IsGenericallyRigidInDimension G d)
    (p : Placement V d) (hp : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  let K := SimpleGraph.completeGraph V
  let P := lengthMask G
  let T := (rigidityOperator G p).ker
  let C := maximumRankLengthFiberChart G p (hp G)
  have heq : (fun q : Placement V d => P (squaredLengthMap K q)) =
      squaredLengthMap G := funext (lengthMask_complete G)
  have C' : Calculus.SmoothLevelChart
      (fun q => P (squaredLengthMap K q)) p T := by
    rw [heq]
    exact C
  have hnear : ∀ᶠ q in 𝓝 p,
      (P.comp (fderiv ℝ (squaredLengthMap K) q)).ker ≤
        (fderiv ℝ (squaredLengthMap K) q).ker := by
    filter_upwards [isOpen_isGenericPlacement.mem_nhds hp] with q hq
    rw [lengthMask_derivative, ker_fderiv_squaredLengthMap,
      ker_fderiv_squaredLengthMap]
    exact (ker_eq_of_le_of_genericRigidityRank_eq
      (show G ≤ K from le_top) hG q hq).symm.le
  let D := C'.of_projection (squaredLengthMap K) P p T
    (squaredLengthMap_contDiff K).contDiffAt hnear
  filter_upwards [C'.fiber_iff, D.fiber_iff] with q hC hD
  intro hq
  apply hD.mpr
  apply hC.mp
  simpa only [P, K, lengthMask_complete] using hq

/-- A real local length-preserving fiber cannot have an infinitesimal
direction changing a complete-graph distance at a maximum-rank point. -/
theorem ker_le_complete_of_isLocallyDistanceRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hlocal : IsLocallyDistanceRigid G p) :
    (rigidityOperator G p).ker ≤
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  let K := SimpleGraph.completeGraph V
  let C := maximumRankLengthFiberChart G p hp
  have hψ : Tendsto C.parametrization
      (𝓝 (0 : (rigidityOperator G p).ker)) (𝓝 p) := by
    simpa only [C.parametrization_zero] using
      C.smooth_parametrization.continuousAt.tendsto
  have hlevel : (fun u => squaredLengthMap K (C.parametrization u)) =ᶠ[𝓝 0]
      (fun _ => squaredLengthMap K p) := by
    filter_upwards [C.level, hψ.eventually hlocal] with u hu hlocalu
    exact hlocalu hu
  have hfull : HasFDerivAt (squaredLengthMap K)
      (LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator K p))
      (C.parametrization 0) := by
    rw [C.parametrization_zero]
    exact squaredLengthMap_hasFDerivAt K p
  have hD := hfull.comp (0 : (rigidityOperator G p).ker) C.tangent.hasFDerivAt
  have hzero : (fderiv ℝ (squaredLengthMap K) p).comp
      (rigidityOperator G p).ker.subtypeL = 0 := by
    rw [fderiv_squaredLengthMap]
    exact hD.fderiv.symm.trans ((Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlevel).trans (fderiv_const_apply _))
  intro u hu
  rw [← ker_fderiv_squaredLengthMap]
  exact congrArg
    (fun A : (rigidityOperator G p).ker →L[ℝ] (V × V → ℝ) => A ⟨u, hu⟩) hzero

/-- Local distance rigidity and generic rigidity rank are equivalent at
every simultaneous regular placement, in every dimension and for every
finite graph. No affine-spanning or cardinality premise is added. -/
theorem isLocallyDistanceRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (p : Placement V d) (hp : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · intro hlocal
    have hker := ker_le_complete_of_isLocallyDistanceRigid G p (hp G) hlocal
    have hr := rigidityRank_le_of_ker_le
      (SimpleGraph.completeGraph V) G p hker
    have hGrank : rigidityRank G p = genericRigidityRank G d := hp G
    have hKrank : rigidityRank (SimpleGraph.completeGraph V) p =
        genericRigidityRank (SimpleGraph.completeGraph V) d := hp (SimpleGraph.completeGraph V)
    rw [hGrank, hKrank] at hr
    change genericRigidityRank G d =
      genericRigidityRank (SimpleGraph.completeGraph V) d
    exact le_antisymm (genericRigidityRank_mono le_top) hr
  · intro hG
    exact hG.isLocallyDistanceRigid p hp

theorem isGenericallyRigid_iff_all_generic_locallyDistanceRigid
    (G : SimpleGraph V) :
    IsGenericallyRigidInDimension G d ↔
      ∀ p : Placement V d, IsGenericPlacement p → IsLocallyDistanceRigid G p := by
  constructor
  · exact fun hG p hp => hG.isLocallyDistanceRigid p hp
  · intro h
    obtain ⟨p, hp⟩ := exists_isGenericPlacement (V := V) d
    exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hp).mp (h p hp)

end

end Papers.Rigidity.BarJoint

end
end BundleSource0064

section BundleSource0065
/- Source: Papers/RigidityFinalSemantics.lean -/





@[expose] public section

/-!
# The principal graph theorems as actual Euclidean rigidity statements

These wrappers use the proved equivalence between the maximum-rank
definition and local preservation of all pairwise distances. The last
statement identifies the actual infinitesimal motion kernel with the
translations and rotations of Euclidean three-space. No equivalence is
assumed as an extra premise.
-/

namespace Papers.Rigidity

open BarJoint

variable {V : Type} [Fintype V]

/-- Theorem 1.1 in the direct local-distance formulation: every sufficiently
nearby placement with the same graph-edge lengths has all the same
pairwise distances. -/
theorem sixConnected_k4Covered_locallyDistanceRigid
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (sixConnected_k4Covered_rigid G hconn hcover)

/-- The edge-cover form of Corollary 1.2, with literal local-distance
rigidity as its conclusion. -/
theorem sixConnected_rigidSubgraphCovered_locallyDistanceRigid
    (G : SimpleGraph V) (hconn : VertexConnected G 6)
    (hcover : RigidSubgraphCovered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (sixConnected_rigidSubgraphCovered_rigid G hconn hcover)

/-- The ambient-cluster form of Corollary 1.2, with all labels retained
and literal local-distance rigidity as its conclusion. -/
theorem rigidCluster_completion_sixConnected_locallyDistanceRigid
    {I : Type} (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (rigidCluster_completion_sixConnected_rigid G C hC hconn)

/-- Theorem 1.1 in literal infinitesimal-motion form. At every generic
general-position placement, every graph motion is a global Euclidean
twist, and every global Euclidean twist is a graph motion. -/
theorem sixConnected_k4Covered_motionKernel_eq_globalTwists
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (rigidityOperator G p).ker = (globalTwistOperator p).range := by
  have hrig := sixConnected_k4Covered_rigid G hconn hcover
  have hker := ker_eq_of_le_of_genericRigidityRank_eq
    (show G ≤ SimpleGraph.completeGraph V from le_top) hrig p hgen
  exact hker.symm.trans (complete_kernel_eq_twist_range_all p hp)

end Papers.Rigidity

end
end BundleSource0065

section BundleSource0066
/- Source: Papers/RigiditySharpnessGraph.lean -/






@[expose] public section

/-!
# A five-connected flexible graph

This is the instance `t = 7` of Jackson--Jordán--Villányi,
Example 7.5. There are five rows and seven cyclic cells in each row.
Each cell is a complete graph on five vertices. Its first two vertices
are left ports, the next two right ports, and the last its hub.
The right pair of each cell is completely joined to the left pair of
the next cell. The five hubs in each column form another complete graph.

The graph has 175 vertices. The other sharpness modules prove its
five-connectivity and the strict rank bound 518 < 519.
-/

namespace Papers.Rigidity.Sharpness

open BarJoint

abbrev Row := Fin 5
abbrev Cell := Fin 7
abbrev Slot := Fin 5
abbrev Vertex := Row × Cell × Slot

def vertex (r : Row) (c : Cell) (s : Slot) : Vertex := (r, c, s)

def hub (r : Row) (c : Cell) : Vertex := vertex r c 4
def left (r : Row) (c : Cell) (a : Fin 2) : Vertex := vertex r c (a.castLE (by decide))
def right (r : Row) (c : Cell) (a : Fin 2) : Vertex := vertex r c ⟨a.val + 2, by omega⟩

/-- The direct adjacency description keeps every vertex and edge explicit. -/
def graph : SimpleGraph Vertex where
  Adj u v := u ≠ v ∧
    ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
      (u.2.2 = 4 ∧ v.2.2 = 4 ∧ u.2.1 = v.2.1) ∨
      (u.1 = v.1 ∧ 2 ≤ u.2.2.val ∧ u.2.2.val < 4 ∧
        v.2.2.val < 2 ∧ v.2.1 = u.2.1 + 1) ∨
      (u.1 = v.1 ∧ 2 ≤ v.2.2.val ∧ v.2.2.val < 4 ∧
        u.2.2.val < 2 ∧ u.2.1 = v.2.1 + 1))
  symm := by
    constructor
    rintro u v ⟨hne, hcell | hhub | hright | hleft⟩
    · exact ⟨hne.symm, Or.inl ⟨hcell.1.symm, hcell.2.symm⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hhub.2.1, hhub.1, hhub.2.2.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr
        ⟨hright.1.symm, hright.2⟩))⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl
        ⟨hleft.1.symm, hleft.2⟩))⟩
  loopless := by constructor; intro u; simp

instance : DecidableRel graph.Adj := fun _ _ => by
  dsimp [graph]
  infer_instance

theorem same_cell_adj (r : Row) (c : Cell) {s t : Slot} (hne : s ≠ t) :
    graph.Adj (vertex r c s) (vertex r c t) := by
  refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
  exact fun h => hne (congrArg (fun v : Vertex => v.2.2) h)

theorem hubs_adj {r t : Row} (c : Cell) (hne : r ≠ t) :
    graph.Adj (hub r c) (hub t c) := by
  refine ⟨?_, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  exact fun h => hne (congrArg (fun v : Vertex => v.1) h)

theorem bridge_adj (r : Row) (c : Cell) (a b : Fin 2) :
    graph.Adj (right r c a) (left r (c + 1) b) := by
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_, rfl⟩))⟩
  · intro h
    have hs := congrArg (fun v : Vertex => v.2.2.val) h
    change a.val + 2 = b.val at hs
    omega
  · change 2 ≤ a.val + 2
    omega
  · change a.val + 2 < 4
    omega
  · exact b.isLt

def cellVertices (r : Row) (c : Cell) : Finset Vertex :=
  Finset.univ.image (vertex r c)

def hubVertices (c : Cell) : Finset Vertex :=
  Finset.univ.image (fun r => hub r c)

def bridgeVertices (r : Row) (c : Cell) : Finset Vertex :=
  {right r c 0, right r c 1, left r (c + 1) 0, left r (c + 1) 1}

theorem cellVertices_card (r : Row) (c : Cell) : (cellVertices r c).card = 5 := by
  rw [cellVertices, Finset.card_image_of_injective]
  · simp
  · intro s t h
    exact congrArg (fun v : Vertex => v.2.2) h

theorem hubVertices_card (c : Cell) : (hubVertices c).card = 5 := by
  rw [hubVertices, Finset.card_image_of_injective]
  · simp
  · intro r t h
    exact congrArg (fun v : Vertex => v.1) h

theorem cellVertices_clique (r : Row) (c : Cell) :
    graph.IsClique (cellVertices r c : Set Vertex) := by
  rintro u hu v hv hne
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  exact same_cell_adj r c (fun h => hne (congrArg (vertex r c) h))

theorem hubVertices_clique (c : Cell) :
    graph.IsClique (hubVertices c : Set Vertex) := by
  rintro u hu v hv hne
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  exact hubs_adj c (fun h => hne (congrArg (fun r => hub r c) h))

theorem bridgeVertices_card (r : Row) (c : Cell) :
    (bridgeVertices r c).card = 4 := by
  simp [bridgeVertices, right, left, vertex]

theorem bridgeVertices_clique (r : Row) (c : Cell) :
    graph.IsClique (bridgeVertices r c : Set Vertex) := by
  intro u hu v hv hne
  simp only [bridgeVertices, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp_all [graph, right, left, vertex]

theorem right_mem_bridgeVertices (r : Row) (c : Cell) (a : Fin 2) :
    right r c a ∈ bridgeVertices r c := by
  fin_cases a <;> simp [bridgeVertices]

theorem left_mem_bridgeVertices (r : Row) (c : Cell) (a : Fin 2) :
    left r (c + 1) a ∈ bridgeVertices r c := by
  fin_cases a <;> simp [bridgeVertices]

/-- Every edge has an actual covering clique of order four or five. -/
theorem exists_covering_clique {u v : Vertex} (hadj : graph.Adj u v) :
    ∃ S : Finset Vertex, 4 ≤ S.card ∧ u ∈ S ∧ v ∈ S ∧
      graph.IsClique (S : Set Vertex) := by
  rcases u with ⟨r, c, s⟩
  rcases v with ⟨t, d, k⟩
  change (r, c, s) ≠ (t, d, k) ∧
    ((r = t ∧ c = d) ∨ (s = 4 ∧ k = 4 ∧ c = d) ∨
      (r = t ∧ 2 ≤ s.val ∧ s.val < 4 ∧ k.val < 2 ∧ d = c + 1) ∨
      (r = t ∧ 2 ≤ k.val ∧ k.val < 4 ∧ s.val < 2 ∧ c = d + 1)) at hadj
  rcases hadj with ⟨_, hcell | hhub | hright | hleft⟩
  · rcases hcell with ⟨rfl, rfl⟩
    refine ⟨cellVertices r c, by rw [cellVertices_card]; decide,
      ?_, ?_, cellVertices_clique r c⟩
    · exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · rcases hhub with ⟨rfl, rfl, rfl⟩
    refine ⟨hubVertices c, by rw [hubVertices_card]; decide,
      ?_, ?_, hubVertices_clique c⟩
    · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · rcases hright with ⟨rfl, hslo, hshi, hk, rfl⟩
    let a : Fin 2 := ⟨s.val - 2, by omega⟩
    let b : Fin 2 := ⟨k.val, hk⟩
    have heqs : right r c a = vertex r c s := by
      apply congrArg (vertex r c)
      apply Fin.ext
      change s.val - 2 + 2 = s.val
      omega
    have heqk : left r (c + 1) b = vertex r (c + 1) k := rfl
    refine ⟨bridgeVertices r c, by rw [bridgeVertices_card],
      ?_, ?_, bridgeVertices_clique r c⟩
    · change vertex r c s ∈ bridgeVertices r c
      rw [← heqs]
      exact right_mem_bridgeVertices r c a
    · change vertex r (c + 1) k ∈ bridgeVertices r c
      rw [← heqk]
      exact left_mem_bridgeVertices r c b
  · rcases hleft with ⟨rfl, hklo, hkhi, hs, rfl⟩
    let a : Fin 2 := ⟨k.val - 2, by omega⟩
    let b : Fin 2 := ⟨s.val, hs⟩
    have heqk : right r d a = vertex r d k := by
      apply congrArg (vertex r d)
      apply Fin.ext
      change k.val - 2 + 2 = k.val
      omega
    have heqs : left r (d + 1) b = vertex r (d + 1) s := rfl
    refine ⟨bridgeVertices r d, by rw [bridgeVertices_card],
      ?_, ?_, bridgeVertices_clique r d⟩
    · change vertex r (d + 1) s ∈ bridgeVertices r d
      rw [← heqs]
      exact left_mem_bridgeVertices r d b
    · change vertex r d k ∈ bridgeVertices r d
      rw [← heqk]
      exact right_mem_bridgeVertices r d a

theorem k4Covered : K4Covered graph := by
  intro u v hadj
  obtain ⟨S, hcard, hu, hv, hclique⟩ := exists_covering_clique hadj
  have hcovered := clusterCompletion_k4Covered (fun _ : Unit => S) (fun _ => hcard)
  obtain ⟨T, hTcard, huT, hvT, hTclique⟩ := hcovered u v ⟨hadj.1, (), hu, hv⟩
  refine ⟨T, hTcard, huT, hvT, SimpleGraph.IsClique.mono ?_ hTclique⟩
  rintro x y ⟨hne, _, hx, hy⟩
  exact hclique hx hy hne

theorem card_vertex : Fintype.card Vertex = 175 := by
  norm_num [Vertex, Row, Cell, Slot]

end Papers.Rigidity.Sharpness

end
end BundleSource0066

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0066/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0066.json"

section BundleSource0067
/- Source: Papers/RigiditySharpnessConnectivity.lean -/




@[expose] public section

/-!
# Five-connectivity of the sharpness graph

Every vertex has five routes to row hubs whose prescribed vertices are
pairwise disjoint. The initial step to each route stays inside the vertex's
own complete cell. Four deleted vertices cannot meet all five routes.

There is also a row containing no deleted vertex. Its cyclic chain of
complete cells is connected, and the vertical hub cliques connect every
surviving vertex to that row. The proof handles every set of fewer than
five deleted vertices without enumerating such deletion sets.
-/

namespace Papers.Rigidity.Sharpness

private abbrev Remaining (S : Finset Vertex) := graph.induce ((S : Set Vertex)ᶜ)

/-- Offsets and slots of five disjoint routes, including their terminal hubs. -/
private def fanTemplate (i : Fin 5) : Finset (Cell × Slot) :=
  match i.val with
  | 0 => {(0,4)}
  | 1 => {(0,2),(1,0),(1,4)}
  | 2 => {(0,3),(1,1),(1,3),(2,1),(2,4)}
  | 3 => {(0,0),(6,2),(6,4)}
  | _ => {(0,1),(6,3),(6,1),(5,3),(5,4)}

private theorem fanTemplate_disjoint :
    ∀ i j : Fin 5, i ≠ j → Disjoint (fanTemplate i) (fanTemplate j) := by
  decide

private def shiftVertex (r : Row) (c : Cell) (z : Cell × Slot) : Vertex :=
  vertex r (c + z.1) z.2

private theorem shiftVertex_injective (r : Row) (c : Cell) :
    Function.Injective (shiftVertex r c) := by
  intro z w h
  have hc : c + z.1 = c + w.1 := congrArg (fun v : Vertex => v.2.1) h
  have hs : z.2 = w.2 := congrArg (fun v : Vertex => v.2.2) h
  exact Prod.ext (add_left_cancel hc) hs

private def fanVertices (r : Row) (c : Cell) (i : Fin 5) : Finset Vertex :=
  (fanTemplate i).image (shiftVertex r c)

private theorem fanVertices_disjoint (r : Row) (c : Cell) {i j : Fin 5}
    (hij : i ≠ j) : Disjoint (fanVertices r c i) (fanVertices r c j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp hj
  have hwz := shiftVertex_injective r c heq
  exact Finset.disjoint_left.mp (fanTemplate_disjoint i j hij) hz (hwz ▸ hw)

private theorem exists_untouched_fan (S : Finset Vertex) (hS : S.card < 5)
    (r : Row) (c : Cell) : ∃ i : Fin 5, Disjoint (fanVertices r c i) S := by
  classical
  by_contra hnone
  have hex (i : Fin 5) : ∃ v, v ∈ fanVertices r c i ∧ v ∈ S := by
    by_contra hmissing
    apply hnone
    refine ⟨i,Finset.disjoint_left.mpr ?_⟩
    intro v hv hs
    exact hmissing ⟨v,hv,hs⟩
  choose v hv hvs using hex
  let f : Fin 5 → S := fun i => ⟨v i,hvs i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (fanVertices_disjoint r c hne)
      (hv i) (heq.symm ▸ hv j)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_coe] at hcard
  omega

private theorem withinCell (S : Finset Vertex) (r : Row) (c : Cell)
    (s t : Slot) (hs : vertex r c s ∉ S) (ht : vertex r c t ∉ S) :
    (Remaining S).Reachable ⟨vertex r c s,hs⟩ ⟨vertex r c t,ht⟩ := by
  by_cases hst : s = t
  · subst t
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact same_cell_adj r c hst

private theorem acrossBridge (S : Finset Vertex) (r : Row) (c d : Cell)
    (hd : d = c + 1) (a b : Fin 2)
    (ha : right r c a ∉ S) (hb : left r d b ∉ S) :
    (Remaining S).Reachable ⟨right r c a,ha⟩ ⟨left r d b,hb⟩ := by
  apply SimpleGraph.Adj.reachable
  change graph.Adj (right r c a) (left r d b)
  subst d
  exact bridge_adj r c a b

private theorem betweenHubs (S : Finset Vertex) (r t : Row) (c : Cell)
    (hr : hub r c ∉ S) (ht : hub t c ∉ S) :
    (Remaining S).Reachable ⟨hub r c,hr⟩ ⟨hub t c,ht⟩ := by
  by_cases hrt : r = t
  · subst t
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact hubs_adj c hrt

private theorem next_two (c : Cell) : (c + 1) + 1 = c + 2 := by
  rw [add_assoc]
  rfl

private theorem previous_next (c : Cell) : (c + 6) + 1 = c := by
  rw [add_assoc]
  change c + 0 = c
  exact add_zero c

private theorem previous_two_next (c : Cell) : (c + 5) + 1 = c + 6 := by
  rw [add_assoc]
  rfl

/-- A surviving vertex reaches a surviving hub in its own row. -/
private theorem reachable_row_hub (S : Finset Vertex) (hS : S.card < 5)
    (r : Row) (c : Cell) (s : Slot) (hs : vertex r c s ∉ S) :
    ∃ d : Cell, ∃ hd : hub r d ∉ S,
      (Remaining S).Reachable ⟨vertex r c s,hs⟩ ⟨hub r d,hd⟩ := by
  obtain ⟨i,hi⟩ := exists_untouched_fan S hS r c
  have ha (z : Cell × Slot) (hz : z ∈ fanTemplate i) : shiftVertex r c z ∉ S := by
    intro hzs
    exact Finset.disjoint_left.mp hi (Finset.mem_image.mpr ⟨z,hz,rfl⟩) hzs
  fin_cases i
  · have hh : hub r c ∉ S := by
      change vertex r c 4 ∉ S
      simpa only [shiftVertex,add_zero] using ha (0,4) (by decide)
    exact ⟨c,hh,withinCell S r c s 4 hs hh⟩
  · have h02 : vertex r c 2 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,2) (by decide)
    have h10 : vertex r (c+1) 0 ∉ S := ha (1,0) (by decide)
    have hh : hub r (c+1) ∉ S := ha (1,4) (by decide)
    exact ⟨c+1,hh,(withinCell S r c s 2 hs h02).trans
      ((acrossBridge S r c (c+1) rfl 0 0 h02 h10).trans
        (withinCell S r (c+1) 0 4 h10 hh))⟩
  · have h03 : vertex r c 3 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,3) (by decide)
    have h11 : vertex r (c+1) 1 ∉ S := ha (1,1) (by decide)
    have h13 : vertex r (c+1) 3 ∉ S := ha (1,3) (by decide)
    have h21 : vertex r (c+2) 1 ∉ S := ha (2,1) (by decide)
    have hh : hub r (c+2) ∉ S := ha (2,4) (by decide)
    exact ⟨c+2,hh,(withinCell S r c s 3 hs h03).trans
      ((acrossBridge S r c (c+1) rfl 1 1 h03 h11).trans
        ((withinCell S r (c+1) 1 3 h11 h13).trans
          ((acrossBridge S r (c+1) (c+2) (next_two c).symm 1 1 h13 h21).trans
            (withinCell S r (c+2) 1 4 h21 hh))))⟩
  · have h00 : vertex r c 0 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,0) (by decide)
    have h62 : vertex r (c+6) 2 ∉ S := ha (6,2) (by decide)
    have hh : hub r (c+6) ∉ S := ha (6,4) (by decide)
    exact ⟨c+6,hh,(withinCell S r c s 0 hs h00).trans
      ((acrossBridge S r (c+6) c (previous_next c).symm 0 0 h62 h00).symm.trans
        (withinCell S r (c+6) 2 4 h62 hh))⟩
  · have h01 : vertex r c 1 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,1) (by decide)
    have h63 : vertex r (c+6) 3 ∉ S := ha (6,3) (by decide)
    have h61 : vertex r (c+6) 1 ∉ S := ha (6,1) (by decide)
    have h53 : vertex r (c+5) 3 ∉ S := ha (5,3) (by decide)
    have hh : hub r (c+5) ∉ S := ha (5,4) (by decide)
    exact ⟨c+5,hh,(withinCell S r c s 1 hs h01).trans
      ((acrossBridge S r (c+6) c (previous_next c).symm 1 1 h63 h01).symm.trans
        ((withinCell S r (c+6) 3 1 h63 h61).trans
          ((acrossBridge S r (c+5) (c+6) (previous_two_next c).symm 1 1 h53 h61).symm.trans
            (withinCell S r (c+5) 3 4 h53 hh))))⟩

private theorem exists_intact_row (S : Finset Vertex) (hS : S.card < 5) :
    ∃ r : Row, ∀ c s, vertex r c s ∉ S := by
  have hex : ∃ r : Row, r ∉ S.image (fun v => v.1) := by
    by_contra hnone
    push_neg at hnone
    have hsub : (Finset.univ : Finset Row) ⊆ S.image (fun v => v.1) :=
      fun r _ => hnone r
    have hcard := Finset.card_le_card hsub
    have himage := Finset.card_image_le (s := S) (f := fun v => v.1)
    simp only [Finset.card_univ,Fintype.card_fin] at hcard
    omega
  obtain ⟨r,hr⟩ := hex
  refine ⟨r,?_⟩
  intro c s h
  exact hr (Finset.mem_image.mpr ⟨vertex r c s,h,rfl⟩)

private theorem intact_row_hubs_connected (S : Finset Vertex) (r : Row)
    (hr : ∀ c s, vertex r c s ∉ S) (c : Cell) :
    (Remaining S).Reachable ⟨hub r 0,hr 0 4⟩ ⟨hub r c,hr c 4⟩ := by
  have hstep (d : Cell) :
      (Remaining S).Reachable ⟨hub r d,hr d 4⟩ ⟨hub r (d+1),hr (d+1) 4⟩ :=
    (withinCell S r d 4 2 (hr d 4) (hr d 2)).trans
      ((acrossBridge S r d (d+1) rfl 0 0 (hr d 2) (hr (d+1) 0)).trans
        (withinCell S r (d+1) 0 4 (hr (d+1) 0) (hr (d+1) 4)))
  have hsucc : ∀ i : Fin 6, (i.castSucc + 1 : Cell) = i.succ := by decide
  induction c using Fin.induction with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ i ih =>
    have h := hstep i.castSucc
    rw [hsucc i] at h
    exact ih.trans h

/-- The explicit 175-vertex graph remains connected after every deletion
of at most four vertices. This is the sharpness assertion's full connectivity
hypothesis, not a fixed list of tested separators. -/
theorem sharpness_fiveConnected : VertexConnected graph 5 := by
  refine ⟨?_,?_⟩
  · rw [card_vertex]
    decide
  · intro S hS
    obtain ⟨r,hr⟩ := exists_intact_row S hS
    apply (SimpleGraph.connected_iff_exists_forall_reachable (Remaining S)).mpr
    refine ⟨⟨hub r 0,hr 0 4⟩,?_⟩
    intro v
    obtain ⟨⟨t,c,s⟩,hv⟩ := v
    obtain ⟨d,hd,hpath⟩ := reachable_row_hub S hS t c s hv
    exact (intact_row_hubs_connected S r hr d).trans
      ((betweenHubs S t r d hd (hr d 4)).symm.trans hpath.symm)

end Papers.Rigidity.Sharpness

end
end BundleSource0067

section BundleSource0068
/- Source: Papers/RigiditySharpnessRank.lean -/





@[expose] public section

/-!
# The rank obstruction for the sharpness graph

The argument is uniform in all real placements, not a rank calculation
at a selected realization. Every cell contributes at most nine rows,
every vertical hub clique contributes at most nine, and the remaining
140 cross edges contribute at most 140. Thus the actual rigidity rank
is at most `35 * 9 + 7 * 9 + 140 = 518`. The complete graph on the
same 175 vertices has generic rank 519.
-/

noncomputable section
namespace Papers.Rigidity.Sharpness

open BarJoint
open scoped Classical BigOperators

abbrev CellIndex := Row × Cell
abbrev BridgeIndex := Row × Cell × Fin 2 × Fin 2

def cellRestriction (i : CellIndex) :
    Velocity Vertex 3 →ₗ[ℝ] Velocity Slot 3 :=
  LinearMap.pi fun s => LinearMap.proj (vertex i.1 i.2 s)

def hubRestriction (c : Cell) :
    Velocity Vertex 3 →ₗ[ℝ] Velocity Row 3 :=
  LinearMap.pi fun r => LinearMap.proj (hub r c)

def cellOperator (p : Placement Vertex 3) (i : CellIndex) :
    Velocity Vertex 3 →ₗ[ℝ] (Slot × Slot → ℝ) :=
  (rigidityOperator (SimpleGraph.completeGraph Slot) (fun s => p (vertex i.1 i.2 s))).comp
    (cellRestriction i)

def hubOperator (p : Placement Vertex 3) (c : Cell) :
    Velocity Vertex 3 →ₗ[ℝ] (Row × Row → ℝ) :=
  (rigidityOperator (SimpleGraph.completeGraph Row) (fun r => p (hub r c))).comp
    (hubRestriction c)

def bridgeOperator (p : Placement Vertex 3) (i : BridgeIndex) :
    Velocity Vertex 3 →ₗ[ℝ] ℝ :=
  edgeFunctional p (right i.1 i.2.1 i.2.2.1) (left i.1 (i.2.1 + 1) i.2.2.2)

abbrev CoverageTarget (p : Placement Vertex 3) :=
  (∀ i : CellIndex, (cellOperator p i).range) ×
    (∀ c : Cell, (hubOperator p c).range) × (BridgeIndex → ℝ)

/-- The target consists of the actual component ranges, so its
dimension counts their ranks rather than the number of duplicated rows. -/
def coverageOperator (p : Placement Vertex 3) :
    Velocity Vertex 3 →ₗ[ℝ] CoverageTarget p :=
  (LinearMap.pi fun i => (cellOperator p i).rangeRestrict).prod
    ((LinearMap.pi fun c => (hubOperator p c).rangeRestrict).prod
      (LinearMap.pi fun i => bridgeOperator p i))

theorem cellOperator_rank_le_nine (p : Placement Vertex 3) (i : CellIndex) :
    Module.finrank ℝ (cellOperator p i).range ≤ 9 := by
  have hcomp := Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (cellRestriction i)
      (rigidityOperator (SimpleGraph.completeGraph Slot) (fun s => p (vertex i.1 i.2 s))))
  have hmax := rigidityRank_le_genericRigidityRank
    (SimpleGraph.completeGraph Slot) 3 (fun s => p (vertex i.1 i.2 s))
  have hcomplete : genericRigidityRank (SimpleGraph.completeGraph Slot) 3 = 9 := by
    rw [genericCompleteRank_eq (V := Slot) (by decide)]
    decide
  exact hcomp.trans (hmax.trans_eq hcomplete)

theorem hubOperator_rank_le_nine (p : Placement Vertex 3) (c : Cell) :
    Module.finrank ℝ (hubOperator p c).range ≤ 9 := by
  have hcomp := Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (hubRestriction c)
      (rigidityOperator (SimpleGraph.completeGraph Row) (fun r => p (hub r c))))
  have hmax := rigidityRank_le_genericRigidityRank
    (SimpleGraph.completeGraph Row) 3 (fun r => p (hub r c))
  have hcomplete : genericRigidityRank (SimpleGraph.completeGraph Row) 3 = 9 := by
    rw [genericCompleteRank_eq (V := Row) (by decide)]
    decide
  exact hcomp.trans (hmax.trans_eq hcomplete)

theorem coverageTarget_finrank_le (p : Placement Vertex 3) :
    Module.finrank ℝ (CoverageTarget p) ≤ 518 := by
  have hcells : (∑ i : CellIndex, Module.finrank ℝ (cellOperator p i).range) ≤ 315 := by
    calc
      _ ≤ ∑ _ : CellIndex, 9 := Finset.sum_le_sum fun i _ => cellOperator_rank_le_nine p i
      _ = 315 := by norm_num [CellIndex, Row, Cell]
  have hhubs : (∑ c : Cell, Module.finrank ℝ (hubOperator p c).range) ≤ 63 := by
    calc
      _ ≤ ∑ _ : Cell, 9 := Finset.sum_le_sum fun c _ => hubOperator_rank_le_nine p c
      _ = 63 := by norm_num [Cell]
  have hbridges : Module.finrank ℝ (BridgeIndex → ℝ) = 140 := by
    simp [BridgeIndex, Row, Cell, Module.finrank_pi_fintype]
  change Module.finrank ℝ
    ((∀ i : CellIndex, (cellOperator p i).range) ×
      (∀ c : Cell, (hubOperator p c).range) × (BridgeIndex → ℝ)) ≤ 518
  rw [Module.finrank_prod, Module.finrank_prod, hbridges,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  omega

theorem coverage_kernel_le_rigidity_kernel (p : Placement Vertex 3) :
    (coverageOperator p).ker ≤ (rigidityOperator graph p).ker := by
  intro u hu
  have hzero : coverageOperator p u = 0 := hu
  have hcell (r : Row) (c : Cell) : cellOperator p (r, c) u = 0 := by
    exact congrArg (fun y : CoverageTarget p => (y.1 (r, c)).val) hzero
  have hhub (c : Cell) : hubOperator p c u = 0 := by
    exact congrArg (fun y : CoverageTarget p => (y.2.1 c).val) hzero
  have hbridge (r : Row) (c : Cell) (a b : Fin 2) :
      edgeConstraint p u (right r c a) (left r (c + 1) b) = 0 := by
    exact congrArg (fun y : CoverageTarget p => y.2.2 (r, c, a, b)) hzero
  rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
  rintro ⟨r, c, s⟩ ⟨t, d, k⟩ hadj
  change (r, c, s) ≠ (t, d, k) ∧
    ((r = t ∧ c = d) ∨ (s = 4 ∧ k = 4 ∧ c = d) ∨
      (r = t ∧ 2 ≤ s.val ∧ s.val < 4 ∧ k.val < 2 ∧ d = c + 1) ∨
      (r = t ∧ 2 ≤ k.val ∧ k.val < 4 ∧ s.val < 2 ∧ c = d + 1)) at hadj
  rcases hadj with ⟨hne, hsame | hvertical | hforward | hbackward⟩
  · rcases hsame with ⟨rfl, rfl⟩
    have hsk : s ≠ k := fun h => hne (by cases h; rfl)
    have hz := congrFun (hcell r c) (s, k)
    simpa [cellOperator, cellRestriction, rigidityOperator,
      SimpleGraph.completeGraph, SimpleGraph.top_adj, hsk, edgeConstraint, vertex] using hz
  · rcases hvertical with ⟨rfl, rfl, rfl⟩
    have hrt : r ≠ t := fun h => hne (by cases h; rfl)
    have hz := congrFun (hhub c) (r, t)
    simpa [hubOperator, hubRestriction, rigidityOperator,
      SimpleGraph.completeGraph, SimpleGraph.top_adj, hrt, edgeConstraint, hub, vertex] using hz
  · rcases hforward with ⟨rfl, hslo, hshi, hk, rfl⟩
    let a : Fin 2 := ⟨s.val - 2, by omega⟩
    let b : Fin 2 := ⟨k.val, hk⟩
    have hs : right r c a = vertex r c s := by
      apply congrArg (vertex r c)
      apply Fin.ext
      change s.val - 2 + 2 = s.val
      omega
    have hk' : left r (c + 1) b = vertex r (c + 1) k := rfl
    simpa only [hs, hk', vertex] using hbridge r c a b
  · rcases hbackward with ⟨rfl, hklo, hkhi, hs, rfl⟩
    let a : Fin 2 := ⟨k.val - 2, by omega⟩
    let b : Fin 2 := ⟨s.val, hs⟩
    have hk : right r d a = vertex r d k := by
      apply congrArg (vertex r d)
      apply Fin.ext
      change k.val - 2 + 2 = k.val
      omega
    have hs' : left r (d + 1) b = vertex r (d + 1) s := rfl
    rw [edgeConstraint_comm]
    simpa only [hk, hs', vertex] using hbridge r d a b

/-- An operator bound for every placement, including nongeneric ones. -/
theorem rigidityRank_le_518 (p : Placement Vertex 3) :
    rigidityRank graph p ≤ 518 := by
  have hk := Submodule.finrank_mono (coverage_kernel_le_rigidity_kernel p)
  have hgraph := (rigidityOperator graph p).finrank_range_add_finrank_ker
  have hcover := (coverageOperator p).finrank_range_add_finrank_ker
  have htarget := Submodule.finrank_le (coverageOperator p).range
  have htargetBound := coverageTarget_finrank_le p
  unfold rigidityRank
  omega

theorem genericRigidityRank_le_518 : genericRigidityRank graph 3 ≤ 518 := by
  obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank graph 3
  rw [← hp]
  exact rigidityRank_le_518 p

theorem complete_genericRank_eq_519 :
    genericRigidityRank (SimpleGraph.completeGraph Vertex) 3 = 519 := by
  rw [genericCompleteRank_eq (V := Vertex) (by rw [card_vertex]; decide), card_vertex]

/-- The finite witness is genuinely generically flexible in three dimensions. -/
theorem not_genericallyRigid : ¬ IsGenericallyRigidInR3 graph := by
  intro hrigid
  have hbound := genericRigidityRank_le_518
  change genericRigidityRank graph 3 =
    genericRigidityRank (SimpleGraph.completeGraph Vertex) 3 at hrigid
  rw [hrigid, complete_genericRank_eq_519] at hbound
  omega

end Papers.Rigidity.Sharpness

end
end
end BundleSource0068

section BundleSource0069
/- Source: Papers/RigiditySharpness.lean -/




@[expose] public section

/-!
# Sharpness of the six-connectivity threshold

The example is finite because the sharpness assertion is existential.
Its flexibility proof remains a rank bound valid for every real placement.
The unrestricted six-connectivity theorem is a separate declaration in
`RigidityFinalTheorems`.
-/

namespace Papers.Rigidity

/-- The hypothesis `six-connected` in Theorem 1.1 cannot be replaced
by `five-connected`. This is the 175-vertex instance of
Jackson--Jordán--Villányi, Example 7.5. -/
theorem fiveConnected_k4Covered_flexible_exists :
    ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
      @VertexConnected V hV G 5 ∧ K4Covered G ∧
        ¬ @BarJoint.IsGenericallyRigidInR3 V hV G := by
  exact ⟨Sharpness.Vertex, inferInstance, Sharpness.graph,
    Sharpness.sharpness_fiveConnected, Sharpness.k4Covered,
    Sharpness.not_genericallyRigid⟩

end Papers.Rigidity

end
end BundleSource0069

section BundleSource0070
/- Source: Papers/RigiditySupportedSharpness.lean -/






@[expose] public section

/-!
# Sharpness of the supported-code inequality

Equality holds for every code meeting the Singleton bound with no
inactive coordinates.  Over an infinite field such codes are constructed
as evaluations of polynomials of degree less than `r` at `r+s-1`
distinct points.  Their dimension and minimum support are proved from
the ordinary polynomial root bound.  No representability or MDS-code
existence theorem is assumed.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

theorem bound_recursion (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    ((r : ℝ) + ((r + s - 1 : ℕ) : ℝ) * bound s (r - 1)) /
      (r + s) = bound s r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hsub : k + 1 + s - 1 = k + s := by omega
  rw [hsub]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (k : ℝ) + s ≠ 0 := by positivity
  have hden' : (k : ℝ) + 1 + s ≠ 0 := by positivity
  unfold bound
  push_cast
  field_simp
  <;> ring

/-- Every nonzero code attaining the Singleton length has every
coordinate active. -/
theorem activeCoordinates_eq_univ_of_singletonEquality
    {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s)
    (hW : W ≠ ⊥) (heq : Module.finrank K W + s = n + 1) :
    activeCoordinates W = Finset.univ := by
  apply Finset.eq_univ_of_card
  have hlow := singleton_bound W s hs hmin hW
  have hu := Finset.card_le_univ (activeCoordinates W)
  simp only [Fintype.card_fin] at hu ⊢
  omega

theorem orderMean_eq_bound_of_singletonEquality
    {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s)
    (heq : Module.finrank K W + s = n + 1) :
    orderMean W = bound s (Module.finrank K W) := by
  induction n with
  | zero =>
    have hzero : Module.finrank K W = 0 := by
      have h := W.finrank_le
      simpa using h
    rw [orderMean_eq_zero_of_finrank_eq_zero W hzero, hzero, bound_zero]
  | succ n ih =>
    by_cases hz : Module.finrank K W = 0
    · rw [orderMean_eq_zero_of_finrank_eq_zero W hz, hz, bound_zero]
    have hW : W ≠ ⊥ := by intro h; simp [h] at hz
    have hactive := activeCoordinates_eq_univ_of_singletonEquality W hs hmin hW heq
    have hshort (i : Fin (n + 1)) :
        Module.finrank K (shorten W i) + 1 = Module.finrank K W :=
      finrank_shorten_of_active W i (by simp [hactive])
    have hmean (i : Fin (n + 1)) :
        orderMean (shorten W i) = bound s (Module.finrank K W - 1) := by
      have hs' := hshort i
      have hd : Module.finrank K (shorten W i) = Module.finrank K W - 1 := by omega
      rw [ih (shorten W i) (minimumSupport_shorten W i hmin) (by omega), hd]
    rw [orderMean_recursion]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : n + 1 = Module.finrank K W + s - 1 := by omega
    have hn' : n + 2 = Module.finrank K W + s := by omega
    rw [show (n + 2 : ℝ) = ((Module.finrank K W + s : ℕ) : ℝ) by exact_mod_cast hn',
      show ((n + 1 : ℕ) : ℝ) = ((Module.finrank K W + s - 1 : ℕ) : ℝ) by
        exact_mod_cast hn]
    simpa only [Nat.cast_add] using bound_recursion s (Module.finrank K W) hs (by omega)

variable {K : Type*} [Field K]

def polynomialEvaluationCodeMap {n : ℕ} (r : ℕ) (a : Fin n ↪ K) :
    Polynomial.degreeLT K r →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => (Polynomial.leval (a i)).comp (Polynomial.degreeLT K r).subtype

@[simp] theorem polynomialEvaluationCodeMap_apply {n r : ℕ} (a : Fin n ↪ K)
    (p : Polynomial.degreeLT K r) (i : Fin n) :
    polynomialEvaluationCodeMap r a p i = p.val.eval (a i) := rfl

def polynomialEvaluationCode {n : ℕ} (r : ℕ) (a : Fin n ↪ K) :
    Submodule K (Fin n → K) := (polynomialEvaluationCodeMap r a).range

theorem polynomialEvaluationCodeMap_injective {n r : ℕ} (a : Fin n ↪ K) (hrn : r ≤ n) :
    Function.Injective (polynomialEvaluationCodeMap r a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro p hp
    apply Subtype.ext
    by_contra hne
    have hdeg : p.val.natDegree < r :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr (Polynomial.mem_degreeLT.mp p.property)
    have heval (i : Fin n) : p.val.eval (a i) = 0 :=
      congrFun (LinearMap.mem_ker.mp hp) i
    exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p.val
      a.injective heval (by simpa using hdeg.trans_le hrn))
  · exact bot_le

theorem polynomialEvaluationCode_finrank {n r : ℕ} (a : Fin n ↪ K) (hrn : r ≤ n) :
    Module.finrank K (polynomialEvaluationCode r a) = r := by
  rw [polynomialEvaluationCode,
    LinearMap.finrank_range_of_inj (polynomialEvaluationCodeMap_injective a hrn),
    (Polynomial.degreeLTEquiv K r).finrank_eq]
  simp

/-- A nonzero polynomial of degree below `r` has at most `r-1`
zero evaluation coordinates at distinct points. -/
theorem polynomialEvaluationCode_minimumSupport {n r s : ℕ}
    (a : Fin n ↪ K) (hlen : r + s ≤ n + 1) :
    MinimumSupport (polynomialEvaluationCode r a) s := by
  intro w hw hwne
  obtain ⟨p, rfl⟩ := hw
  have hpne : p.val ≠ 0 := by
    intro hp
    apply hwne
    ext i
    simp [hp]
  have hdeg : p.val.natDegree < r :=
    (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr (Polynomial.mem_degreeLT.mp p.property)
  let Z : Finset (Fin n) := Finset.univ \ support (polynomialEvaluationCodeMap r a p)
  have hroots : (Z.map a).val ⊆ p.val.roots := by
    intro x hx
    change x ∈ Z.map a at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    apply (Polynomial.mem_roots hpne).mpr
    have hi' : i ∉ support (polynomialEvaluationCodeMap r a p) :=
      (Finset.mem_sdiff.mp hi).2
    simpa using hi'
  have hz := Polynomial.card_le_degree_of_subset_roots hroots
  change (Z.map a).card ≤ p.val.natDegree at hz
  rw [Finset.card_map] at hz
  have hcard : Z.card = n - (support (polynomialEvaluationCodeMap r a p)).card := by
    simp [Z, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hle := Finset.card_le_univ (support (polynomialEvaluationCodeMap r a p))
  simp only [Fintype.card_fin] at hle
  rw [hcard] at hz
  omega

/-- The sharpness clause of Lemma 2.1, under the actual uniform finite
order law, for every rank and every positive support threshold. -/
theorem exists_code_attaining_bound [Infinite K] (r s : ℕ) (hs : 1 ≤ s) :
    ∃ W : Submodule K (Fin (r + s - 1) → K),
      Module.finrank K W = r ∧ MinimumSupport W s ∧ precedingMean W = bound s r := by
  let a : Fin (r + s - 1) ↪ K :=
    ⟨fun i => Infinite.natEmbedding K i.val,
      fun i j hij => Fin.ext ((Infinite.natEmbedding K).injective hij)⟩
  let W := polynomialEvaluationCode r a
  have hd : Module.finrank K W = r := polynomialEvaluationCode_finrank a (by omega)
  have hmin : MinimumSupport W s := polynomialEvaluationCode_minimumSupport a (by omega)
  refine ⟨W, hd, hmin, ?_⟩
  rw [← orderMean_eq_precedingMean,
    orderMean_eq_bound_of_singletonEquality W hs hmin (by omega), hd]

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0070

section BundleSource0071
/- Source: Papers/RigidityDuplicateLoadSupport.lean -/





@[expose] public section

/-!
# Duplicate loads respect every induced vertex set

This is equation (4) of Proposition 6.2. Prefix load spaces use different
balanced-fragment subtypes, so we first put their actual coordinate values
in the common ambient space of body-indexed vertex loads. The resulting
intersection is the literal assertion `D(V) ∩ C(T) = D(T)`.

The proof uses the copied-star independence lemma at each omitted vertex.
No conclusion of the main rigidity theorem is imported or used.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Forget only the balanced-fragment subtype; every actual vertex
coordinate, including its zero extension, is retained. -/
def ambientBodyLoadValues (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyBalancedFamily G p T →ₗ[ℝ] (Body G → Velocity V 3) :=
  LinearMap.pi fun C => (balancedLoadsOn p (C.val ∩ T)).subtype.comp (LinearMap.proj C)

@[simp] theorem ambientBodyLoadValues_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) (C : Body G) :
    ambientBodyLoadValues G p T F C = (F C).val := rfl

theorem ambientBodyLoadValues_injective
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Function.Injective (ambientBodyLoadValues G p T) := by
  intro F H h
  funext C
  exact Subtype.ext (congrFun h C)

def compatibleLoadsInAmbient (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (Body G → Velocity V 3) :=
  (compatibleBodyLoads G p T).map (ambientBodyLoadValues G p T)

def duplicateLoadsInAmbient (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (Body G → Velocity V 3) :=
  (duplicateBodyLoads G p T).map (ambientBodyLoadValues G p T)

def ambientCopiedLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (BodyEdgeOccurrence G T → ℝ) →ₗ[ℝ] (Body G → Velocity V 3) :=
  (ambientBodyLoadValues G p T).comp (bodyCopyForces G p T)

@[simp] theorem ambientCopiedLoads_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) (C : Body G) :
    ambientCopiedLoads G p T a C = (bodyCopyForces G p T a C).val := rfl

theorem mem_duplicateLoadsInAmbient_iff
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : Body G → Velocity V 3) :
    F ∈ duplicateLoadsInAmbient G p T ↔
      ∃ a : BodyEdgeOccurrence G T → ℝ,
        copyAggregate G T a = 0 ∧ ambientCopiedLoads G p T a = F := by
  constructor
  · rintro ⟨H, ⟨a, ha, rfl⟩, hF⟩
    exact ⟨a, LinearMap.mem_ker.mp ha, hF⟩
  · rintro ⟨a, ha, hF⟩
    exact ⟨bodyCopyForces G p T a,
      ⟨a, LinearMap.mem_ker.mpr ha, rfl⟩, hF⟩

private theorem forceOperator_single_eq
    (H : SimpleGraph V) (p : Placement V 3) (e : Edge H) :
    forceOperator H p (Pi.single e 1) = loadWorkEquiv.symm (unorderedFunctional p e.val) := by
  apply loadWorkEquiv.injective
  rw [loadWork_forceOperator, LinearEquiv.apply_symm_apply]
  exact LinearMap.ext fun u => stressOperator_single H p u e

/-- A unit copied coefficient induces the ordinary load of its actual
edge in its actual body, independently of the displayed prefix. -/
theorem ambientCopiedLoads_single
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (i : BodyEdgeOccurrence G T) :
    ambientCopiedLoads G p T (Pi.single i 1) =
      Pi.single i.1 (loadWorkEquiv.symm (unorderedFunctional p i.2.val)) := by
  rcases i with ⟨C, e⟩
  funext D
  by_cases hDC : D = C
  · subst D
    have hr : bodyCopyRestriction G T C (Pi.single (⟨C, e⟩ : BodyEdgeOccurrence G T) 1) =
        Pi.single e 1 := by
      funext f
      by_cases hfe : f = e <;>
        simp [bodyCopyRestriction_apply, Pi.single_apply, hfe]
    rw [ambientCopiedLoads_apply, bodyCopyForces_apply, hr, forceOperator_single_eq]
    simp
  · have hr : bodyCopyRestriction G T D (Pi.single (⟨C, e⟩ : BodyEdgeOccurrence G T) 1) = 0 := by
      funext f
      have hne : (⟨D, f⟩ : BodyEdgeOccurrence G T) ≠ ⟨C, e⟩ :=
        fun h => hDC (congrArg Sigma.fst h)
      simp [bodyCopyRestriction_apply, Pi.single_eq_of_ne hne]
    rw [ambientCopiedLoads_apply, bodyCopyForces_apply, hr, map_zero]
    simp only [Pi.single_eq_of_ne hDC]

/-- The same body-edge occurrence, viewed on another prefix containing
both actual endpoints. -/
def retargetBodyOccurrence (G : SimpleGraph V) {S : Finset V} (T : Finset V)
    (i : BodyEdgeOccurrence G S) (hi : ∀ v, v ∈ i.2.val → v ∈ T) :
    BodyEdgeOccurrence G T :=
  ⟨i.1, ⟨i.2.val, by
    have he : (cliqueOn (i.1.val ∩ S)).Adj i.2.val.out.1 i.2.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, i.2.val.out_eq]
      exact i.2.property
    rw [← i.2.val.out_eq]
    exact ⟨he.1,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he.2.1).1, hi _ (Sym2.out_fst_mem _)⟩,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he.2.2).1, hi _ (Sym2.out_snd_mem _)⟩⟩⟩⟩

private theorem retarget_duplicate_mode
    (G : SimpleGraph V) (p : Placement V 3) {S : Finset V} (T : Finset V)
    (i k : BodyEdgeOccurrence G S)
    (hi : ∀ v, v ∈ i.2.val → v ∈ T) (hk : ∀ v, v ∈ k.2.val → v ∈ T)
    (hik : underlyingCopiedEdge G S i = underlyingCopiedEdge G S k) :
    ambientCopiedLoads G p S (Pi.single i 1 - Pi.single k 1) ∈
      duplicateLoadsInAmbient G p T := by
  let j := retargetBodyOccurrence G T i hi
  let l := retargetBodyOccurrence G T k hk
  have he : i.2.val = k.2.val :=
    congrArg (fun e : Edge (maskedGraph G S) => e.val) hik
  have hjl : underlyingCopiedEdge G T j = underlyingCopiedEdge G T l := by
    apply Subtype.ext
    change i.2.val = k.2.val
    exact he
  have hsingle (m : BodyEdgeOccurrence G T) :
      fiberSum (underlyingCopiedEdge G T) (Pi.single m (1 : ℝ)) =
        Pi.single (underlyingCopiedEdge G T m) 1 := by
    rw [fiberSum_apply, Finset.sum_eq_single m]
    · simp [← Pi.single_smul]
      funext e
      by_cases he : e = underlyingCopiedEdge G T m <;> simp [Pi.single_apply, he]
    · intro q _ hqm
      simp [Pi.single_eq_of_ne hqm]
    · simp
  apply (mem_duplicateLoadsInAmbient_iff G p T _).mpr
  refine ⟨Pi.single j 1 - Pi.single l 1, ?_, ?_⟩
  · rw [map_sub]
    change fiberSum (underlyingCopiedEdge G T) (Pi.single j 1) -
      fiberSum (underlyingCopiedEdge G T) (Pi.single l 1) = 0
    rw [hsingle j, hsingle l, hjl, sub_self]
  · rw [map_sub, map_sub, ambientCopiedLoads_single, ambientCopiedLoads_single,
      ambientCopiedLoads_single, ambientCopiedLoads_single]
    rfl

/-- Decompose a cancelling coefficient family into opposite-copy modes.
Only modes starting at a nonzero coefficient need to be considered. -/
private theorem cancelled_copy_image_mem
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) (ha : copyAggregate G T a = 0)
    (P : Submodule ℝ (Body G → Velocity V 3))
    (hmodes : ∀ i k, a i ≠ 0 →
      underlyingCopiedEdge G T i = underlyingCopiedEdge G T k →
        ambientCopiedLoads G p T (Pi.single i 1 - Pi.single k 1) ∈ P) :
    ambientCopiedLoads G p T a ∈ P := by
  let f := underlyingCopiedEdge G T
  let r : Edge (maskedGraph G T) → BodyEdgeOccurrence G T :=
    fun e => Classical.choose (underlyingCopiedEdge_surjective G hG T e)
  have hr (e) : f (r e) = e :=
    Classical.choose_spec (underlyingCopiedEdge_surjective G hG T e)
  have hunit : (∑ i, a i • Pi.single i 1) = a := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      Finset.univ_sum_single a
  have heq : (∑ i, a i • (Pi.single i 1 - Pi.single (r (f i)) 1)) = a := by
    calc
      _ = a - fiberSum (r ∘ f) a := by
        simp only [smul_sub, Finset.sum_sub_distrib, hunit,
          fiberSum_apply, Function.comp_apply]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        apply congrArg (fun b : BodyEdgeOccurrence G T → ℝ => a x • b)
        funext e
        by_cases he : e = r (f x) <;> simp [Pi.single_apply, he]
      _ = a := by
        rw [← fiberSum_comp f r a, show fiberSum f a = 0 from ha, map_zero, sub_zero]
  rw [← heq, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hai : a i = 0
  · simp [hai]
  · rw [map_smul]
    exact P.smul_mem (a i) (hmodes i (r (f i)) hai (hr (f i)).symm)

theorem duplicateLoadsInAmbient_le_whole
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V) :
    duplicateLoadsInAmbient G p T ≤ duplicateLoadsInAmbient G p Finset.univ := by
  intro F hF
  obtain ⟨a, ha, rfl⟩ := (mem_duplicateLoadsInAmbient_iff G p T F).mp hF
  apply cancelled_copy_image_mem G hG p T a ha
  intro i k _ hik
  exact retarget_duplicate_mode G p Finset.univ i k
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) hik

/-- If duplicate loads vanish outside a prefix, every copied coefficient
in every representing duplicate family also vanishes there. This is the
specific application of Lemma 6.1 in the paper's proof of equation (4). -/
theorem duplicate_coefficients_supported_of_loads_supported
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : BodyEdgeOccurrence M.graph Finset.univ → ℝ)
    (ha : copyAggregate M.graph Finset.univ a = 0)
    (hF : ∀ C v, v ∉ T → (bodyCopyForces M.graph p Finset.univ a C).val v = 0) :
    CopiedSupportedOn M.graph T a := by
  intro e he
  obtain ⟨v, hve, hvT⟩ := he
  let b : Body M.graph → V → ℝ := fun C =>
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ C a)
  have hnonzero (C : Body M.graph) (w : V) (h : b C w ≠ 0) :
      v ∈ C.val ∧ w ∈ C.val ∧ w ≠ v := by
    have hadj : (cliqueOn (C.val ∩ Finset.univ)).Adj v w := by
      by_contra hn
      exact h (starCoordinates_of_not_adj _ _ _ _ hn)
    exact ⟨(Finset.mem_inter.mp hadj.2.1).1,
      (Finset.mem_inter.mp hadj.2.2).1, hadj.1.symm⟩
  have hout (C : Body M.graph) (hC : v ∉ C.val) (w : V) : b C w = 0 := by
    by_contra hn
    exact hC (hnonzero C w hn).1
  have hsum (w : V) : (∑ C : Body M.graph, b C w) = 0 := by
    have h := congrArg
      (fun z => starCoordinates (maskedGraph M.graph Finset.univ) v z w) ha
    rw [copyAggregate_eq_sum_extensions, map_sum] at h
    simpa only [Finset.sum_apply, starCoordinates_extendEdgeCoefficients,
      map_zero, Pi.zero_apply, b] using h
  let I := {C : Body M.graph // v ∈ C.val}
  have hcancel (w : V) : (∑ i : I, b i.val w) = 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun C : Body M.graph => v ∈ C.val) (fun C => b C w)
    have hz : (∑ C : {C : Body M.graph // v ∉ C.val}, b C.val w) = 0 :=
      Finset.sum_eq_zero (fun C _ => hout C.val C.property w)
    rw [hz, add_zero, hsum] at hsplit
    exact hsplit
  have hbalance (i : I) : (∑ w, b i.val w • (p v - p w)) = 0 := by
    change (∑ w, starCoordinates (cliqueOn (i.val.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ i.val a) w • (p v - p w)) = 0
    rw [sum_starCoordinates_eq_incident, ← forceOperator_vertex]
    exact hF i.val v hvT
  have hz := copied_star_coefficients_eq_zero M p hp v (fun i : I => i.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => i.val.property) (fun i => i.property) (fun i : I => b i.val)
    (fun i w h => Finset.mem_erase.mpr
      ⟨(hnonzero i.val w h).2.2, (hnonzero i.val w h).2.1⟩)
    hcancel hbalance
  have hvC : v ∈ e.1.val := by
    obtain ⟨w, hew⟩ := Sym2.mem_iff_exists.mp hve
    have hadj := e.2.property
    rw [hew] at hadj
    exact (Finset.mem_inter.mp hadj.2.1).1
  have h := hz ⟨e.1, hvC⟩
    (incidentOther (cliqueOn (e.1.val ∩ Finset.univ)) v ⟨e.2, hve⟩)
  simpa only [b, starCoordinates_incidentOther, bodyCopyRestriction_apply] using h

theorem supported_duplicate_loads_mem_prefix
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ)
    (ha : copyAggregate G Finset.univ a = 0) (hs : CopiedSupportedOn G T a) :
    ambientCopiedLoads G p Finset.univ a ∈ duplicateLoadsInAmbient G p T := by
  apply cancelled_copy_image_mem G hG p Finset.univ a ha
  intro i k hai hik
  have hi (v : V) (hvi : v ∈ i.2.val) : v ∈ T := by
    by_contra hvT
    exact hai (hs i ⟨v, hvi, hvT⟩)
  have he : i.2.val = k.2.val := congrArg Subtype.val hik
  have hk (v : V) (hvk : v ∈ k.2.val) : v ∈ T := hi v (he.symm ▸ hvk)
  exact retarget_duplicate_mode G p T i k hi hk hik

/-- Proposition 6.2(4), with the original compatible and duplicate
spaces embedded by their actual coordinate values into a common ambient
space. All induced vertex sets, including the empty set, are included. -/
theorem duplicate_loads_prefix_identity
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    duplicateLoadsInAmbient M.graph p Finset.univ ⊓
      compatibleLoadsInAmbient M.graph p T = duplicateLoadsInAmbient M.graph p T := by
  apply le_antisymm
  · intro F hF
    obtain ⟨a, ha, rfl⟩ :=
      (mem_duplicateLoadsInAmbient_iff M.graph p Finset.univ F).mp hF.1
    obtain ⟨H, _, hH⟩ := hF.2
    have hzero (C : Body M.graph) (v : V) (hv : v ∉ T) :
        (bodyCopyForces M.graph p Finset.univ a C).val v = 0 := by
      have hval := congrFun (congrFun hH C) v
      exact hval.symm.trans ((H C).property.2 v
        (fun h => hv (Finset.mem_inter.mp h).2))
    exact supported_duplicate_loads_mem_prefix M.graph M.covered p T a ha
      (duplicate_coefficients_supported_of_loads_supported M p hp T a ha hzero)
  · intro F hF
    exact ⟨duplicateLoadsInAmbient_le_whole M.graph M.covered p T hF,
      Submodule.map_mono (duplicateBodyLoads_le_compatible M.graph p T) hF⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0071

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0071/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0071.json"

section BundleSource0072
/- Source: Papers/RigidityCenterDescent.lean -/



@[expose] public section

/-!
# Descent of the virtual center to the prior coefficient field

A unique common center of coefficient-defined alternating forms is itself
defined over that field.  The proof descends a nonzero solution of the
literal common-kernel equations, then uses their three-dimensional center
space to identify the whole twist space.  Projective scalar uniqueness
also descends, by dividing one nonzero coordinate.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

def coefficientTwistMatrix {K : Type*} [Field K] (X : CoefficientTwist K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, -X.1 2, X.1 1, X.2 0;
     X.1 2, 0, -X.1 0, X.2 1;
     -X.1 1, X.1 0, 0, X.2 2;
     -X.2 0, -X.2 1, -X.2 2, 0]

theorem coefficientTwistMatrix_map {K : Type*} [Field K] [Algebra K ℝ]
    (X : CoefficientTwist K) :
    (coefficientTwistMatrix X).map (algebraMap K ℝ) = twistMatrix (realTwist X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientTwistMatrix, twistMatrix, realTwist]

def pointFromHomogeneousVector (v : Fin 4 → ℝ) : HomogeneousPoint :=
  (![v 0, v 1, v 2], v 3)

@[simp] theorem homogeneousVector_pointFromHomogeneousVector (v : Fin 4 → ℝ) :
    homogeneousVector (pointFromHomogeneousVector v) = v := by
  ext i
  fin_cases i <;> rfl

theorem finrank_homogeneousCenterSpace (q : HomogeneousPoint) (hq : q ≠ 0) :
    Module.finrank ℝ (homogeneousCenterSpace q) = 3 := by
  by_cases hs : q.2 = 0
  · have hd : q.1 ≠ 0 := fun h => hq (Prod.ext h hs)
    have he : q = (q.1, 0) := Prod.ext rfl hs
    rw [he, homogeneousCenterSpace_infinite, finrank_infiniteCenterSpace _ hd]
  · rw [homogeneousCenterSpace_normalize q hs, finrank_finiteCenterSpace]

/-- A scalar relating two nonzero coefficient vectors belongs to the
coefficient field: one nonzero coordinate determines it as a quotient. -/
theorem projective_scalar_descent
    {K L J : Type*} [Field K] [Field L] [Algebra K L]
    (u v : J → K) (hu : u ≠ 0) (c : L) (hc : c ≠ 0)
    (hscale : c • (fun j => algebraMap K L (u j)) =
      (fun j => algebraMap K L (v j))) :
    ∃ a : K, a ≠ 0 ∧ a • u = v := by
  have hnot : ¬ ∀ j, u j = 0 := fun h => hu (funext h)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have hjmap : algebraMap K L (u j) ≠ 0 := by
    simpa only [map_zero] using (RingHom.injective (algebraMap K L)).ne hj
  let a : K := v j / u j
  have hamap : algebraMap K L a = c := by
    dsimp [a]
    rw [map_div₀]
    apply (div_eq_iff hjmap).mpr
    exact (congrFun hscale j).symm
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hamap
    exact hc hamap.symm
  refine ⟨a, ha, ?_⟩
  ext i
  apply RingHom.injective (algebraMap K L)
  change algebraMap K L (a * u i) = algebraMap K L (v i)
  rw [map_mul, hamap]
  exact congrFun hscale i

theorem mapped_homogeneousVector_ne_zero
    {K : Type*} [Field K] [Algebra K ℝ]
    (q : Fin 4 → K) (hq : q ≠ 0) :
    pointFromHomogeneousVector (fun i => algebraMap K ℝ (q i)) ≠ 0 := by
  intro hz
  have hv := congrArg homogeneousVector hz
  rw [homogeneousVector_pointFromHomogeneousVector,
    show homogeneousVector (0 : HomogeneousPoint) = 0 from homogeneousVectorLinear.map_zero] at hv
  apply hq
  ext i
  apply RingHom.injective (algebraMap K ℝ)
  change algebraMap K ℝ (q i) = algebraMap K ℝ 0
  rw [map_zero]
  exact congrFun hv i

/-- Lemma 3.4 with its field of definition retained explicitly.  Both
the common homogeneous center and the scalar witnessing its projective
uniqueness belong to the field chosen before the generic new pin.

The literal matrix/kernel conclusion includes finite centers and centers
at infinity, without a chart assumption.
-/
theorem generic_alternating_space_center_defined_over_coefficients
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hdim : 3 ≤ Module.finrank K (Submodule.span K (Set.range X)))
    (hrank : Module.finrank ℝ
      (matrixPinContraction (coefficientTwistSpan X) p).range ≤ 2) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧
      (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
        twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (q j)) = 0) ∧
      ∀ r : Fin 4 → K, r ≠ 0 →
        (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
          twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (r j)) = 0) →
        ∃ c : K, c ≠ 0 ∧ c • q = r := by
  classical
  obtain ⟨q₀, hq₀, hW₀, hu₀⟩ :=
    generic_alternating_coefficient_space_unique_projective_center X p hp hdim hrank
  let a : (I × Fin 4) → Fin 4 → K := fun ij => coefficientTwistMatrix (X ij.1) ij.2
  have hqvec : homogeneousVector q₀ ≠ 0 := by
    intro hz
    apply hq₀
    apply homogeneousVectorLinear_injective
    rw [map_zero]
    exact hz
  have hrows (ij : I × Fin 4) :
      (fun j => algebraMap K ℝ (a ij j)) ⬝ᵥ homogeneousVector q₀ = 0 := by
    have hm := (hW₀ (realTwist (X ij.1))).mp (Submodule.subset_span ⟨ij.1, rfl⟩)
    rw [← coefficientTwistMatrix_map] at hm
    exact congrFun hm ij.2
  obtain ⟨q, hq, hqa⟩ :=
    exists_nonzero_kernel_over_coefficient_field a (homogeneousVector q₀) hqvec hrows
  let qr := pointFromHomogeneousVector (fun i => algebraMap K ℝ (q i))
  have hqr : qr ≠ 0 := mapped_homogeneousVector_ne_zero q hq
  have hqi (i : I) :
      twistMatrix (realTwist (X i)) *ᵥ homogeneousVector qr = 0 := by
    rw [← coefficientTwistMatrix_map, homogeneousVector_pointFromHomogeneousVector]
    ext j
    have hz := congrArg (algebraMap K ℝ) (hqa (i, j))
    simpa only [map_zero, Pi.zero_apply, dotProduct, map_sum, map_mul, Matrix.mulVec,
      Matrix.map_apply, a] using hz
  have hle : coefficientTwistSpan X ≤ homogeneousCenterSpace qr := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (mem_homogeneousCenterSpace_iff_matrix_kernel qr _).mpr (hqi i)
  have hWq : coefficientTwistSpan X = homogeneousCenterSpace qr := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_homogeneousCenterSpace qr hqr, finrank_coefficientTwistSpan]
    exact hdim
  have hqform (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (q j)) = 0 := by
    rw [hWq, mem_homogeneousCenterSpace_iff_matrix_kernel,
      homogeneousVector_pointFromHomogeneousVector]
  refine ⟨q, hq, hqform, ?_⟩
  intro r hr hWr
  let rr := pointFromHomogeneousVector (fun i => algebraMap K ℝ (r i))
  have hrr : rr ≠ 0 := mapped_homogeneousVector_ne_zero r hr
  have hqworld (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ homogeneousVector qr = 0 := by
    simpa only [homogeneousVector_pointFromHomogeneousVector, qr] using hqform Y
  have hrworld (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ homogeneousVector rr = 0 := by
    simpa only [homogeneousVector_pointFromHomogeneousVector, rr] using hWr Y
  obtain ⟨c, hc, hcq⟩ := hu₀ qr hqr hqworld
  obtain ⟨d, hd, hdr⟩ := hu₀ rr hrr hrworld
  have hscale : (d / c) • qr = rr := by
    rw [← hcq, smul_smul, div_mul_cancel₀ d hc, hdr]
  have hcoordinates := congrArg homogeneousVectorLinear hscale
  rw [map_smul] at hcoordinates
  change (d / c) • homogeneousVector qr = homogeneousVector rr at hcoordinates
  have hscaleCoordinates : (d / c) • (fun j => algebraMap K ℝ (q j)) =
      (fun j => algebraMap K ℝ (r j)) := by
    simpa only [qr, rr, homogeneousVector_pointFromHomogeneousVector] using hcoordinates
  exact projective_scalar_descent q r hq (d / c) (div_ne_zero hd hc) hscaleCoordinates

end

end Papers.Rigidity

end
end BundleSource0072

section BundleSource0073
/- Source: Papers/RigidityTypeAStar.lean -/




@[expose] public section

/-!
# Lemma 3.7: the actual stress star at a type-A vertex

A type-A vertex belongs to exactly two maximal bodies, both tetrahedra,
whose intersection consists of that vertex. This definition uses the
actual graph bodies. The star space below is the image of the ordinary
stress space on the actual incident edges.

The deletion-rank identity bounds its dimension by one. A nonzero star
supported on four bars would place the centre and its four neighbours in
an ambient rigid cluster. Closure would then put the centre in a body of
order at least five, contradicting the two tetrahedral bodies.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint SupportedCode
open scoped Classical

variable {V : Type} [Fintype V]

/-- The type-A alternative of Lemma 3.3, expressed using actual maximal
bodies and their exact common vertex. `TwoBodyPin` includes exhaustivity. -/
def TwoBodyPin.IsTypeA {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) : Prop :=
  Q.left.val.card = 4 ∧ Q.right.val.card = 4 ∧ Q.IsPoint

theorem TwoBodyPin.IsTypeA.degree_eq_six
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (hA : Q.IsTypeA) : M.graph.degree v = 6 := by
  have hd := TwoBodyPin.degree_add_correction M v Q
  rw [if_pos hA.2.2, add_zero,
    clique_degree _ _ Q.left_mem, clique_degree _ _ Q.right_mem,
    hA.1, hA.2.1] at hd
  exact hd

/-- The bound holds even when the actual stress-star image is zero. -/
theorem TwoBodyPin.typeA_stressStar_finrank_le_one
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p) :
    Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) ≤ 1 := by
  rw [stressStar_finrank_eq_degree_sub_deletionRankDrop M.graph p hgen v,
    hA.degree_eq_six M]
  have hdrop := M.five_le_deletionRankDrop v
  omega

/-- Every nonzero vector in the actual star image has at least five
nonzero incident-edge coordinates. No chosen scalar system is involved. -/
theorem TwoBodyPin.typeA_stressStar_minimumSupport_five
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    MinimumSupport (stressStarCode M.graph v (StressSpace M.graph p)) 5 := by
  intro a ha hane
  have hfour := stressStarCode_minimumSupport_four M.graph p hp v
    (StressSpace M.graph p) le_rfl a ha hane
  obtain ⟨ω, hω, rfl⟩ := Submodule.mem_map.mp ha
  let S := support (starRestriction M.graph v ω)
  let N := S.image (incidentOther M.graph v)
  change 5 ≤ S.card
  change 4 ≤ S.card at hfour
  by_contra hsmall
  have hScard : S.card = 4 := by omega
  have hNcard : N.card = 4 := by
    rw [Finset.card_image_of_injective S (incidentOther_injective M.graph v), hScard]
  have hNadj (w : V) (hw : w ∈ N) : M.graph.Adj v w := by
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact incidentOther_adj M.graph v e
  have hout (w : V) (hw : w ∉ N) : starCoordinates M.graph v ω w = 0 := by
    by_cases hadj : M.graph.Adj v w
    · let e : IncidentEdge M.graph v :=
        ⟨⟨s(v,w), hadj⟩, Sym2.mem_mk_left v w⟩
      have hew : incidentOther M.graph v e = w :=
        Sym2.congr_right.mp (Sym2.other_spec e.property)
      have he : e ∉ S := fun he => hw (Finset.mem_image.mpr ⟨e, he, hew⟩)
      have hzero : starRestriction M.graph v ω e = 0 := by
        simpa only [S, mem_support, not_not] using he
      rw [← hew, starCoordinates_incidentOther]
      exact hzero
    · exact starCoordinates_of_not_adj M.graph v w ω hadj
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hcluster := rigidCluster_of_stress_star_four M.graph p hgen hp v N
    hNcard hNadj ⟨ω, hω⟩ hout
    ⟨incidentOther M.graph v e, Finset.mem_image.mpr ⟨e, he, rfl⟩, by
      rw [starCoordinates_incidentOther]
      exact (mem_support _ e).mp he⟩
  have hvN : v ∉ N := fun hv => (hNadj v hv).ne rfl
  have hsize : (insert v N).card = 5 := by
    rw [Finset.card_insert_of_notMem hvN, hNcard]
  have hclique := M.rigidCluster_isClique (insert v N) (by omega) hcluster
  obtain ⟨B, hNB, hB⟩ := exists_body_containing M.graph (insert v N) (by omega) hclique
  have hBfive : 5 ≤ B.card := by
    simpa only [hsize] using Finset.card_le_card hNB
  have hvB : v ∈ B := hNB (Finset.mem_insert_self v N)
  have hBfour : B.card = 4 := by
    rcases Q.exhaustive ⟨B, hB⟩ hvB with h | h
    · have hval : B = Q.left.val := congrArg Subtype.val h
      simpa only [hval] using hA.1
    · have hval : B = Q.right.val := congrArg Subtype.val h
      simpa only [hval] using hA.2.1
  omega

/-- Lemma 3.7 in one statement: the nonzero actual star image is a line,
and every nonzero word in that line has at least five nonzero coordinates. -/
theorem TwoBodyPin.lemma_three_seven
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hstar : stressStarCode M.graph v (StressSpace M.graph p) ≠ ⊥) :
    Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) = 1 ∧
      MinimumSupport (stressStarCode M.graph v (StressSpace M.graph p)) 5 := by
  have hle := Q.typeA_stressStar_finrank_le_one M hA p hgen
  have hpos : Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) ≠ 0 :=
    fun hzero => hstar (Submodule.finrank_eq_zero.mp hzero)
  exact ⟨by omega, Q.typeA_stressStar_minimumSupport_five M hA p hgen hp⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0073

section BundleSource0074
/- Source: Papers/RigidityPriorityOrders.lean -/




@[expose] public section

/-!
# Real priorities and their finite ordering

The supported subspace is defined directly by comparing each real priority
with the marker's priority.  Sorting is used only to identify this genuine
subspace with the existing finite-order construction.  The orbit identity
below is the finite part of the independent-priority expectation formula.
No distributional or independence hypothesis is built into these definitions.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

variable {K : Type*} [Field K]

/-- The coordinates whose priorities are strictly before the extra marker.
Ties are excluded from the support, as in the literal strict comparison. -/
def priorityCode {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    ¬ x i.castSucc < x (Fin.last n) → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

@[simp] theorem mem_priorityCode {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) (w : Fin n → K) :
    w ∈ priorityCode W x ↔ w ∈ W ∧ ∀ i : Fin n,
      ¬ x i.castSucc < x (Fin.last n) → w i = 0 := Iff.rfl

theorem priorityCode_le {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : priorityCode W x ≤ W := fun _ h => h.1

/-- The actual supported-subspace dimension, viewed as a real random variable. -/
def priorityDimension {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : ℝ := Module.finrank K (priorityCode W x)

theorem priorityDimension_nonneg {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : 0 ≤ priorityDimension W x := Nat.cast_nonneg _

theorem priorityDimension_le {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : priorityDimension W x ≤ (Module.finrank K W : ℝ) := by
  change (Module.finrank K (priorityCode W x) : ℝ) ≤ (Module.finrank K W : ℝ)
  exact_mod_cast Submodule.finrank_mono (priorityCode_le W x)

/-- A permutation lists the labels in increasing order of their priorities. -/
def priorityOrderMatches {m : ℕ} (x : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i j : Fin m, σ.symm i < σ.symm j ↔ x i < x j

theorem exists_priorityOrderMatches {m : ℕ} (x : Fin m → ℝ)
    (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin m), priorityOrderMatches x σ := by
  let e := @Fintype.orderIsoFinOfCardEq (Fin m) (LinearOrder.lift' x hx)
    inferInstance m (Fintype.card_fin m)
  refine ⟨e.toEquiv, ?_⟩
  intro i j
  exact @OrderIso.lt_iff_lt (Fin m) (Fin m)
    (LinearOrder.lift' x hx).toPreorder inferInstance
    (@OrderIso.symm (Fin m) (Fin m) inferInstance (LinearOrder.lift' x hx).toLE e) i j

theorem priorityOrderMatches_unique {m : ℕ} {x : Fin m → ℝ}
    {σ τ : Equiv.Perm (Fin m)}
    (hσ : priorityOrderMatches x σ) (hτ : priorityOrderMatches x τ) : σ = τ := by
  have hm : StrictMono (fun k => τ.symm (σ k)) := by
    intro a b hab
    apply (hτ (σ a) (σ b)).mpr
    apply (hσ (σ a) (σ b)).mp
    simpa only [Equiv.symm_apply_apply] using hab
  apply Equiv.ext
  intro k
  have hk : τ.symm (σ k) = k := congrFun hm.eq_id k
  calc
    σ k = τ (τ.symm (σ k)) := (τ.apply_symm_apply (σ k)).symm
    _ = τ k := congrArg τ hk

theorem priorityCode_eq_precedingCode {n : ℕ}
    (W : Submodule K (Fin n → K)) {x : Fin (n + 1) → ℝ}
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : priorityOrderMatches x σ) :
    priorityCode W x = precedingCode W σ := by
  have hiff (i : Fin n) :
      (¬ x i.castSucc < x (Fin.last n)) ↔
        σ.symm (Fin.last n) < σ.symm i.castSucc := by
    rw [← hσ i.castSucc (Fin.last n)]
    have hne : σ.symm i.castSucc ≠ σ.symm (Fin.last n) :=
      σ.symm.injective.ne (Fin.castSucc_ne_last i)
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    · exact fun h => not_lt_of_ge h.le
  ext w
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨hw, fun i hi => hz i ((hiff i).mpr hi)⟩
  · rintro ⟨hw, hz⟩
    exact ⟨hw, fun i hi => hz i ((hiff i).mp hi)⟩

theorem priorityDimension_eq_of_matches {n : ℕ}
    (W : Submodule K (Fin n → K)) {x : Fin (n + 1) → ℝ}
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : priorityOrderMatches x σ) :
    priorityDimension W x = (Module.finrank K (precedingCode W σ) : ℝ) :=
  congrArg (fun A : Submodule K (Fin n → K) => (Module.finrank K A : ℝ))
    (priorityCode_eq_precedingCode W hσ)

/-- On distinct priorities, the dimension is a finite sum of chamber values.
The measure-theoretic bridge uses this formula to prove integrability. -/
theorem priorityDimension_eq_chamber_sum {n : ℕ}
    (W : Submodule K (Fin n → K)) (x : Fin (n + 1) → ℝ)
    (hx : Function.Injective x) :
    priorityDimension W x = ∑ σ : Equiv.Perm (Fin (n + 1)),
      if priorityOrderMatches x σ then (Module.finrank K (precedingCode W σ) : ℝ)
      else 0 := by
  obtain ⟨σ, hσ⟩ := exists_priorityOrderMatches x hx
  rw [priorityDimension_eq_of_matches W hσ]
  symm
  calc
    _ = if priorityOrderMatches x σ then
        (Module.finrank K (precedingCode W σ) : ℝ) else 0 := by
      apply Finset.sum_eq_single σ
      · intro τ _ hτσ
        exact if_neg (fun hτ => hτσ (priorityOrderMatches_unique hτ hσ))
      · intro h
        exact (h (Finset.mem_univ σ)).elim
    _ = _ := if_pos hσ

theorem priorityOrderMatches_relabel {m : ℕ} {x : Fin m → ℝ}
    {σ : Equiv.Perm (Fin m)} (hσ : priorityOrderMatches x σ)
    (τ : Equiv.Perm (Fin m)) :
    priorityOrderMatches (x ∘ τ) (σ.trans τ.symm) := by
  intro i j
  simpa only [Function.comp_apply, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.symm_symm] using hσ (τ i) (τ j)

/-- Relabeling the priorities traverses every possible ordering once. -/
def priorityRelabelEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) where
  toFun τ := σ.trans τ.symm
  invFun ρ := ρ.symm.trans σ
  left_inv τ := by ext i; simp
  right_inv ρ := by ext i; simp

/-- The orbit sum of literal priority dimensions is exactly the finite-order
sum. This identity holds for every injective real priority vector. -/
theorem sum_priorityDimension_relabel {n : ℕ}
    (W : Submodule K (Fin n → K)) (x : Fin (n + 1) → ℝ)
    (hx : Function.Injective x) :
    (∑ τ : Equiv.Perm (Fin (n + 1)), priorityDimension W (x ∘ τ)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (precedingCode W σ) : ℝ) := by
  obtain ⟨σ, hσ⟩ := exists_priorityOrderMatches x hx
  calc
    _ = ∑ τ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (precedingCode W (σ.trans τ.symm)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro τ _
      exact priorityDimension_eq_of_matches W (priorityOrderMatches_relabel hσ τ)
    _ = _ := Equiv.sum_comp (priorityRelabelEquiv σ)
      (fun ρ => (Module.finrank K (precedingCode W ρ) : ℝ))

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0074

section BundleSource0075
/- Source: Papers/RigidityAlgebraicGeneric.lean -/





@[expose] public section

/-!
# Ordinary algebraically independent bar-joint coordinates

The rational polynomial matrix below is identified entry by entry with
the actual real rigidity operator.  Injective polynomial evaluation
therefore proves that algebraically independent coordinates attain all
graph ranks.  Together with the actual length-fiber theorem, this links
the conventional generic local-rigidity statement to the rank target.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open MvPolynomial
open scoped Classical BigOperators

variable {V : Type} [Fintype V] {d : ℕ}

def placementCoordinates (p : Placement V d) : V × Fin d → ℝ :=
  fun c => p c.1 c.2

def barCoordinateUnit {R : Type*} [CommRing R] (c : V × Fin d) : V → Fin d → R :=
  fun v i => if (v, i) = c then 1 else 0

/-- The literal bar row on a coordinate unit, over any coefficient ring. -/
def barMatrix {R : Type*} [CommRing R] (G : SimpleGraph V) (p : V → Fin d → R) :
    Matrix (V × V) (V × Fin d) R :=
  fun e c => if G.Adj e.1 e.2 then
    ∑ i : Fin d, (p e.1 i - p e.2 i) *
      (barCoordinateUnit c e.1 i - barCoordinateUnit c e.2 i)
    else 0

def velocityCoordinateBasis : Module.Basis (V × Fin d) ℝ (Velocity V d) :=
  Module.Basis.ofEquivFun (LinearEquiv.curry ℝ ℝ V (Fin d)).symm

theorem velocityCoordinateBasis_apply (c : V × Fin d) :
    velocityCoordinateBasis c = barCoordinateUnit (R := ℝ) c := by
  rw [velocityCoordinateBasis, Module.Basis.coe_ofEquivFun]
  funext v i
  simp [barCoordinateUnit, LinearEquiv.coe_curry, Pi.single_apply]

theorem barMatrix_eq_coordinateMatrix (G : SimpleGraph V) (p : Placement V d) :
    barMatrix G p = LinearMap.toMatrix velocityCoordinateBasis
      (Pi.basisFun ℝ (V × V)) (rigidityOperator G p) := by
  ext e c
  rw [LinearMap.toMatrix_apply, velocityCoordinateBasis_apply]
  simp only [Pi.basisFun_repr]
  by_cases he : G.Adj e.1 e.2
  · simp only [barMatrix, he, if_true,
      rigidityOperator_apply_of_adj G p _ e.1 e.2 he, edgeConstraint]
  · simp only [barMatrix, he, if_false,
      rigidityOperator_apply_of_not_adj G p _ e.1 e.2 he]

theorem barMatrix_rank_eq (G : SimpleGraph V) (p : Placement V d) :
    (barMatrix G p).rank = rigidityRank G p := by
  rw [barMatrix_eq_coordinateMatrix,
    Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun ℝ (V × V)) velocityCoordinateBasis,
    Matrix.toLin_toMatrix]
  rfl

theorem map_barMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : SimpleGraph V) (p : V → Fin d → R) :
    (barMatrix G p).map f = barMatrix G (fun v i => f (p v i)) := by
  ext e c
  have hunit (v : V) (i : Fin d) :
      f (barCoordinateUnit (R := R) c v i) = barCoordinateUnit (R := S) c v i := by
    by_cases h : (v, i) = c <;>
      simp only [barCoordinateUnit, h, if_true, if_false, map_zero, map_one]
  by_cases he : G.Adj e.1 e.2
  · simp only [Matrix.map_apply, barMatrix, he, if_true, map_sum, map_mul, map_sub, hunit]
  · simp only [Matrix.map_apply, barMatrix, he, if_false, map_zero]

def rationalBarMatrix (G : SimpleGraph V) :
    Matrix (V × V) (V × Fin d) (MvPolynomial (V × Fin d) ℚ) :=
  barMatrix G (fun v i => X (v, i))

theorem realMatrix_rationalBarMatrix (G : SimpleGraph V) (z : V × Fin d → ℝ) :
    PolynomialRank.realMatrix (rationalBarMatrix (d := d) G) z =
      barMatrix G (fun v i => z (v, i)) := by
  rw [PolynomialRank.realMatrix, rationalBarMatrix, map_barMatrix]
  congr 1
  funext v i
  simp

/-- Ordinary algebraically independent coordinates attain the actual
maximum rigidity rank for every graph on the same labelled vertex set. -/
theorem isGenericPlacement_of_algebraicIndependent
    (p : Placement V d) (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsGenericPlacement p := by
  intro G
  have hinj : Function.Injective
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (placementCoordinates p)) := by
    intro a b hab
    apply hp
    exact hab
  have hgeneric := PolynomialRank.realMatrix_rank_eq_generic_of_eval_injective
    (rationalBarMatrix (d := d) G) (placementCoordinates p) hinj
  rw [realMatrix_rationalBarMatrix, barMatrix_rank_eq] at hgeneric
  change rigidityRank G p =
    (PolynomialRank.genericMatrix (rationalBarMatrix (d := d) G)).rank at hgeneric
  obtain ⟨q, hq⟩ := exists_rigidityRank_eq_genericRigidityRank G d
  have hqle := PolynomialRank.realMatrix_rank_le_generic
    (rationalBarMatrix (d := d) G) (placementCoordinates q)
  rw [realMatrix_rationalBarMatrix, barMatrix_rank_eq] at hqle
  change rigidityRank G q ≤
    (PolynomialRank.genericMatrix (rationalBarMatrix (d := d) G)).rank at hqle
  change rigidityRank G p = genericRigidityRank G d
  exact le_antisymm (rigidityRank_le_genericRigidityRank G d p)
    (hq ▸ hgeneric.symm ▸ hqle)

/-- The rank definition is equivalent to actual local distance rigidity
at each placement with algebraically independent real coordinates. -/
theorem localRigidity_iff_rank_at_algebraicallyGeneric
    (G : SimpleGraph V) (p : Placement V d)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p ↔ IsGenericallyRigidInDimension G d :=
  isLocallyDistanceRigid_iff_isGenericallyRigid G p
    (isGenericPlacement_of_algebraicIndependent p hp)

end

end Papers.Rigidity.BarJoint

end
end BundleSource0075

section BundleSource0076
/- Source: Papers/RigidityFinalAlgebraic.lean -/





@[expose] public section

/-!
# The graph conclusions at algebraically independent real coordinates

The maximum-rank formulation is connected to the conventional meaning of
generic coordinates by a proved polynomial-matrix comparison.  These
wrappers expose the paper's three graph conclusions with that hypothesis
and with local equality of actual Euclidean distances as the conclusion.
-/

namespace Papers.Rigidity

open BarJoint

variable {V : Type} [Fintype V]

/-- Theorem 1.1 at every real placement whose coordinates are algebraically
independent over the rationals. -/
theorem sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  sixConnected_k4Covered_locallyDistanceRigid G hconn hcover p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The edge-cover form of Corollary 1.2 at ordinary algebraically
generic real coordinates. -/
theorem sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6)
    (hcover : RigidSubgraphCovered G) (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  sixConnected_rigidSubgraphCovered_locallyDistanceRigid G hconn hcover p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The ambient-cluster completion form of Corollary 1.2 at ordinary
algebraically generic real coordinates. -/
theorem rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent
    {I : Type} (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  rigidCluster_completion_sixConnected_locallyDistanceRigid G C hC hconn p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The literal generic matrix rank in Theorem 1.1. Connectivity supplies
the cardinality needed for the complete-graph rank formula. -/
theorem sixConnected_k4Covered_genericRank
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G) :
    genericRigidityRank G 3 = 3 * Fintype.card V - 6 := by
  have hrig := sixConnected_k4Covered_rigid G hconn hcover
  change genericRigidityRank G 3 =
    genericRigidityRank (SimpleGraph.completeGraph V) 3 at hrig
  have hcard : 3 ≤ Fintype.card V := by
    have := hconn.1
    omega
  exact hrig.trans (genericCompleteRank_eq hcard)

/-- At every algebraically generic real placement, the actual rigidity
operator has the full rank asserted by Theorem 1.1. -/
theorem sixConnected_k4Covered_rigidityRank_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    rigidityRank G p = 3 * Fintype.card V - 6 :=
  (isGenericPlacement_of_algebraicIndependent p hp G).trans
    (sixConnected_k4Covered_genericRank G hconn hcover)

end Papers.Rigidity

end
end BundleSource0076


/- Final endpoint audits; all local proof bodies must be available. -/
set_option maxHeartbeats 0
#print axioms Papers.Rigidity.pairPin_defect_theorem
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.pairPin_defect_theorem to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_pairPin_defect_theorem.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_theorem_at_algebraicallyGeneric_pins.json"
#print axioms Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_QuantitativeHeight_genericIncidencePrime_height_ge_active_add_sparse.json"
#print axioms Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_NullHeight_coefficientMinimalPrime_height_eq_edgeCard.json"
#print axioms Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_genericPinRank_eq_genericMotionMatrix_rank.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_at_maximal_rank_pins.json"
#print axioms Papers.Rigidity.minimalCounterexample_false
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.minimalCounterexample_false to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_minimalCounterexample_false.json"
#print axioms Papers.Rigidity.theorem_one_one
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.theorem_one_one to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_theorem_one_one.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigid.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_subgraph_cover
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_subgraph_cover to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_subgraph_cover.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_cluster_completion
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_cluster_completion to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_cluster_completion.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_rigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_rigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_motionKernel_eq_globalTwists.json"
#print axioms Papers.Rigidity.fiveConnected_k4Covered_flexible_exists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.fiveConnected_k4Covered_flexible_exists to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_fiveConnected_k4Covered_flexible_exists.json"
#print axioms Papers.Rigidity.SupportedCode.exists_code_attaining_bound
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.exists_code_attaining_bound to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_SupportedCode_exists_code_attaining_bound.json"
#print axioms Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BodyLoads_duplicate_loads_prefix_identity.json"
#print axioms Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_generic_alternating_space_center_defined_over_coefficients.json"
#print axioms Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BodyLoads_TwoBodyPin_lemma_three_seven.json"
#print axioms Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_SupportedCode_sum_priorityDimension_relabel.json"
#print axioms Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BarJoint_localRigidity_iff_rank_at_algebraicallyGeneric.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigidityRank_of_algebraicIndependent.json"
