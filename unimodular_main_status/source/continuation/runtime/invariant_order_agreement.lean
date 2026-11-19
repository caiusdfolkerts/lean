module

public import Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.HasLimits

public import Continuation.Runtime.IntrinsicLocalCharacterRatios
public import Continuation.Runtime.NormalAffineComplements
public import Continuation.Runtime.GroupActionSaturation

/-!
# Invariant opens on which two boundary order functions agree

The omitted boundary primes form a finite set. Removing the closures of the
primes where two order functions differ therefore defines an open subset.
Each removed component is invariant under the whole torus scheme, so the
open is invariant as well. Local unit character ratios give such opens
covering the saturation of the original affine open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

local instance orderAgreementLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

local instance orderAgreementTorusOpenNonempty : Nonempty T.torusOpen := by
  let t := genericPoint (splitTorusOver k (Fin n → ℤ)).left
  exact ⟨⟨T.torus.left t, ⟨t, rfl⟩⟩⟩

/-- Every codimension-one boundary closure is invariant on the actual
scheme product, not only under rational torus points. -/
theorem boundaryPrimeClosure_invariant (q : T.BoundaryPrime) :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹' closure {q.val} =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' closure {q.val} := by
  let G := splitTorusOver k (Fin n → ℤ)
  let p := (snd G X).left
  have hgeneric : genericPoint X.left ∉ T.boundary :=
    not_not.mpr (genericPoint_mem_open X.left T.torusOpen)
  have hcomponent := codimensionOne_boundaryComponent T.boundary_isClosed hgeneric
    q.val q.property.2 q.property.1
  have himage := T.graph_preserves_productComponent hcomponent
  have hpre := congrArg (fun Z => T.graphIso.hom ⁻¹' Z) himage
  have hinj : Function.Injective T.graphIso.hom := T.graphIso.hom.homeomorph.injective
  rw [Set.preimage_image_eq _ hinj] at hpre
  have h : (T.graphIso.hom ≫ p) ⁻¹' closure {q.val} = p ⁻¹' closure {q.val} :=
    hpre.symm
  simp only [p, G, T.graph_hom_snd] at h
  exact h

/-- A boundary component meets the saturation of an open exactly when it
already meets that open. At its generic point this is literal membership. -/
theorem boundaryPrime_mem_saturation_iff (U : X.left.Opens) (q : T.BoundaryPrime) :
    q.val ∈ GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) ↔
      q.val ∈ U := by
  constructor
  · rintro ⟨z, hzU, hza⟩
    have haZ : (γ[splitTorusOver k (Fin n → ℤ),X]).left z ∈ closure {q.val} := by
      rw [hza]
      exact subset_closure (Set.mem_singleton q.val)
    have hpZ : (snd (splitTorusOver k (Fin n → ℤ)) X).left z ∈ closure {q.val} := by
      change z ∈ (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' closure {q.val}
      rw [← T.boundaryPrimeClosure_invariant q]
      exact haZ
    exact (specializes_iff_mem_closure.mpr hpZ).mem_open U.isOpen hzU
  · intro hq
    exact GroupAction.subset_saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) hq

variable [NoetherianSpace X.left]

local instance orderAgreementBoundaryFinite : Finite T.BoundaryPrime :=
  (finite_codimensionOne_complement T.torusOpen).to_subtype

/-- The open obtained by removing exactly the boundary components where
the two actual rational order functions differ. -/
def boundaryOrderAgreementOpen (r s : X.left.functionField) : X.left.Opens :=
  ⟨(⋃ q : {q : T.BoundaryPrime // X.left.ord s q.val ≠ X.left.ord r q.val},
      closure {q.val.val})ᶜ,
    (isClosed_iUnion_of_finite (fun _ => isClosed_closure)).isOpen_compl⟩

theorem mem_boundaryOrderAgreementOpen (r s : X.left.functionField) (x : X.left) :
    x ∈ T.boundaryOrderAgreementOpen r s ↔
      ∀ q : T.BoundaryPrime, x ∈ closure {q.val} →
        X.left.ord s q.val = X.left.ord r q.val := by
  constructor
  · intro hx q hxq
    by_contra hne
    exact hx (Set.mem_iUnion.mpr ⟨⟨q, hne⟩, hxq⟩)
  · intro h hx
    obtain ⟨⟨q, hq⟩, hxq⟩ := Set.mem_iUnion.mp hx
    exact hq (h q hxq)

/-- The order-agreement open contains the entire original open torus. -/
theorem torusOpen_le_boundaryOrderAgreementOpen (r s : X.left.functionField) :
    T.torusOpen ≤ T.boundaryOrderAgreementOpen r s := by
  intro x hx
  apply (T.mem_boundaryOrderAgreementOpen r s x).mpr
  intro q hxq
  have hsubset : closure {q.val} ⊆ T.boundary :=
    closure_minimal (Set.singleton_subset_iff.mpr q.property.2) T.boundary_isClosed
  exact False.elim ((hsubset hxq) hx)

/-- Invariance is an equality of inverse-image opens under the actual
action and the actual product projection. -/
theorem boundaryOrderAgreementOpen_invariant (r s : X.left.functionField) :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ T.boundaryOrderAgreementOpen r s =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ
        T.boundaryOrderAgreementOpen r s := by
  apply Opens.ext
  change _ ⁻¹' (⋃ q : {q : T.BoundaryPrime //
      X.left.ord s q.val ≠ X.left.ord r q.val}, closure {q.val.val})ᶜ = _
  change _ = _ ⁻¹' (⋃ q : {q : T.BoundaryPrime //
      X.left.ord s q.val ≠ X.left.ord r q.val}, closure {q.val.val})ᶜ
  simp only [Set.preimage_compl, Set.preimage_iUnion, T.boundaryPrimeClosure_invariant]

/-- A local unit ratio gives membership in the invariant order-agreement
open: every boundary prime specializing to the point has equal orders. -/
theorem mem_boundaryOrderAgreementOpen_of_local_unit_ratio
    {U : X.left.Opens} [Nonempty U] (r s : X.left.functionField)
    (hr : r ≠ 0) (hs : s ≠ 0) (a : Γ(X.left,U))
    (ha : X.left.germToFunctionField U a = s / r)
    (x : X.left) (hx : x ∈ U) (hunit : IsUnit (X.left.presheaf.germ U x hx a)) :
    x ∈ T.boundaryOrderAgreementOpen r s := by
  apply (T.mem_boundaryOrderAgreementOpen r s x).mpr
  intro q hxq
  have hxBasic : x ∈ X.left.basicOpen a := (X.left.mem_basicOpen a x hx).mpr hunit
  have hqBasic : q.val ∈ X.left.basicOpen a :=
    (specializes_iff_mem_closure.mpr hxq).mem_open (X.left.basicOpen a).isOpen hxBasic
  have hqU : q.val ∈ U := X.left.basicOpen_le a hqBasic
  have hqUnit : IsUnit (X.left.presheaf.germ U q.val hqU a) :=
    (X.left.mem_basicOpen a q.val hqU).mp hqBasic
  have hregular : IsRegularUnitAt X.left q.val (s / r) := by
    refine ⟨?_, ?_⟩
    · rw [← ha]
      exact regular_germ_mem_regularAt X.left U a q.val hqU
    · have h := ((isUnit_stalk_iff q.val _).mp hqUnit).2
      rwa [X.left.algebraMap_germ_eq_germToFunctionField hqU a, ha] at h
  have hord := rationalOrder_zero_of_isRegularUnitAt q.val (s / r)
    (div_ne_zero hs hr) hregular
  rw [rationalOrder_div hs hr] at hord
  exact sub_eq_zero.mp hord

/-- The invariant order-agreement opens of the actual character terms
cover the entire scheme-theoretic action saturation of `U`. -/
theorem saturation_subset_characterOrderAgreementOpens
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : AddMonoidAlgebra k (Fin n → ℤ)) (hf : f ≠ 0)
    (hunit : ∀ x ∈ U, x ∈ T.torusOpen → IsRegularUnitAt X.left x
      (openTorusRationalAlgHom k n X.left T.torus.left f)) :
    GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) ⊆
      ⋃ m : {m : Fin n → ℤ // m ∈ f.coeff.support},
        (T.boundaryOrderAgreementOpen
          (openTorusRationalAlgHom k n X.left T.torus.left f)
          (openTorusRationalAlgHom k n X.left T.torus.left
            (AddMonoidAlgebra.single m.val (f.coeff m.val))) : Set X.left) := by
  classical
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hvalue : Function.Injective value :=
    openTorusRationalAlgHom_injective k n X.left T.torus.left
  have hvf : value f ≠ 0 := (map_ne_zero_iff value hvalue).mpr hf
  let W : Set X.left := ⋃ m : {m : Fin n → ℤ // m ∈ f.coeff.support},
    (T.boundaryOrderAgreementOpen (value f)
      (value (AddMonoidAlgebra.single m.val (f.coeff m.val))) : Set X.left)
  have hW : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹' W =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' W := by
    simp only [W, Set.preimage_iUnion]
    congr 1
    funext m
    exact congrArg (fun (V : (splitTorusOver k (Fin n → ℤ) ⊗ X).left.Opens) => (V : Set (splitTorusOver k (Fin n → ℤ) ⊗ X).left))
      (T.boundaryOrderAgreementOpen_invariant _ _)
  apply (GroupAction.saturation_subset_iff _ _ hW).mpr
  intro x hx
  obtain ⟨m, hm, a, ha, hau⟩ := T.exists_local_unit_character_ratio U hU f hf hunit x hx
  have hterm : (AddMonoidAlgebra.single m (f.coeff m) : AddMonoidAlgebra k (Fin n → ℤ)) ≠ 0 := by
    intro hz
    apply (Finsupp.mem_support_iff.mp hm)
    have hcoeff := congrArg (fun b : AddMonoidAlgebra k (Fin n → ℤ) => b.coeff m) hz
    simpa using hcoeff
  refine Set.mem_iUnion.mpr ⟨⟨m, hm⟩, ?_⟩
  exact T.mem_boundaryOrderAgreementOpen_of_local_unit_ratio
    (value f) (value (AddMonoidAlgebra.single m (f.coeff m))) hvf
    ((map_ne_zero_iff value hvalue).mpr hterm) a ha x hx hau

end PaperVerification.ToricSchemes.SplitToricEmbedding
