module

public import Continuation.Runtime.AffineOpenRigidity
public import Continuation.Runtime.IntrinsicReconstruction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Codimension-one detection of affine opens in normal schemes

The Hartogs intersection theorem for a normal affine coordinate ring implies
that a proper affine subopen must omit a point of codimension one. This is the
local input for proving that the complement of an affine open in a normal
separated scheme is a divisor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Integral closedness of the actual stalks implies integral closedness of
every nonempty affine coordinate ring. The ambient field is the scheme's
actual function field. -/
theorem affineOpen_isIntegrallyClosed_of_stalks
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X,U) := by
  letI : IsFractionRing Γ(X,U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply (isIntegrallyClosed_iff X.functionField).mpr
  intro z hz
  apply (mem_regular_range_iff_stalkwise X U z).mpr
  intro x hx
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : IsScalarTower Γ(X,U) (X.presheaf.stalk x) X.functionField :=
    functionField_isScalarTower X U ⟨x, hx⟩
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := hnormal x
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hz.tower_top

/-- A nonempty affine subopen of a normal affine open is the whole open if
it contains every actual codimension-one point of that open. -/
theorem normal_affineOpen_eq_of_contains_codimensionOne
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) [Nonempty V] [IsIntegrallyClosed Γ(X,U)]
    (hcodim : ∀ x ∈ U, Order.coheight x = 1 → x ∈ V) : V = U := by
  letI : Nonempty U :=
    ⟨⟨(Classical.choice (inferInstance : Nonempty V)).1,
      hVU (Classical.choice (inferInstance : Nonempty V)).2⟩⟩
  apply affineOpen_eq_of_bijective_restriction hU hV hVU
  constructor
  · intro a b hab
    apply X.germToFunctionField_injective U
    simpa only [germToFunctionField_restrict] using
      congrArg (X.germToFunctionField V) hab
  · intro b
    have hb : X.germToFunctionField V b ∈
        (X.germToFunctionField U).hom.range := by
      apply (normalAffine_regular_iff_codimensionOne U hU _).mpr
      intro x hx hheight
      exact regular_germ_mem_regularAt X V b x (hcodim x hx hheight)
    obtain ⟨a, ha⟩ := hb
    refine ⟨a, X.germToFunctionField_injective V ?_⟩
    rw [germToFunctionField_restrict]
    exact ha

/-- A proper nonempty affine subopen of a normal affine open omits an
actual codimension-one point. -/
theorem exists_codimensionOne_notMem_of_affineOpen_ne
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) [Nonempty V] [IsIntegrallyClosed Γ(X,U)]
    (hne : V ≠ U) : ∃ x ∈ U, Order.coheight x = 1 ∧ x ∉ V := by
  by_contra h
  push_neg at h
  apply hne
  exact normal_affineOpen_eq_of_contains_codimensionOne hU hV hVU h

/-- A proper generization of a codimension-one point is the generic point,
and hence belongs to every nonempty open. -/
theorem eq_of_codimensionOne_specializes_notMem_open
    (U : X.Opens) [Nonempty U] {x y : X}
    (hx : Order.coheight x = 1) (hyx : y ⤳ x) (hy : y ∉ U) : y = x := by
  by_contra hne
  have hlt : x < y :=
    ⟨hyx, fun hxy => hne (Specializes.antisymm hyx hxy).eq⟩
  have hfin : Order.coheight y < ⊤ :=
    (Order.coheight_anti hlt.le).trans_lt (hx ▸ ENat.one_lt_top)
  have hmax : IsMax y := Order.coheight_eq_zero.mp <| Order.lt_one_iff.mp <|
    hx ▸ Order.coheight_strictAnti hlt hfin
  have hygen : y = genericPoint X :=
    (Specializes.antisymm (hmax (genericPoint_specializes y))
      (genericPoint_specializes y)).eq
  exact hy (hygen ▸ genericPoint_mem_open X U)

/-- Only finitely many codimension-one points can be omitted by a nonempty
open of a noetherian integral scheme. -/
theorem finite_codimensionOne_complement [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {x : X | Order.coheight x = 1 ∧ x ∉ U}.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let g : S → X := fun Z => (hSirreducible Z Z.property).genericPoint
  have hfiniteRange : (Set.range g).Finite := by
    letI : Finite S := hSfinite.to_subtype
    exact Set.finite_range g
  apply hfiniteRange.subset
  rintro x ⟨hx, hxU⟩
  have hxUnion : x ∈ ⋃₀ S := by
    rw [← hSunion]
    exact hxU
  obtain ⟨Z, hZS, hxZ⟩ := Set.mem_sUnion.mp hxUnion
  have hyGeneric : IsGenericPoint (g ⟨Z, hZS⟩) Z :=
    (hSirreducible Z hZS).isGenericPoint_genericPoint (hSclosed Z hZS)
  have hZcompl : Z ⊆ (U : Set X)ᶜ :=
    hSunion.symm ▸ Set.subset_sUnion_of_mem hZS
  exact ⟨⟨Z, hZS⟩,
    eq_of_codimensionOne_specializes_notMem_open U hx
      (hyGeneric.specializes hxZ) (hZcompl hyGeneric.mem)⟩

/-- The complement of a nonempty affine open in a normal separated
noetherian integral scheme is precisely the finite union of closures of
the omitted codimension-one points. In particular, it has no additional
component of higher codimension. -/
theorem affineOpen_complement_eq_codimensionOne_closures
    [NoetherianSpace X] [X.IsSeparated]
    (hnormal : ∀ (V : X.Opens), IsAffineOpen V → Nonempty V →
      IsIntegrallyClosed Γ(X,V))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (U : Set X)ᶜ =
      ⋃ q : {x : X // Order.coheight x = 1 ∧ x ∉ U}, closure {q.val} := by
  let Q := {x : X // Order.coheight x = 1 ∧ x ∉ U}
  letI : Finite Q := (finite_codimensionOne_complement U).to_subtype
  let Z : Set X := ⋃ q : Q, closure {q.val}
  have hZclosed : IsClosed Z := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  have hZU : Z ⊆ (U : Set X)ᶜ := by
    apply Set.iUnion_subset
    intro q
    exact closure_minimal (Set.singleton_subset_iff.mpr q.property.2)
      U.isOpen.isClosed_compl
  change (U : Set X)ᶜ = Z
  apply Set.Subset.antisymm _ hZU
  intro x hxU
  by_contra hxZ
  let W : X.Opens := ⟨Zᶜ, hZclosed.isOpen_compl⟩
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (show x ∈ W from hxZ)
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : Nonempty (V ⊓ U : X.Opens) :=
    ⟨⟨genericPoint X, genericPoint_mem_open X V, genericPoint_mem_open X U⟩⟩
  letI : IsIntegrallyClosed Γ(X,V) := hnormal V hV inferInstance
  have hEq : V ⊓ U = V := by
    apply normal_affineOpen_eq_of_contains_codimensionOne hV (hV.inf hU) inf_le_left
    intro y hy hheight
    refine ⟨hy, ?_⟩
    by_contra hyU
    have hyZ : y ∈ Z :=
      Set.mem_iUnion.mpr ⟨⟨y, hheight, hyU⟩, subset_closure (Set.mem_singleton y)⟩
    exact (hVW hy) hyZ
  exact hxU (show x ∈ U from (show x ∈ V ⊓ U from hEq.symm ▸ hxV).2)

/-- Once an affine open has been enlarged to an open, equality can be
tested on the actual codimension-one points. No extra points of higher
codimension can occur in the enlargement. -/
theorem affineOpen_eq_of_codimensionOne_membership
    [NoetherianSpace X] [X.IsSeparated]
    (hnormal : ∀ (V : X.Opens), IsAffineOpen V → Nonempty V →
      IsIntegrallyClosed Γ(X,V))
    (U W : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (hUW : U ≤ W)
    (hcodim : ∀ x ∈ W, Order.coheight x = 1 → x ∈ U) : W = U := by
  apply le_antisymm _ hUW
  intro x hxW
  by_contra hxU
  have hx : x ∈ ⋃ q : {x : X // Order.coheight x = 1 ∧ x ∉ U},
      closure {q.val} := by
    rw [← affineOpen_complement_eq_codimensionOne_closures hnormal U hU]
    exact hxU
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  have hqW : q.val ∈ W :=
    (specializes_iff_mem_closure.mpr hxq).mem_open W.isOpen hxW
  exact q.property.2 (hcodim q.val hqW q.property.1)

end PaperVerification.ToricSchemes
