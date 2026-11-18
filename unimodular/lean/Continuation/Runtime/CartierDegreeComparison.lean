module

public import Continuation.Divisor.WeilCurveDegree
public import Continuation.Divisor.WallCurves

/-!
# Ordinary degree of the original fractional Cartier sheaf

The two degree interfaces use the same local orders and residue degrees.
This file constructs a rational-section presentation of the *original*
Cartier sheaf, whose local equation is the inverse of its original rational
frame. Consequently the new Cartier coefficients are literally the old Weil
coefficients. No scheme, sheaf, or degree is replaced by a combinatorial model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.CartierData

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Divisors
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X] (D : CartierData X)

/-- An old open-subsite trivialization is an ordinary frame on every smaller open. -/
theorem ordinaryFrame {U : X.Opens} (e : D.Frame U) :
    IsFrame D.sheaf U (D.frameGenerator e U le_rfl) := by
  intro V hVU
  change Function.Bijective (fun a : Γ(X,V) =>
    a • D.sheaf.presheaf.map (homOfLE hVU).op (D.frameGenerator e U le_rfl))
  rw [D.frameGenerator_restrict e hVU]
  have h (a : Γ(X,V)) :
      a • D.frameGenerator e V hVU = (D.frameLinearEquiv e V hVU).symm a := by
    apply (D.frameLinearEquiv e V hVU).injective
    simp [frameGenerator]
  simpa only [h] using (D.frameLinearEquiv e V hVU).symm.bijective

/-- The ratio of the actual rational frame values is the ratio of their generic germs. -/
theorem ordinaryFrame_genericGenerator_transition {U V : X.Opens}
    [Nonempty U] [Nonempty V] (e : D.Frame U) (f : D.Frame V) :
    (D.frameRationalGenerator e / D.frameRationalGenerator f) •
      (D.ordinaryFrame f).genericGenerator = (D.ordinaryFrame e).genericGenerator := by
  let W : X.Opens := U ⊓ V
  letI : Nonempty W := ⟨⟨genericPoint X, genericPoint_mem_open X U,
    genericPoint_mem_open X V⟩⟩
  obtain ⟨a, ha⟩ := D.exists_frameTransitionUnit e f
    (V := W) inf_le_left inf_le_right
  have hs : (a : Γ(X,W)) • D.frameGenerator f W inf_le_right =
      D.frameGenerator e W inf_le_left := by
    apply D.sectionValue_injective W
    rw [D.sectionValue_smul, D.sectionValue_frameGenerator,
      D.sectionValue_frameGenerator, ha,
      div_mul_cancel₀ _ (D.frameRationalGenerator_ne_zero f)]
  have hg := congrArg
    (D.sheaf.presheaf.germ W (genericPoint X) (genericPoint_mem_open X W)) hs
  rw [germ_smul', ← D.frameGenerator_restrict f inf_le_right,
    ← D.frameGenerator_restrict e inf_le_left,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ha] at hg
  exact hg

/-- A rational section normalized to have value one in the original fractional embedding. -/
def normalizedRationalSection {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    D.sheaf.presheaf.stalk (genericPoint X) :=
  (D.frameRationalGenerator e)⁻¹ • (D.ordinaryFrame e).genericGenerator

theorem normalizedRationalSection_ne_zero {U : X.Opens} [Nonempty U]
    (e : D.Frame U) : D.normalizedRationalSection e ≠ 0 :=
  smul_ne_zero (inv_ne_zero (D.frameRationalGenerator_ne_zero e))
    (D.ordinaryFrame e).genericGenerator_ne_zero

/-- In every frame, the normalized rational section has the inverse frame value. -/
theorem ordinaryFrame_normalizedCoordinate {U V : X.Opens}
    [Nonempty U] [Nonempty V] (e : D.Frame U) (f : D.Frame V) :
    (D.ordinaryFrame f).genericCoordinate (D.normalizedRationalSection e) =
      (D.frameRationalGenerator f)⁻¹ := by
  have h := (D.ordinaryFrame f).genericCoordinate_unique
    (D.ordinaryFrame e).genericGenerator
    (D.frameRationalGenerator e / D.frameRationalGenerator f)
    (D.ordinaryFrame_genericGenerator_transition e f)
  rw [normalizedRationalSection, _root_.map_smul, smul_eq_mul, h]
  field_simp [D.frameRationalGenerator_ne_zero e,
    D.frameRationalGenerator_ne_zero f]

variable [IsLocallyNoetherian X]

/-- A finite genuine rational-section presentation with exactly the original Weil coefficients. -/
theorem exists_ordinaryPresentation [CompactSpace X] :
    ∃ q : D.sheaf.presheaf.stalk (genericPoint X),
      ∃ p : LineRationalSectionPresentation D.sheaf q,
        p.cartier.coefficient = D.weilCoefficient := by
  choose U hx e using D.locallyFree
  let e' (x : X) : D.Frame (U x) := (e x).some
  letI : Nonempty (U (genericPoint X)) := ⟨⟨genericPoint X, hx (genericPoint X)⟩⟩
  let q := D.normalizedRationalSection (e' (genericPoint X))
  have cover : ⋃ x : X, (U x : Set X) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨points, hpoints⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen) cover.ge
  let I := {x : X // x ∈ points}
  have hcover : ⋃ i : I, (U i.val : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hpoints (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hix⟩
  let p : LineRationalSectionPresentation D.sheaf q :=
    LineRationalSectionPresentation.ofFiniteFrames D.sheaf
      (fun i : I => U i.val) (fun i => ⟨⟨i.val, hx i.val⟩⟩) hcover
      (fun i => D.frameGenerator (e' i.val) (U i.val) le_rfl)
      (fun i => D.ordinaryFrame (e' i.val)) q
      (D.normalizedRationalSection_ne_zero (e' (genericPoint X)))
  refine ⟨q, p, ?_⟩
  funext x
  let i := p.cartier.indexAt x
  have hxi := p.cartier.indexAt_mem x
  letI : Nonempty (p.cartier.opens i) := ⟨⟨x, hxi⟩⟩
  letI : Nonempty (U i.val) := ⟨⟨i.val, hx i.val⟩⟩
  rw [p.cartier.coefficient_eq_ord_of_mem x i hxi]
  change X.ord ((D.ordinaryFrame (e' i.val)).genericCoordinate q) x = _
  rw [D.ordinaryFrame_normalizedCoordinate,
    rationalOrder_inv (D.frameRationalGenerator_ne_zero (e' i.val)),
    D.weilCoefficient_eq_neg_frameOrder (e' i.val) hxi]

variable [IsNoetherian X]

/-- The ordinary line-bundle degree of the original Cartier sheaf is its original
residue-weighted Weil degree. The proof constructs the rational-section witness. -/
theorem hasLineBundleDegree_original (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfinite : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicGeometry.Intersection.HasLineBundleDegree f hdim D.sheaf
      (D.degree f hfinite) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  obtain ⟨q, p, hp⟩ := D.exists_ordinaryPresentation
  refine ⟨q, p, ?_⟩
  change AlgebraicCycle.degreeOverField (baseField := k) (p.cartier.zeroCycle hdim).val =
    AlgebraicCycle.degree f (D.weilCycle hfinite)
  rw [AlgebraicCycle.degreeOverField, AlgebraicCycle.degree_apply]
  apply finsum_congr
  intro x
  rw [nsmul_eq_mul, mul_comm]
  congr 1
  exact congrFun hp x

/-- Uniqueness of ordinary degree identifies the two interfaces exactly. -/
theorem lineBundleDegree_eq_original (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfinite : LocallyFiniteSupport D.weilCoefficient)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X D.sheaf] :
    AlgebraicGeometry.Intersection.lineBundleDegree f hdim D.sheaf =
      D.degree f hfinite :=
  AlgebraicGeometry.Intersection.lineBundleDegree_value_unique f hdim
    (AlgebraicGeometry.Intersection.hasLineBundleDegree_lineBundleDegree f hdim D.sheaf)
    (D.hasLineBundleDegree_original k f hdim hfinite)

#print axioms exists_ordinaryPresentation
#print axioms hasLineBundleDegree_original
#print axioms lineBundleDegree_eq_original

end PaperVerification.ToricSchemes.CartierData
