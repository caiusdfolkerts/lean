module

public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import all Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Lean.Elab.Tactic.Omega
import all Lean.Elab.Tactic.Omega
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
import all Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Opposite
import all Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import all Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Geometry.Manifold.Immersion
import all Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import all Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import all Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Topology.Category.TopCat.EpiMono
import all Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Algebra.Homology.Homotopy
import all Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import all Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import all Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.MetricSpace.Basic
import all Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
import all Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import all Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.Analysis.Convex.Contractible
import all Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
import all Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.Real.Lemmas
import all Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import all Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import all Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.SingleHomology
import all Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
import all Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SingularSet
import all Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import all Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import all Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Abelian.CommSq
import all Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import all Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Analysis.Convex.Combination
import all Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Convex
import all Mathlib.Analysis.Normed.Module.Convex
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions

noncomputable section

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

def cochainDegreeShiftEmbedding (k : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => k+n) (fun _ _ h => Nat.add_left_cancel h)
    (by intro i j; change (i+1=j) ↔ (k+i+1=k+j); omega)

instance cochainDegreeShiftEmbedding_isRelIff (k : ℕ) : (cochainDegreeShiftEmbedding k).IsRelIff := by
  unfold cochainDegreeShiftEmbedding
  infer_instance

instance cochainDegreeShiftEmbedding_isTruncGE (k : ℕ) : (cochainDegreeShiftEmbedding k).IsTruncGE where
  mem_next {j l} h := by
    refine ⟨j+1,?_⟩
    change k+j+1=l at h
    change k+(j+1)=l
    omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology -/

/-! # Good Shift Cohomology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions

noncomputable section

section

/-! Canonical truncation shifts actual cohomology, including its new degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

def cochainGoodShiftHomologyIso (K : CochainComplex C ℕ) (k n : ℕ) :
    (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).homology n ≅ K.homology (k+n) := by
  let e := RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k
  have : QuasiIsoAt (K.πTruncGE e) (k+n) := K.quasiIsoAt_πTruncGE e (j := n) rfl
  exact ((K.truncGE' e).extendHomologyIso e (j := n) (j' := k+n) rfl).symm ≪≫
    (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).symm

theorem cochainGoodTruncation_quasiIso (K : CochainComplex C ℕ) (k : ℕ)
    (hK : ∀ n, n<k → K.ExactAt n) : QuasiIso (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  apply (K.quasiIso_πTruncGE_iff_isSupported (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).mpr
  constructor
  intro n hn
  apply hK n
  by_contra h
  have he : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).f (n-k) = n := by
    change k+(n-k)=n
    omega
  exact hn (n-k) he


end

/-! The canonical good-shift cohomology isomorphism acts on the original actual cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℕ) (k n : ℕ)

def cochainGoodShiftCyclesMap : K.cycles (k+n) ⟶
    (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).cycles n :=
  cyclesMap (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) (k+n) ≫
    ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).extendCyclesIso
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) (j := n) (j' := k+n) rfl).hom

theorem cochainGoodShiftCyclesMap_inclusion :
    cochainGoodShiftCyclesMap K k n ≫ (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).iCycles n =
      K.iCycles (k+n) ≫ (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n := by
  unfold cochainGoodShiftCyclesMap
  rw [Category.assoc, extendCyclesIso_hom_iCycles, ← Category.assoc]
  change (cyclesMap (K.πTruncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) (k+n) ≫
      (K.truncGE (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).iCycles (k+n)) ≫
      ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).extendXIso (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
        (i := n) (i' := k+n) rfl).hom = _
  rw [cyclesMap_i, Category.assoc]
  rw [πTruncGE, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).liftExtend_f _ _ (i := n) (i' := k+n) rfl]
  simp only [restrictionXIso, eqToIso_refl, Iso.refl_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change K.iCycles (k+n) ≫ 𝟙 (K.X (k+n)) ≫
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n = _
  rw [Category.id_comp]

theorem cochainGoodShiftCyclesMap_homologyπ :
    cochainGoodShiftCyclesMap K k n ≫ (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).homologyπ n ≫
        (cochainGoodShiftHomologyIso K k n).hom = K.homologyπ (k+n) := by
  let e := RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k
  let T := K.truncGE' e
  have : QuasiIsoAt (K.πTruncGE e) (k+n) := K.quasiIsoAt_πTruncGE e (j := n) rfl
  change (cyclesMap (K.πTruncGE e) (k+n) ≫ (T.extendCyclesIso e (j := n) (j' := k+n) rfl).hom) ≫
    T.homologyπ n ≫ ((T.extendHomologyIso e (j := n) (j' := k+n) rfl).inv ≫
      (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).inv) = K.homologyπ (k+n)
  rw [Category.assoc, ← Category.assoc (T.extendCyclesIso e rfl).hom,
    ← homologyπ_extendHomologyIso_hom, Category.assoc]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  change (cyclesMap (K.πTruncGE e) (k+n) ≫ (K.truncGE e).homologyπ (k+n)) ≫
    (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).inv = _
  rw [← homologyπ_naturality, Category.assoc, isoOfQuasiIsoAt_hom_inv_id,
    Category.comp_id]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Basic -/

/-! # Basic -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Basic

noncomputable section

/-!
# Genuine singular cochains with module coefficients

The chain functor is evaluated in the opposite category of modules. Its degreewise
coproducts are therefore products of modules. Passing back from the opposite
category reverses the differential and gives ordinary (unnormalized) singular
cochains, rather than chains relabelled as cochains.

This construction extends the previously checked `AvailableSingular.lean` and
`OppositeCochainAudit.lean` in the frozen September 2026 Hodge audit. The current
definitions are generic in the coefficient module; no Hodge or cycle-class
structure is assumed or added here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

variable {R : Type} [Ring R]

/-- Chains of a simplicial set in the opposite category of coefficient modules. -/
abbrev oppositeSimplicialChains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    ChainComplex (ModuleCat.{0} R)ᵒᵖ ℕ :=
  K.chainComplex (op M)

/-- Ordinary simplicial cochains: degree `n` consists of all coefficient-valued
functions on the `n`-simplices. The function description is established in
`Degreewise.lean`. -/
abbrev simplicialCochains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (oppositeSimplicialChains K M).unop

/-- Genuine continuous singular `n`-simplices of a topological space. -/
abbrev singularSimplices (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X) _⦋n⦌

/-- Unnormalized singular cochains, formed from the genuine singular simplicial set. -/
abbrev singularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  simplicialCochains (TopCat.toSSet.obj X) M

/-- Singular cohomology with coefficients in the indicated module. -/
abbrev singularCohomology (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} R :=
  (singularCochains M X).homology n

/-- Compatibility with mathlib's homology-in-the-opposite-category construction. -/
def singularCohomologyOppositeIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCohomology M X n ≅
      unop (((TopCat.toSSet.obj X).chainComplex (op M)).homology n) :=
  ((TopCat.toSSet.obj X).chainComplex (op M)).homologyUnop n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Basic
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Basic"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Representatives -/

/-! # Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Representatives

noncomputable section

/-!
# Cocycles, coboundaries, and representatives of singular cohomology

The quotient descriptions here are the explicit module quotients already identified
with categorical homology by mathlib's `ShortComplex.moduleCatHomologyIso`. In
particular, no independently chosen cohomology theory or comparison axiom is used.
The final declarations specialize this description to `singularCochains`.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]

/-- The kernel of the outgoing differential in a cochain complex. -/
abbrev cochainCocycles (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (K.X n) :=
  LinearMap.ker (K.sc n).g.hom

/-- The incoming differential, with its codomain restricted to cocycles. -/
abbrev cochainBoundaryMap (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (K.sc n).X₁ →ₗ[R] cochainCocycles K n :=
  (K.sc n).moduleCatToCycles

/-- Coboundaries as a submodule of cocycles. -/
abbrev cochainBoundaries (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (cochainCocycles K n) :=
  LinearMap.range (cochainBoundaryMap K n)

/-- Mathlib's categorical cohomology is the quotient of cocycles by coboundaries. -/
def cohomologyQuotientIso (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    K.homology n ≅ ModuleCat.of R (cochainCocycles K n ⧸ cochainBoundaries K n) :=
  (K.sc n).moduleCatHomologyIso

/-- The cohomology class of a cocycle. -/
def cochainClass (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    cochainCocycles K n →ₗ[R] K.homology n :=
  (cohomologyQuotientIso K n).toLinearEquiv.symm.toLinearMap.comp
    (cochainBoundaries K n).mkQ

@[simp]
theorem mem_cochainCocycles_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : K.X n) :
    x ∈ cochainCocycles K n ↔ (K.d n (n + 1)) x = 0 := by
  change (K.d n ((ComplexShape.up ℕ).next n)) x = 0 ↔ _
  rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

/-- The class map just defined is the canonical categorical homology projection. -/
theorem cochainClass_eq_homologyπ (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : cochainCocycles K n) :
    cochainClass K n x =
      (K.homologyπ n) ((K.sc n).moduleCatCyclesIso.inv x) := by
  change (K.sc n).moduleCatHomologyIso.inv ((K.sc n).moduleCatLeftHomologyData.π x) =
    (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv x)
  exact (ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_π) x).symm

/-- Every categorical cohomology class has a cocycle representative. -/
theorem cochainClass_surjective (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (cochainClass K n) :=
  (cohomologyQuotientIso K n).toLinearEquiv.symm.surjective.comp
    (cochainBoundaries K n).mkQ_surjective

/-- Two cocycles have the same class exactly when their difference is a coboundary. -/
theorem cochainClass_eq_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K n) :
    cochainClass K n x = cochainClass K n y ↔ x - y ∈ cochainBoundaries K n := by
  change (cohomologyQuotientIso K n).toLinearEquiv.symm ((cochainBoundaries K n).mkQ x) =
      (cohomologyQuotientIso K n).toLinearEquiv.symm ((cochainBoundaries K n).mkQ y) ↔ _
  rw [(cohomologyQuotientIso K n).toLinearEquiv.symm.injective.eq_iff]
  exact Submodule.Quotient.eq _

/-- Equality of classes expressed using an actual primitive for the difference. -/
theorem cochainClass_eq_iff_exists (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K n) :
    cochainClass K n x = cochainClass K n y ↔
      ∃ z : (K.sc n).X₁, (K.sc n).f z = (x : K.X n) - (y : K.X n) := by
  rw [cochainClass_eq_iff]
  change (∃ z, cochainBoundaryMap K n z = x - y) ↔ _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

/-- In degree `n + 1`, an equal pair of classes differs by the differential
of an actual degree-`n` cochain. -/
theorem cochainClass_eq_iff_exists_succ (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : cochainCocycles K (n + 1)) :
    cochainClass K (n + 1) x = cochainClass K (n + 1) y ↔
      ∃ z : K.X n, (K.d n (n + 1)) z =
        (x : K.X (n + 1)) - (y : K.X (n + 1)) := by
  rw [cochainClass_eq_iff_exists]
  change (∃ z : K.X ((ComplexShape.up ℕ).prev (n + 1)),
    (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) z =
      (x : K.X (n + 1)) - (y : K.X (n + 1))) ↔ _
  rw [(ComplexShape.up ℕ).prev_eq'
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

@[simp]
theorem cochainClass_eq_zero_iff (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : cochainCocycles K n) :
    cochainClass K n x = 0 ↔ x ∈ cochainBoundaries K n := by
  simpa using cochainClass_eq_iff K n x 0

/-- Cocycles in the genuine singular cochain complex. -/
abbrev singularCocycles (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :=
  cochainCocycles (Basic.singularCochains M X) n

/-- Singular coboundaries, viewed as a submodule of singular cocycles. -/
abbrev singularBoundaries (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :=
  cochainBoundaries (Basic.singularCochains M X) n

/-- The explicit cocycle/coboundary quotient of genuine singular cohomology. -/
abbrev singularCohomologyQuotientIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n ≅
      ModuleCat.of R (singularCocycles M X n ⧸ singularBoundaries M X n) :=
  cohomologyQuotientIso (Basic.singularCochains M X) n

/-- The singular cohomology class of a singular cocycle. -/
abbrev singularClass (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCocycles M X n →ₗ[R] Basic.singularCohomology M X n :=
  cochainClass (Basic.singularCochains M X) n

/-- Every genuine singular cohomology class has a singular cocycle representative. -/
theorem singularClass_surjective (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Function.Surjective (singularClass M X n) :=
  cochainClass_surjective (Basic.singularCochains M X) n

/-- The usual cocycle-modulo-coboundary equality criterion for singular classes. -/
theorem singularClass_eq_iff (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (x y : singularCocycles M X n) :
    singularClass M X n x = singularClass M X n y ↔ x - y ∈ singularBoundaries M X n :=
  cochainClass_eq_iff (Basic.singularCochains M X) n x y

/-- Equality of positive-degree singular classes is precisely the existence
of a singular cochain whose coboundary is their difference. -/
theorem singularClass_eq_iff_exists_succ (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (x y : singularCocycles M X (n + 1)) :
    singularClass M X (n + 1) x = singularClass M X (n + 1) y ↔
      ∃ z : (Basic.singularCochains M X).X n,
        ((Basic.singularCochains M X).d n (n + 1)) z =
          (x : (Basic.singularCochains M X).X (n + 1)) -
            (y : (Basic.singularCochains M X).X (n + 1)) :=
  cochainClass_eq_iff_exists_succ (Basic.singularCochains M X) n x y

@[simp]
theorem singularClass_eq_zero_iff (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (x : singularCocycles M X n) :
    singularClass M X n x = 0 ↔ x ∈ singularBoundaries M X n :=
  cochainClass_eq_zero_iff (Basic.singularCochains M X) n x

end

end OAI.AlgebraicTopology.Cohomology.Singular.Representatives
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Representatives"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Coefficients -/

/-! # Coefficients -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

noncomputable section

section

/-!
# Degreewise meaning of the singular cochain complex

The opposite-category construction in `Basic` has all functions on genuine
simplices as its degreewise objects. In particular, there is no finite-support
restriction on cochains. The final isomorphism indexes these functions directly
by continuous maps from mathlib's standard topological simplex.

The product/coproduct argument generalizes the checked
`OppositeCochainAudit.lean` from the frozen September 2026 audit, replacing its
rational coefficient module with an arbitrary module over a ring.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R : Type} [Ring R]

/-- Evaluate a simplicial cochain at a simplex. -/
def simplicialEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    (s : K _⦋n⦌) : (Basic.simplicialCochains K M).X n ⟶ M :=
  (K.ιChainComplex (R := op M) s).unop

/-- Cochains in degree `n` are all module-valued functions on the `n`-simplices. -/
def degreewiseFunctionIso (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Basic.simplicialCochains K M).X n ≅ ModuleCat.of R (K _⦋n⦌ → M) :=
  (opProductIsoCoproduct (fun _ : K _⦋n⦌ => M)).unop ≪≫
    ModuleCat.piIsoPi (fun _ : K _⦋n⦌ => M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degreewise isomorphism respects evaluation at each simplex. -/
theorem degreewiseFunctionIso_evaluation (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n⦌) :
    (degreewiseFunctionIso K M n).hom ≫ ModuleCat.ofHom (LinearMap.proj s) =
      simplicialEvaluation K M s := by
  simp only [degreewiseFunctionIso, Iso.trans_hom, Iso.unop_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype]
  simpa only [simplicialEvaluation, SSet.ιChainComplex, unop_comp,
    Quiver.Hom.unop_op] using
    congrArg Quiver.Hom.unop (π_comp_opProductIsoCoproduct_hom
      (fun _ : K _⦋n⦌ => M) s)

/-- Function coordinates of a cochain, evaluated at a simplex. -/
@[simp]
theorem degreewiseFunctionIso_hom_apply (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n⦌) :
    (degreewiseFunctionIso K M n).hom c s = simplicialEvaluation K M s c := by
  exact ConcreteCategory.congr_hom (degreewiseFunctionIso_evaluation K M s) c

/-- The singular cochain object is the module of all functions on singular simplices. -/
def singularDegreewiseFunctionIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (Basic.singularCochains M X).X n ≅ ModuleCat.of R (Basic.singularSimplices X n → M) :=
  degreewiseFunctionIso (TopCat.toSSet.obj X) M n

/-- A genuine singular simplex is a continuous map from the standard simplex. -/
def singularSimplicesEquivContinuousMap (X : TopCat.{0}) (n : ℕ) :
    Basic.singularSimplices X n ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv X (op ⦋n⦌)

/-- The degree-`n` singular cochain object is the module of all functions on the
continuous maps from the standard topological `n`-simplex. -/
def singularDegreewiseContinuousFunctionIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    (Basic.singularCochains M X).X n ≅
      ModuleCat.of R (C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M) :=
  singularDegreewiseFunctionIso M X n ≪≫
    (LinearEquiv.piCongrLeft' R (fun _ : Basic.singularSimplices X n => M)
      (singularSimplicesEquivContinuousMap X n)).toModuleIso

end

/-!
# Coefficient maps in genuine singular cohomology

The maps below are induced by mathlib's singular chain functor in the
opposite category of modules. Applying the unop functor turns the map induced
by `f.op` into the ordinary covariant coefficient map on singular cochains.
No cohomology groups or comparison maps are supplied as extra data.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]
variable {M N P : ModuleCat.{0} R}

/-- The cochain map induced by a linear map of coefficient modules. -/
def coefficientCochainMap (f : M ⟶ N) (X : TopCat.{0}) :
    Basic.singularCochains M X ⟶ Basic.singularCochains N X :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)ᵒᵖ).map
      f.op).app X).op

@[simp]
theorem coefficientCochainMap_id (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    coefficientCochainMap (𝟙 M) X = 𝟙 (Basic.singularCochains M X) := by
  simp [coefficientCochainMap]
  exact (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_id _

@[simp]
theorem coefficientCochainMap_comp (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0}) :
    coefficientCochainMap (f ≫ g) X =
      coefficientCochainMap f X ≫ coefficientCochainMap g X := by
  simp [coefficientCochainMap]
  exact (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map_comp _ _

/-- On each simplex, a coefficient map postcomposes evaluation with `f`. -/
@[reassoc]
theorem coefficientCochainMap_evaluation (f : M ⟶ N) (X : TopCat.{0})
    {n : ℕ} (s : Basic.singularSimplices X n) :
    (coefficientCochainMap f X).f n ≫ simplicialEvaluation (TopCat.toSSet.obj X) N s =
      simplicialEvaluation (TopCat.toSSet.obj X) M s ≫ f := by
  change (CategoryTheory.Limits.Sigma.map
      (fun _ : Basic.singularSimplices X n => f.op)).unop ≫
      (CategoryTheory.Limits.Sigma.ι (fun _ : Basic.singularSimplices X n => op N) s).unop =
    (CategoryTheory.Limits.Sigma.ι (fun _ : Basic.singularSimplices X n => op M) s).unop ≫ f
  rw [← unop_comp, CategoryTheory.Limits.Sigma.ι_map]
  rfl

/-- In the established function coordinates, a coefficient map acts pointwise. -/
@[simp]
theorem coefficientCochainMap_apply (f : M ⟶ N) (X : TopCat.{0})
    {n : ℕ} (c : (Basic.singularCochains M X).X n) (s : Basic.singularSimplices X n) :
    (singularDegreewiseFunctionIso N X n).hom ((coefficientCochainMap f X).f n c) s =
      f ((singularDegreewiseFunctionIso M X n).hom c s) := by
  calc
    _ = simplicialEvaluation (TopCat.toSSet.obj X) N s
        ((coefficientCochainMap f X).f n c) :=
      degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) N _ s
    _ = f (simplicialEvaluation (TopCat.toSSet.obj X) M s c) :=
      ConcreteCategory.congr_hom (coefficientCochainMap_evaluation f X s) c
    _ = _ := congrArg (fun x : M => f x)
      (degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) M c s).symm

/-- The singular cohomology map induced by a linear coefficient map. -/
def coefficientMap (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n ⟶ Basic.singularCohomology N X n :=
  HomologicalComplex.homologyMap (coefficientCochainMap f X) n

@[simp]
theorem coefficientMap_id (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    coefficientMap (𝟙 M) X n = 𝟙 (Basic.singularCohomology M X n) := by
  simp [coefficientMap]

@[simp]
theorem coefficientMap_comp (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0}) (n : ℕ) :
    coefficientMap (f ≫ g) X n = coefficientMap f X n ≫ coefficientMap g X n := by
  simp [coefficientMap, HomologicalComplex.homologyMap_comp]

/-- For a fixed space, singular cochains are functorial in the coefficient module. -/
def coefficientCochainFunctor (X : TopCat.{0}) :
    ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} R) ℕ where
  obj M := Basic.singularCochains M X
  map f := coefficientCochainMap f X

/-- For a fixed space and degree, singular cohomology is functorial in coefficients. -/
def coefficientFunctor (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R ⥤ ModuleCat.{0} R where
  obj M := Basic.singularCohomology M X n
  map f := coefficientMap f X n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Coefficients"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Functor -/

/-! # Functor -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Functor

noncomputable section

/-!
# Pullback on genuine singular cochains

The covariant simplicial chain functor, evaluated in the opposite category of
modules, becomes a contravariant cochain functor after passing back from that
opposite category. The maps below therefore pull back actual cochains and their
cohomology along continuous maps.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]

/-- Simplicial cochains depend contravariantly on the simplicial set. -/
def simplicialCochainsFunctor (M : ModuleCat.{0} R) :
    SSet.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  ((SSet.chainComplexFunctor ((ModuleCat.{0} R)ᵒᵖ)).obj (op M)).op ⋙
    HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)

/-- Pullback of cochains along a morphism of simplicial sets. -/
def simplicialPullback (M : ModuleCat.{0} R) {K L : SSet.{0}} (f : K ⟶ L) :
    Basic.simplicialCochains L M ⟶ Basic.simplicialCochains K M :=
  (simplicialCochainsFunctor M).map f.op

@[simp]
theorem simplicialPullback_id (M : ModuleCat.{0} R) (K : SSet.{0}) :
    simplicialPullback M (𝟙 K) = 𝟙 (Basic.simplicialCochains K M) :=
  (simplicialCochainsFunctor M).map_id (op K)

@[simp]
theorem simplicialPullback_comp (M : ModuleCat.{0} R)
    {K L N : SSet.{0}} (f : K ⟶ L) (g : L ⟶ N) :
    simplicialPullback M (f ≫ g) = simplicialPullback M g ≫ simplicialPullback M f :=
  (simplicialCochainsFunctor M).map_comp g.op f.op

/-- Singular cochains as a contravariant functor on topological spaces. -/
def singularCochainsFunctor (M : ModuleCat.{0} R) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  TopCat.toSSet.op ⋙ simplicialCochainsFunctor M

/-- Pullback of singular cochains along a continuous map. -/
def singularPullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Basic.singularCochains M Y ⟶ Basic.singularCochains M X :=
  (singularCochainsFunctor M).map f.op

@[simp]
theorem singularPullback_id (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    singularPullback M (𝟙 X) = 𝟙 (Basic.singularCochains M X) :=
  (singularCochainsFunctor M).map_id (op X)

@[simp]
theorem singularPullback_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularPullback M (f ≫ g) = singularPullback M g ≫ singularPullback M f :=
  (singularCochainsFunctor M).map_comp g.op f.op

/-- Pullback of singular cohomology classes along a continuous map. -/
def singularCohomologyPullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) : Basic.singularCohomology M Y n ⟶ Basic.singularCohomology M X n :=
  HomologicalComplex.homologyMap (singularPullback M f) n

@[simp]
theorem singularCohomologyPullback_id (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCohomologyPullback M (𝟙 X) n = 𝟙 (Basic.singularCohomology M X n) := by
  simp only [singularCohomologyPullback, singularPullback_id,
    HomologicalComplex.homologyMap_id]

@[simp]
theorem singularCohomologyPullback_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    singularCohomologyPullback M (f ≫ g) n =
      singularCohomologyPullback M g n ≫ singularCohomologyPullback M f n := by
  simp only [singularCohomologyPullback, singularPullback_comp,
    HomologicalComplex.homologyMap_comp]

/-- Singular cohomology in a fixed degree as a contravariant functor. -/
def singularCohomologyFunctor (M : ModuleCat.{0} R) (n : ℕ) :
    TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} R :=
  singularCochainsFunctor M ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- Changing coefficients commutes with pullback along a continuous map. -/
theorem coefficientCochainMap_naturality {M N : ModuleCat.{0} R} (u : M ⟶ N)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularPullback M f ≫ Coefficients.coefficientCochainMap u X =
      Coefficients.coefficientCochainMap u Y ≫ singularPullback N f := by
  let F := AlgebraicTopology.singularChainComplexFunctor ((ModuleCat.{0} R)ᵒᵖ)
  let U := HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)
  change U.map (((F.obj (op M)).map f).op) ≫ U.map (((F.map u.op).app X).op) =
    U.map (((F.map u.op).app Y).op) ≫ U.map (((F.obj (op N)).map f).op)
  rw [← U.map_comp, ← U.map_comp]
  exact congrArg U.map (congrArg Quiver.Hom.op ((F.map u.op).naturality f).symm)

/-- Coefficient maps commute with pullback on singular cohomology. -/
theorem coefficientMap_naturality {M N : ModuleCat.{0} R} (u : M ⟶ N)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyPullback M f n ≫ Coefficients.coefficientMap u X n =
      Coefficients.coefficientMap u Y n ≫ singularCohomologyPullback N f n := by
  simp only [singularCohomologyPullback, Coefficients.coefficientMap,
    ← HomologicalComplex.homologyMap_comp]
  rw [coefficientCochainMap_naturality]

end

end OAI.AlgebraicTopology.Cohomology.Singular.Functor
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Functor"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality -/

/-! # Representatives Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

noncomputable section

/-!
# Naturality of cocycle representatives

Cochain maps carry cocycles and coboundaries to cocycles and coboundaries.
The resulting representative map is compatible with mathlib's categorical
homology map. We specialize this to the genuine singular pullback and
coefficient maps, without defining another cohomology theory.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]
variable {K L T : CochainComplex (ModuleCat.{0} R) ℕ}

/-- Restriction of a cochain map to the kernel of the outgoing differential. -/
def cochainCocycleMap (f : K ⟶ L) (n : ℕ) :
    Representatives.cochainCocycles K n →ₗ[R] Representatives.cochainCocycles L n :=
  ((f.f n).hom.comp (Representatives.cochainCocycles K n).subtype).codRestrict _ fun x => by
    rw [Representatives.mem_cochainCocycles_iff]
    change (L.d n (n + 1)) ((f.f n) (x : K.X n)) = 0
    have h := ConcreteCategory.congr_hom (f.comm n (n + 1)) (x : K.X n)
    have hx := (Representatives.mem_cochainCocycles_iff K n (x : K.X n)).mp x.property
    simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h

@[simp]
theorem cochainCocycleMap_val (f : K ⟶ L) (n : ℕ) (x : Representatives.cochainCocycles K n) :
    (cochainCocycleMap f n x : L.X n) = (f.f n) (x : K.X n) := rfl

@[simp]
theorem cochainCocycleMap_id (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    cochainCocycleMap (𝟙 K) n = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem cochainCocycleMap_comp (f : K ⟶ L) (g : L ⟶ T) (n : ℕ) :
    cochainCocycleMap (f ≫ g) n = (cochainCocycleMap g n).comp (cochainCocycleMap f n) := by
  ext x
  rfl

/-- The concrete cocycle map agrees with the categorical map on cycles. -/
theorem cochainCocycleMap_eq_cyclesMap (f : K ⟶ L) (n : ℕ)
    (x : Representatives.cochainCocycles K n) :
    (L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x) =
      (HomologicalComplex.cyclesMap f n) ((K.sc n).moduleCatCyclesIso.inv x) := by
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have hL := ConcreteCategory.congr_hom ((L.sc n).moduleCatCyclesIso_inv_iCycles)
    (cochainCocycleMap f n x)
  have hK := ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_iCycles) x
  have hf := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n)
    ((K.sc n).moduleCatCyclesIso.inv x)
  change (L.iCycles n) ((L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x)) =
    (L.iCycles n) ((HomologicalComplex.cyclesMap f n) ((K.sc n).moduleCatCyclesIso.inv x))
  change (L.iCycles n) ((L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x)) =
    (f.f n) (x : K.X n) at hL
  change (K.iCycles n) ((K.sc n).moduleCatCyclesIso.inv x) = (x : K.X n) at hK
  change (L.iCycles n) ((HomologicalComplex.cyclesMap f n)
    ((K.sc n).moduleCatCyclesIso.inv x)) =
      (f.f n) ((K.iCycles n) ((K.sc n).moduleCatCyclesIso.inv x)) at hf
  rw [hK] at hf
  exact hL.trans hf.symm

/-- Passing to a cohomology class commutes with every cochain map. -/
theorem cochainClass_naturality (f : K ⟶ L) (n : ℕ) (x : Representatives.cochainCocycles K n) :
    (HomologicalComplex.homologyMap f n) (Representatives.cochainClass K n x) =
      Representatives.cochainClass L n (cochainCocycleMap f n x) := by
  rw [Representatives.cochainClass_eq_homologyπ, Representatives.cochainClass_eq_homologyπ,
    cochainCocycleMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    ((K.sc n).moduleCatCyclesIso.inv x)

/-- A cochain map carries the coboundary of a cochain to the coboundary of its image. -/
theorem cochainCocycleMap_boundary (f : K ⟶ L) (n : ℕ) (x : (K.sc n).X₁) :
    cochainCocycleMap f n (Representatives.cochainBoundaryMap K n x) =
      Representatives.cochainBoundaryMap L n ((f.f ((ComplexShape.up ℕ).prev n)) x) := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom
    (f.comm ((ComplexShape.up ℕ).prev n) n) x).symm

/-- Pullback on singular cocycle representatives. -/
abbrev singularCocyclePullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) : Representatives.singularCocycles M Y n →ₗ[R] Representatives.singularCocycles M X n :=
  cochainCocycleMap (Functor.singularPullback M f) n

/-- A pulled-back class is represented by the pulled-back cocycle. -/
theorem singularCohomologyPullback_class (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (x : Representatives.singularCocycles M Y n) :
    (Functor.singularCohomologyPullback M f n) (Representatives.singularClass M Y n x) =
      Representatives.singularClass M X n (singularCocyclePullback M f n x) :=
  cochainClass_naturality (Functor.singularPullback M f) n x

/-- A coefficient map on singular cocycle representatives. -/
abbrev coefficientCocycleMap {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (X : TopCat.{0}) (n : ℕ) : Representatives.singularCocycles M X n →ₗ[R] Representatives.singularCocycles N X n :=
  cochainCocycleMap (Coefficients.coefficientCochainMap f X) n

/-- Changing coefficients of a class changes coefficients of its representative. -/
theorem coefficientMap_class {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (X : TopCat.{0}) (n : ℕ) (x : Representatives.singularCocycles M X n) :
    (Coefficients.coefficientMap f X n) (Representatives.singularClass M X n x) =
      Representatives.singularClass N X n (coefficientCocycleMap f X n x) :=
  cochainClass_naturality (Coefficients.coefficientCochainMap f X) n x

end

end OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives -/

/-! # Good Shift Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions

noncomputable section

/-! The canonical good shift sends an actual cocycle to the same cohomology class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (k n : ℕ)

def cochainRestrictedCocycle (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (K.restriction (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n :=
  ⟨c.val, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (k+n) c.val).mp c.property⟩

def cochainGoodShiftCocycle (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n
    (cochainRestrictedCocycle K k n c)

theorem cochainGoodShiftCocycle_cycles (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).sc n).moduleCatCyclesIso.inv
        (cochainGoodShiftCocycle K k n c) =
      GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap K k n ((K.sc (k+n)).moduleCatCyclesIso.inv c) := by
  let T := K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
  apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
  have hT := ConcreteCategory.congr_hom ((T.sc n).moduleCatCyclesIso_inv_iCycles)
    (cochainGoodShiftCocycle K k n c)
  have hK := ConcreteCategory.congr_hom ((K.sc (k+n)).moduleCatCyclesIso_inv_iCycles) c
  have hs := ConcreteCategory.congr_hom (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap_inclusion K k n)
    ((K.sc (k+n)).moduleCatCyclesIso.inv c)
  change T.iCycles n ((T.sc n).moduleCatCyclesIso.inv (cochainGoodShiftCocycle K k n c)) =
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n c.val at hT
  change K.iCycles (k+n) ((K.sc (k+n)).moduleCatCyclesIso.inv c) = c.val at hK
  change T.iCycles n (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap K k n ((K.sc (k+n)).moduleCatCyclesIso.inv c)) =
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n
      (K.iCycles (k+n) ((K.sc (k+n)).moduleCatCyclesIso.inv c)) at hs
  rw [hK] at hs
  exact hT.trans hs.symm

theorem cochainGoodShiftHomologyIso_class (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso K k n).hom
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n (cochainGoodShiftCocycle K k n c)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (k+n) c := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ, cochainGoodShiftCocycle_cycles, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  exact ConcreteCategory.congr_hom (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap_homologyπ K k n)
    ((K.sc (k+n)).moduleCatCyclesIso.inv c)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter -/

/-! # Normal Pair Recenter -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

/-!
# Genuine local pairs for embedded immersions

A local immersion chart describes the image of one source chart. The embedding
hypothesis supplies an ambient open set whose intersection with the full image
comes entirely from that source chart. After shrinking to a product of balls,
the resulting homeomorphism therefore identifies the actual full image with
the zero normal slice.
-/

open Set Filter
open scoped _root_.Topology _root_.Manifold ContDiff

section TopologicalPairs

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- An actual ambient coordinate neighborhood, with the full image of `f`
identified with the zero normal slice. The fields are constructed below from
a genuine manifold immersion and a topological embedding. -/
structure ImmersionNormalPair (f : M → N) (x : M) where
  radius : ℝ
  radius_pos : 0 < radius
  ambientChart : OpenPartialHomeomorph N (E × F)
  product_subset_target :
    Metric.ball (0 : E) radius ×ˢ Metric.ball (0 : F) radius ⊆ ambientChart.target
  point_mem_source : f x ∈ ambientChart.source
  point_coordinates : ambientChart (f x) = (0, 0)
  range_iff : ∀ y ∈ ambientChart.symm ''
      (Metric.ball (0 : E) radius ×ˢ Metric.ball (0 : F) radius),
    y ∈ Set.range f ↔ (ambientChart y).2 = 0

namespace ImmersionNormalPair

variable {E F} {f : M → N} {x : M} (P : ImmersionNormalPair E F f x)

omit [TopologicalSpace M]

/-- The actual ambient open neighborhood, obtained by pulling back the balls. -/
def neighborhood : Set N :=
  P.ambientChart.symm ''
    (Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius)

theorem isOpen_neighborhood : IsOpen P.neighborhood :=
  P.ambientChart.isOpen_image_symm_of_subset_target
    (Metric.isOpen_ball.prod Metric.isOpen_ball) P.product_subset_target

theorem neighborhood_subset_source : P.neighborhood ⊆ P.ambientChart.source := by
  rintro y ⟨z, hz, rfl⟩
  exact P.ambientChart.map_target (P.product_subset_target hz)

theorem point_mem_neighborhood : f x ∈ P.neighborhood := by
  refine ⟨(0, 0), ⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩, ?_⟩
  rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]

/-- The genuine homeomorphism onto the product of the two open balls. -/
def homeomorph : P.neighborhood ≃ₜ
    (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius) :=
  (P.ambientChart.homeomorphOfImageSubsetSource P.neighborhood_subset_source
    (P.ambientChart.image_symm_image_of_subset_target P.product_subset_target)).trans
      (Homeomorph.Set.prod _ _)

@[simp]
theorem homeomorph_apply_val (y : P.neighborhood) :
    ((P.homeomorph y).1.val, (P.homeomorph y).2.val) = P.ambientChart y.val := rfl

theorem homeomorph_point :
    P.homeomorph ⟨f x, P.point_mem_neighborhood⟩ =
      (⟨0, Metric.mem_ball_self P.radius_pos⟩, ⟨0, Metric.mem_ball_self P.radius_pos⟩) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst P.point_coordinates
  · exact congrArg Prod.snd P.point_coordinates

/-- This equivalence uses the full range of `f`, not a restricted source image. -/
theorem mem_range_iff (y : P.neighborhood) :
    y.val ∈ Set.range f ↔ (P.homeomorph y).2.val = 0 :=
  P.range_iff y.val y.property

theorem mem_complement_iff (y : P.neighborhood) :
    y.val ∉ Set.range f ↔ (P.homeomorph y).2.val ≠ 0 :=
  not_congr (P.mem_range_iff y)

/-- Restriction to the subspace in the pair is an actual homeomorphism. -/
def supportHomeomorph : {y : P.neighborhood // y.val ∈ Set.range f} ≃ₜ
    {z : Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius // z.2.val = 0} :=
  P.homeomorph.subtype P.mem_range_iff

/-- The complements in the local pair are also homeomorphic. -/
def complementHomeomorph : {y : P.neighborhood // y.val ∉ Set.range f} ≃ₜ
    {z : Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius // z.2.val ≠ 0} :=
  P.homeomorph.subtype P.mem_complement_iff

/-- The entire image in the ambient neighborhood is precisely the normal
zero plane in the coordinate product. -/
theorem ambientChart_image_support :
    P.ambientChart '' (P.neighborhood ∩ Set.range f) =
      Metric.ball (0 : E) P.radius ×ˢ ({0} : Set F) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyf⟩, rfl⟩
    exact ⟨(P.homeomorph ⟨y, hy⟩).1.property, (P.range_iff y hy).mp hyf⟩
  · rintro ⟨hz1, hz2⟩
    have hprod : z ∈ Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius := by
      refine ⟨hz1, ?_⟩
      rw [show z.2 = 0 from hz2]
      exact Metric.mem_ball_self P.radius_pos
    have ht := P.product_subset_target hprod
    refine ⟨P.ambientChart.symm z, ⟨⟨z, hprod, rfl⟩, ?_⟩, P.ambientChart.right_inv ht⟩
    apply (P.range_iff _ ⟨z, hprod, rfl⟩).mpr
    rw [P.ambientChart.right_inv ht]
    exact hz2

/-- Shrinking both coordinate radii preserves the exact full-image pair. -/
def restrictRadius (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    ImmersionNormalPair E F f x where
  radius := r
  radius_pos := hr
  ambientChart := P.ambientChart
  product_subset_target := fun _ hz => P.product_subset_target
    ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩
  point_mem_source := P.point_mem_source
  point_coordinates := P.point_coordinates
  range_iff := fun y hy => P.range_iff y (by
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩, rfl⟩)

@[simp]
theorem restrictRadius_ambientChart (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    (P.restrictRadius r hr hle).ambientChart = P.ambientChart := rfl

theorem restrictRadius_neighborhood_subset (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    (P.restrictRadius r hr hle).neighborhood ⊆ P.neighborhood := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩, rfl⟩

/-- Such product neighborhoods can be chosen inside every ambient neighborhood
of the base point, while retaining the same actual coordinate map. -/
theorem exists_restrictRadius_subset (U : Set N) (hU : U ∈ 𝓝 (f x)) :
    ∃ (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius),
      (P.restrictRadius r hr hle).neighborhood ⊆ U := by
  have h0t : (0, 0) ∈ P.ambientChart.target := by
    rw [← P.point_coordinates]
    exact P.ambientChart.map_source P.point_mem_source
  have hinv : P.ambientChart.symm (0, 0) = f x := by
    rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]
  have hpre : P.ambientChart.symm ⁻¹' U ∈ 𝓝 (0, 0) :=
    (P.ambientChart.continuousAt_symm h0t).preimage_mem_nhds (by rwa [hinv])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min ε P.radius, lt_min hε P.radius_pos, min_le_right _ _, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  apply hball
  apply Metric.ball_subset_ball (min_le_left ε P.radius)
  change z ∈ Metric.ball (0 : E) (min ε P.radius) ×ˢ
    Metric.ball (0 : F) (min ε P.radius) at hz
  simpa only [ball_prod_same] using hz

/-- Cofinality stated directly in terms of genuine normal pairs. -/
theorem exists_subpair (U : Set N) (hU : U ∈ 𝓝 (f x)) :
    ∃ Q : ImmersionNormalPair E F f x,
      Q.ambientChart = P.ambientChart ∧ Q.neighborhood ⊆ U := by
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset U hU
  exact ⟨P.restrictRadius r hr hle, rfl, hsub⟩

end ImmersionNormalPair

variable {E F} {f : M → N} {x : M}

/-- The embedding hypothesis excludes all other source points from a suitable
ambient neighborhood. The local normal form then describes the full image. -/
theorem exists_normalPairRadius (hf : Topology.IsEmbedding f)
    (u : OpenPartialHomeomorph M E) (v : OpenPartialHomeomorph N (E × F))
    (hx : x ∈ u.source) (hmap : u.source ⊆ f ⁻¹' v.source)
    (hnormal : ∀ y ∈ u.source, v (f y) = (u y, 0)) (hcenter : u x = 0) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ v.target ∧
      ∀ y ∈ v.symm '' (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r),
        y ∈ Set.range f ↔ (v y).2 = 0 := by
  obtain ⟨O, hO, hpre⟩ := hf.isInducing.isOpen_iff.mp u.open_source
  have hfxO : f x ∈ O := by
    change x ∈ f ⁻¹' O
    rw [hpre]
    exact hx
  have hzero : v (f x) = (0, 0) := by simpa only [hcenter] using hnormal x hx
  let V : Set (E × F) := v '' (v.source ∩ O) ∩ Prod.fst ⁻¹' u.target
  have hV : IsOpen V :=
    (v.isOpen_image_source_inter hO).inter (u.open_target.preimage continuous_fst)
  have h0 : (0, 0) ∈ V := by
    refine ⟨⟨f x, ⟨hmap hx, hfxO⟩, hzero⟩, ?_⟩
    change (0 : E) ∈ u.target
    simpa only [hcenter] using u.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ V := by
    simpa only [ball_prod_same] using hball
  have htarget : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ v.target := by
    intro z hz
    obtain ⟨w, hw, he⟩ := (hprod hz).1
    exact he ▸ v.map_source hw.1
  refine ⟨r, hr, htarget, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzt : z ∈ v.target := htarget hz
  have hys : v.symm z ∈ v.source := v.map_target hzt
  have hright : v (v.symm z) = z := v.right_inv hzt
  have hyO : v.symm z ∈ O := by
    obtain ⟨w, hw, he⟩ := (hprod hz).1
    rw [← he, v.left_inv hw.1]
    exact hw.2
  have huT : z.1 ∈ u.target := (hprod hz).2
  constructor
  · rintro ⟨a, ha⟩
    have haU : a ∈ u.source := by
      rw [← hpre]
      change f a ∈ O
      rwa [ha]
    rw [← ha, hnormal a haU]
  · intro hzero'
    refine ⟨u.symm z.1, ?_⟩
    have haU : u.symm z.1 ∈ u.source := u.map_target huT
    apply v.injOn (hmap haU) hys
    rw [hnormal _ haU, u.right_inv huT, hright]
    apply Prod.ext
    · rfl
    · rw [hright] at hzero'
      exact hzero'.symm

/-- Package the radius just proved, without assuming any full-image claim. -/
def normalPairOfCharts (hf : Topology.IsEmbedding f)
    (u : OpenPartialHomeomorph M E) (v : OpenPartialHomeomorph N (E × F))
    (hx : x ∈ u.source) (hmap : u.source ⊆ f ⁻¹' v.source)
    (hnormal : ∀ y ∈ u.source, v (f y) = (u y, 0)) (hcenter : u x = 0) :
    ImmersionNormalPair E F f x :=
  let h := exists_normalPairRadius hf u v hx hmap hnormal hcenter
  { radius := Classical.choose h
    radius_pos := (Classical.choose_spec h).1
    ambientChart := v
    product_subset_target := (Classical.choose_spec h).2.1
    point_mem_source := hmap hx
    point_coordinates := by simpa only [hcenter] using hnormal x hx
    range_iff := (Classical.choose_spec h).2.2 }

end TopologicalPairs

variable {𝕜 E G C M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- The source chart supplied by the genuine immersion, centered at `x`. -/
def immersionSourceCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    OpenPartialHomeomorph M E :=
  h.domChart.transHomeomorph (Homeomorph.subRight (h.domChart x))

/-- The genuine immersion chart split into tangential and normal coordinates,
and centered at `(x,0)` in those coordinates. -/
def immersionNormalCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    OpenPartialHomeomorph N (E × C) :=
  h.codChart.transHomeomorph
    (h.equiv.symm.toHomeomorph.trans
      ((Homeomorph.subRight (h.domChart x)).prodCongr (Homeomorph.refl C)))

@[simp]
theorem immersionSourceCoordinates_source
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    (immersionSourceCoordinates h).source = h.domChart.source := rfl

@[simp]
theorem immersionNormalCoordinates_source
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    (immersionNormalCoordinates h).source = h.codChart.source := rfl

@[simp]
theorem immersionSourceCoordinates_center
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    immersionSourceCoordinates h x = 0 := by
  change h.domChart x - h.domChart x = 0
  exact sub_self _

/-- Removing the trivial corner models from the genuine normal-form equation. -/
theorem immersion_codChart_apply
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    {y : M} (hy : y ∈ h.domChart.source) :
    h.codChart (f y) = h.equiv (h.domChart y, 0) := by
  have ht : h.domChart y ∈ (h.domChart.extend 𝓘(𝕜, E)).target := by
    rw [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe]
    exact ⟨h.domChart y, h.domChart.map_source hy, rfl⟩
  have he := h.writtenInCharts ht
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
    id_eq, h.domChart.left_inv hy] using he

/-- In the centered coordinates, the actual immersion is the zero section. -/
theorem immersionNormalCoordinates_apply
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    {y : M} (hy : y ∈ (immersionSourceCoordinates h).source) :
    immersionNormalCoordinates h (f y) = (immersionSourceCoordinates h y, 0) := by
  change ((h.equiv.symm (h.codChart (f y))).1 - h.domChart x,
      (h.equiv.symm (h.codChart (f y))).2) = (h.domChart y - h.domChart x, 0)
  rw [immersion_codChart_apply h hy, h.equiv.symm_apply_apply]

/-- A genuine immersion which is a topological embedding has an actual local
normal pair for its full image. No additional normal form is assumed. -/
def normalPairOfImmersion
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) : ImmersionNormalPair E C f x :=
  normalPairOfCharts hf (immersionSourceCoordinates h) (immersionNormalCoordinates h)
    h.mem_domChart_source h.source_subset_preimage_source
    (fun _ hy => immersionNormalCoordinates_apply h hy) (immersionSourceCoordinates_center h)

@[simp]
theorem normalPairOfImmersion_ambientChart
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) :
    (normalPairOfImmersion h hf).ambientChart = immersionNormalCoordinates h := rfl

/-- The same local pair, using the complement proved to exist by mathlib's
standard `IsImmersionAt` proposition. -/
def immersionNormalPair
    (h : Manifold.IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) : ImmersionNormalPair E h.complement f x :=
  normalPairOfImmersion h.isImmersionAtOfComplement_complement hf

end AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

namespace AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair

/-!
# Recentering genuine normal pairs

At another point of the image in a verified normal-pair neighborhood, translate
only the tangential coordinate. A sufficiently small positive product ball
stays inside the original verified neighborhood and any requested neighborhood
of the new point. The resulting pair therefore still describes the full image.
-/

open Set Filter
open scoped _root_.Topology

variable {M N E F : Type*} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ImmersionNormalPair E F f x)

/-- Translate only the tangential coordinate to recenter the actual ambient chart. -/
def recenterChart (z : M) : OpenPartialHomeomorph N (E × F) :=
  P.ambientChart.transHomeomorph
    ((Homeomorph.subRight (P.ambientChart (f z)).1).prodCongr (Homeomorph.refl F))

@[simp]
theorem recenterChart_source (z : M) :
    (P.recenterChart z).source = P.ambientChart.source := rfl

@[simp]
theorem recenterChart_apply (z : M) (y : N) :
    P.recenterChart z y =
      ((P.ambientChart y).1 - (P.ambientChart (f z)).1, (P.ambientChart y).2) := rfl

@[simp]
theorem recenterChart_symm_apply (z : M) (w : E × F) :
    (P.recenterChart z).symm w =
      P.ambientChart.symm (w.1 + (P.ambientChart (f z)).1, w.2) := rfl

/-- In particular, normal coordinates are unchanged everywhere, not merely at the center. -/
@[simp]
theorem recenterChart_normalCoordinate (z : M) (y : N) :
    (P.recenterChart z y).2 = (P.ambientChart y).2 := rfl

theorem recenterChart_point_mem_source (z : M) (hz : f z ∈ P.neighborhood) :
    f z ∈ (P.recenterChart z).source :=
  P.neighborhood_subset_source hz

/-- The full-image property proves that the new image point has zero normal coordinate. -/
@[simp]
theorem recenterChart_point (z : M) (hz : f z ∈ P.neighborhood) :
    P.recenterChart z (f z) = (0, 0) := by
  have hn : (P.ambientChart (f z)).2 = 0 :=
    (P.range_iff (f z) hz).mp ⟨z, rfl⟩
  simp only [recenterChart_apply, sub_self, hn]

theorem recenterChart_zero_mem_target (z : M) (hz : f z ∈ P.neighborhood) :
    (0, 0) ∈ (P.recenterChart z).target := by
  rw [← P.recenterChart_point z hz]
  exact (P.recenterChart z).map_source (P.recenterChart_point_mem_source z hz)

@[simp]
theorem recenterChart_symm_zero (z : M) (hz : f z ∈ P.neighborhood) :
    (P.recenterChart z).symm (0, 0) = f z := by
  rw [← P.recenterChart_point z hz,
    (P.recenterChart z).left_inv (P.recenterChart_point_mem_source z hz)]

/-- A positive product ball in the recentered chart can be chosen inside the
original verified pair and any requested neighborhood of the new point. -/
theorem exists_recenterRadius (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ (P.recenterChart z).target ∧
      (P.recenterChart z).symm ''
        (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r) ⊆ P.neighborhood ∩ U := by
  have ht := P.recenterChart_zero_mem_target z hz
  have hn : P.neighborhood ∩ U ∈ 𝓝 (f z) :=
    inter_mem (P.isOpen_neighborhood.mem_nhds hz) hU
  have hp : (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) ∈ 𝓝 (0, 0) :=
    ((P.recenterChart z).continuousAt_symm ht).preimage_mem_nhds
      (by rwa [P.recenterChart_symm_zero z hz])
  have hv : (P.recenterChart z).target ∩
      (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) ∈ 𝓝 (0, 0) :=
    inter_mem ((P.recenterChart z).open_target.mem_nhds ht) hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hv
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆
      (P.recenterChart z).target ∩
        (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) := by
    simpa only [ball_prod_same] using hball
  refine ⟨r, hr, fun w hw => (hprod hw).1, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  exact (hprod hw).2

/-- A genuine normal pair centered at any image point in the original pair,
with its entire verified neighborhood contained in the requested overlap. -/
def recenterWithin (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) : ImmersionNormalPair E F f z :=
  let h := P.exists_recenterRadius z hz U hU
  { radius := Classical.choose h
    radius_pos := (Classical.choose_spec h).1
    ambientChart := P.recenterChart z
    product_subset_target := (Classical.choose_spec h).2.1
    point_mem_source := P.recenterChart_point_mem_source z hz
    point_coordinates := P.recenterChart_point z hz
    range_iff := fun y hy => P.range_iff y ((Classical.choose_spec h).2.2 hy).1 }

@[simp]
theorem recenterWithin_ambientChart (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).ambientChart = P.recenterChart z := rfl

@[simp]
theorem recenterWithin_ambientChart_apply (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (y : N) :
    (P.recenterWithin z hz U hU).ambientChart y =
      ((P.ambientChart y).1 - (P.ambientChart (f z)).1, (P.ambientChart y).2) := rfl

@[simp]
theorem recenterWithin_normalCoordinate (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (y : N) :
    ((P.recenterWithin z hz U hU).ambientChart y).2 = (P.ambientChart y).2 := rfl

/-- The new normal slice is the original normal fiber over the new tangential coordinate. -/
@[simp]
theorem recenterWithin_normalSlice (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (v : F) :
    (P.recenterWithin z hz U hU).ambientChart.symm (0, v) =
      P.ambientChart.symm ((P.ambientChart (f z)).1, v) := by
  simp only [recenterWithin_ambientChart, recenterChart_symm_apply, zero_add]

theorem recenterWithin_neighborhood_subset (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).neighborhood ⊆ P.neighborhood ∩ U :=
  (Classical.choose_spec (P.exists_recenterRadius z hz U hU)).2.2

/-- An existence version records both the exact translated chart and the overlap containment. -/
theorem exists_recentered_subpair (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    ∃ Q : ImmersionNormalPair E F f z,
      Q.ambientChart = P.recenterChart z ∧ Q.neighborhood ⊆ P.neighborhood ∩ U :=
  ⟨P.recenterWithin z hz U hU, rfl, P.recenterWithin_neighborhood_subset z hz U hU⟩

end AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair

end

end OAI
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology -/

/-! # Local Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles

noncomputable section

section

/-!
# Relative singular chains and local homology

These are genuine integral singular chains. For a subspace `A ⊆ X`, relative
chains are the cokernel of the singular chain map of the continuous inclusion.
In particular, local homology at `x` means `Hₙ(X, X \ {x}; ℤ)`.

The short exact sequence below supplies the chain-level starting point for the
long exact sequence of a pair. It does not assert excision, a local orientation
theorem, a fundamental class, or Poincaré duality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

/-- The ordinary integral singular chain functor already constructed by mathlib. -/
abbrev integralSingularChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Ordinary integral singular chains, with the alternating face differential. -/
abbrev integralSingularChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSingularChainFunctor.obj X

/-- Inclusion of a subspace with its induced topology. -/
def subspaceInclusion (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance subspaceInclusion_mono (X : TopCat.{0}) (A : Set X) :
    Mono (subspaceInclusion X A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The actual chain map induced by the inclusion `A ⊆ X`. -/
abbrev subspaceChainInclusion (X : TopCat.{0}) (A : Set X) :
    integralSingularChains (TopCat.of A) ⟶ integralSingularChains X :=
  integralSingularChainFunctor.map (subspaceInclusion X A)

instance subspaceChainInclusion_mono (X : TopCat.{0}) (A : Set X) :
    Mono (subspaceChainInclusion X A) := by
  dsimp [subspaceChainInclusion]
  infer_instance

/-- Relative integral singular chains, the quotient of `Cₙ(X)` by `Cₙ(A)`. -/
abbrev relativeSingularChains (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (subspaceChainInclusion X A)

/-- Projection from absolute to relative singular chains. -/
abbrev relativeChainProjection (X : TopCat.{0}) (A : Set X) :
    integralSingularChains X ⟶ relativeSingularChains X A :=
  cokernel.π (subspaceChainInclusion X A)

@[reassoc (attr := simp)]
theorem subspaceChainInclusion_projection (X : TopCat.{0}) (A : Set X) :
    subspaceChainInclusion X A ≫ relativeChainProjection X A = 0 :=
  cokernel.condition _

/-- The genuine singular-chain short complex for a pair of spaces. -/
def relativeChainSequence (X : TopCat.{0}) (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (subspaceChainInclusion X A) (relativeChainProjection X A)
    (subspaceChainInclusion_projection X A)

/-- The chain sequence `0 → C(A) → C(X) → C(X,A) → 0` is short exact. -/
theorem relativeChainSequence_shortExact (X : TopCat.{0}) (A : Set X) :
    (relativeChainSequence X A).ShortExact := by
  change (ShortComplex.mk (subspaceChainInclusion X A)
    (cokernel.π (subspaceChainInclusion X A)) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact (subspaceChainInclusion X A) }

/-- The relative-chain sequence is also short exact in every individual degree. -/
theorem relativeChainSequence_degreewiseShortExact (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ((relativeChainSequence X A).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relativeChainSequence_shortExact X A) n

/-- Integral relative singular homology. -/
abbrev relativeSingularHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} ℤ :=
  (relativeSingularChains X A).homology n

/-- Local integral singular homology at a point, with the punctured subspace. -/
abbrev localSingularHomology (X : TopCat.{0}) (x : X) (n : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularHomology X ({x}ᶜ : Set X) n

/-- A continuous map restricting to the indicated subspaces. -/
def subspaceMap {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a, h a.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc]
theorem subspaceMap_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    subspaceMap f h ≫ subspaceInclusion Y B = subspaceInclusion X A ≫ f := by
  rfl

/-- Functoriality of actual relative singular chains for a map of pairs. -/
def relativeSingularChainsMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeSingularChains X A ⟶ relativeSingularChains Y B :=
  cokernel.map (subspaceChainInclusion X A) (subspaceChainInclusion Y B)
    (integralSingularChainFunctor.map (subspaceMap f h))
    (integralSingularChainFunctor.map f) (by
      rw [← Functor.map_comp, ← Functor.map_comp, subspaceMap_inclusion])

@[reassoc (attr := simp)]
theorem relativeChainProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    relativeChainProjection X A ≫ relativeSingularChainsMap f h =
      integralSingularChainFunctor.map f ≫ relativeChainProjection Y B := by
  exact cokernel.π_desc _ _ _

/-- The induced homomorphism of integral relative singular homology groups. -/
abbrev relativeSingularHomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularHomology X A n ⟶ relativeSingularHomology Y B n :=
  HomologicalComplex.homologyMap (relativeSingularChainsMap f h) n

/-- Homeomorphisms of pairs induce isomorphisms of the relative chain complexes. -/
def relativeSingularChainsIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    relativeSingularChains X A ≅ relativeSingularChains Y B := by
  let f := (TopCat.isoOfHomeo e).hom
  have hm : Set.MapsTo f A B := fun x hx ↦ (h x).mp hx
  have hs : subspaceMap f hm = (TopCat.isoOfHomeo (e.subtype h)).hom := by
    ext a
    rfl
  letI : IsIso (subspaceMap f hm) := by
    rw [hs]
    infer_instance
  letI : IsIso (relativeSingularChainsMap f hm) := by
    dsimp [relativeSingularChainsMap]
    infer_instance
  exact asIso (relativeSingularChainsMap f hm)

/-- Homeomorphism invariance of integral relative singular homology. -/
def relativeSingularHomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    relativeSingularHomology X A n ≅ relativeSingularHomology Y B n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (relativeSingularChainsIso e h)

/-- Local homology is transported by an actual homeomorphism. -/
def localSingularHomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    localSingularHomology X x n ≅ localSingularHomology Y (e x) n :=
  relativeSingularHomologyIso e (by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff]) n

end

/-!
# Functoriality of the actual relative singular-chain quotient

The maps here are the existing cokernel maps induced by continuous maps of
pairs. Their identity and composition laws follow from the actual relative
chain projections, which are epimorphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The identity map of a pair induces the identity on relative chains. -/
@[simp]
theorem relativeSingularChainsMap_id (X : TopCat.{0}) (A : Set X) :
    relativeSingularChainsMap (𝟙 X) (A := A) (B := A) (fun _ hx => hx) =
      𝟙 (relativeSingularChains X A) := by
  apply (cancel_epi (relativeChainProjection X A)).mp
  rw [relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

/-- Composition of maps of pairs gives composition of the actual relative
singular-chain maps. -/
@[reassoc]
theorem relativeSingularChainsMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeSingularChainsMap f hf ≫ relativeSingularChainsMap g hg =
      relativeSingularChainsMap (f ≫ g) (fun _ hx => hg (hf hx)) := by
  apply (cancel_epi (relativeChainProjection X A)).mp
  rw [← Category.assoc, relativeChainProjection_naturality, Category.assoc,
    relativeChainProjection_naturality, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    relativeChainProjection_naturality]

/-- The identity map of a pair acts identically on its actual relative homology. -/
@[simp]
theorem relativeSingularHomologyMap_id (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeSingularHomologyMap (𝟙 X) (A := A) (B := A) (fun _ hx => hx) n =
      𝟙 (relativeSingularHomology X A n) := by
  change HomologicalComplex.homologyMap _ n = _
  rw [relativeSingularChainsMap_id, HomologicalComplex.homologyMap_id]

/-- Relative homology maps compose as the underlying continuous maps of pairs. -/
@[reassoc]
theorem relativeSingularHomologyMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    relativeSingularHomologyMap f hf n ≫ relativeSingularHomologyMap g hg n =
      relativeSingularHomologyMap (f ≫ g) (fun _ hx => hg (hf hx)) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]

/-- The existing homeomorphism comparison is induced by its forward map of pairs. -/
@[simp]
theorem relativeSingularChainsIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    (relativeSingularChainsIso e h).hom =
      relativeSingularChainsMap (TopCat.isoOfHomeo e).hom (fun x hx => (h x).mp hx) := rfl

/-- The homeomorphism comparison on relative homology is the usual induced map. -/
@[simp]
theorem relativeSingularHomologyIso_hom {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    (relativeSingularHomologyIso e h n).hom =
      relativeSingularHomologyMap (TopCat.isoOfHomeo e).hom (fun x hx => (h x).mp hx) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent -/

/-! # Cokernel Homotopy Descent -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles

noncomputable section

/-!
# Descending actual homotopies through quotient complexes

For a short exact sequence of complexes, every ambient homotopy component
annihilating the subcomplex after projection has a unique quotient component.
The homotopy identity descends by the epimorphism from the ambient complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {V : Type u} [Category.{v} V] [Abelian V]
  {ι : Type w} {c : ComplexShape ι}
  (S T : ShortComplex (HomologicalComplex V c))
  (hS : S.ShortExact) {f g : S.X₂ ⟶ T.X₂}

/-- The uniquely descended component of an actual ambient homotopy. -/
def quotientHomotopyComponent (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.X₃.X a ⟶ T.X₃.X b :=
  (CokernelCofork.IsColimit.desc'
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).gIsCokernel
    (h.hom a b ≫ T.g.f b) (hz a b)).val

/-- Projection identifies the descended component with the ambient one. -/
@[reassoc]
theorem quotientHomotopyComponent_projection (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.g.f a ≫ quotientHomotopyComponent S T hS h hz a b =
      h.hom a b ≫ T.g.f b :=
  (CokernelCofork.IsColimit.desc'
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).gIsCokernel
    (h.hom a b ≫ T.g.f b) (hz a b)).property

/-- Descend an actual chain homotopy to quotient complexes, with proved
endpoint compatibility and vanishing on the source subcomplex. -/
def descendHomotopy {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) : Homotopy fQ gQ := by
  let K := quotientHomotopyComponent S T hS h hz
  have hK (a b : ι) : S.g.f a ≫ K a b = h.hom a b ≫ T.g.f b :=
    quotientHomotopyComponent_projection S T hS h hz a b
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    let : Epi (S.g.f a) :=
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).epi_g
    apply (cancel_epi (S.g.f a)).1
    rw [hK, h.zero a b hab, zero_comp, comp_zero]
  · intro n
    let : Epi (S.g.f n) :=
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n).epi_g
    apply (cancel_epi (S.g.f n)).1
    have hf' : S.g.f n ≫ fQ.f n = f.f n ≫ T.g.f n :=
      HomologicalComplex.congr_hom hf n
    have hg' : S.g.f n ≫ gQ.f n = g.f n ≫ T.g.f n :=
      HomologicalComplex.congr_hom hg n
    have hd : S.g.f n ≫ dNext n K = dNext n h.hom ≫ T.g.f n := by
      calc
        S.g.f n ≫ dNext n K = dNext n (fun a b => S.g.f a ≫ K a b) :=
          (dNext_comp_left S.g K n).symm
        _ = dNext n (fun a b => h.hom a b ≫ T.g.f b) := by simp only [hK]
        _ = dNext n h.hom ≫ T.g.f n := dNext_comp_right h.hom T.g n
    have hp : S.g.f n ≫ prevD n K = prevD n h.hom ≫ T.g.f n := by
      calc
        S.g.f n ≫ prevD n K = prevD n (fun a b => S.g.f a ≫ K a b) :=
          (prevD_comp_left S.g K n).symm
        _ = prevD n (fun a b => h.hom a b ≫ T.g.f b) := by simp only [hK]
        _ = prevD n h.hom ≫ T.g.f n := prevD_comp_right h.hom T.g n
    calc
      S.g.f n ≫ fQ.f n = f.f n ≫ T.g.f n := hf'
      _ = (dNext n h.hom + prevD n h.hom + g.f n) ≫ T.g.f n := by rw [h.comm n]
      _ = S.g.f n ≫ (dNext n K + prevD n K + gQ.f n) := by
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rw [hd, hp, hg']

/-- The descended homotopy uses the actual quotient components above. -/
theorem descendHomotopy_hom {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    (descendHomotopy S T hS hf hg h hz).hom a b =
      quotientHomotopyComponent S T hS h hz a b := rfl

/-- Projection compatibility for the fully assembled homotopy. -/
@[reassoc]
theorem descendHomotopy_projection {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.g.f a ≫ (descendHomotopy S T hS hf hg h hz).hom a b =
      h.hom a b ≫ T.g.f b :=
  quotientHomotopyComponent_projection S T hS h hz a b

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality -/

/-! # Homotopy Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality

noncomputable section

/-!
# Naturality of the actual singular chain homotopy

A commuting square of topological homotopies gives a commuting square of
the chain homotopy components constructed by mathlib. The proof follows the
actual singular simplicial homotopy and its alternating prism sum. In
particular it applies to restrictions of a homotopy to a subspace pair.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicTopology
open MonoidalCategory Functor.LaxMonoidal
open scoped Simplicial

universe v u w

section SimplicialObjects

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y X' Y' : SimplicialObject C}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The alternating prism construction respects a commuting square of
combinatorial simplicial homotopy components. -/
theorem combinatorialHomotopy_chain_naturality
    (H : SimplicialObject.Homotopy f g) (H' : SimplicialObject.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : ∀ (n : ℕ) (i : Fin (n + 1)),
      u.app (op ⦋n⦌) ≫ H.h i = H'.h i ≫ v.app (op ⦋n + 1⦌))
    (a b : ℕ) :
    ((alternatingFaceMapComplex C).map u).f a ≫ H.toChainHomotopy.hom a b =
      H'.toChainHomotopy.hom a b ≫ ((alternatingFaceMapComplex C).map v).f b := by
  change u.app (op ⦋a⦌) ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom H a b =
    SimplicialObject.Homotopy.ToChainHomotopy.hom H' a b ≫ v.app (op ⦋b⦌)
  by_cases hab : a + 1 = b
  · subst b
    simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, h]
  · simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hab,
      comp_zero, zero_comp]

end SimplicialObjects

section SimplicialSets

variable {X Y X' Y' : SSet.{w}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- A commuting square of geometric simplicial homotopies commutes with
each actual combinatorial prism simplex. -/
theorem simplicialHomotopy_component_naturality
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v)
    (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H.toSimplicialObjectHomotopy.h i =
      H'.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  change ((SSet.yonedaEquiv.symm (u.app (op ⦋n⦌) x) ▷ Δ[1]) ≫ H.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1 =
    v.app _ (((SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ H'.h).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1)
  rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, h]
  rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Naturality of the actual chain homotopy associated to a homotopy of
simplicial sets, with arbitrary coefficients in a preadditive category. -/
theorem simplicialHomotopy_chain_naturality
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ Δ[1]) ≫ H.h = H'.h ≫ v) (A : C) (a b : ℕ) :
    (SSet.chainComplexMap u A).f a ≫ (H.chainComplexMap A).hom a b =
      (H'.chainComplexMap A).hom a b ≫ (SSet.chainComplexMap v A).f b := by
  apply combinatorialHomotopy_chain_naturality
    (H.toSimplicialObjectHomotopy.whiskerRight ((sigmaConst (C := C)).obj A))
    (H'.toSimplicialObjectHomotopy.whiskerRight ((sigmaConst (C := C)).obj A))
  intro n i
  change ((sigmaConst (C := C)).obj A).map (u.app (op ⦋n⦌)) ≫
      ((sigmaConst (C := C)).obj A).map (H.toSimplicialObjectHomotopy.h i) =
    ((sigmaConst (C := C)).obj A).map (H'.toSimplicialObjectHomotopy.h i) ≫
      ((sigmaConst (C := C)).obj A).map (v.app (op ⦋n + 1⦌))
  simpa only [Functor.map_comp] using congrArg (((sigmaConst (C := C)).obj A).map)
    (simplicialHomotopy_component_naturality H H' u v h n i)

end SimplicialSets

variable {X Y X' Y' : TopCat.{w}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The actual singular simplicial homotopies preserve a commuting
topological homotopy square. -/
theorem topologicalHomotopy_simplicial_square
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) :
    (TopCat.toSSet.map u ▷ Δ[1]) ≫ H.toSSet.h =
      H'.toSSet.h ≫ TopCat.toSSet.map v := by
  change (TopCat.toSSet.map u ▷ Δ[1]) ≫
      (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
        μ TopCat.toSSet X TopCat.I ≫ TopCat.toSSet.map H.h) =
    (TopCat.toSSet.obj X' ◁ SSet.stdSimplex.toSSetObjI ≫
        μ TopCat.toSSet X' TopCat.I ≫ TopCat.toSSet.map H'.h) ≫ TopCat.toSSet.map v
  rw [← whisker_exchange_assoc]
  rw [μ_natural_left_assoc]
  rw [← TopCat.toSSet.map_comp, h, TopCat.toSSet.map_comp]
  simp only [Category.assoc]

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Every degree of the actual singular chain homotopy is natural under
a commuting square of topological homotopies. -/
theorem topologicalHomotopy_chain_naturality
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) (A : C) (a b : ℕ) :
    (((singularChainComplexFunctor C).obj A).map u).f a ≫
        (H.singularChainComplexFunctorObjMap A).hom a b =
      (H'.singularChainComplexFunctorObjMap A).hom a b ≫
        (((singularChainComplexFunctor C).obj A).map v).f b :=
  simplicialHomotopy_chain_naturality H.toSSet H'.toSSet
    (TopCat.toSSet.map u) (TopCat.toSSet.map v)
    (topologicalHomotopy_simplicial_square H H' u v h) A a b

end

end OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy -/

/-! # Relative Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles

noncomputable section

/-!
# Homotopy invariance for genuine relative singular chains

A continuous homotopy of pairs restricts to an actual homotopy on their
subspaces. The compatible absolute singular-chain homotopies descend through
the cokernel defining relative chains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

variable {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}

/-- The initial map of a homotopy preserving the subspaces is a map of pairs. -/
theorem homotopy_start_mapsTo (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Set.MapsTo f A B := by
  intro x hx
  exact (H.map_zero_left x) ▸ hH 0 hx

/-- The terminal map of a homotopy preserving the subspaces is a map of pairs. -/
theorem homotopy_end_mapsTo (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Set.MapsTo g A B := by
  intro x hx
  exact (H.map_one_left x) ▸ hH 1 hx

/-- Restriction of an actual homotopy of pairs to the subspaces. -/
def subspaceHomotopy (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    TopCat.Homotopy (LocalHomology.Cycles.subspaceMap f hf) (LocalHomology.Cycles.subspaceMap g hg) where
  toFun p := ⟨H (p.1, p.2.val), hH p.1 p.2.property⟩
  continuous_toFun :=
    (H.continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)

@[simp]
theorem subspaceHomotopy_apply (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B)
    (t : unitInterval) (x : A) :
    (subspaceHomotopy hf hg H hH (t, x)).val = H (t, x.val) := rfl

/-- The square of actual homotopy maps commutes with the subspace inclusions. -/
theorem subspaceHomotopy_square (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    (LocalHomology.Cycles.subspaceInclusion X A ▷ TopCat.I) ≫ H.h =
      (subspaceHomotopy hf hg H hH).h ≫ LocalHomology.Cycles.subspaceInclusion Y B := by
  ext p
  rfl

/-- The actual singular-chain homotopy commutes with the actual inclusions
of the subspaces, by naturality of its prism construction. -/
theorem singularHomotopy_subspace_naturality
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f a ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b =
      ((subspaceHomotopy hf hg H hH).singularChainComplexFunctorObjMap
        (ModuleCat.of ℤ ℤ)).hom a b ≫ (LocalHomology.Cycles.subspaceChainInclusion Y B).f b :=
  OAI.AlgebraicTopology.Cohomology.Singular.HomotopyNaturality.topologicalHomotopy_chain_naturality H (subspaceHomotopy hf hg H hH)
    (LocalHomology.Cycles.subspaceInclusion X A) (LocalHomology.Cycles.subspaceInclusion Y B)
    (subspaceHomotopy_square hf hg H hH) (ModuleCat.of ℤ ℤ) a b

/-- The ambient homotopy vanishes on subspace chains after relative projection. -/
theorem singularHomotopy_subspace_projection_zero
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f a ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b ≫
        (LocalHomology.Cycles.relativeChainProjection Y B).f b = 0 := by
  have hz : (LocalHomology.Cycles.subspaceChainInclusion Y B).f b ≫
      (LocalHomology.Cycles.relativeChainProjection Y B).f b = 0 :=
    HomologicalComplex.congr_hom (LocalHomology.Cycles.subspaceChainInclusion_projection Y B) b
  rw [← Category.assoc, singularHomotopy_subspace_naturality hf hg H hH,
    Category.assoc, hz, comp_zero]

/-- A continuous homotopy of pairs induces a genuine homotopy between
their induced maps on the relative singular-chain complexes. -/
def relativeSingularChainsHomotopy
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Homotopy (LocalHomology.Cycles.relativeSingularChainsMap f hf) (LocalHomology.Cycles.relativeSingularChainsMap g hg) :=
  CokernelHomotopyDescent.Cycles.descendHomotopy (LocalHomology.Cycles.relativeChainSequence X A) (LocalHomology.Cycles.relativeChainSequence Y B)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (LocalHomology.Cycles.relativeChainProjection_naturality f hf) (LocalHomology.Cycles.relativeChainProjection_naturality g hg)
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ))
    (singularHomotopy_subspace_projection_zero hf hg H hH)

/-- Projection of the constructed relative homotopy agrees with the actual
absolute singular-chain homotopy. -/
@[reassoc]
theorem relativeSingularChainsHomotopy_projection
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (LocalHomology.Cycles.relativeChainProjection X A).f a ≫
        (relativeSingularChainsHomotopy hf hg H hH).hom a b =
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom a b ≫
        (LocalHomology.Cycles.relativeChainProjection Y B).f b :=
  CokernelHomotopyDescent.Cycles.descendHomotopy_projection (LocalHomology.Cycles.relativeChainSequence X A) (LocalHomology.Cycles.relativeChainSequence Y B)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (LocalHomology.Cycles.relativeChainProjection_naturality f hf) (LocalHomology.Cycles.relativeChainProjection_naturality g hg)
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ))
    (singularHomotopy_subspace_projection_zero hf hg H hH) a b

/-- Homotopic maps of pairs induce the same map on genuine relative
singular homology in every degree. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap f hf n = LocalHomology.Cycles.relativeSingularHomologyMap g hg n :=
  (relativeSingularChainsHomotopy hf hg H hH).homologyMap_eq n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy"

@[expose] public section ComponentSource_13
/- Original module: OAI.Geometry.Foundations.ConvexStdSimplexMetric -/
/-
Derived from Formal Conjectures:
  HodgeConjecture/Mathlib/Geometry/Convex/StdSimplexMetric.lean
The upstream Formal Conjectures repository is licensed under Apache 2.0.
This file has been modified.
-/

/-! # Convex Std Simplex Metric -/

namespace OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

noncomputable section

open _root_.Convexity
open _root_.Convexity.StdSimplex

/-! The finite real standard simplex carries the metric on its barycentric weights. -/

/-- The sup metric on barycentric coordinates, preserving the standard simplex topology. -/
instance metricSpace (ι : Type*) [Fintype ι] : MetricSpace (StdSimplex ℝ ι) :=
  (isEmbedding_toFun_comp_weights ℝ ι).comapMetricSpace (fun x => (x.weights : ι → ℝ))

/-- Barycentric coordinates of a real simplex point. -/
scoped instance coeFn (ι : Type*) : CoeFun (StdSimplex ℝ ι) (fun _ => ι → ℝ) :=
  ⟨fun x => x.weights⟩

/-- Construct a finite simplex from nonnegative coordinates summing to one. -/
def ofCoordinates {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) : StdSimplex ℝ ι where
  weights := Finsupp.equivFunOnFinite.symm x
  nonneg i := by simpa using hn i
  total := by simpa [Finsupp.sum_fintype] using ht

@[simp]
theorem ofCoordinates_weights {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) (i : ι) :
    (ofCoordinates x hn ht).weights i = x i := by simp [ofCoordinates]

/-- Coordinates of a finite simplex after identifying vertices. -/
theorem weights_map_sum {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (w : StdSimplex ℝ X) (y : Y) :
    (map f w).weights y = ∑ x with f x = y, w.weights x := by
  classical
  simp [map, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
    Finsupp.single_apply, Finset.sum_filter]

/-- Finite barycentric coordinate vectors form a convex set. -/
theorem convex_range_weights (ι : Type*) [Fintype ι] :
    Convex ℝ (Set.range (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ))) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d hc hd hcd
  refine ⟨ofCoordinates (c • (u.weights : ι → ℝ) + d • (v.weights : ι → ℝ)) ?_ ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg hc (u.weights_nonneg i))
      (mul_nonneg hd (v.weights_nonneg i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, total_of_fintype, mul_one, hcd]
  · funext i
    simp

/-- A nonempty finite standard simplex is contractible through its coordinates. -/
instance contractibleSpace (ι : Type*) [Fintype ι] [Nonempty ι] :
    ContractibleSpace (StdSimplex ℝ ι) := by
  classical
  let coord : StdSimplex ℝ ι → ι → ℝ := fun x => x.weights
  let a : StdSimplex ℝ ι := single (Classical.choice ‹Nonempty ι›)
  let : ContractibleSpace (Set.range coord) :=
    (convex_range_weights ι).contractibleSpace ⟨coord a, ⟨a, rfl⟩⟩
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.contractibleSpace

/-- The finite-coordinate linear map agrees with mapping barycentric weights. -/
theorem map_coordinates {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : StdSimplex ℝ X) :
    ((map f w).weights : Y → ℝ) = FunOnFinite.linearMap ℝ ℝ f (w.weights : X → ℝ) := by
  simp [map, FunOnFinite.linearMap]
  rfl

/-- Distance is the sup distance between the barycentric coordinate vectors. -/
theorem dist_eq_weights {ι : Type*} [Fintype ι] (x y : StdSimplex ℝ ι) :
    dist x y = dist (x.weights : ι → ℝ) (y.weights : ι → ℝ) := rfl

/-- Recover a simplex from a vector known to be its barycentric coordinates. -/
def ofMemRange {ι : Type*} (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : StdSimplex ℝ ι => (y.weights : ι → ℝ))) :
    StdSimplex ℝ ι := Classical.choose hx

@[simp]
theorem ofMemRange_weights {ι : Type*} (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : StdSimplex ℝ ι => (y.weights : ι → ℝ))) :
    ((ofMemRange x hx).weights : ι → ℝ) = x := Classical.choose_spec hx

/-- Finite real simplices inherit local path connectedness from their coordinate range. -/
instance locallyPathConnectedSpace (ι : Type*) [Fintype ι] :
    LocallyPathConnectedSpace (StdSimplex ℝ ι) := by
  let : LocallyPathConnectedSpace
      (Set.range (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ))) :=
    (convex_range_weights ι).locallyPathConnectedSpace
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.symm.locallyPathConnectedSpace

/-- Barycentric coordinates realize the chosen metric isometrically. -/
theorem isometry_weights (ι : Type*) [Fintype ι] :
    Isometry (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ)) :=
  Isometry.of_dist_eq fun x y => (dist_eq_weights x y).symm

end

end OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.Geometry.Foundations.ConvexStdSimplexMetric"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact -/

/-! # Relative Homology Exact -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles

noncomputable section

/-!
# The long exact sequence of integral singular homology of a pair

The boundary maps below are the connecting morphisms of the proved short exact
sequence of genuine singular chain complexes. No local orientation, excision,
or fundamental-class assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Ordinary integral singular homology, computed from mathlib's singular chains. -/
abbrev integralSingularHomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  (LocalHomology.Cycles.integralSingularChains X).homology n

/-- The homology map of a continuous map on genuine integral singular chains. -/
abbrev integralSingularHomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    integralSingularHomology X n ⟶ integralSingularHomology Y n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.integralSingularChainFunctor.map f) n

/-- The homology map induced by the inclusion of the subspace. -/
abbrev subspaceHomologyInclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    integralSingularHomology (TopCat.of A) n ⟶ integralSingularHomology X n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.subspaceChainInclusion X A) n

/-- The map from absolute homology to homology relative to the subspace. -/
abbrev relativeHomologyProjection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    integralSingularHomology X n ⟶ LocalHomology.Cycles.relativeSingularHomology X A n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X A) n

/-- The genuine connecting boundary `H_(n+1)(X,A;ℤ) → H_n(A;ℤ)`. -/
def relativeHomologyBoundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X A (n + 1) ⟶
      integralSingularHomology (TopCat.of A) n :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem subspaceHomologyInclusion_projection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    subspaceHomologyInclusion X A n ≫ relativeHomologyProjection X A n = 0 := by
  change HomologicalComplex.homologyMap (LocalHomology.Cycles.subspaceChainInclusion X A) n ≫
    HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X A) n = 0
  rw [← HomologicalComplex.homologyMap_comp, LocalHomology.Cycles.subspaceChainInclusion_projection,
    HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
theorem relativeHomologyProjection_boundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeHomologyProjection X A (n + 1) ≫ relativeHomologyBoundary X A n = 0 :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).comp_δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem relativeHomologyBoundary_inclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeHomologyBoundary X A n ≫ subspaceHomologyInclusion X A n = 0 :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δ_comp (n + 1) n rfl

/-- Exactness at absolute homology in every degree, including degree zero. -/
theorem relativeHomology_exact_absolute (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (subspaceHomologyInclusion X A n)
      (relativeHomologyProjection X A n)
      (subspaceHomologyInclusion_projection X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₂ n

/-- Exactness at positive-degree relative homology. -/
theorem relativeHomology_exact_relative (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeHomologyProjection X A (n + 1))
      (relativeHomologyBoundary X A n)
      (relativeHomologyProjection_boundary X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₃ (n + 1) n rfl

/-- Exactness at subspace homology in every degree, including degree zero. -/
theorem relativeHomology_exact_subspace (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeHomologyBoundary X A n)
      (subspaceHomologyInclusion X A n)
      (relativeHomologyBoundary_inclusion X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₁ (n + 1) n rfl

/-- An absolute class comes from the subspace exactly when its relative class vanishes. -/
theorem relativeHomology_range_inclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (subspaceHomologyInclusion X A n).hom =
      LinearMap.ker (relativeHomologyProjection X A n).hom :=
  (relativeHomology_exact_absolute X A n).moduleCat_range_eq_ker

/-- A positive-degree relative class lifts absolutely exactly when its boundary vanishes. -/
theorem relativeHomology_range_projection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeHomologyProjection X A (n + 1)).hom =
      LinearMap.ker (relativeHomologyBoundary X A n).hom :=
  (relativeHomology_exact_relative X A n).moduleCat_range_eq_ker

/-- A subspace class bounds relatively exactly when its image in the ambient space vanishes. -/
theorem relativeHomology_range_boundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeHomologyBoundary X A n).hom =
      LinearMap.ker (subspaceHomologyInclusion X A n).hom :=
  (relativeHomology_exact_subspace X A n).moduleCat_range_eq_ker

/-- The degree-zero absolute-to-relative map is surjective. -/
instance relativeHomologyProjection_zero_epi (X : TopCat.{0}) (A : Set X) :
    Epi (relativeHomologyProjection X A 0) := by
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j hj
  exact Nat.succ_ne_zero j hj

/-- A map of topological pairs induces a morphism of the actual short exact chain sequences. -/
def relativeChainSequenceMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    LocalHomology.Cycles.relativeChainSequence X A ⟶ LocalHomology.Cycles.relativeChainSequence Y B where
  τ₁ := LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceMap f h)
  τ₂ := LocalHomology.Cycles.integralSingularChainFunctor.map f
  τ₃ := LocalHomology.Cycles.relativeSingularChainsMap f h
  comm₁₂ := by
    change LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceMap f h) ≫
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion Y B) =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X A) ≫
        LocalHomology.Cycles.integralSingularChainFunctor.map f
    rw [← Functor.map_comp, ← Functor.map_comp, LocalHomology.Cycles.subspaceMap_inclusion]
  comm₂₃ := (LocalHomology.Cycles.relativeChainProjection_naturality f h).symm

/-- Connecting boundaries commute with continuous maps of pairs. -/
@[reassoc]
theorem relativeHomologyBoundary_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    relativeHomologyBoundary X A n ≫
        integralSingularHomologyMap (LocalHomology.Cycles.subspaceMap f h) n =
      LocalHomology.Cycles.relativeSingularHomologyMap f h (n + 1) ≫ relativeHomologyBoundary Y B n :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeChainSequenceMap f h)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A) (LocalHomology.Cycles.relativeChainSequence_shortExact Y B)
    (n + 1) n rfl

/-- When two ambient homology groups vanish, the actual relative boundary is an isomorphism. -/
def relativeHomologyBoundaryIso (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (integralSingularHomology X (n + 1)))
    (hj : IsZero (integralSingularHomology X n)) :
    LocalHomology.Cycles.relativeSingularHomology X A (n + 1) ≅
      integralSingularHomology (TopCat.of A) n :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δIso (n + 1) n rfl hi hj

@[simp]
theorem relativeHomologyBoundaryIso_hom (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (integralSingularHomology X (n + 1)))
    (hj : IsZero (integralSingularHomology X n)) :
    (relativeHomologyBoundaryIso X A n hi hj).hom = relativeHomologyBoundary X A n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows -/

/-! # Cech Cover Rows -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows

noncomputable section

/-!
# A Čech row resolution of small singular simplices

The projection from the disjoint union of a set cover has a section. Its
augmented Čech nerve therefore has an extra degeneracy, and applying the free
module functor gives a chain homotopy equivalence to the covered set in degree
zero. We apply this to the actual singular simplices whose images lie in at
least one member of a family of subsets.

This is a row resolution only. It does not identify the full singular complex
with its small-simplex subcomplex and does not assert a nerve theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

universe u

variable {α ι : Type u}

/-- The actual projection from the disjoint union of a family of subsets. -/
def coverProjection (U : ι → Set α) : (Σ i, U i) ⟶ α :=
  TypeCat.ofHom (fun z => z.2.1)

/-- The projection is surjective precisely when the subsets cover. -/
theorem coverProjection_surjective (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) : Function.Surjective (coverProjection U) := by
  intro x
  obtain ⟨i, hi⟩ := hU x
  exact ⟨⟨i, x, hi⟩, rfl⟩

/-- A set-theoretic section of a covering projection. -/
def coverProjectionSplit (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    SplitEpi (coverProjection U) where
  section_ := TypeCat.ofHom (fun x =>
    ⟨Classical.choose (hU x), x, Classical.choose_spec (hU x)⟩)
  id := by
    ext x
    rfl

/-- The augmented Čech nerve of the actual covering projection. -/
def coverCechNerve (U : ι → Set α) : SimplicialObject.Augmented (Type u) :=
  (Arrow.mk (coverProjection U)).augmentedCechNerve

/-- The chosen section supplies an extra degeneracy, with all identities proved
by mathlib's split Čech nerve construction. -/
def coverCechExtraDegeneracy (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    SimplicialObject.Augmented.ExtraDegeneracy (coverCechNerve U) :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (Arrow.mk (coverProjection U)) (coverProjectionSplit U hU)

variable (R : Type u) [Ring R]

/-- Free-module Čech chains of the projection from the disjoint union. -/
def coverCechModuleNerve (U : ι → Set α) :
    SimplicialObject.Augmented (ModuleCat R) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free R)).obj
    (coverCechNerve U)

/-- The alternating face complex resolving the covered set. -/
def coverCechChains (U : ι → Set α) : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (coverCechModuleNerve R U).left

/-- The augmented Čech chain resolution of a set cover contracts onto the free
module on the covered set, concentrated in degree zero. -/
def coverCechHomotopyEquiv (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    HomotopyEquiv (coverCechChains R U)
      ((ChainComplex.single₀ (ModuleCat R)).obj ((ModuleCat.free R).obj α)) :=
  ((coverCechExtraDegeneracy U hU).map (ModuleCat.free R)).homotopyEquiv

/-- Positive homology vanishes in this actual Čech row complex. -/
theorem coverCech_exactAt_succ (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (k : ℕ) :
    (coverCechChains R U).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    (ChainComplex.exactAt_succ_single_obj ((ModuleCat.free R).obj α) k).isZero_homology
    ((coverCechHomotopyEquiv R U hU).toHomologyIso (k + 1))

/-- The zeroth homology of the Čech row is the free module on the covered set. -/
def coverCechHomologyZeroIso (U : ι → Set α) (hU : ∀ x, ∃ i, x ∈ U i) :
    (coverCechChains R U).homology 0 ≅ (ModuleCat.free R).obj α :=
  (coverCechHomotopyEquiv R U hU).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 ((ModuleCat.free R).obj α)

variable (X : TopCat.{u}) (U : ι → Set X) (n : ℕ)

/-- Actual singular n-simplices whose image is contained in one cover member. -/
def SmallSingularSimplex :=
  {σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) //
    ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) ⊆ U i}

/-- The member of the simplex cover corresponding to the spatial subset U i. -/
def smallSingularSimplexCover (i : ι) : Set (SmallSingularSimplex X U n) :=
  {σ | Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ.1) ⊆ U i}

/-- Smallness supplies the required covering property, without an extra
topological or comparison assumption. -/
theorem smallSingularSimplexCover_covers (σ : SmallSingularSimplex X U n) :
    ∃ i, σ ∈ smallSingularSimplexCover X U n i :=
  σ.2

/-- The actual Čech row of free modules on small singular n-simplices is chain
homotopy equivalent to the free module on those simplices in degree zero. -/
def smallSingularCechHomotopyEquiv :
    HomotopyEquiv (coverCechChains R (smallSingularSimplexCover X U n))
      ((ChainComplex.single₀ (ModuleCat R)).obj
        ((ModuleCat.free R).obj (SmallSingularSimplex X U n))) :=
  coverCechHomotopyEquiv R (smallSingularSimplexCover X U n)
    (smallSingularSimplexCover_covers X U n)

/-- Every positive Čech degree in a fixed singular-simplex row is exact. -/
theorem smallSingularCech_exactAt_succ (k : ℕ) :
    (coverCechChains R (smallSingularSimplexCover X U n)).ExactAt (k + 1) :=
  coverCech_exactAt_succ R (smallSingularSimplexCover X U n)
    (smallSingularSimplexCover_covers X U n) k

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.DeRham.Comparison.CechCoverRows"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet -/

/-! # Small Singular Set -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet

noncomputable section

/-!
# Singular simplices subordinate to a family of subsets

Precomposing a singular simplex by any simplicial operator does not enlarge its
image. Thus the simplices contained in some member of a given family form a
genuine subcomplex of mathlib's singular simplicial set.

No subdivision or quasi-isomorphism assertion is made here.
-/

open _root_.CategoryTheory
open scoped Simplicial

universe u

variable (X : TopCat.{u})

/-- A simplicial operator restricts the image of an actual singular simplex. -/
theorem singularSimplex_range_map_subset
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) :
    Set.range (X.toSSetObjEquiv m ((TopCat.toSSet.obj X).map f σ)) ⊆
      Set.range (X.toSSetObjEquiv n σ) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨((SimplexCategory.toTop.{u}.map f.unop) (ULift.up x)).down, ?_⟩
  rfl

variable {ι κ : Type u} (U : ι → Set X)

/-- The actual simplicial subcomplex of simplices contained in a cover member. -/
def smallSingularSubcomplex : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ hσ := by
    obtain ⟨i, hi⟩ := hσ
    exact ⟨i, (singularSimplex_range_map_subset X f σ).trans hi⟩

/-- Membership is the standard image-containment condition. -/
@[simp]
theorem mem_smallSingularSubcomplex {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSubcomplex X U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := Iff.rfl

/-- The inclusion is the actual canonical inclusion of a simplicial subcomplex. -/
def smallSingularInclusion :
    (smallSingularSubcomplex X U : SSet) ⟶ TopCat.toSSet.obj X :=
  (smallSingularSubcomplex X U).ι

instance smallSingularInclusion_mono : Mono (smallSingularInclusion X U) := by
  unfold smallSingularInclusion
  infer_instance

/-- Degreewise identification with the simplex type resolved by CechCoverRows. -/
def smallSingularDegreeEquiv (n : ℕ) :
    ((smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌)) ≃
      CechCoverRows.SmallSingularSimplex X U n :=
  Equiv.refl _

/-- Refining the family can only enlarge the small singular subcomplex. -/
theorem smallSingularSubcomplex_le_of_refinement (V : κ → Set X)
    (h : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularSubcomplex X U ≤ smallSingularSubcomplex X V := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, hi.trans hj⟩

/-- Pointwise inclusion is a special case of refinement. -/
theorem smallSingularSubcomplex_mono (V : ι → Set X) (h : ∀ i, U i ⊆ V i) :
    smallSingularSubcomplex X U ≤ smallSingularSubcomplex X V :=
  smallSingularSubcomplex_le_of_refinement X U V (fun i => ⟨i, h i⟩)

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris -/

/-! # Small Mayer Vietoris -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles

noncomputable section

/-!
# Mayer–Vietoris for the actual binary-cover small singular chains

The union here consists of simplices whose entire image is in one of the two
subsets. It is not the full singular set of the union. The short exact sequence
and its homology sequence do not assume the small-to-all quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- The ordinary integral chain functor on simplicial sets. -/
abbrev integralSimplicialChainFunctor : SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The ordinary simplicial chain functor preserves colimits degree by degree. -/
instance integralSimplicialChainFunctor_preservesColimits :
    PreservesColimits integralSimplicialChainFunctor where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type)).obj (.op ⦋n⦌) ⋙
        sigmaConst.obj (ModuleCat.of ℤ ℤ))
    infer_instance

instance integralSimplicialChainFunctor_preservesMonomorphisms :
    integralSimplicialChainFunctor.PreservesMonomorphisms where
  preserves f _ := by
    dsimp [integralSimplicialChainFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono

/-- Inclusion of one actual subspace in another. -/
def subsetInclusion (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

instance subsetInclusion_mono (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    Mono (subsetInclusion X h) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

/-- The image of the singular set of a genuine subspace in the ambient singular set. -/
abbrev subspaceSingularSubcomplex (X : TopCat.{0}) (U : Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X U))

/-- Image membership is exactly containment of the whole singular simplex in the subspace. -/
theorem mem_subspaceSingularSubcomplex (X : TopCat.{0}) (U : Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (subspaceSingularSubcomplex X U).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ U := by
  constructor
  · rintro ⟨τ, rfl⟩ y ⟨z, rfl⟩
    exact (((TopCat.of U).toSSetObjEquiv n τ) z).property
  · intro hσ
    let τ : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), U) :=
      ⟨fun z => ⟨X.toSSetObjEquiv n σ z, hσ ⟨z, rfl⟩⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl

/-- The contained-simplex subcomplex is the actual singular set of the subspace. -/
def subspaceSingularSetIso (X : TopCat.{0}) (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅ (subspaceSingularSubcomplex X U : SSet) :=
  asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X U)))

/-- Containment in an intersection is the intersection of the two simplex conditions. -/
theorem subspaceSingularSubcomplex_inter (X : TopCat.{0}) (U V : Set X) :
    subspaceSingularSubcomplex X (U ∩ V) =
      subspaceSingularSubcomplex X U ⊓ subspaceSingularSubcomplex X V := by
  ext n σ
  change σ ∈ (subspaceSingularSubcomplex X (U ∩ V)).obj n ↔
    σ ∈ (subspaceSingularSubcomplex X U).obj n ∧
      σ ∈ (subspaceSingularSubcomplex X V).obj n
  rw [mem_subspaceSingularSubcomplex, mem_subspaceSingularSubcomplex,
    mem_subspaceSingularSubcomplex]
  exact Set.subset_inter_iff

/-- Simplices subordinate to the binary family, requiring one whole-image containment. -/
abbrev binarySmallSingularSubcomplex (X : TopCat.{0}) (U V : Set X) :
    (TopCat.toSSet.obj X).Subcomplex :=
  subspaceSingularSubcomplex X U ⊔ subspaceSingularSubcomplex X V

/-- This is the same small-simplex construction used by the comparison infrastructure. -/
theorem binarySmallSingularSubcomplex_eq (X : TopCat.{0}) (U V : Set X) :
    binarySmallSingularSubcomplex X U V =
      OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X (fun b : Bool => if b then V else U) := by
  ext n σ
  change (σ ∈ (subspaceSingularSubcomplex X U).obj n ∨
      σ ∈ (subspaceSingularSubcomplex X V).obj n) ↔
    ∃ b : Bool, Set.range (X.toSSetObjEquiv n σ) ⊆ if b then V else U
  rw [mem_subspaceSingularSubcomplex, mem_subspaceSingularSubcomplex]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

/-- Singular simplices of the first subspace, viewed as small ambient simplices. -/
def binarySmallSingularLeft (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (binarySmallSingularSubcomplex X U V : SSet) :=
  (subspaceSingularSetIso X U).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

/-- Singular simplices of the second subspace, viewed as small ambient simplices. -/
def binarySmallSingularRight (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ (binarySmallSingularSubcomplex X U V : SSet) :=
  (subspaceSingularSetIso X V).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

/-- The binary small singular set is the pushout of the two genuine subspace
singular sets over the genuine singular set of their intersection. -/
theorem binarySmallSingular_isPushout (X : TopCat.{0}) (U V : Set X) :
    IsPushout (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (binarySmallSingularLeft X U V) (binarySmallSingularRight X U V) := by
  let sq : SSet.Subcomplex.BicartSq (subspaceSingularSubcomplex X (U ∩ V))
      (subspaceSingularSubcomplex X U) (subspaceSingularSubcomplex X V)
      (binarySmallSingularSubcomplex X U V) :=
    ⟨rfl, (subspaceSingularSubcomplex_inter X U V).symm⟩
  exact sq.isPushout.of_iso'
    (subspaceSingularSetIso X (U ∩ V)) (subspaceSingularSetIso X U)
    (subspaceSingularSetIso X V) (Iso.refl _)
    (by ext n σ; rfl) (by ext n σ; rfl) (by simp [binarySmallSingularLeft])
    (by simp [binarySmallSingularRight])

/-- Actual integral chains generated by simplices lying wholly in one of the two subsets. -/
abbrev binarySmallSingularChains (X : TopCat.{0}) (U V : Set X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSimplicialChainFunctor.obj (binarySmallSingularSubcomplex X U V : SSet)

/-- The homology of the actual binary-cover small chain complex. -/
abbrev binarySmallSingularHomology (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ModuleCat.{0} ℤ := (binarySmallSingularChains X U V).homology n

/-- The singular-set pushout remains a pushout after forming integral chains. -/
theorem binarySmallChain_isPushout (X : TopCat.{0}) (U V : Set X) :
    IsPushout
      (LocalHomology.Cycles.integralSingularChainFunctor.map
        (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
      (LocalHomology.Cycles.integralSingularChainFunctor.map
        (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (integralSimplicialChainFunctor.map (binarySmallSingularLeft X U V))
      (integralSimplicialChainFunctor.map (binarySmallSingularRight X U V)) :=
  integralSimplicialChainFunctor.map_isPushout (binarySmallSingular_isPushout X U V)

/-- The genuine small-chain sequence `C(U∩V) → C(U)⊕C(V) → C_small(U,V)`.
The first arrow uses the two inclusions with signs `(+,-)`; the second adds them. -/
def smallMayerVietorisSequence (X : TopCat.{0}) (U V : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (binarySmallChain_isPushout X U V).shortComplex

@[simp]
theorem smallMayerVietorisSequence_f (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).f =
      biprod.lift
        (LocalHomology.Cycles.integralSingularChainFunctor.map
          (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)))
        (-LocalHomology.Cycles.integralSingularChainFunctor.map
          (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))) := rfl

@[simp]
theorem smallMayerVietorisSequence_g (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).g =
      biprod.desc
        (integralSimplicialChainFunctor.map (binarySmallSingularLeft X U V))
        (integralSimplicialChainFunctor.map (binarySmallSingularRight X U V)) := rfl

/-- The small-chain sequence is short exact, with no excision or subdivision hypothesis. -/
theorem smallMayerVietorisSequence_shortExact (X : TopCat.{0}) (U V : Set X) :
    (smallMayerVietorisSequence X U V).ShortExact := by
  have hm : Mono (LocalHomology.Cycles.integralSingularChainFunctor.map
      (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))) := by
    change Mono (integralSimplicialChainFunctor.map
      (TopCat.toSSet.map (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))))
    infer_instance
  have : Mono (smallMayerVietorisSequence X U V).f := by
    rw [smallMayerVietorisSequence_f]
    exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hm (biprod.lift_fst _ _)
  have : Epi (smallMayerVietorisSequence X U V).g :=
    (binarySmallChain_isPushout X U V).epi_shortComplex_g
  exact { exact := (binarySmallChain_isPushout X U V).exact_shortComplex }

/-- The short exact sequence is exact in every actual chain degree. -/
theorem smallMayerVietorisSequence_degreewiseShortExact
    (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ((smallMayerVietorisSequence X U V).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (smallMayerVietorisSequence_shortExact X U V) n

/-- The middle homology object has its canonical direct-sum interpretation. -/
def smallMayerVietorisMiddleHomologyIso (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (smallMayerVietorisSequence X U V).X₂.homology n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n ⊞
        RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproduct
      (LocalHomology.Cycles.integralSingularChains (TopCat.of U)) (LocalHomology.Cycles.integralSingularChains (TopCat.of V)) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  exact F.mapBiprod _ _

set_option backward.isDefEq.respectTransparency false in
/-- In the direct-sum description, the first component is the usual inclusion map. -/
@[reassoc]
theorem smallMayerVietoris_homology_f_fst (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n ≫
      (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.fst =
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)) n := by
  have h : (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap biprod.fst n := by
    exact biprod.lift_fst _ _
  rw [h, ← HomologicalComplex.homologyMap_comp, smallMayerVietorisSequence_f,
    biprod.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- In the direct-sum description, the second inclusion carries the opposite sign. -/
@[reassoc]
theorem smallMayerVietoris_homology_f_snd (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n ≫
      (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.snd =
        -RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V)) n := by
  have h : (smallMayerVietorisMiddleHomologyIso X U V n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap biprod.snd n := by
    exact biprod.lift_snd _ _
  rw [h, ← HomologicalComplex.homologyMap_comp, smallMayerVietorisSequence_f,
    biprod.lift_snd, HomologicalComplex.homologyMap_neg]

/-- The genuine connecting map from small homology to intersection homology. -/
def smallMayerVietorisBoundary (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    binarySmallSingularHomology X U V (n + 1) ⟶
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) n :=
  (smallMayerVietorisSequence_shortExact X U V).δ (n + 1) n rfl

/-- Six consecutive terms of the small-chain Mayer–Vietoris homology sequence. -/
def smallMayerVietorisHomologySequence (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℤ) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (smallMayerVietorisSequence_shortExact X U V) (n + 1) n rfl

/-- Exactness of the six-term sequence; the middle objects are canonically the
sums of the two subspace homologies via `smallMayerVietorisMiddleHomologyIso`. -/
theorem smallMayerVietorisHomologySequence_exact
    (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (smallMayerVietorisHomologySequence X U V n).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (smallMayerVietorisSequence_shortExact X U V) (n + 1) n rfl

/-- Exactness at the homology of the two subspaces. -/
theorem smallMayerVietoris_range_left (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).g n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₂ n).moduleCat_range_eq_ker

/-- A small homology class comes from the subspace sum exactly when its boundary vanishes. -/
theorem smallMayerVietoris_range_middle (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range
      (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).g (n + 1)).hom =
        LinearMap.ker (smallMayerVietorisBoundary X U V n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₃
    (n + 1) n rfl).moduleCat_range_eq_ker

/-- An intersection class is a small-homology boundary exactly when it dies in both subspaces. -/
theorem smallMayerVietoris_range_boundary (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    LinearMap.range (smallMayerVietorisBoundary X U V n).hom =
      LinearMap.ker
        (HomologicalComplex.homologyMap (smallMayerVietorisSequence X U V).f n).hom :=
  ((smallMayerVietorisSequence_shortExact X U V).homology_exact₁
    (n + 1) n rfl).moduleCat_range_eq_ker

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh -/

/-! # Barycentric Mesh -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh

noncomputable section

/-!
# Quantitative mesh estimates for barycenters of nested faces

The points are actual vectors in a real normed space and their barycenters are
mathlib's `Finset.centroid`. No simplex mesh estimate is assumed.
-/

open scoped BigOperators

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centroid of a nonempty finite set is the arithmetic mean of its vertices. -/
theorem centroid_eq_inv_card_sum (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    s.centroid ℝ v = (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i := by
  rw [s.centroid_eq_centerMass hs,
    s.centerMass_eq_of_sum_1 v (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, Finset.smul_sum]

/-- Subtracting a point commutes with taking the arithmetic mean. -/
theorem centroid_sub_eq_inv_card_sum (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (x : E) :
    s.centroid ℝ v - x = (s.card : ℝ)⁻¹ • ∑ i ∈ s, (v i - x) := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  rw [centroid_eq_inv_card_sum s hs v, Finset.sum_sub_distrib, smul_sub,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The sum of vertex displacements from their centroid is zero. -/
theorem sum_sub_centroid_eq_zero (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    ∑ i ∈ s, (v i - s.centroid ℝ v) = 0 := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    centroid_eq_inv_card_sum s hs v, smul_smul, mul_inv_cancel₀ hcard,
    one_smul, sub_self]

/-- A centroid remains within every closed ball containing all its vertices. -/
theorem dist_centroid_point_le (s : Finset ι) (hs : s.Nonempty) (v : ι → E)
    (x : E) (D : ℝ) (hD : ∀ i ∈ s, dist (v i) x ≤ D) :
    dist (s.centroid ℝ v) x ≤ D := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  have hnonneg : 0 ≤ (s.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    dist (s.centroid ℝ v) x =
        ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, (v i - x)‖ := by
      rw [dist_eq_norm, centroid_sub_eq_inv_card_sum s hs v x]
    _ = (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, (v i - x)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hnonneg]
    _ ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖v i - x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le s _) hnonneg
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, D := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      exact Finset.sum_le_sum (fun i hi => by simpa only [dist_eq_norm] using hD i hi)
    _ = D := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Nested faces have barycenters closer by the exact missing-vertex proportion. -/
theorem dist_centroid_le_card_sdiff_div [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤
      ((B \ A).card : ℝ) / (B.card : ℝ) * D := by
  have hB : B.Nonempty := hA.mono hAB
  have hnonneg : 0 ≤ (B.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsum : (∑ i ∈ B, (v i - A.centroid ℝ v)) =
      ∑ i ∈ B \ A, (v i - A.centroid ℝ v) := by
    rw [← Finset.sum_sdiff hAB, sum_sub_centroid_eq_zero A hA v, add_zero]
  have hpoint (j : ι) (hj : j ∈ B) : ‖v j - A.centroid ℝ v‖ ≤ D := by
    rw [← dist_eq_norm, dist_comm]
    exact dist_centroid_point_le A hA v (v j) D (fun i hi => hD i (hAB hi) j hj)
  calc
    dist (A.centroid ℝ v) (B.centroid ℝ v) =
        ‖(B.card : ℝ)⁻¹ • ∑ i ∈ B \ A, (v i - A.centroid ℝ v)‖ := by
      rw [dist_comm, dist_eq_norm, centroid_sub_eq_inv_card_sum B hB v, hsum]
    _ = (B.card : ℝ)⁻¹ * ‖∑ i ∈ B \ A, (v i - A.centroid ℝ v)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hnonneg]
    _ ≤ (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, ‖v i - A.centroid ℝ v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le (B \ A) _) hnonneg
    _ ≤ (B.card : ℝ)⁻¹ * ∑ _i ∈ B \ A, D := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      exact Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_sdiff.mp hi).1)
    _ = ((B \ A).card : ℝ) / (B.card : ℝ) * D := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      ring

/-- The exact estimate expressed as the difference of the two face cardinalities. -/
theorem dist_centroid_le_card_sub_div [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤
      ((B.card : ℝ) - (A.card : ℝ)) / (B.card : ℝ) * D := by
  simpa only [Finset.card_sdiff_of_subset hAB, Nat.cast_sub (Finset.card_le_card hAB)]
    using dist_centroid_le_card_sdiff_div v A B hA hAB D hD

/-- A nonempty nested pair of faces with at most `n+1` vertices contracts by `n/(n+1)`. -/
theorem dist_centroid_le_dimension_factor_of_subset [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (n : ℕ) (hcard : B.card ≤ n + 1)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤ (n : ℝ) / (n + 1) * D := by
  have hD0 : 0 ≤ D := by
    obtain ⟨i, hi⟩ := hA
    simpa only [dist_self] using hD i (hAB hi) i (hAB hi)
  have ha1 : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hA.card_pos
  have hbpos : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast (hA.mono hAB).card_pos
  have hbn : (B.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hproduct : (B.card : ℝ) ≤ (A.card : ℝ) * ((n : ℝ) + 1) := by
    have hmul := mul_le_mul_of_nonneg_right ha1 (le_of_lt hn)
    nlinarith
  have hratio : ((B.card : ℝ) - (A.card : ℝ)) / (B.card : ℝ) ≤
      (n : ℝ) / (n + 1) := by
    apply (div_le_div_iff₀ hbpos hn).2
    nlinarith
  exact (dist_centroid_le_card_sub_div v A B hA hAB D hD).trans
    (mul_le_mul_of_nonneg_right hratio hD0)

/-- Any two comparable nonempty faces of `n+1` actual vertices satisfy the mesh bound. -/
theorem dist_centroid_le_dimension_factor {n : ℕ}
    (v : Fin (n + 1) → E) (A B : Finset (Fin (n + 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A ⊆ B ∨ B ⊆ A)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤ (n : ℝ) / (n + 1) * D := by
  have hcard (C : Finset (Fin (n + 1))) : C.card ≤ n + 1 := by
    simpa only [Fintype.card_fin] using C.card_le_univ
  rcases hAB with hAB | hBA
  · exact dist_centroid_le_dimension_factor_of_subset v A B hA hAB n (hcard B) D
      (fun i _ j _ => hD i j)
  · rw [dist_comm]
    exact dist_centroid_le_dimension_factor_of_subset v B A hB hBA n (hcard A) D
      (fun i _ j _ => hD i j)

/-- The same mesh bound holds throughout the convex hull of a chain of face barycenters. -/
theorem dist_convexHull_centroids_le_dimension_factor {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D)
    {x y : E}
    (hx : x ∈ convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v))
    (hy : y ∈ convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) :
    dist x y ≤ (n : ℝ) / (n + 1) * D := by
  obtain ⟨x', ⟨k, rfl⟩, y', ⟨l, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans
    (dist_centroid_le_dimension_factor v (faces k) (faces l) (hne k) (hne l)
      (hchain k l) D hD)

/-- Barycentric subdivision of a finite simplex has mesh at most `n/(n+1)` times its vertex bound. -/
theorem diam_convexHull_centroids_le_dimension_factor {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    Metric.diam (convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) ≤
      (n : ℝ) / (n + 1) * D := by
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hD 0 0
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  exact dist_convexHull_centroids_le_dimension_factor v faces hne hchain D hD hx hy

/-- The geometric mesh estimate with the actual diameter of the original simplex. -/
theorem diam_face_chain_le_simplex_diam {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k) :
    Metric.diam (convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) ≤
      (n : ℝ) / (n + 1) * Metric.diam (convexHull ℝ (Set.range v)) := by
  have hD (i j : Fin (n + 1)) : dist (v i) (v j) ≤ Metric.diam (Set.range v) :=
    Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)
  simpa only [convexHull_diam] using
    diam_convexHull_centroids_le_dimension_factor v faces hne hchain
      (Metric.diam (Set.range v)) hD

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh.diam_face_chain_le_simplex_diam, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "e4272e9a6bfbf2cd6db4e07b2d446434"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:e4272e9a6bfbf2cd6db4e07b2d446434"
