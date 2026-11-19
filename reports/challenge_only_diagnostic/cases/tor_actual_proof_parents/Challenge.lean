module
public import Lean Lean.Util.CollectAxioms Lean.Elab.Tactic.Omega Mathlib.Algebra.Algebra.Bilinear Mathlib.Algebra.Algebra.Subalgebra.Basic Mathlib.Algebra.Algebra.Subalgebra.Lattice Mathlib.Algebra.Algebra.Tower Mathlib.Algebra.BigOperators.Finsupp.Basic Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.Algebra.BigOperators.Pi Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Category.ModuleCat.Basic Mathlib.Algebra.Category.ModuleCat.ChangeOfRings Mathlib.Algebra.Category.ModuleCat.ExteriorPower Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic Mathlib.Algebra.Category.ModuleCat.Projective Mathlib.Algebra.DirectSum.Decomposition Mathlib.Algebra.DirectSum.Module Mathlib.Algebra.Homology.Augment Mathlib.Algebra.Homology.HomologicalComplex Mathlib.Algebra.Homology.HomologicalComplexAbelian Mathlib.Algebra.Homology.HomologicalComplexLimits Mathlib.Algebra.Homology.HomologySequence Mathlib.Algebra.Homology.Homotopy Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle Mathlib.Algebra.Homology.Linear Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex Mathlib.Algebra.Homology.ShortComplex.Linear Mathlib.Algebra.Homology.ShortComplex.ModuleCat Mathlib.Algebra.Homology.ShortComplex.Preadditive Mathlib.Algebra.Homology.ShortComplex.PreservesHomology Mathlib.Algebra.Homology.ShortComplex.ShortExact Mathlib.Algebra.Module.Equiv.Basic Mathlib.Algebra.Module.Pi Mathlib.Algebra.Module.Projective Mathlib.Algebra.Module.SpanRank Mathlib.Algebra.Module.Submodule.Equiv Mathlib.Algebra.MvPolynomial.Basic Mathlib.Algebra.MvPolynomial.CommRing Mathlib.Algebra.MvPolynomial.Eval Mathlib.Algebra.MvPolynomial.Rename Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.Ring.GeomSum Mathlib.Algebra.Ring.Subgroup Mathlib.Algebra.Ring.Subring.Basic Mathlib.CategoryTheory.Limits.Shapes.Kernels Mathlib.CategoryTheory.Monoidal.Braided.Basic Mathlib.CategoryTheory.Monoidal.Tor Mathlib.Data.Finset.Card Mathlib.Data.Finset.Grade Mathlib.Data.Finset.Lattice.Fold Mathlib.Data.Finset.Max Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Sort Mathlib.Data.Finset.Union Mathlib.Data.Finsupp.Order Mathlib.Data.Finsupp.SMul Mathlib.Data.Finsupp.Weight Mathlib.Data.Fintype.BigOperators Mathlib.Data.Fintype.Perm Mathlib.Data.List.Nodup Mathlib.Data.List.OfFn Mathlib.GroupTheory.FreeAbelianGroup Mathlib.GroupTheory.GroupAction.Defs Mathlib.GroupTheory.Perm.Fin Mathlib.GroupTheory.QuotientGroup.Defs Mathlib.LinearAlgebra.Alternating.Uncurry.Fin Mathlib.LinearAlgebra.Basis.Basic Mathlib.LinearAlgebra.Basis.Defs Mathlib.LinearAlgebra.Basis.SMul Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation Mathlib.LinearAlgebra.CliffordAlgebra.Contraction Mathlib.LinearAlgebra.CliffordAlgebra.Grading Mathlib.LinearAlgebra.Dual.Basis Mathlib.LinearAlgebra.Dual.Defs Mathlib.LinearAlgebra.ExteriorAlgebra.Basis Mathlib.LinearAlgebra.ExteriorAlgebra.Grading Mathlib.LinearAlgebra.ExteriorAlgebra.Product Mathlib.LinearAlgebra.ExteriorPower.Basic Mathlib.LinearAlgebra.ExteriorPower.Basis Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.LinearAlgebra.Finsupp.Defs Mathlib.LinearAlgebra.Finsupp.LSum Mathlib.LinearAlgebra.Finsupp.LinearCombination Mathlib.LinearAlgebra.Finsupp.Span Mathlib.LinearAlgebra.Finsupp.Supported Mathlib.LinearAlgebra.Finsupp.VectorSpace Mathlib.LinearAlgebra.FreeModule.Finite.Basic Mathlib.LinearAlgebra.Isomorphisms Mathlib.LinearAlgebra.LinearIndependent.Basic Mathlib.LinearAlgebra.Pi Mathlib.LinearAlgebra.Quotient.Basic Mathlib.LinearAlgebra.Quotient.Bilinear Mathlib.LinearAlgebra.TensorProduct.Basis Mathlib.LinearAlgebra.TensorProduct.Map Mathlib.LinearAlgebra.TensorProduct.Pi Mathlib.LinearAlgebra.TensorProduct.Prod Mathlib.Order.Atoms.Finite Mathlib.Order.Basic Mathlib.Order.Fin.Tuple Mathlib.Order.Interval.Finset.Fin Mathlib.Order.PiLex Mathlib.Order.Preorder.Finite Mathlib.Order.Prod.Lex.Basic Mathlib.RepresentationTheory.Basic Mathlib.RingTheory.Ideal.Operations Mathlib.RingTheory.Ideal.Quotient.Operations Mathlib.RingTheory.Ideal.Span Mathlib.RingTheory.MvPolynomial.Ideal Mathlib.RingTheory.MvPolynomial.Symmetric.Defs Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous Mathlib.RingTheory.Regular.RegularSequence Mathlib.RingTheory.TwoSidedIdeal.Operations Mathlib.Tactic.Abel Mathlib.Tactic.Ext Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination Mathlib.Tactic.Push Mathlib.Tactic.Ring Mathlib.Tactic.SplitIfs Lean.Elab.Command
/-! Theorem 1.2: actual homogeneous Koszul filtration, associated graded, and genuine derived Tor comparison. -/
@[expose] public section
namespace PalomarBarycentricTor
theorem natRightCancelAdd : IsRightCancelAdd ℕ := by infer_instance
theorem coefficientSMulComm {K : Type*} [CommRing K] : SMulCommClass K K K := by infer_instance
theorem functionScalarTower {V K : Type*} [CommRing K] : IsScalarTower K K (V → K) := by infer_instance
theorem exteriorScalarComm {V K : Type*} [CommRing K] : SMulCommClass K K (ExteriorAlgebra K (V → K)) := by infer_instance
theorem tensorPreservesZero {R : Type*} [CommRing R] (M : ModuleCat R) : ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj M).PreservesZeroMorphisms := by infer_instance
attribute [instance 2200] natRightCancelAdd coefficientSMulComm functionScalarTower exteriorScalarComm tensorPreservesZero
end PalomarBarycentricTor
end
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators DirectSum
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
 def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p
 @[simp] theorem mem_faceVertices {p a : P} : a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
 theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
 theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P) (hsu : s ⊆ faceVertices p) : ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
 def faceRank (p : P) : ℕ := (faceVertices p).card
 @[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by sorry
 theorem faceRank_strictMono (hs : IsSimplicialPoset P) : StrictMono (faceRank : P → ℕ) := by sorry
 def koszulExteriorDegree {d i : ℕ} (s : Set.powersetCard (Fin d) i) : ℕ :=
  ∑ j ∈ s.val, (j.val + 1)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
instance palomarNonzeroFaceFintype : Fintype (NonzeroFace P) := Fintype.ofFinite _
 def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
 def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
 def minimalCommonUppers (p q : P) : Finset P :=
  univ.filter (IsMinimalCommonUpper p q)
end FourPapers.Universal
namespace CommAlg.Simplicial
set_option backward.isDefEq.respectTransparency false
open CliffordAlgebra
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
 abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
 def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
 def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | K s ∧ s.card = i})
 def Downward (K : Finset V → Prop) : Prop :=
  ∀ ⦃s t⦄, t ⊆ s → K s → K t
 abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
 lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k} (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by sorry
end CommAlg.Simplicial
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
 abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
 def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
 def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}
 def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)
 abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs
 def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
 abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
 def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
 def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
 def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
 def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
 def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
 def barycentricParameterAction (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)
 def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory
universe u
variable {K : Type u} [CommRing K]
 abbrev complexIncoming (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  (C.d (i + 1) i).hom
 abbrev complexOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  (C.d i (i - 1)).hom
 theorem complexIncomingOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) : (complexOutgoing C i).comp (complexIncoming C i) = 0 := by sorry
end FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Category Limits Module ExteriorAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
 noncomputable def koszulComplex.dAlternating (n : ℕ) : M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))
 noncomputable def koszulComplex.d (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n)
 lemma koszulComplex.d_comp_eq_zero (n : ℕ) : koszulComplex.d φ n ∘ₗ koszulComplex.d φ (n + 1) = 0 := by sorry
 noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])
end
namespace CommAlg.Koszul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TensorProduct
universe u v
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
 abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R x))
 def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)
 def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i :=
    ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
end CommAlg.Koszul
namespace CommAlg.Koszul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MvPolynomial
universe u v
variable {V : Type} {k : Type u} [CommRing k]
 def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)
end CommAlg.Koszul
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
 structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x,
    res hrq (res hqp x) = res (hrq.trans hqp) x
attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module
end FourPapers.Universal
namespace FourPapers.Universal.ModuleDiagram
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable (D : ModuleDiagram K P)
 def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)
end FourPapers.Universal.ModuleDiagram
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
 structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)
end FourPapers.Universal
namespace FourPapers.Universal.CoherentEquiv
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable {D E F : ModuleDiagram K P}
def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) =
      e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (e.component p) c (x.val p)
end
end FourPapers.Universal.CoherentEquiv
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
 abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
instance palomarFaceVertexFintype (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _
 abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
 def polynomialRestriction {p q : P} (hqp : q ≤ p) : PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
 theorem polynomialRestriction_refl (p : P) : polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
 theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) : (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
  polynomialRestriction K (hrq.trans hqp) := by sorry
 abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
 abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] :=
  {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
 def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥
 theorem standardCarrier_le_iff (hs : IsSimplicialPoset P) (a : StandardFaceIndex P) (p : P) : standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by sorry
 abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}
 abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) :=
  Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
 def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
 def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ :=
  a.val.sum (fun F n => n * faceRank F.val)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V]
 def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 def koszulExteriorWeight (d : ℕ) {i : ℕ} (s : Set.powersetCard (Fin d) i) : ℤ :=
  ∑ j ∈ s.val, rankWeight d (j.val + 1)
 def originalKoszulDegree {d i : ℕ} (a : OriginalKoszulIndex P d i) : ℕ :=
  standardOrdinaryDegree a.2 + koszulExteriorDegree a.1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
 def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q
 @[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
 def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a
 def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
 def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val
 theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P) {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) : faceEvaluation K r f = 0 :=
  by sorry
 def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) : FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
 theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p) (f : FaceRing K hs) : polynomialRestriction K hqp (faceRingEvaluation K hs p f) =
  faceRingEvaluation K hs q f := by sorry
 def faceRingSection : FaceRing K hs →ₗ[K] (polynomialDiagram (P := P) K).sections where
  toFun f := ⟨fun p => faceRingEvaluation K hs p f,
    fun p q hqp => faceRingEvaluation_naturality K hs hqp f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact map_add (faceRingEvaluation K hs p) f g
  map_smul' c f := by
    apply Subtype.ext
    funext p
    exact map_smul (faceRingEvaluation K hs p) c f
 def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ :=
  a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : stalkVertexSet p (subfaceOfVertexSet hs p s).val = s
  := by sorry
 def originalKoszulWeight (d : ℕ) {i : ℕ} (a : OriginalKoszulIndex P d i) : ℤ :=
  standardRankWeight d a.2 + koszulExteriorWeight d a.1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
 abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
 def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) : BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val =
        (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv
 theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P) (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p := by sorry
 theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P) (p : P) (q : NonzeroFace P) : q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by
  sorry
 theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
  BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
 theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) : IsChainExponent
  (a.comapDomain (booleanFaceInclusion hs p) (booleanFaceInclusion hs p).injective.injOn) := by sorry
 def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) : {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p),
    standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn,
    chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
 def coefficientStalk (p : P) : Submodule K (I →₀ K) :=
  Finsupp.supported K K {i | carrier i ≤ p}
 def coefficientRestriction {p q : P} (_hqp : q ≤ p) : coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q :=
  (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
    (coefficientStalk K carrier p).subtype
 @[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p) (x : coefficientStalk K carrier p) (i : I) : (coefficientRestriction K carrier hqp x).val i
  = if carrier i ≤ q then x.val i else 0 := by sorry
 abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]
 def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) =
      (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x
 def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K :=
  (x.val (carrier i)).val i
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
variable [Fintype P]
 def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)
 theorem coefficientAssembly_section (x : I →₀ K) : coefficientAssembly K carrier (coefficientSection K carrier x) = x := by sorry
 theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) : coefficientSection K carrier (coefficientAssembly K carrier x) = x := by
  sorry
 def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
 def sectionsFromCoherentCoefficients (D : ModuleDiagram K P) (e : CoherentEquiv D (coefficientDiagram K carrier)) : D.sections ≃ₗ[K] (I →₀ K) :=
  e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]
 def subsetExponent (F : Finset V) : V →₀ ℕ :=
  ∑ v ∈ F, Finsupp.single v 1
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
 def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)
 def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)
 def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V :=
  ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩
 def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ :=
  ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1
 theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by sorry
 theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by sorry
 theorem chainVertexMap_chain_injective : Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} => chainVertexMap a.val) := by sorry
 def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {W : Type*} [Fintype W] [DecidableEq W]
 def chainVertexEquivUnordered : {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
variable {K}
 def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) : StandardInside p ≃ (FaceVertex p →₀ ℕ) :=
  (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered
 def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) : Module.Basis (StandardInside p) K (PolynomialStalk K p) :=
  (MvPolynomial.basisMonomials (FaceVertex p) K).reindex (standardVertexEquiv hs p).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
 def polynomialStandardCoordinates (p : P) : PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p :=
  (polynomialStandardBasis (K := K) hs p).repr.trans
    (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
 theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) : coefficientRestriction K standardCarrier hqp
  (polynomialStandardCoordinates K hs p f) = polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by sorry
 def polynomialCoefficientEquiv : CoherentEquiv (polynomialDiagram (P := P) K) (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f
 def polynomialSectionCoordinates : (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  sectionsFromCoherentCoefficients K standardCarrier (polynomialDiagram K)
    (polynomialCoefficientEquiv K hs)
 def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs :=
  Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)
 theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by sorry
 theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) : polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K
  hs x)) = x := by sorry
 def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h,
      standardFaceCombination_surjective K hs⟩).symm
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
 structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CommAlg
universe u v
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
 def augmentedFaceBoundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Simplicial.Chains (k := K) Λ (i + 1) →ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains Λ (i + 1))).codRestrict _
    (fun x => Simplicial.boundary_mem hΛ x.property)
 def rankSelection {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Finset V → Prop := fun F => D.face F ∧ F.image D.color ⊆ S
 theorem rankSelection_downward {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Simplicial.Downward (rankSelection D S) := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
 def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm
end FourPapers.Universal
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K : Type*} [CommRing K]
 structure Filtration (M : Type*) [AddCommGroup M] [Module K M] where
  level : ℕ → Submodule K M
  zero : level 0 = ⊥
  mono : Monotone level
  exhaustive : ∀ x : M, ∃ n, x ∈ level n
end FourPapers.FilteredHomology
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K : Type*} [CommRing K]
variable {X Y Z : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
 def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) :=
  (F.level n).comap (F.level (n + 1)).subtype
 abbrev Grade (F : Filtration (K := K) X) (n : ℕ) :=
  F.level (n + 1) ⧸ lowerInLevel F n
 def boundaryMap (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : X →ₗ[K] LinearMap.ker g :=
  f.codRestrict _ (fun x => LinearMap.congr_fun hfg x)
 abbrev Homology (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) :=
  LinearMap.ker g ⧸ LinearMap.range (boundaryMap f g hfg)
 def homologyClass (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : LinearMap.ker g →ₗ[K] Homology f g hfg := (LinearMap.range (boundaryMap f g hfg)).mkQ
 def cycleLevel (F : Filtration (K := K) Y) (g : Y →ₗ[K] Z) (n : ℕ) : Submodule K (LinearMap.ker g) := (F.level n).comap (LinearMap.ker g).subtype
 def homologyLevel (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) (n : ℕ) : Submodule K (Homology f g hfg) :=
  (cycleLevel F g n).map (homologyClass f g hfg)
 def homologyFiltration (F : Filtration (K := K) Y) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : Filtration (K := K) (Homology f g hfg) where
  level := homologyLevel F f g hfg
  zero := by simp [homologyLevel, cycleLevel, F.zero]
  mono := fun _ _ h => Submodule.map_mono (Submodule.comap_mono (F.mono h))
  exhaustive x := by
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    obtain ⟨n, hn⟩ := F.exhaustive z.val
    exact ⟨n, z, hn, rfl⟩
end FourPapers.FilteredHomology
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency false
open Classical
variable {K X Y Z : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
 def submoduleFiltration (F : Filtration (K := K) X) (N : Submodule K X) : Filtration (K := K) N where
  level n := (F.level n).comap N.subtype
  zero := by simp only [F.zero, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr N.injective_subtype]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val
 def restrictedMap (f : X →ₗ[K] Y) (N : Submodule K X) (M : Submodule K Y) (hNM : ∀ x, x ∈ N → f x ∈ M) : N →ₗ[K] M :=
  (f.domRestrict N).codRestrict M (fun x => hNM x.val x.property)
end FourPapers.FilteredHomology
namespace FourPapers.Universal.ProperlyColoredComplex
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {C : Type*} [LinearOrder C] [DecidableEq C]
variable {V : Type*} [Fintype V]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C)
 def colorLinearOrder : LinearOrder V :=
  LinearOrder.lift' (fun v => toLex (D.color v, (Fintype.equivFin V) v)) (by
    intro v w h
    apply (Fintype.equivFin V).injective
    exact congrArg (fun p => (ofLex p).2) h)
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.BasisGrading
set_option backward.isDefEq.respectTransparency false
open Classical
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
 def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M :=
  Submodule.span R (b '' {i | deg i = a})
end FourPapers.BasisGrading
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
 def basisFiltration (b : Module.Basis I K X) (w : I → ℕ) : Filtration (K := K) X where
  level n := Submodule.span K (b '' {i | w i < n})
  zero := by simp
  mono := by
    intro m n hmn
    apply Submodule.span_mono
    exact Set.image_mono (fun i hi => hi.trans_le hmn)
  exhaustive x := by
    refine ⟨(b.repr x).support.sup w + 1, ?_⟩
    rw [b.mem_span_image]
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup (f := w) hi)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory CommAlg
universe u v
variable {K B B' : Type u} {C : Type} [CommRing K] [CommRing B] [CommRing B'] [Algebra K B] [Algebra K B'] [Fintype C] [LinearOrder C]
 def parameterKoszulDifferential (γ : C → B) (i : ℕ) : (Set.powersetCard C (i + 1) →₀ B) →ₗ[K] (Set.powersetCard C i →₀ B) :=
  (Koszul.coordinateDifferential γ (ModuleCat.of B B) i).restrictScalars K
 theorem parameterKoszulDifferential_comp (γ : C → B) (i : ℕ) : (parameterKoszulDifferential (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ (i + 1))
  = 0 := by sorry
 def parameterKoszulComplex (γ : C → B) : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (Set.powersetCard C i →₀ B))
    (fun i => ModuleCat.ofHom (parameterKoszulDifferential (K := K) γ i))
    (fun i => ModuleCat.hom_ext (parameterKoszulDifferential_comp (K := K) γ i))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory CommAlg
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 abbrev originalKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
 def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) :=
  Finsupp.basis (fun _ => standardFaceBasis K hs)
 def originalKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ FaceRing K hs) :=
  basisFiltration (originalKoszulBasis K hs d i) (fun a => (originalKoszulWeight d a).toNat)
 def originalKoszulDegreePiece (i j : ℕ) :=
  FourPapers.BasisGrading.Piece (originalKoszulBasis K hs d i) originalKoszulDegree j
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 abbrev originalKoszulDifferential (i : ℕ) := parameterKoszulDifferential (K := K)
  (fun j : Fin d => faceRankParameter K hs (j.val + 1)) i
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
include hrank
 theorem originalKoszulDifferential_degree (i j : ℕ) (x : Set.powersetCard (Fin d) (i + 1) →₀ FaceRing K hs) (hx : x ∈ originalKoszulDegreePiece K hs d (i + 1)
  j) : originalKoszulDifferential K hs d i x ∈ originalKoszulDegreePiece K hs d i j := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 def originalKoszulDegreeDifferential (j i : ℕ) : originalKoszulDegreePiece K hs d (i + 1) j →ₗ[K] originalKoszulDegreePiece K hs d i j :=
  restrictedMap (originalKoszulDifferential K hs d i) _ _
    (originalKoszulDifferential_degree K hs d hrank i j)
 def originalKoszulDegreeComplex (j : ℕ) : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (originalKoszulDegreePiece K hs d i j))
    (fun i => ModuleCat.ofHom (originalKoszulDegreeDifferential K hs d hrank j i)) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (parameterKoszulDifferential_comp
        (K := K) (fun r : Fin d => faceRankParameter K hs (r.val + 1)) i) x.val)
 def originalDegreeTermFiltration (j i : ℕ) : Filtration (K := K) (originalKoszulDegreePiece K hs d i j) :=
  submoduleFiltration (originalKoszulFiltration K hs d i) (originalKoszulDegreePiece K hs d i j)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
 abbrev complexKernelHomology (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) :=
  Homology (complexIncoming C i) (complexOutgoing C i) (complexIncomingOutgoing C i)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u
variable {K : Type u} [CommRing K]
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 abbrev originalInternalKoszulHomology (j i : ℕ) :=
  complexKernelHomology (originalKoszulDegreeComplex K hs d hrank j) i
 def originalInternalHomologyFiltration (j i : ℕ) : Filtration (K := K) (originalInternalKoszulHomology K hs d hrank j i) :=
  homologyFiltration (originalDegreeTermFiltration K hs d j i)
    (complexIncoming (originalKoszulDegreeComplex K hs d hrank j) i)
    (complexOutgoing (originalKoszulDegreeComplex K hs d hrank j) i)
    (complexIncomingOutgoing (originalKoszulDegreeComplex K hs d hrank j) i)
 theorem originalInternalHomologyFiltration_finite (j i : ℕ) : (originalInternalHomologyFiltration K hs d hrank j i).level (2 * d * j + 1) = ⊤ := by sorry
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u
variable {K P : Type u} [CommRing K] [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
local instance originalParameterAlgebra : Algebra (MvPolynomial (Fin d) K) (FaceRing K hs) :=
  (faceParameterAction K hs d).toRingHom.toAlgebra
local instance originalParameterModule : Module (MvPolynomial (Fin d) K) (FaceRing K hs) :=
  @Algebra.toModule _ _ _ _ (originalParameterAlgebra K hs d)
 def originalParameterTor (m : ℕ) : ModuleCat.{u} K :=
  (ModuleCat.restrictScalars (algebraMap K (MvPolynomial (Fin d) K))).obj
    (((Tor (ModuleCat (MvPolynomial (Fin d) K)) m).obj
      (ModuleCat.of (MvPolynomial (Fin d) K) (FaceRing K hs))).obj
        (CommAlg.Koszul.residueCoefficientModule (V := Fin d) (k := K)))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
open Classical FourPapers.FilteredHomology
universe u v
variable {P K : Type u} {G : Type v} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 def rankSubsetDegree {d : ℕ} (S : Finset (Fin d)) : ℕ := ∑ r ∈ S, (r.val + 1)
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory CommAlg
universe u v
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
 def augmentedCoboundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Module.Dual K (Simplicial.Chains (k := K) Λ i) →ₗ[K] Module.Dual K (Simplicial.Chains (k := K) Λ (i + 1)) :=
  (augmentedFaceBoundary Λ hΛ i).dualMap
 theorem augmentedCoboundary_square (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : (augmentedCoboundary (K := K) Λ hΛ (i + 1)).comp
  (augmentedCoboundary (K := K) Λ hΛ i) = 0 := by sorry
 def augmentedCochainComplex (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) : CochainComplex (ModuleCat.{max u v} K) ℕ :=
  CochainComplex.of
    (fun i => ModuleCat.of K (Module.Dual K (Simplicial.Chains (k := K) Λ i)))
    (fun i => ModuleCat.ofHom (augmentedCoboundary Λ hΛ i))
    (fun i => ModuleCat.hom_ext (augmentedCoboundary_square Λ hΛ i))
 def reducedCohomology (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (q : ℤ) : ModuleCat.{max u v} K :=
  if -1 ≤ q then (augmentedCochainComplex (K := K) Λ hΛ).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
end FourPapers.Universal
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 abbrev rankSelectedCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedCohomology (K := K) (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    ((S.card : ℤ) - i - 1)
end FourPapers.Universal
namespace PalomarBarycentricTor
open Classical CategoryTheory FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [Field K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
 theorem actualDerivedTorComparison (i : ℕ) : Nonempty (originalParameterTor K hs d i ≅ (originalKoszulComplex K hs d).homology i) := by sorry
 theorem associatedGraded (j i : ℕ) : Nonempty ((⨁ n, Grade (originalInternalHomologyFiltration K hs d hrank j i) n) ≃ₗ[K] (⨁ (S : {S : Finset (Fin d) //
  rankSubsetDegree S = j}), rankSelectedCohomology K hs d hrank S.val i)) := by sorry
end PalomarBarycentricTor
namespace PalomarDiagnostic
partial def parents (e : Lean.Expr) : StateM (Nat × Array Lean.Json) Unit := do
  let (fuel, rows) ← get
  if fuel == 0 || rows.size >= 16 then return
  set (fuel - 1, rows)
  let args := e.getAppArgs
  let wanted := #[`FourPapers.Universal.complexIncoming._proof_1, `FourPapers.Universal.originalKoszulDegreeComplex._proof_2]
  if args.any (fun a => wanted.any (fun n => a.getAppFn.isConstOf n)) then
    let head := match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant"
    let heads := args.map fun a => match a.getAppFn with | .const n _ => n.toString | .bvar i => "bvar" ++ toString i | _ => "other"
    modify fun (f, rs) => (f, rs.push (Lean.Json.mkObj [("parent", Lean.toJson head), ("argument_heads", Lean.toJson heads)]))
  match e with
  | .app .. => for a in args do parents a
  | .lam _ t b _ | .forallE _ t b _ => parents t; parents b
  | .letE _ t v b _ => parents t; parents v; parents b
  | .mdata _ b | .proj _ _ b => parents b
  | _ => pure ()
end PalomarDiagnostic
run_cmd do
  for n in #[`FourPapers.Universal.complexIncoming, `FourPapers.Universal.originalKoszulDegreeComplex, `FourPapers.Universal.originalInternalHomologyFiltration] do
    if let some ci := (← Lean.getEnv).find? n then
      if let some v := ci.value? (allowOpaque := true) then
        let (_, (remaining, rows)) := (do PalomarDiagnostic.parents ci.type; PalomarDiagnostic.parents v).run (100000, #[])
        Lean.logInfo m!"{(Lean.Json.mkObj [("name", Lean.toJson n.toString), ("remaining", Lean.toJson remaining), ("parents", Lean.Json.arr rows)]).compress}"
