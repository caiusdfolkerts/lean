module

public import theorem13.PalomarPart001
import all theorem13.PalomarPart001
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false


-- Restore the original anonymous enclosing source scopes at this boundary.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedTactic false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
/- BEGIN FourPapers/Universal/StalkAutomorphisms.lean -/
section

section
/-! # Actual relabeling of face stalks

An order automorphism sends an actual vertex below `p` to an actual vertex
below its image.  The two stalk maps are variable renaming in the polynomial
ring and restriction along the inverse vertex bijection in the Boolean
face ring.  Their compatibility with restriction, rank parameters, and
ordinary degree is proved for these maps.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section VertexRelabeling
variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def booleanVertexRelabelEquiv (e : V ≃ W) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing W K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
        ext v
        exact e.apply_symm_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanVertexRelabelEquiv_refl (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (Equiv.refl V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanVertexRelabelEquiv_trans (e : V ≃ W) (f : W ≃ U)
    (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (e.trans f) x =
      booleanVertexRelabelEquiv f (booleanVertexRelabelEquiv e x) := by
  have he : (e.trans f).symm.toEmbedding = f.symm.toEmbedding.trans e.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e.trans f).symm.toEmbedding x =
    booleanRestriction f.symm.toEmbedding (booleanRestriction e.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    f.symm.toEmbedding e.symm.toEmbedding) x).symm

@[simp] theorem booleanVertexRelabelEquiv_parameter (e : V ≃ W) (r : ℕ) :
    booleanVertexRelabelEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

@[simp] theorem booleanVertexRelabelEquiv_face (e : V ≃ W) (F : BooleanFace V) :
    booleanVertexRelabelEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

theorem vertexDegree_finsupp_sum (a : V →₀ ℕ) :
    vertexDegree (fun v => a v) = a.sum (fun _ n => n) :=
  (Finsupp.sum_fintype a (fun _ n => n) (fun _ => rfl)).symm

theorem vertexDegree_mapDomain (f : V → W) (a : V →₀ ℕ) :
    vertexDegree (fun w => a.mapDomain f w) = vertexDegree (fun v => a v) := by
  rw [vertexDegree_finsupp_sum, vertexDegree_finsupp_sum,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem polynomialRename_degree (f : V → W) (n : ℕ)
    (x : MvPolynomial V K) (hx : x ∈ polynomialDegreePiece n) :
    MvPolynomial.rename f x ∈ polynomialDegreePiece n := by
  intro a ha
  apply MvPolynomial.coeff_rename_eq_zero f x a
  intro b hb
  apply hx b
  intro hd
  apply ha
  rw [← hb, vertexDegree_mapDomain, hd]

/-- The same rank-weighted ordinary degree as `chainOrdinaryDegree`, with no
auxiliary ordering of the vertex type required in its interface. -/
def booleanOrdinaryDegree [DecidableEq V] (a : BooleanFace V →₀ ℕ) : ℕ :=
  a.sum (fun F n => n * F.val.card)

theorem booleanOrdinaryDegree_eq_chainOrdinaryDegree [LinearOrder V]
    (a : BooleanFace V →₀ ℕ) : booleanOrdinaryDegree a = chainOrdinaryDegree a := rfl

theorem chainOrdinaryDegree_map_vertexEmbedding [DecidableEq V] [DecidableEq W] (e : V ↪ W)
    (a : BooleanFace V →₀ ℕ) :
    booleanOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = booleanOrdinaryDegree a := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanRestriction_degree (e : V ↪ W) (n : ℕ)
    (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanRestriction e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  rw [booleanRestriction_coefficient]
  apply hx
  change booleanOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e)) ≠ n
  rwa [chainOrdinaryDegree_map_vertexEmbedding]

theorem booleanVertexRelabelEquiv_degree (e : V ≃ W) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanVertexRelabelEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanRestriction_degree e.symm.toEmbedding n x hx

end VertexRelabeling

section Stalks
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

def faceVertexOrderEquiv (e : P ≃o P) (p : P) : FaceVertex p ≃ FaceVertex (e p) where
  toFun a := ⟨e a.val, (e.isAtom_iff a.val).mpr a.property.1, e.monotone a.property.2⟩
  invFun a := ⟨e.symm a.val, (e.symm.isAtom_iff a.val).mpr a.property.1,
    by simpa only [e.symm_apply_apply] using e.symm.monotone a.property.2⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)

@[simp] theorem faceVertexOrderEquiv_apply (e : P ≃o P) (p : P) (a : FaceVertex p) :
    (faceVertexOrderEquiv e p a).val = e a.val := rfl

@[simp] theorem faceVertexOrderEquiv_symm_apply (e : P ≃o P) (p : P)
    (a : FaceVertex (e p)) : ((faceVertexOrderEquiv e p).symm a).val = e.symm a.val := rfl

@[simp] theorem faceVertexOrderEquiv_refl (p : P) :
    faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl _ := by
  ext a
  rfl

theorem faceVertexOrderEquiv_trans (e f : P ≃o P) (p : P) :
    faceVertexOrderEquiv (e.trans f) p =
      (faceVertexOrderEquiv e p).trans (faceVertexOrderEquiv f (e p)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_inclusion (e : P ≃o P) {p q : P} (h : q ≤ p) :
    (faceVertexInclusion h).trans (faceVertexOrderEquiv e p).toEmbedding =
      (faceVertexOrderEquiv e q).toEmbedding.trans (faceVertexInclusion (e.monotone h)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_card (e : P ≃o P) (p : P) :
    Fintype.card (FaceVertex p) = Fintype.card (FaceVertex (e p)) :=
  Fintype.card_congr (faceVertexOrderEquiv e p)

variable (K : Type*) [CommRing K]

def polynomialStalkOrderEquiv (e : P ≃o P) (p : P) :
    PolynomialStalk K p ≃ₐ[K] PolynomialStalk K (e p) :=
  MvPolynomial.renameEquiv K (faceVertexOrderEquiv e p)

def barycentricStalkOrderEquiv (e : P ≃o P) (p : P) :
    BarycentricStalk K p ≃ₐ[K] BarycentricStalk K (e p) :=
  booleanVertexRelabelEquiv (faceVertexOrderEquiv e p)

@[simp] theorem polynomialStalkOrderEquiv_X (e : P ≃o P) (p : P) (a : FaceVertex p) :
    polynomialStalkOrderEquiv K e p (X a) = X (faceVertexOrderEquiv e p a) :=
  MvPolynomial.rename_X _ _

@[simp] theorem polynomialStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    polynomialStalkOrderEquiv K e p (polynomialParameter K p r) =
      polynomialParameter K (e p) r :=
  MvPolynomial.rename_esymm (σ := FaceVertex p) (R := K) r (faceVertexOrderEquiv e p)

@[simp] theorem barycentricStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    barycentricStalkOrderEquiv K e p (booleanRankParameter r) = booleanRankParameter r :=
  booleanVertexRelabelEquiv_parameter (faceVertexOrderEquiv e p) r

@[simp] theorem polynomialStalkOrderEquiv_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  simp only [polynomialStalkOrderEquiv, faceVertexOrderEquiv_refl, MvPolynomial.renameEquiv_refl,
    AlgEquiv.refl]
  rfl

@[simp] theorem barycentricStalkOrderEquiv_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (OrderIso.refl P) p) x = x
  have he : faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl (FaceVertex p) :=
    faceVertexOrderEquiv_refl p
  exact he.symm ▸ booleanVertexRelabelEquiv_refl x

theorem polynomialStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (e.trans f) p x =
      polynomialStalkOrderEquiv K f (e p) (polynomialStalkOrderEquiv K e p x) := by
  rw [polynomialStalkOrderEquiv, faceVertexOrderEquiv_trans, ← MvPolynomial.renameEquiv_trans]
  rfl

theorem barycentricStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (e.trans f) p x =
      barycentricStalkOrderEquiv K f (e p) (barycentricStalkOrderEquiv K e p x) := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (e.trans f) p) x =
    booleanVertexRelabelEquiv (faceVertexOrderEquiv f (e p))
      (booleanVertexRelabelEquiv (faceVertexOrderEquiv e p) x)
  exact (faceVertexOrderEquiv_trans e f p).symm ▸
    booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexOrderEquiv f (e p)) x

theorem polynomialStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : PolynomialStalk K p) :
    polynomialRestriction K (e.monotone h) (polynomialStalkOrderEquiv K e p x) =
      polynomialStalkOrderEquiv K e q (polynomialRestriction K h x) := by
  have he : (polynomialRestriction K (e.monotone h)).comp
      (polynomialStalkOrderEquiv K e p).toAlgHom =
      (polynomialStalkOrderEquiv K e q).toAlgHom.comp (polynomialRestriction K h) := by
    apply MvPolynomial.algHom_ext
    intro a
    by_cases hq : a.val ≤ q
    · have haq : e a.val ≤ e q := e.monotone hq
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_pos hq, dif_pos haq]
      rfl
    · have haq : ¬ e a.val ≤ e q := fun h' => hq (e.le_iff_le.mp h')
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_neg hq, dif_neg haq, map_zero]
  exact DFunLike.congr_fun he x

theorem barycentricStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : BarycentricStalk K p) :
    booleanRestriction (faceVertexInclusion (e.monotone h)) (barycentricStalkOrderEquiv K e p x) =
      barycentricStalkOrderEquiv K e q (booleanRestriction (faceVertexInclusion h) x) := by
  have he : (faceVertexInclusion (e.monotone h)).trans (faceVertexOrderEquiv e p).symm.toEmbedding =
      (faceVertexOrderEquiv e q).symm.toEmbedding.trans (faceVertexInclusion h) := by
    ext a
    rfl
  change booleanRestriction (faceVertexInclusion (e.monotone h))
      (booleanRestriction (faceVertexOrderEquiv e p).symm.toEmbedding x) =
    booleanRestriction (faceVertexOrderEquiv e q).symm.toEmbedding
      (booleanRestriction (faceVertexInclusion h) x)
  calc
    _ = booleanRestriction ((faceVertexInclusion (e.monotone h)).trans
        (faceVertexOrderEquiv e p).symm.toEmbedding) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction ((faceVertexOrderEquiv e q).symm.toEmbedding.trans
        (faceVertexInclusion h)) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

theorem polynomialStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K p) (hx : x ∈ polynomialDegreePiece n) :
    polynomialStalkOrderEquiv K e p x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p) n x hx

theorem barycentricStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricStalkOrderEquiv K e p x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanVertexRelabelEquiv_degree (faceVertexOrderEquiv e p) n x hx

end Stalks
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/StalkGradingBridge.lean -/
section

section
/-! # Ordinary grading and the existing stalk standard coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

/-- Retain a specified equality procedure when choosing an auxiliary order.
Only the comparison proof changes; the equality field is literally `d`. -/
def linearOrderWithDecidableEq {α : Type*} (o : LinearOrder α) (d : DecidableEq α) :
    LinearOrder α :=
  { o with
    toDecidableEq := d
    compare_eq_compareOfLessAndEq := by
      intro a b
      have hd : d = o.toDecidableEq := Subsingleton.elim _ _
      cases hd
      exact o.compare_eq_compareOfLessAndEq a b }

section Basis
variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
theorem scalarOrdinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]

end Basis
section Stalk
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (hs : IsSimplicialPoset P)
/-- Standard-coordinate homogeneity is ordinary homogeneity in the literal
polynomial and chain-monomial bases. -/
theorem ordinaryDegree_of_hasStandardDegree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : HasStandardDegree K hs p f) :
    ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n := by
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  have hb (u : BooleanChainExponent (FaceVertex p)) :
      f (booleanChainBasis u) ∈ polynomialDegreePiece (chainOrdinaryDegree u.val) := by
    intro a ha
    let v : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm a
    have hv : chainVertexMap v.val = a := chainVertexEquiv.apply_symm_apply a
    have hd : standardOrdinaryDegree ((standardInsideEquiv hs p) v).val ≠
        standardOrdinaryDegree ((standardInsideEquiv hs p) u).val := by
      rw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside,
        ← vertexDegree_eq_chainOrdinaryDegree, hv]
      exact ha
    have h := hf ((standardInsideEquiv hs p) u) ((standardInsideEquiv hs p) v).val hd
    rw [barycentricStalkStandardBasis_local,
      polynomialStandardCoordinates_chain, hv] at h
    exact h
  intro n x hx
  rw [← (booleanChainBasis (V := FaceVertex p) (K := K)).linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply (polynomialDegreePiece n).sum_mem
  intro u hu
  rw [map_smul]
  apply (polynomialDegreePiece n).smul_mem
  have hd : booleanOrdinaryDegree u.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hu (hx u hn)
  change chainOrdinaryDegree u.val = n at hd
  exact hd ▸ hb u

end Stalk
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkFamilies.lean -/
section


section

/-! # Linear families on the actual face stalks

All family operations act on genuine Boolean and polynomial stalk maps.
Relabeling uses the inverse order automorphism at the target face, avoiding
arbitrary identifications of vertex sets.  Coherence is an actual restriction
square, and the parameter and degree conditions are the original ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

abbrev StalkLinearFamily := ∀ p : P, BarycentricStalk K p →ₗ[K] PolynomialStalk K p

structure CoherentLinearMap (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p →ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)

def CoherentLinearMap.sectionMap {D E : ModuleDiagram K P} (f : CoherentLinearMap K D E) :
    D.sections →ₗ[K] E.sections where
  toFun x := ⟨fun p => f.component p (x.val p), by
    intro p q h
    rw [f.naturality, x.property p q h]⟩
  map_add' x y := by apply Subtype.ext; funext p; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; funext p; exact map_smul _ _ _

def stalkFamilyRelabel (e : P ≃o P) :
    StalkLinearFamily (P := P) K →ₗ[K] StalkLinearFamily (P := P) K where
  toFun F p := (polynomialStalkOrderEquiv K e.symm p).symm.toLinearMap.comp
    ((F (e.symm p)).comp (barycentricStalkOrderEquiv K e.symm p).toLinearMap)
  map_add' F H := by funext p; apply LinearMap.ext; intro x; simp
  map_smul' c F := by funext p; apply LinearMap.ext; intro x; simp

@[simp] theorem stalkFamilyRelabel_apply (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (p : P) (x : BarycentricStalk K p) :
    stalkFamilyRelabel K e F p x = (polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)) := rfl

theorem polynomialStalkOrderEquiv_trans_symm (e f : P ≃o P) (p : P)
    (x : PolynomialStalk K ((e.trans f) p)) :
    (polynomialStalkOrderEquiv K (e.trans f) p).symm x =
      (polynomialStalkOrderEquiv K e p).symm
        ((polynomialStalkOrderEquiv K f (e p)).symm x) := by
  apply (polynomialStalkOrderEquiv K (e.trans f) p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_trans,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

@[simp] theorem stalkFamilyRelabel_refl (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (OrderIso.refl P) F = F := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (OrderIso.refl P) p).symm
    (F p (barycentricStalkOrderEquiv K (OrderIso.refl P) p x)) = F p x
  apply (polynomialStalkOrderEquiv K (OrderIso.refl P) p).injective
  rw [AlgEquiv.apply_symm_apply, barycentricStalkOrderEquiv_refl,
    polynomialStalkOrderEquiv_refl]

theorem stalkFamilyRelabel_trans (e f : P ≃o P) (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (e.trans f) F = stalkFamilyRelabel K f (stalkFamilyRelabel K e F) := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (f.symm.trans e.symm) p).symm
      (F (e.symm (f.symm p)) (barycentricStalkOrderEquiv K (f.symm.trans e.symm) p x)) = _
  rw [polynomialStalkOrderEquiv_trans_symm, barycentricStalkOrderEquiv_trans]
  rfl

def coherentStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p q (h : q ≤ p) x,
    polynomialRestriction K h (F p x) = F q (booleanRestriction (faceVertexInclusion h) x)}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p q h x
    change polynomialRestriction K h (F p x + H p x) = _
    rw [map_add, hF, hH]
    rfl
  smul_mem' := by
    intro c F hF p q h x
    change polynomialRestriction K h (c • F p x) = _
    rw [map_smul, hF]
    rfl

def parameterStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p r x, F p (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * F p x}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p r x
    change F p (booleanRankParameter (r + 1) * x) + H p (booleanRankParameter (r + 1) * x) =
      polynomialParameter K p (r + 1) * (F p x + H p x)
    rw [hF, hH, mul_add]
  smul_mem' := by
    intro c F hF p r x
    change c • F p _ = polynomialParameter K p (r + 1) * (c • F p x)
    rw [hF, mul_smul_comm]

def gradedStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n → F p x ∈ polynomialDegreePiece n}
  zero_mem' := by intro p n x hx; exact (polynomialDegreePiece n).zero_mem
  add_mem' := by intro F H hF hH p n x hx; exact (polynomialDegreePiece n).add_mem (hF p n x hx) (hH p n x hx)
  smul_mem' := by intro c F hF p n x hx; exact (polynomialDegreePiece n).smul_mem c (hF p n x hx)

def coherentGradedParameterStalkFamilies : Submodule K (StalkLinearFamily (P := P) K) :=
  coherentStalkFamilySubmodule K ⊓ (parameterStalkFamilySubmodule K ⊓ gradedStalkFamilySubmodule K)

theorem polynomialStalkOrderEquiv_symm_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    (polynomialStalkOrderEquiv K e p).symm (polynomialParameter K (e p) r) =
      polynomialParameter K p r := by
  apply (polynomialStalkOrderEquiv K e p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_parameter]

theorem polynomialStalkOrderEquiv_symm_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K (e p)) (hx : x ∈ polynomialDegreePiece n) :
    (polynomialStalkOrderEquiv K e p).symm x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p).symm n x hx

theorem stalkFamilyRelabel_parameter (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ parameterStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ parameterStalkFamilySubmodule K := by
  intro p r x
  rw [stalkFamilyRelabel_apply, map_mul, barycentricStalkOrderEquiv_parameter,
    hF, map_mul, polynomialStalkOrderEquiv_symm_parameter]
  rfl

theorem stalkFamilyRelabel_graded (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ gradedStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  exact polynomialStalkOrderEquiv_symm_degree K e.symm p n _
    (hF (e.symm p) n _ (barycentricStalkOrderEquiv_degree K e.symm p n x hx))

theorem stalkFamilyRelabel_coherent (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  apply (polynomialStalkOrderEquiv K e.symm q).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))
  change polynomialStalkOrderEquiv K e.symm q
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm p).symm
        (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))) =
    polynomialStalkOrderEquiv K e.symm q
      ((polynomialStalkOrderEquiv K e.symm q).symm
        (F (e.symm q) (barycentricStalkOrderEquiv K e.symm q
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hF,
    barycentricStalkOrderEquiv_restriction]

theorem stalkFamilyRelabel_normalized (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (c : K) (hF : ∀ p, F p 1 = MvPolynomial.C c) :
    ∀ p, stalkFamilyRelabel K e F p 1 = MvPolynomial.C c := by
  intro p
  rw [stalkFamilyRelabel_apply, map_one, hF]
  exact (polynomialStalkOrderEquiv K e.symm p).symm.commutes c

section Action
variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def stalkFamilyRepresentation : CyclicRepresentation K G (StalkLinearFamily (P := P) K) where
  toFun g := stalkFamilyRelabel K (act g)
  map_one' := by
    apply LinearMap.ext
    intro F
    rw [h₁, stalkFamilyRelabel_refl]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    rw [hmul, stalkFamilyRelabel_trans]
    rfl

def representationMulAction {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : CyclicRepresentation A G M) : MulAction G M where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [ρ.map_one]; rfl
  mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); rw [ρ.map_mul]; rfl

end Action
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkInduction.lean -/
section


section

/-! # Orbitwise induction for actual coherent stalk maps

The generic orbit choice is applied to families supported at one face.  A
rank stage therefore stores actual maps on exactly the previously constructed
stalks.  Its boundary map is obtained by reading those components, and the
compatibility predicate is the genuine restriction equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def stalkFamilySingle (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    StalkLinearFamily (P := P) K := Pi.single p f

@[simp] theorem stalkFamilySingle_same (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f p = f := by simp [stalkFamilySingle]

@[simp] theorem stalkFamilySingle_ne (p q : P) (h : q ≠ p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f q = 0 := by simp [stalkFamilySingle, h]

theorem stalkFamilySingle_eq_of_supported (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : ∀ q, q ≠ p → F q = 0) : stalkFamilySingle K p (F p) = F := by
  funext q
  by_cases hq : q = p
  · subst q
    exact stalkFamilySingle_same K p (F p)
  · rw [stalkFamilySingle_ne K p q hq, hF q hq]

def StalkLocalGood (p : P) (F : StalkLinearFamily (P := P) K) : Prop :=
  (∀ q, q ≠ p → F q = 0) ∧ F ∈ parameterStalkFamilySubmodule K ∧
    F ∈ gradedStalkFamilySubmodule K ∧ F p 1 = 1

def StalkLocalCompatible (p q : P) (F H : StalkLinearFamily (P := P) K) : Prop :=
  ∀ (h : q ≤ p) x, polynomialRestriction K h (F p x) =
    H q (booleanRestriction (faceVertexInclusion h) x)

theorem stalkFamilySingle_good (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hp : ∀ r x, f (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * f x)
    (hd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (h₁ : f 1 = 1) : StalkLocalGood K p (stalkFamilySingle K p f) := by
  refine ⟨fun q hq => stalkFamilySingle_ne K p q hq f, ?_, ?_, ?_⟩
  · intro q r x
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hp r x
    · rw [stalkFamilySingle_ne K p q hq f]
      simp
  · intro q n x hx
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hd n x hx
    · rw [stalkFamilySingle_ne K p q hq f]
      exact (polynomialDegreePiece n).zero_mem
  · simpa only [stalkFamilySingle_same] using h₁

theorem stalkFamilyRelabel_good (e : P ≃o P) (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K p F) :
    StalkLocalGood K (e p) (stalkFamilyRelabel K e F) := by
  refine ⟨?_, stalkFamilyRelabel_parameter K e F hF.2.1,
    stalkFamilyRelabel_graded K e F hF.2.2.1, ?_⟩
  · intro q hq
    have hn : e.symm q ≠ p := by
      intro he
      exact hq ((e.apply_symm_apply q).symm.trans (congrArg e he))
    apply LinearMap.ext
    intro x
    rw [stalkFamilyRelabel_apply, hF.1 _ hn]
    simp
  · rw [stalkFamilyRelabel_apply, map_one]
    have hhq (q : P) (hq : q = p) : F q 1 = 1 := by
      subst q
      exact hF.2.2.2
    have hh : F (e.symm (e p)) 1 = 1 := hhq _ (e.symm_apply_apply p)
    rw [hh, map_one]

theorem stalkFamilyRelabel_compatible (e : P ≃o P) (p q : P)
    (F H : StalkLinearFamily (P := P) K) (hFH : StalkLocalCompatible K p q F H) :
    StalkLocalCompatible K (e p) (e q) (stalkFamilyRelabel K e F) (stalkFamilyRelabel K e H) := by
  intro h x
  apply (polynomialStalkOrderEquiv K e.symm (e q)).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm (e p)).symm
      (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))
  change polynomialStalkOrderEquiv K e.symm (e q)
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm (e p)).symm
        (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))) =
    polynomialStalkOrderEquiv K e.symm (e q)
      ((polynomialStalkOrderEquiv K e.symm (e q)).symm
        (H (e.symm (e q)) (barycentricStalkOrderEquiv K e.symm (e q)
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [← barycentricStalkOrderEquiv_restriction]
  have hh : StalkLocalCompatible K (e.symm (e p)) (e.symm (e q)) F H := by
    simpa only [e.symm_apply_apply] using hFH
  exact hh (e.symm.monotone h) _

section Stage

variable {G : Type*} [Group G] [MulAction G P] [MulAction G (StalkLinearFamily (P := P) K)]
variable (hs : IsSimplicialPoset P)
variable (hrank : ∀ (g : G) (p : P), faceRank (g • p) = faceRank p)

def EquivariantRankStage.stalkBoundary {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) :
    CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)) where
  component q := old.value ⟨q.val, by
    change faceRank q.val < n
    rw [← hp]
    exact faceRank_strictMono hs q.property⟩ q.val
  naturality q r h x := by
    by_cases he : r = q
    · subst r
      simp only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.toLinearMap_apply, AlgHom.id_apply]
    · have hlt : r.val < q.val := lt_of_le_of_ne h (fun h' => he (Subtype.ext h'))
      exact old.compatible
        ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩
        ⟨r.val, by change faceRank r.val < n; rw [← hp]; exact faceRank_strictMono hs r.property⟩
        hlt h x

theorem EquivariantRankStage.stalkBoundary_parameter {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (r : ℕ) (x : BarycentricStalk K q.val) :
    (old.stalkBoundary K hs hrank p hp).component q (booleanRankParameter (r + 1) * x) =
      polynomialParameter K q.val (r + 1) * (old.stalkBoundary K hs hrank p hp).component q x :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.1 q.val r x

theorem EquivariantRankStage.stalkBoundary_degree {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (m : ℕ) (x : BarycentricStalk K q.val)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m) :
    (old.stalkBoundary K hs hrank p hp).component q x ∈ polynomialDegreePiece m :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.1 q.val m x hx

theorem EquivariantRankStage.stalkBoundary_one {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) :
    (old.stalkBoundary K hs hrank p hp).component q 1 = 1 :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.2

end Stage

section ActualAction

variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def orderActionMulAction : MulAction G P where
  smul g p := act g p
  one_smul p := by change act 1 p = p; rw [h₁]; rfl
  mul_smul g h p := by change act (g * h) p = act g (act h p); rw [hmul]; rfl

theorem exists_equivariant_coherent_stalk_family (hs : IsSimplicialPoset P)
    (hlift :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      ∀ n (old : EquivariantRankStage faceRank
          (fun g p => faceRank_eq_of_orderIso (act g) p)
          (StalkLocalGood K) (StalkLocalCompatible K) n)
        (p : P), faceRank p = n → ∃ y : StalkLinearFamily (P := P) K,
          StalkLocalGood K p y ∧
          (∀ q : rankCut faceRank n, q.val < p →
            StalkLocalCompatible K p q.val y (old.value q)) ∧
          ∀ g : G, act g p = p → stalkFamilyRelabel K (act g) y = y) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧
      F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧
      (∀ p, F p 1 = 1) ∧ ∀ g : G, stalkFamilyRelabel K (act g) F = F := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  obtain ⟨f, hfg, hfc, hfe⟩ := exists_equivariant_rank_family faceRank
    (faceRank_strictMono hs) (fun g p => faceRank_eq_of_orderIso (act g) p)
    (fun g _ _ h => (act g).strictMono h)
    (StalkLocalGood K) (StalkLocalCompatible K)
    (fun g p y hy => stalkFamilyRelabel_good K (act g) p y hy)
    (fun g p q y z hy => stalkFamilyRelabel_compatible K (act g) p q y z hy)
    hlift
  let F : StalkLinearFamily (P := P) K := fun p => f p p
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h x
    by_cases he : q = p
    · subst q
      simpa only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
    · exact hfc p q (lt_of_le_of_ne h he) h x
  · intro p r x
    exact (hfg p).2.1 p r x
  · intro p n x hx
    exact (hfg p).2.2.1 p n x hx
  · intro p
    exact (hfg p).2.2.2
  · intro g
    funext p
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun z : StalkLinearFamily (P := P) K => z p x)
      (hfe g ((act g).symm p))
    change f (act g ((act g).symm p)) p x =
      stalkFamilyRelabel K (act g) (f ((act g).symm p)) p x at hh
    rw [(act g).apply_symm_apply] at hh
    exact hh.symm

end ActualAction
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicConstantStalk.lean -/
section


section

/-! # The normalized constant stalk

The empty face has no vertices, so its actual Boolean stalk is generated by
the constant element over the coefficient ring.  A normalized linear map is
therefore unique; equivariance at the constant stalk requires no averaging.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical Finset MvPolynomial

section Empty
variable {V K : Type*} [Fintype V] [CommRing K] [IsEmpty V]

theorem boolean_empty_exists_smul_one (x : BooleanBarycentricRing V K) :
    ∃ c : K, c • (1 : BooleanBarycentricRing V K) = x := by
  letI : IsEmpty (BooleanFace V) := ⟨fun F => by
    obtain ⟨v, hv⟩ := F.property
    exact isEmptyElim v⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (BooleanFace V) a
  refine ⟨c, ?_⟩
  let q := Ideal.Quotient.mkₐ K (forbiddenIdeal (K := K) (IsChainExponent (V := V)))
  calc
    c • (1 : BooleanBarycentricRing V K) = c • q 1 := by rw [map_one]
    _ = q (c • (1 : MvPolynomial (BooleanFace V) K)) := (map_smul q c 1).symm
    _ = q (MvPolynomial.C c) := by rw [Algebra.smul_def, mul_one]; rfl
    _ = _ := rfl

theorem boolean_empty_linear_ext_one {N : Type*} [AddCommGroup N] [Module K N]
    (f g : BooleanBarycentricRing V K →ₗ[K] N) (h : f 1 = g 1) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := boolean_empty_exists_smul_one x
  rw [map_smul, map_smul, h]

end Empty

section Canonical
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem canonicalBooleanPolynomial_one : canonicalBooleanPolynomial (V := V) (K := K) 1 = 1 := by
  have hzero : booleanChainBasis (K := K) (⟨0, isChainExponent_zero⟩ : BooleanChainExponent V) = 1 := by
    rw [booleanChainBasis, standardMonomialBasis_apply]
    simp
  rw [← hzero, canonicalBooleanPolynomial_basis]
  have hchain : chainVertexMap (0 : BooleanFace V →₀ ℕ) = 0 := by
    ext v
    simp [chainVertexMap, chainVertexMapUnordered]
  rw [hchain]
  simp

theorem canonicalBooleanPolynomial_degree (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n) :
    canonicalBooleanPolynomial x ∈ polynomialDegreePiece n := by
  intro a ha
  let c : BooleanChainExponent V := chainVertexEquiv.symm a
  have hc : chainVertexMap c.val = a := chainVertexEquiv.apply_symm_apply a
  rw [← hc, canonicalBooleanPolynomial_coefficient]
  apply hx c
  change chainOrdinaryDegree c.val ≠ n
  rw [← vertexDegree_eq_chainOrdinaryDegree, hc]
  exact ha

end Canonical

section Stalk
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def emptyFaceVertex : IsEmpty (FaceVertex (⊥ : P)) := ⟨fun v =>
  v.property.1.ne_bot (le_bot_iff.mp v.property.2)⟩

theorem stalkLocalGood_bot_unique (F H : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K ⊥ F) (hH : StalkLocalGood K ⊥ H) : F = H := by
  letI := emptyFaceVertex (P := P)
  funext p
  by_cases hp : p = ⊥
  · subst p
    exact boolean_empty_linear_ext_one _ _ (hF.2.2.2.trans hH.2.2.2.symm)
  · rw [hF.1 p hp, hH.1 p hp]

theorem stalkLocalGood_bot_fixed (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K ⊥ F) : stalkFamilyRelabel K e F = F := by
  apply stalkLocalGood_bot_unique K _ F _ hF
  have hh := stalkFamilyRelabel_good K e ⊥ F hF
  simpa only [e.map_bot] using hh

theorem exists_stalkLocalGood_bot : ∃ F : StalkLinearFamily (P := P) K, StalkLocalGood K ⊥ F := by
  letI := emptyFaceVertex (P := P)
  letI : LinearOrder (FaceVertex (⊥ : P)) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex (⊥ : P)))
      (Fintype.equivFin (FaceVertex (⊥ : P))).injective
  let f : BarycentricStalk K (⊥ : P) →ₗ[K] PolynomialStalk K ⊥ :=
    canonicalBooleanPolynomial.toLinearMap
  refine ⟨stalkFamilySingle K ⊥ f, stalkFamilySingle_good K ⊥ f ?_
    (canonicalBooleanPolynomial_degree) canonicalBooleanPolynomial_one⟩
  intro r x
  have hr : Fintype.card (FaceVertex (⊥ : P)) < r + 1 := by simp
  rw [booleanRankParameter_above _ hr, zero_mul, map_zero,
    polynomialParameter, esymm_above_card _ hr, zero_mul]

end Stalk
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCoherentBoundaryLift.lean -/
section

section
/-! # Ordinary graded extensions of coherent boundary maps

The input is a coherent family of actual linear maps, without any assumption
of invertibility.  The correction uses the established section of the genuine
proper-face restriction map.  Extending its values on the actual descent
basis gives a parameter-linear map with the prescribed restrictions.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def linearCoherentBoundaryCorrection (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  (polynomialCarrierBoundaryExtension K hs p).comp
    ((e.sectionMap K).comp (stalkBoundaryRestriction (barycentricDiagram K) p))

theorem linearCoherentBoundaryCorrection_restrict (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p
      (linearCoherentBoundaryCorrection K hs p e x) =
      e.sectionMap K (stalkBoundaryRestriction (barycentricDiagram K) p x) :=
  polynomialCarrierBoundaryExtension_restrict K hs p _

theorem linearCoherentBoundaryCorrection_coefficient (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p)
    (b : StandardFaceIndex P) :
    (polynomialStandardCoordinates K hs p (linearCoherentBoundaryCorrection K hs p e x)).val b =
      if hb : standardCarrier b < p then
        (polynomialStandardCoordinates K hs (standardCarrier b)
          (e.component ⟨standardCarrier b, hb⟩
            (booleanRestriction (faceVertexInclusion hb.le) x))).val b else 0 := by
  unfold linearCoherentBoundaryCorrection polynomialCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem linearCoherentBoundaryCorrection_standard_degree (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentBoundaryCorrection K hs p e) := by
  intro a b hab
  rw [linearCoherentBoundaryCorrection_coefficient]
  by_cases hb : standardCarrier b < p
  · rw [dif_pos hb]
    have hres := barycentricStandardCoordinates_naturality K hs hb.le
      (barycentricStalkStandardBasis K hs p a)
    rw [barycentricStandardCoordinates_basis, coefficientRestriction_unit] at hres
    by_cases ha : standardCarrier a.val ≤ standardCarrier b
    · rw [dif_pos ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) =
            barycentricStalkStandardBasis K hs (standardCarrier b) ⟨a.val, ha⟩ := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, barycentricStandardCoordinates_basis]
      rw [hval]
      exact he ⟨standardCarrier b, hb⟩ ⟨a.val, ha⟩ b hab
    · rw [dif_neg ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) = 0 := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, map_zero]
      rw [hval, map_zero, map_zero]
      rfl
  · rw [dif_neg hb]

variable (p : P) [LinearOrder (FaceVertex p)]

def linearCoherentLocalExtension
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  exact ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))).restrictScalars K

@[simp] theorem linearCoherentLocalExtension_basis
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) =
      linearCoherentBoundaryCorrection K hs p e (descentVector σ) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  change ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ))) (descentVector σ) = _
  simpa only [booleanColorBasis_apply] using
    (Module.Basis.constr_basis (booleanColorBasis (V := FaceVertex p) (K := K))
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ)) σ)

theorem linearCoherentLocalExtension_parameter_mul
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IsParameterLinear booleanColorMap polynomialColorMap (linearCoherentLocalExtension K hs p e) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  let f :=
    (booleanColorBasis (V := FaceVertex p) (K := K)).constr
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))
  intro a x
  change f (booleanColorMap a * x) = polynomialColorMap a * f x
  exact f.map_smul a x

theorem linearCoherentLocalExtension_intertwinesAllRanks
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IntertwinesAllRanks (linearCoherentLocalExtension K hs p e) :=
  parameterLinear_intertwinesAllRanks _ (linearCoherentLocalExtension_parameter_mul K hs p e)

set_option backward.isDefEq.respectTransparency false in
theorem linearCoherentLocalExtension_naturality
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q ((booleanRankParameter (V := FaceVertex q.val) (K := K) (i + 1)) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (q : Set.Iio p) (x : BarycentricStalk K p) :
    polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x) := by
  let F : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (polynomialRestriction K q.property.le).toLinearMap.comp (linearCoherentLocalExtension K hs p e)
  let G : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (e.component q).comp
      (booleanRestriction (K := K) (faceVertexInclusion q.property.le)).toLinearMap
  have hF : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change polynomialRestriction K q.property.le
      (linearCoherentLocalExtension K hs p e (booleanColorMap (X c) * z)) = _
    erw [linearCoherentLocalExtension_parameter_mul K hs p e, map_mul]
    rw [polynomialColorMap, MvPolynomial.aeval_X,
      polynomialParameterMap, MvPolynomial.aeval_X]
    change polynomialRestriction K q.property.le
      (esymm (FaceVertex p) K (c.val + 1)) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z) =
      esymm (FaceVertex q.val) K (c.val + 1) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z)
    congr 1
    exact polynomialRestriction_parameter K q.property.le (c.val + 1)
  have hG : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) G := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change e.component q (booleanRestriction (faceVertexInclusion q.property.le)
      (booleanColorMap (X c) * z)) = _
    erw [map_mul]
    have hb : booleanRestriction (K := K) (faceVertexInclusion q.property.le)
        (booleanColorMap (X c)) = booleanRankParameter (c.val + 1) := by
      have hc : booleanColorMap (K := K) (X c) = colorSum c := by
        rw [booleanColorMap, MvPolynomial.aeval_X]
        rfl
      have hcol := hc.trans (booleanRankParameter_color (K := K) c).symm
      exact (congrArg (booleanRestriction (K := K) (faceVertexInclusion q.property.le)) hcol).trans
        (booleanRestriction_rankParameter (K := K) (faceVertexInclusion q.property.le) (c.val + 1))
    erw [hb]
    rw [polynomialParameterMap, MvPolynomial.aeval_X]
    change e.component q (booleanRankParameter (c.val + 1) *
      booleanRestriction (faceVertexInclusion q.property.le) z) =
      polynomialParameter K q.val (c.val + 1) *
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) z)
    exact he q c.val (booleanRestriction (faceVertexInclusion q.property.le) z)
  have hfg : F = G := parameterLinear_ext_descent
    (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F G hF hG (by
      intro σ
      change polynomialRestriction K q.property.le
        (linearCoherentLocalExtension K hs p e (descentVector σ)) = _
      rw [linearCoherentLocalExtension_basis]
      have h := congrArg (fun y : ((polynomialDiagram K).restrict (Set.Iio p)).sections => y.val q)
        (linearCoherentBoundaryCorrection_restrict K hs p e (descentVector σ))
      exact h)
  exact DFunLike.congr_fun hfg x

variable {p}

theorem linearCoherentLocalExtension_descent_degree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  intro b hb
  let a := descentChainIndex σ
  let c : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm b
  have hcb : chainVertexMap c.val = b := chainVertexEquiv.apply_symm_apply b
  have hne : standardOrdinaryDegree ((standardInsideEquiv hs p) c).val ≠
      standardOrdinaryDegree ((standardInsideEquiv hs p) a).val := by
    erw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside, descentChainIndex_degree,
      ← vertexDegree_eq_chainOrdinaryDegree, hcb]
    exact hb
  have h := linearCoherentBoundaryCorrection_standard_degree K hs p e he
    ((standardInsideEquiv hs p) a) ((standardInsideEquiv hs p) c).val hne
  erw [barycentricStalkStandardBasis_local, ← descentVector_eq_chainBasis,
    polynomialStandardCoordinates_chain, hcb] at h
  change (linearCoherentLocalExtension K hs p e (descentVector σ)).coeff b = 0
  rw [linearCoherentLocalExtension_basis]
  exact h

theorem linearCoherentLocalExtension_hasStandardDegree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentLocalExtension K hs p e) := by
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := parameterLinear_chain_degree (linearCoherentLocalExtension K hs p e)
      (linearCoherentLocalExtension_parameter_mul K hs p e)
      (linearCoherentLocalExtension_descent_degree K hs p e he) u (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p
      (linearCoherentLocalExtension K hs p e (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p
        (linearCoherentLocalExtension K hs p e (barycentricStalkStandardBasis K hs p a))).property b hb

theorem linearCoherentLocalExtension_graded (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (n : ℕ) (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    linearCoherentLocalExtension K hs p e x ∈ polynomialDegreePiece n :=
  parameterLinear_ordinary_degree _ (linearCoherentLocalExtension_parameter_mul K hs p e)
    (linearCoherentLocalExtension_descent_degree K hs p e he) n x hx

theorem hasStandardDegree_of_ordinary_degree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) :
    HasStandardDegree K hs p f := by
  letI : LinearOrder (FaceVertex p) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := hf (chainOrdinaryDegree u.val) (booleanChainBasis u)
      (ordinaryBasis_mem_piece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) u)
      (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p (f (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).property b hb

theorem polynomialDegreePiece_zero_eq_C {V : Type*} [Fintype V]
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece 0) : f = MvPolynomial.C (f.coeff 0) := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  · rw [MvPolynomial.coeff_C_of_ne_zero ha]
    apply hf a
    intro hd
    apply ha
    ext v
    have hv : a v ≤ vertexDegree (fun w => a w) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    change a v = 0
    omega

/-- The ordinary extension has the same constant normalization as all its
proper-face components.  Positive rank supplies the proper bottom face. -/
theorem linearCoherentLocalExtension_normalized (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    linearCoherentLocalExtension K hs p e 1 = 1 := by
  let σ := weightOrdering (fun _ : FaceVertex p => 0)
  have hdes : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  have hdeg : colorOrdinaryDegree (descentColorExponent σ) = 0 := by
    rw [descentOrdinaryDegree_eq_zero_iff]
    exact weightOrdering_zero_no_descents
  have hdegree := linearCoherentLocalExtension_descent_degree K hs p e hegrade σ
  rw [hdes, hdeg] at hdegree
  have hC := polynomialDegreePiece_zero_eq_C K _ hdegree
  have hp : (⊥ : P) < p := by
    have hr : 0 < faceRank p := by
      rw [← card_faceVertex p]
      exact Fintype.card_pos
    apply bot_lt_iff_ne_bot.mpr
    intro he
    rw [he, faceRank_bot] at hr
    exact (Nat.lt_irrefl 0) hr
  let q : Set.Iio p := ⟨⊥, hp⟩
  have hn := linearCoherentLocalExtension_naturality K hs p e heparam q 1
  rw [hC] at hn
  simp only [polynomialRestriction_C, map_one, heone] at hn
  have hc' : (linearCoherentLocalExtension K hs p e 1).coeff 0 = 1 := by
    apply MvPolynomial.C_injective (FaceVertex (⊥ : P)) K
    exact hn.trans (MvPolynomial.C_1).symm
  rw [hC, hc', MvPolynomial.C_1]

include hs in
/-- A normalized graded parameter-linear extension of an arbitrary coherent
normalized graded boundary family.  This is the actual local choice needed
for the orbit induction; no boundary invertibility is assumed. -/
theorem exists_linearCoherentLocalExtension (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    ∃ f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p,
      IsParameterLinear booleanColorMap polynomialColorMap f ∧
      (∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) ∧ f 1 = 1 := by
  have hd : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q) :=
    fun q => hasStandardDegree_of_ordinary_degree K hs q.val (e.component q) (hegrade q)
  exact ⟨linearCoherentLocalExtension K hs p e,
    linearCoherentLocalExtension_parameter_mul K hs p e,
    linearCoherentLocalExtension_naturality K hs p e heparam,
    linearCoherentLocalExtension_graded K hs p e hd,
    linearCoherentLocalExtension_normalized K hs p e heparam hd heone⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SimplexTransportGeometry.lean -/
section

section
/-! # Literal finite-simplex vertex geometry

Shared exact declarations for finite-subset order isomorphisms, simplex
vertices, and finite embeddings. No cyclic lifting theorem is imported.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
section Simplex
variable {V W U : Type*} [Fintype V] [Fintype W] [Fintype U]

def finsetOrderCongr (e : V ≃ W) : Finset V ≃o Finset W :=
  { e.finsetCongr with map_rel_iff' := by intro s t; exact Finset.map_subset_map }

@[simp] theorem finsetOrderCongr_apply (e : V ≃ W) (s : Finset V) :
    finsetOrderCongr e s = s.map e.toEmbedding := rfl

@[simp] theorem finsetOrderCongr_refl : finsetOrderCongr (Equiv.refl V) = OrderIso.refl _ := by
  ext s
  simp

theorem finsetOrderCongr_trans (e : V ≃ W) (f : W ≃ U) :
    finsetOrderCongr (e.trans f) = (finsetOrderCongr e).trans (finsetOrderCongr f) := by
  apply OrderIso.ext
  funext s
  exact congrArg (fun t : Finset V ≃ Finset U => t s) (Equiv.finsetCongr_trans e f).symm

def simplexIntervalOrderEquiv (s : Finset V) : Set.Iic s ≃o Finset s where
  toFun t := t.val.subtype (fun v => v ∈ s)
  invFun t := ⟨t.map (Function.Embedding.subtype _), by
    intro v hv
    exact Finset.property_of_mem_map_subtype t hv⟩
  left_inv t := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun v hv => t.property hv)
  right_inv t := by
    ext v
    simp
  map_rel_iff' := by
    intro t u
    constructor
    · intro h v hv
      have hv' : (⟨v, t.property hv⟩ : s) ∈ t.val.subtype (fun v => v ∈ s) :=
        Finset.mem_subtype.mpr hv
      exact Finset.mem_subtype.mp (h hv')
    · intro h v hv
      exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hv))

theorem simplex_isSimplicialPoset : IsSimplicialPoset (Finset V) := by
  intro s
  exact ⟨Fintype.card s, ⟨(simplexIntervalOrderEquiv s).trans
    (finsetOrderCongr (Fintype.equivFin s))⟩⟩

def simplexAtomMap (s : Finset V) (v : s) : FaceVertex s :=
  ⟨{v.val}, Finset.isAtom_singleton v.val, Finset.singleton_subset_iff.mpr v.property⟩

theorem simplexAtomMap_bijective (s : Finset V) : Function.Bijective (simplexAtomMap s) := by
  constructor
  · intro v w h
    apply Subtype.ext
    have hh := congrArg (fun a : FaceVertex s => a.val) h
    exact Finset.singleton_injective hh
  · intro a
    obtain ⟨v, hv⟩ := Finset.isAtom_iff.mp a.property.1
    have hvs : v ∈ s := by
      apply a.property.2
      rw [hv]
      exact Finset.mem_singleton_self v
    refine ⟨⟨v, hvs⟩, ?_⟩
    apply Subtype.ext
    exact hv.symm

def simplexVertexEquiv (s : Finset V) : FaceVertex s ≃ s :=
  (Equiv.ofBijective (simplexAtomMap s) (simplexAtomMap_bijective s)).symm

@[simp] theorem simplexVertexEquiv_symm (s : Finset V) (v : s) :
    (simplexVertexEquiv s).symm v = simplexAtomMap s v := rfl

theorem simplex_faceRank (s : Finset V) : faceRank s = s.card := by
  rw [← card_faceVertex]
  exact (Fintype.card_congr (simplexVertexEquiv s)).trans (Fintype.card_coe s)

def simplexTopVertexEquiv : FaceVertex (Finset.univ : Finset V) ≃ V :=
  (simplexVertexEquiv Finset.univ).trans {
    toFun := Subtype.val
    invFun := fun v => ⟨v, Finset.mem_univ v⟩
    left_inv := fun v => Subtype.ext rfl
    right_inv := fun v => rfl }

theorem simplexOrderAction_one : finsetOrderCongr (1 : Equiv.Perm V) = OrderIso.refl _ :=
  finsetOrderCongr_refl

theorem simplexOrderAction_mul (e f : Equiv.Perm V) :
    finsetOrderCongr (e * f) = (finsetOrderCongr f).trans (finsetOrderCongr e) :=
  finsetOrderCongr_trans f e

@[simp] theorem finsetOrderCongr_univ (e : Equiv.Perm V) :
    finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ := by
  change Finset.univ.map e.toEmbedding = Finset.univ
  exact Finset.map_univ_equiv e

@[simp] theorem finsetOrderCongr_empty (e : Equiv.Perm V) :
    finsetOrderCongr e (∅ : Finset V) = ∅ := Finset.map_empty _

end Simplex

section Placements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

def embeddingPlacementFace (i : A ↪ V) : Finset V := Finset.univ.map i

def embeddingPlacementEquiv (i : A ↪ V) : A ≃ embeddingPlacementFace i :=
  Equiv.ofBijective (fun a => ⟨i a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
    ⟨fun a b h => i.injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp a.property
      exact ⟨b, Subtype.ext hb⟩⟩

def embeddingPlacementVertex (i : A ↪ V) : A ≃ FaceVertex (embeddingPlacementFace i) :=
  (embeddingPlacementEquiv i).trans (simplexVertexEquiv (embeddingPlacementFace i)).symm

@[simp] theorem embeddingPlacementVertex_val (i : A ↪ V) (a : A) :
    (embeddingPlacementVertex i a).val = {i a} := rfl

theorem finsetOrderCongr_symm (e : V ≃ V) :
    finsetOrderCongr e.symm = (finsetOrderCongr e).symm := rfl

end Placements
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSimplexGeometry.lean -/
section


section

/-! # The actual Boolean simplex and its prime-cycle action

Faces are literal finite subsets.  Their atoms are literal singleton subsets,
and the resulting simplicial-poset stalk vertices are identified with the
vertices of the subset.  Nonempty proper faces have trivial stabilizer under
a prime cycle.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable (p : ℕ) [Fact p.Prime]

def cyclicSimplexOrderAction (g : PrimeCycleGroup p) : Finset (ZMod p) ≃o Finset (ZMod p) :=
  finsetOrderCongr (cyclicVertexPermutation p g)

theorem cyclicSimplexOrderAction_one : cyclicSimplexOrderAction p 1 = OrderIso.refl _ := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_one]
  exact simplexOrderAction_one

theorem cyclicSimplexOrderAction_mul (g h : PrimeCycleGroup p) :
    cyclicSimplexOrderAction p (g * h) =
      (cyclicSimplexOrderAction p h).trans (cyclicSimplexOrderAction p g) := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_mul]
  exact simplexOrderAction_mul _ _

theorem cyclicSimplex_proper_face_free (s : Finset (ZMod p)) (hs : s.Nonempty)
    (ht : s ≠ Finset.univ) (g : PrimeCycleGroup p)
    (hfix : cyclicSimplexOrderAction p g s = s) : g = 1 := by
  by_contra hg
  have hg0 : g.toAdd ≠ 0 := by intro h; exact hg (congrArg Multiplicative.ofAdd h)
  have hmem : ∀ x : ZMod p, (g.toAdd + x ∈ s) = (x ∈ s) := by
    intro x
    have hh : s.map (Equiv.addLeft g.toAdd).toEmbedding = s := hfix
    have hm := congrArg (fun t : Finset (ZMod p) => (Equiv.addLeft g.toAdd) x ∈ t) hh
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hm
    exact hm.symm
  have hc := primeShift_invariant_constant p (fun x => x ∈ s) g.toAdd hg0 hmem
  obtain ⟨a, ha⟩ := hs
  apply ht
  apply Finset.eq_univ_iff_forall.mpr
  intro b
  rw [hc b, ← hc a]
  exact ha

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFreeFaceAssembly.lean -/
section


section

/-! # Integral coherent extension on free face orbits

Every nonempty proper face of a prime simplex has trivial stabilizer.  An
ordinary boundary extension on one representative therefore suffices on its
whole orbit.  This file packages that argument on the actual face diagrams;
only the stabilizer-fixed extension at the top face remains a separate input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

/-- Read a rank-stage value with its specified actions installed explicitly. -/
def actualRankStageValue (n : ℕ)
    (old :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
        (StalkLocalGood K) (StalkLocalCompatible K) n) :
    equivariantRankCut (fun p : P => faceRank p) n → StalkLinearFamily (P := P) K := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  exact old.value

include hs in
theorem exists_ordinary_rank_stalk_extension
    (n : ℕ)
    (old :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
        (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (hp₀ : p ≠ ⊥) :
    ∃ y : StalkLinearFamily (P := P) K, StalkLocalGood K p y ∧
      ∀ q : rankCut faceRank n, q.val < p → StalkLocalCompatible K p q.val y (actualRankStageValue K act h₁ hmul n old q) := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  have hcard : 0 < Fintype.card (FaceVertex p) := by
    rw [card_faceVertex]
    exact Finset.card_pos.mpr (faceVertices_nonempty hs hp₀)
  letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hcard
  let e := old.stalkBoundary K hs (fun g q => faceRank_eq_of_orderIso (act g) q) p hp
  obtain ⟨f, hfp, hfn, hfg, hf₁⟩ := exists_linearCoherentLocalExtension K hs p e
    (old.stalkBoundary_parameter K hs _ p hp)
    (old.stalkBoundary_degree K hs _ p hp)
    (old.stalkBoundary_one K hs _ p hp)
  refine ⟨stalkFamilySingle K p f,
    stalkFamilySingle_good K p f (parameterLinear_intertwinesAllRanks f hfp) hfg hf₁, ?_⟩
  intro q hqp h x
  rw [stalkFamilySingle_same]
  exact hfn ⟨q.val, hqp⟩ x

variable [OrderTop P]

include hs in
theorem exists_coherent_family_of_prime_top_extension
    (hfree : ∀ (p : P), p ≠ ⊥ → p ≠ ⊤ → ∀ g : G, act g p = p → g = 1)
    (htop :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      ∀ n (old : EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
          (StalkLocalGood K) (StalkLocalCompatible K) n), faceRank (⊤ : P) = n →
        ∃ y : StalkLinearFamily (P := P) K,
          StalkLocalGood K ⊤ y ∧
          (∀ q : rankCut faceRank n, q.val < ⊤ → StalkLocalCompatible K ⊤ q.val y (old.value q)) ∧
          ∀ g : G, stalkFamilyRelabel K (act g) y = y) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧
      F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧
      (∀ p, F p 1 = 1) ∧ ∀ g : G, stalkFamilyRelabel K (act g) F = F := by
  apply exists_equivariant_coherent_stalk_family K act h₁ hmul hs
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  intro n old p hp
  by_cases hp₀ : p = ⊥
  · subst p
    obtain ⟨y, hy⟩ := exists_stalkLocalGood_bot (P := P) K
    exact ⟨y, hy, fun q hq => False.elim (not_lt_bot hq),
      fun g _ => stalkLocalGood_bot_fixed K (act g) y hy⟩
  · by_cases hp₁ : p = ⊤
    · subst p
      obtain ⟨y, hy, hb, he⟩ := htop n old hp
      exact ⟨y, hy, hb, fun g _ => he g⟩
    · obtain ⟨y, hy, hb⟩ := exists_ordinary_rank_stalk_extension K hs act h₁ hmul n old p hp hp₀
      refine ⟨y, hy, hb, ?_⟩
      intro g hg
      rw [hfree p hp₀ hp₁ g hg, h₁, stalkFamilyRelabel_refl]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicVertexTransport.lean -/
section


section

/-! # Transport of actual local parameter maps along vertex bijections -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def vertexMapTransport (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    BooleanBarycentricRing W K →ₗ[K] MvPolynomial W K :=
  (MvPolynomial.rename e).toLinearMap.comp
    (f.comp (booleanVertexRelabelEquiv (K := K) e.symm).toLinearMap)

@[simp] theorem vertexMapTransport_apply (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (x : BooleanBarycentricRing W K) :
    vertexMapTransport e f x = MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm x)) := rfl

theorem intertwinesAllRanks_parameterLinear [LinearOrder V]
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : IntertwinesAllRanks f) :
    IsParameterLinear booleanColorMap polynomialColorMap f := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c x
  rw [booleanColorMap, MvPolynomial.aeval_X, polynomialColorMap, MvPolynomial.aeval_X,
    ← booleanRankParameter_color]
  exact hf c.val x

theorem vertexMapTransport_parameters [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IntertwinesAllRanks f) : IntertwinesAllRanks (vertexMapTransport e f) := by
  intro r x
  erw [vertexMapTransport_apply, map_mul, booleanVertexRelabelEquiv_parameter,
    hf, map_mul, MvPolynomial.rename_esymm]
  rfl

theorem vertexMapTransport_degree (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (n : ℕ) (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    vertexMapTransport e f x ∈ polynomialDegreePiece n :=
  polynomialRename_degree e n _ (hf n _ (booleanVertexRelabelEquiv_degree e.symm n x hx))

theorem vertexMapTransport_one (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : f 1 = 1) :
    vertexMapTransport e f 1 = 1 := by rw [vertexMapTransport_apply, map_one, hf, map_one]

theorem booleanVertexRelabelEquiv_symm_apply (e : V ≃ W) (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv e x) = x :=
  (booleanVertexRelabelEquiv (K := K) e).symm_apply_apply x

theorem vertexMapTransport_symm (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    vertexMapTransport e.symm (vertexMapTransport e f) = f := by
  apply LinearMap.ext
  intro x
  rw [vertexMapTransport_apply, vertexMapTransport_apply, Equiv.symm_symm,
    booleanVertexRelabelEquiv_symm_apply, MvPolynomial.rename_rename]
  have he : (e.symm : W → V) ∘ (e : V → W) = id := by
    funext v
    exact e.symm_apply_apply v
  rw [he, MvPolynomial.rename_id_apply]

theorem rename_fullPolynomialTop (e : V ≃ W) :
    MvPolynomial.rename e (∏ v : V, MvPolynomial.X v : MvPolynomial V K) =
      ∏ w : W, MvPolynomial.X w := by
  rw [map_prod]
  simp only [MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem polynomialBoundary_rename_equiv_congr (e : V ≃ W)
    (f g : MvPolynomial V K) (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff _).mp hz
  have hz' : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    rw [← hy, map_mul, rename_fullPolynomialTop]
  rw [map_sub, map_sub] at hz'
  exact sub_eq_zero.mp hz'

theorem vertexMapTransport_boundary_congr (e : V ≃ W)
    (f g : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : ∀ x, polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (g x)) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f x) =
      polynomialBooleanBoundaryMap (vertexMapTransport e g x) := by
  intro x
  exact polynomialBoundary_rename_equiv_congr e _ _ (h _)

theorem booleanVertexRelabelEquiv_permutation (e : V ≃ W) (h : Equiv.Perm W)
    (x : BooleanBarycentricRing W K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x) =
      booleanVertexRelabelEquiv (e.symm.permCongr h) (booleanVertexRelabelEquiv e.symm x) := by
  rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
  have he : h.trans e.symm = e.symm.trans (e.symm.permCongr h) := by
    apply Equiv.ext
    intro v
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact congrArg (fun q : W ≃ V => booleanVertexRelabelEquiv (K := K) q x) he

theorem polynomialRename_permutation (e : V ≃ W) (h : Equiv.Perm W) (f : MvPolynomial V K) :
    MvPolynomial.rename e (MvPolynomial.rename (e.symm.permCongr h) f) =
      MvPolynomial.rename h (MvPolynomial.rename e f) := by
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  apply congrArg (fun q : V → W => MvPolynomial.rename q f)
  funext v
  exact e.apply_symm_apply (h (e v))

theorem vertexMapTransport_boundary_permutation [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv (e.symm.permCongr h) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (e.symm.permCongr h) (f x))) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f (booleanPermutationAlgEquiv h x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename h (vertexMapTransport e f x)) := by
  intro x
  change polynomialBooleanBoundaryMap (MvPolynomial.rename e
      (f (booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x)))) = _
  rw [booleanVertexRelabelEquiv_permutation]
  have hh := polynomialBoundary_rename_equiv_congr e _ _ (hf (booleanVertexRelabelEquiv e.symm x))
  rw [polynomialRename_permutation] at hh
  exact hh

theorem vertexMapTransport_equivariant [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, f (booleanPermutationAlgEquiv (e.symm.permCongr h) x) =
      MvPolynomial.rename (e.symm.permCongr h) (f x)) :
    ∀ x, vertexMapTransport e f (booleanPermutationAlgEquiv h x) =
      MvPolynomial.rename h (vertexMapTransport e f x) := by
  intro x
  change MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm
    (booleanVertexRelabelEquiv h x))) = _
  change ∀ x, f (booleanVertexRelabelEquiv (e.symm.permCongr h) x) =
    MvPolynomial.rename (e.symm.permCongr h) (f x) at hf
  rw [booleanVertexRelabelEquiv_permutation, hf, polynomialRename_permutation]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeVertexLift.lean -/
section


section

/-! # The integral prime lift on an arbitrary prime-sized vertex set -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem exists_integralPrime_vertex_lift (e : V ≃ ZMod p)
    (f : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ)
    (hfp : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hf₁ : f 1 = 1)
    (hfb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) (f x))) :
    ∃ L : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ,
      IsParameterLinear booleanColorMap polynomialColorMap L ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => chainOrdinaryDegree a.val) n → L x ∈ polynomialDegreePiece n) ∧
      L 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      ∀ (g : PrimeCycleGroup p) x,
        L (booleanPermutationAlgEquiv (e.symm.permCongr (Equiv.addLeft g.toAdd)) x) =
          MvPolynomial.rename (e.symm.permCongr (Equiv.addLeft g.toAdd)) (L x) := by
  let fQ := vertexMapTransport e f
  have hQp : IsParameterLinear booleanColorMap polynomialColorMap fQ :=
    intertwinesAllRanks_parameterLinear fQ
      (vertexMapTransport_parameters e f (parameterLinear_intertwinesAllRanks f hfp))
  let fQA := parameterLinearMap fQ hQp
  have hQd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      fQA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    apply vertexMapTransport_degree e f hfd
    change descentVector σ ∈ basisOrdinaryDegreePiece
      (booleanChainBasis (V := ZMod p) (K := ℤ))
      (fun a => chainOrdinaryDegree a.val) (colorOrdinaryDegree (descentColorExponent σ))
    have hh := (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).generator_mem_piece σ
    rw [booleanScalarGradedBasis_piece_eq] at hh
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply,
      booleanOrdinaryDegree_eq_chainOrdinaryDegree] using hh
  have hQb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (fQA (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (fQA x)) := by
    intro g x
    exact vertexMapTransport_boundary_permutation e f (Equiv.addLeft g.toAdd) (hfb g) x
  obtain ⟨LQ, hLQe, hLQb, hLQd, hLQ₁⟩ := exists_integralPrimeCyclic_boundary_lift p fQA
    hQd hQb (vertexMapTransport_one e f hf₁)
  let L := vertexMapTransport e.symm (LQ.restrictScalars ℤ)
  have hLQp : IsParameterLinear booleanColorMap polynomialColorMap (LQ.restrictScalars ℤ) :=
    fun a x => LQ.map_smul a x
  refine ⟨L, ?_, ?_, vertexMapTransport_one e.symm (LQ.restrictScalars ℤ) hLQ₁, ?_, ?_⟩
  · exact intertwinesAllRanks_parameterLinear L
      (vertexMapTransport_parameters e.symm (LQ.restrictScalars ℤ)
        (parameterLinear_intertwinesAllRanks _ hLQp))
  · intro n x hx
    apply vertexMapTransport_degree e.symm (LQ.restrictScalars ℤ) _ n x hx
    intro m y hy
    apply hLQd m y
    rwa [booleanScalarGradedBasis_piece_eq]
  · intro x
    have hh := vertexMapTransport_boundary_congr e.symm (LQ.restrictScalars ℤ) fQ hLQb x
    rw [vertexMapTransport_symm] at hh
    exact hh
  · intro g x
    let h : Equiv.Perm (ZMod p) := Equiv.addLeft g.toAdd
    have he : e.permCongr (e.symm.permCongr h) = h := e.permCongr.apply_symm_apply h
    apply vertexMapTransport_equivariant e.symm (LQ.restrictScalars ℤ)
      (e.symm.permCongr h) _ x
    intro y
    rw [Equiv.symm_symm, he]
    exact hLQe g y

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedStalk.lean -/
section


section

/-! # Fixed-face actions and the literal prime-cycle action at the top stalk

Equality transports of face indices are made explicit and proved to act by
the corresponding vertex bijection.  This connects the action on whole
families with the polynomial and Boolean permutation actions in the local
prime lift.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial

/-- An additive map is linear for the specified integer-module structures.
The explicit conversion prevents a diamond between quotient and canonical
integer actions at an integral stalk. -/
def integralLinearMapOfAddHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    convert f.map_zsmul c x using 1
    · exact congrArg f (int_smul_eq_zsmul _ c x)
    · exact int_smul_eq_zsmul _ c (f x)


variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def faceVertexCast {p q : P} (h : p = q) : FaceVertex p ≃ FaceVertex q :=
  Equiv.cast (congrArg FaceVertex h)

@[simp] theorem faceVertexCast_val {p q : P} (h : p = q) (a : FaceVertex p) :
    (faceVertexCast h a).val = a.val := by cases h; rfl

def polynomialStalkCast {p q : P} (h : p = q) : PolynomialStalk K p ≃ₐ[K] PolynomialStalk K q :=
  MvPolynomial.renameEquiv K (faceVertexCast h)

def barycentricStalkCast {p q : P} (h : p = q) : BarycentricStalk K p ≃ₐ[K] BarycentricStalk K q :=
  booleanVertexRelabelEquiv (faceVertexCast h)

@[simp] theorem polynomialStalkCast_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkCast K (rfl : p = p) x = x := by
  change MvPolynomial.rename (id : FaceVertex p → FaceVertex p) x = x
  exact MvPolynomial.rename_id_apply x

@[simp] theorem barycentricStalkCast_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkCast K (rfl : p = p) x = x :=
  booleanVertexRelabelEquiv_refl x

theorem stalkFamily_cast (F : StalkLinearFamily (P := P) K) {p q : P} (h : p = q)
    (x : BarycentricStalk K p) :
    polynomialStalkCast K h (F p x) = F q (barycentricStalkCast K h x) := by
  cases h
  rw [polynomialStalkCast_refl, barycentricStalkCast_refl]

def fixedFaceVertexPermutation (e : P ≃o P) (p : P) (h : e p = p) : Equiv.Perm (FaceVertex p) :=
  (faceVertexOrderEquiv e p).trans (faceVertexCast h)

@[simp] theorem fixedFaceVertexPermutation_val (e : P ≃o P) (p : P) (h : e p = p)
    (a : FaceVertex p) : (fixedFaceVertexPermutation e p h a).val = e a.val := by
  rw [fixedFaceVertexPermutation, Equiv.trans_apply, faceVertexCast_val]
  rfl

theorem fixedFaceVertexPermutation_polynomial (e : P ≃o P) (p : P) (h : e p = p)
    (x : PolynomialStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e p h) x =
      polynomialStalkCast K h (polynomialStalkOrderEquiv K e p x) := by
  change MvPolynomial.rename ((faceVertexOrderEquiv e p).trans (faceVertexCast h)) x =
    MvPolynomial.rename (faceVertexCast h) (MvPolynomial.rename (faceVertexOrderEquiv e p) x)
  rw [MvPolynomial.rename_rename]
  rfl

theorem fixedFaceVertexPermutation_barycentric (e : P ≃o P) (p : P) (h : e p = p)
    (x : BarycentricStalk K p) :
    booleanVertexRelabelEquiv (fixedFaceVertexPermutation e p h) x =
      barycentricStalkCast K h (barycentricStalkOrderEquiv K e p x) :=
  booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexCast h) x

theorem stalkFamilyRelabel_fixed_conjugate (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K) (x : BarycentricStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
        F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) := by
  rw [fixedFaceVertexPermutation_polynomial, stalkFamilyRelabel_apply,
    AlgEquiv.apply_symm_apply, stalkFamily_cast,
    ← fixedFaceVertexPermutation_barycentric]

theorem stalkFamilyRelabel_fixed_at (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K)
    (hF : ∀ x, F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)) :
    ∀ x, stalkFamilyRelabel K e F p x = F p x := by
  intro x
  apply (MvPolynomial.renameEquiv K (fixedFaceVertexPermutation e.symm p h)).injective
  change MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)
  rw [stalkFamilyRelabel_fixed_conjugate, hF]

theorem stalkFamilyRelabel_fixed_single (e : P ≃o P) (p : P) (h : e.symm p = p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ x, f (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (f x)) :
    stalkFamilyRelabel K e (stalkFamilySingle K p f) = stalkFamilySingle K p f := by
  funext q
  apply LinearMap.ext
  intro x
  by_cases hq : q = p
  · subst q
    apply stalkFamilyRelabel_fixed_at K e p h
    intro y
    simpa only [stalkFamilySingle_same] using hf y
  · have hq' : e.symm q ≠ p := by
      intro he
      exact hq (e.symm.injective (he.trans h.symm))
    rw [stalkFamilyRelabel_apply, stalkFamilySingle_ne K p q hq,
      stalkFamilySingle_ne K p (e.symm q) hq']
    simp

section Simplex
variable {V : Type*} [Fintype V]

@[simp] theorem simplexTopVertexEquiv_symm_val (v : V) :
    ((simplexTopVertexEquiv (V := V)).symm v).val = {v} := rfl

theorem simplexTopVertexEquiv_val (a : FaceVertex (Finset.univ : Finset V)) :
    a.val = {simplexTopVertexEquiv a} := by
  have hh := congrArg Subtype.val ((simplexTopVertexEquiv (V := V)).symm_apply_apply a)
  exact hh.symm

theorem simplex_fixed_top_permutation (e : Equiv.Perm V)
    (h : finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ) :
    fixedFaceVertexPermutation (finsetOrderCongr e) Finset.univ h =
      (simplexTopVertexEquiv (V := V)).symm.permCongr e := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [fixedFaceVertexPermutation_val, simplexTopVertexEquiv_val a,
    finsetOrderCongr_apply, Finset.map_singleton]
  change {e (simplexTopVertexEquiv a)} =
    ((simplexTopVertexEquiv (V := V)).symm (e (simplexTopVertexEquiv a))).val
  rw [simplexTopVertexEquiv_symm_val]

theorem simplex_top_single_fixed (e : Equiv.Perm V)
    (f : BarycentricStalk K (Finset.univ : Finset V) →ₗ[K]
      PolynomialStalk K (Finset.univ : Finset V))
    (hf : ∀ x, f (booleanVertexRelabelEquiv
      ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) x) =
        MvPolynomial.rename ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) (f x)) :
    stalkFamilyRelabel K (finsetOrderCongr e) (stalkFamilySingle K Finset.univ f) =
      stalkFamilySingle K Finset.univ f := by
  have hsymm : (finsetOrderCongr e).symm = finsetOrderCongr e.symm := rfl
  apply stalkFamilyRelabel_fixed_single K (finsetOrderCongr e) Finset.univ
    (by rw [hsymm, finsetOrderCongr_univ]) f
  intro x
  change f (booleanVertexRelabelEquiv
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) x) =
    MvPolynomial.rename
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) (f x)
  rw [simplex_fixed_top_permutation]
  exact hf x

end Simplex
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SupportCarrier.lean -/
section

section

/-! # The unique supporting face of a polynomial monomial inside a Boolean interval -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The vertices occurring with positive exponent. -/
def exponentVertices {p : P} (a : FaceVertex p →₀ ℕ) : Finset P :=
  a.support.image Subtype.val

theorem exponentVertices_subset {p : P} (a : FaceVertex p →₀ ℕ) :
    exponentVertices a ⊆ faceVertices p := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  exact mem_faceVertices.mpr w.property

/-- The carrier is chosen inside the fixed Boolean interval; distinct global
faces with identical vertices are never identified. -/
def exponentCarrier (hs : IsSimplicialPoset P) {p : P} (a : FaceVertex p →₀ ℕ) : P :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).val

theorem exponentCarrier_le (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a ≤ p :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).property

@[simp] theorem exponentCarrier_vertices (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : faceVertices (exponentCarrier hs a) = exponentVertices a :=
  (existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose_spec.1

theorem exponentCarrier_le_iff (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    exponentCarrier hs a ≤ q ↔ ∀ v ∈ a.support, v.val ≤ q := by
  rw [← faceVertices_subset_iff hs (exponentCarrier_le hs a) hqp,
    exponentCarrier_vertices]
  constructor
  · intro h v hv
    exact (mem_faceVertices.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))).2
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact mem_faceVertices.mpr ⟨w.property.1, h w hw⟩

theorem exponentCarrier_eq_top_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a = p ↔ a.support = univ := by
  constructor
  · intro h
    have hv : exponentVertices a = faceVertices p := by rw [← exponentCarrier_vertices hs a, h]
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hm : v.val ∈ exponentVertices a := hv ▸ mem_faceVertices.mpr v.property
    obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hm
    have he : w = v := Subtype.ext hEq
    exact he ▸ hw
  · intro h
    apply faceVertices_injective_below hs (exponentCarrier_le hs a) le_rfl
    rw [exponentCarrier_vertices]
    ext v
    simp only [exponentVertices, h, Finset.mem_image, mem_univ, true_and, mem_faceVertices]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩

theorem exponentCarrier_lt_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a < p ↔ a.support ≠ univ := by
  rw [lt_iff_le_and_ne]
  simp only [exponentCarrier_le, true_and]
  exact not_congr (exponentCarrier_eq_top_iff hs a)

/-- Pull an exponent vector back along a genuine face inclusion. -/
def restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    FaceVertex q →₀ ℕ :=
  Finsupp.comapDomain (faceVertexInclusion hqp) a (faceVertexInclusion hqp).injective.injOn

@[simp] theorem restrictExponent_apply {p q : P} (hqp : q ≤ p)
    (a : FaceVertex p →₀ ℕ) (v : FaceVertex q) :
    restrictExponent hqp a v = a (faceVertexInclusion hqp v) := rfl

theorem extend_restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ)
    (ha : ∀ v ∈ a.support, v.val ≤ q) :
    (restrictExponent hqp a).mapDomain (faceVertexInclusion hqp) = a := by
  apply Finsupp.mapDomain_comapDomain _ (faceVertexInclusion hqp).injective a
  intro v hv
  refine ⟨⟨v.val, v.property.1, ha v hv⟩, ?_⟩
  exact Subtype.ext rfl

theorem extend_restrictExponent_carrier (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) :
    (restrictExponent (exponentCarrier_le hs a) a).mapDomain
      (faceVertexInclusion (exponentCarrier_le hs a)) = a := by
  apply extend_restrictExponent
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs a) a).mp le_rfl

theorem exponentCarrier_extend_le (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) ≤ q := by
  apply (exponentCarrier_le_iff hs hqp _).mpr
  intro v hv
  have hsupp := Finsupp.mapDomain_support (f := faceVertexInclusion hqp) (s := a)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hsupp hv)
  exact w.property.2

/-- Pullback after extension is compatible with nested actual face inclusions. -/
theorem restrictExponent_extend_of_le {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q)
    (a : FaceVertex q →₀ ℕ) :
    restrictExponent (hrq.trans hqp) (a.mapDomain (faceVertexInclusion hqp)) =
      restrictExponent hrq a := by
  ext v
  change (a.mapDomain (faceVertexInclusion hqp))
      (faceVertexInclusion hqp (faceVertexInclusion hrq v)) =
    a (faceVertexInclusion hrq v)
  exact Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective a _

theorem support_le_exponentCarrier_extend (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    ∀ v ∈ a.support, v.val ≤ exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) := by
  intro v hv
  let b := a.mapDomain (faceVertexInclusion hqp)
  have hbv : faceVertexInclusion hqp v ∈ b.support := by
    rw [Finsupp.mem_support_iff]
    simpa only [b, Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective]
      using Finsupp.mem_support_iff.mp hv
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs b) b).mp le_rfl
    (faceVertexInclusion hqp v) hbv

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkBoundary.lean -/
section

section
/-! # The actual proper-face boundary and graded lifting

These maps are restriction to the inverse limit of all proper faces.  Their
kernels are exactly multiplication by the top rank parameter.  The Boolean
boundary has an explicit graded section, obtained in the already established
standard monomial coordinates.  Thus the positive-degree lifting argument
applies directly to coherent maps of actual stalk diagrams.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

include hs in
theorem polynomialStalkBoundary_eq_zero_iff (p : P) (f : PolynomialStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p f = 0 ↔
      ∃ g : PolynomialStalk K p, polynomialTop K p * g = f := by
  constructor
  · intro hf
    have hm : f ∈ Ideal.span {∏ v : FaceVertex p, (X v : PolynomialStalk K p)} := by
      apply (mem_full_product_ideal_iff (FaceVertex p) K f).mpr
      intro a ha
      have hq : exponentCarrier hs a < p := (exponentCarrier_lt_iff hs a).mpr ha
      have hres := congrArg (fun x => x.val ⟨exponentCarrier hs a, hq⟩) hf
      change polynomialRestriction K hq.le f = 0 at hres
      have hc := congrArg (fun z : PolynomialStalk K (exponentCarrier hs a) =>
        z.coeff (restrictExponent (exponentCarrier_le hs a) a)) hres
      rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl,
        extend_restrictExponent_carrier hs a, MvPolynomial.coeff_zero] at hc
      exact hc
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hm
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    funext q
    change polynomialRestriction K q.property.le (polynomialTop K p * g) = 0
    rw [map_mul, polynomialRestriction_top K hs q.property, zero_mul]

theorem booleanChainCarrier_lt_of_top_zero (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanChainExponent (FaceVertex p)) (ha : a.val booleanTopFace = 0) :
    standardCarrier ((standardInsideEquiv hs p) a).val < p := by
  let b := ((standardInsideEquiv hs p) a).val
  have hproper : ∀ F ∈ b.val.support, faceRank F.val < faceRank p := by
    intro F hF
    change F ∈ (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).support at hF
    rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    have hGt : G.val ≠ Finset.univ := by
      intro h
      have he : G = booleanTopFace := Subtype.ext h
      subst G
      exact Finsupp.mem_support_iff.mp hG ha
    rw [faceRank_booleanFaceInclusion, ← card_faceVertex p]
    simpa only [Finset.card_univ] using
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hGt)
  have hr : faceRank (standardCarrier b) < faceRank p := by
    rcases standardCarrier_mem_or_bot b with h | ⟨F, hF, he⟩
    · rw [h, faceRank_bot, ← card_faceVertex p]
      exact Fintype.card_pos
    · rw [he]
      exact hproper F hF
  apply lt_of_le_of_ne ((standardInsideEquiv hs p) a).property
  intro he
  exact (ne_of_lt hr) (congrArg faceRank he)

theorem barycentricStalkBoundary_coefficient_zero (p : P) (x : BarycentricStalk K p)
    (hx : stalkBoundaryRestriction (barycentricDiagram K) p x = 0)
    (a : StandardFaceIndex P) (ha : standardCarrier a < p) :
    (barycentricStandardCoordinates K hs p x).val a = 0 := by
  have hres := congrArg (fun z => z.val ⟨standardCarrier a, ha⟩) hx
  change booleanRestriction (K := K) (faceVertexInclusion ha.le) x = 0 at hres
  have hc := congrArg (fun z => z.val a)
    (barycentricStandardCoordinates_naturality K hs ha.le x)
  rw [coefficientRestriction_apply, if_pos le_rfl, hres, map_zero] at hc
  exact hc

include hs in
theorem barycentricStalkBoundary_eq_zero_iff (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (barycentricDiagram K) p x = 0 ↔
      ∃ y : BarycentricStalk K p, booleanTop * y = x := by
  constructor
  · intro hx
    apply (booleanBoundaryMap_eq_zero_iff x).mp
    apply (standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr.injective
    ext a
    rw [map_zero, Finsupp.zero_apply]
    change ((standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr (coordinateBoundaryMap IsChainExponent booleanTopFace x)) a = 0
    rw [coordinateBoundaryMap_coefficient]
    let c : BooleanChainExponent (FaceVertex p) := ⟨a.val, a.property.1⟩
    let b := (standardInsideEquiv hs p) c
    have hb : standardCarrier b.val < p :=
      booleanChainCarrier_lt_of_top_zero hs p c a.property.2
    have hz := barycentricStalkBoundary_coefficient_zero K hs p x hx b.val hb
    rw [barycentricStandardCoordinates_apply_of_inside K hs p x b.val b.property] at hz
    have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = c :=
      (standardInsideEquiv hs p).symm_apply_apply c
    rw [hid] at hz
    simpa only [booleanChainBasis, c] using hz
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    funext q
    have hn : ¬ Function.Surjective (faceVertexInclusion q.property.le) := by
      intro hsurj
      have hc := Fintype.card_le_of_surjective _ hsurj
      rw [card_faceVertex, card_faceVertex] at hc
      exact (not_le_of_gt (faceRank_strictMono hs q.property)) hc
    change booleanRestriction (K := K) (faceVertexInclusion q.property.le)
      (booleanTop * y) = 0
    rw [map_mul, booleanRestriction_top _ hn, zero_mul]

def barycentricCarrierBoundaryExtension (p : P) :
    ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections →ₗ[K]
      BarycentricStalk K p :=
  (barycentricStandardCoordinates K hs p).symm.toLinearMap.comp
    ((coefficientBoundaryExtension standardCarrier p).comp
      (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv.toLinearMap))

theorem barycentricCarrierBoundaryExtension_restrict (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections) :
    stalkBoundaryRestriction (barycentricDiagram K) p
      (barycentricCarrierBoundaryExtension K hs p x) = x := by
  apply (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv).injective
  rw [stalkBoundaryRestriction_naturality]
  change stalkBoundaryRestriction (coefficientDiagram K standardCarrier) p
    (barycentricStandardCoordinates K hs p
      ((barycentricStandardCoordinates K hs p).symm
        (coefficientBoundaryExtension standardCarrier p
          (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv x)))) = _
  rw [LinearEquiv.apply_symm_apply, coefficientBoundaryExtension_restrict]

theorem barycentricCarrierBoundaryExtension_coefficient (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (a : StandardFaceIndex P) :
    (barycentricStandardCoordinates K hs p (barycentricCarrierBoundaryExtension K hs p x)).val a =
      if ha : standardCarrier a < p then
        (barycentricStandardCoordinates K hs (standardCarrier a)
          (x.val ⟨standardCarrier a, ha⟩)).val a else 0 := by
  unfold barycentricCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem standardOrdinaryDegree_inside_orderFree (p : P)
    (a : BooleanChainExponent (FaceVertex p)) :
    standardOrdinaryDegree ((standardInsideEquiv hs p) a).val = booleanOrdinaryDegree a.val := by
  change (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).sum
    (fun F n => n * faceRank F.val) = _
  rw [Finsupp.sum_mapDomain_index (fun F => by simp) (fun F i j => by simp only [add_mul])]
  simp only [faceRank_booleanFaceInclusion, booleanOrdinaryDegree]

theorem barycentricCarrierBoundaryExtension_graded (p : P) (n : ℕ)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (hx : ∀ q : Set.Iio p, x.val q ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricCarrierBoundaryExtension K hs p x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  let b := (standardInsideEquiv hs p) a
  have hc := barycentricStandardCoordinates_apply_of_inside K hs p
    (barycentricCarrierBoundaryExtension K hs p x) b.val b.property
  have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = a :=
    (standardInsideEquiv hs p).symm_apply_apply a
  rw [hid] at hc
  rw [← hc, barycentricCarrierBoundaryExtension_coefficient]
  split_ifs with hb
  · rw [barycentricStandardCoordinates_apply_of_inside K hs (standardCarrier b.val)
      (x.val ⟨standardCarrier b.val, hb⟩) b.val le_rfl]
    apply hx ⟨standardCarrier b.val, hb⟩
    have he := standardOrdinaryDegree_inside_orderFree hs (standardCarrier b.val)
      ((standardInsideEquiv hs (standardCarrier b.val)).symm ⟨b.val, le_rfl⟩)
    rw [Equiv.apply_symm_apply] at he
    intro hdeg
    exact ha ((standardOrdinaryDegree_inside_orderFree hs p a).symm.trans
      (he.trans hdeg))
  · rfl

theorem polynomialRestriction_degree {p q : P} (hqp : q ≤ p) (n : ℕ)
    (f : PolynomialStalk K p) (hf : f ∈ polynomialDegreePiece n) :
    polynomialRestriction K hqp f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl]
  apply hf
  rwa [vertexDegree_mapDomain]

theorem stalkLinearEquiv_symm_graded (p : P)
    (e : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p)
    (he : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e x ∈ polynomialDegreePiece n)
    (n : ℕ) (y : PolynomialStalk K p) (hy : y ∈ polynomialDegreePiece n) :
    e.symm y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  apply (basisDegreeProjection_eq_self_iff_mem booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n (e.symm y)).mp
  apply e.injective
  have hg : ∀ m x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) m →
      e x ∈ basisOrdinaryDegreePiece (MvPolynomial.basisMonomials (FaceVertex p) K)
        (fun a => vertexDegree (fun v => a v)) m := by
    intro m x hx
    exact he m x hx
  have hproj := ordinaryProjection_natural booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K) (fun a => booleanOrdinaryDegree a.val)
    (fun a => vertexDegree (fun v => a v)) e.toLinearMap hg n (e.symm y)
  have hh : e (e.symm y) ∈ basisOrdinaryDegreePiece
      (MvPolynomial.basisMonomials (FaceVertex p) K)
      (fun a => vertexDegree (fun v => a v)) n := by
    intro a ha
    change (e (e.symm y)).coeff a = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hy a ha
  simpa only [LinearEquiv.coe_coe] using hproj.symm.trans
    ((basisDegreeProjection_eq_self_iff_mem _ _ _ _).mpr hh)

/-- Top multiplication in the actual stalk coordinates, with no auxiliary
vertex order in the statement or in its equality instances. -/
theorem barycentricTop_shift_coefficient (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) (a : BooleanChainExponent (FaceVertex p)) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem barycentricTop_degree_shift (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanFace (FaceVertex p) →₀ ℕ) :
    booleanOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      booleanOrdinaryDegree a + Fintype.card (FaceVertex p) := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])]
  simp [booleanTopFace]

theorem barycentricTop_predecessor_degree (p : P) [Nonempty (FaceVertex p)]
    (m : ℕ) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (m + Fintype.card (FaceVertex p))) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ m + Fintype.card (FaceVertex p) := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [barycentricTop_shift_coefficient] at hh

theorem barycentricTop_homogeneous_zero_below (p : P) [Nonempty (FaceVertex p)]
    (n : ℕ) (hn : n < Fintype.card (FaceVertex p)) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ n := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    omega
  have hh := hx b hb
  rw [barycentricTop_shift_coefficient] at hh
  exact hh

include hs in
/-- The actual coherent local lifting theorem.  The boundary comparison is
the isomorphism of proper-face inverse limits induced by the already
constructed lower-face isomorphisms.  Grading of their inverses is derived
from their forward grading, and no full-stalk comparison is presupposed. -/
theorem coherentStalkLift_bijective (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hres : ∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) :
    Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K)
    (fun a => booleanOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    (Q := ↥(((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (R := ↥(((polynomialDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (stalkBoundaryRestriction (barycentricDiagram K) p)
    (stalkBoundaryRestriction (polynomialDiagram K) p) e.sectionEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (polynomialTop K p))
    (Fintype.card (FaceVertex p)) (Fintype.card_pos_iff.mpr inferInstance)
    (polynomialTop_mul_injective K p)
    (fun x hx => (barycentricStalkBoundary_eq_zero_iff K hs p x).mp hx)
    (fun y hy => (polynomialStalkBoundary_eq_zero_iff K hs p y).mp hy)
    (fun n a hn ha => barycentricTop_predecessor_degree K p (n - Fintype.card (FaceVertex p)) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card (FaceVertex p)) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop, booleanOrdinaryDegree, chainOrdinaryDegree] using ha))
    (fun n a hn ha => barycentricTop_homogeneous_zero_below K p n hn a
      (by simpa only [LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by simpa only [LinearMap.mulLeft_apply, polynomialTop, ← polynomialOrdinaryPiece_eq_basis] using ha))
    ?_ f ?_ (parameterLinear_top f hf) ?_
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by
      rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    let z := e.sectionEquiv.symm (stalkBoundaryRestriction (polynomialDiagram K) p y)
    refine ⟨barycentricCarrierBoundaryExtension K hs p z, ?_, ?_⟩
    · apply barycentricCarrierBoundaryExtension_graded
      intro q
      exact stalkLinearEquiv_symm_graded K q.val (e.component q) (he q) n
        (polynomialRestriction K q.property.le y)
        (polynomialRestriction_degree K q.property.le n y hy')
    · rw [barycentricCarrierBoundaryExtension_restrict]
      exact (e.sectionEquiv.apply_symm_apply _).symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx
  · intro x
    apply Subtype.ext
    funext q
    exact hres q x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicRankSum.lean -/
section


section

/-! # Completing the equivariant proper-face family at the top

The sum of the previously chosen single-face families is equivariant by
reindexing a finite orbit sum.  Adding an ordinary top extension produces an
actual coherent family.  Its conjugation error is consequently supported at
the top and has zero genuine boundary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped BigOperators

variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K]
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))


abbrev ActualStalkRankStage (n : ℕ) :=
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
    (StalkLocalGood K) (StalkLocalCompatible K) n

def rankStalkSum (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) :
    StalkLinearFamily (P := P) K := ∑ q, (actualRankStageValue K act h₁ hmul n old) q

theorem rankStalkSum_inside (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (p : P) (hp : faceRank p < n) : rankStalkSum K act h₁ hmul n old p = (actualRankStageValue K act h₁ hmul n old) ⟨p, hp⟩ p := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change (∑ q, (actualRankStageValue K act h₁ hmul n old) q) p = _
  rw [Finset.sum_apply]
  change (∑ q : equivariantRankCut (fun p : P => faceRank p) n, old.value q p) =
    old.value ⟨p, hp⟩ p
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_single (s := Finset.univ)
    (f := fun q : equivariantRankCut (fun p : P => faceRank p) n => old.value q p x)
    ⟨p, hp⟩ ?_ ?_
  · intro q hq hne
    rw [(old.good q).1 p (fun he => hne (Subtype.ext he.symm))]
    rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem rankStalkSum_outside (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (p : P) (hp : ¬ faceRank p < n) : rankStalkSum K act h₁ hmul n old p = 0 := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change (∑ q, (actualRankStageValue K act h₁ hmul n old) q) p = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  apply (old.good q).1 p
  intro he
  apply hp
  exact he ▸ q.property

theorem rankStalkSum_fixed (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (g : G) :
    stalkFamilyRelabel K (act g) (rankStalkSum K act h₁ hmul n old) =
      rankStalkSum K act h₁ hmul n old := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  letI := equivariantRankCutMulAction faceRank (fun g p => faceRank_eq_of_orderIso (act g) p) n
  rw [rankStalkSum, map_sum]
  calc
    ∑ q, stalkFamilyRelabel K (act g) ((actualRankStageValue K act h₁ hmul n old) q) = ∑ q, (actualRankStageValue K act h₁ hmul n old) (g • q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (old.equivariant g q).symm
    _ = ∑ q, (actualRankStageValue K act h₁ hmul n old) q := Equiv.sum_comp (MulAction.toPerm g) (actualRankStageValue K act h₁ hmul n old)

variable [OrderTop P]

def completeTopFamily (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P)) : StalkLinearFamily (P := P) K :=
  rankStalkSum K act h₁ hmul n old + stalkFamilySingle K ⊤ f

theorem completeTopFamily_top (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P)) :
    completeTopFamily K act h₁ hmul n old f ⊤ = f := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change rankStalkSum K act h₁ hmul n old ⊤ + stalkFamilySingle K ⊤ f ⊤ = f
  rw [rankStalkSum_outside K act h₁ hmul n old ⊤ (by rw [hn]; exact Nat.lt_irrefl n),
    stalkFamilySingle_same, zero_add]

theorem completeTopFamily_below (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (q : P) (hq : q < ⊤) :
    completeTopFamily K act h₁ hmul n old f q =
      (actualRankStageValue K act h₁ hmul n old) ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ q := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change rankStalkSum K act h₁ hmul n old q + stalkFamilySingle K ⊤ f q = _
  rw [rankStalkSum_inside K act h₁ hmul n old q (by rw [← hn]; exact faceRank_strictMono hs hq),
    stalkFamilySingle_ne K ⊤ q hq.ne f, add_zero]

theorem completeTopFamily_coherent (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (hf : ∀ (q : equivariantRankCut faceRank n), q.val < ⊤ →
      StalkLocalCompatible K ⊤ q.val (stalkFamilySingle K ⊤ f) ((actualRankStageValue K act h₁ hmul n old) q)) :
    completeTopFamily K act h₁ hmul n old f ∈ coherentStalkFamilySubmodule K := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  intro p q h x
  by_cases hqp : q = p
  · subst q
    simpa only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
  · have hqp' : q < p := lt_of_le_of_ne h hqp
    have hq : q < ⊤ := hqp'.trans_le le_top
    rw [completeTopFamily_below K act h₁ hmul hs n old hn f q hq]
    by_cases hp : p = ⊤
    · subst p
      rw [completeTopFamily_top K act h₁ hmul n old hn f]
      simpa only [stalkFamilySingle_same] using
        hf ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ hq h x
    · have hp' : p < ⊤ := lt_top_iff_ne_top.mpr hp
      rw [completeTopFamily_below K act h₁ hmul hs n old hn f p hp']
      exact old.compatible
        ⟨p, by rw [← hn]; exact faceRank_strictMono hs hp'⟩
        ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ hqp' h x

theorem completeTopFamily_relabel_below (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (g : G) (q : P) (hq : q < ⊤) :
    stalkFamilyRelabel K (act g) (completeTopFamily K act h₁ hmul n old f) q =
      completeTopFamily K act h₁ hmul n old f q := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  have hq' : (act g).symm q ≠ ⊤ := by
    intro he
    apply hq.ne
    have hh := congrArg (act g) he
    simpa only [(act g).apply_symm_apply, (act g).map_top] using hh
  change (stalkFamilyRelabel K (act g)
      (rankStalkSum K act h₁ hmul n old + stalkFamilySingle K ⊤ f)) q = _
  rw [map_add, rankStalkSum_fixed]
  apply LinearMap.ext
  intro x
  change rankStalkSum K act h₁ hmul n old q x +
      stalkFamilyRelabel K (act g) (stalkFamilySingle K ⊤ f) q x =
    rankStalkSum K act h₁ hmul n old q x + stalkFamilySingle K ⊤ f q x
  rw [stalkFamilyRelabel_apply, stalkFamilySingle_ne K ⊤ q hq.ne f,
    stalkFamilySingle_ne K ⊤ ((act g).symm q) hq' f]
  simp

theorem completeTopFamily_boundary_error (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (hf : ∀ (q : equivariantRankCut faceRank n), q.val < ⊤ →
      StalkLocalCompatible K ⊤ q.val (stalkFamilySingle K ⊤ f) ((actualRankStageValue K act h₁ hmul n old) q))
    (g : G) (x : BarycentricStalk K (⊤ : P)) :
    polynomialBooleanBoundaryMap
      (stalkFamilyRelabel K (act g) (completeTopFamily K act h₁ hmul n old f) ⊤ x) =
        polynomialBooleanBoundaryMap (f x) := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  let F := completeTopFamily K act h₁ hmul n old f
  have hF : F ∈ coherentStalkFamilySubmodule K :=
    completeTopFamily_coherent K act h₁ hmul hs n old hn f hf
  have hδ : stalkFamilyRelabel K (act g) F - F ∈ coherentStalkFamilySubmodule K :=
    (coherentStalkFamilySubmodule K).sub_mem (stalkFamilyRelabel_coherent K (act g) F hF) hF
  have hz : stalkBoundaryRestriction (polynomialDiagram K) (⊤ : P)
      ((stalkFamilyRelabel K (act g) F - F) ⊤ x) = 0 := by
    apply Subtype.ext
    funext q
    change polynomialRestriction K q.property.le
      ((stalkFamilyRelabel K (act g) F - F) ⊤ x) = 0
    rw [hδ]
    change (stalkFamilyRelabel K (act g) F q.val - F q.val)
      (booleanRestriction (faceVertexInclusion q.property.le) x) = 0
    rw [completeTopFamily_relabel_below K act h₁ hmul hs n old hn f g q.val q.property,
      sub_self, LinearMap.zero_apply]
  have hboundary := (polynomialStalkBoundary_eq_zero_iff K hs ⊤ _).mp hz
  have hh := (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr hboundary
  change polynomialBooleanBoundaryMap
    (stalkFamilyRelabel K (act g) F ⊤ x - F ⊤ x) = 0 at hh
  rw [map_sub] at hh
  have htop : F ⊤ = f := completeTopFamily_top K act h₁ hmul n old hn f
  rw [htop] at hh
  exact sub_eq_zero.mp hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeCoherent.lean -/
section


section

/-! # A normalized integral coherent family on the prime simplex

Proper nonempty faces have free cyclic orbits.  At the top the actual
integral prime-cycle lifting theorem is applied to the ordinary extension of
the already equivariant boundary.  The completed family is coherent on every
face, parameter-linear, graded, normalized, and cyclic-equivariant over ℤ.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Restrictions
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]

theorem polynomialBoundary_eq_restriction (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q < p) (f g : PolynomialStalk K p)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialRestriction K hqp.le f = polynomialRestriction K hqp.le g := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff _).mp hz
  have hr : polynomialRestriction K hqp.le (f - g) = 0 := by
    rw [← hy, map_mul]
    change polynomialRestriction K hqp.le (polynomialTop K p) * polynomialRestriction K hqp.le y = 0
    rw [polynomialRestriction_top K hs hqp, zero_mul]
  rw [map_sub] at hr
  exact sub_eq_zero.mp hr

end Restrictions

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicSimplexOrderAction_inv_symm (g : PrimeCycleGroup p) :
    (cyclicSimplexOrderAction p g⁻¹).symm = cyclicSimplexOrderAction p g := by
  change finsetOrderCongr ((cyclicVertexPermutation p g⁻¹)⁻¹) =
    finsetOrderCongr (cyclicVertexPermutation p g)
  rw [(cyclicVertexPermutation p).map_inv, inv_inv]

theorem exists_integral_prime_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset (ZMod p)) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧
      F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = 1) ∧
      ∀ g : PrimeCycleGroup p, stalkFamilyRelabel ℤ (cyclicSimplexOrderAction p g) F = F := by
  let hs : IsSimplicialPoset (Finset (ZMod p)) := simplex_isSimplicialPoset
  apply exists_coherent_family_of_prime_top_extension ℤ hs
    (cyclicSimplexOrderAction p) (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
  · intro s hs₀ hs₁ g hg
    exact cyclicSimplex_proper_face_free p s (Finset.nonempty_iff_ne_empty.mpr hs₀) hs₁ g hg
  · letI := orderActionMulAction (cyclicSimplexOrderAction p)
      (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
    letI := representationMulAction (stalkFamilyRepresentation ℤ (cyclicSimplexOrderAction p)
      (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p))
    intro n old hn
    have hp : (Finset.univ : Finset (ZMod p)) ≠ ∅ := Finset.univ_nonempty.ne_empty
    obtain ⟨y, hy, hyb⟩ := exists_ordinary_rank_stalk_extension ℤ hs
      (cyclicSimplexOrderAction p) (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
      n old Finset.univ hn hp
    let V := FaceVertex (Finset.univ : Finset (ZMod p))
    let e : V ≃ ZMod p := simplexTopVertexEquiv
    letI : LinearOrder V := linearOrderWithDecidableEq (LinearOrder.lift' e e.injective) inferInstance
    let f : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ := y Finset.univ
    have hsingle : stalkFamilySingle ℤ Finset.univ f = y :=
      stalkFamilySingle_eq_of_supported ℤ Finset.univ y hy.1
    have hfbound : ∀ q : equivariantRankCut faceRank n, q.val < (Finset.univ : Finset (ZMod p)) →
        StalkLocalCompatible ℤ Finset.univ q.val (stalkFamilySingle ℤ Finset.univ f) (old.value q) := by
      rw [hsingle]
      exact hyb
    have hfp : IsParameterLinear booleanColorMap polynomialColorMap f :=
      intertwinesAllRanks_parameterLinear f (hy.2.1 Finset.univ)
    have hfd : ∀ m x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) m → f x ∈ polynomialDegreePiece m :=
      hy.2.2.1 Finset.univ
    have hf₁ : f 1 = 1 := hy.2.2.2
    have hfe : ∀ (g : PrimeCycleGroup p) x,
        polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv
          (e.symm.permCongr (Equiv.addLeft g.toAdd)) x)) =
        polynomialBooleanBoundaryMap (MvPolynomial.rename
          (e.symm.permCongr (Equiv.addLeft g.toAdd)) (f x)) := by
      intro g x
      let a := cyclicSimplexOrderAction p g⁻¹
      have ha : a.symm (Finset.univ : Finset (ZMod p)) = Finset.univ := a.symm.map_top
      let T := completeTopFamily ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p) n old f
      have hb := completeTopFamily_boundary_error ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
        hs n old hn f hfbound g⁻¹ x
      have hrename := polynomialBoundary_rename_equiv_congr
        (fixedFaceVertexPermutation a.symm Finset.univ ha) _ _ hb
      change polynomialBooleanBoundaryMap (MvPolynomial.rename
          (fixedFaceVertexPermutation a.symm Finset.univ ha)
          (stalkFamilyRelabel ℤ a T Finset.univ x)) =
        polynomialBooleanBoundaryMap (MvPolynomial.rename
          (fixedFaceVertexPermutation a.symm Finset.univ ha) (f x)) at hrename
      have hT : T Finset.univ = f := completeTopFamily_top ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p) n old hn f
      rw [stalkFamilyRelabel_fixed_conjugate ℤ a Finset.univ ha T x, hT] at hrename
      have heq : fixedFaceVertexPermutation a.symm Finset.univ ha =
          e.symm.permCongr (Equiv.addLeft g.toAdd) := by
        have hact : a.symm = finsetOrderCongr (Equiv.addLeft g.toAdd) :=
          cyclicSimplexOrderAction_inv_symm p g
        have hh := congrArg
          (fun b : Finset (ZMod p) ≃o Finset (ZMod p) =>
            fixedFaceVertexPermutation b Finset.univ b.map_top) hact
        exact hh.trans (simplex_fixed_top_permutation (Equiv.addLeft g.toAdd)
          (finsetOrderCongr_univ (Equiv.addLeft g.toAdd)))
      rw [heq] at hrename
      exact hrename
    obtain ⟨L, hLp, hLd, hL₁, hLb, hLe⟩ := exists_integralPrime_vertex_lift p e f hfp hfd hf₁ hfe
    let LL : BarycentricStalk ℤ (Finset.univ : Finset (ZMod p)) →ₗ[ℤ]
        PolynomialStalk ℤ (Finset.univ : Finset (ZMod p)) :=
      integralLinearMapOfAddHom L.toAddMonoidHom
    refine ⟨stalkFamilySingle ℤ Finset.univ LL,
      stalkFamilySingle_good ℤ Finset.univ LL (parameterLinear_intertwinesAllRanks LL hLp) hLd hL₁,
      ?_, ?_⟩
    · intro q hq h x
      erw [stalkFamilySingle_same]
      have hb := polynomialBoundary_eq_restriction hs hq (L x) (f x) (hLb x)
      have hh := hfbound q hq h x
      erw [stalkFamilySingle_same] at hh
      erw [hb]
      exact hh
    · intro g
      apply simplex_top_single_fixed ℤ (cyclicVertexPermutation p g) LL
      intro x
      have hi : (cyclicVertexPermutation p g).symm = cyclicVertexPermutation p g⁻¹ :=
        ((cyclicVertexPermutation p).map_inv g).symm
      rw [hi]
      exact hLe g⁻¹ x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSymmetricTrace.lean -/
section


section

/-! # Symmetric coherent families from integral orbit traces

At prime rank the cyclic family is traced over exactly `(p-1)!` cosets.  At
every rank ordinary full-group averaging gives the factorial scalar.  Both
constructions act on the whole genuine coherent family, so all face
restriction squares and ordinary grading are preserved.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped BigOperators

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

theorem exists_normalized_coherent_stalk_family (K : Type*) [CommRing K]
    (hs : IsSimplicialPoset P) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧ F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧ ∀ p, F p 1 = 1 := by
  let G := Equiv.Perm (Fin 0)
  let act : G → P ≃o P := fun _ => OrderIso.refl P
  have h₁ : act 1 = OrderIso.refl P := rfl
  have hmul : ∀ g h, act (g * h) = (act h).trans (act g) := by intros; rfl
  obtain ⟨F, hc, hp, hd, hnorm, he⟩ := exists_equivariant_coherent_stalk_family K act h₁ hmul hs (by
    intro n old p hr
    by_cases hbot : p = ⊥
    · subst p
      obtain ⟨y, hy⟩ := exists_stalkLocalGood_bot (P := P) K
      exact ⟨y, hy, fun q hq => False.elim (not_lt_bot hq), fun _ _ => stalkFamilyRelabel_refl K y⟩
    · obtain ⟨y, hy, hb⟩ := exists_ordinary_rank_stalk_extension K hs act h₁ hmul n old p hr hbot
      exact ⟨y, hy, hb, fun _ _ => stalkFamilyRelabel_refl K y⟩)
  exact ⟨F, hc, hp, hd, hnorm⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def symmetricSimplexFamilyRepresentation (K : Type*) [CommRing K] :
    CyclicRepresentation K (Equiv.Perm V) (StalkLinearFamily (P := Finset V) K) :=
  stalkFamilyRepresentation K finsetOrderCongr simplexOrderAction_one simplexOrderAction_mul

def stalkFamilyEvalOne (K : Type*) [CommRing K] (s : Finset V) :
    StalkLinearFamily (P := Finset V) K →+ PolynomialStalk K s where
  toFun F := F s 1
  map_zero' := rfl
  map_add' F H := rfl

theorem simplexCosetTrace_properties (K : Type*) [CommRing K]
    (H : Subgroup (Equiv.Perm V)) (F : StalkLinearFamily (P := Finset V) K)
    (hH : ∀ h : H, symmetricSimplexFamilyRepresentation K h.val F = F)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K)
    (h₁ : ∀ s, F s 1 = 1) :
    let T := cosetTrace (symmetricSimplexFamilyRepresentation K) H F hH
    T ∈ coherentStalkFamilySubmodule K ∧ T ∈ parameterStalkFamilySubmodule K ∧
      T ∈ gradedStalkFamilySubmodule K ∧
      (∀ s, T s 1 = H.index • (1 : PolynomialStalk K s)) ∧
      ∀ e : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr e) T = T := by
  dsimp only
  refine ⟨cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_coherent K _ y hy) hc,
    cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_parameter K _ y hy) hp,
    cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_graded K _ y hy) hd, ?_, ?_⟩
  · intro s
    apply cosetTrace_map_const (symmetricSimplexFamilyRepresentation K) H F hH
      (stalkFamilyEvalOne K s) 1
    intro e
    change stalkFamilyRelabel K (finsetOrderCongr e) F s 1 = 1
    rw [stalkFamilyRelabel_apply, map_one, h₁, map_one]
  · intro e
    exact cosetTrace_fixed (symmetricSimplexFamilyRepresentation K) H F hH e

theorem exists_integral_factorial_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset V) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧ F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = (Fintype.card V).factorial • (1 : PolynomialStalk ℤ s)) ∧
      ∀ e : Equiv.Perm V, stalkFamilyRelabel ℤ (finsetOrderCongr e) F = F := by
  obtain ⟨F, hc, hp, hd, h₁⟩ := exists_normalized_coherent_stalk_family ℤ
    (simplex_isSimplicialPoset (V := V))
  have hH : ∀ h : (⊥ : Subgroup (Equiv.Perm V)), symmetricSimplexFamilyRepresentation ℤ h.val F = F := by
    intro h
    have he : h.val = 1 := h.property
    rw [he, (symmetricSimplexFamilyRepresentation ℤ).map_one]
    rfl
  refine ⟨cosetTrace (symmetricSimplexFamilyRepresentation ℤ) ⊥ F hH, ?_⟩
  have hh := simplexCosetTrace_properties ℤ ⊥ F hH hc hp hd h₁
  have hi : (⊥ : Subgroup (Equiv.Perm V)).index = (Fintype.card V).factorial := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_perm]
  simpa only [hi] using hh

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicVertexPermutation_injective : Function.Injective (cyclicVertexPermutation p) := by
  intro g h he
  have hh := congrArg (fun e : Equiv.Perm (ZMod p) => e 0) he
  change g.toAdd + 0 = h.toAdd + 0 at hh
  rw [add_zero, add_zero] at hh
  exact congrArg Multiplicative.ofAdd hh

theorem cyclicVertexPermutation_index : (cyclicVertexPermutation p).range.index = (p - 1).factorial :=
  permutationEmbedding_index_factorial (cyclicVertexPermutation p) (cyclicVertexPermutation_injective p)
    p (Fact.out : p.Prime).pos
    (by rw [Nat.card_eq_fintype_card, primeCycle_card]) (ZMod.card p)

theorem exists_integral_prime_symmetric_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset (ZMod p)) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧ F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = (p - 1).factorial • (1 : PolynomialStalk ℤ s)) ∧
      ∀ e : Equiv.Perm (ZMod p), stalkFamilyRelabel ℤ (finsetOrderCongr e) F = F := by
  obtain ⟨F, hc, hp, hd, h₁, he⟩ := exists_integral_prime_simplex_family p
  let H := (cyclicVertexPermutation p).range
  have hH : ∀ h : H, symmetricSimplexFamilyRepresentation ℤ h.val F = F := by
    intro h
    obtain ⟨g, hg⟩ := h.property
    rw [← hg]
    exact he g
  refine ⟨cosetTrace (symmetricSimplexFamilyRepresentation ℤ) H F hH, ?_⟩
  have hh := simplexCosetTrace_properties ℤ H F hH hc hp hd h₁
  simpa only [H, cyclicVertexPermutation_index] using hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFamilyBaseChange.lean -/
section


section

/-! # Scalar extension and normalization of coherent integral families

Each component is extended through its actual integral standard basis.
Coefficient naturality proves preservation of every restriction, parameter
operator, ordinary degree, and order-automorphism symmetry.  A unit constant
scalar is then divided out in the coefficient ring.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def integralStalkLinearExtension (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  integralLinearExtension (barycentricStalkStandardBasis ℤ hs p)
    (barycentricStalkStandardBasis K hs p) (polynomialCoefficientChange (Int.castRingHom K)) f

theorem integralStalkLinearExtension_commutes (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk ℤ p) :
    integralStalkLinearExtension K hs p f (booleanCoefficientChange (Int.castRingHom K) x) =
      polynomialCoefficientChange (Int.castRingHom K) (f x) :=
  integralLinearExtension_commutes (barycentricStalkStandardBasis ℤ hs p)
    (barycentricStalkStandardBasis K hs p) (booleanCoefficientChange (Int.castRingHom K))
    (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p) f x

@[simp] theorem integralStalkLinearExtension_basis (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) (a : StandardInside p) :
    integralStalkLinearExtension K hs p f (barycentricStalkStandardBasis K hs p a) =
      polynomialCoefficientChange (Int.castRingHom K) (f (barycentricStalkStandardBasis ℤ hs p a)) :=
  integralLinearExtension_basis _ _ _ _ a

def integralStalkFamilyExtension (F : StalkLinearFamily (P := P) ℤ) : StalkLinearFamily (P := P) K :=
  fun p => integralStalkLinearExtension K hs p (F p)

theorem integralStalkFamilyExtension_coherent (F : StalkLinearFamily (P := P) ℤ)
    (hF : F ∈ coherentStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  have he : (polynomialRestriction K h).toLinearMap.comp (integralStalkLinearExtension K hs p (F p)) =
      (integralStalkLinearExtension K hs q (F q)).comp
        (booleanRestriction (K := K) (faceVertexInclusion h)).toLinearMap := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    change polynomialRestriction K h
      (integralStalkLinearExtension K hs p (F p) (barycentricStalkStandardBasis K hs p a)) = _
    rw [integralStalkLinearExtension_basis,
      ← polynomialCoefficientChange_restriction (Int.castRingHom K) h, hF,
      ← integralStalkLinearExtension_commutes K hs q (F q),
      booleanCoefficientChange_restriction, booleanCoefficientChange_standardBasis]
    rfl
  exact DFunLike.congr_fun he x

theorem integralStalkFamilyExtension_parameter (F : StalkLinearFamily (P := P) ℤ)
    (hF : F ∈ parameterStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ parameterStalkFamilySubmodule K := by
  change ∀ p r x, F p (booleanRankParameter (r + 1) * x) =
    polynomialParameter ℤ p (r + 1) * F p x at hF
  intro p r x
  have he : (integralStalkLinearExtension K hs p (F p)).comp
      (LinearMap.mulLeft K (booleanRankParameter (V := FaceVertex p) (K := K) (r + 1))) =
    (LinearMap.mulLeft K (polynomialParameter K p (r + 1))).comp
      (integralStalkLinearExtension K hs p (F p)) := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a,
      ← booleanCoefficientChange_parameter (Int.castRingHom K) (r + 1),
      ← booleanCoefficientChange_mul, integralStalkLinearExtension_commutes,
      integralStalkLinearExtension_commutes, hF]
    simp only [polynomialCoefficientChange_eq, map_mul, polynomialParameter, MvPolynomial.map_esymm]
  exact DFunLike.congr_fun he x

theorem integralStalkFamilyExtension_graded (F : StalkLinearFamily (P := P) ℤ)
    (hp : F ∈ parameterStalkFamilySubmodule ℤ)
    (hd : F ∈ gradedStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  apply ordinaryDegree_of_hasStandardDegree hs p
    (integralStalkLinearExtension K hs p (F p)) ?_ n x hx
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkLinearExtension K hs p (F p)
      (barycentricStalkStandardBasis K hs p a))).val b = 0
  rw [integralStalkLinearExtension_basis, polynomialCoefficientChange_coordinates]
  have hh := hasStandardDegree_of_ordinary_degree ℤ hs p (F p) (hd p) a b hab
  rw [hh, map_zero]

theorem integralStalkFamilyExtension_scalar (F : StalkLinearFamily (P := P) ℤ)
    (m : ℕ) (hF : ∀ p, F p 1 = m • (1 : PolynomialStalk ℤ p)) :
    ∀ p, integralStalkFamilyExtension K hs F p 1 = m • (1 : PolynomialStalk K p) := by
  intro p
  have hh := integralStalkLinearExtension_commutes K hs p (F p) 1
  have h₁ : booleanCoefficientChange (V := FaceVertex p) (Int.castRingHom K) 1 = 1 :=
    (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed (Int.castRingHom K)).map_one
  rw [h₁, hF, map_nsmul] at hh
  simpa only [integralStalkFamilyExtension, polynomialCoefficientChange_eq, map_one] using hh

theorem integralStalkFamilyExtension_relabel (F : StalkLinearFamily (P := P) ℤ) (e : P ≃o P) :
    integralStalkFamilyExtension K hs (stalkFamilyRelabel ℤ e F) =
      stalkFamilyRelabel K e (integralStalkFamilyExtension K hs F) := by
  funext p
  apply (barycentricStalkStandardBasis K hs p).ext
  intro a
  change integralStalkLinearExtension K hs p (stalkFamilyRelabel ℤ e F p)
    (barycentricStalkStandardBasis K hs p a) = _
  rw [integralStalkLinearExtension_basis]
  have hB := booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a
  rw [← hB]
  change MvPolynomial.map (Int.castRingHom K)
      ((polynomialStalkOrderEquiv ℤ e.symm p).symm
        (F (e.symm p) (barycentricStalkOrderEquiv ℤ e.symm p
          (barycentricStalkStandardBasis ℤ hs p a)))) =
    (polynomialStalkOrderEquiv K e.symm p).symm
      (integralStalkLinearExtension K hs (e.symm p) (F (e.symm p))
        (barycentricStalkOrderEquiv K e.symm p
          (booleanCoefficientChange (Int.castRingHom K) (barycentricStalkStandardBasis ℤ hs p a))))
  have hn := booleanCoefficientChange_restriction (Int.castRingHom K)
    (faceVertexOrderEquiv e.symm p).symm.toEmbedding (barycentricStalkStandardBasis ℤ hs p a)
  change booleanCoefficientChange (Int.castRingHom K)
      (barycentricStalkOrderEquiv ℤ e.symm p (barycentricStalkStandardBasis ℤ hs p a)) =
    barycentricStalkOrderEquiv K e.symm p
      (booleanCoefficientChange (Int.castRingHom K) (barycentricStalkStandardBasis ℤ hs p a)) at hn
  rw [← hn, integralStalkLinearExtension_commutes]
  exact MvPolynomial.map_rename (Int.castRingHom K) (faceVertexOrderEquiv e.symm p).symm _

include hs in
theorem exists_normalized_scalar_extension (F : StalkLinearFamily (P := P) ℤ)
    (m : ℕ) (hm : IsUnit (m : K))
    (hc : F ∈ coherentStalkFamilySubmodule ℤ)
    (hp : F ∈ parameterStalkFamilySubmodule ℤ)
    (hd : F ∈ gradedStalkFamilySubmodule ℤ)
    (hscalar : ∀ p, F p 1 = m • (1 : PolynomialStalk ℤ p)) :
    ∃ L : StalkLinearFamily (P := P) K,
      L ∈ coherentStalkFamilySubmodule K ∧ L ∈ parameterStalkFamilySubmodule K ∧
      L ∈ gradedStalkFamilySubmodule K ∧ (∀ p, L p 1 = 1) ∧
      ∀ e : P ≃o P, stalkFamilyRelabel ℤ e F = F → stalkFamilyRelabel K e L = L := by
  obtain ⟨u, hu⟩ := hm
  let E := integralStalkFamilyExtension K hs F
  let L : StalkLinearFamily (P := P) K := (↑u⁻¹ : K) • E
  refine ⟨L,
    (coherentStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_coherent K hs F hc),
    (parameterStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_parameter K hs F hp),
    (gradedStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_graded K hs F hp hd),
    ?_, ?_⟩
  · intro p
    change (↑u⁻¹ : K) • (E p 1) = 1
    rw [integralStalkFamilyExtension_scalar K hs F m hscalar]
    rw [← Nat.cast_smul_eq_nsmul K m (1 : PolynomialStalk K p), ← hu]
    exact inv_smul_smul u (1 : PolynomialStalk K p)
  · intro e he
    change stalkFamilyRelabel K e ((↑u⁻¹ : K) • E) = (↑u⁻¹ : K) • E
    rw [map_smul, ← integralStalkFamilyExtension_relabel, he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSymmetricTransport.lean -/
section

section
/-! # Transport of a symmetric simplex family to arbitrary face posets

A full symmetric family on one finite simplex determines maps on every
finite vertex set of at most that cardinality.  The construction chooses an
embedding, and its independence is proved by extending a pair of finite
embeddings to an ambient permutation.  The resulting maps commute with
every vertex inclusion and bijection, so they apply to the actual vertices
of each face of an arbitrary simplicial poset.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section VertexTransport
variable {A B C D K : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [CommRing K]

def vertexTransportLinear
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  (MvPolynomial.renameEquiv K e).symm.toLinearMap.comp
    (f.comp (booleanVertexRelabelEquiv e).toLinearMap)

@[simp] theorem vertexTransportLinear_apply
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (x : BooleanBarycentricRing A K) :
    vertexTransportLinear f e x = MvPolynomial.rename e.symm (f (booleanVertexRelabelEquiv e x)) :=
  rfl

theorem vertexTransportLinear_trans
    (f : BooleanBarycentricRing C K →ₗ[K] MvPolynomial C K) (e : A ≃ B) (g : B ≃ C) :
    vertexTransportLinear (vertexTransportLinear f g) e = vertexTransportLinear f (e.trans g) := by
  apply LinearMap.ext
  intro x
  simp only [vertexTransportLinear_apply, booleanVertexRelabelEquiv_trans,
    MvPolynomial.rename_rename]
  rfl

theorem vertexTransportLinear_of_intertwines
    (f : BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K)
    (g : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (h : ∀ x, MvPolynomial.rename e (f x) = g (booleanVertexRelabelEquiv e x)) :
    vertexTransportLinear g e = f := by
  apply LinearMap.ext
  intro x
  rw [vertexTransportLinear_apply, ← h]
  exact (MvPolynomial.renameEquiv K e).symm_apply_apply (f x)

theorem vertexTransportLinear_parameter
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : ∀ r x, f (booleanRankParameter (r + 1) * x) = esymm B K (r + 1) * f x)
    (r : ℕ) (x : BooleanBarycentricRing A K) :
    vertexTransportLinear f e (booleanRankParameter (r + 1) * x) =
      esymm A K (r + 1) * vertexTransportLinear f e x := by
  rw [vertexTransportLinear_apply, map_mul, booleanVertexRelabelEquiv_parameter,
    hf, map_mul, MvPolynomial.rename_esymm]
  rfl

theorem vertexTransportLinear_graded
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (n : ℕ) (x : BooleanBarycentricRing A K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    vertexTransportLinear f e x ∈ polynomialDegreePiece n :=
  polynomialRename_degree e.symm n _ (hf n _ (booleanVertexRelabelEquiv_degree e n x hx))

theorem vertexTransportLinear_normalized
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : f 1 = 1) : vertexTransportLinear f e 1 = 1 := by
  rw [vertexTransportLinear_apply, map_one, hf, map_one]

theorem coeff_rename_inverse (e : A ≃ B) (f : MvPolynomial B K) (a : A →₀ ℕ) :
    (MvPolynomial.rename e.symm f).coeff a = f.coeff (a.mapDomain e) := by
  have h := MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective f (a.mapDomain e)
  simpa only [← Finsupp.mapDomain_comp, e.symm_comp_self, Finsupp.mapDomain_id] using h

theorem killCompl_equiv (e : A ≃ B) (f : MvPolynomial B K) :
    MvPolynomial.killCompl e.injective f = MvPolynomial.rename e.symm f := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeff_rename_inverse]

theorem killCompl_rename_square (i : A ↪ B) (j : C ↪ D) (e : A ≃ C) (g : B ≃ D)
    (h : i.trans g.toEmbedding = e.toEmbedding.trans j) (f : MvPolynomial D K) :
    MvPolynomial.killCompl i.injective (MvPolynomial.rename g.symm f) =
      MvPolynomial.rename e.symm (MvPolynomial.killCompl j.injective f) := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeff_rename_inverse, coeff_rename_inverse,
    MvPolynomial.coeff_killCompl, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  change f.coeff (a.mapDomain (i.trans g.toEmbedding)) =
    f.coeff (a.mapDomain (e.toEmbedding.trans j))
  rw [h]

theorem booleanRestriction_relabel_square (i : A ↪ B) (j : C ↪ D)
    (e : A ≃ C) (g : B ≃ D) (h : i.trans g.toEmbedding = e.toEmbedding.trans j)
    (x : BooleanBarycentricRing B K) :
    booleanVertexRelabelEquiv e (booleanRestriction i x) =
      booleanRestriction j (booleanVertexRelabelEquiv g x) := by
  have he : e.symm.toEmbedding.trans i = j.trans g.symm.toEmbedding := by
    apply Function.Embedding.ext
    intro a
    apply g.injective
    have hh := congrArg (fun t : A ↪ D => t (e.symm a)) h
    change g (i (e.symm a)) = j (e (e.symm a)) at hh
    change g (i (e.symm a)) = g (g.symm (j a))
    simpa only [Equiv.apply_symm_apply] using hh
  change booleanRestriction e.symm.toEmbedding (booleanRestriction i x) =
    booleanRestriction j (booleanRestriction g.symm.toEmbedding x)
  calc
    _ = booleanRestriction (e.symm.toEmbedding.trans i) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction (j.trans g.symm.toEmbedding) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

end VertexTransport

section StalkTransport
variable {P A B K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype A] [Fintype B] [CommRing K]

theorem stalkFamily_fixed_natural (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : stalkFamilyRelabel K e.symm F = F) (p : P) (x : BarycentricStalk K p) :
    polynomialStalkOrderEquiv K e p (F p x) =
      F (e p) (barycentricStalkOrderEquiv K e p x) := by
  have h := congrArg (fun H : StalkLinearFamily (P := P) K => H p x) hF
  change (polynomialStalkOrderEquiv K e p).symm
    (F (e p) (barycentricStalkOrderEquiv K e p x)) = F p x at h
  have hh := congrArg (polynomialStalkOrderEquiv K e p) h
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem vertexTransport_stalk_order (F : StalkLinearFamily (P := P) K)
    (e : P ≃o P) (hF : stalkFamilyRelabel K e.symm F = F)
    (p q : P) (a : A ≃ FaceVertex p) (b : A ≃ FaceVertex q)
    (hq : q = e p) (hb : ∀ x, (b x).val = e (a x).val) :
    vertexTransportLinear (F q) b = vertexTransportLinear (F p) a := by
  subst q
  have he : b = a.trans (faceVertexOrderEquiv e p) := by
    apply Equiv.ext
    intro x
    exact Subtype.ext (hb x)
  rw [he, ← vertexTransportLinear_trans]
  congr 1
  exact vertexTransportLinear_of_intertwines (F p) (F (e p))
    (faceVertexOrderEquiv e p) (stalkFamily_fixed_natural e F hF p)

theorem vertexTransport_stalk_restriction (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) {p q : P} (hqp : q ≤ p)
    (a : A ≃ FaceVertex q) (b : B ≃ FaceVertex p) (i : A ↪ B)
    (hi : i.trans b.toEmbedding = a.toEmbedding.trans (faceVertexInclusion hqp))
    (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl i.injective (vertexTransportLinear (F p) b x) =
      vertexTransportLinear (F q) a (booleanRestriction i x) := by
  rw [vertexTransportLinear_apply, killCompl_rename_square i (faceVertexInclusion hqp) a b hi,
    ← polynomialRestriction_eq_killCompl]
  have hh := congrArg (MvPolynomial.rename a.symm)
    (hF p q hqp (booleanVertexRelabelEquiv b x))
  have hb := congrArg (fun z => MvPolynomial.rename a.symm (F q z))
    (booleanRestriction_relabel_square i (faceVertexInclusion hqp) a b hi x).symm
  exact hh.trans hb

end StalkTransport

section SimplexPlacements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

def embeddedSimplexMap (F : StalkLinearFamily (P := Finset V) K) (i : A ↪ V) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  vertexTransportLinear (F (embeddingPlacementFace i)) (embeddingPlacementVertex i)

theorem embeddedSimplexMap_independent (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (i j : A ↪ V) : embeddedSimplexMap F i = embeddedSimplexMap F j := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair i j i.injective j.injective
  have he : i.trans σ.toEmbedding = j := Function.Embedding.ext hσ
  have hface : embeddingPlacementFace j = finsetOrderCongr σ (embeddingPlacementFace i) := by
    simp only [finsetOrderCongr_apply, embeddingPlacementFace, Finset.map_map, he]
  have hfixed : stalkFamilyRelabel K (finsetOrderCongr σ).symm F = F := by
    rw [← finsetOrderCongr_symm]
    exact hF σ.symm
  symm
  apply vertexTransport_stalk_order F (finsetOrderCongr σ) hfixed
    (embeddingPlacementFace i) (embeddingPlacementFace j)
    (embeddingPlacementVertex i) (embeddingPlacementVertex j) hface
  intro a
  simp only [embeddingPlacementVertex_val, finsetOrderCongr_apply, Finset.map_singleton,
    Equiv.coe_toEmbedding, hσ]

theorem embeddingPlacementFace_comp_subset (i : B ↪ V) (j : A ↪ B) :
    embeddingPlacementFace (j.trans i) ⊆ embeddingPlacementFace i := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨j a, Finset.mem_univ _, rfl⟩

theorem embeddingPlacementVertex_comp (i : B ↪ V) (j : A ↪ B) :
    j.trans (embeddingPlacementVertex i).toEmbedding =
      (embeddingPlacementVertex (j.trans i)).toEmbedding.trans
        (faceVertexInclusion (embeddingPlacementFace_comp_subset i j)) := by
  apply Function.Embedding.ext
  intro a
  apply Subtype.ext
  rfl

theorem embeddedSimplexMap_restriction (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) (i : B ↪ V) (j : A ↪ B)
    (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl j.injective (embeddedSimplexMap F i x) =
      embeddedSimplexMap F (j.trans i) (booleanRestriction j x) :=
  vertexTransport_stalk_restriction F hF (embeddingPlacementFace_comp_subset i j)
    (embeddingPlacementVertex (j.trans i)) (embeddingPlacementVertex i) j
    (embeddingPlacementVertex_comp i j) x

def finiteVertexMap (F : StalkLinearFamily (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  embeddedSimplexMap F (Classical.choice (Function.Embedding.nonempty_of_card_le hA))

theorem finiteVertexMap_eq_placement (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (i : A ↪ V) :
    finiteVertexMap F hA = embeddedSimplexMap F i :=
  embeddedSimplexMap_independent F hF _ i

theorem finiteVertexMap_restriction (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (i : A ↪ B) (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl i.injective (finiteVertexMap F hB x) =
      finiteVertexMap F hA (booleanRestriction i x) := by
  let j : B ↪ V := Classical.choice (Function.Embedding.nonempty_of_card_le hB)
  rw [finiteVertexMap_eq_placement F hσ hB j,
    finiteVertexMap_eq_placement F hσ hA (i.trans j)]
  exact embeddedSimplexMap_restriction F hF j i x

theorem finiteVertexMap_relabel (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (e : A ≃ B) (x : BooleanBarycentricRing A K) :
    MvPolynomial.rename e (finiteVertexMap F hA x) =
      finiteVertexMap F hB (booleanVertexRelabelEquiv e x) := by
  have h := finiteVertexMap_restriction F hF hσ hB hA e.symm.toEmbedding x
  rw [killCompl_equiv e.symm] at h
  exact h

theorem finiteVertexMap_parameter (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ parameterStalkFamilySubmodule K)
    (hA : Fintype.card A ≤ Fintype.card V) (r : ℕ) (x : BooleanBarycentricRing A K) :
    finiteVertexMap F hA (booleanRankParameter (r + 1) * x) =
      esymm A K (r + 1) * finiteVertexMap F hA x :=
  vertexTransportLinear_parameter _ _ (fun r x => hF _ r x) r x

theorem finiteVertexMap_graded (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ gradedStalkFamilySubmodule K)
    (hA : Fintype.card A ≤ Fintype.card V) (n : ℕ) (x : BooleanBarycentricRing A K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : finiteVertexMap F hA x ∈ polynomialDegreePiece n :=
  vertexTransportLinear_graded _ _ (fun n x hx => hF _ n x hx) n x hx

theorem finiteVertexMap_normalized (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ s, F s 1 = 1) (hA : Fintype.card A ≤ Fintype.card V) :
    finiteVertexMap F hA 1 = 1 := vertexTransportLinear_normalized _ _ (hF _)

end SimplexPlacements

section PosetTransport
variable {P V K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype V] [CommRing K]

def symmetricSimplexStalkFamily (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) : StalkLinearFamily (P := P) K :=
  fun p => finiteVertexMap F (by rw [card_faceVertex]; exact hP p)

theorem symmetricSimplexStalkFamily_coherent (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F) :
    symmetricSimplexStalkFamily F hP ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  rw [polynomialRestriction_eq_killCompl]
  exact finiteVertexMap_restriction F hF hσ _ _ (faceVertexInclusion h) x

theorem symmetricSimplexStalkFamily_parameter (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ parameterStalkFamilySubmodule K) :
    symmetricSimplexStalkFamily F hP ∈ parameterStalkFamilySubmodule K := by
  intro p r x
  exact finiteVertexMap_parameter F hF _ r x

theorem symmetricSimplexStalkFamily_graded (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ gradedStalkFamilySubmodule K) :
    symmetricSimplexStalkFamily F hP ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  exact finiteVertexMap_graded F hF _ n x hx

theorem symmetricSimplexStalkFamily_normalized (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) (hF : ∀ s, F s 1 = 1) :
    ∀ p, symmetricSimplexStalkFamily F hP p 1 = 1 := by
  intro p
  exact finiteVertexMap_normalized F hF _

theorem symmetricSimplexStalkFamily_equivariant (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (e : P ≃o P) (p : P) (x : BarycentricStalk K p) :
    polynomialStalkOrderEquiv K e p (symmetricSimplexStalkFamily F hP p x) =
      symmetricSimplexStalkFamily F hP (e p) (barycentricStalkOrderEquiv K e p x) :=
  finiteVertexMap_relabel F hF hσ _ _ (faceVertexOrderEquiv e p) x

def symmetricSimplexCoherentLinearMap (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F) :
    CoherentLinearMap K (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component := symmetricSimplexStalkFamily F hP
  naturality := symmetricSimplexStalkFamily_coherent F hP hF hσ

end PosetTransport
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCoherentIsomorphism.lean -/
section

section
/-! # From normalized coherent parameter families to actual isomorphisms

The induction is on the actual face rank.  At the bottom, a normalized
linear map is the unique map of constant stalks.  At every positive face,
the already proved lower-face isomorphisms give an actual boundary
isomorphism, and the positive-degree lifting theorem proves bijectivity.
The resulting global comparison is an isomorphism of the original quotient
presentations, linear over their stated universal parameters.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]

theorem coherentNormalizedFamily_bijective (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    ∀ p, Function.Bijective (F p) := by
  have hmain : ∀ n (p : P), faceRank p = n → Function.Bijective (F p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      letI : LinearOrder (FaceVertex p) := LinearOrder.lift'
        (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
      by_cases hbot : p = ⊥
      · subst p
        letI := emptyFaceVertex (P := P)
        have he : F ⊥ = (canonicalBooleanPolynomial (V := FaceVertex (⊥ : P)) (K := K)).toLinearMap :=
          boolean_empty_linear_ext_one _ _ ((h₁ ⊥).trans canonicalBooleanPolynomial_one.symm)
        rw [he]
        exact canonicalBooleanPolynomial.bijective
      · have hpos : 0 < Fintype.card (FaceVertex p) := by
          rw [card_faceVertex]
          have hh := faceRank_strictMono hs (bot_lt_iff_ne_bot.mpr hbot)
          simpa only [faceRank_bot] using hh
        letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hpos
        let e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
            ((polynomialDiagram K).restrict (Set.Iio p)) := {
          component := fun q => LinearEquiv.ofBijective (F q.val)
            (ih (faceRank q.val) (by rw [← hn]; exact faceRank_strictMono hs q.property) q.val rfl)
          naturality := fun q r h x => hc q.val r.val h x }
        exact coherentStalkLift_bijective K hs p e (fun q => hd q.val) (F p)
          (intertwinesAllRanks_parameterLinear (F p) (hp p)) (hd p)
          (fun q x => hc p q.val q.property.le x)
  intro p
  exact hmain (faceRank p) p rfl

def coherentNormalizedFamilyEquiv (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component p := LinearEquiv.ofBijective (F p) (coherentNormalizedFamily_bijective hs F hc hp hd h₁ p)
  naturality := hc

@[simp] theorem coherentNormalizedFamilyEquiv_apply (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1)
    (p : P) (x : BarycentricStalk K p) :
    (coherentNormalizedFamilyEquiv hs F hc hp hd h₁).component p x = F p x := rfl

def coherentNormalizedParameterComparison (hs : IsSimplicialPoset P) (d : ℕ)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) :=
  originalParameterComparison K hs d (coherentNormalizedFamilyEquiv hs F hc hp hd h₁)
    (fun p r x => hp p r x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/OriginalAutomorphisms.lean -/
section

section
/-! # The natural automorphisms of the original face-ring presentations

Every action in this file is induced by renaming the actual face variables.
The quotient ideals and the rank-sum parameters are proved invariant.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def nonzeroFaceOrderEquiv (e : P ≃o P) : NonzeroFace P ≃ NonzeroFace P where
  toFun p := ⟨e p.val, fun h => p.property (e.injective (h.trans e.map_bot.symm))⟩
  invFun p := ⟨e.symm p.val, fun h => p.property (e.symm.injective (h.trans e.symm.map_bot.symm))⟩
  left_inv p := Subtype.ext (e.symm_apply_apply p.val)
  right_inv p := Subtype.ext (e.apply_symm_apply p.val)

@[simp] theorem nonzeroFaceOrderEquiv_apply (e : P ≃o P) (p : NonzeroFace P) :
    (nonzeroFaceOrderEquiv e p).val = e p.val := rfl

theorem faceSymbol_rename (e : P ≃o P) (p : P) :
    MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p) =
      faceSymbol K (e p) := by
  by_cases hp : p = ⊥
  · subst p
    simp [faceSymbol, e.map_bot]
  · have he : e p ≠ ⊥ := fun h => hp (e.injective (h.trans e.map_bot.symm))
    simp only [faceSymbol, dif_neg hp, dif_neg he, rename_X]
    rfl

theorem minimalCommonUppers_orderIso (e : P ≃o P) (p q : P) :
    minimalCommonUppers (e p) (e q) = (minimalCommonUppers p q).image e := by
  ext w
  simp only [mem_minimalCommonUppers, Finset.mem_image]
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    refine ⟨by simpa using e.symm.monotone hw.1,
      by simpa using e.symm.monotone hw.2.1, ?_⟩
    intro v hp hq hv
    apply e.injective
    exact (hw.2.2 (e v) (e.monotone hp) (e.monotone hq)
      (by simpa using e.monotone hv)).trans (e.apply_symm_apply w).symm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨e.monotone hv.1, e.monotone hv.2.1, ?_⟩
    intro w hp hq hw
    have hh := hv.2.2 (e.symm w) (by simpa using e.symm.monotone hp)
      (by simpa using e.symm.monotone hq) (by simpa using e.symm.monotone hw)
    simpa using congrArg e hh

theorem faceMeetBelow_orderIso (e : P ≃o P) (p q w : P)
    (hp : p ≤ w) (hq : q ≤ w) :
    e (faceMeetBelow hs p q w hp hq) =
      faceMeetBelow hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq) := by
  apply le_antisymm
  · exact le_faceMeetBelow hs _ _ _ _ _
      (e.monotone (faceMeetBelow_le_left hs p q w hp hq))
      (e.monotone (faceMeetBelow_le_right hs p q w hp hq))
  · have hl := e.symm.monotone
      (faceMeetBelow_le_left hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq))
    have hr := e.symm.monotone
      (faceMeetBelow_le_right hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq))
    have hm := le_faceMeetBelow hs p q w hp hq
      (by simpa only [e.symm_apply_apply] using hl)
      (by simpa only [e.symm_apply_apply] using hr)
    simpa only [e.apply_symm_apply] using e.monotone hm

theorem faceRelations_rename (e : P ≃o P) {f : FacePolynomial (P := P) K}
    (hf : f ∈ faceRelations K hs) :
    MvPolynomial.rename (nonzeroFaceOrderEquiv e) f ∈ faceRelations K hs := by
  rcases hf with ⟨p, q, w, hp, hq, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · left
    refine ⟨e p, e q, e w, e.monotone hp, e.monotone hq, ?_⟩
    rw [map_sub, map_mul, map_mul, map_sum, faceSymbol_rename, faceSymbol_rename,
      faceSymbol_rename, faceMeetBelow_orderIso, minimalCommonUppers_orderIso]
    congr 1
    congr 1
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      exact faceSymbol_rename K e a
    · exact fun _ _ _ _ h => e.injective h
  · right
    refine ⟨e p, e q, ?_, ?_⟩
    · rintro ⟨w, hp, hq⟩
      exact hnone ⟨e.symm w, by simpa using e.symm.monotone hp,
        by simpa using e.symm.monotone hq⟩
    · rw [map_mul, faceSymbol_rename, faceSymbol_rename]

def faceRingOrderMap (e : P ≃o P) : FaceRing K hs →ₐ[K] FaceRing K hs := by
  let f := (Ideal.Quotient.mkₐ K (faceIdeal K hs)).comp
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e))
  apply Ideal.Quotient.liftₐ (faceIdeal K hs) f
  have hh : faceIdeal K hs ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    change Ideal.Quotient.mk (faceIdeal K hs)
      (MvPolynomial.rename (nonzeroFaceOrderEquiv e) p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (faceRelations_rename K hs e hp))
  exact fun p hp => hh hp

@[simp] theorem faceRingOrderMap_mk (e : P ≃o P) (f : FacePolynomial (P := P) K) :
    faceRingOrderMap K hs e (Ideal.Quotient.mk (faceIdeal K hs) f) =
      Ideal.Quotient.mk (faceIdeal K hs)
        (MvPolynomial.rename (nonzeroFaceOrderEquiv e) f) := rfl

def barycentricRingOrderMap (e : P ≃o P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricRing (P := P) K := by
  let f := (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).comp
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e))
  apply Ideal.Quotient.liftₐ (barycentricIdeal K) f
  have hh : barycentricIdeal (P := P) K ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨a, b, hab, hba, rfl⟩
    change Ideal.Quotient.mk (barycentricIdeal K)
      (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (X a * X b)) = 0
    rw [map_mul, rename_X, rename_X]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨nonzeroFaceOrderEquiv e a, nonzeroFaceOrderEquiv e b,
      fun h => hab (e.le_iff_le.mp h), fun h => hba (e.le_iff_le.mp h), rfl⟩
  exact fun p hp => hh hp

@[simp] theorem barycentricRingOrderMap_mk (e : P ≃o P) (f : FacePolynomial (P := P) K) :
    barycentricRingOrderMap K e (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal K)
        (MvPolynomial.rename (nonzeroFaceOrderEquiv e) f) := rfl

theorem faceRingOrderMap_inverse (e : P ≃o P) (x : FaceRing K hs) :
    faceRingOrderMap K hs e.symm (faceRingOrderMap K hs e x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [faceRingOrderMap_mk, faceRingOrderMap_mk, rename_rename]
  have he : (nonzeroFaceOrderEquiv e.symm) ∘ nonzeroFaceOrderEquiv e = id := by
    funext p
    exact Subtype.ext (e.symm_apply_apply p.val)
  rw [he, rename_id_apply]

theorem barycentricRingOrderMap_inverse (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    barycentricRingOrderMap K e.symm (barycentricRingOrderMap K e x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [barycentricRingOrderMap_mk, barycentricRingOrderMap_mk, rename_rename]
  have he : (nonzeroFaceOrderEquiv e.symm) ∘ nonzeroFaceOrderEquiv e = id := by
    funext p
    exact Subtype.ext (e.symm_apply_apply p.val)
  rw [he, rename_id_apply]

def faceRingOrderAut (e : P ≃o P) : FaceRing K hs ≃ₐ[K] FaceRing K hs :=
  AlgEquiv.ofAlgHom (faceRingOrderMap K hs e) (faceRingOrderMap K hs e.symm)
    (by ext x; exact faceRingOrderMap_inverse K hs e.symm x)
    (by ext x; exact faceRingOrderMap_inverse K hs e x)

def barycentricRingOrderAut (e : P ≃o P) :
    BarycentricRing (P := P) K ≃ₐ[K] BarycentricRing (P := P) K :=
  AlgEquiv.ofAlgHom (barycentricRingOrderMap K e) (barycentricRingOrderMap K e.symm)
    (by ext x; exact barycentricRingOrderMap_inverse K e.symm x)
    (by ext x; exact barycentricRingOrderMap_inverse K e x)

@[simp] theorem faceRingOrderAut_generator (e : P ≃o P) (p : P) :
    faceRingOrderAut K hs e (faceRingGenerator K hs p) = faceRingGenerator K hs (e p) := by
  change Ideal.Quotient.mk (faceIdeal K hs)
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p)) = _
  rw [faceSymbol_rename]
  rfl

@[simp] theorem barycentricRingOrderAut_generator (e : P ≃o P) (p : P) :
    barycentricRingOrderAut K e (barycentricGenerator K p) = barycentricGenerator K (e p) := by
  change Ideal.Quotient.mk (barycentricIdeal K)
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p)) = _
  rw [faceSymbol_rename]
  rfl

theorem rankFaces_orderIso (e : P ≃o P) (r : ℕ) :
    (univ.filter fun p : P => faceRank p = r).image e =
      univ.filter fun p : P => faceRank p = r := by
  ext p
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [faceRank_eq_of_orderIso]
  · intro hp
    exact ⟨e.symm p, by simpa only [faceRank_eq_of_orderIso] using hp, e.apply_symm_apply p⟩

@[simp] theorem faceRingOrderAut_parameter (e : P ≃o P) (r : ℕ) :
    faceRingOrderAut K hs e (faceRankParameter K hs r) = faceRankParameter K hs r := by
  simp only [faceRankParameter, map_sum, faceRingOrderAut_generator]
  conv_rhs => rw [← rankFaces_orderIso e r]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => e.injective h

@[simp] theorem barycentricRingOrderAut_parameter (e : P ≃o P) (r : ℕ) :
    barycentricRingOrderAut K e (barycentricRankParameter K r) = barycentricRankParameter K r := by
  simp only [barycentricRankParameter, map_sum, barycentricRingOrderAut_generator]
  conv_rhs => rw [← rankFaces_orderIso e r]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => e.injective h

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGlobalEquivariance.lean -/
section

section
/-! # Equivariance on the actual quotient presentations

The global actions rename the original face variables.  Their compatibility
with polynomial and Boolean stalk evaluation is proved on those generators.
Consequently an equivariant coherent stalk comparison induces an equivariant
parameter-module equivalence on the original face rings.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem stalkVertexSet_order (e : P ≃o P) (p q : P) :
    (stalkVertexSet p q).map (faceVertexOrderEquiv e p).toEmbedding =
      stalkVertexSet (e p) (e q) := by
  ext a
  simp only [Finset.mem_map_equiv, mem_stalkVertexSet, faceVertexOrderEquiv_symm_apply]
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using e.monotone h
  · intro h
    simpa only [e.symm_apply_apply] using e.symm.monotone h

theorem faceProduct_order (e : P ≃o P) (p q : P) :
    polynomialStalkOrderEquiv K e p (faceProduct K p q) = faceProduct K (e p) (e q) := by
  unfold faceProduct
  rw [map_prod, ← stalkVertexSet_order e p q, Finset.prod_map]
  simp only [polynomialStalkOrderEquiv_X, Function.Embedding.coeFn_mk]

theorem faceValue_order (e : P ≃o P) (p q : P) :
    polynomialStalkOrderEquiv K e p (faceValue K p q) = faceValue K (e p) (e q) := by
  by_cases h : q ≤ p
  · rw [faceValue, if_pos h, faceValue, if_pos (e.monotone h), faceProduct_order]
  · have he : ¬ e q ≤ e p := fun hh => h (e.le_iff_le.mp hh)
    rw [faceValue, if_neg h, faceValue, if_neg he, map_zero]

theorem faceRingEvaluation_orderAut (e : P ≃o P) (p : P) (x : FaceRing K hs) :
    faceRingEvaluation K hs (e p) (faceRingOrderAut K hs e x) =
      polynomialStalkOrderEquiv K e p (faceRingEvaluation K hs p x) := by
  have h : ((faceRingEvaluation K hs (e p)).comp (faceRingOrderAut K hs e).toAlgHom).comp
      (Ideal.Quotient.mkₐ K (faceIdeal K hs)) =
      ((polynomialStalkOrderEquiv K e p).toAlgHom.comp (faceRingEvaluation K hs p)).comp
        (Ideal.Quotient.mkₐ K (faceIdeal K hs)) := by
    apply MvPolynomial.algHom_ext
    intro a
    have hg : faceRingEvaluation K hs (e p)
        (faceRingOrderAut K hs e (faceRingGenerator K hs a.val)) =
          polynomialStalkOrderEquiv K e p (faceRingEvaluation K hs p (faceRingGenerator K hs a.val)) := by
      rw [faceRingOrderAut_generator, faceRingEvaluation_generator, faceRingEvaluation_generator]
      exact (faceValue_order K e p a.val).symm
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      faceRingGenerator, faceSymbol_nonzero] using hg
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem booleanFaceInclusion_order (e : P ≃o P) (p : P)
    (F : BooleanFace (FaceVertex p)) :
    (booleanFaceInclusion hs (e p)
      (booleanFaceEmbedding (faceVertexOrderEquiv e p).toEmbedding F)).val =
        e (booleanFaceInclusion hs p F).val := by
  apply faceVertices_injective_below hs (booleanFaceInclusion_le hs (e p) _)
    (e.monotone (booleanFaceInclusion_le hs p F))
  rw [← image_stalkVertexSet (booleanFaceInclusion_le hs (e p) _),
    stalkVertexSet_booleanFaceInclusion,
    ← image_stalkVertexSet (e.monotone (booleanFaceInclusion_le hs p F)),
    ← stalkVertexSet_order e p (booleanFaceInclusion hs p F).val,
    stalkVertexSet_booleanFaceInclusion]
  rfl

theorem barycentricRingEvaluation_orderAut (e : P ≃o P) (p : P)
    (x : BarycentricRing (P := P) K) :
    barycentricRingEvaluation K hs (e p) (barycentricRingOrderAut K e x) =
      barycentricStalkOrderEquiv K e p (barycentricRingEvaluation K hs p x) := by
  have h : ((barycentricRingEvaluation K hs (e p)).comp (barycentricRingOrderAut K e).toAlgHom).comp
      (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)) =
      ((barycentricStalkOrderEquiv K e p).toAlgHom.comp (barycentricRingEvaluation K hs p)).comp
        (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)) := by
    apply MvPolynomial.algHom_ext
    intro a
    have hg : barycentricRingEvaluation K hs (e p)
        (barycentricRingOrderAut K e (barycentricGenerator K a.val)) =
          barycentricStalkOrderEquiv K e p
            (barycentricRingEvaluation K hs p (barycentricGenerator K a.val)) := by
      rw [barycentricRingOrderAut_generator]
      by_cases ha : a.val ≤ p
      · obtain ⟨F, rfl⟩ := (booleanFaceInclusion_range_iff hs p a).mpr ha
        rw [← booleanFaceInclusion_order hs e p F,
          barycentricRingEvaluation_included, barycentricRingEvaluation_included]
        exact (booleanVertexRelabelEquiv_face (K := K) (faceVertexOrderEquiv e p) F).symm
      · have he : ¬ e a.val ≤ e p := fun h => ha (e.le_iff_le.mp h)
        rw [barycentricRingEvaluation_outside K hs (e p) (e a.val) he,
          barycentricRingEvaluation_outside K hs p a.val ha, map_zero]
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      barycentricGenerator, faceSymbol_nonzero] using hg
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem originalComparison_equivariant_of_stalk
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hE : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (E.component p x) =
      E.component (e p) (barycentricStalkOrderEquiv K e p x))
    (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    faceRingOrderAut K hs e (originalComparison K hs E x) =
      originalComparison K hs E (barycentricRingOrderAut K e x) := by
  apply (faceRingSectionEquiv K hs).injective
  apply Subtype.ext
  funext p
  obtain ⟨q, rfl⟩ := e.surjective p
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  rw [faceRingEvaluation_orderAut, originalComparison_evaluation,
    originalComparison_evaluation, barycentricRingEvaluation_orderAut]
  exact hE e q _

theorem coherentNormalizedParameterComparison_equivariant (d : ℕ)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1)
    (he : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (F p x) =
      F (e p) (barycentricStalkOrderEquiv K e p x))
    (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    faceRingOrderAut K hs e ((coherentNormalizedParameterComparison hs d F hc hp hd h₁).toLinearEquiv x) =
      (coherentNormalizedParameterComparison hs d F hc hp hd h₁).toLinearEquiv
        (barycentricRingOrderAut K e x) :=
  originalComparison_equivariant_of_stalk K hs
    (coherentNormalizedFamilyEquiv hs F hc hp hd h₁) he e x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPositiveTheorem.lean -/
section


section

/-! # The positive direction of Theorem 1.3

The factorial-unit hypothesis first gives a full symmetric template on a
simplex of rank `d`.  Ordinary averaging handles the full-factorial branch;
the integral cyclic construction and relative trace handle prime top rank.
The template is then transported to every actual face of any finite
simplicial poset of maximum rank at most `d`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical

structure SymmetricSimplexTemplate (K : Type*) [CommRing K] (d : ℕ) where
  Vertex : Type
  [fintypeVertex : Fintype Vertex]
  card_eq : Fintype.card Vertex = d
  family : StalkLinearFamily (P := Finset Vertex) K
  coherent : family ∈ coherentStalkFamilySubmodule K
  parameter : family ∈ parameterStalkFamilySubmodule K
  graded : family ∈ gradedStalkFamilySubmodule K
  normalized : ∀ s, family s 1 = 1
  symmetric : ∀ e : Equiv.Perm Vertex, stalkFamilyRelabel K (finsetOrderCongr e) family = family

attribute [instance] SymmetricSimplexTemplate.fintypeVertex

theorem exists_symmetric_simplex_template (K : Type*) [CommRing K]
    (d : ℕ) (hd : 1 ≤ d) (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    Nonempty (SymmetricSimplexTemplate K d) := by
  rcases full_factorial_isUnit_or_prime hd hD with hfull | hprime
  · obtain ⟨F, hc, hp, hg, hscalar, he⟩ := exists_integral_factorial_simplex_family (V := Fin d)
    have hm : IsUnit (((Fintype.card (Fin d)).factorial : ℕ) : K) := by simpa using hfull
    obtain ⟨L, hLc, hLp, hLg, hL₁, hLe⟩ := exists_normalized_scalar_extension K
      (simplex_isSimplicialPoset (V := Fin d)) F (Fintype.card (Fin d)).factorial hm hc hp hg hscalar
    exact ⟨{
      Vertex := Fin d
      card_eq := Fintype.card_fin d
      family := L
      coherent := hLc
      parameter := hLp
      graded := hLg
      normalized := hL₁
      symmetric := fun e => hLe (finsetOrderCongr e) (he e) }⟩
  · letI : Fact d.Prime := ⟨hprime⟩
    letI : LinearOrder (ZMod d) := LinearOrder.lift' ZMod.val (ZMod.val_injective d)
    obtain ⟨F, hc, hp, hg, hscalar, he⟩ := exists_integral_prime_symmetric_simplex_family d
    obtain ⟨L, hLc, hLp, hLg, hL₁, hLe⟩ := exists_normalized_scalar_extension K
      (simplex_isSimplicialPoset (V := ZMod d)) F (d - 1).factorial hD hc hp hg hscalar
    exact ⟨{
      Vertex := ZMod d
      card_eq := ZMod.card d
      family := L
      coherent := hLc
      parameter := hLp
      graded := hLg
      normalized := hL₁
      symmetric := fun e => hLe (finsetOrderCongr e) (he e) }⟩

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
include hs

/-- A genuine coherent graded parameter-module comparison, invariant under
every order automorphism.  The full automorphism group therefore works
simultaneously, and restriction to any automorphism-group action follows. -/
theorem exists_coherent_equivariant_parameter_comparison
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      (∀ p, E.component p 1 = 1) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x) := by
  let T := Classical.choice (exists_symmetric_simplex_template K d hd hD)
  have hP : ∀ p : P, faceRank p ≤ Fintype.card T.Vertex := by
    intro p
    rw [T.card_eq]
    exact hrank p
  let F : StalkLinearFamily (P := P) K := symmetricSimplexStalkFamily T.family hP
  have hc : F ∈ coherentStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_coherent T.family hP T.coherent T.symmetric
  have hp : F ∈ parameterStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_parameter T.family hP T.parameter
  have hg : F ∈ gradedStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_graded T.family hP T.graded
  have h₁ : ∀ p, F p 1 = 1 := symmetricSimplexStalkFamily_normalized T.family hP T.normalized
  refine ⟨coherentNormalizedFamilyEquiv hs F hc hp hg h₁, hp, hg, h₁, ?_⟩
  intro e p x
  exact symmetricSimplexStalkFamily_equivariant T.family hP T.coherent T.symmetric e p x

/-- **Theorem 1.3, positive direction.**  All ranks up to `d`, arbitrary
commutative coefficient rings, actual coherent stalk isomorphisms, actual
parameter actions, and every order automorphism are retained. -/
theorem theorem_1_3_positive
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      (∀ p, E.component p 1 = 1) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x) :=
  exists_coherent_equivariant_parameter_comparison K hs d hd hrank hD

/-- The same positive theorem on the original quotient presentations.  The
last conjunct retains the actual coherent family and its evaluation squares,
so the global equivalence includes the paper's compatibility with restriction.
The degree assertion is an equivalence for the usual quotient grading, rather
than a statement about an auxiliary choice of basis. -/
theorem theorem_1_3_positive_original
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ T : ParameterEquiv (barycentricParameterAction (P := P) K d)
        (faceParameterAction K hs d),
      (∀ n x, T.toLinearEquiv x ∈ usualFaceDegreePiece K hs n ↔
        x ∈ usualBarycentricDegreePiece K n) ∧
      T.toLinearEquiv 1 = 1 ∧
      (∀ (e : P ≃o P) x,
        faceRingOrderAut K hs e (T.toLinearEquiv x) =
          T.toLinearEquiv (barycentricRingOrderAut K e x)) ∧
      ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
        (∀ (p : P) (r : ℕ) x,
          E.component p (booleanRankParameter (r + 1) * x) =
            polynomialParameter K p (r + 1) * E.component p x) ∧
        (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
          (fun a => booleanOrdinaryDegree a.val) n →
            E.component p x ∈ polynomialDegreePiece n) ∧
        (∀ p, E.component p 1 = 1) ∧
        (∀ (e : P ≃o P) p x,
          polynomialStalkOrderEquiv K e p (E.component p x) =
            E.component (e p) (barycentricStalkOrderEquiv K e p x)) ∧
        ∀ x p, faceRingEvaluation K hs p (T.toLinearEquiv x) =
          E.component p (barycentricRingEvaluation K hs p x) := by
  obtain ⟨E, hp, hg, h₁, he⟩ :=
    exists_coherent_equivariant_parameter_comparison K hs d hd hrank hD
  let T := originalParameterComparison K hs d E hp
  have hdegree : ∀ (a b : StandardFaceIndex P),
      standardOrdinaryDegree b ≠ standardOrdinaryDegree a →
      (standardFaceBasis K hs).repr
        (T.toLinearEquiv (barycentricGlobalStandardBasis K a)) b = 0 :=
    originalComparison_degree K hs E
      (fun p => hasStandardDegree_of_ordinary_degree K hs p (E.component p).toLinearMap (hg p))
  refine ⟨T, ?_, ?_, ?_, E, hp, hg, h₁, he, ?_⟩
  · intro n x
    rw [usualFaceDegreePiece_eq, usualBarycentricDegreePiece_eq]
    exact basisOrdinaryDegreePiece_equiv_iff (barycentricGlobalStandardBasis K)
      (standardFaceBasis K hs) standardOrdinaryDegree T.toLinearEquiv hdegree n x
  · apply (faceRingSectionEquiv K hs).injective
    apply Subtype.ext
    funext p
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
    change faceRingEvaluation K hs p (originalComparison K hs E 1) =
      faceRingEvaluation K hs p 1
    rw [originalComparison_evaluation]
    exact (congrArg (E.component p) (map_one (barycentricRingEvaluation K hs p))).trans
      ((h₁ p).trans (map_one (faceRingEvaluation K hs p)).symm)
  · exact originalComparison_equivariant_of_stalk K hs E he
  · exact originalComparison_evaluation K hs E

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ObstructionEigenfunctional.lean -/
section

section
/-! # The modular obstruction without specialization machinery

A parameter-eigenfunctional on the polynomial ring, evaluated at a fixed root
assignment, cannot be transported to a ring whose active-parameter product is
a sum of monomials freely permuted in modular characteristic. This argument
works over the original coefficient ring; the functional may take values in
a polynomial ring over a residue field. It does not assume that an isomorphism
preserves constants, multiplication, a grading, or face restrictions.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal
open Classical Finset

variable {G T I K R B L : Type*}
  [Group G] [Fintype G] [Fintype T] [MulAction G T]
  [CommRing K] [CommRing R] [Algebra K R] [CommRing B] [Algebra K B]
  [CommRing L] [IsDomain L]

/-- The exact algebraic contradiction used for the prime-cycle obstruction.
All the expansion and action hypotheses are instantiated by actual polynomial
and Stanley--Reisner rings in `PrimeCycleObstruction`. -/
theorem no_equiv_of_free_parameter_expansion
    (a : I → R) (b : I → B) (s : Finset I)
    (ρR : G → R →ₐ[K] R) (ρB : G → B →ₐ[K] B)
    (ev : R →+* L) (hev : ∀ g x, ev (ρR g x) = ev x)
    (m : T → B) (hm : ∀ g t, m (g • t) = ρB g (m t))
    (hprod : (∏ i ∈ s, b i) = ∑ t, m t)
    (hactive : ∀ i ∈ s, ev (a i) ≠ 0)
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : L) = 0)
    (f : R ≃ₗ[K] B)
    (hparameter : ∀ i x, f (a i * x) = b i * f x)
    (hequivariant : ∀ g x, f (ρR g x) = ρB g (f x)) : False := by
  let ℓ : B →+ L := ev.toAddMonoidHom.comp f.symm.toLinearMap.toAddMonoidHom
  have hinvParameter : ∀ i x, f.symm (b i * x) = a i * f.symm x := by
    intro i x
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hparameter, LinearEquiv.apply_symm_apply]
  have hinvAction : ∀ g x, f.symm (ρB g x) = ρR g (f.symm x) := by
    intro g x
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hequivariant, LinearEquiv.apply_symm_apply]
  have hℓparameter : ∀ i x, ℓ (b i * x) = ev (a i) * ℓ x := by
    intro i x
    change ev (f.symm (b i * x)) = ev (a i) * ev (f.symm x)
    rw [hinvParameter, map_mul]
  have hℓaction : ∀ g x, ℓ (ρB g x) = ℓ x := by
    intro g x
    change ev (f.symm (ρB g x)) = ev (f.symm x)
    rw [hinvAction, hev]
  have hvector : ∀ g, ρB g (f 1) = f 1 := by
    intro g
    rw [← hequivariant, map_one]
  have hvalue : ℓ (f 1) = 1 := by
    change ev (f.symm (f 1)) = 1
    rw [LinearEquiv.symm_apply_apply, map_one]
  have hprodValue : ∀ t : Finset I,
      ℓ ((∏ i ∈ t, b i) * f 1) = ∏ i ∈ t, ev (a i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hvalue
    | @insert i t hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_assoc, hℓparameter, ih]
  have hconst : ∀ (g : G) (t : T), ℓ (m (g • t) * f 1) = ℓ (m t * f 1) := by
    intro g t
    calc
      ℓ (m (g • t) * f 1) = ℓ (ρB g (m t) * ρB g (f 1)) := by
        rw [hm, hvector]
      _ = ℓ (ρB g (m t * f 1)) := congrArg ℓ (map_mul (ρB g) _ _).symm
      _ = ℓ (m t * f 1) := hℓaction g _
  have hzero : ℓ ((∏ i ∈ s, b i) * f 1) = 0 := by
    rw [hprod, Finset.sum_mul, map_sum]
    exact sum_eq_zero_of_free_action hfree horder (fun t => ℓ (m t * f 1)) hconst
  rw [hprodValue] at hzero
  exact (Finset.prod_ne_zero_iff.mpr hactive) hzero

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ColoredFlagCore.lean -/
section

section
/-! # Original-ring flag indexing and literal vertex actions

Only the definitions used by the unrestricted eigenfunctional obstruction
are collected here. The earlier quotient-fibre development remains in
`ColorFiberComponents.lean` and `ColoredAutomorphisms.lean` as an inactive
draft; the negative theorem does not depend on it. Each declaration body
below is copied exactly from those sources, with its original section
parameters retained. Extraction hashes are recorded in the audit manifest.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ProperlyColoredComplex
open Classical Finset MvPolynomial
section General
variable {V C K G : Type*} [Fintype V] [Fintype C] [CommRing K] [Group G]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C) (K)

def colorRename (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s) : D.Ring K →ₐ[K] D.Ring K := by
  let f := (Ideal.Quotient.mkₐ K (forbiddenIdeal D.allowed)).comp (MvPolynomial.rename e)
  apply Ideal.Quotient.liftₐ (forbiddenIdeal D.allowed) f
  have hh : forbiddenIdeal D.allowed ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (forbiddenIdeal D.allowed)
      (MvPolynomial.rename e (MvPolynomial.monomial a (1 : K))) = 0
    rw [MvPolynomial.rename_monomial]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    refine ⟨a.mapDomain e, ?_, rfl⟩
    intro h
    apply ha
    change D.face (a.mapDomain e).support at h
    rw [Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _)] at h
    exact (hface a.support).mp h
  exact fun p hp => hh hp

@[simp] theorem colorRename_mk (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s) (p : MvPolynomial V K) :
    D.colorRename K e hface (Ideal.Quotient.mk (forbiddenIdeal D.allowed) p) =
      Ideal.Quotient.mk (forbiddenIdeal D.allowed) (MvPolynomial.rename e p) := rfl

def colorFiberEquiv (e : Equiv.Perm V) (hcolor : ∀ v, D.color (e v) = D.color v) (i : C) :
    {v : V // D.color v = i} ≃ {v : V // D.color v = i} where
  toFun v := ⟨e v.val, (hcolor v.val).trans v.property⟩
  invFun v := ⟨e.symm v.val, by
    have hh := hcolor (e.symm v.val)
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

variable {K}

abbrev ActiveColor (c : C → K) := {i : C // c i ≠ 0}

abbrev FiberAssignment (c : C → K) :=
  (i : ActiveColor c) → {v : V // D.color v = i.val}

def assignmentVertices (c : C → K) (a : D.FiberAssignment c) : Finset V :=
  Finset.univ.image (fun i => (a i).val)

def assignmentExponents (c : C → K) (a : D.FiberAssignment c) : V →₀ ℕ :=
  ∑ i : ActiveColor c, Finsupp.single (a i).val 1

theorem assignmentExponents_support (c : C → K) (a : D.FiberAssignment c) :
    (D.assignmentExponents c a).support = D.assignmentVertices c a := by
  ext v
  simp only [assignmentExponents, Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
    Finsupp.single_apply, assignmentVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (Finset.sum_eq_zero (fun i hi => by rw [if_neg (hn i)]))
  · rintro ⟨i, hi⟩
    have hp : 0 < ∑ j : ActiveColor c, if (a j).val = v then 1 else 0 := by
      apply lt_of_lt_of_le (show 0 < (if (a i).val = v then 1 else 0 : ℕ) by simp [hi])
      exact Finset.single_le_sum
        (f := fun j : ActiveColor c => if (a j).val = v then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.ne_of_gt hp

end General

section Field
variable {V C K G : Type*} [Fintype V] [Fintype C] [Field K] [Group G]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C)
variable (ρ : G →* Equiv.Perm V)
  (hface : ∀ g s, D.face (s.image (ρ g)) ↔ D.face s)
  (hcolor : ∀ g v, D.color (ρ g v) = D.color v)

abbrev ActiveFlag (c : C → K) :=
  {a : D.FiberAssignment c // D.face (D.assignmentVertices c a)}

def assignmentRename (c : C → K) (e : Equiv.Perm V)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) : D.FiberAssignment c :=
  fun i => D.colorFiberEquiv e hcolor i.val (a i)

theorem assignmentRename_vertices (c : C → K) (e : Equiv.Perm V)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) :
    D.assignmentVertices c (D.assignmentRename c e hcolor a) =
      (D.assignmentVertices c a).image e := by
  simp only [assignmentVertices, assignmentRename, colorFiberEquiv, Finset.image_image]
  rfl

def activeFlagAction (c : C → K) : MulAction G (D.ActiveFlag c) where
  smul g a := ⟨D.assignmentRename c (ρ g) (hcolor g) a.val,
    by
      rw [D.assignmentRename_vertices]
      exact (hface g (D.assignmentVertices c a.val)).mpr a.property⟩
  one_smul a := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ρ 1 ((a.val i).val) = (a.val i).val
    rw [ρ.map_one]
    rfl
  mul_smul g h a := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ρ (g * h) ((a.val i).val) = ρ g (ρ h ((a.val i).val))
    rw [ρ.map_mul]
    rfl

end Field
end FourPapers.Universal.ProperlyColoredComplex

end
end
end

/- BEGIN FourPapers/Universal/ObstructionExpansion.lean -/
section

section
/-! # Active-rank expansion in the original face ring

The coefficients used to select ranks may belong to a different field from
the original coefficient ring. No base change of the original ring is made.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ProperlyColoredComplex
open Classical Finset MvPolynomial

variable {V C K L : Type*} [Fintype V] [Fintype C] [CommRing K] [Field L]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C) (K)

def assignmentMonomial (c : C → L) (a : D.FiberAssignment c) : D.Ring K :=
  ∏ i : ActiveColor c, Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X (a i).val)

theorem assignmentMonomial_eq_monomial (c : C → L) (a : D.FiberAssignment c) :
    D.assignmentMonomial K c a = D.monomial K (D.assignmentExponents c a) := by
  rw [assignmentMonomial, ← map_prod]
  congr 1
  rw [assignmentExponents, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro i hi
  rfl

theorem assignmentMonomial_forbidden (c : C → L) (a : D.FiberAssignment c)
    (ha : ¬ D.face (D.assignmentVertices c a)) : D.assignmentMonomial K c a = 0 := by
  rw [D.assignmentMonomial_eq_monomial K c a]
  apply D.monomial_eq_zero_of_forbidden K
  unfold allowed
  rwa [D.assignmentExponents_support]

theorem sum_assignmentMonomial (c : C → L) :
    (∑ a : D.FiberAssignment c, D.assignmentMonomial K c a) =
      ∏ i : ActiveColor c, D.colorParameter K i.val := by
  unfold assignmentMonomial
  rw [← Fintype.prod_sum (fun (i : ActiveColor c)
    (v : {v : V // D.color v = i.val}) =>
      Ideal.Quotient.mk (forbiddenIdeal (K := K) D.allowed) (X v.val))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Finset.sum_subtype (Finset.univ.filter (fun v => D.color v = i.val))
    (fun v => by simp) (fun v =>
      Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v : MvPolynomial V K))).symm

/-- The product of active color sums is the sum of exactly the allowed flags.
This is an identity in the original Stanley--Reisner quotient. -/
theorem sum_activeFlagMonomial (c : C → L) :
    (∑ a : D.ActiveFlag c, D.assignmentMonomial K c a.val) =
      ∏ i : ActiveColor c, D.colorParameter K i.val := by
  rw [← D.sum_assignmentMonomial K c]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : D.FiberAssignment c =>
    D.face (D.assignmentVertices c a))) (fun a => by simp)]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hn
  exact D.assignmentMonomial_forbidden K c a (by simpa using hn)

/-- The same finite identity with explicitly supplied enumerations.  This
avoids unfolding large finite function spaces when a specialized application
uses a different, propositionally equal `Fintype` instance. -/
theorem sum_activeFlagMonomial_withFintypes (c : C → L)
    (ft : Fintype (D.ActiveFlag c)) (fi : Fintype (ActiveColor c)) :
    (∑ a ∈ @Finset.univ (D.ActiveFlag c) ft, D.assignmentMonomial K c a.val) =
      ∏ i ∈ @Finset.univ (ActiveColor c) fi, D.colorParameter K i.val := by
  have hi : fi = Subtype.fintype (fun i : C => c i ≠ 0) := Subsingleton.elim _ _
  subst fi
  have ht : ft = Subtype.fintype
      (fun a : D.FiberAssignment c => D.face (D.assignmentVertices c a)) := Subsingleton.elim _ _
  subst ft
  exact D.sum_activeFlagMonomial K c

theorem colorRename_assignmentMonomial (c : C → L) (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) :
    D.colorRename K e hface (D.assignmentMonomial K c a) =
      D.assignmentMonomial K c (D.assignmentRename c e hcolor a) := by
  rw [assignmentMonomial, map_prod, assignmentMonomial]
  apply Finset.prod_congr rfl
  intro i hi
  rw [D.colorRename_mk K e hface, MvPolynomial.rename_X]
  rfl

end FourPapers.Universal.ProperlyColoredComplex

end
end
end

/- BEGIN FourPapers/Universal/ObstructionBoolean.lean -/
section

section
/-! # The actual Boolean order complex and its vertex permutations -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {V K : Type*} [Fintype V] [CommRing K]

local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _

/-- The properly rank-colored order complex of the full Boolean simplex.
Its monomial quotient is definitionally the existing barycentric ring. -/
def booleanColoredComplex (V : Type*) [Fintype V] :
    ProperlyColoredComplex (BooleanFace V) (Fin (Fintype.card V)) where
  face s := ∀ F ∈ s, ∀ G ∈ s, F.val ⊆ G.val ∨ G.val ⊆ F.val
  downward := by
    intro s t hst ht F hF G hG
    exact ht F (hst hF) G (hst hG)
  color := BooleanFace.color
  proper s hs F hF G hG he := by
    apply Subtype.ext
    have hc := BooleanFace.card_eq_of_color_eq he
    rcases hs F hF G hG with h | h
    · exact Finset.eq_of_subset_of_card_le h hc.ge
    · exact (Finset.eq_of_subset_of_card_le h hc.le).symm

theorem booleanColored_ring_eq :
    (booleanColoredComplex V).Ring K = BooleanBarycentricRing V K := rfl

theorem booleanColored_colorParameter (i : Fin (Fintype.card V)) :
    (booleanColoredComplex V).colorParameter K i = colorSum (K := K) i := by
  unfold ProperlyColoredComplex.colorParameter colorSum facesOfColor faceVariable
  apply Finset.sum_congr
  · ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · intro F hF
    rfl

def booleanFacePermutation (e : Equiv.Perm V) : Equiv.Perm (BooleanFace V) where
  toFun F := ⟨F.val.image e, F.property.image e⟩
  invFun F := ⟨F.val.image e.symm, F.property.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]

@[simp] theorem booleanFacePermutation_val (e : Equiv.Perm V) (F : BooleanFace V) :
    (booleanFacePermutation e F).val = F.val.image e := rfl

theorem booleanFacePermutation_color (e : Equiv.Perm V) (F : BooleanFace V) :
    BooleanFace.color (booleanFacePermutation e F) = BooleanFace.color F := by
  apply Fin.ext
  change (F.val.image e).card - 1 = F.val.card - 1
  rw [Finset.card_image_of_injective _ e.injective]

theorem permutation_image_subset_iff (e : Equiv.Perm V) (s t : Finset V) :
    s.image e ⊆ t.image e ↔ s ⊆ t := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    exact e.injective he ▸ hw
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨w, h hw, rfl⟩

theorem booleanFacePermutation_face (e : Equiv.Perm V) (s : Finset (BooleanFace V)) :
    (booleanColoredComplex V).face (s.image (booleanFacePermutation e)) ↔
      (booleanColoredComplex V).face s := by
  constructor
  · intro h F hF G hG
    have hh := h (booleanFacePermutation e F) (Finset.mem_image.mpr ⟨F, hF, rfl⟩)
      (booleanFacePermutation e G) (Finset.mem_image.mpr ⟨G, hG, rfl⟩)
    simpa only [booleanFacePermutation_val, permutation_image_subset_iff] using hh
  · intro h F hF G hG
    obtain ⟨F₀, hF₀, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨G₀, hG₀, rfl⟩ := Finset.mem_image.mp hG
    simpa only [booleanFacePermutation_val, permutation_image_subset_iff] using h F₀ hF₀ G₀ hG₀

def booleanFacePermHom : Equiv.Perm V →* Equiv.Perm (BooleanFace V) where
  toFun := booleanFacePermutation
  map_one' := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change F.val.image id = F.val
    exact Finset.image_id
  map_mul' e f := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change F.val.image (e * f) = (F.val.image f).image e
    rw [Finset.image_image]
    rfl

/-- Relabeling the genuine quotient ring by a vertex permutation. -/
def booleanRename (K : Type*) [CommRing K] (e : Equiv.Perm V) :
    BooleanBarycentricRing V K →ₐ[K] BooleanBarycentricRing V K :=
  (booleanColoredComplex V).colorRename K (booleanFacePermutation e)
    (booleanFacePermutation_face e)

theorem booleanRename_faceVariable (e : Equiv.Perm V) (F : BooleanFace V) :
    booleanRename K e (faceVariable (K := K) F) =
      faceVariable (K := K) (booleanFacePermutation e F) := by
  change (booleanColoredComplex V).colorRename K (booleanFacePermutation e)
    (booleanFacePermutation_face e) (Ideal.Quotient.mk _ (X F)) = _
  rw [(booleanColoredComplex V).colorRename_mk K (booleanFacePermutation e)
    (booleanFacePermutation_face e), MvPolynomial.rename_X]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleCoefficients.lean -/
section

section
/-! # The actual generic character for the prime-cycle obstruction

The moved roots are all one; the fixed roots are algebraically independent
variables.  The parameter values are the coefficients of
`(1+T^p) ∏(1+b_i T)`, interpreted in the fraction field of the polynomial
ring.  A coefficient of a specified squarefree monomial proves exactly which
ranks are active, in every characteristic p.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
section GenericCoefficient
variable {k : Type*} [CommRing k]

def fiberFaceExponent {V : Type*} (s : Finset V) : V →₀ ℕ :=
  ∑ v ∈ s, Finsupp.single v 1

@[simp] theorem fiberFaceExponent_apply {V : Type*} (s : Finset V) (v : V) :
    fiberFaceExponent s v = if v ∈ s then 1 else 0 := by
  simp [fiberFaceExponent, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem fiberFaceExponent_injective {V : Type*} :
    Function.Injective (fiberFaceExponent (V := V)) := by
  intro s t h
  ext v
  have hh := congrArg (fun a : V →₀ ℕ => a v) h
  simp only [fiberFaceExponent_apply] at hh
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp_all

/-- The specified monomial occurs once, over any coefficient ring. -/
theorem esymm_face_coefficient {V : Type*} [Fintype V] (s : Finset V) (n : ℕ) :
    (MvPolynomial.esymm V k n).coeff (fiberFaceExponent s) =
      if s.card = n then 1 else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.coeff_sum]
  change (∑ t ∈ Finset.powersetCard n Finset.univ,
    (MvPolynomial.monomial (fiberFaceExponent t) (1 : k)).coeff (fiberFaceExponent s)) = _
  simp only [MvPolynomial.coeff_monomial, fiberFaceExponent_injective.eq_iff]
  simp [Finset.mem_powersetCard]

theorem esymm_eq_zero_of_card_lt {V : Type*} [Fintype V] (n : ℕ) (hn : Fintype.card V < n) :
    MvPolynomial.esymm V k n = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr (by simpa using hn), Finset.sum_empty]

end GenericCoefficient

variable (p r : ℕ) (k : Type*) [CommRing k]

def primeFiberCoefficient (n : ℕ) : MvPolynomial (Fin r) k :=
  MvPolynomial.esymm (Fin r) k n +
    if p ≤ n then MvPolynomial.esymm (Fin r) k (n - p) else 0

theorem primeFiberCoefficient_nonzero_iff [Nontrivial k] (hp : 0 < p) (n : ℕ) :
    primeFiberCoefficient p r k n ≠ 0 ↔ n ≤ r ∨ (p ≤ n ∧ n ≤ p + r) := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [primeFiberCoefficient, esymm_eq_zero_of_card_lt n (by simpa using hn.1)]
    by_cases hp' : p ≤ n
    · rw [if_pos hp', esymm_eq_zero_of_card_lt (n - p) (by
        have hh := hn.2 hp'
        simp only [Fintype.card_fin]
        omega), zero_add]
    · rw [if_neg hp', add_zero]
  · rintro (hn | ⟨hp', hn⟩)
    · obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin r))) (by simpa using hn)
      intro hz
      have he := congrArg (fun f : MvPolynomial (Fin r) k => f.coeff (fiberFaceExponent s)) hz
      rw [primeFiberCoefficient, MvPolynomial.coeff_add, esymm_face_coefficient, hc,
        if_pos rfl, MvPolynomial.coeff_zero] at he
      by_cases hp' : p ≤ n
      · rw [if_pos hp', esymm_face_coefficient, hc, if_neg (by omega), add_zero] at he
        exact one_ne_zero he
      · simp only [if_neg hp', MvPolynomial.coeff_zero, Finsupp.zero_apply, add_zero] at he
        exact one_ne_zero he
    · obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin r))) (show n - p ≤ (Finset.univ : Finset (Fin r)).card by
          rw [Finset.card_univ, Fintype.card_fin]
          omega)
      intro hz
      have he := congrArg (fun f : MvPolynomial (Fin r) k => f.coeff (fiberFaceExponent s)) hz
      rw [primeFiberCoefficient, MvPolynomial.coeff_add, if_pos hp',
        esymm_face_coefficient, esymm_face_coefficient, hc, if_neg (by omega),
        if_pos rfl, zero_add, MvPolynomial.coeff_zero] at he
      exact one_ne_zero he

theorem primeFiberCoefficient_active [Nontrivial k] [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    primeFiberCoefficient p r k n ≠ 0 ↔ n ∈ primeCycleActiveRanks p r := by
  rw [primeFiberCoefficient_nonzero_iff p r k (Fact.out : p.Prime).pos]
  simp only [primeCycleActiveRanks, Finset.mem_union, Finset.mem_Icc]
  omega

def polynomialPrimeRoots [Fact p.Prime] : PrimeCycleVertex p r → MvPolynomial (Fin r) k :=
  Sum.elim (fun _ => 1) MvPolynomial.X

def fixedRootPolynomial : Polynomial (MvPolynomial (Fin r) k) :=
  ∏ b : Fin r, (Polynomial.X + Polynomial.C (MvPolynomial.X b))

theorem fixedRootPolynomial_coefficient (n : ℕ) (hn : n ≤ r) :
    (fixedRootPolynomial r k).coeff n = MvPolynomial.esymm (Fin r) k (r - n) := by
  have hh := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin r))
    (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k) (k := n) (by simpa using hn)
  simpa only [fixedRootPolynomial, Finset.card_univ, Fintype.card_fin, MvPolynomial.esymm] using hh

theorem fixedRootPolynomial_natDegree [Nontrivial k] :
    (fixedRootPolynomial r k).natDegree = r := by
  have hh := Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    (Finset.univ : Finset (Fin r)) (fun b => -(MvPolynomial.X b : MvPolynomial (Fin r) k))
  simpa only [fixedRootPolynomial, map_neg, sub_neg_eq_add, Finset.card_univ,
    Fintype.card_fin] using hh

theorem fixedRootPolynomial_coefficient_zero [Nontrivial k] (n : ℕ) (hn : r < n) :
    (fixedRootPolynomial r k).coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rwa [fixedRootPolynomial_natDegree]

theorem primeRootPolynomial_factorization [Fact p.Prime] [CharP k p] :
    (∏ v : PrimeCycleVertex p r,
      (Polynomial.X + Polynomial.C (polynomialPrimeRoots p r k v))) =
      (Polynomial.X ^ p + 1) * fixedRootPolynomial r k := by
  rw [Fintype.prod_sum_type]
  simp only [polynomialPrimeRoots, Sum.elim_inl, Sum.elim_inr, map_one,
    Finset.prod_const, Finset.card_univ, ZMod.card, fixedRootPolynomial]
  rw [add_pow_char, one_pow]

/-- The displayed generic coefficients are the actual elementary symmetric
parameter values at the fixed root assignment. -/
theorem primeRoots_esymm [Nontrivial k] [Fact p.Prime] [CharP k p]
    (n : ℕ) (hn : n ≤ p + r) :
    MvPolynomial.aeval (polynomialPrimeRoots p r k)
      (MvPolynomial.esymm (PrimeCycleVertex p r) k n) = primeFiberCoefficient p r k n := by
  have hcard : Fintype.card (PrimeCycleVertex p r) = p + r := by
    rw [Fintype.card_sum, ZMod.card, Fintype.card_fin]
  have he := Finset.prod_X_add_C_coeff (Finset.univ : Finset (PrimeCycleVertex p r))
    (polynomialPrimeRoots p r k) (k := p + r - n) (by
      rw [Finset.card_univ, hcard]
      omega)
  have he' : MvPolynomial.aeval (polynomialPrimeRoots p r k)
      (MvPolynomial.esymm (PrimeCycleVertex p r) k n) =
      (∏ v : PrimeCycleVertex p r,
        (Polynomial.X + Polynomial.C (polynomialPrimeRoots p r k v))).coeff (p + r - n) := by
    rw [he]
    rw [MvPolynomial.esymm, map_sum]
    simp only [map_prod, MvPolynomial.aeval_X, Finset.card_univ, hcard,
      Nat.sub_sub_self hn]
  rw [he', primeRootPolynomial_factorization, add_mul, one_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', primeFiberCoefficient]
  have hleft : (if p ≤ p + r - n then
      (fixedRootPolynomial r k).coeff (p + r - n - p) else 0) =
      MvPolynomial.esymm (Fin r) k n := by
    by_cases hnr : n ≤ r
    · rw [if_pos (by omega), fixedRootPolynomial_coefficient r k _ (by omega)]
      congr 1
      omega
    · rw [if_neg (by omega), esymm_eq_zero_of_card_lt n (by simpa using Nat.lt_of_not_ge hnr)]
  rw [hleft]
  congr 1
  by_cases hpn : p ≤ n
  · rw [if_pos hpn, fixedRootPolynomial_coefficient r k _ (by omega)]
    congr 1
    omega
  · rw [if_neg hpn, fixedRootPolynomial_coefficient_zero r k _ (by omega)]

section Field
variable [IsDomain k]
abbrev PrimeFiberField := FractionRing (MvPolynomial (Fin r) k)

def primeFiberCharacter (n : ℕ) : PrimeFiberField r k :=
  algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k) (primeFiberCoefficient p r k n)

theorem primeFiberCharacter_active [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    primeFiberCharacter p r k n ≠ 0 ↔ n ∈ primeCycleActiveRanks p r := by
  have he : primeFiberCharacter p r k n = 0 ↔ primeFiberCoefficient p r k n = 0 := by
    change algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k) _ = 0 ↔ _
    rw [← map_zero (algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k))]
    exact (IsFractionRing.injective (MvPolynomial (Fin r) k) (PrimeFiberField r k)).eq_iff
  exact (not_congr he).trans (primeFiberCoefficient_active p r k hn)

end Field
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleFlagAction.lean -/
section

section
/-! # Free prime-cycle action on the actual active-flag indexing set -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial ProperlyColoredComplex

variable (p r : ℕ) [Fact p.Prime] (k : Type*) [Field k]

local instance (priority := 2000) : DecidableEq (PrimeCycleVertex p r) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace (PrimeCycleVertex p r)) :=
  Classical.decEq _

abbrev PrimeBooleanComplex := booleanColoredComplex (PrimeCycleVertex p r)

theorem primeCycleVertex_card : Fintype.card (PrimeCycleVertex p r) = p + r := by
  rw [Fintype.card_sum, ZMod.card, Fintype.card_fin]

theorem primeActiveRanks_pos_bound {n : ℕ} (hn : n ∈ primeCycleActiveRanks p r) :
    0 < n ∧ n ≤ p + r := by
  have hp := (Fact.out : p.Prime).pos
  simp only [primeCycleActiveRanks, Finset.mem_union, Finset.mem_Icc] at hn
  omega

/-- A mask for the active ranks. Its values are only used to select ranks;
the actual eigencharacter is the generic polynomial character. -/
def primeRankMask (i : Fin (Fintype.card (PrimeCycleVertex p r))) : k :=
  if i.val + 1 ∈ primeCycleActiveRanks p r then 1 else 0

@[simp] theorem primeRankMask_active (i : Fin (Fintype.card (PrimeCycleVertex p r))) :
    primeRankMask p r k i ≠ 0 ↔ i.val + 1 ∈ primeCycleActiveRanks p r := by
  simp [primeRankMask]

def primeRankIndex (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    ActiveColor (primeRankMask p r k) := by
  have hi := primeActiveRanks_pos_bound p r i.property
  refine ⟨⟨i.val - 1, by rw [primeCycleVertex_card]; omega⟩, ?_⟩
  rw [primeRankMask_active]
  have he : i.val - 1 + 1 = i.val := by omega
  simpa only [he] using i.property

@[simp] theorem primeRankIndex_succ (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeRankIndex p r k i).val.val + 1 = i.val := by
  have hi := (primeActiveRanks_pos_bound p r i.property).1
  change i.val - 1 + 1 = i.val
  omega

def primeActiveRankFace
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) : Finset (PrimeCycleVertex p r) :=
  (a.val (primeRankIndex p r k i)).val.val

theorem primeActiveRankFace_card
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeActiveRankFace p r k a i).card = i.val := by
  have h := congrArg Fin.val (a.val (primeRankIndex p r k i)).property
  have hs := BooleanFace.color_succ (a.val (primeRankIndex p r k i)).val
  change ((a.val (primeRankIndex p r k i)).val.val).card = i.val
  change (BooleanFace.color (a.val (primeRankIndex p r k i)).val).val =
    (primeRankIndex p r k i).val.val at h
  rw [h, primeRankIndex_succ] at hs
  exact hs.symm

def primeActiveRankFlag
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :
    RankFlag (PrimeCycleVertex p r) (primeCycleActiveRanks p r) where
  face := primeActiveRankFace p r k a
  card := primeActiveRankFace_card p r k a
  nested i j hij := by
    have hi : (a.val (primeRankIndex p r k i)).val ∈
        (PrimeBooleanComplex p r).assignmentVertices (primeRankMask p r k) a.val :=
      Finset.mem_image.mpr ⟨primeRankIndex p r k i, Finset.mem_univ _, rfl⟩
    have hj : (a.val (primeRankIndex p r k j)).val ∈
        (PrimeBooleanComplex p r).assignmentVertices (primeRankMask p r k) a.val :=
      Finset.mem_image.mpr ⟨primeRankIndex p r k j, Finset.mem_univ _, rfl⟩
    rcases a.property _ hi _ hj with h | h
    · exact h
    · have he : primeActiveRankFace p r k a j = primeActiveRankFace p r k a i :=
        Finset.eq_of_subset_of_card_le h (by
          rw [primeActiveRankFace_card, primeActiveRankFace_card]
          exact hij)
      rw [he]

def primeBooleanPermutation : PrimeCycleGroup p →* Equiv.Perm (BooleanFace (PrimeCycleVertex p r)) :=
  booleanFacePermHom.comp (primeCyclePermutation p r)

theorem primeBooleanPermutation_face (g : PrimeCycleGroup p)
    (s : Finset (BooleanFace (PrimeCycleVertex p r))) :
    (PrimeBooleanComplex p r).face (s.image (primeBooleanPermutation p r g)) ↔
      (PrimeBooleanComplex p r).face s :=
  booleanFacePermutation_face (primeCyclePermutation p r g) s

theorem primeBooleanPermutation_color (g : PrimeCycleGroup p)
    (F : BooleanFace (PrimeCycleVertex p r)) :
    (PrimeBooleanComplex p r).color (primeBooleanPermutation p r g F) =
      (PrimeBooleanComplex p r).color F :=
  booleanFacePermutation_color (primeCyclePermutation p r g) F

def primeFlagAction : MulAction (PrimeCycleGroup p)
    ((PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :=
  (PrimeBooleanComplex p r).activeFlagAction (primeBooleanPermutation p r)
    (primeBooleanPermutation_face p r) (primeBooleanPermutation_color p r)
    (primeRankMask p r k)

@[simp] theorem primeFlagAction_val (g : PrimeCycleGroup p)
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :
    ((primeFlagAction p r k).smul g a).val =
      (PrimeBooleanComplex p r).assignmentRename (primeRankMask p r k)
        (primeBooleanPermutation p r g) (primeBooleanPermutation_color p r g) a.val := rfl

theorem primeBooleanRename_eq {K : Type*} [CommRing K] (g : PrimeCycleGroup p) :
    booleanRename K (primeCyclePermutation p r g) =
      (PrimeBooleanComplex p r).colorRename K (primeBooleanPermutation p r g)
        (primeBooleanPermutation_face p r g) := rfl

theorem primeFlagAction_faces (g : PrimeCycleGroup p)
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeActiveRankFlag p r k ((primeFlagAction p r k).smul g a)).face i =
      ((primeActiveRankFlag p r k a).face i).image (primeCyclePermutation p r g) := rfl

/-- The exact active-flag indexing set used in the original-ring expansion
has a free action, for every prime and every positive number of fixed vertices. -/
theorem primeFlagAction_free (hr : 0 < r) :
    ∀ a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k),
      Function.Injective (fun g : PrimeCycleGroup p => (primeFlagAction p r k).smul g a) := by
  letI := primeFlagAction p r k
  intro a g h heq
  change g • a = h • a at heq
  have hfix : (h⁻¹ * g) • a = a := by
    rw [mul_smul, heq, inv_smul_smul]
  have hunit : h⁻¹ * g = 1 := by
    by_contra hg
    apply primeCycleActiveFlag_not_fixed p r hr (primeActiveRankFlag p r k a) (h⁻¹ * g) hg
    intro i
    have hh := congrArg (fun b => (primeActiveRankFlag p r k b).face i) hfix
    change (primeActiveRankFlag p r k ((primeFlagAction p r k).smul (h⁻¹ * g) a)).face i =
      (primeActiveRankFlag p r k a).face i at hh
    rw [primeFlagAction_faces] at hh
    apply Finset.ext
    intro v
    have hv := congrArg (fun S : Finset (PrimeCycleVertex p r) => v ∈ S) hh
    simpa only [Finset.mem_image] using Iff.of_eq hv
  exact (inv_mul_eq_one.mp hunit).symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleObstruction.lean -/
section

section
/-! # The unrestricted prime-cycle obstruction on the actual rings

The comparison is not assumed graded, coherent, multiplicative, or normalized.
Its only hypotheses are linear bijectivity, universal-parameter linearity, and
equivariance for a prime cycle with at least one fixed vertex.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial ProperlyColoredComplex

variable (p r : ℕ) [Fact p.Prime]
variable {K k : Type*} [CommRing K] [Field k] [CharP k p]

local instance (priority := 2000) : DecidableEq (PrimeCycleVertex p r) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace (PrimeCycleVertex p r)) :=
  Classical.decEq _

/-- Evaluate the moved variables at one and the fixed variables at independent
indeterminates, reducing the original coefficient ring through `φ`. -/
def primeCycleEvaluation (φ : K →+* k) :
    MvPolynomial (PrimeCycleVertex p r) K →+* MvPolynomial (Fin r) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) (polynomialPrimeRoots p r k)

theorem primeCycleEvaluation_esymm (φ : K →+* k) (n : ℕ) (hn : n ≤ p + r) :
    primeCycleEvaluation p r φ (MvPolynomial.esymm (PrimeCycleVertex p r) K n) =
      primeFiberCoefficient p r k n := by
  rw [← primeRoots_esymm p r k n hn]
  simp only [primeCycleEvaluation, MvPolynomial.esymm, map_sum, map_prod,
    MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]

theorem primeCycleEvaluation_invariant (φ : K →+* k)
    (g : PrimeCycleGroup p) (x : MvPolynomial (PrimeCycleVertex p r) K) :
    primeCycleEvaluation p r φ (MvPolynomial.rename (primeCyclePermutation p r g) x) =
      primeCycleEvaluation p r φ x := by
  have hroots : polynomialPrimeRoots p r k ∘ primeCyclePermutation p r g =
      polynomialPrimeRoots p r k := by
    funext v
    rcases v with v | v <;> rfl
  rw [primeCycleEvaluation, MvPolynomial.eval₂Hom_rename, hroots]

/-- Proposition 9.5 for the prime cycle needed in Theorem 1.3, over an
arbitrary original coefficient ring with a residue characteristic p. The
conclusion concerns the actual polynomial and barycentric quotient rings. -/
theorem no_primeCycle_equivariant_parameter_equiv (hr : 0 < r) (φ : K →+* k)
    (f : MvPolynomial (PrimeCycleVertex p r) K ≃ₗ[K]
      BooleanBarycentricRing (PrimeCycleVertex p r) K)
    (hparameter : ∀ (i : Fin (Fintype.card (PrimeCycleVertex p r))) x,
      f (MvPolynomial.esymm (PrimeCycleVertex p r) K (i.val + 1) * x) =
        colorSum (K := K) i * f x)
    (hequivariant : ∀ (g : PrimeCycleGroup p) x,
      f (MvPolynomial.rename (primeCyclePermutation p r g) x) =
        booleanRename K (primeCyclePermutation p r g) (f x)) : False := by
  let D := PrimeBooleanComplex p r
  let c := primeRankMask p r k
  letI flagFintype : Fintype (D.ActiveFlag c) := inferInstance
  letI colorFintype : Fintype (ActiveColor c) := inferInstance
  letI := primeFlagAction p r k
  apply no_equiv_of_free_parameter_expansion
    (G := PrimeCycleGroup p) (T := D.ActiveFlag c) (I := ActiveColor c)
    (K := K) (R := MvPolynomial (PrimeCycleVertex p r) K)
    (B := D.Ring K) (L := MvPolynomial (Fin r) k)
    (a := fun i : ActiveColor c =>
      MvPolynomial.esymm (PrimeCycleVertex p r) K (i.val.val + 1))
    (b := fun i : ActiveColor c => D.colorParameter K i.val) (s := Finset.univ)
    (ρR := fun g => MvPolynomial.rename (primeCyclePermutation p r g))
    (ρB := fun g => booleanRename K (primeCyclePermutation p r g))
    (ev := primeCycleEvaluation p r φ)
    (hev := primeCycleEvaluation_invariant p r φ)
    (m := fun a : D.ActiveFlag c => D.assignmentMonomial K c a.val)
    (hm := ?_) (hprod := ?_) (hactive := ?_)
    (hfree := primeFlagAction_free p r k hr) (horder := ?_)
    (f := f) (hparameter := ?_) (hequivariant := hequivariant)
  · intro g a
    change D.assignmentMonomial K c ((primeFlagAction p r k).smul g a).val = _
    rw [primeFlagAction_val, primeBooleanRename_eq]
    exact (D.colorRename_assignmentMonomial K c
      (primeBooleanPermutation p r g) (primeBooleanPermutation_face p r g)
      (primeBooleanPermutation_color p r g) a.val).symm
  · change (∏ i : ActiveColor c, D.colorParameter K i.val) =
      ∑ a : D.ActiveFlag c, D.assignmentMonomial K c a.val
    have hsum := D.sum_activeFlagMonomial_withFintypes K c flagFintype colorFintype
    exact hsum.symm
  · intro i hi
    rw [primeCycleEvaluation_esymm p r φ _ (by
      exact Nat.succ_le_of_lt
        (lt_of_lt_of_eq i.val.isLt (primeCycleVertex_card p r)))]
    apply (primeFiberCoefficient_active p r k (Nat.succ_pos _)).mpr
    exact (primeRankMask_active p r k i.val).mp i.property
  · have hc : Fintype.card (PrimeCycleGroup p) = p := by
      simp only [PrimeCycleGroup, Fintype.card_multiplicative, ZMod.card]
    rw [hc]
    exact CharP.cast_eq_zero (MvPolynomial (Fin r) k) p
  · intro i x
    have hb : D.colorParameter K i.val = colorSum (K := K) i.val :=
      booleanColored_colorParameter i.val
    rw [hb]
    exact hparameter i.val x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ObstructionRelabel.lean -/
section

section
/-! # Relabeling the Boolean simplex preserves the actual ring and parameters -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {U V W K : Type*} [Fintype U] [Fintype V] [Fintype W] [CommRing K]

local instance (priority := 2000) : DecidableEq U := Classical.decEq U
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq W := Classical.decEq W
local instance (priority := 2000) : DecidableEq (BooleanFace U) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace W) := Classical.decEq _

def booleanFaceCongr (e : U ≃ V) : BooleanFace U ≃ BooleanFace V where
  toFun F := ⟨F.val.image e, F.property.image e⟩
  invFun F := ⟨F.val.image e.symm, F.property.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]

theorem booleanFaceCongr_subset_iff (e : U ≃ V) (F G : BooleanFace U) :
    (booleanFaceCongr e F).val ⊆ (booleanFaceCongr e G).val ↔ F.val ⊆ G.val := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    exact e.injective he ▸ hw
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨w, h hw, rfl⟩

theorem chainExponent_mapDomain_iff (e : U ≃ V) (a : BooleanFace U →₀ ℕ) :
    IsChainExponent (a.mapDomain (booleanFaceCongr e)) ↔ IsChainExponent a := by
  have hs : (a.mapDomain (booleanFaceCongr e)).support =
      a.support.image (booleanFaceCongr e) :=
    Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _) _
  constructor
  · intro h F hF G hG
    have hh := h (booleanFaceCongr e F) (by rw [hs]; exact Finset.mem_image.mpr ⟨F, hF, rfl⟩)
      (booleanFaceCongr e G) (by rw [hs]; exact Finset.mem_image.mpr ⟨G, hG, rfl⟩)
    simpa only [booleanFaceCongr_subset_iff] using hh
  · intro h F hF G hG
    rw [hs] at hF hG
    obtain ⟨F₀, hF₀, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨G₀, hG₀, rfl⟩ := Finset.mem_image.mp hG
    simpa only [booleanFaceCongr_subset_iff] using h F₀ hF₀ G₀ hG₀

def booleanRelabelHom (K : Type*) [CommRing K] (e : U ≃ V) :
    BooleanBarycentricRing U K →ₐ[K] BooleanBarycentricRing V K := by
  let f := (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))).comp
    (MvPolynomial.rename (booleanFaceCongr e))
  apply Ideal.Quotient.liftₐ (forbiddenIdeal (IsChainExponent (V := U))) f
  have hh : forbiddenIdeal (IsChainExponent (V := U)) ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (forbiddenIdeal (IsChainExponent (V := V)))
      (MvPolynomial.rename (booleanFaceCongr e) (MvPolynomial.monomial a (1 : K))) = 0
    rw [MvPolynomial.rename_monomial]
    exact chainMonomial_eq_zero (fun h => ha ((chainExponent_mapDomain_iff e a).mp h))
  exact fun x hx => hh hx

@[simp] theorem booleanRelabelHom_mk (e : U ≃ V) (x : MvPolynomial (BooleanFace U) K) :
    booleanRelabelHom K e (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) x) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.rename (booleanFaceCongr e) x) := rfl

@[simp] theorem booleanRelabelHom_variable (e : U ≃ V) (F : BooleanFace U) :
    booleanRelabelHom K e (faceVariable (K := K) F) =
      faceVariable (K := K) (booleanFaceCongr e F) := by
  rw [faceVariable, booleanRelabelHom_mk, MvPolynomial.rename_X]
  rfl

theorem booleanRelabelHom_trans (e : U ≃ V) (f : V ≃ W)
    (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K f (booleanRelabelHom K e x) =
      booleanRelabelHom K (e.trans f) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [booleanRelabelHom_mk, booleanRelabelHom_mk, booleanRelabelHom_mk,
    MvPolynomial.rename_rename]
  have he : (booleanFaceCongr f : BooleanFace V → BooleanFace W) ∘ booleanFaceCongr e =
      booleanFaceCongr (e.trans f) := by
    funext F
    apply Subtype.ext
    change (F.val.image e).image f = F.val.image (e.trans f)
    rw [Finset.image_image]
    rfl
  rw [he]

theorem booleanRelabelHom_refl (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K (Equiv.refl U) x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [booleanRelabelHom_mk]
  have he : (booleanFaceCongr (Equiv.refl U) : BooleanFace U → BooleanFace U) = id := by
    funext F
    apply Subtype.ext
    exact Finset.image_id
  rw [he, MvPolynomial.rename_id_apply]

def booleanRelabelEquiv (K : Type*) [CommRing K] (e : U ≃ V) :
    BooleanBarycentricRing U K ≃ₐ[K] BooleanBarycentricRing V K :=
  AlgEquiv.ofAlgHom (booleanRelabelHom K e) (booleanRelabelHom K e.symm)
    (by
      ext x
      rw [AlgHom.comp_apply, booleanRelabelHom_trans]
      simpa using booleanRelabelHom_refl (K := K) x)
    (by
      ext x
      rw [AlgHom.comp_apply, booleanRelabelHom_trans]
      simpa using booleanRelabelHom_refl (K := K) x)

theorem booleanRelabelHom_eq_booleanRename (e : Equiv.Perm V) :
    booleanRelabelHom K e = booleanRename K e := by
  rfl

theorem booleanFaceCongr_color_val (e : U ≃ V) (F : BooleanFace U) :
    (BooleanFace.color (booleanFaceCongr e F)).val = (BooleanFace.color F).val := by
  change (F.val.image e).card - 1 = F.val.card - 1
  rw [Finset.card_image_of_injective _ e.injective]

def booleanColorFaceCongr (e : U ≃ V)
    (i : Fin (Fintype.card U)) (j : Fin (Fintype.card V)) (hij : i.val = j.val) :
    {F : BooleanFace U // BooleanFace.color F = i} ≃
      {F : BooleanFace V // BooleanFace.color F = j} where
  toFun F := ⟨booleanFaceCongr e F.val, by
    apply Fin.ext
    rw [booleanFaceCongr_color_val, F.property]
    exact hij⟩
  invFun F := ⟨booleanFaceCongr e.symm F.val, by
    apply Fin.ext
    rw [booleanFaceCongr_color_val, F.property]
    exact hij.symm⟩
  left_inv F := by
    apply Subtype.ext
    exact (booleanFaceCongr e).symm_apply_apply F.val
  right_inv F := by
    apply Subtype.ext
    exact (booleanFaceCongr e).apply_symm_apply F.val

theorem colorSum_eq_sum_fiber (i : Fin (Fintype.card V)) :
    colorSum (K := K) i =
      ∑ F : {F : BooleanFace V // BooleanFace.color F = i}, faceVariable (K := K) F.val := by
  exact Finset.sum_subtype (facesOfColor i) (fun F => by simp) (faceVariable (K := K))

theorem booleanRelabelHom_colorSum (e : U ≃ V)
    (i : Fin (Fintype.card U)) (j : Fin (Fintype.card V)) (hij : i.val = j.val) :
    booleanRelabelHom K e (colorSum (K := K) i) = colorSum (K := K) j := by
  rw [colorSum_eq_sum_fiber, map_sum, colorSum_eq_sum_fiber]
  simp only [booleanRelabelHom_variable]
  exact Fintype.sum_equiv (booleanColorFaceCongr e i j hij) _ _ (fun _ => rfl)

theorem booleanRelabelHom_naturality (e : U ≃ V) (g : Equiv.Perm U) (h : Equiv.Perm V)
    (hgh : ∀ u, e (g u) = h (e u)) (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K e (booleanRename K g x) =
      booleanRename K h (booleanRelabelHom K e x) := by
  rw [← booleanRelabelHom_eq_booleanRename, ← booleanRelabelHom_eq_booleanRename,
    booleanRelabelHom_trans, booleanRelabelHom_trans]
  have he : g.trans e = e.trans h := Equiv.ext hgh
  rw [he]

theorem polynomialRename_naturality (e : U ≃ V) (g : Equiv.Perm U) (h : Equiv.Perm V)
    (hgh : ∀ u, e (g u) = h (e u)) (x : MvPolynomial U K) :
    MvPolynomial.rename e (MvPolynomial.rename g x) =
      MvPolynomial.rename h (MvPolynomial.rename e x) := by
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  have he : (e : U → V) ∘ g = (h : V → V) ∘ e := funext hgh
  rw [he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FactorialResidueField.lean -/
section

section
/-! # Exact reduction of a nonunit factorial to modular characteristic

No finiteness, domain, reducedness, or Noetherian assumption is imposed on
the coefficient ring.  A nonunit factorial produces a prime below the rank
and a genuine maximal-ideal residue field of that characteristic.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
variable {K : Type*} [CommRing K]

lemma natCast_product_isUnit (l : List ℕ)
    (h : ∀ p ∈ l, IsUnit (p : K)) : IsUnit (l.prod : K) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.prod_cons, Nat.cast_mul]
      exact (h a (List.mem_cons_self)).mul (ih (fun p hp => h p (List.mem_cons_of_mem _ hp)))

/-- Every nonunit factorial has a nonunit prime factor in the exact range. -/
theorem exists_nonunit_prime_of_factorial (n : ℕ)
    (h : ¬ IsUnit (n.factorial : K)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ ¬ IsUnit (p : K) := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  rw [← Nat.prod_primeFactorsList (Nat.factorial_ne_zero n)]
  apply natCast_product_isUnit
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  exact hn p hprime (hprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactorsList hp))

/-- The exact residue-characteristic reduction used in the rank-d obstruction. -/
theorem factorial_nonunit_residueField (d : ℕ) (hd : 1 ≤ d)
    (h : ¬ IsUnit ((d - 1).factorial : K)) :
    ∃ p : ℕ, p.Prime ∧ p < d ∧
      ∃ I : Ideal K, I.IsMaximal ∧ CharP (K ⧸ I) p := by
  obtain ⟨p, hp, hpd, hunit⟩ := exists_nonunit_prime_of_factorial (K := K) (d - 1) h
  obtain ⟨I, hI, hpI⟩ := exists_max_ideal_of_mem_nonunits hunit
  letI : I.IsMaximal := hI
  refine ⟨p, hp, by omega, I, hI, ?_⟩
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  rw [← map_natCast (Ideal.Quotient.mk I) p]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI

end FourPapers.Universal

#print axioms FourPapers.Universal.exists_nonunit_prime_of_factorial

#print axioms FourPapers.Universal.factorial_nonunit_residueField

end
end
end

/- BEGIN FourPapers/Universal/FactorialObstruction.lean -/
section

section
/-! # The nonunit-factorial obstruction over every commutative ring

The result is stated for every finite vertex type and the full permutation
group. Thus it is independent of a chosen labeling of the rank-d simplex.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (V K : Type*) [Fintype V] [CommRing K]

local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _

/-- The actual parameter actions, stated independently of an auxiliary
linear ordering on the vertex type. -/
def simplexPolynomialColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] MvPolynomial V K :=
  MvPolynomial.aeval (fun i => MvPolynomial.esymm V K (i.val + 1))

def simplexBooleanColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] BooleanBarycentricRing V K :=
  MvPolynomial.aeval colorSum

/-- Exactly an unrestricted equivariant universal-parameter module comparison
on one simplex. Grading, coherence, and multiplication preservation are absent. -/
structure SimplexEquivariantParameterComparison where
  equiv : MvPolynomial V K ≃ₗ[K] BooleanBarycentricRing V K
  parameter : ∀ (i : Fin (Fintype.card V)) x,
    equiv (MvPolynomial.esymm V K (i.val + 1) * x) = colorSum (K := K) i * equiv x
  equivariant : ∀ (g : Equiv.Perm V) x,
    equiv (MvPolynomial.rename g x) = booleanRename K g (equiv x)

variable {V K} {U : Type*} [Fintype U]

local instance (priority := 2000) : DecidableEq U := Classical.decEq U
local instance (priority := 2000) : DecidableEq (BooleanFace U) := Classical.decEq _

/-- The explicit generator conditions are genuine linearity over the entire
parameter polynomial ring, via the verified `ParameterEquiv` API. -/
def SimplexEquivariantParameterComparison.parameterEquiv
    (f : SimplexEquivariantParameterComparison V K) :
    ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K) where
  toLinearEquiv := f.equiv
  map_X_mul i x := by
    simpa only [simplexPolynomialColorMap, simplexBooleanColorMap, MvPolynomial.aeval_X] using
      f.parameter i x

def simplexComparisonOfParameterEquiv
    (e : ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K))
    (he : ∀ (g : Equiv.Perm V) x,
      e.toLinearEquiv (MvPolynomial.rename g x) =
        booleanRename K g (e.toLinearEquiv x)) :
    SimplexEquivariantParameterComparison V K where
  equiv := e.toLinearEquiv
  parameter i x := by
    simpa only [simplexPolynomialColorMap, simplexBooleanColorMap, MvPolynomial.aeval_X] using
      e.map_X_mul i x
  equivariant := he

/-- Relabeling preserves every condition in the unrestricted comparison. -/
def SimplexEquivariantParameterComparison.relabel
    (f : SimplexEquivariantParameterComparison V K) (e : U ≃ V) :
    SimplexEquivariantParameterComparison U K := by
  let P := MvPolynomial.renameEquiv K e
  let B := booleanRelabelEquiv K e
  refine ⟨P.toLinearEquiv.trans (f.equiv.trans B.toLinearEquiv.symm), ?_, ?_⟩
  · intro i x
    let j : Fin (Fintype.card V) := ⟨i.val, by
      rw [← Fintype.card_congr e]
      exact i.isLt⟩
    apply B.injective
    change B (B.symm (f.equiv (P (MvPolynomial.esymm U K (i.val + 1) * x)))) =
      B (colorSum (K := K) i * B.symm (f.equiv (P x)))
    rw [B.apply_symm_apply, map_mul B, B.apply_symm_apply]
    change f.equiv (MvPolynomial.rename e (MvPolynomial.esymm U K (i.val + 1) * x)) =
      booleanRelabelHom K e (colorSum (K := K) i) * f.equiv (P x)
    rw [map_mul, MvPolynomial.rename_esymm (σ := U) (R := K) (i.val + 1) e,
      booleanRelabelHom_colorSum e i j rfl]
    exact f.parameter j (P x)
  · intro g x
    let h : Equiv.Perm V := e.symm.trans (g.trans e)
    have hgh : ∀ u, e (g u) = h (e u) := by
      intro u
      simp only [h, Equiv.trans_apply, Equiv.symm_apply_apply]
    apply B.injective
    change B (B.symm (f.equiv (P (MvPolynomial.rename g x)))) =
      B (booleanRename K g (B.symm (f.equiv (P x))))
    rw [AlgEquiv.apply_symm_apply]
    change f.equiv (MvPolynomial.rename e (MvPolynomial.rename g x)) =
      booleanRelabelHom K e (booleanRename K g (B.symm (f.equiv (P x))))
    rw [polynomialRename_naturality e g h hgh, f.equivariant,
      booleanRelabelHom_naturality e g h hgh]
    change booleanRename K h (f.equiv (P x)) =
      booleanRename K h (B (B.symm (f.equiv (P x))))
    rw [AlgEquiv.apply_symm_apply]

/-- The negative half of Theorem 1.3 in its full stated strength: a nonunit
factorial excludes even an ungraded, incoherent parameter-module isomorphism
equivariant under the entire symmetric group. -/
theorem factorial_nonunit_no_simplex_comparison
    (hd : 1 ≤ Fintype.card V)
    (hfactorial : ¬ IsUnit (((Fintype.card V - 1).factorial : ℕ) : K)) :
    IsEmpty (SimplexEquivariantParameterComparison V K) := by
  obtain ⟨p, hp, hpd, I, hI, hchar⟩ :=
    factorial_nonunit_residueField (K := K) (Fintype.card V) hd hfactorial
  letI : Fact p.Prime := ⟨hp⟩
  letI : I.IsMaximal := hI
  letI : Field (K ⧸ I) := Ideal.Quotient.field I
  letI : CharP (K ⧸ I) p := hchar
  let r := Fintype.card V - p
  have hr : 0 < r := Nat.sub_pos_of_lt hpd
  have hcard : Fintype.card (PrimeCycleVertex p r) = Fintype.card V := by
    rw [primeCycleVertex_card]
    dsimp [r]
    exact Nat.add_sub_of_le hpd.le
  let e : PrimeCycleVertex p r ≃ V := Fintype.equivOfCardEq hcard
  refine ⟨fun f => ?_⟩
  let f' := f.relabel e
  exact no_primeCycle_equivariant_parameter_equiv p r hr (Ideal.Quotient.mk I)
    f'.equiv f'.parameter (fun g x => f'.equivariant (primeCyclePermutation p r g) x)

theorem factorial_nonunit_no_equivariant_parameterEquiv
    (hd : 1 ≤ Fintype.card V)
    (hfactorial : ¬ IsUnit (((Fintype.card V - 1).factorial : ℕ) : K))
    (e : ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K))
    (he : ∀ (g : Equiv.Perm V) x,
      e.toLinearEquiv (MvPolynomial.rename g x) =
        booleanRename K g (e.toLinearEquiv x)) : False :=
  (factorial_nonunit_no_simplex_comparison (V := V) (K := K) hd hfactorial).false
    (simplexComparisonOfParameterEquiv e he)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/EquivariantUniformCriterion.lean -/
section

section
/-! # The exact uniform criterion in Theorem 1.3

The positive theorem is combined with the unrestricted simplex obstruction.
The bridge uses actual coherent maps on the Boolean simplex, transports a
component along its literal vertex identification, and proves equality of
the two existing definitions of the Boolean permutation action on generators.
The uniform statement does not impose constant normalization.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section BooleanAction
variable {V : Type u} [Fintype V] (K : Type v) [CommRing K]

theorem booleanRename_eq_vertexRelabel (g : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanRename K g x = booleanVertexRelabelEquiv g x := by
  have h : (booleanRename K g).comp
      (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))) =
      (booleanVertexRelabelEquiv (K := K) g).toAlgHom.comp
        (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))) := by
    apply MvPolynomial.algHom_ext
    intro F
    change booleanRename K g (faceVariable (K := K) F) =
      booleanVertexRelabelEquiv g (faceVariable F)
    rw [booleanRename_faceVariable, booleanVertexRelabelEquiv_face]
    congr 1
    apply Subtype.ext
    exact (Finset.map_eq_image g.toEmbedding F.val).symm
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

end BooleanAction

section CoherentSymmetry
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type v) [CommRing K]

theorem coherentEquiv_family_fixed
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hE : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (E.component p x) =
      E.component (e p) (barycentricStalkOrderEquiv K e p x)) (e : P ≃o P) :
    stalkFamilyRelabel K e (fun p => (E.component p).toLinearMap) =
      (fun p => (E.component p).toLinearMap) := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K e.symm p).symm
    (E.component (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)) = E.component p x
  rw [← hE, AlgEquiv.symm_apply_apply]

end CoherentSymmetry

section SimplexBridge
variable {V : Type u} [Fintype V] (K : Type v) [CommRing K]

/-- A comparison on the actual Boolean face diagram gives the unrestricted
simplex comparison used by the negative theorem.  This bridge itself does
not require grading or normalization. -/
def simplexComparisonOfCoherentEquiv
    (E : CoherentEquiv (barycentricDiagram (P := Finset V) K) (polynomialDiagram K))
    (hp : ∀ (s : Finset V) (r : ℕ) x,
      E.component s (booleanRankParameter (r + 1) * x) =
        polynomialParameter K s (r + 1) * E.component s x)
    (he : ∀ (e : Finset V ≃o Finset V) s x,
      polynomialStalkOrderEquiv K e s (E.component s x) =
        E.component (e s) (barycentricStalkOrderEquiv K e s x)) :
    SimplexEquivariantParameterComparison V K := by
  let F : StalkLinearFamily (P := Finset V) K := fun s => (E.component s).toLinearMap
  have hc : F ∈ coherentStalkFamilySubmodule K := E.naturality
  have hs : ∀ g : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr g) F = F :=
    fun g => coherentEquiv_family_fixed K E he (finsetOrderCongr g)
  let i : V ↪ V := Function.Embedding.refl V
  let a := embeddingPlacementVertex i
  let L : BooleanBarycentricRing V K ≃ₗ[K] MvPolynomial V K :=
    (booleanVertexRelabelEquiv (K := K) a).toLinearEquiv.trans
      ((E.component (embeddingPlacementFace i)).trans
        (MvPolynomial.renameEquiv K a).symm.toLinearEquiv)
  have hL : ∀ x, L x = finiteVertexMap F (le_refl (Fintype.card V)) x := by
    intro x
    exact (LinearMap.congr_fun
      (finiteVertexMap_eq_placement F hs (le_refl (Fintype.card V)) i) x).symm
  have hparam : ∀ r x, L (booleanRankParameter (r + 1) * x) =
      MvPolynomial.esymm V K (r + 1) * L x := by
    intro r x
    rw [hL, hL]
    exact finiteVertexMap_parameter F (fun s r x => hp s r x) (le_refl (Fintype.card V)) r x
  have hsym : ∀ (g : Equiv.Perm V) x, MvPolynomial.rename g (L x) =
      L (booleanVertexRelabelEquiv g x) := by
    intro g x
    rw [hL, hL]
    exact finiteVertexMap_relabel F hc hs (le_refl (Fintype.card V))
      (le_refl (Fintype.card V)) g x
  refine ⟨L.symm, ?_, ?_⟩
  · intro j x
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, ← booleanRankParameter_color, hparam,
      LinearEquiv.apply_symm_apply]
  · intro g x
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, booleanRename_eq_vertexRelabel,
      ← hsym, LinearEquiv.apply_symm_apply]

end SimplexBridge

/-- The paper's uniform existence assertion, in arbitrary finite-poset
universe.  Coherence and ordinary grading are explicit.  Equivariance for
the entire order automorphism group implies equivariance for each of its
group actions, without any hypothesis on the group order in `K`. -/
def UniformCoherentEquivariantComparisons (K : Type v) [CommRing K] (d : ℕ) : Prop :=
  ∀ (P : Type u) [PartialOrder P] [OrderBot P] [Fintype P]
    (hs : IsSimplicialPoset P), (∀ p : P, faceRank p ≤ d) →
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x)

/-- **Theorem 1.3, literal uniform if and only if.**  Necessity is obtained
from a rank-d Boolean simplex in the quantified universe, and the explicit
bridge above supplies the exact polynomial/barycentric rings and actions
required by the unrestricted negative theorem. -/
theorem theorem_1_3_uniform_iff (K : Type v) [CommRing K]
    (d : ℕ) (hd : 1 ≤ d) :
    UniformCoherentEquivariantComparisons.{u, v} K d ↔
      IsUnit (((d - 1).factorial : ℕ) : K) := by
  constructor
  · intro H
    by_contra hD
    let V := ULift.{u} (Fin d)
    have hV : Fintype.card V = d := by simp [V]
    have hrank : ∀ s : Finset V, faceRank s ≤ d := by
      intro s
      rw [simplex_faceRank]
      calc
        s.card ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ s)
        _ = d := by rw [Finset.card_univ, hV]
    obtain ⟨E, hp, hg, he⟩ := H (Finset V) (simplex_isSimplicialPoset (V := V)) hrank
    have hnot := factorial_nonunit_no_simplex_comparison (V := V) (K := K)
      (by simpa only [hV] using hd) (by simpa only [hV] using hD)
    exact hnot.false (simplexComparisonOfCoherentEquiv K E hp he)
  · intro hD P _ _ _ hs hrank
    obtain ⟨E, hp, hg, h₁, he⟩ := theorem_1_3_positive K hs d hd hrank hD
    exact ⟨E, hp, hg, he⟩

end FourPapers.Universal

end
end
end
