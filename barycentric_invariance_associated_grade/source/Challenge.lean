module
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Atoms.Finite
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
namespace PalomarBarycentric
universe uCoefficient
/-- The canonical inverse-pair law for the identity coefficient homomorphism. -/
theorem coefficientIdentityInvPair {K : Type uCoefficient} [CommRing K] :
    RingHomInvPair (RingHom.id K) (RingHom.id K) := by infer_instance
/-- Every ideal of a commutative coefficient algebra is two-sided. -/
theorem coefficientIdealTwoSided {R : Type uCoefficient} [CommRing R] (I : Ideal R) :
    I.IsTwoSided := by infer_instance
/-- Identity inverse-pair with the commutative-semiring projection used by the basis representation. -/
theorem commutativeCoefficientIdentityInvPair {K : Type uCoefficient} [hK : CommRing K] :
    @RingHomInvPair K K hK.toCommSemiring.toSemiring hK.toCommSemiring.toSemiring
      (@RingHom.id K hK.toCommSemiring.toSemiring.toNonAssocSemiring)
      (@RingHom.id K hK.toCommSemiring.toSemiring.toNonAssocSemiring) := by infer_instance
attribute [instance 2100] commutativeCoefficientIdentityInvPair
attribute [instance 2000] coefficientIdentityInvPair coefficientIdealTwoSided
end PalomarBarycentric
end

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Source theorem13.lean:132. -/
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
/-- Source theorem13.lean:136. -/
def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p
/-- Source theorem13.lean:139. -/
@[simp] theorem mem_faceVertices {p a : P} :
    a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
/-- Source theorem13.lean:152. -/
theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
/-- Source theorem13.lean:206. -/
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P)
    (hsu : s ⊆ faceVertices p) :
    ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
/-- Source theorem13.lean:248. -/
def faceRank (p : P) : ℕ := (faceVertices p).card
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
/-- Source theorem13.lean:301. -/
structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x,
    res hrq (res hqp x) = res (hrq.trans hqp) x
attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module
end
end FourPapers.Universal
namespace FourPapers.Universal.ModuleDiagram
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable (D : ModuleDiagram K P)
/-- Source theorem13.lean:319. -/
def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)
end
end FourPapers.Universal.ModuleDiagram
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
/-- Source theorem13.lean:365. -/
structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)
end
end FourPapers.Universal
namespace FourPapers.Universal.CoherentEquiv
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable {D E F : ModuleDiagram K P}
/-- Source theorem13.lean:378. -/
def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
/-- Source theorem13.lean:384. -/
def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) =
      f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]
/-- Source theorem13.lean:392. -/
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
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Source theorem13.lean:490. -/
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
instance palomarFaceVertexFintype (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _
/-- Source theorem13.lean:498. -/
abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
/-- Source theorem13.lean:501. -/
def polynomialRestriction {p q : P} (hqp : q ≤ p) :
    PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
/-- Source theorem13.lean:517. -/
theorem polynomialRestriction_refl (p : P) :
    polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
/-- Source theorem13.lean:524. -/
theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
      polynomialRestriction K (hrq.trans hqp) := by sorry
/-- Source theorem13.lean:554. -/
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Source theorem13.lean:629. -/
abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
/-- Source theorem13.lean:634. -/
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
/-- Source theorem13.lean:682. -/
def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
/-- Source theorem13.lean:685. -/
def minimalCommonUppers (p q : P) : Finset P :=
  univ.filter (IsMinimalCommonUpper p q)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Source theorem13.lean:694. -/
abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
/-- Source theorem13.lean:697. -/
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
/-- Source theorem13.lean:709. -/
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}
/-- Source theorem13.lean:717. -/
def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)
/-- Source theorem13.lean:721. -/
abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs
/-- Source theorem13.lean:725. -/
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
/-- Source theorem13.lean:729. -/
abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
/-- Source theorem13.lean:731. -/
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
/-- Source theorem13.lean:734. -/
def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
/-- Source theorem13.lean:738. -/
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
/-- Source theorem13.lean:741. -/
def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
/-- Source theorem13.lean:744. -/
def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
/-- Source theorem13.lean:748. -/
def barycentricParameterAction (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V]
/-- Source theorem13.lean:782. -/
def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Source theorem13.lean:1059. -/
def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q
/-- Source theorem13.lean:1065. -/
@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
/-- Source theorem13.lean:1070. -/
def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a
/-- Source theorem13.lean:1076. -/
def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
/-- Source theorem13.lean:1156. -/
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val
/-- Source theorem13.lean:1166. -/
theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P)
    {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    faceEvaluation K r f = 0 := by sorry
/-- Source theorem13.lean:1179. -/
def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) :
    FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {V K : Type*} [CommRing K]
/-- Source theorem13.lean:1219. -/
def IsDivisorClosed (P : (V →₀ ℕ) → Prop) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → P b → P a
/-- Source theorem13.lean:1223. -/
def forbiddenIdeal (P : (V →₀ ℕ) → Prop) : Ideal (MvPolynomial V K) :=
  Ideal.span ((fun a : V →₀ ℕ => MvPolynomial.monomial a (1 : K)) '' {a | ¬ P a})
/-- Source theorem13.lean:1241. -/
abbrev MonomialQuotient (P : (V →₀ ℕ) → Prop) :=
  MvPolynomial V K ⧸ forbiddenIdeal P
/-- Source theorem13.lean:1245. -/
def standardCoefficients (P : (V →₀ ℕ) → Prop) :
    MvPolynomial V K →ₗ[K] ({a // P a} →₀ K) :=
  (Finsupp.lsubtypeDomain {a | P a}).comp
    (MvPolynomial.basisMonomials V K).repr.toLinearMap
/-- Source theorem13.lean:1254. -/
lemma standardCoefficients_surjective (P : (V →₀ ℕ) → Prop) :
    Function.Surjective (standardCoefficients (K := K) P) := by sorry
/-- Source theorem13.lean:1267. -/
lemma standardCoefficients_ker (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) :
    LinearMap.ker (standardCoefficients (K := K) P) =
      (forbiddenIdeal P).restrictScalars K := by sorry
/-- Source theorem13.lean:1284. -/
def standardMonomialEquiv (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    MonomialQuotient (K := K) P ≃ₗ[K] ({a // P a} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (standardCoefficients_ker (K := K) P hP).symm).trans
    ((standardCoefficients (K := K) P).quotKerEquivOfSurjective
      (standardCoefficients_surjective (K := K) P))
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
/-- Source theorem13.lean:1597. -/
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
/-- Source theorem13.lean:1620. -/
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Source theorem13.lean:1961. -/
def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
/-- Source theorem13.lean:1976. -/
theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by sorry
/-- Source theorem13.lean:1998. -/
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) :
    BooleanFace (FaceVertex p) ↪ NonzeroFace P where
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
/-- Source theorem13.lean:2012. -/
theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P)
    (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p := by sorry
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Source theorem13.lean:2050. -/
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
/-- Source theorem13.lean:2053. -/
theorem barycentricAllowed_divisorClosed :
    IsDivisorClosed (BarycentricAllowed (P := P)) := by sorry
/-- Source theorem13.lean:2085. -/
theorem barycentricIdeal_eq_forbiddenIdeal :
    barycentricIdeal (P := P) K =
      forbiddenIdeal (K := K) (BarycentricAllowed (P := P)) := by sorry
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Source theorem13.lean:2138. -/
abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] :=
  {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
/-- Source theorem13.lean:2143. -/
def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥
/-- Source theorem13.lean:2148. -/
theorem standardCarrier_le_iff (hs : IsSimplicialPoset P)
    (a : StandardFaceIndex P) (p : P) :
    standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by sorry
/-- Source theorem13.lean:2187. -/
theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P)
    (p : P) (q : NonzeroFace P) :
    q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by sorry
/-- Source theorem13.lean:2205. -/
theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
    BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
/-- Source theorem13.lean:2216. -/
theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) :
    IsChainExponent (a.comapDomain (booleanFaceInclusion hs p)
      (booleanFaceInclusion hs p).injective.injOn) := by sorry
/-- Source theorem13.lean:2229. -/
abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}
/-- Source theorem13.lean:2233. -/
def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) :
    {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
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
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
/-- Source theorem13.lean:2551. -/
def coefficientStalk (p : P) : Submodule K (I →₀ K) :=
  Finsupp.supported K K {i | carrier i ≤ p}
/-- Source theorem13.lean:2554. -/
def coefficientRestriction {p q : P} (_hqp : q ≤ p) :
    coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q :=
  (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
    (coefficientStalk K carrier p).subtype
/-- Source theorem13.lean:2559. -/
@[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p)
    (x : coefficientStalk K carrier p) (i : I) :
    (coefficientRestriction K carrier hqp x).val i =
      if carrier i ≤ q then x.val i else 0 := by sorry
/-- Source theorem13.lean:2564. -/
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
/-- Source theorem13.lean:2585. -/
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
/-- Source theorem13.lean:2610. -/
def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K :=
  (x.val (carrier i)).val i
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)
variable [Fintype P]
/-- Source theorem13.lean:2626. -/
def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)
/-- Source theorem13.lean:2636. -/
theorem coefficientAssembly_section (x : I →₀ K) :
    coefficientAssembly K carrier (coefficientSection K carrier x) = x := by sorry
/-- Source theorem13.lean:2642. -/
theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) :
    coefficientSection K carrier (coefficientAssembly K carrier x) = x := by sorry
/-- Source theorem13.lean:2655. -/
def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
/-- Source theorem13.lean:2666. -/
def sectionsFromCoherentCoefficients (D : ModuleDiagram K P)
    (e : CoherentEquiv D (coefficientDiagram K carrier)) :
    D.sections ≃ₗ[K] (I →₀ K) :=
  e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:2911. -/
def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]
/-- Source theorem13.lean:3050. -/
def subsetExponent (F : Finset V) : V →₀ ℕ :=
  ∑ v ∈ F, Finsupp.single v 1
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
/-- Source theorem13.lean:3320. -/
def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)
/-- Source theorem13.lean:3423. -/
def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)
/-- Source theorem13.lean:3428. -/
def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V :=
  ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩
/-- Source theorem13.lean:3437. -/
def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ :=
  ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1
/-- Source theorem13.lean:3455. -/
theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by sorry
/-- Source theorem13.lean:3469. -/
theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by sorry
/-- Source theorem13.lean:3571. -/
theorem chainVertexMap_chain_injective :
    Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} =>
      chainVertexMap a.val) := by sorry
/-- Source theorem13.lean:3595. -/
def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {W : Type*} [Fintype W] [DecidableEq W]
/-- Source theorem13.lean:3655. -/
def chainVertexEquivUnordered :
    {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
variable {K}
/-- Source theorem13.lean:3760. -/
def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) :
    StandardInside p ≃ (FaceVertex p →₀ ℕ) :=
  (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered
/-- Source theorem13.lean:3777. -/
def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) :
    Module.Basis (StandardInside p) K (PolynomialStalk K p) :=
  (MvPolynomial.basisMonomials (FaceVertex p) K).reindex (standardVertexEquiv hs p).symm
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:3988. -/
theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p)
    (f : FaceRing K hs) :
    polynomialRestriction K hqp (faceRingEvaluation K hs p f) =
      faceRingEvaluation K hs q f := by sorry
/-- Source theorem13.lean:3996. -/
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
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:4037. -/
def polynomialStandardCoordinates (p : P) :
    PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p :=
  (polynomialStandardBasis (K := K) hs p).repr.trans
    (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
/-- Source theorem13.lean:4081. -/
theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) :
    coefficientRestriction K standardCarrier hqp (polynomialStandardCoordinates K hs p f) =
      polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by sorry
/-- Source theorem13.lean:4109. -/
def polynomialCoefficientEquiv :
    CoherentEquiv (polynomialDiagram (P := P) K)
      (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f
/-- Source theorem13.lean:4116. -/
def polynomialSectionCoordinates :
    (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  sectionsFromCoherentCoefficients K standardCarrier (polynomialDiagram K)
    (polynomialCoefficientEquiv K hs)
/-- Source theorem13.lean:4121. -/
def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs :=
  Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)
/-- Source theorem13.lean:4124. -/
theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by sorry
/-- Source theorem13.lean:4137. -/
theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) :
    polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K hs x)) = x := by sorry
/-- Source theorem13.lean:4173. -/
def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h,
      standardFaceCombination_surjective K hs⟩).symm
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:8131. -/
def barycentricPresentationEquiv :
    BarycentricRing (P := P) K ≃ₐ[K]
      MonomialQuotient (K := K) (BarycentricAllowed (P := P)) :=
  Ideal.quotientEquivAlgOfEq K (barycentricIdeal_eq_forbiddenIdeal K)
/-- Source theorem13.lean:8136. -/
def barycentricMonomialEquiv :
    BarycentricRing (P := P) K ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  (barycentricPresentationEquiv K).toLinearEquiv.trans
    (standardMonomialEquiv BarycentricAllowed barycentricAllowed_divisorClosed)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {I K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
/-- Source theorem13.lean:8238. -/
def canonicalBasisEquiv (b : Module.Basis I K M) (c : Module.Basis I K N) : M ≃ₗ[K] N :=
  b.repr.trans c.repr.symm
/-- Source theorem13.lean:8303. -/
abbrev weightFiltrationGrade (F : ℤ → Submodule K M) (n : ℤ) :=
  (F (n + 1)) ⧸ (F n).comap (F (n + 1)).subtype
/-- Source theorem13.lean:8306. -/
def weightFiltrationLevelEquiv (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) : F n ≃ₗ[K] G n where
  toFun x := ⟨e x.val, (he n x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (he n (e.symm y.val)).mp (by
    rw [LinearEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.map_smul a x.val)
/-- Source theorem13.lean:8316. -/
theorem weightFiltrationLevelEquiv_lower (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) :
    ((F n).comap (F (n + 1)).subtype).map
      (weightFiltrationLevelEquiv F G e he (n + 1)).toLinearMap =
        (G n).comap (G (n + 1)).subtype := by sorry
/-- Source theorem13.lean:8331. -/
def weightFiltrationGradeEquiv (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) :
    weightFiltrationGrade F n ≃ₗ[K] weightFiltrationGrade G n :=
  Submodule.Quotient.equiv _ _ (weightFiltrationLevelEquiv F G e he (n + 1))
    (weightFiltrationLevelEquiv_lower F G e he n)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:8975. -/
def barycentricGlobalStandardBasis :
    Module.Basis (StandardFaceIndex P) K (BarycentricRing (P := P) K) :=
  Module.Basis.ofRepr (barycentricMonomialEquiv K)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:9096. -/
def canonicalOriginalComparison : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  canonicalBasisEquiv (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {I V K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:9407. -/
def usualFaceDegreePiece (n : ℕ) : Submodule K (FaceRing K hs) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap
/-- Source theorem13.lean:9423. -/
def usualBarycentricDegreePiece (n : ℕ) : Submodule K (BarycentricRing (P := P) K) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {I V K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
/-- The original scalar-closure proof for the unchanged coefficient predicate. -/
theorem palomarPresentationWeightLevel_smul (w : (V →₀ ℕ) → ℤ) (n : ℤ) :
    ∀ (c : K) (f : MvPolynomial V K), (∀ a, n ≤ w a → f.coeff a = 0) →
      ∀ a, n ≤ w a → (c • f).coeff a = 0 := by sorry

/-- Source theorem13.lean:9660. -/
def presentationWeightLevel (w : (V →₀ ℕ) → ℤ) (n : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a, n ≤ w a → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by intro f g hf hg a ha; simp only [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := palomarPresentationWeightLevel_smul w n

/-- Membership is determined by every monomial coefficient of weight at least n. -/
theorem mem_presentationWeightLevel_iff (w : (V →₀ ℕ) → ℤ) (n : ℤ) (f : MvPolynomial V K) :
    f ∈ presentationWeightLevel w n ↔ ∀ a, n ≤ w a → f.coeff a = 0 := by sorry
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {I V K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:9701. -/
def originalPolynomialWeight (d : ℕ) (a : NonzeroFace P →₀ ℕ) : ℤ :=
  a.sum (fun q n => (n : ℤ) * rankWeight d (faceRank q.val))
/-- Source theorem13.lean:9782. -/
def usualFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap
/-- Source theorem13.lean:9786. -/
def usualBarycentricWeightLevel (d : ℕ) (n : ℤ) : Submodule K (BarycentricRing (P := P) K) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Source theorem13.lean:10391. -/
theorem canonicalOriginalComparison_usualFiltered (d : ℕ) (n : ℤ)
    (x : BarycentricRing (P := P) K) :
    canonicalOriginalComparison K hs x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n := by sorry
end
end FourPapers.Universal
namespace PalomarBarycentricAssociatedGrade
section
open Classical MvPolynomial Finset
open FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Theorem 1.1's prescribed associated-graded comparison on the literal quotient rings. -/
theorem prescribedAssociatedGrade (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs,
      (∀ (a : MvPolynomial (Fin d) K) x,
        e (barycentricParameterAction (P := P) K d a * x) =
          faceParameterAction K hs d a * e x) ∧
      (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
      ∃ hf : ∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n,
        ∀ n : ℤ,
          weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
            (usualFaceWeightLevel K hs d) e hf n =
          weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
            (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
            (canonicalOriginalComparison_usualFiltered K hs d) n := by sorry
end
end PalomarBarycentricAssociatedGrade
