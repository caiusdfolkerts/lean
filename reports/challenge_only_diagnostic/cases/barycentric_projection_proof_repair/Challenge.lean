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
@[expose] public section
namespace PalomarBarycentric
universe uCoefficient
/-- The canonical inverse-pair law for the identity coefficient homomorphism. -/
theorem coefficientIdentityInvPair {K : Type uCoefficient} [CommRing K] :
    RingHomInvPair (RingHom.id K) (RingHom.id K) := by sorry
/-- Every ideal of a commutative coefficient algebra is two-sided. -/
theorem coefficientIdealTwoSided {R : Type uCoefficient} [CommRing R] (I : Ideal R) :
    I.IsTwoSided := by sorry
/-- Identity inverse-pair with the commutative-semiring projection used by the basis representation. -/
theorem commutativeCoefficientIdentityInvPair {K : Type uCoefficient} [hK : CommRing K] :
    @RingHomInvPair K K hK.toCommSemiring.toSemiring hK.toCommSemiring.toSemiring
      (@RingHom.id K hK.toCommSemiring.toSemiring.toNonAssocSemiring)
      (@RingHom.id K hK.toCommSemiring.toSemiring.toNonAssocSemiring) := by infer_instance
attribute [instance 2100] commutativeCoefficientIdentityInvPair
attribute [instance 2000] coefficientIdentityInvPair coefficientIdealTwoSided
end PalomarBarycentric
end
/-!
# Universal parameter modules for actual face rings
The genuine face ring and its barycentric Stanley--Reisner quotient admit
coherent graded comparisons over universal rank parameters. The selected
statements include all relative restriction kernels and integral coefficient
base change, the uniform factorial-unit criterion for equivariance, and the
negative simplex obstruction even without grading or coherence. The canonical
associated-graded map and derived-Tor conclusions remain separate entries.
-/
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
/-- The paper's definition of a finite simplicial poset. -/
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
/-- The canonical vertices, as atoms in the original poset. -/
def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p
/-- Literal retained-source theorem; original position theorem13.lean:152. -/
theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
/-- Every subset of the vertices of a face occurs as exactly one subface. -/
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P)
    (hsu : s ⊆ faceVertices p) :
    ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
/-- Membership in the actual vertex set is exactly being an atom below the face. -/
@[simp] theorem mem_faceVertices {p a : P} :
    a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
/-- The rank is the number of vertices in a Boolean face. -/
def faceRank (p : P) : ℕ := (faceVertices p).card
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
/-- A diagram of coefficient modules with specified face restrictions and their identity and composition laws. -/
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
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
universe u v w
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
/-- An objectwise linear equivalence commuting with every face restriction. -/
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
/-- Literal retained-source def; original position theorem13.lean:384. -/
def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) =
      f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]
end
end FourPapers.Universal.CoherentEquiv
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- The actual atoms of the poset lying below the specified face. -/
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
/-- Literal retained-source instance; original position theorem13.lean:492. -/
instance palomarFaceVertexFintype (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _
/-- Literal retained-source def; original position theorem13.lean:494. -/
def faceVertexInclusion {p q : P} (hqp : q ≤ p) : FaceVertex q ↪ FaceVertex p where
  toFun a := ⟨a.val, a.property.1, a.property.2.trans hqp⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : FaceVertex p => a.val) h)
/-- The polynomial ring on the actual vertices below the specified face. -/
abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
/-- Restriction is an algebra homomorphism, not an abstract chosen linear map. -/
def polynomialRestriction {p q : P} (hqp : q ≤ p) :
    PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
/-- Literal retained-source theorem; original position theorem13.lean:517. -/
theorem polynomialRestriction_refl (p : P) :
    polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
/-- Literal retained-source theorem; original position theorem13.lean:524. -/
theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
      polynomialRestriction K (hrq.trans hqp) := by sorry
/-- The polynomial rings and their actual face restrictions form a diagram. -/
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
/-- On a stalk, the universal rank parameters are elementary symmetric polynomials. -/
def polynomialParameter (p : P) (i : ℕ) : PolynomialStalk K p :=
  MvPolynomial.esymm (FaceVertex p) K i
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- The nonminimal faces of the poset, as a subtype of its elements. -/
abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
/-- Literal retained-source instance; original position theorem13.lean:631. -/
instance palomarNonzeroFaceFintype : Fintype (NonzeroFace P) := Fintype.ofFinite _
/-- The meet of two faces in a specified common Boolean upper interval. -/
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
/-- Literal retained-source def; original position theorem13.lean:682. -/
def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
/-- Literal retained-source def; original position theorem13.lean:685. -/
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
/-- Literal retained-source abbrev; original position theorem13.lean:694. -/
abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
/-- The bottom-face symbol is the scalar one, as in the original definition. -/
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
/-- All conventional straightening relations, with no additional relations. Common-upper witnesses give the same meet, by the independence theorem above. -/
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}
/-- Literal retained-source def; original position theorem13.lean:717. -/
def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)
/-- Two-sidedness of the actual face ideal, specialized to its literal coefficient algebra. -/
theorem palomarFaceIdealTwoSided (hs : IsSimplicialPoset P) :
    (faceIdeal K hs).IsTwoSided := by infer_instance
attribute [instance 2100] palomarFaceIdealTwoSided
/-- The actual face ring, with the straightening relations and the empty face identified with one. -/
abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs
/-- The Stanley--Reisner ideal of the order complex, generated by incomparable pairs. -/
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
/-- The actual Stanley--Reisner quotient of the order complex of nonminimal faces. -/
abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
/-- Literal retained-source def; original position theorem13.lean:731. -/
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
/-- Literal retained-source def; original position theorem13.lean:734. -/
def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
/-- The universal parameters are sums of the actual rank-i face generators. -/
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
/-- Literal retained-source def; original position theorem13.lean:741. -/
def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
/-- Literal retained-source def; original position theorem13.lean:744. -/
def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
/-- Literal retained-source def; original position theorem13.lean:748. -/
def barycentricParameterAction (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V]
/-- Literal retained-source def; original position theorem13.lean:778. -/
def vertexDegree (a : V → ℕ) : ℕ := ∑ v, a v
/-- Literal retained-source def; original position theorem13.lean:782. -/
def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- The vertices of `q` that occur in the ambient face `p`. -/
def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q
/-- Literal retained-source theorem; original position theorem13.lean:1065. -/
@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
/-- Literal retained-source def; original position theorem13.lean:1070. -/
def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a
/-- Literal retained-source def; original position theorem13.lean:1076. -/
def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
/-- Evaluation before taking the original face-ring quotient. -/
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val
/-- Literal retained-source theorem; original position theorem13.lean:1166. -/
theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P)
    {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    faceEvaluation K r f = 0 := by sorry
/-- The map is defined on the conventional face-ring presentation. -/
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
/-- An allowed collection of exponent vectors is closed under divisibility. -/
def IsDivisorClosed (P : (V →₀ ℕ) → Prop) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → P b → P a
/-- The actual ideal generated by the forbidden monomials. -/
def forbiddenIdeal (P : (V →₀ ℕ) → Prop) : Ideal (MvPolynomial V K) :=
  Ideal.span ((fun a : V →₀ ℕ => MvPolynomial.monomial a (1 : K)) '' {a | ¬ P a})
/-- The usual monomial quotient algebra. -/
abbrev MonomialQuotient (P : (V →₀ ℕ) → Prop) :=
  MvPolynomial V K ⧸ forbiddenIdeal P
/-- Read off precisely the coefficients of the allowed monomials. -/
def standardCoefficients (P : (V →₀ ℕ) → Prop) :
    MvPolynomial V K →ₗ[K] ({a // P a} →₀ K) :=
  (Finsupp.lsubtypeDomain {a | P a}).comp
    (MvPolynomial.basisMonomials V K).repr.toLinearMap
/-- Literal retained-source lemma; original position theorem13.lean:1254. -/
lemma standardCoefficients_surjective (P : (V →₀ ℕ) → Prop) :
    Function.Surjective (standardCoefficients (K := K) P) := by sorry
/-- Literal retained-source lemma; original position theorem13.lean:1267. -/
lemma standardCoefficients_ker (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) :
    LinearMap.ker (standardCoefficients (K := K) P) =
      (forbiddenIdeal P).restrictScalars K := by sorry
/-- A coefficient equivalence on the genuine quotient, not on a surrogate vector space. It provides the standard monomial basis over every commutative ring. -/
def standardMonomialEquiv (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    MonomialQuotient (K := K) P ≃ₗ[K] ({a // P a} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (standardCoefficients_ker (K := K) P hP).symm).trans
    ((standardCoefficients (K := K) P).quotKerEquivOfSurjective
      (standardCoefficients_surjective (K := K) P))
/-- The allowed monomials form a basis of the actual quotient. -/
def standardMonomialBasis (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    Module.Basis {a // P a} K (MonomialQuotient (K := K) P) :=
  (Finsupp.basisSingleOne).map (standardMonomialEquiv P hP).symm
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
/-- Nonempty faces of the Boolean simplex on `V`. -/
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
/-- The original finite color bound, with the original cardinality proof. -/
theorem BooleanFace.palomarColorBound (F : BooleanFace V) :
    F.val.card - 1 < Fintype.card V := by sorry
/-- Rank minus one, to index the rank parameters by `Fin (card V)`. -/
def BooleanFace.color (F : BooleanFace V) : Fin (Fintype.card V) :=
  ⟨F.val.card - 1, BooleanFace.palomarColorBound F⟩
/-- Literal retained-source theorem; original position theorem13.lean:1612. -/
theorem BooleanFace.card_eq_of_color_eq {F G : BooleanFace V}
    (h : (BooleanFace.color F) = G.color) : F.val.card = G.val.card := by sorry
/-- The support of a standard barycentric monomial is a chain of faces. -/
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
/-- Literal retained-source theorem; original position theorem13.lean:1623. -/
theorem isChainExponent_divisorClosed : IsDivisorClosed (IsChainExponent (V := V)) := by sorry
/-- The usual Stanley--Reisner ring of the Boolean order complex. -/
abbrev BooleanBarycentricRing (V K : Type*) [Fintype V] [DecidableEq V] [CommRing K] :=
  MonomialQuotient (K := K) (IsChainExponent (V := V))
/-- Its genuine chain-monomial coefficient basis. -/
def booleanChainBasis :
    Module.Basis {a : BooleanFace V →₀ ℕ // IsChainExponent a} K
      (BooleanBarycentricRing V K) :=
  standardMonomialBasis IsChainExponent isChainExponent_divisorClosed
/-- Literal retained-source def; original position theorem13.lean:1658. -/
def faceVariable (F : BooleanFace V) : BooleanBarycentricRing V K :=
  Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent) (MvPolynomial.X F)
/-- Literal retained-source def; original position theorem13.lean:1694. -/
def facesOfColor (c : Fin (Fintype.card V)) : Finset (BooleanFace V) :=
  Finset.univ.filter (fun F => (BooleanFace.color F) = c)
/-- The paper's rank color sum, with `c` representing rank `c+1`. -/
def colorSum (c : Fin (Fintype.card V)) : BooleanBarycentricRing V K :=
  ∑ F ∈ facesOfColor c, faceVariable F
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal retained-source def; original position theorem13.lean:1961. -/
def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
/-- Literal retained-source theorem; original position theorem13.lean:1976. -/
theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by sorry
/-- The original chosen nonempty subface is not the bottom face. -/
theorem palomarBooleanFaceInclusion_nonzero (hs : IsSimplicialPoset P) (p : P)
    (F : BooleanFace (FaceVertex p)) : (subfaceOfVertexSet hs p F.val).val ≠ ⊥ := by sorry
/-- Exactly the original face inclusion function, with its named nonzero proof. -/
def palomarBooleanFaceInclusionValue (hs : IsSimplicialPoset P) (p : P)
    (F : BooleanFace (FaceVertex p)) : NonzeroFace P :=
  ⟨(subfaceOfVertexSet hs p F.val).val, palomarBooleanFaceInclusion_nonzero hs p F⟩
/-- Injectivity by the original vertex-set argument. -/
theorem palomarBooleanFaceInclusionValue_injective (hs : IsSimplicialPoset P) (p : P) :
    Function.Injective (palomarBooleanFaceInclusionValue hs p) := by sorry
/-- Nonempty Boolean faces embed as actual nonzero subfaces of the original poset. The embedding is confined to this Boolean interval. -/
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) :
    BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun := palomarBooleanFaceInclusionValue hs p
  inj' := palomarBooleanFaceInclusionValue_injective hs p
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Exponent vectors whose nonzero support is a chain of nonminimal faces. -/
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
/-- Literal retained-source theorem; original position theorem13.lean:2053. -/
theorem barycentricAllowed_divisorClosed :
    IsDivisorClosed (BarycentricAllowed (P := P)) := by sorry
/-- The ordinary incomparable-pair presentation is exactly the forbidden- monomial ideal. Thus the quotient basis is a theorem about the original ring. -/
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
/-- Literal retained-source theorem; original position theorem13.lean:2205. -/
theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
    BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
variable {V W K : Type*} [CommRing K]
/-- Literal retained-source theorem; original position theorem13.lean:2279. -/
theorem killCompl_mem_forbiddenIdeal
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    {f : MvPolynomial W K} (hf : f ∈ forbiddenIdeal P) :
    MvPolynomial.killCompl e.injective f ∈ forbiddenIdeal Q := by sorry
/-- Restriction between the actual quotient algebras. -/
def monomialRestriction
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) :
    MonomialQuotient (K := K) P →ₐ[K] MonomialQuotient (K := K) Q :=
  Ideal.Quotient.liftₐ (forbiddenIdeal P)
    ((Ideal.Quotient.mkₐ K (forbiddenIdeal Q)).comp
      (MvPolynomial.killCompl e.injective)) (by
        intro f hf
        change Ideal.Quotient.mk (forbiddenIdeal Q)
          (MvPolynomial.killCompl e.injective f) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (killCompl_mem_forbiddenIdeal e P Q hP hQ allowed hf))
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {U V W K : Type*}
  [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W] [CommRing K]
/-- Literal retained-source def; original position theorem13.lean:2350. -/
def booleanFaceEmbedding (e : V ↪ W) : BooleanFace V ↪ BooleanFace W where
  toFun F := ⟨F.val.map e, F.property.map (f := e)⟩
  inj' F G h := Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))
/-- Literal retained-source theorem; original position theorem13.lean:2372. -/
theorem isChainExponent_map_booleanFaceEmbedding (e : V ↪ W)
    {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a.mapDomain (booleanFaceEmbedding e)) := by sorry
/-- Literal retained-source def; original position theorem13.lean:2383. -/
def booleanRestriction (e : V ↪ W) :
    BooleanBarycentricRing W K →ₐ[K] BooleanBarycentricRing V K :=
  monomialRestriction (booleanFaceEmbedding e) IsChainExponent IsChainExponent
    isChainExponent_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => isChainExponent_map_booleanFaceEmbedding e ha)
/-- Literal retained-source theorem; original position theorem13.lean:2425. -/
theorem booleanRestriction_refl :
    booleanRestriction (K := K) (Function.Embedding.refl V) =
      AlgHom.id K (BooleanBarycentricRing V K) := by sorry
/-- Literal retained-source theorem; original position theorem13.lean:2441. -/
theorem booleanRestriction_comp (e : U ↪ V) (f : V ↪ W) :
    (booleanRestriction (K := K) e).comp (booleanRestriction f) =
      booleanRestriction (e.trans f) := by sorry
/-- Rank-indexed color sums include every rank, so they restrict without changing the global parameter index when a face has fewer vertices. -/
def booleanRankParameter (r : ℕ) : BooleanBarycentricRing V K :=
  ∑ F : BooleanFace V, if F.val.card = r then faceVariable F else 0
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Literal retained-source theorem; original position theorem13.lean:2692. -/
@[simp] theorem faceVertexInclusion_refl (p : P) :
    faceVertexInclusion (le_refl p) = Function.Embedding.refl (FaceVertex p) := by sorry
/-- Literal retained-source theorem; original position theorem13.lean:2697. -/
@[simp] theorem faceVertexInclusion_trans {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (faceVertexInclusion hrq).trans (faceVertexInclusion hqp) =
      faceVertexInclusion (hrq.trans hqp) := by sorry
/-- The Boolean barycentric Stanley--Reisner quotient on the vertices of the specified face. -/
abbrev BarycentricStalk (p : P) := BooleanBarycentricRing (FaceVertex p) K
/-- The original identity law for the actual Boolean restriction map. -/
theorem palomarBarycentricDiagram_res_refl (p : P) (x : BarycentricStalk K p) :
    (booleanRestriction (K := K) (faceVertexInclusion (le_refl p))).toLinearMap x = x := by sorry
/-- The original composition law for the actual Boolean restriction maps. -/
theorem palomarBarycentricDiagram_res_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q)
    (x : BarycentricStalk K p) :
    (booleanRestriction (K := K) (faceVertexInclusion hrq)).toLinearMap
      ((booleanRestriction (K := K) (faceVertexInclusion hqp)).toLinearMap x) =
      (booleanRestriction (K := K) (faceVertexInclusion (hrq.trans hqp))).toLinearMap x := by sorry
/-- Literal retained-source abbrev; original position theorem13.lean:2705. -/
abbrev barycentricDiagram : ModuleDiagram K P where
  obj p := BarycentricStalk K p
  res h := (booleanRestriction (K := K) (faceVertexInclusion h)).toLinearMap
  res_refl := palomarBarycentricDiagram_res_refl K
  res_comp := palomarBarycentricDiagram_res_comp K
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]
universe uPolynomialV uPolynomialK
/-- The original scalar-closure proof for the unchanged coefficient predicate. -/
theorem palomarPolynomialDegreePiece_smul {V : Type uPolynomialV} {K : Type uPolynomialK}
    [Fintype V] [CommRing K] (n : ℕ) :
    ∀ (c : K) (f : MvPolynomial V K),
      (∀ a : V →₀ ℕ, vertexDegree (fun v => a v) ≠ n → f.coeff a = 0) →
      ∀ a : V →₀ ℕ, vertexDegree (fun v => a v) ≠ n → (c • f).coeff a = 0 := by sorry
/-- Literal retained-source def; original position theorem13.lean:7499. -/
def polynomialDegreePiece (n : ℕ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a : V →₀ ℕ, vertexDegree (fun v => a v) ≠ n → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by
    intro f g hf hg a ha
    rw [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := palomarPolynomialDegreePiece_smul n
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {V W K L : Type*} [CommRing K] [CommRing L]
variable (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) (h : K →+* L)
/-- Apply the coefficient homomorphism to the actual standard coefficients. -/
def monomialCoefficientMap :
    MonomialQuotient (K := K) P →ₛₗ[h] MonomialQuotient (K := L) P :=
  (standardMonomialEquiv (K := L) P hP).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap h.toSemilinearMap).comp
      (standardMonomialEquiv (K := K) P hP).toLinearMap)
/-- The coefficient-coordinate map is precisely the usual coefficient map on polynomial representatives, so it respects the intended quotient objects. -/
@[simp] theorem monomialCoefficientMap_mk (f : MvPolynomial V K) :
    monomialCoefficientMap P hP h (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      Ideal.Quotient.mk (forbiddenIdeal P) (MvPolynomial.map h f) := by sorry
/-- The same explicit map is a homomorphism of the actual quotient rings. -/
def monomialCoefficientRingHom :
    MonomialQuotient (K := K) P →+* MonomialQuotient (K := L) P where
  toFun := monomialCoefficientMap P hP h
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    have he := monomialCoefficientMap_mk P hP h (1 : MvPolynomial V K)
    simpa only [map_one] using he
  map_mul' x y := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul (Ideal.Quotient.mk (forbiddenIdeal (K := K) P)) f g,
      monomialCoefficientMap_mk, monomialCoefficientMap_mk, monomialCoefficientMap_mk,
      map_mul (MvPolynomial.map h), map_mul]
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Literal retained-source def; original position theorem13.lean:8131. -/
def barycentricPresentationEquiv :
    BarycentricRing (P := P) K ≃ₐ[K]
      MonomialQuotient (K := K) (BarycentricAllowed (P := P)) :=
  Ideal.quotientEquivAlgOfEq K (barycentricIdeal_eq_forbiddenIdeal K)
/-- Actual face restriction sends precisely the generators below the chosen face to their Boolean-interval generators and kills all others. -/
def barycentricRingEvaluation (p : P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricStalk K p :=
  (monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed IsChainExponent
    barycentricAllowed_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)).comp
      (barycentricPresentationEquiv K).toAlgHom
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable {K L : Type*} [CommRing K] [CommRing L]
variable (hs : IsSimplicialPoset P) (h : K →+* L)
/-- Literal retained-source theorem; original position theorem13.lean:9174. -/
theorem map_faceRelation {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    MvPolynomial.map h f ∈ faceRelations L hs := by sorry
/-- Literal retained-source def; original position theorem13.lean:9184. -/
def originalFaceCoefficientChange : FaceRing K hs →+* FaceRing L hs :=
  letI : (faceIdeal K hs).IsTwoSided := palomarFaceIdealTwoSided K hs
  letI : (faceIdeal L hs).IsTwoSided := palomarFaceIdealTwoSided L hs
  Ideal.quotientMap (faceIdeal L hs) (MvPolynomial.map h) (by
    apply Ideal.span_le.mpr
    intro f hf
    exact Ideal.subset_span (map_faceRelation hs h hf))
/-- Literal retained-source def; original position theorem13.lean:9194. -/
def originalBarycentricCoefficientChange : BarycentricRing (P := P) K →+* BarycentricRing (P := P) L :=
  (barycentricPresentationEquiv L).symm.toRingHom.comp
    ((monomialCoefficientRingHom BarycentricAllowed barycentricAllowed_divisorClosed h).comp
      (barycentricPresentationEquiv K).toRingHom)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {I V K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
/-- Zero satisfies the original degree-support predicate. -/
theorem palomarBasisOrdinaryDegreePiece_zero (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) : ∀ i, degree i ≠ n → b.repr (0 : M) i = 0 := by
  intro i hi; simp
/-- Addition preserves the original degree-support predicate. -/
theorem palomarBasisOrdinaryDegreePiece_add (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) :
    ∀ (x y : M), (∀ i, degree i ≠ n → b.repr x i = 0) →
      (∀ i, degree i ≠ n → b.repr y i = 0) → ∀ i, degree i ≠ n → b.repr (x + y) i = 0 := by
  intro x y hx hy i hi; simp only [map_add, Finsupp.add_apply, hx i hi, hy i hi, add_zero]
/-- The original scalar-closure proof for the unchanged coefficient predicate. -/
theorem palomarBasisOrdinaryDegreePiece_smul (b : Module.Basis I K M)
    (degree : I → ℕ) (n : ℕ) :
    ∀ (c : K) (x : M), (∀ i, degree i ≠ n → b.repr x i = 0) →
      ∀ i, degree i ≠ n → b.repr (c • x) i = 0 := by sorry
/-- Literal retained-source def; original position theorem13.lean:9287. -/
def basisOrdinaryDegreePiece (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) : Submodule K M where
  carrier := {x | ∀ i, degree i ≠ n →
    (@LinearEquiv.toLinearMap K K _ _ (RingHom.id K) (RingHom.id K)
      (PalomarBarycentric.commutativeCoefficientIdentityInvPair (K := K))
      (PalomarBarycentric.commutativeCoefficientIdentityInvPair (K := K))
      M (I →₀ K) _ _ _ _ b.repr) x i = 0}
  zero_mem' := palomarBasisOrdinaryDegreePiece_zero b degree n
  add_mem' := fun {x y} => palomarBasisOrdinaryDegreePiece_add b degree n x y
  smul_mem' := palomarBasisOrdinaryDegreePiece_smul b degree n
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
/-- The conventional degree piece is the image of the actual homogeneous polynomials in the original presentation. -/
def usualFaceDegreePiece (n : ℕ) : Submodule K (FaceRing K hs) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap
/-- Literal retained-source def; original position theorem13.lean:9423. -/
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
/-- Literal retained-source def; original position theorem13.lean:9660. -/
def presentationWeightLevel (w : (V →₀ ℕ) → ℤ) (n : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a, n ≤ w a → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by intro f g hf hg a ha; simp only [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := palomarPresentationWeightLevel_smul w n
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {I V K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)
/-- Literal retained-source def; original position theorem13.lean:9701. -/
def originalPolynomialWeight (d : ℕ) (a : NonzeroFace P →₀ ℕ) : ℤ :=
  a.sum (fun q n => (n : ℤ) * rankWeight d (faceRank q.val))
/-- Literal retained-source def; original position theorem13.lean:9782. -/
def usualFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap
/-- Literal retained-source def; original position theorem13.lean:9786. -/
def usualBarycentricWeightLevel (d : ℕ) (n : ℤ) : Submodule K (BarycentricRing (P := P) K) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
/-- A downward-closed simplicial complex with a vertex coloring injective on each face. -/
structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
end
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
variable (D : ProperlyColoredComplex V C)
/-- Literal retained-source def; original position theorem13.lean:10763. -/
def allowed (a : V →₀ ℕ) : Prop := D.face a.support
end
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal.ProperlyColoredComplex
section
set_option backward.isDefEq.respectTransparency false
open Classical Finset MvPolynomial
variable {V C : Type*} [Fintype V] [Fintype C]
variable (D : ProperlyColoredComplex V C)
variable (K : Type*) [CommRing K]
/-- Literal source order: the complex argument precedes its coefficient ring. -/
abbrev Ring := MonomialQuotient (K := K) D.allowed
end
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]
/-- Literal retained-source def; original position theorem13.lean:16746. -/
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
/-- The same rank-weighted ordinary degree as `chainOrdinaryDegree`, with no auxiliary ordering of the vertex type required in its interface. -/
def booleanOrdinaryDegree [DecidableEq V] (a : BooleanFace V →₀ ℕ) : ℕ :=
  a.sum (fun F n => n * F.val.card)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
/-- Literal retained-source def; original position theorem13.lean:16864. -/
def faceVertexOrderEquiv (e : P ≃o P) (p : P) : FaceVertex p ≃ FaceVertex (e p) where
  toFun a := ⟨e a.val, (e.isAtom_iff a.val).mpr a.property.1, e.monotone a.property.2⟩
  invFun a := ⟨e.symm a.val, (e.symm.isAtom_iff a.val).mpr a.property.1,
    by simpa only [e.symm_apply_apply] using e.symm.monotone a.property.2⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]
/-- Literal retained-source def; original position theorem13.lean:16900. -/
def polynomialStalkOrderEquiv (e : P ≃o P) (p : P) :
    PolynomialStalk K p ≃ₐ[K] PolynomialStalk K (e p) :=
  MvPolynomial.renameEquiv K (faceVertexOrderEquiv e p)
/-- Literal retained-source def; original position theorem13.lean:16904. -/
def barycentricStalkOrderEquiv (e : P ≃o P) (p : P) :
    BarycentricStalk K p ≃ₐ[K] BarycentricStalk K (e p) :=
  booleanVertexRelabelEquiv (faceVertexOrderEquiv e p)
end
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable {V C K G : Type*} [Fintype V] [Fintype C] [CommRing K] [Group G]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C) (K)
/-- Literal retained-source def; original position theorem13.lean:21017. -/
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
end
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [CommRing K]
local instance (priority := 2000) palomarLocalInstance21241 : DecidableEq V := Classical.decEq V
local instance (priority := 2000) palomarLocalInstance21242 : DecidableEq (BooleanFace V) := Classical.decEq _
/-- The properly rank-colored order complex of the full Boolean simplex. Its monomial quotient is definitionally the existing barycentric ring. -/
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
/-- Literal retained-source def; original position theorem13.lean:21273. -/
def booleanFacePermutation (e : Equiv.Perm V) : Equiv.Perm (BooleanFace V) where
  toFun F := ⟨F.val.image e, F.property.image e⟩
  invFun F := ⟨F.val.image e.symm, F.property.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]
/-- Literal retained-source theorem; original position theorem13.lean:21302. -/
theorem booleanFacePermutation_face (e : Equiv.Perm V) (s : Finset (BooleanFace V)) :
    (booleanColoredComplex V).face (s.image (booleanFacePermutation e)) ↔
      (booleanColoredComplex V).face s := by sorry
/-- Relabeling the genuine quotient ring by a vertex permutation. -/
def booleanRename (K : Type*) [CommRing K] (e : Equiv.Perm V) :
    BooleanBarycentricRing V K →ₐ[K] BooleanBarycentricRing V K :=
  (booleanColoredComplex V).colorRename K (booleanFacePermutation e)
    (booleanFacePermutation_face e)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable (V K : Type*) [Fintype V] [CommRing K]
local instance (priority := 2000) palomarLocalInstance22075 : DecidableEq V := Classical.decEq V
local instance (priority := 2000) palomarLocalInstance22076 : DecidableEq (BooleanFace V) := Classical.decEq _
/-- Exactly an unrestricted equivariant universal-parameter module comparison on one simplex. Grading, coherence, and multiplication preservation are absent. -/
structure SimplexEquivariantParameterComparison where
  equiv : MvPolynomial V K ≃ₗ[K] BooleanBarycentricRing V K
  parameter : ∀ (i : Fin (Fintype.card V)) x,
    equiv (MvPolynomial.esymm V K (i.val + 1) * x) = colorSum (K := K) i * equiv x
  equivariant : ∀ (g : Equiv.Perm V) x,
    equiv (MvPolynomial.rename g x) = booleanRename K g (equiv x)
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical Finset MvPolynomial
variable (V K : Type*) [Fintype V] [CommRing K]
attribute [local instance 2000] palomarLocalInstance22075
attribute [local instance 2000] palomarLocalInstance22076
variable {V K} {U : Type*} [Fintype U]
local instance (priority := 2000) palomarLocalInstance22099 : DecidableEq U := Classical.decEq U
local instance (priority := 2000) palomarLocalInstance22100 : DecidableEq (BooleanFace U) := Classical.decEq _
/-- The negative half of Theorem 1.3 in its full stated strength: a nonunit factorial excludes even an ungraded, incoherent parameter-module isomorphism equivariant under the entire symmetric group. -/
theorem factorial_nonunit_no_simplex_comparison
    (hd : 1 ≤ Fintype.card V)
    (hfactorial : ¬ IsUnit (((Fintype.card V - 1).factorial : ℕ) : K)) :
    IsEmpty (SimplexEquivariantParameterComparison V K) := by sorry
end
end FourPapers.Universal
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open Classical Finset MvPolynomial
/-- The paper's uniform existence assertion, in arbitrary finite-poset universe. Coherence and ordinary grading are explicit. Equivariance for the entire order automorphism group implies equivariance for each of its group actions, without any hypothesis on the group order in `K`. -/
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
/-- **Theorem 1.3, literal uniform if and only if.** Necessity is obtained from a rank-d Boolean simplex in the quantified universe, and the explicit bridge above supplies the exact polynomial/barycentric rings and actions required by the unrestricted negative theorem. -/
theorem theorem_1_3_uniform_iff (K : Type v) [CommRing K]
    (d : ℕ) (hd : 1 ≤ d) :
    UniformCoherentEquivariantComparisons.{u, v} K d ↔
      IsUnit (((d - 1).factorial : ℕ) : K) := by sorry
end
end FourPapers.Universal
namespace PalomarBarycentric
section
open Classical MvPolynomial Finset
open scoped BigOperators
open FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- The global ordinary-graded, rank-filtered universal-parameter comparison on the actual quotient rings. -/
theorem parameterModuleComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs,
      (∀ (a : MvPolynomial (Fin d) K) x,
        e (barycentricParameterAction (P := P) K d a * x) =
          faceParameterAction K hs d a * e x) ∧
      (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
      (∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n) := by sorry
end
end PalomarBarycentric
namespace PalomarBarycentric
section
open Classical MvPolynomial Finset
open scoped BigOperators
open FourPapers.Universal
universe v
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)
/-- A single integral comparison extends to every coefficient ring, coherently on all stalks and relative restriction kernels. -/
theorem integralCoherentComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ eZ : BarycentricRing (P := P) ℤ ≃ₗ[ℤ] FaceRing ℤ hs,
      ∀ (K : Type v) [CommRing K],
        ∃ (e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs)
          (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)),
          (∀ (a : MvPolynomial (Fin d) K) x,
            e (barycentricParameterAction (P := P) K d a * x) =
              faceParameterAction K hs d a * e x) ∧
          (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
          (∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n) ∧
          (∀ x p, faceRingEvaluation K hs p (e x) = E.component p (barycentricRingEvaluation K hs p x)) ∧
          (∀ (Q : Set P) x,
            (∀ p ∈ Q, faceRingEvaluation K hs p (e x) = 0) ↔
              ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0) ∧
          (∀ x : BarycentricRing (P := P) ℤ,
            originalFaceCoefficientChange hs (Int.castRingHom K) (eZ x) =
              e (originalBarycentricCoefficientChange (P := P) (Int.castRingHom K) x)) := by sorry
end
end PalomarBarycentric

namespace FourPapers.Universal
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
example (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  change b.repr (b i) j = 0
  by_cases h : i = j
  · subst j; exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]
example (b : Module.Basis I K M) (w : I → ℕ) (n : ℕ) (x : M)
    (hx : x ∈ basisOrdinaryDegreePiece b w n) (i : I) (hi : w i ≠ n) : b.repr x i = 0 := by
  change ∀ j, w j ≠ n → b.repr x j = 0 at hx
  exact hx i hi
end FourPapers.Universal
