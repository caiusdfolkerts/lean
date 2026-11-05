module

public import paper_verification.literal008
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Lean.Elab.Tactic.Omega
public import paper_verification.literal004
public import Mathlib.Data.Finset.Sort
public import paper_verification.literal000
public import paper_verification.literal001
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring

set_option Elab.async false

section TAF_LiteralSource_0485
/- Original module: PaperVerification.WeightedBarDegrees -/


/-!
# Actual internal degrees and finite dimensions in the noncommutative bar complex

The subcomplex of degree N is defined by the sum of the actual homogeneous
basis degrees. Its differential is the original multiplication differential.
Finite word counting proves its term dimensions; positivity proves the length
bound. These are supporting results, not a Koszulness assertion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.WeightedBar

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def totalDegree (L : List C) : ℕ := (L.map δ).sum

@[simp] theorem totalDegree_nil : totalDegree δ []=0 := rfl

@[simp] theorem totalDegree_cons (c : C) (L : List C) :
    totalDegree δ (c::L)=δ c+totalDegree δ L := rfl

theorem totalDegree_append (L T : List C) :
    totalDegree δ (L++T)=totalDegree δ L+totalDegree δ T := by
  simp only [totalDegree,List.map_append,List.sum_append]

def degreePiece (N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | totalDegree δ L=N}

theorem degreePiece_eq_span (N : ℕ) :
    degreePiece (K := K) δ N=Submodule.span K
      ((fun L : List C ↦ Finsupp.single L (1 : K)) '' {L | totalDegree δ L=N}) :=
  Finsupp.supported_eq_span_single K _

theorem prefix_mem_degreePiece (c : C) {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : prepend c z∈degreePiece δ (δ c+N) := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change totalDegree δ (c::L)=δ c+N
    change totalDegree δ L=N at hL
    rw [totalDegree_cons,hL]
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ (δ c+N)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ (δ c+N)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ (δ c+N)).smul_mem a ih

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem product_appendTail_mem_degreePiece (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)∈degreePiece δ (δ a+δ b+totalDegree δ L) := by
  rw [appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported K 1
  change totalDegree δ (c::L)=δ a+δ b+totalDegree δ L
  rw [totalDegree_cons,hδ a b c (Finsupp.mem_support_iff.mp hc)]

include hδ in
theorem differentialBasis_mem_degreePiece (L : List C) :
    differentialBasis B L∈degreePiece δ (totalDegree δ L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      rw [differentialBasis]
      apply Submodule.sub_mem
      · rw [merge_single,one_smul,mergeBasis]
        simpa only [totalDegree_cons,Nat.add_assoc] using
          product_appendTail_mem_degreePiece B δ hδ a b L
      · exact prefix_mem_degreePiece δ a _ ih

include hδ in
theorem differential_mem_degreePiece {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : differential B z∈degreePiece δ N := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [differential_single,one_smul]
    change totalDegree δ L=N at hL
    simpa only [hL] using differentialBasis_mem_degreePiece B δ hδ L
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ N).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ N).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ N).smul_mem a ih

end PaperVerification.WeightedBar

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis
open PaperVerification.NoncommutativeBar

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

def Index (r N : ℕ) := {L : List I // L.length=r ∧ totalDegree δ L=N}

def piece (r N : ℕ) : Submodule K (List I →₀ K) :=
  Finsupp.supported K K {L | L.length=r ∧ totalDegree δ L=N}

theorem piece_eq_inf (r N : ℕ) :
    piece (K := K) δ r N=lengthPiece I K r ⊓ degreePiece δ N := by
  ext z
  change ((z.support : Set (List I))⊆{L | L.length=r ∧ totalDegree δ L=N}) ↔
    ((z.support : Set (List I))⊆{L | L.length=r}) ∧
      ((z.support : Set (List I))⊆{L | totalDegree δ L=N})
  simp only [Set.subset_def,Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun L hL ↦ (h L hL).1,fun L hL ↦ (h L hL).2⟩
  · rintro ⟨h₁,h₂⟩ L hL
    exact ⟨h₁ L hL,h₂ L hL⟩

def coordinates (r N : ℕ) :
    piece (K := K) δ r N ≃ₗ[K] (Index δ r N →₀ K) :=
  Finsupp.supportedEquivFinsupp (R := K) _

def basis (r N : ℕ) : Module.Basis (Index δ r N) K (piece (K := K) δ r N) :=
  .ofRepr (coordinates δ r N)

instance indexFinite [Finite I] (r N : ℕ) : Finite (Index δ r N) :=
  Finite.of_injective
    (fun L : Index δ r N ↦ (Equiv.vectorEquivFin I r)
      (⟨L.val,L.property.1⟩ : List.Vector I r))
    (by
      intro L T h
      apply Subtype.ext
      exact congrArg (fun v : List.Vector I r ↦ v.val)
        ((Equiv.vectorEquivFin I r).injective h))

instance indexFintype [Fintype I] (r N : ℕ) : Fintype (Index δ r N) := Fintype.ofFinite _

instance pieceFinite [Fintype I] (r N : ℕ) : Module.Finite K (piece (K := K) δ r N) :=
  Module.Finite.of_basis (basis δ r N)

theorem piece_finrank [Fintype I] (r N : ℕ) :
    Module.finrank K (piece (K := K) δ r N)=Nat.card (Index δ r N) := by
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (basis δ r N)

include hδ in
theorem differential_mem_piece {r N : ℕ} (z : List I →₀ K)
    (hz : z∈piece δ (r+1) N) :
    PaperVerification.ReducedBarBasis.differential B z∈piece δ r N := by
  rw [piece_eq_inf] at hz ⊢
  exact ⟨reducedDifferential_mem_lengthPiece B z hz.1,
    differential_mem_degreePiece B δ hδ z hz.2⟩

def internalDifferential (r N : ℕ) : piece (K := K) δ (r+1) N →ₗ[K] piece (K := K) δ r N where
  toFun z := ⟨-PaperVerification.ReducedBarBasis.differential B z.val,
    Submodule.neg_mem _ (differential_mem_piece B δ hδ z.val z.property)⟩
  map_add' z w := by
    apply Subtype.ext
    change -PaperVerification.ReducedBarBasis.differential B (z.val+w.val)=
      -PaperVerification.ReducedBarBasis.differential B z.val+
        -PaperVerification.ReducedBarBasis.differential B w.val
    rw [map_add,neg_add]
  map_smul' c z := by
    apply Subtype.ext
    change -PaperVerification.ReducedBarBasis.differential B (c • z.val)=
      c • -PaperVerification.ReducedBarBasis.differential B z.val
    rw [map_smul,smul_neg]

include hunit hε in
theorem internalDifferential_squared (r N : ℕ) :
    (internalDifferential B δ hδ r N).comp (internalDifferential B δ hδ (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -PaperVerification.ReducedBarBasis.differential B
    (-PaperVerification.ReducedBarBasis.differential B z.val)=0
  rw [map_neg,neg_neg,PaperVerification.ReducedBarBasis.differential_squared ε B hunit hε]

def internalComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (piece (K := K) δ r N))
    (fun r ↦ ModuleCat.ofHom (internalDifferential B δ hδ r N))
    (fun r ↦ ModuleCat.hom_ext (internalDifferential_squared ε B hunit hε δ hδ r N))

@[simp] theorem internalComplex_d (r N : ℕ) :
    (internalComplex ε B hunit hε δ hδ N).d (r+1) r=
      ModuleCat.ofHom (internalDifferential B δ hδ r N) := by
  simp [internalComplex]

theorem length_le_totalDegree (hpos : ∀ i,0<δ i) (L : List I) :
    L.length≤totalDegree δ L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      have hi := hpos i
      simp only [List.length_cons,totalDegree_cons]
      omega

theorem piece_eq_bot_of_lt (hpos : ∀ i,0<δ i) (r N : ℕ) (hNr : N<r) :
    piece (K := K) δ r N=⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z=0
  apply Finsupp.ext
  intro L
  by_contra hL
  have h := hz (Finsupp.mem_support_iff.mpr hL)
  have bound := length_le_totalDegree δ hpos L
  change L.length=r ∧ totalDegree δ L=N at h
  omega

theorem internalComplex_top_differential (hpos : ∀ i,0<δ i) (N : ℕ) :
    (internalComplex ε B hunit hε δ hδ N).d (N+1) N=0 := by
  have hbot := piece_eq_bot_of_lt (K := K) δ hpos (N+1) N (by omega)
  haveI : Subsingleton (piece (K := K) δ (N+1) N) := by rw [hbot]; infer_instance
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of K (piece (K := K) δ (N+1) N))).eq_of_src _ _

/-- The finite word index is identified with tuples of exactly the same
length and total actual degree. -/
def indexTupleEquiv (r N : ℕ) :
    Index δ r N ≃ {f : Fin r → I // (∑ i,δ (f i))=N} where
  toFun L := ⟨List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r),by
    have he : List.ofFn (List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r))=L.val :=
      by simpa only [List.Vector.toList_ofFn,List.Vector.toList_mk] using
        congrArg List.Vector.toList (List.Vector.ofFn_get (⟨L.val,L.property.1⟩ : List.Vector I r))
    have hd : totalDegree δ
        (List.ofFn (List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r)))=N := by
      rw [he]
      exact L.property.2
    simpa only [totalDegree,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hd⟩
  invFun f := ⟨(List.Vector.ofFn f.val).val,by
    constructor
    · exact (List.Vector.ofFn f.val).property
    · rw [show (List.Vector.ofFn f.val).val=List.ofFn f.val from
        List.Vector.toList_ofFn f.val]
      simpa only [totalDegree,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
        using f.property⟩
  left_inv L := by
    apply Subtype.ext
    exact congrArg (fun v : List.Vector I r ↦ v.val)
      (List.Vector.ofFn_get (⟨L.val,L.property.1⟩ : List.Vector I r))
  right_inv f := by
    apply Subtype.ext
    funext i
    exact List.Vector.get_ofFn f.val i

def positiveSeries [Fintype I] : ℤ⟦X⟧ := ∑ i,PowerSeries.X^(δ i)

theorem coeff_positiveSeries_pow [Fintype I] (r N : ℕ) :
    PowerSeries.coeff N (positiveSeries δ^r)=(Nat.card (Index δ r N) : ℤ) := by
  rw [positiveSeries,Fintype.sum_pow,map_sum]
  simp only [Finset.prod_pow_eq_pow_sum,PowerSeries.coeff_X_pow]
  rw [show (∑ f : Fin r → I,if N=(∑ i,δ (f i)) then (1 : ℤ) else 0)=
      ∑ f : Fin r → I,if (∑ i,δ (f i))=N then (1 : ℤ) else 0 by
        apply Finset.sum_congr rfl
        intro f hf
        simp only [eq_comm]]
  rw [Finset.sum_boole,Nat.card_congr (indexTupleEquiv δ r N),
    Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem internalComplex_term_rank [Fintype I] (r N : ℕ) :
    (Module.finrank K ((internalComplex ε B hunit hε δ hδ N).X r) : ℤ)=
      PowerSeries.coeff N (positiveSeries δ^r) := by
  rw [coeff_positiveSeries_pow]
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (piece_finrank (K := K) δ r N)

theorem positiveSeries_constantCoeff [Fintype I] (hpos : ∀ i,0<δ i) :
    PowerSeries.constantCoeff (positiveSeries δ)=0 := by
  have hne : ∀ i,δ i≠0 := fun i ↦ Nat.ne_of_gt (hpos i)
  simp [positiveSeries,hne]

end PaperVerification.WeightedBar
end
end
end TAF_LiteralSource_0485

section TAF_LiteralSource_0486
/- Original module: TauCeti.Algebra.Category.ModuleCat.Finrank -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Finrank of zero objects, biproducts and short exact sequences in `ModuleCat`

Vanishing and direct sums of objects of `ModuleCat R` are naturally expressed categorically, as
`CategoryTheory.Limits.IsZero` and biproducts `M ⊞ N`, while the dimension counts that consume them
speak of `Module.finrank`. This file supplies the translations between the two: a zero object has
finrank zero, and finrank is additive on biproducts of finite free modules
(`ModuleCat.finrank_biprod`, the analogue of `FGModuleCat.finrank_biprod`).

Over a ring satisfying the rank-nullity theorem (`HasRankNullity`), such as a division ring or a
commutative domain, finrank is moreover additive on every short exact sequence whose middle term
is finitely generated (`CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`). Unlike
Mathlib's `ModuleCat.free_shortExact_finrank_add`, no freeness is assumed, so this covers
sequences of finitely generated abelian groups with torsion.

The first translation is what bounds the `Module.finrank` support of a bounded complex of vector
spaces by its bounding interval, which is in turn what makes Mathlib's `finsum`-based Euler
characteristic of such a complex an honest finite sum. For an `ℕ`-indexed family vanishing from
some degree on, `ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range` records that finite sum
directly.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] [Nontrivial R]

/-- A zero object in `ModuleCat R` has finrank zero. -/
theorem finrank_eq_zero_of_isZero {X : ModuleCat.{v} R} (hX : IsZero X) :
    Module.finrank R X = 0 := by
  let _ : Subsingleton X := ModuleCat.subsingleton_of_isZero hX
  exact Module.finrank_zero_of_subsingleton

/-- If an `ℕ`-indexed family in `ModuleCat R` vanishes from degree `N` on, the alternating
`finsum` of its finranks is the honest finite sum over the degrees below `N`. -/
theorem finsum_neg_one_pow_finrank_eq_sum_range {M : ℕ → ModuleCat.{v} R} {N : ℕ}
    (hN : ∀ n ≥ N, IsZero (M n)) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Module.finrank R (M n) =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * Module.finrank R (M n) := by
  refine finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hn (by simp [finrank_eq_zero_of_isZero (hN n (not_lt.1 h))])

/-- The finrank of a biproduct of finite free modules is the sum of their finranks. -/
@[simp]
theorem finrank_biprod {R : Type u} [Ring R] [StrongRankCondition R] (M N : ModuleCat.{v} R)
    [Module.Free R M] [Module.Free R N] [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R ↑(M ⊞ N) = Module.finrank R M + Module.finrank R N :=
  (biprodIsoProd M N).toLinearEquiv.finrank_eq.trans Module.finrank_prod

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- Over a ring with the rank-nullity property, finrank is additive on a short exact sequence of
modules whose middle term is finitely generated. -/
theorem moduleCat_finrank_eq_add {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Module.Finite R S.X₂] :
    Module.finrank R S.X₂ = Module.finrank R S.X₁ + Module.finrank R S.X₃ := by
  -- Rank-nullity for the kernel of `g`, which is the image of the injective map `f`.
  have h := (LinearMap.ker S.g.hom).finrank_quotient_add_finrank
  rw [(S.g.hom.quotKerEquivOfSurjective hS.moduleCat_surjective_g).finrank_eq,
    ← hS.exact.moduleCat_range_eq_ker,
    (LinearEquiv.ofInjective _ hS.moduleCat_injective_f).finrank_eq.symm] at h
  lia

end CategoryTheory.ShortComplex.ShortExact
end
end TAF_LiteralSource_0486

section TAF_LiteralSource_0487
/- Original module: TauCeti.Algebra.Homology.ShortComplex.ModuleCat -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homology of short complexes of modules

For a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules, its homology is the kernel of the second map
modulo the range of the first.  The projection of Mathlib's explicit left homology data
`S.moduleCatLeftHomologyData` from the kernel onto the homology is surjective, and identifies two
elements exactly when their difference is in the range of the first map
(`CategoryTheory.ShortComplex.moduleCatLeftHomologyData_π_hom_eq_iff`).  This file also records
two finiteness consequences of that description:

* over a ring for which the middle module is noetherian, the homology is finitely generated;
* over a division ring, when the middle term is finite-dimensional, the dimension of the homology
  plus the dimension of the range of the first map is the dimension of the kernel of the second,
  so in particular the homology has dimension at most that of the middle term.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.ShortComplex

/-- The homology of a short complex of modules with noetherian middle term is finitely generated. -/
theorem finite_homology {k : Type u} [Ring k] (S : ShortComplex (ModuleCat.{v} k))
    [IsNoetherian k S.X₂] : Module.Finite k S.homology :=
  -- The homology object of `S.moduleCatLeftHomologyData` is this quotient by construction.
  have : Module.Finite k S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  .equiv S.moduleCatHomologyIso.toLinearEquiv.symm

variable {k : Type u} [DivisionRing k]

/-- The homology of a short complex `X₁ ⟶ X₂ ⟶ X₃` of vector spaces with `X₂` finite-dimensional
has dimension `dim ker g - dim im f`. -/
theorem finrank_homology_add_finrank_range_f (S : ShortComplex (ModuleCat.{v} k))
    [Module.Finite k S.X₂] :
    finrank k S.homology + finrank k (LinearMap.range S.f.hom) =
      finrank k (LinearMap.ker S.g.hom) := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq, moduleCatLeftHomologyData_H,
    ← Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)]
  congr 1
  rw [← Submodule.finrank_map_subtype_eq, ← LinearMap.range_comp]
  -- `S.moduleCatToCycles` is the corestriction of `S.f` to `ker S.g`, so composing it with the
  -- inclusion of `ker S.g` gives `S.f` back by definition; rewriting with
  -- `LinearMap.subtype_comp_codRestrict` fails because Mathlib's corestriction proof is only
  -- well-typed up to unfolding the concrete-category coercions.
  rfl

/-- The homology of a short complex of vector spaces with finite-dimensional middle term has
dimension at most that of the middle term. -/
theorem finrank_homology_le_finrank_X₂ (S : ShortComplex (ModuleCat.{v} k)) [Module.Finite k S.X₂] :
    finrank k S.homology ≤ finrank k S.X₂ := by
  have := S.finrank_homology_add_finrank_range_f
  have := (LinearMap.ker S.g.hom).finrank_le
  omega

section LeftHomologyData

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

/-- Two cycles of a short complex of modules have the same class in the explicit left homology
exactly when their difference is a boundary. -/
lemma moduleCatLeftHomologyData_π_hom_eq_iff (c c' : LinearMap.ker S.g.hom) :
    S.moduleCatLeftHomologyData.π.hom c = S.moduleCatLeftHomologyData.π.hom c' ↔
      ∃ y, S.f.hom y = (c : S.X₂) - c' :=
  (Submodule.Quotient.eq _).trans
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩

/-- Every class of the explicit left homology of a short complex of modules is the class of a
cycle. -/
lemma moduleCatLeftHomologyData_π_hom_surjective :
    Function.Surjective S.moduleCatLeftHomologyData.π.hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

end LeftHomologyData

end CategoryTheory.ShortComplex
end
end TAF_LiteralSource_0487

section TAF_LiteralSource_0488
/- Original module: TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Euler--Poincaré for chain complexes of vector spaces indexed by `ℕ`

A chain complex `K` indexed by `ℕ`, with differentials `Kₙ₊₁ ⟶ Kₙ`, is the shape of singular and
cellular chains.  When its terms are finite-dimensional vector spaces, rank--nullity for each
differential, applied to the boundaries `Bₙ = im (Kₙ₊₁ ⟶ Kₙ)`, gives

```text
dim Kₙ = dim Hₙ(K) + dim Bₙ + dim Bₙ₋₁,
```

(`ChainComplex.finrank_X_zero`, `ChainComplex.finrank_X_succ`), and the alternating sum of these
identities telescopes: up to degree `n` the alternating sums of the dimensions of the terms and
of the homology differ by `(-1)ⁿ dim Bₙ`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology_add`).  If the differential
`Kₙ₊₁ ⟶ Kₙ` vanishes, the last boundary term `dim Bₙ` vanishes, so the alternating sums of the
dimensions of the terms and of the homology agree up to degree `n`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology`).  The terms in degrees above
`n + 1` play no role.

For a complex of finite-dimensional vector spaces that vanishes in all large degrees this is the
equality of Mathlib's term and homology Euler characteristics
(`ChainComplex.eulerChar_eq_homologyEulerChar`).  Both sides are `finsum`s, and the vanishing
hypothesis is what makes them honest finite sums.  The same equality for bounded cochain
complexes indexed by `ℤ` with terms in `FGModuleCat k` is
`HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar`; here the complex stays in
`ModuleCat k` with the homological indexing by `ℕ`, and finite-dimensionality of its terms is a
hypothesis.

The telescoping rests on the description of the homology of one short complex `X₁ ⟶ X₂ ⟶ X₃` of
modules as the kernel of the second map modulo the range of the first: over a division ring its
dimension is `dim ker g - dim im f`
(`CategoryTheory.ShortComplex.finrank_homology_add_finrank_range_f`).  The same description shows
that over a noetherian ring the homology is finitely generated when `X₂` is
(`CategoryTheory.ShortComplex.finite_homology`).

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace ChainComplex

variable {k : Type u} [DivisionRing k] (K : ChainComplex (ModuleCat.{v} k) ℕ)

/-- In degree `0`, every element is a cycle, so `dim K₀ = dim H₀(K) + dim im (K₁ ⟶ K₀)`. -/
theorem finrank_X_zero [Module.Finite k (K.X 0)] :
    finrank k (K.X 0) = finrank k (K.homology 0) + finrank k (LinearMap.range (K.d 1 0).hom) := by
  have : Module.Finite k (K.sc' 1 0 0).X₂ := ‹Module.Finite k (K.X 0)›
  -- The maps of `K.sc' i j k` are `K.d i j` and `K.d j k` by construction.
  have h : finrank k (K.sc' 1 0 0).homology + finrank k (LinearMap.range (K.d 1 0).hom) =
      finrank k (LinearMap.ker (K.d 0 0).hom) :=
    (K.sc' 1 0 0).finrank_homology_add_finrank_range_f
  -- `K.homology j` is by definition the homology of `K.sc j`.
  have e : K.homology 0 ≅ (K.sc' 1 0 0).homology :=
    ShortComplex.homologyMapIso (K.isoSc' 1 0 0 (by simp) (by simp))
  rw [K.shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.ker_zero, finrank_top,
    ← e.toLinearEquiv.finrank_eq] at h
  exact h.symm

/-- In degree `n + 1`, rank--nullity for `Kₙ₊₁ ⟶ Kₙ` gives
`dim Kₙ₊₁ = dim Hₙ₊₁(K) + dim im (Kₙ₊₂ ⟶ Kₙ₊₁) + dim im (Kₙ₊₁ ⟶ Kₙ)`. -/
theorem finrank_X_succ (n : ℕ) [Module.Finite k (K.X (n + 1))] :
    finrank k (K.X (n + 1)) = finrank k (K.homology (n + 1)) +
      finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) +
        finrank k (LinearMap.range (K.d (n + 1) n).hom) := by
  have : Module.Finite k (K.sc' (n + 2) (n + 1) n).X₂ := ‹Module.Finite k (K.X (n + 1))›
  -- The maps of `K.sc' i j k` are `K.d i j` and `K.d j k` by construction.
  have h : finrank k (K.sc' (n + 2) (n + 1) n).homology +
      finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) =
        finrank k (LinearMap.ker (K.d (n + 1) n).hom) :=
    (K.sc' (n + 2) (n + 1) n).finrank_homology_add_finrank_range_f
  -- `K.homology j` is by definition the homology of `K.sc j`.
  have e : K.homology (n + 1) ≅ (K.sc' (n + 2) (n + 1) n).homology :=
    ShortComplex.homologyMapIso (K.isoSc' (n + 2) (n + 1) n (by simp) (by simp))
  rw [← e.toLinearEquiv.finrank_eq] at h
  rw [← LinearMap.finrank_range_add_finrank_ker (K.d (n + 1) n).hom, ← h]
  ring

/-- If the terms of `K` through degree `n` are finite-dimensional, the alternating sums up to
degree `n` of the dimensions of the terms and of the homology of `K` differ by the dimension of
the boundaries `im (Kₙ₊₁ ⟶ Kₙ)` in degree `n`, with sign `(-1)ⁿ`. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology_add (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.homology i) +
        (-1 : ℤ) ^ n * finrank k (LinearMap.range (K.d (n + 1) n).hom) := by
  induction n with
  | zero =>
    let _ := hfinite 0 le_rfl
    simp [K.finrank_X_zero]
  | succ n ih =>
    let _ := hfinite (n + 1) le_rfl
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hfinite i (hi.trans n.le_succ)),
      Finset.sum_range_succ _ (n + 1), K.finrank_X_succ n]
    push_cast
    ring

/-- **Euler--Poincaré for a chain complex of vector spaces indexed by `ℕ`.**  If the terms of
`K` through degree `n` are finite-dimensional and the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then
the alternating sums up to degree `n` of the dimensions of the terms and of the homology of `K`
agree. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) (hn : K.d (n + 1) n = 0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.homology i) := by
  rw [K.sum_range_finrank_X_eq_sum_range_finrank_homology_add n hfinite, hn, ModuleCat.hom_zero,
    LinearMap.range_zero, finrank_bot]
  simp

/-- **Euler--Poincaré for a bounded chain complex of vector spaces.**  For a chain complex of
finite-dimensional vector spaces indexed by `ℕ` whose terms vanish in all large degrees, Mathlib's
Euler characteristic of the terms equals that of the homology. -/
theorem eulerChar_eq_homologyEulerChar [∀ n, Module.Finite k (K.X n)]
    (hK : ∀ᶠ n in Filter.atTop, IsZero (K.X n)) :
    K.eulerChar = K.homologyEulerChar := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hK
  have hX : ∀ i ∉ Finset.range (n + 1), IsZero (K.X i) := fun i hi ↦
    hn i (by simp at hi; omega)
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset K (Finset.range (n + 1))
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero (hX i hi)),
    HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset K
      (Finset.range (n + 1))
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero
          (((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _ (hX i hi))).isZero_homology))]
  simpa using K.sum_range_finrank_X_eq_sum_range_finrank_homology
    (fun _ _ ↦ inferInstance) ((hX (n + 1) (by simp)).eq_of_src _ 0)

end ChainComplex
end
end TAF_LiteralSource_0488

section TAF_LiteralSource_0489
/- Original module: PaperVerification.WeightedBarEuler -/


/-!
# The actual bounded bar Euler characteristic and the Koszul series identity

For each original internal degree `N`, use a genuine chain complex of
vector spaces. Its terms have the coefficients of the powers of the
positive-degree series, its outgoing boundary above length `N` vanishes,
and its homology is concentrated at length `N`. Euler--Poincare then gives
an exact inverse identity of formal power series.

The hypotheses concern actual terms, differentials and homology objects.
They are intermediate inputs to be verified for a bar construction; this
file does not assume or assert that the paper's algebra is Koszul.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators PowerSeries
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.WeightedBarEuler

section FormalSeries

variable {R : Type*} [CommRing R]

/-- Positive series have no coefficient in a degree below their power. -/
theorem coeff_power_eq_zero_of_lt (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) {N r : ℕ} (hNr : N < r) :
    PowerSeries.coeff N (P^r)=0 := by
  induction r generalizing N with
  | zero => omega
  | succ r ih =>
      rw [pow_succ,PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro a ha
      have he := Finset.mem_antidiagonal.mp ha
      by_cases hz : a.2=0
      · rw [hz,hP,mul_zero]
      · rw [ih (by omega),zero_mul]

/-- The coefficientwise finite alternating sum of positive-series powers. -/
def eulerSeries (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun N =>
    ∑ r∈Finset.range (N+1),(-1 : R)^r*PowerSeries.coeff N (P^r))

/-- The finite geometric expression used to check any prescribed coefficient. -/
def finiteGeometric (P : PowerSeries R) (N : ℕ) : PowerSeries R :=
  ∑ r∈Finset.range (N+1),PowerSeries.C ((-1 : R)^r)*P^r

theorem coeff_finiteGeometric (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) {i N : ℕ} (hi : i ≤ N) :
    PowerSeries.coeff i (finiteGeometric P N)=PowerSeries.coeff i (eulerSeries P) := by
  simp only [finiteGeometric,eulerSeries,PowerSeries.coeff_mk,map_sum,
    PowerSeries.coeff_C_mul]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))
  intro r hr hri
  have hir : i < r := by
    have hri' : ¬r < i+1 := fun hr' => hri (Finset.mem_range.mpr hr')
    omega
  rw [coeff_power_eq_zero_of_lt P hP hir,mul_zero]

theorem one_add_mul_finiteGeometric (P : PowerSeries R) (N : ℕ) :
    (1+P)*finiteGeometric P N=1-(-P)^(N+1) := by
  have he : finiteGeometric P N=∑ r∈Finset.range (N+1),(-P)^r := by
    unfold finiteGeometric
    apply Finset.sum_congr rfl
    intro r hr
    simp only [map_pow,map_neg,map_one]
    exact (neg_pow P r).symm
  rw [he]
  simpa only [sub_neg_eq_add] using mul_neg_geom_sum (-P) (N+1)

/-- The coefficientwise finite Euler sum is the genuine inverse of `1+P`. -/
theorem one_add_mul_eulerSeries (P : PowerSeries R)
    (hP : PowerSeries.coeff 0 P=0) : (1+P)*eulerSeries P=1 := by
  apply PowerSeries.ext
  intro N
  calc
    PowerSeries.coeff N ((1+P)*eulerSeries P)=
        PowerSeries.coeff N ((1+P)*finiteGeometric P N) := by
      rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have he := Finset.mem_antidiagonal.mp ha
      rw [coeff_finiteGeometric P hP (by omega : a.2 ≤ N)]
    _=PowerSeries.coeff N (1 : PowerSeries R) := by
      rw [one_add_mul_finiteGeometric,map_sub,
        coeff_power_eq_zero_of_lt (-P)
          (by rw [map_neg,hP,neg_zero]) (Nat.lt_succ_self N),sub_zero]

end FormalSeries

section ActualChainComplexes

universe u v
variable {K : Type u} [Field K]

/-- The signed series of the actual diagonal internal-degree homology. -/
def diagonalHomologySeries (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N => (-1 : ℤ)^N*(Module.finrank K ((C N).homology N) : ℤ))

/-- Finite Euler--Poincare identifies the two series, with every term and
homology object retaining its actual categorical meaning. -/
theorem eulerSeries_eq_diagonalHomologySeries
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hboundary : ∀ N,(C N).d (N+1) N=0)
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    eulerSeries P=diagonalHomologySeries C := by
  apply PowerSeries.ext
  intro N
  simp only [eulerSeries,diagonalHomologySeries,PowerSeries.coeff_mk]
  calc
    (∑ r∈Finset.range (N+1),(-1 : ℤ)^r*PowerSeries.coeff N (P^r))=
        ∑ r∈Finset.range (N+1),(-1 : ℤ)^r*(Module.finrank K ((C N).X r) : ℤ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hterm N r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
    _=∑ r∈Finset.range (N+1),(-1 : ℤ)^r*(Module.finrank K ((C N).homology r) : ℤ) :=
      (C N).sum_range_finrank_X_eq_sum_range_finrank_homology
        (hfinite N) (hboundary N)
    _=(-1 : ℤ)^N*(Module.finrank K ((C N).homology N) : ℤ) := by
      apply Finset.sum_eq_single N
      · intro r hr hne
        rw [ModuleCat.finrank_eq_zero_of_isZero
          (hhomology N r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hne),
          Nat.cast_zero,mul_zero]
      · intro hN
        exact (hN (Finset.mem_range.mpr (Nat.lt_succ_self N))).elim

/-- The same identity needs only the actual boundary above length `N` to
vanish; this is the direct interface for a separately constructed bar complex. -/
theorem one_add_mul_diagonalHomologySeries_of_boundary_zero
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hP : PowerSeries.coeff 0 P=0)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hboundary : ∀ N,(C N).d (N+1) N=0)
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    (1+P)*diagonalHomologySeries C=1 := by
  rw [←eulerSeries_eq_diagonalHomologySeries C P hfinite hboundary hterm hhomology]
  exact one_add_mul_eulerSeries P hP

/-- The Koszul series identity from a bounded actual internal-degree bar
complex. No identification with a quadratic dual is assumed here. -/
theorem one_add_mul_diagonalHomologySeries
    (C : ℕ → ChainComplex (ModuleCat.{v} K) ℕ) (P : PowerSeries ℤ)
    (hP : PowerSeries.coeff 0 P=0)
    (hfinite : ∀ N r, r ≤ N → Module.Finite K ((C N).X r))
    (hbounded : ∀ N,IsZero ((C N).X (N+1)))
    (hterm : ∀ N r, r ≤ N →
      (Module.finrank K ((C N).X r) : ℤ)=PowerSeries.coeff N (P^r))
    (hhomology : ∀ N r, r ≤ N → r≠N → IsZero ((C N).homology r)) :
    (1+P)*diagonalHomologySeries C=1 := by
  rw [←eulerSeries_eq_diagonalHomologySeries C P hfinite
    (fun N => (hbounded N).eq_of_src _ 0) hterm hhomology]
  exact one_add_mul_eulerSeries P hP

end ActualChainComplexes
end PaperVerification.WeightedBarEuler
end
end
end TAF_LiteralSource_0489

section TAF_LiteralSource_0490
/- Original module: PaperVerification.WeightedBarTor -/


/-!
# The original internal grading inside genuine augmentation Tor

Coefficient projections preserve the original homogeneous degree and split
actual subcomplex inclusions. The induced subspaces of ordinary Tor are
isomorphic to their actual internal-degree homology, and exhaust Tor.
No acyclicity or Koszulness premise is incorporated in their definitions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.WeightedBar

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def degreeProjection (N : ℕ) : (List C →₀ K) →ₗ[K] (List C →₀ K) where
  toFun z := z.filter (fun L ↦ totalDegree δ L=N)
  map_add' z w := Finsupp.filter_add
  map_smul' a z := Finsupp.filter_smul

@[simp] theorem degreeProjection_apply (N : ℕ) (z : List C →₀ K) (L : List C) :
    degreeProjection δ N z L=if totalDegree δ L=N then z L else 0 := rfl

theorem degreeProjection_single (N : ℕ) (L : List C) (c : K) :
    degreeProjection δ N (Finsupp.single L c)=
      if totalDegree δ L=N then Finsupp.single L c else 0 := by
  change (Finsupp.single L c).filter (fun T => totalDegree δ T=N)=
    if totalDegree δ L=N then Finsupp.single L c else 0
  by_cases h : totalDegree δ L=N
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos (fun T => totalDegree δ T=N) h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg (fun T => totalDegree δ T=N) h

theorem degreeProjection_homogeneous (N M : ℕ) (z : List C →₀ K)
    (hz : z∈degreePiece δ M) :
    degreeProjection δ N z=if M=N then z else 0 := by
  by_cases h : M=N
  · subst M
    rw [if_pos rfl]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro L hL
    exact hz (Finsupp.mem_support_iff.mpr hL)
  · rw [if_neg h]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro L hL
    apply (Finsupp.mem_supported' K z).mp hz
    intro hM
    exact h (hM.symm.trans hL)

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem differential_degreeProjection (N : ℕ) (z : List C →₀ K) :
    differential B (degreeProjection δ N z)=degreeProjection δ N (differential B z) := by
  have he : (differential B).comp (degreeProjection δ N)=
      (degreeProjection δ N).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,degreeProjection_single,differential_single,map_smul]
    rw [degreeProjection_homogeneous δ N (totalDegree δ L) _
      (differentialBasis_mem_degreePiece B δ hδ L)]
    split_ifs <;> simp only [differential_single,map_zero,smul_zero]
  exact LinearMap.congr_fun he z

/-- Finite completeness of the internal-degree projections on every
actual tensor. No finite-degree bound on the entire bar term is assumed. -/
theorem sum_degreeProjection (z : List C →₀ K) :
    (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z := by
  apply Finsupp.ext
  intro L
  change (Finsupp.applyAddHom L) (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z L
  rw [map_sum]
  change (∑ N∈z.support.image (totalDegree δ),if totalDegree δ L=N then z L else 0)=z L
  rw [Finset.sum_eq_single (totalDegree δ L)]
  · rw [if_pos rfl]
  · intro N hN hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    rw [if_pos rfl]
    by_contra hL
    exact hnot (Finset.mem_image.mpr ⟨L,Finsupp.mem_support_iff.mpr hL,rfl⟩)

end PaperVerification.WeightedBar

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PaperVerification.NoncommutativeBar PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "bar" => reducedComplex ε B hunit hε
local notation "internal" => internalComplex ε B hunit hε δ hδ

def internalInclusion (r N : ℕ) : piece (K := K) δ r N →ₗ[K] lengthPiece I K r :=
  Submodule.inclusion (by rw [piece_eq_inf]; exact inf_le_left)

theorem internalInclusion_differential (r N : ℕ) :
    (internalInclusion (K := K) δ r N).comp (internalDifferential B δ hδ r N)=
      (negativeReducedDegreeDifferential B r).comp (internalInclusion δ (r+1) N) := by
  apply LinearMap.ext
  intro z
  rfl

def inclusionChain (N : ℕ) : internal N ⟶ bar where
  f r := ModuleCat.ofHom (internalInclusion (K := K) δ r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [internalComplex_d,reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (internalInclusion_differential B δ hδ j N).symm

theorem projection_mem_piece (r N : ℕ) (z : List I →₀ K)
    (hz : z∈lengthPiece I K r) : degreeProjection δ N z∈piece (K := K) δ r N := by
  intro L hL
  have hn := Finsupp.mem_support_iff.mp hL
  rw [degreeProjection_apply] at hn
  split_ifs at hn with hN
  · exact ⟨hz (Finsupp.mem_support_iff.mpr hn),hN⟩
  · exact False.elim (hn rfl)

def internalProjection (r N : ℕ) : lengthPiece I K r →ₗ[K] piece (K := K) δ r N :=
  LinearMap.codRestrict _ ((degreeProjection δ N).comp (lengthPiece I K r).subtype)
    (fun z ↦ projection_mem_piece δ r N z.val z.property)

@[simp] theorem internalProjection_val (r N : ℕ) (z : lengthPiece I K r) :
    (internalProjection δ r N z).val=degreeProjection δ N z.val := rfl

theorem internalProjection_inclusion (r N : ℕ) (z : piece (K := K) δ r N) :
    internalProjection δ r N (internalInclusion δ r N z)=z := by
  apply Subtype.ext
  have hz : z.val∈lengthPiece I K r ⊓ degreePiece δ N := by
    rw [←piece_eq_inf]
    exact z.property
  exact (degreeProjection_homogeneous δ N N z.val hz.2).trans (if_pos rfl)

include hδ in
theorem internalProjection_differential (r N : ℕ) :
    (internalProjection δ r N).comp (negativeReducedDegreeDifferential B r)=
      (internalDifferential B δ hδ r N).comp (internalProjection δ (r+1) N) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change degreeProjection δ N (-PaperVerification.ReducedBarBasis.differential B z.val)=
    -PaperVerification.ReducedBarBasis.differential B (degreeProjection δ N z.val)
  rw [map_neg,differential_degreeProjection B δ hδ]

def projectionChain (N : ℕ) : bar ⟶ internal N where
  f r := ModuleCat.ofHom (internalProjection (K := K) δ r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [internalComplex_d,reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (internalProjection_differential B δ hδ j N).symm

theorem chain_retraction (N : ℕ) :
    inclusionChain ε B hunit hε δ hδ N ≫ projectionChain ε B hunit hε δ hδ N=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact internalProjection_inclusion δ r N z

theorem internalHomology_injective (r N : ℕ) :
    Function.Injective (homologyMap (inclusionChain ε B hunit hε δ hδ N) r) := by
  have he := congrArg (fun f ↦ homologyMap f r) (chain_retraction ε B hunit hε δ hδ N)
  rw [homologyMap_comp,homologyMap_id] at he
  apply Function.LeftInverse.injective
    (g := homologyMap (projectionChain ε B hunit hε δ hδ N) r)
  intro z
  exact congrArg (fun f ↦ f z) he

def internalTorMap (r N : ℕ) :
    (internal N).homology r ⟶ AugmentationCoinvariants.augmentationTor ε r :=
  homologyMap (inclusionChain ε B hunit hε δ hδ N) r ≫
    (ordinaryTorReducedBarIso ε B hunit hε r).inv

/-- The image of the original degree-N complex inside ordinary Tor. -/
def torPiece (r N : ℕ) : Submodule K (AugmentationCoinvariants.augmentationTor ε r) :=
  LinearMap.range (internalTorMap ε B hunit hε δ hδ r N).hom

theorem internalTorMap_injective (r N : ℕ) :
    Function.Injective (internalTorMap ε B hunit hε δ hδ r N) :=
  (ordinaryTorReducedBarIso ε B hunit hε r).toLinearEquiv.symm.injective.comp
    (internalHomology_injective ε B hunit hε δ hδ r N)

/-- This isomorphism proves that the grading images cannot discard any
nonzero internal homology class. -/
def internalTorEquiv (r N : ℕ) :
    (internal N).homology r ≃ₗ[K] torPiece ε B hunit hε δ hδ r N :=
  LinearEquiv.ofInjective (internalTorMap ε B hunit hε δ hδ r N).hom
    (internalTorMap_injective ε B hunit hε δ hδ r N)

theorem torPiece_eq_bot_iff (r N : ℕ) :
    torPiece ε B hunit hε δ hδ r N=⊥ ↔ IsZero ((internal N).homology r) := by
  constructor
  · intro h
    haveI : Subsingleton (torPiece ε B hunit hε δ hδ r N) := by rw [h]; infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y ↦ (internalTorEquiv ε B hunit hε δ hδ r N).injective
      (Subsingleton.elim _ _)⟩
  · intro h
    have hm : internalTorMap ε B hunit hε δ hδ r N=0 := h.eq_of_src _ _
    rw [torPiece,hm,ModuleCat.hom_zero,LinearMap.range_zero]

def degreeEndomorphism (N : ℕ) : bar ⟶ bar :=
  projectionChain ε B hunit hε δ hδ N ≫ inclusionChain ε B hunit hε δ hδ N

theorem degreeCycles_value (r N : ℕ) (c : (bar).cycles r) :
    (((bar).iCycles r) (cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)).val=
      degreeProjection δ N (((bar).iCycles r) c).val := by
  have he := congrArg (fun f ↦ f c) (cyclesMap_i (degreeEndomorphism ε B hunit hε δ hδ N) r)
  exact congrArg Subtype.val he

theorem sum_degreeCycles (r : ℕ) (c : (bar).cycles r) :
    (∑ N∈(((bar).iCycles r) c).val.support.image (totalDegree δ),
      cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)=c := by
  apply (ModuleCat.mono_iff_injective ((bar).iCycles r)).mp inferInstance
  rw [map_sum]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp_rw [degreeCycles_value]
  exact sum_degreeProjection δ (((bar).iCycles r) c).val

/-- Every ordinary Tor class is a finite sum of classes in the original
internal degrees. The actual grading images exhaust the whole group. -/
theorem torPieces_iSup (r : ℕ) : (⨆ N,torPiece ε B hunit hε δ hδ r N)=⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective ((bar).homologyπ r)).mp inferInstance
    ((ordinaryTorReducedBarIso ε B hunit hε r).hom x)
  let S := (((bar).iCycles r) c).val.support.image (totalDegree δ)
  have hsum :
      (∑ N∈S,(ordinaryTorReducedBarIso ε B hunit hε r).inv
        (((bar).homologyπ r) (cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)))=x := by
    calc
      _ = (ordinaryTorReducedBarIso ε B hunit hε r).inv (((bar).homologyπ r)
          (∑ N∈S,cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)) := by
        rw [map_sum,map_sum]
      _ = (ordinaryTorReducedBarIso ε B hunit hε r).inv (((bar).homologyπ r) c) := by
        rw [sum_degreeCycles]
      _ = x := by
        rw [hc]
        exact congrArg (fun f ↦ f x) (ordinaryTorReducedBarIso ε B hunit hε r).hom_inv_id
  rw [←hsum]
  apply Submodule.sum_mem
  intro N hN
  apply (le_iSup (fun N ↦ torPiece ε B hunit hε δ hδ r N) N)
  refine ⟨homologyMap (projectionChain ε B hunit hε δ hδ N) r (((bar).homologyπ r) c),?_⟩
  change (ordinaryTorReducedBarIso ε B hunit hε r).inv
    (homologyMap (inclusionChain ε B hunit hε δ hδ N) r
      (homologyMap (projectionChain ε B hunit hε δ hδ N) r (((bar).homologyπ r) c)))=_
  apply congrArg (ordinaryTorReducedBarIso ε B hunit hε r).inv
  have he := congrArg (fun f ↦ f c)
    (homologyπ_naturality (degreeEndomorphism ε B hunit hε δ hδ N) r)
  simpa only [degreeEndomorphism,homologyMap_comp,ModuleCat.comp_apply] using he

/-- Ordinary Tor concentration with its independently specified original
generator degrees. This definition does not posit any dimension formula. -/
def HasDiagonalTor : Prop :=
  ∀ r N,r≠N → torPiece ε B hunit hε δ hδ r N=⊥

theorem hasDiagonalTor_iff : HasDiagonalTor ε B hunit hε δ hδ ↔
    ∀ r N,r≠N → IsZero ((internal N).homology r) := by
  simp only [HasDiagonalTor,torPiece_eq_bot_iff]

/-- The necessary Hilbert identity follows from the real ordinary-Tor
concentration property and finite Euler--Poincare in each internal degree. -/
theorem one_add_mul_signed_diagonalTor [Fintype I] (hpos : ∀ i,0<δ i)
    (hKoszul : HasDiagonalTor ε B hunit hε δ hδ) :
    (1+positiveSeries δ)*WeightedBarEuler.diagonalHomologySeries internal=1 := by
  apply WeightedBarEuler.one_add_mul_diagonalHomologySeries_of_boundary_zero
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact positiveSeries_constantCoeff δ hpos
  · intro N r hr
    change Module.Finite K (piece (K := K) δ r N)
    infer_instance
  · exact internalComplex_top_differential ε B hunit hε δ hδ hpos
  · intro N r hr
    exact internalComplex_term_rank ε B hunit hε δ hδ r N
  · intro N r hr hne
    exact (hasDiagonalTor_iff ε B hunit hε δ hδ).mp hKoszul r N hne

end PaperVerification.WeightedBar
end
end
end TAF_LiteralSource_0490

section TAF_LiteralSource_0491
/- Original module: PaperVerification.QuadraticWordPBW -/


/-!
# Koszul concentration from actual signed quadratic normal words

The basis is a basis of the original augmented algebra. Normal products
concatenate with coefficient one; all other nonzero products have the
same multiset of generators. Sorting strictly lowers the finite number
of forbidden ordered pairs. The actual bar differential therefore has
the proved monomial cut differential as its leading map. Filtered
exactness proves off-diagonal homology vanishing in the actual internal
degree complexes. No PBW-to-Koszul theorem is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.QuadraticWordPBW

open PaperVerification.QuadraticWordBar
open PaperVerification.AlternatingForms.BarCoefficientFormula
open PaperVerification.AlternatingForms.PBWWords
open PaperVerification.AlternatingForms.FilteredComparison
open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis
open PaperVerification.Fermion.BasisFiltered
open CategoryTheory CategoryTheory.Limits

universe u
variable {K A C J : Type u} [Field K] [Ring A] [Algebra K A]
  [Fintype J] {R : J → J → Prop} [IsTrans J R]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option C) K A)
  (hunit : B none=1) (hε : ∀ c,ε (B (some c))=0)
  (e : C ≃ PositiveWord R)
  (hnormal : ∀ a b (h : ((e a).val++(e b).val).IsChain R),
    productCoefficients B a b=Finsupp.single (concatenateNormal e a b h) 1)
  (hperm : ∀ a b c,productCoefficients B a b c≠0 →
    (e c).val.Perm ((e a).val++(e b).val))

def wordDegree (c : C) : ℕ := (e c).val.length

include hperm in
theorem product_degree (a b c : C) (h : productCoefficients B a b c≠0) :
    wordDegree e c=wordDegree e a+wordDegree e b := by
  simpa only [wordDegree,List.length_append] using (hperm a b c h).length_eq

theorem flatten_length (L : List C) :
    (flattenBarWord e L).length=WeightedBar.totalDegree (wordDegree e) L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change ((e a).val++flattenBarWord e L).length=
      wordDegree e a+WeightedBar.totalDegree (wordDegree e) L
    rw [List.length_append,ih]
    rfl

theorem internalPiece_eq (r N : ℕ) :
    internalDegreePiece (K := K) e r N=WeightedBar.piece (K := K) (wordDegree e) r N := by
  unfold internalDegreePiece WeightedBar.piece
  congr 1
  ext L
  simp only [Set.mem_setOf_eq,flatten_length]

def strictWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | (flattenBarWord e L).Perm W ∧
    badPairs R (flattenBarWord e L)<badPairs R W}

def sameWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | flattenBarWord e L=W}

theorem strict_prefix (W : List J) (a : C) (z : List C →₀ K)
    (hz : z∈strictWordPiece (K := K) e W) :
    prepend a z∈strictWordPiece (K := K) e ((e a).val++W) := by
  rw [strictWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    constructor
    · exact hL.1.append_left (e a).val
    · change badPairs R ((e a).val++flattenBarWord e L)<badPairs R ((e a).val++W)
      have hc := badPairs_context_balance R (e a).val [] (flattenBarWord e L) W hL.1
      simp only [List.append_nil] at hc
      have hlt : badPairs R (flattenBarWord e L)<badPairs R W := hL.2
      omega
  | zero => simpa only [map_zero] using (strictWordPiece (K := K) e ((e a).val++W)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (strictWordPiece (K := K) e ((e a).val++W)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (strictWordPiece (K := K) e ((e a).val++W)).smul_mem c ih

theorem same_prefix (W : List J) (a : C) (z : List C →₀ K)
    (hz : z∈sameWordPiece (K := K) e W) :
    prepend a z∈sameWordPiece (K := K) e ((e a).val++W) := by
  rw [sameWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change (e a).val++flattenBarWord e L=(e a).val++W
    rw [hL]
  | zero => simpa only [map_zero] using (sameWordPiece (K := K) e ((e a).val++W)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (sameWordPiece (K := K) e ((e a).val++W)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (sameWordPiece (K := K) e ((e a).val++W)).smul_mem c ih

theorem normal_adjacent_same (a b : C) (L : List C) :
    appendTail L (normalProduct (K := K) e a b)∈sameWordPiece e (flattenBarWord e (a::b::L)) := by
  unfold normalProduct
  split_ifs with h
  · rw [appendTail_single]
    apply Finsupp.single_mem_supported K 1
    change (e (concatenateNormal e a b h)).val++flattenBarWord e L=
      (e a).val++((e b).val++flattenBarWord e L)
    rw [concatenateNormal_word,List.append_assoc]
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem normal_differential_same (L : List C) :
    basisDifferential (normalProduct (K := K) e) L∈sameWordPiece e (flattenBarWord e L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [basisDifferential,adjacent,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      change appendTail L (normalProduct e a b)-
        prepend a (basisDifferential (normalProduct e) (b::L))∈_
      exact Submodule.sub_mem _ (normal_adjacent_same e a b L) (same_prefix e _ a _ ih)

include hnormal hperm in
theorem adjacent_difference_strict (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)-appendTail L (normalProduct e a b)∈
      strictWordPiece e (flattenBarWord e (a::b::L)) := by
  by_cases h : ((e a).val++(e b).val).IsChain R
  · rw [hnormal a b h,normalProduct,dif_pos h,sub_self]
    exact Submodule.zero_mem _
  · rw [normalProduct,dif_neg h,map_zero,sub_zero,
      appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Finsupp.single_mem_supported K 1
    have hp := hperm a b c (Finsupp.mem_support_iff.mp hc)
    constructor
    · simpa only [flattenBarWord,List.map_cons,List.flatten_cons,List.append_assoc] using
        hp.append_right (flattenBarWord e L)
    · have hbad : ¬((e a).val++(e b).val).Pairwise R :=
        fun hh => h (List.isChain_iff_pairwise.mpr hh)
      have hgood : (e c).val.Pairwise R := List.isChain_iff_pairwise.mp (e c).property.2
      have hb := badPairs_context_decrease R [] (flattenBarWord e L)
        ((e a).val++(e b).val) (e c).val hp.symm hbad hgood
      simpa only [QuadraticWordBar.flattenBarWord,List.map_cons,List.flatten_cons,
        List.nil_append,List.append_assoc] using hb

include hnormal hperm in
theorem differential_difference_strict (L : List C) :
    differentialBasis B L-basisDifferential (normalProduct e) L∈
      strictWordPiece e (flattenBarWord e L) := by
  induction L with
  | nil => simpa only [differentialBasis,basisDifferential,sub_self] using
      (strictWordPiece (K := K) e (flattenBarWord e [])).zero_mem
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,basisDifferential,adjacent,merge_single,
        mergeBasis,smul_zero,map_zero,sub_zero,sub_self]
      exact Submodule.zero_mem _
    | cons b L =>
      have h₁ := adjacent_difference_strict B e hnormal hperm a b L
      have h₂ := strict_prefix e (flattenBarWord e (b::L)) a _ ih
      have he : differentialBasis B (a::b::L)-basisDifferential (normalProduct e) (a::b::L)=
          (appendTail L (productCoefficients B a b)-appendTail L (normalProduct e a b))-
            prepend a (differentialBasis B (b::L)-basisDifferential (normalProduct e) (b::L)) := by
        simp only [differentialBasis,basisDifferential,adjacent,merge_single,mergeBasis,
          one_smul,map_sub]
        abel
      rw [he]
      exact Submodule.sub_mem _ h₁ h₂

include hperm in
theorem differential_mem_internal {r N : ℕ} (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N) :
    differential B z∈internalDegreePiece (K := K) e r N := by
  rw [internalPiece_eq] at hz ⊢
  exact WeightedBar.differential_mem_piece B (wordDegree e) (product_degree B e hperm) z hz

def actualDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K] internalDegreePiece (K := K) e r N where
  toFun z := ⟨-differential B z.val,
    Submodule.neg_mem _ (differential_mem_internal B e hperm z.val z.property)⟩
  map_add' x y := by
    apply Subtype.ext
    change -differential B (x.val+y.val)= -differential B x.val + -differential B y.val
    rw [map_add,neg_add]
  map_smul' c x := by
    apply Subtype.ext
    change -differential B (c • x.val)=c • -differential B x.val
    rw [map_smul,smul_neg]

include hunit hε in
theorem actualDifferential_squared (r N : ℕ) :
    (actualDifferential B e hperm r N).comp (actualDifferential B e hperm (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -differential B (-differential B z.val)=0
  rw [map_neg,neg_neg,differential_squared ε B hunit hε]

def wordWeight (r N : ℕ) (L : InternalDegreeIndex e r N) : ℕ :=
  badPairs R (flattenBarWord e L.val)

theorem leading_homogeneous (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    Homogeneous (R := K) (M := ↥(internalDegreePiece (K := K) e r N))
      (tensorBasis e r N) (wordWeight e r N) (wordWeight e (r+1) N L)
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  intro T hT
  rw [tensorBasis_repr_apply,leadingDegreeDifferential_tensorBasis_val,
    Finsupp.neg_apply,neg_ne_zero] at hT
  have hs := normal_differential_same (K := K) e L.val (Finsupp.mem_support_iff.mpr hT)
  change badPairs R (flattenBarWord e T.val)=badPairs R (flattenBarWord e L.val)
  rw [hs]

include hnormal hperm in
theorem actual_hasTop (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    HasTop (R := K) (M := ↥(internalDegreePiece (K := K) e r N))
      (tensorBasis e r N) (wordWeight e r N) (wordWeight e (r+1) N L)
      (actualDifferential B e hperm r N (tensorBasis e (r+1) N L))
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  apply hasTop_of_strict_difference (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis e r N) (wordWeight e r N)
  · exact leading_homogeneous e r N L
  · intro T hT
    have he : (tensorBasis (K := K) e r N).repr
        (actualDifferential B e hperm r N (tensorBasis e (r+1) N L)-
          leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) T=
        -(((differentialBasis B L.val-
          basisDifferential (normalProduct (K := K) e) L.val) : List C →₀ K) T.val) := by
      rw [tensorBasis_repr_sub,leadingDegreeDifferential_tensorBasis_val]
      change (-differential B (tensorBasis e (r+1) N L).val) T.val-
        (-basisDifferential (normalProduct e) L.val) T.val=_
      rw [tensorBasis_val,differential_single,one_smul]
      simp only [Finsupp.neg_apply,Finsupp.sub_apply]
      abel
    rw [he,neg_ne_zero] at hT
    exact (differential_difference_strict B e hnormal hperm L.val
      (Finsupp.mem_support_iff.mpr hT)).2

include hunit hε hnormal hperm in
theorem actual_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (actualDifferential B e hperm (r+1) N).range=(actualDifferential B e hperm r N).ker := by
  exact range_eq_ker_of_basis (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (M₁ := ↥(internalDegreePiece (K := K) e (r+1) N))
    (M₂ := ↥(internalDegreePiece (K := K) e (r+2) N))
    (I₀ := InternalDegreeIndex e r N)
    (I₁ := InternalDegreeIndex e (r+1) N)
    (I₂ := InternalDegreeIndex e (r+2) N)
    (tensorBasis (K := K) e r N) (wordWeight e r N)
    (tensorBasis e (r+1) N) (wordWeight e (r+1) N)
    (tensorBasis e (r+2) N) (wordWeight e (r+2) N)
    (actualDifferential B e hperm r N) (actualDifferential B e hperm (r+1) N)
    (leadingDegreeDifferential (K := K) e r N)
    (leadingDegreeDifferential (K := K) e (r+1) N)
    (actualDifferential_squared ε B hunit hε e hperm r N)
    (actual_hasTop B e hnormal hperm r N)
    (actual_hasTop B e hnormal hperm (r+1) N)
    (leadingDegree_range_eq_ker (K := K) e r N hr)

def actualComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of
    (fun r => ModuleCat.of K (internalDegreePiece (K := K) e r N))
    (fun r => ModuleCat.ofHom (actualDifferential B e hperm r N))
    (fun r => ModuleCat.hom_ext (actualDifferential_squared ε B hunit hε e hperm r N))

@[simp] theorem actualComplex_d (r N : ℕ) :
    (actualComplex ε B hunit hε e hperm N).d (r+1) r=
      ModuleCat.ofHom (actualDifferential B e hperm r N) := by
  simp [actualComplex]

include hunit hε hnormal hperm in
theorem actual_homology_off_diagonal (r N : ℕ) (hr : r≠N) :
    IsZero ((actualComplex ε B hunit hε e hperm N).homology r) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  cases r with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (internalDegreePiece (K := K) e 0 N))
    have hzero (z : internalDegreePiece (K := K) e 0 N) : z=0 := by
      apply Subtype.ext
      apply Finsupp.ext
      intro L
      change z.val L=0
      apply (Finsupp.mem_supported' K z.val).mp z.property
      rintro ⟨hL,hW⟩
      have hn : L=[] := List.length_eq_zero_iff.mp hL
      subst L
      exact hr hW
    letI : Subsingleton (internalDegreePiece (K := K) e 0 N) :=
      ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ r =>
    rw [HomologicalComplex.exactAt_iff' _ (r+2) (r+1) r (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change (((actualComplex ε B hunit hε e hperm N).d (r+2) (r+1)).hom).range=
      (((actualComplex ε B hunit hε e hperm N).d (r+1) r).hom).ker
    rw [actualComplex_d,actualComplex_d]
    exact actual_range_eq_ker ε B hunit hε e hnormal hperm r N hr

/-- The relation-word complex is the original internally graded bar
complex. Its component maps are the identity on every coefficient word. -/
def actualWeightedIso (N : ℕ) :
    actualComplex ε B hunit hε e hperm N ≅
      WeightedBar.internalComplex ε B hunit hε (wordDegree e)
        (product_degree B e hperm) N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (LinearEquiv.ofEq _ _ (internalPiece_eq (K := K) e r N)).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      rw [actualComplex_d,WeightedBar.internalComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      rfl)

include hunit hε hnormal hperm in
/-- Genuine ordinary Tor is concentrated on the original internal-degree
 diagonal. Every structural hypothesis above concerns the actual algebra
basis and actual multiplication and can be checked independently. -/
theorem hasDiagonalTor :
    WeightedBar.HasDiagonalTor ε B hunit hε (wordDegree e) (product_degree B e hperm) := by
  apply (WeightedBar.hasDiagonalTor_iff ε B hunit hε (wordDegree e)
    (product_degree B e hperm)).mpr
  intro r N hr
  exact (actual_homology_off_diagonal ε B hunit hε e hnormal hperm r N hr).of_iso
    (HomologicalComplex.homologyMapIso
      (actualWeightedIso ε B hunit hε e hperm N) r).symm

end PaperVerification.QuadraticWordPBW
end
end
end TAF_LiteralSource_0491

section TAF_LiteralSource_0492
/- Original module: PaperVerification.ExteriorMonomialKoszul -/


/-!
# Ordinary Tor concentration for actual exterior monomial quotients

The quotient, its basis and its augmentation come from the ordinary
exterior algebra. A proved combinatorial description of its surviving
sets as the normal words of a transitive relation supplies the inputs to
the signed word-bar exactness theorem. The internal degree is the literal
number of exterior generators in each basis monomial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.ExteriorMonomialKoszul

open ExteriorMonomialQuotient QuadraticWordBar AugmentedAlgebraBasis

universe u
variable {K M I : Type u} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder I] (b : Module.Basis I K M) (F : Set (Finset I))
  (hF : ∀ S∈F,S.Nonempty)

def emptyAllowed : Allowed F := ⟨∅,by
  rintro ⟨S,hS,hS0⟩
  have he : S=∅ := Finset.subset_empty.mp hS0
  exact (hF S hS).ne_empty he⟩

def PositiveIndex := {S : Allowed F // S.val.Nonempty}

instance [Finite I] : Finite (PositiveIndex F) := by
  unfold PositiveIndex Allowed
  infer_instance

def positiveNeEquiv : PositiveIndex F≃{S : Allowed F // S≠emptyAllowed F hF} :=
  Equiv.subtypeEquivRight (fun S => by
    rw [Finset.nonempty_iff_ne_empty]
    constructor
    · intro h he
      exact h (congrArg Subtype.val he)
    · intro h he
      exact h (Subtype.ext he))

def optionIndexEquiv : Option (PositiveIndex F)≃Allowed F :=
  (Equiv.optionCongr (positiveNeEquiv F hF)).trans
    (Equiv.optionSubtypeNe (emptyAllowed F hF))

@[simp] theorem optionIndexEquiv_none :
    optionIndexEquiv F hF none=emptyAllowed F hF := rfl

@[simp] theorem optionIndexEquiv_some (S : PositiveIndex F) :
    optionIndexEquiv F hF (some S)=S.val := rfl

def augmentedBasis : Module.Basis (Option (PositiveIndex F)) K
    (ExteriorAlgebra K M⧸monomialIdeal b F) :=
  (quotientBasis b F).reindex (optionIndexEquiv F hF).symm

@[simp] theorem augmentedBasis_none : augmentedBasis b F hF none=1 := by
  simp only [augmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    optionIndexEquiv_none,quotientBasis_apply,emptyAllowed]
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  simp

@[simp] theorem augmentedBasis_some (S : PositiveIndex F) :
    augmentedBasis b F hF (some S)=
      Ideal.Quotient.mk (monomialIdeal b F) (b.ExteriorAlgebra S.val.val) := by
  simp only [augmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    optionIndexEquiv_some,quotientBasis_apply]

@[simp] theorem augmentation_positive (S : PositiveIndex F) :
    augmentation b F hF (augmentedBasis b F hF (some S))=0 := by
  rw [augmentedBasis_some,augmentation_mk]
  exact algebraMapInv_basis b S.val.val S.property

variable (R : I→I→Prop) [IsTrans I R]
  (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)

include hlt in
theorem normalWord_nodup (W : PositiveWord R) : W.val.Nodup := by
  have h := (List.isChain_iff_pairwise.mp W.property.2).imp
    (fun {i j} hij => ne_of_lt (hlt i j hij))
  exact h

include hlt in
theorem normalWord_sort (W : PositiveWord R) : W.val.toFinset.sort=W.val := by
  apply (List.toFinset_sort (fun a b : I => a ≤ b) (normalWord_nodup R hlt W)).mpr
  exact (List.isChain_iff_pairwise.mp W.property.2).imp
    (fun {i j} hij => (hlt i j hij).le)

def normalWordEquiv : PositiveIndex F≃PositiveWord R where
  toFun S := ⟨S.val.val.sort,by
    simpa only [Finset.length_sort] using S.property.card_pos,
    (hchain S.val.val).mp S.val.property⟩
  invFun W := ⟨⟨W.val.toFinset,(hchain W.val.toFinset).mpr (by
    rw [normalWord_sort R hlt W]
    exact W.property.2)⟩,by
      have hnonempty : W.val≠[] := List.ne_nil_of_length_pos W.property.1
      obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hnonempty
      exact ⟨i,List.mem_toFinset.mpr hi⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.sort_toFinset _ _
  right_inv W := Subtype.ext (normalWord_sort R hlt W)

@[simp] theorem normalWordEquiv_word (S : PositiveIndex F) :
    (normalWordEquiv F R hlt hchain S).val=S.val.val.sort := rfl

@[simp] theorem normalWordEquiv_degree (S : PositiveIndex F) :
    QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain) S=S.val.val.card :=
  Finset.length_sort (fun a b : I => a ≤ b)

/-- A normal concatenation has coefficient exactly one because the
actual exterior products already occur in their increasing order. -/
theorem normal_product (S T : PositiveIndex F)
    (h : ((normalWordEquiv F R hlt hchain S).val++
      (normalWordEquiv F R hlt hchain T).val).IsChain R) :
    productCoefficients (augmentedBasis b F hF) S T=
      Finsupp.single (concatenateNormal (normalWordEquiv F R hlt hchain) S T h) 1 := by
  let U := concatenateNormal (normalWordEquiv F R hlt hchain) S T h
  have hw : U.val.val.sort=S.val.val.sort++T.val.val.sort :=
    concatenateNormal_word (normalWordEquiv F R hlt hchain) S T h
  have hp : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)=
      augmentedBasis b F hF (some U) := by
    rw [augmentedBasis_some,augmentedBasis_some,augmentedBasis_some,←map_mul]
    congr 1
    rw [b.exteriorAlgebra_eq_prod_map_sort,b.exteriorAlgebra_eq_prod_map_sort,
      b.exteriorAlgebra_eq_prod_map_sort,hw,List.map_append,List.map_append,List.prod_append]
  change positiveCoordinates (augmentedBasis b F hF)
    (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T))=_
  rw [hp]
  exact positiveCoordinates_vector (augmentedBasis b F hF) U

theorem sort_union_perm_append (S T : Finset I) (hd : Disjoint S T) :
    (S∪T).sort.Perm (S.sort++T.sort) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
  · apply (Finset.sort_nodup S _).append (Finset.sort_nodup T _)
    apply List.disjoint_left.mpr
    intro i hiS hiT
    exact Finset.disjoint_left.mp hd ((Finset.mem_sort _).mp hiS)
      ((Finset.mem_sort _).mp hiT)
  · simp only [List.toFinset_append,Finset.sort_toFinset]

/-- Any nonzero product has exactly the multiset of its original exterior
letters. No dimension or normal-form hypothesis enters this assertion. -/
theorem product_perm (S T U : PositiveIndex F)
    (h : productCoefficients (augmentedBasis b F hF) S T U≠0) :
    (normalWordEquiv F R hlt hchain U).val.Perm
      ((normalWordEquiv F R hlt hchain S).val++
        (normalWordEquiv F R hlt hchain T).val) := by
  have hprod : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)≠0 := by
    intro hp
    apply h
    change positiveCoordinates (augmentedBasis b F hF)
      (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)) U=0
    rw [hp,map_zero,Finsupp.zero_apply]
  have hd : Disjoint S.val.val T.val.val := by
    by_contra hnd
    apply hprod
    rw [augmentedBasis_some,augmentedBasis_some,←map_mul,
      basis_mul_not_disjoint b _ _ hnd,map_zero]
  obtain ⟨u,hu⟩ := basis_mul_disjoint b S.val.val T.val.val hd
  have hallowed : ¬Bad F (S.val.val∪T.val.val) := by
    intro hbad
    apply hprod
    rw [augmentedBasis_some,augmentedBasis_some,←map_mul,hu]
    change Ideal.Quotient.mk (monomialIdeal b F)
      ((u : ℤ) • b.ExteriorAlgebra (S.val.val∪T.val.val))=0
    rw [map_zsmul,quotient_monomial_eq_zero_of_bad b F _ hbad,smul_zero]
  let V : PositiveIndex F := ⟨⟨S.val.val∪T.val.val,hallowed⟩,
    S.property.mono Finset.subset_union_left⟩
  have hp : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)=
      u • augmentedBasis b F hF (some V) := by
    rw [augmentedBasis_some,augmentedBasis_some,augmentedBasis_some,←map_mul,hu]
    change Ideal.Quotient.mk (monomialIdeal b F)
      ((u : ℤ) • b.ExteriorAlgebra (S.val.val∪T.val.val))=
      (u : ℤ) • Ideal.Quotient.mk (monomialIdeal b F)
        (b.ExteriorAlgebra (S.val.val∪T.val.val))
    exact map_zsmul _ _ _
  have he : U=V := by
    by_contra hUV
    apply h
    change positiveCoordinates (augmentedBasis b F hF)
      (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)) U=0
    rw [hp,Units.smul_def,map_zsmul]
    change ((u : ℤ) • (positiveCoordinates (augmentedBasis b F hF)
      (positiveVector (augmentedBasis b F hF) V))) U=0
    rw [positiveCoordinates_vector,Finsupp.smul_apply,Finsupp.single_eq_of_ne hUV,smul_zero]
  subst U
  exact sort_union_perm_append S.val.val T.val.val hd

variable [Fintype I]

include R hlt hchain in
/-- The degree of every actual basis monomial is its original exterior
word length. Its multiplication coefficients preserve that degree. -/
theorem product_degree (S T U : PositiveIndex F)
    (h : productCoefficients (augmentedBasis b F hF) S T U≠0) :
    U.val.val.card=S.val.val.card+T.val.val.card := by
  have hp := (product_perm b F hF R hlt hchain S T U h).length_eq
  simpa only [normalWordEquiv_word,Finset.length_sort,List.length_append] using hp

/-- A complete ordinary-Tor conclusion for the actual exterior quotient.
The only extra input is the explicit finite-set/word equivalence; its
specializations to dimensions at most four are proved separately. -/
theorem hasDiagonalTor :
    WeightedBar.HasDiagonalTor (augmentation b F hF) (augmentedBasis b F hF)
      (augmentedBasis_none b F hF) (augmentation_positive b F hF)
      (QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain))
      (QuadraticWordPBW.product_degree (augmentedBasis b F hF)
        (normalWordEquiv F R hlt hchain) (product_perm b F hF R hlt hchain)) :=
  QuadraticWordPBW.hasDiagonalTor (augmentation b F hF) (augmentedBasis b F hF)
    (augmentedBasis_none b F hF) (augmentation_positive b F hF)
    (normalWordEquiv F R hlt hchain) (normal_product b F hF R hlt hchain)
    (product_perm b F hF R hlt hchain)

end PaperVerification.ExteriorMonomialKoszul
end
end
end TAF_LiteralSource_0492

section TAF_LiteralSource_0493
/- Original module: PaperVerification.AlternatingFormsExteriorFullBasis -/


/-! Integral exterior scalar extension. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def exteriorFullQuotientGrading (f g : ⋀[R]^2 M) :
    TauCeti.InternalGrading R
      (ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) ℕ :=
  (TauCeti.InternalGrading.ofDecomposition (fun s : ℕ => ⋀[R]^s M)).quotient
    ((exteriorRelationIdeal f g).restrictScalars R)
    (by
      apply (TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff
        (fun s : ℕ => ⋀[R]^s M) ((exteriorRelationIdeal f g).restrictScalars R)).mpr
      exact exteriorRelationIdeal_homogeneous f g)

theorem exteriorFullQuotientGrading_piece (f g : ⋀[R]^2 M) (s : ℕ) :
    (exteriorFullQuotientGrading f g).piece s =
      (exteriorDegreeProjection f g s).range := by
  rw [exteriorFullQuotientGrading, TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece]
  change (⋀[R]^s M).map
      (((exteriorRelationIdeal f g).restrictScalars R).mkQ.restrictScalars R) =
    (((exteriorRelationIdeal f g).restrictScalars R).mkQ.comp
      (Submodule.subtype (⋀[R]^s M))).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  rfl

def exteriorQuotientDegreeEquivFullPiece (f g : ⋀[R]^2 M) (s : ℕ) :
    ExteriorQuotientDegree f g s ≃ₗ[R] (exteriorFullQuotientGrading f g).piece s :=
  (exteriorQuotientDegreeEquivImage f g s).trans
    (LinearEquiv.ofEq _ _ (exteriorFullQuotientGrading_piece f g s).symm)

@[simp] theorem exteriorQuotientDegreeEquivFullPiece_mk
    (f g : ⋀[R]^2 M) (s : ℕ) (x : ⋀[R]^s M) :
    ((exteriorQuotientDegreeEquivFullPiece f g s (Submodule.Quotient.mk x) :
      (exteriorFullQuotientGrading f g).piece s) :
        ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) =
      Submodule.Quotient.mk (x : ExteriorAlgebra R M) := by
  rfl

/-- Assemble the full basis in the actual ring quotient by the relation
ideal.  The index records the degree and then the chosen basis index. -/
def exteriorFullBasisOfDegreeBases (f g : ⋀[R]^2 M) {ι : ℕ → Type*}
    (b : ∀ s, Module.Basis (ι s) R (ExteriorQuotientDegree f g s)) :
    Module.Basis (Σ s, ι s) R (ExteriorAlgebra R M ⧸ exteriorRelationIdeal f g) :=
  ((exteriorFullQuotientGrading f g).isInternal.collectedBasis
    (fun s => (b s).map (exteriorQuotientDegreeEquivFullPiece f g s))).map
      (Submodule.Quotient.restrictScalarsEquiv R (exteriorRelationIdeal f g))

theorem exteriorFullBasisOfDegreeBases_apply (f g : ⋀[R]^2 M) {ι : ℕ → Type*}
    (b : ∀ s, Module.Basis (ι s) R (ExteriorQuotientDegree f g s))
    (v : ∀ s, ι s → ⋀[R]^s M)
    (hb : ∀ s i, b s i=Submodule.Quotient.mk (v s i)) (s : ℕ) (i : ι s) :
    exteriorFullBasisOfDegreeBases f g b ⟨s,i⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (v s i : ExteriorAlgebra R M) := by
  rw [exteriorFullBasisOfDegreeBases, Module.Basis.map_apply,
    DirectSum.IsInternal.collectedBasis_coe]
  change (Submodule.Quotient.restrictScalarsEquiv R (exteriorRelationIdeal f g))
    ((exteriorQuotientDegreeEquivFullPiece f g s (b s i) :
      (exteriorFullQuotientGrading f g).piece s) :
        ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) = _
  rw [hb, exteriorQuotientDegreeEquivFullPiece_mk]
  rfl

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0493

section TAF_LiteralSource_0494
/- Original module: PaperVerification.AlternatingFormsExteriorAugmentation -/


/-!
# The actual augmentation and original grading of an exterior quotient

The augmentation is induced by the exterior algebra's scalar projection.
The grading is the image of each genuine exterior power in the literal
ring quotient by the two quadratic relations. All comparison maps below
are constructed independently of any Hilbert function or Koszul property.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorAugmented

universe u
variable {K M : Type u} [CommRing K] [AddCommGroup M] [Module K M]

/-- The scalar projection kills every positive homogeneous exterior power. -/
theorem augmentation_homogeneous_zero {d : ℕ} (hd : 0<d)
    (x : ExteriorAlgebra K M) (hx : x∈⋀[K]^d M) :
    ExteriorAlgebra.algebraMapInv x=0 := by
  have h1 : (LinearMap.range (ExteriorAlgebra.ι K : M →ₗ[K] ExteriorAlgebra K M)).map
      (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toLinearMap=⊥ := by
    rw [←LinearMap.range_comp]
    change LinearMap.range ((ExteriorAlgebra.lift K
      ⟨(0 : M →ₗ[K] K),fun _ => by simp⟩).toLinearMap.comp (ExteriorAlgebra.ι K))=⊥
    rw [ExteriorAlgebra.ι_comp_lift,LinearMap.range_zero]
  have hm : ExteriorAlgebra.algebraMapInv x∈
      (⋀[K]^d M).map (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toLinearMap :=
    ⟨x,hx,rfl⟩
  rw [ExteriorAlgebra.exteriorPower,Submodule.map_pow,h1,
    Submodule.bot_pow (Nat.ne_of_gt hd)] at hm
  exact (Submodule.mem_bot K).mp hm

variable (f g : ⋀[K]^2 M)

abbrev Quotient := ExteriorAlgebra K M ⧸ exteriorRelationIdeal f g

/-- The actual coefficient-field augmentation of the full exterior quotient. -/
def augmentation : Quotient f g →ₐ[K] K :=
  Ideal.Quotient.liftₐ (exteriorRelationIdeal f g) ExteriorAlgebra.algebraMapInv (by
    change exteriorRelationIdeal f g≤
      RingHom.ker (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toRingHom
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact augmentation_homogeneous_zero (by decide : 0<2) f.val f.property
    · exact augmentation_homogeneous_zero (by decide : 0<2) g.val g.property)

@[simp] theorem augmentation_mk (x : ExteriorAlgebra K M) :
    augmentation f g (Ideal.Quotient.mk (exteriorRelationIdeal f g) x)=
      ExteriorAlgebra.algebraMapInv x := rfl

/-- The original homogeneous grading on the actual ring quotient. -/
def grading : TauCeti.InternalGrading K (Quotient f g) ℕ :=
  (exteriorFullQuotientGrading f g).map
    (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g))

theorem grading_piece (d : ℕ) :
    (grading f g).piece d=(⋀[K]^d M).map
      (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap := by
  rw [grading,TauCeti.InternalGrading.map_piece,exteriorFullQuotientGrading_piece]
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨z,z.property,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨exteriorDegreeProjection f g d ⟨z,hz⟩,⟨⟨z,hz⟩,rfl⟩,?_⟩
    rfl

def degreeEquivPiece (d : ℕ) :
    ExteriorQuotientDegree f g d ≃ₗ[K] (grading f g).piece d := by
  rw [grading,TauCeti.InternalGrading.map_piece]
  exact (exteriorQuotientDegreeEquivFullPiece f g d).trans
    (Submodule.equivMapOfInjective
      (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g)).toLinearMap
      (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g)).injective
      ((exteriorFullQuotientGrading f g).piece d))

instance grading_piece_finite [Module.Finite K M] (d : ℕ) :
    Module.Finite K ((grading f g).piece d) :=
  Module.Finite.equiv (degreeEquivPiece f g d)

theorem grading_piece_finrank (d : ℕ) :
    Module.finrank K ((grading f g).piece d)=Module.finrank K (ExteriorQuotientDegree f g d) :=
  (degreeEquivPiece f g d).finrank_eq.symm

theorem grading_zero : (grading f g).piece 0=(1 : Submodule K (Quotient f g)) := by
  rw [grading_piece,ExteriorAlgebra.exteriorPower,pow_zero,Submodule.map_one]

theorem grading_mul (d e : ℕ) (x y : Quotient f g)
    (hx : x∈(grading f g).piece d) (hy : y∈(grading f g).piece e) :
    x*y∈(grading f g).piece (d+e) := by
  rw [grading_piece] at hx hy ⊢
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  refine ⟨a*b,?_,map_mul (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)) a b⟩
  exact SetLike.mul_mem_graded ha hb

theorem augmentation_piece_zero (d : ℕ) (hd : 0<d) (x : Quotient f g)
    (hx : x∈(grading f g).piece d) : augmentation f g x=0 := by
  rw [grading_piece] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  exact augmentation_homogeneous_zero hd a ha

end PaperVerification.AlternatingForms.ExteriorAugmented
end
end
end TAF_LiteralSource_0494

section TAF_LiteralSource_0495
/- Original module: PaperVerification.AlternatingFormsExteriorKoszul -/


/-!
# Actual homogeneous Koszul certificates for exterior quotients

A certificate consists of a genuine finite homogeneous augmented basis
of the original quotient, with its original exterior degrees, and
concentration of actual ordinary Tor. It is constructed from the proved
monomial quotient theorem after an equality of the actual generated
ideals. No assertion that the quotient has a normal form is built into
the certificate or into the algebra's definition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open PaperVerification ExteriorAugmented ExteriorMonomialQuotient
  ExteriorMonomialKoszul AugmentedAlgebraBasis QuadraticWordBar

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Every field describes actual algebra, grading or derived-functor data.
The diagonal assertion concerns ordinary Tor and the original grading. -/
structure HomogeneousKoszulCertificate (f g : ⋀[K]^2 M) where
  Index : Type u
  finite : Finite Index
  basis : Module.Basis (Option Index) K (ExteriorAugmented.Quotient f g)
  degree : Index→ℕ
  unit : basis none=1
  positive : ∀ i,0<degree i
  homogeneous : ∀ i,basis (some i)∈(ExteriorAugmented.grading f g).piece (degree i)
  augmentation_zero : ∀ i,ExteriorAugmented.augmentation f g (basis (some i))=0
  product_degree : ∀ a b c,productCoefficients basis a b c≠0 →degree c=degree a+degree b
  diagonal : WeightedBar.HasDiagonalTor (ExteriorAugmented.augmentation f g)
    basis unit augmentation_zero degree product_degree

section Transport

variable {A D C : Type u} [Ring A] [Algebra K A] [Ring D] [Algebra K D]
  (e : A≃ₐ[K]D) (B : Module.Basis (Option C) K A)

/-- Actual basis coefficients of products are unchanged by an algebra
isomorphism; no commutativity of either algebra is required. -/
theorem map_productCoefficients (a b : C) :
    productCoefficients (B.map e.toLinearEquiv) a b=productCoefficients B a b := by
  apply Finsupp.ext
  intro c
  change (B.map e.toLinearEquiv).repr
      ((B.map e.toLinearEquiv) (some a)*(B.map e.toLinearEquiv) (some b)) (some c)=
    B.repr (B (some a)*B (some b)) (some c)
  rw [Module.Basis.map_apply,Module.Basis.map_apply]
  change (B.map e.toLinearEquiv).repr (e (B (some a))*e (B (some b))) (some c)=_
  have hm : e (B (some a)*B (some b))=e (B (some a))*e (B (some b)) :=
    map_mul e _ _
  rw [←hm]
  change B.repr (e.symm (e (B (some a)*B (some b)))) (some c)=_
  rw [e.symm_apply_apply]

end Transport

section Monomial

variable {I : Type u} [LinearOrder I] [Fintype I]
  (b : Module.Basis I K M) (F : Set (Finset I)) (hF : ∀ S∈F,S.Nonempty)
  (R : I→I→Prop) [IsTrans I R] (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)
  (f g : ⋀[K]^2 M) (he : monomialIdeal b F=exteriorRelationIdeal f g)

def actualBasis : Module.Basis (Option (PositiveIndex F)) K
    (ExteriorAugmented.Quotient f g) :=
  (augmentedBasis b F hF).map (Ideal.quotientEquivAlgOfEq K he).toLinearEquiv

@[simp] theorem actualBasis_none : actualBasis b F hF f g he none=1 := by
  rw [actualBasis,Module.Basis.map_apply,augmentedBasis_none]
  change Ideal.quotientEquivAlgOfEq K he (1 : ExteriorAlgebra K M⧸monomialIdeal b F)=1
  exact map_one (Ideal.quotientEquivAlgOfEq K he)

@[simp] theorem actualBasis_some (S : PositiveIndex F) :
    actualBasis b F hF f g he (some S)=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (b.ExteriorAlgebra S.val.val) := by
  rw [actualBasis,Module.Basis.map_apply,augmentedBasis_some]
  rfl

theorem actualBasis_homogeneous (S : PositiveIndex F) :
    actualBasis b F hF f g he (some S)∈(ExteriorAugmented.grading f g).piece
      (QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain) S) := by
  rw [normalWordEquiv_degree,actualBasis_some,ExteriorAugmented.grading_piece]
  refine ⟨b.ExteriorAlgebra S.val.val,?_,rfl⟩
  have h := ExteriorAlgebra.basis_eq_coe_basis b
    (⟨S.val.val,rfl⟩ : Set.powersetCard I S.val.val.card)
  rw [h]
  exact (b.exteriorPower S.val.val.card
    (⟨S.val.val,rfl⟩ : Set.powersetCard I S.val.val.card)).property

theorem actualBasis_augmentation (S : PositiveIndex F) :
    ExteriorAugmented.augmentation f g (actualBasis b F hF f g he (some S))=0 := by
  rw [actualBasis_some,ExteriorAugmented.augmentation_mk]
  exact algebraMapInv_basis b S.val.val S.property

theorem actualBasis_productCoefficients (S T : PositiveIndex F) :
    productCoefficients (actualBasis b F hF f g he) S T=
      productCoefficients (augmentedBasis b F hF) S T :=
  map_productCoefficients (Ideal.quotientEquivAlgOfEq K he) (augmentedBasis b F hF) S T

theorem actualBasis_normal_product (S T : PositiveIndex F)
    (h : ((normalWordEquiv F R hlt hchain S).val++
      (normalWordEquiv F R hlt hchain T).val).IsChain R) :
    productCoefficients (actualBasis b F hF f g he) S T=
      Finsupp.single (concatenateNormal (normalWordEquiv F R hlt hchain) S T h) 1 := by
  rw [actualBasis_productCoefficients]
  exact normal_product b F hF R hlt hchain S T h

theorem actualBasis_product_perm (S T U : PositiveIndex F)
    (h : productCoefficients (actualBasis b F hF f g he) S T U≠0) :
    (normalWordEquiv F R hlt hchain U).val.Perm
      ((normalWordEquiv F R hlt hchain S).val++
        (normalWordEquiv F R hlt hchain T).val) := by
  rw [actualBasis_productCoefficients] at h
  exact product_perm b F hF R hlt hchain S T U h

/-- The positive ordinary-Tor theorem is obtained on the actual quotient
and the actual exterior grading. The preceding ideal equality is proved
from the concrete generic normal forms in the small-dimensional cases. -/
def certificateOfMonomialIdeal : HomogeneousKoszulCertificate f g where
  Index := PositiveIndex F
  finite := inferInstance
  basis := actualBasis b F hF f g he
  degree := QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain)
  unit := actualBasis_none b F hF f g he
  positive i := by rw [normalWordEquiv_degree]; exact i.property.card_pos
  homogeneous := actualBasis_homogeneous b F hF R hlt hchain f g he
  augmentation_zero := actualBasis_augmentation b F hF f g he
  product_degree := QuadraticWordPBW.product_degree (actualBasis b F hF f g he)
    (normalWordEquiv F R hlt hchain)
    (actualBasis_product_perm b F hF R hlt hchain f g he)
  diagonal := QuadraticWordPBW.hasDiagonalTor (ExteriorAugmented.augmentation f g)
    (actualBasis b F hF f g he) (actualBasis_none b F hF f g he)
    (actualBasis_augmentation b F hF f g he) (normalWordEquiv F R hlt hchain)
    (actualBasis_normal_product b F hF R hlt hchain f g he)
    (actualBasis_product_perm b F hF R hlt hchain f g he)

end Monomial
end PaperVerification.AlternatingForms.ExteriorKoszul
end
end
end TAF_LiteralSource_0495

section TAF_LiteralSource_0496
/- Original module: PaperVerification.ExteriorMonomialRenaming -/


/-!
# Order-preserving renaming of actual exterior monomial quotients

The renaming identifies literal exterior products and ordinary generated
ideals. In particular it permits a finite index type to be lifted to the
universe of the coefficient field without changing the algebra, its
relations, or its original degrees.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.ExteriorMonomialQuotient

variable {K M I J : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder I] [LinearOrder J]
  (b : Module.Basis I K M) (e : J ≃o I) (F : Set (Finset I))

def renamedForbidden : Set (Finset J) := {S | S.map e.toEquiv.toEmbedding ∈ F}

@[simp] theorem map_inverse (S : Finset I) :
    (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding=S := by
  rw [Finset.map_map]
  have he : e.symm.toEquiv.toEmbedding.trans e.toEquiv.toEmbedding=
      Function.Embedding.refl I := by
    apply Function.Embedding.ext
    intro i
    exact e.apply_symm_apply i
  rw [he,Finset.map_refl]

theorem renamed_bad (S : Finset J) :
    Bad (renamedForbidden e F) S ↔ Bad F (S.map e.toEquiv.toEmbedding) := by
  constructor
  · rintro ⟨T,hT,hTS⟩
    exact ⟨T.map e.toEquiv.toEmbedding,hT,Finset.map_subset_map.mpr hTS⟩
  · rintro ⟨T,hT,hTS⟩
    refine ⟨T.map e.symm.toEquiv.toEmbedding,?_,?_⟩
    · change (T.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding∈F
      rw [map_inverse]
      exact hT
    · apply (Finset.map_subset_map (f := e.toEquiv.toEmbedding)).mp
      rw [map_inverse]
      exact hTS

theorem renamedForbidden_nonempty (hF : ∀ S∈F,S.Nonempty) :
    ∀ S∈renamedForbidden e F,S.Nonempty := by
  intro S hS
  exact Finset.map_nonempty.mp (hF (S.map e.toEquiv.toEmbedding) hS)

theorem sort_renamed (S : Finset J) :
    S.sort.map e=(S.map e.toEquiv.toEmbedding).sort := by
  exact Finset.map_sort e.toEquiv.toEmbedding S (· ≤ ·) (· ≤ ·)
    (fun a _ b _ => e.le_iff_le.symm)

/-- An increasing reindexing changes the index set but introduces no
exterior sign. Both sides are the same ordered generator product. -/
theorem exteriorBasis_reindex (S : Finset J) :
    (b.reindex e.toEquiv.symm).ExteriorAlgebra S=
      b.ExteriorAlgebra (S.map e.toEquiv.toEmbedding) := by
  rw [(b.reindex e.toEquiv.symm).exteriorAlgebra_eq_prod_map_sort,
    b.exteriorAlgebra_eq_prod_map_sort,←sort_renamed e S]
  simp only [List.map_map,Module.Basis.coe_reindex,Equiv.symm_symm]
  rfl

/-- Equality of the ordinary generated ideals under this genuine basis
reindexing. The quotient is not redefined by a combinatorial rule. -/
theorem monomialIdeal_reindex :
    monomialIdeal (b.reindex e.toEquiv.symm) (renamedForbidden e F)=
      monomialIdeal b F := by
  unfold monomialIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact ⟨S.map e.toEquiv.toEmbedding,hS,(exteriorBasis_reindex b e S).symm⟩
  · rintro ⟨S,hS,rfl⟩
    refine ⟨S.map e.symm.toEquiv.toEmbedding,?_,?_⟩
    · change (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding∈F
      rw [map_inverse]
      exact hS
    · rw [exteriorBasis_reindex,map_inverse]

def renamedRelation (R : I→I→Prop) : J→J→Prop := fun i j => R (e i) (e j)

instance renamedRelation_trans (R : I→I→Prop) [IsTrans I R] :
    IsTrans J (renamedRelation e R) where
  trans a b c hab hbc := IsTrans.trans (e a) (e b) (e c) hab hbc

theorem renamedRelation_increasing (R : I→I→Prop)
    (hlt : ∀ i j,R i j→i<j) : ∀ i j,renamedRelation e R i j→i<j := by
  intro i j h
  exact e.lt_iff_lt.mp (hlt (e i) (e j) h)

theorem renamed_chain (R : I→I→Prop)
    (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R) :
    ∀ S : Finset J,¬Bad (renamedForbidden e F) S↔S.sort.IsChain (renamedRelation e R) := by
  intro S
  rw [renamed_bad,hchain,←sort_renamed e S]
  exact List.isChain_map e

end PaperVerification.ExteriorMonomialQuotient
end
end
end TAF_LiteralSource_0496

section TAF_LiteralSource_0497
/- Original module: PaperVerification.AlternatingFormsFiniteExteriorKoszul -/


/-!
# Finite-index Koszul certificates in arbitrary universes

The ordinary derived-functor construction uses coefficient, module and
basis types in one universe. A literal finite coordinate basis is lifted
along its order isomorphism, and the preceding renaming theorem proves
that its actual exterior monomial ideal is unchanged. No algebraic
hypothesis or restriction on the field/vector-space universe is added.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open PaperVerification ExteriorMonomialQuotient

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  {I : Type} [LinearOrder I] [Fintype I]
  (b : Module.Basis I K M) (F : Set (Finset I)) (hF : ∀ S∈F,S.Nonempty)
  (R : I→I→Prop) [IsTrans I R] (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)
  (f g : ⋀[K]^2 M) (he : monomialIdeal b F=exteriorRelationIdeal f g)

/-- The actual original-grading ordinary-Tor certificate, using a finite
coordinate index type without restricting the ambient universe. -/
def certificateOfFiniteMonomialIdeal : HomogeneousKoszulCertificate f g := by
  let e : ULift.{u} I ≃o I := ULift.orderIso
  let b' : Module.Basis (ULift.{u} I) K M := b.reindex e.toEquiv.symm
  let F' : Set (Finset (ULift.{u} I)) := renamedForbidden e F
  let R' : ULift.{u} I→ULift.{u} I→Prop := renamedRelation e R
  letI : IsTrans (ULift.{u} I) R' := renamedRelation_trans e R
  exact certificateOfMonomialIdeal b' F' (renamedForbidden_nonempty e F hF)
    R' (renamedRelation_increasing e R hlt) (renamed_chain e F R hchain) f g
    ((monomialIdeal_reindex b e F).trans he)

end PaperVerification.AlternatingForms.ExteriorKoszul
end
end
end TAF_LiteralSource_0497

section TAF_LiteralSource_0498
/- Original module: PaperVerification.AlternatingFormsThreeNormalForm -/


/-!
# A genuine generic normal form for a pair of two-forms in dimension three

A single coefficient minor defines a nonempty principal open in the full
space of pairs. On it, explicit row reduction and a determinant-one shear
produce the monomial relations e₀∧e₁ and e₁∧e₂. No assertion about dominant
maps having rational preimages is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.ThreeNormalForm

variable {K : Type*} [Field K]

def slotRow : Fin 3 → Fin 3 := ![0,0,1]
def slotCol : Fin 3 → Fin 3 := ![1,2,2]

theorem slots : OrbitPairSlots slotRow slotCol := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slotRow,slotCol]
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [slotRow,slotCol,Fin.exists_fin_succ]

def formEquiv : (Fin 3 → K) ≃ₗ[K] (⋀[K]^2 (Fin 3 → K)) := orbitSlotLinearEquiv slots

def formBasis : Module.Basis (Fin 3) K (⋀[K]^2 (Fin 3 → K)) := orbitSlotBasis slots

def coefficientMinor (c d : Fin 3 → K) : K := c 0*d 2-d 0*c 2

def shear (a b : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0+b*x 1,x 1,x 2+a*x 1]
  invFun x := ![x 0-b*x 1,x 1,x 2-a*x 1]
  left_inv x := by ext i; fin_cases i <;> simp <;> ring
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def shearBasis (a b : K) : Module.Basis (Fin 3) K (Fin 3 → K) :=
  (Pi.basisFun K (Fin 3)).map (shear a b)

def first (B : Module.Basis (Fin 3) K (Fin 3 → K)) : ⋀[K]^2 (Fin 3 → K) :=
  exteriorPower.ιMulti K 2 ![B 0,B 1]

def second (B : Module.Basis (Fin 3) K (Fin 3 → K)) : ⋀[K]^2 (Fin 3 → K) :=
  exteriorPower.ιMulti K 2 ![B 1,B 2]

theorem first_coordinates (a b : K) :
    (formEquiv (K := K)).symm (first (shearBasis a b))=![1,a,0] := by
  funext i
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      first,shearBasis,Module.Basis.map_apply,shear,orbitExteriorCoefficient_word,
      slotRow,slotCol,Pi.basisFun_apply,Pi.single_apply]

theorem second_coordinates (a b : K) :
    (formEquiv (K := K)).symm (second (shearBasis a b))=![0,b,1] := by
  funext i
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      second,shearBasis,Module.Basis.map_apply,shear,orbitExteriorCoefficient_word,
      slotRow,slotCol,Pi.basisFun_apply,Pi.single_apply]

/-- Explicit generator row reduction on the full coefficient principal open. -/
theorem normal_form (c d : Fin 3 → K) (hD : coefficientMinor c d≠0) :
    ∃ B : Module.Basis (Fin 3) K (Fin 3 → K),
      Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 3 → K)))=
        Submodule.span K ({first B,second B} : Set (⋀[K]^2 (Fin 3 → K))) := by
  let a := (d 2*c 1-c 2*d 1)/coefficientMinor c d
  let b := (c 0*d 1-d 0*c 1)/coefficientMinor c d
  let B := shearBasis a b
  let F := first B
  let G := second B
  have hF : (formEquiv (K := K)).symm F=![1,a,0] := first_coordinates a b
  have hG : (formEquiv (K := K)).symm G=![0,b,1] := second_coordinates a b
  have hf : formEquiv c=c 0 • F+c 2 • G := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,hF,hG,LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hg : formEquiv d=d 0 • F+d 2 • G := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,hF,hG,LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hF' : F=(d 2/coefficientMinor c d) • formEquiv c+
      (-c 2/coefficientMinor c d) • formEquiv d := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,hF]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hG' : G=(-d 0/coefficientMinor c d) • formEquiv c+
      (c 0/coefficientMinor c d) • formEquiv d := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,hG]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  refine ⟨B,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [hf]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [F])))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G])))
    · rw [hg]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [F])))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G])))
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [show first B=F from rfl,hF']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [show second B=G from rfl,hG']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

def principalPolynomial : MvPolynomial (Fin 3 ⊕ Fin 3) K :=
  MvPolynomial.X (.inl 0)*MvPolynomial.X (.inr 2)-
    MvPolynomial.X (.inr 0)*MvPolynomial.X (.inl 2)

theorem principalPolynomial_eval (y : (Fin 3 ⊕ Fin 3) → K) :
    MvPolynomial.eval y principalPolynomial=
      coefficientMinor (fun i => y (.inl i)) (fun i => y (.inr i)) := by
  simp [principalPolynomial,coefficientMinor]

def canonicalPoint : (Fin 3 ⊕ Fin 3) → K := Sum.elim ![1,0,0] ![0,0,1]

theorem principalPolynomial_canonical :
    MvPolynomial.eval (canonicalPoint (K := K)) principalPolynomial=1 := by
  norm_num [principalPolynomial_eval,coefficientMinor,canonicalPoint]

theorem principalPolynomial_ne_zero : (principalPolynomial (K := K))≠0 := by
  intro hz
  have h := principalPolynomial_canonical (K := K)
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem formsFromCoordinates (y : (Fin 3 ⊕ Fin 3) → K) :
    orbitFormsFromCoordinates (formBasis (K := K)) y=
      (formEquiv (fun i => y (.inl i)),formEquiv (fun i => y (.inr i))) := by
  apply Prod.ext <;>
    simp only [orbitFormsFromCoordinates,formBasis,orbitSlotBasis_apply,formEquiv,
      orbitSlotLinearEquiv_apply,orbitTwoFormOfSlots]

theorem coordinateForms_map {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 3 → K) ≃ₗ[K] M)
    (b₂ : Module.Basis (Fin 3) K (⋀[K]^2 (Fin 3 → K)))
    (y : (Fin 3 ⊕ Fin 3) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y=
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates,Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply,map_sum,map_smul]

theorem exterior_map_pair {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 3 → K) ≃ₗ[K] M) (u v : Fin 3 → K) :
    exteriorPower.map 2 e.toLinearMap (exteriorPower.ιMulti K 2 ![u,v])=
      exteriorPower.ιMulti K 2 ![e u,e v] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The normal form exists on an explicitly nonempty principal open in
all pairs of forms on an arbitrary three-dimensional vector space. -/
theorem generic_normal_form {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (hdim : Module.finrank K M=3) :
    ∃ b₂ : Module.Basis (Fin 3) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 3 ⊕ Fin 3) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 → ∃ B : Module.Basis (Fin 3) K M,
          Submodule.span K ({(orbitFormsFromCoordinates b₂ y).1,
            (orbitFormsFromCoordinates b₂ y).2} : Set (⋀[K]^2 M))=
          Submodule.span K ({exteriorPower.ιMulti K 2 ![B 0,B 1],
            exteriorPower.ιMulti K 2 ![B 1,B 2]} : Set (⋀[K]^2 M)) := by
  let e : (Fin 3 → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun,hdim])
  refine ⟨formBasis.map (orbitExteriorPowerEquiv e 2),principalPolynomial,
    principalPolynomial_ne_zero,?_,?_⟩
  · exact ⟨canonicalPoint,by rw [principalPolynomial_canonical]; exact one_ne_zero⟩
  · intro y hy
    rw [principalPolynomial_eval] at hy
    obtain ⟨B,hB⟩ := normal_form (fun i => y (.inl i)) (fun i => y (.inr i)) hy
    refine ⟨B.map e,?_⟩
    have hmap := congrArg (Submodule.map (exteriorPower.map 2 e.toLinearMap)) hB
    rw [coordinateForms_map,formsFromCoordinates]
    simpa only [Submodule.map_span,Set.image_insert_eq,Set.image_singleton,first,second,
      exterior_map_pair,Module.Basis.map_apply] using hmap

end PaperVerification.AlternatingForms.ThreeNormalForm
end
end
end TAF_LiteralSource_0498

section TAF_LiteralSource_0499
/- Original module: PaperVerification.AlternatingFormsFourPfaffian -/


/-!
# Exact four-dimensional Pfaffian factorization

Six coordinates are an actual exterior basis. Vanishing of the displayed
Pfaffian, with a nonzero 01 coefficient, gives explicit decomposable
factors. The mixed Pfaffian is exactly the determinant of the four factors,
so its nonvanishing constructs a genuine basis of the vector space.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.FourPfaffian

variable {R : Type*} [CommRing R]

def pfaffian (c : Fin 6 → R) : R := c 0*c 5-c 1*c 4+c 2*c 3

def polar (c d : Fin 6 → R) : R :=
  c 0*d 5+d 0*c 5-c 1*d 4-d 1*c 4+c 2*d 3+d 2*c 3

def pencil (c d : Fin 6 → R) (t : R) : Fin 6 → R := fun i => c i-t*d i

def discriminant (c d : Fin 6 → R) : R :=
  (polar c d)^2-4*pfaffian d*pfaffian c

def pivotResultant (c d : Fin 6 → R) : R :=
  pfaffian d*(c 0)^2-polar c d*c 0*d 0+pfaffian c*(d 0)^2

theorem pfaffian_pencil (c d : Fin 6 → R) (t : R) :
    pfaffian (pencil c d t)=pfaffian d*t^2-polar c d*t+pfaffian c := by
  dsimp [pfaffian,polar,pencil]
  ring

theorem pencil_polar_identity (c d : Fin 6 → R) (r s : R) :
    polar (pencil c d r) (pencil c d s)+pfaffian d*(r-s)^2=
      pfaffian (pencil c d r)+pfaffian (pencil c d s) := by
  dsimp [pfaffian,polar,pencil]
  ring

variable {K : Type*} [Field K]

def slotRow : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def slotCol : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

theorem slots : OrbitPairSlots slotRow slotCol := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slotRow,slotCol]
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [slotRow,slotCol,Fin.exists_fin_succ]

def formEquiv : (Fin 6 → K) ≃ₗ[K] (⋀[K]^2 (Fin 4 → K)) := orbitSlotLinearEquiv slots

def formBasis : Module.Basis (Fin 6) K (⋀[K]^2 (Fin 4 → K)) := orbitSlotBasis slots

def leftFactor (c : Fin 6 → K) : Fin 4 → K := ![1,0,-c 3/c 0,-c 4/c 0]
def rightFactor (c : Fin 6 → K) : Fin 4 → K := ![0,c 0,c 1,c 2]

/-- A literal factorization in the genuine second exterior power. -/
theorem decomposable_of_pfaffian_zero (c : Fin 6 → K)
    (hc : c 0≠0) (hp : pfaffian c=0) :
    formEquiv c=exteriorPower.ιMulti K 2 ![leftFactor c,rightFactor c] := by
  apply (formEquiv (K := K)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext i
  dsimp only [pfaffian] at hp
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      orbitExteriorCoefficient_word,slotRow,slotCol,leftFactor,rightFactor]
  all_goals field_simp [hc]
  all_goals linear_combination hp

def factorMatrix (c d : Fin 6 → K) : Matrix (Fin 4) (Fin 4) K :=
  ![leftFactor c,rightFactor c,leftFactor d,rightFactor d]

/-- The determinant records genuine independence of all four factor vectors. -/
theorem factorMatrix_det (c d : Fin 6 → K) (hc : c 0≠0) (hd : d 0≠0)
    (hpc : pfaffian c=0) (hpd : pfaffian d=0) :
    (factorMatrix c d).det=polar c d := by
  have hc5 : c 5=(c 1*c 4-c 2*c 3)/c 0 := by
    apply (eq_div_iff hc).mpr
    dsimp only [pfaffian] at hpc
    linear_combination hpc
  have hd5 : d 5=(d 1*d 4-d 2*d 3)/d 0 := by
    apply (eq_div_iff hd).mpr
    dsimp only [pfaffian] at hpd
    linear_combination hpd
  dsimp only [polar]
  rw [hc5,hd5,Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  norm_num [Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove,factorMatrix,leftFactor,rightFactor]
  field_simp [hc,hd]
  ring

def factorBasis (c d : Fin 6 → K) (h : (factorMatrix c d).det≠0) :
    Module.Basis (Fin 4) K (Fin 4 → K) :=
  basisOfLinearIndependentOfCardEqFinrank' (factorMatrix c d)
    (Matrix.linearIndependent_rows_of_det_ne_zero h) (by simp)

theorem factorBasis_apply (c d : Fin 6 → K) (h : (factorMatrix c d).det≠0) (i : Fin 4) :
    factorBasis c d h i=factorMatrix c d i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank' (K := K) (factorMatrix c d)
      (Matrix.linearIndependent_rows_of_det_ne_zero h) (by simp)) i

/-- Every simple Pfaffian root lies in the explicit decomposability chart. -/
theorem pencil_pivot_ne_zero (c d : Fin 6 → K) (hR : pivotResultant c d≠0)
    (t : K) (ht : pfaffian (pencil c d t)=0) : pencil c d t 0≠0 := by
  intro hz
  have hc : c 0=t*d 0 := sub_eq_zero.mp hz
  rw [pfaffian_pencil] at ht
  apply hR
  dsimp only [pivotResultant]
  rw [hc]
  linear_combination (d 0)^2*ht

theorem distinct_root_polar_ne_zero (c d : Fin 6 → K) (hd : pfaffian d≠0)
    (r s : K) (hrs : r≠s)
    (hr : pfaffian (pencil c d r)=0) (hs : pfaffian (pencil c d s)=0) :
    polar (pencil c d r) (pencil c d s)≠0 := by
  intro hz
  have h := pencil_polar_identity c d r s
  rw [hz,hr,hs,zero_add,add_zero] at h
  exact (mul_ne_zero hd (pow_ne_zero 2 (sub_ne_zero.mpr hrs))) h

/-- Distinct quadratic roots are constructed in the algebraically closed
coefficient field; no root-existence hypothesis is added to the normal form. -/
theorem quadratic_distinct_roots [CharZero K] [IsAlgClosed K]
    (a b c : K) (ha : a≠0) (hD : b^2-4*a*c≠0) :
    ∃ r s : K,r≠s ∧ a*r^2+b*r+c=0 ∧ a*s^2+b*s+c=0 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (b^2-4*a*c) (n := 2) (by decide)
  have hz0 : z≠0 := by intro h; rw [h,zero_pow (by decide)] at hz; exact hD hz.symm
  let r := (-b+z)/(2*a)
  let s := (-b-z)/(2*a)
  have hrs : r-s=z/a := by dsimp [r,s]; field_simp [ha]; ring
  refine ⟨r,s,?_,?_,?_⟩
  · intro he
    have hq : z/a=0 := by rw [←hrs,he,sub_self]
    exact (div_ne_zero hz0 ha) hq
  · dsimp [r]
    field_simp [ha]
    linear_combination hz
  · dsimp [s]
    field_simp [ha]
    linear_combination hz

end PaperVerification.AlternatingForms.FourPfaffian
end
end
end TAF_LiteralSource_0499

section TAF_LiteralSource_0500
/- Original module: PaperVerification.AlternatingFormsFourNormalForm -/


/-!
# The actual generic normal form in dimension four

The displayed polynomial is nonzero at an explicit pair of forms. On its
principal open, the two distinct Pfaffian roots give two decomposable forms;
their four factors are a basis. Their span is exactly the original relation
span. This proves existence of a genuine vector-space normal form, rather
than relying on any assertion about preimages of a dominant orbit map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.FourNormalForm
open FourPfaffian

variable {K : Type*} [Field K]

def first (B : Module.Basis (Fin 4) K (Fin 4 → K)) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![B 0,B 1]

def second (B : Module.Basis (Fin 4) K (Fin 4 → K)) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![B 2,B 3]

theorem formEquiv_pencil (c d : Fin 6 → K) (t : K) :
    formEquiv (pencil c d t)=formEquiv c-t • formEquiv d := by
  rw [←map_smul,←map_sub]
  rfl

theorem span_pencil_pair (c d : Fin 6 → K) (r s : K) (hrs : r≠s) :
    Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 4 → K)))=
      Submodule.span K ({formEquiv (pencil c d r),formEquiv (pencil c d s)} :
        Set (⋀[K]^2 (Fin 4 → K))) := by
  have hsr : s-r≠0 := sub_ne_zero.mpr hrs.symm
  have hf : formEquiv c=(s/(s-r)) • formEquiv (pencil c d r)+
      (-r/(s-r)) • formEquiv (pencil c d s) := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pencil]
    field_simp [hsr]
    ring
  have hg : formEquiv d=(1/(s-r)) • formEquiv (pencil c d r)+
      (-1/(s-r)) • formEquiv (pencil c d s) := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pencil]
    field_simp [hsr]
    ring
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [hf]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [hg]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl) <;> rw [formEquiv_pencil]
    all_goals
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- On the explicit Pfaffian principal open, the actual relation span is the
span of two disjoint exterior basis monomials. -/
theorem normal_form [CharZero K] [IsAlgClosed K] (c d : Fin 6 → K)
    (ha : pfaffian d≠0) (hD : discriminant c d≠0)
    (hR : pivotResultant c d≠0) :
    ∃ B : Module.Basis (Fin 4) K (Fin 4 → K),
      Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 4 → K)))=
        Submodule.span K ({first B,second B} : Set (⋀[K]^2 (Fin 4 → K))) := by
  obtain ⟨r,s,hrs,hr,hs⟩ := quadratic_distinct_roots
    (pfaffian d) (-polar c d) (pfaffian c) ha (by simpa [discriminant] using hD)
  have hpr : pfaffian (pencil c d r)=0 := by
    rw [pfaffian_pencil]
    simpa only [neg_mul,sub_eq_add_neg] using hr
  have hps : pfaffian (pencil c d s)=0 := by
    rw [pfaffian_pencil]
    simpa only [neg_mul,sub_eq_add_neg] using hs
  have hcr := pencil_pivot_ne_zero c d hR r hpr
  have hcs := pencil_pivot_ne_zero c d hR s hps
  have hdet : (factorMatrix (pencil c d r) (pencil c d s)).det≠0 := by
    rw [factorMatrix_det _ _ hcr hcs hpr hps]
    exact distinct_root_polar_ne_zero c d ha r s hrs hpr hps
  let B := factorBasis (pencil c d r) (pencil c d s) hdet
  have hfirst : first B=formEquiv (pencil c d r) := by
    rw [decomposable_of_pfaffian_zero _ hcr hpr]
    simp only [first,B,factorBasis_apply,factorMatrix,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hsecond : second B=formEquiv (pencil c d s) := by
    rw [decomposable_of_pfaffian_zero _ hcs hps]
    simp only [second,B,factorBasis_apply,factorMatrix,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  exact ⟨B,by rw [hfirst,hsecond]; exact span_pencil_pair c d r s hrs⟩

def principalPolynomial : MvPolynomial (Fin 6 ⊕ Fin 6) K :=
  let c := fun i : Fin 6 => MvPolynomial.X (Sum.inl i)
  let d := fun i : Fin 6 => MvPolynomial.X (Sum.inr i)
  pfaffian d*discriminant c d*pivotResultant c d

theorem principalPolynomial_eval (y : (Fin 6 ⊕ Fin 6) → K) :
    MvPolynomial.eval y principalPolynomial=
      pfaffian (fun i => y (.inr i))*
        discriminant (fun i => y (.inl i)) (fun i => y (.inr i))*
        pivotResultant (fun i => y (.inl i)) (fun i => y (.inr i)) := by
  simp [principalPolynomial,pfaffian,discriminant,polar,pivotResultant]

/-- This pair is F+G,F+2G with F=e₀∧e₁ and
G=(e₀+e₂)∧(e₁+e₃). Both simple root forms meet the same pivot chart. -/
def canonicalPoint : (Fin 6 ⊕ Fin 6) → K :=
  Sum.elim ![2,0,1,-1,0,1] ![3,0,2,-2,0,2]

theorem principalPolynomial_canonical :
    MvPolynomial.eval (canonicalPoint (K := K)) principalPolynomial= -2 := by
  norm_num [principalPolynomial_eval,pfaffian,discriminant,polar,pivotResultant,canonicalPoint]

theorem principalPolynomial_ne_zero [CharZero K] : (principalPolynomial (K := K))≠0 := by
  intro hz
  have h := principalPolynomial_canonical (K := K)
  rw [hz,map_zero] at h
  norm_num at h

theorem formsFromCoordinates (y : (Fin 6 ⊕ Fin 6) → K) :
    orbitFormsFromCoordinates (formBasis (K := K)) y=
      (formEquiv (fun i => y (.inl i)),formEquiv (fun i => y (.inr i))) := by
  apply Prod.ext <;>
    simp only [orbitFormsFromCoordinates,formBasis,orbitSlotBasis_apply,formEquiv,
      orbitSlotLinearEquiv_apply,orbitTwoFormOfSlots]

theorem coordinateForms_map {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 4 → K) ≃ₗ[K] M)
    (b₂ : Module.Basis (Fin 6) K (⋀[K]^2 (Fin 4 → K)))
    (y : (Fin 6 ⊕ Fin 6) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y=
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates,Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply,map_sum,map_smul]

theorem exterior_map_pair {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 4 → K) ≃ₗ[K] M) (u v : Fin 4 → K) :
    exteriorPower.map 2 e.toLinearMap (exteriorPower.ιMulti K 2 ![u,v])=
      exteriorPower.ιMulti K 2 ![e u,e v] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Actual normal forms for all pairs in a nonempty principal open of the
full coefficient space, on an arbitrary four-dimensional vector space. -/
theorem generic_normal_form [CharZero K] [IsAlgClosed K]
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (hdim : Module.finrank K M=4) :
    ∃ b₂ : Module.Basis (Fin 6) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 6 ⊕ Fin 6) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 → ∃ B : Module.Basis (Fin 4) K M,
          Submodule.span K ({(orbitFormsFromCoordinates b₂ y).1,
            (orbitFormsFromCoordinates b₂ y).2} : Set (⋀[K]^2 M))=
          Submodule.span K ({exteriorPower.ιMulti K 2 ![B 0,B 1],
            exteriorPower.ιMulti K 2 ![B 2,B 3]} : Set (⋀[K]^2 M)) := by
  let e : (Fin 4 → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun,hdim])
  refine ⟨formBasis.map (orbitExteriorPowerEquiv e 2),principalPolynomial,
    principalPolynomial_ne_zero,?_,?_⟩
  · exact ⟨canonicalPoint,by rw [principalPolynomial_canonical]; norm_num⟩
  · intro y hy
    rw [principalPolynomial_eval] at hy
    have hpair := (mul_ne_zero_iff.mp hy).1
    have hR := (mul_ne_zero_iff.mp hy).2
    have ha := (mul_ne_zero_iff.mp hpair).1
    have hD := (mul_ne_zero_iff.mp hpair).2
    obtain ⟨B,hB⟩ := normal_form (fun i => y (.inl i)) (fun i => y (.inr i)) ha hD hR
    refine ⟨B.map e,?_⟩
    have hmap := congrArg (Submodule.map (exteriorPower.map 2 e.toLinearMap)) hB
    rw [coordinateForms_map,formsFromCoordinates]
    simpa only [Submodule.map_span,Set.image_insert_eq,Set.image_singleton,first,second,
      exterior_map_pair,Module.Basis.map_apply] using hmap

end PaperVerification.AlternatingForms.FourNormalForm
end
end
end TAF_LiteralSource_0500

section TAF_LiteralSource_0501
/- Original module: PaperVerification.AlternatingFormsSmallExteriorKoszul -/


/-!
# The actual exterior quotient Koszul direction in small dimensions

The small finite-set checks below establish only which monomials survive
in dimensions at most four. The homological conclusion has unbounded
homological and internal degrees and follows from the proved actual
word-bar resolution and filtered exactness theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.SmallExteriorKoszul

open PaperVerification ExteriorMonomialQuotient ExteriorMonomialKoszul ExteriorKoszul

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- In dimension two the single exterior pair is killed. -/
def forbiddenTwo : Set (Finset (Fin 2)) := {{0,1}}

/-- The canonical independent pair in dimension three. -/
def forbiddenThree : Set (Finset (Fin 3)) := {{0,1},{1,2}}

/-- The two complementary decomposable forms in dimension four. -/
def forbiddenFour : Set (Finset (Fin 4)) := {{0,1},{2,3}}

def relationEmpty (I : Type*) : I→I→Prop := fun _ _ => False

def relationThree (i j : Fin 3) : Prop := i=0 ∧ j=2

def relationFour (i j : Fin 4) : Prop := i.val<2 ∧ 2≤j.val

instance emptyTransitive (I : Type*) : IsTrans I (relationEmpty I) where
  trans _ _ _ h _ := h.elim

instance threeTransitive : IsTrans (Fin 3) relationThree where
  trans a b c hab hbc := by
    have hb : (2 : Fin 3)=0 := hab.2.symm.trans hbc.1
    contradiction

instance fourTransitive : IsTrans (Fin 4) relationFour where
  trans a b c hab hbc := by
    exact False.elim (Nat.not_lt_of_ge hab.2 hbc.1)

theorem empty_increasing (I : Type*) [LinearOrder I] :
    ∀ i j,relationEmpty I i j→i<j := fun _ _ h => h.elim

theorem three_increasing : ∀ i j,relationThree i j→i<j := by
  rintro i j ⟨rfl,rfl⟩
  decide

theorem four_increasing : ∀ i j,relationFour i j→i<j := by
  intro i j h
  change i.val<j.val
  exact Nat.lt_of_lt_of_le h.1 h.2

theorem two_nonempty : ∀ S∈forbiddenTwo,S.Nonempty := by
  simp [forbiddenTwo]

theorem three_nonempty : ∀ S∈forbiddenThree,S.Nonempty := by
  simp [forbiddenThree]

theorem four_nonempty : ∀ S∈forbiddenFour,S.Nonempty := by
  simp [forbiddenFour]

private theorem pairwise_iff_on_sorted {I : Type*} [LinearOrder I]
    (R : I→I→Prop) (l : List I) (hs : l.Pairwise (· < ·)) :
    l.Pairwise R ↔ ∀ i∈l,∀ j∈l,i<j→R i j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hs ⊢
    constructor
    · rintro ⟨ha,hl⟩ i hi j hj hij
      rcases List.mem_cons.mp hi with hia | hil
      · subst i
        rcases List.mem_cons.mp hj with hja | hjl
        · subst j
          exact (lt_irrefl _ hij).elim
        · exact ha j hjl
      · rcases List.mem_cons.mp hj with hja | hjl
        · subst j
          exact (lt_asymm (hs.1 i hil) hij).elim
        · exact (ih hs.2).mp hl i hil j hjl hij
    · intro h
      refine ⟨?_,(ih hs.2).mpr ?_⟩
      · intro j hj
        exact h a (by simp) j (List.mem_cons_of_mem _ hj) (hs.1 j hj)
      · intro i hi j hj hij
        exact h i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) hij

private theorem sort_chain_iff {I : Type*} [LinearOrder I]
    (R : I→I→Prop) [IsTrans I R] (S : Finset I) :
    S.sort.IsChain R ↔ ∀ i∈S,∀ j∈S,i<j→R i j := by
  rw [List.isChain_iff_pairwise,pairwise_iff_on_sorted R _ (Finset.sortedLT_sort S).pairwise]
  simp only [Finset.mem_sort]

theorem zero_words : ∀ S : Finset (Fin 0),
    ¬Bad (∅ : Set (Finset (Fin 0))) S↔S.sort.IsChain (relationEmpty (Fin 0)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,Fin.forall_fin_succ]

theorem one_words : ∀ S : Finset (Fin 1),
    ¬Bad (∅ : Set (Finset (Fin 1))) S↔S.sort.IsChain (relationEmpty (Fin 1)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,Fin.forall_fin_succ]

theorem two_words : ∀ S : Finset (Fin 2),
    ¬Bad forbiddenTwo S↔S.sort.IsChain (relationEmpty (Fin 2)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenTwo,relationEmpty,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem three_words : ∀ S : Finset (Fin 3),
    ¬Bad forbiddenThree S↔S.sort.IsChain relationThree := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenThree,relationThree,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem four_words : ∀ S : Finset (Fin 4),
    ¬Bad forbiddenFour S↔S.sort.IsChain relationFour := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenFour,relationFour,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem empty_monomial_ideal {I : Type*} [LinearOrder I] (b : Module.Basis I K M) :
    monomialIdeal b ∅=exteriorRelationIdeal (0 : ⋀[K]^2 M) 0 := by
  simp [monomialIdeal,exteriorRelationIdeal]

theorem two_monomial_ideal (b : Module.Basis (Fin 2) K M) :
    monomialIdeal b forbiddenTwo=exteriorRelationIdeal (exteriorPair (b 0) (b 1)) 0 := by
  simp only [monomialIdeal,forbiddenTwo,Set.image_singleton,exteriorRelationIdeal,
    exteriorPair_coe,TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 2)<1),
    ZeroMemClass.coe_zero]
  simp

theorem three_monomial_ideal (b : Module.Basis (Fin 3) K M) :
    monomialIdeal b forbiddenThree=
      exteriorRelationIdeal (exteriorPair (b 0) (b 1)) (exteriorPair (b 1) (b 2)) := by
  simp only [monomialIdeal,forbiddenThree,Set.image_insert_eq,Set.image_singleton,
    exteriorRelationIdeal,exteriorPair_coe,
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 3)<1),
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (1 : Fin 3)<2)]

theorem four_monomial_ideal (b : Module.Basis (Fin 4) K M) :
    monomialIdeal b forbiddenFour=
      exteriorRelationIdeal (exteriorPair (b 0) (b 1)) (exteriorPair (b 2) (b 3)) := by
  simp only [monomialIdeal,forbiddenFour,Set.image_insert_eq,Set.image_singleton,
    exteriorRelationIdeal,exteriorPair_coe,
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 4)<1),
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (2 : Fin 4)<3)]

def zero_normal_form (b : Module.Basis (Fin 0) K M) :
    HomogeneousKoszulCertificate (K := K) (0 : ⋀[K]^2 M) 0 :=
  certificateOfFiniteMonomialIdeal b ∅ (by simp) (relationEmpty (Fin 0))
    (empty_increasing (Fin 0)) zero_words 0 0 (empty_monomial_ideal b)

def one_normal_form (b : Module.Basis (Fin 1) K M) :
    HomogeneousKoszulCertificate (K := K) (0 : ⋀[K]^2 M) 0 :=
  certificateOfFiniteMonomialIdeal b ∅ (by simp) (relationEmpty (Fin 1))
    (empty_increasing (Fin 1)) one_words 0 0 (empty_monomial_ideal b)

def two_normal_form (b : Module.Basis (Fin 2) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (0 : ⋀[K]^2 M) :=
  certificateOfFiniteMonomialIdeal b forbiddenTwo two_nonempty (relationEmpty (Fin 2))
    (empty_increasing (Fin 2)) two_words _ _ (two_monomial_ideal b)

def three_normal_form (b : Module.Basis (Fin 3) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (exteriorPair (b 1) (b 2)) :=
  certificateOfFiniteMonomialIdeal b forbiddenThree three_nonempty relationThree
    three_increasing three_words _ _ (three_monomial_ideal b)

def four_normal_form (b : Module.Basis (Fin 4) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (exteriorPair (b 2) (b 3)) :=
  certificateOfFiniteMonomialIdeal b forbiddenFour four_nonempty relationFour
    four_increasing four_words _ _ (four_monomial_ideal b)

variable [FiniteDimensional K M]

/-- All two-forms vanish below dimension two; no genericity restriction is
needed for either of these boundary algebras. -/
theorem dimension_le_one (hdim : Module.finrank K M≤1) (f g : ⋀[K]^2 M) :
    Nonempty (HomogeneousKoszulCertificate f g) := by
  have hz : Module.finrank K (⋀[K]^2 M)=0 := by
    rw [exteriorPower.finrank_eq]
    exact Nat.choose_eq_zero_of_lt (by omega)
  letI : Subsingleton (⋀[K]^2 M) := (Module.finrank_zero_iff).mp hz
  have hf : f=0 := Subsingleton.elim _ _
  have hg : g=0 := Subsingleton.elim _ _
  subst f
  subst g
  rcases Nat.eq_zero_or_pos (Module.finrank K M) with h0 | h1
  · exact ⟨zero_normal_form (Module.finBasisOfFinrankEq K M h0)⟩
  · have h1' : Module.finrank K M=1 := by omega
    exact ⟨one_normal_form (Module.finBasisOfFinrankEq K M h1')⟩

/-- Every pair in dimension two with nonzero first form has the same
actual relation ideal as the single top exterior monomial. -/
theorem dimension_two (hdim : Module.finrank K M=2) (f g : ⋀[K]^2 M) (hf : f≠0) :
    Nonempty (HomogeneousKoszulCertificate f g) := by
  let b := Module.finBasisOfFinrankEq K M hdim
  let q : ⋀[K]^2 M := exteriorPair (b 0) (b 1)
  have hq : q≠0 := by
    apply (exteriorPower.ιMulti_ne_zero_iff ![b 0,b 1]).mpr
    convert b.linearIndependent using 1
    funext i
    fin_cases i <;> rfl
  have hdim2 : Module.finrank K (⋀[K]^2 M)=1 := by
    rw [exteriorPower.finrank_eq,hdim]
    decide
  have hfspan : Submodule.span K ({f} : Set (⋀[K]^2 M))=⊤ :=
    (finrank_eq_one_iff_of_nonzero f hf).mp hdim2
  have hqspan : Submodule.span K ({q} : Set (⋀[K]^2 M))=⊤ :=
    (finrank_eq_one_iff_of_nonzero q hq).mp hdim2
  have hpair (x y : ⋀[K]^2 M) (hx : Submodule.span K ({x} : Set (⋀[K]^2 M))=⊤) :
      Submodule.span K ({x,y} : Set (⋀[K]^2 M))=⊤ := by
    apply top_unique
    rw [←hx]
    exact Submodule.span_mono (by intro a ha; exact Or.inl (Set.mem_singleton_iff.mp ha))
  have hs : Submodule.span K ({f,g} : Set (⋀[K]^2 M))=
      Submodule.span K ({q,0} : Set (⋀[K]^2 M)) :=
    (hpair f g hfspan).trans (hpair q 0 hqspan).symm
  have he : monomialIdeal b forbiddenTwo=exteriorRelationIdeal f g :=
    (two_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq f g q 0 hs).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenTwo two_nonempty (relationEmpty (Fin 2))
    (empty_increasing (Fin 2)) two_words f g he⟩

/-- The nonzero first coordinate is a genuine nonempty principal open
in the full two-dimensional coefficient space of a pair of two-forms. -/
theorem dimension_two_generic (hdim : Module.finrank K M=2) :
    ∃ b₂ : Module.Basis (Fin 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 1 ⊕ Fin 1) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  have hd : Module.finrank K (⋀[K]^2 M)=1 := by
    rw [exteriorPower.finrank_eq,hdim]
    decide
  let b₂ := Module.finBasisOfFinrankEq K (⋀[K]^2 M) hd
  let Q : MvPolynomial (Fin 1 ⊕ Fin 1) K := MvPolynomial.X (.inl 0)
  refine ⟨b₂,Q,MvPolynomial.X_ne_zero _,?_,?_⟩
  · refine ⟨fun _ => 1,?_⟩
    simpa only [Q,MvPolynomial.eval_X] using (one_ne_zero : (1 : K)≠0)
  · intro y hy
    have hy0 : y (.inl 0)≠0 := by simpa only [Q,MvPolynomial.eval_X] using hy
    apply dimension_two hdim
    have hf : (orbitFormsFromCoordinates b₂ y).1=y (.inl 0) • b₂ 0 := by
      simp [orbitFormsFromCoordinates]
    rw [hf]
    exact smul_ne_zero hy0 (b₂.ne_zero 0)

/-- The complete generic positive result in dimension three, on an
explicit nonempty principal open in the full space of pairs. -/
theorem dimension_three (hdim : Module.finrank K M=3) :
    ∃ b₂ : Module.Basis (Fin 3) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 3 ⊕ Fin 3) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := ThreeNormalForm.generic_normal_form (K := K) (M := M) hdim
  refine ⟨b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := h y hy
  have he : monomialIdeal b forbiddenThree=
      exteriorRelationIdeal (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 :=
    (three_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ hb).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenThree three_nonempty relationThree
    three_increasing three_words _ _ he⟩

/-- The complete generic positive result in dimension four. Algebraic
closure is faithful to the paper's coefficient field ℂ. -/
theorem dimension_four [CharZero K] [IsAlgClosed K]
    (hdim : Module.finrank K M=4) :
    ∃ b₂ : Module.Basis (Fin 6) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 6 ⊕ Fin 6) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := FourNormalForm.generic_normal_form (K := K) (M := M) hdim
  refine ⟨b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := h y hy
  have he : monomialIdeal b forbiddenFour=
      exteriorRelationIdeal (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 :=
    (four_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ hb).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenFour four_nonempty relationFour
    four_increasing four_words _ _ he⟩

/-- The full positive direction of Proposition 5.3: every dimension at
most four, an actual basis of all quadratic forms, a nonempty principal
open in the complete pair space, and genuine ordinary-Tor concentration
in the original exterior grading at every point of that open. -/
theorem paper_proposition_5_3_koszul_small [CharZero K] [IsAlgClosed K]
    (hdim : Module.finrank K M≤4) :
    ∃ m : ℕ,∃ b₂ : Module.Basis (Fin m) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin m ⊕ Fin m) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  by_cases h1 : Module.finrank K M≤1
  · have hd : Module.finrank K (⋀[K]^2 M)=0 := by
      rw [exteriorPower.finrank_eq]
      exact Nat.choose_eq_zero_of_lt (by omega)
    let b₂ := Module.finBasisOfFinrankEq K (⋀[K]^2 M) hd
    refine ⟨0,b₂,1,one_ne_zero,?_,?_⟩
    · refine ⟨fun _ => 0,?_⟩
      rw [map_one]
      exact one_ne_zero
    · intro y hy
      exact dimension_le_one h1 _ _
  · by_cases h2 : Module.finrank K M=2
    · obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_two_generic (K := K) (M := M) h2
      exact ⟨1,b₂,Q,hQ,hpoint,h⟩
    · by_cases h3 : Module.finrank K M=3
      · obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_three (K := K) (M := M) h3
        exact ⟨3,b₂,Q,hQ,hpoint,h⟩
      · have h4 : Module.finrank K M=4 := by omega
        obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_four (K := K) (M := M) h4
        exact ⟨6,b₂,Q,hQ,hpoint,h⟩

end PaperVerification.AlternatingForms.SmallExteriorKoszul
end
end
end TAF_LiteralSource_0501

section TAF_LiteralSource_0502
/- Original module: PaperVerification.KoszulHilbertObstruction -/


/-!
# The dimension-five reciprocal obstruction

This is the exact numerical step used in Proposition 5.3.  It concerns
ordinary formal power series over the integers.  Any inverse of
`1 - 5t + 8t² - t³` has coefficient `-26` in degree six, and consequently
cannot be a series of dimensions.  The recurrence is obtained from the
actual coefficient formula for multiplication, rather than a numerical
experiment or a truncated inverse accepted as a hypothesis.

This supporting result does not assert the Koszul identity or identify a
series with Tor.  Those are separate homological proof obligations.  This
source remains a candidate until its complete proof is checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.KoszulHilbertObstruction

def dimensionFiveSignedHilbert : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => if d=0 then 1 else if d=1 then -5 else
    if d=2 then 8 else if d=3 then -1 else 0)

theorem inverse_coefficient_six (F : ℤ⟦X⟧)
    (hF : dimensionFiveSignedHilbert*F=1) : PowerSeries.coeff 6 F = -26 := by
  have hc (d : ℕ) :
      (∑ i ∈ Finset.range (d+1),
        PowerSeries.coeff i dimensionFiveSignedHilbert*PowerSeries.coeff (d-i) F)=
          if d=0 then 1 else 0 := by
    have h := congrArg (PowerSeries.coeff d) hF
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i dimensionFiveSignedHilbert*PowerSeries.coeff j F) d,
      PowerSeries.coeff_one] at h
    exact h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  norm_num [dimensionFiveSignedHilbert,PowerSeries.coeff_mk,
    Finset.sum_range_succ] at h0 h1 h2 h3 h4 h5 h6
  omega

theorem no_nonnegative_inverse (F : ℤ⟦X⟧)
    (hF : dimensionFiveSignedHilbert*F=1)
    (hnonnegative : ∀ d,0≤PowerSeries.coeff d F) : False := by
  have h6 := inverse_coefficient_six F hF
  have hpos := hnonnegative 6
  omega

end PaperVerification.KoszulHilbertObstruction
end
end
end TAF_LiteralSource_0502

section TAF_LiteralSource_0503
/- Original module: PaperVerification.KoszulBarObstruction -/


/-!
# Exact homological and series obstructions in Proposition 5.3

The dimension-five result forces nonzero off-diagonal homology in the
actual internal-degree-six bar complex. Its input is the independently
specified positive basis-degree series; its terms and differential are the
actual noncommutative bar construction, not a proposed inverse series.

The independent formal-series lemma excludes the Koszul identity when a
bounded series and the stated PBW denominator are given. It is not a
claim of the full Koszul classification: identification of diagonal bar
homology with the quadratic dual and the small-dimensional positive cases
remain separate proof obligations. This file is a candidate until checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries
open CategoryTheory CategoryTheory.Limits

namespace PaperVerification.KoszulBarObstruction

universe u

open PaperVerification.WeightedBarEuler PaperVerification.KoszulHilbertObstruction

def dimensionFivePositiveSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => if d=1 then 5 else if d=2 then 8 else if d=3 then 1 else 0)

theorem dimensionFive_signed_rescale :
    PowerSeries.rescale (-1 : ℤ) (1+dimensionFivePositiveSeries)=
      dimensionFiveSignedHilbert := by
  apply PowerSeries.ext
  intro d
  by_cases h0 : d=0
  · subst d
    rw [PowerSeries.coeff_rescale]
    norm_num [dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h1 : d=1
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h2 : d=2
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  by_cases h3 : d=3
  · subst d
    norm_num [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert]
  simp [PowerSeries.coeff_rescale,dimensionFivePositiveSeries,dimensionFiveSignedHilbert,
    h0,h1,h2,h3]

theorem dimensionFive_euler_coefficient_six :
    PowerSeries.coeff 6 (eulerSeries dimensionFivePositiveSeries) = -26 := by
  have h0 : PowerSeries.coeff 0 dimensionFivePositiveSeries=0 := by
    simp [dimensionFivePositiveSeries]
  have h := congrArg (PowerSeries.rescale (-1 : ℤ))
    (one_add_mul_eulerSeries dimensionFivePositiveSeries h0)
  rw [map_mul,dimensionFive_signed_rescale,map_one] at h
  have h6 := inverse_coefficient_six _ h
  simpa only [PowerSeries.coeff_rescale,show (-1 : ℤ)^6=1 by norm_num,one_mul] using h6

/-- The negative Euler coefficient forces actual lower-length homology;
no vanishing or Koszul identity is assumed in this conclusion. -/
theorem dimensionFive_complex_off_diagonal
    {K : Type*} [Field K] (C : ChainComplex (ModuleCat K) ℕ)
    (hfinite : ∀ r, r≤6 → Module.Finite K (C.X r))
    (hboundary : C.d 7 6=0)
    (hterm : ∀ r, r≤6 → (Module.finrank K (C.X r) : ℤ)=
      PowerSeries.coeff 6 (dimensionFivePositiveSeries^r)) :
    ∃ r, r<6 ∧ ¬IsZero (C.homology r) := by
  by_contra h
  have hz (r : ℕ) (hr : r<6) : IsZero (C.homology r) := by
    by_contra hn
    exact h ⟨r,hr,hn⟩
  have ht : (∑ r∈Finset.range 7,(-1 : ℤ)^r*(Module.finrank K (C.X r) : ℤ)) = -26 := by
    calc
      _ = PowerSeries.coeff 6 (eulerSeries dimensionFivePositiveSeries) := by
        simp only [eulerSeries,PowerSeries.coeff_mk]
        apply Finset.sum_congr rfl
        intro r hr
        rw [hterm r (by have := Finset.mem_range.mp hr; omega)]
      _ = -26 := dimensionFive_euler_coefficient_six
  have hh : (∑ r∈Finset.range 7,(-1 : ℤ)^r*(Module.finrank K (C.homology r) : ℤ)) =
      (Module.finrank K (C.homology 6) : ℤ) := by
    rw [Finset.sum_eq_single 6]
    · norm_num
    · intro r hr hne
      rw [ModuleCat.finrank_eq_zero_of_isZero (hz r (by
        have := Finset.mem_range.mp hr
        omega)),Nat.cast_zero,mul_zero]
    · intro h6
      exact (h6 (by simp)).elim
  have he := C.sum_range_finrank_X_eq_sum_range_finrank_homology hfinite hboundary
  rw [ht,hh] at he
  have hnonnegative : (0 : ℤ)≤(Module.finrank K (C.homology 6) : ℤ) :=
    Int.natCast_nonneg _
  omega

set_option maxHeartbeats 800000 in
/-- The preceding obstruction for the actual noncommutative reduced bar
complex, using the real original homogeneous basis degrees. -/
theorem dimensionFive_actual_bar_off_diagonal
    {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
    (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
    (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
    (δ : I → ℕ)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 →
      δ c=δ a+δ b)
    (hpos : ∀ i,0<δ i)
    (hseries : WeightedBar.positiveSeries δ=dimensionFivePositiveSeries) :
    let C : ChainComplex (ModuleCat K) ℕ :=
      WeightedBar.internalComplex (K := K) (A := A) (I := I) ε B hunit hε δ hδ 6
    ∃ r,r<6 ∧ ¬IsZero (C.homology r) := by
  let C : ChainComplex (ModuleCat K) ℕ :=
    WeightedBar.internalComplex (K := K) (A := A) (I := I) ε B hunit hε δ hδ 6
  have hf : ∀ r,r≤6 → Module.Finite K (C.X r) := fun r _ =>
    WeightedBar.pieceFinite (K := K) (I := I) δ r 6
  have hb : C.d 7 6=0 :=
    WeightedBar.internalComplex_top_differential (K := K) ε B hunit hε δ hδ hpos 6
  have ht : ∀ r,r≤6 → (Module.finrank K (C.X r) : ℤ)=
      PowerSeries.coeff 6 (dimensionFivePositiveSeries^r) := by
    intro r hr
    exact (WeightedBar.internalComplex_term_rank (K := K)
      ε B hunit hε δ hδ r 6).trans (congrArg (fun P : ℤ⟦X⟧ =>
        PowerSeries.coeff 6 (P^r)) hseries)
  exact dimensionFive_complex_off_diagonal C hf hb ht

theorem coeff_one_add_X_pow (n d : ℕ) :
    PowerSeries.coeff d ((1+PowerSeries.X)^n : ℤ⟦X⟧)=(n.choose d : ℤ) := by
  have hp : ((1+PowerSeries.X)^n : ℤ⟦X⟧)=
      (((1+Polynomial.X)^n : Polynomial ℤ) : ℤ⟦X⟧) := by simp
  rw [hp,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

/-- The exact impossible coefficient above the exterior degree ceiling. -/
theorem proposedKoszulPolynomial_top (n : ℕ) :
    PowerSeries.coeff (n+4)
      (((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2) : ℤ⟦X⟧)=1 := by
  let A : ℤ⟦X⟧ := (1+PowerSeries.X)^n
  have hhigh : PowerSeries.coeff (n+4) A=0 := by
    dsimp only [A]
    rw [coeff_one_add_X_pow,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
  have hmid : PowerSeries.coeff (n+2) A=0 := by
    dsimp only [A]
    rw [coeff_one_add_X_pow,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
  have hself : PowerSeries.coeff n A=1 := by simp [A,coeff_one_add_X_pow]
  have htwo : PowerSeries.coeff (n+4) (A*PowerSeries.X^2)=0 := by
    rw [show n+4=(n+2)+2 by omega,PowerSeries.coeff_mul_X_pow,hmid]
  have hfour : PowerSeries.coeff (n+4) (A*PowerSeries.X^4)=1 := by
    rw [PowerSeries.coeff_mul_X_pow,hself]
  have hexp : A*(1-PowerSeries.X^2)^2=
      A-(A*PowerSeries.X^2+A*PowerSeries.X^2)+A*PowerSeries.X^4 := by ring
  change PowerSeries.coeff (n+4) (A*(1-PowerSeries.X^2)^2)=1
  rw [hexp,map_add,map_sub,map_add,hhigh,htwo,hfour]
  norm_num

/-- The PBW denominator and a bounded exterior Hilbert function cannot
satisfy the Koszul identity, in any dimension in which that denominator holds. -/
theorem no_bounded_koszul_identity (n : ℕ) (H D : ℤ⟦X⟧)
    (hH : PowerSeries.coeff (n+4) H=0)
    (hD : D*((1-PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1) :
    H*PowerSeries.rescale (-1 : ℤ) D≠1 := by
  intro hKoszul
  have hdual : PowerSeries.rescale (-1 : ℤ) D*
      ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1 := by
    have h := congrArg (PowerSeries.rescale (-1 : ℤ)) hD
    simpa only [map_mul,map_pow,map_sub,map_one,PowerSeries.rescale_neg_one_X,
      neg_sq,sub_neg_eq_add] using h
  have he : H=(1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2 := by
    calc
      H=H*1 := (mul_one H).symm
      _=H*(PowerSeries.rescale (-1 : ℤ) D*
          ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2)) := by rw [hdual]
      _=(H*PowerSeries.rescale (-1 : ℤ) D)*
          ((1+PowerSeries.X)^n*(1-PowerSeries.X^2)^2) := (mul_assoc _ _ _).symm
      _=_ := by rw [hKoszul,one_mul]
  have hc := congrArg (PowerSeries.coeff (n+4)) he
  rw [hH,proposedKoszulPolynomial_top] at hc
  exact zero_ne_one hc

end PaperVerification.KoszulBarObstruction
end
end
end TAF_LiteralSource_0503

section TAF_LiteralSource_0504
/- Original module: PaperVerification.DimensionFiveGradedBasis -/


/-!
# A genuine homogeneous augmented basis for the dimension-five Hilbert profile

The grading is supplied independently as an internal direct sum in an actual
algebra. The basis is assembled from its genuine homogeneous components;
its product coefficients are proved homogeneous from multiplication in that
algebra. The resulting obstruction lies in ordinary augmentation Tor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.DimensionFiveGradedBasis

universe u

abbrev rankProfile : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | 2 => 8
  | 3 => 1
  | _+4 => 0

abbrev PositiveIndex := ULift.{u} (Fin 5 ⊕ (Fin 8 ⊕ Fin 1))

def positiveDegree : PositiveIndex.{u} → ℕ
  | ⟨.inl _⟩ => 1
  | ⟨.inr (.inl _)⟩ => 2
  | ⟨.inr (.inr _)⟩ => 3

theorem positiveDegree_pos (i : PositiveIndex.{u}) : 0<positiveDegree i := by
  rcases i with ⟨i | i | i⟩ <;> simp only [positiveDegree] <;> omega

def indexEquiv : (Σ d,Fin (rankProfile d)) ≃ Option PositiveIndex.{u} where
  toFun
    | ⟨0,_⟩ => none
    | ⟨1,i⟩ => some ⟨.inl i⟩
    | ⟨2,i⟩ => some ⟨.inr (.inl i)⟩
    | ⟨3,i⟩ => some ⟨.inr (.inr i)⟩
    | ⟨_+4,i⟩ => Fin.elim0 i
  invFun
    | none => ⟨0,0⟩
    | some ⟨.inl i⟩ => ⟨1,i⟩
    | some ⟨.inr (.inl i)⟩ => ⟨2,i⟩
    | some ⟨.inr (.inr i)⟩ => ⟨3,i⟩
  left_inv := by
    rintro ⟨d,i⟩
    rcases d with _ | _ | _ | _ | d
    · have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
    · rfl
    · rfl
    · exact Fin.elim0 i
  right_inv := by
    rintro (_ | ⟨i | i | i⟩) <;> rfl

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (hzero : G.piece 0=(1 : Submodule K A))

/-- The degree-zero isomorphism is the actual scalar inclusion. -/
def scalarPieceMap : K →ₗ[K] G.piece 0 :=
  LinearMap.codRestrict _ (Algebra.ofId K A).toLinearMap (fun c => by
    rw [hzero]
    exact Submodule.mem_one.mpr ⟨c,rfl⟩)

@[simp] theorem scalarPieceMap_val (c : K) :
    (scalarPieceMap G hzero c).val=algebraMap K A c := rfl

def scalarPieceEquiv : K ≃ₗ[K] G.piece 0 :=
  LinearEquiv.ofBijective (scalarPieceMap G hzero) (by
    constructor
    · intro c d h
      have he := congrArg (fun x : G.piece 0 => ε x.val) h
      simpa only [scalarPieceMap_val,AlgHom.commutes,Algebra.algebraMap_self,
        RingHom.id_apply] using he
    · intro x
      have hx : x.val∈(1 : Submodule K A) := hzero ▸ x.property
      obtain ⟨c,hc⟩ := Submodule.mem_one.mp hx
      exact ⟨c,Subtype.ext hc⟩)

@[simp] theorem scalarPieceEquiv_val (c : K) :
    (scalarPieceEquiv G ε hzero c).val=algebraMap K A c := rfl

variable [∀ d,Module.Finite K (G.piece d)]
  (hprofile : ∀ d,Module.finrank K (G.piece d)=rankProfile d)

def degreeBasis : (d : ℕ) → Module.Basis (Fin (rankProfile d)) K (G.piece d)
  | 0 => (Module.Basis.singleton (Fin 1) K).map (scalarPieceEquiv G ε hzero)
  | d+1 => Module.finBasisOfFinrankEq K (G.piece (d+1)) (hprofile (d+1))

def basis : Module.Basis (Option PositiveIndex.{u}) K A :=
  (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)).reindex indexEquiv

theorem basis_none : basis G ε hzero hprofile none=1 := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  change ((degreeBasis G ε hzero hprofile 0) 0 : A)=1
  simp only [degreeBasis,Module.Basis.map_apply,Module.Basis.singleton_apply,
    scalarPieceEquiv_val,map_one]

theorem basis_positive_mem (i : PositiveIndex.{u}) :
    basis G ε hzero hprofile (some i)∈G.piece (positiveDegree i) := by
  rw [basis,Module.Basis.reindex_apply]
  rcases i with ⟨i | i | i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨1,i⟩∈G.piece 1
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨1,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨2,i⟩∈G.piece 2
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨2,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨3,i⟩∈G.piece 3
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨3,i⟩

theorem basis_repr_of_mem_ne {d : ℕ} {x : A} (hx : x∈G.piece d)
    (i : PositiveIndex.{u}) (hi : d≠positiveDegree i) :
    (basis G ε hzero hprofile).repr x (some i)=0 := by
  rw [basis,Module.Basis.repr_reindex_apply]
  rcases i with ⟨i | i | i⟩ <;>
    exact G.isInternal.collectedBasis_repr_of_mem_ne
      (degreeBasis G ε hzero hprofile) hi hx

variable (hε : ∀ d,0<d → ∀ x,x∈G.piece d → ε x=0)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hε in
theorem basis_positive_augmentation (i : PositiveIndex.{u}) :
    ε (basis G ε hzero hprofile (some i))=0 :=
  hε _ (positiveDegree_pos i) _ (basis_positive_mem G ε hzero hprofile i)

include hmul in
theorem product_homogeneous (a b c : PositiveIndex.{u})
    (h : AugmentedAlgebraBasis.productCoefficients (basis G ε hzero hprofile) a b c≠0) :
    positiveDegree c=positiveDegree a+positiveDegree b := by
  by_contra hc
  apply h
  change (basis G ε hzero hprofile).repr
    (basis G ε hzero hprofile (some a)*basis G ε hzero hprofile (some b)) (some c)=0
  exact basis_repr_of_mem_ne G ε hzero hprofile
    (hmul _ _ _ _ (basis_positive_mem G ε hzero hprofile a)
      (basis_positive_mem G ε hzero hprofile b)) c (Ne.symm hc)

theorem positiveSeries_eq :
    WeightedBar.positiveSeries positiveDegree.{u}=KoszulBarObstruction.dimensionFivePositiveSeries := by
  have he : WeightedBar.positiveSeries positiveDegree.{u}=
      5 • (PowerSeries.X : ℤ⟦X⟧)+8 • PowerSeries.X^2+PowerSeries.X^3 := by
    change (∑ i : PositiveIndex.{u},PowerSeries.X^(positiveDegree i))=_
    calc
      _ = ∑ i : Fin 5 ⊕ (Fin 8 ⊕ Fin 1),
          (PowerSeries.X : ℤ⟦X⟧)^(positiveDegree (ULift.up i : PositiveIndex.{u})) :=
        Fintype.sum_equiv (Equiv.ulift : PositiveIndex.{u} ≃ _) _ _ (fun _ => rfl)
      _ = _ := by simp [Fintype.sum_sum_type,positiveDegree,add_assoc]
  rw [he]
  apply PowerSeries.ext
  intro d
  rw [map_add,map_add,map_nsmul,map_nsmul]
  rw [←pow_one (PowerSeries.X : ℤ⟦X⟧)]
  simp only [PowerSeries.coeff_X_pow,KoszulBarObstruction.dimensionFivePositiveSeries,
    PowerSeries.coeff_mk]
  split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
/-- The degree-six obstruction survives as a nonzero subspace of ordinary Tor. -/
theorem ordinaryTor_off_diagonal :
    ∃ r,r<6 ∧ WeightedBar.torPiece ε (basis G ε hzero hprofile)
      (basis_none G ε hzero hprofile)
      (basis_positive_augmentation G ε hzero hprofile hε)
      positiveDegree (product_homogeneous G ε hzero hprofile hmul) r 6≠⊥ := by
  obtain ⟨r,hr,hn⟩ := KoszulBarObstruction.dimensionFive_actual_bar_off_diagonal
    ε (basis G ε hzero hprofile) (basis_none G ε hzero hprofile)
      (basis_positive_augmentation G ε hzero hprofile hε)
      positiveDegree (product_homogeneous G ε hzero hprofile hmul)
      positiveDegree_pos positiveSeries_eq
  refine ⟨r,hr,?_⟩
  intro hz
  exact hn ((WeightedBar.torPiece_eq_bot_iff ε (basis G ε hzero hprofile)
    (basis_none G ε hzero hprofile)
    (basis_positive_augmentation G ε hzero hprofile hε)
    positiveDegree (product_homogeneous G ε hzero hprofile hmul) r 6).mp hz)

end PaperVerification.DimensionFiveGradedBasis
end
end
end TAF_LiteralSource_0504

section TAF_LiteralSource_0505
/- Original module: PaperVerification.HomogeneousBasisProfile -/


/-!
# The positive Hilbert series is independent of a homogeneous basis

Actual projections in an internal grading show that the vectors of any
homogeneous basis of a fixed degree form a basis of that genuine graded
piece. Thus the dimension-five ordinary Tor obstruction holds for every
homogeneous augmented basis, rather than only for the chosen construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.HomogeneousBasisProfile

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))

def projection (d : ℕ) : A →ₗ[K] A :=
  (G.piece d).subtype.comp
    ((DirectSum.component K ℕ (fun j => G.piece j) d).comp
      (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap)

@[simp] theorem projection_apply (d : ℕ) (x : A) :
    projection G d x=(DirectSum.decompose G.piece x d : A) := rfl

theorem projection_self {d : ℕ} {x : A} (hx : x∈G.piece d) :
    projection G d x=x := DirectSum.decompose_of_mem_same G.piece hx

include hzero hunit in
theorem projection_none (d : ℕ) (hd : 0<d) : projection G d (B none)=0 := by
  apply DirectSum.decompose_of_mem_ne G.piece (i := 0)
  · rw [hunit,hzero]
    exact Submodule.mem_one.mpr ⟨1,map_one _⟩
  · omega

include hhom in
theorem projection_positive (d : ℕ) (i : I) :
    projection G d (B (some i))=if δ i=d then B (some i) else 0 := by
  by_cases hi : δ i=d
  · rw [if_pos hi]
    exact DirectSum.decompose_of_mem_same G.piece (hi ▸ hhom i)
  · rw [if_neg hi]
    exact DirectSum.decompose_of_mem_ne G.piece (hhom i) hi

include hzero hunit hhom in
/-- The positive vectors in degree d span exactly the original degree-d piece. -/
theorem span_degree (d : ℕ) (hd : 0<d) :
    Submodule.span K (Set.range (fun i : {i : I // δ i=d} => B (some i.val)))=G.piece d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change B (some i.val)∈G.piece d
    exact Eq.mp (congrArg (fun n : ℕ => B (some i.val)∈G.piece n) i.property)
      (hhom i.val)
  · intro x hx
    rw [←projection_self G hx,←B.sum_repr x,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    cases i with
    | none =>
        rw [projection_none G B hzero hunit d hd,smul_zero]
        exact Submodule.zero_mem _
    | some i =>
        rw [projection_positive G B δ hhom]
        split_ifs with he
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i,he⟩,rfl⟩)
        · rw [smul_zero]
          exact Submodule.zero_mem _

include hzero hunit hhom in
theorem card_degree (d : ℕ) (hd : 0<d) :
    Fintype.card {i : I // δ i=d}=Module.finrank K (G.piece d) := by
  rw [←span_degree G B δ hzero hunit hhom d hd]
  exact (finrank_span_eq_card (B.linearIndependent.comp
    (fun i : {i : I // δ i=d} => some i.val)
    (fun i j h => Subtype.ext (Option.some.inj h)))).symm

theorem coeff_positiveSeries (d : ℕ) :
    PowerSeries.coeff d (WeightedBar.positiveSeries δ)=
      (Fintype.card {i : I // δ i=d} : ℤ) := by
  simp only [WeightedBar.positiveSeries,map_sum,PowerSeries.coeff_X_pow]
  rw [show (∑ i : I,if d=δ i then (1 : ℤ) else 0)=
      ∑ i : I,if δ i=d then (1 : ℤ) else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eq_comm]]
  simp only [Finset.sum_boole,Fintype.card_subtype]

variable (hpos : ∀ i,0<δ i)
  (hprofile : ∀ d,Module.finrank K (G.piece d)=DimensionFiveGradedBasis.rankProfile d)

include hzero hunit hhom hpos hprofile in
theorem positiveSeries_eq_dimensionFive :
    WeightedBar.positiveSeries δ=KoszulBarObstruction.dimensionFivePositiveSeries := by
  apply PowerSeries.ext
  intro d
  by_cases hd : d=0
  · subst d
    have hn : ∀ i,δ i≠0 := fun i => Nat.ne_of_gt (hpos i)
    simp [coeff_positiveSeries,KoszulBarObstruction.dimensionFivePositiveSeries,hn]
  · have hdpos : 0<d := Nat.pos_of_ne_zero hd
    rw [coeff_positiveSeries,card_degree G B δ hzero hunit hhom d hdpos,hprofile]
    rcases d with _ | _ | _ | _ | d <;>
      simp_all [DimensionFiveGradedBasis.rankProfile,
        KoszulBarObstruction.dimensionFivePositiveSeries]

variable (ε : A →ₐ[K] K) (hε : ∀ i,ε (B (some i))=0)
  (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hzero hhom hpos hprofile in
set_option maxHeartbeats 800000 in
/-- Every actual homogeneous augmented basis gives nonzero off-diagonal
ordinary Tor. Thus choosing another basis cannot remove the obstruction. -/
theorem every_basis_ordinaryTor_off_diagonal :
    ∃ r,r<6 ∧ WeightedBar.torPiece ε B hunit hε δ hδ r 6≠⊥ := by
  obtain ⟨r,hr,hn⟩ := KoszulBarObstruction.dimensionFive_actual_bar_off_diagonal
    ε B hunit hε δ hδ hpos
    (positiveSeries_eq_dimensionFive G B δ hzero hunit hhom hpos hprofile)
  exact ⟨r,hr,fun hz => hn ((WeightedBar.torPiece_eq_bot_iff
    ε B hunit hε δ hδ r 6).mp hz)⟩

include hzero hhom hpos hprofile in
set_option maxHeartbeats 800000 in
theorem not_hasDiagonalTor : ¬WeightedBar.HasDiagonalTor ε B hunit hε δ hδ := by
  intro hdiag
  obtain ⟨r,hr,hn⟩ := every_basis_ordinaryTor_off_diagonal
    G B δ hzero hunit hhom hpos hprofile ε hε hδ
  exact hn (hdiag r 6 (Nat.ne_of_lt hr))

end PaperVerification.HomogeneousBasisProfile
end
end
end TAF_LiteralSource_0505

section TAF_LiteralSource_0506
/- Original module: PaperVerification.AlternatingFormsDimensionFiveKoszul -/


/-!
# The actual dimension-five negative case of Proposition 5.3

One principal open in the full space of pairs has the proved homogeneous
ranks (1,5,8,1). Its actual exterior quotient therefore has nonzero ordinary
Tor in internal degree six and homological degree strictly below six.
The augmented basis and every compatibility with the original exterior
grading are constructed here; none is added as a genericity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.DimensionFiveKoszul

open DimensionFiveGradedBasis ExteriorAugmented

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Independently specified graded data and an actual nonzero ordinary Tor
piece. The basis's degrees are the original exterior degrees. -/
structure OriginalDegreeSixTorObstruction (f g : ⋀[K]^2 M) where
  basis : Module.Basis (Option PositiveIndex.{u}) K (ExteriorAugmented.Quotient f g)
  unit : basis none=1
  homogeneous : ∀ i,basis (some i)∈(grading f g).piece (positiveDegree i)
  augmentation_zero : ∀ i,augmentation f g (basis (some i))=0
  product_degree : ∀ a b c,AugmentedAlgebraBasis.productCoefficients basis a b c≠0 →
    positiveDegree c=positiveDegree a+positiveDegree b
  ordinaryTor_nonzero : ∃ r,r<6 ∧
    WeightedBar.torPiece (augmentation f g) basis unit augmentation_zero
      positiveDegree product_degree r 6≠⊥

/-- Failure of ordinary Tor concentration for every finite homogeneous
augmented basis compatible with the actual exterior grading. This is
universally quantified data, not a choice assumed at the principal open. -/
def EveryHomogeneousBasisHasOffDiagonalTor (f g : ⋀[K]^2 M) : Prop :=
  ∀ (I : Type u) [Fintype I]
    (B : Module.Basis (Option I) K (ExteriorAugmented.Quotient f g))
    (hunit : B none=1) (δ : I → ℕ) (hpos : ∀ i,0<δ i)
    (hhom : ∀ i,B (some i)∈(grading f g).piece (δ i))
    (hε : ∀ i,augmentation f g (B (some i))=0)
    (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b),
    ¬WeightedBar.HasDiagonalTor (augmentation f g) B hunit hε δ hδ

variable [FiniteDimensional K M] (f g : ⋀[K]^2 M)

def obstructionOfHilbertProfile
    (h : ∀ d,Module.finrank K (ExteriorQuotientDegree f g d)=rankProfile d) :
    OriginalDegreeSixTorObstruction f g := by
  let hp : ∀ d,Module.finrank K ((grading f g).piece d)=rankProfile d :=
    fun d => (grading_piece_finrank f g d).trans (h d)
  exact {
    basis := DimensionFiveGradedBasis.basis (grading f g) (augmentation f g)
      (grading_zero f g) hp
    unit := basis_none (grading f g) (augmentation f g) (grading_zero f g) hp
    homogeneous := basis_positive_mem (grading f g) (augmentation f g) (grading_zero f g) hp
    augmentation_zero := basis_positive_augmentation (grading f g) (augmentation f g)
      (grading_zero f g) hp (augmentation_piece_zero f g)
    product_degree := product_homogeneous (grading f g) (augmentation f g)
      (grading_zero f g) hp (grading_mul f g)
    ordinaryTor_nonzero := ordinaryTor_off_diagonal (grading f g) (augmentation f g)
      (grading_zero f g) hp (augmentation_piece_zero f g) (grading_mul f g) }

theorem every_basis_obstructionOfHilbertProfile
    (h : ∀ d,Module.finrank K (ExteriorQuotientDegree f g d)=rankProfile d) :
    EveryHomogeneousBasisHasOffDiagonalTor f g := by
  intro I inst B hunit δ hpos hhom hε hδ
  exact HomogeneousBasisProfile.not_hasDiagonalTor
    (grading f g) B δ (grading_zero f g) hunit hhom hpos
    (fun d => (grading_piece_finrank f g d).trans (h d))
    (augmentation f g) hε hδ

/-- All natural degrees are included. Only the four low determinant
coefficients are evaluated; the remaining degrees use the proved cutoff. -/
theorem dimensionFive_walk_profile (d : ℕ) : StripWalks.paperWalkCount 5 d=rankProfile d := by
  rcases d with _ | _ | _ | _ | d
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 0 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_zero]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 1 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_one,PathDeterminant.paperMatrix]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 2 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_two,PathDeterminant.paperMatrix]
  · apply Int.natCast_inj.mp
    rw [PathDeterminant.paperWalkCount_determinant 5 3 (by decide)]
    norm_num [rankProfile,Matrix.det_fin_three,PathDeterminant.paperMatrix]
  · exact paperWalkCount_odd_above_cutoff 2 (d+4) (by omega)

/-- A certificate of diagonal ordinary Tor contradicts the obstruction
for every compatible homogeneous augmented basis. -/
theorem not_certificate_of_every_basis (h : EveryHomogeneousBasisHasOffDiagonalTor f g) :
    ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate f g) := by
  rintro ⟨C⟩
  letI : Finite C.Index := C.finite
  letI : Fintype C.Index := Fintype.ofFinite _
  exact h C.Index C.basis C.unit C.degree C.positive C.homogeneous
    C.augmentation_zero C.product_degree C.diagonal

variable [CharZero K]

/-- The full dimension-five generic negative case: the coefficient basis
covers all two-forms on every five-dimensional space, and the principal
open is proved nonempty. Every point has a nonzero off-diagonal subspace
of genuine ordinary augmentation Tor in the original exterior grading. -/
theorem paper_proposition_5_3_dimension_five (hdim : Module.finrank K M=5) :
    ∃ b₂ : Module.Basis (OddOrbitSlot 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) K,Q≠0 ∧
        (∃ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0) ∧
        ∀ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0 →
          Nonempty (OriginalDegreeSixTorObstruction
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) ∧
          EveryHomogeneousBasisHasOffDiagonalTor
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨b₂,Q,hQ,h⟩ := odd_generic_paperHilbert_in_vector_space (K := K) (M := M) 1
    (by simpa using hdim)
  refine ⟨b₂,Q,hQ,?_,?_⟩
  · by_contra hn
    apply hQ
    apply MvPolynomial.funext
    intro y
    rw [map_zero]
    by_contra hy
    exact hn ⟨y,hy⟩
  · intro y hy
    have hp : ∀ d,Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 d)=rankProfile d :=
      fun d => ((h y hy).1 d).trans (dimensionFive_walk_profile d)
    exact ⟨⟨obstructionOfHilbertProfile _ _ hp⟩,every_basis_obstructionOfHilbertProfile _ _ hp⟩

/-- The generic dimension-five quotient admits no actual homogeneous
Koszul certificate for its original exterior grading. -/
theorem paper_proposition_5_3_dimension_five_not_koszul (hdim : Module.finrank K M=5) :
    ∃ b₂ : Module.Basis (OddOrbitSlot 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) K,Q≠0 ∧
        (∃ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0) ∧
        ∀ y : (OddOrbitSlot 1 ⊕ OddOrbitSlot 1) → K,MvPolynomial.eval y Q≠0 →
          ¬Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ :=
    paper_proposition_5_3_dimension_five (K := K) (M := M) hdim
  exact ⟨b₂,Q,hQ,hpoint,fun y hy => not_certificate_of_every_basis _ _ (h y hy).2⟩

end PaperVerification.AlternatingForms.DimensionFiveKoszul
end
end
end TAF_LiteralSource_0506

section TAF_LiteralSource_0507
/- Original module: PaperVerification.HomogeneousBasisHilbert -/


/-!
# Intrinsic Hilbert series from every actual homogeneous augmented basis

The coefficient comparison uses genuine homogeneous pieces of the given
internal grading. It therefore makes no basis choice part of the Hilbert
series, and it includes degree zero through the actual augmentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.HomogeneousBasisHilbert

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)

def series : PowerSeries ℤ := PowerSeries.mk (fun d => (Module.finrank K (G.piece d) : ℤ))

include ε hzero in
theorem degree_zero_finrank : Module.finrank K (G.piece 0)=1 := by
  have he := (DimensionFiveGradedBasis.scalarPieceEquiv G ε hzero).finrank_eq
  simpa only [Module.finrank_self] using he.symm

include ε hzero hunit hhom hpos in
theorem one_add_positiveSeries_eq : 1+WeightedBar.positiveSeries δ=series G := by
  apply PowerSeries.ext
  intro d
  rw [map_add,PowerSeries.coeff_one,HomogeneousBasisProfile.coeff_positiveSeries,
    series,PowerSeries.coeff_mk]
  by_cases hd : d=0
  · subst d
    have hn : ∀ i,δ i≠0 := fun i => Nat.ne_of_gt (hpos i)
    simp [hn,degree_zero_finrank G ε hzero]
  · rw [HomogeneousBasisProfile.card_degree G B δ hzero hunit hhom d (Nat.pos_of_ne_zero hd)]
    simp [hd]

end PaperVerification.HomogeneousBasisHilbert
end
end
end TAF_LiteralSource_0507

