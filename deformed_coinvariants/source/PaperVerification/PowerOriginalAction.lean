module

public import PaperVerification.PowerOriginalBasis
public import PaperVerification.PowerPermutationAction
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Equivariant transport to the original power operators

The diagonal conjugation has weights fixed by every coefficient-preserving
permutation. It commutes with each homogeneous projection, as does its inverse.
Thus its actual quotient equivalence is both equivariant and graded. This
transfers the full representation assertion under exactly condition (2.3).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem rename_original (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K)
    (hfix : ∀ i, c (e i) = c i) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    MvPolynomial.rename e (original c lam k p) =
      original c lam k (MvPolynomial.rename e p) := by
  simp only [original,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_mul,map_pow,
    map_add,map_smul,MvPolynomial.rename_X,rename_euler]
  calc
    _ = ∑ i : Fin n,
        (c (e i) • (X (e i) ^ k * MvPolynomial.rename e p) +
          lam • (X (e i) ^ k * euler (e i) (MvPolynomial.rename e p))) := by
      simp only [hfix]
    _ = _ := Equiv.sum_comp e (fun i : Fin n =>
      c i • (X i ^ k * MvPolynomial.rename e p) +
        lam • (X i ^ k * euler i (MvPolynomial.rename e p)))

theorem rename_mem_originalTailHit (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K)
    (hfix : ∀ i, c (e i) = c i) (m : ℕ)
    {p : MvPolynomial (Fin n) K} (hp : p ∈ originalTailHit c lam m) :
    MvPolynomial.rename e p ∈ originalTailHit c lam m := by
  have hle : originalTailHit c lam m ≤
      (originalTailHit c lam m).comap (MvPolynomial.rename e).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,q,rfl⟩
    change MvPolynomial.rename e (original c lam k q) ∈ originalTailHit c lam m
    rw [rename_original e c lam hfix]
    exact Submodule.subset_span ⟨k,hk,MvPolynomial.rename e q,rfl⟩
  exact hle hp

theorem diagonalWeight_mapDomain (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K)
    (hfix : ∀ i, c (e i) = c i) (a : Fin n →₀ ℕ) :
    diagonalWeight c lam (a.mapDomain e) = diagonalWeight c lam a := by
  unfold diagonalWeight
  calc
    _ = ∏ i : Fin n, (c (e i) + lam * ((a.mapDomain e) (e i) : K)) :=
      (Equiv.prod_comp e _).symm
    _ = _ := by simp only [Finsupp.mapDomain_apply_of_injective e.injective,hfix]

theorem diagonalEquiv_rename (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (hfix : ∀ i, c (e i) = c i) (p : MvPolynomial (Fin n) K) :
    diagonalEquiv c lam h (MvPolynomial.rename e p) =
      MvPolynomial.rename e (diagonalEquiv c lam h p) := by
  have hl : (diagonalEquiv c lam h).toLinearMap.comp (MvPolynomial.rename e).toLinearMap =
      (MvPolynomial.rename e).toLinearMap.comp (diagonalEquiv c lam h).toLinearMap := by
    apply (basisMonomials (Fin n) K).ext
    intro a
    change diagonalEquiv c lam h (MvPolynomial.rename e (monomial a 1)) =
      MvPolynomial.rename e (diagonalEquiv c lam h (monomial a 1))
    rw [MvPolynomial.rename_monomial,diagonalEquiv_monomial,diagonalEquiv_monomial,
      map_smul,MvPolynomial.rename_monomial,diagonalWeight_mapDomain e c lam hfix]
  exact LinearMap.congr_fun hl p

theorem diagonalEquiv_homogeneousComponent (c : Fin n → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (d : ℕ) (p : MvPolynomial (Fin n) K) :
    diagonalEquiv c lam h (homogeneousComponent d p) =
      homogeneousComponent d (diagonalEquiv c lam h p) := by
  have hl : (diagonalEquiv c lam h).toLinearMap.comp (homogeneousComponent d) =
      (homogeneousComponent d).comp (diagonalEquiv c lam h).toLinearMap := by
    apply (basisMonomials (Fin n) K).ext
    intro a
    change diagonalEquiv c lam h (homogeneousComponent d (monomial a 1)) =
      homogeneousComponent d (diagonalEquiv c lam h (monomial a 1))
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial (1 : K) rfl),
      diagonalEquiv_monomial,map_smul,
      homogeneousComponent_of_mem (isHomogeneous_monomial (1 : K) rfl)]
    split_ifs <;> simp only [diagonalEquiv_monomial,map_zero,smul_zero]
  exact LinearMap.congr_fun hl p

theorem diagonalEquiv_preserves_homogeneous (c : Fin n → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (d : ℕ) {p : MvPolynomial (Fin n) K} (hp : p ∈ homogeneousSubmodule (Fin n) K d) :
    diagonalEquiv c lam h p ∈ homogeneousSubmodule (Fin n) K d := by
  have he : homogeneousComponent d (diagonalEquiv c lam h p) = diagonalEquiv c lam h p := by
    rw [← diagonalEquiv_homogeneousComponent,homogeneousComponent_eq_self hp]
  rw [← he]
  exact homogeneousComponent_mem _ _

theorem diagonalEquiv_symm_preserves_homogeneous (c : Fin n → K) (lam : K)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (d : ℕ) {p : MvPolynomial (Fin n) K} (hp : p ∈ homogeneousSubmodule (Fin n) K d) :
    (diagonalEquiv c lam h).symm p ∈ homogeneousSubmodule (Fin n) K d := by
  have he : homogeneousComponent d ((diagonalEquiv c lam h).symm p) =
      (diagonalEquiv c lam h).symm p := by
    apply (diagonalEquiv c lam h).injective
    rw [diagonalEquiv_homogeneousComponent,LinearEquiv.apply_symm_apply,
      homogeneousComponent_eq_self hp]
  rw [← he]
  exact homogeneousComponent_mem _ _

theorem diagonalQuotientEquiv_preserves_degree (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (d : ℕ)
    {x : MvPolynomial (Fin n) K ⧸ originalTailHit c lam m}
    (hx : x ∈ originalTailQuotientDegree c lam m d) :
    diagonalQuotientEquiv c lam m h x ∈ tailQuotientDegree c lam m d := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [diagonalQuotientEquiv_mkQ]
  exact ⟨_,diagonalEquiv_preserves_homogeneous c lam h d hp,rfl⟩

theorem diagonalQuotientEquiv_symm_preserves_degree (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (d : ℕ)
    {x : MvPolynomial (Fin n) K ⧸ tailHit c lam m}
    (hx : x ∈ tailQuotientDegree c lam m d) :
    (diagonalQuotientEquiv c lam m h).symm x ∈ originalTailQuotientDegree c lam m d := by
  obtain ⟨p,hp,rfl⟩ := hx
  refine ⟨(diagonalEquiv c lam h).symm p,
    diagonalEquiv_symm_preserves_homogeneous c lam h d hp,?_⟩
  apply (diagonalQuotientEquiv c lam m h).injective
  rw [diagonalQuotientEquiv_mkQ,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- An actual internal grading whose pieces are proved to be the images of
the ordinary homogeneous polynomial pieces. -/
def originalTailQuotientGrading (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) :
    TauCeti.InternalGrading K (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) ℕ :=
  (tailQuotientGrading c lam m).map (diagonalQuotientEquiv c lam m h).symm

@[simp] theorem originalTailQuotientGrading_piece (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) (d : ℕ) :
    (originalTailQuotientGrading c lam m h).piece d = originalTailQuotientDegree c lam m d := by
  rw [originalTailQuotientGrading,TauCeti.InternalGrading.map_piece,tailQuotientGrading_piece]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact diagonalQuotientEquiv_symm_preserves_degree c lam m h d hy
  · intro hx
    exact ⟨diagonalQuotientEquiv c lam m h x,
      diagonalQuotientEquiv_preserves_degree c lam m h d hx,
      (diagonalQuotientEquiv c lam m h).symm_apply_apply x⟩

def originalTailQuotientAction (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → K) (lam : K) (m : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Representation K G (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) := by
  refine QuotientLinearAction.action (polynomialPermutationAction K G)
    (originalTailHit c lam m) ?_
  intro g p hp
  change MvPolynomial.rename (g : Equiv.Perm (Fin n)) p ∈ originalTailHit c lam m
  exact rename_mem_originalTailHit (g : Equiv.Perm (Fin n)) c lam (hfix g) m hp

@[simp] theorem originalTailQuotientAction_mkQ (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → K) (lam : K) (m : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    (g : G) (p : MvPolynomial (Fin n) K) :
    originalTailQuotientAction G c lam m hfix g ((originalTailHit c lam m).mkQ p) =
      (originalTailHit c lam m).mkQ (MvPolynomial.rename (g : Equiv.Perm (Fin n)) p) := rfl

def diagonalQuotientRepresentationEquiv (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    (originalTailQuotientAction G c lam m hfix).Equiv (tailQuotientAction G c lam m hfix) :=
  Representation.Equiv.mk (diagonalQuotientEquiv c lam m h) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨p,rfl⟩ := (originalTailHit c lam m).mkQ_surjective x
    change diagonalQuotientEquiv c lam m h
      (originalTailQuotientAction G c lam m hfix g ((originalTailHit c lam m).mkQ p)) =
      tailQuotientAction G c lam m hfix g
        (diagonalQuotientEquiv c lam m h ((originalTailHit c lam m).mkQ p))
    rw [originalTailQuotientAction_mkQ,diagonalQuotientEquiv_mkQ,
      diagonalQuotientEquiv_mkQ,tailQuotientAction_mkQ,diagonalEquiv_rename g c lam h (hfix g)])

end PaperVerification.PowerOperators
