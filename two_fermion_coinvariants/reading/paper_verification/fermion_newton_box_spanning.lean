module

public import PaperVerification.FermionNewtonRestrictionIdeal
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Literal rectangular monomials and deletion spanning

The space here is the span of precisely the bounded exponent vectors.  The
deletion step uses the actual coordinate specialization of ideals and the
inclusion of the deleted ideal after multiplication by the removed variable.
It assumes neither a colon identity nor independence of the rectangle.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

abbrev RectangleIndex (h : Fin n → ℕ) :=
  {a : Fin n →₀ ℕ // ∀ i, a i < h i}

def rectangleIndexEquiv (h : Fin n → ℕ) :
    RectangleIndex h ≃ (∀ i : Fin n, Fin (h i)) where
  toFun a i := ⟨a.val i,a.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).val),fun i ↦ (a i).isLt⟩
  left_inv a := by apply Subtype.ext; ext i; rfl
  right_inv a := by funext i; apply Fin.ext; rfl

instance rectangleIndex_fintype (h : Fin n → ℕ) : Fintype (RectangleIndex h) :=
  Fintype.ofEquiv _ (rectangleIndexEquiv h).symm

theorem card_rectangleIndex (h : Fin n → ℕ) :
    Fintype.card (RectangleIndex h) = ∏ i, h i := by
  rw [Fintype.card_congr (rectangleIndexEquiv h),Fintype.card_pi]
  simp only [Fintype.card_fin]

def rectangleSpan (h : Fin n → ℕ) : Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F (Set.range (fun a : RectangleIndex h ↦ monomial a.val (1 : F)))

theorem monomial_mem_rectangleSpan (h : Fin n → ℕ) (a : Fin n →₀ ℕ)
    (ha : ∀ i, a i < h i) : monomial a (1 : F) ∈ rectangleSpan h :=
  Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩

def rectangleBasis (h : Fin n → ℕ) : Module.Basis (RectangleIndex h) F (rectangleSpan (F := F) h) :=
  Module.Basis.span ((basisMonomials (Fin n) F).linearIndependent.comp
    (fun a : RectangleIndex h ↦ a.val) Subtype.val_injective)

@[simp] theorem rectangleBasis_apply (h : Fin n → ℕ) (a : RectangleIndex h) :
    (rectangleBasis (F := F) h a : MvPolynomial (Fin n) F) = monomial a.val 1 :=
  Module.Basis.coe_span_apply _ _

instance rectangleSpan_finite (h : Fin n → ℕ) : Module.Finite F (rectangleSpan (F := F) h) :=
  Module.Finite.of_basis (rectangleBasis h)

theorem rectangleSpan_finrank (h : Fin n → ℕ) :
    Module.finrank F (rectangleSpan (F := F) h) = ∏ i, h i := by
  rw [Module.finrank_eq_card_basis (rectangleBasis h),card_rectangleIndex]

/-- Every polynomial has a representative in the literal rectangle. -/
def BoxSpans (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ) : Prop :=
  ∀ p, ∃ v ∈ rectangleSpan (F := F) h, p - v ∈ I

theorem rectangleSpan_zero_variables (h : Fin 0 → ℕ) :
    rectangleSpan (F := F) h = ⊤ := by
  apply top_unique
  rw [← (basisMonomials (Fin 0) F).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact monomial_mem_rectangleSpan h a (fun i ↦ Fin.elim0 i)

theorem boxSpans_zero_variables (I : Ideal (MvPolynomial (Fin 0) F)) (h : Fin 0 → ℕ) :
    BoxSpans I h := by
  intro p
  refine ⟨p,?_,?_⟩
  · rw [rectangleSpan_zero_variables]
    trivial
  · simpa only [sub_self] using I.zero_mem

theorem rename_mem_rectangleSpan (h : Fin (n + 1) → ℕ) (q : Fin (n + 1))
    (hq : 0 < h q) {p : MvPolynomial (Fin n) F}
    (hp : p ∈ rectangleSpan (h ∘ q.succAbove)) :
    rename q.succAbove p ∈ rectangleSpan (F := F) h := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨a,rfl⟩ := hp
      rw [rename_monomial]
      apply monomial_mem_rectangleSpan
      intro i
      by_cases hi : i = q
      · subst i
        rw [Finsupp.mapDomain_of_notMem_range a.val q (by
          rintro ⟨j,hj⟩
          exact Fin.succAbove_ne q j hj)]
        exact hq
      · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
        rw [Finsupp.mapDomain_apply_of_injective (Fin.strictMono_succAbove q).injective]
        exact a.property j
  | zero => simpa only [map_zero] using (rectangleSpan (F := F) h).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (rectangleSpan (F := F) h).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (rectangleSpan (F := F) h).smul_mem c ih

theorem X_mul_mem_rectangleSpan (h : Fin n → ℕ) (q : Fin n)
    {p : MvPolynomial (Fin n) F}
    (hp : p ∈ rectangleSpan (Function.update h q (h q - 1))) :
    X q * p ∈ rectangleSpan (F := F) h := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨a,rfl⟩ := hp
      have he : X q * monomial a.val (1 : F) = monomial (Finsupp.single q 1 + a.val) 1 := by
        rw [X,monomial_mul_monomial,one_mul]
      rw [he]
      apply monomial_mem_rectangleSpan
      intro i
      have hi : a.val i < Function.update h q (h q - 1) i := a.property i
      by_cases heq : i = q
      · subst i
        simp only [Finsupp.add_apply,Finsupp.single_eq_same,Function.update_self] at hi ⊢
        omega
      · simpa only [Finsupp.add_apply,Finsupp.single_eq_of_ne heq,zero_add,
          Function.update_of_ne heq] using hi
  | zero => simpa only [mul_zero] using (rectangleSpan (F := F) h).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [mul_add] using (rectangleSpan (F := F) h).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [mul_smul_comm] using (rectangleSpan (F := F) h).smul_mem c ih

/-- The precise polynomial division step, before any independence assertion.
The deleted quotient can be zero; this is included by the first disjunct. -/
theorem boxSpans_of_deletion
    (I J : Ideal (MvPolynomial (Fin (n + 1)) F))
    (L : Ideal (MvPolynomial (Fin n) F)) (h : Fin (n + 1) → ℕ)
    (q : Fin (n + 1)) (hq : 0 < h q)
    (hres : Ideal.map (removeCoordinate (F := F) q).toRingHom I = L)
    (hdel : ∀ p ∈ J, X q * p ∈ I)
    (hL : BoxSpans L (h ∘ q.succAbove))
    (hJ : J = ⊤ ∨ BoxSpans J (Function.update h q (h q - 1))) :
    BoxSpans I h := by
  intro p
  obtain ⟨v,hv,hpv⟩ := hL (removeCoordinate q p)
  have hm : removeCoordinate q p - v ∈ Ideal.map (removeCoordinate (F := F) q).toRingHom I := by
    simpa only [hres] using hpv
  obtain ⟨j,hj,hje⟩ := (Ideal.mem_map_iff_of_surjective
    (removeCoordinate (F := F) q).toRingHom (removeCoordinate_surjective q)).mp hm
  have hz : removeCoordinate q (p - j - rename q.succAbove v) = 0 := by
    change removeCoordinate q j = removeCoordinate q p - v at hje
    rw [map_sub,map_sub,removeCoordinate_rename,hje]
    ring
  obtain ⟨g,hg⟩ := (removeCoordinate_eq_zero_iff q _).mp hz
  have hp : p = j + rename q.succAbove v + X q * g := by
    rw [← hg]
    ring
  have hvl := rename_mem_rectangleSpan h q hq hv
  rcases hJ with hJ | hJ
  · refine ⟨rename q.succAbove v,hvl,?_⟩
    have hgI := hdel g (by rw [hJ]; trivial)
    have hh := I.add_mem hj hgI
    rw [hp]
    convert hh using 1 <;> ring
  · obtain ⟨w,hw,hgw⟩ := hJ g
    refine ⟨rename q.succAbove v + X q * w,
      (rectangleSpan h).add_mem hvl (X_mul_mem_rectangleSpan h q hw),?_⟩
    have hh := I.add_mem hj (hdel (g - w) hgw)
    rw [hp]
    convert hh using 1 <;> ring

def rectangleQuotientMap (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ) :
    rectangleSpan (F := F) h →ₗ[F] (MvPolynomial (Fin n) F ⧸ I) :=
  (Ideal.Quotient.mkₐ F I).toLinearMap.comp (rectangleSpan h).subtype

theorem rectangleQuotientMap_surjective
    (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ) (hs : BoxSpans I h) :
    Function.Surjective (rectangleQuotientMap I h) := by
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨v,hv,hpv⟩ := hs p
  refine ⟨⟨v,hv⟩,?_⟩
  change Ideal.Quotient.mk I v = Ideal.Quotient.mk I p
  apply (Ideal.Quotient.eq).mpr
  simpa only [neg_sub] using I.neg_mem hpv

/-- Spanning and the independently obtained length identify the actual
quotient with its literal rectangular representatives. -/
def rectangleQuotientEquiv
    (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ)
    [Module.Finite F (MvPolynomial (Fin n) F ⧸ I)]
    (hs : BoxSpans I h) (hd : Module.finrank F (MvPolynomial (Fin n) F ⧸ I) = ∏ i, h i) :
    rectangleSpan (F := F) h ≃ₗ[F] (MvPolynomial (Fin n) F ⧸ I) :=
  LinearEquiv.ofBijective (rectangleQuotientMap I h)
    (OrzechProperty.bijective_of_surjective_of_finrank_le
      (rectangleQuotientMap I h) (rectangleQuotientMap_surjective I h hs)
      (by rw [rectangleSpan_finrank,hd]))

def rectangleQuotientBasis
    (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ)
    [Module.Finite F (MvPolynomial (Fin n) F ⧸ I)]
    (hs : BoxSpans I h) (hd : Module.finrank F (MvPolynomial (Fin n) F ⧸ I) = ∏ i, h i) :
    Module.Basis (RectangleIndex h) F (MvPolynomial (Fin n) F ⧸ I) :=
  (rectangleBasis h).map (rectangleQuotientEquiv I h hs hd)

@[simp] theorem rectangleQuotientBasis_apply
    (I : Ideal (MvPolynomial (Fin n) F)) (h : Fin n → ℕ)
    [Module.Finite F (MvPolynomial (Fin n) F ⧸ I)]
    (hs : BoxSpans I h) (hd : Module.finrank F (MvPolynomial (Fin n) F ⧸ I) = ∏ i, h i)
    (a : RectangleIndex h) :
    rectangleQuotientBasis I h hs hd a = Ideal.Quotient.mk I (monomial a.val 1) := by
  change Ideal.Quotient.mk I (rectangleBasis h a).val = _
  rw [rectangleBasis_apply]

end PaperVerification.Fermion.Newton
