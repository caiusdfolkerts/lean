module

public import PaperVerification.ToricAffineActionCoaction
public import PaperVerification.ToricOrbitChartQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Prime character ideals and their actual additive faces

The component property of an equivariant quotient kernel is derived
from the actual affine action. Primality then makes its surviving
characters an additive face, and the ideal is exactly the kernel of the
literal semigroup-face quotient.
-/

noncomputable section

universe u v

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes
open scoped TensorProduct Classical

variable (k : Type (max u v)) [Field k] {M : Type v} [AddCommGroup M]
    (S : AddSubmonoid M)

theorem semigroupCoefficient_quotient
    (B : Type (max u v)) [CommRing B] [Algebra k B]
    (q : AddMonoidAlgebra k S→ₐ[k]B) (s : S) (f : AddMonoidAlgebra k S) :
    characterCoefficient k (s:M)
      (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q
        (semigroupChartCoaction k S f))=q (single s (f.coeff s)) := by
  have h : (characterCoefficient k (s:M)).comp
        (((Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q).toLinearMap).comp
          (semigroupChartCoaction k S).toLinearMap)=
      q.toLinearMap.comp ((AddMonoidAlgebra.lsingle (R:=k) s).comp
        ((AddMonoidAlgebra.basis S k).coord s)) := by
    apply (AddMonoidAlgebra.basis S k).ext
    intro t
    by_cases ht : t=s
    · subst t
      simp [AddMonoidAlgebra.basis,semigroupChartCoaction_single,characterCoefficient_tmul]
    · have hv : (t:M)≠(s:M) := fun h=>ht (Subtype.ext h)
      simp [AddMonoidAlgebra.basis,semigroupChartCoaction_single,characterCoefficient_tmul,ht,hv,Ne.symm ht,Ne.symm hv]
  exact congrArg (fun φ=>φ f) h

/-- An actual equivariant affine quotient kernel contains every literal
character component of each of its elements. -/
theorem equivariant_kernel_component
    (B : CommAlgCat.{max u v} k)
    [ModObj (splitTorusOver k M) ((algSpec (CommRingCat.of k)).obj (op B))]
    (q : AddMonoidAlgebra k S→ₐ[k]B)
    [IsModHom (splitTorusOver k M)
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom q).op)]
    {f : AddMonoidAlgebra k S} (hf : f∈RingHom.ker q.toRingHom) (s : S) :
    single s (f.coeff s)∈RingHom.ker q.toRingHom := by
  have h := semigroupCoaction_quotient_zero k M S B q (RingHom.mem_ker.mp hf)
  have hc := congrArg (characterCoefficient k (s:M)) h
  rw [semigroupCoefficient_quotient,map_zero] at hc
  exact RingHom.mem_ker.mpr hc

variable {S}

/-- The component property is an intermediate theorem, rather than a
replacement for equivariance in the geometric endpoint. -/
def IsMonomialIdeal (P : Ideal (AddMonoidAlgebra k S)) : Prop :=
  ∀ f∈P,∀ s : S,single s (f.coeff s)∈P

theorem single_one_mem_of_component
    (P : Ideal (AddMonoidAlgebra k S)) (hP : IsMonomialIdeal k P)
    {f : AddMonoidAlgebra k S} (hf : f∈P) {s : S} (hs : f.coeff s≠0) :
    single s (1:k)∈P := by
  have h := (P.restrictScalars k).smul_mem (f.coeff s)⁻¹ (hP f hf s)
  change (f.coeff s)⁻¹ • single s (f.coeff s) ∈ P at h
  simpa only [smul_single,smul_eq_mul,inv_mul_cancel₀ hs] using h

def survivingCharacterFace (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] :
    AddSubmonoid S where
  carrier := {s | single s (1:k)∉P}
  zero_mem' := by
    change single (0 : S) (1 : k) ∉ P
    simpa only [← AddMonoidAlgebra.one_def] using Ideal.one_notMem P
  add_mem' := by
    intro s t hs ht
    change single s (1 : k) ∉ P at hs
    change single t (1 : k) ∉ P at ht
    change single (s + t) (1 : k) ∉ P
    have h := (inferInstance : P.IsPrime).mul_notMem hs ht
    simpa only [single_mul_single,one_mul] using h

theorem survivingCharacterFace_isAdditiveFace
    (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] :
    IsAdditiveFace (survivingCharacterFace k P) := by
  intro s t h
  constructor
  · intro hs
    apply h
    have hm := P.mul_mem_right (single t (1:k)) hs
    simpa only [single_mul_single,one_mul] using hm
  · intro ht
    apply h
    have hm := P.mul_mem_left (single s (1:k)) ht
    simpa only [single_mul_single,one_mul] using hm

theorem additiveFaceRetraction_coeff
    (F : AddSubmonoid S) (hF : IsAdditiveFace F)
    (f : AddMonoidAlgebra k S) (s : F) :
    (additiveFaceRetraction k F hF f).coeff s=f.coeff s.val := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,coeff_add,hf,hg,Finsupp.add_apply]
  | single t c =>
    by_cases ht : t∈F
    · rw [additiveFaceRetraction_single_of_mem k F hF t ht]
      by_cases hts : t=s.val
      · subst t
        simp
      · have hn : (⟨t,ht⟩:F)≠s := fun h=>hts (congrArg Subtype.val h)
        simp [hts,hn,Ne.symm hts,Ne.symm hn]
    · rw [additiveFaceRetraction_single_of_not_mem k F hF t ht]
      have hts : t≠s.val := fun h=>ht (h.symm ▸ s.property)
      simp [hts,Ne.symm hts]

/-- The quotient ideal is the actual kernel of the canonical face
retraction, with equality of all polynomials, not only characters. -/
theorem monomialPrime_eq_face_kernel
    (P : Ideal (AddMonoidAlgebra k S)) [P.IsPrime] (hP : IsMonomialIdeal k P) :
    P=RingHom.ker (additiveFaceRetraction k (survivingCharacterFace k P)
      (survivingCharacterFace_isAdditiveFace k P)).toRingHom := by
  let F := survivingCharacterFace k P
  let hF := survivingCharacterFace_isAdditiveFace k P
  ext f
  rw [RingHom.mem_ker]
  constructor
  · intro hf
    change additiveFaceRetraction k F hF f = 0
    ext s
    rw [additiveFaceRetraction_coeff]
    change f.coeff s.val=0
    by_contra hs
    exact s.property (single_one_mem_of_component k P hP hf hs)
  · intro hf
    change additiveFaceRetraction k F hF f = 0 at hf
    have hsum : f=∑ s∈f.coeff.support,single s (f.coeff s) :=
      (AddMonoidAlgebra.sum_coeff_single f).symm
    rw [hsum]
    apply P.sum_mem
    intro s hs
    by_cases hsF : s∈F
    · have hz := congrArg (fun g : AddMonoidAlgebra k F=>g.coeff ⟨s,hsF⟩) hf
      rw [additiveFaceRetraction_coeff] at hz
      have hc : f.coeff s=0 := by simpa using hz
      simp only [hc,single_zero,P.zero_mem]
    · have hm : single s (1:k)∈P := by
        change ¬¬single s (1:k)∈P at hsF
        exact not_not.mp hsF
      have h := (P.restrictScalars k).smul_mem (f.coeff s) hm
      change f.coeff s • single s (1 : k) ∈ P at h
      simpa only [smul_single,smul_eq_mul,mul_one] using h

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.equivariant_kernel_component
#print axioms PaperVerification.ToricCharacters.monomialPrime_eq_face_kernel
