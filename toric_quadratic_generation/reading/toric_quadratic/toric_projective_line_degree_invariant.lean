module

public import PaperVerification.ToricProjectiveLineTwists
public import PaperVerification.ToricCartierSchemeIso
public import PaperVerification.ToricSectionTensorNaturality
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Degree is independent of a projective-line coordinate

The actual global sections of O(d) have dimension max(d+1,0), proved by
the actual character-coordinate equivalence and a finite interval count.
The dimension determines all nonnegative degrees. For negative degrees,
tensoring with the opposite twist reduces to degree zero. Consequently
every actual k-scheme automorphism preserves the degree of every Cartier
sheaf. No invariance of principal-divisor degrees is assumed.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical BaseSections

theorem projectiveLineTwist_exponents (d : ℤ) (m : Lattice 1) :
    m ∈ projectiveLineFan.fanIntegralExponents (projectiveLineTwistCoefficients d) ↔
      0 ≤ m 0 ∧ m 0 ≤ d := by
  change (∀ v ∈ projectiveLineFan.rays,
    -(projectiveLineTwistCoefficients d v : ℝ) ≤
      (dotProductEquiv ℝ (Fin 1) (embed 1 v)) (embed 1 m)) ↔ _
  rw [projectiveLineFan_rays]
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,
    forall_eq,projectiveLineTwistCoefficients_positive,
    projectiveLineTwistCoefficients_negative]
  rw [SmoothCompleteFan.normalRay_pairing_lattice,
    SmoothCompleteFan.normalRay_pairing_lattice]
  simp only [Fin.sum_univ_one,projectiveLineRay,Bool.false_eq_true,if_false,
    if_true,one_mul,neg_one_mul,Int.cast_neg,neg_zero,neg_le_neg_iff]
  exact_mod_cast (Iff.rfl : (0 ≤ m 0 ∧ m 0 ≤ d) ↔ (0 ≤ m 0 ∧ m 0 ≤ d))

/-- The actual allowed character set is a finite integer interval, with
the empty interval retained for every degree below zero. -/
def projectiveLineTwistExponentEquiv (d : ℤ) :
    projectiveLineFan.fanIntegralExponents (projectiveLineTwistCoefficients d) ≃
      Fin (d+1).toNat where
  toFun m := ⟨(m.val 0).toNat,by
    have hm := (projectiveLineTwist_exponents d m.val).mp m.property
    omega⟩
  invFun i := ⟨fun _ => (i.val : ℤ),by
    apply (projectiveLineTwist_exponents d _).mpr
    have hi := i.isLt
    constructor <;> omega⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    have hm := (projectiveLineTwist_exponents d m.val).mp m.property
    simp only [hi]
    exact Int.toNat_of_nonneg hm.1
  right_inv i := by
    apply Fin.ext
    simp only [Int.toNat_natCast]

variable (k : Type u) [Field k]

def projectiveLineTwistSectionCoordinates (d : ℤ) :
    Γ((projectiveLineTwist k d).sheaf,⊤) ≃ₗ[k] (Fin (d+1).toNat →₀ k) :=
  (projectiveLineFan.fanCartierSectionCoordinates k projectiveLineFan_isPure
    (projectiveLineTwistCoefficients d)).trans
      ((AddMonoidAlgebra.supportedEquivFinsupp (R:=k) (S:=k) _).trans
        (Finsupp.domLCongr (projectiveLineTwistExponentEquiv d)))

theorem projectiveLineTwist_finrank (d : ℤ) :
    Module.finrank k Γ((projectiveLineTwist k d).sheaf,⊤)=(d+1).toNat := by
  rw [(projectiveLineTwistSectionCoordinates k d).finrank_eq,
    Module.finrank_finsupp_self,Fintype.card_fin]

theorem projectiveLineHasDegree_finrank
    {M : (projectiveLineScheme k).Modules} {d : ℤ} (h : ProjectiveLineHasDegree k M d) :
    Module.finrank k Γ(M,⊤)=(d+1).toNat := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k M d).mp h
  exact (BaseSections.globalSectionsIso k F).finrank_eq.trans
    (projectiveLineTwist_finrank k d)

theorem projectiveLineHasDegree_add
    (D E : CartierData (projectiveLineScheme k)) {d e : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d)
    (hE : ProjectiveLineHasDegree k E.sheaf e) :
    ProjectiveLineHasDegree k (D.add E).sheaf (d+e) := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k D.sheaf d).mp hD
  obtain ⟨G⟩ := (projectiveLineHasDegree_iff_twist k E.sheaf e).mp hE
  let a := projectiveLineTwistCoefficients d
  let b := projectiveLineTwistCoefficients e
  let J : (D.add E).sheaf ≅ (projectiveLineCartierData k (a+b)).sheaf :=
    D.addSheafIso (projectiveLineTwist k d) E (projectiveLineTwist k e) F G ≪≫
      (projectiveLineFan.fanCartierData_add_equivalent k projectiveLineFan_isPure a b).choose
  refine ⟨a+b,⟨J⟩,?_⟩
  simp only [a,b,Pi.add_apply,projectiveLineTwistCoefficients_positive,
    projectiveLineTwistCoefficients_negative,zero_add]

variable (e : projectiveLineScheme k ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))]

/-- Preservation in nonnegative degree follows from the dimension of the
actual global-section vector space under the actual scheme isomorphism. -/
theorem projectiveLineHasDegree_pullback_of_nonneg
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hd : 0≤d) (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k (D.dominantPullback e.hom).sheaf d := by
  obtain ⟨r,hr,_⟩ := projectiveLineCartier_existsUnique_degree k (D.dominantPullback e.hom)
  have hdim : (d+1).toNat=(r+1).toNat :=
    (projectiveLineHasDegree_finrank k hD).symm.trans
      ((D.schemeIsoGlobalSections k e).finrank_eq.trans
        (projectiveLineHasDegree_finrank k hr))
  have hrd : r=d := by omega
  simpa only [hrd] using hr

/-- Every integral degree, including negative degree, is preserved by an
arbitrary actual k-scheme automorphism of the projective line. -/
theorem projectiveLineHasDegree_pullback
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k (D.dominantPullback e.hom).sheaf d := by
  by_cases hd : 0≤d
  · exact projectiveLineHasDegree_pullback_of_nonneg k e D hd hD
  · obtain ⟨r,hr,_⟩ := projectiveLineCartier_existsUnique_degree k (D.dominantPullback e.hom)
    let E := projectiveLineTwist k (-d)
    have hE : ProjectiveLineHasDegree k E.sheaf (-d) :=
      (projectiveLineHasDegree_iff_twist k E.sheaf (-d)).mpr ⟨Iso.refl _⟩
    have hDE : ProjectiveLineHasDegree k (D.add E).sheaf 0 := by
      simpa only [add_neg_cancel] using projectiveLineHasDegree_add k D E hD hE
    have hE' : ProjectiveLineHasDegree k (E.dominantPullback e.hom).sheaf (-d) :=
      projectiveLineHasDegree_pullback_of_nonneg k e E (by omega) hE
    have hDE' : ProjectiveLineHasDegree k ((D.add E).dominantPullback e.hom).sheaf 0 :=
      projectiveLineHasDegree_pullback_of_nonneg k e (D.add E) (by omega) hDE
    have hsum : ProjectiveLineHasDegree k
        ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).sheaf 0 :=
      (projectiveLineHasDegree_iso k
        (D.dominantPullback_add_equivalent E e.hom).choose 0).mp hDE'
    have hnum := projectiveLineHasDegree_unique k
      (projectiveLineHasDegree_add k (D.dominantPullback e.hom)
        (E.dominantPullback e.hom) hr hE') hsum
    have hrd : r=d := by omega
    simpa only [hrd] using hr

/-- The same invariance for Mathlib's actual module-sheaf pullback,
without referring to a fractional embedding in its conclusion. -/
theorem projectiveLineHasDegree_pullbackSheaf
    (D : CartierData (projectiveLineScheme k)) {d : ℤ}
    (hD : ProjectiveLineHasDegree k D.sheaf d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.hom).obj D.sheaf) d :=
  (projectiveLineHasDegree_iso k (D.dominantPullbackSheafIso e.hom) d).mpr
    (projectiveLineHasDegree_pullback k e D hD)

/-- The embedding in rational functions is unnecessary: a degree
certificate itself gives an actual twist presentation of the module sheaf. -/
theorem projectiveLineHasDegree_pullbackModule
    {M : (projectiveLineScheme k).Modules} {d : ℤ}
    (hM : ProjectiveLineHasDegree k M d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.hom).obj M) d := by
  obtain ⟨F⟩ := (projectiveLineHasDegree_iff_twist k M d).mp hM
  apply (projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullback e.hom).mapIso F) d).mpr
  apply projectiveLineHasDegree_pullbackSheaf k e (projectiveLineTwist k d)
  exact (projectiveLineHasDegree_iff_twist k _ d).mpr ⟨Iso.refl _⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineTwist_finrank
#print axioms PaperVerification.ToricGeometry.projectiveLineHasDegree_pullbackSheaf
