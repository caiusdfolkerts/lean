module

public import PaperVerification.ToricRankOneDegree
public import PaperVerification.ToricFanCharacterTranslations

@[expose] public section

/-!
# The usual O(d) characterization of degree on the actual projective line

The divisor `d·∞` is defined by its two actual boundary coefficients. Its
Cartier sheaf is the usual twist O(d). Every fan Cartier presentation is
isomorphic to exactly the twist indexed by the sum of its coefficients.
Together with the arbitrary-Cartier classification, this identifies the
previous curve-degree relation with the intrinsic O(d) characterization
for every actual Cartier sheaf, including negative degrees.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

def projectiveLineTwistCoefficients (d : ℤ) (v : Lattice 1) : ℤ :=
  if v=projectiveLineRay true then d else 0

def projectiveLineTwist (d : ℤ) : CartierData (projectiveLineScheme k) :=
  projectiveLineCartierData k (projectiveLineTwistCoefficients d)

@[simp] theorem projectiveLineTwistCoefficients_positive (d : ℤ) :
    projectiveLineTwistCoefficients d (projectiveLineRay false)=0 := by
  simp only [projectiveLineTwistCoefficients,projectiveLineRay_ne,if_false]

@[simp] theorem projectiveLineTwistCoefficients_negative (d : ℤ) :
    projectiveLineTwistCoefficients d (projectiveLineRay true)=d := by
  simp only [projectiveLineTwistCoefficients,if_true]

/-- Multiplication by the explicit integral character moves all the
degree to the point at infinity. This is an actual sheaf isomorphism. -/
theorem projectiveLineCartier_linearlyEquivalent_twist (a : Lattice 1 → ℤ) :
    (projectiveLineCartierData k a).LinearlyEquivalent
      (projectiveLineTwist k (a (projectiveLineRay false)+a (projectiveLineRay true))) := by
  apply projectiveLineFan.fanCartierData_characterTranslation k projectiveLineFan_isPure
    a (projectiveLineTwistCoefficients
      (a (projectiveLineRay false)+a (projectiveLineRay true)))
    (fun _ => a (projectiveLineRay false))
  intro v hv
  rw [projectiveLineFan_rays,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl
  · simp only [projectiveLineTwistCoefficients_positive,integerPairing,Fin.sum_univ_one,
      projectiveLineRay,Bool.false_eq_true,if_false,one_mul,sub_self]
  · simp only [projectiveLineTwistCoefficients_negative,integerPairing,Fin.sum_univ_one,
      projectiveLineRay,if_true,neg_one_mul,sub_neg_eq_add]
    exact add_comm _ _

/-- This is the usual degree definition by the unique projective-line
twist, now justified for the actual sheaf and both integral signs. -/
theorem projectiveLineHasDegree_iff_twist (M : (projectiveLineScheme k).Modules) (d : ℤ) :
    ProjectiveLineHasDegree k M d ↔ Nonempty (M ≅ (projectiveLineTwist k d).sheaf) := by
  constructor
  · rintro ⟨a,⟨F⟩,ha⟩
    have h := projectiveLineCartier_linearlyEquivalent_twist k a
    rw [ha] at h
    exact ⟨F ≪≫ h.some⟩
  · rintro ⟨F⟩
    refine ⟨projectiveLineTwistCoefficients d,⟨F⟩,?_⟩
    simp only [projectiveLineTwistCoefficients_positive,
      projectiveLineTwistCoefficients_negative,zero_add]

theorem projectiveLineTwists_iso_iff (d e : ℤ) :
    Nonempty ((projectiveLineTwist k d).sheaf ≅ (projectiveLineTwist k e).sheaf) ↔ d=e := by
  constructor
  · rintro ⟨F⟩
    have hd := (projectiveLineHasDegree_iff_twist k (projectiveLineTwist k d).sheaf d).mpr
      ⟨Iso.refl _⟩
    have he := (projectiveLineHasDegree_iff_twist k (projectiveLineTwist k d).sheaf e).mpr ⟨F⟩
    exact projectiveLineHasDegree_unique k hd he
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Every actual invertible fractional sheaf is a unique O(d). This is
the full projective-line Picard classification used by the degree bridge. -/
theorem projectiveLineCartier_existsUnique_twist (D : CartierData (projectiveLineScheme k)) :
    ∃! d : ℤ,Nonempty (D.sheaf ≅ (projectiveLineTwist k d).sheaf) := by
  simpa only [projectiveLineHasDegree_iff_twist] using
    projectiveLineCartier_existsUnique_degree k D

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineHasDegree_iff_twist
#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_existsUnique_twist
