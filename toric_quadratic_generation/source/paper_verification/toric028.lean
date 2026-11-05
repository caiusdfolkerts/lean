module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Group.Basic
public import paper_verification.toric001
public import paper_verification.toric002
public import paper_verification.toric009
public import paper_verification.toric013
public import paper_verification.toric016
public import paper_verification.toric018
public import paper_verification.toric019
public import paper_verification.toric021
public import paper_verification.toric022
public import paper_verification.toric023
public import paper_verification.toric024
public import paper_verification.toric026
public import paper_verification.toric027
public import paper_verification.toric030
public import paper_verification.toric038
public import paper_verification.toric041
public import paper_verification.toric043

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineTwists
section Source_ToricProjectiveLineTwists

-- original header: module

-- original header: public import PaperVerification.ToricRankOneDegree
-- original header: public import PaperVerification.ToricFanCharacterTranslations

-- original header: @[expose] public section

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
end
end Source_ToricProjectiveLineTwists
-- END ORIGINAL PaperVerification.ToricProjectiveLineTwists


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineDegreeInvariant
section Source_ToricProjectiveLineDegreeInvariant

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineTwists
-- original header: public import PaperVerification.ToricCartierSchemeIso
-- original header: public import PaperVerification.ToricSectionTensorNaturality
-- original header: public import Mathlib.LinearAlgebra.Dimension.Constructions

-- original header: @[expose] public section

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
end
end Source_ToricProjectiveLineDegreeInvariant
-- END ORIGINAL PaperVerification.ToricProjectiveLineDegreeInvariant


-- BEGIN ORIGINAL PaperVerification.ToricRationalCurveDegree
section Source_ToricRationalCurveDegree

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineDegreeInvariant
-- original header: public import PaperVerification.ToricDegreePolytopeBridge

-- original header: @[expose] public section

/-!
# Intrinsic degree on a curve isomorphic to the projective line

Degree uses an actual isomorphism over the original field and the actual
pullback of the line bundle. The preceding automorphism theorem proves
that it is independent of this isomorphism. The wall-curve degree used in
the polytope comparison is then a special case of this intrinsic relation.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]

/-- The usual degree of a line bundle on an actual rational smooth
projective curve, with a genuine k-scheme isomorphism as its witness. -/
def RationalCurveHasDegree (M : C.Modules) (d : ℤ) : Prop :=
  ∃ e : C ≅ projectiveLineScheme k,
    e.hom.IsOver (Spec (CommRingCat.of k)) ∧
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d

theorem projectiveLineDegree_coordinate_independent
    (M : C.Modules) (e f : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))]
    [f.hom.IsOver (Spec (CommRingCat.of k))] {d : ℤ}
    (h : ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback f.inv).obj M) d := by
  let g : projectiveLineScheme k ≅ projectiveLineScheme k := f.symm.trans e
  letI : Scheme.Hom.IsOver g.hom (Spec (CommRingCat.of k)) := by
    change Scheme.Hom.IsOver (f.inv ≫ e.hom) (Spec (CommRingCat.of k))
    infer_instance
  have hg : g.hom≫e.inv=f.inv := by
    change (f.inv≫e.hom)≫e.inv=f.inv
    simp only [Category.assoc,e.hom_inv_id,Category.comp_id]
  let J : (Scheme.Modules.pullback g.hom).obj
      ((Scheme.Modules.pullback e.inv).obj M) ≅
        (Scheme.Modules.pullback f.inv).obj M :=
    (Scheme.Modules.pullbackComp g.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M
  exact (projectiveLineHasDegree_iso k J d).mp
    (projectiveLineHasDegree_pullbackModule k g h)

/-- Any actual k-isomorphism with the projective line computes the same
integer, so the existential choice in the definition carries no ambiguity. -/
theorem rationalCurveHasDegree_iff
    (M : C.Modules) (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] (d : ℤ) :
    RationalCurveHasDegree k M d ↔
      ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d := by
  constructor
  · rintro ⟨f,hf,hd⟩
    letI := hf
    exact projectiveLineDegree_coordinate_independent k M f e hd
  · intro hd
    exact ⟨e,inferInstance,hd⟩

theorem rationalCurveHasDegree_unique {M : C.Modules} {d e : ℤ}
    (hd : RationalCurveHasDegree k M d) (he : RationalCurveHasDegree k M e) : d=e := by
  obtain ⟨f,hf,hfd⟩ := hd
  letI := hf
  exact projectiveLineHasDegree_unique k hfd
    ((rationalCurveHasDegree_iff k M f e).mp he)

theorem rationalCurveHasDegree_iso {M N : C.Modules} (F : M ≅ N) (d : ℤ) :
    RationalCurveHasDegree k M d ↔ RationalCurveHasDegree k N d := by
  constructor
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mp hd⟩
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mpr hd⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

instance oneDimensionalFanSchemeIso_isOver :
    (oneDimensionalFanSchemeIso Γ hd k).hom.IsOver (Spec (CommRingCat.of k)) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  change Scheme.Hom.IsOver (𝟙 (projectiveLineScheme k)) (Spec (CommRingCat.of k))
  infer_instance

theorem oneDimensionalHasDegree_iff_rationalCurve (M : (Γ.fanScheme k).Modules) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ RationalCurveHasDegree k M r :=
  (rationalCurveHasDegree_iff k M (oneDimensionalFanSchemeIso Γ hd k) r).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem wallCurve_hasDegree (hpure : «Σ».IsPure)
    (s : «Σ».fullCones) (j : Fin n) (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) :=
  ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    («Σ».wallIndices_codimension s j) _ _).mp
      («Σ».wallCurve_cartier_hasDegree s j k hpure D t w ht hw)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.rationalCurveHasDegree_unique
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_hasDegree
end
end Source_ToricRationalCurveDegree
-- END ORIGINAL PaperVerification.ToricRationalCurveDegree


-- BEGIN ORIGINAL PaperVerification.ToricInvariantCurveBounds
section Source_ToricInvariantCurveBounds

-- original header: module

-- original header: public import PaperVerification.ToricRationalCurveDegree
-- original header: public import PaperVerification.ToricIntrinsicAction
-- original header: public import PaperVerification.ToricEquivariantRigidity

-- original header: @[expose] public section

/-!
# Actual invariant integral curves and their degree bounds

An invariant curve is an actual integral scheme of ordinary Krull
dimension one, with a closed immersion and a genuine group-scheme action
making that immersion equivariant. The curve itself is not defined by a
fan wall. Bounds on these actual curves imply the wall bounds used in the
polytope proof, and transport through actual equivariant scheme isomorphisms.

The degree relation is the coordinate-independent O(d) degree on rational
smooth projective curves. The classification and degree-existence theorem
for all invariant curves is a separate obligation in the intrinsic dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]

/-- A genuine invariant integral curve, including its scheme structure
and its action on arbitrary test schemes. -/
structure InvariantIntegralCurve where
  curve : Over (Spec (CommRingCat.of k))
  integral : IsIntegral curve.left
  action : ModObj (splitTorusOver k (Fin n→ℤ)) curve
  inclusion : curve ⟶ X
  closed : IsClosedImmersion inclusion.left
  dimension : topologicalKrullDim curve.left=1
  equivariant : letI := action
    IsModHom (splitTorusOver k (Fin n→ℤ)) inclusion

attribute [instance] InvariantIntegralCurve.integral InvariantIntegralCurve.action
  InvariantIntegralCurve.closed InvariantIntegralCurve.equivariant

variable [IsIntegral X.left]

/-- Degree bounds on the actual restricted line bundles. No wall, edge,
coefficient function, or polytope appears in this condition. -/
def InvariantCurveDegreesAtLeast (D : CartierData X.left) (bound : ℕ) : Prop :=
  ∀ C : InvariantIntegralCurve k n X, ∀ d : ℤ,
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d → (bound : ℤ)≤d

theorem invariantCurveDegreesAtLeast_sheafIso
    (D E : CartierData X.left) (F : D.sheaf ≅ E.sheaf) (bound : ℕ) :
    InvariantCurveDegreesAtLeast k n X D bound ↔
      InvariantCurveDegreesAtLeast k n X E bound := by
  constructor
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mpr hd
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mp hd

namespace InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y]
    (e : X ≅ Y) [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]

/-- Composition with an actual equivariant isomorphism transports the
whole curve, rather than only its set of points. -/
def mapIso (C : InvariantIntegralCurve k n X) : InvariantIntegralCurve k n Y where
  curve := C.curve
  integral := C.integral
  action := C.action
  inclusion := C.inclusion≫e.hom
  closed := by
    change IsClosedImmersion (C.inclusion.left≫e.hom.left)
    infer_instance
  dimension := C.dimension
  equivariant := by
    letI := C.action
    infer_instance

variable [IsIntegral Y.left]

def restrictionPullbackIso (C : InvariantIntegralCurve k n X) (D : CartierData Y.left) :
    (Scheme.Modules.pullback C.inclusion.left).obj (D.dominantPullback e.hom.left).sheaf ≅
      (Scheme.Modules.pullback (C.mapIso e).inclusion.left).obj D.sheaf :=
  (Scheme.Modules.pullback C.inclusion.left).mapIso
      (D.dominantPullbackSheafIso e.hom.left).symm ≪≫
    (Scheme.Modules.pullbackComp C.inclusion.left e.hom.left).app D.sheaf

end InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y] [IsIntegral Y.left]

/-- The actual geometric degree hypothesis pulls back along a genuine
equivariant k-scheme isomorphism. -/
theorem invariantCurveDegreesAtLeast_pullbackIso (e : X ≅ Y)
    [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]
    (D : CartierData Y.left) (bound : ℕ)
    (hD : InvariantCurveDegreesAtLeast k n Y D bound) :
    InvariantCurveDegreesAtLeast k n X (D.dominantPullback e.hom.left) bound := by
  intro C d hd
  apply hD (C.mapIso e) d
  exact (rationalCurveHasDegree_iso k (C.restrictionPullbackIso e D) d).mp hd

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

/-- A fan wall supplies a genuine instance of the intrinsic curve type. -/
def wallInvariantCurve (s : «Σ».fullCones) (j : Fin n) :
    InvariantIntegralCurve k n («Σ».fanSchemeOver k) where
  curve := («Σ».wallCurveFan s j).fanSchemeOver k
  integral := by
    change IsIntegral («Σ».wallCurve s j k)
    exact «Σ».wallCurve_isIntegral s j k
  action := «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)
  inclusion := («Σ».wallCurveInclusion s j k).asOver (Spec (CommRingCat.of k))
  closed := by
    change IsClosedImmersion («Σ».wallCurveInclusion s j k)
    exact «Σ».wallCurveInclusion_isClosedImmersion s j k
  dimension := «Σ».wallCurve_dimension s j k
  equivariant := «Σ».wallCurve_equivariant s j k

theorem cartierWallDegreesAtLeast_of_invariantCurveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ)
    (hD : InvariantCurveDegreesAtLeast k n («Σ».fanSchemeOver k) D bound) :
    «Σ».CartierWallDegreesAtLeast k D bound := by
  intro s j d hd
  apply hD («Σ».wallInvariantCurve k s j) d
  exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    («Σ».wallIndices_codimension s j) _ d).mp hd

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.invariantCurveDegreesAtLeast_pullbackIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierWallDegreesAtLeast_of_invariantCurveDegrees
end
end Source_ToricInvariantCurveBounds
-- END ORIGINAL PaperVerification.ToricInvariantCurveBounds


-- BEGIN ORIGINAL PaperVerification.ToricPolytopeTranslation
section Source_ToricPolytopeTranslation

-- original header: module

-- original header: public import PaperVerification.ToricParityClasses
-- original header: public import Mathlib.Topology.Algebra.Group.Basic

-- original header: @[expose] public section

/-!
# Integral translations in the two mixed assertions

The divisor polytope depends on a torus frame by an integral translation.
These lemmas keep both independent translation vectors, their sum in the
target, and the resulting change of the prescribed parity class explicit.
No choice of frame changes either of the full mixed assertions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise

def translateSet {V : Type*} [Add V] (v : V) (S : Set V) : Set V :=
  (fun x => v+x) '' S

theorem translateSet_add {V : Type*} [AddCommGroup V]
    (v w : V) (S T : Set V) :
    translateSet v S + translateSet w T=translateSet (v+w) (S+T) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨x+y,⟨x,hx,y,hy,rfl⟩,by simp only [add_assoc,add_left_comm,add_comm]⟩
  · rintro ⟨_,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨v+x,⟨x,hx,rfl⟩,w+y,⟨y,hy,rfl⟩,by simp only [add_assoc,add_left_comm,add_comm]⟩

theorem interior_translateSet {n : ℕ} (v : Ambient n) (S : Set (Ambient n)) :
    interior (translateSet v S)=translateSet v (interior S) :=
  ((Homeomorph.addLeft v).image_interior S).symm

theorem lattice_mem_translateSet_iff {n : ℕ} (v m : Lattice n)
    (S : Set (Ambient n)) :
    embed n m ∈ translateSet (embed n v) S ↔ embed n (m-v)∈S := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    have he : embed n (m-v)=x := by
      rw [map_sub,← hxm]
      exact add_sub_cancel_left (embed n v) x
    simpa only [he] using hx
  · intro hm
    refine ⟨embed n (m-v),hm,?_⟩
    rw [map_sub]
    abel

theorem latticePoints_translateSet {n : ℕ} (v : Lattice n) (S : Set (Ambient n)) :
    {m : Lattice n | embed n m∈translateSet (embed n v) S}=
      translateSet v {m : Lattice n | embed n m∈S} := by
  ext m
  rw [Set.mem_setOf_eq,lattice_mem_translateSet_iff]
  constructor
  · intro hm
    exact ⟨m-v,hm,by abel⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [add_sub_cancel_left,Set.mem_setOf_eq] using hz

theorem latticePoints_interior_translateSet {n : ℕ}
    (v : Lattice n) (S : Set (Ambient n)) :
    {m : Lattice n | embed n m∈interior (translateSet (embed n v) S)}=
      translateSet v {m : Lattice n | embed n m∈interior S} := by
  rw [interior_translateSet,latticePoints_translateSet]

/-- The first summand's prescribed class changes by precisely the class
of its translation vector, independently of the second translation. -/
theorem prescribedParity_translate {n : ℕ} (P Q : Set (Ambient n))
    (h : ∀ m : Lattice n, embed n m∈interior (P+Q) → ∀ α : ParityClass n,
      ∃ a b : Lattice n,embed n a∈P ∧ embed n b∈Q ∧
        a+b=m ∧ parityClass n a=α)
    (v w : Lattice n) (m : Lattice n)
    (hm : embed n m∈interior
      (translateSet (embed n v) P+translateSet (embed n w) Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈translateSet (embed n v) P ∧
      embed n b∈translateSet (embed n w) Q ∧ a+b=m ∧ parityClass n a=α := by
  have hm' : embed n (m-(v+w))∈interior (P+Q) := by
    rw [translateSet_add,← map_add,interior_translateSet,
      lattice_mem_translateSet_iff] at hm
    exact hm
  obtain ⟨a,b,ha,hb,hab,hα⟩ := h (m-(v+w)) hm' (α-parityClass n v)
  refine ⟨v+a,w+b,?_,?_,?_,?_⟩
  · exact ⟨embed n a,ha,(map_add (embed n) v a).symm⟩
  · exact ⟨embed n b,hb,(map_add (embed n) w b).symm⟩
  · calc
      v+a+(w+b)=(v+w)+(a+b) := by abel
      _=(v+w)+(m-(v+w)) := by rw [hab]
      _=m := by abel
  · rw [map_add,hα]
    abel

/-- The exact adjoint set equality is preserved by independent integral
translations of the two actual polytopes. -/
theorem adjointLatticePoints_translate {n : ℕ} (P Q : Set (Ambient n))
    (h : {m : Lattice n | embed n m∈P}+{m : Lattice n | embed n m∈interior Q}=
      {m : Lattice n | embed n m∈interior (P+Q)}) (v w : Lattice n) :
    {m : Lattice n | embed n m∈translateSet (embed n v) P}+
        {m : Lattice n | embed n m∈interior (translateSet (embed n w) Q)}=
      {m : Lattice n | embed n m∈interior
        (translateSet (embed n v) P+translateSet (embed n w) Q)} := by
  have hsum : translateSet (embed n v) P+translateSet (embed n w) Q=
      translateSet (embed n (v+w)) (P+Q) := by
    rw [translateSet_add,map_add]
  rw [hsum,latticePoints_translateSet,latticePoints_interior_translateSet,
    latticePoints_interior_translateSet,translateSet_add,h]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.prescribedParity_translate
#print axioms PaperVerification.ToricGeometry.adjointLatticePoints_translate
end
end Source_ToricPolytopeTranslation
-- END ORIGINAL PaperVerification.ToricPolytopeTranslation


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicMixedTheorems
section Source_ToricIntrinsicMixedTheorems

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicFanClassification
-- original header: public import PaperVerification.ToricInvariantCurveBounds
-- original header: public import PaperVerification.ToricIntrinsicSectionPolytopes
-- original header: public import PaperVerification.ToricFanDivisorTheorems
-- original header: public import PaperVerification.ToricPolytopeTranslation

-- original header: @[expose] public section

/-!
# Intrinsic mixed lattice-point statements

The input is an ordinary smooth proper integral scheme with an actual
dense equivariant split torus and actual ample integral Cartier divisors.
Its polytopes are defined from its actual normalized global sections.
The fan, all wall curves, their degrees, the support polytopes, and both
integral translation vectors are derived. The two translations are
retained through the target sum and the prescribed quotient class.

The independent invariant-curve classification and degree-existence
dictionary completes the comparison of the geometric degree predicate
with the manuscript's usual degree condition. The separate intrinsic
canonical-sheaf comparison is needed for the section formulation.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical Pointwise

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance («Σ» : SmoothCompleteFan n) : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

/-- The reconstructed isomorphism preserves the actual actions because
it preserves the actual dense torus, not by an extra classification input. -/
theorem exists_equivariant_completeFan
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».IsPure ∧
      ∃ e : «Σ».fanSchemeOver k ≅ X,
        («Σ».intrinsicToricEmbedding k).torus≫e.hom=T.torus ∧
        IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom := by
  obtain ⟨P,«Σ»,e,hP,hfan,hpure,hbase,htorus⟩ := T.exists_smooth_complete_fan D hD
  let E : «Σ».fanSchemeOver k ≅ X := Over.isoMk e hbase
  letI : Smooth («Σ».fanSchemeStructureMap k) := by
    rw [← hbase]
    infer_instance
  letI : Smooth («Σ».fanSchemeOver k).hom :=
    inferInstanceAs (Smooth («Σ».fanSchemeStructureMap k))
  have hE : («Σ».intrinsicToricEmbedding k).torus≫E.hom=T.torus := by
    apply Over.OverMorphism.ext
    exact htorus
  exact ⟨«Σ»,hpure,E,hE,
    («Σ».intrinsicToricEmbedding k).iso_isModHom_of_torus_compatibility T E hE⟩

/-- A simultaneous fan model of the two actual divisors, including the
independent integral translations of their intrinsically defined polytopes. -/
theorem exists_mixed_divisor_fan_model
    (D E : CartierData X.left) (hampleD : D.IsAmple)
    (bound : ℕ) (hbound : 0<bound ∨ n=0)
    (hD : InvariantCurveDegreesAtLeast k n X D bound)
    (hE : InvariantCurveDegreesAtLeast k n X E bound) :
    ∃ «Σ» : SmoothCompleteFan n, ∃ hpure : «Σ».IsPure,
      ∃ e : «Σ».fanSchemeOver k ≅ X,
        let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
        let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
        «Σ».CartierWallDegreesAtLeast k F bound ∧
        «Σ».CartierWallDegreesAtLeast k G bound ∧
        ∃ v w : Lattice n,
          intrinsicSectionPolytope k n X.left T.torus.left D=
            translateSet (embed n v) («Σ».divisorPolytope k hpure F) ∧
          intrinsicSectionPolytope k n X.left T.torus.left E=
            translateSet (embed n w) («Σ».divisorPolytope k hpure G) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hampleD
  letI := hequiv
  let F₀ := torusNormalizedCartier k n X.left T.torus.left D
  let G₀ := torusNormalizedCartier k n X.left T.torus.left E
  let F := F₀.dominantPullback e.hom.left
  let G := G₀.dominantPullback e.hom.left
  have hF₀ : InvariantCurveDegreesAtLeast k n X F₀ bound :=
    (invariantCurveDegreesAtLeast_sheafIso k n X F₀ D
      (torusNormalizedCartier_linearlyEquivalent k n X.left T.torus.left D).some bound).mpr hD
  have hG₀ : InvariantCurveDegreesAtLeast k n X G₀ bound :=
    (invariantCurveDegreesAtLeast_sheafIso k n X G₀ E
      (torusNormalizedCartier_linearlyEquivalent k n X.left T.torus.left E).some bound).mpr hE
  have hF : «Σ».CartierWallDegreesAtLeast k F bound :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k F bound
      (invariantCurveDegreesAtLeast_pullbackIso e F₀ bound hF₀)
  have hG : «Σ».CartierWallDegreesAtLeast k G bound :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k G bound
      (invariantCurveDegreesAtLeast_pullbackIso e G₀ bound hG₀)
  have hnef (J : CartierData («Σ».fanScheme k))
      (hJ : «Σ».CartierWallDegreesAtLeast k J bound) :
      «Σ».IsNef (fun z => («Σ».cartierCoefficients k hpure J z : ℝ)) := by
    apply SmoothCompleteFan.IsStrictSupport.isNef
    rcases hbound with hb|hn
    · exact «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure J bound hb hJ
    · exact SmoothCompleteFan.isStrictSupport_of_dimension_zero «Σ» hn _
  let e₀ : «Σ».fanScheme k ≅ X.left := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.hom.IsOver (Spec (CommRingCat.of k)) := ⟨e.hom.w⟩
  have htorus₀ : «Σ».splitTorusOpenMap k≫e₀.hom=T.torus.left :=
    congrArg (fun f => f.left) htorus
  obtain ⟨v,hv,hPv⟩ := «Σ».intrinsic_sections_fan_translate k hpure X.left
    T.torus.left e₀ htorus₀ D (hnef F hF)
  obtain ⟨w,hw,hQw⟩ := «Σ».intrinsic_sections_fan_translate k hpure X.left
    T.torus.left e₀ htorus₀ E (hnef G hG)
  exact ⟨«Σ»,hpure,e,hF,hG,v,w,hPv,hQw⟩

/-- The prescribed-parity conclusion for intrinsically defined divisor
polytopes on an arbitrary smooth proper split-toric scheme. -/
theorem toric_theorem_1_2
    (D E : CartierData X.left) (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D n)
    (hE : InvariantCurveDegreesAtLeast k n X E n)
    (m : Lattice n)
    (hm : embed n m∈interior
      (intrinsicSectionPolytope k n X.left T.torus.left D+
        intrinsicSectionPolytope k n X.left T.torus.left E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈intrinsicSectionPolytope k n X.left T.torus.left D ∧
      embed n b∈intrinsicSectionPolytope k n X.left T.torus.left E ∧
      a+b=m ∧ parityClass n a=α := by
  have hn : 0<n ∨ n=0 := by omega
  obtain ⟨«Σ»,hpure,e,hF,hG,v,w,hP,hQ⟩ :=
    T.exists_mixed_divisor_fan_model D E hampleD n hn hD hE
  let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
  let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
  rw [hP,hQ] at hm ⊢
  exact prescribedParity_translate («Σ».divisorPolytope k hpure F)
    («Σ».divisorPolytope k hpure G)
    (fun z hz β => «Σ».fanDivisor_prescribedParity k hpure F G hF hG z hz β)
    v w m hm α

/-- The full adjoint lattice-point equality for intrinsically defined
divisor polytopes, with all dimensions and both inclusions retained. -/
theorem toric_theorem_1_3_latticePoints
    (D E : CartierData X.left) (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    {m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)} := by
  obtain ⟨«Σ»,hpure,e,hF,hG,v,w,hP,hQ⟩ :=
    T.exists_mixed_divisor_fan_model D E hampleD (n+1) (Or.inl (by omega)) hD hE
  let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
  let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
  rw [hP,hQ]
  exact adjointLatticePoints_translate («Σ».divisorPolytope k hpure F)
    («Σ».divisorPolytope k hpure G)
    («Σ».fanDivisor_adjointLatticePoints k hpure F G hF hG) v w

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_2
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3_latticePoints
end
end Source_ToricIntrinsicMixedTheorems
-- END ORIGINAL PaperVerification.ToricIntrinsicMixedTheorems


-- BEGIN ORIGINAL PaperVerification.ToricModuleSectionMultiplication
section Source_ToricModuleSectionMultiplication

-- original header: module

-- original header: public import PaperVerification.ToricSectionTensorNaturality

-- original header: @[expose] public section

/-!
# The ordinary tensor multiplication of sections of arbitrary module sheaves

This map is defined before choosing any fractional Cartier presentation.
It sends a pure tensor of global sections to the corresponding section of
the actual tensor sheaf. The base scalars come from the structural morphism.
For Cartier sheaves it is identified with the rational-product construction.
Actual sheaf isomorphisms preserve its surjectivity.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

def moduleSectionProductOver (M N : X.Modules) :
    Γ(M,⊤) →ₗ[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) := by
  letI : Module Γ(X,⊤) Γ(tensorSheaf M N,⊤) :=
    ModuleCat.isModule ((tensorSheaf M N).val.obj (op ⊤))
  let unitMap : Γ(M,⊤) ⊗[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    ((tensorSheafUnit M N).app (op ⊤)).hom
  let product : Γ(M,⊤) →ₗ[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    (TensorProduct.mk Γ(X,⊤) Γ(M,⊤) Γ(N,⊤)).compr₂
      (R := Γ(X,⊤)) (A := Γ(X,⊤)) unitMap
  exact product.restrictScalars₁₂ k k

/-- The usual base-linear multiplication into the genuine tensor sheaf. -/
def moduleSectionMultiplicationOver (M N : X.Modules) :
    Γ(M,⊤) ⊗[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) :=
  TensorProduct.lift (moduleSectionProductOver k M N)

@[simp] theorem moduleSectionMultiplicationOver_tmul (M N : X.Modules)
    (s : Γ(M,⊤)) (t : Γ(N,⊤)) :
    moduleSectionMultiplicationOver k M N (s⊗ₜ[k]t) =
      (tensorSheafUnit M N).app (op ⊤) (s⊗ₜ[Γ(X,⊤)]t) := rfl

theorem moduleSectionMultiplicationOver_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    (BaseSections.globalSectionsIso k (tensorSheafIso F G)).toLinearMap.comp
        (moduleSectionMultiplicationOver k M N) =
      (moduleSectionMultiplicationOver k M' N').comp
        (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
          (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change (tensorSheafIso F G).hom.app ⊤
      ((tensorSheafUnit M N).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    (tensorSheafUnit M' N').app (op ⊤)
      (F.hom.app ⊤ s ⊗ₜ[Γ(X,⊤)] G.hom.app ⊤ t)
  exact tensorSheafIso_pure_sections F G ⊤ s t

/-- This is an invariant of the actual module sheaves, independently
of frames, divisors, fans, or rational embeddings. -/
theorem moduleSectionMultiplicationOver_surjective_iff_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    Function.Surjective (moduleSectionMultiplicationOver k M N) ↔
      Function.Surjective (moduleSectionMultiplicationOver k M' N') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (tensorSheafIso F G)
  have he (z) : et (moduleSectionMultiplicationOver k M N z) =
      moduleSectionMultiplicationOver k M' N' (es z) :=
    congrArg (fun h=>h z) (moduleSectionMultiplicationOver_sheafIso k F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

namespace CartierData

variable [IsIntegral X] (D E : CartierData X)

/-- Multiplication in the function field is precisely the ordinary
tensor-sheaf section map, followed by the actual O(D)⊗O(E)≅O(D+E). -/
theorem sectionMultiplicationOver_eq_moduleSectionMultiplicationOver :
    (BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)).toLinearMap.comp
      (moduleSectionMultiplicationOver k D.sheaf E.sheaf) =
        D.sectionMultiplicationOver k E := by
  apply TensorProduct.ext'
  intro s t
  change (D.tensorSheafAddIso E).hom.app ⊤
      ((tensorSheafUnit D.sheaf E.sheaf).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    D.sectionProduct E ⊤ s t
  exact D.tensorSheafAddIso_pure_sections E ⊤ s t

theorem sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (moduleSectionMultiplicationOver k D.sheaf E.sheaf) := by
  let et := BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)
  have he (z) : et (moduleSectionMultiplicationOver k D.sheaf E.sheaf z) =
      D.sectionMultiplicationOver k E z :=
    congrArg (fun h=>h z)
      (D.sectionMultiplicationOver_eq_moduleSectionMultiplicationOver k E)
  constructor
  · intro h t
    obtain ⟨z,hz⟩ := h (et t)
    exact ⟨z,et.injective (by rw [he,hz])⟩
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨z,(he z).symm.trans (by rw [hz,ht])⟩

/-- Any actual presentation of a canonical line bundle can be removed
from the final multiplication statement. -/
theorem moduleSectionMultiplicationOver_adjoint_of_cartier
    (K : CartierData X) (ω : X.Modules) (F : K.sheaf≅ω)
    (h : Function.Surjective (D.sectionMultiplicationOver k (E.add K))) :
    Function.Surjective
      (moduleSectionMultiplicationOver k D.sheaf (tensorSheaf E.sheaf ω)) := by
  let G : (E.add K).sheaf≅tensorSheaf E.sheaf ω :=
    (E.tensorSheafAddIso K).symm ≪≫ tensorSheafIso (Iso.refl E.sheaf) F
  exact (moduleSectionMultiplicationOver_surjective_iff_sheafIso k
    (Iso.refl D.sheaf) G).mp
      ((D.sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver k
        (E.add K)).mp h)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.moduleSectionMultiplicationOver_surjective_iff_sheafIso
#print axioms PaperVerification.ToricSchemes.CartierData.moduleSectionMultiplicationOver_adjoint_of_cartier
end
end Source_ToricModuleSectionMultiplication
-- END ORIGINAL PaperVerification.ToricModuleSectionMultiplication


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicAdjointSections
section Source_ToricIntrinsicAdjointSections

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicMixedTheorems
-- original header: public import PaperVerification.ToricFanIntrinsicCanonical
-- original header: public import PaperVerification.ToricIntrinsicDimension
-- original header: public import PaperVerification.ToricInvertibleFractionalPresentation
-- original header: public import PaperVerification.ToricModuleSectionMultiplication
-- original header: public import PaperVerification.ToricCartierSchemeIso

-- original header: @[expose] public section

/-!
# Intrinsic adjoint multiplication on the original toric variety

The canonical factor in the final statement is the genuine top exterior
power of the intrinsic Kähler sheaf. It is defined before choosing a fan.
The fan reconstruction and the actual differential calculation prove its
invertibility and produce a Cartier presentation. Surjectivity is then
transported through the actual scheme and sheaf isomorphisms, and the
presentation is removed from the final section-multiplication statement.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical Pointwise BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance («Σ» : SmoothCompleteFan n) : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

include T in
/-- A canonical Cartier presentation is derived from the genuine
intrinsic cotangent sheaf, with no fan or canonical-divisor input. -/
theorem exists_intrinsicCanonicalCartier
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ K : CartierData X.left,
      Nonempty (K.sheaf≅topDifferentialSheaf k X.left n) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hD
  let e₀ : «Σ».fanScheme k≅X.left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.inv.IsOver (Spec (CommRingCat.of k)) := ⟨e.inv.w⟩
  let b₀ : Module.Basis (Fin n) ℤ (Lattice n) := Pi.basisFun ℤ (Fin n)
  let «KΣ» := «Σ».differentialVolumeData k hpure b₀
  refine ⟨«KΣ».dominantPullback e₀.inv,⟨?_⟩⟩
  exact («KΣ».dominantPullbackSheafIso e₀.inv).symm ≪≫
    (Scheme.Modules.pullback e₀.inv).mapIso
      («Σ».intrinsicTopDifferentialVolumeIso k hpure b₀).symm ≪≫
    topDifferentialSheafPullbackIso e₀.inv n k

include T in
theorem intrinsicCanonical_isInvertible
    (D : CartierData X.left) (hD : D.IsAmple) :
    IsInvertibleModule (topDifferentialSheaf k X.left n) := by
  obtain ⟨K,⟨F⟩⟩ := T.exists_intrinsicCanonicalCartier D hD
  exact isInvertibleModule_of_iso F K.locallyFree

/-- An actual Cartier presentation whose underlying sheaf is literally
the intrinsic canonical sheaf. Its fractional embedding is constructed. -/
def intrinsicCanonicalCartier
    (D : CartierData X.left) (hD : D.IsAmple) : CartierData X.left :=
  invertibleFractionalPresentation (topDifferentialSheaf k X.left n)
    (T.intrinsicCanonical_isInvertible D hD)

@[simp] theorem intrinsicCanonicalCartier_sheaf
    (D : CartierData X.left) (hD : D.IsAmple) :
    (T.intrinsicCanonicalCartier D hD).sheaf=topDifferentialSheaf k X.left n := rfl

include T in
/-- The Cartier notation A, B+K has its usual multiplication meaning
for every genuine canonical presentation, independently of its rational
frame or its particular representative as a divisor. -/
theorem adjointSectionMultiplication_of_canonical
    (D E K : CartierData X.left)
    (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1))
    (hK : K.sheaf≅topDifferentialSheaf k X.left n) :
    Function.Surjective (D.sectionMultiplicationOver k (E.add K)) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hampleD
  letI := hequiv
  let e₀ : «Σ».fanScheme k≅X.left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.hom.IsOver (Spec (CommRingCat.of k)) := ⟨e.hom.w⟩
  let F := D.dominantPullback e₀.hom
  let G := E.dominantPullback e₀.hom
  let b₀ : Module.Basis (Fin n) ℤ (Lattice n) := Pi.basisFun ℤ (Fin n)
  let «KΣ» := «Σ».differentialVolumeData k hpure b₀
  have hF : «Σ».CartierWallDegreesAtLeast k F (n+1) :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k F (n+1)
      (invariantCurveDegreesAtLeast_pullbackIso e D (n+1) hD)
  have hG : «Σ».CartierWallDegreesAtLeast k G (n+1) :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k G (n+1)
      (invariantCurveDegreesAtLeast_pullbackIso e E (n+1) hE)
  let H : (K.dominantPullback e₀.hom).sheaf≅«KΣ».sheaf :=
    (K.dominantPullbackSheafIso e₀.hom).symm ≪≫
      (Scheme.Modules.pullback e₀.hom).mapIso hK ≪≫
      topDifferentialSheafPullbackIso e₀.hom n k ≪≫
      «Σ».intrinsicTopDifferentialVolumeIso k hpure b₀
  let J : ((E.add K).dominantPullback e₀.hom).sheaf≅(G.add «KΣ»).sheaf :=
    (E.dominantPullback_add_equivalent K e₀.hom).choose ≪≫
      G.addSheafIso G (K.dominantPullback e₀.hom) «KΣ» (Iso.refl G.sheaf) H
  apply (D.sectionMultiplicationOver_surjective_iff_schemeIso k e₀ (E.add K)).mpr
  apply (F.sectionMultiplicationOver_surjective_iff_sheafIso k F
    ((E.add K).dominantPullback e₀.hom) (G.add «KΣ») (Iso.refl F.sheaf) J).mpr
  exact «Σ».fanDivisor_adjointSectionMultiplication k hpure F G hF hG b₀

include T in
/-- Theorem 1.3, using the actual base-field tensor map of actual global
sections and the genuine intrinsic canonical sheaf. The theorem has no
assumption supplying a fan, a canonical presentation, a section-space
identification, or a classification theorem. -/
theorem toric_theorem_1_3_sections
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    Function.Surjective
      (moduleSectionMultiplicationOver k D.sheaf
        (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) := by
  let K := T.intrinsicCanonicalCartier D hampleD
  have hK : K.sheaf≅topDifferentialSheaf k X.left n := Iso.refl _
  exact D.moduleSectionMultiplicationOver_adjoint_of_cartier k E K
    (topDifferentialSheaf k X.left n) hK
    (T.adjointSectionMultiplication_of_canonical D E K hampleD hampleE hD hE hK)

/-- Both formulations of Theorem 1.3 on the original intrinsic variety. -/
theorem toric_theorem_1_3
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    ({m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)}) ∧
      Function.Surjective
        (moduleSectionMultiplicationOver k D.sheaf
          (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) :=
  ⟨T.toric_theorem_1_3_latticePoints D E hampleD hampleE hD hE,
    T.toric_theorem_1_3_sections D E hampleD hampleE hD hE⟩

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.intrinsicCanonical_isInvertible
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3_sections
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3
end
end Source_ToricIntrinsicAdjointSections
-- END ORIGINAL PaperVerification.ToricIntrinsicAdjointSections


-- BEGIN ORIGINAL PaperVerification.ToricEquivariantPullbacks
section Source_ToricEquivariantPullbacks

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicAction
-- original header: public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

-- original header: @[expose] public section

/-!
# Actual equivariant fibre products

The action on a fibre product is constructed by its categorical universal
property.  Both projections are genuine equivariant morphisms.  Forgetting
the base scheme preserves this pullback, so the construction supplies the
actual invariant affine restrictions used in the orbit classification.
-/

noncomputable section

universe v u

namespace PaperVerification.ToricSchemes

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (G : C) [MonObj G] {X Y Z : C}
    [ModObj G X] [ModObj G Y] [ModObj G Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsModHom G f] [IsModHom G g]
    [HasPullback f g]

def equivariantPullbackActionMap : G ⊗ pullback f g ⟶ pullback f g :=
  pullback.lift
    (G ◁ pullback.fst f g ≫ γ[G,X])
    (G ◁ pullback.snd f g ≫ γ[G,Y]) (by
      have hf := IsModHom.smul_hom (A := G) (f := f)
      have hg := IsModHom.smul_hom (A := G) (f := g)
      change γ[G,X] ≫ f = G ◁ f ≫ γ[G,Z] at hf
      change γ[G,Y] ≫ g = G ◁ g ≫ γ[G,Z] at hg
      rw [Category.assoc, hf, ← whiskerLeft_comp_assoc,
        pullback.condition, whiskerLeft_comp, Category.assoc, ← hg, Category.assoc])

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_fst :
    equivariantPullbackActionMap G f g ≫ pullback.fst f g =
      G ◁ pullback.fst f g ≫ γ[G,X] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem equivariantPullbackActionMap_snd :
    equivariantPullbackActionMap G f g ≫ pullback.snd f g =
      G ◁ pullback.snd f g ≫ γ[G,Y] :=
  pullback.lift_snd _ _ _

/-- Actions on schemes, rather than only actions on geometric points,
are preserved by an equivariant fibre product. -/
def equivariantPullbackModObj : ModObj G (pullback f g) where
  smul := equivariantPullbackActionMap G f g
  one_smul := by
    change (η[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (λ_ (pullback f g)).hom
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whisker_exchange_assoc, ModObj.one_smul_self,
        leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ pullback f g) ≫ equivariantPullbackActionMap G f g =
      (α_ G G (pullback f g)).hom ≫
        (G ◁ equivariantPullbackActionMap G f g) ≫ equivariantPullbackActionMap G f g
    apply pullback.hom_ext
    · simp only [Category.assoc, equivariantPullbackActionMap_fst]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_fst,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]
    · simp only [Category.assoc, equivariantPullbackActionMap_snd]
      rw [← whiskerLeft_comp_assoc, equivariantPullbackActionMap_snd,
        whiskerLeft_comp, ← whisker_exchange_assoc,
        ModObj.mul_smul_self, associator_naturality_right_assoc]
      simp only [Category.assoc]

theorem equivariantPullback_fst_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.fst f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_fst G f g⟩

theorem equivariantPullback_snd_isModHom :
    letI := equivariantPullbackModObj G f g
    IsModHom G (pullback.snd f g) := by
  letI := equivariantPullbackModObj G f g
  exact ⟨equivariantPullbackActionMap_snd G f g⟩

end Categorical

open AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The underlying square is the actual scheme-theoretic fibre product.
Connected-limit preservation is a theorem of the ordinary over category. -/
theorem overPullback_isPullback :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f g)

theorem overPullback_fst_isClosedImmersion [IsClosedImmersion g.left] :
    IsClosedImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g).flip inferInstance

theorem overPullback_snd_isOpenImmersion [IsOpenImmersion f.left] :
    IsOpenImmersion (pullback.snd f g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback f g) inferInstance

/-- An actual point in the inverse image of an open chart produces a
point of the equivariant pullback, including its residue-field data. -/
theorem overPullback_nonempty [IsOpenImmersion f.left]
    (y : Y.left) (hy : g.left y ∈ f.left.opensRange) :
    Nonempty (pullback f g).left := by
  have hy' : y ∈ Set.range (pullback.snd f.left g.left) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hy
  obtain ⟨p, hp⟩ := hy'
  exact ⟨(overPullback_isPullback f g).isoPullback.inv p⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.equivariantPullbackModObj
#print axioms PaperVerification.ToricSchemes.overPullback_isPullback
end
end Source_ToricEquivariantPullbacks
-- END ORIGINAL PaperVerification.ToricEquivariantPullbacks


-- BEGIN ORIGINAL PaperVerification.ToricAffineActionCoaction
section Source_ToricAffineActionCoaction

-- original header: module

-- original header: public import PaperVerification.ToricTorusAction
-- original header: public import Mathlib.AlgebraicGeometry.Group.Affine

-- original header: @[expose] public section

/-!
# Comorphisms of actual affine torus actions

The coaction of an arbitrary affine torus scheme is extracted from its
actual action morphism by the fully faithful affine Spec functor and
the proved tensor-product/fiber-product isomorphism. Equivariance of
actual scheme maps implies the corresponding algebraic coaction equation.
-/

noncomputable section

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped TensorProduct

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).Monoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).OplaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toOplaxMonoidal

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "T" => op (CommAlgCat.of k (AddMonoidAlgebra k M))
local notation "G" => splitTorusOver k M

/-- The actual semigroup action, on the literally bundled affine Spec object. -/
instance semigroupChart_algSpec_torusAction (S : AddSubmonoid M) :
    ModObj G ((F).obj (op (CommAlgCat.of k (AddMonoidAlgebra k S)))) := by
  change ModObj G (semigroupChartOver k S)
  exact semigroupChart_torusAction k S

def affineTorusActionArrow (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] : T⊗op B⟶op B :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).preimage
    (Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)])

@[simp] theorem affineTorusActionArrow_spec (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    (F).map (affineTorusActionArrow k M B)=
      Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)] :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).map_preimage _

/-- The literal algebra comorphism of the given action. -/
def affineTorusActionCoaction (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    B→ₐ[k]AddMonoidAlgebra k M⊗[k]B :=
  (affineTorusActionArrow k M B).unop.hom

theorem affineTorusActionArrow_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (f : op B⟶op C) [IsModHom G ((F).map f)] :
    affineTorusActionArrow k M B≫f=
      (T◁f)≫affineTorusActionArrow k M C := by
  let a : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op B) := γ[G,(F).obj (op B)]
  let b : (F).obj T ⊗ (F).obj (op C) ⟶ (F).obj (op C) := γ[G,(F).obj (op C)]
  have ha : (F).map (affineTorusActionArrow k M B) =
      Functor.OplaxMonoidal.δ F T (op B) ≫ a := affineTorusActionArrow_spec k M B
  have hb : (F).map (affineTorusActionArrow k M C) =
      Functor.OplaxMonoidal.δ F T (op C) ≫ b := affineTorusActionArrow_spec k M C
  have heq : a ≫ (F).map f = ((F).obj T ◁ (F).map f) ≫ b :=
    IsModHom.smul_hom (A := G) (f := (F).map f)
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  calc
    (F).map (affineTorusActionArrow k M B ≫ f) =
        (F).map (affineTorusActionArrow k M B) ≫ (F).map f := (F).map_comp _ _
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ a) ≫ (F).map f :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj (op B) => g ≫ (F).map f) ha
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (a ≫ (F).map f) := Category.assoc _ _ _
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (((F).obj T ◁ (F).map f) ≫ b) :=
      congrArg (fun g : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op C) =>
        Functor.OplaxMonoidal.δ F T (op B) ≫ g) heq
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ ((F).obj T ◁ (F).map f)) ≫ b :=
      (Category.assoc _ _ _).symm
    _ = ((F).map (T ◁ f) ≫ Functor.OplaxMonoidal.δ F T (op C)) ≫ b :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj T ⊗ (F).obj (op C) => g ≫ b)
        (Functor.OplaxMonoidal.δ_natural_right F T f)
    _ = (F).map (T ◁ f) ≫ (Functor.OplaxMonoidal.δ F T (op C) ≫ b) :=
      Category.assoc _ _ _
    _ = (F).map (T ◁ f) ≫ (F).map (affineTorusActionArrow k M C) :=
      congrArg (fun g : (F).obj (T ⊗ op C) ⟶ (F).obj (op C) => (F).map (T ◁ f) ≫ g) hb.symm
    _ = (F).map ((T ◁ f) ≫ affineTorusActionArrow k M C) := ((F).map_comp _ _).symm

/-- Naturality is obtained from actual equivariance, for arbitrary
affine actions on the source and target. -/
theorem affineTorusActionCoaction_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (q : C→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q).comp
        (affineTorusActionCoaction k M C)=
      (affineTorusActionCoaction k M B).comp q := by
  have h := congrArg (fun f : T⊗op B⟶op C=>f.unop.hom)
    (affineTorusActionArrow_natural k M (CommAlgCat.ofHom q).op)
  exact h.symm

theorem affineTorusActionCoaction_semigroup (S : AddSubmonoid M) :
    affineTorusActionCoaction k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      semigroupChartCoaction k S := by
  have h : affineTorusActionArrow k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op := by
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    rw [affineTorusActionArrow_spec]
    apply Over.OverMorphism.ext
    change (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (AddMonoidAlgebra k M))
        (CommRingCat.of (AddMonoidAlgebra k S))).inv≫
      (γ[G,semigroupChartOver k S]).left=
        Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom)
    rw [semigroupChart_action_spec]
    exact (pullbackSpecIso (CommRingCat.of k)
      (CommRingCat.of (AddMonoidAlgebra k M))
      (CommRingCat.of (AddMonoidAlgebra k S))).inv_hom_id_assoc
        (Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom))
  exact congrArg (fun f=>f.unop.hom) h

/-- Vanishing in an actual equivariant affine quotient is preserved by
the true semigroup coaction after applying that quotient in the second
factor. No character-stability hypothesis appears. -/
theorem semigroupCoaction_quotient_zero (S : AddSubmonoid M)
    (B : CommAlgCat.{max u v} k) [ModObj G ((F).obj (op B))]
    (q : AddMonoidAlgebra k S→ₐ[k]B)
    [IsModHom G ((F).map (CommAlgCat.ofHom q).op)]
    {f : AddMonoidAlgebra k S} (hf : q f=0) :
    Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q
      (semigroupChartCoaction k S f)=0 := by
  have h := congrArg
    (fun φ : AddMonoidAlgebra k S →ₐ[k] AddMonoidAlgebra k M ⊗[k] B => φ f)
    (affineTorusActionCoaction_natural k M
      (B := B) (C := CommAlgCat.of k (AddMonoidAlgebra k S)) q)
  rw [affineTorusActionCoaction_semigroup] at h
  simpa only [AlgHom.comp_apply,hf,map_zero] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.semigroupCoaction_quotient_zero
end
end Source_ToricAffineActionCoaction
-- END ORIGINAL PaperVerification.ToricAffineActionCoaction


-- BEGIN ORIGINAL PaperVerification.ToricMonomialPrimeFaces
section Source_ToricMonomialPrimeFaces

-- original header: module

-- original header: public import PaperVerification.ToricAffineActionCoaction
-- original header: public import PaperVerification.ToricOrbitChartQuotient
-- original header: public import Mathlib.RingTheory.Ideal.Quotient.Operations

-- original header: @[expose] public section

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
end
end Source_ToricMonomialPrimeFaces
-- END ORIGINAL PaperVerification.ToricMonomialPrimeFaces


-- BEGIN ORIGINAL PaperVerification.ToricSmoothMonoidFaces
section Source_ToricSmoothMonoidFaces

-- original header: module

-- original header: public import PaperVerification.ToricOrbitQuotientCoordinates

-- original header: @[expose] public section

/-!
# Additive faces of an actual smooth full cone

A full smooth dual cone is the nonnegative integer span of an integral
basis. Every additive face is obtained by forcing a subset of those
coordinates to zero. This is proved by basis expansion and the actual
additive-face property.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]
    (b : Module.Basis ι ℤ E)

abbrev fullCoordinateMonoid := coordinateConeMonoid b Finset.univ

def fullConeBasisVector (i : ι) : fullCoordinateMonoid b :=
  ⟨b i,by
    intro j hj
    rw [b.repr_self_apply]
    split_ifs <;> norm_num⟩

@[simp] theorem fullConeBasisVector_repr (i j : ι) :
    b.repr (fullConeBasisVector b i).val j=if i=j then 1 else 0 :=
  b.repr_self_apply (i := i) j

theorem fullCoordinate_nonneg (x : fullCoordinateMonoid b) (i : ι) :
    0≤b.repr x.val i := x.property i (Finset.mem_univ i)

theorem fullCoordinate_basis_sum (x : fullCoordinateMonoid b) :
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i)=x := by
  apply Subtype.ext
  change (fullCoordinateMonoid b).subtype
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i) = x.val
  rw [map_sum]
  simp only [map_nsmul]
  change (∑ i,(b.repr x.val i).toNat • b i)=x.val
  calc
    _=(∑ i,b.repr x.val i • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← natCast_zsmul,Int.toNat_of_nonneg (fullCoordinate_nonneg b x i)]
    _=x.val :=
      (Finset.sum_congr rfl (fun i _ =>
        (int_smul_eq_zsmul (inferInstance : Module ℤ E)
          (b.repr x.val i) (b i)).symm)).trans (b.sum_repr x.val)

def fullConeSubtractBasis (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) : fullCoordinateMonoid b :=
  ⟨x.val-b i,by
    intro j hj
    rw [map_sub,Finsupp.sub_apply,b.repr_self_apply]
    by_cases h : i=j
    · subst j
      simp only [if_pos rfl]
      omega
    · simp only [if_neg h,sub_zero]
      exact fullCoordinate_nonneg b x j⟩

theorem fullConeSubtractBasis_add (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) :
    fullConeBasisVector b i+fullConeSubtractBasis b x i hi=x := by
  apply Subtype.ext
  change b i+(x.val-b i)=x.val
  abel

theorem additiveFace_basis_mem_of_coordinate_pos
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    {x : fullCoordinateMonoid b} (hx : x∈F) (i : ι)
    (hi : 0<b.repr x.val i) : fullConeBasisVector b i∈F := by
  have hsum : fullConeBasisVector b i+fullConeSubtractBasis b x i hi∈F := by
    rwa [fullConeSubtractBasis_add]
  exact (hF _ _ hsum).1

/-- Exactly the coordinates omitted by an additive face. -/
def forbiddenFaceCoordinates (F : AddSubmonoid (fullCoordinateMonoid b)) : Finset ι :=
  Finset.univ.filter (fun i=>fullConeBasisVector b i∉F)

theorem additiveFace_mem_iff_zero_coordinates
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    (x : fullCoordinateMonoid b) :
    x∈F ↔ ∀ i∈forbiddenFaceCoordinates b F,b.repr x.val i=0 := by
  constructor
  · intro hx i hi
    have hnot := (Finset.mem_filter.mp hi).2
    have hn := fullCoordinate_nonneg b x i
    by_contra hz
    have hp : 0<b.repr x.val i := lt_of_le_of_ne hn (Ne.symm hz)
    exact hnot (additiveFace_basis_mem_of_coordinate_pos b F hF hx i hp)
  · intro hx
    rw [← fullCoordinate_basis_sum b x]
    apply F.sum_mem
    intro i hi
    by_cases hmem : fullConeBasisVector b i∈F
    · exact F.nsmul_mem hmem _
    · have hz := hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hmem⟩)
      simp only [hz,Int.toNat_zero,zero_nsmul,F.zero_mem]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))

def fullDualConeBasisVector (i : Fin n) :
    dualConeMonoid (Finset.univ.image b) :=
  ⟨integralDualBasis b i,by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,(integralDualBasis b).repr_self_apply]
    split_ifs <;> norm_num⟩

def fullDualForbiddenCoordinates
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b))) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>fullDualConeBasisVector b i∉F)

/-- Every actual additive face of a smooth full dual cone is the face
annihilating an actual subset of the original primitive cone rays. -/
theorem fullDual_additiveFace_eq_orbitFace
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b)))
    (hF : IsAdditiveFace F) :
    F=orbitCharacterFace (Finset.univ.image b)
      ((fullDualForbiddenCoordinates b F).image b) := by
  have he : dualConeMonoid (Finset.univ.image b)=
      fullCoordinateMonoid (integralDualBasis b) := dualConeMonoid_basis_eq b Finset.univ
  let e : dualConeMonoid (Finset.univ.image b)≃+
      fullCoordinateMonoid (integralDualBasis b) :=
    { toFun x := ⟨x.val,he ▸ x.property⟩
      invFun x := ⟨x.val,he.symm ▸ x.property⟩
      left_inv x := Subtype.ext rfl
      right_inv x := Subtype.ext rfl
      map_add' x y := Subtype.ext rfl }
  let F' := F.map e.toAddMonoidHom
  have hF' : IsAdditiveFace F' := by
    intro x y h
    obtain ⟨z,hz,hzxy⟩ := h
    have heq : z=e.symm x+e.symm y := by
      apply e.injective
      simpa using hzxy
    have hm := hF _ _ (heq ▸ hz)
    exact ⟨⟨e.symm x,hm.1,e.apply_symm_apply x⟩,
      ⟨e.symm y,hm.2,e.apply_symm_apply y⟩⟩
  have hmem (x : dualConeMonoid (Finset.univ.image b)) : e x∈F'↔x∈F := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have haxis (i : Fin n) : e (fullDualConeBasisVector b i)=
      fullConeBasisVector (integralDualBasis b) i := by
    apply Subtype.ext
    rfl
  have hind : forbiddenFaceCoordinates (integralDualBasis b) F'=
      fullDualForbiddenCoordinates b F := by
    ext i
    simp only [forbiddenFaceCoordinates,fullDualForbiddenCoordinates,Finset.mem_filter,
      Finset.mem_univ,true_and,← haxis,hmem]
  ext x
  rw [← hmem x,additiveFace_mem_iff_zero_coordinates _ F' hF',hind]
  change (∀ i∈fullDualForbiddenCoordinates b F,
    (integralDualBasis b).repr x.val i=0) ↔
      ∀ u∈(fullDualForbiddenCoordinates b F).image b,integerPairing u x.val=0
  constructor
  · intro hx u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate]
    exact hx i hi
  · intro hx i hi
    rw [← integerPairing_basis_eq_dualCoordinate]
    exact hx (b i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.fullDual_additiveFace_eq_orbitFace
end
end Source_ToricSmoothMonoidFaces
-- END ORIGINAL PaperVerification.ToricSmoothMonoidFaces


-- BEGIN ORIGINAL PaperVerification.ToricInvariantChartPrimes
section Source_ToricInvariantChartPrimes

-- original header: module

-- original header: public import PaperVerification.ToricMonomialPrimeFaces
-- original header: public import PaperVerification.ToricSmoothMonoidFaces
-- original header: public import PaperVerification.ToricChartActions
-- original header: public import PaperVerification.ToricOrbitChartMaps
-- original header: public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

-- original header: @[expose] public section

/-!
# Actual invariant prime closed subschemes of smooth affine charts

An arbitrary integral affine quotient with its genuine equivariant
torus action has a monomial prime kernel. The actual smooth basis then
identifies this kernel with the literal coordinate-face orbit quotient.
The final statement is equality of actual scheme ideal sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped Classical

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_ringKernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      RingHom.ker q.toRingHom=
        RingHom.ker (orbitQuotientAlgebraMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).toRingHom := by
  let e := monoidChartAlgebraEquiv k S
  let q' := q.comp e.toAlgHom
  let f₀ : (F).obj (op B) ⟶ monoidChartSchemeOver k S :=
    (F).map (CommAlgCat.ofHom q).op
  letI : IsModHom G f₀ :=
    inferInstanceAs (IsModHom G ((F).map (CommAlgCat.ofHom q).op))
  have hspec : (F).map (CommAlgCat.ofHom q').op=
      f₀≫(monoidChartSchemeOverIso k S).hom := by
    change (F).map (CommAlgCat.ofHom q').op =
      (F).map (CommAlgCat.ofHom q).op ≫
        (F).map (CommAlgCat.ofHom e.toAlgHom).op
    exact (F).map_comp (CommAlgCat.ofHom q).op (CommAlgCat.ofHom e.toAlgHom).op
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q').op) :=
    hspec.symm ▸ (inferInstance : IsModHom G (f₀≫(monoidChartSchemeOverIso k S).hom))
  let P := RingHom.ker q'.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime q'.toRingHom
  have hP : IsMonomialIdeal k P := fun f hf m=>equivariant_kernel_component k S B q' hf m
  let J := survivingCharacterFace k P
  let I := fullDualForbiddenCoordinates b J
  have hJ : J=orbitCharacterFace s (I.image b) :=
    fullDual_additiveFace_eq_orbitFace b J (survivingCharacterFace_isAdditiveFace k P)
  have hker := monomialPrime_eq_face_kernel k P hP
  change P=RingHom.ker (additiveFaceRetraction k J
    (survivingCharacterFace_isAdditiveFace k P)).toRingHom at hker
  have hfaceKernel (J₁ J₂ : AddSubmonoid S)
      (h₁ : IsAdditiveFace J₁) (h₂ : IsAdditiveFace J₂) (h : J₁ = J₂) :
      RingHom.ker (additiveFaceRetraction k J₁ h₁).toRingHom =
        RingHom.ker (additiveFaceRetraction k J₂ h₂).toRingHom := by
    cases h
    rfl
  have hker := hker.trans (hfaceKernel J (orbitCharacterFace s (I.image b))
    (survivingCharacterFace_isAdditiveFace k P)
    (orbitCharacterFace_isAdditiveFace s (I.image b)
      (Finset.image_subset_image (Finset.subset_univ I))) hJ)
  refine ⟨I,?_⟩
  ext f
  rw [RingHom.mem_ker,RingHom.mem_ker]
  change q f = 0 ↔ orbitQuotientAlgebraMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I)) f = 0
  have hz : q f=0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)=0 := by
    have he := Iff.of_eq
      (congrArg (fun K : Ideal (AddMonoidAlgebra k S)=>e.symm f∈K) hker)
    change q (e (e.symm f)) = 0 ↔
      additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b)
          (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f) = 0 at he
    simpa only [AlgEquiv.apply_symm_apply] using he
  rw [hz]
  let e₁ := AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)
  let e₂ := monoidChartAlgebraEquiv k (dualConeMonoid (orbitQuotientCone b I s))
  let z : AddMonoidAlgebra k (orbitCharacterFace s (I.image b)) :=
    additiveFaceRetraction k (orbitCharacterFace s (I.image b))
      (orbitCharacterFace_isAdditiveFace s (I.image b)
        (Finset.image_subset_image (Finset.subset_univ I))) (e.symm f)
  change z = 0 ↔ e₂ (e₁ z) = 0
  constructor
  · intro h
    rw [h,map_zero,map_zero]
  · intro h
    apply e₁.injective
    apply e₂.injective
    simpa only [map_zero] using h

end PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical

/-- Equal affine coordinate kernels give equal actual scheme ideal
sheaves through the proved ΓSpec natural isomorphisms. -/
theorem specMap_kernel_eq_of_ringKernel_eq
    {A B C : CommRingCat.{u}} (f : A⟶B) (g : A⟶C)
    (h : RingHom.ker f.hom=RingHom.ker g.hom) :
    (Spec.map f).ker=(Spec.map g).ker := by
  rw [Scheme.ker_of_isAffine,Scheme.ker_of_isAffine]
  congr 1
  ext a
  have hf : (Spec.map f).appTop a=0 ↔ f ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality f)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso B).hom ((Spec.map f).appTop a) =
        (Scheme.ΓSpecIso B).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  have hg : (Spec.map g).appTop a=0 ↔ g ((Scheme.ΓSpecIso A).hom a)=0 := by
    have he := congrArg (fun φ=>φ a) (Scheme.ΓSpecIso_naturality g)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he.symm
    · intro hz
      apply (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso C).hom ((Spec.map g).appTop a) =
        (Scheme.ΓSpecIso C).hom 0
      simpa only [ConcreteCategory.comp_apply,hz,map_zero] using he
  rw [RingHom.mem_ker,RingHom.mem_ker,hf,hg]
  simpa only [RingHom.mem_ker] using
    Iff.of_eq (congrArg (fun I : Ideal A=>(Scheme.ΓSpecIso A).hom a∈I) h)

variable (k : Type u) [Field k] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))

local notation "s" => Finset.univ.image b
local notation "S" => dualConeMonoid s
local notation "R" => monoidChartAlgebra k S
local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "G" => splitTorusOver k (Lattice n)

local instance fullChart_algSpec_torusAction :
    ModObj G ((F).obj (op (CommAlgCat.of k R))) := by
  change ModObj G (monoidChartSchemeOver k S)
  exact monoidChartScheme_torusAction k S

theorem invariant_fullCone_Spec_kernel
    (B : CommAlgCat.{u} k) [IsDomain B]
    [ModObj G ((F).obj (op B))]
    (q : R→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    ∃ I : Finset (Fin n),
      (Spec.map (CommRingCat.ofHom q.toRingHom)).ker=
        (orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  obtain ⟨I,hI⟩ := invariant_fullCone_ringKernel k b B q
  exact ⟨I,specMap_kernel_eq_of_ringKernel_eq _ _ hI⟩

/-- Every actual invariant integral closed subscheme of a full smooth
chart is exactly one of its coordinate-face orbit closures. The source
is any integral scheme with an actual group-scheme action; affineness,
the coordinate quotient, and character stability are all derived. -/
theorem invariant_integral_closed_fullChart_kernel
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s
        (Finset.image_subset_image (Finset.subset_univ I))).ker := by
  letI : IsAffine (monoidChartSchemeOver k S).left := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  letI : Y.left.Over (Spec (CommRingCat.of k)) := OverClass.fromOver Y
  letI : IsAffine Y.left := (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).1
  let ρ : CommRingCat.of k ⟶ Γ(Y.left,⊤) :=
    (Spec.fullyFaithful.preimage (Y.left.isoSpec.inv ≫ Y.hom)).unop
  letI : Algebra k Γ(Y.left,⊤) := ρ.hom.toAlgebra
  let B : CommAlgCat.{u} k := CommAlgCat.of k Γ(Y.left,⊤)
  have hρ : Spec.map ρ = Y.left.isoSpec.inv ≫ Y.hom :=
    Spec.fullyFaithful.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let e : Y≅(F).obj (op B) := Over.isoMk Y.left.isoSpec (by
    change Y.left.isoSpec.hom ≫ Spec.map ρ = Y.hom
    rw [hρ,Iso.hom_inv_id_assoc])
  letI : IsMonHom (Iso.refl G).hom := by
    change IsMonHom (𝟙 G)
    infer_instance
  letI : ModObj G ((F).obj (op B)) := ModObj.ofIso (Iso.refl G) e
  letI : IsModHom G e.hom := by
    refine ⟨?_⟩
    change γ[G,Y]≫e.hom=
      (G◁e.hom)≫((𝟙 G⊗ₘe.inv)≫γ[G,Y]≫e.hom)
    simp only [id_tensorHom,← Category.assoc,← whiskerLeft_comp,Iso.hom_inv_id,
      whiskerLeft_id,Category.id_comp]
  let f₀ : Y ⟶ (F).obj (op (CommAlgCat.of k R)) := f
  letI : IsModHom G f₀ := inferInstanceAs (IsModHom G f)
  let q : R→ₐ[k]B :=
    ((algSpec.fullyFaithful («R» := CommRingCat.of k)).preimage
      (X := op B) (Y := op (CommAlgCat.of k R)) (e.inv≫f₀)).unop.hom
  have hq : (F).map (CommAlgCat.ofHom q).op=e.inv≫f₀ :=
    (algSpec.fullyFaithful («R» := CommRingCat.of k)).map_preimage (e.inv≫f₀)
  letI : IsModHom G ((F).map (CommAlgCat.ofHom q).op) := by
    rw [hq]
    infer_instance
  obtain ⟨I,hI⟩ := invariant_fullCone_Spec_kernel k b B q
  refine ⟨I,?_⟩
  have hleft := congrArg (fun g=>g.left) hq
  change Spec.map (CommRingCat.ofHom q.toRingHom)=e.inv.left≫f.left at hleft
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hcomp : (e.inv.left ≫ f.left).ker = f.left.ker :=
    Scheme.Hom.ker_comp_of_isIso e₀.inv f.left
  have hker : (Spec.map (CommRingCat.ofHom q.toRingHom)).ker =
      (e.inv.left ≫ f.left).ker :=
    congrArg (fun g : ((F).obj (op B)).left ⟶ (monoidChartSchemeOver k S).left => g.ker) hleft
  exact hcomp.symm.trans (hker.symm.trans hI)

/-- The ideal equality yields an actual local scheme isomorphism over
the original chart, using the universal property of closed immersions. -/
theorem invariant_integral_closed_fullChart_exists_faceIso
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k S)
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),
      ∃ e : Y.left≅coneChart k (orbitQuotientCone b I s),
        e.hom≫orbitQuotientChartMap k b I s
          (Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  obtain ⟨I,hI⟩ := invariant_integral_closed_fullChart_kernel k b Y f
  let g : coneChart k (orbitQuotientCone b I s) ⟶
      (monoidChartSchemeOver k S).left := orbitQuotientChartMap k b I s
    (Finset.image_subset_image (Finset.subset_univ I))
  letI : IsClosedImmersion g := inferInstanceAs
    (IsClosedImmersion (orbitQuotientChartMap k b I s
      (Finset.image_subset_image (Finset.subset_univ I))))
  letI := IsClosedImmersion.isIso_lift g f.left hI.symm
  exact ⟨I,asIso (IsClosedImmersion.lift g f.left hI.symm.le),
    IsClosedImmersion.lift_fac _ _ _⟩

theorem invariant_integral_closed_fullChart_kernel_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),f.left.ker=
      (orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))).ker := by
  subst s₀
  exact invariant_integral_closed_fullChart_kernel k b Y f

theorem invariant_integral_closed_fullChart_faceIso_of_basis
    (s₀ : Finset (Lattice n)) (hs : s₀=Finset.univ.image b)
    (Y : Over (Spec (CommRingCat.of k))) [IsIntegral Y.left]
    [ModObj G Y]
    (f : Y⟶monoidChartSchemeOver k (dualConeMonoid s₀))
    [IsClosedImmersion f.left] [IsModHom G f] :
    ∃ I : Finset (Fin n),∃ e : Y.left≅coneChart k (orbitQuotientCone b I s₀),
      e.hom≫orbitQuotientChartMap k b I s₀
        (by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ I))=f.left := by
  subst s₀
  exact invariant_integral_closed_fullChart_exists_faceIso k b Y f

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invariant_integral_closed_fullChart_kernel
end
end Source_ToricInvariantChartPrimes
-- END ORIGINAL PaperVerification.ToricInvariantChartPrimes


-- BEGIN ORIGINAL PaperVerification.ToricInvariantOrbitClosure
section Source_ToricInvariantOrbitClosure

-- original header: module

-- original header: public import PaperVerification.ToricEquivariantPullbacks
-- original header: public import PaperVerification.ToricInvariantChartPrimes
-- original header: public import PaperVerification.ToricInvariantCurveBounds
-- original header: public import PaperVerification.ToricMonomialImageComparison
-- original header: public import PaperVerification.ToricFanDimension
-- original header: public import PaperVerification.ToricOrbitActions

-- original header: @[expose] public section

/-!
# Actual invariant integral curves are orbit closures

An invariant integral closed subscheme meets a full affine chart.  Its
actual equivariant pullback has a prime monomial kernel, which is the
coordinate-face kernel.  This gives a common dense open subscheme with
the quotient-star orbit closure.  Equality of the two actual closed
immersion kernels then identifies the whole schemes.  Ordinary Krull
dimension, rather than a prescribed fan rank, forces the quotient fan
of a curve to have rank one.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The orbit-closure classification is derived from the actual action
on an arbitrary integral closed subscheme.  In particular the curve
need not be presented by an orbit or a fan wall. -/
theorem invariantIntegralCurve_isOrbitClosure (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
      (hF : I.image b ∈ «Σ».cones),
      ∃ e : C.curve ≅ («Σ».completeQuotientStarFan b I hF).fanSchemeOver k,
        e.hom.left ≫ «Σ».orbitClosureMap k b I hF = C.inclusion.left := by
  let G := splitTorusOver k (Lattice n)
  obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure
    (C.inclusion.left (genericPoint C.curve.left))
  let j : (coneChart k s.val).asOver (Spec (CommRingCat.of k)) ⟶ «Σ».fanSchemeOver k :=
    («Σ».fanChartMap k («Σ».fullConeIndex s)).asOver (Spec (CommRingCat.of k))
  letI : IsOpenImmersion j.left := by
    change IsOpenImmersion («Σ».fanChartMap k («Σ».fullConeIndex s))
    infer_instance
  letI : IsModHom G j := «Σ».fanChartMap_isModHom k («Σ».fullConeIndex s)
  let Y := pullback j C.inclusion
  let p : Y ⟶ (coneChart k s.val).asOver (Spec (CommRingCat.of k)) :=
    pullback.fst j C.inclusion
  let q : Y ⟶ C.curve := pullback.snd j C.inclusion
  letI : ModObj G Y := equivariantPullbackModObj G j C.inclusion
  letI : IsModHom G p := equivariantPullback_fst_isModHom G j C.inclusion
  letI : IsModHom G q := equivariantPullback_snd_isModHom G j C.inclusion
  letI : IsClosedImmersion p.left := overPullback_fst_isClosedImmersion j C.inclusion
  letI : IsOpenImmersion q.left := overPullback_snd_isOpenImmersion j C.inclusion
  letI : Nonempty Y.left := overPullback_nonempty j C.inclusion
    (genericPoint C.curve.left) hs
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion q.left
  let b := «Σ».fullConeBasis s
  let p₀ : Y ⟶ monoidChartSchemeOver k (dualConeMonoid s.val) := p
  letI : IsClosedImmersion p₀.left := inferInstanceAs (IsClosedImmersion p.left)
  letI : IsModHom G p₀ := inferInstanceAs (IsModHom G p)
  obtain ⟨I, E, hE⟩ := invariant_integral_closed_fullChart_faceIso_of_basis
    k b s.val («Σ».fullConeBasis_ray_set s) Y p₀
  have hIs : I.image b ⊆ s.val := by
    rw [«Σ».fullConeBasis_ray_set s]
    exact Finset.image_subset_image (Finset.subset_univ I)
  have hF : I.image b ∈ «Σ».cones :=
    «Σ».downward s.val («Σ».fullCones_mem s) _ hIs
  let Γ := «Σ».completeQuotientStarFan b I hF
  let t : «Σ».OrbitConeIndex b I := ⟨s.val, «Σ».fullCones_mem s, hIs⟩
  let t₀ : Γ.ConeIndex := «Σ».orbitConeQuotientIndex b I hF t
  let U := coneChart k (orbitQuotientCone b I s.val)
  let a : U ⟶ C.curve.left := E.inv ≫ q.left
  let z : U ⟶ Γ.fanScheme k := Γ.fanChartMap k t₀
  let i : Γ.fanScheme k ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
  let c : C.curve.left ⟶ «Σ».fanScheme k := C.inclusion.left
  let j₀ : coneChart k s.val ⟶ «Σ».fanScheme k := j.left
  let p₁ : Y.left ⟶ coneChart k s.val := p.left
  let f : U ⟶ coneChart k s.val := orbitQuotientChartMap k b I s.val hIs
  letI : IsClosedImmersion c := C.closed
  letI : IsIntegral U := Γ.coneChart_isIntegral k t₀
  letI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (E.inv ≫ q.left))
  letI : IsOpenImmersion z := inferInstanceAs (IsOpenImmersion (Γ.fanChartMap k t₀))
  letI : IsSchemeTheoreticallyDominant a := IsSchemeTheoreticallyDominant.of_isDominant a
  letI : IsSchemeTheoreticallyDominant z := IsSchemeTheoreticallyDominant.of_isDominant z
  letI : IsClosedImmersion i := inferInstanceAs
    (IsClosedImmersion («Σ».orbitClosureMap k b I hF))
  have hpq : p₁ ≫ j₀ = q.left ≫ c :=
    (overPullback_isPullback j C.inclusion).w
  have hE' : E.hom ≫ f = p₁ := hE
  have hinv : E.inv ≫ p₁ = f := by
    calc
      E.inv ≫ p₁ = E.inv ≫ (E.hom ≫ f) :=
        congrArg (fun q : Y.left ⟶ coneChart k s.val => E.inv ≫ q) hE'.symm
      _ = f := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hcommon : a ≫ c = z ≫ i := by
    calc
      a ≫ c = E.inv ≫ (q.left ≫ c) := Category.assoc E.inv q.left c
      _ = E.inv ≫ (p₁ ≫ j₀) :=
        congrArg (fun q : Y.left ⟶ «Σ».fanScheme k => E.inv ≫ q) hpq.symm
      _ = (E.inv ≫ p₁) ≫ j₀ := (Category.assoc E.inv p₁ j₀).symm
      _ = f ≫ j₀ := congrArg (fun q : U ⟶ coneChart k s.val => q ≫ j₀) hinv
      _ = z ≫ i := («Σ».orbitClosureMap_chart k b I hF t).symm
  let F := closedImageIsoOfDenseComposite a z c i hcommon
  have hFmap : F.hom ≫ i = c :=
    closedImageIsoOfDenseComposite_embedding a z c i hcommon
  have hiBase : i ≫ («Σ».fanSchemeOver k).hom = (Γ.fanSchemeOver k).hom :=
    comp_over («Σ».orbitClosureMap k b I hF) (Spec (CommRingCat.of k))
  have hbase : F.hom ≫ (Γ.fanSchemeOver k).hom = C.curve.hom := by
    calc
      F.hom ≫ (Γ.fanSchemeOver k).hom = F.hom ≫ (i ≫ («Σ».fanSchemeOver k).hom) :=
        congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => F.hom ≫ q) hiBase.symm
      _ = (F.hom ≫ i) ≫ («Σ».fanSchemeOver k).hom :=
        (Category.assoc F.hom i («Σ».fanSchemeOver k).hom).symm
      _ = c ≫ («Σ».fanSchemeOver k).hom :=
        congrArg (fun q : C.curve.left ⟶ «Σ».fanScheme k => q ≫ («Σ».fanSchemeOver k).hom) hFmap
      _ = C.curve.hom := C.inclusion.w
  exact ⟨b, I, hF, Over.isoMk F hbase, hFmap⟩

/-- Every genuine invariant integral curve is the projective line over
the original field.  The rank-one conclusion follows from the curve's
ordinary Krull dimension. -/
theorem invariantIntegralCurve_exists_projectiveLineIso (hpure : «Σ».IsPure)
    (C : InvariantIntegralCurve k n («Σ».fanSchemeOver k)) :
    ∃ e : C.curve.left ≅ projectiveLineScheme k,
      e.hom.IsOver (Spec (CommRingCat.of k)) := by
  obtain ⟨b, I, hF, e, he⟩ := «Σ».invariantIntegralCurve_isOrbitClosure k hpure C
  let Γ := «Σ».completeQuotientStarFan b I hF
  have hpureΓ : Γ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hdim : n-I.card = 1 := by
    have h := IsHomeomorph.topologicalKrullDim_eq _
      ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.isHomeomorph
    change topologicalKrullDim C.curve.left = topologicalKrullDim (Γ.fanScheme k) at h
    rw [C.dimension, Γ.fanScheme_topologicalKrullDim k hpureΓ] at h
    exact_mod_cast h.symm
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let e₁ := oneDimensionalFanSchemeIso Γ hdim k
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  change (e.hom.left ≫ e₁.hom).IsOver (Spec (CommRingCat.of k))
  letI : e₁.hom.IsOver (Spec (CommRingCat.of k)) := inferInstanceAs
    ((oneDimensionalFanSchemeIso Γ hdim k).hom.IsOver (Spec (CommRingCat.of k)))
  refine ⟨?_⟩
  change (e.hom.left ≫ e₁.hom) ≫ (projectiveLineScheme k ↘ Spec (CommRingCat.of k)) =
    C.curve.hom
  exact (Category.assoc e.hom.left e₁.hom _).trans
    ((congrArg (fun q : Γ.fanScheme k ⟶ Spec (CommRingCat.of k) => e.hom.left ≫ q)
      (comp_over e₁.hom (Spec (CommRingCat.of k)))).trans e.hom.w)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_isOrbitClosure
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.invariantIntegralCurve_exists_projectiveLineIso
end
end Source_ToricInvariantOrbitClosure
-- END ORIGINAL PaperVerification.ToricInvariantOrbitClosure


-- BEGIN ORIGINAL PaperVerification.ToricRationalCurveDegreeExistence
section Source_ToricRationalCurveDegreeExistence

-- original header: module

-- original header: public import PaperVerification.ToricRationalCurveDegree
-- original header: public import PaperVerification.ToricInvertiblePullback

-- original header: @[expose] public section

/-!
# Existence of the ordinary degree for every invertible sheaf on a rational curve

Every invertible sheaf has an actual fractional Cartier presentation. On
the projective line its integer degree is the unique twist O(d). Pullback
by any genuine isomorphism with the projective line gives existence on a
rational curve; coordinate independence was proved separately.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes

variable (k : Type u) [Field k]

/-- The usual integer degree exists for every actual invertible sheaf
on the projective line, without a chosen divisor presentation. -/
theorem projectiveLineModule_existsUnique_degree
    (M : (projectiveLineScheme k).Modules) (hM : IsInvertibleModule M) :
    ∃! d : ℤ, ProjectiveLineHasDegree k M d := by
  obtain ⟨D,⟨F⟩⟩ := exists_cartierData_of_isInvertibleModule M hM
  obtain ⟨d,hd,_⟩ := projectiveLineCartier_existsUnique_degree k D
  have hMd : ProjectiveLineHasDegree k M d :=
    (projectiveLineHasDegree_iso k F d).mpr hd
  exact ⟨d,hMd,fun e he => projectiveLineHasDegree_unique k he hMd⟩

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]

/-- Every invertible sheaf on a curve genuinely isomorphic to P¹ has
exactly one degree. The isomorphism is over the original base field. -/
theorem rationalCurveModule_existsUnique_degree
    (M : C.Modules) (hM : IsInvertibleModule M)
    (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] :
    ∃! d : ℤ, RationalCurveHasDegree k M d := by
  obtain ⟨d,hd,_⟩ := projectiveLineModule_existsUnique_degree k
    ((Scheme.Modules.pullback e.inv).obj M)
    (isInvertibleModule_pullback e.inv hM)
  have hMd : RationalCurveHasDegree k M d :=
    (rationalCurveHasDegree_iff k M e d).mpr hd
  exact ⟨d,hMd,fun r hr => rationalCurveHasDegree_unique k hr hMd⟩

/-- The degree relation is nonempty precisely when the actual curve is
the projective line over k. In particular, a geometric classification
of invariant curves supplies existence for every restricted line bundle. -/
theorem rationalCurveHasDegree_exists_iff
    (M : C.Modules) (hM : IsInvertibleModule M) :
    (∃ d : ℤ, RationalCurveHasDegree k M d) ↔
      ∃ e : C ≅ projectiveLineScheme k,
        e.hom.IsOver (Spec (CommRingCat.of k)) := by
  constructor
  · rintro ⟨d,e,he,_⟩
    exact ⟨e,he⟩
  · rintro ⟨e,he⟩
    letI := he
    obtain ⟨d,hd,_⟩ := rationalCurveModule_existsUnique_degree k M hM e
    exact ⟨d,hd⟩

/-- Restricting any actual Cartier line bundle along any curve
immersion preserves invertibility, so its degree exists once the curve
has been identified with the projective line. -/
theorem restrictedCartier_existsUnique_degree
    {X : Scheme.{u}} [IsIntegral X]
    (D : CartierData X) (i : C ⟶ X)
    (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] :
    ∃! d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback i).obj D.sheaf) d :=
  rationalCurveModule_existsUnique_degree k _
    (isInvertibleModule_pullback i D.locallyFree) e

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.rationalCurveModule_existsUnique_degree
#print axioms PaperVerification.ToricGeometry.restrictedCartier_existsUnique_degree
end
end Source_ToricRationalCurveDegreeExistence
-- END ORIGINAL PaperVerification.ToricRationalCurveDegreeExistence


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicInvariantCurves
section Source_ToricIntrinsicInvariantCurves

-- original header: module

-- original header: public import PaperVerification.ToricInvariantOrbitClosure
-- original header: public import PaperVerification.ToricIntrinsicMixedTheorems
-- original header: public import PaperVerification.ToricRationalCurveDegreeExistence

-- original header: @[expose] public section

/-!
# Ordinary degrees on all intrinsic invariant curves

Every actual invariant integral curve of a smooth proper split toric
scheme with an ample Cartier divisor is isomorphic over its original
field to P¹.  Consequently every restricted invertible sheaf has its
unique ordinary O(d) degree.  The geometric degree-bound predicate used
in the principal theorems is exactly the inequality for these integers;
it cannot hold merely because some invariant curve has no degree witness.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

include T in
/-- This classifies an arbitrary genuine invariant integral curve, with
no toric presentation or normality premise on the curve itself. -/
theorem invariantCurve_exists_projectiveLineIso
    (A : CartierData X.left) (hA : A.IsAmple)
    (C : InvariantIntegralCurve k n X) :
    ∃ e : C.curve.left ≅ projectiveLineScheme k,
      e.hom.IsOver (Spec (CommRingCat.of k)) := by
  obtain ⟨«Σ», hpure, e, htorus, hequiv⟩ := T.exists_equivariant_completeFan A hA
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.hom := hequiv
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.symm.hom :=
    inferInstanceAs (IsModHom (splitTorusOver k (Fin n → ℤ)) e.inv)
  exact «Σ».invariantIntegralCurve_exists_projectiveLineIso k hpure (C.mapIso e.symm)

include T in
/-- The ordinary degree exists uniquely on every invariant curve for
every actual restricted Cartier line bundle. -/
theorem invariantCurve_restriction_existsUnique_degree
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    ∃! d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d := by
  obtain ⟨e, he⟩ := T.invariantCurve_exists_projectiveLineIso A hA C
  letI := he
  exact restrictedCartier_existsUnique_degree k D C.inclusion.left e

/-- The ordinary integer degree of the restricted line bundle.  The
ample divisor is used only to prove the classification and existence;
the uniqueness theorem below removes this auxiliary choice. -/
def invariantCurveDegree
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) : ℤ :=
  Classical.choose (T.invariantCurve_restriction_existsUnique_degree A hA D C)

theorem invariantCurveDegree_spec
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf)
      (T.invariantCurveDegree A hA D C) :=
  (Classical.choose_spec (T.invariantCurve_restriction_existsUnique_degree A hA D C)).1

theorem invariantCurveDegree_eq_iff
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) (d : ℤ) :
    T.invariantCurveDegree A hA D C = d ↔
      RationalCurveHasDegree k
        ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d := by
  constructor
  · intro h
    rw [← h]
    exact T.invariantCurveDegree_spec A hA D C
  · intro h
    exact rationalCurveHasDegree_unique k (T.invariantCurveDegree_spec A hA D C) h

theorem invariantCurveDegree_independent_ample
    (A B : CartierData X.left) (hA : A.IsAmple) (hB : B.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    T.invariantCurveDegree A hA D C = T.invariantCurveDegree B hB D C :=
  rationalCurveHasDegree_unique k (T.invariantCurveDegree_spec A hA D C)
    (T.invariantCurveDegree_spec B hB D C)

/-- The theorem hypothesis is exactly an inequality for the ordinary
degree of every actual invariant curve, with existence already proved. -/
theorem invariantCurveDegreesAtLeast_iff
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (bound : ℕ) :
    InvariantCurveDegreesAtLeast k n X D bound ↔
      ∀ C : InvariantIntegralCurve k n X,
        (bound : ℤ) ≤ T.invariantCurveDegree A hA D C := by
  constructor
  · intro h C
    exact h C _ (T.invariantCurveDegree_spec A hA D C)
  · intro h C d hd
    rw [← (T.invariantCurveDegree_eq_iff A hA D C d).mpr hd]
    exact h C

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurve_exists_projectiveLineIso
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurve_restriction_existsUnique_degree
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurveDegreesAtLeast_iff
end
end Source_ToricIntrinsicInvariantCurves
-- END ORIGINAL PaperVerification.ToricIntrinsicInvariantCurves


-- BEGIN ORIGINAL PaperVerification.ToricPaperTheorems
section Source_ToricPaperTheorems

-- original header: module

-- original header: public import PaperVerification.ToricMainTheorems
-- original header: public import PaperVerification.ToricIntrinsicAdjointSections
-- original header: public import PaperVerification.ToricIntrinsicInvariantCurves

-- original header: @[expose] public section

/-!
# The intrinsic principal statements with ordinary integer curve degrees

Theorem 1.1 is `ToricGeometry.toric_theorem_1_1`. The two mixed
statements below use the actual degree of each actual restricted line
bundle. Existence and uniqueness of every such degree, and independence
of the auxiliary ample presentation used to construct it, were proved
in the preceding module. The intrinsic section polytopes and the genuine
canonical sheaf keep their definitions independent of the reconstructed fan.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Pointwise BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- Theorem 1.2: prescribed parity for actual ample integral divisors,
with ordinary degrees on all actual invariant integral curves. -/
theorem toric_paper_theorem_1_2
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ)≤T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ)≤T.invariantCurveDegree D hampleD E C)
    (m : Lattice n)
    (hm : embed n m∈interior
      (intrinsicSectionPolytope k n X.left T.torus.left D+
        intrinsicSectionPolytope k n X.left T.torus.left E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈intrinsicSectionPolytope k n X.left T.torus.left D ∧
      embed n b∈intrinsicSectionPolytope k n X.left T.torus.left E ∧
      a+b=m ∧ parityClass n a=α :=
  T.toric_theorem_1_2 D E hampleD hampleE
    ((T.invariantCurveDegreesAtLeast_iff D hampleD D n).mpr hD)
    ((T.invariantCurveDegreesAtLeast_iff D hampleD E n).mpr hE) m hm α

/-- Theorem 1.3 in both of the manuscript's formulations, with no
additional existence premise for degrees or for a canonical Cartier
presentation. The tensor product of sections is over the original field. -/
theorem toric_paper_theorem_1_3
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      ((n+1 : ℕ) : ℤ)≤T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      ((n+1 : ℕ) : ℤ)≤T.invariantCurveDegree D hampleD E C) :
    ({m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)}) ∧
      Function.Surjective
        (moduleSectionMultiplicationOver k D.sheaf
          (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) :=
  T.toric_theorem_1_3 D E hampleD hampleE
    ((T.invariantCurveDegreesAtLeast_iff D hampleD D (n+1)).mpr hD)
    ((T.invariantCurveDegreesAtLeast_iff D hampleD E (n+1)).mpr hE)

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_paper_theorem_1_2
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_paper_theorem_1_3
end
end Source_ToricPaperTheorems
-- END ORIGINAL PaperVerification.ToricPaperTheorems


-- BEGIN ORIGINAL PaperVerification.ToricAdjointCharacters
section Source_ToricAdjointCharacters

-- original header: module

-- original header: public import PaperVerification.ToricMainTheorems
-- original header: public import PaperVerification.ToricCharacterMultiplication

-- original header: @[expose] public section

/-!
# Adjoint multiplication in the actual Laurent character algebra

This composes the unrestricted lattice-point equality with the proved
image of tensor-product multiplication. Identification of these character
modules with scheme-theoretic global sections is a separate sheaf theorem;
it is not built into the definitions used here.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set PaperVerification.ToricCharacters
open scoped Pointwise TensorProduct

variable {n : ℕ} (P Q : LatticePolytope n)

def latticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ P.carrier}

def interiorLatticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ interior P.carrier}

def sumInteriorLatticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ interior (P.minkowskiSum Q)}

theorem latticePoint_add_interior_subset :
    P.latticePointSet + Q.interiorLatticePointSet ⊆ P.sumInteriorLatticePointSet Q := by
  rintro m ⟨a, ha, b, hb, rfl⟩
  exact P.add_mem_interior_minkowskiSum Q a b ha hb

/-- The actual multiplication of Laurent polynomials with the indicated
support restrictions, on the tensor product over the ground field. -/
def adjointCharacterMultiplication (k : Type*) [Field k] :
    characterModule k P.latticePointSet ⊗[k] characterModule k Q.interiorLatticePointSet →ₗ[k]
      characterModule k (P.sumInteriorLatticePointSet Q) :=
  characterMultiplication k P.latticePointSet Q.interiorLatticePointSet
    (P.sumInteriorLatticePointSet Q) (P.latticePoint_add_interior_subset Q)

/-- The mixed theorem gives surjectivity of the genuine multiplication
map over every field, in every characteristic. -/
theorem adjointCharacterMultiplication_surjective (k : Type*) [Field k]
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    Function.Surjective (P.adjointCharacterMultiplication Q k) := by
  apply (characterMultiplication_surjective_iff k _ _ _ _).mpr
  exact (toric_theorem_1_3_polytope_sets n P Q hP hQ hfan hboundP hboundQ).symm

end PaperVerification.ToricGeometry.LatticePolytope

#print axioms PaperVerification.ToricGeometry.LatticePolytope.adjointCharacterMultiplication_surjective
end
end Source_ToricAdjointCharacters
-- END ORIGINAL PaperVerification.ToricAdjointCharacters


-- BEGIN ORIGINAL PaperVerification.ToricCartierDeformations
section Source_ToricCartierDeformations

-- original header: module
-- original header: public import PaperVerification.ToricNormalFan
-- original header: public import Mathlib.Data.Set.Finite.Lemmas
-- original header: @[expose] public section
/-!
# Nonnegative edge degrees give globally feasible Cartier points

This is the elementary polytope form of the nef Cartier criterion. It is proved
on an actual finite reference polytope using a descending edge for every
nonminimal linear functional. The argument checks genuine vertex assignments
and their edge differences, with no global feasibility assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricVertexCone

/-- Vanishing of all but one genuine basis coordinate characterizes the
corresponding real edge direction. -/
theorem eq_basis_smul_of_offdiagonal_zero {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (x : Ambient n) (i : Fin n)
    (h : ∀ j, j ≠ i → b.repr x j = 0) :
    x = b.repr x i • b i := by
  apply b.ext_elem
  intro j
  by_cases hji : j = i
  · subst j
    simp [LinearEquiv.map_smul]
  · simp [LinearEquiv.map_smul, h j hji, Module.Basis.repr_self,
      Finsupp.single_apply, hji, Ne.symm hji]

/-- Agreement on the active hyperplanes containing a reference edge forces
Cartier point differences to be parallel to that actual edge. -/
theorem cartier_difference_parallel {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v w c d : Ambient n)
    (i : Fin n) (l : ℝ) (hl : l ≠ 0) (hedge : w - v = l • b i)
    (hactive : ∀ j, b.repr w j = b.repr v j → b.repr d j = b.repr c j) :
    d - c = (b.repr (d - c) i / l) • (w - v) := by
  have hoff (j : Fin n) (hji : j ≠ i) : b.repr (d - c) j = 0 := by
    have hcoord := congrArg (fun x => b.repr x j) hedge
    simp only [map_sub, Finsupp.sub_apply, LinearEquiv.map_smul,
      Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hji), mul_zero] at hcoord
    have hdc := hactive j (sub_eq_zero.mp hcoord)
    simp only [map_sub, Finsupp.sub_apply, hdc, sub_self]
  rw [hedge, smul_smul, div_mul_cancel₀ _ hl]
  exact eq_basis_smul_of_offdiagonal_zero b (d - c) i hoff

/-- Nonnegative coordinate edge degree gives a nonnegative parallel factor
for Cartier point differences. -/
theorem cartier_difference_nonnegative_multiple {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v w c d : Ambient n)
    (i : Fin n) (l : ℝ) (hl : 0 < l) (hedge : w - v = l • b i)
    (hactive : ∀ j, b.repr w j = b.repr v j → b.repr d j = b.repr c j)
    (hdegree : 0 ≤ b.repr (d - c) i) :
    ∃ t : ℝ, 0 ≤ t ∧ d - c = t • (w - v) :=
  ⟨b.repr (d - c) i / l, div_nonneg hdegree hl.le,
    cartier_difference_parallel b v w c d i l hl.ne' hedge hactive⟩

namespace LatticePolytope

/-- At any vertex that does not minimize a linear functional, an actual
incident edge decreases that functional. This follows from the proved tangent
cone theorem for finite convex hulls. -/
theorem exists_descending_edge {n : ℕ} (P : LatticePolytope n)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (f : Ambient n →ₗ[ℝ] ℝ) (hnotmin : ∃ x ∈ P.carrier, f x < f v) :
    ∃ w : Ambient n, P.IsEdge v w ∧ f w < f v := by
  classical
  by_contra h
  have hnonneg : ∀ w, P.IsEdge v w → 0 ≤ f (w - v) := by
    intro w hw
    have hle : f v ≤ f w := le_of_not_gt (fun hlt => h ⟨w, hw, hlt⟩)
    simpa only [map_sub, sub_nonneg] using hle
  let s := P.generators.image (embed n)
  have hcarrier : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hcarrier] using hv
  have hglobal := linear_nonneg_of_incident_edges s v hv' f
    (fun w hvw hface => hnonneg w ⟨hvw, by simpa only [hcarrier] using hface⟩)
  obtain ⟨x, hx, hlt⟩ := hnotmin
  have hx' : x ∈ convexHull ℝ (s : Set (Ambient n)) := by
    simpa only [hcarrier] using hx
  have hle := hglobal x hx'
  simp only [map_sub, sub_nonneg] at hle
  exact (not_lt_of_ge hle) hlt

/-- Assign a Cartier point to each actual reference vertex. If every
oriented edge difference is a nonnegative multiple of its original direction,
then all assigned points satisfy every target supporting halfspace.
The proof is finite descent in the original support height. -/
theorem cartier_feasible_of_nonnegative_edges {n : ℕ} (P : LatticePolytope n)
    {I : Type*} (u : I → Ambient n →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (c : P.carrier.extremePoints ℝ → Ambient n)
    (hsupport : ∀ i x, x ∈ P.carrier → a i ≤ u i x)
    (hattain : ∀ i, ∃ x ∈ P.carrier, u i x = a i)
    (hactive : ∀ (j : P.carrier.extremePoints ℝ) i,
      u i (j : Ambient n) = a i → u i (c j) = d i)
    (hedge : ∀ v w : P.carrier.extremePoints ℝ, P.IsEdge v w →
      ∃ t : ℝ, 0 ≤ t ∧ c w - c v = t • ((w : Ambient n) - v)) :
    ∀ j, c j ∈ normalHalfspaces u d := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  intro j0 i
  by_contra hbad
  have hj0 : u i (c j0) < d i := lt_of_not_ge hbad
  let B : Set J := {j | u i (c j) < d i}
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image B (fun j : J => u i (j : Ambient n))
    B.toFinite ⟨j0, hj0⟩
  have hnotactive : u i (j : Ambient n) ≠ a i := by
    intro he
    have h := hactive j i he
    exact (ne_of_lt hj) h
  have hheight : a i < u i (j : Ambient n) :=
    lt_of_le_of_ne (hsupport i j j.property.1) hnotactive.symm
  obtain ⟨x, hx, hxi⟩ := hattain i
  obtain ⟨w, hjw, hdec⟩ := P.exists_descending_edge j j.property (u i)
    ⟨x, hx, by simpa only [hxi] using hheight⟩
  let wJ : J := ⟨w, (P.edge_endpoints_extreme hjw).2⟩
  obtain ⟨t, ht, he⟩ := hedge j wJ hjw
  have he' := congrArg (u i) he
  simp only [map_sub, map_smul, smul_eq_mul] at he'
  have hdecle : u i (wJ : Ambient n) - u i (j : Ambient n) ≤ 0 := by
    exact sub_nonpos.mpr hdec.le
  have htargetle : u i (c wJ) ≤ u i (c j) := by
    have h := mul_nonpos_of_nonneg_of_nonpos ht hdecle
    rw [← he'] at h
    exact sub_nonpos.mp h
  have hwbad : wJ ∈ B := htargetle.trans_lt hj
  exact (not_lt_of_ge (hmin wJ hwbad)) hdec

/-- The complete convex-hull form of the nef Cartier criterion, using actual
reference-vertex basis cones and the proven global feasibility above. -/
theorem cartier_halfspaces_eq_hull_of_nonnegative_edges {n : ℕ} (P : LatticePolytope n)
    {I : Type*} (u : I → Ambient n →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℝ (Ambient n))
    (active : P.carrier.extremePoints ℝ → Fin n → I)
    (c : P.carrier.extremePoints ℝ → Ambient n)
    (hsupport : ∀ i x, x ∈ P.carrier → a i ≤ u i x)
    (hattain : ∀ i, ∃ x ∈ P.carrier, u i x = a i)
    (hactive_original : ∀ j k, u (active j k) (j : Ambient n) = a (active j k))
    (hactive : ∀ (j : P.carrier.extremePoints ℝ) i,
      u i (j : Ambient n) = a i → u i (c j) = d i)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : Ambient n →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hedge : ∀ v w : P.carrier.extremePoints ℝ, P.IsEdge v w →
      ∃ t : ℝ, 0 ≤ t ∧ c w - c v = t • ((w : Ambient n) - v)) :
    normalHalfspaces u d = convexHull ℝ (Set.range c) := by
  classical
  letI : Fintype (P.carrier.extremePoints ℝ) := P.finite_vertices.fintype
  apply shifted_halfspaces_eq_convexHull u d b active c hdual hcomplete
  · intro j k
    exact hactive j (active j k) (hactive_original j k)
  · exact P.cartier_feasible_of_nonnegative_edges u a d c hsupport hattain hactive hedge

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricCartierDeformations
-- END ORIGINAL PaperVerification.ToricCartierDeformations


-- BEGIN ORIGINAL PaperVerification.ToricLatticeCoordinates
section Source_ToricLatticeCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: public import PaperVerification.ToricIdeal
-- original header: public import Mathlib.Algebra.MvPolynomial.Rename
-- original header: public import Mathlib.Algebra.Polynomial.Eval.Degree
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Basis

-- original header: @[expose] public section

/-!
# The lattice-basis representation bridge

An abstract rank-`n` lattice and its realification are identified with
`Fin n → ℤ` and `Fin n → ℝ` by an actual integral basis and its base change.
The proofs below preserve every degree of integer decomposition and identify
the actual polynomial kernels and quadratic ideals by variable renaming.
Thus choosing coordinates does not change either conclusion of Theorem 1.1.
-/

noncomputable section

namespace PaperVerification.ToricCoordinateTransport

open PaperVerification.ToricExchange
open PaperVerification.ToricGeometry
open scoped TensorProduct

section Configuration

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable (e : M ≃+ N) {A : Set M} {B : Set N}
variable (hAB : ∀ m, m ∈ A ↔ e m ∈ B)

/-- The actual bijection between lattice-point variables. -/
def configurationEquiv : A ≃ B where
  toFun a := ⟨e a, (hAB a).mp a.property⟩
  invFun b := ⟨e.symm b, (hAB (e.symm b)).mpr (by simpa using b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)

@[simp] theorem configurationEquiv_coe (a : A) :
    (configurationEquiv e hAB a : N) = e a := rfl

@[simp] theorem configurationEquiv_symm_coe (b : B) :
    ((configurationEquiv e hAB).symm b : M) = e.symm b := rfl

/-- Both the lattice sum and the degree are retained by the variable bijection. -/
theorem total_map_configurationEquiv (s : Multiset A) :
    total B (s.map (configurationEquiv e hAB)) = e (total A s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, total_cons, configurationEquiv_coe, ih, map_add]

variable (R : Type*) [CommRing R]

/-- Literal renaming of the polynomial variables indexed by lattice points. -/
def configurationPolynomialEquiv : MvPolynomial A R ≃ₐ[R] MvPolynomial B R :=
  MvPolynomial.renameEquiv R (configurationEquiv e hAB)

@[simp] theorem configurationPolynomialEquiv_X (a : A) :
    configurationPolynomialEquiv e hAB R (MvPolynomial.X a) =
      MvPolynomial.X (configurationEquiv e hAB a) := by
  simp [configurationPolynomialEquiv]

@[simp] theorem configurationPolynomialEquiv_C (r : R) :
    configurationPolynomialEquiv e hAB R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [configurationPolynomialEquiv, MvPolynomial.rename_C]

/-- The target isomorphism changes character exponents and fixes the
homogenizing variable. Its source and target are exactly the paper's rings. -/
def characterTargetEquiv :
    Polynomial (AddMonoidAlgebra R M) ≃+* Polynomial (AddMonoidAlgebra R N) :=
  Polynomial.mapEquiv (AddMonoidAlgebra.mapDomainRingEquiv R e)

@[simp] theorem characterTargetEquiv_C_single (m : M) (r : R) :
    characterTargetEquiv e R (Polynomial.C (AddMonoidAlgebra.single m r)) =
      Polynomial.C (AddMonoidAlgebra.single (e m) r) := by
  simp [characterTargetEquiv, Polynomial.mapEquiv]

@[simp] theorem characterTargetEquiv_X :
    characterTargetEquiv e R Polynomial.X = Polynomial.X := by
  simp [characterTargetEquiv, Polynomial.mapEquiv]

/-- The square of the actual toric homomorphisms commutes, on every polynomial. -/
theorem paperToricMap_naturality :
    (paperToricMap B R).comp (configurationPolynomialEquiv e hAB R).toRingHom =
      (characterTargetEquiv e R).toRingHom.comp (paperToricMap A R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change paperToricMap B R (configurationPolynomialEquiv e hAB R (MvPolynomial.C r)) =
      characterTargetEquiv e R (paperToricMap A R (MvPolynomial.C r))
    simp only [configurationPolynomialEquiv_C, paperToricMap_C,
      characterTargetEquiv_C_single, map_zero]
  · intro a
    change paperToricMap B R (configurationPolynomialEquiv e hAB R (MvPolynomial.X a)) =
      characterTargetEquiv e R (paperToricMap A R (MvPolynomial.X a))
    simp only [configurationPolynomialEquiv_X, paperToricMap_X,
      map_mul, characterTargetEquiv_C_single, characterTargetEquiv_X,
      configurationEquiv_coe]

theorem paperToricMap_naturality_apply (p : MvPolynomial A R) :
    paperToricMap B R (configurationPolynomialEquiv e hAB R p) =
      characterTargetEquiv e R (paperToricMap A R p) :=
  RingHom.congr_fun (paperToricMap_naturality e hAB R) p

/-- Kernel membership is exactly preserved, not merely implied. -/
theorem mem_paper_kernel_iff (p : MvPolynomial A R) :
    configurationPolynomialEquiv e hAB R p ∈ RingHom.ker (paperToricMap B R) ↔
      p ∈ RingHom.ker (paperToricMap A R) := by
  change paperToricMap B R (configurationPolynomialEquiv e hAB R p) = 0 ↔
    paperToricMap A R p = 0
  rw [paperToricMap_naturality_apply]
  exact (characterTargetEquiv e R).map_eq_zero_iff

/-- The kernel is transported by the literal variable-renaming ring isomorphism. -/
theorem paper_kernel_map :
    (RingHom.ker (paperToricMap A R)).map
        (configurationPolynomialEquiv e hAB R).toRingHom =
      RingHom.ker (paperToricMap B R) := by
  ext p
  rw [Ideal.mem_map_iff_of_surjective (configurationPolynomialEquiv e hAB R).toRingHom
    (configurationPolynomialEquiv e hAB R).surjective]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_paper_kernel_iff e hAB R q).mpr hq
  · intro hp
    obtain ⟨q, rfl⟩ := (configurationPolynomialEquiv e hAB R).surjective p
    exact ⟨q, (mem_paper_kernel_iff e hAB R q).mp hp, rfl⟩

/-- The full ideal of equal-sum quadratic binomials is transported exactly. -/
theorem polynomialQuadraticIdeal_map :
    (polynomialQuadraticIdeal A R).map
        (configurationPolynomialEquiv e hAB R).toRingHom =
      polynomialQuadraticIdeal B R := by
  rw [polynomialQuadraticIdeal, Ideal.map_span, polynomialQuadraticIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨a, b, c, d, he, rfl⟩, rfl⟩
    refine ⟨configurationEquiv e hAB a, configurationEquiv e hAB b,
      configurationEquiv e hAB c, configurationEquiv e hAB d, ?_, ?_⟩
    · simpa only [configurationEquiv_coe, map_add] using congrArg e he
    · simp only [map_sub, map_mul, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv, configurationPolynomialEquiv_X]
  · rintro ⟨a, b, c, d, he, rfl⟩
    let a' := (configurationEquiv e hAB).symm a
    let b' := (configurationEquiv e hAB).symm b
    let c' := (configurationEquiv e hAB).symm c
    let d' := (configurationEquiv e hAB).symm d
    have he' : (a' : M) + b' = (c' : M) + d' := by
      simpa only [a', b', c', d', configurationEquiv_symm_coe, map_add] using
        congrArg e.symm he
    refine ⟨MvPolynomial.X a' * MvPolynomial.X b' -
      MvPolynomial.X c' * MvPolynomial.X d', ⟨a', b', c', d', he', rfl⟩, ?_⟩
    simp [a', b', c', d', map_sub, map_mul]

include e hAB in
/-- Equality of the actual toric kernel and quadratic ideal is independent
of a choice of lattice coordinates, over any commutative coefficient ring. -/
theorem quadratic_generation_iff :
    RingHom.ker (paperToricMap A R) = polynomialQuadraticIdeal A R ↔
      RingHom.ker (paperToricMap B R) = polynomialQuadraticIdeal B R := by
  constructor
  · intro h
    rw [← paper_kernel_map e hAB R, h, polynomialQuadraticIdeal_map]
  · intro h
    ext p
    have hq : configurationPolynomialEquiv e hAB R p ∈ polynomialQuadraticIdeal B R ↔
        p ∈ polynomialQuadraticIdeal A R := by
      rw [← polynomialQuadraticIdeal_map e hAB R,
        Ideal.mem_map_iff_of_surjective (configurationPolynomialEquiv e hAB R).toRingHom
          (configurationPolynomialEquiv e hAB R).surjective]
      constructor
      · rintro ⟨q, hq, hqp⟩
        exact (configurationPolynomialEquiv e hAB R).injective hqp ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    rw [← mem_paper_kernel_iff e hAB R p, h, hq]

end Configuration

section RealCoordinateTransport

variable {M N V W : Type*} [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable (ι : M →+ V) (κ : N →+ W) (e : M ≃+ N) (f : V ≃ₗ[ℝ] W)
variable (hcompat : ∀ m, κ (e m) = f (ι m))

/-- An integral basis of precisely the incident primitive edge directions,
written before choosing coordinates. This is the literal geometric
smoothness condition used in `LatticePolytope.Smooth`. -/
def SmoothEdgeBasis (n : ℕ) (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ v ∈ P.extremePoints ℝ,
    ∃ (vZ : M) (b : Module.Basis (Fin n) ℤ M) (lengths : Fin n → ℕ),
      embedding vZ = v ∧
      (∀ i, 0 < lengths i ∧
        v ≠ embedding (vZ + (lengths i : ℤ) • b i) ∧
        IsExtreme ℝ P (segment ℝ v (embedding (vZ + (lengths i : ℤ) • b i)))) ∧
      (∀ w : V, v ≠ w → IsExtreme ℝ P (segment ℝ v w) →
        ∃ i, w = embedding (vZ + (lengths i : ℤ) • b i))

/-- Actual vertices are preserved by the real coordinate isomorphism. -/
theorem extremePoints_image_iff (P : Set V) (v : V) :
    f v ∈ (f '' P).extremePoints ℝ ↔ v ∈ P.extremePoints ℝ := by
  rw [← isExtreme_singleton, ← isExtreme_singleton]
  simpa only [Set.image_singleton, LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] using
    affine_isExtreme_image_iff f.toLinearMap.toAffineMap f.injective P {v}

/-- Actual nondegenerate segment faces, hence edges, are preserved exactly. -/
theorem edge_image_iff (P : Set V) (v w : V) :
    (f v ≠ f w ∧ IsExtreme ℝ (f '' P) (segment ℝ (f v) (f w))) ↔
      (v ≠ w ∧ IsExtreme ℝ P (segment ℝ v w)) := by
  have hface : IsExtreme ℝ (f '' P) (segment ℝ (f v) (f w)) ↔
      IsExtreme ℝ P (segment ℝ v w) := by
    have h := affine_isExtreme_image_iff f.toLinearMap.toAffineMap
      f.injective P (segment ℝ v w)
    rw [image_segment] at h
    simpa only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] using h
  constructor
  · rintro ⟨hne, hF⟩
    exact ⟨fun h => hne (congrArg f h), hface.mp hF⟩
  · rintro ⟨hne, hF⟩
    exact ⟨fun h => hne (f.injective h), hface.mpr hF⟩

include hcompat in
/-- The full primitive edge-basis condition transfers, including the clause
that every incident edge is one of the displayed basis directions. -/
theorem smoothEdgeBasis_image (n : ℕ) (P : Set V)
    (hP : SmoothEdgeBasis n ι P) : SmoothEdgeBasis n κ (f '' P) := by
  intro v' hv'
  obtain ⟨v, hv, rfl⟩ := hv'.1
  have hvext := (extremePoints_image_iff f P v).mp hv'
  obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := hP v hvext
  let b' := b.map e.toIntLinearEquiv
  have hend (i : Fin n) :
      κ (e vZ + (lengths i : ℤ) • b' i) =
        f (ι (vZ + (lengths i : ℤ) • b i)) := by
    rw [← hcompat]
    congr 1
    simp [b', map_add, map_zsmul]
  refine ⟨e vZ, b', lengths, ?_, ?_, ?_⟩
  · rw [hcompat, hvZ]
  · intro i
    refine ⟨(hinc i).1, ?_⟩
    rw [hend]
    exact (edge_image_iff f P v _).mpr (hinc i).2
  · intro w' hne hF
    obtain ⟨w, rfl⟩ := f.surjective w'
    have hw := (edge_image_iff f P v w).mp ⟨hne, hF⟩
    obtain ⟨i, rfl⟩ := hall w hw.1 hw.2
    exact ⟨i, (hend i).symm⟩

include hcompat in
theorem smoothEdgeBasis_iff (n : ℕ) (P : Set V) :
    SmoothEdgeBasis n ι P ↔ SmoothEdgeBasis n κ (f '' P) := by
  constructor
  · exact smoothEdgeBasis_image ι κ e f hcompat n P
  · intro hP
    have hsymm : ∀ z, ι (e.symm z) = f.symm (κ z) := by
      intro z
      apply f.injective
      rw [← hcompat, e.apply_symm_apply, f.apply_symm_apply]
    have h := smoothEdgeBasis_image κ ι e.symm f.symm hsymm n (f '' P) hP
    simpa only [Set.image_image, Function.comp_def, f.symm_apply_apply, Set.image_id'] using h

include hcompat in
/-- Actual lattice points correspond to actual lattice points in the image. -/
theorem latticePoints_compatible_image (P : Set V) (m : M) :
    m ∈ latticePoints ι P ↔ e m ∈ latticePoints κ (f '' P) := by
  change ι m ∈ P ↔ κ (e m) ∈ f '' P
  rw [hcompat]
  constructor
  · intro hm
    exact ⟨ι m, hm, rfl⟩
  · rintro ⟨x, hx, hxm⟩
    exact f.injective hxm ▸ hx

include hcompat in
/-- Every positive-degree integral decomposition is carried to the image. -/
theorem integerDecompositionProperty_image (P : Set V)
    (hP : IntegerDecompositionProperty ι P) :
    IntegerDecompositionProperty κ (f '' P) := by
  intro k hk z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hz
  have hu : ι (e.symm z) = (k : ℝ) • x := by
    apply f.injective
    rw [← hcompat, e.apply_symm_apply, map_smul]
    exact hz
  obtain ⟨s, hs, hsum⟩ := hP k hk (e.symm z) ⟨x, hx, hu⟩
  let g := configurationEquiv e (latticePoints_compatible_image ι κ e f hcompat P)
  refine ⟨s.map g, ?_, ?_⟩
  · simpa only [Multiset.card_map] using hs
  · rw [total_map_configurationEquiv, hsum, e.apply_symm_apply]

include hcompat in
/-- IDP is invariant under a compatible lattice and real linear equivalence. -/
theorem integerDecompositionProperty_iff (P : Set V) :
    IntegerDecompositionProperty ι P ↔ IntegerDecompositionProperty κ (f '' P) := by
  constructor
  · exact integerDecompositionProperty_image ι κ e f hcompat P
  · intro hP
    have hsymm : ∀ z, ι (e.symm z) = f.symm (κ z) := by
      intro z
      apply f.injective
      rw [← hcompat, e.apply_symm_apply, f.apply_symm_apply]
    have h := integerDecompositionProperty_image κ ι e.symm f.symm hsymm (f '' P) hP
    simpa only [Set.image_image, Function.comp_def, f.symm_apply_apply, Set.image_id'] using h

/-- The same lattice basis change preserves every prescribed parity class. -/
theorem sameParity_iff (a b : M) : SameParity (e a) (e b) ↔ SameParity a b := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.symm w, ?_⟩
    simpa only [map_sub, map_add, e.symm_apply_apply] using congrArg e.symm hw
  · rintro ⟨w, hw⟩
    refine ⟨e w, ?_⟩
    simpa only [map_sub, map_add] using congrArg e hw

end RealCoordinateTransport

section Realification

variable {M : Type*} [AddCommGroup M] {n : ℕ}

/-- The ordinary lattice inclusion in `M_ℝ = ℝ ⊗[ℤ] M`. -/
def realificationEmbedding : M →+ ℝ ⊗[ℤ] M where
  toFun m := (1 : ℝ) ⊗ₜ[ℤ] m
  map_zero' := TensorProduct.tmul_zero M (1 : ℝ)
  map_add' m₁ m₂ := TensorProduct.tmul_add (1 : ℝ) m₁ m₂

/-- The real coordinates are obtained by genuine scalar extension of an
integral basis; no compatible real isomorphism is an additional premise. -/
def basisRealCoordinates (b : Module.Basis (Fin n) ℤ M) :
    (ℝ ⊗[ℤ] M) ≃ₗ[ℝ] Ambient n :=
  (b.baseChange ℝ).equivFun

theorem basisRealCoordinates_compatible (b : Module.Basis (Fin n) ℤ M) (m : M) :
    embed n (b.equivFun m) = basisRealCoordinates b (realificationEmbedding m) := by
  ext i
  change ((b.repr m i : ℤ) : ℝ) = (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℤ] m) i
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [zsmul_eq_mul, mul_one]

/-- A specified isomorphism `M ≃ ℤⁿ` alone supplies the compatible real
coordinate equivalence. -/
def realCoordinatesOfEquiv (e : M ≃+ Lattice n) :
    (ℝ ⊗[ℤ] M) ≃ₗ[ℝ] Ambient n :=
  basisRealCoordinates (Module.Basis.ofEquivFun e.toIntLinearEquiv)

theorem realCoordinatesOfEquiv_compatible (e : M ≃+ Lattice n) (m : M) :
    embed n (e m) = realCoordinatesOfEquiv e (realificationEmbedding m) := by
  simpa only [realCoordinatesOfEquiv, Module.Basis.equivFun_ofEquivFun,
    AddEquiv.coe_toIntLinearEquiv] using
    basisRealCoordinates_compatible (Module.Basis.ofEquivFun e.toIntLinearEquiv) m

theorem realificationEmbedding_injective (e : M ≃+ Lattice n) :
    Function.Injective (realificationEmbedding (M := M)) := by
  intro x y h
  apply e.injective
  apply embed_injective n
  simpa only [← realCoordinatesOfEquiv_compatible] using
    congrArg (realCoordinatesOfEquiv e) h

/-- Finite lattice convex hulls become precisely their coordinate convex
hulls under this isomorphism. -/
theorem realCoordinatesOfEquiv_convexHull (e : M ≃+ Lattice n) (s : Set M) :
    realCoordinatesOfEquiv e '' convexHull ℝ (realificationEmbedding '' s) =
      convexHull ℝ (embed n '' (e '' s)) := by
  change (realCoordinatesOfEquiv e).toLinearMap ''
      convexHull ℝ (realificationEmbedding '' s) = _
  rw [(realCoordinatesOfEquiv e).toLinearMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨e m, ⟨m, hm, rfl⟩, realCoordinatesOfEquiv_compatible e m⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨realificationEmbedding m, ⟨m, hm, rfl⟩,
      (realCoordinatesOfEquiv_compatible e m).symm⟩

/-- A finite full-dimensional abstract lattice polytope gives an actual
coordinate `LatticePolytope`, with no extra geometric hypothesis. -/
def coordinatePolytope (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    LatticePolytope n where
  generators := s.image e
  nonempty := hs.image e
  fullDimensional := by
    rw [Finset.coe_image, ← realCoordinatesOfEquiv_convexHull]
    exact (realCoordinatesOfEquiv e).toLinearMap.toAffineMap.span_eq_top_of_surjective
      (realCoordinatesOfEquiv e).surjective hfull

theorem coordinatePolytope_carrier (e : M ≃+ Lattice n) (s : Finset M)
    (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    (coordinatePolytope e s hs hfull).carrier =
      realCoordinatesOfEquiv e '' convexHull ℝ (realificationEmbedding '' (s : Set M)) := by
  simp only [LatticePolytope.carrier, coordinatePolytope, Finset.coe_image,
    realCoordinatesOfEquiv_convexHull]

/-- Coordinate smoothness is exactly the abstract primitive edge-basis
condition; in particular no incident edges disappear under coordinate choice. -/
theorem coordinatePolytope_smooth_iff (e : M ≃+ Lattice n) (s : Finset M)
    (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    (coordinatePolytope e s hs hfull).Smooth ↔
      SmoothEdgeBasis n realificationEmbedding
        (convexHull ℝ (realificationEmbedding '' (s : Set M))) := by
  have hsmooth (Q : LatticePolytope n) :
      Q.Smooth ↔ SmoothEdgeBasis n (embed n) Q.carrier := by
    unfold LatticePolytope.Smooth SmoothEdgeBasis LatticePolytope.IsEdge
    constructor
    · intro h v hv
      obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := h v hv
      exact ⟨vZ, b, lengths, hvZ, hinc, fun w hne hF => hall w ⟨hne, hF⟩⟩
    · intro h v hv
      obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := h v hv
      exact ⟨vZ, b, lengths, hvZ, hinc, fun w hw => hall w hw.1 hw.2⟩
  rw [hsmooth, coordinatePolytope_carrier]
  exact (smoothEdgeBasis_iff realificationEmbedding (embed n) e
    (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) n _).symm

/-- The coordinate gcd is exactly intrinsic divisibility of the original
lattice vector, so its segment-length meaning is independent of the basis. -/
theorem dvd_coordinateContent_iff (e : M ≃+ Lattice n) (k : ℕ) (m : M) :
    k ∣ latticeContent (e m) ↔ ∃ w : M, m = (k : ℤ) • w := by
  rw [dvd_latticeContent_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.symm w, ?_⟩
    apply e.injective
    simpa only [map_zsmul, e.apply_symm_apply] using hw
  · rintro ⟨w, rfl⟩
    exact ⟨e w, map_zsmul e _ _⟩

/-- The usual gcd length of a lattice segment does not depend on which
integral basis supplies its coordinates. -/
theorem latticeLength_independent_of_basis (e e' : M ≃+ Lattice n) (v w : M) :
    LatticePolytope.latticeLength (e v) (e w) =
      LatticePolytope.latticeLength (e' v) (e' w) := by
  have hlen (g : M ≃+ Lattice n) :
      LatticePolytope.latticeLength (g v) (g w) = latticeContent (g (w - v)) := by
    simp only [LatticePolytope.latticeLength, latticeContent, map_sub, Pi.sub_apply]
  rw [hlen, hlen]
  apply Nat.dvd_antisymm
  · exact (dvd_coordinateContent_iff e' _ (w - v)).mpr
      ((dvd_coordinateContent_iff e _ (w - v)).mp dvd_rfl)
  · exact (dvd_coordinateContent_iff e _ (w - v)).mpr
      ((dvd_coordinateContent_iff e' _ (w - v)).mp dvd_rfl)

/-- Every actual abstract lattice edge corresponds to exactly one actual
coordinate edge, with the same intrinsic lattice length. -/
theorem coordinatePolytope_edgesAtLeast_iff
    (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤)
    (bound : ℕ) :
    (coordinatePolytope e s hs hfull).EdgesAtLeast bound ↔
      ∀ v w : M, realificationEmbedding v ≠ realificationEmbedding w →
        IsExtreme ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M)))
          (segment ℝ (realificationEmbedding v) (realificationEmbedding w)) →
        bound ≤ latticeContent (e (w - v)) := by
  let P := convexHull ℝ (realificationEmbedding '' (s : Set M))
  have hedge (v w : M) :
      (coordinatePolytope e s hs hfull).IsEdge (embed n (e v)) (embed n (e w)) ↔
        realificationEmbedding v ≠ realificationEmbedding w ∧
          IsExtreme ℝ P (segment ℝ (realificationEmbedding v) (realificationEmbedding w)) := by
    unfold LatticePolytope.IsEdge
    rw [coordinatePolytope_carrier, realCoordinatesOfEquiv_compatible,
      realCoordinatesOfEquiv_compatible]
    exact edge_image_iff (realCoordinatesOfEquiv e) P _ _
  have hlen (v w : M) :
      LatticePolytope.latticeLength (e v) (e w) = latticeContent (e (w - v)) := by
    simp only [LatticePolytope.latticeLength, latticeContent, map_sub, Pi.sub_apply]
  rw [LatticePolytope.edgesAtLeast_iff]
  constructor
  · intro h v w hne hF
    exact hlen v w ▸ h (e v) (e w) ((hedge v w).mpr ⟨hne, hF⟩)
  · intro h v w hF
    obtain ⟨v', rfl⟩ := e.surjective v
    obtain ⟨w', rfl⟩ := e.surjective w
    obtain ⟨hne, hF⟩ := (hedge v' w').mp hF
    rw [hlen]
    exact h v' w' hne hF

/-- The exact unrestricted IDP statement on an abstract lattice is equivalent
to the coordinate statement used by the principal theorem. -/
theorem lattice_basis_idp_iff (e : M ≃+ Lattice n) (P : Set (ℝ ⊗[ℤ] M)) :
    IntegerDecompositionProperty realificationEmbedding P ↔
      IntegerDecompositionProperty (embed n) (realCoordinatesOfEquiv e '' P) :=
  integerDecompositionProperty_iff realificationEmbedding (embed n) e
    (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) P

/-- The exact paper-kernel quadratic-generation statement on an abstract
lattice is equivalent to the coordinate assertion, with all lattice points
and every polynomial degree retained. -/
theorem lattice_basis_quadratic_generation_iff
    (e : M ≃+ Lattice n) (P : Set (ℝ ⊗[ℤ] M))
    (R : Type*) [CommRing R] :
    RingHom.ker (paperToricMap (latticePoints realificationEmbedding P) R) =
        polynomialQuadraticIdeal (latticePoints realificationEmbedding P) R ↔
      RingHom.ker (paperToricMap
        (latticePoints (embed n) (realCoordinatesOfEquiv e '' P)) R) =
        polynomialQuadraticIdeal
          (latticePoints (embed n) (realCoordinatesOfEquiv e '' P)) R :=
  quadratic_generation_iff e
    (latticePoints_compatible_image realificationEmbedding (embed n) e
      (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) P) R

/-- Both principal conclusions for the coordinate polytope are exactly the
paper's conclusions for the original abstract lattice and its realification. -/
theorem coordinatePolytope_principal_conclusions_iff
    (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤)
    (R : Type*) [CommRing R] :
    ((coordinatePolytope e s hs hfull).HasIDP ∧
      (coordinatePolytope e s hs hfull).QuadraticallyGenerated R) ↔
      (IntegerDecompositionProperty realificationEmbedding
          (convexHull ℝ (realificationEmbedding '' (s : Set M))) ∧
        RingHom.ker (paperToricMap (latticePoints realificationEmbedding
          (convexHull ℝ (realificationEmbedding '' (s : Set M)))) R) =
          polynomialQuadraticIdeal (latticePoints realificationEmbedding
            (convexHull ℝ (realificationEmbedding '' (s : Set M)))) R) := by
  apply and_congr
  · change IntegerDecompositionProperty (embed n) (coordinatePolytope e s hs hfull).carrier ↔ _
    rw [coordinatePolytope_carrier]
    exact (lattice_basis_idp_iff e _).symm
  · let Q (A : Set (Ambient n)) : Prop :=
      RingHom.ker (paperToricMap (latticePoints (embed n) A) R) =
        polynomialQuadraticIdeal (latticePoints (embed n) A) R
    have hc : Q (coordinatePolytope e s hs hfull).carrier =
        Q (realCoordinatesOfEquiv e ''
          convexHull ℝ (realificationEmbedding '' (s : Set M))) :=
      congrArg Q (coordinatePolytope_carrier e s hs hfull)
    exact (iff_of_eq hc).trans (lattice_basis_quadratic_generation_iff e _ R).symm

end Realification

end PaperVerification.ToricCoordinateTransport
end
end Source_ToricLatticeCoordinates
-- END ORIGINAL PaperVerification.ToricLatticeCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricStarIntegralSupport
section Source_ToricStarIntegralSupport

-- original header: module

-- original header: public import PaperVerification.ToricStarStrictSupport
-- original header: public import Mathlib.Algebra.Order.Archimedean.Basic

-- original header: @[expose] public section

/-!
# Integral strict support survives smooth star subdivisions

The all-small perturbation theorem permits ε=1/N. Multiplication by N makes
all coefficients integral: the exceptional coefficient is N times the old
focus sum minus one, and every other coefficient is N times its old value.
This provides the integral descending cost required by primitive reductions,
without assuming the primitive nef criterion or a rational approximation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_integral_strictSupport_starSubdivision
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ K : Lattice n → ℤ,
      («Σ».starSubdivision t ht hne).IsStrictSupport (fun v => (K v : ℝ)) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    «Σ».strictSupport_starSubdivision_all_small (fun v => (H v : ℝ)) hH t ht hne hcard
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (max (1 : ℝ) δ⁻¹)
  have hNR : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hNlarge)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hε : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNR
  have hεle : (N : ℝ)⁻¹ ≤ δ := by
    have hlarge : δ⁻¹ < (N : ℝ) := (le_max_right _ _).trans_lt hNlarge
    have hmul := mul_lt_mul_of_pos_left hlarge hδ
    rw [mul_inv_cancel₀ (ne_of_gt hδ)] at hmul
    rw [← one_div]
    apply (div_le_iff₀ hNR).mpr
    nlinarith
  have hs := hsmall (N : ℝ)⁻¹ hε hεle
  have hscaled := IsStrictSupport.smul («Σ».starSubdivision t ht hne) hs hNR
  let K : Lattice n → ℤ := fun v =>
    if v = ∑ w ∈ t, w then (N : ℤ) * (∑ w ∈ t, H w) - 1 else (N : ℤ) * H v
  have hcoeff : (fun v => (K v : ℝ)) = (N : ℝ) •
      (fun v => starCoefficientBase (fun w => (H w : ℝ)) t v +
        (N : ℝ)⁻¹ * starCoefficientSlope t v) := by
    funext v
    by_cases hv : v = ∑ w ∈ t, w
    · simp only [K, starCoefficientBase, starCoefficientSlope, if_pos hv,
        Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_sum, Int.cast_one]
      field_simp
      ring
    · simp only [K, starCoefficientBase, starCoefficientSlope, if_neg hv,
        Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast]
  exact ⟨K, hcoeff.symm ▸ hscaled⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarIntegralSupport
-- END ORIGINAL PaperVerification.ToricStarIntegralSupport


