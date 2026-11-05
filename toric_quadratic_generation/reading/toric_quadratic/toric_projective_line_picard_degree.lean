module

public import PaperVerification.ToricProjectiveLineUnits
public import PaperVerification.ToricCartierFrameIsomorphisms
public import PaperVerification.ToricArbitraryCartierFan

@[expose] public section

/-!
# Degree of the actual line bundle on the rank-one fan

An arbitrary isomorphism of the two Cartier sheaves preserves the sum of
their ray coefficients. The proof compares their genuine local frames:
the changes on the two affine-line charts are polynomial units, and the
remaining transition ratio is measured by actual local order. Thus the
degree is a property of the actual line bundle, not of a chosen fractional
embedding. Every Cartier sheaf has such a fan presentation by the proved
arbitrary-Cartier classification.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLine_cartierPoint_coordinate (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) 0 =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  have h := projectiveLineFan.cartierLatticePoint_pairing a
    (projectiveLineFullCone negative) (projectiveLineRay negative)
      (Finset.mem_singleton_self _)
  cases negative <;> simp only [integerPairing,Fin.sum_univ_one,
    projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] at h ⊢ <;> omega

instance projectiveLine_fullChart_nonempty (negative : Bool) :
    Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) := by
  rw [← projectiveLinePolynomialChart_image k negative]
  exact openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤

def projectiveLineCartierFrame (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).Frame
      (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) :=
  (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_generator (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).frameRationalGenerator
      (projectiveLineCartierFrame k a negative) =
        (projectiveLineFan.rationalCharacter k
          (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) :
            (projectiveLineScheme k).functionField) := by
  letI : Nonempty ((projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).openSet
      ⟨projectiveLineFullCone negative⟩) := projectiveLine_fullChart_nonempty k negative
  exact (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame_rationalGenerator
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_order (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineScheme k).ord
      ((projectiveLineCartierData k a).frameRationalGenerator
        (projectiveLineCartierFrame k a negative)) (projectiveLineBoundaryPoint k false) =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  rw [projectiveLineCartierFrame_generator,projectiveLine_character_order_boundary]
  exact projectiveLine_cartierPoint_coordinate a negative

/-- Degree invariance is proved for every genuine sheaf isomorphism,
without requiring compatibility with the rational embeddings. -/
theorem projectiveLine_coefficientSum_eq_of_sheafIso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    a (projectiveLineRay false)+a (projectiveLineRay true) =
      b (projectiveLineRay false)+b (projectiveLineRay true) := by
  let X := projectiveLineScheme k
  let D := projectiveLineCartierData k a
  let E := projectiveLineCartierData k b
  let x := projectiveLineBoundaryPoint k false
  let e (negative : Bool) := projectiveLineCartierFrame k a negative
  let q (negative : Bool) := projectiveLineCartierFrame k b negative
  have hsame (negative : Bool) :
      X.ord (D.frameRationalGenerator (e negative)) x =
        X.ord (D.frameRationalGenerator (ModuleFrame.precompose F (q negative))) x := by
    obtain ⟨u,hu⟩ := D.exists_frameTransitionUnit
      (e negative) (ModuleFrame.precompose F (q negative)) le_rfl le_rfl
    have hzero := projectiveLine_fullChartUnit_order k negative u x
    rw [hu,rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _)] at hzero
    omega
  have hratio := D.precompose_frameRatio E F (q false) (q true)
  have hord := congrArg (fun r : X.functionField=>X.ord r x) hratio
  rw [rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _),
    rationalOrder_div (E.frameRationalGenerator_ne_zero _)
      (E.frameRationalGenerator_ne_zero _),← hsame false,← hsame true] at hord
  change X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a false)) x -
      X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a true)) x =
    X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b false)) x -
      X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b true)) x at hord
  rw [projectiveLineCartierFrame_order,projectiveLineCartierFrame_order,
    projectiveLineCartierFrame_order,projectiveLineCartierFrame_order] at hord
  simp only [Bool.false_eq_true,if_false,if_true] at hord
  omega

theorem projectiveLineCartier_degree_iso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    (projectiveLineCartierData k a).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
    (projectiveLineCartierData k b).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k b) := by
  rw [projectiveLineCartier_degree,projectiveLineCartier_degree]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b F

/-- Degree via the actual integral fan Cartier presentations. Existence
for arbitrary Cartier sheaves and uniqueness are proved below. Each such
presentation has exactly this Mathlib Weil-cycle degree. -/
def ProjectiveLineHasDegree (M : (projectiveLineScheme k).Modules) (d : ℤ) : Prop :=
  ∃ a : Lattice 1→ℤ, Nonempty (M ≅ (projectiveLineCartierData k a).sheaf) ∧
    a (projectiveLineRay false)+a (projectiveLineRay true)=d

theorem projectiveLineHasDegree_unique {M : (projectiveLineScheme k).Modules}
    {d e : ℤ} (hd : ProjectiveLineHasDegree k M d) (he : ProjectiveLineHasDegree k M e) : d=e := by
  obtain ⟨a,⟨Fa⟩,ha⟩ := hd
  obtain ⟨b,⟨Fb⟩,hb⟩ := he
  rw [← ha,← hb]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b (Fa.symm ≪≫ Fb)

theorem projectiveLineHasDegree_iso {M N : (projectiveLineScheme k).Modules}
    (F : M ≅ N) (d : ℤ) : ProjectiveLineHasDegree k M d ↔ ProjectiveLineHasDegree k N d := by
  constructor
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F.symm ≪≫ G⟩,ha⟩
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F ≪≫ G⟩,ha⟩

theorem projectiveLineCartier_hasDegree (a : Lattice 1→ℤ) :
    ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
      (a (projectiveLineRay false)+a (projectiveLineRay true)) :=
  ⟨a,⟨Iso.refl _⟩,rfl⟩

/-- Every arbitrary actual Cartier sheaf has a unique degree; no
character presentation or equivariance is assumed of the input. -/
theorem projectiveLineCartier_existsUnique_degree (D : CartierData (projectiveLineScheme k)) :
    ∃! d : ℤ,ProjectiveLineHasDegree k D.sheaf d := by
  let a := projectiveLineFan.cartierCoefficients k projectiveLineFan_isPure D
  let d := a (projectiveLineRay false)+a (projectiveLineRay true)
  have hd : ProjectiveLineHasDegree k D.sheaf d :=
    ⟨a,projectiveLineFan.cartierData_linearlyEquivalent_fanCartier k projectiveLineFan_isPure D,rfl⟩
  exact ⟨d,hd,fun e he=>projectiveLineHasDegree_unique k he hd⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_coefficientSum_eq_of_sheafIso
#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_existsUnique_degree
