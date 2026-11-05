module

public import PaperVerification.ToricDegreePolytopeBridge
public import PaperVerification.ToricSectionTensorNaturality
public import PaperVerification.ToricCanonicalDifferentialGluing
public import PaperVerification.ToricFanSectionMultiplication
public import PaperVerification.ToricMainTheorems

@[expose] public section

/-!
# The mixed theorems for arbitrary Cartier divisors on the actual fan scheme

The inputs here are actual invertible fractional sheaves. The lower
bounds refer to the degrees of their actual restrictions to the invariant
wall curves. The recovered polytopes and their edge bounds are consequences
of those inputs. The adjoint section map is the actual base-field tensor
multiplication; its canonical factor comes from the local top differential
modules and their proved gluing.

The separate reconstruction of an intrinsic toric variety as a fan scheme
is needed to apply these statements to the manuscript's intrinsic inputs.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical Pointwise BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
    (hpure : «Σ».IsPure)

def divisorPolytope (D : CartierData («Σ».fanScheme k)) : Set (Ambient n) :=
  «Σ».fanPolytope (fun v => («Σ».cartierCoefficients k hpure D v : ℝ))

theorem cartierCoefficients_strictSupport_of_curveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ) (hbound : 0 < bound)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    «Σ».IsStrictSupport (fun v => («Σ».cartierCoefficients k hpure D v : ℝ)) :=
  «Σ».strictSupport_of_positive_wallSlacks hpure _
    («Σ».positiveWallSlacks_of_bound _ bound hbound
      («Σ».cartierCoefficients_hasWallSlacksAtLeast k hpure D bound hD))

/-- Dimension zero has no rays, so every support polytope is the actual
one-point ambient space. No positive lower bound is inserted in that case. -/
theorem divisorPolytope_dimension_zero (hn : n = 0)
    (D : CartierData («Σ».fanScheme k)) : «Σ».divisorPolytope k hpure D = Set.univ := by
  subst n
  ext x
  simp only [Set.mem_univ,iff_true]
  intro v hv
  exact («Σ».ray_ne_zero hv (Subsingleton.elim v 0)).elim

/-- The manuscript's prescribed quotient class, for arbitrary actual
Cartier divisors on the constructed smooth complete fan scheme. -/
theorem fanDivisor_prescribedParity
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D n)
    (hE : «Σ».CartierWallDegreesAtLeast k E n)
    (m : Lattice n)
    (hm : embed n m ∈ interior
      («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ «Σ».divisorPolytope k hpure D ∧
      embed n b ∈ «Σ».divisorPolytope k hpure E ∧
      a + b = m ∧ parityClass n a = α := by
  by_cases hn : n = 0
  · subst n
    refine ⟨m,0,?_,?_,add_zero m,?_⟩
    · rw [«Σ».divisorPolytope_dimension_zero k hpure rfl D]
      exact Set.mem_univ _
    · rw [«Σ».divisorPolytope_dimension_zero k hpure rfl E]
      exact Set.mem_univ _
    · obtain ⟨r,hr⟩ := parityClass_surjective 0 α
      exact (congrArg (parityClass 0) (Subsingleton.elim m r)).trans hr
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨P,hP,hPs,hPf,hPb⟩ :=
      «Σ».exists_polytope_of_cartierCurveDegrees k hpure D n hnpos hD
    obtain ⟨Q,hQ,hQs,hQf,hQb⟩ :=
      «Σ».exists_polytope_of_cartierCurveDegrees k hpure E n hnpos hE
    have hPQ : P.SameNormalFan Q := hPf.trans hQf.symm
    have hm' : embed n m ∈ interior (P.minkowskiSum Q) := by
      simpa only [LatticePolytope.minkowskiSum,hP,hQ,divisorPolytope] using hm
    obtain ⟨a,b,ha,hb,hab,hα⟩ := toric_theorem_1_2_quotient_classes
      n P Q hPs hQs hPQ hPb hQb m hm' α
    exact ⟨a,b,by simpa only [hP,divisorPolytope] using ha,
      by simpa only [hQ,divisorPolytope] using hb,hab,hα⟩

/-- The full literal equality of lattice-point sets, with the interior
on the second summand and on the whole Minkowski sum. -/
theorem fanDivisor_adjointLatticePoints
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1)) :
    {m : Lattice n | embed n m ∈ «Σ».divisorPolytope k hpure D} +
      {m : Lattice n | embed n m ∈ interior («Σ».divisorPolytope k hpure E)} =
    {m : Lattice n | embed n m ∈ interior
      («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E)} := by
  obtain ⟨P,hP,hPs,hPf,hPb⟩ :=
    «Σ».exists_polytope_of_cartierCurveDegrees k hpure D (n+1) (by omega) hD
  obtain ⟨Q,hQ,hQs,hQf,hQb⟩ :=
    «Σ».exists_polytope_of_cartierCurveDegrees k hpure E (n+1) (by omega) hE
  have hPQ : P.SameNormalFan Q := hPf.trans hQf.symm
  simpa only [LatticePolytope.minkowskiSum,hP,hQ,divisorPolytope] using
    toric_theorem_1_3_polytope_sets n P Q hPs hQs hPQ hPb hQb

theorem fanDivisor_adjointExponentSum
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1)) :
    «Σ».fanIntegralExponents
        («Σ».cartierCoefficients k hpure D +
          («Σ».cartierCoefficients k hpure E + fun _ => -1)) =
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) +
        «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure E + fun _ => -1) := by
  let a := «Σ».cartierCoefficients k hpure D
  let b := «Σ».cartierCoefficients k hpure E
  have ha := «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure D
    (n+1) (by omega) hD
  have hb := «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure E
    (n+1) (by omega) hE
  have hsum : «Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E =
      «Σ».fanPolytope (fun v => ((a v+b v : ℤ) : ℝ)) := by
    change «Σ».fanPolytope (fun v => (a v : ℝ)) +
      «Σ».fanPolytope (fun v => (b v : ℝ)) = _
    calc
      _ = «Σ».fanPolytope ((fun v => (a v : ℝ)) + (fun v => (b v : ℝ))) :=
        («Σ».fanPolytope_add hpure (fun v => (a v : ℝ)) (fun v => (b v : ℝ))
          (IsStrictSupport.isNef «Σ» ha) (IsStrictSupport.isNef «Σ» hb)).symm
      _ = _ := congrArg «Σ».fanPolytope (funext (fun v =>
        (Int.cast_add (a v) (b v)).symm))
  have he := («Σ».fanDivisor_adjointLatticePoints k hpure D E hD hE).symm
  have hleft : {m : Lattice n | embed n m ∈ interior
        («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E)} =
      «Σ».fanIntegralExponents (a+(b+fun _ => -1)) := by
    ext m
    rw [Set.mem_setOf_eq,hsum,«Σ».lattice_mem_interior_iff_adjointSupport]
    simp only [fanIntegralExponents,Set.mem_setOf_eq,Pi.add_apply,sub_eq_add_neg,add_assoc]
  have hright : {m : Lattice n | embed n m ∈ interior («Σ».divisorPolytope k hpure E)} =
      «Σ».fanIntegralExponents (b+fun _ => -1) := by
    ext m
    change (embed n m ∈ interior («Σ».fanPolytope (fun v => (b v : ℝ)))) ↔ _
    rw [«Σ».lattice_mem_interior_iff_adjointSupport]
    simp only [fanIntegralExponents,Set.mem_setOf_eq,Pi.add_apply,sub_eq_add_neg]
  rw [hleft,hright] at he
  exact he

/-- Surjectivity of multiplication of the actual global sections of
`D` and `E + K`, where the canonical presentation is obtained by gluing
the actual local top Kähler differential modules. -/
theorem fanDivisor_adjointSectionMultiplication
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1))
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    Function.Surjective (D.sectionMultiplicationOver k
      (E.add («Σ».differentialVolumeData k hpure b₀))) := by
  let a := «Σ».cartierCoefficients k hpure D
  let b := «Σ».cartierCoefficients k hpure E
  let A := «Σ».fanCartierData k hpure a
  let B := «Σ».fanCartierData k hpure b
  let K := «Σ».differentialVolumeData k hpure b₀
  let K' := «Σ».fanCartierData k hpure (fun _ => -1)
  let F : D.sheaf ≅ A.sheaf :=
    («Σ».cartierData_linearlyEquivalent_fanCartier k hpure D).some
  let G : E.sheaf ≅ B.sheaf :=
    («Σ».cartierData_linearlyEquivalent_fanCartier k hpure E).some
  let H : K.sheaf ≅ K'.sheaf :=
    («Σ».differentialVolumeData_equivalent_canonical k hpure b₀).choose
  let J : (E.add K).sheaf ≅ («Σ».fanCartierData k hpure (b+fun _ => -1)).sheaf :=
    E.addSheafIso B K K' G H ≪≫
      («Σ».fanCartierData_add_equivalent k hpure b (fun _ => -1)).choose
  apply (D.sectionMultiplicationOver_surjective_iff_sheafIso k A
    (E.add K) («Σ».fanCartierData k hpure (b+fun _ => -1)) F J).mpr
  apply («Σ».fanSectionMultiplication_surjective_iff k hpure a (b+fun _ => -1)).mpr
  exact «Σ».fanDivisor_adjointExponentSum k hpure D E hD hE

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_prescribedParity
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_adjointLatticePoints
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_adjointSectionMultiplication
