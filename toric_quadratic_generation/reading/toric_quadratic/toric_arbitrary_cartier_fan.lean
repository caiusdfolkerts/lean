module

public import PaperVerification.ToricFanRegularCharacters
public import PaperVerification.ToricFanIntegralCoefficients
public import PaperVerification.ToricLaurentUnits
public import PaperVerification.ToricCartierRangeEquality

@[expose] public section

/-!
# Arbitrary Cartier data on a smooth fan scheme

Every actual invertible fractional sheaf on the actual glued fan scheme
has a linearly equivalent integral invariant presentation. The proof
normalizes on the dense torus, trivializes each actual affine chart by
its proved Picard vanishing, classifies the resulting Laurent units,
and reconstructs integral ray coefficients from the genuine overlaps.
The final equality preserves the actual rational embeddings after the
explicit principal translation used for torus normalization.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem exists_normalizedChartFactor (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    ∃ c : kˣ, ∃ m : Lattice n,
      «Σ».normalizedChartGenerator k D s =
        («Σ».rationalScalarUnit k c : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
  obtain ⟨v,hv⟩ := «Σ».exists_normalizedChartLaurentUnit k D s
  obtain ⟨c,m,hv'⟩ := laurent_unit_single k n v
  refine ⟨c,m,?_⟩
  rw [← hv,hv',«Σ».torusRationalMap_single]
  rfl

def normalizedChartScalar (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) : kˣ :=
  («Σ».exists_normalizedChartFactor k D s).choose

def normalizedChartExponent (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) : Lattice n :=
  («Σ».exists_normalizedChartFactor k D s).choose_spec.choose

theorem normalizedChartGenerator_factor (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    «Σ».normalizedChartGenerator k D s =
      («Σ».rationalScalarUnit k («Σ».normalizedChartScalar k D s) :
        («Σ».fanScheme k).functionField) *
      («Σ».rationalCharacter k («Σ».normalizedChartExponent k D s) :
        («Σ».fanScheme k).functionField) :=
  («Σ».exists_normalizedChartFactor k D s).choose_spec.choose_spec

theorem normalizedChartExponent_pairing (D : CartierData («Σ».fanScheme k))
    (s t : «Σ».ConeIndex) (v : Lattice n) (hvs : v∈s.val) (hvt : v∈t.val) :
    integerPairing v («Σ».normalizedChartExponent k D s) =
      integerPairing v («Σ».normalizedChartExponent k D t) := by
  exact «Σ».frameCharacter_pairing_eq k («Σ».normalizedCartier k D) s t
    («Σ».normalizedChartFrame k D s) («Σ».normalizedChartFrame k D t)
    («Σ».normalizedChartScalar k D s) («Σ».normalizedChartScalar k D t)
    («Σ».normalizedChartExponent k D s) («Σ».normalizedChartExponent k D t)
    («Σ».normalizedChartGenerator_factor k D s) («Σ».normalizedChartGenerator_factor k D t)
    v hvs hvt

/-- Integral coefficients recovered from an arbitrary actual Cartier
divisor. They are not included as part of its definition. -/
def cartierCoefficients (hpure : «Σ».IsPure) (D : CartierData («Σ».fanScheme k)) :
    Lattice n→ℤ :=
  «Σ».coefficientsOfCharacters hpure
    (fun s=>«Σ».normalizedChartExponent k D («Σ».fullConeIndex s))

theorem normalizedChartExponent_eq_cartierPoint (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) (s : «Σ».fullCones) :
    «Σ».normalizedChartExponent k D («Σ».fullConeIndex s) =
      «Σ».cartierLatticePoint («Σ».cartierCoefficients k hpure D) s := by
  change «Σ».normalizedChartExponent k D («Σ».fullConeIndex s) =
    «Σ».cartierLatticePoint («Σ».coefficientsOfCharacters hpure
      (fun t => «Σ».normalizedChartExponent k D («Σ».fullConeIndex t))) s
  apply «Σ».characters_eq_cartierLatticePoint hpure
    (fun t => «Σ».normalizedChartExponent k D («Σ».fullConeIndex t))
  intro s t v hvs hvt
  exact «Σ».normalizedChartExponent_pairing k D («Σ».fullConeIndex s) («Σ».fullConeIndex t)
    v hvs hvt

/-- Scalar units do not change the actual principal fractional module on
a chart. This statement uses actual regular sections on every subopen. -/
theorem mem_normalizedCartier_range_iff (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) (V : («Σ».fanScheme k).Opens) [Nonempty V]
    (hV : V≤(«Σ».fanChartMap k s).opensRange) (r : («Σ».fanScheme k).functionField) :
    r∈(«Σ».normalizedCartier k D).sectionValueRange V ↔
      r/(«Σ».rationalCharacter k («Σ».normalizedChartExponent k D s) :
        («Σ».fanScheme k).functionField) ∈
          ((«Σ».fanScheme k).germToFunctionField V).hom.range := by
  letI := «Σ».coneChart_isIntegral k s
  let N := «Σ».normalizedCartier k D
  let e := «Σ».normalizedChartFrame k D s
  let q := «Σ».normalizedChartGenerator k D s
  let c := «Σ».normalizedChartScalar k D s
  let m := «Σ».normalizedChartExponent k D s
  have hq : q=(«Σ».rationalScalarUnit k c : («Σ».fanScheme k).functionField) *
      («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) :=
    «Σ».normalizedChartGenerator_factor k D s
  constructor
  · intro hr
    obtain ⟨a,ha⟩ := (N.mem_sectionValueRange_iff_chartFrame
      («Σ».fanChartMap k s) e V hV r).mp hr
    apply (mem_regular_range_iff_stalkwise («Σ».fanScheme k) V _).mpr
    intro x hx
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem
      (regular_germ_mem_regularAt («Σ».fanScheme k) V a x hx)
      («Σ».rationalScalar_mem_regularAt k (c:k) x)
    have he : («Σ».fanScheme k).germToFunctionField V a * «Σ».rationalScalar k (c:k) =
        r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
      apply (eq_div_iff (Units.ne_zero («Σ».rationalCharacter k m))).mpr
      rw [mul_assoc]
      exact (congrArg ((«Σ».fanScheme k).germToFunctionField V a * ·) hq.symm).trans ha
    simpa only [he] using h
  · intro hr
    have hr' := (mem_regular_range_iff_stalkwise («Σ».fanScheme k) V _).mp hr
    have hregular : ∀ x∈V,r/q∈regularAtSubring («Σ».fanScheme k) x := by
      intro x hx
      have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem (hr' x hx)
        («Σ».rationalScalar_mem_regularAt k ((c⁻¹:kˣ):k) x)
      change (r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField)) *
        «Σ».rationalScalar k ((c⁻¹:kˣ):k) ∈ regularAtSubring («Σ».fanScheme k) x at h
      have he : (r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField)) *
          «Σ».rationalScalar k ((c⁻¹:kˣ):k) = r/q := by
        have hc : «Σ».rationalScalar k (c:k)≠0 := Units.ne_zero («Σ».rationalScalarUnit k c)
        rw [hq]
        simp only [rationalScalarUnit,Units.coe_map,Units.val_inv_eq_inv_val,map_inv₀]
        field_simp [hc,Units.ne_zero]
        rfl
      simpa only [he] using h
    obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise («Σ».fanScheme k) V (r/q) hregular
    apply (N.mem_sectionValueRange_iff_chartFrame («Σ».fanChartMap k s) e V hV r).mpr
    refine ⟨a,?_⟩
    rw [ha]
    exact div_mul_cancel₀ r («Σ».normalizedChartGenerator_ne_zero k D s)

/-- Equality of actual Cartier-divisor presentations after the explicit
principal normalization on the dense torus. No invariant presentation is
assumed for the input divisor. -/
theorem normalizedCartier_equivalent_fanCartier (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).Equivalent
      («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)) := by
  apply («Σ».normalizedCartier k D).equivalent_of_local_ranges
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».fullChartOpen k) («Σ».fullChartOpen_cover k hpure)
  intro s V _ hV
  ext r
  change r ∈ («Σ».normalizedCartier k D).sectionValueRange V ↔
    r ∈ («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)).sectionValueRange V
  rw [«Σ».mem_normalizedCartier_range_iff k D («Σ».fullConeIndex s) V hV r]
  rw [«Σ».normalizedChartExponent_eq_cartierPoint k hpure D s]
  exact ((«Σ».fanCartierCocycle k hpure («Σ».cartierCoefficients k hpure D)).mem_sectionValueRange_iff (ULift.up s) V hV r).symm

/-- Every arbitrary Cartier sheaf on the actual smooth fan scheme is
linearly equivalent to a proved integral invariant presentation. -/
theorem cartierData_linearlyEquivalent_fanCartier (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    D.LinearlyEquivalent
      («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)) := by
  exact D.linearlyEquivalent_trans («Σ».normalizedCartier k D) _
    ((«Σ».normalizedCartier k D).linearlyEquivalent_symm D
      («Σ».normalizedCartier_linearlyEquivalent k D))
    ⟨(«Σ».normalizedCartier_equivalent_fanCartier k hpure D).choose⟩

/-- The actual section-space dictionary for an arbitrary Cartier divisor,
after the explicitly recorded principal translation. -/
theorem normalizedCartier_globalRange (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) =
      «Σ».torusRationalMap k ''
        (characterModule k («Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D)) :
          Set (AddMonoidAlgebra k (Lattice n))) := by
  have hr := («Σ».normalizedCartier k D).equivalent_sectionValueRange
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D) ⊤
  change (↑((«Σ».normalizedCartier k D).sectionValueRange ⊤) :
    Set («Σ».fanScheme k).functionField)=_
  rw [hr]
  exact «Σ».fanCartier_globalRange k hpure _

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_equivalent_fanCartier
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierData_linearlyEquivalent_fanCartier
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_globalRange
