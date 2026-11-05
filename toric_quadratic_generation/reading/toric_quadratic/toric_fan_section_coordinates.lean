module

public import PaperVerification.ToricArbitraryCartierFan
public import PaperVerification.ToricFanAction
public import PaperVerification.ToricBaseSectionNaturality

@[expose] public section

/-!
# The actual base-linear character coordinates of global sections

The scalar maps are induced by the actual structural morphism to Spec(k).
The resulting isomorphism therefore concerns the ordinary vector space
of genuine global sections over the base field, with its true rational
value map.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite



namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BaseSections Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance fanSectionCoordinates_splitTorus_integral : IsIntegral (ToricGeometry.splitTorus k n) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- Constants in the character algebra agree with constants from the
actual structural morphism of the glued scheme. -/
theorem rationalScalar_eq_algebraMap (c : k) :
    «Σ».rationalScalar k c=algebraMap k («Σ».fanScheme k).functionField c := by
  let j := «Σ».splitTorusOpenMap k
  let A := AddMonoidAlgebra k (Lattice n)
  have hconst : j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    calc
      j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
          BaseSections.scalarMap k (ToricGeometry.splitTorus k n) ⊤ c :=
        BaseSections.scalarMap_top_natural k j c
      _ = _ := by
        change BaseSections.scalarMap k (Spec (CommRingCat.of A)) ⊤ c = _
        exact BaseSections.scalarMap_affine_top k A c
  change «Σ».torusRationalMap k (algebraMap k A c) =
    («Σ».fanScheme k).germToFunctionField ⊤ (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)
  rw [«Σ».torusRationalMap_eq_openImmersion]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : («Σ».fanScheme k).Opens)) :=
    openImmersion_preimage_nonempty j ⊤
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
    ((openImmersionFunctionFieldEquiv j).symm
      ((ToricGeometry.splitTorus k n).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c)))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun a : Γ(ToricGeometry.splitTorus k n, ⊤) =>
    (ToricGeometry.splitTorus k n).germToFunctionField ⊤ a) hconst.symm).trans
    (openImmersionFunctionFieldEquiv_germ j ⊤
      (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)).symm

/-- The actual Laurent embedding is an algebra map over the true base. -/
def torusRationalAlgHom : AddMonoidAlgebra k (Lattice n) →ₐ[k]
    («Σ».fanScheme k).functionField where
  __ := «Σ».torusRationalMap k
  commutes' := «Σ».rationalScalar_eq_algebraMap k

theorem torusRationalAlgHom_injective : Function.Injective («Σ».torusRationalAlgHom k) :=
  «Σ».torusRationalMap_injective k

/-- Base-linear Laurent evaluation on the allowed exponent submodule. -/
def fanCharacterValue (a : Lattice n→ℤ) :
    characterModule k («Σ».fanIntegralExponents a) →ₗ[k] («Σ».fanScheme k).functionField :=
  («Σ».torusRationalAlgHom k).toLinearMap.comp
    (characterModule k («Σ».fanIntegralExponents a)).subtype

theorem fanCharacterValue_injective (a : Lattice n→ℤ) :
    Function.Injective («Σ».fanCharacterValue k a) :=
  («Σ».torusRationalMap_injective k).comp Subtype.val_injective

theorem fanCartier_globalSectionValue_range (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    ((«Σ».fanCartierData k hpure a).globalSectionValue k).range =
      («Σ».fanCharacterValue k a).range := by
  apply SetLike.coe_injective
  change Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) = _
  rw [«Σ».fanCartier_globalRange]
  ext r
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact ⟨⟨f,hf⟩,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨f.val,f.property,rfl⟩

/-- The actual global-section vector space is canonically identified by
its rational values with the literal finite-support character module. -/
def fanCartierSectionCoordinates (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    Γ((«Σ».fanCartierData k hpure a).sheaf,⊤) ≃ₗ[k]
      characterModule k («Σ».fanIntegralExponents a) :=
  (LinearEquiv.ofInjective ((«Σ».fanCartierData k hpure a).globalSectionValue k)
    ((«Σ».fanCartierData k hpure a).globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ («Σ».fanCartier_globalSectionValue_range k hpure a)).trans
      (LinearEquiv.ofInjective («Σ».fanCharacterValue k a)
        («Σ».fanCharacterValue_injective k a)).symm)

theorem fanCartierSectionCoordinates_value (hpure : «Σ».IsPure) (a : Lattice n→ℤ)
    (s : Γ((«Σ».fanCartierData k hpure a).sheaf,⊤)) :
    «Σ».torusRationalMap k ((«Σ».fanCartierSectionCoordinates k hpure a s).val) =
      («Σ».fanCartierData k hpure a).globalSectionValue k s := by
  change «Σ».fanCharacterValue k a («Σ».fanCartierSectionCoordinates k hpure a s)=_
  simp only [fanCartierSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rationalScalar_eq_algebraMap
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates_value
