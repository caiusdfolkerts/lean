module

public import PaperVerification.ToricInvertibleAffine
public import PaperVerification.ToricFunctionFieldBridge

@[expose] public section

/-!
# Restriction of actual rank-one sheaves

An open immersion transports actual local frames through its actual
isomorphisms on sections. The proof constructs the linear maps on every
smaller open and checks their restriction compatibility.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : IsInvertibleModule M)

theorem invertibleFrameCoordinates_restrict (x : X)
    {U V : X.Opens} (i : V ⟶ U)
    (hU : U≤ invertibleOpen hM x) (hV : V≤ invertibleOpen hM x)
    (s : Γ(M,U)) :
    invertibleFrameCoordinates hM x V hV (M.presheaf.map i.op s) =
      X.presheaf.map i.op (invertibleFrameCoordinates hM x U hU s) := by
  let f : Over.mk (homOfLE hV) ⟶ Over.mk (homOfLE hU) :=
    Over.homMk i (by subsingleton)
  exact PresheafOfModules.naturality_apply (invertibleFrame hM x).hom.val f.op s

/-- Local frame coordinates transported along the actual section
isomorphism of an open immersion. -/
def restrictFrameCoordinates (x : X) (U : Y.Opens)
    (hU : j ''ᵁ U≤ invertibleOpen hM x) :
    Γ(M.restrict j,U) ≃ₗ[Γ(Y,U)] Γ(Y,U) := by
  let eM := (M.restrictAppIso j U).addCommGroupIsoToAddEquiv
  let eX := invertibleFrameCoordinates hM x (j ''ᵁ U) hU
  let eR := (j.appIso U).commRingCatIsoToRingEquiv
  refine
    { toFun := fun s=>eR (eX (eM s))
      invFun := fun a=>eM.symm (eX.symm (eR.symm a))
      left_inv := by intro s; simp
      right_inv := by intro a; simp
      map_add' := by intro s t; simp
      map_smul' := ?_ }
  intro a s
  change eR (eX (eR.symm a • eM s)) = a * eR (eX (eM s))
  rw [eX.map_smul]
  change eR (eR.symm a * eX (eM s)) = _
  rw [map_mul,RingEquiv.apply_symm_apply]

theorem restrictFrameCoordinates_restrict (x : X)
    {U V : Y.Opens} (i : V ⟶ U)
    (hU : j ''ᵁ U≤ invertibleOpen hM x)
    (hV : j ''ᵁ V≤ invertibleOpen hM x) (s : Γ(M.restrict j,U)) :
    restrictFrameCoordinates j hM x V hV ((M.restrict j).presheaf.map i.op s) =
      Y.presheaf.map i.op (restrictFrameCoordinates j hM x U hU s) := by
  let i' : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_mono i.le)
  let t : Γ(M,j ''ᵁ U) := (M.restrictAppIso j U).hom s
  change (j.appIso V).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ V) hV (M.presheaf.map i'.op t)) =
    Y.presheaf.map i.op ((j.appIso U).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t))
  have hn : X.presheaf.map i'.op ≫ (j.appIso V).hom =
      (j.appIso U).hom ≫ Y.presheaf.map i.op := by
    simp [Scheme.Hom.appIso_hom']
  calc
    _ = (j.appIso V).hom (X.presheaf.map i'.op
        (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) :=
      congrArg (fun a : Γ(X,j ''ᵁ V) => (j.appIso V).hom a)
        (invertibleFrameCoordinates_restrict hM x i' hU hV t)
    _ = _ := congrArg (fun f : Γ(X,j ''ᵁ U) ⟶ Γ(Y,V) =>
      f (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) hn

include hM in
/-- Restriction along an actual open immersion preserves local rank one. -/
theorem isInvertibleModule_restrict : IsInvertibleModule (M.restrict j) := by
  intro y
  let U : Y.Opens := j ⁻¹ᵁ invertibleOpen hM (j y)
  have hy : y∈U := mem_invertibleOpen hM (j y)
  refine ⟨U,hy,⟨?_⟩⟩
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V=>?_) ?_
  · have hV : j ''ᵁ V.unop.left≤ invertibleOpen hM (j y) := by
      rintro z ⟨v,hv,rfl⟩
      exact V.unop.hom.le hv
    exact (restrictFrameCoordinates j hM (j y) V.unop.left hV).toModuleIso
  · intro V W f
    ext s
    exact restrictFrameCoordinates_restrict j hM (j y) f.unop.left _ _ s

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_restrict
