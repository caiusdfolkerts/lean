module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots27

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row27.offset : Nat :=
16802
def Papers.RationalityTen.SharedEmptyKeys.Row27.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row27.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row27.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row27.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row27.offset + i) =
      (27,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row27.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row27.rootCount i))))

