module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots19

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row19.offset : Nat :=
1263
def Papers.RationalityTen.SharedEmptyKeys.Row19.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row19.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row19.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row19.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row19.offset + i) =
      (19,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row19.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row19.rootCount i))))

