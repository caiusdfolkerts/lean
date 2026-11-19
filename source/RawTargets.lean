module
public import RawTargetChunks.C000
public import RawTargetChunks.C001
public import RawTargetChunks.C002
public import RawTargetChunks.C003
public import RawTargetChunks.C004
public import RawTargetChunks.C005
public import RawTargetChunks.C006
public import RawTargetChunks.C007
public import RawTargetChunks.C008
public import RawTargetChunks.C009
public import RawTargetChunks.C010
public import RawTargetChunks.C011
public import RawTargetChunks.C012
public import RawTargetChunks.C013
public import RawTargetChunks.C014
public import RawTargetChunks.C015
public import RawTargetChunks.C016
public import RawTargetChunks.C017
public import RawTargetChunks.C018
public import RawTargetChunks.C019
public import RawTargetChunks.C020
public import RawTargetChunks.C021
public import RawTargetChunks.C022
public import RawTargetChunks.C023
public import RawTargetChunks.C024
public import RawTargetChunks.C025
public import RawTargetChunks.C026
public import RawTargetChunks.C027
public import RawTargetChunks.C028
public import RawTargetChunks.C029
public import RawTargetChunks.C030
public import RawTargetChunks.C031
public import RawTargetChunks.C032
public import RawTargetChunks.C033
public import RawTargetChunks.C034
public import RawTargetChunks.C035
public import RawTargetChunks.C036

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def targetCount : Nat := 4726

noncomputable def targetTree : TargetTree :=
  (.branch 2304 ((.branch 1152 ((.branch 512 ((.branch 256 ((.branch 128 (chunkTree000) (chunkTree001))) ((.branch 128 (chunkTree002) (chunkTree003))))) ((.branch 256 ((.branch 128 (chunkTree004) (chunkTree005))) ((.branch 128 (chunkTree006) ((.branch 128 (chunkTree007) (chunkTree008))))))))) ((.branch 512 ((.branch 256 ((.branch 128 (chunkTree009) (chunkTree010))) ((.branch 128 (chunkTree011) (chunkTree012))))) ((.branch 256 ((.branch 128 (chunkTree013) (chunkTree014))) ((.branch 128 (chunkTree015) ((.branch 128 (chunkTree016) (chunkTree017))))))))))) ((.branch 1152 ((.branch 512 ((.branch 256 ((.branch 128 (chunkTree018) (chunkTree019))) ((.branch 128 (chunkTree020) (chunkTree021))))) ((.branch 256 ((.branch 128 (chunkTree022) (chunkTree023))) ((.branch 128 (chunkTree024) ((.branch 128 (chunkTree025) (chunkTree026))))))))) ((.branch 640 ((.branch 256 ((.branch 128 (chunkTree027) (chunkTree028))) ((.branch 128 (chunkTree029) ((.branch 128 (chunkTree030) (chunkTree031))))))) ((.branch 256 ((.branch 128 (chunkTree032) (chunkTree033))) ((.branch 128 (chunkTree034) ((.branch 128 (chunkTree035) (chunkTree036))))))))))))

noncomputable def targets (i : Nat) : RawBoundary := targetTree.get i

end Nonrational.TerminalData
