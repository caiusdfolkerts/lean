module
public import RawTargetChunks.C036A
public import RawTargetChunks.C036B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree036 : TargetTree :=
  .branch 64 chunkPart036A chunkPart036B

end Nonrational.TerminalData
