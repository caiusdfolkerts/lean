module
public import RawTargetChunks.C022A
public import RawTargetChunks.C022B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree022 : TargetTree :=
  .branch 64 chunkPart022A chunkPart022B

end Nonrational.TerminalData
