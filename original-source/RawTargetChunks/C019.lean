module
public import RawTargetChunks.C019A
public import RawTargetChunks.C019B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree019 : TargetTree :=
  .branch 64 chunkPart019A chunkPart019B

end Nonrational.TerminalData
