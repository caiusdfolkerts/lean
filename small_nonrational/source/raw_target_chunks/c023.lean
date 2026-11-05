module
public import RawTargetChunks.C023A
public import RawTargetChunks.C023B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree023 : TargetTree :=
  .branch 64 chunkPart023A chunkPart023B

end Nonrational.TerminalData
