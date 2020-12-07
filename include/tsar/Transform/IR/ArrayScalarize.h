#include "Passes.h"
#include <bcl/utility.h>
#include <llvm/Pass.h>

#ifndef TSAR_ARRAY_SCALARIZE_H
#define TSAR_ARRAY_SCALARIZE_H

namespace llvm {
class ArrayScalarizePass : public FunctionPass, private bcl::Uncopyable {
public:
  /// Pass identification, replacement for typeid.
  static char ID;

  /// Default constructor.
  ArrayScalarizePass() : FunctionPass(ID) {
    initializeArrayScalarizePassPass(*PassRegistry::getPassRegistry());
  }

  /// Executes reach definition analysis for a specified function.
  bool runOnFunction(Function &F) override;

  /// Specifies a list of analyzes that are necessary for this pass.
  void getAnalysisUsage(AnalysisUsage &AU) const override;

  /// Releases memory.
  void releaseMemory() override { }
};

FunctionPass *createArrayScalarizePass() {
  return new ArrayScalarizePass();
}
}
#endif//TSAR_ARRAY_SCALARIZE_H
