//===--- NoMacroAssert.cpp - No Macro Assert (Clang) -----------*- C++ -*-===//
//
//                       Traits Static Analyzer (SAPFOR)
//
//===----------------------------------------------------------------------===//
//
// This file implements a pass which checks absence of macro in a specified
// source range marked with `#pragma spf assert nomacro`. Note, that all
// preprocessor directives (except #pragma) are also treated as a macros.
//
//===----------------------------------------------------------------------===//

#include "NoMacroAssert.h"
#include "Diagnostic.h"
#include "GlobalInfoExtractor.h"
#include "tsar_query.h"
#include "PassGroupRegistry.h"
#include "tsar_transformation.h"
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>

using namespace clang;
using namespace llvm;
using namespace tsar;

#undef DEBUG_TYPE
#define DEBUG_TYPE "clang-nomacro-assert"

char ClangNoMacroAssert::ID = 0;
INITIALIZE_PASS_IN_GROUP_BEGIN(ClangNoMacroAssert, "clang-nomacro-assert",
  "No Macro Assert (Clang)", false, false, CheckQueryManager::getPassRegistry())
  INITIALIZE_PASS_DEPENDENCY(TransformationEnginePass)
  INITIALIZE_PASS_DEPENDENCY(ClangGlobalInfoPass)
INITIALIZE_PASS_IN_GROUP_END(ClangNoMacroAssert, "clang-nomacro-assert",
  "No Macro Assert (Clang)", false, false, CheckQueryManager::getPassRegistry())

FunctionPass * llvm::createClangNoMacroAssert(bool *IsInvalid) {
  return new ClangNoMacroAssert(IsInvalid);
}

void ClangNoMacroAssert::getAnalysisUsage(AnalysisUsage& AU) const {
  AU.addRequired<TransformationEnginePass>();
  AU.addRequired<ClangGlobalInfoPass>();
  AU.setPreservesAll();
}

namespace {
class NoMacroChecker : public RecursiveASTVisitor<NoMacroChecker> {
public:
  NoMacroChecker(const SourceManager &SrcMgr, const LangOptions &LangOpts,
    const StringMap<SourceLocation> &RawMacros) :
    mSrcMgr(SrcMgr), mLangOpts(LangOpts), mRawMacros(RawMacros) {}

  bool isValid() const noexcept { return !mIsInvalid; }
  bool isInvalid() const noexcept { return mIsInvalid; }

  bool TraverseStmt(Stmt *S) {
    if (!S)
      return true;
    SmallVector<Stmt *, 1> Clauses;
    Pragma P(*S);
    if (findClause(P, ClauseId::AssertNoMacro, Clauses)) {
      mActiveClause = !mActiveClause ? Clauses.front() : mActiveClause;
      return true;
    }
    if (P)
      return true;
    if (mActiveClause) {
      checkNode(S);
      mActiveClause = nullptr;
      return true;
    }
    return RecursiveASTVisitor::TraverseStmt(S);
  }

  bool TraverseDecl(Decl *D) {
    if (mActiveClause) {
      checkNode(D);
      mActiveClause = nullptr;
      return true;
    }
    return RecursiveASTVisitor::TraverseDecl(D);
  }

  bool VisitiTypeLoc(TypeLoc T) {
    if (mActiveClause) {
      checkNode(T);
      mActiveClause = nullptr;
      return true;
    }
    return RecursiveASTVisitor::TraverseTypeLoc(T);
  }

private:
  template<class T> void checkNode(T Node) {
    auto MacroVisitor = [this](SourceLocation Loc) {
      mIsInvalid = true;
      toDiag(mSrcMgr.getDiagnostics(), mActiveClause->getLocStart(),
        diag::err_assert);
      toDiag(mSrcMgr.getDiagnostics(), Loc,
        diag::note_assert_no_macro);
    };
    if (!for_each_macro(Node, mSrcMgr, mLangOpts, mRawMacros, MacroVisitor)) {
      mIsInvalid = true;
      toDiag(mSrcMgr.getDiagnostics(), mActiveClause->getLocStart(),
        diag::err_assert);
      toDiag(mSrcMgr.getDiagnostics(), getPointer(Node)->getLocStart(),
        diag::note_source_range_not_single_file);
      toDiag(mSrcMgr.getDiagnostics(), getPointer(Node)->getLocEnd(),
        diag::note_end_location);
    }
  }

  template<class T> T * getPointer(T *Ptr) noexcept { return Ptr; }
  TypeLoc * getPointer(TypeLoc &TL) noexcept { return &TL; }

  const SourceManager &mSrcMgr;
  const LangOptions &mLangOpts;
  const StringMap<SourceLocation> &mRawMacros;
  clang::Stmt *mActiveClause = nullptr;
  bool mIsInvalid = false;
};
}

bool ClangNoMacroAssert::runOnFunction(Function &F) {
  auto *M = F.getParent();
  auto TfmCtx = getAnalysis<TransformationEnginePass>().getContext(*M);
  if (!TfmCtx || !TfmCtx->hasInstance()) {
    M->getContext().emitError("can not check sources"
        ": transformation context is not available");
    if (mIsInvalid)
      *mIsInvalid = true;
    return false;
  }
  auto &SrcMgr = TfmCtx->getContext().getSourceManager();
  auto &LangOpts = TfmCtx->getContext().getLangOpts();
  auto *Unit = TfmCtx->getContext().getTranslationUnitDecl();
  auto &GIP = getAnalysis<ClangGlobalInfoPass>();
  NoMacroChecker Checker(SrcMgr, LangOpts, GIP.getRawInfo().Macros);
  Checker.TraverseDecl(Unit);
  if (mIsInvalid)
    *mIsInvalid = Checker.isInvalid();
  return false;
}
