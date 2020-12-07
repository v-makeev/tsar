#include "tsar/Transform/IR/ArrayScalarize.h"

#include "tsar/Analysis/Memory/DefinedMemory.h"
#include "tsar/Analysis/Memory/EstimateMemory.h"
#include "tsar/Core/Query.h"
#include "tsar/Support/IRUtils.h"
#include "tsar/Support/PassAAProvider.h"

#include <iostream>
#include <llvm/IR/DIBuilder.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/InitializePasses.h>


#undef DEBUG_TYPE
#define DEBUG_TYPE "arr-sc"

using namespace llvm;
using namespace tsar;

char ArrayScalarizePass::ID = 0;

INITIALIZE_PASS_BEGIN(ArrayScalarizePass, "arr-sc",
                      "Array Scalarization Pass", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(GlobalDefinedMemoryWrapper)
INITIALIZE_PASS_END(ArrayScalarizePass, "arr-sc",
                    "Array Scalarization Pass", false, false)

void ArrayScalarizePass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<LoopInfoWrapperPass>();
  AU.addRequired<GlobalDefinedMemoryWrapper>();
}

class arrayScalarizeContext {
  public:
  arrayScalarizeContext(Value *V, ArrayType *arrType) : V(V), ArrType(arrType) {}

  void insertScalars(BasicBlock *InsertAtEnd) {
    auto *Int64Ty = Type::getInt64Ty(InsertAtEnd->getContext());
    auto *Int0 = ConstantInt::get(Int64Ty, 0);
    for (int i = 0; i < ArrType->getNumElements(); ++i) {
      auto *IntI = ConstantInt::get(Int64Ty, i);
      auto *GEP = GetElementPtrInst::Create(ArrType, V, {Int0, IntI}, V->getName(), InsertAtEnd->getTerminator());
      ScalarGEPList.insert(GEP);
    }
  }

  ArrayType *ArrType;
  Value *V;
  SetVector<GetElementPtrInst *> ScalarGEPList;
};

struct splitBBInfo {
  splitBBInfo(BasicBlock *begin, BasicBlock *end, Value *idxValue) : Begin(begin), End(end), IdxValue(idxValue) {}

  BasicBlock *Begin;
  BasicBlock *End;
  Value *IdxValue;
};

void createBBSwitch(Function &F, arrayScalarizeContext &Ctx, const splitBBInfo &Info) {
  if (Ctx.ScalarGEPList.empty()) {
    return;
  }

  Info.Begin->back().eraseFromParent();
  auto *switchInst = SwitchInst::Create(Info.IdxValue, Info.End, Ctx.ArrType->getNumElements(), Info.Begin);

  auto *IdxType = Info.IdxValue->getType();
  auto insertedLoads = SetVector<LoadInst *>();
  for (int i = 0; i < Ctx.ArrType->getNumElements(); ++i) {
    auto val = ConstantInt::get(IdxType, i);
    assert(isa<ConstantInt>(val));

    auto *newBB = BasicBlock::Create(Info.Begin->getContext(), Ctx.V->getName() + "_case_" + std::to_string(i), &F);
    BranchInst::Create(Info.End, newBB);
    auto *load = new LoadInst(Ctx.ScalarGEPList[i]->getType()->getPointerElementType(), Ctx.ScalarGEPList[i], "load_" + Ctx.V->getName() + std::to_string(i), &newBB->back());
    insertedLoads.insert(load);

    switchInst->addCase(dyn_cast<ConstantInt>(val), newBB);
  }

  auto phiType = Ctx.ScalarGEPList[0]->getType()->getPointerElementType();
  auto *phiNode = PHINode::Create(phiType, Ctx.ScalarGEPList.size());

  // first node of End BB is always GEP and its children is always LoadInst
  auto *GEP = Info.End->getFirstNonPHIOrDbgOrLifetime();
  while (!GEP->user_empty()) {
    if (auto *Inst = dyn_cast<Instruction>(*GEP->user_begin())) {
      Inst->replaceAllUsesWith(phiNode);
      Inst->dropAllReferences();
      Inst->eraseFromParent();
    }
  }
  GEP->dropAllReferences();
  GEP->eraseFromParent();
  phiNode->insertBefore(&Info.End->front());
  for (auto *load : insertedLoads) {
    phiNode->addIncoming(load, load->getParent());
  }
}

bool ArrayScalarizePass::runOnFunction(Function &F) {
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &GDM = getAnalysis<GlobalDefinedMemoryWrapper>().get();


  for_each_loop(LI, [&F, &GDM](Loop *L) {
    // collect all array variables that are use inside loop's GEP instructions
    // they can either be global of local (defined with alloca inst)
    auto GlobalAT = DenseSet<GlobalVariable *>();
    auto LocalAT = DenseSet<AllocaInst *>();

    for (auto *BB : L->getBlocks()) {
      for (auto &Inst : BB->getInstList()) {
        if (auto *GEP = dyn_cast<GetElementPtrInst>(&Inst)) {
          auto *sourceOp = GEP->getPointerOperand();
          if (auto *Parent = dyn_cast<GlobalVariable>(sourceOp)) {
            if (auto *AT = dyn_cast<ArrayType>(Parent->getType()->getPointerElementType())) {
              printf("got a global array with %lu elements\n", AT->getNumElements());
              GlobalAT.insert(Parent);
            }
          }

          if (auto *Parent = dyn_cast<AllocaInst>(sourceOp)) {
            if (auto *AT = dyn_cast<ArrayType>(Parent->getOperand(0)->getType())) {
              printf("got a local array with %lu elements\n", AT->getNumElements());
              LocalAT.insert(Parent);
            }
          }
        }
      }
    }

    // delete all global variables that are used in other functions
    // for now
    auto GlobalsToDelete = DenseSet<GlobalVariable *>();
    for (auto it = GDM.begin(); it != GDM.end(); ++it) {
      if (it->getFirst() == &F) {
        continue;
      }
      for (auto *AT : GlobalAT) {
        for (auto &Use : it->getSecond()->getUses()) {
          if (AT == Use.Ptr) {
            GlobalsToDelete.insert(AT);
          }
        }
        for (auto &Def : it->getSecond()->getDefs()) {
          if (AT == Def.Ptr) {
            GlobalsToDelete.insert(AT);
          }
        }
      }
    }
    for (auto *GL : GlobalsToDelete) {
      printf("skipping global arr %s\n", GL->getName().data());
      GlobalAT.erase(GL);
    }

    // create new context for every array candidate
    auto Ctxs = SmallVector<arrayScalarizeContext, 8>();
    for (auto *AT : GlobalAT) {
      Ctxs.emplace_back(AT, dyn_cast<ArrayType>(AT->getOperand(0)->getType()));
    }
    for (auto *AT : LocalAT) {
      Ctxs.emplace_back(AT, dyn_cast<ArrayType>(AT->getType()->getPointerElementType()));
    }

    for (auto &Ctx : Ctxs) {
      Ctx.insertScalars(L->getLoopPredecessor());
    }

    for (auto &Ctx : Ctxs) {
      SmallVector<splitBBInfo, 16> BBInfo;
      while (true) {
        bool hasSplit = false;
        for (auto *BB : L->getBlocks()) {
          for (auto &Inst : BB->getInstList()) {
            if (auto *GEP = dyn_cast<GetElementPtrInst>(&Inst)) {
              // TODO: get arbitrary index
              auto *idxVal = GEP->getOperand(2);
              auto newBB = BB->splitBasicBlock(GEP);
              BBInfo.emplace_back(BB, newBB, idxVal);
              hasSplit = true;
              break;
            }
          }
        }
        if (!hasSplit) {
          break;
        }
      }

      for (auto &Info : BBInfo) {
        createBBSwitch(F, Ctx, Info);
      }
    }
  });
  return false;
}
