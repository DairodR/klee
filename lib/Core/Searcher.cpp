
//===-- Searcher.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Searcher.h"

#include "CoreStats.h"
#include "ExecutionState.h"
#include "ExecutionTree.h"
#include "Executor.h"
#include "MergeHandler.h"
#include "StatsTracker.h"

#include "klee/ADT/DiscretePDF.h"
#include "klee/ADT/RNG.h"
#include "klee/Statistics/Statistics.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/System/Time.h"

#include "klee/Support/CompilerWarning.h"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <igraph/igraph_foreign.h>
#include <igraph/igraph_interface.h>
#include <igraph/igraph_interrupt.h>
#include <igraph/igraph_paths.h>
#include <igraph/igraph_types.h>
#include <igraph/igraph_vector.h>
#include <iostream>
#include <llvm-13/llvm/ADT/GraphTraits.h>
#include <llvm-13/llvm/ADT/PostOrderIterator.h>
#include <llvm-13/llvm/IR/BasicBlock.h>
#include <llvm-13/llvm/IR/DebugInfoMetadata.h>
#include <llvm-13/llvm/IR/Function.h>
#include <llvm-13/llvm/IR/LLVMContext.h>
#include <llvm-13/llvm/IR/LegacyPassManager.h>
#include <llvm-13/llvm/IRReader/IRReader.h>
#include <llvm-13/llvm/Support/SourceMgr.h>
#include <llvm-13/llvm/Support/raw_ostream.h>
#include <llvm-13/llvm/IR/CFG.h>
#include <string>
#include <system_error>
DISABLE_WARNING_PUSH
DISABLE_WARNING_DEPRECATED_DECLARATIONS

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"


#include "llvm/Analysis/CFGPrinter.h"
DISABLE_WARNING_POP

#include <cassert>
#include <cmath>

#include <unordered_map>
#include <vector>
#include <igraph/igraph.h>


using namespace klee;
using namespace llvm;


///

ExecutionState &DFSSearcher::selectState() {
  return *states.back();
}

void DFSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  // insert states
  states.insert(states.end(), addedStates.begin(), addedStates.end());

  // remove states
  for (const auto state : removedStates) {
    if (state == states.back()) {
      states.pop_back();
    } else {
      auto it = std::find(states.begin(), states.end(), state);
      assert(it != states.end() && "invalid state removed");
      states.erase(it);
    }
  }
}

bool DFSSearcher::empty() {
  return states.empty();
}

void DFSSearcher::printName(llvm::raw_ostream &os) {
  os << "DFSSearcher\n";
}


///

ExecutionState &BFSSearcher::selectState() {
  return *states.front();
}

void BFSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  // update current state
  // Assumption: If new states were added KLEE forked, therefore states evolved.
  // constraints were added to the current state, it evolved.
  if (!addedStates.empty() && current &&
      std::find(removedStates.begin(), removedStates.end(), current) == removedStates.end()) {
    auto pos = std::find(states.begin(), states.end(), current);
    assert(pos != states.end());
    states.erase(pos);
    states.push_back(current);
  }

  // insert states
  states.insert(states.end(), addedStates.begin(), addedStates.end());

  // remove states
  for (const auto state : removedStates) {
    if (state == states.front()) {
      states.pop_front();
    } else {
      auto it = std::find(states.begin(), states.end(), state);
      assert(it != states.end() && "invalid state removed");
      states.erase(it);
    }
  }
}

bool BFSSearcher::empty() {
  return states.empty();
}

void BFSSearcher::printName(llvm::raw_ostream &os) {
  os << "BFSSearcher\n";
}


///

RandomSearcher::RandomSearcher(RNG &rng) : theRNG{rng} {}

ExecutionState &RandomSearcher::selectState() {
  return *states[theRNG.getInt32() % states.size()];
}

void RandomSearcher::update(ExecutionState *current,
                            const std::vector<ExecutionState *> &addedStates,
                            const std::vector<ExecutionState *> &removedStates) {
  // insert states
  states.insert(states.end(), addedStates.begin(), addedStates.end());

  // remove states
  for (const auto state : removedStates) {
    auto it = std::find(states.begin(), states.end(), state);
    assert(it != states.end() && "invalid state removed");
    states.erase(it);
  }
}

bool RandomSearcher::empty() {
  return states.empty();
}

void RandomSearcher::printName(llvm::raw_ostream &os) {
  os << "RandomSearcher\n";
}


///

WeightedRandomSearcher::WeightedRandomSearcher(WeightType type, RNG &rng)
  : states(std::make_unique<DiscretePDF<ExecutionState*, ExecutionStateIDCompare>>()),
    theRNG{rng},
    type(type) {

  switch(type) {
  case Depth:
  case RP:
    updateWeights = false;
    break;
  case InstCount:
  case CPInstCount:
  case QueryCost:
  case MinDistToUncovered:
  case CoveringNew:
    updateWeights = true;
    break;
  default:
    assert(0 && "invalid weight type");
  }
}

ExecutionState &WeightedRandomSearcher::selectState() {
  return *states->choose(theRNG.getDoubleL());
}

double WeightedRandomSearcher::getWeight(ExecutionState *es) {
  switch(type) {
    default:
    case Depth:
      return es->depth;
    case RP:
      return std::pow(0.5, es->depth);
    case InstCount: {
      uint64_t count = theStatisticManager->getIndexedValue(stats::instructions,
                                                            es->pc->info->id);
      double inv = 1. / std::max((uint64_t) 1, count);
      return inv * inv;
    }
    case CPInstCount: {
      StackFrame &sf = es->stack.back();
      uint64_t count = sf.callPathNode->statistics.getValue(stats::instructions);
      double inv = 1. / std::max((uint64_t) 1, count);
      return inv;
    }
    case QueryCost:
      return (es->queryMetaData.queryCost.toSeconds() < .1)
                 ? 1.
                 : 1. / es->queryMetaData.queryCost.toSeconds();
    case CoveringNew:
    case MinDistToUncovered: {
      uint64_t md2u = computeMinDistToUncovered(es->pc,
                                                es->stack.back().minDistToUncoveredOnReturn);

      double invMD2U = 1. / (md2u ? md2u : 10000);
      if (type == CoveringNew) {
        double invCovNew = 0.;
        if (es->instsSinceCovNew)
          invCovNew = 1. / std::max(1, (int) es->instsSinceCovNew - 1000);
        return (invCovNew * invCovNew + invMD2U * invMD2U);
      } else {
        return invMD2U * invMD2U;
      }
    }
  }
}

void WeightedRandomSearcher::update(ExecutionState *current,
                                    const std::vector<ExecutionState *> &addedStates,
                                    const std::vector<ExecutionState *> &removedStates) {

  // update current
  if (current && updateWeights &&
      std::find(removedStates.begin(), removedStates.end(), current) == removedStates.end())
    states->update(current, getWeight(current));

  // insert states
  for (const auto state : addedStates)
    states->insert(state, getWeight(state));

  // remove states
  for (const auto state : removedStates)
    states->remove(state);
}

bool WeightedRandomSearcher::empty() {
  return states->empty();
}

void WeightedRandomSearcher::printName(llvm::raw_ostream &os) {
  os << "WeightedRandomSearcher::";
  switch(type) {
    case Depth              : os << "Depth\n"; return;
    case RP                 : os << "RandomPath\n"; return;
    case QueryCost          : os << "QueryCost\n"; return;
    case InstCount          : os << "InstCount\n"; return;
    case CPInstCount        : os << "CPInstCount\n"; return;
    case MinDistToUncovered : os << "MinDistToUncovered\n"; return;
    case CoveringNew        : os << "CoveringNew\n"; return;
    default                 : os << "<unknown type>\n"; return;
  }
}


///

// Check if n is a valid pointer and a node belonging to us
#define IS_OUR_NODE_VALID(n)                                                   \
  (((n).getPointer() != nullptr) && (((n).getInt() & idBitMask) != 0))

RandomPathSearcher::RandomPathSearcher(InMemoryExecutionTree *executionTree, RNG &rng)
    : executionTree{executionTree}, theRNG{rng},
      idBitMask{static_cast<uint8_t>(executionTree ? executionTree->getNextId() : 0)} {
  assert(executionTree);
};

ExecutionState &RandomPathSearcher::selectState() {
  unsigned flips=0, bits=0;
  assert(executionTree->root.getInt() & idBitMask &&
         "Root should belong to the searcher");
  ExecutionTreeNode *n = executionTree->root.getPointer();
  while (!n->state) {
    if (!IS_OUR_NODE_VALID(n->left)) {
      assert(IS_OUR_NODE_VALID(n->right) && "Both left and right nodes invalid");
      assert(n != n->right.getPointer());
      n = n->right.getPointer();
    } else if (!IS_OUR_NODE_VALID(n->right)) {
      assert(IS_OUR_NODE_VALID(n->left) && "Both right and left nodes invalid");
      assert(n != n->left.getPointer());
      n = n->left.getPointer();
    } else {
      if (bits==0) {
        flips = theRNG.getInt32();
        bits = 32;
      }
      --bits;
      n = ((flips & (1U << bits)) ? n->left : n->right).getPointer();
    }
  }

  return *n->state;
}

void RandomPathSearcher::update(ExecutionState *current,
                                const std::vector<ExecutionState *> &addedStates,
                                const std::vector<ExecutionState *> &removedStates) {
  // insert states
  for (auto es : addedStates) {
    ExecutionTreeNode *etnode = es->executionTreeNode, *parent = etnode->parent;
    ExecutionTreeNodePtr *childPtr;

    childPtr = parent ? ((parent->left.getPointer() == etnode) ? &parent->left
                                                               : &parent->right)
                      : &executionTree->root;
    while (etnode && !IS_OUR_NODE_VALID(*childPtr)) {
      childPtr->setInt(childPtr->getInt() | idBitMask);
      etnode = parent;
      if (etnode)
        parent = etnode->parent;

      childPtr = parent
                     ? ((parent->left.getPointer() == etnode) ? &parent->left
                                                              : &parent->right)
                     : &executionTree->root;
    }
  }

  // remove states
  for (auto es : removedStates) {
    ExecutionTreeNode *etnode = es->executionTreeNode, *parent = etnode->parent;

    while (etnode && !IS_OUR_NODE_VALID(etnode->left) &&
           !IS_OUR_NODE_VALID(etnode->right)) {
      auto childPtr =
          parent ? ((parent->left.getPointer() == etnode) ? &parent->left
                                                          : &parent->right)
                 : &executionTree->root;
      assert(IS_OUR_NODE_VALID(*childPtr) &&
             "Removing executionTree child not ours");
      childPtr->setInt(childPtr->getInt() & ~idBitMask);
      etnode = parent;
      if (etnode)
        parent = etnode->parent;
    }
  }
}

bool RandomPathSearcher::empty() {
  return !IS_OUR_NODE_VALID(executionTree->root);
}

void RandomPathSearcher::printName(llvm::raw_ostream &os) {
  os << "RandomPathSearcher\n";
}


///

MergingSearcher::MergingSearcher(Searcher *baseSearcher)
  : baseSearcher{baseSearcher} {};

void MergingSearcher::pauseState(ExecutionState &state) {
  assert(std::find(pausedStates.begin(), pausedStates.end(), &state) == pausedStates.end());
  pausedStates.push_back(&state);
  baseSearcher->update(nullptr, {}, {&state});
}

void MergingSearcher::continueState(ExecutionState &state) {
  auto it = std::find(pausedStates.begin(), pausedStates.end(), &state);
  assert(it != pausedStates.end());
  pausedStates.erase(it);
  baseSearcher->update(nullptr, {&state}, {});
}

ExecutionState& MergingSearcher::selectState() {
  assert(!baseSearcher->empty() && "base searcher is empty");

  if (!UseIncompleteMerge)
    return baseSearcher->selectState();

  // Iterate through all MergeHandlers
  for (auto cur_mergehandler: mergeGroups) {
    // Find one that has states that could be released
    if (!cur_mergehandler->hasMergedStates()) {
      continue;
    }
    // Find a state that can be prioritized
    ExecutionState *es = cur_mergehandler->getPrioritizeState();
    if (es) {
      return *es;
    } else {
      if (DebugLogIncompleteMerge){
        llvm::errs() << "Preemptively releasing states\n";
      }
      // If no state can be prioritized, they all exceeded the amount of time we
      // are willing to wait for them. Release the states that already arrived at close_merge.
      cur_mergehandler->releaseStates();
    }
  }
  // If we were not able to prioritize a merging state, just return some state
  return baseSearcher->selectState();
}

void MergingSearcher::update(ExecutionState *current,
                             const std::vector<ExecutionState *> &addedStates,
                             const std::vector<ExecutionState *> &removedStates) {
  // We have to check if the current execution state was just deleted, as to
  // not confuse the nurs searchers
  if (std::find(pausedStates.begin(), pausedStates.end(), current) == pausedStates.end()) {
    baseSearcher->update(current, addedStates, removedStates);
  }
}

bool MergingSearcher::empty() {
  return baseSearcher->empty();
}

void MergingSearcher::printName(llvm::raw_ostream &os) {
  os << "MergingSearcher\n";
}


///

BatchingSearcher::BatchingSearcher(Searcher *baseSearcher,
                                   time::Span timeBudget,
                                   unsigned instructionBudget)
    : baseSearcher{baseSearcher}, timeBudgetEnabled{timeBudget},
      timeBudget{timeBudget}, instructionBudgetEnabled{instructionBudget > 0},
      instructionBudget{instructionBudget} {};

bool BatchingSearcher::withinTimeBudget() const {
  return !timeBudgetEnabled ||
         (time::getWallTime() - lastStartTime) <= timeBudget;
}

bool BatchingSearcher::withinInstructionBudget() const {
  return !instructionBudgetEnabled ||
         (stats::instructions - lastStartInstructions) <= instructionBudget;
}

ExecutionState &BatchingSearcher::selectState() {
  if (lastState && withinTimeBudget() && withinInstructionBudget()) {
    // return same state for as long as possible
    return *lastState;
  }

  // ensure time budget is larger than time between two calls (for same state)
  if (lastState && timeBudgetEnabled) {
    time::Span delta = time::getWallTime() - lastStartTime;
    auto t = timeBudget;
    t *= 1.1;
    if (delta > t) {
      klee_message("increased time budget from %f to %f\n",
                   timeBudget.toSeconds(), delta.toSeconds());
      timeBudget = delta;
    }
  }

  // pick a new state
  lastState = &baseSearcher->selectState();
  if (timeBudgetEnabled) {
    lastStartTime = time::getWallTime();
  }
  if (instructionBudgetEnabled) {
    lastStartInstructions = stats::instructions;
  }
  return *lastState;
}

void BatchingSearcher::update(ExecutionState *current,
                              const std::vector<ExecutionState *> &addedStates,
                              const std::vector<ExecutionState *> &removedStates) {
  // drop memoized state if it is marked for deletion
  if (std::find(removedStates.begin(), removedStates.end(), lastState) != removedStates.end())
    lastState = nullptr;
  // update underlying searcher
  baseSearcher->update(current, addedStates, removedStates);
}

bool BatchingSearcher::empty() {
  return baseSearcher->empty();
}

void BatchingSearcher::printName(llvm::raw_ostream &os) {
  os << "<BatchingSearcher> timeBudget: " << timeBudget
     << ", instructionBudget: " << instructionBudget
     << ", baseSearcher:\n";
  baseSearcher->printName(os);
  os << "</BatchingSearcher>\n";
}


///

IterativeDeepeningTimeSearcher::IterativeDeepeningTimeSearcher(Searcher *baseSearcher)
  : baseSearcher{baseSearcher} {};

ExecutionState &IterativeDeepeningTimeSearcher::selectState() {
  ExecutionState &res = baseSearcher->selectState();
  startTime = time::getWallTime();
  return res;
}

void IterativeDeepeningTimeSearcher::update(ExecutionState *current,
                                            const std::vector<ExecutionState *> &addedStates,
                                            const std::vector<ExecutionState *> &removedStates) {

  const auto elapsed = time::getWallTime() - startTime;

  // update underlying searcher (filter paused states unknown to underlying searcher)
  if (!removedStates.empty()) {
    std::vector<ExecutionState *> alt = removedStates;
    for (const auto state : removedStates) {
      auto it = pausedStates.find(state);
      if (it != pausedStates.end()) {
        pausedStates.erase(it);
        alt.erase(std::remove(alt.begin(), alt.end(), state), alt.end());
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }

  // update current: pause if time exceeded
  if (current &&
      std::find(removedStates.begin(), removedStates.end(), current) == removedStates.end() &&
      elapsed > time) {
    pausedStates.insert(current);
    baseSearcher->update(nullptr, {}, {current});
  }

  // no states left in underlying searcher: fill with paused states
  if (baseSearcher->empty()) {
    time *= 2U;
    klee_message("increased time budget to %f\n", time.toSeconds());
    std::vector<ExecutionState *> ps(pausedStates.begin(), pausedStates.end());
    baseSearcher->update(nullptr, ps, std::vector<ExecutionState *>());
    pausedStates.clear();
  }
}

bool IterativeDeepeningTimeSearcher::empty() {
  return baseSearcher->empty() && pausedStates.empty();
}

void IterativeDeepeningTimeSearcher::printName(llvm::raw_ostream &os) {
  os << "IterativeDeepeningTimeSearcher\n";
}


///

InterleavedSearcher::InterleavedSearcher(const std::vector<Searcher*> &_searchers) {
  searchers.reserve(_searchers.size());
  for (auto searcher : _searchers)
    searchers.emplace_back(searcher);
}

ExecutionState &InterleavedSearcher::selectState() {
  Searcher *s = searchers[--index].get();
  if (index == 0) index = searchers.size();
  return s->selectState();
}

void InterleavedSearcher::update(ExecutionState *current,
                                 const std::vector<ExecutionState *> &addedStates,
                                 const std::vector<ExecutionState *> &removedStates) {

  // update underlying searchers
  for (auto &searcher : searchers)
    searcher->update(current, addedStates, removedStates);
}

bool InterleavedSearcher::empty() {
  return searchers[0]->empty();
}

void InterleavedSearcher::printName(llvm::raw_ostream &os) {
  os << "<InterleavedSearcher> containing " << searchers.size() << " searchers:\n";
  for (const auto &searcher : searchers)
    searcher->printName(os);
  os << "</InterleavedSearcher>\n";
}












































// /*====================================================================================================================*/

// //update this searcher so that it also takes a filename as an input
// //this is necessary to get the target line number
// SDSESearcher::SDSESearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor)
//     :  target{target}, targetFile{targetFile}, executionTree{executionTree}, idBitMask{static_cast<uint8_t>(executionTree ? executionTree->getNextId() : 0)},
//         bbToIndex(), icfg(*kmodule.module.get(), bbToIndex), executor(executor), kmodule{kmodule}
//       {
//   assert(executionTree);
//   // std::cout << "SDSESearcher created" << std::endl;
//   llvm::Module *module = kmodule.module.get();
  


//   icfg.generateIGraph(i_cfg);

  
//   //generate in memory CFG, not used anymore, keeping it here to keep it real
//   for(llvm::Function &F : *module) {
//     for(llvm::BasicBlock &BB : F) {
//       for(llvm::succ_iterator SI = succ_begin(&BB), E = succ_end(&BB); SI != E; ++SI) {
//         llvm::BasicBlock *SuccBB = *SI;
//         Mycfg.addEdge(&BB, SuccBB);
//       }
//     }
//   }

//   bool debug =false;
//   if(debug){
//     generateCFG();
//   }


// }



// //change to leave out the mycfg stuff to work with icfg instead
// //should return an int with the length of the shortest path
// //this can than be used to select the state with the shortest path left to the target
// int SDSESearcher::computeShortestPath(unsigned int t, llvm::BasicBlock *currnode, std::unordered_map<llvm::BasicBlock*, int> bbToIndex) {
//         std::unordered_map<ExecutionTreeNode*, int> distances;
//         std::unordered_map<ExecutionTreeNode*, ExecutionTreeNode*> predecessors;
        
        
        
        
        
        
//         llvm::raw_ostream &os = llvm::errs();
        
//         llvm::BasicBlock *target = nullptr;
  


//         //where do i need to go
//         for (const auto &nodePair: icfg.blockToICFGNodes){
//           llvm::BasicBlock *BB = nodePair.first;

//           for (auto &inst: *BB){
//             if(llvm::DILocation *loc = inst.getDebugLoc()){
//               auto line = loc->getLine();
//               // os <<"Instruction: "<<inst << "\n";
//               // os <<"Source: "<<loc->getFilename().str() << " Line: " << line << "\n";
//               if(loc->getFilename().str() == targetFile && line == t){
//                 // os << "Target line found" << "\n";
//                 target = BB;
//                 break;
//               }
//             }
//           }
//           if (target!=nullptr) break;
//         }

//         if (!target){
//           // os << "Target not found" << "\n";
//           return -1;
//         }


//         igraph_integer_t from = bbToIndex[currnode];
//         igraph_integer_t to = bbToIndex[target];



//         assert(target && "Target not found");
//         // as i have access to the igraph version of the CFG, i can use the igraph library to compute the shortest path
//         // required parameters: next node(s), target node, cfg

//         igraph_vector_t shortestpath;
//         igraph_vector_init(&shortestpath, 0);

//         igraph_get_shortest_path_dijkstra(&i_cfg,&shortestpath, NULL, from, to, NULL,  IGRAPH_OUT);

//         // if (igraph_vector_size(&shortestpath) > 0) {
//         //   os << "Shortest path from node " << from << " to node " << to << " is:\n";
//         //   for (int i = 0; i < igraph_vector_size(&shortestpath); ++i) {
//         //       os << VECTOR(shortestpath)[i] << " ";
//         //   }
//         //   os << "\n";
//         // } else {
//         //   os << "No path found from node " << from << " to node " << to << "\n";
//         // }

//         if(from == to){
//           os<<"path completed"<<"\n";
//           foundTarget=true;
//         } 

//         if (igraph_vector_size(&shortestpath) > 0) {
//           return igraph_vector_size(&shortestpath);
//         } else {
//           return -1;
//         }
//         // assert(igraph_vector_size(&shortestpath) > 0 && "No path found");

      




//       // return igraph_vector_size(&shortestpath);
//     }

// void SDSESearcher::printName(llvm::raw_ostream &os) {
//   os << "SDSESearcher\n";
// }

// bool SDSESearcher::empty() {
//   return !IS_OUR_NODE_VALID(executionTree->root);
// }


// void SDSESearcher::update(ExecutionState *current,
//                                 const std::vector<ExecutionState *> &addedStates,
//                                 const std::vector<ExecutionState *> &removedStates) {


//   if(foundTarget){
//     executor.prepareForEarlyExit();
//     executor.setHaltExecution(true);
//     igraph_destroy(&i_cfg);
//     return;
//   }

//   states.insert(states.end(), addedStates.begin(), addedStates.end());



//   //remove states
//   for (const auto state : removedStates) {
//     auto it = std::find(states.begin(), states.end(), state);
//     assert(it != states.end() && "invalid state removed");
//     states.erase(it);
//   }

// }

// void ICFG::dumpToDOTFile(llvm::StringRef filename) const {
//     std::error_code code;
//     llvm::raw_fd_ostream outputFile(filename, code);
//     assert(code.value() == 0);

//     outputFile << "digraph \"ICFG\" {\n";

//     // we want to draw boundary boxes around functions in the ICFG
//     // first figure out which functions exist 
//     llvm::DenseSet<llvm::Function*> funcs;
//     for (auto& [bb, icfgnodes] : blockToICFGNodes) {
//         funcs.insert(bb->getParent());
//     }

//     // first dump all the intra-function nodes
//     // i'm using the unique in-memory node address as the label here
//     // dump them all as part of a subgraph per-function
//     size_t numNodes = 0;
//     for (auto func : funcs) {
//         outputFile << llvm::formatv("\tsubgraph cluster_{0} {\n", func->getName());
//         outputFile << llvm::formatv("\t\tlabel = \"{0}\";\n", func->getName());
//         for (auto& bb : *func) {
//             auto& icfgNodes = blockToICFGNodes.find(&bb)->getSecond();
//             for (auto& icfgnode : icfgNodes) {
//                 auto line = llvm::formatv("\t\tnode{0} [shape=record,style=\"filled\",color=\"black\",penwidth=1,fillcolor=\"grey\",label=\"#block{0}\"];", (void*) icfgnode.get()).str();
//                 outputFile << line << "\n";
//                 numNodes++;
//             }
//         }
//         outputFile << "\tcolor=blue;\n";
//         outputFile << "\t}\n";
//     }

//     // then dump the dummy nodes for the library calls
//     for (auto& dummyLibFuncNode : externalFuncICFGNodes) {
//         auto line = llvm::formatv("\tnode{0} [shape=record,style=\"filled\",color=\"black\",penwidth=1,fillcolor=\"darkgrey\",label=\"{1}\"];", (void*) dummyLibFuncNode.get(), dummyLibFuncNode->enclosingFunction->getName()).str();
//         outputFile << line << "\n";
//         numNodes++;
//     }

//     // then dump all the edges
//     size_t numEdges = 0;
//     for (auto& [src, dests] : icfgEdges) {
//         for (auto dest : dests) {
//             auto line = llvm::formatv("\tnode{0} -> node{1} [penwidth=1];", (void*)src, (void*)dest).str();
//             outputFile << line << "\n";
//             numEdges++;
//         }
//     }

//     outputFile << "}\n";
//     outputFile.flush();
//     outputFile.close();

//     llvm::errs() << llvm::formatv("Dumped DOT graph with {0} nodes and {1} edges to {2}\n", numNodes, numEdges, filename);
// }




// void SDSESearcher::generateCFG() {

//   FILE *f = fopen("igraph_cfg.dot", "w");
//   if (f == NULL) {
//       llvm::errs() << "Error: Could not open file " << "igraph_cfg.dot" << " for writing.\n";
//       return;
//     }
  
  
//     igraph_write_graph_dot(&i_cfg, f);
//     fclose(f);
  
// }

// void ICFG::generateIGraph(igraph_t& i_graph) {
//     // Map to store ICFGNode to vertex index mapping
//     std::unordered_map<ICFGNode*, int> nodeToIndex;
//     int index = 0;

//     // Count the total number of nodes
//     int totalNodes = 0;
//     for (const auto& entry : blockToICFGNodes) {
//         totalNodes += entry.second.size();
//     }
//     // Initialize the igraph with the correct number of vertices
//     igraph_empty(&i_graph, totalNodes, IGRAPH_DIRECTED);
//     // Assign each ICFGNode a unique vertex index
//     for (const auto& entry : blockToICFGNodes) {
//         for (const auto& icfgNode : entry.second) {
//             nodeToIndex[icfgNode.get()] = index++;
//         }
//     }

//     // Add edges to the igraph
//     for (const auto& [fromNode, successors] : icfgEdges) {
//         int fromIndex = nodeToIndex[fromNode];
//         for (ICFGNode* toNode : successors) {
//             int toIndex = nodeToIndex[toNode];
//             igraph_add_edge(&i_graph, fromIndex, toIndex);
//         }
//     }
// }



// ICFGNode* ICFG::getICFGNodeStartingWith(llvm::Instruction* startingInst) const {
//     auto& retblockICFGNodes = blockToICFGNodes.find(startingInst->getParent())->getSecond();
//     for (auto& node : retblockICFGNodes) {
//         for (auto inst : node->insts) {
//             if (inst == startingInst)
//                 return node.get();
//         }
//     }
//     assert(!"Can't find ICFG node starting with `inst`!");
// };

// ICFG::ICFG(llvm::Module& module, std::unordered_map<llvm::BasicBlock *, int> &bbToIndex) {
//   int index = 0;
//  // first just build the ICFG nodes for all blocks, split on known calls
//     for (auto& func : module) {
//         for (auto& bb : func) {
//             auto& blockNodes = blockToICFGNodes[&bb];
//             blockNodes.emplace_back(std::make_unique<ICFGNode>(&func, &bb));

//             bbToIndex[&bb] = index++;

//             auto currentNode = [&] () -> Node* {
//                 return blockNodes.back().get();
//             };

//             for (auto& inst : bb) {
//                 currentNode()->insts.push_back(&inst);
//                 if (auto call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
//                     auto callee = call->getCalledFunction();
//                     if (callee) { // this is a direct call
//                         assert(!interproceduralCallEdges.count(call)); // we should only visit each call once
//                         interproceduralCallEdges[call] = callee;
//                         blockNodes.emplace_back(std::make_unique<Node>(&func, &bb));
//                     }
//                 }
//             }

//             if (currentNode()->insts.empty())
//                 blockNodes.pop_back();
//             assert(!blockNodes.empty());
//         }
//     }

//     // then link them all based on intraprocedural & interprocedural edges
//     // initialize the edges
//     for (auto& [bb, icfgnodes] : blockToICFGNodes) {
//         for (auto& icfgNode : icfgnodes) {
//             auto edgeIt = interproceduralCallEdges.find(icfgNode->getTerminator());
//             if (edgeIt != interproceduralCallEdges.end()) {
//                 // this edge is interprocedural

//                 // figure out the return site in the caller
//                 auto callerReturnSiteICFGNode = [&] () -> ICFGNode* {
//                     ///FIXME: we do not model the exceptional flow here.
//                     auto callerReturnSite = [&] (llvm::CallBase* call) -> llvm::Instruction* {
//                         if (auto invoke = llvm::dyn_cast<llvm::InvokeInst>(call))
//                             return &invoke->getNormalDest()->front();
//                         auto next = call->getNextNode();
//                         assert(next && "if it isnt an invoke, it cant be a terminator!");
//                         return next;
//                     } (llvm::cast<llvm::CallBase>(icfgNode->getTerminator()));
//                     assert(callerReturnSite);
//                     // for invokes, the return BB may not be the same as the caller BB
//                     return getICFGNodeStartingWith(callerReturnSite);
//                 } ();

//                 auto callee = edgeIt->getSecond();
//                 assert(callee);
//                 ///TODO: it's annoying that the ICFG will contain infeasible flow from one callsite to all the others, through the callee
//                 // i wish there was a way to avoid this, without context cloning the function (which has its own set of problems)
//                 // link this icfgnode to the entry icfgnode of the callee
//                 if (callee->isDeclaration()) {
//                     auto calleeICFGNode = externalFuncICFGNodes.emplace_back(std::make_unique<ICFGNode>(callee)).get();
//                     icfgEdges[icfgNode.get()].insert(calleeICFGNode);
//                     icfgEdges[calleeICFGNode].insert(callerReturnSiteICFGNode);
//                 } else {
//                     auto entryBlock = &callee->getEntryBlock();
//                     auto entryICFGNode = blockToICFGNodes.find(entryBlock)->getSecond().front().get();
//                     assert(entryICFGNode->insts.front() == &entryBlock->front());
//                     icfgEdges[icfgNode.get()].insert(entryICFGNode);

//                     // link all normal return paths in the callee back to the normal return site in the caller
//                     ///FIXME: we ignore exceptional flow here
//                     for (auto& calleeBB : *callee) {
//                         if (auto ret = llvm::dyn_cast<llvm::ReturnInst>(calleeBB.getTerminator())) {
//                             auto retICFGNode = blockToICFGNodes.find(&calleeBB)->getSecond().back().get();
//                             assert(retICFGNode->insts.back() == ret);
//                             icfgEdges[retICFGNode].insert(callerReturnSiteICFGNode);
//                         }
//                     }
//                 }
//             } else {
//                 // all this node's successors are intraprocedural
//                 assert(icfgNode->getTerminator() == bb->getTerminator() && "this edge should always be intraprocedural!");
//                 // this is inter-block flow
//                 for (auto successor : llvm::successors(bb)) {
//                     auto succICFGNode = blockToICFGNodes.find(successor)->getSecond().front().get();
//                     assert(succICFGNode->insts.front() == &successor->front());
//                     icfgEdges[icfgNode.get()].insert(succICFGNode);
//                 }
//             }
//         }
//     }

// }






// ExecutionState &SDSESearcher::selectState() {
//   //need something to calculate said distance (graph needed)
//   //find a way to translate the targetline to a target node
//   //how does llvm get compute the CFG?

//   //use path for further logic


  
//   //check what state/line we are at
//   //use ICFG to check the distance to the target line
//   //we don't take into account the library calls

//   llvm::raw_ostream &os = llvm::outs();




//   ICFGNode *currentNode = nullptr;

//   bool nodeFound = false;

//   //where am i right now
//   // find out where the state is right now
//   for (auto es : states) {
//     auto pc = es->prevPC;
//     auto source = pc->info->file;
//     // os << "Source: " << source << "\n";
//     // if(source.find("libc") != std::string::npos || source.find("POSIX") != std::string::npos || source.find("klee") != std::string::npos){
//     //   os << "Source is a lib file \n";
//     //   continue;
//     // }
//     // else{
//     //   correct_function = true;
//     // }
//     if (icfg.blockToICFGNodes.count(pc->inst->getParent())) {
//         // os << "Found a node in the CFG corresponding to the current BB\n";
//         auto& icfgNodes =icfg.blockToICFGNodes[pc->inst->getParent()];
//         if(!icfgNodes.empty()){
//           currentNode = icfgNodes.front().get();
//           nodeFound=true;
//           // os << "Current node: " << currentNode << "\n";
//         }
//     }
//   }
//     //compare next options wrt distance to the target node, choose the one with the smallest distance
//     //if the distance is the same, choose the one with the smallest number of instructions
//     //the computeShortestPath retuns the length of the shortest path
//     //then we select the state with the shortest path left to the target


//     ///ISSUE: this is not correct, i think, right now im checking the successors of the current node
//     ///These are not yet states that can be selected from the engine's point of view
//     ///SOLUTION: if this really is the case, i need to iterate over the states available in states,
//     ///and then check the distance to the target line from those states.
//   int shortestPath = std::numeric_limits<int>::max();
//   ExecutionState *nextState_test = nullptr;
//   if(nodeFound){
//     for (auto es:states){
//       auto pc = es->pc;
//       int temp = computeShortestPath(this->getTarget(), pc->inst->getParent(), bbToIndex);
//       if (temp == -1){
//         return *states.back();
//       }
//       if (temp < shortestPath){
//         shortestPath = temp;
//         nextState_test = es;
//       }
//     }
//     return *nextState_test;
//   }


//   // if no node is found, just return the last state
//   return *states.back();
// }















// ASTARSearcher::ASTARSearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor)
//     :  target{target}, targetFile{targetFile}, executionTree{executionTree}, idBitMask{static_cast<uint8_t>(executionTree ? executionTree->getNextId() : 0)},
//         bbToIndex(), icfg(*kmodule.module.get(), bbToIndex),  distanceToTarget(), bbReoccurence(), executor(executor) ,kmodule{kmodule}
//       {
//   assert(executionTree);
//   llvm::Module *module = kmodule.module.get();



//   //this needs to be set when calling KLEE, as a cmdline argument
//   //don't know how to do it, so ill just hardcode it for now
//   ///TODO: make this a cmdline argument



//   icfg.generateIGraph(i_cfg);

  
  


//   //generate in memory CFG, not used anymore, keeping it here to keep it real
//   for(llvm::Function &F : *module) {
//     for(llvm::BasicBlock &BB : F) {
//       for(llvm::succ_iterator SI = succ_begin(&BB), E = succ_end(&BB); SI != E; ++SI) {
//         llvm::BasicBlock *SuccBB = *SI;
//         Mycfg.addEdge(&BB, SuccBB);
//       }
//     }
//   }

//   // //convert the in memory cfg to an igraph one
//   // igraph_empty(&i_cfg, Mycfg.Nodes.size(), IGRAPH_DIRECTED);

  
  

//   // //i_cfg is not correct... 
//   // int index = 0;

//   // for (const auto &nodePair : Mycfg.Nodes) {
//   //     bbToIndex[nodePair.second->BB] = index++;
//   // }
//   // for (const auto &nodePair : Mycfg.Nodes) {
//   //     llvm::BasicBlock *BB = nodePair.second->BB;
//   //     int from = bbToIndex[BB];
//   //     for (auto succ = llvm::succ_begin(BB); succ != llvm::succ_end(BB); ++succ) {
//   //         llvm::BasicBlock *succBB = *succ;
//   //         int to = bbToIndex[succBB];
//   //         igraph_add_edge(&i_cfg, from, to);
//   //     }
//   // }




//   bool debug =false;
//   if(debug){
//     generateCFG();
//   }


// }






// ExecutionState &ASTARSearcher::selectState() {
//   //need something to calculate said distance (graph needed)
//   //find a way to translate the targetline to a target node
//   //how does llvm get compute the CFG?

//   //use path for further logic


  
//   //check what state/line we are at
//   //use ICFG to check the distance to the target line
//   //we don't take into account the library calls

//   llvm::raw_ostream &os = llvm::outs();




//   ICFGNode *currentNode = nullptr;

//   bool nodeFound = false;

//   //where am i right now
//   // find out where the state is right now
//   for (auto es : states) {
//     auto pc = es->prevPC;
//     auto source = pc->info->file;
//     // os << "Source: " << source << "\n";
//     // if(source.find("libc") != std::string::npos || source.find("POSIX") != std::string::npos || source.find("klee") != std::string::npos){
//     //   os << "Source is a lib file \n";
//     //   continue;
//     // }
//     // else{
//     //   correct_function = true;
//     // }
//     if (icfg.blockToICFGNodes.count(pc->inst->getParent())) {
//         // os << "Found a node in the CFG corresponding to the current BB\n";
//         auto& icfgNodes =icfg.blockToICFGNodes[pc->inst->getParent()];
//         if(!icfgNodes.empty()){
//           currentNode = icfgNodes.front().get();
//           nodeFound=true;
//           // os << "Current node: " << currentNode << "\n";
//         }
//     }
//   }
//     //compare next options wrt distance to the target node, choose the one with the smallest distance
//     //if the distance is the same, choose the one with the smallest number of instructions
//     //the computeShortestPath retuns the length of the shortest path
//     //then we select the state with the shortest path left to the target


//     ///ISSUE: this is not correct, i think, right now im checking the successors of the current node
//     ///These are not yet states that can be selected from the engine's point of view
//     ///SOLUTION: if this really is the case, i need to iterate over the states available in states,
//     ///and then check the distance to the target line from those states.
//   int shortestPath = std::numeric_limits<int>::max();
//   ExecutionState *nextState_test = nullptr;
//   if(nodeFound){
//     for (auto es:states){
//       int temp = computeASTARPath(this->getTarget(), es, bbToIndex);
//       if (temp == -1){
//         return *states.back();
//       }
//       if (temp < shortestPath){
//         shortestPath = temp;
//         nextState_test = es;
//       }
//     }
//     return *nextState_test;
//   }
//   return *states.back();
// }






// void ASTARSearcher::printName(llvm::raw_ostream &os) {
//   os << "ASTARSearcher\n";
// }

// bool ASTARSearcher::empty() {
//   return !IS_OUR_NODE_VALID(executionTree->root);
// }


// void ASTARSearcher::update(ExecutionState *current,
//                                 const std::vector<ExecutionState *> &addedStates,
//                                 const std::vector<ExecutionState *> &removedStates) {



//   // early exit if the target has been found
//   if(foundTarget){
//     executor.prepareForEarlyExit();
//     executor.setHaltExecution(true);
//     igraph_destroy(&i_cfg);
//     return;
//   }
//   states.insert(states.end(), addedStates.begin(), addedStates.end());




//   //remove states
//   for (const auto state : removedStates) {
//     auto it = std::find(states.begin(), states.end(), state);
//     assert(it != states.end() && "invalid state removed");
//     states.erase(it);
//   }

// }

// void ASTARSearcher::generateCFG() {

//   FILE *f = fopen("igraph_cfg.dot", "w");
//   if (f == NULL) {
//       llvm::errs() << "Error: Could not open file " << "igraph_cfg.dot" << " for writing.\n";
//       return;
//     }
  
  
//     igraph_write_graph_dot(&i_cfg, f);
//     fclose(f);
  
// }




// int ASTARSearcher::computeASTARPath(unsigned int t, klee::ExecutionState *currstate, std::unordered_map<llvm::BasicBlock*, int> bbToIndex) {
//         std::unordered_map<ExecutionTreeNode*, int> distances;
//         std::unordered_map<ExecutionTreeNode*, ExecutionTreeNode*> predecessors;
        
        
        
        
        
//         int Theta = 3; //As per the paper by De Castro Pinto et al. (2023), so hardcoded for now
//         uint32_t lambda = 0; 
//         llvm::raw_ostream &os = llvm::errs();
        
//         llvm::BasicBlock *target = nullptr;
//         std::string currFile = "";  


//         //where do i need to go
//         for (const auto &nodePair: icfg.blockToICFGNodes){
//           llvm::BasicBlock *BB = nodePair.first;

//           for (auto &inst: *BB){
//             if(llvm::DILocation *loc = inst.getDebugLoc()){
//               auto line = loc->getLine();

//               currFile = loc->getFilename().str();
//               if(loc->getFilename().str() == targetFile && line == t){
//                 // os << "Target line found" << "\n";
//                 target = BB;
//                 break;
//               }
//             }
//           }
//           if (target!=nullptr) break;
//         }

//         if (!target){
//           // os << "Target not found" << "\n";
//           return -1;
//         }

//         llvm::BasicBlock *currnode = currstate->pc->inst->getParent();
//         igraph_integer_t from = bbToIndex[currnode];
//         igraph_integer_t to = bbToIndex[target];    

//         uint32_t depth =  currstate->depth;
//         bbReoccurence[currnode] = bbReoccurence[currnode] + 1;



//         assert(target && "Target not found");
//         // as i have access to the igraph version of the CFG, i can use the igraph library to compute the shortest path
//         // required parameters: next node(s), target node, cfg

//         igraph_vector_t shortestpath;
//         igraph_vector_init(&shortestpath, 0);

       
//         ///in the ASTAR algorithm, we make use of the depth, the reoccurrence and the length of the path to the target.
       
       
//         igraph_get_shortest_path_dijkstra(&i_cfg,&shortestpath, NULL, from, to, NULL,  IGRAPH_OUT);
//         distanceToTarget[from] = igraph_vector_size(&shortestpath);



//         if (bbReoccurence[currnode] > Theta){
//           lambda = std::log10(1+bbReoccurence[currnode]-Theta);
//         }




//         if(from == to){
//           os<<"path completed"<<"\n";
//           foundTarget=true;
//         } 

//         if (igraph_vector_size(&shortestpath) > 0) {
//           return depth*lambda + distanceToTarget[from];
//         } else {
//           return -1;
//         }
//         // assert(igraph_vector_size(&shortestpath) > 0 && "No path found");

//       // return igraph_vector_size(&shortestpath);
// }

