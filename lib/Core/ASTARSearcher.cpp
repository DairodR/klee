
#include "ASTARSearcher.h"
#include "klee/Module/KModule.h" // Include KModule header
#include "klee/Support/CompilerWarning.h"
#include <llvm-13/llvm/Support/raw_ostream.h> // Required for raw_ostream &os
#include <llvm-13/llvm/IR/DebugInfoMetadata.h> // Required for DILocation
#include <llvm-13/llvm/IR/Instructions.h> // Required for Instructions
#include <limits> // Required for std::numeric_limits
#include <cmath> // Required for std::cmath

#include <igraph/igraph.h> // Required for igraph functions
#include <igraph/igraph_paths.h> // Required for shortest path functions
#include <cassert> // Required for assert

using namespace klee;
using namespace llvm;


ASTARSearcher::ASTARSearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor)
    :  target{target}, targetFile{targetFile}, executionTree{executionTree}, idBitMask{static_cast<uint8_t>(executionTree ? executionTree->getNextId() : 0)},
        bbToIndex(), icfg(*kmodule.module.get(), bbToIndex),  distanceToTarget(), bbReoccurence(), executor(executor) ,kmodule{kmodule}
      {
  assert(executionTree);
  llvm::Module *module = kmodule.module.get();


  icfg.generateIGraph(i_cfg);


  bool debug =false;
  if(debug){
    generateCFG();
  }
}

// Check if n is a valid pointer and a node belonging to us
#define IS_OUR_NODE_VALID(n)                                                   \
  (((n).getPointer() != nullptr) && (((n).getInt() & idBitMask) != 0))



ExecutionState &ASTARSearcher::selectState() {

  llvm::raw_ostream &os = llvm::outs();

  ICFGNode *currentNode = nullptr;

  bool nodeFound = false;

  for (auto es : states) {
    auto pc = es->prevPC;
    auto source = pc->info->file;

    if (icfg.blockToICFGNodes.count(pc->inst->getParent())) {

        auto& icfgNodes =icfg.blockToICFGNodes[pc->inst->getParent()];
        if(!icfgNodes.empty()){
          currentNode = icfgNodes.front().get();
          nodeFound=true;
        }
    }
  }

  int shortestPath = std::numeric_limits<int>::max();
  ExecutionState *nextState_test = nullptr;
  if(nodeFound){
    for (auto es:states){
      int temp = computeASTARPath(this->getTarget(), es, bbToIndex);
      if (temp == -1){
        return *states.back();
      }
      if (temp < shortestPath){
        shortestPath = temp;
        nextState_test = es;
      }
    }
    return *nextState_test;
  }
  return *states.back();
}


void ASTARSearcher::printName(llvm::raw_ostream &os) {
  os << "ASTARSearcher\n";
}

bool ASTARSearcher::empty() {
  return !IS_OUR_NODE_VALID(executionTree->root);
}


void ASTARSearcher::update(ExecutionState *current,
                                const std::vector<ExecutionState *> &addedStates,
                                const std::vector<ExecutionState *> &removedStates) {


  // early exit if the target has been found
  if(foundTarget){
    executor.prepareForEarlyExit();
    executor.setHaltExecution(true);
    igraph_destroy(&i_cfg);
    return;
  }
  states.insert(states.end(), addedStates.begin(), addedStates.end());


  //remove states
  for (const auto state : removedStates) {
    auto it = std::find(states.begin(), states.end(), state);
    assert(it != states.end() && "invalid state removed");
    states.erase(it);
  }

}

void ASTARSearcher::generateCFG() {

  FILE *f = fopen("igraph_cfg.dot", "w");
  if (f == NULL) {
      llvm::errs() << "Error: Could not open file " << "igraph_cfg.dot" << " for writing.\n";
      return;
    }


    igraph_write_graph_dot(&i_cfg, f);
    fclose(f);

}


int ASTARSearcher::computeASTARPath(unsigned int t, klee::ExecutionState *currstate, std::unordered_map<llvm::BasicBlock*, int> bbToIndex) {
        std::unordered_map<ExecutionTreeNode*, int> distances;
        std::unordered_map<ExecutionTreeNode*, ExecutionTreeNode*> predecessors;

        int Theta = 3; //As per the paper by De Castro Pinto et al. (2023), so hardcoded for now
        uint32_t lambda = 0;
        llvm::raw_ostream &os = llvm::errs();

        llvm::BasicBlock *target = nullptr;
        std::string currFile = "";


        //where do i need to go
        for (const auto &nodePair: icfg.blockToICFGNodes){
          llvm::BasicBlock *BB = nodePair.first;

          for (auto &inst: *BB){
            if(llvm::DILocation *loc = inst.getDebugLoc()){
              auto line = loc->getLine();

              currFile = loc->getFilename().str();
              if(loc->getFilename().str() == targetFile && line == t){
                // os << "Target line found" << "\n";
                target = BB;
                break;
              }
            }
          }
          if (target!=nullptr) break;
        }

        if (!target){
          // os << "Target not found" << "\n";
          return -1;
        }

        llvm::BasicBlock *currnode = currstate->pc->inst->getParent();
        igraph_integer_t from = bbToIndex[currnode];
        igraph_integer_t to = bbToIndex[target];

        uint32_t depth =  currstate->depth;
        bbReoccurence[currnode] = bbReoccurence[currnode] + 1;



        assert(target && "Target not found");


        igraph_vector_t shortestpath;
        igraph_vector_init(&shortestpath, 0);


        ///in the ASTAR algorithm, we make use of the depth, the reoccurrence and the length of the path to the target.


        igraph_get_shortest_path_dijkstra(&i_cfg,&shortestpath, NULL, from, to, NULL,  IGRAPH_OUT);
        distanceToTarget[from] = igraph_vector_size(&shortestpath);



        if (bbReoccurence[currnode] > Theta){
          lambda = std::log10(1+bbReoccurence[currnode]-Theta);
        }


        if(from == to){
          os<<"path completed"<<"\n";
          foundTarget=true;
        }

        if (igraph_vector_size(&shortestpath) > 0) {
          return depth*lambda + distanceToTarget[from];
        } else {
          return -1;
        }
}