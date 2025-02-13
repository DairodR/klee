#ifndef ASTARSEARCHER_H
#define ASTARSEARCHER_H

#include "Searcher.h"
#include "ICFG.h" // Include ICFG header as ASTARSearcher uses ICFG
#include "ExecutionTree.h" // Include ExecutionTree header as ASTARSearcher uses InMemoryExecutionTree
#include "Executor.h" // Include Executor header as ASTARSearcher uses Executor

#include <string>
#include <unordered_map>
#include <limits>

namespace llvm {
    class raw_ostream;
    class BasicBlock;
    class Module;
}

namespace klee {
    class KModule;
    class ExecutionState;
    class InMemoryExecutionTree;
    class Executor;

class ASTARSearcher : public Searcher {
private:
    InMemoryExecutionTree *executionTree;
    uint8_t idBitMask;
    std::vector<ExecutionState*> states;

    int target;
    std::string targetFile;
    std::unordered_map<llvm::BasicBlock*, int> bbToIndex;
    ICFG icfg;
    igraph_t i_cfg;
    class Executor &executor; // Executor is a member
    KModule &kmodule;
    bool foundTarget = false;
    std::unordered_map<int, int> distanceToTarget; //map vertex id to distance
    std::unordered_map<llvm::BasicBlock*, int> bbReoccurence; //map bb to reoccurence count

    int computeASTARPath(unsigned int t, ExecutionState *currstate, std::unordered_map<llvm::BasicBlock*, int> bbToIndex);
    void generateCFG();


public:
    ASTARSearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor);
    ~ASTARSearcher() override {}; // Ensure proper destruction if needed

    ExecutionState &selectState() override;
    void update(ExecutionState *current,
                const std::vector<ExecutionState *> &addedStates,
                const std::vector<ExecutionState *> &removedStates) override;
    bool empty() override;
    void printName(llvm::raw_ostream &os) override;

    unsigned int getTarget() const { return target; }
};

} // namespace klee

#endif // ASTARSEARCHER_H