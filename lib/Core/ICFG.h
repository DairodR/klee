#ifndef ICFG_H
#define ICFG_H

#include <llvm-13/llvm/IR/InstrTypes.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <memory>
#include <igraph/igraph.h>

namespace llvm {
    class BasicBlock;
    class Instruction;
    class Function;
    class Module;
    class StringRef;
}

namespace klee {

class ICFGNode {
public:
    llvm::Function* enclosingFunction;
    llvm::BasicBlock* bb;
    std::vector<llvm::Instruction*> insts;

    ICFGNode(llvm::Function* enclosingFunction, llvm::BasicBlock* bb = nullptr);
    ICFGNode(llvm::Function* enclosingFunction); // Constructor for external function nodes

    llvm::Instruction* getTerminator() const;
};

class ICFG {
public:
    using Node = ICFGNode;

    std::unordered_map<llvm::BasicBlock*, std::vector<std::unique_ptr<ICFGNode>>> blockToICFGNodes;
    std::unordered_map<ICFGNode*, std::unordered_set<ICFGNode*>> icfgEdges;
    std::vector<std::unique_ptr<ICFGNode>> externalFuncICFGNodes;
    igraph_t i_cfg;

    ICFG(llvm::Module& module, std::unordered_map<llvm::BasicBlock *, int> &bbToIndex);
    ~ICFG(); // Destructor to handle igraph_destroy

    ICFGNode* getICFGNodeStartingWith(llvm::Instruction* startingInst) const;
    void dumpToDOTFile(llvm::StringRef filename) const;
    void generateIGraph(igraph_t& i_graph);

private:
    std::unordered_map<llvm::CallBase*, llvm::Function*> interproceduralCallEdges;
};

} // namespace klee

#endif // ICFG_H