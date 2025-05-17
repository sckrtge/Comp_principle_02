#include"front/semantic.h"

#include<cassert>

using ir::Instruction;
using ir::Function;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); 
#define ANALYSIS(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); analysis##type(node, buffer);
#define COPY_EXP_NODE(from, to) to->is_computable = from->is_computable; to->v = from->v; to->t = from->t;

map<std::string,ir::Function*>* frontend::get_lib_funcs() {
    static map<std::string,ir::Function*> lib_funcs = {
        {"getint", new Function("getint", Type::Int)},
        {"getch", new Function("getch", Type::Int)},
        {"getfloat", new Function("getfloat", Type::Float)},
        {"getarray", new Function("getarray", {Operand("arr", Type::IntPtr)}, Type::Int)},
        {"getfarray", new Function("getfarray", {Operand("arr", Type::FloatPtr)}, Type::Int)},
        {"putint", new Function("putint", {Operand("i", Type::Int)}, Type::null)},
        {"putch", new Function("putch", {Operand("i", Type::Int)}, Type::null)},
        {"putfloat", new Function("putfloat", {Operand("f", Type::Float)}, Type::null)},
        {"putarray", new Function("putarray", {Operand("n", Type::Int), Operand("arr", Type::IntPtr)}, Type::null)},
        {"putfarray", new Function("putfarray", {Operand("n", Type::Int), Operand("arr", Type::FloatPtr)}, Type::null)},
    };
    return &lib_funcs;
}

void frontend::SymbolTable::add_scope(Block* node) {
    ScopeInfo scope_node;
    scope_node.cnt = ++scope_cnt;
    scope_node.name = 'b';
    scope_stack.push_back(scope_node);
}
void frontend::SymbolTable::exit_scope() {
    scope_stack.pop_back();
}

string frontend::SymbolTable::get_scoped_name(string id) const {
    auto scope_node = *scope_stack.rbegin();
    return id + "_in_" + std::to_string(scope_node.cnt);
}

Operand frontend::SymbolTable::get_operand(string id) const {
    for(int i=scope_stack.size()-1;i>=0;--i) {
        auto table = scope_stack[i].table;
        if(table.find(id) != table.end()) {
            return table[id].operand;
        }
    }
}

frontend::STE frontend::SymbolTable::get_ste(string id) const {
    for(int i=scope_stack.size()-1;i>=0;--i) {
        auto table = scope_stack[i].table;
        if(table.find(id) != table.end()) {
            return table[id];
        }
    }
}

frontend::Analyzer::Analyzer(): tmp_cnt(0), symbol_table() {
    ScopeInfo global;
    global.cnt = 0;
    global.name = 'g';
    symbol_table.scope_stack.push_back(global);
}

ir::Program frontend::Analyzer::get_ir_program(CompUnit* root) {
    TODO;
}
