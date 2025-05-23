#include "front/semantic.h"
#include <iostream>
#include <cassert>
using ir::Function;
using ir::Instruction;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type *>(root->children[index]);assert(node);

#define ANALYSIS(node, type, index) auto node = dynamic_cast<type *>(root->children[index]);assert(node);analysis##type(node, buffer);

#define COPY_EXP_NODE(from, to) to->is_computable = from->is_computable;to->v = from->v;to->t = from->t;

map<std::string, ir::Function *> *frontend::get_lib_funcs()
{
    static map<std::string, ir::Function *> lib_funcs = {
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

int eval_int(std::string s) {
#if (DEBUG_EXEC_DETAIL)
    std::cout << "\teval_int: " << s << std::endl;
#endif
    if (s.size() >= 2 && (s.substr(0,2)=="0b" || s.substr(0,2)=="0B")) {
        return std::stoi(s.substr(2, s.size()-2), nullptr, 2); 
    }
    else if (s.size() >= 2 && (s.substr(0,2)=="0x" || s.substr(0,2)=="0X")) {
        return std::stoi(s.substr(2, s.size()-2), nullptr, 16);
    }
    else if (s.size() > 1 && s.substr(0,1)=="0") {
        return std::stoi(s.substr(1, s.size()-1), nullptr, 8);
    }
    else {
        return std::stoi(s);
    }
}

void frontend::Analyzer::type_transform(Operand &a, Operand &b, vector<Instruction *> &buffer)
{
    if (a.type == Type::Int)
    {
        if (b.type == Type::Float)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::cvt_i2f));
            a = tmp_op;
        }
        else if (b.type == Type::FloatLiteral)
        {
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::cvt_i2f));
            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::fdef));
            a = tmp_op1;
            b = tmp_op2;
        }
        else if (b.type == Type::IntLiteral)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::def));
            b = tmp_op;
        }
    }
    else if (a.type == Type::IntLiteral)
    {
        if (b.type == Type::Float)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            a = tmp_op;
        }
        else if (b.type == Type::Int)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::def));
            a = tmp_op;
        }
        else if(b.type == Type::IntLiteral)
        {
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(Operand(a.name, Type::IntLiteral), {}, tmp_op1, Operator::def));
            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(Operand(b.name, Type::IntLiteral), {}, tmp_op2, Operator::def));
            a = tmp_op1;
            b = tmp_op2;
        }
        else {
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op1, Operator::fdef));
            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(b.name, Type::FloatLiteral), {}, tmp_op2, Operator::fdef));
            a = tmp_op1;
            b = tmp_op2;
        }
    }
    else if (a.type == Type::Float)
    {
        if (b.type == Type::Int)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::cvt_i2f));
            b = tmp_op;
        }
        else if (b.type == Type::IntLiteral)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(b.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            b = tmp_op;
        }
        else if (b.type == Type::FloatLiteral)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::fdef));
            b = tmp_op;
        }
    }
    else if (a.type == Type::FloatLiteral)
    {
        if (b.type == Type::Int)
        {
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::fdef));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::cvt_i2f));

            a = tmp_op1;
            b = tmp_op2;
        }
        else if (b.type == Type::Float)
        {
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::fdef));
            a = tmp_op;
        }
        else {
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op1, Operator::fdef));
            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
            buffer.push_back(new Instruction(Operand(b.name, Type::FloatLiteral), {}, tmp_op2, Operator::fdef));
            a = tmp_op1;
            b = tmp_op2;
        }
    }
}

void frontend::SymbolTable::add_scope(Block *node)
{
    ScopeInfo scope_info;
    scope_info.cnt = ++scope_cnt;
    scope_stack.push_back(scope_info);
}

void frontend::SymbolTable::exit_scope()
{
    scope_stack.pop_back();
}

string frontend::SymbolTable::get_scoped_name(string id) const
{
    int cnt = scope_stack.back().cnt;
    return id + "_" + std::to_string(cnt);
}

Operand frontend::SymbolTable::get_operand(string id) const
{
    map_str_ste temp;
    for (int i = scope_stack.size() - 1; i >= 0; i--)
    {
        temp = scope_stack[i].table;
        if (temp.find(id) != temp.end())
        {
            return temp[id].operand;
        }
    }
    assert(0 && "get_operand error");
}

frontend::STE frontend::SymbolTable::get_ste(string id) const
{
    map_str_ste temp;
    for (int i = scope_stack.size() - 1; i >= 0; i--)
    {
        temp = scope_stack[i].table;
        if (temp.find(id) != temp.end())
        {
            return temp[id];
        }
    }
    assert(0 && "get_ste error");
}

frontend::Analyzer::Analyzer() : tmp_cnt(0), symbol_table()
{
    symbol_table.scope_stack.push_back({0, "global", map_str_ste()});
}

ir::Program frontend::Analyzer::get_ir_program(CompUnit *root)
{
    ir::Program buffer = ir::Program();
    Function *global_func = new Function("global", Type::null);

    symbol_table.functions.insert({"global", global_func});
    buffer.addFunction(*global_func);
    auto lib_funcs = *get_lib_funcs();
    for (auto it = lib_funcs.begin(); it != lib_funcs.end(); it++)
        symbol_table.functions[it->first] = it->second;

    analysisCompUnit(root, buffer);

    buffer.functions[0].addInst(new ir::Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return}));
    return buffer;
}

void frontend::Analyzer::analysisCompUnit(CompUnit *root, ir::Program &buffer)
{

    if (root->children[0]->type == NodeType::DECL)
    {
        GET_CHILD_PTR(decl, Decl, 0);
        assert(decl);
        analysisDecl(decl, buffer.functions.back().InstVec);
    }
    else if (root->children[0]->type == NodeType::FUNCDEF)
    {

        if (buffer.functions.size() == 1)
        {

            auto global_ir = buffer.functions[0].InstVec;
            for (int i = 0; i < (int)global_ir.size(); i++)
            {
                buffer.globalVal.push_back(ir::GlobalVal(global_ir[i]->des));
            }
        }
        GET_CHILD_PTR(funcdef, FuncDef, 0);
        assert(funcdef);
        auto tmp = ir::Function();
        analysisFuncDef(funcdef, tmp);
        buffer.addFunction(tmp);
    }

    if ((int)(int)root->children.size() == 2)
    {
        ANALYSIS(compunit, CompUnit, 1);
    }
}

void frontend::Analyzer::analysisFuncDef(FuncDef *root, ir::Function &function)
{

    auto tk = dynamic_cast<Term *>(root->children[0]->children[0])->token.type;
    root->t = tk == TokenType::VOIDTK ? Type::null : tk == TokenType::INTTK ? Type::Int
                                                                            : Type::Float;
    root->n = dynamic_cast<Term *>(root->children[1])->token.value;
    function.name = root->n;
    function.returnType = root->t;

    int cnt = ++symbol_table.scope_cnt;
    symbol_table.scope_stack.push_back({cnt, "fp", map_str_ste()});
    symbol_table.functions.insert({root->n, &function});
    curr_function = &function;

    if (function.name == "main")
    {
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::null);
        auto global_callinst = new ir::CallInst(Operand("global", Type::null), vector<Operand>(), tmp);
        curr_function->addInst(global_callinst);
    }

    auto paras = dynamic_cast<FuncFParams *>(root->children[3]);
    if (paras)
    {
        analysisFuncFParams(paras, function);
        analysisBlock(dynamic_cast<Block *>(root->children[5]), function.InstVec);
    }
    else
    {
        analysisBlock(dynamic_cast<Block *>(root->children[4]), function.InstVec);
    }

    if (function.returnType == Type::null)
    {
        auto return_inst = new Instruction({Operand("null", Type::null), {}, {}, Operator::_return});
        curr_function->addInst(return_inst);
    }

    symbol_table.exit_scope();
}

void frontend::Analyzer::analysisDecl(Decl *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::CONSTDECL)
    {
        ANALYSIS(constdecl, ConstDecl, 0);
    }
    else if (root->children[0]->type == NodeType::VARDECL)
    {
        ANALYSIS(vardecl, VarDecl, 0);
    }
}

void frontend::Analyzer::analysisConstDecl(ConstDecl *root, vector<ir::Instruction *> &buffer)
{
    ANALYSIS(btype, BType, 1);
    root->t = btype->t;
    ANALYSIS(constdef1, ConstDef, 2);
    int i = 3;
    while (dynamic_cast<Term *>(root->children[i])->token.type == TokenType::COMMA)
    {
        ANALYSIS(constdef2, ConstDef, i + 1);
        i += 2;
    }
}

void frontend::Analyzer::analysisBType(BType *root, vector<ir::Instruction *> &buffer)
{
    auto tk = dynamic_cast<Term *>(root->children[0])->token.type;
    root->t = tk == TokenType::INTTK ? Type::Int : Type::Float;
}

void frontend::Analyzer::analysisConstDef(ConstDef *root, vector<ir::Instruction *> &buffer)
{
    auto root_type = dynamic_cast<ConstDecl *>(root->parent)->t;
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;
    string new_name = symbol_table.get_scoped_name(id);
    root->arr_name = new_name;

    GET_CHILD_PTR(term, Term, 1);
    if (term->token.type == TokenType::ASSIGN)
    {
        ANALYSIS(constinitval, ConstInitVal, 2);
        Operand des = Operand(new_name, root_type);
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        Operand op1 = Operand(constinitval->v, constinitval->t);
        if (root_type == Type::Float)
        {
            if (constinitval->t == Type::Int)
            {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                op1 = tmp;
            }
            else if (constinitval->t == Type::IntLiteral)
            {
                op1.type = Type::FloatLiteral;
            }
        }
        else
        {
            assert(root_type == Type::Int);
            if (constinitval->t == Type::Float)
            {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                op1 = tmp;
            }
            else if (constinitval->t == Type::FloatLiteral)
            {
                op1.name = std::to_string((int)std::stof(op1.name));
                op1.type = Type::IntLiteral;
            }
        }
        buffer.push_back(new Instruction(op1, Operand(), des, opcode));
        symbol_table.scope_stack.back().table.insert({id, {op1, {}}});
    }
    else if ((int)root->children.size() == 6)
    {
        ANALYSIS(constexp, ConstExp, 2);
        int array_size = std::stoi(constexp->v);
        STE arr_ste;
        arr_ste.dimension.push_back(array_size);
        ir::Type curr_type = root_type;
        if (curr_type == ir::Type::Int)
        {
            curr_type = ir::Type::IntPtr;
        }
        else if (curr_type == ir::Type::Float)
        {
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;
        buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

        GET_CHILD_PTR(constinitval, ConstInitVal, 5);
        if (constinitval->children.size() == 2)
        {
            for (int i = 0; i < array_size; i++)
            {
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
            }
        }
        else
        {
            int cnt = 0;
            for (int i = 1; i < (int)constinitval->children.size() - 1; i += 2, cnt++)
            {
                ConstInitVal *child = dynamic_cast<ConstInitVal *>(constinitval->children[i]);
                ConstExp *constexp = dynamic_cast<ConstExp *>(child->children[0]);
                analysisConstExp(constexp, buffer);
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(constexp->v, Type::IntLiteral), Operator::store}));
            }
        }
    }
    else if ((int)root->children.size() == 9)
    {
        ANALYSIS(constexp1, ConstExp, 2);
        ANALYSIS(constexp2, ConstExp, 5);
        int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);
        STE arr_ste;
        arr_ste.dimension.push_back(std::stoi(constexp1->v));
        arr_ste.dimension.push_back(std::stoi(constexp2->v));
        ir::Type curr_type = root_type;
        if (curr_type == ir::Type::Int)
        {
            curr_type = ir::Type::IntPtr;
        }
        else if (curr_type == ir::Type::Float)
        {
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;
        buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

        GET_CHILD_PTR(constinitval, ConstInitVal, 8);
        if (constinitval->children.size() == 2)
        {
            for (int i = 0; i < array_size; i++)
            {
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
            }
        }
        else
        {
            int cnt = 0;
            for (int i = 1; i < (int)constinitval->children.size() - 1; i += 2, cnt++)
            {
                ConstInitVal *child = dynamic_cast<ConstInitVal *>(constinitval->children[i]);
                ConstExp *constexp = dynamic_cast<ConstExp *>(child->children[0]);
                analysisConstExp(constexp, buffer);
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(constexp->v, Type::IntLiteral), Operator::store}));
            }
        }
    }
}

void frontend::Analyzer::analysisConstInitVal(ConstInitVal *root, vector<ir::Instruction *> &buffer)
{
    if (root->children[0]->type == NodeType::CONSTEXP)
    {
        ANALYSIS(constexp, ConstExp, 0);
        root->v = constexp->v;
        root->t = constexp->t;
    }
}

void frontend::Analyzer::analysisVarDecl(VarDecl *root, vector<ir::Instruction *> &buffer)
{

    ANALYSIS(btype, BType, 0);
    root->t = btype->t;
    ANALYSIS(vardef, VarDef, 1);
    int i = 2;
    while (i < (int)root->children.size() - 1)
    {
        ANALYSIS(vardef, VarDef, i + 1);
        i += 2;
    }
}

void frontend::Analyzer::analysisVarDef(VarDef *root, vector<ir::Instruction *> &buffer)
{
    auto root_type = dynamic_cast<VarDecl *>(root->parent)->t;
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;

    string new_name = symbol_table.get_scoped_name(id);
    if ((int)root->children.size() == 1)
    {
        Operand des = Operand(new_name, root_type);
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        if (root_type == Type::Float)
        {
            buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), des, opcode));
        }
        else
        {
            buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), des, opcode));
        }

        symbol_table.scope_stack.back().table.insert({id, {des, {}}});
    }
    else
    {
        GET_CHILD_PTR(term, Term, 1);
        if (term->token.type == TokenType::ASSIGN)
        {
            ANALYSIS(initval, InitVal, 2);
            Operand des = Operand(new_name, root_type);
            auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
            Operand op1 = Operand(initval->v, initval->t);
            if (root_type == Type::Float)
            {
                if (initval->t == Type::Int)
                {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                    op1 = tmp;
                }
                else if (initval->t == Type::IntLiteral)
                {
                    op1.type = Type::FloatLiteral;
                }
            }
            else
            {
                assert(root_type == Type::Int);
                if (initval->t == Type::Float)
                {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                    op1 = tmp;
                }
                else if (initval->t == Type::FloatLiteral)
                {
                    op1.name = std::to_string((int)std::stof(op1.name));
                    op1.type = Type::IntLiteral;
                }
            }
            buffer.push_back(new Instruction(op1, Operand(), des, opcode));
            symbol_table.scope_stack.back().table.insert({id, {des, {}}});
        }
        else if (root->children.back()->type == NodeType::INITVAL)
        {

            if ((int)root->children.size() == 6)
            {
                ANALYSIS(constexp, ConstExp, 2);
                int array_size = std::stoi(constexp->v);
                STE arr_ste;
                arr_ste.dimension.push_back(array_size);
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int)
                {
                    curr_type = ir::Type::IntPtr;
                }
                else if (curr_type == ir::Type::Float)
                {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                GET_CHILD_PTR(initval, InitVal, 5);
                if (initval->children.size() == 2)
                {
                    for (int i = 0; i < array_size; i++)
                    {
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
                else
                {
                    int cnt = 0;
                    for (int i = 1; i < (int)initval->children.size() - 1; i += 2, cnt++)
                    {
                        InitVal *child = dynamic_cast<InitVal *>(initval->children[i]);
                        Exp *exp = dynamic_cast<Exp *>(child->children[0]);
                        analysisExp(exp, buffer);
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(exp->v, Type::IntLiteral), Operator::store}));
                    }

                    for (; cnt < array_size; cnt++)
                    {
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
            }
            else if ((int)root->children.size() == 9)
            {
                ANALYSIS(constexp1, ConstExp, 2);
                ANALYSIS(constexp2, ConstExp, 5);
                int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);
                STE arr_ste;
                arr_ste.dimension.push_back(std::stoi(constexp1->v));
                arr_ste.dimension.push_back(std::stoi(constexp2->v));
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int)
                {
                    curr_type = ir::Type::IntPtr;
                }
                else if (curr_type == ir::Type::Float)
                {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                GET_CHILD_PTR(initval, InitVal, 8);
                if (initval->children.size() == 2)
                {
                    for (int i = 0; i < array_size; i++)
                    {
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
                else
                {
                    int cnt = 0;
                    for (int i = 1; i < (int)initval->children.size() - 1; i += 2, cnt++)
                    {
                        InitVal *child = dynamic_cast<InitVal *>(initval->children[i]);
                        Exp *exp = dynamic_cast<Exp *>(child->children[0]);
                        analysisExp(exp, buffer);
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(exp->v, Type::IntLiteral), Operator::store}));
                    }
                }
            }
        }
        else
        {

            if ((int)root->children.size() == 4)
            {
                ANALYSIS(constexp, ConstExp, 2);
                int array_size = std::stoi(constexp->v);
                STE arr_ste;
                arr_ste.dimension.push_back(array_size);
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int)
                {
                    curr_type = ir::Type::IntPtr;
                }
                else if (curr_type == ir::Type::Float)
                {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                for (int i = 0; i < array_size; i++)
                {
                    buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
            else if ((int)root->children.size() == 7)
            {
                ANALYSIS(constexp1, ConstExp, 2);
                ANALYSIS(constexp2, ConstExp, 5);
                int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);
                STE arr_ste;
                arr_ste.dimension.push_back(std::stoi(constexp1->v));
                arr_ste.dimension.push_back(std::stoi(constexp2->v));
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int)
                {
                    curr_type = ir::Type::IntPtr;
                }
                else if (curr_type == ir::Type::Float)
                {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                for (int i = 0; i < array_size; i++)
                {
                    buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        }
    }
}

void frontend::Analyzer::analysisInitVal(InitVal *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::EXP)
    {
        ANALYSIS(exp, Exp, 0);
        root->v = exp->v;
        root->t = exp->t;
    }
}

void frontend::Analyzer::analysisFuncFParam(FuncFParam *root, ir::Function &buffer)
{

    auto btype = dynamic_cast<BType *>(root->children[0]);
    assert(btype);
    analysisBType(btype, buffer.InstVec);
    std::string name = dynamic_cast<Term *>(root->children[1])->token.value;
    if ((int)root->children.size() > 2)
    {

        auto type = (btype->t == Type::Int) ? Type::IntPtr : Type::FloatPtr;
        buffer.ParameterList.push_back(Operand(name, type));
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, type), {}}});
    }
    else
    {
        buffer.ParameterList.push_back(Operand(name, btype->t));
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, btype->t), {}}});
    }
}

void frontend::Analyzer::analysisFuncFParams(FuncFParams *root, ir::Function &buffer)
{

    if ((int)root->children.size() == 1)
    {
        ANALYSIS(funcfparam, FuncFParam, 0);
    }
    else
    {
        ANALYSIS(funcfparam, FuncFParam, 0);
        int i = 1;
        while (i < (int)root->children.size())
        {
            ANALYSIS(funcfparam, FuncFParam, i + 1);
            i += 2;
        }
    }
}

void frontend::Analyzer::analysisBlock(Block *root, vector<ir::Instruction *> &buffer)
{

    symbol_table.add_scope(root);

    if ((int)root->children.size() > 2)
    {
        int i = 1;
        while (i < (int)root->children.size() - 1)
        {
            ANALYSIS(blockitem, BlockItem, i);
            i += 1;
        }
    }

    symbol_table.exit_scope();
}

void frontend::Analyzer::analysisBlockItem(BlockItem *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::DECL)
    {
        ANALYSIS(decl, Decl, 0);
    }
    else if (root->children[0]->type == NodeType::STMT)
    {
        ANALYSIS(stmt, Stmt, 0);
    }
}

void frontend::Analyzer::analysisStmt(Stmt *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::LVAL)
    {
        ANALYSIS(exp, Exp, 2);
        ANALYSIS(lval, LVal, 0);
    }
    else if (root->children[0]->type == NodeType::BLOCK)
    {

        ANALYSIS(block, Block, 0);
    }
    else if (root->children[0]->type == NodeType::EXP)
    {

        ANALYSIS(exp, Exp, 0);
    }
    else if (dynamic_cast<Term *>(root->children[0])->token.type == TokenType::IFTK)
    {

        auto tmp1 = vector<Instruction *>();
        GET_CHILD_PTR(cond, Cond, 2);
        analysisCond(cond, tmp1);
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());

        buffer.push_back(new Instruction(Operand(cond->v, cond->t), Operand(), Operand("2", Type::IntLiteral), Operator::_goto));

        GET_CHILD_PTR(stmt1, Stmt, 4);
        auto tmp2 = vector<Instruction *>();
        analysisStmt(stmt1, tmp2);

        if ((int)root->children.size() == 5)
        {

            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size() + 1), Type::IntLiteral), Operator::_goto}));

            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));
        }
        else
        {
            auto tmp3 = vector<Instruction *>();
            GET_CHILD_PTR(stmt2, Stmt, 6);
            analysisStmt(stmt2, tmp3);

            tmp2.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp3.size() + 1), Type::IntLiteral), Operator::_goto}));
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size() + 1), Type::IntLiteral), Operator::_goto}));
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());
            buffer.insert(buffer.end(), tmp3.begin(), tmp3.end());
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));
        }
    }
    else if (dynamic_cast<Term *>(root->children[0])->token.type == TokenType::WHILETK)
    {

        GET_CHILD_PTR(cond, Cond, 2);
        auto tmp1 = vector<Instruction *>();
        analysisCond(cond, tmp1);

        GET_CHILD_PTR(stmt, Stmt, 4);
        auto tmp2 = vector<Instruction *>();
        analysisStmt(stmt, tmp2);

        tmp2.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));

        for (int i = 0; i < (int)tmp2.size(); i++)
        {
            if (tmp2[i]->op == Operator::__unuse__ && tmp2[i]->op1.type == Type::null)
            {
                if (tmp2[i]->op1.name == "break")
                {
                    tmp2[i] = new Instruction({Operand(), Operand(), Operand(std::to_string((int)tmp2.size() - i), Type::IntLiteral), Operator::_goto});
                }
                else if (tmp2[i]->op1.name == "continue")
                {
                    auto goto_inst = new Instruction({Operand(), Operand(), Operand(std::to_string(-(2 + i + (int)tmp1.size())), Type::IntLiteral), Operator::_goto});
                    tmp2[i] = goto_inst;
                }
            }
        }

        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());

        buffer.push_back(new Instruction({Operand(cond->v, cond->t), Operand(), Operand("2", Type::IntLiteral), Operator::_goto}));

        buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size() + 1), Type::IntLiteral), Operator::_goto}));

        buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

        buffer.push_back(new Instruction(Operand(), Operand(), Operand(), Operator::__unuse__));
    }
    else if (dynamic_cast<Term *>(root->children[0])->token.type == TokenType::BREAKTK)
    {

        buffer.push_back(new Instruction({Operand("break", Type::null), Operand(), Operand(), Operator::__unuse__}));
    }
    else if (dynamic_cast<Term *>(root->children[0])->token.type == TokenType::CONTINUETK)
    {

        buffer.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));
    }
    else if (dynamic_cast<Term *>(root->children[0])->token.type == TokenType::RETURNTK)
    {

        if ((int)root->children.size() == 2)
        {
            Instruction *return_inst = new Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return});
            buffer.push_back(return_inst);
        }
        else
        {

            auto tmp = vector<Instruction *>();
            GET_CHILD_PTR(exp, Exp, 1);
            analysisExp(exp, tmp);
            buffer.insert(buffer.end(), tmp.begin(), tmp.end());

            if (curr_function->returnType == Type::Int)
            {

                if (exp->t == Type::Int || exp->t == Type::IntLiteral)
                {
                    Instruction *rerurn_inst = new Instruction({Operand(exp->v, exp->t), Operand(), Operand(), Operator::_return});
                    buffer.push_back(rerurn_inst);
                }

                else if (exp->t == Type::FloatLiteral)
                {
                    buffer.push_back(new Instruction({Operand(std::to_string((int)std::stof(exp->v)), Type::IntLiteral), Operand(), Operand(), Operator::_return}));
                }
                else if (exp->t == Type::Float)
                {
                    Operand tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(Operand(exp->v, Type::Float), Operand(), tmp, Operator::cvt_f2i));
                    buffer.push_back(new Instruction(tmp, Operand(), Operand(), Operator::_return));
                }
            }
            else if (curr_function->returnType == Type::Float)
            {

                if (exp->t == Type::Float || exp->t == Type::FloatLiteral)
                {
                    Instruction *retInst = new Instruction(Operand(exp->v, exp->t), Operand(), Operand(), Operator::_return);
                    buffer.push_back(retInst);
                }
                else if (exp->t == Type::IntLiteral)
                {
                    float val = (float)std::stoi(exp->v);
                    Instruction *retInst = new Instruction(Operand(std::to_string(val), Type::FloatLiteral), Operand(), Operand(), Operator::_return);
                    buffer.push_back(retInst);
                }
                else if (exp->t == Type::Int)
                {
                    Operand tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    Instruction *cvtInst = new Instruction(Operand(exp->v, exp->t), Operand(), tmp, Operator::cvt_i2f);
                    Instruction *retInst = new Instruction(tmp, Operand(), Operand(), Operator::_return);
                    buffer.push_back(cvtInst);
                    buffer.push_back(retInst);
                }
            }
        }
    }
}

void frontend::Analyzer::analysisExp(Exp *root, vector<ir::Instruction *> &buffer)
{

    ANALYSIS(addexp, AddExp, 0);
    COPY_EXP_NODE(addexp, root);
}

void frontend::Analyzer::analysisCond(Cond *root, vector<ir::Instruction *> &buffer)
{
    ANALYSIS(lorexp, LOrExp, 0);
    COPY_EXP_NODE(lorexp, root);
}

void frontend::Analyzer::analysisLVal(LVal *root, vector<ir::Instruction *> &buffer)
{

    auto tk = dynamic_cast<Term *>(root->children[0])->token;

    auto op = symbol_table.get_operand(tk.value);
    root->t = op.type;

    if ((int)root->children.size() == 1)
    {

        root->v = op.name;
        root->is_computable = (root->t == Type::IntLiteral || root->t == Type::FloatLiteral) ? true : false;
        root->i = 0;

        if (root->parent->type == NodeType::STMT)
        {
            auto exp_par = dynamic_cast<Exp *>(root->parent->children[2]);
            auto op1 = Operand(exp_par->v, exp_par->t);
            auto des = Operand(root->v, root->t);
            if (root->t == Type::Int)
            {
                auto mov_inst = new Instruction({op1, Operand(), des, Operator::mov});
                buffer.push_back(mov_inst);
            }
            else
            {
                buffer.push_back(new Instruction({op1, Operand(), des, Operator::fmov}));
            }
        }
    }
    else
    {

        STE arr = symbol_table.get_ste(tk.value);
        vector<int> dimension = arr.dimension;

        if ((int)root->children.size() == 4)
        {

            ANALYSIS(exp, Exp, 2);
            Type t = (root->t == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            Operand index = Operand(exp->v, exp->t);
            if (root->parent->type == NodeType::STMT)
            {
                auto exp_par = dynamic_cast<Exp *>(root->parent->children[2]);
                Operand des = Operand(exp_par->v, exp_par->t);
                buffer.push_back(new Instruction({arr.operand, index, des, Operator::store}));
                root->v = des.name;
            }
            else
            {
                Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));
                root->v = des.name;
            }
        }
        else
        {

            ANALYSIS(exp1, Exp, 2);
            ANALYSIS(exp2, Exp, 5);
            Type t = (root->t == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            if (exp1->is_computable && exp2->is_computable)
            {
                std::string i = std::to_string(std::stoi(exp1->v) * dimension[1] + std::stoi(exp2->v));
                Operand index = Operand(i, Type::IntLiteral);
                if (root->parent->type == NodeType::STMT)
                {
                    auto exp_par = dynamic_cast<Exp *>(root->parent->children[2]);
                    Operand des = Operand(exp_par->v, exp_par->t);
                    buffer.push_back(new Instruction({arr.operand, index, des, Operator::store}));
                    root->v = des.name;
                }
                else
                {
                    Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                    buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));
                    root->v = des.name;
                }
            }
            else
            {
                auto op1 = Operand(exp1->v, exp1->t);
                auto op2 = Operand(std::to_string(dimension[1]), Type::IntLiteral);
                auto op3 = Operand(exp2->v, exp2->t);
                type_transform(op1, op2, buffer);
                auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                auto tmp2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction({op1, op2, tmp1, Operator::mul}));
                buffer.push_back(new Instruction({tmp1, op3, tmp2, Operator::add}));
                if (root->parent->type == NodeType::STMT)
                {
                    auto exp_par = dynamic_cast<Exp *>(root->parent->children[2]);
                    Operand des = Operand(exp_par->v, exp_par->t);
                    buffer.push_back(new Instruction({arr.operand, tmp2, des, Operator::store}));
                    root->v = des.name;
                }
                else
                {
                    Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                    buffer.push_back(new Instruction({arr.operand, tmp2, des, Operator::load}));
                    root->v = des.name;
                }
            }
        }
    }
}

void frontend::Analyzer::analysisPrimaryExp(PrimaryExp *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::TERMINAL)
    {
        ANALYSIS(exp, Exp, 1);
        COPY_EXP_NODE(exp, root);
    }
    else if (root->children[0]->type == NodeType::LVAL)
    {
        ANALYSIS(lval, LVal, 0);
        COPY_EXP_NODE(lval, root);
    }
    else
    {
        root->is_computable = true;
        auto number_tk = dynamic_cast<Term *>(root->children[0]->children[0])->token;
        root->t = (number_tk.type == TokenType::INTLTR) ? Type::IntLiteral : Type::FloatLiteral;
        if (root->t == Type::IntLiteral)
        {
            root->v = std::to_string(eval_int(number_tk.value));
        }
        else
        {
            root->v = number_tk.value;
        }
    }
}

void frontend::Analyzer::analysisUnaryExp(UnaryExp *root, vector<ir::Instruction *> &buffer)
{

    if (root->children[0]->type == NodeType::PRIMARYEXP)
    {
        ANALYSIS(primaryexp, PrimaryExp, 0);
        COPY_EXP_NODE(primaryexp, root);
    }
    else if (root->children[0]->type == NodeType::TERMINAL)
    {
        std::string func_name = dynamic_cast<Term *>(root->children[0])->token.value;
        auto op1 = Operand(func_name, Type::null);
        Type t = symbol_table.functions[func_name]->returnType;
        auto des = Operand("t" + std::to_string(tmp_cnt++), t);
        if ((int)root->children.size() == 3)
        {
            buffer.push_back(new ir::CallInst(op1, des));
        }
        else
        {
            auto callinst = new ir::CallInst(op1, vector<Operand>(), des);
            GET_CHILD_PTR(funcrparams, FuncRParams, 2);
            assert(funcrparams);
            analysisFuncRParams(funcrparams, buffer, *callinst);
            buffer.push_back(callinst);
        }
        root->v = des.name;
        root->t = t;
    }
    else
    {
        auto tk = dynamic_cast<Term *>(root->children[0]->children[0])->token.type;
        ANALYSIS(unaryexp, UnaryExp, 1);
        if (tk == TokenType::PLUS)
        {
            COPY_EXP_NODE(unaryexp, root);
        }
        else
        {
            root->is_computable = unaryexp->is_computable;
            root->t = unaryexp->t;
            if (unaryexp->is_computable)
            {
                if (unaryexp->t == Type::IntLiteral)
                {
                    if (tk == TokenType::MINU)
                    {
                        root->v = std::to_string(-std::stoi(unaryexp->v));
                    }
                    else
                    {
                        root->v = std::to_string(!std::stoi(unaryexp->v));
                    }
                }
                else
                {
                    if (tk == TokenType::MINU)
                    {
                        root->v = std::to_string(-std::stof(unaryexp->v));
                    }
                    else
                    {
                        root->v = std::to_string(!std::stof(unaryexp->v));
                    }
                }
            }
            else
            {
                if (unaryexp->t == Type::Int)
                {
                    auto op1 = Operand(unaryexp->v, unaryexp->t);
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    if (tk == TokenType::MINU)
                    {
                        auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                        buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), tmp, Operator::def));
                        buffer.push_back(new Instruction(tmp, op1, tmp1, Operator::sub));
                        root->v = tmp1.name;
                    }
                    else
                    {
                        buffer.push_back(new Instruction(op1, Operand(), tmp, Operator::_not));
                        root->v = tmp.name;
                    }
                }
                else
                {
                    auto op1 = Operand(unaryexp->v, unaryexp->t);
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    if (tk == TokenType::MINU)
                    {
                        auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                        buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), tmp, Operator::fdef));
                        buffer.push_back(new Instruction(tmp, op1, tmp1, Operator::fsub));
                        root->v = tmp1.name;
                    }
                }
            }
        }
    }
}

void frontend::Analyzer::analysisFuncRParams(FuncRParams *root, vector<ir::Instruction *> &buffer, ir::CallInst &callinst)
{
    ANALYSIS(exp1, Exp, 0);
    callinst.argumentList.push_back(Operand(exp1->v, exp1->t));
    int i = 1;
    while (i < (int)root->children.size())
    {
        ANALYSIS(exp2, Exp, i + 1);
        callinst.argumentList.push_back(Operand(exp2->v, exp2->t));
        i += 2;
    }
}

void frontend::Analyzer::analysisMulExp(MulExp *root, vector<ir::Instruction *> &buffer)
{

    if ((int)root->children.size() == 1)
    {

        ANALYSIS(unaryexp1, UnaryExp, 0);
        COPY_EXP_NODE(unaryexp1, root);
    }
    else if ((int)root->children.size() > 1)
    {
        ANALYSIS(unaryexp1, UnaryExp, 0);
        root->is_computable = unaryexp1->is_computable;
        root->t = unaryexp1->t;
        root->v = unaryexp1->v;
        int i = 1;
        while (i < (int)root->children.size())
        {
            auto tk = dynamic_cast<Term *>(root->children[i])->token.type;
            ANALYSIS(unaryexp2, UnaryExp, i + 1);
            if (root->is_computable && unaryexp2->is_computable)
            {
                root->is_computable = true;
                if (root->t != unaryexp2->t)
                {
                    root->t = Type::FloatLiteral;
                }

                if (root->t == Type::IntLiteral)
                {
                    if (tk == TokenType::MULT)
                    {
                        root->v = std::to_string(std::stoi(root->v) * std::stoi(unaryexp2->v));
                    }
                    else if (tk == TokenType::DIV)
                    {
                        root->v = std::to_string(std::stoi(root->v) / std::stoi(unaryexp2->v));
                    }
                    else if(tk == TokenType::MOD)
                    {
                        root->v = std::to_string(std::stoi(root->v) % std::stoi(unaryexp2->v));
                    }
                }
                else
                {
                    if (tk == TokenType::MULT)
                    {
                        root->v = std::to_string(std::stof(root->v) * std::stof(unaryexp2->v));
                    }
                    else if (tk == TokenType::DIV)
                    {
                        root->v = std::to_string(std::stof(root->v) / std::stof(unaryexp2->v));
                    }
                }
            }
            else
            {
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(unaryexp2->v, unaryexp2->t);
                Operand des = Operand("t" + std::to_string(tmp_cnt++), root->t);
                type_transform(op1, op2, buffer);
                des.type = op1.type;
                if(tk == TokenType::MULT) {
                    if(op1.type == Type::Int) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::mul}));
                    }
                    else if(op1.type == Type::Float) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::fmul}));
                    }
                }
                else if(tk == TokenType::DIV) {
                    if(op1.type == Type::Int) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::div}));
                    }
                    else if(op1.type == Type::Float) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::fdiv}));
                    }
                }
                else if(tk == TokenType::MOD) {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::mod}));
                }
                else assert(0&&"mul error");
                root->v = des.name;
                root->t = des.type;
            }

            i += 2;
        }
    }
}

void frontend::Analyzer::analysisAddExp(AddExp *root, vector<ir::Instruction *> &buffer)
{
    if ((int)root->children.size() == 1)
    {
        ANALYSIS(mulexp1, MulExp, 0);
        COPY_EXP_NODE(mulexp1, root);
    }
    else if ((int)root->children.size() > 1)
    {

        ANALYSIS(mulexp1, MulExp, 0);

        root->is_computable = mulexp1->is_computable;
        root->t = mulexp1->t;
        root->v = mulexp1->v;

        int i = 1;
        while (i < (int)root->children.size())
        {

            auto tk = dynamic_cast<Term *>(root->children[i])->token.type;
            ANALYSIS(mulexp2, MulExp, i + 1);
            if (root->is_computable && mulexp2->is_computable)
            {
                root->is_computable = true;
                if (root->t != mulexp2->t)
                {
                    root->t = Type::FloatLiteral;
                }
                if (root->t == Type::IntLiteral)
                {
                    if (tk == TokenType::PLUS)
                    {
                        root->v = std::to_string(std::stoi(root->v) + std::stoi(mulexp2->v));
                    }
                    else if(tk == TokenType::MINU)
                    {
                        root->v = std::to_string(std::stoi(root->v) - std::stoi(mulexp2->v));
                    }
                }
                else
                {
                    if (tk == TokenType::PLUS)
                    {
                        root->v = std::to_string(std::stof(root->v) + std::stof(mulexp2->v));
                    }
                    else if(tk == TokenType::MINU)
                    {
                        root->v = std::to_string(std::stof(root->v) - std::stof(mulexp2->v));
                    }
                }
            }
            else
            {
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(mulexp2->v, mulexp2->t);
                Operand des = Operand("t" + std::to_string(tmp_cnt++), root->t);
                type_transform(op1, op2, buffer);
                des.type = op1.type;
                if(tk == TokenType::PLUS) {
                    if(op1.type == Type::Int) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::add}));
                    }
                    else {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::fadd}));
                    }
                }
                else if(tk == TokenType::MINU) {
                    if(op1.type == Type::Int) {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::sub}));
                    }
                    else {
                        buffer.push_back(new Instruction({op1, op2, des, Operator::fsub}));
                    }
                }
                else assert(0&&"ADD error");
                root->v = des.name;
                root->t = des.type;
            }

            i += 2;
        }
    }
}

void frontend::Analyzer::analysisRelExp(RelExp *root, vector<ir::Instruction *> &buffer)
{

    if ((int)root->children.size() == 1)
    {

        ANALYSIS(addexp, AddExp, 0);
        COPY_EXP_NODE(addexp, root);
    }
    else
    {

        ANALYSIS(addexp1, AddExp, 0);
        root->is_computable = addexp1->is_computable;
        root->t = addexp1->t;
        root->v = addexp1->v;

        int i = 1;
        while (i < (int)root->children.size())
        {

            ANALYSIS(addexp2, AddExp, i + 1);
            auto tk = dynamic_cast<Term *>(root->children[i])->token.type;

            root->is_computable = false;
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(addexp2->v, addexp2->t);
            type_transform(op1, op2, buffer);
            Operand des = Operand("t" + std::to_string(tmp_cnt++), op1.type);
            if (tk == TokenType::LSS)
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::lss}));
                }
                else
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::flss}));
                }
            }
            else if (tk == TokenType::GTR)
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::gtr}));
                }
                else
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgtr}));
                }
            }
            else if (tk == TokenType::LEQ)
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::leq}));
                }
                else
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fleq}));
                }
            }
            else
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::geq}));
                }
                else
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgeq}));
                }
            }

            root->v = des.name;
            root->t = Type::Int;

            i += 2;
        }
    }
}

void frontend::Analyzer::analysisEqExp(EqExp *root, vector<ir::Instruction *> &buffer)
{
    if ((int)root->children.size() == 1)
    {

        ANALYSIS(relexp, RelExp, 0);
        COPY_EXP_NODE(relexp, root);
    }
    else
    {

        ANALYSIS(relexp1, RelExp, 0);
        root->is_computable = relexp1->is_computable;
        root->v = relexp1->v;
        root->t = relexp1->t;

        int i = 1;
        while (i < (int)root->children.size())
        {
            ANALYSIS(relexp2, RelExp, i + 1);
            auto tk = dynamic_cast<Term *>(root->children[i])->token.type;

            root->is_computable = false;
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(relexp2->v, relexp2->t);
            type_transform(op1, op2, buffer);
            Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            if (tk == TokenType::EQL)
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::eq}));
                }
                else
                {
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::feq}));
                }
            }
            else
            {
                if (op1.type == Type::Int)
                {
                    buffer.push_back(new Instruction({op1, op2, des, Operator::neq}));
                }
                else
                {
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fneq}));
                }
            }

            root->v = des.name;
            root->t = Type::Int;

            i += 2;
        }
    }
}

void frontend::Analyzer::analysisLAndExp(LAndExp *root, vector<ir::Instruction *> &buffer)
{
    if ((int)root->children.size() == 1)
    {

        ANALYSIS(eqexp, EqExp, 0);
        COPY_EXP_NODE(eqexp, root);
    }
    else
    {

        ANALYSIS(eqexp, EqExp, 0);

        auto tmp = vector<ir::Instruction *>();
        auto andexp = dynamic_cast<LAndExp *>(root->children[2]);
        assert(andexp);
        analysisLAndExp(andexp, tmp);

        root->t = Type::Int;

        Operand op1 = Operand(eqexp->v, eqexp->t);
        Operand op2 = Operand(andexp->v, andexp->t);
        Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), op1.type);

        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));
        buffer.push_back(new Instruction({t1, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({{}, {}, {std::to_string(tmp.size() + 3), Type::IntLiteral}, Operator::_goto}));
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"0", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}

void frontend::Analyzer::analysisLOrExp(LOrExp *root, vector<ir::Instruction *> &buffer)
{
    if ((int)root->children.size() == 1)
    {

        ANALYSIS(landexp, LAndExp, 0);
        COPY_EXP_NODE(landexp, root);
    }
    else
    {

        root->t = Type::Int;

        ANALYSIS(andexp, LAndExp, 0);

        auto tmp = vector<ir::Instruction *>();
        auto orexp = dynamic_cast<LOrExp *>(root->children[2]);
        assert(orexp);
        analysisLOrExp(orexp, tmp);

        Operand op1 = Operand(andexp->v, andexp->t);
        Operand op2 = Operand(orexp->v, orexp->t);
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), root->t);
        Operand des = Operand("t" + std::to_string(tmp_cnt++), root->t);

        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));
        buffer.push_back(new Instruction({t1, {}, {std::to_string(tmp.size() + 3), Type::IntLiteral}, Operator::_goto}));
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"1", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}

void frontend::Analyzer::analysisConstExp(ConstExp *root, vector<ir::Instruction *> &buffer)
{
    ANALYSIS(addexp, AddExp, 0);
    root->v = addexp->v;
    root->t = addexp->t;
}