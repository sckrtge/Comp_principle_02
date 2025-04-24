#include"front/syntax.h"

#include<iostream>
#include<cassert>

using frontend::Parser;

#define DEBUG_PARSER
#define TODO assert(0 && "todo")
#define CUR_TOKEN_IS(tk_type) (index < token_stream.size() && token_stream[index].type == TokenType::tk_type)
#define NXT_TOKEN_IS(tk_type, nxt) (index + nxt < token_stream.size() && token_stream[index + nxt].type == TokenType::tk_type)
#define PARSE_TOKEN(tk_type) root->children.push_back(parseTerm(root, TokenType::tk_type))
#define PARSE(name, type) auto name = new type(root); assert(parse##type(name)); root->children.push_back(name); 


Parser::Parser(const std::vector<frontend::Token>& tokens): index(0), token_stream(tokens) {}

Parser::~Parser() {}

bool frontend::Parser::isExp() {
    return CUR_TOKEN_IS(LPARENT) || CUR_TOKEN_IS(IDENFR) 
    || CUR_TOKEN_IS(INTLTR) || CUR_TOKEN_IS(FLOATLTR) 
    || CUR_TOKEN_IS(PLUS) || CUR_TOKEN_IS(MINU) 
    || CUR_TOKEN_IS(NOT);
}

frontend::Term* frontend::Parser::parseTerm(AstNode *parent, TokenType expected) {
    if(index < token_stream.size() && token_stream[index].type == expected) {
        auto node = new Term(token_stream[index], parent);
        index++;
        return node;
    }
    else {
        assert(0 && "Term error");
    }
}

frontend::CompUnit* Parser::get_abstract_syntax_tree(){
    CompUnit* root = new CompUnit(nullptr);
    if(parseCompUnit(root) == false) {
        assert(0 && "get_abstruct_syntax_tree error");
    }
    return root;
}

bool frontend::Parser::parseCompUnit(CompUnit* root) {
    if(CUR_TOKEN_IS(CONSTTK) || CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK) || CUR_TOKEN_IS(VOIDTK)) {
        if((CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK) || CUR_TOKEN_IS(VOIDTK)) && NXT_TOKEN_IS(IDENFR, 1) && NXT_TOKEN_IS(LPARENT, 2) ) {
            PARSE(son, FuncDef);
        }
        else if(CUR_TOKEN_IS(CONSTTK) || CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
            PARSE(son, Decl);
        }
        else return false;
    }
    else return false;
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(CONSTTK) || CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK) || CUR_TOKEN_IS(VOIDTK)) {
            PARSE(son, CompUnit);
        }
    }
    return true;
}

bool frontend::Parser::parseDecl(Decl* root) {
    if(CUR_TOKEN_IS(CONSTTK)) {
        PARSE(son, ConstDecl);
    }
    else if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, VarDecl);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseConstDecl(ConstDecl* root) {
    if(CUR_TOKEN_IS(CONSTTK)) {
        PARSE_TOKEN(CONSTTK);
    }
    else return false;
    if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, BType);
    }
    else return false;
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE(son, ConstDef);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(COMMA)) {
            PARSE_TOKEN(COMMA);
        }
        else break;
        if(CUR_TOKEN_IS(IDENFR)) {
            PARSE(son, ConstDef);
        }
        else return false;
    }
    if(CUR_TOKEN_IS(SEMICN)) {
        PARSE_TOKEN(SEMICN);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseBType(BType* root) {
    if(CUR_TOKEN_IS(INTTK)) {
        PARSE_TOKEN(INTTK);
    }
    else if(CUR_TOKEN_IS(FLOATTK)) {
        PARSE_TOKEN(FLOATTK);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseConstDef(ConstDef* root) {
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE_TOKEN(IDENFR);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(LBRACK)) {
            PARSE_TOKEN(LBRACK);
        }
        else break;
        if(isExp()) {
            PARSE(son, ConstExp);
        }
        else return false;
        if(CUR_TOKEN_IS(RBRACK)) {
            PARSE_TOKEN(RBRACK);
        }
        else return false;
    }
    if(CUR_TOKEN_IS(ASSIGN)) {
        PARSE_TOKEN(ASSIGN);
    }
    else return false;
    if(isExp() || CUR_TOKEN_IS(LBRACE)) {
        PARSE(son, ConstInitVal);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseConstInitVal(ConstInitVal* root) {
    if(isExp()) {
        PARSE(son, ConstExp);
    }
    else if(CUR_TOKEN_IS(LBRACE)) {
        PARSE_TOKEN(LBRACE);
        if(index < token_stream.size()) {
                if((isExp() || CUR_TOKEN_IS(LBRACE))) {
                PARSE(son, ConstInitVal);
                while(index < token_stream.size()) {
                    if(CUR_TOKEN_IS(COMMA)) {
                        PARSE_TOKEN(COMMA);
                    }
                    else break;
                    if(isExp() || CUR_TOKEN_IS(LBRACE)) {
                        PARSE(son, ConstInitVal);
                    }
                    else return false;
                }
            }
        }
        if(CUR_TOKEN_IS(RBRACE)) {
            PARSE_TOKEN(RBRACE);
        }
        else return false;
    }
    else return false;
    return true;
}

bool frontend::Parser::parseVarDecl(VarDecl* root) {
    if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, BType);
    }
    else return false;
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE(son, VarDef);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(COMMA)) {
            PARSE_TOKEN(COMMA);
        }
        else break;
        if(CUR_TOKEN_IS(IDENFR)) {
            PARSE(son, VarDef);
        }
        else return false;
    }
    if(CUR_TOKEN_IS(SEMICN)) {
        PARSE_TOKEN(SEMICN);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseVarDef(VarDef* root) {
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE_TOKEN(IDENFR);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(LBRACK)) {
            PARSE_TOKEN(LBRACK);
        }
        else break;
        if(isExp()) {
            PARSE(son, ConstExp);
        }
        else return false;
        if(CUR_TOKEN_IS(RBRACK)) {
            PARSE_TOKEN(RBRACK);
        }
        else return false;
    }
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(ASSIGN)) {
            PARSE_TOKEN(ASSIGN);
            if(isExp() || CUR_TOKEN_IS(LBRACE)) {
                PARSE(son, InitVal);
            }
            else return false;
        }
    }
    return true;
}

bool frontend::Parser::parseInitVal(InitVal* root) {
    if(isExp()) {
        PARSE(son, Exp);
    }
    else if(CUR_TOKEN_IS(LBRACE)) {
        PARSE_TOKEN(LBRACE);
        if(index < token_stream.size()) {
            if(isExp() || CUR_TOKEN_IS(LBRACE)) {
                PARSE(son, InitVal);
                while(index < token_stream.size()) {
                    if(CUR_TOKEN_IS(COMMA)) {
                        PARSE_TOKEN(COMMA);
                    }
                    else break;
                    if(isExp() || CUR_TOKEN_IS(LBRACE)) {
                        PARSE(son, InitVal);
                    }
                    else return false;
                }
            }
        }
        if(CUR_TOKEN_IS(RBRACE)) {
            PARSE_TOKEN(RBRACE);
        }
        else return false;
    }
    else return false;
    return true;
}

bool frontend::Parser::parseFuncDef(FuncDef* root) {
    if(CUR_TOKEN_IS(VOIDTK) || CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, FuncType);
    }
    else return false;
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE_TOKEN(IDENFR);
    }
    else return false;
    if(CUR_TOKEN_IS(LPARENT)) {
        PARSE_TOKEN(LPARENT);
    }
    else return false;
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
            PARSE(son, FuncFParams);
        }
    }
    if(CUR_TOKEN_IS(RPARENT)) {
        PARSE_TOKEN(RPARENT);
    }
    else return false;
    if(CUR_TOKEN_IS(LBRACE)) {
        PARSE(son,Block);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseFuncType(FuncType* root) {
    if(CUR_TOKEN_IS(VOIDTK)) {
        PARSE_TOKEN(VOIDTK);
    }
    else if(CUR_TOKEN_IS(INTTK)) {
        PARSE_TOKEN(INTTK);
    }
    else if(CUR_TOKEN_IS(FLOATTK)) {
        PARSE_TOKEN(FLOATTK);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseFuncFParam(FuncFParam* root) {
    if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, BType);
    }
    else return false;
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE_TOKEN(IDENFR);
    }
    else return false;
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(LBRACK)) {
            PARSE_TOKEN(LBRACK);
            if(CUR_TOKEN_IS(RBRACK)) {
                PARSE_TOKEN(RBRACK);
            }
            else return false;
            while(index < token_stream.size()) {
                if(CUR_TOKEN_IS(LBRACK)) {
                    PARSE_TOKEN(LBRACK);
                }
                else break;
                if(isExp()) {
                    PARSE(son,Exp);
                }
                else return false;
                if(CUR_TOKEN_IS(RBRACK)) {
                    PARSE_TOKEN(RBRACK);
                }
                else return false;
            }
        }
    }
    return true;
}

bool frontend::Parser::parseFuncFParams(FuncFParams* root) {
    if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, FuncFParam);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(COMMA)) {
            PARSE_TOKEN(COMMA);
        }
        else break;
        if(CUR_TOKEN_IS(INTTK) || CUR_TOKEN_IS(FLOATTK)) {
            PARSE(son, FuncFParam);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseBlock(Block* root) {
    if(CUR_TOKEN_IS(LBRACE)) {
        PARSE_TOKEN(LBRACE);
    }
    else return false;
    while(index < token_stream.size()) {
        if(isExp() || CUR_TOKEN_IS(CONSTTK) || CUR_TOKEN_IS(INTTK)
        || CUR_TOKEN_IS(FLOATTK) || CUR_TOKEN_IS(LBRACE) || CUR_TOKEN_IS(IFTK)
        || CUR_TOKEN_IS(WHILETK) || CUR_TOKEN_IS(BREAKTK) || CUR_TOKEN_IS(CONTINUETK)
        || CUR_TOKEN_IS(RETURNTK) || CUR_TOKEN_IS(SEMICN)) {
            PARSE(son, BlockItem);
        }
        else break;
    }
    if(CUR_TOKEN_IS(RBRACE)) {
        PARSE_TOKEN(RBRACE);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseBlockItem(BlockItem* root) {
    if(CUR_TOKEN_IS(CONSTTK) || CUR_TOKEN_IS(INTTK)
    || CUR_TOKEN_IS(FLOATTK)) {
        PARSE(son, Decl);
    }
    else if(isExp() || CUR_TOKEN_IS(LBRACE) || CUR_TOKEN_IS(IFTK)
    || CUR_TOKEN_IS(WHILETK) || CUR_TOKEN_IS(BREAKTK) || CUR_TOKEN_IS(CONTINUETK)
    || CUR_TOKEN_IS(RETURNTK) || CUR_TOKEN_IS(SEMICN)) {
        PARSE(son, Stmt);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseStmt(Stmt* root) {
    if(CUR_TOKEN_IS(LBRACE)) {
        PARSE(son, Block);
        parseBlock(son);
    }
    else if(CUR_TOKEN_IS(IFTK)) {
        PARSE_TOKEN(IFTK);
        if(CUR_TOKEN_IS(LPARENT)) {
            PARSE_TOKEN(LPARENT);
        }
        else return false;
        if(isExp()) {
            PARSE(son, Cond);
        }
        else return false;
        if(CUR_TOKEN_IS(RPARENT)) {
            PARSE_TOKEN(RPARENT);
        }
        else return false;
        if(isExp() || CUR_TOKEN_IS(LBRACE) || CUR_TOKEN_IS(IFTK)
        || CUR_TOKEN_IS(WHILETK) || CUR_TOKEN_IS(BREAKTK) || CUR_TOKEN_IS(CONTINUETK)
        || CUR_TOKEN_IS(RETURNTK) || CUR_TOKEN_IS(SEMICN)) {
            PARSE(son, Stmt);
        }
        else return false;
        if(index < token_stream.size()) {
            if(CUR_TOKEN_IS(ELSETK)) {
                PARSE_TOKEN(ELSETK);
                if(isExp() || CUR_TOKEN_IS(LBRACE) || CUR_TOKEN_IS(IFTK)
                || CUR_TOKEN_IS(WHILETK) || CUR_TOKEN_IS(BREAKTK) || CUR_TOKEN_IS(CONTINUETK)
                || CUR_TOKEN_IS(RETURNTK) || CUR_TOKEN_IS(SEMICN)) {
                    PARSE(son, Stmt);
                }
                else return false;
            }
        }
    }
    else if(CUR_TOKEN_IS(WHILETK)) {
        PARSE_TOKEN(WHILETK);
        if(CUR_TOKEN_IS(LPARENT)) {
            PARSE_TOKEN(LPARENT);
        }
        else return false;
        if(isExp()) {
            PARSE(son, Cond);
        }
        else return false;
        if(CUR_TOKEN_IS(RPARENT)) {
            PARSE_TOKEN(RPARENT);
        }
        else return false;
        if(isExp() || CUR_TOKEN_IS(LBRACE) || CUR_TOKEN_IS(IFTK)
        || CUR_TOKEN_IS(WHILETK) || CUR_TOKEN_IS(BREAKTK) || CUR_TOKEN_IS(CONTINUETK)
        || CUR_TOKEN_IS(RETURNTK) || CUR_TOKEN_IS(SEMICN)) {
            PARSE(son, Stmt);
        }
        else return false;
    }
    else if(CUR_TOKEN_IS(BREAKTK)) {
        PARSE_TOKEN(BREAKTK);
        if(CUR_TOKEN_IS(SEMICN)) {
            PARSE_TOKEN(SEMICN);
        }
        else return false;
    }
    else if(CUR_TOKEN_IS(CONTINUETK)) {
        PARSE_TOKEN(CONTINUETK);
        if(CUR_TOKEN_IS(SEMICN)) {
            PARSE_TOKEN(SEMICN);
        }
        else return false;
    }
    else if(CUR_TOKEN_IS(RETURNTK)) {
        PARSE_TOKEN(RETURNTK);
        if(index < token_stream.size()) {
            if(isExp()) {
                PARSE(son, Exp);
            }
        }
        if(CUR_TOKEN_IS(SEMICN)) {
            PARSE_TOKEN(SEMICN);
        }
        else return false;
    }
    else if(isExp() || CUR_TOKEN_IS(SEMICN)) {
        if(CUR_TOKEN_IS(IDENFR) && !NXT_TOKEN_IS(LPARENT, 1)) {
            PARSE(son, LVal);
            if(CUR_TOKEN_IS(ASSIGN)) {
                PARSE_TOKEN(ASSIGN);
            }
            else return false;
            if(isExp()) {
                PARSE(son,Exp);
            }
            else return false;
            if(CUR_TOKEN_IS(SEMICN)) {
                PARSE_TOKEN(SEMICN);
            }
            else return false;
        }
        else {
            if(index < token_stream.size()) {
                if(isExp()) {
                    PARSE(son, Exp);
                }
            }
            if(CUR_TOKEN_IS(SEMICN)) {
                PARSE_TOKEN(SEMICN);
            }
            else return false;
        }
    }
    return true;
}

bool frontend::Parser::parseExp(Exp* root) {
    if(isExp()) {
        PARSE(son, AddExp);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseCond(Cond* root) {
    if(isExp()) {
        PARSE(son, LOrExp);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseLVal(LVal* root) {
    if(CUR_TOKEN_IS(IDENFR)) {
        PARSE_TOKEN(IDENFR);
        while(index < token_stream.size()) {
            if(CUR_TOKEN_IS(LBRACK)) {
                PARSE_TOKEN(LBRACK);
            }
            else break;
            if(isExp()) {
                PARSE(son,Exp);
            }
            else return false;
            if(CUR_TOKEN_IS(RBRACK)) {
                PARSE_TOKEN(RBRACK);
            }
            else return false;
        }
    }
    else return false;
    return true;
}

bool frontend::Parser::parseNumber(Number* root) {
    if(CUR_TOKEN_IS(INTLTR)) {
        PARSE_TOKEN(INTLTR);
    }
    else if(CUR_TOKEN_IS(FLOATLTR)) {
        PARSE_TOKEN(FLOATLTR);
    }
    else return false;
    return true;
}

bool frontend::Parser::parsePrimaryExp(PrimaryExp* root) {
    if(CUR_TOKEN_IS(LPARENT)) {
        PARSE_TOKEN(LPARENT);
        if(isExp()) {
            PARSE(son, Exp);
        }
        else return false;
        if(CUR_TOKEN_IS(RPARENT)) {
            PARSE_TOKEN(RPARENT);
        }
        else return false;
    }
    else if(CUR_TOKEN_IS(IDENFR)) {
        PARSE(son, LVal);
    }
    else if(CUR_TOKEN_IS(INTLTR) || CUR_TOKEN_IS(FLOATLTR)) {
        PARSE(son, Number);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseUnaryExp(UnaryExp* root) {
    if(CUR_TOKEN_IS(IDENFR) && NXT_TOKEN_IS(LPARENT, 1)) {
        PARSE_TOKEN(IDENFR);
        if(CUR_TOKEN_IS(LPARENT)) {
            PARSE_TOKEN(LPARENT);
        }
        else return false;
        if(index < token_stream.size()) {
            if(isExp()) {
                PARSE(son,FuncRParams);
            }
        }
        if(CUR_TOKEN_IS(RPARENT)) {
            PARSE_TOKEN(RPARENT);
        }
        else return false;
    }
    else if(CUR_TOKEN_IS(LPARENT) || CUR_TOKEN_IS(IDENFR) 
    || CUR_TOKEN_IS(INTLTR) || CUR_TOKEN_IS(FLOATLTR) ) {
        PARSE(son, PrimaryExp);
    }
    else if(CUR_TOKEN_IS(PLUS) || CUR_TOKEN_IS(MINU) || CUR_TOKEN_IS(NOT)) {
        PARSE(son, UnaryOp);
        if(isExp()) {
            PARSE(son, UnaryExp);
        }
        else return false;
    }
    else return false;
    return true;
}

bool frontend::Parser::parseUnaryOp(UnaryOp* root) {
    if(CUR_TOKEN_IS(PLUS)) {
        PARSE_TOKEN(PLUS);
    }
    else if(CUR_TOKEN_IS(MINU)) {
        PARSE_TOKEN(MINU);
    }
    else if(CUR_TOKEN_IS(NOT)) {
        PARSE_TOKEN(NOT);
    }
    else return false;
    return true;
}

bool frontend::Parser::parseFuncRParams(FuncRParams* root) {
    if(isExp()) {
        PARSE(son, Exp);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(COMMA)) {
            PARSE_TOKEN(COMMA);
        }
        else break;
        if(isExp()) {
            PARSE(son, Exp);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseMulExp(MulExp* root) {
    if(isExp()) {
        PARSE(son, UnaryExp);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(MULT)) {
            PARSE_TOKEN(MULT);
        }
        else if(CUR_TOKEN_IS(DIV)) {
            PARSE_TOKEN(DIV);
        }
        else if(CUR_TOKEN_IS(MOD)) {
            PARSE_TOKEN(MOD);
        }
        else break;
        if(isExp()) {
            PARSE(son, UnaryExp);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseAddExp(AddExp* root) {
    if(isExp()) {
        PARSE(son, MulExp);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(PLUS)) {
            PARSE_TOKEN(PLUS);
        }
        else if(CUR_TOKEN_IS(MINU)) {
            PARSE_TOKEN(MINU);
        }
        else break;
        if(isExp()) {
            PARSE(son, MulExp);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseRelExp(RelExp* root) {
    if(isExp()) {
        PARSE(son, AddExp);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(LSS)) {
            PARSE_TOKEN(LSS);
        }
        else if(CUR_TOKEN_IS(GTR)) {
            PARSE_TOKEN(GTR);
        }
        else if(CUR_TOKEN_IS(LEQ)) {
            PARSE_TOKEN(LEQ);
        }
        else if(CUR_TOKEN_IS(GEQ)) {
            PARSE_TOKEN(GEQ);
        }
        else break;
        if(isExp()) {
            PARSE(son, AddExp);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseEqExp(EqExp* root) {
    if(isExp()) {
        PARSE(son, RelExp);
    }
    else return false;
    while(index < token_stream.size()) {
        if(CUR_TOKEN_IS(EQL)) {
            PARSE_TOKEN(EQL);
        }
        else if(CUR_TOKEN_IS(NEQ)) {
            PARSE_TOKEN(NEQ);
        }
        else break;
        if(isExp()) {
            PARSE(son, RelExp);
        }
        else return false;
    }
    return true;
}

bool frontend::Parser::parseLAndExp(LAndExp* root) {
    if(isExp()) {
        PARSE(son, EqExp);
    }
    else return false;
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(AND)) {
            PARSE_TOKEN(AND);
            if(isExp()) {
                PARSE(son, LAndExp);
            }
            else return false;
        }
    }
    return true;
}

bool frontend::Parser::parseLOrExp(LOrExp* root) {
    if(isExp()) {
        PARSE(son, LAndExp);
    }
    else return false;
    if(index < token_stream.size()) {
        if(CUR_TOKEN_IS(OR)) {
            PARSE_TOKEN(OR);
            if(isExp()) {
                PARSE(son, LOrExp);
            }
            else return false;
        }
    }
    return true;
}

bool frontend::Parser::parseConstExp(ConstExp* root) {
    if(isExp()) {
        PARSE(son, AddExp);
    }
    else return false;
    return true;
}


void Parser::log(AstNode* node){
#ifdef DEBUG_PARSER
        std::cout << "in parse" << toString(node->type) << ", cur_token_type::" << toString(token_stream[index].type) << ", token_val::" << token_stream[index].value << '\n';
#endif
}
