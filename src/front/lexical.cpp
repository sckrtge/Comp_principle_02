#include"front/lexical.h"

#include<map>
#include<cassert>
#include<string>

#define TODO assert(0 && "todo")

// #define DEBUG_DFA
// #define DEBUG_SCANNER

std::string frontend::toString(State s) {
    switch (s) {
    case State::Empty: return "Empty";
    case State::Ident: return "Ident";
    case State::IntLiteral: return "IntLiteral";
    case State::FloatLiteral: return "FloatLiteral";
    case State::op: return "op";
    default:
        assert(0 && "invalid State");
    }
    return "";
}

std::set<std::string> frontend::keywords= {
    "const", "int", "float", "if", "else", "while", "continue", "break", "return", "void"
};

frontend::DFA::DFA(): cur_state(frontend::State::Empty), cur_str() {}

frontend::DFA::~DFA() {}

bool isSymbolChar(char c) {
    return c == '+' || c == '-' || c == '*' || c == '/' || c == '%' ||
        c == '<' || c == '>' || c == ':' || c == '=' || c == ';' ||
        c == ',' || c == '(' || c == ')' || c == '[' || c == ']' ||
        c == '{' || c == '}' || c == '!' || c == '&' || c == '|';
}

bool isSymbolString(std::string s) {
    return s == "<=" || s == "==" || s == ">=" || s == "!=" || s == "&&" || s == "||";
}

bool isalldigit(char c)
{
    return std::isdigit(c) || c == 'x' || c == 'X' || c == 'b' || c == 'B' || (c >= 'a' && c <= 'f');
}

bool isempty(char c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t' || c == '\v' || c == '\f';
}

frontend::TokenType frontend::DFA::str2operator(const std::string &str) {
    return operatorMap.find(str)->second;
}

frontend::TokenType frontend::DFA::str2keyword(const std::string &str) {
    if(keywordMap.find(str) == keywordMap.end())
        return TokenType::IDENFR;
    return keywordMap.find(str)->second;
}

bool frontend::DFA::change_status(Token &buf, State state, std::string str, bool output=false, TokenType type=TokenType::IDENFR, std::string value="") {
    cur_state = state;
    cur_str = str;
    if(output) {
        buf.type = type;
        buf.value = value;
    }
    return output;
};


bool frontend::DFA::next(char input, Token& buf) {
#ifdef DEBUG_DFA
#include<iostream>
    std::cout << "in state [" << toString(cur_state) << "], input = \'" << input << "\', str = " << cur_str << "\t";
#endif
    std::string sinput(1,input);
    switch(cur_state) {
        case State::Empty: {
            if(isSymbolChar(input)) {
                return change_status(buf, State::op, sinput);
            }
            else if(std::isdigit(input)) {
                return change_status(buf, State::IntLiteral, sinput);
            }
            else if(input == '.') {
                return change_status(buf, State::FloatLiteral, sinput);
            }
            else if(std::isalpha(input)||input == '_') {
                return change_status(buf, State::Ident,sinput);
            }
            else if(isempty(input)) {
                return change_status(buf, State::Empty,sinput);
            }
            break;
        }
        case State::Ident: {
            if(isSymbolChar(input)) {
                return change_status(buf, State::op, sinput, true, str2keyword(cur_str), cur_str);
            }
            else if(std::isdigit(input)) {
                return change_status(buf, State::Ident, cur_str + sinput);
            }
            else if(input == '.') {
                return change_status(buf, State::FloatLiteral, sinput, true, str2keyword(cur_str), cur_str);
            }
            else if(std::isalpha(input)||input == '_') {
                return change_status(buf, State::Ident, cur_str + sinput);
            }
            else if(isempty(input)) {
                return change_status(buf, State::Empty, sinput, true, str2keyword(cur_str), cur_str);
            }
            break;
        }
        case State::IntLiteral: {
            if(isSymbolChar(input)) {
                return change_status(buf, State::op, sinput, true, TokenType::INTLTR, cur_str);
            }
            else if(isalldigit(input)) {
                return change_status(buf, State::IntLiteral, cur_str + sinput);
            }
            else if(input == '.') {
                return change_status(buf, State::FloatLiteral, cur_str + sinput);
            }
            else if(std::isalpha(input)||input == '_') {
                return change_status(buf, State::Ident, sinput, true, TokenType::INTLTR, cur_str);
            }
            else if(isempty(input)) {
                return change_status(buf, State::Empty, sinput, true, TokenType::INTLTR, cur_str);
            }
            break;
        }
        case State::FloatLiteral: {
            if(isSymbolChar(input)) {
                return change_status(buf, State::op, sinput, true, TokenType::FLOATLTR, cur_str);
            }
            else if(std::isdigit(input)) {
                return change_status(buf, State::FloatLiteral, cur_str + sinput);
            }
            else if(std::isalpha(input)||input == '_') {
                return change_status(buf, State::Ident, sinput, true, TokenType::FLOATLTR, cur_str);
            }
            else if(isempty(input)) {
                return change_status(buf, State::Empty, sinput, true, TokenType::FLOATLTR, cur_str);
            }
            break;
        }
        case State::op: {
            if(isSymbolChar(input)) {
                if(isSymbolString(cur_str + input))
                    return change_status(buf, State::op, cur_str + input);
                else
                    return change_status(buf, State::op, sinput, true, str2operator(cur_str), cur_str);
            }
            else if(std::isdigit(input)) {
                return change_status(buf, State::IntLiteral, sinput, true, str2operator(cur_str), cur_str);
            }
            else if(input == '.') {
                return change_status(buf, State::FloatLiteral, sinput, true, str2operator(cur_str), cur_str);
            }
            else if(std::isalpha(input)||input == '_') {
                return change_status(buf, State::Ident, sinput, true, str2operator(cur_str), cur_str);
            }
            else if(isempty(input)) {
                return change_status(buf, State::Empty, sinput, true, str2operator(cur_str), cur_str);
            }
            break;
        }
        default:
        assert(0&&"in DFA next: State type wrong!");
        return 0;
    }
    assert(0&&"in DFA next:input wrong!");
    return 0;
#ifdef DEBUG_DFA
    std::cout << "next state is [" << toString(cur_state) << "], next str = " << cur_str << "\t, ret = " << ret << std::endl;
#endif
}

void frontend::DFA::reset() {
    cur_state = State::Empty;
    cur_str = "";
}

frontend::Scanner::Scanner(std::string filename): fin(filename) {
    if(!fin.is_open()) {
        assert(0 && "in Scanner constructor, input file cannot open");
    }
}

frontend::Scanner::~Scanner() {
    fin.close();
}

std::string preprossing(std::istream &fin) {
    std::string code((std::istreambuf_iterator<char>(fin)),
                    std::istreambuf_iterator<char>());
    std::string output;
    
    enum State { NORMAL, LINE_COMMENT, BLOCK_COMMENT, STRING_LITERAL, CHAR_LITERAL };
    State state = NORMAL;
    
    for (size_t i = 0; i < code.size(); ++i) {
        char c = code[i];
        if (state == NORMAL) {
            if (c == '/' && i + 1 < code.size()) {
                if (code[i+1] == '/') {
                    state = LINE_COMMENT;
                    ++i; // 跳过第二个 '/'
                    continue;
                } else if (code[i+1] == '*') {
                    state = BLOCK_COMMENT;
                    ++i; // 跳过 '*'
                    continue;
                }
            }
            if (c == '"') { 
                state = STRING_LITERAL; 
            } else if (c == '\'') { 
                state = CHAR_LITERAL; 
            }
            output.push_back(c);
        }
        else if (state == LINE_COMMENT) {
            if (c == '\n') {
                state = NORMAL;
                output.push_back(c);
            }
            // 其他字符跳过
        }
        else if (state == BLOCK_COMMENT) {
            if (c == '*' && i + 1 < code.size() && code[i+1] == '/') {
                state = NORMAL;
                ++i; // 跳过 '/'
            }
            // 块注释内容不输出
        }
        else if (state == STRING_LITERAL) {
            output.push_back(c);
            if (c == '\\' && i + 1 < code.size()) {
                output.push_back(code[++i]);  // 处理转义字符
            } else if (c == '"') {
                state = NORMAL;
            }
        }
        else if (state == CHAR_LITERAL) {
            output.push_back(c);
            if (c == '\\' && i + 1 < code.size()) {
                output.push_back(code[++i]);
            } else if (c == '\'') {
                state = NORMAL;
            }
        }
    }
    
    return output;
}

std::vector<frontend::Token> frontend::Scanner::run() {
    std::vector<Token> tokens;
    DFA dfa;
    Token tk;
    dfa.reset();
    std::string remove_comment_s = preprossing(fin);
    remove_comment_s.push_back('\n');
    for(auto input: remove_comment_s) {
        if(dfa.next(input, tk)) {
            tokens.push_back(tk);
        }
    }
    return tokens;
#ifdef DEBUG_SCANNER
#include<iostream>
            std::cout << "token: " << toString(tk.type) << "\t" << tk.value << std::endl;
#endif
}