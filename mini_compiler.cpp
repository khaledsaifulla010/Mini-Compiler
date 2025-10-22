#include <bits/stdc++.h>
using namespace std;

/* =========================
   TOKEN/Lexer (unchanged)
   ========================= */

enum class TokenType {
    END, IDENT, INT_LITERAL,
    KW_INT, KW_IF, KW_ELSE, KW_WHILE, KW_RETURN, KW_PRINT,
    PLUS, MINUS, MUL, DIV, ASSIGN,
    LPAREN, RPAREN, LBRACE, RBRACE, COMMA, SEMI,
    EQ, NEQ, LT, GT, LE, GE,
    UNKNOWN
};

struct Token {
    TokenType type;
    string lexeme;
    int line;
    int col;
};

string tokName(TokenType t) {
    switch(t){
        case TokenType::END: return "END";
        case TokenType::IDENT: return "IDENT";
        case TokenType::INT_LITERAL: return "INT_LITERAL";
        case TokenType::KW_INT: return "KW_INT";
        case TokenType::KW_IF: return "KW_IF";
        case TokenType::KW_ELSE: return "KW_ELSE";
        case TokenType::KW_WHILE: return "KW_WHILE";
        case TokenType::KW_RETURN: return "KW_RETURN";
        case TokenType::KW_PRINT: return "KW_PRINT";
        case TokenType::PLUS: return "PLUS";
        case TokenType::MINUS: return "MINUS";
        case TokenType::MUL: return "MUL";
        case TokenType::DIV: return "DIV";
        case TokenType::ASSIGN: return "ASSIGN";
        case TokenType::LPAREN: return "LPAREN";
        case TokenType::RPAREN: return "RPAREN";
        case TokenType::LBRACE: return "LBRACE";
        case TokenType::RBRACE: return "RBRACE";
        case TokenType::COMMA: return "COMMA";
        case TokenType::SEMI: return "SEMI";
        case TokenType::EQ: return "EQ";
        case TokenType::NEQ: return "NEQ";
        case TokenType::LT: return "LT";
        case TokenType::GT: return "GT";
        case TokenType::LE: return "LE";
        case TokenType::GE: return "GE";
        default: return "UNKNOWN";
    }
}

struct Lexer {
    string src;
    size_t pos = 0;
    int line = 1, col = 1;
    Lexer(const string &s): src(s) {}
    char peek(){ return pos < src.size() ? src[pos] : '\0'; }
    char get(){ if(pos>=src.size()) return '\0'; char c = src[pos++]; if(c=='\n'){ line++; col=1;} else col++; return c; }
    void unget(){ if(pos>0){ pos--; /*col approximate*/ } }
    bool isIdentStart(char c){ return isalpha((unsigned char)c) || c=='_'; }
    bool isIdentPart(char c){ return isalnum((unsigned char)c) || c=='_'; }

    Token next(){
        while(isspace((unsigned char)peek())) get();
        int tline = line, tcol = col;
        char c = peek();
        if(c=='\0') return {TokenType::END, "", tline, tcol};
        // identifiers/keywords
        if(isIdentStart(c)){
            string s;
            while(isIdentPart(peek())) s.push_back(get());
            if(s=="int") return {TokenType::KW_INT,s,tline,tcol};
            if(s=="if") return {TokenType::KW_IF,s,tline,tcol};
            if(s=="else") return {TokenType::KW_ELSE,s,tline,tcol};
            if(s=="while") return {TokenType::KW_WHILE,s,tline,tcol};
            if(s=="return") return {TokenType::KW_RETURN,s,tline,tcol};
            if(s=="print") return {TokenType::KW_PRINT,s,tline,tcol};
            return {TokenType::IDENT,s,tline,tcol};
        }
        // numbers
        if(isdigit((unsigned char)c)){
            string s;
            while(isdigit((unsigned char)peek())) s.push_back(get());
            return {TokenType::INT_LITERAL, s, tline, tcol};
        }
        // operators/punct
        c = get();
        switch(c){
            case '+': return {TokenType::PLUS, "+", tline,tcol};
            case '-': return {TokenType::MINUS, "-", tline,tcol};
            case '*': return {TokenType::MUL, "*", tline,tcol};
            case '/': return {TokenType::DIV, "/", tline,tcol};
            case '(' : return {TokenType::LPAREN,"(",tline,tcol};
            case ')' : return {TokenType::RPAREN,")",tline,tcol};
            case '{' : return {TokenType::LBRACE,"{",tline,tcol};
            case '}' : return {TokenType::RBRACE,"}",tline,tcol};
            case ',' : return {TokenType::COMMA,",",tline,tcol};
            case ';' : return {TokenType::SEMI,";",tline,tcol};
            case '=':
                if(peek()=='='){ get(); return {TokenType::EQ,"==",tline,tcol}; }
                return {TokenType::ASSIGN,"=",tline,tcol};
            case '!':
                if(peek()=='='){ get(); return {TokenType::NEQ,"!=",tline,tcol}; }
                break;
            case '<':
                if(peek()=='='){ get(); return {TokenType::LE,"<=",tline,tcol}; }
                return {TokenType::LT,"<",tline,tcol};
            case '>':
                if(peek()=='='){ get(); return {TokenType::GE,">=",tline,tcol}; }
                return {TokenType::GT,">",tline,tcol};
        }
        string s(1,c);
        return {TokenType::UNKNOWN, s, tline, tcol};
    }

    vector<Token> tokenizeAll(){
        vector<Token> out;
        Token tk;
        do { tk = next(); out.push_back(tk); } while(tk.type != TokenType::END);
        return out;
    }
};

/* =========================
   AST Nodes
   ========================= */

struct AST { virtual ~AST()=default; virtual void dump(int=0) const=0; };
using ASTPtr = shared_ptr<AST>;

struct Expr : AST {};
struct Stmt : AST {};

struct IntLit : Expr {
    int val;
    IntLit(int v): val(v) {}
    void dump(int indent=0) const override { cout<<string(indent,' ')<<"Int("<<val<<")\n"; }
};

struct VarRef : Expr {
    string name;
    VarRef(const string &n): name(n) {}
    void dump(int indent=0) const override { cout<<string(indent,' ')<<"Var("<<name<<")\n"; }
};

struct Binary : Expr {
    string op;
    ASTPtr left, right;
    Binary(const string &o, ASTPtr l, ASTPtr r): op(o), left(l), right(r) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Binary("<<op<<")\n";
        left->dump(indent+2);
        right->dump(indent+2);
    }
};

struct Block : Stmt {
    vector<shared_ptr<Stmt>> stmts;
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Block\n";
        for(auto &s: stmts) s->dump(indent+2);
    }
};

struct Decl : Stmt {
    vector<string> names;
    Decl(vector<string> n): names(move(n)) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Decl:";
        for(auto &nm:names) cout<<" "<<nm;
        cout<<"\n";
    }
};

struct Assign : Stmt {
    string name;
    ASTPtr expr;
    Assign(string n, ASTPtr e): name(move(n)), expr(e) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Assign("<<name<<")\n";
        expr->dump(indent+2);
    }
};

struct IfStmt : Stmt {
    ASTPtr cond; shared_ptr<Block> thenb; shared_ptr<Block> elseb;
    IfStmt(ASTPtr c, shared_ptr<Block> t, shared_ptr<Block> e): cond(c), thenb(t), elseb(e) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"If\n";
        cond->dump(indent+2);
        thenb->dump(indent+2);
        if(elseb) elseb->dump(indent+2);
    }
};

struct WhileStmt : Stmt {
    ASTPtr cond; shared_ptr<Block> body;
    WhileStmt(ASTPtr c, shared_ptr<Block> b): cond(c), body(b) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"While\n";
        cond->dump(indent+2);
        body->dump(indent+2);
    }
};

struct PrintStmt : Stmt {
    ASTPtr expr;
    PrintStmt(ASTPtr e): expr(e) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Print\n";
        expr->dump(indent+2);
    }
};

struct ReturnStmt : Stmt {
    ASTPtr expr;
    ReturnStmt(ASTPtr e): expr(e) {}
    void dump(int indent=0) const override {
        cout<<string(indent,' ')<<"Return\n";
        if(expr) expr->dump(indent+2);
    }
};

struct Function {
    string name;
    vector<string> params;
    shared_ptr<Block> body;
    Function(string n, vector<string> p, shared_ptr<Block> b): name(n), params(p), body(b) {}
    void dump() const {
        cout<<"Function "<<name<<"(";
        for(size_t i=0;i<params.size();++i){ if(i) cout<<", "; cout<<params[i]; }
        cout<<")\n";
        body->dump(2);
    }
};

/* =========================
   Parser (recursive-descent)
   ========================= */

struct Parser {
    vector<Token> toks; size_t idx = 0;
    vector<string> errors;
    vector<shared_ptr<Stmt>> globals;
    vector<Function> functions;

    Parser(const vector<Token> &t): toks(t) {}
    Token cur(){ return idx < toks.size() ? toks[idx] : Token{TokenType::END,"",0,0}; }
    Token consume(){ return toks[idx++]; }
    bool match(TokenType tt){ if(cur().type==tt){ idx++; return true;} return false; }
    bool expect(TokenType tt, const string &msg){
        if(cur().type==tt){ idx++; return true; }
        errors.push_back("Expected " + tokName(tt) + " but got " + tokName(cur().type) + " at line " + to_string(cur().line));
        return false;
    }
    void parseProgram(){
        while(cur().type != TokenType::END){
            if(cur().type==TokenType::KW_INT){
                size_t save = idx;
                consume(); // int
                if(cur().type==TokenType::IDENT){
                    string name = cur().lexeme;
                    idx++;
                    if(cur().type==TokenType::LPAREN){
                        idx = save; parseFunction();
                    } else {
                        idx = save; parseDecl();
                    }
                } else {
                    errors.push_back("Expected identifier after int");
                    break;
                }
            } else {
                errors.push_back("Unexpected top-level token: " + cur().lexeme);
                break;
            }
        }
    }

    void parseFunction(){
        expect(TokenType::KW_INT, "function start");
        string fname = cur().lexeme; expect(TokenType::IDENT, "func name");
        expect(TokenType::LPAREN, "(");
        vector<string> params;
        if(cur().type!=TokenType::RPAREN){
            while(true){
                expect(TokenType::KW_INT, "param type");
                if(cur().type==TokenType::IDENT){ params.push_back(cur().lexeme); idx++; } else { errors.push_back("param name expected"); break; }
                if(match(TokenType::COMMA)) continue; else break;
            }
        }
        expect(TokenType::RPAREN, ")");
        auto body = parseBlock();
        functions.emplace_back(fname, params, body);
    }

    shared_ptr<Block> parseBlock(){
        expect(TokenType::LBRACE, "{");
        auto blk = make_shared<Block>();
        while(cur().type!=TokenType::RBRACE && cur().type!=TokenType::END){
            auto s = parseStmt();
            if(s) blk->stmts.push_back(s);
            else { /* try to recover: skip a token if stuck */ if(cur().type!=TokenType::END) idx++; }
        }
        expect(TokenType::RBRACE, "}");
        return blk;
    }

    shared_ptr<Stmt> parseStmt(){
        if(cur().type==TokenType::KW_INT){ parseDecl(); return nullptr; }
        if(cur().type==TokenType::LBRACE) return parseBlock();
        if(cur().type==TokenType::KW_IF){
            consume();
            expect(TokenType::LPAREN,"(");
            auto cond = parseExpr();
            expect(TokenType::RPAREN,")");
            auto thenb = parseBlock();
            shared_ptr<Block> elseb = nullptr;
            if(match(TokenType::KW_ELSE)) elseb = parseBlock();
            return make_shared<IfStmt>(cond, thenb, elseb);
        }
        if(match(TokenType::KW_WHILE)){
            expect(TokenType::LPAREN,"(");
            auto cond = parseExpr();
            expect(TokenType::RPAREN,")");
            auto body = parseBlock();
            return make_shared<WhileStmt>(cond, body);
        }
        if(match(TokenType::KW_PRINT)){
            expect(TokenType::LPAREN,"(");
            auto e = parseExpr();
            expect(TokenType::RPAREN,")");
            expect(TokenType::SEMI,";");
            return make_shared<PrintStmt>(e);
        }
        if(match(TokenType::KW_RETURN)){
            ASTPtr e = nullptr;
            if(cur().type!=TokenType::SEMI) e = parseExpr();
            expect(TokenType::SEMI,";");
            return make_shared<ReturnStmt>(e);
        }
        if(cur().type==TokenType::IDENT){
            string name = cur().lexeme; idx++;
            if(match(TokenType::ASSIGN)){
                auto e = parseExpr();
                expect(TokenType::SEMI,";");
                return make_shared<Assign>(name,e);
            } else {
                errors.push_back("Unexpected token after identifier in statement");
                while(cur().type!=TokenType::SEMI && cur().type!=TokenType::END) idx++;
                match(TokenType::SEMI);
                return nullptr;
            }
        }
        if(match(TokenType::SEMI)) return nullptr;
        errors.push_back("Unknown statement starting with " + cur().lexeme);
        return nullptr;
    }

    void parseDecl(){
        expect(TokenType::KW_INT,"decl int");
        vector<string> names;
        while(true){
            if(cur().type==TokenType::IDENT){ names.push_back(cur().lexeme); idx++; } else { errors.push_back("ident expected in decl"); break; }
            if(match(TokenType::COMMA)) continue; else break;
        }
        expect(TokenType::SEMI,";");
        globals.push_back(make_shared<Decl>(names));
    }

    // Expression grammar
    ASTPtr parseExpr(){ return parseEquality(); }
    ASTPtr parseEquality(){
        auto left = parseRelational();
        while(cur().type==TokenType::EQ || cur().type==TokenType::NEQ){
            string op = cur().lexeme; idx++;
            auto right = parseRelational();
            left = make_shared<Binary>(op,left,right);
        }
        return left;
    }
    ASTPtr parseRelational(){
        auto left = parseAdd();
        while(cur().type==TokenType::LT || cur().type==TokenType::GT || cur().type==TokenType::LE || cur().type==TokenType::GE){
            string op = cur().lexeme; idx++;
            auto right = parseAdd();
            left = make_shared<Binary>(op,left,right);
        }
        return left;
    }
    ASTPtr parseAdd(){
        auto left = parseMul();
        while(cur().type==TokenType::PLUS || cur().type==TokenType::MINUS){
            string op = cur().lexeme; idx++;
            auto right = parseMul();
            left = make_shared<Binary>(op,left,right);
        }
        return left;
    }
    ASTPtr parseMul(){
        auto left = parsePrimary();
        while(cur().type==TokenType::MUL || cur().type==TokenType::DIV){
            string op = cur().lexeme; idx++;
            auto right = parsePrimary();
            left = make_shared<Binary>(op,left,right);
        }
        return left;
    }
    ASTPtr parsePrimary(){
        if(cur().type==TokenType::INT_LITERAL){ int v = stoi(cur().lexeme); idx++; return make_shared<IntLit>(v); }
        if(cur().type==TokenType::IDENT){ string n = cur().lexeme; idx++; return make_shared<VarRef>(n); }
        if(match(TokenType::LPAREN)){ auto e = parseExpr(); expect(TokenType::RPAREN,")"); return e; }
        errors.push_back("Expected expression");
        return make_shared<IntLit>(0);
    }
};

/* =========================
   Semantic Analysis
   ========================= */

struct Symbol {
    string name; string type;
    bool isParam=false;
    Symbol(string n="", string t=""): name(n), type(t) {}
};

struct Semantic {
    vector<shared_ptr<Stmt>> globals;
    vector<Function> funcs;
    unordered_map<string, Symbol> globalSym;
    vector<string> errors;
    Semantic(const vector<shared_ptr<Stmt>> &g, const vector<Function> &f): globals(g), funcs(f){}
    void run(){
        for(auto &gs : globals){
            if(auto d = dynamic_pointer_cast<Decl>(gs)){
                for(auto &nm: d->names){
                    if(globalSym.count(nm)) errors.push_back("Redeclaration of global " + nm);
                    globalSym[nm] = Symbol(nm,"int");
                }
            }
        }
        for(auto &fn : funcs){
            unordered_map<string, Symbol> sym;
            for(auto &p: fn.params){
                if(sym.count(p)) errors.push_back("Duplicate param " + p + " in " + fn.name);
                sym[p] = Symbol(p,"int"); sym[p].isParam = true;
            }
            checkBlock(fn.body, sym);
        }
    }
    void checkBlock(shared_ptr<Block> b, unordered_map<string, Symbol> &sym){
        for(auto &st : b->stmts){
            if(auto d = dynamic_pointer_cast<Decl>(st)){
                for(auto &nm : d->names){
                    if(sym.count(nm)) errors.push_back("Redeclaration of " + nm);
                    sym[nm] = Symbol(nm,"int");
                }
            } else if(auto a = dynamic_pointer_cast<Assign>(st)){
                if(!sym.count(a->name) && !globalSym.count(a->name)) errors.push_back("Undeclared variable used: " + a->name);
                checkExpr(a->expr, sym);
            } else if(auto ifs = dynamic_pointer_cast<IfStmt>(st)){
                checkExpr(ifs->cond, sym);
                checkBlock(ifs->thenb, sym);
                if(ifs->elseb) checkBlock(ifs->elseb, sym);
            } else if(auto w = dynamic_pointer_cast<WhileStmt>(st)){
                checkExpr(w->cond, sym);
                checkBlock(w->body, sym);
            } else if(auto p = dynamic_pointer_cast<PrintStmt>(st)){
                checkExpr(p->expr, sym);
            } else if(auto r = dynamic_pointer_cast<ReturnStmt>(st)){
                if(r->expr) checkExpr(r->expr, sym);
            } else if(auto bl = dynamic_pointer_cast<Block>(st)){
                auto inner = sym; checkBlock(bl, inner);
            }
        }
    }
    void checkExpr(ASTPtr e, unordered_map<string, Symbol>& sym){
        if(!e) return;
        if(dynamic_pointer_cast<IntLit>(e)) return;
        if(auto v = dynamic_pointer_cast<VarRef>(e)){
            if(!sym.count(v->name) && !globalSym.count(v->name)) errors.push_back("Undeclared variable used: " + v->name);
            return;
        }
        if(auto b = dynamic_pointer_cast<Binary>(e)){
            checkExpr(b->left, sym);
            checkExpr(b->right, sym);
        }
    }
    void dump(){
        cout<<"-- Global Symbol Table --\n";
        for(auto &p: globalSym) cout<<p.first<<" : "<<p.second.type<<"\n";
    }
};

/* =========================
   Three-Address Code Generation & Assembly
   ========================= */

struct TAC {
    string op, a, b, c;
    TAC(string o, string aa="", string bb="", string cc=""): op(o), a(aa), b(bb), c(cc) {}
    string str() const {
        if(op=="LABEL") return a + ":";
        if(op=="GOTO") return "GOTO " + a;
        if(op=="IFZ") return "IFZ " + a + " GOTO " + b;
        if(op=="PRINT") return "PRINT " + a;
        if(op=="ASSIGN") return c + " = " + a;
        if(!c.empty()) return c + " = " + a + " " + op + " " + b;
        return op + " " + a;
    }
};

struct CodeGen {
    vector<TAC> code;
    int tmp = 0, lab = 0;
    vector<shared_ptr<Stmt>> globals;
    vector<Function> funcs;
    CodeGen(const vector<shared_ptr<Stmt>> &g, const vector<Function> &f): globals(g), funcs(f) {}
    string newTmp(){ return "t" + to_string(++tmp); }
    string newLabel(){ return "L" + to_string(++lab); }

    void generate(){
        for(auto &g : globals){
            if(auto d = dynamic_pointer_cast<Decl>(g)){
                for(auto &nm : d->names) code.emplace_back("ASSIGN","0","","" + nm);
            }
        }
        for(auto &fn : funcs){
            code.emplace_back("LABEL", fn.name);
            for(auto &s : fn.body->stmts) genStmt(s);
        }
    }

    string genExpr(ASTPtr e){
        if(auto i = dynamic_pointer_cast<IntLit>(e)){
            string t = newTmp();
            code.emplace_back("ASSIGN", to_string(i->val), "", t);
            return t;
        }
        if(auto v = dynamic_pointer_cast<VarRef>(e)) return v->name;
        if(auto b = dynamic_pointer_cast<Binary>(e)){
            string l = genExpr(b->left), r = genExpr(b->right);
            string t = newTmp();
            code.emplace_back(b->op, l, r, t);
            return t;
        }
        return "0";
    }

    void genStmt(shared_ptr<Stmt> s){
        if(auto d = dynamic_pointer_cast<Decl>(s)){
            for(auto &nm : d->names) code.emplace_back("ASSIGN","0","","" + nm);
        } else if(auto as = dynamic_pointer_cast<Assign>(s)){
            string r = genExpr(as->expr);
            code.emplace_back("ASSIGN", r, "", as->name);
        } else if(auto p = dynamic_pointer_cast<PrintStmt>(s)){
            string v = genExpr(p->expr);
            code.emplace_back("PRINT", v, "", "");
        } else if(auto ifs = dynamic_pointer_cast<IfStmt>(s)){
            string cond = genExpr(ifs->cond);
            string lelse = newLabel();
            string lend = newLabel();
            code.emplace_back("IFZ", cond, lelse, "");
            for(auto &st : ifs->thenb->stmts) genStmt(st);
            code.emplace_back("GOTO", lend, "", "");
            code.emplace_back("LABEL", lelse, "", "");
            if(ifs->elseb) for(auto &st : ifs->elseb->stmts) genStmt(st);
            code.emplace_back("LABEL", lend, "", "");
        } else if(auto w = dynamic_pointer_cast<WhileStmt>(s)){
            string lb = newLabel(), le = newLabel();
            code.emplace_back("LABEL", lb, "", "");
            string cond = genExpr(w->cond);
            code.emplace_back("IFZ", cond, le, "");
            for(auto &st : w->body->stmts) genStmt(st);
            code.emplace_back("GOTO", lb, "", "");
            code.emplace_back("LABEL", le, "", "");
        } else if(auto r = dynamic_pointer_cast<ReturnStmt>(s)){
            if(r->expr){ string v = genExpr(r->expr); code.emplace_back("ASSIGN", v, "", "RET"); }
            code.emplace_back("GOTO", "ENDFUNC", "", "");
        } else if(auto bl = dynamic_pointer_cast<Block>(s)){
            for(auto &st : bl->stmts) genStmt(st);
        }
    }

    void dumpTAC(ostream &out){
        out<<"-- Three Address Code --\n";
        for(auto &t : code) out<<t.str()<<"\n";
    }

    void dumpAsm(ostream &out){
        out<<"\n-- Pseudo Assembly --\n";
        for(auto &t : code){
            if(t.op=="LABEL") out<<t.a<<":\n";
            else if(t.op=="GOTO") out<<"    JMP "<<t.a<<"\n";
            else if(t.op=="IFZ"){
                out<<"    CMP "<<t.a<<", 0\n";
                out<<"    JE "<<t.b<<"\n";
            } else if(t.op=="PRINT") out<<"    PRINT "<<t.a<<"\n";
            else if(t.op=="ASSIGN") out<<"    MOV "<<t.c<<", "<<t.a<<"\n";
            else {
                string opcode;
                if(t.op=="+") opcode="ADD";
                else if(t.op=="-") opcode="SUB";
                else if(t.op=="*") opcode="MUL";
                else if(t.op=="/") opcode="DIV";
                else opcode=t.op;
                if(opcode=="CMP"){
                    out<<"    CMP "<<t.a<<", "<<t.b<<"\n";
                    out<<"    SET_OP "<<t.op<<" -> "<<t.c<<"\n";
                } else {
                    out<<"    "<<opcode<<" "<<t.c<<", "<<t.a<<", "<<t.b<<"\n";
                }
            }
        }
    }
};

/* =========================
   Utility: read from stdin or file
   ========================= */

string readFromStdinUntilEOF(){
    string line, all;
    // read until EOF
    while(true){
        if(!std::getline(cin, line)) break;
        all += line;
        all.push_back('\n');
    }
    return all;
}

string readFile(const string &fname){
    ifstream in(fname);
    if(!in) return "";
    stringstream ss; ss<<in.rdbuf(); return ss.str();
}

/* =========================
   Main (interactive prompt + capture output)
   ========================= */

int main(int argc, char** argv){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    // If filename provided, read from file; otherwise interactive prompt
    string src;
    if(argc >= 2){
        src = readFile(argv[1]);
        if(src.empty()){
            cerr << "Cannot read file: " << argv[1] << "\n";
            return 1;
        }
    } else {
        cout << "Please give me the input (finish with Ctrl+Z then Enter on Windows, Ctrl+D on Linux):\n";
        // Read all lines until EOF entered by user
        src = readFromStdinUntilEOF();
        if(src.empty()){
            cout << "No input received. Exiting.\n";
            return 0;
        }
    }
    ostringstream capture;
    streambuf *old_buf = cout.rdbuf(capture.rdbuf());

    // 1. Lexing
    Lexer lexer(src);
    auto tokens = lexer.tokenizeAll();
    capture << "-- Tokens --\n";
    for(auto &t: tokens){
        capture << t.line << ":" << t.col << " " << tokName(t.type) << " '" << t.lexeme << "'\n";
    }

    // 2. Parsing
    Parser parser(tokens);
    parser.parseProgram();
    if(!parser.errors.empty()){
        capture << "\n-- Parser Errors --\n";
        for(auto &e: parser.errors) capture << e << "\n";
    }

    capture << "\n-- Global Declarations --\n";
    for(auto &g: parser.globals) g->dump(2);
    capture << "\n-- Functions Parsed --\n";
    for(auto &f: parser.functions) f.dump();

    // 3. Semantic
    Semantic sem(parser.globals, parser.functions);
    sem.run();
    if(!sem.errors.empty()){
        capture << "\n-- Semantic Errors/Warnings --\n";
        for(auto &e: sem.errors) capture << e << "\n";
    }
    sem.dump();

    // 4. TAC
    CodeGen cg(parser.globals, parser.functions);
    cg.generate();
    capture << "\n";
    cg.dumpTAC(capture);

    // 5. Pseudo-Assembly
    cg.dumpAsm(capture);

    // restore cout
    cout.rdbuf(old_buf);

    // Print header + captured output
    cout << "\nThe Output is\n\n";
    cout << capture.str() << "\n";

    return 0;
}

