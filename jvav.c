#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

typedef enum { V_VOID, V_INT, V_CHAR, V_FLOAT, V_DOUBLE, V_STR } Type;

typedef struct { Type type; double num; char *str; } Value;

typedef struct Expr Expr;
typedef struct Stmt Stmt;

typedef enum { EX_NUM, EX_STR, EX_VAR, EX_BIN, EX_UN, EX_CALL, EX_ASSIGN } ExprKind;

struct Expr {
    ExprKind kind;
    Type type;
    double num;
    char *str;
    char *name;
    int op;
    int post;
    int line;
    Expr *left, *right;
    Expr **args;
    int nargs, argcap;
};

typedef enum { S_MARKER, S_DECL, S_EXPR, S_IF, S_FOR, S_WHILE, S_RETURN, S_PRINT, S_READ, S_BLOCK } StmtKind;

struct Stmt {
    StmtKind kind;
    Type type;
    int line;
    char *name;
    Expr *e1, *e2, *e3;
    Stmt *s1, *s2;
    Stmt *next;
};

typedef struct Func {
    char *name;
    Type ret;
    int nparams;
    char **pnames;
    Type *ptypes;
    Stmt *body;
    struct Func *next;
} Func;

static Func *gfuncs;

typedef enum { T_EOF, T_IDENT, T_NUMBER, T_STRING, T_OP, T_PUNCT } TokKind;

typedef struct { int type; char text[512]; double num; size_t start; } Token;

typedef struct { const char *src; size_t len, pos; Token cur, nxt; } Parser;

typedef enum { CTRL_NORMAL, CTRL_RET } Ctrl;

typedef struct { int ctrl; Value value; } Result;

typedef struct { char *name; Type type; double num; char *str; int depth; } Var;

static Var *vars;
static int nvar, capvar, scope_depth;

static int startswith(const char *s, const char *p) {
    return strncmp(s, p, strlen(p)) == 0;
}

static int endswith(const char *s, const char *p) {
    size_t ls = strlen(s), lp = strlen(p);
    return ls >= lp && strcmp(s + ls - lp, p) == 0;
}

static int eq_ci(const char *a, const char *b) {
    while (*a && *b) {
        if (tolower((unsigned char)*a) != tolower((unsigned char)*b)) return 0;
        a++; b++;
    }
    return *a == 0 && *b == 0;
}

static int line_of(const char *src, size_t pos) {
    int line = 1;
    for (size_t i = 0; i < pos && src[i]; i++)
        if (src[i] == '\n') line++;
    return line;
}

static void java_err(const char *cls, const char *msg, int line) {
    fprintf(stderr, "Exception in thread \"main\" JvavMmLang.%s: %s\n", cls, msg);
    fprintf(stderr, "\tat JvavMmLang.%s(JvavMmLang.java:%d)\n", cls, line);
}

static void perr(Parser *p, const char *cls, const char *msg) {
    java_err(cls, msg, line_of(p->src, p->cur.start));
    exit(1);
}

static void rerr(const char *cls, const char *msg, int line) {
    java_err(cls, msg, line);
    exit(1);
}

static void push_scope(void) { scope_depth++; }

static void pop_scope(void) {
    int j = 0;
    for (int i = 0; i < nvar; i++)
        if (vars[i].depth != scope_depth) vars[j++] = vars[i];
    nvar = j;
    if (scope_depth > 0) scope_depth--;
}

static Var *add_var(const char *name, Type t) {
    if (nvar == capvar) {
        capvar = capvar ? capvar * 2 : 16;
        vars = realloc(vars, sizeof(Var) * capvar);
    }
    Var *v = &vars[nvar++];
    v->name = strdup(name);
    v->type = t;
    v->num = 0;
    v->str = NULL;
    v->depth = scope_depth;
    return v;
}

static Var *find_var(const char *name) {
    for (int i = nvar - 1; i >= 0; i--)
        if (eq_ci(vars[i].name, name)) return &vars[i];
    return NULL;
}

static Token read_token(Parser *p) {
    Token t;
    t.type = T_EOF;
    t.text[0] = 0;
    t.num = 0;
    t.start = 0;
    for (;;) {
        while (p->pos < p->len &&
               (p->src[p->pos] == ' ' || p->src[p->pos] == '\t' ||
                p->src[p->pos] == '\n' || p->src[p->pos] == '\r'))
            p->pos++;
        if (p->pos >= p->len) return t;
        t.start = p->pos;
        char c = p->src[p->pos];
        if (c == '"') {
            p->pos++;
            int k = 0;
            while (p->pos < p->len && p->src[p->pos] != '"') {
                char d = p->src[p->pos++];
                if (d == '\\' && p->pos < p->len) {
                    char e = p->src[p->pos++];
                    switch (e) {
                        case 'n': d = '\n'; break;
                        case 't': d = '\t'; break;
                        case 'r': d = '\r'; break;
                        case '"': d = '"'; break;
                        case '\\': d = '\\'; break;
                        default: d = e;
                    }
                }
                t.text[k++] = d;
            }
            if (p->pos < p->len) p->pos++;
            t.text[k] = 0;
            t.type = T_STRING;
            return t;
        }
        if (isdigit((unsigned char)c) || (c == '.' && isdigit((unsigned char)p->src[p->pos + 1]))) {
            int k = 0;
            while (p->pos < p->len &&
                   (isdigit((unsigned char)p->src[p->pos]) || p->src[p->pos] == '.'))
                t.text[k++] = p->src[p->pos++];
            t.text[k] = 0;
            t.num = atof(t.text);
            t.type = T_NUMBER;
            return t;
        }
        if (isalpha((unsigned char)c) || c == '_') {
            int k = 0;
            while (p->pos < p->len &&
                   (isalnum((unsigned char)p->src[p->pos]) || p->src[p->pos] == '_'))
                t.text[k++] = p->src[p->pos++];
            t.text[k] = 0;
            t.type = T_IDENT;
            if (strcmp(t.text, "ThisIsAComment") == 0) {
                while (p->pos < p->len && p->src[p->pos] != '\n') p->pos++;
                continue;
            }
            return t;
        }
        char two[3] = { c, p->src[p->pos + 1], 0 };
        static const char *twos[] = { "++", "--", "==", "!=", ">=", "<=", "&&", "||" };
        int found = 0;
        for (int i = 0; i < 8; i++) {
            if (strcmp(two, twos[i]) == 0) {
                strcpy(t.text, twos[i]);
                found = 1;
                break;
            }
        }
        if (found) {
            p->pos += 2;
            t.type = T_OP;
            return t;
        }
        if (strchr("+-*/%=><!", c)) {
            t.text[0] = c;
            t.text[1] = 0;
            p->pos++;
            t.type = T_OP;
            return t;
        }
        if (strchr("(){};,", c)) {
            t.text[0] = c;
            t.text[1] = 0;
            p->pos++;
            t.type = T_PUNCT;
            return t;
        }
        {
            char mbuf[64];
            snprintf(mbuf, sizeof mbuf, "无法识别的字符 '%c'，已跳过", c);
            java_err("UnknownCharacter", mbuf, line_of(p->src, t.start));
        }
        p->pos++;
    }
}

static void parser_init(Parser *p, const char *src) {
    p->src = src;
    p->len = strlen(src);
    p->pos = 0;
    p->cur = read_token(p);
    p->nxt = read_token(p);
}

static void advance(Parser *p) {
    p->cur = p->nxt;
    p->nxt = read_token(p);
}

static int is_op(Parser *p, const char *s) {
    return p->cur.type == T_OP && strcmp(p->cur.text, s) == 0;
}

static int is_punct(Parser *p, char c) {
    return p->cur.type == T_PUNCT && p->cur.text[0] == c;
}

static int is_ident(Parser *p) { return p->cur.type == T_IDENT; }

static int is_kw(Parser *p, const char *s) {
    return p->cur.type == T_IDENT && strcmp(p->cur.text, s) == 0;
}

static const char *var_type_kws[] = {
    "TheTypeOfTheVariableIsAnIntegerWholeNumber",
    "TheTypeOfTheVariableIsASingleCharacter",
    "TheTypeOfTheVariableIsADecimalNumberWithFloatingPoint",
    "TheTypeOfTheVariableIsADecimalNumberWithDoublePrecision",
    "TheTypeOfTheVariableIsNothingAtAllAndHoldsNoValue",
};

static const char *ret_type_kws[] = {
    "TheReturnValueTypeOfTheFunctionIsAnIntegerWholeNumber",
    "TheReturnValueTypeOfTheFunctionIsASingleCharacter",
    "TheReturnValueTypeOfTheFunctionIsADecimalNumberWithFloatingPoint",
    "TheReturnValueTypeOfTheFunctionIsADecimalNumberWithDoublePrecision",
    "TheReturnValueTypeOfTheFunctionIsNothingAtAllAndReturnsNoValue",
};

static int var_type_from_kw(const char *s) {
    for (int i = 0; i < 5; i++)
        if (strcmp(s, var_type_kws[i]) == 0) return i + 1;
    return -1;
}

static int ret_type_from_kw(const char *s) {
    for (int i = 0; i < 5; i++)
        if (strcmp(s, ret_type_kws[i]) == 0) return i + 1;
    return -1;
}

static int param_type_from_kw(const char *s) {
    static const char *ords[] = {
        "First", "Second", "Third", "Fourth", "Fifth",
        "Sixth", "Seventh", "Eighth", "Ninth", "Tenth"
    };
    static const char *suffs[] = {
        "AnIntegerWholeNumber",
        "ASingleCharacter",
        "ADecimalNumberWithFloatingPoint",
        "ADecimalNumberWithDoublePrecision"
    };
    char buf[128];
    for (int o = 0; o < 10; o++) {
        for (int i = 0; i < 4; i++) {
            snprintf(buf, sizeof buf, "The%sParameterIs%sNamed", ords[o], suffs[i]);
            if (strcmp(s, buf) == 0) return i + 1;
        }
    }
    return -1;
}

static int opcode(const char *s) {
    if (s[0] == '=' && s[1] == '=') return 'E';
    if (s[0] == '!' && s[1] == '=') return 'N';
    if (s[0] == '>' && s[1] == '=') return 'G';
    if (s[0] == '<' && s[1] == '=') return 'L';
    if (s[0] == '&' && s[1] == '&') return 'A';
    if (s[0] == '|' && s[1] == '|') return 'O';
    if (s[0] == '+' && s[1] == '+') return 'P';
    if (s[0] == '-' && s[1] == '-') return 'D';
    return s[0];
}

static Expr *new_expr(void) { return calloc(1, sizeof(Expr)); }
static Stmt *new_stmt(void) { return calloc(1, sizeof(Stmt)); }

static Expr *mkbin(int op, Expr *l, Expr *r, int line) {
    Expr *e = new_expr();
    e->kind = EX_BIN;
    e->op = op;
    e->left = l;
    e->right = r;
    e->line = line;
    return e;
}

static Expr *parse_expr(Parser *p);
static Stmt *parse_stmt(Parser *p);
static Stmt *parse_block(Parser *p);

static Expr *parse_primary(Parser *p) {
    Expr *e = new_expr();
    e->line = line_of(p->src, p->cur.start);
    if (p->cur.type == T_NUMBER) {
        e->kind = EX_NUM;
        e->num = p->cur.num;
        e->type = (e->num == (double)(long)e->num) ? V_INT : V_DOUBLE;
        advance(p);
        return e;
    }
    if (p->cur.type == T_STRING) {
        e->kind = EX_STR;
        e->str = strdup(p->cur.text);
        advance(p);
        return e;
    }
    if (is_punct(p, '(')) {
        advance(p);
        e = parse_expr(p);
        if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "表达式内缺少右括号 )");
        advance(p);
        return e;
    }
    if (is_ident(p)) {
        char *name = strdup(p->cur.text);
        advance(p);
        if (is_punct(p, '(')) {
            advance(p);
            e->kind = EX_CALL;
            e->name = name;
            while (!is_punct(p, ')')) {
                if (p->cur.type == T_EOF) perr(p, "MissingRightParenthesis", "函数调用未闭合");
                if (e->nargs == e->argcap) {
                    e->argcap = e->argcap ? e->argcap * 2 : 8;
                    e->args = realloc(e->args, sizeof(Expr *) * e->argcap);
                }
                e->args[e->nargs++] = parse_expr(p);
                if (is_punct(p, ',')) advance(p);
                else break;
            }
            if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "函数调用缺少右括号 )");
            advance(p);
            return e;
        }
        e->kind = EX_VAR;
        e->name = name;
        return e;
    }
    perr(p, "SyntaxError", "无法解析该表达式");
    return e;
}

static Expr *parse_postfix(Parser *p) {
    Expr *e = parse_primary(p);
    while (is_op(p, "++") || is_op(p, "--")) {
        int op = p->cur.text[0] == '+' ? 'P' : 'D';
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        Expr *u = new_expr();
        u->kind = EX_UN;
        u->op = op;
        u->left = e;
        u->post = 1;
        u->line = ln;
        e = u;
    }
    return e;
}

static Expr *parse_unary(Parser *p) {
    if (is_op(p, "!")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        Expr *e = new_expr();
        e->kind = EX_UN;
        e->op = '!';
        e->left = parse_unary(p);
        e->line = ln;
        return e;
    }
    if (is_op(p, "++")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        Expr *e = new_expr();
        e->kind = EX_UN;
        e->op = 'P';
        e->left = parse_unary(p);
        e->line = ln;
        return e;
    }
    if (is_op(p, "--")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        Expr *e = new_expr();
        e->kind = EX_UN;
        e->op = 'D';
        e->left = parse_unary(p);
        e->line = ln;
        return e;
    }
    return parse_postfix(p);
}

static Expr *parse_mul(Parser *p) {
    Expr *e = parse_unary(p);
    while (is_op(p, "*") || is_op(p, "/") || is_op(p, "%")) {
        int op = opcode(p->cur.text);
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin(op, e, parse_unary(p), ln);
    }
    return e;
}

static Expr *parse_add(Parser *p) {
    Expr *e = parse_mul(p);
    while (is_op(p, "+") || is_op(p, "-")) {
        int op = opcode(p->cur.text);
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin(op, e, parse_mul(p), ln);
    }
    return e;
}

static Expr *parse_rel(Parser *p) {
    Expr *e = parse_add(p);
    while (is_op(p, ">") || is_op(p, "<") || is_op(p, ">=") || is_op(p, "<=")) {
        int op = opcode(p->cur.text);
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin(op, e, parse_add(p), ln);
    }
    return e;
}

static Expr *parse_eq(Parser *p) {
    Expr *e = parse_rel(p);
    while (is_op(p, "==") || is_op(p, "!=")) {
        int op = opcode(p->cur.text);
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin(op, e, parse_rel(p), ln);
    }
    return e;
}

static Expr *parse_and(Parser *p) {
    Expr *e = parse_eq(p);
    while (is_op(p, "&&")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin('A', e, parse_eq(p), ln);
    }
    return e;
}

static Expr *parse_or(Parser *p) {
    Expr *e = parse_and(p);
    while (is_op(p, "||")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        e = mkbin('O', e, parse_and(p), ln);
    }
    return e;
}

static Expr *parse_assign(Parser *p) {
    Expr *left = parse_or(p);
    if (is_op(p, "=")) {
        int ln = line_of(p->src, p->cur.start);
        advance(p);
        Expr *right = parse_assign(p);
        Expr *e = new_expr();
        e->kind = EX_ASSIGN;
        e->op = '=';
        e->left = left;
        e->right = right;
        e->line = ln;
        return e;
    }
    return left;
}

static Expr *parse_expr(Parser *p) { return parse_assign(p); }

static void expect_semicolon(Parser *p) {
    if (!is_punct(p, ';')) perr(p, "MissingSemicolon", "此处缺少分号 ;");
    advance(p);
    if (p->cur.type == T_IDENT && strcmp(p->cur.text, "ThisIsTheEndOfALineOfCode") != 0)
        fprintf(stderr, "编译提示：您是否忘记描述这行的结束？\n");
}

static Stmt *parse_stmts_until(Parser *p, char endc) {
    Stmt *head = NULL, **tail = &head;
    while (p->cur.type != T_EOF && !(is_punct(p, endc))) {
        Stmt *s = parse_stmt(p);
        *tail = s;
        tail = &s->next;
    }
    return head;
}

static Stmt *parse_block(Parser *p) {
    if (!is_punct(p, '{')) perr(p, "MissingLeftBrace", "此处应为代码块左花括号 {");
    advance(p);
    Stmt *head = parse_stmts_until(p, '}');
    if (!is_punct(p, '}')) perr(p, "MissingRightBrace", "代码块缺少右花括号 }");
    advance(p);
    Stmt *s = new_stmt();
    s->kind = S_BLOCK;
    s->s1 = head;
    return s;
}

static Stmt *parse_decl(Parser *p) {
    Stmt *s = new_stmt();
    s->kind = S_DECL;
    s->line = line_of(p->src, p->cur.start);
    s->type = (Type)var_type_from_kw(p->cur.text);
    advance(p);
    if (is_ident(p) && startswith(p->cur.text, "TheNameOfTheVariableThatStores") &&
        endswith(p->cur.text, "Is")) {
        advance(p);
        if (!is_ident(p)) perr(p, "MissingVariableName", "变量声明缺少变量名");
        s->name = strdup(p->cur.text);
        if (strlen(s->name) < 20)
            fprintf(stderr, "警告：变量名 \"%s\" 长度不足20字符，本解释器宽大处理。\n", s->name);
        advance(p);
    } else {
        perr(p, "CannotFindThisKeyword", "变量声明缺少 TheNameOfTheVariableThatStores...Is 描述");
    }
    if (is_kw(p, "AndTheInitialValueAssignedToTheVariableIs")) {
        advance(p);
        s->e1 = parse_expr(p);
    }
    expect_semicolon(p);
    return s;
}

static Stmt *parse_if(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "条件判断缺少左括号 (");
    advance(p);
    Expr *cond = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "条件判断缺少右括号 )");
    advance(p);
    if (!is_kw(p, "ThenExecuteTheFollowingBlockOfCode")) perr(p, "CannotFindThisKeyword", "条件判断缺少 ThenExecuteTheFollowingBlockOfCode");
    advance(p);
    Stmt *then_s = parse_block(p);
    Stmt *else_s = NULL;
    if (is_kw(p, "OtherwiseWhenTheConditionWasNotTrue")) {
        advance(p);
        if (!is_kw(p, "ThenExecuteThisOtherBlockOfCode")) perr(p, "CannotFindThisKeyword", "条件判断缺少 ThenExecuteThisOtherBlockOfCode");
        advance(p);
        else_s = parse_block(p);
    }
    Stmt *s = new_stmt();
    s->kind = S_IF;
    s->e1 = cond;
    s->s1 = then_s;
    s->s2 = else_s;
    return s;
}

static Stmt *parse_for(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "for 循环初始化缺少左括号 (");
    advance(p);
    Expr *init = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "for 循环初始化缺少右括号 )");
    advance(p);
    if (!is_kw(p, "AndItContinuesWhileTheConditionIsTrue")) perr(p, "CannotFindThisKeyword", "for 循环缺少 AndItContinuesWhileTheConditionIsTrue");
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "for 循环条件缺少左括号 (");
    advance(p);
    Expr *cond = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "for 循环条件缺少右括号 )");
    advance(p);
    if (!is_kw(p, "AndItIncrementsByOneOnEachIteration")) perr(p, "CannotFindThisKeyword", "for 循环缺少 AndItIncrementsByOneOnEachIteration");
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "for 循环增量缺少左括号 (");
    advance(p);
    Expr *incr = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "for 循环增量缺少右括号 )");
    advance(p);
    if (!is_kw(p, "ThenRepeatTheFollowingBlockOfCode")) perr(p, "CannotFindThisKeyword", "for 循环缺少 ThenRepeatTheFollowingBlockOfCode");
    advance(p);
    Stmt *body = parse_block(p);
    Stmt *s = new_stmt();
    s->kind = S_FOR;
    s->e1 = init;
    s->e2 = cond;
    s->e3 = incr;
    s->s1 = body;
    return s;
}

static Stmt *parse_while(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "while 循环缺少左括号 (");
    advance(p);
    Expr *cond = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "while 循环缺少右括号 )");
    advance(p);
    if (!is_kw(p, "ThenExecuteTheCodeInsideRepeatedly")) perr(p, "CannotFindThisKeyword", "while 循环缺少 ThenExecuteTheCodeInsideRepeatedly");
    advance(p);
    Stmt *body = parse_block(p);
    Stmt *s = new_stmt();
    s->kind = S_WHILE;
    s->e1 = cond;
    s->s1 = body;
    return s;
}

static Stmt *parse_return(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "return 语句缺少左括号 (");
    advance(p);
    Expr *e = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "return 语句缺少右括号 )");
    advance(p);
    expect_semicolon(p);
    Stmt *s = new_stmt();
    s->kind = S_RETURN;
    s->e1 = e;
    return s;
}

static Stmt *parse_print(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "print 语句缺少左括号 (");
    advance(p);
    Expr *e = parse_expr(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "print 语句缺少右括号 )");
    advance(p);
    expect_semicolon(p);
    Stmt *s = new_stmt();
    s->kind = S_PRINT;
    s->e1 = e;
    return s;
}

static Type fmt_type(const char *fmt) {
    if (strstr(fmt, "%lf")) return V_DOUBLE;
    if (strstr(fmt, "%f")) return V_FLOAT;
    if (strstr(fmt, "%d")) return V_INT;
    if (strstr(fmt, "%c")) return V_CHAR;
    return V_INT;
}

static Stmt *parse_read(Parser *p) {
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "read 语句缺少左括号 (");
    advance(p);
    if (p->cur.type != T_STRING) perr(p, "MissingFormatString", "read 语句缺少格式串，如 \"%d\"");
    char *fmt = strdup(p->cur.text);
    advance(p);
    if (!is_punct(p, ',')) perr(p, "MissingComma", "read 语句缺少逗号 ,");
    advance(p);
    if (!is_ident(p) || !startswith(p->cur.text, "TheAddressOfTheVariableThatStores"))
        perr(p, "CannotFindThisKeyword", "read 语句缺少 TheAddressOfTheVariableThatStores... 地址描述");
    Stmt *s = new_stmt();
    s->kind = S_READ;
    s->line = line_of(p->src, p->cur.start);
    s->type = fmt_type(fmt);
    s->name = strdup(p->cur.text + strlen("TheAddressOfTheVariableThatStores"));
    advance(p);
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "read 语句缺少右括号 )");
    advance(p);
    expect_semicolon(p);
    return s;
}

static Stmt *parse_stmt(Parser *p) {
    if (is_punct(p, ';')) {
        advance(p);
        Stmt *s = new_stmt();
        s->kind = S_MARKER;
        return s;
    }
    if (is_kw(p, "ThisIsTheEndOfALineOfCode")) {
        advance(p);
        if (is_punct(p, ';')) advance(p);
        Stmt *s = new_stmt();
        s->kind = S_MARKER;
        return s;
    }
    if (is_punct(p, '{')) return parse_block(p);
    if (is_ident(p)) {
        if (var_type_from_kw(p->cur.text) >= 0) return parse_decl(p);
        if (strcmp(p->cur.text, "IfTheFollowingConditionHappensToBeTrue") == 0) return parse_if(p);
        if (strcmp(p->cur.text, "TheLoopCounterStartsAtTheValue") == 0) return parse_for(p);
        if (strcmp(p->cur.text, "KeepRepeatingTheFollowingBlockWhileTheConditionHolds") == 0) return parse_while(p);
        if (strcmp(p->cur.text, "TheFunctionShallNowReturnTheFollowingValueBackToCaller") == 0) return parse_return(p);
        if (startswith(p->cur.text, "PrintTheGivenContentOntoTheConsoleScreenInReadableFormat")) return parse_print(p);
        if (startswith(p->cur.text, "ReadInputFromTheUserAndStoreItIntoTheGivenVariable")) return parse_read(p);
    }
    Stmt *s = new_stmt();
    s->kind = S_EXPR;
    s->e1 = parse_expr(p);
    expect_semicolon(p);
    return s;
}

static void parse_func(Parser *p, Func **list) {
    int ret = ret_type_from_kw(p->cur.text);
    if (ret < 0) perr(p, "CannotFindThisKeyword", "函数缺少返回值类型声明");
    advance(p);
    if (!is_ident(p)) perr(p, "MissingFunctionName", "函数缺少函数名");
    Func *f = calloc(1, sizeof(Func));
    f->ret = (Type)ret;
    f->name = strdup(p->cur.text);
    advance(p);
    if (!is_punct(p, '(')) perr(p, "MissingLeftParenthesis", "函数名后缺少左括号 (");
    advance(p);
    while (!is_punct(p, ')')) {
        int pt = param_type_from_kw(p->cur.text);
        if (pt < 0) perr(p, "CannotFindThisKeyword", "无效的参数声明");
        advance(p);
        if (!is_ident(p)) perr(p, "MissingParameterName", "参数缺少参数名");
        f->pnames = realloc(f->pnames, sizeof(char *) * (f->nparams + 1));
        f->ptypes = realloc(f->ptypes, sizeof(Type) * (f->nparams + 1));
        f->pnames[f->nparams] = strdup(p->cur.text);
        f->ptypes[f->nparams] = (Type)pt;
        f->nparams++;
        advance(p);
        if (is_punct(p, ',')) advance(p);
        else break;
    }
    if (!is_punct(p, ')')) perr(p, "MissingRightParenthesis", "参数列表缺少右括号 )");
    advance(p);
    if (is_kw(p, "ThenExecuteTheFollowingBody")) advance(p);
    if (!is_punct(p, '{')) perr(p, "MissingLeftBrace", "函数体缺少左花括号 {");
    advance(p);
    f->body = parse_stmts_until(p, '}');
    if (!is_punct(p, '}')) perr(p, "MissingRightBrace", "函数体缺少右花括号 }");
    advance(p);
    f->next = *list;
    *list = f;
}

static Func *parse_program(Parser *p) {
    Func *list = NULL;
    while (p->cur.type != T_EOF) {
        if (is_ident(p) && ret_type_from_kw(p->cur.text) >= 0) {
            parse_func(p, &list);
        } else {
            perr(p, "SyntaxError", "顶层只允许函数定义，且函数必须声明完整返回值类型");
        }
    }
    return list;
}

static Func *find_func(const char *name) {
    for (Func *f = gfuncs; f; f = f->next)
        if (strcmp(f->name, name) == 0) return f;
    return NULL;
}

static int is_truthy(Value v) {
    if (v.type == V_STR) return v.str && v.str[0];
    return v.num != 0;
}

static char *concat(Value a, Value b) {
    char ba[64], bb[64];
    char *ls, *rs;
    if (a.type == V_STR) ls = a.str ? a.str : "";
    else {
        if (a.num == (double)(long)a.num) snprintf(ba, sizeof ba, "%ld", (long)a.num);
        else snprintf(ba, sizeof ba, "%g", a.num);
        ls = ba;
    }
    if (b.type == V_STR) rs = b.str ? b.str : "";
    else {
        if (b.num == (double)(long)b.num) snprintf(bb, sizeof bb, "%ld", (long)b.num);
        else snprintf(bb, sizeof bb, "%g", b.num);
        rs = bb;
    }
    char *out = malloc(strlen(ls) + strlen(rs) + 1);
    strcpy(out, ls);
    strcat(out, rs);
    return out;
}

static Result exec_stmts(Stmt *s);
static Value eval_expr(Expr *e);

static Value eval_expr(Expr *e) {
    Value v;
    v.type = V_VOID;
    v.num = 0;
    v.str = NULL;
    if (!e) return v;
    switch (e->kind) {
        case EX_NUM:
            v.type = e->type;
            v.num = e->num;
            return v;
        case EX_STR:
            v.type = V_STR;
            v.str = e->str;
            return v;
        case EX_VAR: {
            Var *var = find_var(e->name);
            if (!var) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "未声明的变量 \"%s\"", e->name);
                rerr("VariableNotDeclared", mbuf, e->line);
            }
            v.type = var->type;
            v.num = var->num;
            if (var->str) v.str = var->str;
            return v;
        }
        case EX_ASSIGN: {
            Value r = eval_expr(e->right);
            if (e->left->kind != EX_VAR) rerr("InvalidAssignmentTarget", "赋值目标不是变量", e->line);
            Var *var = find_var(e->left->name);
            if (!var) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "未声明的变量 \"%s\"", e->left->name);
                rerr("VariableNotDeclared", mbuf, e->left->line);
            }
            var->num = r.num;
            if (var->str) free(var->str);
            var->str = r.str ? strdup(r.str) : NULL;
            return r;
        }
        case EX_BIN:
            if (e->op == 'A') {
                Value l = eval_expr(e->left);
                v.type = V_INT;
                v.num = is_truthy(l) && is_truthy(eval_expr(e->right)) ? 1 : 0;
                return v;
            }
            if (e->op == 'O') {
                Value l = eval_expr(e->left);
                v.type = V_INT;
                v.num = is_truthy(l) || is_truthy(eval_expr(e->right)) ? 1 : 0;
                return v;
            }
            {
                Value l = eval_expr(e->left);
                Value r = eval_expr(e->right);
                int any_str = l.type == V_STR || r.type == V_STR;
                double a = (l.type == V_STR) ? 0 : l.num;
                double b = (r.type == V_STR) ? 0 : r.num;
                if (any_str) {
                    if (e->op == '+') {
                        v.type = V_STR;
                        v.str = concat(l, r);
                        return v;
                    }
                    const char *ls = l.str ? l.str : "";
                    const char *rs = r.str ? r.str : "";
                    int c = 0;
                    switch (e->op) {
                        case 'E': c = strcmp(ls, rs) == 0; break;
                        case 'N': c = strcmp(ls, rs) != 0; break;
                        case '>': c = strcmp(ls, rs) > 0; break;
                        case '<': c = strcmp(ls, rs) < 0; break;
                        case 'G': c = strcmp(ls, rs) >= 0; break;
                        case 'L': c = strcmp(ls, rs) <= 0; break;
                    }
                    v.type = V_INT;
                    v.num = c;
                    return v;
                }
                switch (e->op) {
                    case '+':
                        v.type = (l.type == V_FLOAT || l.type == V_DOUBLE ||
                                  r.type == V_FLOAT || r.type == V_DOUBLE) ? V_DOUBLE : V_INT;
                        v.num = a + b;
                        return v;
                    case '-':
                        v.type = (l.type == V_FLOAT || l.type == V_DOUBLE ||
                                  r.type == V_FLOAT || r.type == V_DOUBLE) ? V_DOUBLE : V_INT;
                        v.num = a - b;
                        return v;
                    case '*':
                        v.type = (l.type == V_FLOAT || l.type == V_DOUBLE ||
                                  r.type == V_FLOAT || r.type == V_DOUBLE) ? V_DOUBLE : V_INT;
                        v.num = a * b;
                        return v;
                    case '/':
                        if (b == 0) rerr("ArithmeticException", "除以零，宇宙炸裂了", e->line);
                        v.type = (l.type == V_FLOAT || l.type == V_DOUBLE ||
                                  r.type == V_FLOAT || r.type == V_DOUBLE) ? V_DOUBLE : V_INT;
                        v.num = a / b;
                        return v;
                    case '%':
                        if (b == 0) rerr("ArithmeticException", "取模零，宇宙炸裂了", e->line);
                        v.type = V_INT;
                        v.num = (long)a % (long)b;
                        return v;
                    case 'E': v.type = V_INT; v.num = (a == b); return v;
                    case 'N': v.type = V_INT; v.num = (a != b); return v;
                    case '>': v.type = V_INT; v.num = (a > b); return v;
                    case '<': v.type = V_INT; v.num = (a < b); return v;
                    case 'G': v.type = V_INT; v.num = (a >= b); return v;
                    case 'L': v.type = V_INT; v.num = (a <= b); return v;
                }
            }
            return v;
        case EX_UN:
            if (e->op == '!') {
                v.type = V_INT;
                v.num = !is_truthy(eval_expr(e->left));
                return v;
            }
            if (e->op == 'P' || e->op == 'D') {
                if (e->left->kind != EX_VAR) rerr("InvalidAssignmentTarget", "自增自减只能作用于变量", e->line);
                Var *var = find_var(e->left->name);
                if (!var) {
                    char mbuf[160];
                    snprintf(mbuf, sizeof mbuf, "未声明的变量 \"%s\"", e->left->name);
                    rerr("VariableNotDeclared", mbuf, e->left->line);
                }
                double old = var->num;
                var->num = (e->op == 'P') ? old + 1 : old - 1;
                v.type = var->type;
                v.num = e->post ? old : var->num;
                return v;
            }
            return v;
        case EX_CALL: {
            Func *f = find_func(e->name);
            if (!f) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "调用了未定义的函数 \"%s\"", e->name);
                rerr("FunctionNotDefined", mbuf, e->line);
            }
            if (e->nargs != f->nparams) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "函数 \"%s\" 的参数数量不匹配", e->name);
                rerr("ArgumentCountMismatch", mbuf, e->line);
            }
            push_scope();
            for (int i = 0; i < f->nparams; i++) {
                Value a = eval_expr(e->args[i]);
                Var *var = add_var(f->pnames[i], f->ptypes[i]);
                var->num = a.num;
            }
            Result r = exec_stmts(f->body);
            pop_scope();
            if (r.ctrl == CTRL_RET && f->ret != V_VOID) return r.value;
            return v;
        }
    }
    return v;
}

static void print_value(Value v) {
    if (v.type == V_STR) {
        printf("%s\n", v.str ? v.str : "");
    } else if (v.type == V_CHAR) {
        printf("%c\n", (int)v.num);
    } else if (v.type == V_VOID) {
        printf("\n");
    } else {
        if (v.num == (double)(long)v.num) printf("%ld\n", (long)v.num);
        else printf("%g\n", v.num);
    }
}

static Result exec_stmt(Stmt *s);

static Result exec_stmts(Stmt *s) {
    Result r;
    r.ctrl = CTRL_NORMAL;
    r.value.type = V_VOID;
    r.value.num = 0;
    r.value.str = NULL;
    for (; s; s = s->next) {
        r = exec_stmt(s);
        if (r.ctrl == CTRL_RET) break;
    }
    return r;
}

static Result exec_stmt(Stmt *s) {
    Result r;
    r.ctrl = CTRL_NORMAL;
    r.value.type = V_VOID;
    r.value.num = 0;
    r.value.str = NULL;
    if (!s) return r;
    switch (s->kind) {
        case S_MARKER:
            return r;
        case S_EXPR:
            eval_expr(s->e1);
            return r;
        case S_DECL: {
            Var *old = find_var(s->name);
            if (old && old->depth == scope_depth) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "变量 \"%s\" 重复定义", s->name);
                rerr("VariableAlreadyDefined", mbuf, s->line);
            }
            Var *var = add_var(s->name, s->type);
            if (s->e1) {
                Value val = eval_expr(s->e1);
                var->num = val.num;
                if (val.str) {
                    if (var->str) free(var->str);
                    var->str = strdup(val.str);
                }
            }
            return r;
        }
        case S_IF: {
            Value c = eval_expr(s->e1);
            if (is_truthy(c)) return exec_stmt(s->s1);
            if (s->s2) return exec_stmt(s->s2);
            return r;
        }
        case S_FOR:
            eval_expr(s->e1);
            while (is_truthy(eval_expr(s->e2))) {
                Result b = exec_stmt(s->s1);
                if (b.ctrl == CTRL_RET) return b;
                eval_expr(s->e3);
            }
            return r;
        case S_WHILE:
            while (is_truthy(eval_expr(s->e1))) {
                Result b = exec_stmt(s->s1);
                if (b.ctrl == CTRL_RET) return b;
            }
            return r;
        case S_RETURN:
            r.ctrl = CTRL_RET;
            r.value = eval_expr(s->e1);
            return r;
        case S_PRINT: {
            Value val = eval_expr(s->e1);
            print_value(val);
            return r;
        }
        case S_READ: {
            Var *var = find_var(s->name);
            if (!var) {
                char mbuf[160];
                snprintf(mbuf, sizeof mbuf, "读取目标变量 \"%s\" 未声明", s->name);
                rerr("VariableNotDeclared", mbuf, s->line);
            }
            fflush(stdout);
            if (s->type == V_INT) {
                int x;
                if (scanf("%d", &x) != 1) x = 0;
                var->num = x;
            } else if (s->type == V_CHAR) {
                int c;
                do { c = getchar(); } while (c != EOF && isspace(c));
                var->num = (double)c;
            } else if (s->type == V_FLOAT) {
                float f;
                if (scanf("%f", &f) != 1) f = 0;
                var->num = f;
            } else {
                double d;
                if (scanf("%lf", &d) != 1) d = 0;
                var->num = d;
            }
            var->type = s->type;
            return r;
        }
        case S_BLOCK:
            push_scope();
            {
                Result b = exec_stmts(s->s1);
                pop_scope();
                return b;
            }
    }
    return r;
}

static char *read_all(FILE *fp) {
    size_t cap = 1 << 16, len = 0;
    char *buf = malloc(cap);
    int c;
    while ((c = fgetc(fp)) != EOF) {
        if (len + 1 >= cap) {
            cap *= 2;
            buf = realloc(buf, cap);
        }
        buf[len++] = (char)c;
    }
    buf[len] = 0;
    return buf;
}

int main(int argc, char **argv) {
    const char *fname = (argc > 1) ? argv[1] : NULL;
    FILE *fp = fname ? fopen(fname, "rb") : stdin;
    if (!fp) {
        char mbuf[160];
        snprintf(mbuf, sizeof mbuf, "无法打开文件：%s", fname);
        java_err("FileNotFoundException", mbuf, 1);
        return 1;
    }
    char *src = read_all(fp);
    if (fp != stdin) fclose(fp);

    Parser p;
    parser_init(&p, src);
    gfuncs = parse_program(&p);

    Func *entry = find_func("ThisIsTheFunctionThatStartsTheProgram");
    if (!entry) {
        java_err("EntryFunctionNotFound", "找不到入口函数 ThisIsTheFunctionThatStartsTheProgram", 1);
        return 1;
    }

    push_scope();
    Result r = exec_stmts(entry->body);
    pop_scope();

    if (r.ctrl == CTRL_RET && r.value.type != V_VOID) return (int)r.value.num;
    return 0;
}
