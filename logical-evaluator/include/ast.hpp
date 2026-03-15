#pragma once

#include <tuple>
#include <vector>

#include "tokens.hpp"
#include "types.hpp"

// Read as X('Name', 'Token Name') -> ASTNode'Name', TokenType::'Token Name'
// Defines every single node type and their case. e.g. TokenType:NAME
#define _AST_NODES(X)               \
    X(Biconditional, BICONDITIONAL) \
    X(Conditional, CONDITIONAL)     \
    X(Or, OR)                       \
    X(Xor, XOR)                     \
    X(Xnor, XNOR)                   \
    X(Nor, NOR)                     \
    X(And, AND)                     \
    X(Nand, NAND)                   \
    X(NotPstfx, NOT_PSTFX)          \
    X(NotPrfx, NOT_PRFX)            \
    X(ConstantTrue, CONST_T)        \
    X(ConstantFalse, CONST_F)       \
    X(Variable, VARIABLE)

// Read as X('Name'). Used for special handling in ASTParse.
#define _AST_TERMINAL_NODES(X) \
    X(ConstantTrue)            \
    X(ConstantFalse)           \
    X(Variable)

// Defines the precedence list for all supported node types.
// Read as X('Name', 'Token Name', 'Next Name', 'Operation Type')
// Operation Type can be the following: (binary, unary_pstfx, unary_prfx)
#define _AST_PRECEDENCE_NODE_LIST(X)                     \
    X(Biconditional, BICONDITIONAL, Conditional, binary) \
    X(Conditional, CONDITIONAL, Or, binary)              \
    X(Or, OR, Xor, binary)                               \
    X(Xor, XOR, Xnor, binary)                            \
    X(Xnor, XNOR, Nor, binary)                           \
    X(Nor, NOR, And, binary)                             \
    X(And, AND, Nand, binary)                            \
    X(Nand, NAND, NotPstfx, binary)                      \
    X(NotPstfx, NOT_PSTFX, NotPrfx, unary_pstfx)         \
    X(NotPrfx, NOT_PRFX, Primary, unary_prfx)

// Defines the operation to be done for binary node types.
// Read as X('Name', 'Operation')
// Operation uses 'l' and 'r' to define the left
// and right side of an expression.
#define _AST_BINARY_NODE_OPS(X) \
    X(Biconditional, l == r)    \
    X(Conditional, !l || r)     \
    X(Or, l || r)               \
    X(Xor, l != r)              \
    X(Xnor, l == r)             \
    X(Nor, !(l || r))           \
    X(And, (l && r))            \
    X(Nand, !(l && r))

// Defines the operation to be done for special node types.
// Read as X('Name', 'Operation', 'Left is available', 'Right is available')
// Operation uses 'l' and 'r' to define the left
// and right side of an expression. Booleans are passed to determine if
// said operation supports a left or right-hand side. (Useful for unary -prfx, -postfx ops.)
#define _AST_SPEC_NODE_OPS(X)        \
    X(NotPrfx, !r, false, true)      \
    X(NotPstfx, !l, true, false)     \
    X(ConstantTrue, 1, false, false) \
    X(ConstantFalse, 1, false, false)

// Defines the formatting to be done for all supported node types.
// Read as X('Name', 'Left is available', 'Right is available').
// True and True gives you (LEFT OP RIGHT), and either one by itself or none
// will return the expression as side-by-side.
// e.g. True,False gives you LEFTOP
#define _AST_FORMAT_ENTRY(X)       \
    X(Biconditional, true, true)   \
    X(Conditional, true, true)     \
    X(Or, true, true)              \
    X(Xor, true, true)             \
    X(Xnor, true, true)            \
    X(Nor, true, true)             \
    X(And, true, true)             \
    X(Nand, true, true)            \
    X(NotPstfx, true, false)       \
    X(NotPrfx, false, true)        \
    X(ConstantTrue, false, false)  \
    X(ConstantFalse, false, false) \
    X(Variable, false, false)

//---------------------------------------------------------------------------------------------//

namespace lge
{

#define _LGE_AST_TEMPLATE(name, case) \
    struct ASTNode##name {            \
        i32 left = -1;                \
        i32 right = -1;               \
        i32 token_id = -1;            \
        i32 node_id = -1;             \
    };
_AST_NODES(_LGE_AST_TEMPLATE)

// Special-case. But fields are put in for
// compatibility reasons, it is not meant to be functional.
struct ASTNodePrimary {
    i32 left = -1;
    i32 right = -1;
    i32 token_id = -1;
    i32 node_id = -1;
};

#undef _LGE_AST_TEMPLATE

#define _LGE_AST_NAME(name, case) ASTNode##name,
using ASTNode = std::variant<_AST_NODES(_LGE_AST_NAME) ASTNodePrimary>;
#undef _LGE_AST_NAME

struct ASTTree {
    std::vector<u8> values{};

    // (Subexpression, Values) index in sorted order, by length,
    // then variables at leftmost sorted alphabetically.
    std::vector<std::pair<isize, isize>> columns{};
    std::vector<ASTNode> nodes{};
    std::vector<std::string> subexpressions{};
    isize varcount = 0;
};

//---------------------------------------------------------------------------------------------//

#define _AST_EVAL_BINARY_OPERATOR(name, op)                                \
    void operator()(ASTNode##name &node)                                   \
    {                                                                      \
        evaluate<[](u8 &result, u8 l, u8 r) { result = op; }, true, true>( \
            node.node_id, node.left, node.right                            \
        );                                                                 \
    }
#define _AST_EVAL_SPEC_OPERATOR(name, op, bl, br)                      \
    void operator()(ASTNode##name &node)                               \
    {                                                                  \
        evaluate<[](u8 &result, u8 l, u8 r) { result = op; }, bl, br>( \
            node.node_id, node.left, node.right                        \
        );                                                             \
    }

struct ASTNodeEvaluator {
    isize rcount = 0;
    std::vector<u8> &vector;    // Is compressed to unique elements.
    std::vector<isize> &remap;  // Maps nodes to compressed table rows
    std::vector<bool> &evaluated;

    template <auto lambda, bool el, bool er>
    void evaluate(isize id, isize left, isize right)
    {
        const isize start = remap[id] * rcount;
        const isize sl = [&] {
            if constexpr (el) {
                return remap[left] * rcount;
            } else {
                return 0;
            }
        }();
        const isize sr = [&] {
            if constexpr (er) {
                return remap[right] * rcount;
            } else {
                return 0;
            }
        }();
        if (evaluated[remap[id]]) {
            return;
        }
        for (isize i = 0; i < rcount; ++i) {
            u8 lval = 0;
            u8 rval = 0;
            if constexpr (el) {
                lval = vector[sl + i];
            }
            if constexpr (er) {
                rval = vector[sr + i];
            }
            lambda(vector[start + i], lval, rval);
        }
        evaluated[remap[id]] = true;
    }

    _AST_BINARY_NODE_OPS(_AST_EVAL_BINARY_OPERATOR)
    _AST_SPEC_NODE_OPS(_AST_EVAL_SPEC_OPERATOR)

    // NO-OP. Must be handled separately at start of evaluation.
    void operator()(ASTNodeVariable &node) {}

    // NO-OP. Special-case.
    void operator()(ASTNodePrimary &node) {}
};

#undef _AST_EVAL_SPEC_OPERATOR
#undef _AST_EVAL_BINARY_OPERATOR
#undef _AST_EVAL_BINARY_NODE_OPS
#undef _AST_SPEC_NODE_OPS

//---------------------------------------------------------------------------------------------//

#define _AST_FACTORY_CASE(name, case_name) \
    case TokenType::case_name: return ASTNode##name();
struct ASTNodeFactory {
    ASTNode create_node(TokenType ttype)
    {
        switch (ttype) {
            _AST_NODES(_AST_FACTORY_CASE)
            default: throw std::runtime_error("NODE_FCTRY_UNEXPECTED_TOKEN");
        }
    }
};
#undef _AST_FACTORY_CASE

//---------------------------------------------------------------------------------------------//

#define _AST_PARSE_OP(current, current_case, next, op_type)                                   \
    isize operator()(const ASTNode##current &node)                                            \
    {                                                                                         \
        return parse_##op_type<                                                               \
            TokenType::current_case, [] { return ASTNode##next{}; },                          \
            [](i32 l, i32 r, i32 tkid, i32 nid) { return ASTNode##current{l, r, tkid, nid}; } \
        >();                                                                                  \
    }
#define _AST_PARSE_TERMINAL(name)                                         \
    isize operator()(const ASTNode##name &node)                           \
    {                                                                     \
        const i32 n_id = nodes.size();                                    \
        nodes.push_back(ASTNode##name{-1, -1, i32(current_count), n_id}); \
        ++current_count;                                                  \
        return n_id;                                                      \
    }

struct ASTNodeParsing {
    std::vector<ASTNode> &nodes;
    std::vector<Token> &tokenlist;

    isize current_count = 0;

    _AST_PRECEDENCE_NODE_LIST(_AST_PARSE_OP)
    _AST_TERMINAL_NODES(_AST_PARSE_TERMINAL)

    isize operator()(const ASTNodePrimary &node)
    {
        static ASTNode root{ASTNodeBiconditional{}};
        static ASTNode cont{ASTNodeConstantTrue{}};
        static ASTNode conf{ASTNodeConstantFalse{}};
        static ASTNode var{ASTNodeVariable{}};

        if (current_count >= tokenlist.size()) {
            throw std::runtime_error("PARSE_ERR_UNEXPECTED_EOF");
        }
        const TokenType ctok = tokenlist[current_count].type;
        bool is_punctuator = false;
        bool is_open_punctuator = false;
        switch (ctok) {
            case TokenType::O_BRACE:
            case TokenType::O_BRACKET:
            case TokenType::O_PAREN: is_open_punctuator = true;
            case TokenType::C_BRACE:
            case TokenType::C_BRACKET:
            case TokenType::C_PAREN: is_punctuator = true; break;
            default: break;
        }
        if (is_open_punctuator) {
            ++current_count;
            isize node = std::visit(*this, root);

            /// NOTE: Checking not required. Lexer already guarantees
            /// each pair exists in the expression.
            ++current_count;
            return node;
        }
        switch (ctok) {
            case TokenType::CONST_F: return std::visit(*this, conf);
            case TokenType::CONST_T: return std::visit(*this, cont);
            case TokenType::VARIABLE: return std::visit(*this, var);
            default: throw std::runtime_error("PARSE_ERR_UNRECOGNIZED_TOKEN");
        }
    }

   private:
    template <TokenType ttype, auto next, auto current>
    isize parse_binary()
    {
        const static ASTNode next_node{next()};
        isize lhs = std::visit(*this, next_node);
        while (current_count < tokenlist.size() && tokenlist[current_count].type == ttype) {
            const isize tkid = current_count;
            ++current_count;
            isize rhs = std::visit(*this, next_node);
            nodes.push_back(current(lhs, rhs, tkid, nodes.size()));
            lhs = nodes.size() - 1;
        }
        return lhs;
    }

    template <TokenType ttype, auto next, auto current>
    isize parse_unary_pstfx()
    {
        const static ASTNode next_node{next()};
        isize lhs = std::visit(*this, next_node);
        while (current_count < tokenlist.size() && tokenlist[current_count].type == ttype) {
            const isize tkid = current_count;
            ++current_count;
            nodes.push_back(current(lhs, -1, tkid, nodes.size()));
            lhs = nodes.size() - 1;
        }
        return lhs;
    }

    template <TokenType ttype, auto next, auto current>
    isize parse_unary_prfx()
    {
        const static ASTNode next_node{next()};
        if (current_count < tokenlist.size() && tokenlist[current_count].type == ttype) {
            const isize tkid = current_count;
            ++current_count;
            isize rhs = parse_unary_prfx<ttype, next, current>();
            nodes.push_back(current(-1, rhs, tkid, nodes.size()));
            return nodes.size() - 1;
        }
        return std::visit(*this, next_node);
    }
};

#undef _AST_PARSE_OP
#undef _AST_PARSE_TERMINAL

//---------------------------------------------------------------------------------------------//

#define _AST_FORMAT_SIG(name, l, r)                                       \
    void operator()(ASTNode##name &node)                                  \
    {                                                                     \
        format<l, r>(node.token_id, node.node_id, node.left, node.right); \
    }

struct ASTNodeFormatter {
    std::vector<ASTNode> &nodes;
    std::vector<Token> &tokenlist;
    std::vector<std::string> &subexprs;

    template <bool el, bool er>
    void format(isize token_id, isize node_id, isize li, isize ri)
    {
        if constexpr (el) {
            if (subexprs[li].empty()) {
                std::visit(*this, nodes[li]);
            }
        }
        if constexpr (er) {
            if (subexprs[ri].empty()) {
                std::visit(*this, nodes[ri]);
            }
        }
        if constexpr (er && el) {
            const std::string &left = subexprs[li];
            const std::string &right = subexprs[ri];
            subexprs[node_id] = "(" + left + " " + tokenlist[token_id].data + " " + right + ")";
        } else if (er) {
            subexprs[node_id] = tokenlist[token_id].data + subexprs[ri];
        } else if (el) {
            subexprs[node_id] = subexprs[li] + tokenlist[token_id].data;
        } else {
            subexprs[node_id] = tokenlist[token_id].data;
        }
    }
    _AST_FORMAT_ENTRY(_AST_FORMAT_SIG)
    void operator()(ASTNodePrimary &node)
    {
        // No-op. Sole purpose is to centralize handling in parser.
    }
};

#undef _AST_FORMAT_ENTRY
#undef _AST_FORMAT_SIG

#define _AST_VISITOR(name, case)                                     \
    std::tuple<i32, i32, i32, i32> operator()(ASTNode##name &node)   \
    {                                                                \
        return {node.left, node.right, node.token_id, node.node_id}; \
    }
struct ASTNodeVisitor {
    _AST_NODES(_AST_VISITOR)

    // Special-case.
    std::tuple<i32, i32, i32, i32> operator()(ASTNodePrimary &node)
    {
        return {node.left, node.right, node.token_id, node.node_id};
    }
};

ASTTree get_ast(std::vector<Token> &tokens);
std::string get_formatted_ast(ASTTree &tree);

}  // namespace lge

#undef _AST_NODES
#undef _AST_TERMINAL_NODES
#undef _AST_SPEC_NODE_OPS