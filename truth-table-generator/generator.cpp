#include "generator.hpp"

/**
 * BUG: BROKEN MULTI-CHAR support.
 */
#include <format>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string_view>
#include <unordered_map>
#include <utility>

namespace ttg::detail
{

const std::unordered_map<std::string, Token> token_map = [] {
    std::unordered_map<std::string, Token> tmap = {};
    for (char c = 'A'; c <= 'Z'; ++c) {
        char maps[] = {c, char(c | 0x20), char('0' + (c - 'A'))};
        for (isize i = 0; i < 2 + (c - 'A' < 10); ++i) {
            char tdata[] = {maps[i], '\0'};
            tmap[tdata] = Token{
                .data = std::string(tdata),
                .is_terminal = true,
                .is_alphanumeric = true,
                .type = TokenType::UNKNOWN,  // Incomplete.
            };
        }
    }
    tmap["&"] = Token{.data = "&", .is_operation = true, .type = TokenType::AND};
    tmap["*"] = Token{.data = "*", .is_operation = true, .type = TokenType::AND};
    tmap["|"] = Token{.data = "|", .is_operation = true, .type = TokenType::OR};
    tmap["+"] = Token{.data = "+", .is_operation = true, .type = TokenType::OR};
    tmap["->"] = Token{.data = "->", .is_operation = true, .type = TokenType::CONDITIONAL};
    tmap["<->"] = Token{.data = "<->", .is_operation = true, .type = TokenType::BICONDITIONAL};
    tmap["~"] = Token{.data = "~", .is_operation = true, .type = TokenType::NOT_PREFIX};
    tmap["!"] = Token{.data = "!", .is_operation = true, .type = TokenType::NOT_PREFIX};
    tmap["\'"] = Token{.data = "\'", .is_operation = true, .type = TokenType::NOT_POSTFIX};
    tmap["^"] = Token{.data = "^", .is_operation = true, .type = TokenType::XOR};
    tmap["("] = Token{.data = "(", .is_parenthesis = true, .type = TokenType::OPEN_PARENTHESIS};
    tmap[")"] = Token{.data = ")", .is_parenthesis = true, .type = TokenType::CLOSED_PARENTHESIS};
    tmap[" "] = Token{.data = " ", .is_terminal = true, .type = TokenType::SEPARATOR};
    tmap["\n"] = Token{.data = "\n", .is_terminal = true, .type = TokenType::SEPARATOR};
    tmap["\t"] = Token{.data = "\t", .is_terminal = true, .type = TokenType::SEPARATOR};
    return tmap;
}();

i32 Parsers::parse_or()
{
    i32 lhs = parse_xor();
    while (token_list[tokens_consumed].type == TokenType::OR) {
        const int tid = tokens_consumed;
        ++tokens_consumed;
        i32 rhs = parse_xor();
        ast.push_back(Node{tid, lhs, rhs});
        lhs = ast.size() - 1;
    }
    return lhs;
}

i32 Parsers::parse_xor()
{
    i32 lhs = parse_and();
    while (token_list[tokens_consumed].type == TokenType::XOR) {
        const int tid = tokens_consumed;
        ++tokens_consumed;
        i32 rhs = parse_and();

        ast.push_back(Node{tid, lhs, rhs});
        lhs = ast.size() - 1;
    }
    return lhs;
}

i32 Parsers::parse_and()
{
    i32 lhs = parse_not_prefix();
    while (token_list[tokens_consumed].type == TokenType::AND) {
        const int tid = tokens_consumed;
        ++tokens_consumed;
        i32 rhs = parse_not_prefix();
        ast.push_back(Node{tid, lhs, rhs});
        lhs = ast.size() - 1;
    }
    return lhs;
}

i32 Parsers::parse_not_prefix()
{
    if (token_list[tokens_consumed].type == TokenType::NOT_PREFIX) {
        const int tid = tokens_consumed;
        ++tokens_consumed;
        i32 rhs = parse_not_prefix();
        ast.push_back(Node{tid, -1, rhs});
        return ast.size() - 1;
    }
    return parse_not_postfix();
}

i32 Parsers::parse_not_postfix()
{
    i32 lhs = parse_atom();
    while (token_list[tokens_consumed].type == TokenType::NOT_POSTFIX) {
        const int tid = tokens_consumed;
        ++tokens_consumed;
        ast.push_back(Node{tid, lhs, -1});
        lhs = ast.size() - 1;
    }
    return lhs;
}

i32 Parsers::parse_atom()
{
    if (tokens_consumed >= token_list.size()) {
        throw std::runtime_error("Parsing failure. Unexpected EOF.");
    }
    switch (token_list[tokens_consumed].type) {
        case TokenType::OPEN_PARENTHESIS: {
            ++tokens_consumed;
            const i32 expr = parse_or();
            if (token_list[tokens_consumed].type != TokenType::CLOSED_PARENTHESIS) {
                throw std::runtime_error("Parsing failure. Incomplete parenthesis. Expected ')'.");
            } else {
                ++tokens_consumed;
                return expr;
            }
            break;
        }
        case TokenType::CONSTANT_FALSE: [[fallthrough]];
        case TokenType::CONSTANT_TRUE: [[fallthrough]];
        case TokenType::VARIABLE:
            ast.push_back(Node{tokens_consumed, -1, -1});
            ++tokens_consumed;
            return ast.size() - 1;
        default: throw std::runtime_error("Parsing failure. Expected 'VAR' or 'PAREN'.");
    }
}

}  // namespace ttg::detail

namespace ttg
{

using namespace ttg::detail;
using TT = TokenType;

Table::Table(std::string_view expression)
{
    _run_lexer(expression);
    _run_parser();
}

void Table::set_expression(std::string_view expression)
{
    _run_lexer(expression);
    _run_parser();
}

void Table::evaluate_table()
{
    _run_evaluator();
}

void Table::_run_lexer(std::string_view expression)
{
    _token_list.clear();
    bool pvarmode = false;
    bool pmlenopmode = false;
    std::string pvarstr = "";
    std::string pmlenopstr = "";
    const auto handle_variable = [&] {
        if (pvarstr.size() == 1 && (pvarstr[0] == 'T' || pvarstr[0] == 'F')) {
            const TT ttype = pvarstr[0] == 'T' ? TT::CONSTANT_TRUE : TT::CONSTANT_FALSE;
            const Token token{
                .data = pvarstr[0] == 'T' ? "T" : "F",
                .is_terminal = true,
                .is_alphanumeric = true,
                .type = ttype
            };
            _token_list.push_back(std::move(token));
        } else {
            _token_list.push_back(
                Token{
                    .data = pvarstr,
                    .vcount = _varcount,  // Exclusive to variables.
                    .is_terminal = true,
                    .type = TT::VARIABLE
                }
            );
            ++_varcount;
        }
    };

    for (isize i = 0; i < expression.size();) {
        char chstr[] = {expression[i], '\0'};
        auto it = token_map.find(chstr);
        const bool pmlenop = chstr[0] == '-' || chstr[0] == '<' || chstr[0] == '>';
        if (it == token_map.end() && !pmlenop) {
            throw std::runtime_error("Unknown symbol.");
        }
        Token token = !pmlenop ? it->second : Token{};
        if (token.is_alphanumeric) {
            pvarmode = true;
            pvarstr.push_back(chstr[0]);
            ++i;
            continue;
        } else if (pvarmode) {  // !alphanumeric
            pvarmode = false;
            handle_variable();
            pvarstr.clear();
        }
        if (pmlenop) {
            pmlenopmode = true;
            pmlenopstr.push_back(chstr[0]);
            ++i;
            continue;
        } else if (pmlenopmode) {
            pmlenopmode = false;
            if (pmlenopstr == "->" || pmlenopstr == "<->") {
                _token_list.push_back(token_map.at(pmlenopstr));
                pmlenopstr.clear();
                continue;
            } else {
                throw std::runtime_error("Unknown symbol. Expected '->' or '<->'.");
            }
        }
        if (token.type == TT::SEPARATOR) {
            ++i;
            continue;
        }
        _token_list.push_back(token);
        ++i;
    }
    if (pvarmode) {
        handle_variable();
    }
    if (pmlenopmode) {
        throw std::runtime_error("Expected EOF.");
    }
}

void Table::_run_parser()
{
    _ast.clear();
    if (_token_list.empty()) {
        return;
    }
    i32 tk = 0;
    Parsers parsers{.ast = _ast, .token_list = _token_list, .tokens_consumed = tk};
    _root = parsers.parse_or();
    if (tk != _token_list.size()) {
        throw std::runtime_error("Parsing failure. Something went wrong.");
    }
}

void Table::_run_evaluator()
{
    _entries.clear();
    if (_varcount == 0) {
        return;
    } else {
        _entries = std::vector<std::vector<i8>>(1 << _varcount, std::vector<i8>(_ast.size(), -1));
        _expression_substr = std::vector<std::string>(_ast.size());
    }
    isize total_rows = 1 << _varcount;
    for (isize i = 0; i < _ast.size(); ++i) {
        _eval_recursor(i, total_rows);
    }
}

void Table::_eval_recursor(isize eval, u64 rows)
{
    if (_expression_substr[eval].size()) {
        return;
    }
    const bool has_left = _ast[eval].left > -1;
    const bool has_right = _ast[eval].right > -1;
    if (has_left) {
        _eval_recursor(_ast[eval].left, rows);
    }
    if (has_right) {
        _eval_recursor(_ast[eval].right, rows);
    }
    const Token token = _token_list[_ast[eval].token_id];
    switch (token.type) {
        case TokenType::AND:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = _entries[i][_ast[eval].left] & _entries[i][_ast[eval].right];
            }
            break;
        case TokenType::OR:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = _entries[i][_ast[eval].left] | _entries[i][_ast[eval].right];
            }
            break;
        case TokenType::XOR:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = _entries[i][_ast[eval].left] ^ _entries[i][_ast[eval].right];
            }
            break;
        case TokenType::NOT_PREFIX:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = !_entries[i][_ast[eval].right];
            }
            break;
        case TokenType::NOT_POSTFIX:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = !_entries[i][_ast[eval].left];
            }
            break;
        case TokenType::CONSTANT_TRUE:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = 1;
            }
            break;
        case TokenType::CONSTANT_FALSE:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = 0;
            }
            break;
        case TokenType::VARIABLE:
            for (u64 i = 0; i < rows; ++i) {
                _entries[i][eval] = (i >> token.vcount) & 1;
            }
            break;
        default: throw std::runtime_error("Invalid eval token. Expected operation or variable.");
    }
    std::string lstr{""}, rstr{""};
    if (has_left) {
        lstr = _expression_substr[_ast[eval].left];
    }
    if (has_right) {
        rstr = _expression_substr[_ast[eval].right];
    }
    switch ((has_left << 1) | has_right) {
        case 0: _expression_substr[eval] = token.data; break;
        case 1: _expression_substr[eval] = token.data + rstr; break;
        case 2: _expression_substr[eval] = lstr + token.data; break;
        case 3: _expression_substr[eval] = "(" + lstr + " " + token.data + " " + rstr + ")"; break;
    }
}

std::string Table::get_table()
{
    std::string table = "";
    std::vector<isize> subexprs(_expression_substr.size(), 0);
    std::iota(subexprs.begin(), subexprs.end(), 0);
    std::sort(subexprs.begin(), subexprs.end(), [this](auto a, auto b) {
        return _expression_substr[a].size() < _expression_substr[b].size();
    });
    for (auto i : subexprs) {
        table.append(
            std::format("{0:^{1}} ", _expression_substr[i], _expression_substr[i].size() + 2)
        );
    }
    table.append("\n");
    for (auto &row : _entries) {
        for (auto i : subexprs) {
            table.append(
                std::format(
                    "{0}{1:^{2}}{3} ", row[i] ? "\e[0;32m" : "\e[0;31m", row[i],
                    _expression_substr[i].size() + 2, "\e[0m"
                )
            );
        }
        table.append("\n");
    }
    return table;
}

}  // namespace ttg

int main()
{
    std::cout << "Enter boolean expression: ";
    std::string buffer{};
    std::getline(std::cin, buffer);
    ttg::Table table(buffer);
    table.evaluate_table();
    std::cout << table.get_table();
    return 0;
}
