#include "lexer.hpp"

#include <cctype>
#include <span>
#include <stack>
#include <stdexcept>
#include <utility>

#include "tokens.hpp"

namespace
{

using namespace lge;

/**
 * @brief
 * Collapses whitespace, merges alphanumeric
 * letters, distinguishes special characters.
 */
std::vector<Token> lexer_pretokenizer(std::string_view expression)
{
    std::vector<Token> tokens{};
    std::string buffer{};
    i32 mode = 0;
    for (auto ch : expression) {
        if (std::isalnum(ch) || ch == '_') {  // HAS ALNUM
            if (mode == 2) {     // FROM WHITESPACE
                Token tk{.type = TokenType::INDETERMINATE_WHITE, .data = " "};
                tokens.push_back(tk);
            }
            buffer.push_back(ch);
            mode = 1;
            continue;
        } else if (mode == 1) {  // FROM ALNUM, HAS NON-ALNUM
            Token tk{.type = TokenType::INDETERMINATE_ALPHA, .data = buffer};
            tokens.push_back(std::move(tk));
            buffer.clear();
        }
        if (std::isspace(ch)) {  // HAS WHITESPACE
            mode = 2;
            continue;
        } else {                 // GENSPEC CHAR
            if (mode == 2) {     // FROM WHITESPACE
                Token tk{.type = TokenType::INDETERMINATE_WHITE, .data = " "};
                tokens.push_back(tk);
            }
            buffer.push_back(ch);
            Token tk{.type = TokenType::INDETERMINATE_SPEC, .data = buffer};
            tokens.push_back(std::move(tk));
            buffer.pop_back();
            mode = 0;
        }
    }
    switch (mode) {
        case 1: {
            Token tk{.type = TokenType::INDETERMINATE_ALPHA, .data = buffer};
            tokens.push_back(std::move(tk));
            break;
        }
        case 2: {
            Token tk{.type = TokenType::INDETERMINATE_WHITE, .data = " "};
            tokens.push_back(std::move(tk));
            break;
        }
        default: break;
    }
    tokens.push_back(Token{.type = TokenType::END_OF_FILE});
    return tokens;
}

/**
 * @brief
 * Finds punctuators. Must be called
 * immediately after the pretokenizer.
 */
void lexer_set_punctuators(std::span<Token> pretokenized)
{
    static const TokenMap &tmap = TokenMap::get_instance();
    static const std::unordered_map<TokenType, TokenType> pairs = [] {
        std::unordered_map<TokenType, TokenType> pmap{};
        pmap[TokenType::O_BRACE] = TokenType::C_BRACE;
        pmap[TokenType::O_PAREN] = TokenType::C_PAREN;
        pmap[TokenType::O_BRACKET] = TokenType::C_BRACKET;
        pmap[TokenType::C_BRACE] = TokenType::O_BRACE;
        pmap[TokenType::C_PAREN] = TokenType::O_PAREN;
        pmap[TokenType::C_BRACKET] = TokenType::O_BRACKET;
        return pmap;
    }();
    std::stack<TokenType> punctuators = {};

    for (auto &token : pretokenized) {
        const TokenType ttype = tmap.find(token.data);
        bool is_open = false;
        const auto match = pairs.find(ttype);
        if (match == pairs.end()) {
            continue;
        }
        switch (ttype) {
            case TokenType::O_BRACE: [[fallthrough]];
            case TokenType::O_BRACKET: [[fallthrough]];
            case TokenType::O_PAREN: is_open = true; break;
            default: break;
        }
        if (is_open) {
            punctuators.push(ttype);
        } else if (punctuators.empty() || punctuators.top() != match->second) {
            throw std::runtime_error("LEXING_ERR_UNEXPECTED_CLOSING_PUNCTUATOR");
        } else {
            punctuators.pop();
        }
        token.type = ttype;
    }
    if (!punctuators.empty()) {
        throw std::runtime_error("LEXING_ERR_EXPECTED_CLOSING_PUNCTUATOR");
    }
}

/**
 * @brief
 * Identifies and merges special token types.
 */
void lexer_identifier(std::span<Token> tokens)
{
    // EOF token is required to flush the stream at the end.
    static const TokenMap &tmap = TokenMap::get_instance();
    for (isize i = 0, j = 0; i < tokens.size();) {
        const Token &token = tokens[i];
        if (token.type == TokenType::INDETERMINATE_SPEC) {
            ++i;  // Extend window.
            continue;
        }
        const isize window_size = i - j;
        if (window_size == 0) {
            j = ++i; 
            continue;
        }

        // Merge tokens.
        std::string ndata{};
        for (isize k = j; k < i; ++k) {
            ndata.append(tokens[k].data);
        }
        const TokenType match = tmap.find(ndata);
        if (match == TokenType::NONE) {
            throw std::runtime_error("LEX_ERR_UNRECOGNIZED_TOKEN");
        }
        tokens[j].type = match;
        tokens[j].data = ndata;
        for (isize k = j + 1; k < i; ++k) {
            tokens[k].type = TokenType::INDETERMINATE_DISCARD;
        }
        j = ++i;
    }
}

/**
 * @brief
 * Identifies alphanumeric token types or sets them as variables.
 */
void lexer_set_variables(std::span<Token> tokens)
{
    static const TokenMap &tmap = TokenMap::get_instance();
    for (auto &token : tokens) {
        if (token.type != TokenType::INDETERMINATE_ALPHA) {
            continue;
        }
        const TokenType ttype = tmap.find(token.data);
        if (ttype == TokenType::NONE) {
            token.type = TokenType::VARIABLE;
            continue;
        }
        token.type = ttype;
    }
}

void lexer_discard_remainders(std::vector<Token> &tokens)
{
    isize j = 0;
    for (isize i = 0; i < tokens.size(); ++i) {
        const Token &token = tokens[i];
        switch (token.type) {
            case TokenType::INDETERMINATE_WHITE:
            case TokenType::INDETERMINATE_DISCARD:
            case TokenType::END_OF_FILE: break;
            default:
                if (i != j) {
                    tokens[j] = std::move(tokens[i]);
                }
                ++j;
                break;
        }
    }
    tokens.resize(j);
}

}  // namespace

namespace lge
{

std::vector<Token> run_lexer(std::string_view expression)
{
    static const TokenMap &tmap = TokenMap::get_instance();
    std::vector<Token> tokens = lexer_pretokenizer(expression);
    lexer_set_punctuators(tokens);
    lexer_identifier(tokens);
    lexer_set_variables(tokens);
    lexer_discard_remainders(tokens);
    return tokens;
}

}  // namespace lge