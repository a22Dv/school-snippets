#pragma once

#include <string>
#include <unordered_map>

#include "types.hpp"

namespace lge
{

enum class TokenType : u8 {
    NONE,
    END_OF_FILE,
    INDETERMINATE_DISCARD,
    INDETERMINATE_SPEC,
    INDETERMINATE_ALPHA,
    INDETERMINATE_WHITE,
    BICONDITIONAL,
    CONDITIONAL,
    OR,
    XOR,
    XNOR,
    NOR,
    AND,
    NAND,
    NOT_PSTFX,
    NOT_PRFX,
    O_BRACKET,
    C_BRACKET,
    O_PAREN,
    C_PAREN,
    O_BRACE,
    C_BRACE,
    CONST_T,
    CONST_F,
    VARIABLE,
};

struct Token {
    TokenType type;
    std::string data{};
};

class TokenMap
{
   public:
    static const TokenMap &get_instance()
    {
        static TokenMap map = {};
        return map;
    };
    TokenType find(const std::string &str) const
    {
        const auto it = _map.find(str);
        if (it == _map.end()) {
            return TokenType::NONE;
        }
        return it->second;
    }
    std::string get_name(TokenType type) const
    {
        const auto it = _name_map.find(type);
        if (it == _name_map.end()) {
            return "";
        }
        return it->second;
    }

   private:
    TokenMap()
    {
        /*
         * Casing is handled separately as
         * case-normalization is avoided to preserve
         * user preference in the final table.
         */
        _map["THEN"] = TokenType::CONDITIONAL;
        _map["Then"] = TokenType::CONDITIONAL;
        _map["then"] = TokenType::CONDITIONAL;
        _map["-->"] = TokenType::CONDITIONAL;
        _map["->"] = TokenType::CONDITIONAL;

        _map["IFF"] = TokenType::BICONDITIONAL;
        _map["iff"] = TokenType::BICONDITIONAL;
        _map["Iff"] = TokenType::BICONDITIONAL;
        _map["<-->"] = TokenType::BICONDITIONAL;
        _map["<->"] = TokenType::BICONDITIONAL;

        _map["OR"] = TokenType::OR;
        _map["or"] = TokenType::OR;
        _map["Or"] = TokenType::OR;
        _map["||"] = TokenType::OR;
        _map["|"] = TokenType::OR;
        _map["+"] = TokenType::OR;

        _map["XOR"] = TokenType::XOR;
        _map["xor"] = TokenType::XOR;
        _map["Xor"] = TokenType::XOR;
        _map["^"] = TokenType::XOR;

        _map["XNOR"] = TokenType::XNOR;
        _map["xnor"] = TokenType::XNOR;

        _map["NOR"] = TokenType::NOR;
        _map["nor"] = TokenType::NOR;
        _map["Nor"] = TokenType::NOR;

        _map["AND"] = TokenType::AND;
        _map["and"] = TokenType::AND;
        _map["And"] = TokenType::AND;
        _map["&&"] = TokenType::AND;
        _map["&"] = TokenType::AND;
        _map["*"] = TokenType::AND;

        _map["NAND"] = TokenType::NAND;
        _map["nand"] = TokenType::NAND;

        _map["not"] = TokenType::NOT_PRFX;
        _map["NOT"] = TokenType::NOT_PRFX;
        _map["Not"] = TokenType::NOT_PRFX;
        _map["~"] = TokenType::NOT_PRFX;
        _map["`"] = TokenType::NOT_PRFX;
        _map["-"] = TokenType::NOT_PRFX;

        _map["'"] = TokenType::NOT_PSTFX;

        _map["["] = TokenType::O_BRACKET;
        _map["]"] = TokenType::C_BRACKET;
        _map["("] = TokenType::O_PAREN;
        _map[")"] = TokenType::C_PAREN;
        _map["{"] = TokenType::O_BRACE;
        _map["}"] = TokenType::C_BRACE;

        _map["T"] = TokenType::CONST_T;
        _map["F"] = TokenType::CONST_F;
        _map["0"] = TokenType::CONST_F;
        _map["1"] = TokenType::CONST_T;
        _map["TRUE"] = TokenType::CONST_T;
        _map["FALSE"] = TokenType::CONST_F;
        _map["true"] = TokenType::CONST_T;
        _map["false"] = TokenType::CONST_F;
        _map["True"] = TokenType::CONST_T;
        _map["False"] = TokenType::CONST_F;
        _map["t"] = TokenType::CONST_T;
        _map["f"] = TokenType::CONST_F;

        _name_map[TokenType::NONE] = "NONE";
        _name_map[TokenType::END_OF_FILE] = "END_OF_FILE";
        _name_map[TokenType::INDETERMINATE_DISCARD] = "INDETERMINATE_DISCARD";
        _name_map[TokenType::INDETERMINATE_SPEC] = "INDETERMINATE_SPEC";
        _name_map[TokenType::INDETERMINATE_ALPHA] = "INDETERMINATE_ALPHA";
        _name_map[TokenType::INDETERMINATE_WHITE] = "INDETERMINATE_WHITE";
        _name_map[TokenType::BICONDITIONAL] = "BICONDITIONAL";
        _name_map[TokenType::CONDITIONAL] = "CONDITIONAL";
        _name_map[TokenType::OR] = "OR";
        _name_map[TokenType::XOR] = "XOR";
        _name_map[TokenType::XNOR] = "XNOR";
        _name_map[TokenType::NOR] = "NOR";
        _name_map[TokenType::AND] = "AND";
        _name_map[TokenType::NAND] = "NAND";
        _name_map[TokenType::NOT_PSTFX] = "NOT_PSTFX";
        _name_map[TokenType::NOT_PRFX] = "NOT_PRFX";
        _name_map[TokenType::O_BRACKET] = "O_BRACKET";
        _name_map[TokenType::C_BRACKET] = "C_BRACKET";
        _name_map[TokenType::O_PAREN] = "O_PAREN";
        _name_map[TokenType::C_PAREN] = "C_PAREN";
        _name_map[TokenType::O_BRACE] = "O_BRACE";
        _name_map[TokenType::C_BRACE] = "C_BRACE";
        _name_map[TokenType::CONST_T] = "CONST_T";
        _name_map[TokenType::CONST_F] = "CONST_F";
        _name_map[TokenType::VARIABLE] = "VARIABLE";
    }
    std::unordered_map<std::string, TokenType> _map{};
    std::unordered_map<TokenType, std::string> _name_map{};
};

}  // namespace lge