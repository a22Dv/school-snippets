#pragma once

#include <vector>
#include <string_view>

#include "tokens.hpp"

namespace lge
{

/// @brief 
/// Runs the lexer on the given string expression and
/// returns a list of tokens.
std::vector<Token> run_lexer(std::string_view expression);

}  // namespace lge
