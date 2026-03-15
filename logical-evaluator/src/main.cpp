/** 
 * BUG: 
 * Postfix NOTs are ignored. 
 */

#include <iostream>

#include "ast.hpp"
#include "lexer.hpp"
#include "tokens.hpp"

int main(int argc, char** argv)
{
    static lge::TokenMap tmap = lge::TokenMap::get_instance();
    if (argc != 2) {
        std::cerr << "USAGE: logeval \"<EXPRESSION>\"\n";
        return 1;
    }
    std::cout << "\x1B[2J\x1B[H"; // Clear console.
    std::vector<lge::Token> tokens = lge::run_lexer(argv[1]);
    lge::ASTTree ast = lge::get_ast(tokens);
    std::cout << lge::get_formatted_ast(ast);
    return 0;
}