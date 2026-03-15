#include "ast.hpp"

#include <format>
#include <map>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "types.hpp"

namespace lge
{

ASTTree get_ast(std::vector<Token> &tokens)
{
    ASTTree tree{};
    static ASTNode start = ASTNodeBiconditional{};

    ASTNodeParsing nparse{tree.nodes, tokens, 0};
    const isize root = std::visit(nparse, start);  // Start parsing at highest level. Standard RDP

    // Now, the number of nodes is defined
    tree.subexpressions.resize(tree.nodes.size());
    ASTNodeFormatter nformat{tree.nodes, tokens, tree.subexpressions};
    std::visit(nformat, tree.nodes.back());

    // Each subexpression string maps to several
    // indices if duplicate subexpressions are
    // found, along with a boolean evaluation state.
    isize varcount = 0;
    std::map<std::string, std::vector<isize>> mapped_subexprs{};
    for (isize i = 0; i < tree.subexpressions.size(); ++i) {
        std::string &str = tree.subexpressions[i];
        auto it = mapped_subexprs.find(str);

        if (it == mapped_subexprs.end()) {
            // Left, Right, Token ID, Node ID.
            const auto [left, right, tid, nid] = std::visit(ASTNodeVisitor{}, tree.nodes[i]);
            if (tokens[tid].type == TokenType::VARIABLE) {
                ++varcount;
            }
            mapped_subexprs[str] = {i};
        } else {
            it->second.push_back(i);
        }
    }
    tree.varcount = varcount;

    // Number of variables multiplied by number of unique subexpressions.
    const isize n_exprs = mapped_subexprs.size();
    const isize n_entries = 1 << varcount;
    tree.values.resize(n_entries * n_exprs);
    std::vector<isize> remap(tree.nodes.size());
    std::vector<bool> evaluated(n_exprs);
    for (isize cvar = 0, idx = 0; auto &entry : mapped_subexprs) {
        ASTNode &node = tree.nodes[entry.second[0]];
        const auto [left, right, tid, nid] = std::visit(ASTNodeVisitor{}, node);
        for (auto i : entry.second) {
            remap[i] = idx;
        }
        if (tokens[tid].type != TokenType::VARIABLE) {
            ++idx;
            continue;
        }
        const isize seqlen = n_entries >> cvar;
        for (isize i = 0; i < n_entries; ++i) {
            tree.values[idx * n_entries + i] = (i & (seqlen - 1)) < (seqlen >> 1);
        }
        ++cvar;
        ++idx;
    }

    ASTNodeEvaluator eval{n_entries, tree.values, remap, evaluated};
    for (isize i = 0; i < tree.nodes.size(); ++i) {
        std::visit(eval, tree.nodes[i]);  // Variables are skipped.
    }

    // (Subexpression, Values) index in sorted order, by length,
    // then variables at leftmost sorted alphabetically.
    std::unordered_map<std::string, isize> smap = {};
    for (isize i = 0; i < tree.subexpressions.size(); ++i) {
        smap[tree.subexpressions[i]] = i;
    }
    std::vector<std::pair<isize, isize>> variables{};
    for (auto entry : mapped_subexprs) {
        const auto [l, r, t, n] = std::visit(ASTNodeVisitor{}, tree.nodes[entry.second[0]]);
        if (tokens[t].type == TokenType::VARIABLE) {
            variables.push_back({smap[entry.first], remap[entry.second[0]]});
            continue;
        }
        tree.columns.push_back({smap[entry.first], remap[entry.second[0]]});
    }
    std::sort(variables.begin(), variables.end(), [&](auto &a, auto &b) {
        const auto &astr = tree.subexpressions[a.first];
        const auto &bstr = tree.subexpressions[b.first];
        if (astr.size() != bstr.size()) {
            const isize minlen = std::min(astr.size(), bstr.size());
            const std::string_view min_a(astr.begin(), astr.begin() + minlen);
            const std::string_view min_b(bstr.begin(), bstr.begin() + minlen);
            return min_a < min_b;
        }
        return astr < bstr;
    });
    std::sort(tree.columns.begin(), tree.columns.end(), [&](auto a, auto b) {
        return tree.subexpressions[a.first].size() < tree.subexpressions[b.first].size();
    });
    for (auto &c : tree.columns) {
        variables.push_back(c);  // Actual columns are appended at the end.
    }
    std::swap(tree.columns, variables);
    return tree;
}

std::string get_formatted_ast(ASTTree &tree)
{
    std::string formatted_output{};
    for (isize i = 0; i < tree.columns.size(); ++i) {
        formatted_output.append(tree.subexpressions[tree.columns[i].first]);
        if (i < tree.columns.size() - 1) {
            formatted_output.append("   ");
        }
    }
    formatted_output.append("\n");
    formatted_output.append(std::string(formatted_output.size() - 1, '='));
    formatted_output.append("\n");
    const isize rcount = (1 << tree.varcount);
    for (isize i = 0; i < rcount; ++i) {
        for (isize j = 0; j < tree.columns.size(); ++j) {
            const isize hlen = tree.subexpressions[tree.columns[j].first].size();
            const u8 val = tree.values[tree.columns[j].second * rcount + i];
            const std::string leading_ansi = val ? "\x1B[1;32m" : "\x1B[1;31m";
            const std::string strval = val ? "T" : "F";
            const std::string formatted = std::format("{:^{}}", strval, hlen);
            formatted_output.append(leading_ansi);
            formatted_output.append(formatted);
            formatted_output.append("\x1B[0m");
            if (j < tree.columns.size() - 1) {
                formatted_output.append("   ");
            }
        }
        formatted_output.append("\n");
    }
    return formatted_output;
}

}  // namespace lge