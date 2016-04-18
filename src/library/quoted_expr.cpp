/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Gallagher, Daniel Selsam
*/
#include <string>
#include "assert.h"
#include "kernel/kernel_exception.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/quoted_expr.h"
#include "library/string.h"
#include "library/kernel_serializer.h"
#include "util/sstream.h"

namespace lean {
static name * g_quoted_expr_name = nullptr;
static std::string * g_quoted_expr_opcode = nullptr;
static macro_definition * g_quoted_expr = nullptr;

name const & get_quoted_expr_name() { return *g_quoted_expr_name; }
std::string const & get_quoted_expr_opcode() { return *g_quoted_expr_opcode; }

class quoted_expr_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception("invalid quoted-expr, incorrect number of arguments");
    }

    expr quote_name(name const & n) const {
        if (n.is_numeral()) {
            throw exception(sstream() << "quoting names with ints not supported"); // TODO(dhs, jack): reflect names with uint components
        } else if (n.is_anonymous()) {
            return mk_app(mk_constant(get_list_nil_name(), {mk_level_one()}), mk_constant(get_string_name()));
        } else if (n.is_string()) {
            return mk_app(mk_constant(get_list_cons_name(), {mk_level_one()}), 
                          {mk_constant(get_string_name()), from_string(n.get_string()), quote_name(n.get_prefix())});
        }
        lean_unreachable();
    }

    expr quote_level(level const & l) const {
        switch (l.kind()) {
        case level_kind::Zero:
            return mk_constant(get_lean_syntax_level_zero_name());
        case level_kind::Succ: 
            return mk_app(mk_constant(get_lean_syntax_level_succ_name()), quote_level(succ_of(l)));
        case level_kind::Max:
            return mk_app(mk_constant(get_lean_syntax_level_max_name()), {quote_level(max_lhs(l)), quote_level(max_rhs(l))});
        case level_kind::IMax:
            return mk_app(mk_constant(get_lean_syntax_level_imax_name()), {quote_level(imax_lhs(l)), quote_level(imax_rhs(l))});
        case level_kind::Param:
            return mk_app(mk_constant(get_lean_syntax_level_param_name()), quote_name(param_id(l)));
        case level_kind::Global: 
            return mk_app(mk_constant(get_lean_syntax_level_global_name()), quote_name(global_id(l)));
        case level_kind::Meta: 
            return mk_app(mk_constant(get_lean_syntax_level_meta_name()), quote_name(meta_id(l)));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    expr quote_levels(levels const & ls) const {
        if(is_nil(ls)) {
            return mk_app(mk_constant(get_list_nil_name(), {mk_level_one()}), mk_constant(get_lean_syntax_level_name()));
        } else {
            return mk_app(mk_constant(get_list_cons_name(), {mk_level_one()}), 
                          {mk_constant(get_lean_syntax_level_name()),
                                  quote_level(head(ls)),
                                  quote_levels(tail(ls))});
        }
    }
    expr quote_nat(unsigned i) const {
        expr r_i = mk_constant(get_nat_zero_name());
        for (unsigned j = 1; j < i; ++j) {
            r_i = mk_app(mk_constant(get_nat_succ_name()), r_i);
        }
        return r_i;
    }

    expr quote_expr(expr const & e)  const {
        switch (e.kind()) {
        case expr_kind::Var:
            return mk_app(mk_constant(get_lean_syntax_expr_var_name()), quote_nat(var_idx(e)));
        case expr_kind::Sort:
            return mk_app(mk_constant(get_lean_syntax_expr_sort_name()), quote_level(sort_level(e)));
        case expr_kind::Constant:
            return mk_app(mk_constant(get_lean_syntax_expr_const_name()), 
                          {quote_name(const_name(e)), quote_levels(const_levels(e))});
        case expr_kind::Lambda:
            return mk_app(mk_constant(get_lean_syntax_expr_lam_name()), {quote_expr(binding_domain(e)), quote_expr(binding_body(e))});
        case expr_kind::Pi:
            return mk_app(mk_constant(get_lean_syntax_expr_pi_name()), {quote_expr(binding_domain(e)), quote_expr(binding_body(e))});
        case expr_kind::App:
            return mk_app(mk_constant(get_lean_syntax_expr_app_name()), {quote_expr(app_fn(e)), quote_expr(app_arg(e))});
        case expr_kind::Let:
            return mk_app(mk_constant(get_lean_syntax_expr_elet_name()), 
                          { quote_name(let_name(e)), quote_expr(let_type(e))
                          , quote_expr(let_value(e)), quote_expr(let_body(e)) });
        case expr_kind::Meta:
            return mk_app(mk_constant(get_lean_syntax_expr_meta_name()), {quote_name(mlocal_name(e)), quote_expr(mlocal_type(e))});
        case expr_kind::Macro:
            throw exception(sstream() << "quoting unexpanded macros not supported"); // TODO(dhs, jack): reflect macros
        case expr_kind::Local:
            lean_unreachable();  // LCOV_EXCL_LINE
        }
        lean_unreachable();
    }

public:
    virtual name get_name() const { return get_quoted_expr_name(); }
    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context &, bool) const {
        constraint_seq cseq;
        check_macro(m);
        return mk_pair(mk_constant(get_lean_syntax_expr_name()), cseq);
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(quote_expr(get_quoted_expr_expr(m)));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_quoted_expr_opcode());
    }
};

bool is_quoted_expr(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_quoted_expr;
}

expr mk_quoted_expr(expr const & v) {
    expr args[1] = {v};
    return mk_macro(*g_quoted_expr, 1, args);
}

expr get_quoted_expr_expr(expr const & e) { lean_assert(is_quoted_expr(e)); return macro_arg(e, 0); }


void initialize_quoted_expr() {
    g_quoted_expr_name = new name("quoted_expr");
    g_quoted_expr_opcode = new std::string("QuoteE");
    g_quoted_expr = new macro_definition(new quoted_expr_macro_definition_cell());
    register_macro_deserializer(*g_quoted_expr_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_quoted_expr(args[0]);
                                });
}

void finalize_quoted_expr() {
    delete g_quoted_expr;
    delete g_quoted_expr_opcode;
    delete g_quoted_expr_name;
}
}
