/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "util/lazy_list_fn.h"
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/error_msgs.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/app_builder.h"
#include "library/quoted_expr.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic reflect_goal_tactic(elaborate_fn const & elab, expr const & denote_fn) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
            }
            expr t            = head(gs).get_type();

            goal const & g      = head(gs);
            substitution subst  = new_s.get_subst();
            auto tc             = mk_type_checker(env);
            constraint_seq cs;

            expr lhs, rhs;
            if (!is_eq(t, lhs, rhs)) {
                throw_tactic_exception_if_enabled(new_s, [=](formatter const & fmt) {
                        format r = format("invalid 'reflect' tactic, the goal type must be an equality");
                        return r;
                    });
                return proof_state_seq();
            }

            app_builder ab(env, ios.get_options());
            expr new_lhs = mk_app(denote_fn, mk_quoted_expr(lhs));
            expr new_rhs = mk_app(denote_fn, mk_quoted_expr(rhs));
            expr new_t = ab.mk_app(get_eq_name(), new_lhs, new_rhs);

            if (tc->is_def_eq(t, new_t, justification(), cs)) {
                if (cs) {
                    unifier_config cfg(ios.get_options());
                    buffer<constraint> cs_buf;
                    cs.linearize(cs_buf);
                    to_buffer(new_s.get_postponed(), cs_buf);
                    unify_result_seq rseq = unify(env, cs_buf.size(), cs_buf.data(), subst, cfg);
                    return map2<proof_state>(rseq, [=](pair<substitution, constraints> const & p) -> proof_state {
                            substitution const & subst    = p.first;
                            constraints const & postponed = p.second;
                            substitution new_subst = subst;
                            expr final_e = new_subst.instantiate_all(new_t);
                            expr M       = g.mk_meta(mk_fresh_name(), final_e);
                            goal new_g(M, final_e);
                            assign(new_subst, g, M);
                            return proof_state(new_s, cons(new_g, tail(gs)), new_subst, postponed);
                        });
                }
                expr M   = g.mk_meta(mk_fresh_name(), new_t);
                goal new_g(M, new_t);
                assign(subst, g, M);
                return proof_state_seq(proof_state(new_s, cons(new_g, tail(gs)), subst));
            } else {
                    throw_tactic_exception_if_enabled(new_s, [=](formatter const & fmt) {
                            format r = format("invalid 'reflect' tactic, the quoting and denoting yields new goal type");
                            r += pp_indent_expr(fmt, new_t);
                            r += compose(line(), format("which does not match the goal type"));
                            r += pp_indent_expr(fmt, t);
                            return r;
                        });
                    return proof_state_seq();
            }
            return proof_state_seq();
        });
}

void initialize_reflect_tactic() {
    register_tac(get_tactic_reflect_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'reflect' tactic, invalid argument");
                     return reflect_goal_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });
}
void finalize_reflect_tactic() {
}
}
