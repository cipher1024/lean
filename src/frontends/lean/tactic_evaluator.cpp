/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/vm/vm_list.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/smt/smt_state.h"
#include "library/tactic/elaborator_exception.h"
#include "frontends/lean/tactic_evaluator.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    format msg = fmt + line() + format("state:") + line() + ts.pp();
    return elaborator_exception(ref, msg);
}

elaborator_exception unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    return unsolved_tactic_state(ts, format(msg), ref);
}

[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    throw unsolved_tactic_state(ts, fmt, ref);
}

[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    throw_unsolved_tactic_state(ts, format(msg), ref);
}

void tactic_evaluator::process_failure(vm_state & S, vm_obj const & r) {
    if (optional<tactic::exception_info> ex = tactic::is_exception(S, r)) {
        format fmt             = std::get<0>(*ex);
        optional<pos_info> pos = std::get<1>(*ex);
        tactic_state s1        = std::get<2>(*ex);
        if (pos)
            throw elaborator_exception(pos, fmt);
        else
            throw_unsolved_tactic_state(s1, fmt, m_ref);
    }
    /* Do nothing if it is a silent failure */
    lean_assert(tactic::is_silent_exception(r));
}

vm_obj tactic_evaluator::operator()(expr const & tactic, tactic_state const & s) {
    vm_obj r = tactic::evaluator::operator()(tactic, s);
    if (auto s = tactic::is_success(r))
        if (s->goals())
            throw_unsolved_tactic_state(*s, "tactic failed, there are unsolved goals", m_ref);
    return r;
}
}
