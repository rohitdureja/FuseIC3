/** -*- C++ -*-
 * 
 * implicit abstraction
 * author: Alberto Griggio <griggio@fbk.eu>
 * 
 * This file is part of ic3ia.
 * Copyright (C) 2015 Fondazione Bruno Kessler.
 *
 * ic3ia is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ic3ia is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with ic3ia.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "ia.h"

namespace vtsa2015 {

namespace {

/**
 * helper function for extracting atomic predicates occurring in a given
 * formula
 */
void get_predicates(msat_env env, msat_term t, TermSet &out)
{
    auto visit = [](msat_env e, msat_term t, int preorder,
                    void *data) -> msat_visit_status
        {
            TermSet *s = static_cast<TermSet *>(data);
            if (preorder && msat_term_is_atom(e, t) &&
                !msat_term_is_boolean_constant(e, t)) {
                s->insert(t);
                return MSAT_VISIT_SKIP;
            }
            return MSAT_VISIT_PROCESS;
        };
    msat_visit_term(env, t, visit, &out);
}

} // namespace


//-----------------------------------------------------------------------------
// Abstractor
//-----------------------------------------------------------------------------

Abstractor::Abstractor(const TransitionSystem &ts):
    ts_(ts)
{
}


msat_term Abstractor::abstract(msat_term t)
{
    auto subst = [=](msat_term v) -> msat_term
        {
            // replace each non-Boolean next-state variable in the input
            // formula with its abstract version
            if (ts_.is_nextstatevar(v) &&
                !msat_term_is_boolean_constant(ts_.get_env(), v)) {
                msat_term c = ts_.cur(v);
                msat_decl s = msat_term_get_decl(c);
                std::ostringstream buf;
                char *n = msat_decl_get_name(s);
                buf << n << "^";
                msat_free(n);
                std::string name = buf.str();
                s = msat_declare_function(ts_.get_env(), name.c_str(),
                                          msat_term_get_type(v));
                return msat_make_constant(ts_.get_env(), s);
            } else {
                return v;
            }
        };
    return apply_substitution(ts_.get_env(), t, cache_, subst);
}    


void Abstractor::initial_predicates(TermSet &out)
{
    get_predicates(ts_.get_env(), ts_.init(), out);
    get_predicates(ts_.get_env(), ts_.prop(), out);
}


//-----------------------------------------------------------------------------
// Refiner
//-----------------------------------------------------------------------------


Refiner::Refiner(const TransitionSystem &ts, const Options &opts):
    ts_(ts),
    un_(ts)
{
    msat_config cfg = get_config(FULL_MODEL, true);
    if (!opts.trace.empty()) {
        std::string name = opts.trace + ".itp.smt2";
        msat_set_option(cfg, "debug.api_call_trace", "1");
        msat_set_option(cfg, "debug.api_call_trace_filename", name.c_str());
    }
    solver_ = msat_create_shared_env(cfg, ts_.get_env());
    msat_destroy_config(cfg);
}


Refiner::~Refiner()
{
    if (!MSAT_ERROR_ENV(solver_)) {
        msat_destroy_env(solver_);
    }
}


bool Refiner::refine(const std::vector<TermList> &cex)
{
    // reset the interpolating solver
    msat_reset_env(solver_);
    preds_.clear();
    groups_.clear();

    // create the interpolation groups
    for (size_t k = groups_.size(); k < cex.size(); ++k) {
        groups_.push_back(msat_create_itp_group(solver_));
    }

    // generate the BMC problem for the input abstract counterexample trace,
    // putting each step in a different interpolation group
    for (size_t k = 0; k < cex.size(); ++k) {
        msat_set_itp_group(solver_, groups_[k]);
        msat_assert_formula(solver_, un_.at_time(make_and(cex[k]), k));
        if (k != cex.size()-1) {
            msat_assert_formula(solver_, un_.at_time(ts_.trans(), k));
        }
    }
    // check whether the counterexample is concrete
    msat_result res = msat_solve(solver_);    

    if (res == MSAT_UNSAT) {
        // compute a sequence interpolant for the spurious cex trace, and
        // extract the atomic predicates occurring in each element of the
        // sequence (after proper untiming -- see Unroller::untime())
        extract_predicates(solver_);
    }

    return (res == MSAT_UNSAT);
}


void Refiner::extract_predicates(msat_env env)
{
    preds_.clear();

    for (size_t i = 1; i < groups_.size(); ++i) {
        msat_term t = msat_get_interpolant(env, &groups_[0], i);
        logger(3) << "got interpolant " << i << ": " << logterm(env, t)
                  << endlog;
        get_predicates(env, un_.untime(t), preds_);
    }
}


msat_term Refiner::make_and(const TermList &c)
{
    msat_term ret = msat_make_true(ts_.get_env());
    for (msat_term l : c) {
        ret = msat_make_and(ts_.get_env(), ret, l);
    }
    return ret;
}


bool Refiner::counterexample(std::vector<TermList> &cex)
{
    auto eq = [=](msat_term a, msat_term b)
        {
            if (msat_is_bool_type(solver_, msat_term_get_type(a))) {
                return msat_make_iff(solver_, a, b);
            } else {
                return msat_make_equal(solver_, a, b);
            }
        };
    
    for (size_t i = 0; i < groups_.size(); ++i) {
        cex.push_back(TermList());
        TermList &state = cex.back();
        const TermList *vl[] = { &(ts_.statevars()), &(ts_.inputvars()) };
        for (size_t j = 0; j < (i == groups_.size()-1 ? 1 : 2); ++j) {
            for (msat_term v : *(vl[j])) {
                msat_term vi = un_.at_time(v, i);
                msat_term val = msat_get_model_value(solver_, vi);
                if (MSAT_ERROR_TERM(val)) {
                    return false;
                } else if (val != v) {
                    // val == v means the variable is a don't care, so we
                    // don't include it in the trace
                    state.push_back(eq(v, val));
                }
            }
        }
    }

    return true;
}

} // namespace vtsa2015
