/** -*- C++ -*-
 * 
 * SMT solver interface for IC3
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

#include "solver.h"

namespace nexus {


Solver::Solver(msat_env env, const Options &opts)
{
    msat_config cfg = get_config(BOOL_MODEL);
    env_ = msat_create_shared_env(cfg, env);
    msat_destroy_config(cfg);
}


Solver::~Solver()
{
    if (!MSAT_ERROR_ENV(env_)) {
        msat_destroy_env(env_);
    }
}


void Solver::reset()
{
    msat_reset_env(env_);
}


void Solver::add(msat_term formula, msat_term label)
{
    msat_assert_formula(env_, msat_make_or(env_, msat_make_not(env_, label),
                                           formula));
}


void Solver::add_clause(const TermList &clause, msat_term label)
{
    msat_term f = msat_make_not(env_, label);
    for (msat_term t : clause) {
        f = msat_make_or(env_, f, t);
    }
    msat_assert_formula(env_, f);
}


void Solver::push()
{
    msat_push_backtrack_point(env_);
}


void Solver::pop()
{
    msat_pop_backtrack_point(env_);
}


void Solver::add_cube_as_clause(const TermList &cube, msat_term label)
{
    msat_term c = msat_make_false(env_);
    for (msat_term t : cube) {
        c = msat_make_or(env_, c, msat_make_not(env_, t));
    }
    if (!MSAT_ERROR_TERM(label)) {
        c = msat_make_or(env_, msat_make_not(env_, label), c);
    }
    msat_assert_formula(env_, c);
}


void Solver::add_cube_as_clause(const TermList &cube)
{
    msat_term label;
    MSAT_MAKE_ERROR_TERM(label);
    add_cube_as_clause(cube, label);
}

void Solver::add_disjunct_cubes(const std::vector<TermList> &cubes)
{
    msat_term expr = msat_make_false(env_);
    for (TermList cube: cubes) {
        msat_term c = msat_make_true(env_);
        for(msat_term lit : cube) {
            c = msat_make_and(env_, c, lit);
        }
        expr = msat_make_or(env_, expr, c);
    }
    msat_assert_formula(env_, expr);
}


void Solver::assume(msat_term a)
{
    a_.push_back(a);
}


bool Solver::check()
{
    uc_.clear();
    msat_result res = msat_solve_with_assumptions(env_, &a_[0], a_.size());
    assert(res != MSAT_UNKNOWN);
    a_.clear();
    return (res == MSAT_SAT);
}


const TermSet &Solver::unsat_assumptions()
{
    if (uc_.empty()) {
        size_t sz;
        msat_term *u = msat_get_unsat_assumptions(env_, &sz);
        assert(u);
        for (size_t i = 0; i < sz; ++i) {
            msat_term l = u[i];
            uc_.insert(l);
            logger(3) << "unsat assumption: " << logterm(env_, l) << endlog;
        }
        msat_free(u);
    }
    return uc_;
}


bool Solver::model_value(msat_term pred)
{
    msat_term v = msat_get_model_value(env_, pred);
    switch (msat_decl_get_tag(env_, msat_term_get_decl(v))) {
    case MSAT_TAG_TRUE:
        return true;
        break;
    case MSAT_TAG_FALSE:
        return false;
        break;
    default:
        return false; // pick a random assignment
    }
}


} // namespace nexus
