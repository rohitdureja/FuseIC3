/**
 * Manager for transition systems
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

#include "ts.h"
#include <algorithm>

namespace nexus {

// constructor for TransitionSystem object
TransitionSystem::TransitionSystem(msat_env env):
    env_(env)
{
    reset();
}

// Initialize the various fields in the TransitionSystem object
// These fields are init, trans, prop, statevars, nextstatevars,
// cur2next, next2cur, statevars_set, nextstatevars_set
void TransitionSystem::initialize(
    const TermMap &statevars,
    msat_term init, msat_term trans, msat_term prop)
{
    reset();

    for (auto p : statevars) {
        statevars_.push_back(p.first);
    }
    std::sort(statevars_.begin(), statevars_.end());

    for (auto s : statevars_) {
        msat_term n = statevars.find(s)->second;
        nextstatevars_.push_back(n);
        cur2next_[s] = n;
        next2cur_[n] = s;
        statevars_set_.insert(s);
        nextstatevars_set_.insert(n);
    }

    init_ = init;
    trans_ = trans;
    prop_ = prop;

    // find the inputs from the set of variables
    collect_inputs();
}

// reset the transition system
void TransitionSystem::reset()
{
    statevars_.clear();
    nextstatevars_.clear();
    inputvars_.clear();

    statevars_set_.clear();
    nextstatevars_set_.clear();
    inputvars_set_.clear();

    cur2next_.clear();
    next2cur_.clear();
}


void TransitionSystem::collect_inputs()
{
    auto visit = [](msat_env e, msat_term t, int preorder,
                    void *data) -> msat_visit_status
        {
            TermList *out = static_cast<TermList *>(data);
            // a variable is a term with no children and no built-in
            // interpretation
            if (preorder &&
                msat_term_arity(t) == 0 &&
                msat_decl_get_tag(
                    e, msat_term_get_decl(t)) == MSAT_TAG_UNKNOWN) {
                out->push_back(t);
            }
            return MSAT_VISIT_PROCESS;
        };

    TermList allvars;
    // mark all variables in trans_ that are not state vars as inputs
    msat_visit_term(env_, trans_, visit, &allvars);

    for (msat_term v : allvars) {
        if (statevars_set_.find(v) == statevars_set_.end() &&
            nextstatevars_set_.find(v) == nextstatevars_set_.end()) {
            inputvars_.push_back(v);
            cur2next_[v] = v;
            next2cur_[v] = v;
            inputvars_set_.insert(v);
        }
    }
    std::sort(inputvars_.begin(), inputvars_.end());
}


msat_term TransitionSystem::cur(msat_term next_formula) const
{
    auto it = next2cur_.find(next_formula);
    if (it != next2cur_.end()) {
        return it->second;
    }
    auto identity = [](msat_term v) -> msat_term { return v; };
    // next2cur_ is already filled for state variables, so identity will only
    // be called for input vars (see apply_substitution in utils.h)
    return apply_substitution(env_, next_formula, next2cur_, identity);
}


msat_term TransitionSystem::next(msat_term cur_formula) const
{
    auto it = cur2next_.find(cur_formula);
    if (it != cur2next_.end()) {
        return it->second;
    }
    auto identity = [](msat_term v) -> msat_term { return v; };
    // cur2next_ is already filled for state variables, so identity will only
    // be called for input vars (see apply_substitution in utils.h)
    return apply_substitution(env_, cur_formula, cur2next_, identity);
}

} // namespace nexus
