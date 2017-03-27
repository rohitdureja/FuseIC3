/** -*- C++ -*-
 * 
 * Unrolling of transition systems
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

#include "unroll.h"
#include <iterator>


namespace vtsa2015 {

Unroller::Unroller(const TransitionSystem &ts):
    ts_(ts)
{
}


Unroller::~Unroller()
{
    for (auto p : time_cache_) {
        delete p;
    }
}


msat_term Unroller::at_time(msat_term f, unsigned int k)
{
    auto subst = [=](msat_term v) -> msat_term
        {
            if (ts_.is_statevar(v) || ts_.is_inputvar(v)) {
                return at_time_var(v, k);
            } else if (ts_.is_nextstatevar(v)) {
                return at_time_var(ts_.cur(v), k+1);
            } else {
                return v;
            }
        };
    return apply_substitution(ts_.get_env(), f, time_cache(k), subst);
}


msat_term Unroller::at_time_var(msat_term v, unsigned int k)
{
    TermMap &cache = time_cache(k);

    auto it = cache.find(v);
    if (it != cache.end()) {
        return it->second;
    }
    
    msat_decl s = msat_term_get_decl(v);
    char *n = NULL;
    std::ostringstream buf;
    n = msat_decl_get_name(s);
    buf << n << "@" << k;
    msat_free(n);
    std::string name = buf.str();
    s = msat_declare_function(ts_.get_env(), name.c_str(),
                              msat_term_get_type(v));
    msat_term r = msat_make_constant(ts_.get_env(), s);
    cache[v] = r;
    untime_cache_[r] = v;
    return r;
}


TermMap &Unroller::time_cache(unsigned int k)
{
    while (time_cache_.size() <= k) {
        time_cache_.push_back(new TermMap());
    }
    return *(time_cache_[k]);
}


msat_term Unroller::untime(msat_term f)
{
    // for variables x@k, untime_cache_[x@k] is set in Unroller::at_time_var
    // (see above)
    return apply_substitution(ts_.get_env(), f, untime_cache_,
                              [](msat_term v) -> msat_term { return v; });
}

} // namespace vtsa2015
