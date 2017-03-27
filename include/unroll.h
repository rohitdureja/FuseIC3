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

#pragma once

#include "ts.h"

namespace vtsa2015 {

/**
 * Helper class for building an unrolling of a transition system.
 * For example, a BMC problem for depth k can be built as follows:
 *
 * Unroller un(ts);
 * msat_assert_formula(env, un.at_time(ts.init(), 0));
 * for (size_t i = 0; i < k; ++i) {
 *     msat_assert_formula(env, un.at_time(ts.trans(), i));
 * }
 * msat_assert_formula(env, un.at_time(msat_make_not(env, ts.prop()), k));
 */
class Unroller {
public:
    Unroller(const TransitionSystem &ts);
    ~Unroller();

    msat_term at_time(msat_term f, unsigned int k);
    ///< replaces every state variable x in f with x@k
    
    msat_term untime(msat_term f);
    ///< replaces every state variable x@k in f with x

private:
    msat_term at_time_var(msat_term v, unsigned int k);
    TermMap &time_cache(unsigned int k);
    
    const TransitionSystem &ts_;

    typedef std::vector<TermMap *> TimeCache;
    TimeCache time_cache_;
    TermMap untime_cache_;
};

} // namespace vtsa2015
