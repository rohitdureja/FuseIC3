/** -*- C++ -*-
 * 
 * Options
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

#include <string>

namespace vtsa2015 {

struct Options {
    int verbosity;
    bool witness;
    bool nopreds;
    std::string filename;
    std::string trace;
    int seed;
    bool stack;

    Options()
    {
        verbosity = 0;
        witness = false;
        nopreds = false;
        filename = "";
        trace = "";
        seed = 0;
        stack = false;
    }
};

} // namespace vtsa2015
