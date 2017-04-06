/*
 * This file is part of Nexus Model Checker.
 * author: Rohit Dureja <dureja at iastate dot edu>
 *
 * Copyright (C) 2017 Rohit Dureja,
 *                    Iowa State University
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


#include <iostream>
#include <stdlib.h>
#include <signal.h>
#include <simple_ic3.h>
#include <family_ic3.h>
#include <dirent.h>
#include <algorithm>
#include <unistd.h>
#include <string.h>

#define VERSION "0.0.1a"


using namespace nexus;

// pointer to algorithm instances
FamilyIC3 *family_ic3 = NULL;


/** \brief Handler for raised interrupts
 *
 * This functions handles interrupts raised during the execution of Nexus
 *
 * \return 	None
 *
 * \param 	signo	Number of the signal that interrupted execution.
 */
void handle_interrupt(int signo)
{
    if (family_ic3) {
        family_ic3->print_stats();
    }
    std::cout 	<< "interrupted by signal " << signo << "\nunknown"
    			<< std::endl;

    exit(signo);
}

/** \brief Read the VMT file
 *
 * This function reads the VMT specified as input and splits it into the
 * transition relation, initial state, and bad property
 *
 * \return 			True if file parsed successfully, otherwise false.
 *
 * \param 	opts	Command line options in which opts.filename is the file
 * 					to read.
 *
 * \param 	ts		Transition system object to store read file contents.
 */
bool read_file(const Options &opts, TransitionSystem &ts)
{

    // create pointer to mathsat terms
    msat_term *terms;

    // create 2-D array to store annotations
    char **annots;

    // number of mathsat terms
    size_t n;

    // file handler for input file
    FILE *file = nullptr;

    // if filename specified in otions, then open the file
    if (!opts.filename.empty()) {
        file = fopen(opts.filename.c_str(), "r");
    }

    // error in opening file
    if (!file) {
        std::cout << "Error in opening file" << std::endl;
        std::cout << strerror(errno) << std::endl;
        return false;
    }

    // parse the VMT file to an annotated list
    int err = msat_annotated_list_from_smtlib2_file(ts.get_env(), file, &n,
                                                    &terms, &annots);

    // close the file
    fclose(file);

    // if error in reading file
    if (err) {
        std::cout << "parsing error" << std::endl;
        return false;
    }

    // unordered map of msat terms to msat terms
    TermMap statevars;

    // create msat terms
    msat_term init, trans, prop;

    // parse annotated list
    for (size_t i = 0; i < n; ++i) {
        std::string key(annots[2*i]);
        msat_term t = terms[i];
        if (key == "init") {
            init = t;
        } else if (key == "trans") {
            trans = t;
        } else if (key == "invar-property") {
            prop = t;
        } else if (key == "next") {
            std::string val(annots[2*i+1]);
            if (val.length() && val[0] == '|') {
                val = val.substr(1, val.length()-2);
            }
            msat_decl d = msat_find_decl(ts.get_env(), val.c_str());
            if (MSAT_ERROR_DECL(d)) {
                d = msat_declare_function(ts.get_env(), val.c_str(),
                                          msat_term_get_type(terms[i]));
            }
            msat_term n = msat_make_constant(ts.get_env(), d);
            statevars[t] = n;
        }
    }

    // initialize the transition system
    ts.initialize(statevars, init, trans, prop);

    // free up msat terms
    msat_free(terms);
    for (size_t i = 0; i < n; ++i) {
        msat_free(annots[2*i]);
        msat_free(annots[2*i+1]);
    }
    msat_free(annots);

    logger(1) << "parsed system with " << statevars.size() << " state variables"
              << endlog;

    return true;
}


Options parse_options(int argc, const char **argv)
{
    Options ret;

    bool ok = true;
    for (int i = 1; i < argc; ++i) {
        std::string a(argv[i]);
        if (a == "-v") {
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.verbosity = val;
                    set_verbosity(val);
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-w") {
            ret.witness = true;
        } else if (a == "-f") {
            ret.family = true;
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.algorithm = val;
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-p") {
            ret.stack = false;
        } else if (a == "-h" || a == "-help" || a == "--help") {
            std::cout << "Nexus Model Checker [" << VERSION << "]"
                      << "\nUsage: \t" << argv[0] << " [options] folder\n"
                      << "\n Algorithm options"
                      << "\n   -p           priority-queue proof obligation management (default: false)"
                      << "\n                if not enabled, a stack-based approach is used"
					  << "\n   -f number    enable family mode; set algorithm number between 1...12 (default: disabled)"
					  << "\n   folder       path of folder containing .vmt files to check (required)"
					  << "\n\n Miscellaneous"
                      << "\n   -v level     set verbosity level (default: 0)"
                      << "\n   -w           print witness (default: false)"
					  << "\n   -h, --help   display this message\n"
					  << "\n\n Example usage scenarios"
					  << "\n " << argv[0] << " folder             runs simple algorithm on files in folder"
					  << "\n " << argv[0] << " -p folder          runs simple algorithm using priority queues on files in folder"
					  << "\n " << argv[0] << " -f 10 folder       runs family algorithm number 10 on files in folder"
					  << "\n " << argv[0] << " -p -f 2 folder     runs family algorithm number 2 using priority queues on files in folder"
                      << std::endl << std::endl;
            exit(0);
            break;
        } else if (a[0] != '-' && ret.filename.empty()) {
            ret.filename = a;
        } else {
            ok = false;
            break;
        }
    }
    if (!ok) {
        std::cout << "Error in parsing command-line options (use -h for help)"
                  << std::endl;
        exit(1);
    }

    return ret;
}


int main(int argc, const char **argv)
{

    // parse command line options
    Options options = parse_options(argc, argv);

    // create mathsat configuration and environment
    msat_config config = msat_create_config();
    msat_env env = msat_create_env(config);

    // destroy mathsat configurations
    msat_destroy_config(config);

    // delete mathsat environment
    EnvDeleter del_env(env);

    // open folder
    DIR *dir;
    struct dirent *ent;

    // vector to store files
    std::vector<std::string> files;

    // parse directory and retrieve files ending in .vmt
    if((dir = opendir(options.filename.c_str())) != nullptr) {
        // print all files in the directory
        while((ent = readdir(dir)) != NULL) {
            std::string file = ent->d_name;
            if (file.find(".vmt") != std::string::npos)
                files.push_back(file);
        }
        closedir(dir);
    } else {
        std::cout << "No such file or directory" << std::endl;
        exit(1);
    }
    logger(1) << "Folder read statistics"
              << "\nFolder name : " << options.filename
              << "\nFiles read  : " << files.size() << endlog;

    // sort files by filename
    std::sort(files.begin(), files.end());


    // get current working directory
    std::string cwd = get_current_dir_name();

    // change directory
    if(chdir(options.filename.c_str()) < 0) {
        std::cout << "Can't read/write in directory " << options.filename << std::endl;
        exit(-1);
    }

    // create algorithm object
    FamilyIC3 fic3(env, options);
    family_ic3 = &fic3;

    // start reading files and running algorithm
    for(std::string file : files) {

        logger(1) << "Checking file: " << file << endlog;

        // set file to current file
        options.filename = file;

        // reset mathsat env
        msat_reset_env(env);

        // create object to store transition system
        TransitionSystem ts(env);

        // read_ts parses the VMT file
        if (!read_file(options, ts)) {
            // error in reading file
            std::cout << "Error reading input from file: " << options.filename << std::endl;
            exit(-1);
        }

        // configure algorithm instance with current model
        fic3.configure(&ts);

        // check the transition system
        bool safe = fic3.prove();

        if (options.witness) {
            std::vector<TermList> wit;
            if (!fic3.witness(wit)) {
                std::cout << "Error computing witness" << std::endl;
            } else {
                std::cout << (safe ? "invariant" : "counterexample") << "\n";
                for (size_t i = 0; i < wit.size(); ++i) {
                    TermList &w = wit[i];
                    std::cout << ";; " << (safe ? "clause " : "step ") << i
                              << "\n" << (safe ? "(or" : "(and") << "\n";
                    for (msat_term t : w) {
                        std::cout << "  " << logterm(env, t) << "\n";
                    }
                    std::cout << ")\n";
                }
                std::cout.flush();
            }
        }

        fic3.print_stats();
        fic3.save_stats();

        std::cout << (safe ? "safe" : "unsafe") << std::endl;

    }

    // back to home directory
    if(chdir(cwd.c_str()) < 0) {
        std::cout << "Can't read/write in directory " << options.filename << std::endl;
        exit(-1);
    }


    return 0;
}
