# FuseIC3
### An algorithm for checking large design spaces

FuseIC3 is a SAT-based algorithm for checking a set of models. It extends IC3 to minimize time spent in exploring the common state space between related models. 

For more details about FuseIC3, please visit: http://temporallogic.org/research/FMCAD17

---

## Building FuseIC3

* System Requirements
  * MathSAT5 (mathsat.fbk.eu)
  * C++11
  * libgmp, libgmpxx 
  
CMake is the default build tool. To install FuseIC3, download the unzip the repository. Run the following commands to build and install FuseIC3.

```
cd FuseIC3-master
mkdir build
cd build
cmake ..
make
```

## Using FuseIC3

```
Usage:  ./FuseIC3 [options] folder

 Algorithm options
   -p           priority-queue proof obligation management (default: false)
                if not enabled, a stack-based approach is used
   -f number    enable model-set mode; set algorithm number between [1...4] (default: disabled)
   folder       path of folder containing .vmt files to check (required)

 Miscellaneous
   -v level     set verbosity level (default: 0)
   -w           print witness (default: false)
   -s seed      seed value for random number generator
   -h, --help   display this message


 Available model-set checking algorithms
 (supplied as argument with -f options)
  -----------------------------------------------------------------
  | Number | Algorithm                                            |
  -----------------------------------------------------------------
  |   1    | Incremental IC3 (FMCAD 2011)                         |
  |   2    | Basic Check (re-use and check last invariant)        |
  |   3    | Basic Check + Drop Violating Clauses                 |
  |   4    | Basic Check + Repair Violating Clauses               |
  -----------------------------------------------------------------

 Example usage scenarios
 ./FuseIC3 folder             runs simple algorithm on files in folder
 ./FuseIC3 -p folder          runs simple algorithm using priority queues on files in folder
 ./FuseIC3 -f 3 folder        runs family algorithm number 10 on files in folder
 ./FuseIC3 -p -f 2 folder     runs family algorithm number 2 using priority queues on files in folder
```
