cmake_minimum_required(VERSION 2.8)
project(FuseIC3 CXX)
enable_language(CXX C)

# set the c++ standard
set(CMAKE_CXX_STANDARD 11)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static-libstdc++")
# bring in the source files
file(GLOB SOURCES "src/*.cpp")

# add sources to executable
add_executable(FuseIC3 ${SOURCES})

# bring in the header files
target_include_directories(FuseIC3 PRIVATE include . $(CMAKE_CURRENT_BINDARY_DIR))

# find required libraries
find_library(MATHSAT_LIB mathsat)
find_library(GMP_LIB gmp)
find_library(GMPXX_LIB gmpxx)

# link libraries
target_link_libraries(FuseIC3 ${MATHSAT_LIB} ${GMP_LIB} ${GMPXX_LIB})
