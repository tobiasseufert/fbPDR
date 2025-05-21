cmake_minimum_required(VERSION 3.12)
project(IC3 VERSION 0.1.0 LANGUAGES C CXX)

set(CMAKE_C_COMPILER "gcc")
set(CMAKE_CXX_COMPILER "g++")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_RELEASE ON)
set(CMAKE_VERBOSE_MAKEFILE ON)

include(CTest)
enable_testing()

include_directories(
    ${PROJECT_SOURCE_DIR} 
    ${PROJECT_SOURCE_DIR}/minisat 
    ${PROJECT_SOURCE_DIR}/aiger 
    ${PROJECT_SOURCE_DIR}/minisat/minisat/core 
    ${PROJECT_SOURCE_DIR}/minisat/minisat/mtl 
    ${PROJECT_SOURCE_DIR}/minisat/minisat/simp)

ADD_LIBRARY(fbpdr Model.cpp IC3.cpp aiger/aiger.c)
target_link_libraries(fbpdr PRIVATE -lz)
target_link_libraries(fbpdr PRIVATE ${CMAKE_SOURCE_DIR}/minisat/build/libminisat.a)

add_executable(IC3 main.cpp)

target_link_libraries(IC3 fbpdr)

# Option to link statically to the standard library
option(STATIC_LINK "Link statically to the standard library" OFF)

if(STATIC_LINK)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
endif()

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
