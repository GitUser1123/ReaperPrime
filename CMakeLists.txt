
cmake_minimum_required(VERSION 2.8)
project(reaper)

## Version ##

set(REAPER_VERSION "v13")

## Options ##

option(CPU_MINING_ONLY "Do not compile the GPU mining part" OFF)
if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
option(REAPER_BUILD_64BIT "AUTOMATIC, DO NOT TOUCH: Compiling 64bit" ON)
else( CMAKE_SIZEOF_VOID_P EQUAL 8 )
option(REAPER_BUILD_32BIT "AUTOMATIC, DO NOT TOUCH: Compiling 32bit" ON)
endif( CMAKE_SIZEOF_VOID_P EQUAL 8 )


## Global config ##

configure_file(
    "${PROJECT_SOURCE_DIR}/CMakeConf.h.in"
    "${PROJECT_BINARY_DIR}/CMakeConf.h"
)

## Source files ##

set(SOURCES
    App.cpp
    AppOpenCL.cpp
    Config.cpp
	CPUAlgos_global.cpp
	CPUAlgos_mtrlt.cpp
	CPUAlgos_hp7.cpp
    CPUMiner.cpp
    Curl.cpp
    main.cpp
    ServerSettings.cpp
    SHA256.cpp
    Util.cpp
	Sieve.cpp
	Primes.cpp
	CSieveOfEratosthenes.cpp
)

set(HEADERS 
	App.h
	AppOpenCL.h
	Config.h
	CPUAlgos.h
	CPUAlgos_global.h
	CPUMiner.h
	Curl.h
	Global.h
	ServerSettings.h
	SHA256.h
	Util.h
	Sieve.h
	Primes.h
	CSieveOfEratosthenes.h
)

## Targets ##

add_executable(reaper ${SOURCES} ${HEADERS})
include_directories(${PROJECT_BINARY_DIR})
set_target_properties(reaper PROPERTIES COMPILE_FLAGS -O2)

## OpenCL detection ##
if(NOT CPU_MINING_ONLY)
    
    if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
		find_library(OPENCL_LIBRARY OpenCL PATHS "$ENV{AMDAPPSDKROOT}/lib/x86_64")
	else( CMAKE_SIZEOF_VOID_P EQUAL 8 )
		find_library(OPENCL_LIBRARY OpenCL PATHS "$ENV{AMDAPPSDKROOT}/lib/x86")
	endif( CMAKE_SIZEOF_VOID_P EQUAL 8 )
    
    if(APPLE)
        find_path(OPENCL_INCLUDE_DIR OpenCL/cl.h PATHS "$ENV{AMDAPPSDKROOT}/include")
    else(APPLE)
        find_path(OPENCL_INCLUDE_DIR CL/cl.h PATHS "$ENV{AMDAPPSDKROOT}/include")
    endif(APPLE)
    
    mark_as_advanced(OPENCL_INCLUDE_DIR OPENCL_LIBRARY)
    
    include_directories(${OPENCL_INCLUDE_DIR})
    
endif(NOT CPU_MINING_ONLY)

## Library configuration ##

if(CPU_MINING_ONLY)
    target_link_libraries(reaper curldll gmp blkmaker-0.1 blkmaker_jansson-0.1 jansson pthread)
else(CPU_MINING_ONLY)
    target_link_libraries(reaper curldll gmp blkmaker-0.1 blkmaker_jansson-0.1 jansson pthread ${OPENCL_LIBRARY})
endif(CPU_MINING_ONLY)
