# project(YOSYS_EXTENSION)

# Collect all source files
file(GLOB MY_SOURCES "./*.cc")

# Make the plugin library with the .so suffix
set(CMAKE_SHARED_LIBRARY_SUFFIX ".so")

# random_sim shells out to compile .sim_main.cpp; use the same CXX and crucial flags.
# This prevents local CLT builds from failing to find libc++ headers at runtime compile.
set(GV_RANDOM_SIM_CXXFLAGS "")
if(APPLE AND CMAKE_OSX_SYSROOT)
    string(APPEND GV_RANDOM_SIM_CXXFLAGS " --sysroot=${CMAKE_OSX_SYSROOT}")
    set(_gv_random_sim_libcxx_dir "${CMAKE_OSX_SYSROOT}/usr/include/c++/v1")
    if(EXISTS "${_gv_random_sim_libcxx_dir}/algorithm")
        string(APPEND GV_RANDOM_SIM_CXXFLAGS " -isystem ${_gv_random_sim_libcxx_dir}")
    endif()
endif()

configure_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/sim_random_compile_config.h.in
    ${CMAKE_CURRENT_BINARY_DIR}/sim_random_compile_config.h
    @ONLY)

# Compile each .cc file into a .so file
foreach(source_file ${MY_SOURCES})
    # Extract the file name (without path and extension)
    get_filename_component(name ${source_file} NAME_WE)
    # Compile each .cc file into a .so file
    add_library(${name} SHARED ${source_file})
    set_property(TARGET ${name} PROPERTY POSITION_INDEPENDENT_CODE ON)
    target_include_directories(${name} PRIVATE ${YOSYS_DIR} ${CMAKE_CURRENT_BINARY_DIR})
    if(APPLE)
        target_link_options(${name} PRIVATE "-dynamic" "-undefined" "dynamic_lookup")
    else()
        target_link_options(${name} PRIVATE "-rdynamic")
    endif()
    target_compile_definitions(${name} PRIVATE _YOSYS_ GV_YOSYS_BIN_PATH="${YOSYS_DIR}/yosys")
    add_dependencies(${name} engine-yosys)
endforeach()
