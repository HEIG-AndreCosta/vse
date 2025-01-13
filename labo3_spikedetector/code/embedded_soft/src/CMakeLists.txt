cmake_minimum_required(VERSION 3.16)
project(Embedded)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "-Wall")

add_executable(embedded_soft)
target_sources(embedded_soft PUBLIC
    fpgaaccessremote.cpp
    fpgaaccessremote.hpp
    main.cpp
)
