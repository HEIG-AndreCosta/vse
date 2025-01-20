cmake_minimum_required(VERSION 3.15)
project(AppTests)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(GTest REQUIRED)

include_directories("../../src")

file(GLOB APP_SOURCES "../../src/spike_detector.cpp"
                      "../../src/fpgaaccessremote.cpp")

file(GLOB TEST_COMMON_SOURCES "./common/*.cpp")

file(GLOB TEST_SOURCES "./*.cpp")

add_library(app_lib ${APP_SOURCES})
add_library(test_common_lib ${TEST_COMMON_SOURCES})

foreach(TEST_SOURCE ${TEST_SOURCES})
    # Get the test name from the filename
    get_filename_component(TEST_NAME ${TEST_SOURCE} NAME_WE)

    # Create a test executable for each test file
    add_executable(${TEST_NAME} ${TEST_SOURCE})

    # Link the test executable with the app library and Google Test
    target_link_libraries(${TEST_NAME} PRIVATE test_common_lib app_lib GTest::GTest GTest::Main)

    # Add the test to CTest
    add_test(NAME ${TEST_NAME} COMMAND ${TEST_NAME})
endforeach()

