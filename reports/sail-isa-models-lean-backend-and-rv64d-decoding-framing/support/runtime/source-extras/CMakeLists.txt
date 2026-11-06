# PREPARATION ONLY: not configured or executed.
# Reuse the exact upstream config subdirectory without configuring C++/emulator dependencies.
cmake_minimum_required(VERSION 3.20)
project(AnnealSelectedConfig LANGUAGES NONE)
set(CMAKE_INSTALL_DATADIR share)
if(NOT EXISTS "${ANNEAL_MODEL_SOURCE}/config/CMakeLists.txt")
  message(FATAL_ERROR "ANNEAL_MODEL_SOURCE must be the exact parent-verified model source root")
endif()
add_subdirectory("${ANNEAL_MODEL_SOURCE}/config" "${CMAKE_BINARY_DIR}/config")
