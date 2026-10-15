set(generated_config_filenames)

# Create a variety of configuration files for different XLEN/ELEN/VLENs.
foreach(CONFIG__BASE__XLEN IN ITEMS 32 64)
    foreach(CONFIG__V__ELEN_EXP RANGE 5 6)
        foreach(CONFIG__V__VLEN_EXP RANGE 6 9)
            math(EXPR vlen "1 << ${CONFIG__V__VLEN_EXP}")
            math(EXPR elen "1 << ${CONFIG__V__ELEN_EXP}")

            set(config_filename "rv${CONFIG__BASE__XLEN}d_v${vlen}_e${elen}.json")

            set(CONFIG_XLEN_IS_32 "false")
            set(CONFIG_XLEN_IS_64 "false")
            set(CONFIG_XLEN_IS_${CONFIG__BASE__XLEN} "true")

            if (${CONFIG__BASE__XLEN} EQUAL 32)
              set(CONFIG_MIDELEG_DELEGATABLE_BITS_VALUE   "0x0000_2222")
              set(CONFIG_SDTRIG_SUPPORTED_ETRIGGERS_VALUE "0x00fd_bfff")
              set(CONFIG_SDTRIG_SUPPORTED_ITRIGGERS_VALUE "0x0000_3eee")
            else()
              set(CONFIG_MIDELEG_DELEGATABLE_BITS_VALUE   "0x0000_0000_0000_2222")
              set(CONFIG_SDTRIG_SUPPORTED_ETRIGGERS_VALUE "0x0000_0000_00fd_bfff")
              set(CONFIG_SDTRIG_SUPPORTED_ITRIGGERS_VALUE "0x0000_0000_0000_3eee")
            endif()

            set(CONFIG_ELEN_IS_32 "false")
            set(CONFIG_ELEN_IS_64 "false")
            set(CONFIG_ELEN_IS_${elen} "true")

            if(CONFIG_ELEN_IS_32 STREQUAL true)
              set(CONFIG__V__SUPPORT "Float_single")
            # Check if we can enable the full V extension.
            elseif((CONFIG_ELEN_IS_64 STREQUAL true) AND (vlen GREATER 64))
              set(CONFIG__V__SUPPORT "Full")
            # Otherwise fallback to Float_double for ELEN=64.
            elseif(CONFIG_ELEN_IS_64 STREQUAL true)
              set(CONFIG__V__SUPPORT "Float_double")
            endif()

            if(CONFIG_XLEN_IS_32 STREQUAL true)
                set(CONFIG__PHYSADDR__BITS 34)
                set(CONFIG__ASID__LEN 9)
                set(CONFIG__VMID__LEN 7)
                set(CONFIG__SDTRIG__MHVALUE__LEN 6)
                set(CONFIG__SDTRIG__SVALUE__LEN 16)
                set(CONFIG__STATEEN__P1P13 CSRBit_Writable)
            elseif(CONFIG_XLEN_IS_64 STREQUAL true)
                set(CONFIG__PHYSADDR__BITS 56)
                set(CONFIG__ASID__LEN 16)
                set(CONFIG__VMID__LEN 14)
                set(CONFIG__SDTRIG__MHVALUE__LEN 13)
                set(CONFIG__SDTRIG__SVALUE__LEN 32)
                # P1P13 only exists on RV32.
                set(CONFIG__STATEEN__P1P13 CSRBit_ReadOnlyZero)
            endif()

            # GEILEN is at most XLEN-1.
            math(EXPR CONFIG__H__GEILEN "${CONFIG__BASE__XLEN} - 1")

            configure_file(config.json.in ${CMAKE_CURRENT_BINARY_DIR}/${config_filename})

            install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${config_filename}
                DESTINATION ${CMAKE_INSTALL_DATADIR}/${CMAKE_PROJECT_NAME}/config
            )

            list(APPEND generated_config_filenames "${CMAKE_CURRENT_BINARY_DIR}/${config_filename}")
        endforeach()
    endforeach()
endforeach()

# Make list of config files visible to c_emulator build.
set(generated_config_filenames "${generated_config_filenames}" PARENT_SCOPE)

# Embed the default configs in a C header.
file(READ "${CMAKE_CURRENT_BINARY_DIR}/rv64d_v256_e64.json" DEFAULT_JSON)
file(READ "${CMAKE_CURRENT_BINARY_DIR}/rv32d_v256_e64.json" DEFAULT_JSON_RV32)
configure_file("default_config.h.in" "default_config.h" @ONLY)

add_library(default_config INTERFACE
    "default_config.h"
)

target_include_directories(default_config INTERFACE "${CMAKE_CURRENT_BINARY_DIR}")
