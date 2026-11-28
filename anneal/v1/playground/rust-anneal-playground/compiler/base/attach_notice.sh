#!/usr/bin/env bash

set -eu

NOTICE_FILE=$1 # full path to the notice file
TARGET_FILE=$2 # full patch to the target file

POSITION=${3:-"top"} # possible values: top or bottom; default value: top

function attach_notice() {
    echo "Attaching ${NOTICE_FILE} to ${TARGET_FILE} (position: ${POSITION})"

    if [[ "${POSITION}" == "bottom" ]]; then
        cat "${NOTICE_FILE}" >> "${TARGET_FILE}"
    else
        combined=$(mktemp)
        cat "${NOTICE_FILE}" "${TARGET_FILE}" >> "${combined}"
        chmod --reference "${TARGET_FILE}" "${combined}"
        mv "${combined}" "${TARGET_FILE}"
    fi

    echo "Done."
}

if [[ -f "${NOTICE_FILE}" ]] && [[ -f "${TARGET_FILE}" ]]; then
    attach_notice
fi
