#!/bin/zsh
#
# requires the profile visualizor `profiteur`

THIS_DIR="${0:A:h}"

# build the project in profile mode and run the executable `-p` option
"${THIS_DIR}/xenon" +RTS -p -RTS $@

PROF_FILE=$(ls -t ${THIS_DIR}/*.prof | head -n1)
[ -f "${PROF_FILE}" ] || exit 1

profiteur "${PROF_FILE}"

type xdg-open &>/dev/null && xdg-open "${PROF_FILE}.html"
