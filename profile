#!/bin/zsh

THIS_DIR="${0:A:h}"

cd "${THIS_DIR}"

# install the profile visualizor if necessary
# stack install profiteur

# build the project in profile mode and run the executable `-p` option
"${THIS_DIR}/debug" --profile +RTS -p -RTS $@

PROF_FILE=$(ls -t *.prof | head -n1)
[ -f "${PROF_FILE}" ] || exit 1

profiteur "${PROF_FILE}"

type xdg-open &>/dev/null && xdg-open "${PROF_FILE}.html"
