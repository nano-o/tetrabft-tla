#!/bin/bash

TRACE=$(find ./_apalache-out -type f -name "*.tla" -printf "%T@ %p\n" | sort -n | tail -n 1 | cut -d' ' -f2-)

PRE_FILE=$(mktemp)
POST_FILE=$(mktemp)

echo $TRACE > $PRE_FILE
echo $TRACE > $POST_FILE
awk -v RS="" 'NR==4' ${TRACE} | sed '1,2d' >> $PRE_FILE
awk -v RS="" 'NR==5' ${TRACE} | sed '1,2d' >> $POST_FILE
nvim -d $PRE_FILE $POST_FILE
