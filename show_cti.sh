#!/bin/bash

# uses diff to display the latext counterexample to induction found by Apalache

TRACE=$(find ./_apalache-out -type f -name "violation1.tla" -printf "%T@ %p\n" | sort -n | tail -n 1 | cut -d' ' -f2-)

PRE_FILE=$(mktemp)
POST_FILE=$(mktemp)

awk -v RS="" 'NR==4' ${TRACE} | sed '1,2d' >> $PRE_FILE
awk -v RS="" 'NR==5' ${TRACE} | sed '1,2d' >> $POST_FILE
# diff --colors=always --side-by-side --width=$COLUMNS $PRE_FILE $POST_FILE | less -REX
nvim -d $PRE_FILE $POST_FILE 
