#!/bin/sh
#
# Extract the version from NEWS.adoc, presented on standard input
# so there's a single authority for it.  Ship it to standard output
# bare or in a Go wrapper.

mode=$1

while read -r line
do
    if expr "$line" : "^[0-9]" 1>/dev/null
    then
	break
    fi
done

# shellcheck disable=2086
IFS=: set -- $line
# shellcheck disable=2086,2116
version=$(echo $1)

case $mode in
    -g)
	cat <<EOF
/*
 * Copyright by Eric S. Raymond
 * SPDX-License-Identifier: BSD-2-Clause
 */

package main

const version = "$version"

// end
EOF
	;;
    *)  echo "$version"
	;;
esac

# end
