#!/bin/sh
#
# Extract the version from NEWS.adoc, presented on standard input
# so there's a single authority for it.  Ship it to standard output
# bare or in a Go wrapper.

mode=$1

while IFS=: read -r version _; do
    case $version in [0-9]*) break ;; esac
done

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
    *)  printf '%s\n' "$version"
	;;
esac

# end
