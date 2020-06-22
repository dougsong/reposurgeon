#!/bin/sh
# Create artifical test load containing svn:ignore or
# svn:global-ignores.  Takes the property suffix - ignores or
# global-ignores - as first argument. Writes the stream to stdout.
#
# Normally global-ignores is a property that is created and interpreted
# on the client side only.  Forcing it with a propset is a bit
# perverse. Nevertheless we've had a request to handle this case

set -e

if [ "$1" != "ignore" ] && [ "$1" != "global-ignores" ]
then
    echo "$0: invalid argument"
fi

command -v realpath >/dev/null 2>&1 ||
    realpath() { test -z "${1%%/*}" && echo "$1" || echo "$PWD/${1#./}"; }

# Necessary so we can see repocutter
PATH=$(realpath ..):$(realpath .):${PATH}

trap 'rm -fr test-repo-$$ test-checkout-$$ test-checkout2-$$' EXIT HUP INT QUIT TERM

svnadmin create test-repo-$$
svn checkout --quiet "file://$(pwd)/test-repo-$$" test-checkout-$$

cd test-checkout-$$ >/dev/null || ( echo "$0: cd failed"/ exit 1 )

mkdir -p trunk/subdir
svn add --quiet trunk

echo "this file should be versioned" > trunk/keepme.txt
echo "this file should also be versioned" > trunk/subdir/keepme2.txt
echo "this file should be ignored" > trunk/ignoreme.foo
echo "this file should also be ignored" > trunk/subdir/ignoreme.foo

#svn status
# should include *.foo file:
# A       trunk
# ?       trunk/ignoreme.foo
# ?       trunk/keepme.txt
# A       trunk/subdir
# ?       trunk/subdir/ignoreme.foo
# ?       trunk/subdir/keepme2.txt

svn propset --quiet "svn:$1" "*.foo" trunk

#svn status
# should _not_ list *.foo file:
# A       trunk
# ?       trunk/keepme.txt
# A       trunk/subdir
# ?       trunk/subdir/keepme2.txt

# shellcheck disable=SC2035
svn add --quiet * --force
# should only add *.txt
# A         trunk/keepme.txt
# A         trunk/subdir/keepme2.txt

svn commit --quiet -m "Test svn:global-ignores property."

# test that the property is stored in the repository by using a new clean checkout
cd .. >/dev/null || ( echo "$0: cd failed"/ exit 1 )
svn checkout --quiet "file://$(pwd)/test-repo-$$" test-checkout2-$$
cd test-checkout2-$$ >/dev/null
echo "ignored" > trunk/something.foo
echo "ignored" > trunk/subdir/something.foo

# svn status
# should return empty

# create dump and ship to standard output
# shellcheck disable=2103
cd .. >/dev/null || ( echo "$0: cd failed"/ exit 1 )
# shellcheck disable=1117
svnadmin dump --quiet test-repo-$$  | repocutter -q testify | sed "1a\
\ ## svn:$1 property-setting example
"

# end
