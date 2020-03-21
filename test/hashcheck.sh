#!/bin/sh
## Verify git hash computation

set -e
repo=${PWD}/hashcheck-git-$$

trap 'rm -fr ${repo}' EXIT HUP INT QUIT TERM

command -v git >/dev/null 2>&1 || ( echo "$0: git is not installed"; exit 1 )

git init --quiet "${repo}"
cd "${repo}" >/dev/null
# Required for CI
git config user.email jrh@random.net
git config user.name "J. Random Hacker"
mkdir some
echo 'Hello, World!' >some/file.txt
git add some/file.txt

# shellcheck disable=SC2034
GIT_AUTHOR_NAME="John Doe" GIT_AUTHOR_EMAIL="john@doe.com"
# shellcheck disable=SC2034
GIT_AUTHOR_DATE="1234567890" GIT_COMMITTER_NAME="John Doe"
# shellcheck disable=SC2034
GIT_COMMITTER_EMAIL="john@doe.com" GIT_COMMITTER_DATE="1234567890"
TZ=UTC
export GIT_AUTHOR_NAME GIT_AUTHOR_EMAIL GIT_AUTHOR_DATE GIT_COMMITTER_NAME TZ

git commit --quiet  -a -m "Lovely commit message"

# Verify blob hash computation
filehash=$(git hash-object some/file.txt)
# shellcheck disable=SC2046
set -- $(reposurgeon 'read .' hash)

if [ "${filehash}" != "$2" ]
then
    echo "hashcheck: file and synthetic hash for some/file.txt do not match." >&2
    exit 1
fi

# end
