# reposurgeon - a repository surgeon

`reposurgeon` enables risky operations that version-control systems
don't want to let you do, such as (a) editing past comments and metadata,
(b) excising commits, (c) coalescing commits, and (d) removing files and
subtrees from repo history. The original motivation for `reposurgeon`
was to clean up artifacts created by repository conversions.

`reposurgeon` is also useful for scripting very high-quality conversions
from Subversion.  It is better than `git-svn` at tag lifting,
automatically cleaning up `cvs2svn` conversion artifacts, dealing with
nonstandard repository layouts, recognizing branch merges, handling
mixed-branch commits, and generally at coping with Subversion's many
odd corner cases.  Normally Subversion repos should be analyzed at a
rate of upwards of ten thousand commits per minute.

`repodiffer` is a program that reports differences between repository
histories. It uses a `diff(1)`-like algorithm to identify spans of
identical revisions, and to pick out revisions that have been
changed or deleted or inserted. It may be useful for comparing the
output of different repository-conversion tools in detail.

Another auxiliary program, `repotool`, performs various useful
operations such as checkouts and tag listing in a VCS-independent
manner.  Yet another, `repomapper`, assists in automatically preparing
contributor maps of CVS and SVN repositories.

A 'patchpipe' program supports converting among version-control patch
formats.

This distribution supports a generic conversion workflow using these
tools, and includes the DVCS Migration Guide that describes how to use it.

The file 'reposurgeon-git-aliases` can be appended to your `~/.gitconfig' to
support working directly with action stamps in git.

Finally, an Emacs Lisp mode with useful functions for editing large
comment mailboxes is included.

There is an extensive regression-test suite in the `test/` directory.
To test the correctness of this software, ensure that `pylint`
is installed and then type `make check`.

See `reporting-bugs.asc` for advice on how to troubleshoot problems
with `reposurgeon` and report bugs.

The main `reposurgeon` website along with the documentation in HTML files
lives at [www.catb.org/esr/reposurgeon/](http://www.catb.org/esr/reposurgeon/).

The files Dockerfile, .dockerignore, requirements.txt, and .gitlab-ci.yml
are not distributed; they are configuration for test builds on GitLab's
CI machinery.
