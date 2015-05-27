## Legacy-ID pattern-matching
read <legacy.fi
print Initially no sourcetype is set, so =N should be empty
=N resolve
sourcetype cvs
print Expect 2 CVS results
=N list
sourcetype svn
print Expect 4 SVN results
=N list
