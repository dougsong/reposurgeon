## Test subversion tags nested below the root
verbose 0
branchify cpp-msbuild/trunk cpp-msbuild/branches/* cpp-msbuild/tags/*
branchify_map \
   :cpp-msbuild/trunk/:heads/master: \
   :cpp-msbuild/tags/(.*)/:tags/\1:
read <nesting.svn
prefer git
write -
