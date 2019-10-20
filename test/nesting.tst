## Test subversion tags nested below the root
branchify cpp-msbuild/trunk cpp-msbuild/branches/* cpp-msbuild/tags/*
branchmap \
   :cpp-msbuild/trunk/:heads/master: \
   :cpp-msbuild/tags/(.*)/:tags/\1:
read <nesting.svn
prefer git
write -
