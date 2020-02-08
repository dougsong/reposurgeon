## Test dissection of multiproject repo
branchify project1/trunk project1/branches/* project1/tags
branchmap :project1/trunk:trunk: :project1/tags:tags: :project1/branches:branches:
read <svncheck4.svn
prefer git
write -
