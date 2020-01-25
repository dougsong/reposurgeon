## Check backreferences are dropped for ops before deletealls
read <discard-deleteall.fi
# force a canonicalization of commit :4
:4 tagify --canonicalize
write -
