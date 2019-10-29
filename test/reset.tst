## Reset tests
set echo
set relax
read <be-bookmarks.fi
=R index
reset D move :6
reset A delete
reset B rename Z
27 reset default move :10
=R index

# error: unknown reset name
reset X delete
# error: move multiple resets
reset default move :15
# error: non-singleton target
reset D move :6,:10,:15
# error: empty new name
reset C rename
# error: reference collision
reset C rename D
# error: bogus verb
reset C fizzle
