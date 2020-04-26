## Test the macro facility
set echo
set testmode
read <simple.fi
set interactive
print Test that we can define and see macro definitions
define fubar list
define
print Test that invoking the macro produces output
:49 do fubar
print Test that undefining the only macro removes it from the internal list
undefine fubar
define
print Test multiline macroexpansion
define fubaz {
{0} list
}
do fubaz :49
undefine fubaz
print Tests complete
