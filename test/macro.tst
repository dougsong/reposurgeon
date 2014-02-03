## Test the macro facility
read <simple.fi
define fubar list
:49 do fubar
undefine fubar
define fubaz {
inspect {0}
}
do fubaz :49
undefine fubaz
