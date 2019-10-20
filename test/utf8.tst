## Test matching non standard ASCII chars
read <utf8.fi
set interactive
/Baldoví/a resolve Should match
/György/c resolve Should match
/Peña/a resolve Should match
/Александр/c resolve Should match
/李/c resolve Should match
