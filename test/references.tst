## Test authors command, heredocs, and comment editing
read nut.svn
authors read <<EOF
esr-guest = Eric S. Raymond <esr-guest@alioth.debian.org>
lestat-guest = David Goncalves <david@lestat.st>
agordeev-guest = Alexander Gordeev <agordeev-guest@alioth.debian.org>
emilienkia-guest = Emilien Kia <emilienkia-guest@alioth.debian.org>
prachi-guest = Prachi Gandhi <prachi-guest@alioth.debian.org>
praveenkumar-guest = Praveen Kumar <praveenkumar-guest@alioth.debian.org>
msoltyspl-guest = Michal Soltys <msoltyspl-guest@alioth.debian.org>
keyson-guest = Kjell Claesson <keyson-guest@alioth.debian.org>
chetanagarwal-guest = Chetan Agarwal <chetanagarwal-guest@alioth.debian.org>
fbohe-guest = Frederic Bohe <fbohe-guest@alioth.debian.org>
aquette = Arnaud Quette <arnaud.quette@free.fr>
clepple-guest = Charles Lepple <clepple+nut@gmail.com>
adkorte-guest = Arjen de Korte <adkorte-guest@alioth.debian.org>
(no author) = no author <nobody@networkupstools.org>
selinger-guest = Peter Selinger <selinger@users.sourceforge.net>
carlosefr-guest = Carlos Rodrigues <cefrodrigues@gmail.com>
nba-guest = Niels Baggesen <nba@users.sourceforge.net>
lyrgard-guest = Jonathan Dion <lyrgard-guest@alioth.debian.org>
jongough-guest = Jon Gough <jon.gough@eclipsesystems.com.au>
EOF
mailbox_in nut.mbox
references lift
write
