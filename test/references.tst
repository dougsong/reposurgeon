## Test authors read, legacy-ID refs, heredocs, comment editing
set relax
read <references.svn
set interactive
<1>,<2>,<13> resolve
<1>..<2> resolve
<3>..<7> resolve
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
tobi = Tobias Schlüter <tobias.schlueter@physik.uni-muenchen.de> Europe/Berlin
tocarip = Ilya Tocar <tocarip@gmail.com> Europ/Moscow
tomby = Tomas Bily <tbily@suse.cz> Europe/Prague
EOF
msgin <<EOF
------------------------------------------------------------------------------
Author: Peter Selinger <selinger@users.sourceforge.net>
Author-Date: Sat 04 Mar 2006 17:44:41 +0000

backported [[SVN:352]] from trunk to Testing

newhidups: rewrote logical-to-physical value conversion. Rewrote
extraction of logical values from report. Added Kelvin-to-Celsius
conversion. Tweaked APC date conversion. Back-UPS BF500 support.
Deleted unused items in HIDItem structure.
EOF
<352> inspect
references lift
prefer git
clear interactive
write -
