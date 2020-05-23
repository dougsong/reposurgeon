#!/bin/sh
## Test mailbox analysis in repomapper

trap 'rm -f /tmp/contrib$$ /tmp/mailbox$$' EXIT HUP INT QUIT TERM

cat >/tmp/contrib$$ <<EOF
esr = esr <esr>
EOF

cat >/tmp/mailbox$$ <<EOF
From esr Fri May 22 18:01:14 -0400 2020
Date: Fri, 22 May 2020 18:01:14 -0400
From: "Eric S. Raymond" <esr@thyrsus.com>
To: daniel.waddington@ibm.com
Subject: Ae you one of the authors of Proteus?

Ae you one of the authors of Proteus?  I've had it recommended to me
as a tool for high-quality source translation, but web searches are
not turning up the source code. What is its present status?
-- 
		<a href="http://www.catb.org/~esr/">Eric S. Raymond</a>

No kingdom can be secured otherwise than by arming the people.  The possession
of arms is the distinction between a freeman and a slave. 
        -- "Political Disquisitions", a British republican tract of 1774-1775
EOF

# The esr line should be filled in with a fullname
${REPOMAPPER:-repomapper} /tmp/contrib$$ /tmp/mailbox$$

#end
