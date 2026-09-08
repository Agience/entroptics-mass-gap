"""Make this process's console able to print the characters the reads are named with.

The certification scripts print their quantities under the names the paper uses -- `beta`, `kappa_0`,
`Delta`, `mu`, `rho'` -- as the actual characters.  On Windows the default console encoding is the
ANSI code page (cp1252 here), which cannot encode any of them, so `print` raises
`UnicodeEncodeError` and the script dies partway through its table.  That turns a certification into
a crash for a reason that has nothing to do with the certificate.

`PYTHONIOENCODING=utf-8` on the invocation fixes it too, but a script that only runs under an
environment variable someone has to remember is a script that fails for the next person.  Python 3.7+
lets the process fix its own streams, so it does.

Import for the effect, before the first print:

    import console  # noqa: F401  -- UTF-8 stdout, so the read names print on any console
"""
from __future__ import annotations

import sys


def use_utf8() -> None:
    """Re-encode stdout/stderr as UTF-8 where the platform left them narrower.

    `errors="replace"` on the way out: a console that genuinely cannot render a glyph should show a
    replacement character, not abort a run that has already done the work.
    """
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:                     # a redirected/wrapped stream may not offer it
            continue
        try:
            reconfigure(encoding="utf-8", errors="replace")
        except (ValueError, OSError):               # already detached, or not re-configurable
            pass


use_utf8()
