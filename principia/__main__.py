"""Entry point for ``python -m principia``."""

import sys

from .cli import main

if __name__ == "__main__":
    sys.exit(main())
