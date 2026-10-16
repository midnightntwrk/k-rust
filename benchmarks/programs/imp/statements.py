#!/usr/bin/env python3
"""Print an IMP (imp-semantics) program of N assignment statements, for the parse ladder.

Statement i assigns to x<i> an expression over x<i-1>, y and the literal i, so the program
holds N statements, N identifiers on the left, and 3N leaves on the right.
"""

import sys


def main():
    count = int(sys.argv[1])
    for index in range(1, count + 1):
        print(f"x{index} = x{index - 1} + {index} * (y - {index});")


if __name__ == "__main__":
    main()
