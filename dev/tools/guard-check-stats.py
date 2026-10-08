#!/usr/bin/env python3
"""Summarize `rocq compile -d guard-check` logs as a Markdown table.

Usage: guard-check-stats.py [--root SOURCE_ROOT] [LOG ...]
Read stdin when no logs are supplied, or use '-' among the log arguments.
"""

import argparse
from collections import Counter
import html
import json
import os
from pathlib import Path
import re
import sys


PREFIX = "ROCQ_GUARD_CHECK "
ANSI_ESCAPE = re.compile(r"\x1b\[[0-9;]*m")


def read_events(lines, source):
    """Ignore unrelated output; reject malformed diagnostic records."""
    for number, line in enumerate(lines, 1):
        line = ANSI_ESCAPE.sub("", line).strip()
        if line.startswith("Debug:"):
            line = line[len("Debug:"):].lstrip()
        if not (line.startswith(PREFIX) or line == PREFIX.rstrip()):
            continue
        try:
            event = json.loads(line[len(PREFIX):])
            if (not isinstance(event, dict) or set(event) != {"file", "name"}
                    or not all(isinstance(value, str) for value in event.values())):
                raise ValueError("expected string fields 'file' and 'name'")
        except (ValueError, TypeError) as error:
            raise ValueError(f"{source}:{number}: invalid guard-check record: {error}") from error
        yield os.path.normpath(event["file"]), event["name"]


def display_path(filename, root):
    if root is None:
        return filename
    path = Path(filename).resolve()
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return str(path)


def code(text):
    # Keep filenames and binder names within a single Markdown table cell.
    escaped = html.escape(text).replace("|", "&#124;")
    escaped = escaped.replace("\n", "&#10;").replace("\r", "&#13;")
    return f"<code>{escaped}</code>"


def write_table(counts, output, root=None):
    print("| File name | Fixpoint name | Number of guard checks |", file=output)
    print("| --- | --- | ---: |", file=output)
    rows = sorted((display_path(filename, root), name, count)
                  for (filename, name), count in counts.items())
    for filename, name, count in rows:
        print(f"| {code(filename)} | {code(name)} | {count} |", file=output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="*", help="compiler/build logs; '-' reads stdin")
    parser.add_argument("--root", type=Path, help="display paths relative to this source root")
    args = parser.parse_args()
    logs = args.logs or ["-"]
    if logs.count("-") > 1:
        parser.error("stdin may only be read once")
    counts = Counter()
    try:
        for filename in logs:
            if filename == "-":
                counts.update(read_events(sys.stdin, "<stdin>"))
            else:
                with open(filename, encoding="utf-8") as stream:
                    counts.update(read_events(stream, filename))
    except (OSError, UnicodeError, ValueError) as error:
        parser.error(str(error))
    root = args.root.resolve() if args.root is not None else None
    write_table(counts, sys.stdout, root)


if __name__ == "__main__":
    main()
