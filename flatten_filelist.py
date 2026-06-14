#!/usr/bin/env python3
"""Flatten Verilog filelists for veri-kompass.

The caller should source any project environment setup before running this
script. Environment variables in filelist entries are expanded from the current
process environment.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Iterable


SOURCE_EXTENSIONS = {".v", ".sv"}
FILELIST_EXTENSIONS = {".f", ".flist", ".list"}
FILELIST_OPTIONS = {"-f", "-F", "-file", "--filelist"}
NESTED_FILELIST_PREFIX = "@filelist:"


class FilelistError(RuntimeError):
    """Raised when filelist expansion cannot continue."""


class FilelistFlattener:
    def __init__(
        self,
        root: Path,
        source_extensions: Iterable[str] = SOURCE_EXTENSIONS,
        filelist_extensions: Iterable[str] = FILELIST_EXTENSIONS,
    ) -> None:
        self.root = root.resolve()
        self.source_extensions = {self._normalize_ext(ext) for ext in source_extensions}
        self.filelist_extensions = {
            self._normalize_ext(ext) for ext in filelist_extensions
        }
        self.seen_filelists: set[Path] = set()
        self.seen_modules: set[str] = set()
        self.files: list[Path] = []
        self.warnings: list[str] = []

    @staticmethod
    def _normalize_ext(ext: str) -> str:
        ext = ext.strip()
        if not ext:
            return ext
        return ext if ext.startswith(".") else f".{ext}"

    def flatten(self, filelist: Path) -> list[Path]:
        self._read_filelist(filelist.resolve())
        return self.files

    def _read_filelist(self, filelist: Path) -> None:
        if filelist in self.seen_filelists:
            return
        if not filelist.is_file():
            raise FilelistError(f"Filelist not found: {filelist}")
        self.seen_filelists.add(filelist)

        base = filelist.parent
        lines = filelist.read_text(encoding="utf-8", errors="replace").splitlines()
        for line_no, line in enumerate(lines, 1):
            for entry in self._entries_from_line(line):
                self._handle_entry(entry, base, filelist, line_no)

    def _entries_from_line(self, line: str) -> list[str]:
        clean = self._strip_comments(line).strip()
        if not clean or clean.startswith("#"):
            return []

        tokens = clean.split()
        entries: list[str] = []
        idx = 0
        while idx < len(tokens):
            token = tokens[idx]
            if token in FILELIST_OPTIONS:
                if idx + 1 >= len(tokens):
                    raise FilelistError(f"Missing filelist path after {token}")
                entries.append(f"{NESTED_FILELIST_PREFIX}{tokens[idx + 1]}")
                idx += 2
            elif any(token.startswith(f"{opt}=") for opt in FILELIST_OPTIONS):
                entries.append(
                    f"{NESTED_FILELIST_PREFIX}{token.split('=', 1)[1]}"
                )
                idx += 1
            elif token.startswith("-f") and len(token) > 2:
                entries.append(f"{NESTED_FILELIST_PREFIX}{token[2:]}")
                idx += 1
            elif token.startswith("-F") and len(token) > 2:
                entries.append(f"{NESTED_FILELIST_PREFIX}{token[2:]}")
                idx += 1
            elif token.startswith("+incdir+") or token.startswith("+define+"):
                idx += 1
            elif token.startswith("+") or token.startswith("-"):
                idx += 1
            else:
                entries.append(token)
                idx += 1
        return entries

    @staticmethod
    def _strip_comments(line: str) -> str:
        return re.sub(r"//.*$", "", line)

    def _handle_entry(
        self, entry: str, base: Path, filelist: Path, line_no: int
    ) -> None:
        is_nested = False
        raw_path = entry
        if entry.startswith(NESTED_FILELIST_PREFIX):
            is_nested = True
            raw_path = entry[len(NESTED_FILELIST_PREFIX) :]

        expanded = os.path.expandvars(os.path.expanduser(raw_path))
        if "$" in expanded:
            raise FilelistError(
                f"Unexpanded environment variable in {filelist}:{line_no}: {raw_path}"
            )

        path = self._resolve_path(expanded, base)
        suffix = path.suffix.lower()
        if is_nested or suffix in self.filelist_extensions:
            self._read_filelist(path)
        elif suffix in self.source_extensions:
            self._add_source(path, filelist, line_no)
        else:
            self.warnings.append(
                f"skip non-source entry at {filelist}:{line_no}: {raw_path}"
            )

    def _resolve_path(self, token: str, base: Path) -> Path:
        path = Path(token)
        candidates = [path] if path.is_absolute() else [base / path, self.root / path]
        for candidate in candidates:
            resolved = candidate.resolve()
            if resolved.exists():
                return resolved
        return candidates[0].resolve()

    def _add_source(self, path: Path, filelist: Path, line_no: int) -> None:
        if not path.is_file():
            raise FilelistError(f"Source file not found at {filelist}:{line_no}: {path}")
        module_name = path.stem
        if module_name in self.seen_modules:
            self.warnings.append(
                f"skip duplicate module {module_name} at {filelist}:{line_no}: {path}"
            )
            return
        self.seen_modules.add(module_name)
        self.files.append(path)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Expand environment variables and recursively flatten Verilog filelists."
    )
    parser.add_argument("input", type=Path, help="Input filelist")
    parser.add_argument("output", type=Path, help="Output flattened filelist")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="Project root for resolving root-relative entries (default: current dir)",
    )
    parser.add_argument(
        "--extensions",
        default="v,sv",
        help="Comma-separated source extensions to keep (default: v,sv)",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    extensions = [ext.strip() for ext in args.extensions.split(",") if ext.strip()]
    flattener = FilelistFlattener(args.root, source_extensions=extensions)

    try:
        files = flattener.flatten(args.input)
    except FilelistError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "".join(f"{path}\n" for path in files),
        encoding="utf-8",
    )
    for warning in flattener.warnings:
        print(f"warning: {warning}", file=sys.stderr)
    print(f"wrote {len(files)} files to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
