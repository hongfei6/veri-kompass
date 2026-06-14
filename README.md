[![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![MELPA](https://melpa.org/packages/veri-kompass-badge.svg)](https://melpa.org/#/veri-kompass)

# veri-kompass

GNU Emacs extension that parse a Verilog design and provide some navigation facilities like hierarchy bar and wire following capabilities.
veri-kompass parse has a built-in parser, because of that does not depends on external software.
You can point it at either a project directory or at a Verilog filelist file.

[![asciicast](https://asciinema.org/a/191880.png)](https://asciinema.org/a/191880)

## Installation

Clone this repo somewhere

Add into your .emacs

(add-to-list 'load-path "path-to-veri-kompass-here")
(require 'veri-kompass)
;; Enable veri kompass minor mode mode
(add-hook 'verilog-mode-hook 'veri-kompass-minor-mode)

## Usage

To start using veri-kompass:

- M-x veri-kompass
- Provide your folder directory or a Verilog filelist (for example `dut.f`)
- Select your top module

For project filelists that depend on shell environment variables or nested
filelists, source the project setup first and generate a flattened filelist:

```sh
source path/to/project_setup.sh
scripts/flatten_filelist.py path/to/rtl.f /tmp/rtl.flat.f --root path/to/project
```

Then give `/tmp/rtl.flat.f` to `M-x veri-kompass`.

Once in the hieracky bar select modules with RET to mark and visit them

In verilog sources follow signals as follow:

- C-c d to search for the drivers of the symbol at point
- C-c l to search for the loads of the symbol at point
- C-c b to go back to the previous confirmed trace jump
- C-c f to go forward after trace back

## Recent Enhancements

Features:

- Accept either a project directory or a Verilog filelist, including common
  `.f` entries with include/define options and project-root-relative paths.
- Provide `scripts/flatten_filelist.py` to expand shell environment variables,
  recursively flatten nested filelists, and remove duplicate module basenames
  while preserving first-seen source order.
- Show driver/load ambiguity in a previewable trace selection buffer; use
  `C-j` / `C-k` to preview candidates and `RET` to commit the jump.
- Continue driver tracing through same-name input port connections when a
  child input is wired directly to the parent signal.
- Continue load tracing through child input/inout port connections, including
  renamed named-port connections such as `.child_clk(clk)`.
- Keep trace jump history for confirmed driver/load jumps, with `C-c b` and
  `C-c f` for back/forward navigation.
- Highlight the current trace target signal during preview, jump, and trace
  history navigation.
- Report hierarchy warnings when an instantiated module cannot be found,
  instead of silently omitting it from the hierarchy view.

Bug fixes:

- Recognize uppercase Verilog identifiers in modules and instances.
- Parse module headers and parameterized instances written as `# (` with
  whitespace between `#` and `(`.
- Preserve candidate source positions while building snippets, fixing preview
  and `RET` jumps in driver/load selection buffers.
- Recognize common ANSI input port declarations with aligned whitespace and
  optional type/range modifiers.
- Avoid treating child output connections such as `.out(foo)` as signal loads.
- Follow loads from a marked child output port up to the parent signal before
  reporting a top/current module boundary.
- Follow drivers through child output/inout port connections instead of
  stopping at the parent instance connection line.
- Keep symbol lookup stable around port declaration punctuation, so trailing
  commas do not make driver/load tracing search for direction keywords.
- Resolve the full signal name when point is on the first, middle, or last
  character of an identifier.
- Ignore commented-out code when searching drivers, loads, declarations, and
  named port connections.
- Keep the current hierarchy selection visibly marked with a dedicated overlay,
  instead of relying on delayed regexp fontification.
- Report top/current module port boundaries clearly when driver/load tracing
  cannot continue past an input/output port.
