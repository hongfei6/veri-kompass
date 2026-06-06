;;; veri-kompass.el --- verilog codebase navigation facility -*- lexical-binding:t -*-

;; Copyright (C) 2018 Andrea Corallo

;; Maintainer: andrea_corallo@yahoo.it
;; Package: veri-kompass
;; Homepage: https://gitlab.com/koral/veri-kompass
;; Version: 0.2
;; Package-Requires: ((emacs "25") (cl-lib "0.5") (org "8.2.0"))
;; Keywords: languages, extensions, verilog, hardware, rtl

;; This file is not part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Provide verilog codebase navigation facility.
;; Including a hierarchy sidebar and functions to follow drivers and loads
;; within the design.

;;; Code:

(require 'custom)
(require 'cl-macs)
(require 'pcase)
(require 'sort)
(require 'cl-extra)
(require 'subr-x)
(require 'files)
(require 'format)
(require 'whitespace)
(require 'simple)
(require 'message)
(require 'thingatpt)
(require 'org)
(require 'easy-mmode)
(require 'derived)
(require 'hashtable-print-readable)

(eval-when-compile
  (require 'ert nil t))

(defgroup veri-kompass nil
  "Customization options for veri-kompass."
  :prefix "veri-kompass"
  :group 'languages)

(defcustom veri-kompass-top ""
  "Default top module name."
  :type 'string
  :group 'veri-kompass)

(defcustom veri-kompass-extention-regexp ".+\\.s?v$"
  "Regexp matching project files."
  :type 'string
  :group 'veri-kompass)

(defcustom veri-kompass-skip-regexp "^.*CONFORMTO.*$"
  "Regexp matching files to be skip."
  :type 'string
  :group 'veri-kompass)

(defcustom veri-kompass-trace-history-limit 100
  "Maximum number of trace jumps kept in history."
  :type 'integer
  :group 'veri-kompass)

(defface veri-kompass-inst-marked-face
  '((t :foreground "red1"))
  "Face for marking instance selected."
  :group 'veri-kompass)

(defface veri-kompass-trace-highlight-face
  '((t :inherit highlight :weight bold))
  "Face for the current trace target signal."
  :group 'veri-kompass)

(defvar veri-kompass-module-list nil)

(defvar veri-kompass-module-hier nil)

(defvar veri-kompass-mod-str-hash nil
  "This hash contains module structure hashed per module name.")

(defconst veri-kompass-bar-name "*veri-kompass-bar*")

(defconst veri-kompass-load-select-buffer-name "*veri-kompass-load-select*"
  "Buffer displaying the list of loads when multiple entries exist.")

(defconst veri-kompass-ignore-keywords '("if" "task" "assert" "disable" "define" "posedge"
                                         "negedge" "int" "for" "logic" "wire" "reg"
                                         "module" "endmodule"))

(defconst veri-kompass-ident-regex "[a-zA-Z_][a-zA-Z0-9_$]*"
  "Regexp matching a common Verilog identifier.")

(defconst veri-kompass-sym-regex veri-kompass-ident-regex
  "Regexp matching a Verilog symbol at point.")

(defconst veri-kompass-ops-regex "[\]\[ ()|&\+-/%{}=<>]")

(defconst veri-kompass-module-import-clause-regexp
  "\\(?:[[:space:]\n]+import[[:space:]\n]+[^;]+;\\)*"
  "Regexp matching optional SystemVerilog import clauses in a module header.")

(defconst veri-kompass-module-start-regexp
  (concat "^[[:space:]]*module[[:space:]\n]+\\(" veri-kompass-ident-regex "\\)"
          veri-kompass-module-import-clause-regexp))

(defconst veri-kompass-module-end-regexp "^[[:space:]]*endmodule")

(defconst veri-kompass-parameter-start-regexp "#[[:space:]\n]*("
  "Regexp matching the start of a Verilog parameter override block.")

(defvar veri-kompass-hier nil
  "Holds the design hierarchy.")

(defvar veri-kompass-hier-warnings nil
  "Warnings collected while building the hierarchy.")

(defvar veri-kompass-curr-select nil
  "Holds the position of the current instance selected (if any).")

(defvar veri-kompass-history nil
  "Holds the instance selection history.")

(defvar veri-kompass-trace-back-stack nil
  "Trace jump back history.")

(defvar veri-kompass-trace-forward-stack nil
  "Trace jump forward history.")

(defvar veri-kompass-trace-history--in-navigation nil
  "Non-nil while trace history navigation is moving point.")

(defvar veri-kompass-trace-highlight-overlay nil
  "Overlay highlighting the current trace target signal.")

(cl-defstruct (veri-kompass-mod-inst (:copier nil))
  "Holds a module instantiations."
  inst-name mod-name file-name line)

(cl-defstruct (veri-kompass-trace-candidate (:copier nil))
  "Holds one driver/load trace result."
  direction label marker file line snippet reason trace)

(defmacro veri-kompass-within-current-module (&rest code)
  "Execute code CODE narrowing into the current module definition."
  `(let* ((point-orig (point))
          (start (re-search-backward veri-kompass-module-start-regexp nil t))
          (end (re-search-forward veri-kompass-module-end-regexp nil t)))
     (goto-char point-orig)
     (if (and start end)
         (save-restriction
           (narrow-to-region start end)
           ,@code)
       (error "Not in a module definition?"))))

(defmacro veri-kompass-make-thread (f)
  "Make thread if threading is available.
Argument F is the thread name."
  (if (fboundp 'make-thread)
      `(make-thread ,f)
    `(funcall ,f)))

(defmacro veri-kompass-thread-yield ()
  "Yield a thread if threading is available."
  (when (fboundp 'thread-yield)
    '(thread-yield)))

(defun veri-kompass-completing-read (msg candidates &optional buff-name)
  "Complete user input between CANDIDATES using helm if available.
MSG is a string to prompt with.
BUFF-NAME is the buffer name created in case helm is used."
  (if (fboundp 'helm)
      (progn
	(require 'helm-source)
	(helm :sources (helm-build-sync-source msg
			 :candidates candidates)
	      :buffer buff-name))
    (completing-read msg candidates)))

(defun veri-kompass-sym-classify-at-point ()
  "Classify if a symbol is l-val or r-val."
  (save-excursion
    (re-search-forward "[=;]" nil t)
    (pcase (aref (match-string-no-properties 0) 0)
      (?\= 'l-val)
      (?\; 'r-val))))

(defun veri-kompass--identifier-bounds-near-point ()
  "Return bounds of the Verilog identifier nearest point."
  (let ((origin (point))
        (line-start (line-beginning-position))
        (chars "a-zA-Z0-9_$"))
    (save-excursion
      (cond
       ((looking-at veri-kompass-ident-regex)
        (cons (match-beginning 0) (match-end 0)))
       ((and (> origin line-start)
             (save-excursion
               (backward-char)
               (looking-at (concat "[" chars "]"))))
        (skip-chars-backward chars line-start)
        (when (looking-at veri-kompass-ident-regex)
          (cons (match-beginning 0) (match-end 0))))
       (t
        (skip-chars-backward " \t,;)]" line-start)
        (when (and (> (point) line-start)
                   (save-excursion
                     (backward-char)
                     (looking-at (concat "[" chars "]"))))
          (skip-chars-backward chars line-start)
          (when (looking-at veri-kompass-ident-regex)
            (cons (match-beginning 0) (match-end 0)))))))))

(defun veri-kompass-sym-at-point ()
  "Return an a-list containing (sym-name . 'r-val) or (sym-name . 'l-val)."
  (let ((bounds (veri-kompass--identifier-bounds-near-point)))
    (if (not bounds)
        (save-excursion
          (re-search-backward veri-kompass-ops-regex nil t)
          (re-search-forward veri-kompass-sym-regex nil t)
          (cons (match-string-no-properties 0)
                (veri-kompass-sym-classify-at-point)))
      (save-excursion
        (goto-char (car bounds))
        (cons (buffer-substring-no-properties (car bounds) (cdr bounds))
              (veri-kompass-sym-classify-at-point))))))

(defun veri-kompass--search-direct-drivers (sym)
  "Return direct assignment drivers for SYM in the current restriction."
  (let ((res ()))
    (goto-char (point-max))
    (while (re-search-backward
            (concat
             "\\(\\<"
             sym
             "\\>\\)[[:space:]]*\\(\\[.*\\] +\\)?\\(=\\|<=\\)[^=].*")
            nil t)
      (let ((pos (match-beginning 0)))
        (push (cons (veri-kompass--line-snippet) pos)
              res)))
    res))

(defun veri-kompass--search-input-drivers (sym)
  "Return input port declarations for SYM in the current restriction."
  (veri-kompass--port-declarations 'input sym))

(defun veri-kompass--port-declarations (direction sym)
  "Return port declarations for DIRECTION and SYM in the current restriction."
  (let ((res ()))
    (goto-char (point-min))
    (while (re-search-forward
            (concat
             "\\<" (symbol-name direction) "\\>"
             "\\(?:[[:space:]]+\\(?:wire\\|reg\\|logic\\|signed\\|unsigned\\)\\)*"
             "\\(?:[[:space:]]+\\[[^]]+\\]\\)?"
             "[[:space:]]+\\("
             sym
             "\\)")
            nil t)
      (let ((pos (match-beginning 1)))
        (push (cons (veri-kompass--line-snippet) pos)
              res)))
    (nreverse res)))

(defun veri-kompass--input-port-p (sym)
  "Return non-nil when SYM is an input port in the current restriction."
  (save-excursion
    (veri-kompass--port-declarations 'input sym)))

(defun veri-kompass--output-port-p (sym)
  "Return non-nil when SYM is an output port in the current restriction."
  (save-excursion
    (veri-kompass--port-declarations 'output sym)))

(defun veri-kompass--point-on-port-declaration-p (direction sym)
  "Return non-nil when point is on DIRECTION port declaration for SYM."
  (let ((point-orig (point)))
    (save-excursion
      (cl-some (lambda (candidate)
                 (let ((start (cdr candidate))
                       (end (+ (cdr candidate) (length sym))))
                   (and (<= start point-orig)
                        (<= point-orig end))))
               (veri-kompass--port-declarations direction sym)))))

(defun veri-kompass--module-name-at-point-safe ()
  "Return current module name, or nil when point is not inside a module."
  (save-excursion
    (when (re-search-backward veri-kompass-module-start-regexp nil t)
      (match-string-no-properties 1))))

(defun veri-kompass--message-port-boundary (sym direction)
  "Message that SYM is a DIRECTION port boundary."
  (message "Signal %s is an %s port of module %s; no parent/top-level boundary to continue."
           sym
           direction
           (or (veri-kompass--module-name-at-point-safe) "<unknown>")))

(defsubst veri-kompass-forward-balanced ()
  "After an opening parenthesys find the matching closing one."
  (save-match-data
    (let ((x 1))
      (while (and (> x 0)
                  (re-search-forward "\\((\\|)\\)" nil t))
        (if (equal (match-string 0) "(")
            (setq x (1+ x))
          (setq x (1- x)))))))

(defun veri-kompass--search-submodule-port-drivers (sym)
  "Return submodule output/inout port connection candidates for SYM."
  (let ((drivers nil))
    (dolist (instance (veri-kompass--submodule-instances-in-current-module))
      (dolist (connection (veri-kompass--simple-port-connections sym instance))
        (let ((direction
               (veri-kompass--port-direction-in-module
                (plist-get instance :mod)
                (plist-get connection :port))))
          (when (memq direction '(output inout))
            (setq drivers
                  (append drivers
                          (veri-kompass--child-driver-candidates
                           instance connection direction)))))))
    (nreverse drivers)))

(defun veri-kompass--parent-port-signal-at-point (port-name)
  "Return (SIGNAL . POSITION) for parent connection PORT-NAME near point."
  (when (re-search-forward
         (concat "\\."
                 (regexp-quote port-name)
                 "[[:space:]\n]*([[:space:]\n]*\\("
                 veri-kompass-ident-regex
                 "\\)")
         nil t)
    (cons (match-string-no-properties 1)
          (match-beginning 1))))

(defun veri-kompass--skip-parameter-override ()
  "Skip a parameter override at point, returning non-nil if one was skipped."
  (when (looking-at veri-kompass-parameter-start-regexp)
    (goto-char (match-end 0))
    (veri-kompass-forward-balanced)
    t))

(defun veri-kompass--submodule-instances-in-current-module ()
  "Return submodule instance records found in the current restriction."
  (let ((instances nil))
    (goto-char (point-min))
    (while (re-search-forward
            (concat "\\<\\(" veri-kompass-ident-regex "\\)\\>")
            nil t)
      (let ((mod-name (match-string-no-properties 1)))
        (unless (or (char-equal (aref mod-name 0) ?\`)
                    (veri-kompass--ignored-inst-token-p mod-name))
          (save-excursion
            (skip-chars-forward " \t\n")
            (veri-kompass--skip-parameter-override)
            (skip-chars-forward " \t\n")
            (when (looking-at
                   (concat "\\(" veri-kompass-ident-regex "\\)[[:space:]\n]*("))
              (let ((inst-name (match-string-no-properties 1))
                    (args-start (match-end 0)))
                (unless (veri-kompass--ignored-inst-token-p inst-name)
                  (goto-char args-start)
                  (veri-kompass-forward-balanced)
                  (when (looking-at "[[:space:]\n]*;")
                    (push (list :mod mod-name
                                :inst inst-name
                                :start args-start
                                :end (1- (point)))
                          instances)))))))))
    (nreverse instances)))

(defun veri-kompass--simple-port-connections (sym instance)
  "Return simple named port connections to SYM inside INSTANCE."
  (let ((connections nil)
        (regexp (concat "\\.\\(" veri-kompass-ident-regex "\\)"
                        "[[:space:]\n]*([[:space:]\n]*\\("
                        (regexp-quote sym)
                        "\\)\\(?:[[:space:]]*\\[[^]]+\\]\\)?"
                        "[[:space:]\n]*)")))
    (save-excursion
      (goto-char (plist-get instance :start))
      (while (re-search-forward regexp (plist-get instance :end) t)
        (push (list :port (match-string-no-properties 1)
                    :signal (match-string-no-properties 2)
                    :pos (match-beginning 2))
              connections)))
    (nreverse connections)))

(defun veri-kompass--module-restriction (mod-name)
  "Return (BUFFER START END) for MOD-NAME, or nil if the module is unknown."
  (let ((coords (veri-kompass-mod-to-file-name-pos mod-name)))
    (when coords
      (let ((buffer (find-file-noselect (car coords))))
        (with-current-buffer buffer
          (save-excursion
            (save-restriction
              (widen)
              (goto-char (cadr coords))
              (let ((start (point)))
                (when (re-search-forward veri-kompass-module-end-regexp nil t)
                  (list buffer start (point)))))))))))

(defun veri-kompass--port-direction-in-module (mod-name port-name)
  "Return the direction symbol for PORT-NAME in MOD-NAME."
  (let ((restriction (veri-kompass--module-restriction mod-name))
        (direction nil))
    (when restriction
      (with-current-buffer (nth 0 restriction)
        (save-excursion
          (save-restriction
            (narrow-to-region (nth 1 restriction) (nth 2 restriction))
            (cond
             ((veri-kompass--port-declarations 'input port-name)
              (setq direction 'input))
             ((veri-kompass--port-declarations 'inout port-name)
              (setq direction 'inout))
             ((veri-kompass--port-declarations 'output port-name)
              (setq direction 'output)))))))
    direction))

(defun veri-kompass--candidate-at-point (direction label reason)
  "Return a trace candidate at point with DIRECTION, LABEL, and REASON."
  (make-veri-kompass-trace-candidate
   :direction direction
   :label label
   :marker (copy-marker (point))
   :file (buffer-file-name)
   :line (line-number-at-pos (point) t)
   :snippet (veri-kompass--line-snippet)
   :reason reason))

(defun veri-kompass--child-driver-candidates (instance connection direction)
  "Return child module driver candidates through INSTANCE CONNECTION."
  (let* ((mod-name (plist-get instance :mod))
         (inst-name (plist-get instance :inst))
         (port-name (plist-get connection :port))
         (restriction (veri-kompass--module-restriction mod-name))
         (label (format "%s.%s" inst-name port-name))
         (reason (format "%s child output driver" (symbol-name direction)))
         (candidates nil))
    (when restriction
      (with-current-buffer (nth 0 restriction)
        (save-excursion
          (save-restriction
            (narrow-to-region (nth 1 restriction) (nth 2 restriction))
            (let ((drivers (veri-kompass-search-driver port-name 'internal)))
              (dolist (driver drivers)
                (goto-char (if (veri-kompass-trace-candidate-p driver)
                               (veri-kompass-trace-candidate-marker driver)
                             (cdr driver)))
                (push (veri-kompass--candidate-at-point 'driver label reason)
                      candidates)))
            (unless candidates
              (let ((ports (or (veri-kompass--port-declarations direction port-name)
                               (veri-kompass--port-declarations 'output port-name)
                               (veri-kompass--port-declarations 'inout port-name))))
                (when ports
                  (goto-char (cdar ports))
                  (push (veri-kompass--candidate-at-point 'driver label reason)
                        candidates))))))))
    (nreverse candidates)))

(defun veri-kompass--child-load-candidates (sym instance connection)
  "Return child module load candidates for SYM through INSTANCE CONNECTION."
  (let* ((mod-name (plist-get instance :mod))
         (inst-name (plist-get instance :inst))
         (port-name (plist-get connection :port))
         (direction (veri-kompass--port-direction-in-module mod-name port-name))
         (restriction (veri-kompass--module-restriction mod-name))
         (label (format "%s.%s" inst-name port-name))
         (renamed (not (equal sym port-name)))
         (reason (format "%s child %s%s"
                         (symbol-name direction)
                         label
                         (if renamed " (renamed boundary)" "")))
         (candidates nil))
    (when (and restriction (memq direction '(input inout)))
      (with-current-buffer (nth 0 restriction)
        (save-excursion
          (save-restriction
            (narrow-to-region (nth 1 restriction) (nth 2 restriction))
            (dolist (load (veri-kompass--search-local-loads port-name))
              (goto-char (cdr load))
              (push (veri-kompass--candidate-at-point 'load label reason)
                    candidates))
            (unless candidates
              (let ((ports (veri-kompass--port-declarations direction port-name)))
                (when ports
                  (goto-char (cdar ports))
                  (push (veri-kompass--candidate-at-point 'load label reason)
                        candidates))))))))
    (nreverse candidates)))

(defun veri-kompass--search-submodule-port-loads (sym)
  "Return child module load candidates for simple connections to SYM."
  (let ((loads nil))
    (dolist (instance (veri-kompass--submodule-instances-in-current-module))
      (dolist (connection (veri-kompass--simple-port-connections sym instance))
        (setq loads
              (append loads
                      (veri-kompass--child-load-candidates
                       sym instance connection)))))
    loads))

(defun veri-kompass--submodule-output-connection-positions (sym)
  "Return positions where SYM is connected to child output ports."
  (let ((positions nil))
    (dolist (instance (veri-kompass--submodule-instances-in-current-module))
      (dolist (connection (veri-kompass--simple-port-connections sym instance))
        (when (eq (veri-kompass--port-direction-in-module
                   (plist-get instance :mod)
                   (plist-get connection :port))
                  'output)
          (push (plist-get connection :pos) positions))))
    positions))

(defun veri-kompass--declaration-positions (sym)
  "Return declaration positions for SYM in the current restriction."
  (let ((positions nil))
    (dolist (kind '("input" "output" "inout" "wire" "reg" "logic"))
      (goto-char (point-min))
      (while (re-search-forward
              (concat
               "\\<" kind "\\>"
               "\\(?:[[:space:]]+\\(?:wire\\|reg\\|logic\\|signed\\|unsigned\\)\\)*"
               "\\(?:[[:space:]]+\\[[^]]+\\]\\)?"
               "[[:space:]]+\\("
               (regexp-quote sym)
               "\\)")
              nil t)
        (push (match-beginning 1) positions)))
    positions))

(defun veri-kompass--search-local-loads (sym)
  "Return loads for SYM in the current restriction only."
  (let* ((loads nil)
         (origin-buffer (current-buffer))
         (drivers (mapcar
                   (lambda (driver)
                     (veri-kompass--candidate-position driver origin-buffer))
                   (veri-kompass-search-driver sym 'internal)))
         (output-connections
          (veri-kompass--submodule-output-connection-positions sym))
         (declarations (veri-kompass--declaration-positions sym)))
    (goto-char (point-max))
    (while (re-search-backward (concat "^.*\\(\\<" sym "\\>\\).*") nil t)
      (let ((pos (match-beginning 1)))
        (unless (or (member pos drivers)
                    (member pos output-connections)
                    (member pos declarations))
          (push (cons (match-string 0) pos)
                loads))))
    loads))

(defun veri-kompass-search-driver (sym &optional internal)
  "Given the symbol SYM search for it's driver.
INTERNAL if the search is limited to the current module."
  (save-excursion
    (let ((direct (veri-kompass--search-direct-drivers sym)))
      (if direct
          direct
        (let ((inputs (veri-kompass--search-input-drivers sym)))
          (cond
           ((and inputs (not internal))
            'go-up)
           (inputs
            inputs)
           (t
            (veri-kompass--search-submodule-port-drivers sym))))))))

(defun veri-kompass--go-up-same-name-from-point (signal-name)
  "Move from current input SIGNAL-NAME to the same-name parent connection.
Return `same', `renamed', `no-parent', or nil."
  (if veri-kompass-curr-select
      (let* ((curr-mark (veri-kompass-curr-mark))
             (mark-mod (car curr-mark))
             (mark-inst (cdr curr-mark))
             (module-name (veri-kompass-module-name-at-point)))
        (if (not (equal module-name mark-mod))
            (progn
              (message "Marked module is different from current one.")
              nil)
          (veri-kompass-trace-history--record-jump)
          (set-buffer (veri-kompass-go-up 'jump))
          (search-forward mark-inst nil t)
          (let ((connection (veri-kompass--parent-port-signal-at-point signal-name)))
            (when connection
              (let ((parent-signal (car connection))
                    (parent-pos (cdr connection)))
               (goto-char parent-pos)
               (if (equal parent-signal signal-name)
                   'same
                (message "Signal %s is renamed to %s at parent boundary."
                         signal-name parent-signal)
                'renamed))))))
    'no-parent))

(defun veri-kompass--search-driver-at-point-rec (sym depth)
  "Search driver for SYM at point, climbing same-name inputs up to DEPTH."
  (veri-kompass-within-current-module
   (let ((res (veri-kompass-search-driver sym)))
     (cond
      ((eq res 'go-up)
       (pcase (and (> depth 0)
                   (veri-kompass--go-up-same-name-from-point sym))
         ('same
          (veri-kompass--search-driver-at-point-rec sym (1- depth)))
         ('renamed
           nil)
         ('no-parent
          (veri-kompass--message-port-boundary sym "input"))
         (_
          (veri-kompass--message-port-boundary sym "input"))))
      ((null res)
       (message "Cannot find driver for %s" sym))
      ((equal (length res) 1)
       (veri-kompass-trace-history--record-jump)
       (veri-kompass--goto-candidate (car res) (current-buffer)))
      (t
       (veri-kompass--show-trace-selection res "Select driver line"))))))

(defun veri-kompass-search-driver-at-point ()
  "Goto the driver for symbol at point."
  (interactive)
  (veri-kompass--search-driver-at-point-rec
   (car (veri-kompass-sym-at-point)) 32))

(defun veri-kompass-module-name-at-point ()
  "Return the module containing the current point."
  (save-excursion
    (forward-word 2)
    (re-search-backward veri-kompass-module-start-regexp)
    (match-string-no-properties 1)))

(defun veri-kompass--go-up-output-loads-from-point (signal-name)
  "Return parent loads for output SIGNAL-NAME at point.
Return `no-parent' if the current hierarchy mark cannot move upward."
  (if veri-kompass-curr-select
      (let* ((curr-mark (veri-kompass-curr-mark))
             (mark-mod (car curr-mark))
             (mark-inst (cdr curr-mark))
             (module-name (veri-kompass-module-name-at-point)))
        (if (not (equal module-name mark-mod))
            (progn
              (message "Marked module is different from current one.")
              nil)
          (set-buffer (veri-kompass-go-up 'jump))
          (search-forward mark-inst nil t)
          (let ((connection
                 (veri-kompass--parent-port-signal-at-point signal-name)))
            (if (not connection)
                nil
              (let ((parent-signal (car connection))
                    (parent-pos (cdr connection)))
                (goto-char parent-pos)
                (veri-kompass-within-current-module
                 (mapcar
                  (lambda (load)
                    (goto-char (cdr load))
                    (veri-kompass--candidate-at-point
                     'load
                     parent-signal
                     (format "parent output %s%s"
                             signal-name
                             (if (equal signal-name parent-signal)
                                 ""
                               (format " -> %s" parent-signal)))))
                  (veri-kompass-search-load parent-signal))))))))
    'no-parent))

(defun veri-kompass-search-load (sym)
  "Given the simbol SYM search for all its loads."
  (save-excursion
    (append (veri-kompass--search-local-loads sym)
            (veri-kompass--search-submodule-port-loads sym))))

(defvar-local veri-kompass-load-select--origin-window nil
  "Window that displayed the source buffer when load selection started.")

(defvar-local veri-kompass-load-select--origin-marker nil
  "Marker for the source position before trace selection started.")

(defun veri-kompass--line-snippet ()
  "Return the current line trimmed for candidate display."
  (string-trim
   (buffer-substring-no-properties
    (line-beginning-position) (line-end-position))))

(defun veri-kompass--candidate-marker (candidate origin-buffer)
  "Return a marker for CANDIDATE, using ORIGIN-BUFFER for legacy candidates."
  (cond
   ((veri-kompass-trace-candidate-p candidate)
    (veri-kompass-trace-candidate-marker candidate))
   ((markerp (cdr candidate))
    (cdr candidate))
   (t
    (with-current-buffer origin-buffer
      (copy-marker (cdr candidate))))))

(defun veri-kompass--candidate-position (candidate origin-buffer)
  "Return buffer position for CANDIDATE in ORIGIN-BUFFER."
  (let ((marker (veri-kompass--candidate-marker candidate origin-buffer)))
    (when (markerp marker)
      (marker-position marker))))

(defun veri-kompass--candidate-display (candidate)
  "Return display text for CANDIDATE."
  (if (veri-kompass-trace-candidate-p candidate)
      (let ((prefix (upcase (symbol-name
                             (veri-kompass-trace-candidate-direction candidate))))
            (line (veri-kompass-trace-candidate-line candidate))
            (snippet (veri-kompass-trace-candidate-snippet candidate))
            (reason (veri-kompass-trace-candidate-reason candidate)))
        (string-join
         (remove nil
                 (list prefix
                       (veri-kompass-trace-candidate-label candidate)
                       (when line (format "line %s" line))
                       reason
                       snippet))
          " | "))
    (car candidate)))

(defun veri-kompass-clear-trace-highlight ()
  "Clear the current trace target highlight."
  (interactive)
  (when (overlayp veri-kompass-trace-highlight-overlay)
    (delete-overlay veri-kompass-trace-highlight-overlay))
  (setq veri-kompass-trace-highlight-overlay nil))

(defun veri-kompass--trace-token-bounds-at-point ()
  "Return bounds of the Verilog identifier around point."
  (let ((pos (point))
        (chars "a-zA-Z0-9_$"))
    (save-excursion
      (skip-chars-backward chars)
      (when (looking-at veri-kompass-ident-regex)
        (let ((start (match-beginning 0))
              (end (match-end 0)))
          (when (and (<= start pos)
                     (<= pos end))
            (cons start end)))))))

(defun veri-kompass-highlight-trace-target (&optional marker)
  "Highlight the trace target signal at MARKER or point."
  (let ((target (or marker (copy-marker (point)))))
    (when (and (markerp target)
               (buffer-live-p (marker-buffer target)))
      (veri-kompass-clear-trace-highlight)
      (with-current-buffer (marker-buffer target)
        (save-excursion
          (goto-char target)
          (let ((bounds (veri-kompass--trace-token-bounds-at-point)))
            (when bounds
              (setq veri-kompass-trace-highlight-overlay
                    (make-overlay (car bounds) (cdr bounds) (current-buffer)
                                  nil t))
              (overlay-put veri-kompass-trace-highlight-overlay
                           'face 'veri-kompass-trace-highlight-face)
              (overlay-put veri-kompass-trace-highlight-overlay
                           'priority 1000)
              veri-kompass-trace-highlight-overlay)))))))

(defun veri-kompass-trace-history--make-marker ()
  "Return a marker for the current buffer and point."
  (copy-marker (point)))

(defun veri-kompass-trace-history--live-entry-p (entry)
  "Return non-nil when trace history ENTRY is still valid."
  (and (markerp entry)
       (buffer-live-p (marker-buffer entry))))

(defun veri-kompass-trace-history--trim (stack)
  "Return STACK trimmed to `veri-kompass-trace-history-limit'."
  (let ((limit (max 0 veri-kompass-trace-history-limit)))
    (if (<= (length stack) limit)
        stack
      (cl-subseq stack 0 limit))))

(defun veri-kompass-trace-history--push-back (entry)
  "Push ENTRY onto the trace back history."
  (when (and (> veri-kompass-trace-history-limit 0)
             (veri-kompass-trace-history--live-entry-p entry))
    (setq veri-kompass-trace-back-stack
          (veri-kompass-trace-history--trim
           (cons entry veri-kompass-trace-back-stack)))))

(defun veri-kompass-trace-history--push-forward (entry)
  "Push ENTRY onto the trace forward history."
  (when (and (> veri-kompass-trace-history-limit 0)
             (veri-kompass-trace-history--live-entry-p entry))
    (setq veri-kompass-trace-forward-stack
          (veri-kompass-trace-history--trim
           (cons entry veri-kompass-trace-forward-stack)))))

(defun veri-kompass-trace-history--record-jump ()
  "Record the current position before a real trace jump."
  (unless veri-kompass-trace-history--in-navigation
    (veri-kompass-trace-history--push-back
     (veri-kompass-trace-history--make-marker))
    (setq veri-kompass-trace-forward-stack nil)))

(defun veri-kompass-trace-history--record-entry (entry)
  "Record trace history ENTRY before a real trace jump."
  (unless veri-kompass-trace-history--in-navigation
    (veri-kompass-trace-history--push-back entry)
    (setq veri-kompass-trace-forward-stack nil)))

(defun veri-kompass-trace-history--pop-live (stack)
  "Return (ENTRY . REST) for the first live item in STACK."
  (while (and stack
              (not (veri-kompass-trace-history--live-entry-p (car stack))))
    (setq stack (cdr stack)))
  (when stack
    (cons (car stack) (cdr stack))))

(defun veri-kompass-trace-history--goto-entry (entry)
  "Move to trace history ENTRY."
  (when (veri-kompass-trace-history--live-entry-p entry)
    (let ((buffer (marker-buffer entry)))
      (switch-to-buffer buffer)
      (goto-char entry)
      (veri-kompass-highlight-trace-target entry)
      t)))

(defun veri-kompass-trace-back ()
  "Move backward in trace jump history."
  (interactive)
  (let ((item (veri-kompass-trace-history--pop-live
               veri-kompass-trace-back-stack)))
    (if (not item)
        (progn
          (setq veri-kompass-trace-back-stack nil)
          (message "Trace history is empty."))
      (setq veri-kompass-trace-back-stack (cdr item))
      (let ((current (veri-kompass-trace-history--make-marker))
            (target (car item))
            (veri-kompass-trace-history--in-navigation t))
        (veri-kompass-trace-history--push-forward current)
        (veri-kompass-trace-history--goto-entry target)))))

(defun veri-kompass-trace-forward ()
  "Move forward in trace jump history."
  (interactive)
  (let ((item (veri-kompass-trace-history--pop-live
               veri-kompass-trace-forward-stack)))
    (if (not item)
        (progn
          (setq veri-kompass-trace-forward-stack nil)
          (message "Trace forward history is empty."))
      (setq veri-kompass-trace-forward-stack (cdr item))
      (let ((current (veri-kompass-trace-history--make-marker))
            (target (car item))
            (veri-kompass-trace-history--in-navigation t))
        (veri-kompass-trace-history--push-back current)
        (veri-kompass-trace-history--goto-entry target)))))

(defun veri-kompass--goto-candidate (candidate origin-buffer)
  "Go to CANDIDATE in ORIGIN-BUFFER."
  (let ((marker (veri-kompass--candidate-marker candidate origin-buffer)))
    (when (and (markerp marker)
               (buffer-live-p (marker-buffer marker)))
      (switch-to-buffer (marker-buffer marker))
      (goto-char marker)
      (veri-kompass-highlight-trace-target marker)
      t)))

(defun veri-kompass-load-select--current-marker ()
  "Return the marker stored on the current line, if any."
  (get-text-property (line-beginning-position)
                     'veri-kompass-load-marker))

(defun veri-kompass-load-select--first-candidate-pos ()
  "Return buffer position of the first selectable load line."
  (save-excursion
    (goto-char (point-min))
    (while (and (not (eobp))
                (not (veri-kompass-load-select--current-marker)))
      (forward-line 1))
    (when (veri-kompass-load-select--current-marker)
      (line-beginning-position))))

(defun veri-kompass-load-select--find-next (direction)
  "Find the next selectable line following DIRECTION.
DIRECTION should be positive to move down or negative to move up."
  (let ((step (if (> direction 0) 1 -1))
        (target nil)
        (continue t))
    (save-excursion
      (while (and continue (= (forward-line step) 0))
        (when (veri-kompass-load-select--current-marker)
          (setq target (line-beginning-position))
          (setq continue nil)))
      target)))

(defun veri-kompass-load-select--preview-marker (marker)
  "Preview MARKER in the original verilog window."
  (when (and (markerp marker)
             (buffer-live-p (marker-buffer marker)))
    (let* ((buffer (marker-buffer marker))
           (window veri-kompass-load-select--origin-window)
           (target-window (cond
                           ((and (window-live-p window)
                                 (eq (window-buffer window) buffer))
                            window)
                           ((window-live-p window)
                            (with-selected-window window
                              (switch-to-buffer buffer))
                            window)
                           (t
                            (display-buffer buffer)))))
      (when (window-live-p target-window)
        (setq veri-kompass-load-select--origin-window target-window)
        (with-selected-window target-window
          (goto-char marker)
          (veri-kompass-highlight-trace-target marker)
          (recenter))
        target-window))))

(defun veri-kompass-load-select--preview-at-point ()
  "Preview the load that corresponds to the current line."
  (veri-kompass-load-select--preview-marker
   (veri-kompass-load-select--current-marker)))

(defun veri-kompass-load-select--move (direction)
  "Move selection following DIRECTION and preview the result."
  (let ((target (veri-kompass-load-select--find-next direction)))
    (if target
        (progn
          (goto-char target)
          (veri-kompass-load-select--preview-at-point))
      (message (if (> direction 0)
                   "Already at last load."
                 "Already at first load.")))))

(defun veri-kompass-load-select-next ()
  "Move to the next load entry and preview it."
  (interactive)
  (veri-kompass-load-select--move 1))

(defun veri-kompass-load-select-previous ()
  "Move to the previous load entry and preview it."
  (interactive)
  (veri-kompass-load-select--move -1))

(defun veri-kompass-load-select-commit ()
  "Jump to the load under point and close the selection buffer."
  (interactive)
  (let ((marker (veri-kompass-load-select--current-marker))
        (window nil))
    (if (not (and (markerp marker)
                  (buffer-live-p (marker-buffer marker))))
        (message "No load at current line.")
      (veri-kompass-trace-history--record-entry
       veri-kompass-load-select--origin-marker)
      (setq window (veri-kompass-load-select--preview-marker marker))
      (quit-window t)
      (when (window-live-p window)
        (select-window window)))))

(defun veri-kompass-load-select-quit ()
  "Quit the load selection window."
  (interactive)
  (let ((window veri-kompass-load-select--origin-window))
    (quit-window t)
    (when (window-live-p window)
      (select-window window))))

(defvar veri-kompass-load-select-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-j") #'veri-kompass-load-select-next)
    (define-key map (kbd "C-k") #'veri-kompass-load-select-previous)
    (define-key map (kbd "RET") #'veri-kompass-load-select-commit)
    (define-key map (kbd "q") #'veri-kompass-load-select-quit)
    map)
  "Keymap for `veri-kompass-load-select-mode'.")

(define-derived-mode veri-kompass-load-select-mode special-mode "Veri-Load"
  "Mode for displaying load lines so they can be navigated."
  (setq truncate-lines t)
  (hl-line-mode 1))

(defun veri-kompass--show-trace-selection (candidates title)
  "Show trace CANDIDATES in the selection buffer using TITLE."
  (let* ((origin-window (selected-window))
         (buffer (get-buffer-create veri-kompass-load-select-buffer-name))
         (origin-buffer (window-buffer origin-window)))
    (with-current-buffer buffer
      (veri-kompass-load-select-mode)
      (setq veri-kompass-load-select--origin-window origin-window)
      (setq veri-kompass-load-select--origin-marker
            (with-current-buffer origin-buffer
              (copy-marker (point))))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert title " (C-j/C-k to preview, RET to jump, q to quit).\n\n")
        (dolist (cand candidates)
          (let* ((line-start (point))
                 (marker (veri-kompass--candidate-marker cand origin-buffer)))
            (insert (veri-kompass--candidate-display cand) "\n")
            (put-text-property line-start (1- (point))
                               'veri-kompass-load-marker marker))))
      (let ((first (veri-kompass-load-select--first-candidate-pos)))
        (when first
          (goto-char first))))
    (pop-to-buffer buffer '(display-buffer-pop-up-window))
    (with-current-buffer buffer
      (veri-kompass-load-select--preview-at-point))))

(defun veri-kompass--show-load-selection (candidates)
  "Show load CANDIDATES in the selection buffer."
  (veri-kompass--show-trace-selection candidates "Select load line"))

(defun veri-kompass-search-load-at-point ()
  "Goto the loads for symbol at point."
  (interactive)
  (let ((origin-buffer (current-buffer))
        (origin-marker (copy-marker (point)))
        (res nil)
        (output-port nil)
        (parent-search nil)
        (sym nil))
    (veri-kompass-within-current-module
     (setq sym (car (veri-kompass-sym-at-point)))
     (setq output-port
           (veri-kompass--point-on-port-declaration-p 'output sym))
     (setq res
           (if output-port
               (progn
                 (setq parent-search t)
                 (veri-kompass--go-up-output-loads-from-point sym))
             (veri-kompass-search-load sym))))
    (when parent-search
      (switch-to-buffer origin-buffer)
      (goto-char origin-marker))
    (cond
     ((and res (not (eq res 'no-parent)))
      (if (equal (length res) 1)
          (progn
            (if parent-search
                (veri-kompass-trace-history--record-entry origin-marker)
              (veri-kompass-trace-history--record-jump))
            (veri-kompass--goto-candidate (car res) origin-buffer))
        (veri-kompass--show-load-selection res)))
     (output-port
      (veri-kompass--message-port-boundary sym "output"))
     (t
      (message "Cannot find load for %s" sym)))))

(defun veri-kompass-follow-from-point ()
  "Follow symbol at point.
If is an l-val search for loads, if r-val search for drivers."
  (interactive)
  (let ((sym (veri-kompass-sym-at-point)))
    (pcase (cdr sym)
      ('l-val (veri-kompass-search-load-at-point))
      ('r-val (veri-kompass-search-driver-at-point)))))


(defun veri-kompass-directory-files-recursively-with-symlink (dir regexp &optional include-directories)
  "This function is a variant of ‘directory-files-recursively’ from files.el.
Return list of all files under DIR that have file names matching REGEXP.
This function works recursively following symlinks.
Files are returned in \"depth first\" order, and files from each directory are
 sorted in alphabetical order.
Each file name appears in the returned list in its absolute form.
Optional argument INCLUDE-DIRECTORIES non-nil means also include in the
output directories whose names match REGEXP."
  (let ((result nil)
        (files nil)
        ;; When DIR is "/", remote file names like "/method:" could
        ;; also be offered.  We shall suppress them.
        (tramp-mode (and tramp-mode (file-remote-p (expand-file-name dir)))))
    (dolist (file (sort (file-name-all-completions "" dir)
                        'string<))
      (unless (member file '("./" "../"))
        (if (directory-name-p file)
            (let* ((leaf (substring file 0 (1- (length file))))
                   (full-file (expand-file-name leaf dir)))
              (setq result
                    (nconc result (directory-files-recursively
                                   full-file regexp include-directories)))
              (when (and include-directories
                         (string-match regexp leaf))
                (setq result (nconc result (list full-file)))))
          (when (string-match regexp file)
            (push (expand-file-name file dir) files)))))
    (nconc result (nreverse files))))

(defun veri-kompass--valid-source-file-p (file)
  "Return non-nil when FILE should be considered part of the project."
  (and (string-match-p veri-kompass-extention-regexp file)
       (not (string-match-p "/\\." file))
       (not (string-match-p veri-kompass-skip-regexp file))))

(defun veri-kompass-list-file-in-proj (dir)
  "Return a list of all project files present in DIR ver.excluding the one specified by ‘veri-kompass-skip-regexp’."
  (remove nil
          (mapcar (lambda (x)
                    (if (veri-kompass--valid-source-file-p x) x))
                  (veri-kompass-directory-files-recursively-with-symlink
                   dir veri-kompass-extention-regexp))))

(defun veri-kompass--filelist-option-p (line)
  "Return non-nil when LINE is a Verilog filelist option."
  (or (string-prefix-p "+" line)
      (string-prefix-p "-" line)))

(defun veri-kompass--expand-filelist-token (token)
  "Expand environment variables in filelist TOKEN."
  (substitute-in-file-name token))

(defun veri-kompass--filelist-candidate-paths (token base roots)
  "Return candidate paths for filelist TOKEN relative to BASE and ROOTS."
  (let ((expanded (veri-kompass--expand-filelist-token token)))
    (if (file-name-absolute-p expanded)
        (list expanded)
      (delete-dups
       (cons (expand-file-name expanded base)
             (mapcar (lambda (root)
                       (expand-file-name expanded root))
                     roots))))))

(defun veri-kompass--filelist-roots (base)
  "Return plausible project roots for a filelist in BASE."
  (let* ((base-dir (directory-file-name base))
         (parent (file-name-directory base-dir)))
    (delete-dups
     (delq nil
           (list default-directory
                 parent)))))

(defun veri-kompass--files-from-filelist (filelist)
  "Return a list of source files defined in FILELIST."
  (let ((base (file-name-directory (expand-file-name filelist)))
        (roots nil)
        (result nil))
    (setq roots (veri-kompass--filelist-roots base))
    (with-temp-buffer
      (insert-file-contents filelist)
      (while (not (eobp))
        (let* ((line (buffer-substring-no-properties
                      (line-beginning-position) (line-end-position)))
               (clean (string-trim line)))
          (unless (or (string-empty-p clean)
                      (string-prefix-p "#" clean)
                      (string-prefix-p "//" clean)
                      (veri-kompass--filelist-option-p clean))
            (catch 'found
              (dolist (candidate (veri-kompass--filelist-candidate-paths clean base roots))
                (when (and (file-exists-p candidate)
                           (veri-kompass--valid-source-file-p candidate))
                  (push candidate result)
                  (throw 'found candidate))))))
        (forward-line 1)))
    (delete-dups (nreverse result))))

(defun veri-kompass--project-files-from (source)
  "Return all source files described by SOURCE.
SOURCE can be a directory or a file list."
  (let ((expanded (expand-file-name source)))
    (cond
     ((file-directory-p expanded)
      (veri-kompass-list-file-in-proj expanded))
     ((file-regular-p expanded)
      (veri-kompass--files-from-filelist expanded))
     (t
      (error "Path %s is neither a directory nor a readable file" source)))))

(defun veri-kompass-list-modules-in-file (file)
  "Return the list of all declared modules present in FILE."
  (with-temp-buffer
    (insert-file-contents-literally file)
    (let ((mod-list))
      (while (re-search-forward
              (concat veri-kompass-module-start-regexp
                      "[[:space:]]*\n*[[:space:]]*\\((\\|#[[:space:]\n]*(\\|`\\|;\\)")
              nil t)
        (push (list
               (match-string-no-properties 1)
               file
               (point)
               (line-number-at-pos (point))
               (match-string-no-properties 0))
              mod-list))
      mod-list)))

(defun veri-kompass-list-modules-in-proj (files)
  "Return the list of all declared modules present in FILES."
  (remove nil
          (cl-mapcan 'veri-kompass-list-modules-in-file files)))

(defun veri-kompass-mod-to-file-name-pos (name)
  "Given the module name NAME return its position." ;; improve
  (cdr (assoc name veri-kompass-module-list)))

(defun veri-kompass--add-hier-warning (fmt &rest args)
  "Record a hierarchy warning formatted with FMT and ARGS."
  (push (apply #'format fmt args) veri-kompass-hier-warnings))

(defun veri-kompass--ignored-inst-token-p (token)
  "Return non-nil when TOKEN should not be treated as a module or instance."
  (member (downcase token) veri-kompass-ignore-keywords))

(defun veri-kompass-mark-comments ()
  "Scanning a buffer mark all comments with property 'comment."
  (interactive)
  (save-mark-and-excursion
    (goto-char (point-min))
    (while (re-search-forward "//.*" nil t) ;; TODO add other comment style
      (put-text-property (match-beginning 0) (point) 'comment t))))

(defsubst veri-kompass-mark-code-blocks ()
  "Mark all text within code blocks with property 'code."
  (interactive)
  (save-mark-and-excursion
    (veri-kompass-mark-comments)
    (goto-char (point-min))
    (while (search-forward "begin" nil t)
      (unless (get-char-property 0 'comment (match-string 0))
        (backward-word)
        (set-mark (point))
        (forward-word)
        (let ((nest 1))
          (while (> nest 0)
            (re-search-forward "\\(begin\\|end$\\|end \\)" nil t)
            (setq nest (if (and (equal (match-string 1) "begin")
                                (not (get-char-property
                                      0
                                      'comment
                                      (match-string 0))))
                           (1+ nest)
                         (1- nest)))))
        (put-text-property (mark) (point) 'code t)))))

(defsubst veri-kompass-delete-parameters ()
  "Remove all #( ... )."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward veri-kompass-parameter-start-regexp nil t)
      (veri-kompass-forward-balanced)
      (delete-region (match-beginning 0) (point)))))

(defsubst veri-kompass-remove-macros ()
  "Remove all `SOMETHIING ."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "`[a-z_0-9]+" nil t)
      (unless (equal (match-string 0) "`define")
        (delete-region (match-beginning 0) (match-end 0))))))

(defun veri-kompass-retrive-original-line (inst-name mod-name content)
  "Given instance name INST-NAME module name MOD-NAME and the original buffer instantiation content CONTENT return the module instantiation line."
  (save-match-data
    (with-temp-buffer
      (insert content)
      (goto-char (point-min))
      (or (re-search-forward
           (format
            "\\<%s\\>[ a-z-0-9_.#(),\n]*\\<%s\\>"
            inst-name
            mod-name) nil t)
          (search-forward inst-name))
      (line-number-at-pos (match-beginning 0)))))

(defun veri-kompass-build-hier-rec (mod-name)
  "Given MOD-NAME return a list rappresenting the design hierarchy.
This recursive function call itself walking all the verilog design."
  (veri-kompass-thread-yield)
  (let ((cached (gethash mod-name veri-kompass-mod-str-hash :missing)))
    (cond
     ((eq cached :building)
      (veri-kompass--add-hier-warning
       "Detected recursive hierarchy while parsing module %s" mod-name)
      nil)
     ((not (eq cached :missing))
      cached)
     (t
      (puthash mod-name :building veri-kompass-mod-str-hash)
      (let ((hier
             (let ((target (veri-kompass-mod-to-file-name-pos mod-name))
                   (struct)
                   (orig-buff))
               (if target
                   (with-temp-buffer
                     (insert-file-contents-literally (car target))
                     (setq orig-buff (buffer-string))
                     (goto-char (cadr target))
                     (set-mark (point))
                     (re-search-forward veri-kompass-module-end-regexp nil t)
                     (narrow-to-region (mark) (point))
                     (veri-kompass-thread-yield)
                     (veri-kompass-delete-parameters)
                     (veri-kompass-thread-yield)
                     (veri-kompass-remove-macros)
                     (veri-kompass-thread-yield)
                     (veri-kompass-mark-code-blocks)
                     (veri-kompass-thread-yield)
                     (goto-char (point-min))
                     (while (re-search-forward
                             (concat "\\(" veri-kompass-ident-regex "\\)"
                                     "[[:space:]]+"
                                     "\\(" veri-kompass-ident-regex "\\)"
                                     "[[:space:]]*(")
                             nil t)
                       (when (save-match-data
                               (veri-kompass-thread-yield)
                               (veri-kompass-forward-balanced)
                               (looking-at "[[:space:]]*;"))
                         (unless (or (get-char-property 0 'code (match-string 0))
                                     (get-char-property 0 'comment (match-string 0))
                                     (char-equal (aref (match-string-no-properties 1) 0)
                                                 ?\`)
                                     (veri-kompass--ignored-inst-token-p
                                      (match-string-no-properties 1))
                                     (veri-kompass--ignored-inst-token-p
                                      (match-string-no-properties 2)))
                           (veri-kompass-thread-yield)
                           (let* ((child-mod (match-string-no-properties 1))
                                  (child-inst (match-string-no-properties 2))
                                  (child-line
                                   (veri-kompass-retrive-original-line child-inst
                                                                       child-mod
                                                                       orig-buff)))
                             (push (make-veri-kompass-mod-inst
                                    :mod-name child-mod
                                    :inst-name child-inst
                                    :file-name (car target)
                                    :line child-line)
                                   struct)
                             (unless (veri-kompass-mod-to-file-name-pos child-mod)
                               (veri-kompass--add-hier-warning
                                "Cannot find module %s instantiated as %s at %s:%s"
                                child-mod child-inst (car target) child-line))
                             (let ((sub-hier
                                    (veri-kompass-build-hier-rec child-mod)))
                               (when sub-hier
                                 (push sub-hier struct)))))))
                     (reverse struct))
                 (message "Cannot find module %s" mod-name)
                 nil))))
        (puthash mod-name hier veri-kompass-mod-str-hash)
        hier)))))

(defun veri-kompass-build-hier (top)
  "Given a TOP module return the hierarcky.
This is the entry point function for parsing the design."
  (setq veri-kompass-hier-warnings nil)
  (let ((target (veri-kompass-mod-to-file-name-pos top)))
    (if target
        (list (make-veri-kompass-mod-inst
               :inst-name top
               :mod-name top
               :file-name (car target)
               :line (caddr target))
              (veri-kompass-build-hier-rec top))
      (veri-kompass--add-hier-warning "Cannot find top module %s" top)
      (message "Cannot find top module %s" top))))

(defun veri-kompass-orgify-link (inst)
  "Given a module instance INST return an org link."
  (let ((coords (veri-kompass-mod-to-file-name-pos (veri-kompass-mod-inst-mod-name inst))))
    (if coords
        (format "[[%s::%s][%s]] [[%s::%s][%s]]"
                (veri-kompass-mod-inst-file-name inst)
                (veri-kompass-mod-inst-line inst)
                (veri-kompass-mod-inst-inst-name inst)
                (nth 0 coords)
                (with-temp-buffer
                  (insert (nth 3 coords))
                  (re-search-backward "module.*$" nil t)
                  (match-string 0))
                (veri-kompass-mod-inst-mod-name inst))
      (veri-kompass-mod-inst-inst-name inst))))

(defun veri-kompass-orgify-hier (hier nest)
  "Given an hierarcky HIER and a nesting level NEST produce an org rappresentation of the hierarcky."
  (mapconcat (lambda (h)
               (if (consp h)
                   (veri-kompass-orgify-hier h (1+ nest))
                 (format "%s %s" (let ((x ""))
                                   (dotimes (_ nest)
                                     (setq x (concat x "*")))
                                    x)
                          (veri-kompass-orgify-link h)))) hier "\n"))

(defun veri-kompass-orgify-hier-warnings ()
  "Return org text for hierarchy warnings."
  (when veri-kompass-hier-warnings
    (concat "\n\n* veri-kompass warnings\n"
            (mapconcat (lambda (warning)
                         (concat "- " warning))
                       (nreverse veri-kompass-hier-warnings)
                       "\n"))))

(defun veri-kompass-compute-and-create-bar (top-name)
  "Given a top module TOP-NAME create and populate the hierarky bar."
  (setq veri-kompass-hier (veri-kompass-build-hier top-name))
  (message "Parsing done%s."
           (if veri-kompass-hier-warnings
               (format " with %s warning(s)" (length veri-kompass-hier-warnings))
             ""))
  (switch-to-buffer-other-window veri-kompass-bar-name)
  (let ((inhibit-read-only t))
    (erase-buffer)
    (insert (or (veri-kompass-orgify-hier veri-kompass-hier 1) ""))
    (let ((warnings (veri-kompass-orgify-hier-warnings)))
      (when warnings
        (insert warnings))))
  (read-only-mode)
  (veri-kompass-mode)
  (highlight-regexp "->\\|<-" 'veri-kompass-inst-marked-face)
  (whitespace-turn-off))

(defun veri-kompass-open-at-point (&rest _)
  "Follow link into the hierarchy bar."
  (interactive)
  (org-open-at-point)
  (window-buffer))

(defun veri-kompass-curr-mark ()
  "Return a pair (module-name . instance-name) for the current mark."
  (if veri-kompass-curr-select
      (save-excursion
        (switch-to-buffer-other-window veri-kompass-bar-name)
        (goto-char (point-min))
        ;; enjoy
        (re-search-forward "-> \\[\\[.*\\]\\[\\(.*\\)\\]\\] \\[\\[.*\\]\\[\\(.*\\)\\]\\] <-")
        (cons (match-string-no-properties 2)
              (match-string-no-properties 1)))
    (message "Select an instance first.")
    nil))

(defun veri-kompass-unmark ()
  "Remove mark on current instance selected."
  (interactive)
  (with-current-buffer veri-kompass-bar-name
    (save-excursion
      (when veri-kompass-curr-select
        (let ((inhibit-read-only t))
          (goto-char (point-min))
          (re-search-forward " ->" nil t)
          (replace-match "")
          (re-search-forward " <-" nil t)
          (replace-match "")
          (setq veri-kompass-curr-select nil))))))

(defun veri-kompass-mark ()
  "Mark the instance at point."
  (interactive)
  (with-current-buffer veri-kompass-bar-name
    (veri-kompass-mark-and-jump)
    (switch-to-buffer-other-window veri-kompass-bar-name)))

(defun veri-kompass-mark-and-jump ()
  "Mark the instance at point and jump to its definition."
  (interactive)
  (with-current-buffer veri-kompass-bar-name
    (when veri-kompass-curr-select
      (veri-kompass-unmark))
    (let ((inhibit-read-only t))
      (re-search-backward "^")
      (re-search-forward "\\*+")
      (setq veri-kompass-curr-select (point))
      (unless (equal (car veri-kompass-history) (point)) ;; should count lines
        (push (point) veri-kompass-history))
      (insert " ->")
      (re-search-forward "$")
      (insert " <-")
      (backward-char 4)
      (veri-kompass-open-at-point))))

(defun veri-kompass-go-backward ()
  "Move backward into the instance selection history."
  (interactive)
  (if veri-kompass-history
      (progn
        (setq veri-kompass-history (cdr veri-kompass-history))
        (with-current-buffer veri-kompass-bar-name
          (veri-kompass-unmark)
          (when (car veri-kompass-history)
            (goto-char (car veri-kompass-history))
            (veri-kompass-mark))))
    (message "History is empty")))

(defun veri-kompass-go-up (&optional jump)
  "Move up into the hierarchy.
If JUMP is not nil follow link too."
  (interactive)
  (with-current-buffer veri-kompass-bar-name
    (if veri-kompass-curr-select
        (progn
          (goto-char veri-kompass-curr-select)
          (veri-kompass-unmark)
          (org-up-element)
          (if jump
              (veri-kompass-mark-and-jump)
            (veri-kompass-mark)))
      (message "Select an instance first."))))

(defun veri-kompass-go-up-from-point ()
  "Move up into the hierarchy starting from point into a verilog file."
  (interactive)
  (if veri-kompass-curr-select ;; sanity check missing
      (let* ((signal-name (word-at-point))
             (curr-mark (veri-kompass-curr-mark))
             (mark-mod (car curr-mark))
             (mark-inst (cdr curr-mark))
             (module-name (veri-kompass-module-name-at-point)))
        (if (not (equal module-name mark-mod))
            (print "Marked module is different from current one.")
          (set-buffer (veri-kompass-go-up 'jump))
          (search-forward mark-inst)
          (re-search-forward
           (concat "\\." signal-name "[[:space:]]*\\((\\|\n\\)"))))
    "Please mark current instance into hierarchy buffer."))

(defun veri-kompass-full-mark-position()
  "Return a list with the current instance position in the hierarchy."
  (save-excursion
    (let ((res)
          (p))
      (while
          (progn
            (re-search-backward "^")
            (setq p (point))
            (search-forward "][")
            (re-search-forward "\\(.*\\)]] ")
            (push
             (match-string-no-properties 1) res)
            (unless (equal p (point-min))
              (org-up-element)
              t)))
      res)))

;;;###autoload
(defun veri-kompass (source &optional top-name)
  "Enable Veri-Kompass.
Veri-Kompass is a verilog codebase navigation facility.
The codebase to be parsed will be provided by SOURCE, which can be either
a directory or a Verilog filelist.
The decendent parsing will start from module TOP-NAME."
  (interactive
   (list (read-file-name "Directory or filelist: " nil nil t)))
  (setq veri-kompass-mod-str-hash (make-hash-table :test 'equal))
  (setq veri-kompass-module-list
        (veri-kompass-list-modules-in-proj
         (veri-kompass--project-files-from source)))
  (unless top-name
    (setq top-name
	  (veri-kompass-completing-read "specify top module: "
					(mapcar (lambda (x)
						  (car x))
						veri-kompass-module-list)
					"*veri-kompass-module-top-select*")))
  (message "Parsing design...")
  (veri-kompass-make-thread (lambda ()
                              (veri-kompass-compute-and-create-bar top-name))))

(define-minor-mode veri-kompass-minor-mode
  "Minor mode to be used into verilog files."
  :lighter " VK"
  :keymap (let ((map (make-sparse-keymap)))
            (define-key map (kbd "C-c d") 'veri-kompass-search-driver-at-point)
            (define-key map (kbd "C-c l") 'veri-kompass-search-load-at-point)
            (define-key map (kbd "C-c b") 'veri-kompass-trace-back)
            (define-key map (kbd "C-c f") 'veri-kompass-trace-forward)
            map))

(defvar veri-kompass-mode-map nil "Keymap for `veri-kompass-mode'.")

(progn
  (setq veri-kompass-mode-map (make-sparse-keymap))
  (define-key veri-kompass-mode-map (kbd "o") 'veri-kompass-open-at-point)
  (define-key veri-kompass-mode-map (kbd "m") 'veri-kompass-mark)
  (define-key veri-kompass-mode-map (kbd "RET") 'veri-kompass-mark-and-jump)
  (define-key veri-kompass-mode-map (kbd "u") 'veri-kompass-go-up)
  (define-key veri-kompass-mode-map (kbd "q") 'veri-kompass-unmark)
  (define-key veri-kompass-mode-map (kbd "b") 'veri-kompass-go-backward)
  (define-key veri-kompass-mode-map (kbd "C-S-<right>")
    'enlarge-window-horizontally)
  (define-key veri-kompass-mode-map (kbd "C-S-<left>")
    'shrink-window-horizontally))

(define-derived-mode
  veri-kompass-mode
  org-mode
  "Veri-Kompass"
  "Generate and handle verilog project hierarchy.")

(defmacro veri-kompass-test-with-captured-message (&rest body)
  "Execute BODY and return the last message string."
  `(let ((captured-message nil))
     (cl-letf (((symbol-function 'message)
                (lambda (fmt &rest args)
                  (setq captured-message (apply #'format fmt args)))))
       ,@body
       captured-message)))

(defmacro veri-kompass-test-with-verilog-file (content &rest body)
  "Create a temporary Verilog file containing CONTENT and execute BODY."
  `(let ((tmp-file (make-temp-file "veri-kompass-design" nil ".v"))
         (buffer nil))
     (unwind-protect
         (progn
           (with-temp-file tmp-file
             (insert ,content))
           (setq veri-kompass-module-list
                 (veri-kompass-list-modules-in-file tmp-file))
           (setq buffer (find-file-noselect tmp-file))
           (with-current-buffer buffer
             ,@body))
       (when (buffer-live-p buffer)
         (kill-buffer buffer))
       (when (file-exists-p tmp-file)
         (delete-file tmp-file)))))

(when (featurep 'ert)
  (ert-deftest veri-kompass-test-filelist-parsing ()
    "Ensure filelists are parsed as absolute filtered paths."
    (let ((tmp-dir (make-temp-file "veri-kompass-test" t)))
      (unwind-protect
          (let* ((foo (expand-file-name "foo.sv" tmp-dir))
                 (bar (expand-file-name "sub/bar.v" tmp-dir))
                 (skip (expand-file-name "skipme.v" tmp-dir))
                 (filelist (expand-file-name "dut.f" tmp-dir))
                 (veri-kompass-skip-regexp "skipme"))
            (make-directory (file-name-directory bar) t)
            (dolist (path (list foo bar skip))
              (with-temp-file path
                (insert "// test file\n")))
            (with-temp-file filelist
              (insert "# comment line\n")
              (insert (file-relative-name foo tmp-dir) "\n")
              (insert (file-relative-name bar tmp-dir) "\n")
              (insert "// another comment\n")
              (insert (file-relative-name foo tmp-dir) "\n")
              (insert (file-relative-name skip tmp-dir) "\n")
              (insert "missing.v\n"))
            (should (equal (veri-kompass--files-from-filelist filelist)
                           (list foo bar))))
        (when (file-directory-p tmp-dir)
          (delete-directory tmp-dir t)))))
  (ert-deftest veri-kompass-test-filelist-project-root-relative-paths ()
    "Ensure filelists can contain root-relative paths and option lines."
    (let ((tmp-dir (make-temp-file "veri-kompass-root-test" t)))
      (unwind-protect
          (let* ((default-directory temporary-file-directory)
                 (rtl-dir (expand-file-name "rtl" tmp-dir))
                 (source (expand-file-name "blinky.sv" rtl-dir))
                 (filelist (expand-file-name "rtl/rtl.f" tmp-dir)))
            (make-directory rtl-dir t)
            (with-temp-file source
              (insert "module blinky; endmodule\n"))
            (with-temp-file filelist
              (insert "-I${BASEJUMP_STL_DIR}/bsg_misc\n")
              (insert "${BASEJUMP_STL_DIR}/bsg_misc/bsg_counter_up_down.sv\n")
              (insert "rtl/blinky.sv\n"))
            (should (equal (veri-kompass--files-from-filelist filelist)
                           (list source)))
            (should (equal (mapcar #'car
                                   (veri-kompass-list-modules-in-proj
                                    (veri-kompass--files-from-filelist filelist)))
                           '("blinky"))))
        (when (file-directory-p tmp-dir)
          (delete-directory tmp-dir t)))))
  (ert-deftest veri-kompass-test-hierarchy-recognizes-uppercase-instance ()
    "Ensure uppercase module and instance identifiers are included."
    (let ((tmp-file (make-temp-file "veri-kompass-upper" nil ".sv")))
      (unwind-protect
          (progn
            (with-temp-file tmp-file
              (insert "module ChildModule;\n")
              (insert "endmodule\n")
              (insert "module TopModule;\n")
              (insert "  ChildModule U_CHILD ();\n")
              (insert "endmodule\n"))
            (let* ((veri-kompass-module-list
                    (veri-kompass-list-modules-in-file tmp-file))
                   (veri-kompass-mod-str-hash (make-hash-table :test 'equal))
                   (hier (veri-kompass-build-hier "TopModule")))
              (should (equal veri-kompass-hier-warnings nil))
              (should (string-match-p
                       "U_CHILD"
                       (veri-kompass-orgify-hier hier 1)))))
        (when (file-exists-p tmp-file)
          (delete-file tmp-file)))))
  (ert-deftest veri-kompass-test-hierarchy-warns-for-missing-module ()
    "Ensure missing instantiated modules are reported."
    (let ((tmp-file (make-temp-file "veri-kompass-missing" nil ".sv")))
      (unwind-protect
          (progn
            (with-temp-file tmp-file
              (insert "module top;\n")
              (insert "  MissingModule u_missing ();\n")
              (insert "endmodule\n"))
            (let ((veri-kompass-module-list
                   (veri-kompass-list-modules-in-file tmp-file))
                  (veri-kompass-mod-str-hash (make-hash-table :test 'equal)))
              (veri-kompass-build-hier "top")
              (should (equal (length veri-kompass-hier-warnings) 1))
              (should (string-match-p
                       "Cannot find module MissingModule instantiated as u_missing"
                       (car veri-kompass-hier-warnings)))
              (should (string-match-p
                       "veri-kompass warnings"
                       (veri-kompass-orgify-hier-warnings)))))
        (when (file-exists-p tmp-file)
          (delete-file tmp-file)))))
  (ert-deftest veri-kompass-test-module-header-with-spaced-parameter-block ()
    "Ensure module declarations using `# (' are recognized."
    (let ((tmp-file (make-temp-file "veri-kompass-param-top" nil ".v")))
      (unwind-protect
          (progn
            (with-temp-file tmp-file
              (insert "module TOP # (\n")
              (insert "  parameter WIDTH = 8\n")
              (insert ") (\n")
              (insert "  input clk\n")
              (insert ");\n")
              (insert "endmodule\n"))
            (should (equal (mapcar #'car
                                   (veri-kompass-list-modules-in-file tmp-file))
                           '("TOP"))))
        (when (file-exists-p tmp-file)
          (delete-file tmp-file)))))
  (ert-deftest veri-kompass-test-parameterized-instance-with-spaced-block ()
    "Ensure instances using `# (' parameter blocks are kept in hierarchy."
    (let ((tmp-file (make-temp-file "veri-kompass-param-inst" nil ".v")))
      (unwind-protect
          (progn
            (with-temp-file tmp-file
              (insert "module child #(parameter WIDTH = 8) (); endmodule\n")
              (insert "module top;\n")
              (insert "  child # (\n")
              (insert "    .WIDTH(16)\n")
              (insert "  ) u_child ();\n")
              (insert "endmodule\n"))
            (let* ((veri-kompass-module-list
                    (veri-kompass-list-modules-in-file tmp-file))
                   (veri-kompass-mod-str-hash (make-hash-table :test 'equal))
                   (hier (veri-kompass-build-hier "top")))
              (should (string-match-p "u_child"
                                      (veri-kompass-orgify-hier hier 1)))))
        (when (file-exists-p tmp-file)
          (delete-file tmp-file)))))
  (ert-deftest veri-kompass-test-driver-input-without-local-driver-goes-up ()
    "Ensure input-only signals are treated as parent-driven."
    (with-temp-buffer
      (insert "module child(input clk, output out);\n")
      (insert "assign out = clk;\n")
      (insert "endmodule\n")
      (should (eq (veri-kompass-search-driver "clk") 'go-up))))
  (ert-deftest veri-kompass-test-driver-ansi-input-with-spacing-goes-up ()
    "Ensure ANSI input ports with spacing and ranges are parent-driven."
    (with-temp-buffer
      (insert "module child (\n")
      (insert "  input                   mac_en,\n")
      (insert "  input   signed  [20:0]  psum_in,\n")
      (insert "  input logic             clk\n")
      (insert ");\n")
      (insert "assign foo = mac_en & clk;\n")
      (insert "endmodule\n")
      (should (eq (veri-kompass-search-driver "mac_en") 'go-up))
      (should (eq (veri-kompass-search-driver "psum_in") 'go-up))
      (should (eq (veri-kompass-search-driver "clk") 'go-up))))
  (ert-deftest veri-kompass-test-driver-top-input-port-boundary-message ()
    "Ensure top/current input port driver tracing reports a boundary."
    (with-temp-buffer
      (insert "module top(input clk, output out);\n")
      (insert "assign out = clk;\n")
      (insert "endmodule\n")
      (goto-char (point-min))
      (search-forward "clk")
      (let ((msg (veri-kompass-test-with-captured-message
                   (veri-kompass-search-driver-at-point))))
        (should (string-match-p
                 "Signal clk is an input port of module top"
                 msg)))))
  (ert-deftest veri-kompass-test-driver-direct-assignment-wins ()
    "Ensure local direct drivers are preferred over input declarations."
    (with-temp-buffer
      (insert "module child(input clk, input root_clk);\n")
      (insert "assign clk = root_clk;\n")
      (insert "endmodule\n")
      (let ((drivers (veri-kompass-search-driver "clk")))
        (should (listp drivers))
        (should (string-match-p "assign clk = root_clk" (caar drivers))))))
  (ert-deftest veri-kompass-test-symbol-at-point-after-port-comma ()
    "Ensure symbol lookup near a port comma does not return direction keywords."
    (with-temp-buffer
      (insert "module child;\n")
      (insert "output                  former_data_write_fin,\n")
      (insert "assign former_data_write_fin = done;\n")
      (insert "endmodule\n")
      (goto-char (point-min))
      (search-forward "former_data_write_fin,")
      (should (equal (car (veri-kompass-sym-at-point))
                     "former_data_write_fin"))
      (veri-kompass-search-driver-at-point)
      (should (looking-at "former_data_write_fin = done"))))
  (ert-deftest veri-kompass-test-driver-candidate-keeps-source-position ()
    "Ensure snippet formatting does not clobber driver match positions."
    (with-temp-buffer
      (insert "module child;\n")
      (insert "assign foo = bar;\n")
      (insert "assign foo = baz;\n")
      (insert "endmodule\n")
      (let ((drivers (veri-kompass-search-driver "foo")))
        (should (= (length drivers) 2))
        (should (> (cdar drivers) 1))
        (goto-char (cdar drivers))
        (should (looking-at "foo = bar")))))
  (ert-deftest veri-kompass-test-current-module-ignores-comment-module-text ()
    "Ensure comments containing module do not corrupt current module parsing."
    (with-temp-buffer
      (insert "module real_mod;\n")
      (insert "// PE pad module\n")
      (insert "wire foo;\n")
      (insert "assign sink = foo;\n")
      (insert "endmodule\n")
      (goto-char (point-min))
      (search-forward "foo")
      (should (equal (veri-kompass--module-name-at-point-safe)
                     "real_mod"))
      (should (equal (veri-kompass-module-name-at-point)
                     "real_mod"))))
  (ert-deftest veri-kompass-test-driver-crosses-child-output-port ()
    "Ensure driver tracing follows a parent signal into a child output."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(output done, input src);\n"
      "assign done = src;\n"
      "endmodule\n"
      "module top(input src);\n"
      "wire child_done;\n"
      "child u_child (.done(child_done), .src(src));\n"
      "assign sink = child_done;\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let* ((drivers (veri-kompass-within-current-module
                      (veri-kompass-search-driver "child_done")))
            (driver (car drivers)))
       (should (= (length drivers) 1))
       (should (veri-kompass-trace-candidate-p driver))
       (should (equal (veri-kompass-trace-candidate-label driver)
                      "u_child.done"))
       (with-current-buffer (marker-buffer
                             (veri-kompass-trace-candidate-marker driver))
         (goto-char (veri-kompass-trace-candidate-marker driver))
         (should (looking-at "done = src"))))))
  (ert-deftest veri-kompass-test-driver-ignores-child-input-port-load ()
    "Ensure child input connections are not treated as drivers."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(input din);\n"
      "endmodule\n"
      "module top;\n"
      "wire parent_sig;\n"
      "child u_child (.din(parent_sig));\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let ((drivers (veri-kompass-within-current-module
                     (veri-kompass-search-driver "parent_sig"))))
       (should (null drivers)))))
  (ert-deftest veri-kompass-test-parent-port-signal-parser ()
    "Ensure parent port parsing distinguishes same-name and renamed nets."
    (with-temp-buffer
      (insert "child u_child (\n")
      (insert "  .clk(clk),\n")
      (insert "  .rst(parent_rst)\n")
      (insert ");\n")
      (goto-char (point-min))
      (let ((clk (veri-kompass--parent-port-signal-at-point "clk")))
        (should (equal (car clk) "clk"))
        (goto-char (cdr clk))
        (should (looking-at "clk")))
      (goto-char (point-min))
      (should (equal (car (veri-kompass--parent-port-signal-at-point "rst"))
                     "parent_rst"))
      (goto-char (point-min))
      (insert "  .DATA_OUT(Parent_SIG)\n")
      (goto-char (point-min))
      (should (equal (car (veri-kompass--parent-port-signal-at-point "DATA_OUT"))
                     "Parent_SIG"))))
  (ert-deftest veri-kompass-test-trace-candidate-display ()
    "Ensure structured trace candidates render useful result lines."
    (with-temp-buffer
      (insert "assign clk = root_clk;\n")
      (let ((candidate (make-veri-kompass-trace-candidate
                        :direction 'driver
                        :label "top.clk"
                        :marker (copy-marker (point-min))
                        :line 1
                        :snippet "assign clk = root_clk;"
                        :reason "same-name parent")))
        (should (string-match-p "DRIVER | top.clk | line 1"
                                (veri-kompass--candidate-display candidate)))
        (should (string-match-p "same-name parent"
                                (veri-kompass--candidate-display candidate))))))
  (ert-deftest veri-kompass-test-trace-highlight-direct-jump ()
    "Ensure direct trace jumps highlight the target signal."
    (let ((veri-kompass-trace-highlight-overlay nil)
          (veri-kompass-trace-back-stack nil))
      (with-temp-buffer
        (insert "module child;\n")
        (insert "assign foo = bar;\n")
        (insert "assign sink = foo;\n")
        (insert "endmodule\n")
        (insert "endmodule\n")
        (goto-char (point-min))
        (search-forward "sink = foo")
        (veri-kompass--search-driver-at-point-rec "foo" 32)
        (should (overlayp veri-kompass-trace-highlight-overlay))
        (should (equal (buffer-substring-no-properties
                        (overlay-start veri-kompass-trace-highlight-overlay)
                        (overlay-end veri-kompass-trace-highlight-overlay))
                       "foo")))))
  (ert-deftest veri-kompass-test-trace-highlight-selection-preview ()
    "Ensure selection preview moves the trace highlight."
    (let ((veri-kompass-trace-highlight-overlay nil))
      (with-temp-buffer
        (insert "assign foo = bar;\n")
        (let ((first (point-min))
              (second nil))
          (goto-char (point-max))
          (setq second (point))
          (insert "assign foo = baz;\n")
          (save-window-excursion
            (delete-other-windows)
            (let ((origin-window (selected-window)))
              (set-window-buffer origin-window (current-buffer))
              (veri-kompass--show-trace-selection
               (list (cons "assign foo = bar;" first)
                     (cons "assign foo = baz;" second))
               "Select driver line")
              (should (overlayp veri-kompass-trace-highlight-overlay))
              (should (= (overlay-start veri-kompass-trace-highlight-overlay)
                         first))
              (select-window (get-buffer-window veri-kompass-load-select-buffer-name))
              (with-current-buffer veri-kompass-load-select-buffer-name
                (veri-kompass-load-select-next))
              (should (= (overlay-start veri-kompass-trace-highlight-overlay)
                         second)))))))
  (ert-deftest veri-kompass-test-load-select-preview ()
    "Ensure moving across load entries previews the source location."
    (with-temp-buffer
      (insert "assign foo = bar;\nassign baz = foo;\n")
      (goto-char (point-min))
      (let ((marker (copy-marker (line-beginning-position 2))))
        (save-window-excursion
          (delete-other-windows)
          (let* ((origin-window (selected-window))
                 (select-buffer (get-buffer-create "*veri-kompass-test*")))
            (set-window-buffer origin-window (current-buffer))
            (with-current-buffer select-buffer
              (setq veri-kompass-load-select--origin-window origin-window)
              (goto-char (point-min))
              (should (veri-kompass-load-select--preview-marker marker)))
            (should (= (window-point origin-window) marker))
            (kill-buffer select-buffer)))))))
  (ert-deftest veri-kompass-test-load-top-output-port-boundary-message ()
    "Ensure top/current output port load tracing reports a boundary."
    (with-temp-buffer
      (insert "module top(input clk, output out);\n")
      (insert "assign out = clk;\n")
      (insert "endmodule\n")
      (goto-char (point-min))
      (search-forward "output ")
      (search-forward "out")
      (let ((msg (veri-kompass-test-with-captured-message
                   (veri-kompass-search-load-at-point))))
        (should (string-match-p
                 "Signal out is an output port of module top"
                 msg)))))
  (ert-deftest veri-kompass-test-load-output-port-goes-up-to-parent-load ()
    "Ensure child output port load tracing follows the parent connection."
    (let ((veri-kompass-curr-select nil)
          (veri-kompass-history nil))
      (veri-kompass-test-with-verilog-file
       (concat
        "module child(output DATA_OUT);\n"
        "assign DATA_OUT = 1'b1;\n"
        "endmodule\n"
        "module top;\n"
        "wire Parent_SIG;\n"
        "child u_child (.DATA_OUT(Parent_SIG));\n"
        "assign sink = Parent_SIG;\n"
        "endmodule\n")
       (save-window-excursion
         (delete-other-windows)
         (let ((bar (get-buffer-create veri-kompass-bar-name)))
           (setq veri-kompass-mod-str-hash (make-hash-table :test 'equal))
           (setq veri-kompass-hier (veri-kompass-build-hier "top"))
           (switch-to-buffer bar)
           (let ((inhibit-read-only t))
             (erase-buffer)
             (insert (veri-kompass-orgify-hier veri-kompass-hier 1)))
           (veri-kompass-mode)
           (goto-char (point-min))
           (search-forward "u_child")
           (veri-kompass-mark-and-jump)
           (let ((coords (veri-kompass-mod-to-file-name-pos "child")))
             (switch-to-buffer (find-file-noselect (car coords)))
             (goto-char (cadr coords)))
           (search-forward "output ")
           (search-forward "DATA_OUT")
           (veri-kompass-search-load-at-point)
           (should (string-match-p "module top" (buffer-string)))
           (should (looking-at "Parent_SIG"))
            (should (string-match-p
                     "assign sink = Parent_SIG"
                     (veri-kompass--line-snippet))))))))
  (ert-deftest veri-kompass-test-load-crosses-child-input-port ()
    "Ensure load tracing follows a parent signal into a child input."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(input clk, output out);\n"
      "assign out = clk;\n"
      "endmodule\n"
      "module top(input clk);\n"
      "child u_child (.clk(clk), .out());\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let* ((loads (veri-kompass-within-current-module
                    (veri-kompass-search-load "clk")))
            (child-load (cl-find-if #'veri-kompass-trace-candidate-p loads)))
       (should child-load)
       (should (equal (veri-kompass-trace-candidate-label child-load)
                      "u_child.clk"))
       (should (string-match-p
                "input child u_child.clk"
                (veri-kompass-trace-candidate-reason child-load)))
       (with-current-buffer (marker-buffer
                             (veri-kompass-trace-candidate-marker child-load))
         (goto-char (veri-kompass-trace-candidate-marker child-load))
         (should (looking-at "clk"))))))
  (ert-deftest veri-kompass-test-load-ignores-child-output-port ()
    "Ensure child output connections are not treated as loads."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(output out);\n"
      "assign out = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "child u_child (.out(foo));\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let ((loads (veri-kompass-within-current-module
                   (veri-kompass-search-load "foo"))))
       (should (null loads)))))
  (ert-deftest veri-kompass-test-load-crosses-renamed-child-input-port ()
    "Ensure renamed child input connections can be traced as loads."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(input child_clk, output out);\n"
      "assign out = child_clk;\n"
      "endmodule\n"
      "module top(input clk);\n"
      "child u_child (.child_clk(clk), .out());\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let* ((loads (veri-kompass-within-current-module
                    (veri-kompass-search-load "clk")))
            (child-load (cl-find-if #'veri-kompass-trace-candidate-p loads)))
       (should child-load)
       (should (equal (veri-kompass-trace-candidate-label child-load)
                      "u_child.child_clk"))
       (should (string-match-p
                "renamed boundary"
                (veri-kompass-trace-candidate-reason child-load))))))
  (ert-deftest veri-kompass-test-load-multiple-child-input-fanout ()
    "Ensure multiple child input loads produce multiple trace candidates."
    (veri-kompass-test-with-verilog-file
     (concat
      "module child(input din, output out);\n"
      "assign out = din;\n"
      "endmodule\n"
      "module top(input foo);\n"
      "child u_a (.din(foo), .out());\n"
      "child u_b (.din(foo), .out());\n"
      "endmodule\n")
     (goto-char (point-min))
     (search-forward "module top")
     (let* ((loads (veri-kompass-within-current-module
                    (veri-kompass-search-load "foo")))
            (child-loads (cl-remove-if-not
                          #'veri-kompass-trace-candidate-p loads)))
       (should (= (length child-loads) 2))
       (should (cl-find "u_a.din" child-loads
                        :key #'veri-kompass-trace-candidate-label
                        :test #'equal))
       (should (cl-find "u_b.din" child-loads
                        :key #'veri-kompass-trace-candidate-label
                        :test #'equal)))))
  (ert-deftest veri-kompass-test-trace-selection-legacy-preview-and-commit ()
    "Ensure legacy candidates preview and commit to their source positions."
    (with-temp-buffer
      (insert "module child;\n")
      (let ((first (point)))
        (insert "assign foo = bar;\n")
        (let ((second (point)))
          (insert "assign foo = baz;\n")
          (save-window-excursion
            (delete-other-windows)
            (let ((origin-window (selected-window)))
              (set-window-buffer origin-window (current-buffer))
              (veri-kompass--show-trace-selection
               (list (cons "assign foo = bar;" first)
                     (cons "assign foo = baz;" second))
               "Select driver line")
              (select-window (get-buffer-window veri-kompass-load-select-buffer-name))
              (with-current-buffer veri-kompass-load-select-buffer-name
                (veri-kompass-load-select-next)
                (should (= (window-point origin-window) second))
                (veri-kompass-load-select-commit))
              (should (eq (selected-window) origin-window))
              (should (= (window-point origin-window) second))))))))
  (ert-deftest veri-kompass-test-trace-history-back-and-forward ()
    "Ensure single-candidate trace jumps can move back and forward."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil))
      (with-temp-buffer
        (insert "module child;\n")
        (insert "assign foo = bar;\n")
        (insert "assign baz = foo;\n")
        (insert "endmodule\n")
        (goto-char (point-min))
        (search-forward "baz = foo")
        (let ((origin (point)))
          (veri-kompass--search-driver-at-point-rec "foo" 32)
          (should (= (length veri-kompass-trace-back-stack) 1))
          (should (looking-at "foo = bar"))
          (veri-kompass-trace-back)
          (should (= (point) origin))
          (should (= (length veri-kompass-trace-forward-stack) 1))
          (veri-kompass-trace-forward)
          (should (looking-at "foo = bar"))))))
  (ert-deftest veri-kompass-test-trace-highlight-history-navigation ()
    "Ensure trace history navigation highlights the target signal."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil)
          (veri-kompass-trace-highlight-overlay nil))
      (with-temp-buffer
        (insert "module child;\n")
        (insert "assign foo = bar;\n")
        (insert "assign sink = foo;\n")
        (insert "endmodule\n")
        (goto-char (point-min))
        (search-forward "sink = foo")
        (let ((origin (point)))
          (veri-kompass--search-driver-at-point-rec "foo" 32)
          (veri-kompass-trace-back)
          (should (= (point) origin))
          (should (overlayp veri-kompass-trace-highlight-overlay))
          (should (equal (buffer-substring-no-properties
                          (overlay-start veri-kompass-trace-highlight-overlay)
                          (overlay-end veri-kompass-trace-highlight-overlay))
                         "foo"))))))
  (ert-deftest veri-kompass-test-trace-history-new-jump-clears-forward ()
    "Ensure a new trace jump clears forward history."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil))
      (with-temp-buffer
        (insert "module child;\n")
        (insert "assign foo = bar;\n")
        (insert "assign baz = qux;\n")
        (insert "assign sink1 = foo;\n")
        (insert "assign sink2 = baz;\n")
        (insert "endmodule\n")
        (goto-char (point-min))
        (search-forward "sink1 = foo")
        (veri-kompass--search-driver-at-point-rec "foo" 32)
        (should veri-kompass-trace-back-stack)
        (veri-kompass-trace-back)
        (should veri-kompass-trace-forward-stack)
        (goto-char (point-min))
        (search-forward "sink2 = baz")
        (veri-kompass--search-driver-at-point-rec "baz" 32)
        (should (null veri-kompass-trace-forward-stack)))))
  (ert-deftest veri-kompass-test-trace-selection-preview-does-not-record-history ()
    "Ensure preview does not record history, while commit does."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil))
      (with-temp-buffer
        (insert "module child;\n")
        (let ((origin (point)))
          (insert "assign foo = bar;\n")
          (let ((second (point)))
            (insert "assign foo = baz;\n")
            (save-window-excursion
              (delete-other-windows)
              (let ((origin-window (selected-window)))
                (set-window-buffer origin-window (current-buffer))
                (goto-char origin)
                (veri-kompass--show-trace-selection
                 (list (cons "assign foo = bar;" origin)
                       (cons "assign foo = baz;" second))
                 "Select driver line")
                (select-window (get-buffer-window veri-kompass-load-select-buffer-name))
                (with-current-buffer veri-kompass-load-select-buffer-name
                  (veri-kompass-load-select-next)
                  (should (null veri-kompass-trace-back-stack))
                  (veri-kompass-load-select-commit))
                (should (= (length veri-kompass-trace-back-stack) 1)))))))))
  (ert-deftest veri-kompass-test-trace-history-limit ()
    "Ensure trace history limit trims oldest entries."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-history-limit 2))
      (with-temp-buffer
        (dotimes (_ 3)
          (insert "x\n")
          (veri-kompass-trace-history--record-jump))
        (should (= (length veri-kompass-trace-back-stack) 2)))))
  (ert-deftest veri-kompass-test-trace-history-skips-dead-marker ()
    "Ensure dead markers are skipped during trace back."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil))
      (with-temp-buffer
        (let ((live (copy-marker (point)))
              (dead-buffer (generate-new-buffer " *veri-kompass-dead*")))
          (with-current-buffer dead-buffer
            (insert "dead")
            (setq veri-kompass-trace-back-stack (list (copy-marker (point)))))
          (kill-buffer dead-buffer)
          (push live veri-kompass-trace-back-stack)
          (setq veri-kompass-trace-back-stack (nreverse veri-kompass-trace-back-stack))
          (veri-kompass-trace-back)
          (should (= (point) live))
          (should (null veri-kompass-trace-back-stack))))))
  (ert-deftest veri-kompass-test-trace-history-empty-messages ()
    "Ensure empty history commands only report messages."
    (let ((veri-kompass-trace-back-stack nil)
          (veri-kompass-trace-forward-stack nil))
      (should (string-match-p
               "Trace history is empty"
               (veri-kompass-test-with-captured-message
                (veri-kompass-trace-back))))
      (should (string-match-p
               "Trace forward history is empty"
               (veri-kompass-test-with-captured-message
                (veri-kompass-trace-forward))))))
  (ert-deftest veri-kompass-test-trace-highlight-dead-marker-noop ()
    "Ensure dead markers do not create trace highlights."
    (let ((veri-kompass-trace-highlight-overlay nil)
          (dead-buffer (generate-new-buffer " *veri-kompass-highlight-dead*"))
          (marker nil))
      (with-current-buffer dead-buffer
        (insert "foo")
        (goto-char (point-min))
        (setq marker (copy-marker (point))))
      (kill-buffer dead-buffer)
      (veri-kompass-highlight-trace-target marker)
      (should (null veri-kompass-trace-highlight-overlay))))
  )

(provide 'veri-kompass)

;;; veri-kompass.el ends here
