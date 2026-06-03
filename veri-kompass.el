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
(require 'seq)
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

(defcustom veri-kompass-predefined-macros nil
  "List of predefined macro names enabled before parsing starts."
  :type '(repeat string)
  :group 'veri-kompass)

(defface veri-kompass-inst-marked-face
  '((t :foreground "red1"))
  "Face for marking instance selected."
  :group 'veri-kompass)

(defvar veri-kompass-module-list nil)

(defvar veri-kompass-module-hier nil)

(defvar veri-kompass-mod-str-hash nil
  "This hash contains module structure hashed per module name.")

(defvar veri-kompass-project-files nil
  "Ordered list of top-level project files used for the current parse.")

(defvar veri-kompass-auto-enable-minor-mode t
  "When non-nil, enable `veri-kompass-minor-mode' for project buffers after startup.")

(defvar veri-kompass-source-kind nil
  "Kind of source used for the current parse.
The value is either `directory' or `filelist'.")

(defvar veri-kompass-include-dirs nil
  "Include directories used to resolve `include directives.")

(defvar veri-kompass-preprocessed-file-cache nil
  "Cache mapping file names to preprocessed file contents.")

(defvar veri-kompass-file-macro-env-cache nil
  "Cache mapping file names to macro environments active before each file.")

(defconst veri-kompass-bar-name "*veri-kompass-bar*")

(defconst veri-kompass-load-select-buffer-name "*veri-kompass-load-select*"
  "Buffer displaying the list of loads when multiple entries exist.")

(defconst veri-kompass-ignore-keywords '("if" "task" "assert" "disable" "define" "posedge"
                                         "negedge" "int" "for" "logic" "wire" "reg"))

(defconst veri-kompass-sym-regex "[0-9a-z_]+")

(defconst veri-kompass-ops-regex "[\]\[ ()|&\+-/%{}=<>]")

(defconst veri-kompass-module-import-clause-regexp
  "\\(?:[[:space:]\n]+import[[:space:]\n]+[^;]+;\\)*"
  "Regexp matching optional SystemVerilog import clauses in a module header.")

(defconst veri-kompass-module-start-regexp
  (concat "module[[:space:]\n]+\\([0-9A-Za-z_$]+\\)"
          veri-kompass-module-import-clause-regexp))

(defconst veri-kompass-module-end-regexp "^[[:space:]]*endmodule")

(defvar veri-kompass-hier nil
  "Holds the design hierarchy.")

(defvar veri-kompass-curr-select nil
  "Holds the position of the current instance selected (if any).")

(defvar veri-kompass-history nil
  "Holds the instance selection history.")

(cl-defstruct (veri-kompass-mod-inst (:copier nil))
  "Holds a module instantiations."
  inst-name mod-name file-name line)

<<<<<<< HEAD
(cl-defstruct (veri-kompass-trace-candidate (:copier nil))
  "Holds one driver/load trace result."
  direction label marker file line snippet reason trace)
=======
(cl-defstruct (veri-kompass-pp-result (:copier nil))
  "Holds the result of preprocessing a file."
  content env)
>>>>>>> 9a49c9006c15772ab07da50305bacc711f3118c6

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

(defun veri-kompass-sym-at-point ()
  "Return an a-list containing (sym-name . 'r-val) or (sym-name . 'l-val)."
  (save-excursion
    (re-search-backward veri-kompass-ops-regex nil t)
    (re-search-forward veri-kompass-sym-regex nil t)
    (cons (match-string-no-properties 0) (veri-kompass-sym-classify-at-point))))

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
      (push (cons (veri-kompass--line-snippet)
                  (match-beginning 0))
            res))
    res))

(defun veri-kompass--search-input-drivers (sym)
  "Return input port declarations for SYM in the current restriction."
  (let ((res ()))
    (goto-char (point-min))
    (while (re-search-forward
            (concat
             "input +\\(wire +\\)?\\(logic +\\)?\\(\\[[^]]+\\][[:space:]]*\\)?\\("
             sym
             "\\)")
            nil t)
      (push (cons (veri-kompass--line-snippet)
                  (match-beginning 4))
            res))
    (nreverse res)))

(defun veri-kompass--search-submodule-port-drivers (sym)
  "Return submodule port connection candidates for SYM."
  (let ((res ()))
    (goto-char (point-max))
    (while (re-search-backward
            (concat
             "\\..+([[:space:]]*\\("
             sym
             "\\)\\(\\[.*\\][[:space:]]*\\)?)")
            nil t)
      (push (cons (veri-kompass--line-snippet)
                  (match-beginning 1))
            res))
    res))

(defun veri-kompass--parent-port-signal-at-point (port-name)
  "Return (SIGNAL . POSITION) for parent connection PORT-NAME near point."
  (when (re-search-forward
         (concat "\\."
                 (regexp-quote port-name)
                 "[[:space:]\n]*([[:space:]\n]*\\([0-9a-z_]+\\)")
         nil t)
    (cons (match-string-no-properties 1)
          (match-beginning 1))))

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
Return `same' for same-name, `renamed' for renamed, or nil on failure."
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
    (message "Please mark current instance into hierarchy buffer.")
    nil))

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
         (_
          (veri-kompass-go-up-from-point))))
      ((null res)
       (message "Cannot find driver for %s" sym))
      ((equal (length res) 1)
       (goto-char (cdar res)))
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

(defun veri-kompass-search-load (sym)
  "Given the simbol SYM search for all its loads."
  (save-excursion
    (let ((loads ())
          (drivers (mapcar #'cdr (veri-kompass-search-driver sym 'internal))))
      (goto-char (point-max))
      (while (re-search-backward (concat "^.*\\(\\<" sym "\\>\\).*") nil t)
        (unless (member (match-beginning 1) drivers)
          (push (cons (match-string 0) (match-beginning 1))
                loads)))
      loads)))

(defvar-local veri-kompass-load-select--origin-window nil
  "Window that displayed the source buffer when load selection started.")

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

(defun veri-kompass--goto-candidate (candidate origin-buffer)
  "Go to CANDIDATE in ORIGIN-BUFFER."
  (let ((marker (veri-kompass--candidate-marker candidate origin-buffer)))
    (when (and (markerp marker)
               (buffer-live-p (marker-buffer marker)))
      (switch-to-buffer (marker-buffer marker))
      (goto-char marker)
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
  (veri-kompass-within-current-module
   (let ((res (veri-kompass-search-load (car (veri-kompass-sym-at-point)))))
     (when res
       (if (equal (length res) 1)
           (goto-char (cdar res))
         (veri-kompass--show-load-selection res))))))

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

(defun veri-kompass--copy-macro-env (env)
  "Return a copy of macro environment ENV."
  (let ((copy (make-hash-table :test 'equal)))
    (when env
      (maphash (lambda (key value)
                 (puthash key value copy))
               env))
    copy))

(defun veri-kompass--initial-macro-env ()
  "Return a fresh macro environment seeded with predefined macros."
  (let ((env (make-hash-table :test 'equal)))
    (dolist (macro veri-kompass-predefined-macros)
      (puthash macro t env))
    env))

(defun veri-kompass--current-branch-active-p (cond-stack)
  "Return non-nil when COND-STACK marks the current branch as active."
  (if cond-stack
      (plist-get (car cond-stack) :active)
    t))

(defun veri-kompass--pp-directive-line (line)
  "Return LINE stripped of comments for directive parsing."
  (string-trim (replace-regexp-in-string "//.*\\'" "" line)))

(defun veri-kompass--pp-push-branch (cond-stack parent-active condition)
  "Push a conditional branch onto COND-STACK.
PARENT-ACTIVE is the active state of the parent branch.
CONDITION is the result of the branch condition."
  (cons (list :parent-active parent-active
              :branch-taken (and parent-active condition)
              :active (and parent-active condition))
        cond-stack))

(defun veri-kompass--pp-handle-elsif (cond-stack condition)
  "Update COND-STACK for an `elsif using CONDITION."
  (if (null cond-stack)
      cond-stack
    (let* ((frame (car cond-stack))
           (parent-active (plist-get frame :parent-active))
           (branch-taken (plist-get frame :branch-taken))
           (active (and parent-active (not branch-taken) condition)))
      (setcar cond-stack
              (list :parent-active parent-active
                    :branch-taken (or branch-taken active)
                    :active active))
      cond-stack)))

(defun veri-kompass--pp-handle-else (cond-stack)
  "Update COND-STACK for an `else."
  (if (null cond-stack)
      cond-stack
    (let* ((frame (car cond-stack))
           (parent-active (plist-get frame :parent-active))
           (branch-taken (plist-get frame :branch-taken))
           (active (and parent-active (not branch-taken))))
      (setcar cond-stack
              (list :parent-active parent-active
                    :branch-taken (or branch-taken active)
                    :active active))
      cond-stack)))

(defun veri-kompass--include-file-name (line file)
  "Extract included file name from LINE relative to FILE."
  (when (string-match
         "^[[:space:]]*`include[[:space:]]+[\"<]\\([^\">]+\\)[\">]"
         line)
    (let* ((name (match-string 1 line))
           (search-dirs (cons (file-name-directory file)
                              veri-kompass-include-dirs))
           (resolved nil))
      (while (and search-dirs (not resolved))
        (let ((candidate (expand-file-name name (car search-dirs))))
          (when (file-exists-p candidate)
            (setq resolved candidate)))
        (setq search-dirs (cdr search-dirs)))
      resolved)))

(defun veri-kompass--insert-with-source (text file line)
  "Return TEXT tagged with source FILE and LINE properties."
  (let ((copy (copy-sequence text)))
    (add-text-properties 0 (length copy)
                         (list 'veri-kompass-source-file file
                               'veri-kompass-source-line line)
                         copy)
    copy))

(defun veri-kompass--preprocess-file (file env &optional include-stack)
  "Preprocess FILE using macro ENV.
INCLUDE-STACK tracks nested includes to prevent recursion loops.
Return a `veri-kompass-pp-result'."
  (let ((stack (or include-stack (list file))))
    (if (member file (cdr stack))
        (make-veri-kompass-pp-result
         :content ""
         :env env)
      (with-temp-buffer
        (insert-file-contents-literally file)
        (let ((out nil)
              (cond-stack nil))
          (goto-char (point-min))
          (while (not (eobp))
            (let* ((line-num (line-number-at-pos))
                   (line (buffer-substring-no-properties
                          (line-beginning-position) (line-end-position)))
                   (directive-line (veri-kompass--pp-directive-line line))
                   (active (veri-kompass--current-branch-active-p cond-stack)))
              (cond
               ((string-match "^[[:space:]]*`ifdef[[:space:]]+\\([0-9A-Za-z_$]+\\)" directive-line)
                (setq cond-stack
                      (veri-kompass--pp-push-branch
                       cond-stack
                       active
                       (gethash (match-string 1 directive-line) env))))
               ((string-match "^[[:space:]]*`ifndef[[:space:]]+\\([0-9A-Za-z_$]+\\)" directive-line)
                (setq cond-stack
                      (veri-kompass--pp-push-branch
                       cond-stack
                       active
                       (not (gethash (match-string 1 directive-line) env)))))
               ((string-match "^[[:space:]]*`elsif[[:space:]]+\\([0-9A-Za-z_$]+\\)" directive-line)
                (setq cond-stack
                      (veri-kompass--pp-handle-elsif
                       cond-stack
                       (gethash (match-string 1 directive-line) env))))
               ((string-match "^[[:space:]]*`else\\([[:space:]]*//.*\\)?\\'" directive-line)
                (setq cond-stack (veri-kompass--pp-handle-else cond-stack)))
               ((string-match "^[[:space:]]*`endif\\([[:space:]]*//.*\\)?\\'" directive-line)
               (when cond-stack
                  (setq cond-stack (cdr cond-stack))))
               ((and active
                     (string-match "^[[:space:]]*`define[[:space:]]+\\([0-9A-Za-z_$]+\\)" directive-line))
                (puthash (match-string 1 directive-line) t env))
               ((and active
                     (string-match "^[[:space:]]*`undef\\(ine\\)?[[:space:]]+\\([0-9A-Za-z_$]+\\)" directive-line))
                (remhash (match-string 2 directive-line) env))
               ((and active
                     (veri-kompass--include-file-name directive-line file))
                (let* ((include-file (veri-kompass--include-file-name directive-line file))
                       (result (veri-kompass--preprocess-file
                                include-file
                                env
                                (cons include-file stack))))
                  (push (veri-kompass-pp-result-content result) out)
                  (setq env (veri-kompass-pp-result-env result))))
               (active
                (push (veri-kompass--insert-with-source
                       (concat line "\n")
                       file
                       line-num)
                      out))))
            (forward-line 1))
          (make-veri-kompass-pp-result
           :content (apply #'concat (nreverse out))
           :env env))))))

(defun veri-kompass--source-files-from (source)
  "Return a pair (KIND . FILES) describing SOURCE."
  (let ((expanded (expand-file-name source)))
    (cond
     ((file-directory-p expanded)
      (setq veri-kompass-include-dirs (list expanded))
      (cons 'directory
            (veri-kompass-list-file-in-proj expanded)))
     ((file-regular-p expanded)
      (cons 'filelist
            (veri-kompass--files-from-filelist expanded)))
     (t
      (error "Path %s is neither a directory nor a readable file" source)))))

(defun veri-kompass--setup-preprocessor-context (files)
  "Initialize preprocessing caches for ordered top-level FILES."
  (setq veri-kompass-preprocessed-file-cache (make-hash-table :test 'equal))
  (setq veri-kompass-file-macro-env-cache (make-hash-table :test 'equal))
  (let ((env (veri-kompass--initial-macro-env)))
    (dolist (file files)
      (puthash file
               (veri-kompass--copy-macro-env env)
               veri-kompass-file-macro-env-cache)
      (when (eq veri-kompass-source-kind 'filelist)
        (setq env
              (veri-kompass-pp-result-env
               (veri-kompass--preprocess-file
                file
                (veri-kompass--copy-macro-env env))))))))

(defun veri-kompass--macro-env-before-file (file)
  "Return the macro environment active before FILE starts."
  (if (eq veri-kompass-source-kind 'filelist)
      (veri-kompass--copy-macro-env
       (or (gethash file veri-kompass-file-macro-env-cache)
           (veri-kompass--initial-macro-env)))
    (veri-kompass--initial-macro-env)))

(defun veri-kompass--preprocessed-file-content (file)
  "Return cached preprocessed content for FILE."
  (or (gethash file veri-kompass-preprocessed-file-cache)
      (let* ((result (veri-kompass--preprocess-file
                      file
                      (veri-kompass--macro-env-before-file file)))
             (content (veri-kompass-pp-result-content result)))
        (puthash file content veri-kompass-preprocessed-file-cache)
        content)))

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
<<<<<<< HEAD
    (setq roots (veri-kompass--filelist-roots base))
=======
    (setq veri-kompass-include-dirs nil)
>>>>>>> 9a49c9006c15772ab07da50305bacc711f3118c6
    (with-temp-buffer
      (insert-file-contents filelist)
      (while (not (eobp))
        (let* ((line (buffer-substring-no-properties
                      (line-beginning-position) (line-end-position)))
               (clean (string-trim line)))
<<<<<<< HEAD
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
=======
          (cond
           ((or (string-empty-p clean)
                (string-prefix-p "#" clean)
                (string-prefix-p "//" clean)))
           ((string-match "^\\+incdir\\+\\(.+\\)$" clean)
            (dolist (dir (split-string (match-string 1 clean) "+" t))
              (push (expand-file-name dir base) veri-kompass-include-dirs)))
           ((string-match "^-I\\(.+\\)$" clean)
            (push (expand-file-name (match-string 1 clean) base)
                  veri-kompass-include-dirs))
           ((string-match "^-I[[:space:]]+\\(.+\\)$" clean)
            (push (expand-file-name (match-string 1 clean) base)
                  veri-kompass-include-dirs))
           (t
            (let ((candidate (expand-file-name clean base)))
              (when (and (file-exists-p candidate)
                         (veri-kompass--valid-source-file-p candidate))
                (push candidate result))))))
>>>>>>> 9a49c9006c15772ab07da50305bacc711f3118c6
        (forward-line 1)))
    (setq veri-kompass-include-dirs
          (delete-dups (nreverse veri-kompass-include-dirs)))
    (delete-dups (nreverse result))))

(defun veri-kompass-list-modules-in-file (file)
  "Return the list of all declared modules present in FILE."
  (with-temp-buffer
    (insert (veri-kompass--preprocessed-file-content file))
    (goto-char (point-min))
    (let ((mod-list))
      (while (re-search-forward
              (concat "^[[:space:]]*module[[:space:]\n]+\\([0-9A-Za-z_$]+\\)"
                      veri-kompass-module-import-clause-regexp
                      "[[:space:]]*\n*[[:space:]]*\\((\\|#(\\|`\\|;\\)")
              nil t)
        (push (list
               (match-string-no-properties 1)
               (or (get-text-property (match-beginning 0) 'veri-kompass-source-file)
                   file)
               (point)
               (or (get-text-property (match-beginning 0) 'veri-kompass-source-line)
                   (line-number-at-pos (point)))
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

(defsubst veri-kompass-forward-balanced ()
  "After an opening parenthesys find the matching closing one."
  (save-match-data
    (let ((x 1))
      (while (and (> x 0)
                  (re-search-forward "\\((\\|)\\)" nil t))
        (if (equal (match-string 0) "(")
            (setq x (1+ x))
          (setq x (1- x)))))))

(defsubst veri-kompass-delete-parameters ()
  "Remove all #( ... )."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "#(" nil t)
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
  (if (gethash mod-name veri-kompass-mod-str-hash) ;; some memoization is gonna help
      (gethash mod-name veri-kompass-mod-str-hash)
    (puthash
     mod-name
     (let ((target (veri-kompass-mod-to-file-name-pos mod-name))
           (struct))
       (if target
           (with-temp-buffer
             (insert (veri-kompass--preprocessed-file-content (car target)))
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
                     "\\([0-9a-z_]+\\)[[:space:]]+\\([0-9a-z_]+\\)[[:space:]]*("  nil t)
               (when (save-match-data
                       (veri-kompass-thread-yield)
                       (veri-kompass-forward-balanced)
                       (looking-at "[[:space:]]*;"))
                 (unless (or (get-char-property 0 'code (match-string 0))
                             (get-char-property 0 'comment (match-string 0))
                             (char-equal (aref (match-string-no-properties 1) 0)
                                         ?\`)
                             (member (match-string-no-properties 1)
                                     veri-kompass-ignore-keywords)
                             (member (match-string-no-properties 2)
                                     veri-kompass-ignore-keywords))
                   (veri-kompass-thread-yield)
                   (push (make-veri-kompass-mod-inst
                          :mod-name (match-string-no-properties 1)
                          :inst-name (match-string-no-properties 2)
                          :file-name (or (get-text-property
                                          (match-beginning 0)
                                          'veri-kompass-source-file)
                                         (car target))
                          :line (or (get-text-property
                                     (match-beginning 0)
                                     'veri-kompass-source-line)
                                    (line-number-at-pos (match-beginning 0))))
                         struct)
                   (let ((sub-hier
                          (veri-kompass-build-hier-rec
                           (match-string-no-properties 1))))
                     (when sub-hier
                       (push sub-hier struct)))
                   )))
             (reverse struct))
         (message "Cannot find module %s" mod-name)
         nil))
     veri-kompass-mod-str-hash)))

(defun veri-kompass-build-hier (top)
  "Given a TOP module return the hierarcky.
This is the entry point function for parsing the design."
  (let ((target (veri-kompass-mod-to-file-name-pos top)))
    (if target
        (list (make-veri-kompass-mod-inst
               :inst-name top
               :mod-name top
               :file-name (car target)
               :line (caddr target))
              (veri-kompass-build-hier-rec top))
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

(defun veri-kompass-compute-and-create-bar (top-name)
  "Given a top module TOP-NAME create and populate the hierarky bar."
  (setq veri-kompass-hier (veri-kompass-build-hier top-name))
  (message "Parsing done.")
  (switch-to-buffer-other-window veri-kompass-bar-name)
  (let ((inhibit-read-only t))
    (erase-buffer)
    (insert (veri-kompass-orgify-hier veri-kompass-hier 1)))
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

(defun veri-kompass--project-buffer-p (&optional buffer)
  "Return non-nil when BUFFER visits a file indexed by veri-kompass."
  (let ((file-name (buffer-file-name buffer)))
    (and file-name
         veri-kompass-project-files
         (member (expand-file-name file-name) veri-kompass-project-files))))

(defun veri-kompass--maybe-enable-minor-mode ()
  "Enable `veri-kompass-minor-mode' in the current project buffer."
  (when (and veri-kompass-auto-enable-minor-mode
             (derived-mode-p 'verilog-mode)
             (veri-kompass--project-buffer-p))
    (veri-kompass-minor-mode 1)))

(defun veri-kompass--enable-minor-mode-for-project-buffers ()
  "Enable `veri-kompass-minor-mode' for currently open project buffers."
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (veri-kompass--maybe-enable-minor-mode))))

;;;###autoload
(defun veri-kompass (source &optional top-name)
  "Enable Veri-Kompass.
Veri-Kompass is a verilog codebase navigation facility.
The codebase to be parsed will be provided by SOURCE, which can be either
a directory or a Verilog filelist.
The decendent parsing will start from module TOP-NAME."
  (interactive
   (list (read-file-name "Directory or filelist: " nil nil t)))
  (let* ((source-info (veri-kompass--source-files-from source))
         (source-kind (car source-info))
         (files (cdr source-info)))
    (setq veri-kompass-source-kind source-kind)
    (setq veri-kompass-project-files files)
    (veri-kompass--setup-preprocessor-context files)
    (veri-kompass--enable-minor-mode-for-project-buffers)
  (setq veri-kompass-mod-str-hash (make-hash-table :test 'equal))
  (setq veri-kompass-module-list
        (veri-kompass-list-modules-in-proj
         files))
  (unless top-name
    (setq top-name
	  (veri-kompass-completing-read "specify top module: "
					(mapcar (lambda (x)
						  (car x))
						veri-kompass-module-list)
					"*veri-kompass-module-top-select*")))
  (message "Parsing design...")
  (veri-kompass-make-thread (lambda ()
                              (veri-kompass-compute-and-create-bar top-name)))))

(define-minor-mode veri-kompass-minor-mode
  "Minor mode to be used into verilog files."
  :lighter " VK"
  :keymap (let ((map (make-sparse-keymap)))
            (define-key map (kbd "C-c d") 'veri-kompass-search-driver-at-point)
            (define-key map (kbd "C-c l") 'veri-kompass-search-load-at-point)
            map))

(add-hook 'verilog-mode-hook #'veri-kompass--maybe-enable-minor-mode)

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

(when (featurep 'ert)
  (defun veri-kompass-test--instance-names (hier)
    "Return flat instance names extracted from HIER."
    (mapcar #'veri-kompass-mod-inst-inst-name
            (seq-filter #'veri-kompass-mod-inst-p (cadr hier))))

  (defun veri-kompass-test--build-hier-from-files (top-name files source-kind)
    "Build hierarchy for TOP-NAME from FILES using SOURCE-KIND."
    (let ((veri-kompass-source-kind source-kind)
          (veri-kompass-project-files files)
          (veri-kompass-mod-str-hash (make-hash-table :test 'equal)))
      (veri-kompass--setup-preprocessor-context veri-kompass-project-files)
      (setq veri-kompass-module-list
            (veri-kompass-list-modules-in-proj veri-kompass-project-files))
      (veri-kompass-build-hier top-name)))

  (ert-deftest veri-kompass-test-filelist-parsing ()
    "Ensure filelists are parsed as absolute filtered paths."
    (let ((tmp-dir (make-temp-file "veri-kompass-test" t)))
      (unwind-protect
          (let* ((foo (expand-file-name "foo.sv" tmp-dir))
                 (bar (expand-file-name "sub/bar.v" tmp-dir))
                 (inc (expand-file-name "inc" tmp-dir))
                 (skip (expand-file-name "skipme.v" tmp-dir))
                 (filelist (expand-file-name "dut.f" tmp-dir))
                 (veri-kompass-skip-regexp "skipme"))
            (make-directory (file-name-directory bar) t)
            (make-directory inc t)
            (dolist (path (list foo bar skip))
              (with-temp-file path
                (insert "// test file\n")))
            (with-temp-file filelist
              (insert "# comment line\n")
              (insert "+incdir+" (file-relative-name inc tmp-dir) "\n")
              (insert (file-relative-name foo tmp-dir) "\n")
              (insert (file-relative-name bar tmp-dir) "\n")
              (insert (file-relative-name skip tmp-dir) "\n"))
            (should (equal (veri-kompass--files-from-filelist filelist)
                           (list foo bar)))
            (should (equal veri-kompass-include-dirs
                           (list inc))))
        (when (file-directory-p tmp-dir)
          (delete-directory tmp-dir t)))))
<<<<<<< HEAD
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
  (ert-deftest veri-kompass-test-driver-input-without-local-driver-goes-up ()
    "Ensure input-only signals are treated as parent-driven."
    (with-temp-buffer
      (insert "module child(input clk, output out);\n")
      (insert "assign out = clk;\n")
      (insert "endmodule\n")
      (should (eq (veri-kompass-search-driver "clk") 'go-up))))
  (ert-deftest veri-kompass-test-driver-direct-assignment-wins ()
    "Ensure local direct drivers are preferred over input declarations."
    (with-temp-buffer
      (insert "module child(input clk, input root_clk);\n")
      (insert "assign clk = root_clk;\n")
      (insert "endmodule\n")
      (let ((drivers (veri-kompass-search-driver "clk")))
        (should (listp drivers))
        (should (string-match-p "assign clk = root_clk" (caar drivers))))))
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
                     "parent_rst"))))
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
=======

  (ert-deftest veri-kompass-test-preprocess-ifdef-in-file ()
    "Ensure inactive conditional branches are filtered from hierarchy."
    (let ((tmp-dir (make-temp-file "veri-kompass-test" t)))
      (unwind-protect
          (let* ((top (expand-file-name "top.sv" tmp-dir))
                 (child (expand-file-name "child.sv" tmp-dir))
                 (veri-kompass-predefined-macros '("USE_SVT"))
                 (veri-kompass-source-kind 'directory)
                 (veri-kompass-include-dirs (list tmp-dir))
                 (veri-kompass-project-files (list top child)))
            (with-temp-file top
              (insert "module top;\n")
              (insert "`ifdef USE_SVT\n")
              (insert "child chosen();\n")
              (insert "`else\n")
              (insert "child filtered();\n")
              (insert "`endif\n")
              (insert "endmodule\n"))
            (with-temp-file child
              (insert "module child;\nendmodule\n"))
            (should
             (equal
              (veri-kompass-test--instance-names
               (veri-kompass-test--build-hier-from-files
                "top"
                veri-kompass-project-files
                veri-kompass-source-kind))
              '("chosen"))))
        (when (file-directory-p tmp-dir)
          (delete-directory tmp-dir t)))))

  (ert-deftest veri-kompass-test-auto-enable-minor-mode-for-project-buffers ()
    "Enable the minor mode automatically for project buffers only."
    (let* ((file-a (expand-file-name "a.sv" temporary-file-directory))
           (file-b (expand-file-name "b.sv" temporary-file-directory))
           (veri-kompass-project-files (list file-a))
           (veri-kompass-auto-enable-minor-mode t))
      (with-temp-buffer
        (setq buffer-file-name file-a)
        (verilog-mode)
        (veri-kompass--maybe-enable-minor-mode)
        (should veri-kompass-minor-mode))
      (with-temp-buffer
        (setq buffer-file-name file-b)
        (verilog-mode)
        (veri-kompass--maybe-enable-minor-mode)
        (should-not veri-kompass-minor-mode)))))
>>>>>>> 9a49c9006c15772ab07da50305bacc711f3118c6

(provide 'veri-kompass)

;;; veri-kompass.el ends here
