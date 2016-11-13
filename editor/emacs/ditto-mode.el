;;; ditto-mode.el --- Ditto major mode

;; Copyright (C) 2015-2016, Larry Diehl
;; Author: Larry Diehl
;; License: MIT

;; To use this mode add the follwing to your emacs initialization file:
;; (load-file "/path/to/ditto-mode.el")
;; (require 'ditto-mode)

(require 'generic-x)
(require 'comint)

(defun ditto-bind-keys ()
  (global-set-key (kbd "C-c C-l") 'ditto-check-file)
  )

(define-generic-mode 'ditto-mode
  '("#") ;; comments
  '("mutual" "data" "def" "where" "end" "|" "Type" "TYPE") ;; keywords
  '()
  '("\\.dtt$") ;; file extension
  (list 'ditto-bind-keys) ;; other functions to call
  "A mode for Ditto programs." ;; doc string
  )

(defconst *ditto* "*Ditto*"
  "Buffer used by Ditto")

(defun ditto-check-file ()
  "Type check a file using Ditto as an inferior mode."
  (interactive)
  (save-buffer 0)
  (when (get-buffer *ditto*)
    (with-current-buffer *ditto*
      (when (comint-check-proc *ditto*)
        (comint-kill-subjob))
      (delete-region (point-min) (point-max))
      )
    )

  (apply 'make-comint "Ditto" "stack" nil
         (list "exec" "dtt" "--" "-t" (buffer-file-name))
         )
  ;; Turn on compilation mode so that, e.g., 'C-x `' can be used to
  ;; jump to the next error.  This depends on compilation mode being
  ;; able to recognize the location information in the error messages.
  ;; Regexps associated with compilation mode define the location
  ;; patterns; one built-in pattern is "<file>:<line>:<column>:".
  (with-current-buffer *ditto*
    (compilation-minor-mode 1))
  (display-buffer *ditto*)
  )


(provide 'ditto-mode)
