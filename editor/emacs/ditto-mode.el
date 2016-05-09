;;; ditto-mode.el --- Ditto major mode

;; Copyright (C) 2015, Larry Diehl
;; Author: Larry Diehl
;; License: MIT

;; To use this mode add the follwing to your emacs initialization file:
;; (load-file "/path/to/ditto-mode.el")
;; (require 'ditto-mode)

(require 'generic-x)

(define-generic-mode 'ditto-mode
  '("#") ;; comments
  '("mutual" "data" "def" "where" "end" "|") ;; keywords
  '()
  '("\\.dtt$") ;; file extension
  () ;; other functions to call
  "A mode for Ditto programs." ;; doc string
  )

(provide 'ditto-mode)
