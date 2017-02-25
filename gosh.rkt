#lang racket
(require (except-in racket/control set)
         "parse.rkt" "compile.rkt" "runtime.rkt"
         "bi.rkt"
         "toplevel.rkt"
         racket/async-channel readline/readline)
;         (for-syntax "runtime.rkt") (for-syntax "compile.rkt"))

(provide run-gosh)

(define-namespace-anchor gosh-user-namespace-anchor)
(define gosh-user-ns (namespace-anchor->namespace gosh-user-namespace-anchor))

(define (run-gosh place-channel)
  (parameterize
      [(current-namespace gosh-user-ns)]
    (repl)))

(module+ main
         (parameterize
          [(current-namespace gosh-user-ns)]
          (let ([init-file (string-append (getenv "HOME") "/.goshrc")])
            (when (file-exists? init-file)
                (gosh-load init-file)))
          (repl)))


