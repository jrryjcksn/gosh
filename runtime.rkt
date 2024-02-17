#lang racket/base

(require ;rackunit
         (except-in racket/control set)
         racket/async-channel ;racket/trace
         racket/generator
         racket/format
         (only-in racket/port with-output-to-string)
;         racket/pretty
         db
         racket/mpair "parse.rkt" "lex.rkt"
         ;mzlib/os
         (only-in racket/system system process*/ports)
         racket/set
         racket/match
         (only-in racket/string string-prefix? string-join
                  string-replace string-append* string-split)
         )

(provide (all-defined-out)
         extract-regexp-field-names
         (all-from-out racket/mpair racket/generator))

(define-namespace-anchor a)
(define gosh-ns (namespace-anchor->namespace a))
(define gosh-namespace (make-parameter gosh-ns))

(define parse-continuations (make-parameter #f))

(define gosh-root "/Users/jerry/src/github.com/jrryjcksn/gosh")

(define module-name (make-parameter #f))
(define .cmd-success (make-parameter #t))
(define .throw-to-or. (make-parameter (lambda (x) x)))
(define .env (make-parameter
              (let* ([e (current-environment-variables)]
                     [names (environment-variables-names e)])
                (apply hash
                       (apply
                        append
                        (map
                         (lambda (name)
                           (let ([sname (bytes->string/locale name)])
                             (list (string->symbol sname)
                                   (bytes->string/locale
                                    (environment-variables-ref e name)))))
                         names))))))
(define .dollar-q-box (box 0))
(define .dollar-q-getter (make-parameter (lambda () (unbox .dollar-q-box))))
(define .dollar-q-setter
  (make-parameter (lambda (val) (set-box! .dollar-q-box val))))

(define .free-vars (make-parameter (make-hash)))

(define (.set-empty? x) (and (set? x) (set-empty? x)))
(define (.hash-empty? x) (and (hash? x) (hash-empty? x)))

;; (define $$ (getpid))
;; (define $? 0)
(define .code-set #f)

(define (set-code-set! val) (hash-set! (.free-vars) '.code-set val))
(define (set-dollar-q val) ((.dollar-q-setter) val))
(define (get-dollar-q) ((.dollar-q-getter)))

(define (adjust-return-code)
  (if (hash-ref (.free-vars) '.code-set #f)
      (set-code-set! #f)
      (set-dollar-q 0))
  (get-dollar-q))

(define (.look-up-free-var name)
  (or (hash-ref (.env) name #f)
      (hash-ref (.free-vars) name "")))

(define .gosh-root "/Users/jerry/src/github.com/jrryjcksn/gosh")

(define (root-path item) (string-append .gosh-root "/" item))

(define .gosh-home
  (or (getenv "GOSH_HOME") (string-append (getenv "HOME") "/.gosh")))

(define .gosh-db-name (string-append .gosh-home ".db"))

(define .gosh-db-sem (make-semaphore 1))

(define (.connect db)
  (virtual-connection
   (connection-pool
    (lambda () (sqlite3-connect #:database db #:mode 'create)))))

(define .gosh-db #f)

(define .modsym-check "select count(*) from module_symbols")

(define .modsym-clear "delete from module_symbols where mod = ?")

(define .modsym-create
  (string-append
    "create table module_symbols "
    "(name text, mod text, basename text, basemod text, "
    "constraint symkey primary key (name, mod))"))

(define .modsym-insert
  "insert into module_symbols values (?, ?, ?, ?)")

(define (.modsym-present name mod basename basemod)
  (> (gqv (string-append
           "select count(*) from module_symbols where "
           "name = ? "
           "and mod = ? "
           "and basename = ? "
           "and basemod = ? ")
          name mod basename basemod)
     0))

(define (gqe . args) (apply query-exec .gosh-db args))
(define (gqr . args) (apply query-rows .gosh-db args))
(define (gqv . args) (apply query-value .gosh-db args))
(define (gqrow . args) (apply query-row .gosh-db args))

(define (.populate-gosh-db)
  (eprintf "populating with: ~s~%" .modsym-create)
  (gqe .modsym-create))

(define (.set-up-gosh-db)
  (call-with-semaphore
   .gosh-db-sem
   (lambda ()
    (with-handlers
     ([exn? (lambda (err)
              (.populate-gosh-db)
              #t)])
     (unless .gosh-db (set! .gosh-db (.connect .gosh-db-name)))
     (gqr .modsym-check)))))

(define (gosh-arg-error str val)
  (error (format "~a -- ~a" str (.gosh-sprint val))))

(define (.gosh-field-constrain str num)
  (define len (string-length str))
  (define (constrain s)
    (if (negative? num)
        (let ([pnum (- num)])
          (if (< len pnum)
              (string-append (make-string (- pnum len) #\space) s)
              (substring s (- pnum len))))
        (if (< len num)
            (string-append s (make-string (- num len) #\space))
            (substring s 0 num))))
  (constrain str))

(define (gcall fun)
  (let ([result '()] [debugging .debugging]
        [actual-fun (string->symbol
                     (string-append ".." (symbol->string fun)))])
    (.nodebug)
    ((namespace-variable-value actual-fun (current-namespace))
     (lambda (x) (set! result (cons x result)))
     '())
    (when debugging (.debug))
    (reverse result)))

(define (.start-parse tokens combinator)
  (parameterize [(parse-continuations (make-hash))]
    (combinator tokens)))

;; (define-syntax (gcall stx)
;;   (let* ([exp (syntax->datum stx)] [fun (cadr exp)] [res (gensym "result")]
;;          [debugging (gensym "debugging-")])
;;     (datum->syntax
;;      stx
;;      `(eval
;;        '(let ([,res '()] [,debugging .debugging])
;;           (.nodebug)
;;           ,(list (string->symbol
;;                   (string-append ".."
;;                                  (symbol->string fun)))
;;                  `(lambda (x) (set! ,res (cons x ,res)))
;;                  `(list ,@(cddr exp)))
;;           (when ,debugging (.debug))
;;           (reverse ,res))
;;        (current-namespace)))))

(define .pwd (~a (current-directory)))
(define .oldpwd "/")

(define (.cd cont args)
  (let* ([new-dir (if (null? args) (getenv "HOME") (.ghead args))]
         [dir-string (cond [(symbol? new-dir) (~a new-dir)]
                           [(string? new-dir) new-dir]
                           [else
                            new-dir
                            (gosh-arg-error "Not a directory" new-dir)])])
    (if (directory-exists? dir-string)
        (begin
          (current-directory dir-string)
          (let ([dir-path (~a (current-directory))])
            (set! .pwd dir-path)
            (unless (equal? .oldpwd .pwd) (update-oldpwd))
            (cont dir-path)))
        (gosh-arg-error "No such directory" dir-string))))

(define (update-oldpwd) (set! .oldpwd .pwd) (gcall 'chdir))

(define (.install-shell-lookup name)
  (unless (hash-ref function-clauses name #f)
          (let ([fun (gensym "fun-")])
            (eval `(let ([,fun (make-shell-lookup ',name)])
                     (set! ,(fun->gosh-fun (symbol->string name)) ,fun)
                     (hash-set! function-clauses
                                ',name (list ,fun)))
                  (current-namespace)))))

(define (make-shell-lookup cmd)
  (let ([canonical (if (symbol? cmd)
                       (symbol->string cmd)
                       cmd)])
    (lambda (cont args . matchtail)
      (when (not (null? matchtail))
            (let ([matched? (car matchtail)])
              (when matched? (vector-set! matched? 0 #t))))
      (let ([path (find-executable-path canonical)])
        (and path (invoke-cmd path args cont))))))

(define (invoke-cmd path args cont)
  (if (executable-script? path)
      (run-script path args cont)
      (invoke-executable path args cont)))

(define (run-script path args cont)
  (let ([first-line (with-input-from-file path read-line)])
    (if (string-prefix? first-line "#!")
        (invoke-executable
         (string-append (substring first-line 2) path args cont))
        (let ([ns (make-base-namespace)])
          (parameterize [(current-namespace ns)]
                        (namespace-require 'racket/match)
                        (namespace-require
                         `(file ,(string-join `(,gosh-root "gosh.rkt") "/")))
                        (init-script-variables path args)
                        (with-input-from-file
                          (path->string (simplify-path path))
                          (lambda () (.exec cont))))))))

(define (.set-up-external-prog-lookup! namestr)
  (define name (string->symbol namestr))
  (define gname (fun->gosh-fun namestr))
  (if (hash-ref function-clauses name #f)
      (unless (namespace-variable-value gname #t (lambda () #f))
        (namespace-set-variable-value! gname (make-shell-lookup namestr)))
      (let ([fun (make-shell-lookup name)])
        (namespace-set-variable-value! gname fun)
        (hash-set! function-clause-names name (list 'fun))
        (hash-set! function-clauses name (list fun))
        (hash-set! function-defs name (list)))))

(define (get-fun f)
  (if (goshfun? f) (goshfun-fun f) f))

(struct association (key val) #:transparent)

(struct goshfun (fun defs name-str gosh-name)
        #:property prop:procedure
        (lambda (self cont args)
          (if .debugging
              (let* ([level .trace-level]
                     [level-fun (.set-tracelevel level)])
                (.trace-call (goshfun-name-str self) args cont)
                (dynamic-wind
                    level-fun
                    (lambda ()
                      ((.set-tracelevel (add1 level)))
                      ((goshfun-fun self)
                       (lambda (val)
                         (level-fun)
                         (.trace-exit (goshfun-name-str self) args val cont
                                      level-fun))
                       args
                       #f))
                    (lambda () (void)))
                (level-fun)
                (.trace-fail (goshfun-name-str self) (goshfun-gosh-name self)
                             args cont))
              ((goshfun-fun self) cont args #f))))

(struct bracefun (str procval)
        #:methods gen:custom-write
        [(define (write-proc bfun port mode)
           (fprintf port "~a" (bracefun-str bfun)))]
        #:property prop:procedure
        (lambda (self cont args)
          ((bracefun-procval self) cont args)))

(struct gregexp (str vars re)
        #:methods gen:custom-write
        [(define (write-proc gre port mode)
           (fprintf port "~a" (gregexp-str gre)))]
        #:property prop:procedure
        (lambda (self cont args)
          (match (regexp-match (gregexp-re self) (.ghead args))
                 [(list-rest _ vals)
                  (let ([results (apply append
                                        (map list (gregexp-vars self) vals))])
                    (and results (cont (apply hash results))))]
                 [_ #f])))

(define (get-defs prev mod new-def)
  (if (goshfun? prev)
      (cons (list mod new-def) (goshfun-defs prev))
      (list (list mod new-def))))

;; Unique value to tell if a cell has had a value assigned
(define cell-default (mlist 'singleton))

(define (foe thunk)
  (with-handlers ([exn:fail? (lambda (_) #f)]) (thunk)))

(define racket-funs (mutable-seteq))

(define (fun->racket-fun fun)
  (string->symbol (string-append "." (symbol->string fun))))

(define (racket-fun->fun fun)
  (string->symbol (substring (symbol->string fun) 1)))

(define (.fun-name name)
  (if (set-member? racket-funs name)
      (fun->racket-fun name)
      (fun->gosh-fun name)))

(define-syntax-rule (gosh-def! (name arg ...) body ...)
  (begin
    (set-add! racket-funs (racket-fun->fun 'name))
    (define (name cont arg ...) (cont (begin body ...)))))

(define-syntax-rule (gosh-def (name arg ...) body ...)
  (begin
    (set-add! racket-funs (racket-fun->fun 'name))
    (define (name cont args)
      (match (.mlist->list args)
             [(list arg ...)
              (cont (begin body ...))]
             [_ #f]))))

;; Debugger

(define .ports '("call" "exit" "redo" "fail"))

(define .debugging #f)

(define .tracing #f)

(define .trace-level 0)

(define .spyhash (make-hash))

(define .leashed-ports (make-hash))

(define .skip-name #f)

(define .skip-level 0)

(define (.set-tracelevel val)
  (lambda () (set! .trace-level val)))

(define (.skip name level)
  (set! .skip-name name)
  (set! .skip-level level))

(define (.noskip)
  (set! .skip-name #f))

(define (.leashed? port) (hash-ref .leashed-ports port #f))

(define (.spied? name) (hash-ref .spyhash name #f))

(define (.spy names)
  ((if (mpair? names) mfor-each for-each)
   (lambda (name)
     (set! .debugging #t)
     (hash-set! .spyhash name #t))
   names)
  (hash-keys .spyhash))

(define (.nospy names)
  ((if (mpair? names) mfor-each for-each)
   (lambda (name)
     (hash-remove! .spyhash name))
   names)
  (hash-keys .spyhash))

(define (.nospyall) (hash-clear! .spyhash) '())

(define (.debug) (set! .debugging #t) 'ok)

(define (.nodebug) (set! .debugging #f) 'ok)

(define (.trace) (set! .debugging #t) (set! .tracing #t) 'ok)

(define (.notrace) (set! .tracing #f) 'ok)

(define (.leash ports)
  (let ([set-leash
         (lambda (val)
           (lambda (port)
             (if (member port .ports)
                 (if val
                     (hash-set! .leashed-ports port #t)
                     (hash-remove! .leashed-ports port))
                 (gosh-arg-error "Not a valid port" port))))])
    (match ports
           [(or (mcons "--all" '()) (list "--all"))
            (for-each (set-leash #t) .ports)]
           [(or (mcons "--none" '()) (list "--none"))
            (for-each (set-leash #f) .ports)]
           ['() 'ok]
           [(and port-list (mcons _ _))
            (mfor-each (set-leash #t) port-list)]
           [(and port-list (list _))
            (for-each (set-leash #t) port-list)]))
  (hash-keys .leashed-ports))

(define-syntax-rule (.should-trace? name)
  (and .debugging
       (or .tracing (.spied? name))
       (or (not .skip-name)
           (and (eq? .skip-name name) (eqv? .skip-level .trace-level)))))

(define-syntax-rule (.trace-call name args cont)
  (when (.should-trace? name)
        (.debug-format "CALL" name args)
        (.process-user-debug-input "call" name args cont)))

(define-syntax-rule (.trace-redo name args cont)
  (when (.should-trace? name)
        (.debug-format "REDO" name args)
        (.process-user-debug-input "redo" name args cont)))

(define-syntax-rule (.trace-fail name gosh-name args cont)
  (when (.should-trace? name)
        (.noskip)
        (.debug-format "FAIL" name args)
        (let ([result (.process-user-debug-input "fail" name args cont)])
          (when (eq? result 'redo)
            ((namespace-variable-value gosh-name) cont args)))))

(define-syntax-rule (.trace-exit name args val cont lev-fun)
  (if (.should-trace? name)
      (begin
        (.noskip)
        (.debug-format "EXIT" name args)
        (printf " = ~a" (.gosh-format val))
        (flush-output)
        (let ([result (.process-user-debug-input "exit" name args cont)])
          (when result (cont val))
          (lev-fun)
          (.trace-redo name args cont)))
      (cont val)))

(define (.debug-format port name args)
  (printf (make-string .trace-level #\space))
  (cond [(vector? args)
         (printf "(~a) ~a: ~a(~a)" .trace-level port name
                 (string-join (for/list ([a args]) (.gosh-format a)) ", "))]
        [(or (mpair? args) (pair? args))
         (printf "(~a) ~a: ~a[~a]" .trace-level port name
                 (string-join (.mmap .gosh-format args) ", "))]
        [else
         (printf "(~a) ~a: ~a(~a)" .trace-level port name
                 (.gosh-format args))])
  (flush-output))

(define (.gosh-format arg)
  (with-output-to-string (lambda () (.gosh-print arg))))

(define (.process-user-debug-input port name args cont)
  (if (.leashed? port)
      (.interact port name args cont)
      (begin (printf "~%")
             #t)))

(define (.interact port name args cont)
  (printf "? ")
  (flush-output)
  (match port
         ["call" (case (read-line)
                   [("c") (set! .tracing #t) #t]
                   [("l") (set! .tracing #f) #t]
                   [("s") (.skip name .trace-level) #t])]
         ["redo" (case (read-line)
                   [("c") (set! .tracing #t) #t]
                   [("l") (set! .tracing #f) #t])]
         ["fail" (case (read-line)
                   [("c") (set! .tracing #t) #t]
                   [("l") (set! .tracing #f) #t]
                   [("r") 'redo])]
         ["exit" (case (read-line)
                   [("c") (set! .tracing #t) #t]
                   [("f") #f]
                   [("l") (set! .tracing #f) #t])]))

;; Pipes

(define (.as-mlist val)
  (if (pair? val)
      (list->mlist val)
      val))

(define .stdin (make-thread-cell #f))
(define .pipelist (make-thread-cell #f))
(define .semidetapp (make-thread-cell #f))

(define .main-thread (make-parameter (current-thread)))

(define .gosh-loader
  (make-parameter (lambda ignore
                    (error "No loader defined."))))

(define .gosh-executer #f)

(define .gosh-compiler
  (make-parameter (lambda ignore
                    (error "No compiler defined."))))

(define .toplevel-semaphore (make-semaphore))
(define .toplevel-chan (make-async-channel))

(define (.toplevel-wait)
  (semaphore-wait .toplevel-semaphore))

(define .channel-empty (list 'empty))

(define (clear-channel chan)
  (when (async-channel-try-get chan) (clear-channel chan)))

(define (reset-toplevel-channel!)
  (clear-channel .toplevel-chan))

(define *path* '("/bin" "/usr/bin"))

(define (set-gosh-executer! val) (set! .gosh-executer val))

(define (.load cont file [display #t])
  ((.gosh-loader) file (current-namespace) display)
  (cont (if display file (void))))

(define (.exec cont)
  (.gosh-executer)
  (cont (void)))

(define (.in)
  (let ([chan (thread-cell-ref .stdin)])
    (and chan (async-channel-get chan))))

(define (.sendin cont)
  (let ([val (.in)])
    (and (not (eq? val .channel-empty))
         (begin (cont val) (.sendin cont)))))

(define (.gosh-> x y) (and (> x y) y))
(define (.gosh->= x y) (and (>= x y) y))
(define (.gosh-< x y) (and (< x y) y))
(define (.gosh-<= x y) (and (<= x y) y))
(define (.gosh-== x y) (and (.gosh-equal? x y) y))
(define (.gosh-!= x y) (and (not (.gosh-equal? x y)) x))

(define (.gosh-equal? x y)
  (cond [(or (number? x)
             (string? x)
             (symbol? x)
             (char? x)
             (boolean? x)
             (pregexp? x)
             (set? x)
             (null? x))
         (equal? x y)]
        [(association? x) (and (association? y)
                               (.gosh-equal? (association-key x)
                                             (association-key y))
                               (.gosh-equal? (association-val x)
                                             (association-val y)))]
        [(hash? x) (and (hash? y)
                        (= (hash-count x) (hash-count y))
                        (andmap
                         (lambda (k)
                           (and (hash-has-key? y k)
                                (.gosh-equal? (hash-ref x k) (hash-ref y k))))
                         (hash-keys x)))]
        [(vector? x)
         (and (vector? y)
              (let ([xlen (vector-length x)])
                (and (= xlen (vector-length y))
                     (let loop ([i 0])
                       (cond [(>= i xlen) #t]
                             [(.gosh-equal? (vector-ref x i) (vector-ref y i))
                              (loop (add1 i))]
                             [else #f])))))]
        [(or (pair? x) (mpair? x))
         (and (or (pair? y) (mpair? y))
              (.gosh-equal? (.ghead x) (.ghead y))
              (.gosh-equal? (.gtail x) (.gtail y)))]
        [else #f]))

(define (.gosh-fail . ignore) #f)

(define (.reverse cont x)
  (cont (.rev-append (.ghead x) '())))

(define (.rev-append x acc)
  (if (null? x)
      acc
      (.rev-append (.gtail x) (mcons (.ghead x) acc))))

(define (.force glist)
  (unless (not (mpair? glist))
          (let ([the-tail (mcdr glist)])
            (when (box? the-tail)
                  (set-mcdr! glist (reset ((unbox the-tail)))))))
  #t)

(define (.possibly-stringify x)
  (match x
         [(? symbol?) (symbol->string x)]
         [(? path?) (path->string x)]
         [_ x]))

;; (define (ppwrap . things-to-pprint)
;;   (for ([item (in-list things-to-pprint)])
;;        (pretty-print item (current-error-port)))
;;   (let loop ([l things-to-pprint])
;;     (if (null? (cdr l))
;;         (car l)
;;         (loop (cdr l)))))

(define (.head cont args)
  (protected-cell-access cont (lambda () (.ghead (.ghead args)))))

(define (.tail cont args)
  (protected-cell-access cont (lambda () (.gtail (.ghead args)))))

(define (.rawtail cont arg)
  (protected-cell-access cont (lambda () (.gtail arg))))

(define (protected-cell-access cont fun)
  (let ([cell
         (with-handlers
             ([exn:fail? (lambda (_) cell-default)])
           (fun))])
    (and (not (eq? cell cell-default)) (cont cell))))

(define (.list-length l)
  (define (gl-aux l res)
    (if (null? l)
        res
        (gl-aux (.gtail l) (add1 res))))
  (gl-aux l 0))

(define (.length cont args)
  (define (process l)
    (match l
           [(? null?) (cont 0)]
           [(or (? mpair?) (? pair?)) (cont (.list-length l))]
           [(? string?) (cont (string-length l))]
           [_ (gosh-arg-error "'length' not defined for value" l)]))
  (match args
         [(? mpair?) (process (.car args))]
         [(list l) (process l)]
         [_ #f]))

(define (.racket cont args)
  (cont (mapply (eval (string->symbol (.ghead args))) (.gtail args))))

(define (.racket-pred cont args)
  (when (mapply (eval (string->symbol (.ghead args))) (.gtail args))
        (cont 'ok)))

(define (.ghead glist)
  (cond [(mpair? glist) (.car glist)]
        [(pair? glist) (car glist)]
        [(null? glist) (error "Empty list (head)")]
        [else (error "Not a list (head)")]))

(define (.gtail glist)
  (cond [(mpair? glist)
         (let ([the-tail (mcdr glist)])
           (let ([result
                  (if (box? the-tail)
                      (begin
                        (let ([new-tail (reset ((unbox the-tail) #f))])
                          (set-mcdr! glist new-tail)
                          new-tail))
                      the-tail)])
             result))]
        [(pair? glist) (cdr glist)]
        [(null? glist) (error "Empty list (tail)")]
        [else (error "Not a list (tail)")]))

(define (.nth-cdr glist n)
  (if (<= n 0)
      glist
      (.nth-cdr (.gtail glist) (sub1 n))))

(define (.iterate* start step cont)
  (cond [(and (char? start) (real? step))
         (let loop ([n (char->integer start)])
           (cont (integer->char n))
           (loop (+ n step)))]
        [(and (real? start) (real? step))
         (let loop ([n start])
           (cont n)
           (loop (+ n step)))]
        [else (gosh-arg-error "Bad iteration variables" (vector start step))]))

(define (.iterate start stop step cont)
  (cond [(and (char? start) (real? step) (char? stop))
         (let ([start-int (char->integer start)]
               [stop-int (char->integer stop)])
           (if (or (and (> start-int stop-int) (positive? step))
                   (and (< start-int stop-int) (negative? step)))
               (gosh-arg-error "Bad iteration variables" (vector start step))
               (if (>= stop-int start-int)
                   (let loop ([n start-int])
                     (and (<= n stop-int)
                          (begin
                            (cont (integer->char n))
                            (loop (+ n step)))))
                   (let loop ([n start-int])
                     (and (>= n stop-int)
                          (begin
                            (cont (integer->char n))
                            (loop (+ n step))))))))]
        [(and (real? start) (real? step) (real? stop))
         (if (or (and (> start stop) (positive? step))
                 (and (< start stop) (negative? step)))
             (gosh-arg-error "Bad iteration variables" (vector start step))
             (if (>= stop start)
                 (let loop ([n start])
                   (and (<= n stop)
                        (begin
                          (cont n)
                          (loop (+ n step)))))
                 (let loop ([n start])
                   (and (>= n stop)
                        (begin
                          (cont n)
                          (loop (+ n step)))))))]
        [else (gosh-arg-error "Bad iteration variables"
                              (vector start stop step))]))

(define (.dot cont container)
  (define (.dotlist cont lyst)
    (if (null? lyst)
        #f
        (begin
          (cont (.ghead lyst))
          (.dot cont (.gtail lyst)))))
  (define (.dothash cont hash)
    (for ([(k v) (in-hash hash)])
         (cont (association k v))))
  (define (.dotset cont set)
    (for ([val (in-set set)]) (cont val)))
  (define (.dotstring cont string)
    (for ([ch (in-string string)]) (cont ch)))
  (cond [(or (mpair? container) (pair? container)) (.dotlist cont container)]
        [(hash? container) (.dothash cont container)]
        [(set? container) (.dotset cont container)]
        [(string? container) (.dotstring cont container)]))

(define (.remove cont container item)
  (cond [(hash? container)
         (cont (hash-remove container item))]
        [(set? container)
         (cond [(set? item) (cont (set-subtract container item))]
               [(mpair? item)
                (cont
                 (let loop ([current item] [result container])
                   (if (null? current)
                       result
                       (loop (.gtail current)
                             (let ([current-val (.car current)])
                               (set-remove result current-val))))))]
               [(list? item)
                (cont
                 (foldl
                  (lambda (val acc) (set-remove acc val))
                  container
                  item))]
               [(hash? item)
                (cont (foldl
                       (lambda (val acc)
                         (set-remove acc
                                     (association val (hash-ref item val))))
                       container
                       (hash-keys item)))]
               [#t (cont (set-remove container item))])]
        [(or (mpair? container) (pair? container) (null? container))
         (let ([reslist (mlist #f)])
           (let loop ([current container] [res-tail reslist])
             (if (null? current)
                 (cont (mcdr reslist))
                 (let ([h (.ghead current)])
                   (if (.gosh-equal? h item)
                       (begin
                         (set-mcdr! res-tail
                                    (if (pair? current)
                                        (list->mlist (cdr current))
                                        (mcdr current)))
                         (cont (mcdr reslist)))
                       (let ([new-tail (mlist h)])
                         (set-mcdr! res-tail new-tail)
                         (loop (.gtail current) new-tail)))))))]
        [#t (gosh-arg-error "Not a container" container)]))

(define (.to-hash setval)
  (let loop ([result (hash)] [vals setval])
    (if (set-empty? vals)
        result
        (loop (hash-set result (set-first vals) 'ok) (set-rest vals)))))

(define (.addfold . arglist)
  (define args (if (pair? arglist) (list->mlist arglist) arglist))
  (match (mlength args)
         [0 #f]
         [1 (.ghead args)]
         [2 (.add (.ghead args) (.ghead (.gtail args)))]
         [_ (mapply .addfold
                    (mcons (.add (.ghead args) (.ghead (.gtail args)))
                           (.gtail (.gtail args))))]))

(define (.addcontainerfold . arglist)
  (define args (if (pair? arglist) (list->mlist arglist) arglist))
  (match (mlength args)
         [0 #f]
         [1 (.ghead args)]
         [2 (.addcontainer (.ghead args) (.ghead (.gtail args)))]
         [_ (mapply .addcontainerfold
                    (mcons (.addcontainer (.ghead args) (.ghead (.gtail args)))
                           (.gtail (.gtail args))))]))

(define (.addcontainer container item)
  (cond [(hash? container)
         (cond [(hash? item)
                (foldl
                 (lambda (key acc)
                   (hash-set acc key (hash-ref item key)))
                 container
                 (hash-keys item))]
               [(mpair? item)
                (let loop ([current item] [result container])
                  (if (null? current)
                      result
                      (loop (.gtail current)
                            (let ([current-assoc (.car current)])
                              (if (association? current-assoc)
                                  (hash-set
                                   result
                                   (association-key current-assoc)
                                   (association-val current-assoc))
                                  (gosh-arg-error "Not an association"
                                         current-assoc))))))]
               [(list? item)
                (foldl
                 (lambda (assoc acc)
                   (if (association? assoc)
                       (hash-set acc
                                 (association-key assoc)
                                 (association-val assoc))
                       (gosh-arg-error "Not an association" assoc)))
                 container
                 item)]
               [#t (gosh-arg-error "Not an association container" item)])]
        [(set? container)
         (cond [(hash? item)
                (foldl
                 (lambda (val acc)
                   (set-add acc (association val (hash-ref item val))))
                 container
                 (hash-keys item))]
               [(set? item) (set-union container item)]
               [(mpair? item)
                (let loop ([current item] [result container])
                  (if (null? current)
                      result
                      (loop (.gtail current)
                            (let ([current-val (.car current)])
                              (set-add result current-val)))))]
               [(list? item)
                (foldl
                 (lambda (val acc) (set-add acc val))
                 container
                 item)]
               [(string? item)
                (let ([strlen (string-length item)])
                  (let loop ([index 0] [result container])
                    (if (>= index strlen)
                         result
                         (loop (add1 index)
                               (set-add result (string-ref item index))))))]
               [#t (gosh-arg-error "Not a container" item)])]
        [(string? container)
         (cond [(set? item) (.addcontainer container (set->list item))]
               [(mpair? item)
                (let loop ([current item] [result '()])
                  (if (null? current)
                      (string-append container (reverse result))
                      (loop (.gtail current)
                            (let ([current-val (.car current)])
                              (if (char? current-val)
                                  (cons current-val result)
                                  (gosh-arg-error "Not a character"
                                                  current-val))))))]
               [(list? item)
                (for-each (lambda (c)
                            (unless (char? c)
                                    (gosh-arg-error "Not a character" c)))
                          item)
                (string-append container (list->string item))]
               [(string? item) (string-append container item)]
               [#t (gosh-arg-error "Not a container of characters" item)])]
        [(null? container)
         (cond [(mlist? item) item]
               [(list? item) (list->mlist item)]
               [(null? item) '()]
               [(set? item) (list->mlist (set->list item))]
               [(hash? item) (list->mlist
                              (for/list ([(k v) (in-hash item)])
                                        (association k v)))]
               [(string? item) (list->mlist (string->list item))]
               [(vector? item) (list->mlist (vector->list item))]
               [#t (gosh-arg-error "Not a container" item)])]
        [(or (mpair? container) (pair? container))
         (let ([mlist (cond [(mlist? item) item]
                            [(list? item) (list->mlist item)]
                            [(null? item) '()]
                            [(set? item) (list->mlist (set->list item))]
                            [(hash? item) (list->mlist
                                           (for/list ([(k v) (in-hash item)])
                                                     (association k v)))]
                            [(string? item) (list->mlist (string->list item))]
                            [(vector? item) (list->mlist (vector->list item))]
                            [#t (gosh-arg-error "Not a container" item)])])
           (if mlist
               (let-values ([(cfirst clast) (.copy container)])
                 (set-mcdr! clast mlist)
                 cfirst)
               #f))]
        [#t (gosh-arg-error "Not a container" item)]))

(define (.add container item)
  (cond [(hash? container)
         (if (association? item)
             (hash-set container
                       (association-key item)
                       (association-val item))
             (gosh-arg-error "Not an association" item))]
        [(set? container) (set-add container item)]
        [(string? container)
         (cond [(char? item) (string-append container (string item))]
               [#t (gosh-arg-error "Not a character" item)])]
        [(null? container) (mlist item)]
        [(or (pair? container) (mpair? container))
         (let-values ([(cfirst clast) (.copy container)])
           (set-mcdr! clast (mlist item))
           cfirst)]
        [#t (gosh-arg-error "Not a container" item)]))

(define (.cons x y)
  (if (mpair? y) (mcons x y) (cons x y)))

(define (.car x)
  (if (mpair? x) (mcar x) (car x)))

(define (.cdr x)
  (if (mpair? x) (mcdr x) (cdr x)))

(define (.lcopy l)
  (let ([h (mlist (car l))])
    (let loop ([current h] [next (cdr l)])
      (if (pair? next)
          (let ([next-cell (mlist (car next))])
            (set-mcdr! current next-cell)
            (loop next-cell (cdr next)))
          (values h current)))))

(define (.mcopy l)
  (let ([h (mlist (mcar l))])
    (let loop ([current h] [next (mcdr l)])
      (if (mpair? next)
          (let ([next-cell (mlist (mcar next))])
            (set-mcdr! current next-cell)
            (loop next-cell (mcdr next)))
          (values h current)))))

(define (.copy l)
  (if (mpair? l) (.mcopy l) (.lcopy l)))

(define (adjust-index index container len-fun)
  (and (integer? index)
       (let* ([len (len-fun container)]
              [idx (if (< index 0) (+ len index) index)])
         (and (< -1 idx len) idx))))

(define (adjust-slice-index index container len-fun)
  (and (integer? index)
       (let* ([len (len-fun container)]
              [idx (if (< index 0) (+ len index) index)])
         (and (<= 0 idx len) idx))))

(define (.fetch cont container indices)
  (define (frame-fetch frame index)
    (cond [(hash? container)
           (hash-ref container index #f)]
          [(vector? container)
           (let ([idx (adjust-index index container vector-length)])
             (and idx (vector-ref container idx)))]
          [(set? container)
           (and (set-member? container index) container)]
          [(association? container) ; assoc
           (let ([idx (adjust-index index container (lambda _ 2))])
             (and idx (if (= idx 0)
                          (association-key container)
                          (association-val container))))]
          [(mpair? container)
           (let ([idx (adjust-index index container mlength)])
             (and idx (.list-ref (lambda (x) x) container idx)))]
          [(list? container)
           (let ([idx (adjust-index index container length)])
             (and idx (list-ref container idx)))]
          [(string? container)
           (let ([idx (adjust-index index container string-length)])
             (and idx (string-ref container idx)))]
          [#t (gosh-arg-error "Not a container" frame)]))
  (match indices
         ['()
          (cont container)
          #f]
         [(? .force (mcons car cdr))
          (let ([sub-container (frame-fetch container car)])
            (and sub-container (.fetch cont sub-container cdr)))
          #f]
         [(cons car cdr)
          (let ([sub-container (frame-fetch container car)])
            (and sub-container (.fetch cont sub-container cdr)))
          #f]
         [_
          (gosh-arg-error "Non-list passed for indices" indices)]))

(define (mlist->vector mlyst)
  (let* ([len (.list-length mlyst)]
         [vec (make-vector len)])
    (let loop ([i 0] [current mlyst])
      (if (>= i len)
          vec
          (begin
            (vector-set! vec i (.ghead current))
            (loop (add1 i) (.gtail current)))))))

(define (.assign cont container indices val)
  (define (hash-assign h idx idxs item)
    (if (null? idxs)
        (hash-set h idx item)
        (hash-set h idx (assign-aux (hash-ref h idx) idxs item))))
  (define (vector-assign vec idx idxs item)
    (match
     idx
     [(struct association (key val))
      (mlist->vector (list-assign (vector->list vec) idx idxs item))]
     [(? integer?)
      (let ([adjusted-idx (adjust-index idx vec vector-length)])
        (and adjusted-idx
             (match
              vec
              ['#() #f]
              [_ (let ([new-vec
                        (let* ([vlen (vector-length vec)]
                               [out-vec (make-vector vlen)])
                          (let loop ([idx 0])
                            (if (>= idx vlen)
                                out-vec
                                (begin
                                  (vector-set! out-vec
                                               idx
                                               (vector-ref vec idx))
                                  (loop (add1 idx))))))])
                   (vector-set! new-vec adjusted-idx
                                (if (null? idxs)
                                    item
                                    (assign-aux (vector-ref vec adjusted-idx)
                                                idxs
                                                item)))
                   new-vec)]
              [_ (gosh-arg-error "Invalid tuple index" idx)])))]))
  (define (list-assign lyst idx idxs item)
    (match
     idx
     [(struct association (key val))
      (and (null? idxs)
           (integer? key)
           (integer? val)
           (or (and (null? lyst)
                    (and (or (= key 0) (= key -1))
                         (or (= val 0) (= val -1)))
                    (.addcontainer '() item))
               (let ([adjusted-start
                      (adjust-slice-index key lyst .list-length)]
                     [adjusted-end
                      (adjust-slice-index val lyst .list-length)])
                 (and adjusted-start
                      adjusted-end
                      (match
                       lyst
                       [(or (? .force (mcons kar kdr))
                            (cons kar kdr))
                        (cond
                         [(eq? key 0)
                          (let ([to-add (if (null? idxs)
                                            item
                                            (assign-aux kar idxs item))])
                            (when (or (string? to-add)
                                      (set? to-add)
                                      (hash? to-add)
                                      (vector? to-add))
                                  (set! to-add (.addcontainer '() to-add)))
                            (and (or (pair? to-add) (mpair? to-add))
                                 (.addcontainer to-add
                                                (.nth-cdr lyst (- val key)))))]
                         [else
                          (let ([res (list-assign
                                      kdr
                                      (association (sub1 adjusted-start)
                                                   (sub1 adjusted-end))
                                      idxs
                                      item)])
                            (and res (mcons kar res)))])])))))]
      [(? integer?)
       (let ([adjusted-idx (adjust-index idx lyst .list-length)])
         (and adjusted-idx
              (match
               lyst
               ['() #f]
               [(or (? .force (mcons kar kdr))
                    (cons kar kdr))
                (if (eq? adjusted-idx 0)
                    (mcons
                     (if (null? idxs)
                         item
                         (assign-aux kar idxs item))
                     kdr)
                    (let ([res (list-assign kdr (sub1 adjusted-idx) idxs item)])
                      (and res (mcons kar res))))])))]
      [_ (gosh-arg-error "Invalid list index" idx)]))
  (define (string-assign str idx idxs item)
    (match
     idx
     [(struct association (key val))
      (when (or (pair? item)
                (mpair? item)
                (set? item)
                (hash? item)
                (vector? item))
            (set! item (.addcontainer "" item)))
      (and (null? idxs)
           (integer? key)
           (integer? val)
           (or (and (equal? str "")
                    (and (or (= key 0) (= key -1))
                         (or (= val 0) (= val -1)))
                    (.addcontainer "" item))
               (let ([adjusted-start
                      (adjust-slice-index key str string-length)]
                     [adjusted-end
                      (adjust-slice-index val str string-length)])
                 (and adjusted-start
                      adjusted-end
                      (string-append (substring str 0 adjusted-start)
                                     item
                                     (substring str adjusted-end))))))]
      [(? integer?)
       (let ([adjusted-idx (adjust-index idx str string-length)])
         (and adjusted-idx
              (match
               str
               ["" #f]
               [_ (string-append (substring str 0 adjusted-idx)
                                 (string item)
                                 (substring str (add1 adjusted-idx)))])))]
      [_ (gosh-arg-error "Invalid string index" idx)]))
  (define (assign-aux container indices val)
    (unless (or (mpair? indices) (pair? indices))
            (gosh-arg-error "Invalid indices" indices))
    (cond [(or (mpair? container) (pair? container) (null? container))
           (list-assign container
                        (.ghead indices)
                        (.gtail indices)
                        val)]
          [(string? container)
           (string-assign container (.ghead indices) (.gtail indices) val)]
          [(hash? container)
           (hash-assign container (.ghead indices) (.gtail indices) val)]
          [(vector? container)
           (vector-assign container (.ghead indices) (.gtail indices) val)]
          [else (gosh-arg-error "Invalid container for assignment"
                       container)]))
  (let ([res (assign-aux container indices val)])
    (and res (cont res))))

  ;; (define (frame-fetch frame index)
  ;;   (cond [(hash? container)
  ;;          (hash-ref container index #f)]
  ;;         [(set? container)
  ;;          (and (set-member? container index) container)]
  ;;         [(association? container) ; assoc
  ;;          (let ([idx (adjust-index index container (lambda _ 2))])
  ;;            (and idx (if (= idx 0)
  ;;                         (association-key container)
  ;;                         (association-val container))))]
  ;;         [(mpair? container)
  ;;          (let ([idx (adjust-index index container mlength)])
  ;;            (and idx (.list-ref identity container idx)))]
  ;;         [(list? container)
  ;;          (let ([idx (adjust-index index container length)])
  ;;            (and idx (list-ref container idx)))]
  ;;         [(string? container)
  ;;          (let ([idx (adjust-index index container string-length)])
  ;;            (and idx (string-ref container idx)))]
  ;;         [#t #f]))
  ;; (match indices
  ;;        ['()
  ;;         (cont container)
  ;;         #f]
  ;;        [(? .force (mcons car cdr))
  ;;         (let ([sub-container (frame-fetch container car)])
  ;;           (and sub-container (.fetch cont sub-container cdr)))
  ;;         #f]
  ;;        [(cons car cdr)
  ;;         (let ([sub-container (frame-fetch container car)])
  ;;           (and sub-container (.fetch cont sub-container cdr)))
  ;;         #f]
  ;;        [_
  ;;         (error "Non-list passed for indices." indices)]))

(define (without-errors cont thunk val)
  (call-with-values
      (lambda () (catching-errors thunk val))
    (lambda (val success?) (and success? (cont val)))))

(define (catching-errors thunk val)
  (let ([success? #t]
        [retval val])
    (with-handlers ([exn:fail? (lambda (ignore) (set! success? #f))])
      (set! retval (thunk)))
    (values retval success?)))

(define (display-error thunk)
  (let ([success? #t])
    (with-handlers
     ([exn? (lambda (err)
              (set! success? #f)
              (fprintf (current-error-port) "Error: ~s~n" (exn-message err)))])
     (thunk))
    success?))

(define (zip f l1 l2)
  (cond [(and (null? l1) (null? l2)) '()]
        [(or (null? l1) (null? l2)) #f]
        [else (let ([tail (zip f (cdr l1) (cdr l2))])
                (and tail
                     (cons (cons (car l1) (car l2)) tail)))]))

(define (.list-ref cont container index)
  (cond [(or (null? container) (not (integer? index))) #f]
        [(eqv? index 0) (cont (.car container))]
        [#t (.list-ref cont (.gtail container) (sub1 index))]))

(define (.gosh-print val)
  (.gosh-fprint (current-output-port) val))

(define (.gosh-sprint val)
  (with-output-to-string (lambda () (.gosh-print val))))

(define (.gosh-fprint out val)
  (.gosh-fprint-aux out val 0 0))

(define (.gosh-fprint-aux out val len depth)
  (if (> depth (.print-depth))
      (fprintf out "<..>")
      (match val
        [(? number?)
         (fprintf out "~s" val)]
        [(? string?)
         (.gosh-str-fprint out val)]
        [(? symbol?)
         (.gosh-sym-fprint out val)]
        [(? char?)
         (fprintf out "?~c" val)]
        [(? boolean?)
         (fprintf out (if val "&!t" "&!f"))]
        [(? pregexp?)
         (fprintf out "~a" (string-append "$" (substring (~a val) 3)))]
        ['() (fprintf out "[]")]
        [(struct association (left right))
         (.gosh-fprint-aux out left 0 (add1 depth))
         (fprintf out "=>")
         (.gosh-fprint-aux out right 0 (add1 depth))]
        [(? hash?)
         (fprintf out "&[")
         (let ([first-time #t])
           (for ([(k v) (in-hash val)]
                 [i (in-range (.print-length))])
                (if first-time
                    (set! first-time #f)
                    (fprintf out ", "))
                (.gosh-fprint-aux out k 0 (add1 depth))
                (fprintf out "=>")
                (.gosh-fprint-aux out v 0 (add1 depth)))
           (when (> (hash-count val) (.print-length))
             (fprintf out ", ..."))
           (fprintf out "]"))]
        [(? set?)
         (fprintf out "&{")
         (let ([first-time #t])
           (for ([v (in-set val)]
                 [i (in-range (.print-length))])
                (if first-time
                    (set! first-time #f)
                    (fprintf out ", "))
                (.gosh-fprint-aux out v 0 (add1 depth)))
           (when (> (set-count val) (.print-length))
             (fprintf out ", ..."))
           (fprintf out "}"))]
        [(? .force (mcons car cdr))
         (fprintf out "[")
         (.gosh-fprint-aux out car 0 (add1 depth))
         (.gosh-fprint-tail out cdr (add1 len) depth)]
        [(cons car cdr)
         (fprintf out "[")
         (.gosh-fprint-aux out car 0 (add1 depth))
         (.gosh-fprint-tail out cdr (add1 len) depth)]
        [(vector vals ...)
         (fprintf out "(")
         (cond [(= (length vals) 0) (fprintf out ")")]
               [(= (length vals) 1)
                (.gosh-fprint-aux out (car vals) 0 (add1 depth))
                (fprintf out ",)")]
               [else
                (.gosh-fprint-aux out (car vals) 0 (add1 depth))
                (.gosh-fprint-tuple-tail out (cdr vals) 1 depth)])]
        [(? void?) #t]
        [_
         (fprintf out "~s" val)])))

(define (.gosh-fprint-tuple-tail out val len depth)
  (if (> len (.print-length))
      (fprintf out ", ...)")
      (match val
        ['() (fprintf out ")")]
        [(cons car cdr)
         (fprintf out ", ")
         (.gosh-fprint-aux out car 0 (add1 depth))
         (.gosh-fprint-tuple-tail out cdr (add1 len) depth)])))

(define (.gosh-fprint-tail out val len depth)
  (if (> len (.print-length))
      (fprintf out ", ...]")
      (match val
        ['() (fprintf out "]")]
        [(? .force (mcons car cdr))
         (fprintf out ", ")
         (.gosh-fprint-aux out car 0 (add1 depth))
         (.gosh-fprint-tail out cdr (add1 len) depth)]
        [(cons car cdr)
         (fprintf out ", ")
         (.gosh-fprint-aux out car 0 (add1 depth))
         (.gosh-fprint-tail out cdr (add1 len) depth)]
        [_
         (fprintf out " . ")
         (.gosh-fprint-aux out val 0 depth)
         (fprintf out "]")])))

(define (.gosh-sym-fprint out sym)
  (let ([str (symbol->string sym)])
    (.gosh-str-fprint out str)))

(define (.gosh-str-fprint out str)
  (if (or (equal? str "")
          (hash-ref keywords str #f)
          (and (not (eqv? (string-ref str 0) #\&))
               (or (has-special-char? str)
                   (starts-with-nonstart-char? str)))
          (regexp-match #px"^\\d+$" str))
      (fprintf out "'~a'" (quote-single-quotes str))
      (fprintf out "~a" str)))

(define (quote-single-quotes str)
  (string-replace str "'" "\\'"))

(define (starts-with-nonstart-char? str)
  (regexp-match #"^[^a-zA-Z_].*" str))

(define (has-special-char? str)
  (regexp-match #"[^-a-zA-Z0-9_+/.]+" str))

(define-logger wmatch)

(define (splitf-at lyst pred)
  (let loop ([in-list lyst] [out-prefix '()])
    (cond [(null? in-list) (values (reverse out-prefix) '())]
          [(not (pred (car in-list))) (values (reverse out-prefix) in-list)]
          [else (loop (cdr in-list) (cons (car in-list) out-prefix))])))

(define (.wild-match path-item current-dir cont)
  (if (or (symbol? path-item) (string? path-item))
        (call/ec
         (lambda (exit)
           (define (first-char str) (string-ref str 0))
           (define starts-with-slash? (eqv? (first-char path-item) #\/))
           (define starts-with-dot?
             (or (regexp-match #px"^[.][^/]+$" path-item)
                 (regexp-match #px"^.*/[.][^./]+$" path-item)))
           (define (remove-prefix str prefix)
             (substring str (string-length prefix)))
           (define (strip-result str)
             (if starts-with-slash? str (remove-prefix str current-dir)))
           (define magic-dot-star ".*")
           (define (fail) (exit #f))
           (define (exists? f) (or (file-exists? f) (directory-exists? f)))
           (define (pathify-seg seg)
             (case seg
               [(up) ".."]
               [(same) "."]
               [else (path->string seg)]))
           (define (base-path-segments str)
             (map pathify-seg (explode-path str)))
           (define (path-string segs)
             (if (null? segs) "" (path->string (apply build-path segs))))
           (define (path-segments str)
             (let* ([base-segments (base-path-segments str)]
                    [segments
                     (if (equal? (car base-segments) "/")
                         base-segments
                         (append (base-path-segments current-dir)
                                 base-segments))])
               segments))
           (define (translate-seg seg)
             (let ([result
                    (match seg
                           ["**" magic-dot-star]
                           ["*" "[^/]*"]
                           ["?" "[^/]"]
                           [s (translate-wild-chars s)])])
               (values result (string=? result seg))))
           (define (translate-wild-chars seg)
             (log-wmatch-debug "translate-wild-chars -- Seg: ~s" seg)
             (define seg-len (string-length seg))
             (let loop ([index 0] [chunk-index 0] [chunks '()])
               (define (add-chunk)
                 (cons (substring seg chunk-index index) chunks))
               (if (>= index seg-len)
                   (if (> index chunk-index)
                       (string-append* (reverse (add-chunk)))
                       (string-append* (reverse chunks)))
                   (match (string (string-ref seg index))
                          ["\\"
                           (if (= (add1 index) seg-len)
                               (string-append* (reverse (add-chunk)))
                               (let ([new-index (+ index 2)])
                                 (loop new-index
                                       new-index
                                       (cons (string-append
                                              "["
                                              (string-ref seg (add1 index))
                                              "]")
                                             (add-chunk)))))]
                          ["["
                           (let brackloop ([here index])
                             (cond [(>= here seg-len) (failure-cont)]
                                   [(eqv? (string-ref seg here) #\])
                                    (let ([new-index (add1 here)])
                                      (loop new-index new-index
                                            (cons (substring seg index
                                                             new-index)
                                                  (add-chunk))))]
                                   [else (brackloop (add1 here))]))]
                          [(regexp #rx"[^*?.]")
                           (loop (+ index 1) chunk-index chunks)]
                          ["*"
                           (let ([recur
                                  (lambda (increment)
                                    (let ([new-index (+ index increment)])
                                      (loop new-index
                                            new-index
                                            (cons "[^/]*" (add-chunk)))))])
                             (if (and (> seg-len (add1 index))
                                      (eqv? (string-ref seg (add1 index)) #\*))
                                 (recur 2)
                                 (recur 1)))]
                          ["?"
                           (let ([new-index (add1 index)])
                             (loop new-index new-index (cons "[^/]" (add-chunk))))]
                          ["."
                           (let ([new-index (add1 index)])
                             (loop new-index new-index (cons "[.]" (add-chunk))))]))))
           (define (no-wild? str)
             (define end-index (string-length str))
             (define (nowild-impl index)
               (if (>= index end-index)
                   #t
                   (let ([next-ch (string-ref str index)])
                     (case next-ch
                       [(#\\) (or (= index (sub1 end-index))
                                  (nowild-impl (+ index 2)))]
                       [(#\* #\? #\[) #f]
                       [else (nowild-impl (add1 index))]))))
             (nowild-impl 0))
           (define (header-and-wild str)
             (let-values ([(header-segs wild) (splitf-at (path-segments str)
                                                         no-wild?)])
               (log-wmatch-debug "header-and-wild -- Path String: ~s, Wild: ~s"
                                 (path-string header-segs) wild)
               (values (path-string header-segs) wild)))
           (define (wild-impl header segs)
             (log-wmatch-debug "wild-impl -- Header: ~s, Segs: ~s"
                               header segs)
             (if (null? segs)
                 (when (exists? header) (cont (strip-result header)))
                 (let-values ([(translated nowild)
                               (translate-seg (car segs))])
                   (log-wmatch-debug "wild-impl -- Translated: ~s, Nowild: ~s"
                                     translated nowild)
                   (let* ([last-seg (null? (cdr segs))]
                          [is-magic? (eq? translated magic-dot-star)]
                          [pattern (pregexp
                                    (string-append "^" translated "$"))])
                     (log-wmatch-debug "wild-impl -- IsMagic: ~s, Pattern: ~s"
                                       is-magic? pattern)
                     (when is-magic? (wild-impl header (cdr segs)))
                     (for ([f (in-list (with-handlers*
                                        ([exn:fail? (lambda (_) '())])
                                        (directory-list header)))])
                          (let ([fstr (path->string f)])
                            (when (and (or starts-with-dot?
                                           (not (eqv? (string-ref fstr 0) #\.)))
                                       (if nowild
                                           (string=? translated fstr)
                                           (regexp-match pattern fstr)))
                                  (let ([new-header
                                         (path->string
                                          (build-path header fstr))])
                                    (when (or last-seg
                                              (directory-exists? new-header))
                                          (log-wmatch-debug
                                           "wild-impl -- New Header: ~s "
                                           new-header)
                                          (wild-impl new-header
                                                     (if is-magic?
                                                         segs
                                                         (cdr segs))))))))))))
           (let ([path-str (~a path-item)])
             (unless (> (string-length path-str) 0) (fail))
             (call-with-values (lambda () (header-and-wild path-str))
               wild-impl))))
  #f))

(define (.strip-backslashes str)
  (if (string? str)
      (regexp-replace* #rx"[\\](.)" str "\\1")
      str))

(define function-clause-names (make-hasheq))
(define function-clauses (make-hasheq))
(define function-defs (make-hasheq))
(define module-symbols (make-hasheq))

(define .loading (make-parameter #f))
(define .print-length (make-parameter 8))
(define .print-depth (make-parameter 4))

(define (fun->gosh-fun fun)
  (let ([gosh-name (string->symbol (string-append ".." fun))])
    gosh-name))

;; (define-for-syntax (translate-fun fun)
;;   (string->symbol (string-append "." fun)))

(define (ensure-mlist l)
  (if (mpair? l) l (list->mlist l)))

(define (mapply f ml)
  (cond
   [(null? ml) (f)]
   [(pair? ml) (apply f ml)]
   [(null? (mcdr ml)) (f (mcar ml))]
   [(null? (mcdr (mcdr ml))) (f (mcar ml) (mcar (mcdr ml)))]
   [else (apply f (mlist->list ml))]))

;; (define-syntax (pass-through exp)
;;   (syntax-case exp ()
;;     [(pass-through fun)
;;      (let ([fun-name (syntax-e #'fun)])
;;        (with-syntax ([translated-fun-name
;;                       (datum->syntax #'fun (translate-fun fun-name))])
;;                     #'(begin (set-add! racket-funs 'fun)
;;                              (define (translated-fun-name cont args)
;;                                (cont (mapply fun args))))))]))

(define (.pop-clause name)
  (let ([clause-list (hash-ref function-clauses name #f)])
    (when clause-list
          (let ([new-clause-list (cdr clause-list)])
            (if (null? new-clause-list)
                (error "Attempt to pop last function clause.")
                (begin (hash-set! function-clauses name new-clause-list)
                       (hash-set!
                        function-clause-names name
                        (cdr (hash-ref function-clause-names name)))
                       (hash-set!
                        function-defs name
                        (cdr (hash-ref function-defs name)))))))))

(define (ensure-var-defined name)
  (let ([local-names (.free-vars)]
        [var-defined? #t])
    (if local-names
        (let ([ref (hash-ref local-names name local-names)])
          (when (eq? ref local-names)
                (let ([top-level-val
                       (namespace-variable-value
                        name #f (lambda () (set! var-defined? #f)))])
                  (if var-defined?
                      (namespace-set-variable-value! name "")
                      (hash-set! local-names name "")))))
        (begin
          (namespace-variable-value
           name #f (lambda () (set! var-defined? #f)))
          (unless var-defined?
                  (namespace-set-variable-value! name ""))))))

(define (.stringify item)
  (cond [(string? item) item]
        [(symbol? item) (symbol->string item)]
        [else (with-output-to-string (lambda () (.gosh-print item)))]))

(define (strip-$ sym)
  (substring (.stringify sym) 1))

(define (flatlist item)
  (string-join (.mmap .stringify item) " "))

(define (.split-words cont arg)
  (if (string? arg)
      (.dot cont (filter (lambda (x) (not (equal? x "")))
                         (string-split arg)))
      (cont arg)))

(define (on-error thunk value)
  (with-handlers
   ([exn? (lambda (err) value)])
   (thunk)))

(define (process-port-input port fun)
  (with-handlers
   ([exn? (lambda (err) #f)])
   (let loop ([val (read-line port)])
     (if (eof-object? val)
         (begin (close-input-port port)
                #f)
         (begin
           (fun val)
           (loop (read-line port)))))))

(define (top-level-print val)
  (top-level-fprint (current-output-port) val))

(define (top-level-eprint val)
  (top-level-fprint (current-error-port) val))

(define (top-level-fprint port val)
  (if (string? val)
      (fprintf port "~a" val)
      (.gosh-fprint port val)))

(define (.print-defs fname)
  (define base-string "---------------")
  (define base-length (string-length base-string))
  (define (print-defs-aux lyst mod)
    (unless (null? lyst)
            (if (or (null? (caar lyst)) (equal? (caar lyst) mod))
                (printf "~%~a~%" (cadar lyst))
                (printf "~%~a:~%~%~a~%" (caar lyst) (cadar lyst)))
            (print-defs-aux (cdr lyst) (caar lyst))))
  (printf "~a ~a ~a" base-string fname base-string)
  (let* ([fun (on-error (lambda ()
                          (namespace-variable-value (fun->gosh-fun fname)))
                        #f)]
         [defs (if (goshfun? fun) (goshfun-defs fun) '())])
    (if (null? defs)
        (printf "~%")
        (print-defs-aux (reverse defs) #f)))
  (printf "~a~%~%" (string-append
                    base-string
                    (make-string (+ 2 (string-length (~a fname))) #\-)
                    base-string)))

(define (.print-all-defs)
  (for ([key (sort (hash-keys function-defs)
                   (lambda (f1 f2)
                     (string<? (symbol->string f1) (symbol->string f2))))])
       (.print-defs (symbol->string key))))

(define (.mmap fun arg-list)
  (define (aux args)
    (if (null? args)
        '()
;;        (cons (fun (mcar args)) (.mmap fun (mcdr args)))))
        (cons (fun (mcar args)) (.mmap fun (.gtail args)))))
  (if (mpair? arg-list)
      (aux arg-list)
      (map fun arg-list)))

(define (.tolist listish)
  (.mmap (lambda (x) x) listish))

(define (.mlist->list mlist)
  (if (null? mlist)
      '()
      (cons (mcar mlist) (.mlist->list (mcdr mlist)))))

(define (.colon-cont val)
  (async-channel-put .toplevel-chan val)
  (.toplevel-wait))

(define (.default-cont val)
  (.display val)
  (unless (void? val) (newline)))

(define (.display val)
  (if (or (string? val) (char? val))
      (printf "~a" val)
      (.gosh-fprint (current-output-port) val)))

(define (.chunked-lazy-list thunk chunk-size cont)
  (let* ([results (mcons '() '())]
         [tail results]
         [count 0]
         [val (reset
               (thunk
                (lambda (arg-val)
                  (set! count (add1 count))
                  (set-mcdr! tail (mcons arg-val '()))
                  (set! tail (mcdr tail))
                  (when (>= count chunk-size)
                        (shift ret
                               (set-mcdr! tail (box ret))
                               (let ([ret-val (mcdr results)])
                                 (set! results (mcons '() '()))
                                 (set! tail results)
                                 ret-val)))))
               (mcdr results))])
    (cont val)))

(define (.pipe-list chunk-size)
  (let* ([results (mcons '() '())]
         [tail results]
         [count 0]
         [val (reset
               (let loop ([item (.in)])
                 (if (not (eq? item .channel-empty))
                     (begin
                       (set! count (add1 count))
                       (set-mcdr! tail (mcons item '()))
                       (set! tail (mcdr tail))
                       (when (>= count chunk-size)
                             (shift ret
                                    (set-mcdr! tail (box ret))
                                    (let ([ret-val (mcdr results)])
                                      (set! results (mcons '() '()))
                                      (set! tail results)
                                      ret-val)))
                       (loop (.in)))
                     (begin
                       (thread-cell-set! .stdin #f)
                       '())))
               (mcdr results))])
    (thread-cell-set! .pipelist val)
    val))

(define (gre regexp)
  (let-values ([(vars pat) (extract-regexp-field-names regexp)])
    (gregexp (string-append "$'" regexp "'")
             (map strip-$ vars)
             (pregexp pat))))

(define (.strict-list thunk cont)
  (let* ([results (mlist #f)]
         [tail results])
    (thunk
     (lambda (arg-val)
       (set-mcdr! tail (mlist arg-val))
       (set! tail (mcdr tail))))
    (cont (mcdr results))))

(define (.debug-wrapper name-str gosh-name clause)
  (lambda (cont args)
    (if .debugging
        (let* ([level .trace-level]
               [level-fun (.set-tracelevel level)])
          (.trace-call name-str args cont)
          (dynamic-wind
              level-fun
              (lambda ()
                ((.set-tracelevel (add1 level)))
                (clause
                 (lambda (val)
                   (level-fun)
                   (.trace-exit name-str args val cont level-fun))
                 args
                 #f))
              (lambda () (void)))
          (level-fun)
          (.trace-fail name-str gosh-name args cont))
        (clause cont args #f))))

(define (.anon-debug-wrapper name-str gosh-name fun)
  (lambda (cont args)
    (if .debugging
        (let* ([level .trace-level]
               [level-fun (.set-tracelevel level)])
          (.trace-call name-str args cont)
          (dynamic-wind
              level-fun
              (lambda ()
                ((.set-tracelevel (add1 level)))
                (fun
                 (lambda (val)
                   (level-fun)
                   (.trace-exit name-str args val cont level-fun))
                 args))
              (lambda () (void)))
          (level-fun)
          (.trace-fail name-str gosh-name args cont))
        (fun cont args))))

(define (set-func! name func)
  (parameterize [(compile-allow-set!-undefined #t)]
    (eval `(set! ,name ,func))))
;;     (namespace-set-variable-value! name func)))

;; (define (init-clause-name name)
;;   (eval `(define ,name #f) gosh-ns))

;; (define (set-func! name func)
;;   (parameterize [(current-namespace gosh-ns)]
;;     (namespace-set-variable-value! name func)))

;; (define (init-clause-name name)
;;   (eval `(define ,name #f) gosh-ns))

(define (.define-clause-wrapper name clause-name clause gosh-name def)
  ;; (when (equal? gosh-name "..max")
  ;;       (ppwrap 'namespace gosh-name (current-namespace)))
;;  (set-func! clause-name clause)
  (let ([name-str (symbol->string name)])
;;    (parameterize [(current-namespace gosh-ns)]
      ;; (set-func!
      ;;  gosh-name
      ;;  (.debug-wrapper name-str gosh-name clause))
      (hash-set! function-clause-names name
                 (cons clause-name
                       (hash-ref! function-clause-names name '())))
      (hash-set! function-clauses name
                 (cons clause
                       (hash-ref! function-clauses name '())))
      (when def
        (hash-set! function-defs name
                   (cons def (hash-ref! function-defs name '()))))))

(define (executable-script? path)
  (and (member 'execute (file-or-directory-permissions path))
       (regexp-match #".*text\n$"
                     (with-output-to-string
                       (lambda ()
                         (system (string-append "file "
                                                (path->string path))))))))

(define (init-script-variables path args)
  (namespace-set-variable-value! '$0 (path->string path))
  (namespace-set-variable-value! '$* args)
  (let ([num-args (.list-length args)])
    (let loop ([index 1] [lyst args])
      (if (> index num-args)
          'ok
          (begin
            (hash-set (.free-vars)
                      (string->symbol (format "<toplevel>..~a" index))
                      (.car lyst))
            (loop (add1 index) (.cdr lyst)))))))

(define (invoke-executable path args cont)
  (if (eq? cont .default-cont)
      (match-let*
       ([stdin (thread-cell-ref .stdin)]
        [(list in-port out-port _ err-port proc)
         (apply process*/ports (current-output-port)
                (if stdin #f (current-input-port))
                (current-error-port)
                path #:set-pwd? #t (.mmap .stringify args))])
       (when stdin
             (let loop ([val (async-channel-get stdin)])
               (if (not (eq? val .channel-empty))
                   (begin
                     (top-level-fprint out-port val)
                     (newline out-port)
                     (flush-output out-port)
                     (loop (async-channel-get stdin)))
                   (close-output-port out-port))))
       (proc 'wait)
       (when (.cmd-success)
             (let ([ecode (proc 'exit-code)])
               (.cmd-success (= ecode 0))
               (set-code-set! #t)
               (set-dollar-q ecode))))
      (match-let* ([stdin (thread-cell-ref .stdin)]
                   [(list in-port out-port _ err-port proc)
                    (apply process*/ports #f (if stdin #f (current-input-port))
                           (current-error-port) path #:set-pwd? #t
                           (.mmap .stringify args))])
                 (when stdin
                       (thread
                        (lambda ()
                          (let loop ([val (async-channel-get stdin)])
                            (if (not (eq? val .channel-empty))
                                (begin
                                  (top-level-fprint out-port val)
                                  (newline out-port)
                                  (flush-output out-port)
                                  (loop (async-channel-get stdin)))
                                (close-output-port out-port))))))
                 (process-port-input in-port cont)
                 (proc 'wait)
                 (when (.cmd-success)
                       (let ([ecode (proc 'exit-code)])
                         (.cmd-success (= ecode 0))
                         (set-code-set! #t)
                         (set-dollar-q ecode))))))

(define (.app-return fun arg)
  (lambda (cont) (when (fun arg) (cont arg))))

