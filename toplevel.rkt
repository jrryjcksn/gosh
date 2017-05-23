#lang racket
(require (except-in racket/control set) db
         "parse.rkt" "compile.rkt" "runtime.rkt"
         racket/async-channel readline/readline racket/trace
         (for-syntax "runtime.rkt") (for-syntax "compile.rkt")
         compiler/cm  parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(provide (all-defined-out))

(struct hist-record (str pieces) #:transparent)

(define local-custodian (make-parameter #f))

(define .history '())

(define (repl)
  (.set-up-gosh-db)
  (let ([cp (make-continuation-prompt-tag)])
    (call-with-continuation-prompt
     (lambda ()
       (parameterize* [(print-as-expression #f)
                       (.loading #f)
                       (local-custodian #f)
                       (uncaught-exception-handler
                        (lambda (_)
                          (fprintf (current-error-port) "user break~%")
                          (when (local-custodian)
                                (custodian-shutdown-all (local-custodian))
                                (local-custodian #f))
                          (abort-current-continuation cp repl)))]
                      (do-repl)))
     cp
     #f)))

(define (do-repl)
  (let ([in (current-input-port)]
        [out (current-output-port)])
    (repl-aux 'default in out)))

(define (repl-aux read-state in out)
  (reset-toplevel-channel!)
  (case read-state
    [(default)
     (safe-prompt out #f)
     (read-and-process read-state in out)]
    [(colon)
     (safe-prompt out #t)
     (read-and-process read-state in out)]))

(define (safe-prompt out with-colon?)
  (define (colon-wrap str)
    (if with-colon? (string-append str ": ") (string-append str ". ")))

  (parameterize [(current-directory .pwd)]
                (fprintf out
                         "~a"
                         (with-handlers
                          ([exn:fail?
                            (lambda (e)
                              (colon-wrap (string-append
                                           (~a (current-directory))
                                           ">")))])
                          (colon-wrap (car (gcall prompt)))))))

(define (flat-eval exp ns)
  (if (eq? (first exp) 'begin)
      (for-each (lambda (e) (flat-eval e ns)) (rest exp))
      (eval exp ns)))

(define (run-exp exp token-state)
  (let ([ec (gensym "ec-")])
    (parameterize
     ([current-directory .pwd])
     (with-handlers
      ([exn?
        (lambda (err)
          (printf "Error executing ~s: ~s~%" exp err))])
      (let ([parsed (gosh exp token-state)]
            [cust (make-custodian)])
        (parameterize ([compile-allow-set!-undefined #t]
                       [current-custodian cust]
                       [.gosh-loader gosh-load]
                       [gosh-namespace gosh-ns]
                       [.cmd-success #t])
                      (flat-eval
                       (gosh-compile
                        parsed
                        '(lambda (val)
                           (async-channel-put .toplevel-chan val)))
                       gosh-ns)
                      (adjust-return-code)
                      (custodian-shutdown-all cust)))))))

(define (gosh-load file [ns (current-namespace)] [display #f] [retry #t])
  (let* ([src-mod (file-or-directory-modify-seconds file)]
         [dst-path (compiled-path file)]
         [dst-mod (if (file-exists? dst-path)
                      (file-or-directory-modify-seconds dst-path)
                      0)])
    (when (> src-mod dst-mod)
      (compile-gosh-file file)
      (parameterize [(compile-allow-set!-undefined #t)]
        (managed-compile-zo dst-path)))
    (parameterize
     [(.loading #t)
      (.cmd-success #t)]
     (with-handlers
      ([(lambda (e) retry)
        (lambda (err)
          (delete-file dst-path)
          (gosh-load file ns display #f))])
      (eval `(require (file ,dst-path)) (current-namespace))
      file))))

(define (use-library lib)
  (parameterize [(.loading #t)
                 (.cmd-success #t)]
    (eval `(require (file ,(compiled-path lib #:is-library? #t)))
          (current-namespace)))
  lib)

(define (gosh-exec str)
  (with-input-from-string str exec-impl))

(define (quiet-gosh-exec str ns)
  (with-input-from-string str (lambda () (exec-impl ns)))
  (values))

(define (exec-impl [ns gosh-ns] [display #f])
  (let loop ([read-state 'default] [final-results '()])
    (let-values ([(exp token-state new-read-state)
                  (gosh-read (current-input-port) read-state)])
      (parameterize
       ([current-exp-string exp])
       (cond [(eof-object? exp)
              (if (empty? final-results)
                  (void)
                  (reverse final-results))]
             [(or (not exp) (equal? exp ""))
              (loop new-read-state final-results)]
             [#t (let ([ec (gensym "ec-")] [results '()])
                   (with-handlers
                    ([exn?
                      (lambda (err)
                        (eprintf "Error executing ~s: ~s~%" exp err))])
                    (let* ([parsed (gosh exp token-state)]
                           [cust (make-custodian)]
                           [results-arg (new-arg)]
                           [results
                            (and parsed
                                 (parameterize
                                     ([compile-allow-set!-undefined #t]
                                      [current-custodian cust]
                                      [.gosh-loader gosh-load]
                                      [current-directory .pwd]
                                      [current-namespace ns]
                                      [gosh-namespace ns]
                                      [.cmd-success #t])
                                   (begin0
                                       (flat-eval
                                        `(let ([,results-arg '()])
                                           ,(gosh-compile
                                             parsed
                                             (if display
                                                 '.default-cont
                                                 `(lambda (val)
                                                    (set!
                                                     ,results-arg
                                                     (cons val
                                                           ,results-arg)))))
                                           ,(if display
                                                '(void)
                                                `(reverse ,results-arg)))
                                        ns)
                                       (adjust-return-code)
                                       (custodian-shutdown-all cust))))])
                      (loop new-read-state
                            (if (and results (not (void? results)))
                                (cons results final-results)
                                final-results)))))])))))

(define (clean-path path)
  (path->complete-path (simplify-path path)))

(define (compile-gosh-file gosh-file)
  (.set-up-gosh-db)
  (let* ([racket-file (compiled-path gosh-file)]
         [sym-file (sym-path racket-file)]
         [path (path-only racket-file)])
    (when path
      (make-directory* path)
      (make-directory* (path-only sym-file)))
    (parameterize [(module-being-compiled (clean-path gosh-file))]
      (with-input-from-file gosh-file
        (thunk (with-output-to-file racket-file
                 (thunk (compile-forms gosh-file sym-file))
                 #:exists 'replace))))))

(define (sym-path path-str)
  (let* ([home (getenv "HOME")]
         [nonlib-dir (string-append home "/.gosh")])
    (string-replace
     (string-replace path-str (string-append home "/.goshlib") nonlib-dir
                     #:all? #f)
     nonlib-dir
     (string-append home "/.goshsyms")
     #:all? #f)))

(define (compiled-path gosh-filename #:is-library? [islib? #f]
                       #:suffix [suffix ".rkt"])
  (define path (if (path? gosh-filename)
                   gosh-filename
                   (string->path gosh-filename)))
  (path->string
   (reroot-path (clean-path
                 (if (regexp-match #px".*\\.gosh$" (path->string path))
                     (path-replace-suffix path suffix)
                     (string-append (path->string path) ".rkt")))
                (build-path (getenv "HOME")
                            (if islib? ".goshlib" ".gosh")))))

(define (update-builtin-module mod-path)
  (compile-gosh-file mod-path)
  (let ([cpath (compiled-path mod-path)])
    (rename-file-or-directory cpath
                              (build-path (or (path-only mod-path)
                                              .pwd)
                                          (file-name-from-path cpath))
                              #t)))

(define (process-import import)
  (if (and (pair? import) (eq? (first import) 'import))
      (begin
        (imports (cons import (imports)))
        #t)
      #f))

(define (resolve-gosh-module name)
  (build-path (path-only (module-being-compiled)) name))

;; (define (resolve-gosh-module name)
;;   (ppfile "/tmp/y" name)
;;   (reroot-path name
;;             (ppfile "/tmp/z"
;;                     (path-only
;;                      (ppfile "/tmp/q"
;;                              (module-being-compiled)))))))

(define (rmodname name) `(file ,(rmodpath name)))

(define (rmodpath name)
  (match name
         [(list 'library val) (compiled-path (library-path val)
                                             #:is-library? #t)]
         [_ (compiled-path (resolve-gosh-module name))]))

(define (gosh-mod-path mod)
  (path->string (clean-path mod)))

(define (relative-mod-path mod)
  (string-append (path->string (path-only (module-being-compiled))) mod))

(define (library-path name)
  name)

(define (path-fname path)
  (path->string (file-name-from-path path)))

(define (make-lib name)
  (let* ([dest (compiled-path name #:is-library? #t)]
         [compiled-dest
          (build-path (path-only dest)
                      "compiled"
                      (path-add-suffix (file-name-from-path dest) ".zo"))])
    (make-directory* (build-path (path-only dest) "compiled"))
    (copy-file (compiled-path (build-path .pwd name)) dest #t)
    (copy-file (compiled-path
                (build-path .pwd "compiled"
                            (path-add-suffix (path-replace-suffix name ".rkt")
                                             ".zo"))
                #:suffix ".zo")
               compiled-dest
               #t)))

;; (define (rmodname name)
;;   (string-append name ".rkt"))

(define (gnamestr name)
  (string-append ".." name))

(define (gname name)
  (string->symbol (gnamestr name)))

(define (name-pair s)
  (let ([rname (gname s)])
    (list rname (setter-name rname))))

(define (make-requires imports)
  (reverse
   (map (lambda (import)
          (match import
            [(list 'import name 'all)
             (rmodname name)]
            [(list 'import name (list 'only syms))
             `(only-in ,(rmodname name)
                       ,@(append-map name-pair syms))]
            [(list 'import name (list 'except syms))
             `(combine-in
               (except-in ,(rmodname name)
                          ,@(foldl (lambda (val acc)
                                     (if (string? val)
                                         (append (name-pair val) acc)
                                         (append (name-pair (first val)) acc)))
                                   '()
                                   syms))
               (rename-in ,(rmodname name)
                          ,@(foldl (lambda (val acc)
                                     (if (pair? val)
                                         (cons (map gname val)
                                               (cons (map (lambda (v)
                                                            (setter-name
                                                             (gname v)))
                                                          val)
                                                     acc))
                                         acc))
                                   '()
                                   syms)))]))
        imports)))

(define (post-process-sym-entry entry)
  (match entry
         [(vector sym mod basename basemod)
          (list sym mod basename basemod)]))

(define (post-process-sym-entries entries)
  (map post-process-sym-entry entries))

(define (all-mod-syms name)
  (post-process-sym-entries
   (gqr "select * from module_symbols where mod = ?" (relative-mod-path name))))

(define (partition-excepts syms)
  (let loop ([slist syms] [skip '()] [rename '()])
    (if (empty? slist)
        (values skip rename)
        (if (pair? (first slist))
            (loop (rest slist) skip (cons (first slist) rename))
            (loop (rest slist) (cons (first slist) skip) rename)))))

(define (modsyms-except modname syms)
  (define mod (relative-mod-path modname))
  (let-values ([(skip rename) (partition-excepts syms)])
    (append
     (post-process-sym-entries
      (gqr (string-append
            "select * from module_symbols where mod = '"
            mod
            "' and name not in "
            (make-query-sym-list (append skip (map first rename))))))
     (let ([shash (apply hash (flatten rename))])
       (map (lambda (vec)
              (match vec
                [(vector sym mod basename basemod)
                 (let ([newsym (hash-ref shash sym)])
                   (list newsym mod basename basemod))]))
            (gqr
             (string-append
              "select * from module_symbols where name in "
              (make-query-sym-list (map first rename))
              " and mod = '" mod "'")))))))


(define (make-query-sym-list syms)
  (if (empty? syms)
      "()"
      (with-output-to-string
        (thunk (printf "('~a'" (first syms))
               (for-each (lambda (s) (printf ", '~a'" s)) (rest syms))
               (display ")")))))

(define (lookup-mod-sym s name)
  (if (pair? s)
      (let ([row
             (gqrow
              "select * from module_symbols where name=? and mod=?"
              (first s) name)])
        (match row
               [(vector _ mod basename basemod)
                (list (second s) mod basename basemod)]))
      (match (gqrow "select * from module_symbols where name=? and mod=?"
                    s name)
             [(vector _ mod basename basemod)
              (list s mod basename basemod)])))

(define (gosh-name name) (string-append name ".gosh"))

(define (gather-gosh-imports imports)
  (define (gather imps syms)
    (if (empty? imps)
        syms
        (append
         syms
         (gather (rest imps)
                 (match (first imps)
                        [(list 'import name 'all)
                         (all-mod-syms (gosh-name name))]
                        [(list 'import name (list 'only osyms))
                         (let ([gname (gosh-name name)])
                           (map (lambda (s) (lookup-mod-sym s gname)) osyms))]
                        [(list 'import name (list 'except syms))
                         (modsyms-except (gosh-name name) syms)])))))
  (append (if (equal? (path->string (module-being-compiled))
                      "/home/jerry/gosh/bi.gosh")
              '()
              (all-mod-syms "/home/jerry/gosh/bi.gosh"))
          (gather imports '())))

(define (translate-imports imports)
  (let ([symset (set)])
    (let loop ([imps imports] [s symset])
      (if (empty? imps)
          s
          (loop (rest imps)
                (match (first imps)
                       [(list rawname mod basename basemod)
                        (let ([name (string-append ".." rawname)])
                          (set-add (if (equal? mod basemod)
                                       (set-add s (setter-name name))
                                       s)
                                   name))]))))))


(define (check-conflicts imported-syms)
  (let ([symmap (make-hash)])
    (let loop ([syms imported-syms])
      (if (empty? syms)
          imported-syms
          (begin
            (match (first syms)
                   [(list name mod basename basemod)
                    (let ([existing (hash-ref symmap name #f)])
                      (match existing
                             [(list _ emod ebasename ebasemod)
                              (unless (and (equal? basename ebasename)
                                           (equal? basemod ebasemod))
                                      (mismatch-error (first syms) existing))]
                             [#f (hash-set! symmap name (first syms))]))])
            (loop (rest syms)))))))

(define (mismatch-error sym prevsym)
  (match (vector sym prevsym)
         [(vector (list name mod basename basemod)
                  (list pname pmod pbasename pbasemod))
          (error
           (format (string-append
                    "Symbol: '~a' imported from module: ~a (~a:~a) "
                    "conflicts with "
                    "symbol '~a' imported from module: ~a (~a:~a). "
                    "Please rename one "
                    "of the symbols.")
                   name mod basename basemod pname pmod pbasename pbasemod))]))

(define (gather-imported-syms imports)
  (define (gather imps syms)
    (if (empty? imps)
        syms
        (set-union
         syms
         (gather
          (rest imps)
          (match (first imps)
                 [(list 'import name 'all)
                  (apply set (modsyms (rmodname name)))]
                 [(list 'import name (list 'only osyms))
                  (apply set
                         (append-map
                          (lambda (s)
                            (let ([rname
                                   (gnamestr (if (pair? s) (second s) s))])
                              (list rname (setter-name rname))))
                          osyms))]
                 [(list 'import name (list 'except syms))
                  (let ([module-syms
                         (set-subtract
                          (apply set (modsyms (rmodname name)))
                          (apply set
                                 (append-map
                                  (lambda (s)
                                    (let ([rname
                                           (gnamestr
                                            (if (pair? s) (first s) s))])
                                      (list rname (setter-name rname))))
                                  syms)))])
                    (foldl
                     (lambda (val acc)
                       (if (pair? val)
                           (let ([rname (gnamestr (second val))])
                             (set-add (set-add acc rname) (setter-name rname)))
                           acc))
                     module-syms
                     syms))])))))
  (set-union (gather imports (set))
             (if (equal? (path->string (module-being-compiled))
                         "/home/jerry/gosh/bi.gosh")
                 (set)
                 (list->set (modsyms '(file "/home/jerry/gosh/bi.rkt"))))))

(define (ppfile filename val)
  (with-output-to-file filename (lambda () (write val) (newline))
                       #:exists 'append)
  val)

;; INITIALIZE rootnames TO eqhash()
;;
;; FOR EACH $module IN imported_modules[]:
;;     FOR EACH $fname IN imported_function_names[$module]:
;;         rootname[$module, $fname] ~> $root_name=([$root_mod, $root_sym]) IN
;;         IF !rootnames[$fname] THEN
;;             UPDATE rootnames TO rootnames += ($fname=>$root_name)
;;         ELSE IF rootnames[$fname] != $root_name THEN
;;             error["incompatible imports for function: ~s in modules: " +=
;;                   "(~s, ~s).", $fname, rootnames[$fname][0], $root_mod]
;;         END IF
;;     END FOR EACH funcname
;; END FOR EACH module
;;
;; imported_function_names[$mod] ->
;;
;; If a function name is declared directly in this module, its root is
;; itself in the current module.  Otherwise, the search continues with
;; the first imported module to provide the symbol, recursively.
;;
;; rootname[$mod, $fname] ->
;;     IF local_name[$mod, $fname] THEN RETURN [$mod, $fname]
;;     ELSE
;;         FOR $imod IN imported_modules[$mod]
;;             IF provides_fname[$imod, $fname] THEN
;;                 RETURN rootname[$imod, $fname]
;;         FAIL

(define (extract-imports gosh-file)
  (parameterize
      [(imports '())]
      (with-input-from-file gosh-file
        (lambda ()
          (let loop ([read-state 'default])
            (let-values ([(exp token-state new-read-state)
                          (gosh-read (current-input-port) read-state)])
              (parameterize
                  ([current-exp-string exp])
                (cond [(eof-object? exp) (imports)]
                      [(or (not exp) (equal? exp ""))
                       (loop new-read-state)]
                      [#t (with-handlers
                              ([exn?
                                (lambda (err)
                                  (eprintf "Error executing ~s: ~s~%"
                                           exp err))])
                            (let* ([parsed (gosh exp token-state)])
                              (when parsed (process-import parsed))
                              (loop new-read-state)))]))))))))

(define (compile-forms mod syms)
  (display "#lang racket")
  (newline)
  (parameterize [(exports (set))
                 (imports '())
                 (app-refs '())
                 (clause-names '())
                 (top-level-vars (mutable-set))
                 (module-name mod)]
    (let* ([defs
            (let loop ([read-state 'default] [defs '()])
              (let-values ([(exp token-state new-read-state)
                            (gosh-read (current-input-port) read-state)])
                (parameterize
                    ([current-exp-string exp])
                  (cond [(eof-object? exp) (reverse defs)]
                        [(or (not exp) (equal? exp ""))
                         (loop new-read-state defs)]
                        [#t (with-handlers
                                ([exn?
                                  (lambda (err)
                                    (eprintf "Error executing ~s: ~s~%"
                                             exp err))])
                              (let* ([parsed (gosh exp token-state)])
                                (if parsed
                                    (loop new-read-state
                                          (if (process-import parsed)
                                              defs
                                              (cons
                                               ;; (parameterize
                                               ;;     ([current-namespace
                                               ;;       gosh-ns]
                                               ;;      [gosh-namespace
                                               ;;       gosh-ns])
                                               (gosh-file-compile
                                                parsed
                                                '(lambda ignore (void)))
                                               ;; )
                                               defs)))
                                    (loop new-read-state defs))))]))))])
    (let* ([exported-syms (exports)]
             [exported-sym-list (set->list exported-syms)]
;;             [imported-syms (gather-imported-syms (imports))]
             [imported-syms (translate-imports
                             (gather-gosh-imports (imports)))]
             [imported-sym-map (gather-gosh-imports (imports))]
             [shell-refs
              (set->list
               (set-subtract
                (set-union (list->set (map (lambda (x)
                                             (string-append ".." (~a x)))
                                           (app-refs)))
                           (list->set (map ~a exported-sym-list)))
                (apply set (set-map imported-syms ~a))))]
             [locally-defined
              (append-map
               (lambda (e)
                 (if (set-member? imported-syms (symbol->string e))
                     '()
                     (list e)))
               exported-sym-list)])
        (write `(require (file "/home/jerry/gosh/runtime.rkt")
                         (file "/home/jerry/gosh/toplevel.rkt")
;;                         (file "/home/jerry/gosh/pcomb.rkt")
                         ,@(if (equal? (path->string (module-being-compiled))
                                       "/home/jerry/gosh/bi.gosh")
                               '(db)
                               '((file "/home/jerry/gosh/bi.rkt")))
                         ,@(make-requires (imports))))

        (newline)
        (write `(provide ,@exported-sym-list
                         ,@(map setter-name exported-sym-list)))
        (newline)
        (for-each (lambda (cn) (write `(define ,cn #f)) (newline))
                  (append (set->list (top-level-vars)) (clause-names)))
        (for-each (lambda (e)
                    (let* ([namestr (~a e)]
                           [cmd-name (substring namestr 2)]
                           [racket-sym (string->symbol namestr)])
                      (write `(define ,racket-sym
                                (make-shell-lookup ,cmd-name)))
                      (newline)
                      (write `(hash-set! function-clauses
                                         ',(string->symbol cmd-name)
                                         (list ,racket-sym)))
                      (newline)))
                  shell-refs)
        (for-each (lambda (e)
                    (write `(define ,(setter-name e)
                              (lambda (fun) (set! ,e fun))))
                    (newline))
                  locally-defined)
        (for-each (lambda (d) (write d) (newline)) defs)
        (let ([modpath (gosh-mod-path mod)])
          (call-with-transaction
           .gosh-db
           (thunk
            (gqe .modsym-clear modpath)
            (for-each
             (lambda (sym)
               (let ([s (substring (symbol->string sym) 2)])
                 (gqe .modsym-insert s modpath s modpath)))
             locally-defined)
            (check-conflicts imported-sym-map)
            (for-each
             (lambda (slist)
               (match
                slist
                [(list s mod basename basemod)
                 (unless (.modsym-present s modpath basename basemod)
                         (gqe .modsym-insert s modpath basename basemod))]))
             imported-sym-map))))
        (write-to-file locally-defined syms #:exists 'replace)))))

(define (sym-present? sym mod)
  (> (query-value
      .gosh-db
      "select count(*) from module_symbols where sym=? and mod=?"
      sym mod)
     0))

;; (define (compile-forms)
;;   (let loop ([read-state 'default] [final-results '()])
;;     (let-values ([(exp token-state new-read-state)
;;                   (gosh-read (current-input-port) read-state)])
;;       (parameterize
;;        ([current-exp-string exp])
;;        (cond [(eof-object? exp)
;;               (if (empty? final-results)
;;                   (void)
;;                   (reverse final-results))]
;;              [(or (not exp) (equal? exp ""))
;;               (loop new-read-state final-results)]
;;              [#t (let ([ec (gensym "ec-")] [results '()])
;;                    (with-handlers
;;                     ([exn?
;;                       (lambda (err)
;;                         (printf "Error executing ~s: ~s~%" exp err))])
;;                     (let* ([parsed (gosh exp token-state)])
;;                       (parameterize
;;                           ([current-namespace gosh-ns]
;;                            [gosh-namespace gosh-ns])
;;                         (write
;;                          (gosh-compile
;;                           parsed
;;                           '(lambda ignore (void)))))
;;                       (loop new-read-state
;;                             (if (and results (not (void? results)))
;;                                 (cons results final-results)
;;                                 final-results)))))])))))

(define histlex
  (lexer [(:* (complement (:: (:* (:~ "!")) "!" (complement " ")))) lexeme]
         [(:: "!" (:or "!"
                       (:: (:? "-") (:* (:/ "0" "9")))
                       (:: "{" (:? "-") (:* (:/ "0" "9")) "}")
                       (:: "?" (:* (:~ " " "\n" "\t" "\r" "?")))
                       (:: (:~ "{") (:* (:~ " " "\n" "\t" "\r" "?")))
                       (:: "{" (:? "?")
                           (:* (:~ " " "\n" "\t" "\r" "?" "}")) "}")))
          lexeme]))

(define (hist-chunks str)
  (let ([port (open-input-string str)])
    (let loop ([chunk (histlex port)] [chunks '()])
      (if (eq? chunk 'eof)
          (reverse chunks)
          (loop (histlex port) (cons chunk chunks))))))

(define (hist-expand str)
  (let ([chunks (hist-chunks str)])
    (let loop ([c chunks] [rep-chunks '()])
      (if (empty? c)
          (apply string-append (reverse rep-chunks))
          (let ([hchunk (hist-replace (first c))])
            (and hchunk (loop (rest c) (cons hchunk rep-chunks))))))))

(define (hist-replace-num hist numstr pos)
  (let ([num (string->number numstr)])
    (let loop ([h hist] [index (sub1 num)])
      (cond [(null? h)
             (top-level-eprint (format "No such event: ~s~%"
                                       (if pos num (- (length hist) num))))
             ""]
             [(<= index 0) (hist-record-str (first h))]
             [else (loop (rest h) (sub1 index))]))))

(define (hist-replace-prefix hist str)
  (let loop ([h hist])
    (cond [(empty? h)
           (top-level-eprint (format "No such event: ~s~%" str))
           ""]
          [(string-prefix? (first h) str)
           (hist-record-str (first h))]
          [else (loop (rest h))])))

(define (hist-replace-contains hist str)
  (let loop ([h hist])
    (cond [(empty? h)
           (top-level-eprint (format "No such event: ~s~%" str))
           ""]
          [(string-contains? (first h) str)
           (hist-record-str (first h))]
          [else (loop (rest h))])))

(define (hist-value rec range)
  (let* ([str (hist-record-str rec)]
         [pieces (hist-record-pieces rec)]
         [num-pieces (length pieces)]
         [low (first range)]
         [high (second range)])
    (or
     (and (<= low high)
          (< high num-pieces)
          (let ([refs (take (list-tail pieces low) (add1 (- high low)))])
            (string-join
             (map (lambda (ref)
                    (substring str
                               (sub1 (position-offset (first ref)))
                               (sub1 (position-offset (second ref)))))
                  refs)
             " ")))
     (begin
       (top-level-eprint (format "No such reference: ~s~%" str))
       ""))))

(define (hist-range hr l . h)
  (when (and (equal? l "*") (null? h))
        (set! l "^")
        (set! h '("$")))
  (define pieces (hist-record-pieces hr))
  (define num-pieces (length pieces))
  (define lnum
    (cond [(equal? l "^") 1]
          [(equal? l "$") (sub1 num-pieces)]
          [else (string->number l)]))
  (define hnum
    (cond [(null? h) lnum]
          [(equal? (first h) "$") (sub1 num-pieces)]
          [else (string->number (first h))]))
  (list lnum hnum))

(trace hist-range hist-value)

(define (hist-replace str)
  (let ([hist .history])
    (match str
           ["!!" (if (null? hist) str (hist-record-str (first hist)))]
           [(pregexp #px"^![!]?:([0-9]+|[$^])$" (list _ numstr))
            (if (null? hist)
                str
                (let ([fhist (first hist)])
                  (hist-value fhist (hist-range fhist numstr))))]
           [(pregexp #px"^![!]?:([0-9]+|[$^])[-]([0-9]+|[$^])$"
                     (list _ lnumstr hnumstr))
            (if (null? hist)
                str
                (let ([fhist (first hist)])
                  (hist-value fhist (hist-range fhist lnumstr hnumstr))))]
           [(pregexp #px"^![!]?:[*]$" (list _))
            (if (null? hist)
                str
                (let ([fhist (first hist)])
                  (hist-value fhist (hist-range fhist "*"))))]
           [(pregexp #px"^![-]([0-9]+)$" (list _ numstr))
            (hist-replace-num hist numstr #f)]
           [(pregexp #px"^!([0-9]+)$" (list _ numstr))
            (hist-replace-num (reverse hist) numstr #t)]
           [(pregexp #px"^[!][?][^{][^ \n\t\r?]*$" (list _))
            (hist-replace-contains hist (substring str 2))]
           [(pregexp #px"^[!][^{][^ \n\t\r?]*$" (list _))
            (hist-replace-prefix hist (substring str 1))]
           [_ str])))

(define (parse-history exp)
    (match (gosh exp 'default)
           [(struct pos (val p)) (hist-record exp p)]
           [other (hist-record other '())]))

(define (cont-for-read-state read-state)
  (if (eq? read-state 'colon)
      '.colon-cont
      '.default-cont))

(define (read-and-process read-state in out)
  (adjust-return-code)
  (let-values ([(exp token-state new-read-state)
                (gosh-read in read-state)])
    (cond [(eof-object? exp) 'done]
          [(or (equal? exp "") (not exp)) (repl-aux new-read-state in out)]
          ;; (cond [(or (eof-object? exp) (equal? exp "")) 'done]
          ;;       [(not exp) (repl-aux new-read-state in out)]
          [#t
           (let ([cust (make-custodian)]
                 [is-assignment? #f]) ; if x=<exp>, don't kill custodian
             (parameterize
              [(current-custodian cust)
               (current-directory .pwd)
               (current-exp-string exp)]
              (local-custodian cust)
              (when (equal? read-state 'default)
                    (set! exp (hist-expand exp)))
              (set! .history
                    (if (or (equal? exp "")
                            (equal? read-state 'colon)
                            (regexp-match #rx"\\s*[:].*" exp)
                            (regexp-match #rx"\\s*history\\s*" exp))
                        .history
                        (cons (parse-history exp) .history)))
              (thread
               (lambda ()
                 (with-handlers
                  ([exn?
                    (lambda (err)
                      (reset-toplevel-channel!)
                      ;; (printf "~a~%" (continuation-mark-set->context
                      ;;                 (exn-continuation-marks err)))
                      (log-error "ERROR: ~a~%" (exn-message err))
                      (async-channel-put .toplevel-chan .channel-empty))])
                  (let ([parsed (gosh exp token-state)])
                    (if parsed
                        (parameterize ([compile-allow-set!-undefined #t]
                                       [.gosh-loader gosh-load]
                                       [.gosh-compiler compile-gosh-file]
                                       [gosh-namespace (current-namespace)]
                                       [.cmd-success #t])
                                      (match parsed
                                             [(list 'assignment _ _)
                                              (set! is-assignment? #t)]
                                             [_ #t])
                                      (flat-eval
                                       (gosh-compile
                                        parsed
                                        (cont-for-read-state token-state))
                                       (current-namespace))
                                      (async-channel-put .toplevel-chan
                                                         .channel-empty))
                        (async-channel-put .toplevel-chan
                                           .channel-empty)))))))
             (let loop ([val (async-channel-get .toplevel-chan)])
               (when (not (eq? val .channel-empty))
                     (if (and (eq? token-state 'default) (string? val))
                         (fprintf out "~a" val)
                         (.gosh-fprint out val))
                     (cond [(and (eq? token-state 'colon) (not (.loading)))
                            (printf "? ")
                            (let ([input-val (read-line in)])
                              (semaphore-post .toplevel-semaphore)
                              (if (equal? input-val ";")
                                  (loop (async-channel-get .toplevel-chan))
                                  (reset-toplevel-channel!)))]
                           [#t
                            (newline out)
                            (semaphore-post .toplevel-semaphore)
                            (loop (async-channel-get .toplevel-chan))])))
             (unless is-assignment?
                     (custodian-shutdown-all cust)
                     (local-custodian #f)))
          (repl-aux new-read-state in out)])))

(define (gosh-read port read-state)
  (case read-state
    [(default)
     (let ([line (read-line port)])
       (cond [(eof-object? line) (values line 'default 'default)]
             [(= 0 (string-length line)) (gosh-read port read-state)]
             [(eqv? (string-ref line 0) #\:)
              (if (eqv? (string-length line) 1)
                  (values #f 'colon 'colon)
                  (let loop ([lines '()] [next-line line])
                    (if (or (eof-object? next-line)
                            (and (> (string-length next-line) 0)
                                 (eqv? (string-ref
                                        next-line
                                        (sub1 (string-length next-line)))
                                       #\.)))
                        (values
                         (apply string-append
                                (reverse (cons next-line lines)))
                         'colon
                         'default)
                        (loop (cons (string-append next-line "\n") lines)
                              (read-line port)))))]
             [else (values line 'default 'default)]))]
    ;; [(default)
    ;;  (let ([line (read-line port)])
    ;;    (cond [(or (eof-object? line) (= 0 (string-length line)))
    ;;           (values line 'default 'default)]
    ;;          [(eqv? (string-ref line 0) #\:)
    ;;           (if (eqv? (string-length line) 1)
    ;;               (values #f 'colon 'colon)
    ;;               (let loop ([lines '()] [next-line line])
    ;;                 (if (or (eof-object? next-line)
    ;;                         (eqv? (string-ref next-line
    ;;                                           (sub1 (string-length next-line)))
    ;;                               #\.))
    ;;                     (values
    ;;                      (apply string-append
    ;;                             (reverse (cons next-line lines)))
    ;;                      'colon
    ;;                      'default)
    ;;                     (loop (cons (string-append next-line "\n") lines)
    ;;                           (read-line port)))))]
    ;;          [else (values line 'default 'default)]))]
    [(colon)
     (let ([line (read-line port)])
       (cond [(eof-object? line) (values line 'default)]
             [(= 0 (string-length line)) (gosh-read port read-state)]
             [(and (eqv? (string-ref line 0) #\.)
                   (eqv? (string-length line) 1))
              (values #f 'colon 'default)]
             [(eqv? (string-ref line 0) #\:)
              (let loop ([lines '()] [next-line line])
                (if (or (eof-object? next-line)
                        (eqv? (string-ref next-line
                                          (sub1 (string-length next-line)))
                              #\.))
                    (values
                     (apply string-append
                            (reverse (cons next-line lines)))
                     'colon
                     'colon)
                    (loop (cons (string-append next-line "\n") lines)
                          (read-line port))))]
             [(eqv? (string-ref line 0) #\.)
              (let loop ([lines '()] [next-line (substring line 1)])
                (if (eof-object? next-line)
                    (values
                     (apply string-append (reverse lines))
                     'default
                     'colon)
                    (let ([last-char-index (sub1 (string-length next-line))])
                      (if (eqv? (string-ref next-line last-char-index) #\:)
                          (values
                           (apply string-append
                                  (reverse
                                   (cons (substring next-line 0 last-char-index)
                                         lines)))
                           'default
                           'colon)
                          (loop (cons (string-append next-line " ") lines)
                                (read-line port))))))]
             [#t (values
                  (if (eqv? (string-ref line 0) #\:)
                      (if (eqv? (string-ref line (sub1 (string-length line)))
                                #\.)
                          line
                          (string-append line "."))
                      (if (eqv? (string-ref line (sub1 (string-length line)))
                                #\.)
                          (string-append ":" line)
                          (string-append ":" line ".")))
                  'colon 'colon)]))]))

(module+ main (repl))

