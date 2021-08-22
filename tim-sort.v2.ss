(eval-when (compile load eval) (optimize-level 3))
(meta define do-assert? #f)

(define-syntax do-assert
  (lambda (x)
    (syntax-case x ()
      [(_ expr)
       do-assert?
       #'(let ([result expr])
          (when (not result)
                (printf "~a\n" 'expr)
                (assert result)))]
      [else #f])))

(define-syntax inc!
  (syntax-rules ()
    [(_ x) (set! x (fx+ x 1))]
    [(_ x d) (set! x (fx+ x d))]))

(define-syntax dec!
  (syntax-rules ()
    [(_ x) (set! x (fx- x 1))]
    [(_ x d) (set! x (fx- x d))]))

(define (tim-sort-range! lt? v lo hi)
  (define MIN_MERGE 32)
  (define MIN_GALLOP 7)
  (define INITIAL_TMP_STORAGE_LENGTH 256)

  (define range-length (fx- hi lo))
  (define min-gallop MIN_GALLOP)
  (define tmp-array)
  (define run-bases)
  (define run-lengths)
  (define stack-size 0)
  (define stack-length
    (cond
      [(fx< range-length 120) 5]
      [(fx< range-length 1542) 10]
      [(fx< range-length 119151) 24]
      [else 40]))
  (define (init-stack-and-tmp-array)
    (set! run-bases (make-fxvector stack-length))
    (set! run-lengths (make-fxvector stack-length))
    (set! tmp-array
          (make-vector
            (if (fx< range-length (* 2 INITIAL_TMP_STORAGE_LENGTH))
                (fxsll range-length 1)
                INITIAL_TMP_STORAGE_LENGTH))))
  (define-syntax t-get
    (syntax-rules ()
      [(_ i) (vector-ref tmp-array i)]))

  (define-syntax v-get
    (syntax-rules ()
      [(_ i) (vector-ref v i)]))
  (define-syntax v-set!
    (syntax-rules ()
      [(_ i val) (vector-set! v i val)]))

  (define-syntax rb-get
    (syntax-rules ()
      [(_ i) (fxvector-ref run-bases i)]))
  (define-syntax rb-set!
    (syntax-rules ()
      [(_ i val) (fxvector-set! run-bases i val)]))

  (define-syntax rl-get
    (syntax-rules ()
      [(_ i) (fxvector-ref run-lengths i)]))
  (define-syntax rl-set!
    (syntax-rules ()
      [(_ i val) (fxvector-set! run-lengths i val)]))

  (define (push-run! run-base run-length)
    (rb-set! stack-size run-base)
    (rl-set! stack-size run-length)
    (inc! stack-size))

  (define (tmp-array-length min-gallop)
    (let ([new-size min-gallop])
      (set! new-size (fxlogor new-size (fxsrl new-size 1)))
      (set! new-size (fxlogor new-size (fxsrl new-size 2)))
      (set! new-size (fxlogor new-size (fxsrl new-size 4)))
      (set! new-size (fxlogor new-size (fxsrl new-size 8)))
      (set! new-size (fxlogor new-size (fxsrl new-size 16)))
      (set! new-size (fx+ new-size 1))
      (if (fx< new-size 0)
          min-gallop
          (min new-size (fxsra range-length 1)))))

  (define (ensure-capacity! min-gallop)
    (if (fx< (vector-length tmp-array) min-gallop)
        (let ([len (tmp-array-length min-gallop)])
          ; (printf "[94] old-length: ~a\n" (vector-length tmp-array))
          ; (printf "[95] new-length: ~a\n" len)
          (set! tmp-array (make-vector len)))))

  (define (vector-copy! vsrc isrc vdst idst len)
    (define-syntax copy-loop
      (syntax-rules ()
        [(_ end* isrc* idst* next predict)
         (let ([end end*])
           (let loop ([isrc isrc*][idst idst*])
             (when (predict isrc end)
                   (vector-set! vdst idst (vector-ref vsrc isrc))
                   (loop (next isrc 1) (next idst 1)))))]))
    (if (eq? vsrc vdst)
        (cond
          [(fx< isrc idst) (copy-loop isrc (fx+ isrc len -1) (fx+ idst len -1) fx- fx>=)]
          [(fx> isrc idst) (copy-loop (fx+ isrc len) isrc idst fx+ fx<)]
          [else #f])
        (copy-loop (fx+ isrc len) isrc idst fx+ fx<)))

  (define (binary-insertion-sort lo hi start)
    (do-assert (and (fx<= lo start) (fx<= start hi)))

    (let for ([start (or (and (fx= start lo) (fx+ start 1)) start)])
      (when (fx< start hi)
            (let ([pivot (v-get start)])
              (do-assert (fx<= lo start))
              (let while ([left lo][right start])
                (if (fx< left right)
                    (let ([mid (fxsrl (fx+ left right) 1)])
                      (if (lt? pivot (v-get mid))
                          (while left mid)
                          (while (fx+ mid 1) right)))
                    (let ([n (fx- start left)])
                      (do-assert (fx= left right))
                      (cond
                        [(fx= n 2)
                         (v-set! (fx+ left 2) (v-get (fx+ left 1)))
                         (v-set! (fx+ left 1) (v-get left))]
                        [(fx= n 1)
                         (v-set! (fx+ left 1) (v-get left))]
                        [else (vector-copy! v left v (fx+ left 1) n)])
                      (v-set! left pivot)))))
            (for (fx+ start 1)))))

  (define (reverse-range lo hi)
    (if (fx< lo hi)
        (let ([t (v-get lo)])
          (v-set! lo (v-get hi))
          (v-set! hi t)
          (reverse-range (fx+ lo 1) (fx- hi 1)))))

  (define (count-run-and-make-ascending lo hi)
    (do-assert (fx< lo hi))

    (let ([run-hi (fx+ lo 1)])
      (cond
        [(fx= run-hi hi) 1]
        ;; strict descending
        [(lt? (v-get run-hi) (v-get lo))
         (let while ([run-hi (fx+ run-hi 1)])
           (if (and (fx< run-hi hi)
                    (lt? (v-get run-hi)
                         (v-get (fx- run-hi 1))))
               (while (fx+ run-hi 1))
               (begin
                 (reverse-range lo (fx- run-hi 1))
                 (fx- run-hi lo))))]
        ;; ascending
        [else
         (let while ([run-hi (fx+ run-hi 1)])
           (if (and (fx< run-hi hi)
                    (not (lt? (v-get run-hi)
                              (v-get (fx- run-hi 1)))))
               (while (fx+ run-hi 1))
               (fx- run-hi lo)))])))

  (define (compute-min-run-length n)
    (do-assert (fx>= n 0))
    (let while ([r 0][n n])
      (if (fx>= n MIN_MERGE)
          (while (fxlogor r (fxlogand n 1)) (fxsrl n 1))
          (fx+ n r))))

  (define (merge-collapse)
    (define (helper n)
      (cond
        [(and (fx> n 0)
              (fx<= (rl-get (fx- n 1))
                    (fx+ (rl-get n)
                         (rl-get (fx+ n 1)))))
         (if (fx< (rl-get (fx- n 1))
                  (rl-get (fx+ n 1)))
             (fx- n 1)
             n)]
        [(fx<= (rl-get n) (rl-get (fx+ n 1))) n]
        [else #f]))
    (if (fx> stack-size 1)
        (let ([n (helper (fx- stack-size 2))])
          (when (not (eq? n #f))
                (merge-at n)
                (merge-collapse)))))

  (define (merge-force-collapse)
    (define (helper n)
      (if (and (fx> n 0)
               (fx< (rl-get (fx- n 1))
                    (rl-get (fx+ n 1))))
          (fx- n 1)
          n))
    (when (fx> stack-size 1)
          (merge-at (helper (fx- stack-size 2)))
          (merge-force-collapse)))

  (define-syntax compute-with-hint1
    (syntax-rules ()
      [(_ hint) (lambda (last-ofs ofs) (values (fx+ last-ofs hint) (fx+ ofs hint)))]))
  (define-syntax compute-with-hint2
    (syntax-rules ()
      [(_ hint) (lambda (last-ofs ofs) (values (fx- hint ofs) (fx- hint last-ofs)))]))
  (define-syntax gallop
    (syntax-rules ()
      [(_ max-ofs* lt?-with-ofs compute-with-hint last-while-loop)
       (let ([max-ofs max-ofs*])
         (let while ([last-ofs 0][ofs 1])
           (cond
             [(and (fx< ofs max-ofs) (lt?-with-ofs ofs))
              (while ofs (let ([ofs (fx+ (fxsll ofs 1) 1)])
                           (if (fx<= ofs 0)
                               max-ofs
                               ofs)))]
             [else (let ([ofs (if (fx> ofs max-ofs) max-ofs ofs)])
                     (call-with-values
                       (lambda () (compute-with-hint last-ofs ofs))
                       last-while-loop))])))]))

  (define (gallop-left key a base len hint)
    (define-syntax get
      (syntax-rules ()
        [(_ i) (vector-ref a i)]))

    (define (last-while last-ofs ofs)
      (do-assert (and (fx<= -1 last-ofs) (fx< last-ofs ofs) (fx<= ofs len)))
      (let while ([last-ofs (fx+ last-ofs 1)] [ofs ofs])
        (cond
          [(fx< last-ofs ofs)
           (let ([m (fx+ last-ofs (fxsrl (fx- ofs last-ofs) 1))])
             (if (lt? (get (fx+ base m)) key)
                 (while (fx+ m 1) ofs)
                 (while last-ofs m)))]
          [else (do-assert (fx= last-ofs ofs)) ofs])))
    (do-assert (and (fx> len 0) (fx>= hint 0) (fx< hint len)))

    (if (lt? (get (fx+ base hint)) key)
        (gallop (fx- len hint)
                (lambda (ofs) (lt? (get (fx+ base hint ofs)) key))
                (compute-with-hint1 hint)
                last-while)
        (gallop (fx+ hint 1)
                (lambda (ofs) (not (lt? (get (fx- (fx+ base hint) ofs)) key)))
                (compute-with-hint2 hint)
                last-while)))

  (define (gallop-right key a base len hint)
    (define-syntax get
      (syntax-rules ()
        [(_ i) (vector-ref a i)]))

    (define (last-while last-ofs ofs)
      (do-assert (and (fx<= -1 last-ofs) (fx< last-ofs ofs) (fx<= ofs len)))
      (let while ([last-ofs (fx+ last-ofs 1)] [ofs ofs])
        (cond
          [(fx< last-ofs ofs)
           (let ([m (fx+ last-ofs (fxsrl (fx- ofs last-ofs) 1))])
             (if (lt? key (get (fx+ base m)))
                 (while last-ofs m)
                 (while (fx+ m 1) ofs)))]
          [else (do-assert (fx= last-ofs ofs)) ofs])))
    (do-assert (and (fx> len 0) (fx>= hint 0) (fx< hint len)))

    (if (lt? key (get (fx+ base hint)))
        (gallop (fx+ hint 1)
                (lambda (ofs) (lt? key (get (fx- (fx+ base hint) ofs))))
                (compute-with-hint2 hint)
                last-while)
        (gallop (fx- len hint)
                (lambda (ofs) (not (lt? key (get (fx+ base hint ofs)))))
                (compute-with-hint1 hint)
                last-while)))

  (define (merge-at i)
    (do-assert (fx>= stack-size 2))
    (do-assert (fx>= i 0))
    (do-assert (or (fx= i (fx- stack-size 2))
                   (fx= i (fx- stack-size 3))))

    (let ([base1 (rb-get i)][len1 (rl-get i)]
          [base2 (rb-get (fx+ i 1))][len2 (rl-get (fx+ i 1))])
      (do-assert (and (fx> len1 1)
                      (fx> len2 0)))
      (do-assert (fx= (fx+ base1 len1) base2))

      (rl-set! i (fx+ len1 len2))
      (when (fx= i (fx- stack-size 3))
            (rb-set! (fx+ i 1) (rb-get (fx+ i 2)))
            (rl-set! (fx+ i 1) (rl-get (fx+ i 2))))
      (dec! stack-size)

      (let ([k (gallop-right (v-get base2) v base1 len1 0)])
        (do-assert (fx>= k 0))

        (let ([base1 (fx+ base1 k)] [len1 (fx- len1 k)])
          (if (not (fx= len1 0))
              (let ([len2 (gallop-left (v-get (fx+ base1 len1 -1)) v base2 len2 (fx- len2 1))])
                (do-assert (fx>= len2 0))
                (cond
                  [(fx= len2 0) #f]
                  [(fx<= len1 len2)
                   (merge-lo base1 len1 base2 len2)]
                  [else
                   (merge-hi base1 len1 base2 len2)])))))))

  (define (merge-lo base1 len1 base2 len2)
    (define (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
      (do-assert (and (fx> len1 1) (fx> len2 0)))
      (cond
        [(lt? (v-get cur2) (t-get cur1))
         (v-set! dest (v-get cur2))
         (let ([dest (fx+ dest 1)]
               [cur2 (fx+ cur2 1)]
               [len2 (fx- len2 1)])
           (if (fx= len2 0)
               (break cur1 cur2 dest len1 len2 mgp)
               (let ([cnt2 (fx+ cnt2 1)][cnt1 0])
                 (if (fx< (fxlogor cnt1 cnt2) mgp)
                     (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
                     (do-while2 cur1 cur2 dest len1 len2 mgp)))))]
        [else
         (v-set! dest (t-get cur1))
         (let ([dest (fx+ dest 1)]
               [cur1 (fx+ cur1 1)]
               [len1 (fx- len1 1)])
           (if (fx= len1 1)
               (break cur1 cur2 dest len1 len2 mgp)
               (let ([cnt1 (fx+ cnt1 1)][cnt2 0])
                 (if (fx< (fxlogor cnt1 cnt2) mgp)
                     (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
                     (do-while2 cur1 cur2 dest len1 len2 mgp)))))]))

    (define (do-while2 cur1 cur2 dest len1 len2 mgp)
      (define (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (v-get cur2))
        (let ([dest (fx+ dest 1)]
              [cur2 (fx+ cur2 1)]
              [len2 (fx- len2 1)])
          (cond
            [(fx= len2 0) (break cur1 cur2 dest len1 len2 mgp)]
            [else
             (let ([cnt2 (gallop-left (t-get cur1) v cur2 len2 0)])
               (cond
                 [(not (fx= cnt2 0))
                  (vector-copy! v cur2 v dest cnt2)
                  (let ([dest (fx+ dest cnt2)]
                        [cur2 (fx+ cur2 cnt2)]
                        [len2 (fx- len2 cnt2)])
                    (if (fx= len2 0)
                        (break cur1 cur2 dest len1 len2 mgp)
                        (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)))]
                 [else (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)]))])))
      (define (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (t-get cur1))
        (let ([dest (fx+ dest 1)]
              [cur1 (fx+ cur1 1)]
              [len1 (fx- len1 1)])
          (if (fx= len1 1)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([mgp (fx- mgp 1)])
                (cond
                  [(or (fx>= cnt1 MIN_GALLOP)
                       (fx>= cnt2 MIN_GALLOP))
                   (do-while2 cur1 cur2 dest len1 len2 mgp)]
                  [else
                   (let ([mgp (if (fx< mgp 0) 2 (fx+ mgp 2))])
                     (do-while1 0 0 cur1 cur2 dest len1 len2 mgp))])))))

      (do-assert (and (fx> len1 1) (fx> len2 0)))
      (let ([cnt1 (gallop-right (v-get cur2) tmp-array cur1 len1 0)])
        (cond
          [(not (fx= cnt1 0))
           (vector-copy! tmp-array cur1 v dest cnt1)
           (let ([dest (fx+ dest cnt1)]
                 [cur1 (fx+ cur1 cnt1)]
                 [len1 (fx- len1 cnt1)])
             (if (fx<= len1 1)
                 (break cur1 cur2 dest len1 len2 mgp)
                 (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)))]
          [else (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)])))

    (define (break cur1 cur2 dest len1 len2 mgp)
      (set! min-gallop (max 1 mgp))
      (cond
        [(fx= len1 1)
         (do-assert (fx> len2 0))
         (vector-copy! v cur2 v dest len2)
         (v-set! (fx+ dest len2) (t-get cur1))]
        [(fx= len1 0)
         (do-assert (fx= len2 0))
         (error 'merge-lo
                "Comparison method violates its general contract!")]
        [else
         (do-assert (fx= len2 0))
         (do-assert (fx> len1 1))
         (vector-copy! tmp-array cur1 v dest len1)]))

    (do-assert (and (fx> len1 0) (fx> len2 0) (fx= (fx+ base1 len1) base2)))
    (ensure-capacity! len1)
    (vector-copy! v base1 tmp-array 0 len1)

    (let ([cur1 0][cur2 base2][dest base1])
      (v-set! dest (v-get cur2))
      (let ([dest (fx+ dest 1)]
            [cur2 (fx+ cur2 1)]
            [len2 (fx- len2 1)])
        (cond
          [(fx= len2 0) (vector-copy! tmp-array cur1 v dest len1)]
          [(fx= len1 1)
           (vector-copy! v cur2 v dest len2)
           (v-set! (fx+ dest len2) (t-get cur1))]
          [else (do-while1 0 0 cur1 cur2 dest len1 len2 min-gallop)]))))

  (define (merge-hi base1 len1 base2 len2)
    (define (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
      (do-assert (and (fx> len1 0) (fx> len2 1)))
      (cond
        [(lt? (t-get cur2) (v-get cur1))
         (v-set! dest (v-get cur1))
         (let ([dest (fx- dest 1)]
               [cur1 (fx- cur1 1)]
               [len1 (fx- len1 1)])
           (if (fx= len1 0)
               (break cur1 cur2 dest len1 len2 mgp)
               (let ([cnt1 (fx+ cnt1 1)][cnt2 0])
                 (if (fx< (fxlogor cnt1 cnt2) mgp)
                     (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
                     (do-while2 cur1 cur2 dest len1 len2 mgp)))))]
        [else
         (v-set! dest (t-get cur2))
         (let ([dest (fx- dest 1)]
               [cur2 (fx- cur2 1)]
               [len2 (fx- len2 1)])
           (if (fx= len2 1)
               (break cur1 cur2 dest len1 len2 mgp)
               (let ([cnt2 (fx+ cnt2 1)][cnt1 0])
                 (if (fx< (fxlogor cnt1 cnt2) mgp)
                     (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
                     (do-while2 cur1 cur2 dest len1 len2 mgp)))))]))

    (define (do-while2 cur1 cur2 dest len1 len2 mgp)
      (define (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (t-get cur2))
        (let ([dest (fx- dest 1)]
              [cur2 (fx- cur2 1)]
              [len2 (fx- len2 1)])
          (if (fx= len2 1)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([cnt2 (fx- len2 (gallop-left (v-get cur1) tmp-array 0 len2 (fx- len2 1)))])
                (if (not (fx= cnt2 0))
                    (let ([dest (fx- dest cnt2)]
                          [cur2 (fx- cur2 cnt2)]
                          [len2 (fx- len2 cnt2)])
                      (vector-copy! tmp-array (fx+ cur2 1) v (fx+ dest 1) cnt2)
                      (if (fx<= len2 1)
                          (break cur1 cur2 dest len1 len2 mgp)
                          (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)))
                    (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp))))))
      (define (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (v-get cur1))
        (let ([dest (fx- dest 1)]
              [cur1 (fx- cur1 1)]
              [len1 (fx- len1 1)])
          (if (fx= len1 0)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([mgp (fx- mgp 1)])
                (if (or (fx>= cnt1 MIN_GALLOP)
                        (fx>= cnt2 MIN_GALLOP))
                    (do-while2 cur1 cur2 dest len1 len2 mgp)
                    (let ([mgp (if (fx< mgp 0) 2 (fx+ mgp 2))])
                      (do-while1 0 0 cur1 cur2 dest len1 len2 mgp)))))))

      (do-assert (and (fx> len1 0) (fx> len2 1)))
      (let ([cnt1 (fx- len1 (gallop-right (t-get cur2) v base1 len1 (fx- len1 1)))])
        (if (not (fx= cnt1 0))
            (let ([dest (fx- dest cnt1)]
                  [cur1 (fx- cur1 cnt1)]
                  [len1 (fx- len1 cnt1)])
              (vector-copy! v (fx+ cur1 1) v (fx+ dest 1) cnt1)
              (if (fx= len1 0)
                  (break cur1 cur2 dest len1 len2 mgp)
                  (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)))
            (continue1 cnt1 cur1 cur2 dest len1 len2 mgp))))

    (define (break cur1 cur2 dest len1 len2 mgp)
      (set! min-gallop (max 1 mgp))
      (cond
        [(fx= len2 1)
         (do-assert (fx> len1 0))
         (let ([dest (fx- dest len1)]
               [cur1 (fx- cur1 len1)])
           (vector-copy! v (fx+ cur1 1) v (fx+ dest 1) len1)
           (v-set! dest (t-get cur2)))]
        [(fx= len2 0)
         (error 'merge-hi
                "Comparison method violates its general contract!")]
        [else
         (do-assert (fx= len1 0))
         (do-assert (fx> len2 1))
         (vector-copy! tmp-array 0 v (fx- dest (fx- len2 1)) len2)]))

    (do-assert (and (fx> len1 0) (fx> len2 0) (fx= (fx+ base1 len1) base2)))
    (ensure-capacity! len2)
    (vector-copy! v base2 tmp-array 0 len2)

    (let ([cur1 (fx+ base1 len1 -1)]
          [cur2 (fx- len2 1)]
          [dest (fx+ base2 len2 -1)])
      (v-set! dest (v-get cur1))
      (let ([dest (fx- dest 1)]
            [cur1 (fx- cur1 1)]
            [len1 (fx- len1 1)])
        (cond
          [(fx= len1 0) (vector-copy! tmp-array 0 v (fx- dest (fx- len2 1)) len2)]
          [(fx= len2 1)
           (let ([dest (fx- dest len1)]
                 [cur1 (fx- cur1 len1)])
             (vector-copy! v (fx+ cur1 1) v (fx+ dest 1) len1)
             (v-set! dest (t-get cur2)))]
          [else (do-while1 0 0 cur1 cur2 dest len1 len2 min-gallop)]))))

  (do-assert (fx>= range-length 1))

  (if (fx>= range-length 2)
      (if (fx< range-length MIN_MERGE)
          (let ([init-run-len (count-run-and-make-ascending lo hi)])
            (binary-insertion-sort lo hi (fx+ lo init-run-len)))
          (let ([min-run-len (compute-min-run-length range-length)])
            (init-stack-and-tmp-array)
            (let do-while ([n-remaining range-length]
                           [lo lo])
              (let ([run-len (count-run-and-make-ascending lo hi)])
                (if (fx< run-len min-run-len)
                    (let ([force (min n-remaining min-run-len)])
                      (binary-insertion-sort lo (fx+ lo force) (fx+ lo run-len))
                      (set! run-len force)))
                (push-run! lo run-len)
                (merge-collapse)
                (cond
                  [(fx> n-remaining run-len)
                   (do-while (fx- n-remaining run-len)
                             (fx+ lo run-len))]
                  [else
                   (do-assert (fx= (fx+ lo run-len) hi))
                   (merge-force-collapse)
                   (do-assert (fx= stack-size 1))]))))))
  v)

(define (tim-sort! lt? v)
  (tim-sort-range! lt? v 0 (vector-length v)))

(define (tim-sort lt? v)
  (tim-sort! lt? (vector-copy v)))


; Test
(include "test.ss")


#|
Check stability with v: #((0 . 0) (1 . 1) (2 . 2) (0 . 3) (1 . 4) (2 . 5))
    (tim-sort    <  v): #((0 . 0) (0 . 3) (1 . 1) (1 . 4) (2 . 2) (2 . 5))
    (vector-sort <  v): #((0 . 0) (0 . 3) (1 . 1) (1 . 4) (2 . 2) (2 . 5))

    (tim-sort    >  v): #((2 . 2) (2 . 5) (1 . 1) (1 . 4) (0 . 0) (0 . 3))
    (vector-sort >  v): #((2 . 2) (2 . 5) (1 . 1) (1 . 4) (0 . 0) (0 . 3))

    (tim-sort    <= v): #((0 . 3) (0 . 0) (1 . 4) (1 . 1) (2 . 5) (2 . 2))
    (vector-sort <= v): #((0 . 3) (0 . 0) (1 . 4) (1 . 1) (2 . 5) (2 . 2))

    (tim-sort    >= v): #((2 . 5) (2 . 2) (1 . 4) (1 . 1) (0 . 3) (0 . 0))
    (vector-sort >= v): #((2 . 5) (2 . 2) (1 . 4) (1 . 1) (0 . 3) (0 . 0))


Bench with size=10000000, range=1000000
(time (tim-sort < ...))
    12 collections
    5.671875000s elapsed cpu time, including 0.281250000s collecting
    5.784103500s elapsed real time, including 0.296505600s collecting
    204098304 bytes allocated, including 107475328 bytes reclaimed
comparations: 220247255, ordered: #t
(time (tim-sort < ...))
    no collections
    0.062500000s elapsed cpu time
    0.072210200s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (tim-sort >= ...))
    no collections
    0.109375000s elapsed cpu time
    0.116561100s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (tim-sort <= ...))
    no collections
    0.109375000s elapsed cpu time
    0.130977300s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (bench-tim-sort!))
    27 collections
    13.671875000s elapsed cpu time, including 1.671875000s collecting
    14.223362300s elapsed real time, including 1.770293600s collecting
    728264448 bytes allocated, including 531695584 bytes reclaimed

(time (vector-sort < ...))
    no collections
    3.500000000s elapsed cpu time
    3.502645100s elapsed real time
    80000064 bytes allocated
comparations: 240976582, ordered: #t
(time (vector-sort < ...))
    no collections
    0.171875000s elapsed cpu time
    0.182527500s elapsed real time
    80000064 bytes allocated
comparations: 9999999, ordered: #t
(time (vector-sort >= ...))
    no collections
    1.703125000s elapsed cpu time
    1.717274800s elapsed real time
    80000064 bytes allocated
comparations: 124434623, ordered: #t
(time (vector-sort <= ...))
    no collections
    1.593750000s elapsed cpu time
    1.638002100s elapsed real time
    80000064 bytes allocated
comparations: 124434623, ordered: #t
(time (bench-vector-sort!))
    4 collections
    16.937500000s elapsed cpu time, including 1.359375000s collecting
    17.231441600s elapsed real time, including 1.342752400s collecting
    960048192 bytes allocated, including 800068160 bytes reclaimed

[Finished in 33.2s]
 |#
