(defpackage :heap-violation-test (:use :CL :violation-heap :lisp-unit))

(in-package :heap-violation-test)

(define-test test-basic
  (let ((heap (make-instance 'violation-heap))
        (htable (make-hash-table :test #'eql)))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (dotimes (i 100)
      (let ((ii (+ i 100)))
        (setf (gethash ii htable) 
              (insert heap ii ii))))
    (assert-false (empty-p heap))
    (assert-eql 100 (heap-size heap))
    (decrease-key heap (gethash 120 htable) 50)
    (decrease-key heap (gethash 140 htable) 25)
    (decrease-key heap (gethash 160 htable) 15)
    (assert-eql 160 (peek-min heap))
    (assert-eql 160 (extract-min heap))
    (assert-eql 140 (peek-min heap))
    (assert-eql 140 (extract-node heap (gethash 140 htable)))
    (assert-eql 120 (extract-min heap))
    (assert-eql 100 (peek-min heap))
    (assert-eql 97 (heap-size heap))
    (clear-heap heap)
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-multiple-keys
  (let ((heap (make-instance 'violation-heap)))
    (loop for i in '(2 3 2 4 1 2)
          do (insert heap i i))
    (assert-eql 6 (heap-size heap))
    (assert-eql 1 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 3 (extract-min heap))
    (assert-eql 4 (extract-min heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-mk
  (let ((heap (make-instance 'violation-heap)))
    (loop for i in '(2 4 2 3 1)
          do (insert heap i i))
    (assert-eql 1 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 3 (extract-min heap))
    (assert-eql 4 (extract-min heap))))

(define-test test-stress
  (let ((heap (make-instance 'violation-heap))
        (size 75000))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (let ((list (remove-duplicates (loop for i below size
                                         collect (random most-positive-fixnum)))))
      (dolist (key list)
        (insert heap key key))
      (assert-false (empty-p heap))
      (dolist (key (sort list #'<))
        (assert-eql key (extract-min heap))))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-stress-2
  (let ((heap (make-instance 'violation-heap))
        (size 150))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (let ((list (remove-duplicates (loop for i below size
                                         collect i))))
      (dolist (key list)
        (insert heap key key))
      (assert-false (empty-p heap))
      (dolist (key (sort list #'<))
        (assert-eql key (extract-min heap))))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-multiple-keys-stress
  (let ((heap (make-instance 'violation-heap))
        (size 350)
        (key-range 100))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (let ((list (loop for i below size
                      collect (random key-range))))
      (dolist (key list)
        (insert heap key key))
      (assert-false (empty-p heap))
      (dolist (key (sort list #'<))
        (assert-eql key (extract-min heap))))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-meld
  (let ((heap-1 (make-instance 'violation-heap))
        (heap-2 (make-instance 'violation-heap)))
    (assert-true (empty-p heap-1))
    (assert-eql 0 (heap-size heap-1))
    (assert-true (empty-p heap-2))
    (assert-eql 0 (heap-size heap-2))
    (loop for i in '(1 2 3 4 5)
          do (insert heap-1 i i))
    (assert-false (empty-p heap-1))
    (assert-eql 5 (heap-size heap-1))
    (loop for i in '(6 7 8 9)
          do (insert heap-2 i i))
    (assert-false (empty-p heap-2))
    (assert-eql 4 (heap-size heap-2))
    (let ((melded-heap (meld heap-1 heap-2)))
      (assert-false (empty-p melded-heap))
      (assert-true (empty-p heap-2))
      (assert-eql 9 (heap-size melded-heap))
      (loop for i in '(1 2 3 4 5 6 7 8 9)
            do (assert-eql i (extract-min melded-heap)))
      (assert-true (empty-p melded-heap))
      (assert-eql 0 (heap-size melded-heap)))))

(define-test test-meld-2
  (let ((heap-1 (make-instance 'violation-heap))
        (heap-2 (make-instance 'violation-heap)))
    (assert-true (empty-p heap-1))
    (assert-eql 0 (heap-size heap-1))
    (assert-true (empty-p heap-2))
    (assert-eql 0 (heap-size heap-2))
    (loop for i in '(1 2 3 4 5)
          do (insert heap-2 i i))
    (assert-false (empty-p heap-2))
    (assert-eql 5 (heap-size heap-2))
    (loop for i in '(6 7 8 9 10 11)
          do (insert heap-1 i i))
    (assert-false (empty-p heap-1))
    (assert-eql 6 (heap-size heap-1))
    (let ((melded-heap (meld heap-1 heap-2)))
      (assert-false (empty-p melded-heap))
      (assert-true (empty-p heap-2))
      (assert-eql 11 (heap-size melded-heap))
      (loop for i in '(1 2 3 4 5 6 7 8 9 10 11)
            do (assert-eql i (extract-min melded-heap)))
      (assert-true (empty-p melded-heap))
      (assert-eql 0 (heap-size melded-heap)))))

(define-test test-cascading
  (let* ((heap (make-instance 'violation-heap))
         (list (cdr (sort (loop for i in '(5 3 0 2 4 1 7)
                                collect (insert heap i i))
                          #'< :key #'violation-heap::node-key))))
    (assert-eql 7 (heap-size heap))
    (extract-min heap)
    (decrease-key heap (caddr list) 0)   ; set key of node 3 to 0
    (decrease-key heap (car (subseq list 4)) 2) ; set key of node 5 to 2
    (decrease-key heap (car (subseq list 4)) -1) ; set key of node 5 to -1
    (dolist (value '(5 3 1 2 4 7))
      (assert-eql value (extract-min heap)))
    (assert-eql 0 (heap-size heap))))

(define-test test-cascading-2
  (let* ((heap (make-instance 'violation-heap))
         (list (loop for i in '(7 6 5 4 3 2 1)
                     collect (insert heap i i))))
    (assert-eql 7 (heap-size heap))
    (extract-min heap)
    (decrease-key heap (car list) 1) ; set key of node 7 to 1
    (decrease-key heap (car (subseq list 2)) 0) ; set key of node 5 to 0
    (decrease-key heap (car (subseq list 3)) -1) ; set key of node 4 to -1
    (dolist (value '(4 5 7 2 3 6))
      (assert-eql value (extract-min heap)))
    (assert-eql 0 (heap-size heap))))

(defun timing ()
  (let ((heap (make-instance 'violation-heap))
        (size 100000)
        list)
    (dotimes (i size)
      (let ((key (random most-positive-fixnum)))
        (push key list)))
    (time
     (progn
       (loop for i in list
             do (insert heap i i))
       (dotimes (i size)
         (extract-min heap))))))
