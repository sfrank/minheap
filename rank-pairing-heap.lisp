;;;; MINHEAP is by Stephan Frank <defclass@googlemail.com>, 2007-2012.
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defpackage :rank-pairing-heap (:use :cl)
  (:export
   #:rank-pairing-heap
   #:clear-heap
   #:empty-p
   #:insert
   #:peek-min
   #:extract-min
   #:extract-node
   #:heap-size
   #:decrease-key
   #:meld
   ))

(in-package :rank-pairing-heap)

;;;; Rank-Pairing min-heap, see "Bernhard Haeupler, Siddartha Sen,
;;;; Robert E. Tarjan: Rank-Pairing Heaps, ESA 2009, Lecture Notes in
;;;; Computer Science, 2009, Volume 5757/2009, 659--670."

;;; This is the one tree variant where the root is not a cyclic list,
;;; but a single node.

(defstruct (node (:constructor %make-node (key data)))
  (key 0 :type fixnum)
  (data nil)
  (lchild nil :type (or null node))
  (rchild nil :type (or null node))
  (parent nil :type (or null node))
  (rank 0 :type (integer 0 #.(floor (log most-positive-fixnum 2)))))

(defclass rank-pairing-heap ()
  ((size :initform 0 :initarg :size
         :type (integer 0 *)
         :accessor heap-size-access)
   (root :initform nil :initarg :roots
         :type (or null node))))

(defmethod print-object ((obj rank-pairing-heap) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (slot-value obj 'size))))

(defun heap-size (heap)
  (slot-value heap 'size))

(defun empty-p (heap)
  (zerop (slot-value heap 'size)))

(defun clear-heap (heap)
  (setf (slot-value heap 'size) 0
        (slot-value heap 'root) nil)
  heap)

(defun peek-min (heap)
  (let ((node (slot-value heap 'root)))
    (when node
      (values (node-data node)
              (node-key node)))))


(defun extract-min (heap)
  (declare (type rank-pairing-heap heap))
  (let ((root (slot-value heap 'root))
        (size (slot-value heap 'size))
        (buckets (make-array #.(ceiling (log most-positive-fixnum 2))
                             ;; approx of max. required buckets
                             :element-type '(or null node)
                             :initial-element nil)))
    (declare (dynamic-extent buckets)
             (optimize (speed 3) (space 0))
             (type (integer 1 #.most-positive-fixnum) size))
    (if (zerop (setf (slot-value heap 'size) (1- size)))
        (setf (slot-value heap 'root) nil)
        (let (tree)
          (loop for i = (node-lchild root) then next
                for next = (shiftf (node-rchild i) nil)
                do (let ((rank (node-rank i)))
                     (setf (node-parent i) nil)
                     (if (aref buckets rank)
                         (setf tree (link (link-fair (aref buckets rank) i) tree)
                               (aref buckets rank) nil)
                         (setf (aref buckets rank) i)))
                while next
                finally
                   (loop for v across buckets
                         ;; reducing the max. number of buckets to check
                         ;; depending on the max_rank <= lg(size) approximation
                         ;; makes it actually slower, so leave it for now.
                         ;for idx from (ceiling (log size 2)) downto 0
                         when v
                           do (setf tree (link v tree))
                         finally
                            (setf (slot-value heap 'root) tree)))))
    (values (node-data root)
            (node-key root))))

(defun insert (heap key data)
  (let ((node (%make-node key data)))
    (if (= (incf (slot-value heap 'size)) 1)
        (setf (slot-value heap 'root) node)
        (setf (slot-value heap 'root) 
              (link (slot-value heap 'root) node)))
    node))

(defun decrease-key (heap node key)
  (if (< (node-key node) key)
      (error "Cannot decrease key: new key greater than current key.")
      (progn (setf (node-key node) key)
             (setf (node-rank node)
                   (1+ (d-rank (node-lchild node))))))
  (unless (eq node (slot-value heap 'root))
    (setf (slot-value heap 'root) 
          (link (slot-value heap 'root)
                (cut-parent node))))
  node)

(defun extract-node (heap node)
  (decrease-key heap node #.most-negative-fixnum)
  (extract-min heap))

(defun meld (heap-a heap-b)
  "Melds HEAP-A and HEAP-B into HEAP-A and returns it. HEAP-B will be
empty after this operation but may be used further."
  (unless (zerop (slot-value heap-b 'size))
    (if (zerop (slot-value heap-a 'size))
        (setf (slot-value heap-a 'root)
              (slot-value heap-b 'root))
        (setf (slot-value heap-a 'root)
              (link (slot-value heap-a 'root)
                    (slot-value heap-b 'root))))
    (incf (slot-value heap-a 'size)
          (slot-value heap-b 'size))
    (clear-heap heap-b))
  heap-a)


;;; internal structure maintaining functions

(declaim (ftype (function ((or null node))
                          (integer -1 #.(floor (log most-positive-fixnum 2))))
                d-rank))

(defun attach-child (parent child)
  (declare (type node parent child)
           (optimize (speed 3) (space 0)))
  (when (node-lchild parent)
    (setf (node-parent (node-lchild parent))
          child))
  (shiftf (node-rchild child) (node-lchild parent) child)
  (setf (node-parent child) parent))

(defun link (node-a node-b)
  (declare (type (or null node) node-a node-b)
           (optimize (speed 3) (space 0)))
  (cond
    ((null node-b)
      node-a)
    ((null node-a)
      node-b)
    ((= (node-rank node-a)
        (node-rank node-b))
     (link-fair node-a node-b))
    (t
     (link-unfair node-a node-b))))

(defun link-fair (node-a node-b)
  (declare (type node node-a node-b)
           (optimize (speed 3) (space 0)))
  (cond 
    ((< (node-key node-a) (node-key node-b))
     (incf (node-rank node-a))
     (attach-child node-a node-b))
    (t
     (incf (node-rank node-b))
     (attach-child node-b node-a))))

(defun link-unfair (node-a node-b)
  (declare (type node node-a node-b)
           (optimize (speed 3) (space 0)))
  (cond 
    ((< (node-key node-a) (node-key node-b))
     (when (< (node-rank node-a)
              (node-rank node-b))
       (setf (node-rank node-a)
             (node-rank node-b)))
     (attach-child node-a node-b))
    (t
     (when (< (node-rank node-b)
              (node-rank node-a))
       (setf (node-rank node-b)
             (node-rank node-a)))
     (attach-child node-b node-a))))

(defun cut-parent (node)
  (declare (type node node)
           (optimize (speed 3) (space 0)))
  (if (eq (node-lchild (node-parent node)) node)
      (shiftf (node-lchild (node-parent node))
              (node-rchild node)
              nil)
      (shiftf (node-rchild (node-parent node))
              (node-rchild node)
              nil))
  ;; restore rank rule for decreased node
  (setf (node-rank node)
        (1+ (the fixnum (d-rank (node-lchild node)))))
  ;; type-2 rank reduction
  (loop for u = (shiftf (node-parent node) nil) then (node-parent u)
        for rv = (d-rank (node-lchild u))
        until (null (node-parent u))
        for rw = (d-rank (node-rchild u))
        for k = (if (> (abs (- rv rw)) 1)
                    (max rv rw)
                    (1+ (max rv rw)))
        while (< k (node-rank u))
        do (setf (node-rank u) k)
        finally 
           ;; set rank in case u is a root
           (unless (node-parent u)
             (setf (node-rank u) (1+ rv)))
           (return node)))

(declaim (inline d-rank))
(defun d-rank (node)
  (declare (type (or null node) node)
           (optimize (speed 3) (space 0)))
  (if node
      (node-rank node)
      -1))
