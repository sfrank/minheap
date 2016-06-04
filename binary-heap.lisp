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

(defpackage :binary-heap (:use :cl)
  (:export
   #:binary-heap
   #:clear-heap
   #:empty-p
   #:insert
   #:peek-min
   #:extract-min
   #:extract-node
   #:heap-size
   #:decrease-key
   #:meld
   #:alist-to-heap
   ))

(in-package :binary-heap)

(deftype array-index () `(integer 0 ,(1- array-dimension-limit)))

(defconstant +initial-size+ 50 "initial queue vector size")

;;;; binary min-heap

(defstruct (node (:constructor %make-node (key data index)))
  (key 0 :type fixnum)
  (index 0 :type array-index)
  (data nil))

(defclass binary-heap ()
  ((array :accessor bin-heap-array
          :type (vector (or null node))
          :initarg :array
          :initform (make-array +initial-size+
                                :adjustable t 
                                :fill-pointer 0 
                                :element-type '(or null node)
                                :initial-element nil))))

(defmethod print-object ((obj binary-heap) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (heap-size obj))))

;(declaim (inline parent left right %make-node))

(defun parent (k)
  (declare (type array-index k))
  (floor (1- k) 2))

(defun left (k)
  (declare (type (integer 0 #.(floor array-dimension-limit 2)) k))
  (1+ (* k 2)))

(defun right (k)
  (declare (type (integer 0 #.(floor array-dimension-limit 2)) k))
  (* (1+ k) 2))

(defun peek-min (heap)
  (let ((node (aref (bin-heap-array heap) 0)))
    (values (node-data node)
            (node-key node))))

(defun clear-heap (heap)
  (setf (fill-pointer (bin-heap-array heap)) 0))

(defun empty-p (heap)
  (zerop (fill-pointer (bin-heap-array heap))))

(defun heap-size (heap)
  (length (bin-heap-array heap)))

(defun extract-min (heap)
  (let ((array (bin-heap-array heap))
	(node (aref (bin-heap-array heap) 0)))
    (assert node)
    (setf (aref array 0) (aref array (1- (length array)))
          (aref array (1- (length array))) nil)
    (when (> (decf (fill-pointer array)) 1)
      (sink array 0))
    (values (node-data node)
            (node-key node))))

;(declaim (inline swap-nodes))
(defun swap-nodes (array i j)
  (declare (type array-index i j))
  (setf (node-index (aref array i)) j
        (node-index (aref array j)) i)
  (rotatef (aref array i) (aref array j)))

(defun sink (array index)
  (let ((maxindex (1- (length array))))
    (if (zerop maxindex)
        maxindex
        (loop for i = index then j
              with j = 0
              while (<= (left i) maxindex) do
                (cond
                  ((< maxindex (right i))
                   (setf j (left i)))
                  ((<= (node-key (aref array (left i)))
                       (node-key (aref array (right i))))
                   (setf j (left i)))
                  (t
                   (setf j (right i))))
                (when (<= (node-key (aref array i))
                          (node-key (aref array j)))
                  (loop-finish))
                (swap-nodes array i j)
              finally (return array)))))

(defun perlocate-up (array vindex)
  (loop for index = vindex then parent
        for parent = (parent index)
        with key = (node-key (aref array vindex))
        while (and (>= parent 0)
                   (< key (node-key (aref array parent))))
        do (swap-nodes array index parent) 
        finally (return (aref array index))))

(defun insert (heap key data)
  (let ((node (%make-node key data 0))
        (array (bin-heap-array heap)))
    (perlocate-up array (setf (node-index node) 
                              (vector-push-extend node array)))))

(defun decrease-key (heap node key)
  (let ((vector (bin-heap-array heap)))
    (when (< (node-key node) key)
      (error "Cannot decrease key: new key greater than current key."))
    (setf (node-key node) key)
    (perlocate-up vector (node-index node))))

(defun extract-node (heap node)
  (let ((key (node-key node))
        (value (node-data node)))
    (decrease-key heap node most-negative-fixnum)
    (extract-min heap)
    (values value key)))

(defun meld (heap-a heap-b)
  "Melds HEAP-A and HEAP-B into a new heap and returns it. HEAP-A is
returned as new union of both heaps."
  (let ((vector (bin-heap-array heap-a)))
    (loop for v across (bin-heap-array heap-b)
          do (vector-push-extend v vector))
    (vector-to-heapvector vector)
    heap-a))

(defun alist-to-heap (alist)
  "Coerces an ALIST of (KEY . VALUE) conses into a heap."
  (let ((node-list (loop for (key . value) in alist
                         collect (%make-node key value 0)))
        (length (length alist)))
    (let ((vector (make-array length 
                              :adjustable t 
                              :fill-pointer length
                              :element-type '(or null node)
                              :initial-contents node-list)))
      (make-instance 'binary-heap :array (vector-to-heapvector vector)))))

(defun vector-to-heapvector (vector)
  (loop for index from (floor (length vector) 2) downto 0
        do (sink vector index)
        finally (loop for n across vector
                      for i from 0 do (setf (node-index n) i))
                (return vector)))
